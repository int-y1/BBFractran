# python -m decider.oned_progress_to_lean
import os
import re
from math import comb

from decider.oned_progress import (_pnorm, _padd, _psub, _pscale,
                                   oned_progress_cert, cert_str)
from decider.utils import unparse_line

"""
Translate a `oned_progress` certificate into a self-contained Lean 4 proof.

The entry point is

    oned_progress_to_lean(F, cert, name) -> str

which returns the contents of a Lean file proving `¬halts fm c₀` for the
Fractran machine `F`.  Dropping that string into `proofs/BBfLean/Size23/Foo.lean`
(with `name='Foo'`) gives a file that compiles against `BBfLean.FM` and uses only
the three usual axioms (`propext`, `Classical.choice`, `Quot.sound`).

For a batch there is

    oned_progress_to_lean_dir(pairs, out_dir) -> list[str]

which writes one file per `(F, cert)` plus a `Summary.lean` restating every
`nonhalt` against a spelled-out `fm`, laid out so that moving `out_dir` into
`proofs/BBfLean/` compiles as-is.

--------------------------------------------------------------------------------
WHAT HAS TO BE TRANSLATED

`oned_progress` proves non-halting by exhibiting a 1-D family f(u) of states with
f(u) |-+ f(u') for some u' > u, plus a concrete reachable member f(w).  The
family and the thresholds are only the *statement*; the proof lives in the
symbolic transcript that the engine records for each residue branch:

    ('step', j)             -- rule j fires once
    ('accel', cyc, Dc, V)   -- the rule sequence `cyc` (constant net delta `Dc`)
                               is iterated V times, V a polynomial in m

So the Lean file is assembled as:

  * `def Q`, `def c₀`, `def fm`   -- same encoding as `other/gen_lean.py`
  * one `cycN_core` induction lemma per distinct accelerated cycle, in the
    classical "chain" shape `∀ k x…, ⟨…+ k*d …⟩ [fm]⊢* ⟨…⟩`
  * one `transN` theorem per residue branch, composed out of `execute fm n`
    blocks (runs of primitive steps) and applications of the cycle lemmas
  * `progress_nonhalt(_simple)` glue, and `execute fm N` for the bootstrap.

--------------------------------------------------------------------------------
THE ONE REAL DIFFICULTY: MAKING `step fm` REDUCE

`step fm` closes `fm ⟨…⟩ = some ⟨…⟩` by `rfl`, so Lean's `match` decision tree
has to reduce on symbolic register values.  A register written `e + c` (c a
numeral) can be peeled c times; a numeral can be peeled arbitrarily; a bare
`2*m` is stuck.  Since a `match` column is split at most `maxneed i` times
(the largest `k` occurring in a pattern `xᵢ+k` for that column), the condition

    every register is a numeral, or has a trailing numeral ≥ maxneed i     (C)

is *sufficient* for the whole tree to reduce, whatever column order the match
compiler picks.

(C) is arranged by a change of variable.  The engine's decisions are only valid
for m ≥ m_lo, so we are free to substitute m := m + T for any T ≥ m_lo — this
shrinks the domain, so every recorded decision stays valid, and the transcript
replays verbatim (only the polynomials change).  Every register polynomial is
either constant — emitted as a numeral, always fine — or has a positive leading
coefficient, so its constant term p(T) grows without bound with T.  Hence a large
enough T gives (C) everywhere, and simultaneously makes every polynomial have
non-negative coefficients, which is what lets it be written in ℕ at all.

Inside a cycle lemma the registers are `x + d*k + off` with `off` a numeral of
our choosing, so (C) there reads `off + pre_t ≥ maxneed i` at every position t of
the cycle.  `off` is capped by how much slack the instantiation has, so when it
does not fit we peel whole cycles off the front (`c1`) and/or the back (`c2`) of
the acceleration and emit them as ordinary steps; both knobs monotonically
increase the available slack, so the search terminates.

Registers that must be *small* (they block a higher-priority rule) are always
constant with zero net delta — an acceleration whose blockers moved, or whose
count was bounded by a blocker, would have had a constant cycle count and been
rejected by the engine — so they are always emitted as numerals.  This is
re-checked while planning, and the whole plan is additionally replayed against a
concrete simulation for several values of m before anything is printed.

--------------------------------------------------------------------------------
COVERAGE

Checked against every machine `oned_progress` decides in `holdout/sz23_21233.txt`
minus `holdout/sz23_8021.txt` (13212: 7956 additive / 4781 multiplicative / 475
template) and in `holdout/sz24_231432.txt` minus `holdout/sz24_85726.txt`
(145706: 79108 / 60433 / 6165).  Every certificate translates with the default
arguments, and every one of the 158918 Lean files compiles under default options,
in Lean 4.33.0-rc1 and again in 4.36.0-rc1: no errors, no `sorryAx`, only
`[propext]` or `[propext, Quot.sound]`.

With `lean -j1` (Lean 4.33.0-rc1), one file takes ~5s of CPU at the median (p99
50-63s, max 350s) and ~1.6 GiB peak RSS, ~1.5 GiB of which is the shared Mathlib
import (max 7.8 GiB); 32 CPU-hours for sz23 and 314 for sz24.  Lean 4.36.0-rc1 is
somewhat faster per file and uses less memory (max 6.9 GiB).  The tail is the bootstrap
`c₀ [fm]⊢* f(w)`, which is a literal step-by-step run -- `max_boot` caps how
long a one the translator will accept, at the price of rejecting the
certificate.  It is uncapped by default: every anchor is already within
`oned_progress_cert`'s own `step_cap`, and a cap below that (the old default was
30000) rejects certificates that are fine.
"""


class TranslationError(Exception):
    """The certificate could not be turned into a Lean proof."""


class _Fail(Exception):
    """This attempt (this shift T) does not work; try the next one."""


_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")


def _check_ident(name):
    if not _IDENT.match(name):
        raise TranslationError(f'{name!r} is not a Lean identifier')
    return name


# ============================================================================
# integer polynomials in the branch variable m  (p[k] = coefficient of m**k)
# ============================================================================

def _is_const(p):
    return len(_pnorm(p)) <= 1


def _cval(p):
    q = _pnorm(p)
    return q[0] if q else 0


def _c0(p):
    q = _pnorm(p)
    return q[0] if q else 0


def _nonneg(p):
    return all(c >= 0 for c in _pnorm(p))


def _shift(p, T):
    """p(m) -> p(m+T)."""
    out = []
    for k, c in enumerate(_pnorm(p)):
        out = _padd(out, [c * comb(k, i) * T ** (k - i) for i in range(k + 1)])
    return _pnorm(out)


def _peval(p, m):
    v = 0
    for c in reversed(_pnorm(p)):
        v = v * m + c
    return v


def _lean_poly(p, var='m'):
    """Lean term for a non-negative-coefficient polynomial.

    The constant term is printed last, so that `step fm` can peel it."""
    p = _pnorm(p)
    if not p:
        return '0'
    assert all(c >= 0 for c in p), p
    terms = []
    for d in range(len(p) - 1, 0, -1):
        if p[d] == 0:
            continue
        mono = '*'.join([var] * d)
        terms.append(mono if p[d] == 1 else f'{p[d]}*{mono}')
    if p[0] or not terms:
        terms.append(str(p[0]))
    return ' + '.join(terms)


def _lean_state(state, var='m'):
    return ', '.join(_lean_poly(p, var) for p in state)


_OPEN, _CLOSE = '(⟨[', ')⟩]'


def _atoms(text):
    """Split on spaces, but keep a bracketed group together."""
    out, cur, depth = [], '', 0
    for tok in text.split(' '):
        cur = tok if not cur else cur + ' ' + tok
        depth += sum(c in _OPEN for c in tok) - sum(c in _CLOSE for c in tok)
        if depth <= 0:
            out.append(cur)
            cur, depth = '', 0
    return out + ([cur] if cur else [])


def _wrap_line(line, width=96, anydepth=False):
    """Break an over-long Lean line, continuing on deeper-indented lines.

    Breaks are taken between bracketed groups; `anydepth` breaks at any space,
    which is only safe for a line that is one plain term."""
    if len(line) <= width:
        return [line]
    body = line.lstrip()
    indent = line[:len(line) - len(body)]
    out, cur = [], indent
    for atom in (body.split(' ') if anydepth else _atoms(body)):
        if cur.strip() and len(cur) + 1 + len(atom) > width:
            out.append(cur)
            cur = indent + '    '
        cur += atom if not cur.strip() else ' ' + atom
    return out + [cur]


def _wrap_text(text, width=96):
    out = []
    for line in text.split('\n'):
        wrapped = _wrap_line(line, width)
        if (any(len(w) > width for w in wrapped)
                and line.lstrip().startswith('exact ')):
            wrapped = _wrap_line(line, width, anydepth=True)
        out += wrapped
    return '\n'.join(out)


def _paren(s):
    return s if (s.isdigit() or s.isidentifier()) else f'({s})'


# ============================================================================
# planning a branch: transcript -> list of Lean-emittable operations
# ============================================================================

def _prefix_deltas(F, cyc, W):
    pre = [[0] * W]
    for j in cyc:
        pre.append([pre[-1][i] + F[j][i] for i in range(W)])
    return pre


def _check_state(state, maxneed):
    """Condition (C) plus representability in ℕ."""
    for i, p in enumerate(state):
        if not _nonneg(p):
            return False
        if _is_const(p):
            if _cval(p) < 0:
                return False
        elif _c0(p) < maxneed[i]:
            return False
    return True


def _fires(F, state, j):
    """Is rule `j` the one that fires, uniformly?  (sanity check on the plan)"""
    for rp in range(j + 1):
        blocked = False
        for i, d in enumerate(F[rp]):
            if d >= 0:
                continue
            p = state[i]
            if _is_const(p):
                if _cval(p) + d < 0:
                    blocked = True
                    break
            elif _c0(p) + d < 0:
                return False        # cannot decide uniformly
        if rp == j:
            return not blocked
        if not blocked:
            return False
    return False


def _try_cycle(F, W, maxneed, cyc, Dc, V, S0, c1, c2):
    """Plan one acceleration as c1 raw cycles, `k` chained cycles, c2 raw cycles."""
    L = len(cyc)
    pre = _prefix_deltas(F, cyc, W)
    mu = [min(pre[t][i] for t in range(L)) for i in range(W)]
    S1 = [_pnorm(_padd(S0[i], [c1 * Dc[i]])) for i in range(W)]
    k = _psub(V, [c1 + c2])
    if not _nonneg(k) or _c0(k) < 1 or _is_const(k):
        return None

    lits, offs, xs = {}, {}, {}
    for i in range(W):
        if Dc[i] == 0 and _is_const(S1[i]):
            lits[i] = _cval(S1[i])
            continue
        off = max(0, maxneed[i] - mu[i] - (-Dc[i] if Dc[i] < 0 else 0))
        if Dc[i] < 0:
            x = _psub(S1[i], _padd(_pscale(k, -Dc[i]), [off]))
        else:
            x = _psub(S1[i], [off])
        if not _nonneg(x):
            return None
        offs[i], xs[i] = off, x

    # every guard of the fired rule holds, and every higher-priority rule is
    # blocked by a register that is a numeral for the whole chain
    for t in range(L):
        rj = cyc[t]
        for i in range(W):
            need = -F[rj][i]
            if need > 0 and i in lits and lits[i] + pre[t][i] < need:
                return None
        for rp in range(rj):
            if not any(-F[rp][i] > 0 and i in lits
                       and lits[i] + pre[t][i] < -F[rp][i] for i in range(W)):
                return None
    return {'c1': c1, 'c2': c2, 'k': k, 'lits': lits, 'offs': offs, 'xs': xs}


def _plan_branch(F, W, maxneed, start, events, T, min_c1=0):
    """Replay a transcript at shift T and turn it into Lean-emittable ops."""
    cur = [_shift(p, T) for p in start]
    ops = []

    def do_steps(seq):
        nonlocal cur
        for j in seq:
            if not _check_state(cur, maxneed):
                raise _Fail
            if not _fires(F, cur, j):
                raise _Fail
            ops.append({'kind': 'step', 'rule': j, 'src': list(cur)})
            cur = [_pnorm(_padd(cur[i], [F[j][i]])) for i in range(W)]

    first_accel = True
    for ev in events:
        if ev[0] == 'step':
            do_steps([ev[1]])
            continue
        _, cyc, Dc, V = ev
        Vs = _shift(V, T)
        lo = min_c1 if first_accel else 0
        first_accel = False
        plan = None
        for tot in range(lo, lo + 13):
            for c1 in range(lo, tot + 1):
                plan = _try_cycle(F, W, maxneed, cyc, Dc, Vs, cur, c1, tot - c1)
                if plan is not None:
                    break
            if plan is not None:
                break
        if plan is None:
            raise _Fail
        do_steps(list(cyc) * plan['c1'])
        src = list(cur)
        cur = [_pnorm(_padd(cur[i], _pscale(plan['k'], Dc[i]))) for i in range(W)]
        if not _check_state(src, maxneed) or not _check_state(cur, maxneed):
            raise _Fail
        plan.update(kind='cycle', cyc=list(cyc), Dc=list(Dc), src=src, dst=list(cur))
        ops.append(plan)
        do_steps(list(cyc) * plan['c2'])
    if not _check_state(cur, maxneed):
        raise _Fail
    return ops, cur


def _has_step(ops):
    return any(o['kind'] == 'step' for o in ops)


def _plan(F, W, maxneed, start, events, T):
    ops, end = _plan_branch(F, W, maxneed, start, events, T)
    if not _has_step(ops):
        ops, end = _plan_branch(F, W, maxneed, start, events, T, min_c1=1)
    if not _has_step(ops):
        raise _Fail
    return ops, end


# ============================================================================
# concrete cross-check of a plan
# ============================================================================

def _concrete_step(F, s):
    for j, rule in enumerate(F):
        if all(s[i] + d >= 0 for i, d in enumerate(rule)):
            return j, [s[i] + d for i, d in enumerate(rule)]
    return -1, None


def _verify_plan(F, W, ops, start, end, mvals=(0, 1, 2), budget=2 * 10 ** 6):
    """Replay the plan against a concrete simulation.  Catches planning bugs.

    `m = 0` is always checked; the later values only while `budget` lasts."""
    for m in mvals:
        if budget <= 0 and m:
            break
        s = [_peval(p, m) for p in start]
        for op in ops:
            if [_peval(p, m) for p in op['src']] != s:
                return False
            if op['kind'] == 'step':
                budget -= 1
                j, s2 = _concrete_step(F, s)
                if j != op['rule']:
                    return False
                s = s2
            else:
                budget -= _peval(op['k'], m) * len(op['cyc'])
                for _ in range(_peval(op['k'], m)):
                    for r in op['cyc']:
                        j, s2 = _concrete_step(F, s)
                        if j != r:
                            return False
                        s = s2
        if [_peval(p, m) for p in end] != s:
            return False
    return True


# ============================================================================
# Lean emission
# ============================================================================

def _fm_lines(F):
    W = len(F[0])
    out = []
    for inst in F:
        s0 = ', '.join(chr(ord('a') + i) + (f'+{-inst[i]}' if inst[i] < 0 else '')
                       for i in range(W))
        s1 = ', '.join(chr(ord('a') + i) + (f'+{inst[i]}' if inst[i] > 0 else '')
                       for i in range(W))
        out.append(f'⟨{s0}⟩ => some ⟨{s1}⟩')
    return out


# `execute fm n` is `iterate n step fm`, which recurses once per step, so long
# runs have to be cut into pieces to stay under Lean's `maxRecDepth`.
_CHUNK = 100

# Heartbeats are per declaration, so a branch whose proof is a long chain of
# blocks is cut into standalone segment theorems of at most this many blocks.
# (Chains of 89+ blocks have been seen to exceed the default 200000.)
_SEG = 32


def _boot(F, W, steps, st):
    """`c₀ [fm]⊢* <anchor>`.

    Emitted as `_CHUNK`-sized standalone theorems: `execute fm n` recurses once
    per step, and a single long run blows both `maxRecDepth` and the
    per-declaration heartbeat budget."""
    s = [1] + [0] * (W - 1)
    states = [tuple(s)]
    for _ in range(steps):
        j, s = _concrete_step(F, s)
        if j < 0:
            raise _Fail
        states.append(tuple(s))
    if ', '.join(map(str, states[-1])) != st:
        raise _Fail
    thms, pos, last = [], 0, None
    while pos < steps:
        nxt = min(pos + _CHUNK, steps)
        dst = '⟨' + ', '.join(map(str, states[nxt])) + '⟩'
        nm = f'boot{len(thms)}'
        run = f'by execute fm {nxt - pos}'
        # left-associated: every term stays shallow, and every chunk gets its
        # own `maxRecDepth` and heartbeat budget
        pf = f'({run})' if last is None else f'stepStar_trans {last} ({run})'
        thms.append(f'theorem {nm} : (c₀ : Q) [fm]⊢* {dst} := {pf}\n')
        last, pos = nm, nxt
    term = last if last is not None else '(by exists 0)'
    return thms, [f'  exact stepStar_not_halts_not_halts (c₂ := ⟨{st}⟩) {term} key']


def _add_lit(expr, c):
    return expr if c == 0 else f'{expr} + {c}'


def _mul(c, expr):
    return expr if c == 1 else f'{c}*{expr}'


class _Emitter:
    """Collects the cycle lemmas (shared between branches) and emits proofs."""

    def __init__(self, F, W, maxneed):
        self.F, self.W, self.maxneed = F, W, maxneed
        self.cycles = {}            # cycle signature -> (name, x indices)
        self.order = []

    # -- cycle lemma ---------------------------------------------------------

    def cycle_lemma(self, op):
        W, F = self.W, self.F
        Dc, cyc, lits, offs = op['Dc'], op['cyc'], op['lits'], op['offs']
        sig = (tuple(cyc), tuple(Dc), tuple(sorted(lits.items())),
               tuple(sorted(offs.items())))
        if sig in self.cycles:
            return self.cycles[sig]
        name = f'cyc{len(self.cycles) + 1}'

        xs = sorted(offs)
        var = {i: f'x{i}' for i in xs}

        def lhs(i, kexpr='k', sub=None):
            if i in lits:
                return str(lits[i])
            v = (sub or var)[i]
            return (_add_lit(f'{v} + ' + _mul(-Dc[i], _paren(kexpr)), offs[i]) if Dc[i] < 0
                    else _add_lit(v, offs[i]))

        def rhs(i, kexpr='k', sub=None):
            if i in lits:
                return str(lits[i])
            v = (sub or var)[i]
            return (_add_lit(f'{v} + ' + _mul(Dc[i], _paren(kexpr)), offs[i]) if Dc[i] > 0
                    else _add_lit(v, offs[i]))

        xv = ' '.join(var[i] for i in xs)
        body = [f'/-- The rule block {", ".join(f"R{j + 1}" for j in cyc)}, '
                'iterated `k` times. -/',
                f'theorem {name}_core : ∀ k {xv},',
                f'    (⟨{", ".join(lhs(i, "k") for i in range(W))}⟩ : Q) [fm]⊢* '
                f'⟨{", ".join(rhs(i, "k") for i in range(W))}⟩ := by',
                '  intro k',
                '  induction k with',
                f'  | zero => intro {xv}; exists 0',
                '  | succ k ih =>',
                f'    intro {xv}']
        rws = [f'show {lhs(i, "k+1")} = '
               f'{_add_lit(f"{var[i]} + " + _mul(-Dc[i], "k"), offs[i] - Dc[i])} from by ring'
               for i in xs if Dc[i] < 0]
        if rws:
            body.append('    rw [' + ',\n         '.join(rws) + ']')
        body.extend(['    step fm'] * len(cyc))
        nxt = {i: (f'({var[i]} + {Dc[i]})' if Dc[i] > 0 else var[i]) for i in xs}
        body.append(f'    apply stepStar_trans (ih {" ".join(nxt[i] for i in xs)})')
        rws = [f'show {rhs(i, "k+1")} = {rhs(i, "k", nxt)} from by ring'
               for i in xs if Dc[i] > 0]
        if rws:
            body.append('    rw [' + ',\n         '.join(rws) + ']')
        body.append('    exists 0')

        ys = ' '.join(f'y{i}' for i in range(W))
        zs = ' '.join(f'z{i}' for i in range(W))
        hyp = ''.join(f' (hy{i} : y{i} = {lhs(i, "k")})' for i in range(W))
        hyp += ''.join(f' (hz{i} : z{i} = {rhs(i, "k")})' for i in range(W))
        body += ['',
                 f'theorem {name} (k {xv} {ys} {zs} : ℕ){hyp} :',
                 f'    (⟨{", ".join(f"y{i}" for i in range(W))}⟩ : Q) [fm]⊢* '
                 f'⟨{", ".join(f"z{i}" for i in range(W))}⟩ := by',
                 '  rw [' + ', '.join([f'hy{i}' for i in range(W)]
                                      + [f'hz{i}' for i in range(W)]) + ']',
                 f'  exact {name}_core k {xv}']
        self.cycles[sig] = (name, xs)
        self.order.append('\n'.join(body) + '\n')
        return name, xs

    def cycle_call(self, op, var='m'):
        name, xs = self.cycle_lemma(op)
        args = [_paren(_lean_poly(op['k'], var))]
        args += [_paren(_lean_poly(op['xs'][i], var)) for i in xs]
        args += [_paren(_lean_poly(p, var)) for p in op['src']]
        args += [_paren(_lean_poly(p, var)) for p in op['dst']]
        args += ['(by ring)'] * (2 * self.W)
        return f'{name} {" ".join(args)}'

    # -- branch theorem ------------------------------------------------------

    def branch(self, name, ops, start, end, var='m', doc=None):
        """A `⊢⁺` theorem taking the branch from `start` to `end`."""
        blocks = []                 # (src, dst, proof text, is_plus)
        i = 0
        while i < len(ops):
            if ops[i]['kind'] == 'step':
                j = i
                while (j < len(ops) and ops[j]['kind'] == 'step'
                       and j - i < _CHUNK):
                    j += 1
                dst = (ops[j]['src'] if j < len(ops) else end)
                blocks.append([ops[i]['src'], dst, f'by execute fm {j - i}', False])
                i = j
            else:
                blocks.append([ops[i]['src'], ops[i]['dst'],
                               self.cycle_call(ops[i], var), False])
                i += 1
        plus = next(k for k, b in enumerate(blocks) if b[2].startswith('by execute'))
        blocks[plus][3] = True

        head = ([f'/-- {doc} -/'] if doc else []) + [
                f'theorem {name} ({var} : ℕ) :',
                f'    (⟨{_lean_state(start, var)}⟩ : Q) [fm]⊢⁺ '
                f'⟨{_lean_state(end, var)}⟩ := by']
        if len(blocks) <= _SEG:
            return '\n'.join(head + self._chain(blocks, plus, var))

        # too long for one heartbeat budget: each segment becomes its own
        # theorem, and the branch theorem chains the segments
        segs, out = [], []
        for g, a in enumerate(range(0, len(blocks), _SEG)):
            seg = blocks[a:a + _SEG]
            p = plus - a if a <= plus < a + _SEG else None
            arrow = '⊢*' if p is None else '⊢⁺'
            out.append('\n'.join([
                f'theorem {name}_seg{g} ({var} : ℕ) :',
                f'    (⟨{_lean_state(seg[0][0], var)}⟩ : Q) [fm]{arrow} '
                f'⟨{_lean_state(seg[-1][1], var)}⟩ := by']
                + self._chain(seg, p, var)) + '\n')
            segs.append([seg[0][0], seg[-1][1], f'{name}_seg{g} {var}', p is not None])
        return '\n'.join(out + head + self._chain(segs, plus // _SEG, var))

    @staticmethod
    def _chain(blocks, plus, var):
        """`have h_k` per block, then their composition (`⊢⁺` iff `plus` is set)."""
        lines = []
        for k, b in enumerate(blocks):
            arrow = '⊢⁺' if b[3] else '⊢*'
            lines.append(f'  have h{k} : (⟨{_lean_state(b[0], var)}⟩ : Q) [fm]{arrow} '
                         f'⟨{_lean_state(b[1], var)}⟩ := {b[2]}')
        lines.append('  exact ' + _compose(len(blocks), plus))
        return lines


def _compose(n, plus):
    """Fold h0..h_{n-1} into a single `⊢⁺`, with block `plus` supplying the `⁺`,
    or into a single `⊢*` if `plus` is None."""
    def star(a, b):                 # h_a .. h_{b-1}, all ⊢*
        if b - a == 1:
            return f'h{a}'
        return f'(stepStar_trans h{a} {star(a + 1, b)})'
    if plus is None:
        return star(0, n)
    out = f'h{plus}'
    if plus + 1 < n:
        out = f'(stepPlus_stepStar_stepPlus {out} {star(plus + 1, n)})'
    if plus > 0:
        out = f'(stepStar_stepPlus_stepPlus {star(0, plus)} {out})'
    return out


def _pmul(a, b):
    a, b = _pnorm(a), _pnorm(b)
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return _pnorm(out)


def _poly_compose(p, q):
    """p(q(m))."""
    out = []
    for c in reversed(_pnorm(p)):
        out = _padd(_pmul(out, q), [c])
    return _pnorm(out)


def _wrap(name, core, start, end, W, var='m', wrap_src=False):
    """`core`, restated with equational hypotheses so callers can `by ring`."""
    xs = [f'x{i}' for i in range(W)]
    ys = [f'y{i}' for i in range(W)]
    binders, hyps, subs = [var], [], []
    src = _lean_state(start, var)
    if wrap_src:
        binders += xs
        hyps += [f'(hx{i} : x{i} = {_lean_poly(start[i], var)})' for i in range(W)]
        subs += [f'hx{i}' for i in range(W)]
        src = ', '.join(xs)
    binders += ys
    hyps += [f'(hy{i} : y{i} = {_lean_poly(end[i], var)})' for i in range(W)]
    subs += [f'hy{i}' for i in range(W)]
    return '\n'.join([
        f'theorem {name} ({" ".join(binders)} : ℕ) {" ".join(hyps)} :',
        f'    (⟨{src}⟩ : Q) [fm]⊢⁺ ⟨{", ".join(ys)}⟩ := by',
        '  rw [' + ', '.join(subs) + ']',
        f'  exact {core} {var}'])


def _or_term(s, n, inner='rfl'):
    """The `s`-th injection into a right-nested `n`-fold disjunction."""
    if n == 1:
        return inner
    t = inner if s == n - 1 else f'Or.inl {inner}'
    for _ in range(s):
        t = f'Or.inr ({t})'
    return t


def _plan_all(F, W, maxneed, cert, T):
    """Plan every residue branch of the certificate.

    `T` is either one shift for all branches or one shift per branch."""
    if isinstance(T, int):
        T = [T] * len(cert['branches'])
    out = []
    for b, T in zip(cert['branches'], T):
        start = [_shift(p, T) for p in b['start']]
        end = [_shift(p, T) for p in b['target']]
        ops, e = _plan(F, W, maxneed, b['start'], b['events'], T)
        if [_pnorm(p) for p in e] != [_pnorm(p) for p in end]:
            raise _Fail
        if not _verify_plan(F, W, ops, start, end):
            raise _Fail
        out.append((start, end, ops))
    return out


# ============================================================================
# per-flavour proof assembly
# ============================================================================

def _build_add(F, W, maxneed, cert, setup):
    """u -> u+1 additive family, anchored at the concrete member u = j.

    Writing j = M*T + r0, the canonical member is C(m) = f(M*m + j) and one
    period walks the residues r0, r0+1, …, M-1, 0, …, r0-1; the residues that
    wrap around are one period further along, so they are planned at shift T+1."""
    M, (r0, shifts, anchor) = cert['M'], setup
    plans = _plan_all(F, W, maxneed, cert, shifts)
    order = [(r0 + i) % M for i in range(M)]
    for a, b in zip(order, order[1:]):
        if plans[a][1] != plans[b][0]:
            raise _Fail
    em = _Emitter(F, W, maxneed)
    parts = [em.branch(f'trans{r}', plans[r][2], plans[r][0], plans[r][1],
                       doc=f'Residue {r} (mod {M}): f(u) ⊢⁺ f(u+1).') + '\n'
             for r in range(M)]

    S0, E = plans[order[0]][0], plans[order[-1]][1]
    if [_shift(p, 1) for p in S0] != E:
        raise _Fail
    ys = [f'y{i}' for i in range(W)]
    body = f'trans{order[0]} m'
    for r in order[1:]:
        body = f'stepPlus_trans ({body}) (trans{r} m)'
    parts.append('\n'.join([
        f'/-- One period of the family: f(u) ⊢⁺ f(u+{M}). -/',
        f'theorem main_trans (m {" ".join(ys)} : ℕ) '
        + ' '.join(f'(hy{i} : y{i} = {_lean_poly(E[i])})' for i in range(W)) + ' :',
        f'    (⟨{_lean_state(S0)}⟩ : Q) [fm]⊢⁺ ⟨{", ".join(ys)}⟩ := by',
        '  rw [' + ', '.join(f'hy{i}' for i in range(W)) + ']',
        f'  exact {body}', '']))

    st = ', '.join(str(v) for v in anchor[2])
    lines = [
        'theorem nonhalt : ¬halts fm c₀ := by',
        f'  have key : ¬halts fm (⟨{st}⟩ : Q) := by',
        '    apply progress_nonhalt_simple (fm := fm) (A := ℕ) '
        f'(fun m ↦ (⟨{_lean_state(S0)}⟩ : Q)) 0',
        '    intro m',
        f'    refine ⟨m+1, main_trans m {" ".join(["_"] * W)} '
        f'{" ".join(["?_"] * W)}⟩',
        '    all_goals ring']
    bthms, blines = _boot(F, W, anchor[1], st)
    parts += bthms
    parts.append('\n'.join(lines + blines))
    return em, parts


def _build_mul(F, W, maxneed, cert, T, anchor):
    B, Mp = cert['B'], cert['M']
    plans = _plan_all(F, W, maxneed, cert, T)
    em = _Emitter(F, W, maxneed)
    parts, wit = [], []
    for s in range(Mp):
        start, end, ops = plans[s]
        j = cert['branches'][s]['j']
        parts.append(em.branch(f'trans{s}_core', ops, start, end,
                               doc=f'Residue {s} (mod {Mp}): f(X) ⊢⁺ f({B}^{j}·X).')
                     + '\n')
        parts.append(_wrap(f'trans{s}', f'trans{s}_core', start, end, W) + '\n')
        Bj, g = B ** j, (B ** j - 1) // (B - 1)
        cst = Bj * (Mp * T + s) + g
        s2, kk = cst % Mp, (cst - cst % Mp) // Mp - T
        if kk < 0:
            raise _Fail
        if [_poly_compose(p, [kk, Bj]) for p in plans[s2][0]] != end:
            raise _Fail
        wit.append((s2, f'{Bj}*m + {kk}' if kk else f'{Bj}*m'))

    fam = ' ∨ '.join(f'q = (⟨{_lean_state(plans[s][0])}⟩ : Q)' for s in range(Mp))
    st = ', '.join(str(v) for v in anchor[2])
    lines = ['theorem nonhalt : ¬halts fm c₀ := by',
             f'  have key : ¬halts fm (⟨{st}⟩ : Q) := by',
             '    apply progress_nonhalt (fm := fm) '
             f'(P := fun q ↦ ∃ m : ℕ, {fam})',
             '    · rintro c ⟨m, ' + ' | '.join(['rfl'] * Mp) + '⟩']
    for s in range(Mp):
        s2, w = wit[s]
        lines.append(f'      · refine ⟨_, ⟨{w}, {_or_term(s2, Mp)}⟩, ?_⟩')
        lines.append(f'        exact trans{s} m {" ".join(["_"] * W)} '
                     + ' '.join(['(by ring)'] * W))
    lines.append(f'    · exact ⟨{anchor[3]}, {_or_term(anchor[4], Mp)}⟩')
    bthms, blines = _boot(F, W, anchor[1], st)
    parts += bthms
    parts.append('\n'.join(lines + blines))
    return em, parts


def _build_tmpl(F, W, maxneed, cert, T, anchor):
    M, pc = cert['M'], cert['pc']
    base = M * T
    plans = _plan_all(F, W, maxneed, cert, T)
    em = _Emitter(F, W, maxneed)
    parts, wit = [], []
    for r in range(M):
        start, end, ops = plans[r]
        for i in range(W):
            if i != pc and (start[i] != end[i] or not _is_const(start[i])):
                raise _Fail
        w = _psub(end[pc], [base])
        if not _nonneg(w) or _c0(w) < 1:
            raise _Fail
        wit.append(w)
        parts.append(em.branch(f'trans{r}_core', ops, start, end,
                               doc=f'Residue {r} (mod {M}): the template reaches '
                                   'a strictly larger member.') + '\n')
        parts.append(_wrap(f'trans{r}', f'trans{r}_core', start, end, W,
                           wrap_src=True) + '\n')

    tmpl = ', '.join(('n + ' + str(base) if base else 'n') if i == pc
                     else _lean_poly(plans[0][0][i]) for i in range(W))
    st = ', '.join(str(v) for v in anchor[2])
    lines = ['theorem nonhalt : ¬halts fm c₀ := by',
             f'  have key : ¬halts fm (⟨{st}⟩ : Q) := by',
             '    apply progress_nonhalt (fm := fm) '
             f'(P := fun q ↦ ∃ n : ℕ, q = (⟨{tmpl}⟩ : Q))',
             '    · rintro c ⟨n, rfl⟩']
    ind = '      '
    if M > 1:
        lines.append(f'{ind}obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < {M} ∧ n = {M}*m + r :='
                     f' ⟨n / {M}, n % {M}, by omega, by omega⟩')
        lines.append(f'{ind}have hr2 : ' + ' ∨ '.join(f'r = {r}' for r in range(M))
                     + ' := by omega')
        lines.append(f'{ind}rcases hr2 with ' + ' | '.join(['rfl'] * M))
    for r in range(M):
        var = 'm' if M > 1 else 'n'
        pre, cont = (f'{ind}· ', ind + '  ') if M > 1 else (ind, ind)
        lines.append(f'{pre}refine ⟨_, ⟨{_lean_poly(wit[r], var)}, rfl⟩, ?_⟩')
        lines.append(f'{cont}exact trans{r} {var} '
                     + ' '.join(['_'] * (2 * W)) + ' '
                     + ' '.join(['(by ring)'] * (2 * W)))
    lines.append(f'    · exact ⟨{anchor[0] - base}, rfl⟩')
    bthms, blines = _boot(F, W, anchor[1], st)
    parts += bthms
    parts.append('\n'.join(lines + blines))
    return em, parts


# ============================================================================
# top level
# ============================================================================

def oned_progress_to_lean(F: list[list[int]], cert: dict, name: str = 'Foo',
                          max_boot: int | None = None) -> str:
    """Translate a `oned_progress` certificate for `F` into a Lean 4 file.

    `name` is used both as the module name and as the namespace, so the result
    belongs in `<name>.lean`.  `max_boot`, if given, rejects bootstraps longer
    than that many steps.  Raises `TranslationError` on failure."""
    if cert is None:
        raise TranslationError('no certificate')
    _check_ident(name)
    W = cert['width']
    if not 1 <= W <= 26:
        raise TranslationError('unsupported register count')
    maxneed = [max([0] + [-r[i] for r in F]) for i in range(W)]
    flavour = cert['flavour']

    for setup in _setups(cert, max_boot):
        try:
            if flavour == 'add':
                em, parts = _build_add(F, W, maxneed, cert, setup)
            elif flavour == 'mul':
                em, parts = _build_mul(F, W, maxneed, cert, *setup)
            else:
                em, parts = _build_tmpl(F, W, maxneed, cert, *setup)
        except _Fail:
            continue
        return _assemble(F, W, name, cert, setup, em, parts)
    raise TranslationError('no usable shift / bootstrap found')


def oned_progress_to_lean_dir(pairs: list[tuple[list[list[int]], dict]],
                              out_dir: str, stem: str | None = None,
                              **kwargs) -> list[str]:
    """Write a whole batch of certificates as one self-contained BBfLean library.

    `pairs` is a list of `(F, cert)`.  The basename of `out_dir` is used as the
    Lean module component, so `out_dir='other/lean/Size23Oned'` produces

        Size23Oned/Size23Oned_1.lean   -- `namespace Size23Oned_1`
        ...
        Size23Oned/Summary.lean        -- imports them all and restates each
                                          `nonhalt` against a spelled-out `fm`

    and moving `Size23Oned` into `proofs/BBfLean/` makes every file compile,
    the summary included.  Returns the paths written, summary last.

    Raises `TranslationError` if `out_dir` is a non-empty directory, or if any
    certificate fails to translate -- pre-filter `pairs` to tolerate those."""
    directory = _check_ident(os.path.basename(os.path.normpath(out_dir)))
    stem = _check_ident(stem or directory)
    if os.path.isdir(out_dir) and os.listdir(out_dir):
        raise TranslationError(f'{out_dir} already exists and is not empty')

    written, imports, theorems = [], [], []
    for i, (F, cert) in enumerate(pairs, 1):
        name = f'{stem}_{i}'
        try:
            text = oned_progress_to_lean(F, cert, name, **kwargs)
        except TranslationError as e:
            for done in written:            # leave no half-written library
                os.unlink(done)
            if os.path.isdir(out_dir) and not os.listdir(out_dir):
                os.rmdir(out_dir)
            raise TranslationError(f'{name} ({unparse_line(F, 0)}): {e}') from e
        os.makedirs(out_dir, exist_ok=True)
        path = os.path.join(out_dir, f'{name}.lean')
        with open(path, 'w', encoding='utf-8') as f:
            f.write(text)
        written.append(path)
        imports.append(f'import BBfLean.{directory}.{name}')
        W = cert['width']
        theorems.append(
            f'theorem nonhalt{i} : ¬halts (Q := {" × ".join(["ℕ"] * W)}) '
            '(fun q ↦ match q with\n  | ' + '\n  | '.join(_fm_lines(F))
            + '\n  | _ => none) '
            f'⟨{", ".join("1" if k == 0 else "0" for k in range(W))}⟩ '
            f':= {name}.nonhalt\n')

    os.makedirs(out_dir, exist_ok=True)
    summary = '\n'.join(['import BBfLean.FM'] + imports + [
        '',
        '/-!',
        f'# {directory} summary',
        '',
        f'Summary of all proofs in `{directory}`.',
        'This file provides extra confidence that the FMs are properly stated.',
        '',
        f'The {len(pairs)} proofs here were generated by',
        '`decider/oned_progress_to_lean.py` from 1-D progress certificates.',
        '-/',
        '',
    ] + theorems)
    path = os.path.join(out_dir, 'Summary.lean')
    with open(path, 'w', encoding='utf-8') as f:
        f.write(summary)
    return written + [path]


def _setups(cert, max_boot, tries=40):
    """Candidate (shift, concrete anchor) pairs, cheapest bootstrap first."""
    mlo = [b['m_lo'] for b in cert['branches']]

    def too_long(steps):
        return max_boot is not None and steps > max_boot
    if cert['flavour'] == 'add':
        M = cert['M']
        for u, steps, state in cert['anchors']:
            T, r0 = divmod(u, M)
            shifts = [T if r >= r0 else T + 1 for r in range(M)]
            if too_long(steps) or any(s < lo for s, lo in zip(shifts, mlo)):
                continue
            yield (r0, shifts, (u, steps, state))
            tries -= 1
            if not tries:
                return
        return
    for T in range(max(mlo), max(mlo) + tries):
        if cert['flavour'] == 'mul':
            B, Mp = cert['B'], cert['M']
            for X, steps, state in cert['anchors']:
                n = (X - 1) // (B - 1)
                if n // Mp >= T:
                    if not too_long(steps):
                        yield T, (X, steps, state, n // Mp - T, n % Mp)
                    break
        else:
            M = cert['M']
            for n, steps, state in cert['anchors']:
                if n >= M * T:
                    if not too_long(steps):
                        yield T, (n, steps, state)
                    break


def _assemble(F, W, name, cert, setup, em, parts):
    T = setup[1] if cert['flavour'] == 'add' else [setup[0]]
    T = T[0] if len(set(T)) == 1 else ', '.join(map(str, T))
    ns = name
    head = ['import BBfLean.FM',
            'import Mathlib.Tactic.Ring',
            '',
            '/-!',
            f'# {ns}: {unparse_line(F, 0)}',
            '',
            'Vector representation:',
            '```',
            unparse_line(F, 1),
            '```',
            '',
            "This Fractran program doesn't halt.",
            '',
            'This file was generated by `decider/oned_progress_to_lean.py` from the',
            f'1-D progress certificate `{cert_str(cert)}`',
            f'with the change of variable `m := m + {T}` (per residue branch).',
            '-/',
            '',
            f'namespace {ns}',
            '',
            f'def Q := {" × ".join("ℕ" for _ in range(W))}',
            f'def c₀ : Q := ⟨{", ".join("1" if i == 0 else "0" for i in range(W))}⟩',
            'def fm : Q → Option Q := fun q ↦ match q with',
            '  | ' + ('\n  | '.join(_fm_lines(F))),
            '  | _ => none',
            '']
    body = _wrap_text('\n'.join(em.order + parts))
    return '\n'.join(head + [body] + ['', f'end {ns}', ''])


if __name__ == '__main__':
    # python -m decider.oned_progress_to_lean "[1/18, 175/2, 2/55, 3/5, 11/21, 2/3]" Foo
    import sys
    from decider.utils import parse_line

    fm_line = sys.argv[1] if len(sys.argv) > 1 else \
        '[1/18, 175/2, 2/55, 3/5, 11/21, 2/3]'
    module = sys.argv[2] if len(sys.argv) > 2 else 'Foo'
    machine = parse_line(fm_line)
    certificate = oned_progress_cert(machine)
    if certificate is None:
        sys.exit(f'oned_progress found no certificate for {fm_line}')
    print(oned_progress_to_lean(machine, certificate, module), end='')
