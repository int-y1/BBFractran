# python -m decider.nd_progress_to_lean
import copy
import itertools
from fractions import Fraction
from math import ceil, floor, gcd

from decider.nd_progress import (_compose as _subst, _simplify_region, cert_str,
                                 implies_ge0, nd_progress_cert)
from decider.ndr_progress import cert_str as ndr_cert_str
from decider.oned_progress_to_lean import (TranslationError, _CHUNK, _SEG, _Fail, _boot,
                                           _check_ident, _compose as _chain,
                                           _concrete_step, _fm_lines, _paren, _wrap_text)
from decider.utils import unparse_line

"""
Translate an `nd_progress` certificate into a self-contained Lean 4 proof.

The entry point is

    nd_progress_to_lean(F, cert, name) -> str

which returns the contents of a Lean file proving `¬halts fm c₀` for the
Fractran machine `F`.  Dropping that string into `proofs/BBfLean/Size23/Foo.lean`
(with `name='Foo'`) gives a file that compiles against `BBfLean.FM` and uses only
the three usual axioms (`propext`, `Classical.choice`, `Quot.sound`).  The
certificate must come from `nd_progress_cert` (it needs the proof trees).

--------------------------------------------------------------------------------
WHAT HAS TO BE TRANSLATED

`nd_progress` proves non-halting with a family C(x) of states (x = N params in
fixed registers, every other register 0 -- or a constant given by the optional
certificate field 'consts') and a polyhedron P such that every
C(x), x ∈ P, reaches some C(x'), x' ∈ P, in ≥ 1 steps.  In Lean that is
`progress_nonhalt` with

    abbrev Inv (x…) : Prop := <the inequalities of P>
    abbrev Pr (q : Q) : Prop := ∃ x…, q = C(x…) ∧ Inv x…

The proof of the macro-step is the engine's, recorded per residue class
x_k = M_k·m_k + r_k as a tree: inner nodes split the region on the sign of an
affine form g(m) ({g ≥ 0} / {g ≤ -1}, exhaustive over the integers), and each
leaf carries the symbolic transcript of the run on its sub-region:

    ('step', j)              -- rule j fires once
    ('accel', cyc, Dc, V)    -- the rule block `cyc` (net delta Dc) runs V times
    ('loop', cyc)            -- the rule block `cyc` has net delta 0

so the file is assembled as

  * `def Q`, `def c₀`, `def fm`  -- same encoding as `other/gen_lean.py`
  * `cycN_core` / `cycN`         -- one induction lemma per accelerated block,
                                    as in `oned_progress_to_lean.py`
  * `slN`                        -- one-step lemmas for states where `step fm`
                                    cannot reduce the match (see below)
  * `run_rR_L`                   -- the run of leaf L of residue class R
                                    (`_segK` pieces if it is long)
  * `leaf_rR_L`                  -- that run, glued to `Pr`
  * `res_rR`                     -- the case analysis of residue class R
  * `progress`                   -- the residue split
  * `bootK`, `nonhalt`           -- the bootstrap and `progress_nonhalt`

A leaf whose run ends in a net-zero cycle S ⊢⁺ S (never seen in practice, but
the engine accepts it) is glued to `Pr` through a disjunct `¬halts fm q`.

Certificates of `ndr_progress` may also carry a residue restriction: 'allowed', a
set of residue vectors mod 'rmod' (each rmod_k divides moduli_k).  Then `Inv` also
requires (x_0 mod rmod_0, ...) ∈ allowed, written as a disjunction of `x % M = r`
conjunctions; only the residue classes whose reduction is allowed have trees, the
others are closed in `progress` by `exfalso; omega`, and every leaf's end state
must have a uniform, allowed residue (checked while planning).  `omega` is never
asked about the disjunction itself, since it case-splits on it (with 40 allowed
pairs mod 7×7, a single leaf exceeded the default heartbeats): each leaf drops it
from its hypothesis `_h`; a leaf's end state is shown to satisfy `Inv` by
`inv_mk`, with its polyhedral part proved by one `omega` and the matching
disjunct selected explicitly (one `omega` per conjunct was seen to hit
`maxRecDepth`); the bootstrap's `Inv`, over numerals, is proved conjunct by
conjunct; and `progress` is split into one theorem `progress_r<r>` per residue of
the first parameter with a modulus.  A certificate without 'allowed' (or with
None) is translated exactly as before.

--------------------------------------------------------------------------------
ℕ COORDINATES

Every register is an affine form in the m-variables, but with coefficients of
either sign (`2m₀ − m₁ + 3` is fine when the region forces it ≥ 0).  Inside a
leaf, the variables are first shifted to their lower bounds (m = n + lo, the
N-D counterpart of the 1-D shift `m := m + T`), and then each register is written
as an ℕ-term that is *exact* on the leaf's region:

    L(n) + c                  if L has no negative coefficient, or
    P(n) − N(n) + c'          with P(n) − N(n) ≥ 0 everywhere on the region,

the trailing numeral (c resp. c') being what `step fm` peels.  The truncated
subtraction never truncates, so the region's inequalities are passed to every run
lemma as hypotheses and `omega` glues the blocks together (`ring` where no
subtraction is involved).  Within a run of primitive steps a register keeps its
form and only the numeral changes, so consecutive states are definitionally
equal to what `step fm` produces.

`step fm` reduces the `match` only when Lean's decision tree never has to split a
register that is a bare variable.  Condition (C) of `oned_progress_to_lean.py`
(every register a numeral, or with a trailing numeral ≥ the largest pattern
offset of its column) guarantees that, and is aimed for when choosing c'.  When it
fails -- or when a higher-priority rule is blocked by a register that is bounded
on the region but not a numeral -- the step is taken with a lemma `slN`, proved by
case analysis on the offending registers (`rcases x with _ | _ | x`, then `rfl`),
with the bounds as hypotheses discharged by `omega`.

`_Region` reasons over the rationals, so a fact that holds on every integer point
of a thin leaf region but not on its rational relaxation (n0 <= 0 on
{-5*n0 + 8*n1 + 1 >= 0, n1 <= 0}, whose vertex is (1/5, 0)) is invisible to the
planner.  When a leaf fails to plan, it is planned once more on its region
tightened by integer cuts (d.n <= floor(max d.n) for the unit vectors and facet
normals d, and the same from below); they become hypotheses of the run, proved by
`omega`.  Leaves that plan without the cuts are translated exactly as before.

Two opt-in options work around limits of `omega`.  They are off by default, so
existing translations do not change, except for the machines listed in
`_MACHINE_OPTIONS`, which get them automatically (3 machines of sz24 need one):
  * `enumerate_empty`: a case-analysis branch whose region has rational but no
    integer points is closed by enumerating bounded parameters, not by a bare
    `omega`, which lacks the dark/grey shadows and can fail there.
  * `lattice_hints`: on a leaf whose region is a line (its integer points
    c + u*v), a lemma `lat_…` proves the parametrization once, substituting the
    equalities with a unit coefficient first, and the leaf and its run then work
    with the unit equalities n_k = c_k + v_k*u.  Without it every `omega` of such a
    leaf re-solves the region's non-unit equalities (seconds each).

Every plan is replayed against a concrete simulation at integer points of each
leaf before anything is printed.
"""


class _Planning(Exception):
    """A leaf could not be planned (a bug, or an unexpected certificate)."""


class _Refine(Exception):
    """A leaf has to be split further: the form (over the leaf's n) is bounded on
    the leaf, and each of its values gives a leaf that can be planned."""

    def __init__(self, form):
        super().__init__('refine')
        self.form = form


_VAR = 'n'          # leaf (shifted) variables n0, n1, n2
_RVAR = 'm'         # residue variables m0, m1, m2


# ============================================================================
# affine forms over the N params: f = [c_0, ..., c_{N-1}, const]
# ============================================================================

def _fadd(a, b):
    return [x + y for x, y in zip(a, b)]


def _fsub(a, b):
    return [x - y for x, y in zip(a, b)]


def _fscale(a, c):
    return [x * c for x in a]


def _fconst(c, N):
    return [0] * N + [c]


def _is_const(f):
    return all(x == 0 for x in f[:-1])


def _feval(f, pt):
    return sum(f[k] * pt[k] for k in range(len(pt))) + f[-1]


def _round(f):
    """Chvátal-Gomory rounding of a constraint f >= 0: same lattice points."""
    g = 0
    for x in f[:-1]:
        g = gcd(g, x)
    if g <= 1:
        return list(f)
    return [x // g for x in f[:-1]] + [f[-1] // g]


def _shift(f, lo):
    """f(n + lo)."""
    return list(f[:-1]) + [f[-1] + sum(f[k] * lo[k] for k in range(len(lo)))]


# ============================================================================
# a leaf's region {n >= 0, c(n) >= 0 for c in cons}  (exact rational arithmetic)
# ============================================================================

def _solve(rows, rhs):
    n = len(rows)
    A = [[Fraction(x) for x in r] + [Fraction(b)] for r, b in zip(rows, rhs)]
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [A[r][k] - f * A[c][k] for k in range(n + 1)]
    return [A[i][n] for i in range(n)]


class _Region:
    """A pointed polyhedron; every form we ask about is bounded below on it."""

    def __init__(self, N, cons):
        self.N = N
        self.cons = [list(c) for c in cons]
        units = [[1 if j == k else 0 for j in range(N)] + [0] for k in range(N)]
        self.all = self.cons + units
        self.phi = [(c, False) for c in self.all]
        verts = set()
        for sub in itertools.combinations(self.all, N):
            x = _solve([c[:N] for c in sub], [-c[N] for c in sub])
            if x is not None and all(_feval(c, x) >= 0 for c in self.all):
                verts.add(tuple(x))
        self.verts = sorted(verts)

    def empty(self):
        return not self.verts

    def ge0(self, f):
        return implies_ge0(self.phi, self.N, f)

    def floor_min(self, f):
        """The largest integer c with f >= c on the region."""
        c = floor(min(_feval(f, v) for v in self.verts))
        if not self.ge0(_fsub(f, _fconst(c, self.N))):
            raise _Planning('form not bounded below on the region')
        return c

    def ceil_max(self, f):
        """The smallest integer c with f <= c on the region, or None if f is
        unbounded above."""
        c = floor(max(_feval(f, v) for v in self.verts))
        return c if self.ge0(_fsub(_fconst(c, self.N), f)) else None

    def const_value(self, f):
        """The value of f if it is constant on the region, else None."""
        if _is_const(f):
            return f[-1]
        v = _feval(f, self.verts[0])
        if v.denominator != 1:
            return None
        c = _fconst(int(v), self.N)
        if self.ge0(_fsub(f, c)) and self.ge0(_fsub(c, f)):
            return int(v)
        return None

    def points(self, want=3, extra=2, box=None):
        """A few integer points of the region: the smallest ones, plus a couple
        of larger ones."""
        N = self.N
        box = box or (40 if N == 2 else 16)
        pts = [pt for pt in itertools.product(range(box + 1), repeat=N)
               if all(_feval(c, pt) >= 0 for c in self.cons)]
        pts.sort(key=lambda pt: (sum(pt), pt))
        out = pts[:want]
        rest = pts[want:]
        for t in range(1, extra + 1):
            if rest:
                out.append(rest[(len(rest) * t) // (extra + 1)])
        return out


# ============================================================================
# Lean rendering of terms and constraints
# ============================================================================

def _lin(coefs, names):
    return ' + '.join(nm if c == 1 else f'{c}*{nm}'
                      for c, nm in zip(coefs, names) if c)


def _nat(coefs, const, names):
    """An ℕ-term for a form with non-negative coefficients, numeral last."""
    s = _lin(coefs, names)
    if not s:
        return str(const)
    return f'{s} + {const}' if const else s


def _sides(f, names):
    """(lhs, rhs) with f >= 0  <=>  lhs <= rhs, both ℕ-terms."""
    pos = _nat([max(x, 0) for x in f[:-1]], max(f[-1], 0), names)
    neg = _nat([max(-x, 0) for x in f[:-1]], max(-f[-1], 0), names)
    return neg, pos


def _ineq(f, names):
    lhs, rhs = _sides(f, names)
    return f'{lhs} ≤ {rhs}'


def _trivial(f):
    return all(x >= 0 for x in f)


class _Rep:
    """How one register is written along a run of primitive steps.

    `kind` is 'num' (a numeral), 'nat' (a non-negative-coefficient form, written
    as such) or 'sub' (`core + c`, core a non-truncating ℕ-subtraction term).
    `base` is the register's form at the start of the run; renderings at later
    positions take the form there, which differs from `base` by a constant."""

    def __init__(self, kind, base, names, value=None, core=None, c0=None, P=None, Nn=None):
        self.kind, self.base, self.names = kind, base, names
        self.value, self.core, self.c0 = value, core, c0
        self.P, self.Nn = P, Nn

    def delta(self, f):
        d = _fsub(f, self.base)
        assert _is_const(d), (f, self.base)
        return d[-1]

    def render(self, f):
        d = self.delta(f)
        if self.kind == 'num':
            assert self.value + d >= 0
            return str(self.value + d)
        if self.kind == 'nat':
            assert f[-1] >= 0
            return _nat(f[:-1], f[-1], self.names)
        c = self.c0 + d
        assert c >= 0
        return f'{self.core} + {c}' if c else self.core

    def trailing(self, f):
        """The numeral `step fm` can peel (None for a numeral register)."""
        if self.kind == 'num':
            return None
        if self.kind == 'nat':
            return f[-1]
        return self.c0 + self.delta(f)

    def poly(self, f):
        """The form the rendered term denotes as a polynomial, or None if it uses
        truncated subtraction (then it only agrees with `f` on the region)."""
        if self.kind == 'num':
            return _fconst(self.value + self.delta(f), len(f) - 1)
        return list(f) if self.kind == 'nat' else None

    def number(self, f):
        return self.value + self.delta(f) if self.kind == 'num' else None

    def evaluate(self, f, pt):
        """The value of the rendered ℕ-term at `pt` (with truncated subtraction)."""
        if self.kind == 'num':
            return self.value + self.delta(f)
        if self.kind == 'nat':
            return _feval(f, pt)
        core = max(_feval(self.P, pt) - _feval(self.Nn, pt), 0)
        return core + self.c0 + self.delta(f)


def _choose_rep(R, f0, deltas, needs, want, names):
    """A rendering of a register whose form is `f0 + deltas[t]` at position t of a
    run, that is exact on the region, keeps a trailing numeral of at least
    `needs[t]` (the guard of the rule fired there) and preferably `want[t]`."""
    v = R.const_value(f0)
    if v is not None:
        return _Rep('num', f0, names, value=v)
    req = max(max(-d for d in deltas), max(n - d for n, d in zip(needs, deltas)))
    if all(x >= 0 for x in f0[:-1]) and f0[-1] >= req:
        return _Rep('nat', f0, names)
    fm = R.floor_min(f0)
    if fm < req:
        raise _Planning('register below its guard on the region')
    c0 = max(req, min(fm, max(w - d for w, d in zip(want, deltas))))
    core = _fsub(f0, _fconst(c0, R.N))
    P = [max(x, 0) for x in core[:-1]] + [max(core[-1], 0)]
    Nn = [max(-x, 0) for x in core[:-1]] + [max(-core[-1], 0)]
    ps = _nat(P[:-1], P[-1], names)
    ns = _nat(Nn[:-1], Nn[-1], names)
    assert ns != '0'                # else f0 = P + c0 has no negative part: 'nat'
    return _Rep('sub', f0, names, core=f'{ps} - {_paren(ns)}', c0=c0, P=P, Nn=Nn)


def _eq_proof(a, b, pa, pb):
    """A proof of `a = b` for rendered terms denoting the polynomials pa, pb
    (None: uses truncated subtraction).  `ring` only for polynomial identities;
    everything else holds on the region and is left to `omega`."""
    if a == b:
        return 'rfl'
    if pa is not None and pa == pb:
        return '(by ring)'
    return '(by omega)'


# ============================================================================
# replaying and planning one leaf
# ============================================================================

def _prefix(F, cyc, W):
    pre = [[0] * W]
    for j in cyc:
        pre.append([pre[-1][i] + F[j][i] for i in range(W)])
    return pre


class _Step:
    __slots__ = ('rule', 'src')

    def __init__(self, rule, src):
        self.rule, self.src = rule, src


class _Cycle:
    __slots__ = ('cyc', 'Dc', 'k', 'src', 'dst', 'lits', 'offs', 'xs', 'src_rend', 'dst_rend',
                 'src_poly', 'dst_poly')

    def __init__(self, cyc, Dc, k, src, dst):
        self.cyc, self.Dc, self.k, self.src, self.dst = cyc, Dc, k, src, dst


def _replay(F, W, N, R, start, events):
    """Turn a transcript into primitive steps and cycles (over the leaf's n),
    checking every decision against the region.  Returns (ops, end, loop) where
    `loop` is the rule block of a final net-zero cycle, or None."""
    cur = [list(f) for f in start]
    ops = []

    def step(j):
        nonlocal cur
        for i in range(W):
            if F[j][i] < 0 and not R.ge0(_fadd(cur[i], _fconst(F[j][i], N))):
                raise _Planning(f'rule {j} not applicable')
        for rp in range(j):
            if not any(F[rp][i] < 0 and R.ge0(_fsub(_fconst(-F[rp][i] - 1, N), cur[i]))
                       for i in range(W)):
                raise _Planning(f'rule {rp} not blocked')
        ops.append(_Step(j, cur))
        cur = [_fadd(cur[i], _fconst(F[j][i], N)) for i in range(W)]

    loop = None
    for ev in events:
        if ev[0] == 'step':
            step(ev[1])
        elif ev[0] == 'accel':
            _, cyc, Dc, V = ev
            ops.append(_Cycle(list(cyc), list(Dc), list(V), cur, None))
            cur = [_fadd(cur[i], _fscale(V, Dc[i])) for i in range(W)]
        else:
            loop = list(ev[1])
            for j in loop:
                step(j)
            if any(_fsub(a, b) != _fconst(0, N) for a, b in zip(cur, ops[-len(loop)].src)):
                raise _Planning('loop is not net-zero')
    return ops, cur, loop


def _peel(F, W, N, op, c):
    """`c` iterations of the cycle `op` as primitive steps, and the rest of it
    (None if nothing is left)."""
    out, cur = [], op.src
    for _ in range(c):
        for j in op.cyc:
            out.append(_Step(j, cur))
            cur = [_fadd(cur[i], _fconst(F[j][i], N)) for i in range(W)]
    k = _fsub(op.k, _fconst(c, N))
    return out, (None if k == _fconst(0, N) else _Cycle(op.cyc, op.Dc, k, cur, None))


def _expand(F, W, N, ops, c1):
    """Peel `c1` cycles off the front of the first cycle (as primitive steps)."""
    out = []
    for op in ops:
        if isinstance(op, _Step) or c1 == 0:
            out.append(op)
            continue
        steps, rest = _peel(F, W, N, op, c1)
        out += steps + ([rest] if rest else [])
        c1 = 0
    return out


def _plan_cycle(F, W, N, R, maxneed, op):
    """Choose the literals / offsets of the cycle lemma for `op` (the 1-D
    `_try_cycle`, with the slack read off the region)."""
    cyc, Dc, L = op.cyc, op.Dc, len(op.cyc)
    pre = _prefix(F, cyc, W)
    if not R.ge0(op.k):
        raise _Planning('cycle count negative')
    lits, offs, xs = {}, {}, {}
    for i in range(W):
        S1 = op.src[i]
        if Dc[i] == 0:
            v = R.const_value(S1)
            if v is not None:
                lits[i] = v
                continue
        if Dc[i] < 0:
            d = -Dc[i]
            lo = max(0, -min(d + pre[t][i] for t in range(L + 1)))
            want = max(maxneed[i] - (d + pre[t][i]) for t in range(L))
            x0 = _fadd(S1, _fscale(op.k, Dc[i]))
        else:
            lo = max(0, -min(pre[t][i] for t in range(L + 1)))
            want = max(maxneed[i] - pre[t][i] for t in range(L))
            x0 = S1
        hi = R.floor_min(x0)
        if hi < lo:
            raise _Planning('no room for the cycle offset')
        off = max(lo, min(want, hi))
        offs[i], xs[i] = off, _fsub(x0, _fconst(off, N))
    for t in range(L):
        rj = cyc[t]
        for i in lits:
            if lits[i] + pre[t + 1][i] < 0:
                raise _Planning('literal goes negative in the cycle')
        for rp in range(rj):
            if not any(F[rp][i] < 0 and lits[i] + pre[t][i] + F[rp][i] < 0 for i in lits):
                # blocked by a register that is bounded, but not constant, on the
                # region (or the cycle count is bounded): split on its value
                for i in range(W):
                    if (F[rp][i] < 0 and i not in lits and Dc[i] == 0
                            and R.ceil_max(op.src[i]) is not None):
                        raise _Refine(op.src[i])
                if R.ceil_max(op.k) is not None:
                    raise _Refine(op.k)
                raise _Planning('higher-priority rule not blocked by a literal')
    op.lits, op.offs, op.xs = lits, offs, xs


# ============================================================================
# Lean emission
# ============================================================================

class _Emitter:
    """Collects the shared lemmas (cycle lemmas, step lemmas) and emits proofs."""

    def __init__(self, F, W, maxneed):
        self.F, self.W, self.maxneed = F, W, maxneed
        self.cycles = {}            # signature -> (name, x indices, lhs, rhs)
        self.steps = {}             # signature -> (name, variables, bounded columns)
        self.order = []             # lemma texts, in order of creation

    # -- one-step lemmas -----------------------------------------------------

    def step_lemma(self, j, spec):
        """`fm <state> = some <state'>` for rule j, the state given per column as
        ('n', value) or ('s', trailing numeral, strict upper bound or None)."""
        sig = (j, tuple(spec))
        if sig in self.steps:
            return self.steps[sig]
        name = f'sl{len(self.steps) + 1}'
        F = self.F
        xs, hyps, cases, src, dst = [], [], [], [], []
        for i, s in enumerate(spec):
            if s[0] == 'n':
                src.append(str(s[1]))
                dst.append(str(s[1] + F[j][i]))
                continue
            _, c, ub = s
            x = f'x{i}'
            xs.append(x)
            src.append(f'{x} + {c}' if c else x)
            dst.append(f'{x} + {c + F[j][i]}' if c + F[j][i] else x)
            depth = max(self.maxneed[i] - c, ub - c if ub is not None else 0)
            if ub is not None:
                hyps.append(f'(h{i} : {x} + {c} < {ub})' if c else f'(h{i} : {x} < {ub})')
            if depth > 0:
                cases.append(f'rcases {x} with ' + ' | '.join(['_'] * depth + [x]))
        head = f'theorem {name}'
        if xs:
            head += f' ({" ".join(xs)} : ℕ)'
        if hyps:
            head += ' ' + ' '.join(hyps)
        head += f' :\n    fm ⟨{", ".join(src)}⟩ = some ⟨{", ".join(dst)}⟩ := by'
        body = [head]
        if cases:
            body.append('  ' + cases[0])
            body += ['  all_goals ' + c for c in cases[1:]]
            body.append('  all_goals first | rfl | omega' if hyps else '  all_goals rfl')
        else:
            body.append('  rfl')
        self.order.append('\n'.join(body) + '\n')
        self.steps[sig] = (name, xs, [i for i, s in enumerate(spec)
                                      if s[0] == 's' and s[2] is not None])
        return self.steps[sig]

    def step_line(self, j, spec, plus):
        """A tactic taking one step; `plus` if the goal is `⊢⁺` (else `⊢*`)."""
        if all(s[0] == 'n' or (s[2] is None and s[1] >= self.maxneed[i])
               for i, s in enumerate(spec)):
            return 'step fm'
        name, xs, hyps = self.step_lemma(j, spec)
        args = ' '.join(['_'] * len(xs) + ['(by omega)'] * len(hyps))
        call = f'{name} {args}' if args else name
        return (f'apply step_stepStar_stepPlus ({call})' if plus
                else f'apply sstar ({call})')

    # -- cycle lemma ---------------------------------------------------------

    def cycle_lemma(self, op):
        W, F = self.W, self.F
        Dc, cyc, lits, offs = op.Dc, op.cyc, op.lits, op.offs
        sig = (tuple(cyc), tuple(Dc), tuple(sorted(lits.items())),
               tuple(sorted(offs.items())))
        if sig in self.cycles:
            return self.cycles[sig]
        name = f'cyc{len(self.cycles) + 1}'
        pre = _prefix(F, cyc, W)
        xs = sorted(offs)
        var = {i: f'x{i}' for i in xs}

        def _add(e, c):
            return e if c == 0 else f'{e} + {c}'

        def _mul(c, e):
            return e if c == 1 else f'{c}*{e}'

        def lhs(i, kexpr='k', sub=None):
            if i in lits:
                return str(lits[i])
            v = (sub or var)[i]
            return (_add(f'{v} + ' + _mul(-Dc[i], _paren(kexpr)), offs[i]) if Dc[i] < 0
                    else _add(v, offs[i]))

        def rhs(i, kexpr='k', sub=None):
            if i in lits:
                return str(lits[i])
            v = (sub or var)[i]
            return (_add(f'{v} + ' + _mul(Dc[i], _paren(kexpr)), offs[i]) if Dc[i] > 0
                    else _add(v, offs[i]))

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
               f'{_add(f"{var[i]} + " + _mul(-Dc[i], "k"), offs[i] - Dc[i])} from by ring'
               for i in xs if Dc[i] < 0]
        if rws:
            body.append('    rw [' + ',\n         '.join(rws) + ']')
        for t, j in enumerate(cyc):
            spec = []
            for i in range(W):
                if i in lits:
                    spec.append(('n', lits[i] + pre[t][i]))
                else:
                    base = offs[i] + (-Dc[i] if Dc[i] < 0 else 0)
                    spec.append(('s', base + pre[t][i], None))
            body.append('    ' + self.step_line(j, spec, False))
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
        self.cycles[sig] = (name, xs, lhs, rhs)
        self.order.append('\n'.join(body) + '\n')
        return self.cycles[sig]

    def cycle_call(self, op, src, dst, psrc, pdst, krep, xreps):
        """`cycN …` taking the rendered state `src` to the rendered state `dst`
        (denoting the polynomials `psrc`, `pdst`)."""
        name, xs, lhs, rhs = self.cycle_lemma(op)
        k = krep.render(op.k)
        xt = {i: xreps[i].render(op.xs[i]) for i in xs}
        args = [_paren(k)] + [_paren(xt[i]) for i in xs]
        args += [_paren(s) for s in src] + [_paren(s) for s in dst]
        sub = {i: _paren(xt[i]) for i in xs}
        # the polynomials denoted by both sides of every hypothesis of `cycN`
        pk = krep.poly(op.k)
        N = len(op.k) - 1

        def side(i, before):
            if i in op.lits:
                return _fconst(op.lits[i], N)
            px = xreps[i].poly(op.xs[i])
            if px is None or pk is None:
                return None
            off = _fconst(op.offs[i], N)
            grow = (op.Dc[i] < 0) == before and op.Dc[i] != 0
            return _fadd(_fadd(px, off), _fscale(pk, abs(op.Dc[i]))) if grow else _fadd(px, off)
        args += [_eq_proof(src[i], lhs(i, _paren(k), sub), psrc[i], side(i, True))
                 for i in range(self.W)]
        args += [_eq_proof(dst[i], rhs(i, _paren(k), sub), pdst[i], side(i, False))
                 for i in range(self.W)]
        return f'{name} {" ".join(args)}'


class _Leaf:
    """Plans and emits the proof of one leaf of one residue class."""

    def __init__(self, cx, rkey, idx, mcons, splits, node, tight=False):
        self.cx, self.rkey, self.idx = cx, rkey, idx
        self.splits = splits            # [(g, 'lt' | 'ge', the constraint >= 0)]
        self.node = node
        N = cx.N
        mcons = [_round(c) for c in mcons]
        self.region_m = _Region(N, mcons)
        if self.region_m.empty():
            self.lo = None
            return
        lo = [max(0, -floor(-min(v[k] for v in self.region_m.verts))) for k in range(N)]
        self.lo = lo
        ncons = [_shift(c, lo) for c in mcons]
        ncons = [c for c in ncons if not _trivial(c)]
        if ncons:
            ncons = _simplify_region(ncons + [[1 if j == k else 0 for j in range(N)] + [0]
                                              for k in range(N)], N)
            ncons = [c for c in ncons if not _trivial(c)]
        self.ncons = ncons
        self.R = _Region(N, ncons)
        self.names = [f'{_VAR}{k}' for k in range(N)]
        if self.R.empty():              # no lattice point: m_k >= lo_k cuts it away
            self.lo = None
        elif tight:
            self._tighten()

    def _tighten(self):
        """Add the integer cuts d.n <= floor(max d.n) and d.n >= ceil(min d.n)
        wherever the rational bound is fractional, for d the unit vectors and the
        facet normals of the region.  `R.ge0` reasons over the rationals, so
        without them a fact that holds on every integer point of a thin region
        (e.g. n0 <= 0 on {-5*n0 + 8*n1 + 1 >= 0, n1 <= 0}, whose rational vertex
        is (1/5, 0)) cannot be used.  The cuts lose no integer point; they become
        hypotheses of the leaf's run, discharged by `omega`."""
        N = self.cx.N
        for _ in range(4):
            cons = [list(c) for c in self.R.cons]
            dirs = [[1 if j == k else 0 for j in range(N)] for k in range(N)]
            dirs += [list(c[:N]) for c in self.R.cons if any(c[:N])]
            for d in dirs:
                vals = [sum(a * x for a, x in zip(d, v)) for v in self.R.verts]
                vmax, vmin = max(vals), min(vals)
                if vmax.denominator != 1 and self.R.ge0([-x for x in d] + [ceil(vmax)]):
                    cut = [-x for x in d] + [floor(vmax)]
                    if cut not in cons:
                        cons.append(cut)
                if vmin.denominator != 1 and self.R.ge0(d + [-floor(vmin)]):
                    cut = d + [-ceil(vmin)]
                    if cut not in cons:
                        cons.append(cut)
            if len(cons) == len(self.R.cons):
                return
            cons = _simplify_region(cons + [[1 if j == k else 0 for j in range(N)] + [0]
                                            for k in range(N)], N)
            self.ncons = [c for c in cons if not _trivial(c)]
            self.R = _Region(N, self.ncons)
            if self.R.empty():
                self.lo = None
                return

    @property
    def name(self):
        return f'{self.cx.rname(self.rkey)}_{self.idx}'

    # -- planning ------------------------------------------------------------

    def plan(self):
        cx, N, W, F, R = self.cx, self.cx.N, self.cx.W, self.cx.F, self.R
        start_m = cx.start_state(self.rkey)
        start = [_shift(f, self.lo) for f in start_m]
        events = [(ev[0], ev[1], ev[2], _shift(ev[3], self.lo)) if ev[0] == 'accel' else ev
                  for ev in self.node['events']]
        ops, end, loop = _replay(F, W, N, R, start, events)
        if loop is None:
            want_end = [_shift(f, self.lo) for f in self.node['end']]
            if end != want_end:
                raise _Planning('transcript does not reproduce the end state')
            for i in range(W):
                if i not in cx.param_regs and R.const_value(end[i]) != cx.const(i):
                    raise _Planning('end state not in the family')
            xprime = [end[r] for r in cx.param_regs]
            for q in cx.P:
                if not R.ge0(_subst(q, xprime, N)):
                    raise _Planning('end state outside the invariant')
            if cx.allowed is not None:
                for k in range(N):
                    if any(c % cx.rmod[k] for c in xprime[k][:-1]):
                        raise _Planning('end state residue is not uniform')
                if not cx.admits([f[-1] for f in xprime]):
                    raise _Planning('end state outside the residue restriction')
                self.end_res = [f[-1] for f in xprime]
        if not any(isinstance(op, _Step) for op in ops):
            ops = _expand(F, W, N, ops, 1)
        planned = []
        for op in ops:
            if isinstance(op, _Cycle):
                try:
                    _plan_cycle(F, W, N, R, cx.maxneed, op)
                except _Refine:
                    c = R.const_value(op.k)
                    if c is None:
                        raise
                    planned += _peel(F, W, N, op, c)[0]     # a constant count: unroll
                    continue
            planned.append(op)
        self.ops, self.end, self.loop, self.start = planned, end, loop, start
        self._segments()

    def _segments(self):
        """Group the primitive steps between cycles and choose the renderings.

        `self.segs` alternates (steps, states, reps) and cycles, starting and
        ending with a (possibly empty) run of steps."""
        cx, W, F, R, N = self.cx, self.cx.W, self.cx.F, self.R, self.cx.N
        raw, cur = [], []
        for op in self.ops:
            if isinstance(op, _Step):
                cur.append(op)
            else:
                raw += [cur, op]
                cur = []
        raw.append(cur)
        out, state = [], self.start
        for s in raw:
            if isinstance(s, _Cycle):
                if s.src != state:
                    raise _Planning('cycle does not start where the steps end')
                state = [_fadd(s.src[i], _fscale(s.k, s.Dc[i])) for i in range(W)]
                s.dst = state
                out.append(s)
                continue
            states = [state]
            for op in s:
                if op.src != states[-1]:
                    raise _Planning('steps do not chain')
                states.append([_fadd(op.src[i], _fconst(F[op.rule][i], N)) for i in range(W)])
            reps = []
            for i in range(W):
                f0 = states[0][i]
                deltas = [st[i][-1] - f0[-1] for st in states]
                needs = [max(0, -F[op.rule][i]) for op in s] + [0]
                want = [cx.maxneed[i]] * len(s) + [0]
                reps.append(_choose_rep(R, f0, deltas, needs, want, self.names))
            out.append((s, states, reps))
            state = states[-1]
        if state != self.end:
            raise _Planning('plan does not reach the end state')
        self.segs = out
        for k, s in enumerate(out):
            if isinstance(s, _Cycle):
                s.src_rend = self.render(out[k - 1][2], s.src)
                s.dst_rend = self.render(out[k + 1][2], s.dst)
                s.src_poly = self.poly(out[k - 1][2], s.src)
                s.dst_poly = self.poly(out[k + 1][2], s.dst)

    def render(self, reps, state):
        return [reps[i].render(state[i]) for i in range(self.cx.W)]

    def poly(self, reps, state):
        return [reps[i].poly(state[i]) for i in range(self.cx.W)]

    def krep(self, form):
        return _choose_rep(self.R, form, [0], [0], [0], self.names)

    # -- concrete cross-check --------------------------------------------------

    def verify(self, budget=200000):
        """Replay the plan concretely at integer points of the region, checking
        every block boundary against the rendered ℕ-terms."""
        W, F = self.cx.W, self.cx.F
        pts = self.R.points()
        for pt in pts:
            s = [_feval(f, pt) for f in self.start]
            for seg in self.segs:
                if isinstance(seg, _Cycle):
                    k = _feval(seg.k, pt)
                    budget -= k * len(seg.cyc)
                    if budget < 0:
                        return
                    for _ in range(k):
                        for r in seg.cyc:
                            j, s = _concrete_step(F, s)
                            if j != r:
                                raise _Planning('cycle diverges from the simulation')
                    continue
                steps, states, reps = seg
                for t, st in enumerate(states):
                    vals = [reps[i].evaluate(st[i], pt) for i in range(W)]
                    if vals != s or [_feval(f, pt) for f in st] != s:
                        raise _Planning('rendering diverges from the simulation')
                    if t < len(steps):
                        j, s = _concrete_step(F, s)
                        if j != steps[t].rule:
                            raise _Planning('step diverges from the simulation')
            if [_feval(f, pt) for f in self.end] != s:
                raise _Planning('end state diverges from the simulation')

    # -- emission ------------------------------------------------------------

    def hyps(self):
        return [f'(_h{k} : {_ineq(c, self.names)})' for k, c in enumerate(self.ncons)]

    def lattice(self):
        """(c, v, j, umax, eqs) with the integer points of the region exactly
        c + u*v, 0 <= u <= umax (umax None: unbounded), when the region spans a line
        (N - 1 independent implicit equalities, `eqs`); j is a coordinate with
        v_j != 0 to read u off.  None otherwise.  Used by `lattice_hints` (see
        `_emit_leaf`)."""
        N, R = self.cx.N, self.R
        if N < 2 or self.loop is not None:
            return None
        eqs = [c for c in R.all if R.ge0([-x for x in c])]
        rows = [c[:N] for c in eqs]
        if N == 2:
            ind = [r for r in rows if any(r)][:1]
            if not ind:
                return None
            a = ind[0]
            v = [a[1], -a[0]]
        elif N == 3:
            v = None
            for r1, r2 in itertools.combinations(rows, 2):
                w = [r1[1] * r2[2] - r1[2] * r2[1], r1[2] * r2[0] - r1[0] * r2[2],
                     r1[0] * r2[1] - r1[1] * r2[0]]
                if any(w):
                    v = w
                    break
            if v is None:
                return None
        else:
            return None
        if any(sum(a * b for a, b in zip(r, v)) for r in rows):
            return None                 # rank of the equalities is not N - 1
        g = 0
        for x in v:
            g = gcd(g, abs(x))
        v = [x // g for x in v]
        # an integer point of the line through a vertex q: consecutive ones differ
        # by v, so |v_j| consecutive values of coordinate j suffice
        q = R.verts[0]
        j = min((k for k in range(N) if v[k]), key=lambda k: abs(v[k]))
        p = None
        for m in range(ceil(q[j]), ceil(q[j]) + abs(v[j])):
            sc = Fraction(m - q[j], v[j])
            cand = [q[k] + sc * v[k] for k in range(N)]
            if all(x.denominator == 1 for x in cand):
                p = [int(x) for x in cand]
                break
        if p is None:
            return None
        lo, hi = None, None              # t-range of p + t*v inside the region
        for c in R.all:
            cv = sum(a * b for a, b in zip(c[:N], v))
            cp = sum(a * b for a, b in zip(c[:N], p)) + c[N]
            if cv > 0:
                b = ceil(Fraction(-cp, cv))
                lo = b if lo is None else max(lo, b)
            elif cv < 0:
                b = floor(Fraction(cp, -cv))
                hi = b if hi is None else min(hi, b)
            elif cp < 0:
                return None
        if lo is None and hi is None:
            return None
        if lo is None:                   # orient t towards the bounded end
            v, lo, hi = [-x for x in v], -hi, None
        c0 = [p[k] + lo * v[k] for k in range(N)]
        if any(x < 0 for x in c0) or (hi is not None and hi < lo):
            return None
        j = min((k for k in range(N) if v[k]), key=lambda k: abs(v[k]))
        return c0, v, j, (None if hi is None else hi - lo), eqs

    def blocks(self, em):
        """[src, dst, proof, is_plus] per block; proofs of step blocks are
        functions of `plus`."""
        blocks = []
        for seg in self.segs:
            if isinstance(seg, _Cycle):
                krep = self.krep(seg.k)
                xreps = {i: self.krep(seg.xs[i]) for i in seg.xs}
                blocks.append([seg.src_rend, seg.dst_rend,
                               em.cycle_call(seg, seg.src_rend, seg.dst_rend, seg.src_poly,
                                             seg.dst_poly, krep, xreps),
                               False])
                continue
            steps, states, reps = seg
            for a in range(0, len(steps), _CHUNK):
                b = min(a + _CHUNK, len(steps))
                specs = []
                for t in range(a, b):
                    specs.append((steps[t].rule, self._spec(reps, states[t], steps[t].rule)))

                def proof(plus, specs=specs):
                    lines = [em.step_line(j, sp, plus and n == 0)
                             for n, (j, sp) in enumerate(specs)]
                    return _tactics(lines)
                blocks.append([self.render(reps, states[a]), self.render(reps, states[b]),
                               proof, False])
        return blocks

    def _spec(self, reps, state, j):
        """Per-column description of `state` for the step lemma of rule j."""
        W, F, R, N = self.cx.W, self.cx.F, self.R, self.cx.N
        spec = []
        for i in range(W):
            v = reps[i].number(state[i])
            spec.append(('n', v) if v is not None else ['s', reps[i].trailing(state[i]), None])
        for rp in range(j):
            if any(F[rp][i] < 0 and spec[i][0] == 'n' and spec[i][1] + F[rp][i] < 0
                   for i in range(W)):
                continue
            for i in range(W):
                if (F[rp][i] < 0 and spec[i][0] == 's'
                        and R.ge0(_fsub(_fconst(-F[rp][i] - 1, N), state[i]))):
                    ub = -F[rp][i]
                    spec[i][2] = ub if spec[i][2] is None else min(spec[i][2], ub)
                    break
            else:
                raise _Planning('no blocker for a higher-priority rule')
        return [tuple(s) for s in spec]


def _tactics(lines):
    """Compress runs of `step fm`; finish with `exists 0`."""
    out, i = [], 0
    while i < len(lines):
        j = i
        while j < len(lines) and lines[j] == 'step fm':
            j += 1
        if j - i >= 2:
            out.append(f'iterate {j - i} step fm')
            i = j
        elif j > i:
            out.append('step fm')
            i = j
        else:
            out.append(lines[i])
            i += 1
    return out + ['exists 0']


# ============================================================================
# the whole certificate
# ============================================================================

class _Context:
    def __init__(self, F, cert):
        self.F = F
        self.W = W = len(F[0])
        self.N = N = cert['nvars']
        self.param_regs = list(cert['param_regs'])
        self.moduli = list(cert['moduli'])
        if len(self.param_regs) != N or len(self.moduli) != N or len(set(self.param_regs)) != N:
            raise TranslationError('malformed certificate')
        if not all(0 <= r < W for r in self.param_regs) or not all(M >= 1 for M in self.moduli):
            raise TranslationError('malformed certificate')
        self.maxneed = [max([0] + [-r[i] for r in F]) for i in range(W)]
        P = [list(q) for q in cert['P']]
        if any(len(q) != N + 1 for q in P):
            raise TranslationError('malformed certificate')
        P = [q for q in P if not _trivial(q)]
        if P:
            P = _simplify_region(P + [[1 if j == k else 0 for j in range(N)] + [0]
                                      for k in range(N)], N)
            P = [q for q in P if not _trivial(q)]
        self.P = P
        self.pnames = [chr(ord('a') + r) for r in self.param_regs]
        # registers that are constant but not 0 in the family (absent: all 0)
        self.consts = {int(i): int(v) for i, v in (cert.get('consts') or {}).items()}
        if any(i in self.param_regs or not 0 <= i < W or v < 0
               for i, v in self.consts.items()):
            raise TranslationError('malformed certificate')
        # optional residue restriction (certificates of `ndr_progress`): the invariant
        # also requires (x_k mod rmod_k)_k to be in `allowed` (absent: no restriction)
        self.rmod = self.allowed = None
        if cert.get('allowed') is not None:
            rmod = [int(M) for M in cert['rmod']]
            allowed = {tuple(int(r) for r in a) for a in cert['allowed']}
            if len(rmod) != N or any(M < 1 or self.moduli[k] % M for k, M in enumerate(rmod)):
                raise TranslationError('malformed certificate')
            if not allowed or any(len(a) != N or any(not 0 <= a[k] < rmod[k] for k in range(N))
                                  for a in allowed):
                raise TranslationError('malformed certificate')
            self.rmod, self.allowed = rmod, allowed

    def admits(self, x):
        """Whether a parameter vector (or a residue key mod `moduli`) satisfies the
        residue restriction."""
        return self.allowed is None or \
            tuple(x[k] % self.rmod[k] for k in range(self.N)) in self.allowed

    def residue_parts(self):
        """(ks, proj): the coordinates the residue restriction depends on, and the
        allowed residue vectors on them, in the order of `residue_prop`'s
        disjuncts; None if the restriction is vacuous."""
        if not hasattr(self, '_rparts'):
            self._rparts = self._residue_parts()
        return self._rparts

    def _residue_parts(self):
        if self.allowed is None:
            return None
        allowed = set(self.allowed)
        ks = []
        for k in range(self.N):             # drop coordinates the restriction ignores
            if self.rmod[k] == 1:
                continue
            rest = {a[:k] + a[k + 1:] for a in allowed}
            if len(allowed) == len(rest) * self.rmod[k]:
                allowed = {a[:k] + (0,) + a[k + 1:] for a in allowed}
                continue
            ks.append(k)
        proj = sorted({tuple(a[k] for k in ks) for a in allowed})
        total = 1
        for k in ks:
            total *= self.rmod[k]
        if len(proj) == total:
            return None
        return ks, proj

    def residue_prop(self, names):
        """The residue restriction as a Lean proposition, or None if it is vacuous."""
        parts = self.residue_parts()
        if parts is None:
            return None
        ks, proj = parts
        conj = [' ∧ '.join(f'{names[k]} % {self.rmod[k]} = {a[j]}' for j, k in enumerate(ks))
                for a in proj]
        if len(conj) == 1:
            return conj[0]
        return ' ∨ '.join(f'({c})' if len(ks) > 1 else c for c in conj)

    def residue_proof(self, res):
        """A proof term of `residue_prop` for parameters with residues `res` (mod
        `rmod`): the matching disjunct is selected explicitly, so `omega` only sees
        the single facts `x % M = r`, never the disjunction."""
        ks, proj = self.residue_parts()
        i = proj.index(tuple(res[k] % self.rmod[k] for k in ks))
        t = '(by omega)' if len(ks) == 1 else f'⟨{", ".join(["(by omega)"] * len(ks))}⟩'
        if i < len(proj) - 1:
            t = f'(Or.inl {t})'
        for _ in range(i):
            t = f'(Or.inr {t})'
        return t

    def const(self, i):
        """The value of the non-parameter register i in the family."""
        return self.consts.get(i, 0)

    def rname(self, rkey):
        return 'r' + '_'.join(map(str, rkey))

    def xform(self, rkey):
        """x_k = M_k*m_k + r_k as forms over m."""
        out = []
        for k in range(self.N):
            f = _fconst(rkey[k], self.N)
            f[k] = self.moduli[k]
            out.append(f)
        return out

    def start_state(self, rkey):
        st = [_fconst(self.const(i), self.N) for i in range(self.W)]
        for k, f in enumerate(self.xform(rkey)):
            st[self.param_regs[k]] = f
        return st

    def family(self, args):
        """C(args) as a Lean tuple body."""
        out = [str(self.const(i)) for i in range(self.W)]
        for k, a in enumerate(args):
            out[self.param_regs[k]] = a
        return ', '.join(out)

    def inv(self, args):
        return f'Inv {" ".join(_paren(a) for a in args)}'


def _leaves(node, splits, out):
    kind = node.get('kind')
    if kind in ('empty', 'leaf'):
        out.append((node, list(splits)))
        return
    if kind != 'split':
        raise TranslationError('malformed proof tree')
    g = list(node['g'])
    neg = [-a for a in g]
    neg[-1] -= 1
    _leaves(node['le'], splits + [(g, 'lt', neg)], out)
    _leaves(node['ge'], splits + [(g, 'ge', g)], out)


def _split_hyp(g, rel, mnames):
    """The hypothesis produced by `rcases Nat.lt_or_ge (pos) (neg)` on g."""
    neg, pos = _sides(g, mnames)
    return f'{pos} < {neg}' if rel == 'lt' else f'{pos} ≥ {neg}'


def _xterm(cx, rkey, mnames):
    """x_k = M_k*m_k + r_k as ℕ-terms."""
    out = []
    for k in range(cx.N):
        f = [0] * cx.N + [rkey[k]]
        f[k] = cx.moduli[k]
        out.append(_nat(f[:-1], f[-1], mnames))
    return out


_MAX_REFINE = 64


def _refine(node, lf, form):
    """Replace the leaf `node` by a chain of splits on the values of `form` (over
    the leaf's n, bounded on its region), each ending in a copy of the leaf."""
    a, b = lf.R.floor_min(form), lf.R.ceil_max(form)
    if b is None:
        raise _Planning('refinement form is unbounded')
    fm = list(form[:-1]) + [form[-1] - sum(form[k] * lf.lo[k] for k in range(len(lf.lo)))]
    leaf = dict(node)
    chain = dict(leaf)
    for v in range(b - 1, a - 1, -1):           # {f <= v} / {f >= v+1}
        g = fm[:-1] + [fm[-1] - (v + 1)]
        chain = {'kind': 'split', 'g': g, 'ge': chain, 'le': dict(leaf)}
    node.clear()
    node.update(chain)


def _residue_parts(cx, em, rkey, tree):
    """Theorems for one residue class: runs, leaves, and the case analysis."""
    N = cx.N
    mnames = [f'{_RVAR}{k}' for k in range(N)]
    xt = _xterm(cx, rkey, mnames)
    root = [_subst(q, cx.xform(rkey), N) for q in cx.P]
    tree = copy.deepcopy(tree)
    for _ in range(_MAX_REFINE):
        leaves = []
        _leaves(tree, [], leaves)
        plan, refined = {}, False
        regions = {id(node): root + [s[2] for s in splits] for node, splits in leaves}
        for idx, (node, splits) in enumerate(leaves):
            if node['kind'] == 'empty':
                plan[id(node)] = None
                continue
            lf = _Leaf(cx, rkey, idx, root + [s[2] for s in splits], splits, node)
            if lf.lo is None:               # no point with m >= 0
                plan[id(node)] = None
                continue
            try:
                try:
                    lf.plan()
                except _Planning:
                    # rational reasoning on the region was not enough: retry once on
                    # the region tightened by integer cuts (only then, so that leaves
                    # that already plan are translated exactly as before)
                    lf2 = _Leaf(cx, rkey, idx, root + [s[2] for s in splits], splits, node,
                                tight=True)
                    if lf2.lo is not None and lf2.ncons == lf.ncons:
                        raise
                    lf = lf2
                    if lf.lo is None:       # no integer point at all
                        plan[id(node)] = None
                        continue
                    lf.plan()
            except _Refine as r:
                _refine(node, lf, r.form)
                refined = True
                break
            lf.verify()
            plan[id(node)] = lf
        if not refined:
            break
    else:
        raise _Planning('too many refinements')
    parts = []
    concl = (f'∃ c\', Pr c\' ∧ (⟨{cx.family(xt)}⟩ : Q) [fm]⊢⁺ c\'')
    for node, _ in leaves:
        if plan[id(node)] is not None:
            parts += _emit_leaf(cx, em, plan[id(node)], mnames)

    # the case analysis
    rn = cx.rname(rkey)
    lines = [f'theorem res_{rn} ({" ".join(mnames)} : ℕ) (h : {cx.inv(xt)}) :',
             f'    {concl} := by']

    def walk(node, depth, ind, hyps):
        kind = node['kind']
        if kind == 'empty' or (kind == 'leaf' and plan[id(node)] is None):
            if cx.enumerate_empty:
                lines.append(f'{ind}exfalso')
                lines.extend(_enumerate_empty(N, regions[id(node)], mnames, ind))
            else:
                lines.append(f'{ind}exfalso; omega')
            return
        if kind == 'leaf':
            args = ' '.join(mnames + ['h'] + hyps)
            lines.append(f'{ind}exact leaf_{plan[id(node)].name} {args}')
            return
        neg, pos = _sides(node['g'], mnames)
        s = f's{depth}'
        lines.append(f'{ind}rcases Nat.lt_or_ge ({pos}) ({neg}) with {s} | {s}')
        for child in (node['le'], node['ge']):
            mark = len(lines)
            walk(child, depth + 1, ind + '  ', hyps + [s])
            lines[mark] = ind + '· ' + lines[mark][len(ind) + 2:]

    walk(tree, 0, '  ', [])
    parts.append('\n'.join(lines) + '\n')
    return parts


_ENUM_MAX = 16


def _enumerate_empty(N, cons, names, ind, fixed=None):
    """Tactic lines closing `False` on a region with no integer point.

    `omega` refutes a region with no rational point, and one with a single free
    variable, but it does not implement the dark/grey shadows, so it can fail on
    a region that has rational points and no integer point (e.g. 0 <= a <= 1,
    2a - 3b <= -2, 4a - 3b >= 0).  So bounded variables are enumerated over their
    rational range rounded outward, smallest range first, until the region is
    rationally empty or one variable is left; both are exact for `omega`."""
    fixed = dict(fixed or {})
    free = [k for k in range(N) if k not in fixed]

    def sub(c):                 # substitute the fixed values, over the free variables
        return [c[k] for k in free] + [c[N] + sum(c[k] * v for k, v in fixed.items())]
    sc = [sub(c) for c in cons]
    if len(free) <= 1 or any(not any(c[:-1]) and c[-1] < 0 for c in sc):
        return [f'{ind}omega']
    R = _Region(len(free), [c for c in sc if any(c[:-1])])
    if R.empty():
        return [f'{ind}omega']
    best = None
    for j, k in enumerate(free):
        hi = max(v[j] for v in R.verts)
        if not R.ge0([-1 if i == j else 0 for i in range(len(free))] + [ceil(hi)]):
            continue            # unbounded above
        # rounded outward: `omega` proves the disjunction from the rational
        # bounds alone (the inward-rounded range would need integer reasoning)
        lo = max(0, floor(min(v[j] for v in R.verts)))
        vals = list(range(lo, ceil(hi) + 1))
        if best is None or len(vals) < len(best[1]):
            best = (k, vals)
    if best is None or len(best[1]) > _ENUM_MAX:
        return [f'{ind}omega']
    k, vals = best
    out = [f'{ind}rcases (by omega : ' + ' ∨ '.join(f'{names[k]} = {v}' for v in vals)
           + ') with ' + ' | '.join(['rfl'] * len(vals))]
    for v in vals:
        body = _enumerate_empty(N, cons, names, ind + '  ', {**fixed, k: v})
        body[0] = ind + '· ' + body[0][len(ind) + 2:]
        out += body
    return out


def _emit_leaf(cx, em, lf, mnames):
    """The run theorem(s) and the leaf theorem of one leaf."""
    N, W = cx.N, cx.W
    names = lf.names
    rn = lf.name
    hyps = lf.hyps()
    blocks = lf.blocks(em)
    start_r = lf.render(lf.segs[0][2], lf.start)
    last = lf.segs[-1]
    end_r = lf.render(last[2], last[1][-1])
    plus = next(k for k, b in enumerate(blocks) if callable(b[2]))
    blocks[plus][3] = True
    parts = []
    # `lattice_hints`: on a region whose integer points are c + u*v, the run gets u
    # and the equalities n_k = c_k + v_k*u as hypotheses (`_eK`), so that `omega`
    # eliminates the n_k exactly instead of re-solving the region's equalities
    # The region then needs no other hypothesis: the run gets the equalities (and
    # u <= umax) instead of the region's inequalities.
    lat = lf.lattice() if cx.lattice_hints else None
    lat_hyps, lat_names = [], []
    if lat is not None:
        c0, v, _, umax, _ = lat
        for k in range(N):
            if v[k] >= 0:
                rhs = _nat([v[k]], c0[k], ['u'])
            else:
                rhs = f'{c0[k]} - {_nat([-v[k]], 0, ["u"])}'
            lat_hyps.append(f'(_e{k} : {names[k]} = {rhs})')
            lat_names.append(f'_e{k}')
        if umax is not None:
            lat_hyps.append(f'(_eu : u ≤ {umax})')
            lat_names.append('_eu')
    binders = ' '.join(names + (['u'] if lat else []))
    hyps_all = lat_hyps if lat else hyps
    hyp_s = (' ' + ' '.join(hyps_all)) if hyps_all else ''


    def chain(seg, p, ind='  '):
        lines = []
        for k, b in enumerate(seg):
            arrow = '⊢⁺' if b[3] else '⊢*'
            head = f'{ind}have h{k} : (⟨{", ".join(b[0])}⟩ : Q) [fm]{arrow} ⟨{", ".join(b[1])}⟩ :='
            if isinstance(b[2], list):
                lines.append(head + ' by')
                lines += [f'{ind}  {t}' for t in b[2]]
            else:
                lines.append(f'{head} {b[2]}')
        lines.append(f'{ind}exact ' + _chain(len(seg), p))
        return lines

    ys = [f'y{i}' for i in range(W)]
    zs = [f'z{i}' for i in range(W)]
    eqs = [f'(hy{i} : y{i} = {start_r[i]})' for i in range(W)]
    eqs += [f'(hz{i} : z{i} = {end_r[i]})' for i in range(W)]
    head = [f'/-- Residue class {lf.rkey}, leaf {lf.idx}. -/',
            f'theorem run_{rn} ({binders} {" ".join(ys)} {" ".join(zs)} : ℕ){hyp_s} '
            + ' '.join(eqs) + ' :',
            f'    (⟨{", ".join(ys)}⟩ : Q) [fm]⊢⁺ ⟨{", ".join(zs)}⟩ := by',
            '  rw [' + ', '.join([f'hy{i}' for i in range(W)] + [f'hz{i}' for i in range(W)])
            + ']']
    blocks = [[b[0], b[1], b[2](b[3]) if callable(b[2]) else b[2], b[3]] for b in blocks]
    if len(blocks) <= _SEG:
        parts.append('\n'.join(head + chain(blocks, plus)) + '\n')
    else:
        segs = []
        hargs = ' '.join(lat_names if lat else [f'_h{k}' for k in range(len(hyps))])
        for g, a in enumerate(range(0, len(blocks), _SEG)):
            seg = blocks[a:a + _SEG]
            p = plus - a if a <= plus < a + _SEG else None
            arrow = '⊢*' if p is None else '⊢⁺'
            parts.append('\n'.join([
                f'theorem run_{rn}_seg{g} ({binders} : ℕ){hyp_s} :',
                f'    (⟨{", ".join(seg[0][0])}⟩ : Q) [fm]{arrow} ⟨{", ".join(seg[-1][1])}⟩ := by']
                + chain(seg, p)) + '\n')
            call = f'run_{rn}_seg{g} {binders}' + (f' {hargs}' if hargs else '')
            segs.append([seg[0][0], seg[-1][1], call, p is not None])
        parts.append('\n'.join(head + chain(segs, plus // _SEG)) + '\n')

    # the leaf theorem: shift, then glue the run to `Pr` (a variable that is not
    # shifted is called n_k from the start)
    bnames = [mnames[k] if lf.lo[k] else names[k] for k in range(N)]
    xt = _xterm(cx, lf.rkey, bnames)
    rel_hyps = [f'(_s{d} : {_split_hyp(g, rel, bnames)})'
                for d, (g, rel, _) in enumerate(lf.splits)]
    lines = [f'theorem leaf_{rn} ({" ".join(bnames)} : ℕ) (_h : {cx.inv(xt)})'
             + ''.join(' ' + r for r in rel_hyps) + ' :',
             f'    ∃ c\', Pr c\' ∧ (⟨{cx.family(xt)}⟩ : Q) [fm]⊢⁺ c\' := by']
    # with a residue restriction, keep only the polyhedral part of `Inv`: the
    # disjunction is not needed here, and every `omega` would case-split on it
    restricted = cx.residue_parts() is not None
    if restricted:
        lines.append(f'  obtain ⟨{", ".join(f"_h{k}" for k in range(len(cx.P)))}, -⟩ := _h'
                     if cx.P else '  clear _h')
    if lat is not None:
        # The region's equalities have non-unit coefficients, and an `omega` that sees
        # them over all the variables takes seconds.  So the parametrization
        # m_k = C_k + v_k*u is proved in a lemma `lat_…`, which first substitutes the
        # equalities that solve for one variable with a unit coefficient; after the
        # call every later `omega` of the leaf has a unit equality for each m_k.
        c0, v, j, umax, eqs = lat
        C = [c0[k] + lf.lo[k] for k in range(N)]

        def mexpr(k):
            if v[k] >= 0:
                return _nat([v[k]], C[k], ['u'])
            return f'{C[k]} - {_nat([-v[k]], 0, ["u"])}'
        # unit pivots: m_k = (non-negative combination of the others) + b
        meqs = [list(e[:N]) + [e[N] - sum(e[i] * lf.lo[i] for i in range(N))] for e in eqs]
        subs, done = [], set()
        for e in meqs:
            for k in range(N):
                if k in done or abs(e[k]) != 1 or k == j:
                    continue
                f = [x * -e[k] for x in e]          # m_k = sum f_i m_i + f_N (i != k)
                f[k] = 0
                if any(f[i] and i in done for i in range(N)):
                    continue
                if all(x >= 0 for x in f):
                    subs.append((k, _nat(f[:N], f[N], bnames)))
                    done.add(k)
                    break
        lhyps = [f'(_h : {cx.inv(xt)})'] + rel_hyps
        concl = ' ∧ '.join([f'{bnames[k]} = {mexpr(k)}' for k in range(N)]
                           + ([f'u ≤ {umax}'] if umax is not None else []))
        diff = (f'{bnames[j]} - {C[j]}' if v[j] > 0 else f'{C[j]} - {bnames[j]}') \
            if C[j] else bnames[j]
        wit = diff if abs(v[j]) == 1 else f'({diff}) / {abs(v[j])}'
        body = [f'theorem lat_{rn} ({" ".join(bnames)} : ℕ) ' + ' '.join(lhyps) + ' :',
                f'    ∃ u, {concl} := by']
        if restricted:
            body.append(f'  obtain ⟨{", ".join(f"_h{k}" for k in range(len(cx.P)))}, -⟩ := _h'
                        if cx.P else '  clear _h')
        for t, (k, ex) in enumerate(subs):
            body.append(f'  have _q{t} : {bnames[k]} = {ex} := by omega')
            body.append(f'  subst _q{t}')
        nconj = N + (umax is not None)
        body.append(f'  exact ⟨{wit}, {", ".join(["by omega"] * nconj)}⟩')
        parts.append('\n'.join(body) + '\n')
        fnames = [f'_f{k}' for k in range(N)] + (['_eu'] if umax is not None else [])
        call = ' '.join(bnames + ['_h'] + [f'_s{d}' for d in range(len(lf.splits))])
        lines.insert(2, f'  obtain ⟨u, {", ".join(fnames)}⟩ := lat_{rn} {call}')
    vnames = list(names)
    if lat is None:
        for k in range(N):
            if lf.lo[k]:
                lines.append(f'  obtain ⟨{names[k]}, rfl⟩ : ∃ n, {mnames[k]} = n + {lf.lo[k]} := '
                             f'⟨{mnames[k]} - {lf.lo[k]}, by omega⟩')
    else:
        # substitute m_k := C_k + v_k*u (an `omega` that only has the equalities as
        # hypotheses stays slow), then name n_k = c_k + v_k*u for the run
        lines += [f'  subst _f{k}' for k in range(N)]
        for k in range(N):
            h = lat_hyps[k]
            lines.append(f'  obtain ⟨{names[k]}, _e{k}⟩ : ∃ n, n = {h[h.index("=") + 2:-1]} '
                         f':= ⟨_, rfl⟩')
    goal = [_nat([cx.moduli[k] if j == k else 0 for j in range(N)], lf.rkey[k],
                 [f'({vnames[j]} + {lf.lo[j]})' if lf.lo[j] else vnames[j]
                  for j in range(N)]) for k in range(N)]
    goal_state = [str(cx.const(i)) for i in range(W)]
    for k in range(N):
        goal_state[cx.param_regs[k]] = goal[k]
    args = vnames + (['u'] if lat else []) + ['_'] * (2 * W) \
        + (lat_names if lat else ['(by omega)'] * len(hyps))
    start_p = lf.poly(lf.segs[0][2], lf.start)
    if lat is None:
        args += [_eq_proof(goal_state[i], start_r[i], lf.start[i], start_p[i])
                 for i in range(W)]
    else:                           # the leaf's state is over u, the run's over n
        args += ['rfl' if goal_state[i] == start_r[i] else '(by omega)' for i in range(W)]
    if lf.loop is None:
        xprime = [end_r[r] for r in cx.param_regs]
        end_p = lf.poly(last[2], last[1][-1])
        tgt = [str(cx.const(i)) for i in range(W)]
        for k, r in enumerate(cx.param_regs):
            tgt[r] = xprime[k]
        args += [_eq_proof(tgt[i], end_r[i], end_p[i] if i in cx.param_regs
                           else _fconst(cx.const(i), N), end_p[i]) for i in range(W)]
        if restricted:
            # the polyhedral part by one `omega`, the residue disjunct selected
            # explicitly (`inv_mk`); `omega` on the whole `Inv` case-splits on the
            # disjunction, and one `omega` per conjunct can hit `maxRecDepth`
            res = cx.residue_proof(lf.end_res)
            mem = (f'⟨{", ".join(_paren(x) for x in xprime)}, rfl, '
                   + (f'inv_mk (by omega) {res}⟩' if cx.P else f'{res}⟩'))
        else:
            mem = f'⟨{", ".join(_paren(x) for x in xprime)}, rfl, by omega⟩'
        lines.append(f'  exact ⟨_, {"Or.inl " if cx.loops else ""}{mem},')
        lines.append(f'    run_{rn} {" ".join(args)}⟩')
    else:
        args += ['rfl'] * W
        loop_args = ' '.join(vnames + ['(by omega)'] * len(hyps))
        lines.append(f'  exact ⟨(⟨{", ".join(end_r)}⟩ : Q), Or.inr (cycle_nonhalt '
                     f'(loop_{rn} {loop_args})),')
        lines.append(f'    run_{rn} {" ".join(args)}⟩')
        parts.append(_emit_loop(em, lf, hyps))
    parts.append('\n'.join(lines) + '\n')
    return parts


def _emit_loop(em, lf, hyps):
    """`S ⊢⁺ S` for the final net-zero cycle of a leaf."""
    steps, states, reps = lf.segs[-1]
    L = len(lf.loop)
    st = states[len(states) - 1 - L:]
    specs = [(steps[len(steps) - L + t].rule,
              lf._spec(reps, st[t], steps[len(steps) - L + t].rule)) for t in range(L)]
    lines = [em.step_line(j, sp, n == 0) for n, (j, sp) in enumerate(specs)]
    s0 = lf.render(reps, st[0])
    return '\n'.join([f'theorem loop_{lf.name} ({" ".join(lf.names)} : ℕ)'
                      + ''.join(' ' + h for h in hyps) + ' :',
                      f'    (⟨{", ".join(s0)}⟩ : Q) [fm]⊢⁺ ⟨{", ".join(s0)}⟩ := by']
                     + ['  ' + t for t in _tactics(lines)]) + '\n'


# ============================================================================
# top level
# ============================================================================

# Machines whose certificates verify under default options only with an opt-in
# option (found on holdout/sz24_10572.txt, NDRPC with time_budget=3600; the line
# number in that list is given).  `nd_progress_to_lean` applies these unless the
# option is passed explicitly, so that the sz24 files are reproduced by a plain call.
_MACHINE_OPTIONS = {
    '[27/10, 44/21, 91/2, 5/121, 15/13]': {'lattice_hints': True},     # line 3628
    '[9/10, 88/21, 91/2, 5/11, 75/13]': {'lattice_hints': True},       # line 9580
    '[9/10, 22/21, 343/2, 175/121, 3/7]': {'enumerate_empty': True},   # line 9199
}


def nd_progress_to_lean(F: list[list[int]], cert: dict, name: str = 'Foo',
                        max_heartbeats: int | None = None,
                        enumerate_empty: bool | None = None,
                        lattice_hints: bool | None = None) -> str:
    """Translate an `nd_progress_cert` certificate for `F` into a Lean 4 file.

    `name` is used both as the module name and as the namespace, so the result
    belongs in `<name>.lean`.  `max_heartbeats`, if given, raises Lean's
    per-declaration limit with a `set_option` in the file (for the rare file
    whose declarations do not fit the default 200000).  `enumerate_empty`
    closes the case-analysis branches without integer points by enumerating
    bounded parameters instead of a bare `omega` (see `_enumerate_empty`).
    `lattice_hints` hands each run on a 1-dimensional lattice region its
    parametrization (see `_Leaf.lattice`).  Both are off unless given, or unless
    `_MACHINE_OPTIONS` lists them for F.  Raises `TranslationError` on failure."""
    known = _MACHINE_OPTIONS.get(unparse_line(F), {})
    if enumerate_empty is None:
        enumerate_empty = known.get('enumerate_empty', False)
    if lattice_hints is None:
        lattice_hints = known.get('lattice_hints', False)
    if cert is None:
        raise TranslationError('no certificate')
    if 'trees' not in cert or cert['trees'] is None:
        raise TranslationError('certificate has no proof trees (use nd_progress_cert)')
    _check_ident(name)
    W = len(F[0])
    if not 1 <= W <= 26:
        raise TranslationError('unsupported register count')
    cx = _Context(F, cert)
    cx.enumerate_empty = enumerate_empty
    cx.lattice_hints = lattice_hints
    keys = [k for k in itertools.product(*[range(M) for M in cx.moduli]) if cx.admits(k)]
    if sorted(cert['trees']) != keys:
        raise TranslationError('certificate does not cover every residue class')
    cx.loops = any(_has_loop(cert['trees'][k]) for k in keys)

    # bootstrap anchor: a family member in the invariant
    boot = list(cert['boot_state'])
    if len(boot) != W or any(boot[i] != cx.const(i) for i in range(W)
                             if i not in cx.param_regs):
        raise TranslationError('bootstrap state is not a family member')
    x0 = [boot[r] for r in cx.param_regs]
    if any(_feval(q, x0) < 0 for q in cx.P) or not cx.admits(x0):
        raise TranslationError('bootstrap state is outside the invariant')

    em = _Emitter(F, W, cx.maxneed)
    parts = []
    try:
        for k in keys:
            parts += _residue_parts(cx, em, k, cert['trees'][k])
    except _Planning as e:
        raise TranslationError(f'planning failed: {e}') from e
    parts.append(_progress(cx))
    st = ', '.join(map(str, boot))
    try:
        bthms, blines = _boot(F, W, cert['boot_t'], st)
    except _Fail:
        raise TranslationError('bootstrap does not reach the anchor') from None
    parts += bthms
    pnames = cx.pnames
    lines = ['theorem nonhalt : ¬halts fm c₀ := by',
             f'  have key : ¬halts fm (⟨{st}⟩ : Q) := by',
             '    apply progress_nonhalt (fm := fm) (P := Pr)']
    if cx.loops:
        lines += [f'    · rintro c (⟨{", ".join(pnames)}, rfl, h⟩ | h)',
                  f'      · exact progress {" ".join(pnames)} h',
                  '      · exact nonhalt_next h']
    else:
        lines += [f'    · rintro c ⟨{", ".join(pnames)}, rfl, h⟩',
                  f'      exact progress {" ".join(pnames)} h']
    if cx.residue_parts() is not None:     # as in the leaves: no `omega` on the disjunction
        boot_mem = (f'⟨{", ".join(map(str, x0))}, rfl, ' + ''.join('(by omega), ' for _ in cx.P)
                    + f'{cx.residue_proof(x0)}⟩')
    else:
        boot_mem = f'⟨{", ".join(map(str, x0))}, rfl, by omega⟩'
    lines.append(f'    · exact {boot_mem}' if not cx.loops else f'    · exact Or.inl {boot_mem}')
    parts.append('\n'.join(lines + blines))
    out = _assemble(F, W, name, cert, cx, em, parts)
    if max_heartbeats is not None:
        imports = 'import BBfLean.FM\nimport Mathlib.Tactic.Ring\n'
        assert out.startswith(imports)
        out = imports + f'\nset_option maxHeartbeats {int(max_heartbeats)}\n' + out[len(imports):]
    return out


def _has_loop(node):
    if node.get('kind') == 'split':
        return _has_loop(node['ge']) or _has_loop(node['le'])
    return (node.get('kind') == 'leaf' and node['events']
            and node['events'][-1][0] == 'loop')


def _progress(cx):
    """The residue split, dispatching to the `res…` theorems."""
    N = cx.N
    pn = cx.pnames
    lines = [f'theorem progress ({" ".join(pn)} : ℕ) (h : {cx.inv(pn)}) :',
             f'    ∃ c\', Pr c\' ∧ (⟨{cx.family(pn)}⟩ : Q) [fm]⊢⁺ c\' := by']
    mnames = [pn[k] if cx.moduli[k] == 1 else f'{_RVAR}{k}' for k in range(N)]

    def go(k, rkey, ind):
        if k == N:
            if cx.admits(rkey):
                lines.append(f'{ind}exact res_{cx.rname(tuple(rkey))} {" ".join(mnames)} h')
            else:
                lines.append(f'{ind}exfalso; omega')
            return
        M = cx.moduli[k]
        if M == 1:
            go(k + 1, rkey + [0], ind)
            return
        lines.append(f'{ind}obtain ⟨{mnames[k]}, r{k}, hr{k}, rfl⟩ : ∃ m r, r < {M} ∧ '
                     f'{pn[k]} = {M}*m + r := ⟨{pn[k]} / {M}, {pn[k]} % {M}, by omega, by omega⟩')
        lines.append(f'{ind}rcases (by omega : ' + ' ∨ '.join(f'r{k} = {r}' for r in range(M))
                     + ') with ' + ' | '.join(['rfl'] * M))
        for r in range(M):
            mark = len(lines)
            go(k + 1, rkey + [r], ind + '  ')
            lines[mark] = ind + '· ' + lines[mark][len(ind) + 2:]

    ks = [k for k in range(N) if cx.moduli[k] > 1]
    if cx.residue_parts() is None or not ks:
        go(0, [], '  ')
        return '\n'.join(lines) + '\n'

    # with a residue restriction every `omega` here sees the disjunction, and the
    # whole case analysis can exceed one declaration's heartbeats: split it on the
    # first parameter with a modulus, one theorem `progress_r<r>` per residue
    k0 = ks[0]
    M = cx.moduli[k0]
    out = []
    binders = [mnames[k0] if k == k0 else pn[k] for k in range(N)]
    for r in range(M):
        args = list(pn)
        args[k0] = _nat([M if j == k0 else 0 for j in range(N)], r, binders)
        sub = [f'theorem progress_r{r} ({" ".join(binders)} : ℕ) (h : {cx.inv(args)}) :',
               f'    ∃ c\', Pr c\' ∧ (⟨{cx.family(args)}⟩ : Q) [fm]⊢⁺ c\' := by']
        lines, keep = sub, lines
        go(k0 + 1, [0] * k0 + [r], '  ')
        out.append('\n'.join(lines) + '\n')
        lines = keep
    lines.append(f'  obtain ⟨{mnames[k0]}, r{k0}, hr{k0}, rfl⟩ : ∃ m r, r < {M} ∧ '
                 f'{pn[k0]} = {M}*m + r := ⟨{pn[k0]} / {M}, {pn[k0]} % {M}, by omega, by omega⟩')
    lines.append(f'  rcases (by omega : ' + ' ∨ '.join(f'r{k0} = {r}' for r in range(M))
                 + ') with ' + ' | '.join(['rfl'] * M))
    for r in range(M):
        lines.append(f'  · exact progress_r{r} {" ".join(binders)} h')
    return '\n'.join(out + lines) + '\n'


def _assemble(F, W, name, cert, cx, em, parts):
    ns = name
    pn = cx.pnames
    rp = cx.residue_prop(pn)
    inv = ' ∧ '.join([_ineq(q, pn) for q in cx.P] + ([f'({rp})'] if rp else [])) or 'True'
    fam = f'∃ {" ".join(pn)}, q = (⟨{cx.family(pn)}⟩ : Q) ∧ {cx.inv(pn)}'
    mods = ', '.join(f'{pn[k]} mod {cx.moduli[k]}' for k in range(cx.N) if cx.moduli[k] > 1)
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
            'This file was generated by `decider/nd_progress_to_lean.py` from the',
            'N-D progress certificate',
            '```',
            cert_str(cert) if cx.allowed is None else ndr_cert_str(cert),
            '```',
            f'with invariant family C({", ".join(pn)}) = ⟨{cx.family(pn)}⟩'
            + (f', verified per residue class ({mods}).' if mods else '.')]
    if rp:
        head += [f'The invariant is restricted to the residues {rp}.']
    head += [
        '-/',
        '',
        f'namespace {ns}',
        '',
        f'def Q := {" × ".join("ℕ" for _ in range(W))}',
        f'def c₀ : Q := ⟨{", ".join("1" if i == 0 else "0" for i in range(W))}⟩',
        'def fm : Q → Option Q := fun q ↦ match q with',
        '  | ' + ('\n  | '.join(_fm_lines(F))),
        '  | _ => none',
        '',
        '/-- The invariant region. -/',
        f'abbrev Inv ({" ".join(p if any(q[k] for q in cx.P) or (rp and cx.rmod[k] > 1) else "_" + p for k, p in enumerate(pn))}'
        f' : ℕ) : Prop := {inv}',
        '',
        '/-- The invariant set of states. -/',
        f'abbrev Pr (q : Q) : Prop := ({fam}) ∨ ¬halts fm q' if cx.loops else
        f'abbrev Pr (q : Q) : Prop := {fam}',
        '']
    if rp and cx.P:
        k = len(cx.P)
        proj = [f'hp{".2" * j}.1' for j in range(k - 1)] + [f'hp{".2" * (k - 1)}']
        head += [
            '/-- `Inv` from its polyhedral part and its residue part. -/',
            f'theorem inv_mk {{{" ".join(pn)} : ℕ}} (hp : {" ∧ ".join(_ineq(q, pn) for q in cx.P)})',
            f'    (hr : {rp}) : Inv {" ".join(pn)} :=',
            f'  ⟨{", ".join(proj)}, hr⟩',
            '']
    head += [
        'theorem sstar {c₁ c₂ c₃ : Q} (h₁ : fm c₁ = some c₂) (h₂ : c₂ [fm]⊢* c₃) :',
        '    c₁ [fm]⊢* c₃ :=',
        '  stepPlus_stepStar (step_stepStar_stepPlus h₁ h₂)',
        '']
    if cx.loops:
        head += ['theorem cycle_nonhalt {c : Q} (h : c [fm]⊢⁺ c) : ¬halts fm c :=',
                 '  progress_nonhalt_simple (A := Unit) (fun _ ↦ c) () (fun _ ↦ ⟨(), h⟩)',
                 '',
                 'theorem nonhalt_next {c : Q} (h : ¬halts fm c) : ∃ c\', Pr c\' ∧ c [fm]⊢⁺ c\' := by',
                 '  rcases hc : fm c with _ | c\'',
                 '  · exact absurd (halted_halts hc) h',
                 '  · exact ⟨c\', Or.inr fun h\' ↦ h (step_halts hc h\'), step_stepPlus hc⟩',
                 '']
    body = _wrap_text('\n'.join(em.order + parts))
    return '\n'.join(head + [body] + ['', f'end {ns}', ''])


if __name__ == '__main__':
    # python -m decider.nd_progress_to_lean "[9/35, 5/33, 98/3, 11/49, 15/2]" Foo
    import sys
    from decider.utils import parse_line

    fm_line = sys.argv[1] if len(sys.argv) > 1 else '[9/35, 5/33, 98/3, 11/49, 15/2]'
    module = sys.argv[2] if len(sys.argv) > 2 else 'Foo'
    machine = parse_line(fm_line)
    certificate = nd_progress_cert(machine)
    if certificate is None:
        sys.exit(f'nd_progress found no certificate for {fm_line}')
    print(nd_progress_to_lean(machine, certificate, module), end='')
