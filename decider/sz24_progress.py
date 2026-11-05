# python -m decider.sz24_progress
import inspect
import itertools
import re
import textwrap
from collections import defaultdict
from contextlib import contextmanager
from fractions import Fraction
from math import gcd

import decider.nd_progress as _N
import decider.ndr_progress as _R
import decider.oned_progress as _O
import decider.nd_progress_to_lean as _NL
import decider.oned_progress_to_lean as _OL
from decider.nd_progress_to_lean import nd_progress_to_lean
from decider.ndr_progress import verify_region_r
from decider.oned_progress import (_add_anchors, _fit_poly, _mul_anchors, _peval_fr, _pnorm,
                                   _pnorm_fr, _verify_additive, _verify_multiplicative)
from decider.utils import parse_file, unparse_line

"""
WARNING: This decider was entirely written by AI (Claude). It reuses the soundness-critical
engines of `oned_progress` and `nd_progress`/`ndr_progress` unchanged; see the warnings there.

---

Progress certificates for `holdout/sz24_3580.txt`, with a hardcoded table of settings.

Two kinds of certificate, both in an existing format and translated into Lean by the existing
translators (`oned_progress_to_lean`, `nd_progress_to_lean`):

1. STRIDED 1-D PROGRESS (format of `oned_progress_cert`, flavour 'add' or 'mul').
   `oned_progress` fits its family f(u) to CONSECUTIVE occurrences of a shape.  Many sz24
   machines have such a family only on every S-th occurrence; the occurrences in between
   follow a different formula (a period-S cycle of phases).  Examples:
     * [1/105, 10/3, 27/22, 7/2, 33/5, 3/7]: the shape (a,0,c,0,0) has a = 7,8,9,11,13,14,..
       (increments 1,1,2,2 repeating); every 4th member is f(u) = (6u+1, 0, 8u+1, 0, 0).
     * [1/90, 98/15, 3/7, 3125/2, 3/5]: c_{k+1} = 2*c_k + r_k with r_k of period 6, so every
       6th member is c*64^j + d (base 64).
     * [25/63, 242/7, 14/55, 3/2, 245/3]: consecutive ratios alternate 2 and 3/2, so
       v_{k+2} = 3*v_k + c_phase.
   A family on every S-th member is still a 1-D progress family: the engine proves
   f(u) |-+ f(u+1) (resp. f(X) |-+ f(B^j X)) and runs through the S-1 intermediate members,
   which are other polynomials and never satisfy the exact target test.  Besides the stride,
   the engine needs a residue split u = M*m + r whose modulus makes every accelerated loop
   count a clean floor; `oned_progress` tries a fixed list, `_smart_M` grows M by exactly the
   factor a failed floor division asked for (e.g. [1/30, 15/7, 49/33, 16/5, 847/2]: a' = 3a+2
   needs a split divisible by 5 for the loop ⌊(24m+8)/5⌋).

2. N-D RESIDUE PROGRESS (format of `ndr_progress_cert`).  The certificates were found by
   `ndr_progress_cert` with larger limits than the official NDRPC run: up to 5 parameters
   (shapes with 4-5 varying registers are often a 2-D family in disguise) and a residue-split
   product of up to 400 or 1000 instead of 64 (e.g. [100/63, 7/22, 27/2, 11/5, 14/3]:
   (b, c) -> (b + c + 6, 2c + 2) needs moduli [12, 6]).

DETERMINISM.  Both searches stop on wall-clock budgets, so they are not part of the decider.
The table `_TABLE` stores, per machine, the settings that the search found:
  * 1-D: flavour, stride, the family polynomials, M (and the base B), the anchors as
    (u or X, step count);
  * N-D: the parameter registers, constant registers, the final invariant P, the residue
    restriction (rmod, allowed), the engine variant (split_gates), the step count of the
    bootstrap.
`sz24_progress_cert(F)` rebuilds the whole certificate from these with the engine and no time
limit (the engine is deterministic: the same inputs give the same proof trees), and the
concrete states (anchors, bootstrap) by simulation.  The engine re-proves everything; the
table only says where to look.  Machines not in the table: None.

LEAN.  `sz24_progress_to_lean(F, cert, name)` translates.  Strided anchors can be ~10^6 steps
out, so 1-D certificates use an ACCELERATED BOOTSTRAP (`_boot_fast`): on the concrete run
from c₀, a rule block that the real run repeats >= 10 times is discharged by one application
of the translator's own cycle lemma `cycN` (`∀ k x…`), instantiated at numerals, instead of
`execute fm 100` chunks.  It is swapped into `oned_progress_to_lean` only for the duration of
the call (`_fast_boot`), so the module's behaviour is unchanged for everyone else.  A few
N-D machines need `max_heartbeats` (`_LEAN_OPTIONS`).

RESULTS.  1463 of the 3580 machines: 220 strided 1-D (141 'add' + 79 'mul'), 1233 N-D
(308 'nd', 525 'ndx', 328 'ndcv', 19 'ndz', 51 'ndxz', 2 'ndcvz') and 10 valuation chains ('val').
None of them is in `sz24_2002_hydra_unofficial.txt`.  Every Lean file `sz24_progress_to_lean`
produces for them was checked with `lean -j1` (Lean 4.36.0-rc1, one file per process): it compiles
with no errors, and `#print axioms <name>.nonhalt` lists only propext, Classical.choice, Quot.sound;
its `Q`, `c₀`, `fm` are the canonical encoding (as in `other/gen_lean.py`) and it states
`theorem nonhalt : ¬halts fm c₀`.  CPU per file: median 32 s, p99 667 s, max 1460 s (about 34
core-hours in all); peak RSS: median 2.1 GB, max 14.0 GB.  Where an existing certificate was
expensive, the cheaper of the variants (the same invariant rebuilt with the lazy loop bound or the
integer LP, a re-searched certificate, `fast_boot`) was kept.
"""

# ===========================================================================
# 1-D: adaptive residue split
# ===========================================================================


@contextmanager
def _record_divisors():
    """While active, every non-clean floor division of the 1-D engine appends to the yielded
    list the factor by which the split modulus would have to grow.  The result of the
    division is unchanged."""
    need = []
    orig = _O._floordiv

    def rec(p, d):
        r = orig(p, d)
        if r is None:
            f = 1
            for c in _pnorm(p)[1:]:
                g = d // gcd(d, c)
                f = f * g // gcd(f, g)
            need.append(f)
        return r
    _O._floordiv = rec
    try:
        yield need
    finally:
        _O._floordiv = orig


def _smart_M(verify, Mmax=360, tries=15):
    """verify(M) -> result or None.  M = 1 first, then M grown by the recorded factors
    (falling back to 2M, 3M).  Returns (M, result) or None."""
    tried = set()
    queue = [1]
    for _ in range(tries):
        if not queue:
            return None
        M = queue.pop(0)
        if M in tried or M > Mmax:
            continue
        tried.add(M)
        with _record_divisors() as need:
            r = verify(M)
        if r is not None:
            return M, r
        f = 1
        for x in need:
            f = f * x // gcd(f, x)
        if f > 1:
            queue.insert(0, M * f // gcd(M, f))
        for k in (2, 3):
            if M * k not in tried:
                queue.append(M * k)
    return None


_KW1 = dict(max_prim=3000, max_accel=200, max_deg=6, Lmax=48)

# ===========================================================================
# 1-D: search for strided families (deterministic, bounded by candidate counts)
# ===========================================================================


def _shapes(F, width, step_cap, min_occ, max_occ=None):
    """[(shape, [(t, state)])] for the shapes seen >= min_occ times in the first step_cap
    steps (shapes seen > max_occ times are dropped), fewest non-zero registers first, then
    most occurrences.  None if the machine halts."""
    guards = [[(i, -d) for i, d in enumerate(r) if d < 0] for r in F]
    deltas = [[(i, d) for i, d in enumerate(r) if d != 0] for r in F]
    s = [0] * width
    s[0] = 1
    by = defaultdict(list)
    dropped = set()
    for t in range(step_cap):
        for j in range(len(F)):
            if all(s[i] >= k for i, k in guards[j]):
                break
        else:
            return None
        for i, d in deltas[j]:
            s[i] += d
        key = tuple(x == 0 for x in s)
        if key in dropped:
            continue
        by[key].append((t + 1, tuple(s)))
        if max_occ is not None and len(by[key]) > max_occ:
            dropped.add(key)
            del by[key]
    out = [(k, v) for k, v in by.items() if len(v) >= min_occ]
    out.sort(key=lambda kv: (sum(0 if z else 1 for z in kv[0]), -len(kv[1]), kv[0]))
    return out


def _fit_mul_periodic(seq, width, Bs=range(2, 10), Ss=range(1, 13)):
    """[(base, S, start, fams)]: every varying register follows v_{k+1} = B v_k + r_k with
    r_k of period S on seq[start:]; base = B^S; fams = [(p, family of seq[start+p::S] as
    [d, c] polynomials in X = base^j)]."""
    n = len(seq)
    cols = [[s[i] for s in seq] for i in range(width)]
    var = [i for i in range(width) if len(set(cols[i][n // 2:])) > 1]
    if not var:
        return []
    for S in Ss:
        need = 2 * S + 2
        if need + 1 > n:
            break
        for B in Bs:
            rs = {}
            for i in var:
                r = [cols[i][k + 1] - B * cols[i][k] for k in range(n - 1)]
                tail = r[-need:]
                if not all(tail[a] == tail[a + S] for a in range(len(tail) - S)):
                    break
                rs[i] = r
            else:
                start = n - 1 - need
                while start > 0 and all(rs[i][start - 1] == rs[i][start - 1 + S] for i in var):
                    start -= 1
                base = B ** S
                fams = []
                for p in range(S):
                    k = start + p
                    if k + S >= n:
                        break
                    fam = []
                    for i in range(width):
                        if i not in var:
                            fam.append(_pnorm_fr([Fraction(cols[i][k])]))
                            continue
                        C = sum(B ** (S - 1 - t) * rs[i][k + t] for t in range(S))
                        d = Fraction(-C, base - 1)
                        fam.append(_pnorm_fr([d, Fraction(cols[i][k]) - d]))
                    fams.append((p, fam))
                return [(base, S, start, fams)]
    return []


def _fit_mul_strided(seq, width, Ss=range(1, 13), Bmax=10 ** 6):
    """Like `_fit_mul_periodic`, for v_{k+S} = base*v_k + C_{k mod S} (any integer base)."""
    n = len(seq)
    cols = [[s[i] for s in seq] for i in range(width)]
    var = [i for i in range(width) if len(set(cols[i][n // 2:])) > 1]
    if not var:
        return []
    for S in Ss:
        if 3 * S + 1 > n:
            break
        base = None
        ok = True
        for i in var:
            v = cols[i]
            for k in range(n - 3 * S, n - 2 * S):
                d1, d2 = v[k + S] - v[k], v[k + 2 * S] - v[k + S]
                if d1 == 0 or d2 % d1 or (base is not None and d2 // d1 != base):
                    ok = False
                    break
                base = d2 // d1
            if not ok:
                break
        if not ok or base is None or base < 2 or base > Bmax:
            continue

        def holds(k):
            return all(cols[i][k + 2 * S] - base * cols[i][k + S]
                       == cols[i][k + S] - base * cols[i][k] for i in var)
        if not all(holds(k) for k in range(n - 3 * S, n - 2 * S)):
            continue
        start = n - 3 * S
        while start > 0 and holds(start - 1):
            start -= 1
        fams = []
        for p in range(S):
            k = start + p
            fam = []
            for i in range(width):
                if i not in var:
                    fam.append(_pnorm_fr([Fraction(cols[i][k])]))
                    continue
                d = Fraction(-(cols[i][k + S] - base * cols[i][k]), base - 1)
                fam.append(_pnorm_fr([d, Fraction(cols[i][k]) - d]))
            fams.append((p, fam))
        return [(base, S, start, fams)]
    return []


def _fit_all(seq, width, dmax):
    fam = []
    for i in range(width):
        p = _fit_poly([s[i] for s in seq], dmax)
        if p is None:
            return None
        fam.append(p)
    return fam


def _matches(fam, s, j):
    return all(_peval_fr(fam[i], j) == s[i] for i in range(len(s)))


def oned_stride_search(F, max_shapes=8, max_verify=60):
    """Search for a strided 1-D progress certificate (deterministic: at most `max_verify`
    candidate families are handed to the engine).  Returns a certificate in
    `oned_progress_cert`'s format plus 'stride', or None.  Used to build `_TABLE`."""
    width = len(F[0])
    budget = [max_verify]
    shapes = _shapes(F, width, 3000000, min_occ=5, max_occ=20000)
    if shapes is None:
        return None
    for _sh, occ in shapes[:max_shapes]:                                    # MUL
        seq = [s for _, s in occ]
        cands = _fit_mul_periodic(seq, width)
        cands += [c for c in _fit_mul_strided(seq, width)
                  if not any(c[0] == d[0] and c[1] == d[1] for d in cands)]
        for base, S, start, fams in cands:
            for p, fam in fams:
                budget[0] -= 1
                if budget[0] < 0:
                    return None
                res = _smart_M(lambda M: _verify_multiplicative(F, width, fam, base, _KW1,
                                                                Mmul=(M,)))
                if res is None:
                    continue
                Mp, X0, branches = res[1]
                sub = occ[start + p::S]
                body, body_t = [s for _, s in sub], [t for t, _ in sub]
                for kk, s in enumerate(body):
                    X = base ** kk
                    if X < X0:
                        continue
                    if tuple(int(_peval_fr(fam[i], X)) for i in range(width)) == tuple(s):
                        return {'flavour': 'mul', 'width': width, 'P': fam, 'B': base, 'M': Mp,
                                'X0': X0, 'branches': branches,
                                'anchors': _mul_anchors(fam, width, body, body_t, base, kk),
                                'stride': S}
                    break
    shapes = _shapes(F, width, 200000, min_occ=12)                         # ADD
    tried = set()
    for _sh, occ in shapes[:max_shapes]:
        for S in range(1, 13):
            for phase in range(S):
                sub = occ[phase::S]
                if len(sub) < 8:
                    continue
                k = len(sub) // 3
                seq = [s for _, s in sub]
                fam = _fit_all(seq[k:k + 24], width, 3)
                if fam is None or all(len(_pnorm_fr(p)) <= 1 for p in fam):
                    continue
                if not all(_matches(fam, seq[j], j - k) for j in range(k, len(seq))):
                    continue
                k0 = k
                while k0 > 0 and _matches(fam, seq[k0 - 1], k0 - 1 - k):
                    k0 -= 1
                body, body_t = seq[k0:], [t for t, _ in sub[k0:]]
                fam = _fit_all(body[:24], width, 3)
                key = tuple(tuple(p) for p in fam)
                if key in tried:
                    continue
                tried.add(key)
                budget[0] -= 1
                if budget[0] < 0:
                    return None
                res = _smart_M(lambda M: _verify_additive(F, width, fam, (M,), _KW1))
                if res is None:
                    continue
                M, u0, branches = res[1]
                if u0 >= len(body):
                    continue
                return {'flavour': 'add', 'width': width, 'P': fam, 'M': M, 'u0': u0,
                        'deg': max(len(_pnorm_fr(p)) - 1 for p in fam), 'branches': branches,
                        'anchors': _add_anchors(fam, width, body, body_t, u0,
                                                min(len(body) - 1, u0 + 3)),
                        'stride': S}
    return None


# ===========================================================================
# rebuilding a certificate from the table (deterministic)
# ===========================================================================

def _fr(s):
    return Fraction(s)


def _states_at(F, steps):
    """The concrete states after each step count in `steps` (from "2")."""
    width = len(F[0])
    want = sorted(set(steps))
    out = {}
    s = [0] * width
    s[0] = 1
    t = 0
    for w in want:
        while t < w:
            for rule in F:
                if all(s[i] + d >= 0 for i, d in enumerate(rule)):
                    break
            else:
                raise ValueError('machine halted during the bootstrap')
            s = [s[i] + d for i, d in enumerate(rule)]
            t += 1
        out[w] = tuple(s)
    return out


def _rebuild_1d(F, row):
    width = len(F[0])
    kind, stride, P = row[0], row[1], [[_fr(c) for c in p] for p in row[2]]
    if kind == 'add':
        M, anchors = row[3], row[4]
        res = _verify_additive(F, width, P, (M,), _KW1)
        if res is None:
            return None
        M, u0, branches = res
        st = _states_at(F, [t for _, t in anchors])
        anc = [(u, t, st[t]) for u, t in anchors]
        for u, t, s in anc:
            if tuple(int(_peval_fr(P[i], u)) for i in range(width)) != s:
                return None
        return {'flavour': 'add', 'width': width, 'P': P, 'M': M, 'u0': u0,
                'deg': max(len(_pnorm_fr(p)) - 1 for p in P), 'branches': branches,
                'anchors': anc, 'stride': stride}
    B, M, anchors = row[3], row[4], row[5]
    res = _verify_multiplicative(F, width, P, B, _KW1, Mmul=(M,))
    if res is None:
        return None
    Mp, X0, branches = res
    st = _states_at(F, [t for _, t in anchors])
    anc = [(X, t, st[t]) for X, t in anchors]
    for X, t, s in anc:
        if tuple(int(_peval_fr(P[i], X)) for i in range(width)) != s:
            return None
    return {'flavour': 'mul', 'width': width, 'P': P, 'B': B, 'M': Mp, 'X0': X0,
            'branches': branches, 'anchors': anc, 'stride': stride}


_KWN = dict(max_prim=2500, max_accel=200, max_configs=300, max_restart=24)


def _decode_allowed(rmod, h):
    if h is None:
        return None
    bits = int(h, 16)
    return {r for k, r in enumerate(itertools.product(*[range(M) for M in rmod]))
            if bits >> k & 1}


def _encode_allowed(rmod, allowed):
    if allowed is None:
        return None
    allowed = set(map(tuple, allowed))
    bits = 0
    for k, r in enumerate(itertools.product(*[range(M) for M in rmod])):
        if r in allowed:
            bits |= 1 << k
    return format(bits, 'x')


# ---------------------------------------------------------------------------
# 'ndx' rows: the N-D engine with a lazier loop-count bound
# ---------------------------------------------------------------------------
# `nd_progress.compute_V` bounds the repetition count V of an accelerated loop by
# floor(base_i / d_i) for EVERY register i the loop drains (d_i per cycle), and raises
# NeedModulus whenever one of these floors is not a clean affine form -- even for a register
# that never binds V.  A loop that drains x by 1 and y by 7 then refines the residue split by
# 7 although V = x (e.g. line 3, [1/105, 10/9, 27/55, 7/2, 6655/7]: the macro-step has period
# 22, but the stock engine asks for a split of 2*4*11*5*3*7 and gives up).
# `_compute_V_lazy` sets such a register aside, takes V = the uniform minimum of the clean
# bounds (as before), and then requires d_i * V <= base_i uniformly on the region (one
# `implies_ge0`), i.e. V <= floor(base_i / d_i).  If that fails, or there is no clean bound at
# all, it raises NeedModulus exactly as `compute_V` would.  So V is the same exact maximal
# cycle count whenever it is accepted; only unnecessary splits are avoided.  It is swapped
# into the engines only while an 'ndx' or 'ndcv' row is rebuilt (`_lazy_V`).

def _compute_V_lazy(F, hist, rules, p0, L, Dc, Phi, nvars, mode='x'):
    """`nd_progress.compute_V` with set-aside draining registers (see above).  The two modes
    are two independent implementations of the idea (agents A and B); they differ only in
    which registers a NeedModulus asks to refine, and both are kept so that every row
    rebuilds exactly as it was found and checked:
      'x'  (rows 'ndx'):  like `compute_V`, the first set-aside register that needs it;
      'cv' (rows 'ndcv'): all set-aside registers that fail, or, when there is no clean
                          bound at all, only a set-aside register that provably binds."""
    R = len(Dc)
    bounds = []
    lazy = []
    # (A) non-negativity of every draining register at every position/cycle
    for i in range(R):
        if Dc[i] < 0:
            col = [hist[t][i] for t in range(p0, p0 + L + 1)]
            base_i = _N.umin_forms(col, Phi, nvars)
            b = _N.clean_floor(base_i, -Dc[i])
            if b is None:
                lazy.append((i, base_i))
                continue
            bounds.append(b)
    # (B) higher-priority rules stay inapplicable (verbatim from compute_V)
    for j in range(L):
        rj = rules[p0 + j]
        state_j = hist[p0 + j]
        for rp in range(rj):
            rule = F[rp]
            perm = False
            wit = []
            for i, d in enumerate(rule):
                if d < 0:
                    val0 = _N.add(state_j[i], _N.const_form(d, nvars))
                    if _N.implies_le_neg1(Phi, nvars, val0):
                        if Dc[i] <= 0:
                            perm = True
                            break
                        neg = _N.sub(_N.const_form(-1, nvars), val0)
                        b = _N.clean_floor(neg, Dc[i])
                        if b is not None:
                            wit.append(b)
            if perm:
                continue
            if not wit:
                if mode == 'x':
                    for i, base_i in lazy:          # same exception order as compute_V
                        _N.clean_floor_or_modulus(base_i, -Dc[i])
                return None
            bounds.append(_N.umin_forms(wit, Phi, nvars))

    def need_for(items):
        need = {}
        for i, base_i in items:
            for k, a in enumerate(base_i[:-1]):
                if a % (-Dc[i]):
                    f = (-Dc[i]) // gcd(-Dc[i], a)
                    need[k] = need.get(k, 1) * f // gcd(need.get(k, 1), f)
        return need

    if not bounds:
        if mode == 'x':
            for i, base_i in lazy:
                _N.clean_floor_or_modulus(base_i, -Dc[i])
            return None
        if lazy:
            # a set-aside register that provably binds (base_i/d_i <= base_j/d_j for all j)
            # is the only one that needs a clean floor
            for i, bi in lazy:
                if all(_N.implies_ge0(Phi, nvars, _N.sub(_N.scale(bj, -Dc[i]), _N.scale(bi, -Dc[j])))
                       for j, bj in lazy if j != i):
                    raise _N.NeedModulus(need_for([(i, bi)]))
            raise _N.NeedModulus(need_for(lazy))
        return None
    V = _N.umin_forms(bounds, Phi, nvars)
    # V <= floor(base_i / d_i)  <=>  base_i - d_i*V >= 0 (uniformly on the region)
    bad = [(i, b) for i, b in lazy if not _N.implies_ge0(Phi, nvars, _N.add(b, _N.scale(V, Dc[i])))]
    if bad:
        if mode == 'x':
            _N.clean_floor_or_modulus(bad[0][1], -Dc[bad[0][0]])    # raises NeedModulus
        raise _N.NeedModulus(need_for(bad))
    return V


@contextmanager
def _lazy_V(mode):
    orig_n, orig_r = _N.compute_V, _R.compute_V

    def cv(F, hist, rules, p0, L, Dc, Phi, nvars):
        return _compute_V_lazy(F, hist, rules, p0, L, Dc, Phi, nvars, mode)
    _N.compute_V = _R.compute_V = cv
    try:
        yield
    finally:
        _N.compute_V, _R.compute_V = orig_n, orig_r


_KWX = dict(max_prim=20000, max_accel=2000, max_configs=3000, max_restart=40)


# ---------------------------------------------------------------------------
# 'ndz' / 'ndxz' / 'ndcvz' rows: the same, with an integer-tightened LP
# ---------------------------------------------------------------------------
# The engine decides every branch with exact RATIONAL Fourier-Motzkin, so after residue splits
# it can walk into slices that contain rational but no integer points (e.g. 12(m0 - m1) = 13)
# and fail there.  `_norm_int` replaces `nd_progress._norm` during the rebuild: a strict L > 0
# becomes L - 1 >= 0, and the variable part is divided by the gcd of its coefficients with the
# constant rounded down (a Chvatal-Gomory cut).  Every inequality FM derives holds at all
# integer points of the original system (the engine's variables are integers), so rounding it
# never loses one: "infeasible" still means "no integer point", which is what the engine needs.
# The translation uses the stock LP; Lean re-checks every leaf (integer-empty leaves are closed
# by `omega`).  (Written by agent D.)

def _norm_int(L, strict):
    L = list(L)
    if strict:
        L[-1] -= 1
    g = 0
    for a in L[:-1]:
        g = gcd(g, a)
    if g > 1:
        L = [a // g for a in L[:-1]] + [L[-1] // g]      # floor of the constant
    return (tuple(L), False)


@contextmanager
def _int_lp():
    orig = _N._norm
    _N._norm = _norm_int
    try:
        yield
    finally:
        _N._norm = orig


def _rebuild_nd(F, row):
    kind, pregs, consts, P, rmod, ah, mprod, split, boot_t = row
    width = len(F[0])
    nvars = len(pregs)
    consts = {int(k): v for k, v in consts.items()}
    allowed = _decode_allowed(rmod, ah)
    if kind in ('ndx', 'ndcv'):
        with _lazy_V('x' if kind == 'ndx' else 'cv'):
            res = verify_region_r(F, width, pregs, P, nvars, rmod, allowed, consts=consts,
                                  record=True, split_gates=split, max_moduli_product=mprod,
                                  **(_KWX if kind == 'ndx' else _KWN))
    else:
        res = verify_region_r(F, width, pregs, P, nvars, rmod, allowed, consts=consts,
                              record=True, split_gates=split, max_moduli_product=mprod, **_KWN)
    if not res['ok']:
        return None
    boot = _states_at(F, [boot_t])[boot_t]
    pt = [boot[r] for r in pregs]
    if any(boot[i] != consts.get(i, 0) for i in range(width) if i not in pregs):
        return None
    if any(sum(q[k] * pt[k] for k in range(nvars)) + q[-1] < 0 for q in res['P']):
        return None
    if res['allowed'] is not None and \
            tuple(pt[k] % res['rmod'][k] for k in range(nvars)) not in set(map(tuple, res['allowed'])):
        return None
    shape = tuple(i not in pregs and consts.get(i, 0) == 0 for i in range(width))
    cert = {'shape': shape, 'param_regs': pregs}
    if consts:
        cert['consts'] = consts
    cert.update({'nvars': nvars, 'P': res['P'], 'moduli': res['moduli'], 'rmod': res['rmod'],
                 'allowed': res['allowed'], 'region0': P, 'boot_t': boot_t,
                 'boot_state': list(boot), 'trees': res['trees']})
    return cert


def sz24_progress_cert(F):
    """The certificate for F (rebuilt from `_TABLE`, deterministically), or None.
    'kind' is '1d' or 'nd'."""
    row = _TABLE.get(unparse_line(F))
    if row is None:
        return None
    if row[0] in ('nd', 'ndx', 'ndcv'):
        c = _rebuild_nd(F, row)
        kind = 'nd'
    elif row[0] in ('ndz', 'ndxz', 'ndcvz'):
        with _int_lp():
            c = _rebuild_nd(F, (row[0][:-1],) + tuple(row[1:]))
        kind = 'nd'
    elif row[0] == 'val':
        c = _val_cert(F, row)
        kind = 'val'
    else:
        c = _rebuild_1d(F, row)
        kind = '1d'
    if c is not None:
        c['kind'] = kind
    return c


def sz24_progress(F):
    c = sz24_progress_cert(F)
    if c is None:
        return None
    if c['kind'] == '1d':
        return _O.cert_str(c)[:-1] + f",stride={c['stride']})"
    from decider.ndr_progress import cert_str
    return cert_str(c)


# ===========================================================================
# Lean: accelerated bootstrap for 1-D certificates
# ===========================================================================

_BOOT_MIN_K = 10


def _boot_cycle(F, W, maxneed, cyc, Dc, S0, K):
    """Plan `cycN` at the concrete state S0 for the largest k <= K it allows.

    A register is a literal if it does not move and could drop below its `maxneed` inside
    the block (it may then block a rule); every other register is `x + d*k + off` with `off`
    chosen as in `_try_cycle`, so that it never blocks anything.  None unless every
    higher-priority rule is blocked by a literal at every position."""
    L = len(cyc)
    pre = _OL._prefix_deltas(F, cyc, W)
    mu = [min(pre[t][i] for t in range(L)) for i in range(W)]
    lits, offs, k = {}, {}, K
    for i in range(W):
        if Dc[i] == 0 and S0[i] + mu[i] < maxneed[i]:
            lits[i] = S0[i]
            continue
        off = max(0, maxneed[i] - mu[i] - (-Dc[i] if Dc[i] < 0 else 0))
        if Dc[i] < 0:
            k = min(k, (S0[i] - off) // (-Dc[i]))
        elif S0[i] < off:
            return None
        offs[i] = off
    if k < 1:
        return None
    for t in range(L):
        rj = cyc[t]
        for i in range(W):
            if -F[rj][i] > 0 and i in lits and lits[i] + pre[t][i] < -F[rj][i]:
                return None
        for rp in range(rj):
            if not any(-F[rp][i] > 0 and i in lits and lits[i] + pre[t][i] < -F[rp][i]
                       for i in range(W)):
                return None
    xs = {i: S0[i] - (-Dc[i] * k if Dc[i] < 0 else 0) - offs[i] for i in offs}
    return {'k': k, 'lits': lits, 'offs': offs, 'xs': xs, 'cyc': list(cyc), 'Dc': list(Dc)}


def _boot_blocks(F, W, maxneed, steps, Lmax=48):
    """The run of `steps` steps from c₀ as blocks (src, dst, kind, payload): 'steps'
    (payload: a count <= 100) or 'cycle' (payload: a `_boot_cycle` plan).  Follows the real
    trajectory exactly."""
    s = [1] + [0] * (W - 1)
    blocks = []
    t = 0
    seg_start, seg_rules, hist = list(s), [], [list(s)]

    def flush(upto):
        nonlocal seg_start
        cur, pos = seg_start, 0
        while pos < upto:
            n = min(_OL._CHUNK, upto - pos)
            blocks.append((cur, hist[pos + n], 'steps', n))
            cur = hist[pos + n]
            pos += n
        seg_start = cur

    while t < steps:
        j, s2 = _OL._concrete_step(F, s)
        if j < 0:
            raise _OL._Fail
        seg_rules.append(j)
        hist.append(s2)
        s = s2
        t += 1
        L = _O._detect_period(seg_rules, Lmax)
        if not L:
            continue
        p0 = len(seg_rules) - 2 * L
        S0 = hist[p0]
        cyc = seg_rules[p0:p0 + L]
        Dc = [hist[p0 + L][i] - S0[i] for i in range(W)]
        if all(d == 0 for d in Dc):
            continue
        t0 = t - 2 * L
        K, cur = 0, list(S0)            # full repetitions the real run makes from S0
        while t0 + (K + 1) * L <= steps:
            nxt = cur
            for r in cyc:
                jj, nxt = _OL._concrete_step(F, nxt)
                if jj != r:
                    break
            else:
                cur = nxt
                K += 1
                continue
            break
        plan = _boot_cycle(F, W, maxneed, cyc, Dc, S0, K)
        if plan is None or plan['k'] < _BOOT_MIN_K:
            continue
        flush(p0)
        dst = [S0[i] + plan['k'] * Dc[i] for i in range(W)]
        blocks.append((list(S0), dst, 'cycle', plan))
        s = list(dst)
        t = t0 + plan['k'] * L
        seg_start, seg_rules, hist = list(s), [], [list(s)]
    flush(len(seg_rules))
    return blocks


def _boot_fast(F, W, steps, st, em):
    """`c₀ [fm]⊢* <anchor>` like `oned_progress_to_lean._boot`, but every loop of at least
    `_BOOT_MIN_K` cycles is one application of a cycle lemma of `em` (shared with the branch
    proofs; hypotheses are numeral identities closed by `rfl`).  Each block is its own
    top-level theorem, left-associated.  A 195 051-step bootstrap becomes ~850 blocks."""
    blocks = _boot_blocks(F, W, em.maxneed, steps)
    end = blocks[-1][1] if blocks else [1] + [0] * (W - 1)
    if ', '.join(map(str, end)) != st:
        raise _OL._Fail
    thms, last = [], None
    for n, (src, dst, kind, pay) in enumerate(blocks):
        if kind == 'steps':
            pf = f'(by execute fm {pay})'
        else:
            name, xs = em.cycle_lemma(pay)
            args = [str(pay['k'])] + [str(pay['xs'][i]) for i in xs]
            args += [str(v) for v in src] + [str(v) for v in dst] + ['rfl'] * (2 * W)
            pf = f'({name} {" ".join(args)})'
        body = pf if last is None else f'stepStar_trans {last} {pf}'
        thms.append(f'theorem boot{n} : (c₀ : Q) [fm]⊢* ⟨{", ".join(map(str, dst))}⟩ := '
                    f'{body}\n')
        last = f'boot{n}'
    term = last if last is not None else '(by exists 0)'
    return thms, [f'  exact stepStar_not_halts_not_halts (c₂ := ⟨{st}⟩) {term} key']


@contextmanager
def _fast_boot():
    """For the duration of the block, `oned_progress_to_lean` emits `_boot_fast`
    bootstraps.  (Its builders create one `_Emitter` and then call `_boot`; the patched
    emitter remembers itself so that `_boot` can use its cycle lemmas.)"""
    orig_boot, orig_em = _OL._boot, _OL._Emitter
    cur = []

    class _Em(orig_em):
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            cur.append(self)

    _OL._Emitter = _Em
    _OL._boot = lambda F, W, steps, st: _boot_fast(F, W, steps, st, cur[-1])
    try:
        yield
    finally:
        _OL._boot, _OL._Emitter = orig_boot, orig_em


# per-machine options of `nd_progress_to_lean` (declarations over the default heartbeats)
_LEAN_OPTIONS = {
    '[1/30, 5/9, 297/35, 2/11, 1715/2]': {'fast_boot': True},
    '[1/90, 4/21, 33/2, 25/3, 7/11, 2/5]': {'fast_boot': True},
    '[11/105, 2/3, 567/55, 5/2, 63/5]': {'fast_boot': True},
    '[11/105, 4/3, 15/22, 49/2, 198/7]': {'fast_boot': True},
    '[11/105, 5/66, 16/5, 21/2, 25/7]': {'fast_boot': True},
    '[11/105, 567/55, 2/3, 5/2, 63/5]': {'fast_boot': True},
    '[11/1575, 343/33, 10/7, 9/2, 7/3]': {'fast_boot': True},
    '[11/1575, 6/7, 343/55, 25/2, 7/5]': {'fast_boot': True},
    '[14/15, 1/66, 63/2, 121/3, 5/7, 3/11]': {'fast_boot': True},
    '[2/105, 5/66, 2401/2, 33/7, 4/11]': {'fast_boot': True},
    '[22/105, 297/10, 245/2, 5/11, 2/7]': {'fast_boot': True},
    '[25/18, 22/35, 1029/2, 3/11, 15/7]': {'fast_boot': True},
    '[28/15, 9/154, 35/2, 11/5, 50/11]': {'fast_boot': True},
    '[35/6, 28/605, 1331/2, 3/7, 15/11]': {'fast_boot': True},
    '[35/6, 8/55, 1001/2, 51/7, 2/221]': {'max_heartbeats': 1000000},
    '[4/15, 1/126, 33/2, 49/3, 5/11, 2/7]': {'fast_boot': True},
    '[4/15, 9/14, 605/2, 7/5, 50/77]': {'fast_boot': True},
    '[4/15, 9/154, 245/2, 11/5, 50/11]': {'fast_boot': True},
    '[5/6, 1/70, 484/5, 7/2, 3/11, 25/7]': {'fast_boot': True},
    '[63/10, 2431/2, 28/429, 5/7, 3/17]': {'max_heartbeats': 1000000},
    '[63/10, 25/231, 14/3, 11/2, 12/11]': {'fast_boot': True},
    '[63/10, 28/33, 2431/2, 5/7, 3/221]': {'max_heartbeats': 1000000, 'fast_boot': True},
    '[7/15, 1/42, 1089/7, 2/3, 5/11, 49/2]': {'fast_boot': True},
    '[7/15, 2/3, 99/14, 5/11, 33/2, 21/5]': {'fast_boot': True},
    '[7/30, 11/2, 80/21, 3/11, 20/3]': {'fast_boot': True},
    '[7/30, 11/3, 405/14, 2/11, 45/2]': {'fast_boot': True},
    '[7/30, 1331/2, 40/63, 3/11, 7/3]': {'fast_boot': True},
    '[7/30, 14641/3, 9/35, 10/11, 15/2]': {'fast_boot': True},
    '[7/30, 2/231, 14641/2, 15/11, 4/5]': {'fast_boot': True},
    '[7/30, 40/63, 121/2, 9/11, 7/3]': {'fast_boot': True},
    '[7/30, 40/63, 1331/2, 3/11, 7/3]': {'fast_boot': True},
    '[7/30, 405/14, 11/3, 2/11, 45/2]': {'fast_boot': True},
    '[7/30, 5/231, 16/7, 33/2, 49/11]': {'fast_boot': True},
    '[7/30, 80/21, 11/2, 3/11, 20/3]': {'fast_boot': True},
    '[7/30, 88/21, 275/2, 3/55, 7/5]': {'fast_boot': True},
    '[7/30, 9/35, 14641/3, 10/11, 15/2]': {'fast_boot': True},
    '[7/90, 9/2, 88/21, 5/11, 35/3]': {'fast_boot': True},
    '[77/30, 297/35, 20/7, 5/11, 7/2]': {'fast_boot': True},
    '[8/15, 33/14, 715/2, 119/11, 2/221]': {'max_heartbeats': 1000000},
    '[8/15, 33/14, 715/2, 119/11, 3/221]': {'max_heartbeats': 1000000},
    '[9/10, 25/231, 98/3, 11/2, 12/11]': {'fast_boot': True},
    '[9/70, 2/15, 16807/2, 5/7, 21/5]': {'fast_boot': True},
    '[9/70, 2/15, 16807/2, 5/7, 4/5]': {'fast_boot': True},
    '[9/70, 2/15, 16807/2, 5/7, 6/5]': {'fast_boot': True},
    '[9/70, 4/165, 539/2, 5/7, 9/5]': {'fast_boot': True},
    '[9/70, 7/15, 32/7, 5/2, 21/5]': {'fast_boot': True},
    '[9/70, 7/15, 32/7, 5/2, 6/5]': {'fast_boot': True},
}


_RE_CYC = re.compile(r'\bcyc(\d+)')


def _boot_nd_fast(F, W, steps, st):
    """`_boot_fast` for `nd_progress_to_lean`: a private 1-D emitter supplies the cycle
    lemmas, renamed `cycN` -> `bcycN` (the N-D emitter has its own `cycN`), and they are
    emitted just before the bootstrap theorems.  (Written by agent C.)"""
    maxneed = [max([0] + [-r[i] for r in F]) for i in range(W)]
    em = _OL._Emitter(F, W, maxneed)
    thms, lines = _boot_fast(F, W, steps, st, em)
    lem = [_RE_CYC.sub(r'bcyc\1', t) for t in em.order]
    thms = [_RE_CYC.sub(r'bcyc\1', t) for t in thms]
    return lem + thms, lines


@contextmanager
def _nd_fast_boot():
    """For the duration of the block, `nd_progress_to_lean` emits `_boot_nd_fast`
    bootstraps."""
    orig = _NL._boot
    _NL._boot = _boot_nd_fast
    try:
        yield
    finally:
        _NL._boot = orig


def sz24_progress_to_lean(F, cert, name='Foo'):
    """The Lean file (a string) proving ¬halts for F from `sz24_progress_cert(F)`.
    N-D options (`_LEAN_OPTIONS`): `max_heartbeats` is passed to `nd_progress_to_lean`;
    `fast_boot` emits the bootstrap with cycle lemmas (`_boot_nd_fast`)."""
    if cert['kind'] == '1d':
        c = {k: v for k, v in cert.items() if k != 'kind'}
        with _fast_boot():
            return _OL.oned_progress_to_lean(F, c, name)
    if cert['kind'] == 'val':
        return _val_to_lean(F, cert, name)
    c = {k: v for k, v in cert.items() if k != 'kind'}
    opts = dict(_LEAN_OPTIONS.get(unparse_line(F), {}))
    if opts.pop('fast_boot', False):
        with _nd_fast_boot():
            return nd_progress_to_lean(F, c, name, **opts)
    return nd_progress_to_lean(F, c, name, **opts)


# ===========================================================================
# 'val' rows: valuation-chain certificates  (written by agent G)
# ===========================================================================
# Lines 1294-1297, 1838, 1839, 3010, 3011, 3568, 3570 have a shape Y(x, e) with two affine
# macro steps chosen by the parity of x:
#     x even:  Y(x, e) |-+ Y(x', e - 1),   2 x' = 3 x + kappa      (x + kappa -> 3(x + kappa)/2)
#     x odd:   Y(x, e) |-+ Y(x', e'),      2 x' = ao x + bo,  2 e' = 2 e + co x + do
# A run of even steps has length v2(x + kappa) and costs one unit of e each; the machine halts iff
# e runs out inside such a run.  The invariant e > v2(x + kappa), i.e.
#     J(x, e) := forall k, 2^k | x + kappa -> k + 1 <= e,   Inv'(x, e) := X0 <= x /\ 1 <= e /\ J(x, e),
# is neither polyhedral nor a residue condition.
#   * even step: 2^k | x' + kappa gives 2^(k+1) | 3(x + kappa), hence 2^(k+1) | x + kappa (3 is
#     odd), so k + 2 <= e, i.e. k + 1 <= e - 1 = e'  (Lean lemma `inv_even`);
#   * odd step: 2^k | x' + kappa gives 2^k <= x' + kappa, and k <= 6 or 8k <= 2^k (`pow_bound`), so
#     linear side conditions on the region suffice (`inv_odd`, `omega`); `_val_odd_ok` pre-checks them.
# The macro steps are proved per residue class of x by the stock engine (`verify_config`) on
# {X0 <= x, 1 <= e}, with a target test that accepts the first return to the shape; every leaf must
# end exactly at the declared map.  The Lean file is the stock `nd_progress_to_lean` translation, run
# with two temporary patches (restored afterwards, guarded by assertions on the translator's source):
# a leaf proves membership of its end state with `inv_even`/`inv_odd`, and the planner's polyhedral
# end-state check is skipped (membership is the lemmas' job); then the polyhedral `Inv` is replaced
# by `J`/`Inv'`, the lemmas are inserted, and the bootstrap membership uses `pow_bound` + `omega`.
# Only the invariant changes; the machine, `c₀` and the statement `nonhalt : ¬halts fm c₀` are the
# stock ones, and Lean checks everything.
# Row: ('val', px, pe, consts, kappa, X0, [ao, bo, co, do], boot_t, lazy).

_KWV = dict(max_prim=20000, max_accel=2000, max_configs=3000)


# ---------------------------------------------------------------------------
# engine: macro steps per residue class of x, target = first return to the shape
# ---------------------------------------------------------------------------

def _val_region(X0, ix, ie):
    P = [[0, 0, 0], [0, 0, 0]]
    P[0][ix] = 1; P[0][2] = -X0
    P[1][ie] = 1; P[1][2] = -1
    return P


def _val_verify_class(F, W, pregs, P, subst, consts, out):
    zero_regs = [i for i in range(W) if i not in pregs]
    regs = [_N.const_form(consts.get(i, 0), 2) for i in range(W)]
    for k, pr in enumerate(pregs):
        regs[pr] = list(subst[k])
    Phi = [(_N._compose(q, subst, 2), False) for q in P]
    st = _N.feasible(Phi, 2)
    if st == _N.INFEAS:
        out['kind'] = 'empty'
        return 'ok'
    if st == _N.UNKNOWN:
        return 'fail'

    def target_test(cur, Phi):
        for i in zero_regs:
            f = cur[i] if i not in consts else _N.add(cur[i], _N.const_form(-consts[i], 2))
            if not _N.uniform_zero(Phi, 2, f):
                return False
        return True

    bud = _N.Budget(**_KWV)
    try:
        ok = _N.verify_config(F, regs, [list(regs)], [], Phi, 2, target_test, False, bud, 48,
                             node=out, ev=[])
    except _N.NeedAssume as e:
        return ('assume', list(e.g))
    except _N.NeedModulus as e:
        return ('modulus', dict(e.need))
    return 'ok' if ok else 'fail'


def _val_leaf_list(node, out):
    if node['kind'] == 'split':
        _val_leaf_list(node['ge'], out); _val_leaf_list(node['le'], out)
    else:
        out.append(node)


def _val_macro_trees(F, px, pe, consts, X0, maps, kappa, lazy=None, max_mod=64):
    """Per residue class (moduli refined on demand), the engine's tree; checks every leaf
    against the declared maps.  Returns (moduli, trees) or None."""
    W = len(F[0])
    pregs = sorted([px, pe]); ix = pregs.index(px); ie = pregs.index(pe)
    P = _val_region(X0, ix, ie)
    ao, bo, co, do = maps
    moduli = [1, 1]; moduli[ix] = 2
    ctx = _lazy_V(lazy) if lazy else _val_null()
    with ctx:
        for _ in range(12):
            trees = {}
            restart = False
            for res in itertools.product(*[range(M) for M in moduli]):
                subst = []
                for k in range(2):
                    f = _N.const_form(res[k], 2); f[k] = moduli[k]; subst.append(f)
                out = {}
                r = _val_verify_class(F, W, pregs, P, subst, consts, out)
                if r == 'ok':
                    trees[res] = out
                    continue
                if isinstance(r, tuple) and r[0] == 'modulus':
                    for k, fac in r[1].items():
                        moduli[k] *= fac
                    if max(moduli) > max_mod:
                        return None
                    restart = True
                    break
                return None
            if not restart:
                break
        else:
            return None
    # every leaf ends at the declared map
    for res, t in trees.items():
        leaves = []
        _val_leaf_list(t, leaves)
        par = res[ix] % 2
        xf = [0, 0, res[ix]]; xf[ix] = moduli[ix]      # x, e as forms over m
        ef = [0, 0, res[ie]]; ef[ie] = moduli[ie]
        for lf in leaves:
            if lf['kind'] == 'empty':
                continue
            if lf['events'] and lf['events'][-1][0] == 'loop':
                return None
            end = lf['end']
            x2, e2 = end[px], end[pe]
            if any(end[i] != _N.const_form(consts.get(i, 0), 2) for i in range(W) if i not in pregs):
                return None
            if par == 0:
                ok = all(2 * x2[j] == 3 * xf[j] + (kappa if j == 2 else 0) for j in range(3)) and \
                    all(e2[j] == ef[j] - (1 if j == 2 else 0) for j in range(3))
            else:
                ok = all(2 * x2[j] == ao * xf[j] + (bo if j == 2 else 0) for j in range(3)) and \
                    all(2 * e2[j] == 2 * ef[j] + co * xf[j] + (do if j == 2 else 0) for j in range(3))
            if not ok:
                return None
    return moduli, trees


@contextmanager
def _val_null():
    yield


def _val_odd_ok(X0, kappa, maps):
    """The linear side conditions of `inv_odd` on {x >= X0 odd, e >= 1}: x' >= X0, e' >= 7,
    (x' + kappa) <= 8 (e' - 1).  With 2x' = ao x + bo, 2e' = 2e + co x + do; the worst case
    is e = 1 and, the forms being affine in x, x = X0 and x -> infinity."""
    ao, bo, co, do = maps
    for x in (X0, X0 + 1):
        if (ao * x + bo) % 2 or (2 + co * x + do) % 2:
            continue
        xp = (ao * x + bo) // 2; ep = (2 + co * x + do) // 2
        if xp < X0 or ep < 7 or xp + kappa > 8 * (ep - 1):
            return False
    # slopes: x' grows like ao/2, 8 e' like 4 co
    return ao >= 2 and 4 * co >= ao / 2 * 1 and co >= 0


def _val_boot_ok(x0, e0, X0, kappa):
    return x0 >= X0 and e0 >= 7 and x0 + kappa <= 8 * (e0 - 1)


# ---------------------------------------------------------------------------
# certificate
# ---------------------------------------------------------------------------

def _val_cert(F, row):
    kind, px, pe, consts, kappa, X0, maps, boot_t, lazy = row
    assert kind == 'val'
    consts = {int(k): v for k, v in consts.items()}
    W = len(F[0])
    pregs = sorted([px, pe])
    if not _val_odd_ok(X0, kappa, tuple(maps)):
        return None
    mt = _val_macro_trees(F, px, pe, consts, X0, tuple(maps), kappa, lazy)
    if mt is None:
        return None
    moduli, trees = mt
    boot = _states_at(F, [boot_t])[boot_t]
    if any(boot[i] != consts.get(i, 0) for i in range(W) if i not in pregs):
        return None
    if not _val_boot_ok(boot[px], boot[pe], X0, kappa):
        return None
    ix = pregs.index(px); ie = pregs.index(pe)
    shape = tuple(i not in pregs and consts.get(i, 0) == 0 for i in range(W))
    c = {'shape': shape, 'param_regs': pregs}
    if consts:
        c['consts'] = consts
    c.update({'nvars': 2, 'P': _val_region(X0, ix, ie), 'moduli': moduli, 'rmod': [1, 1],
              'allowed': None, 'region0': _val_region(X0, ix, ie), 'boot_t': boot_t,
              'boot_state': list(boot), 'trees': trees,
              'val': {'px': px, 'pe': pe, 'ix': ix, 'ie': ie, 'kappa': kappa, 'X0': X0,
                      'maps': tuple(maps)}})
    return c


# ---------------------------------------------------------------------------
# Lean
# ---------------------------------------------------------------------------

_VAL_PLAN_OLD = "raise _Planning('end state outside the invariant')"
_VAL_HOOK_OLD = "mem = f'⟨{\", \".join(_paren(x) for x in xprime)}, rfl, by omega⟩'"
_VAL_HOOK_NEW = "mem = f'⟨{\", \".join(_paren(x) for x in xprime)}, rfl, {_VAL_MEM(cx, lf, xprime)}⟩'"


def _val_mem(V):
    def mem(cx, lf, xprime):
        par = lf.rkey[V['ix']] % 2 if cx.moduli[V['ix']] % 2 == 0 else None
        if par is None:
            raise _NL.TranslationError('x modulus is odd')
        xp, ep = xprime[V['ix']], xprime[V['ie']]
        lem = 'inv_even' if par == 0 else 'inv_odd'
        return f"{lem} (x' := {xp}) (e' := {ep}) _h (by omega) (by omega)" + \
            (' (by omega)' if par == 0 else '')
    return mem


def _val_lemmas(V, pn):
    kappa, X0 = V['kappa'], V['X0']
    ao, bo, co, do = V['maps']
    sgn = lambda v: f'+ {v}' if v >= 0 else f'- {-v}'
    odd_x = f'2 * x\' = {ao} * x + {bo}' if bo >= 0 else f'2 * x\' + {-bo} = {ao} * x'
    odd_e = f'2 * e\' = 2 * e + {co} * x + {do}' if do >= 0 else f'2 * e\' + {-do} = 2 * e + {co} * x'
    return f'''
/-- `pow_bound`: used to bound the 2-adic valuation linearly. -/
theorem pow_bound : ∀ k : ℕ, k ≤ 6 ∨ 8 * k ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => left; omega
  | succ k ih =>
    rcases (by omega : k ≤ 5 ∨ k = 6 ∨ 7 ≤ k) with hk | rfl | hk
    · left; omega
    · right; norm_num
    · rcases ih with h | h
      · omega
      · right
        have h2 : 8 ≤ 2 ^ k :=
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ]; omega

/-- The even macro step keeps the invariant: x + {kappa} ↦ 3(x + {kappa})/2, e ↦ e - 1. -/
theorem inv_even {{x e x' e' : ℕ}} (h : Inv' x e) (h0 : x % 2 = 0) (h1 : 2 * x' = 3 * x + {kappa})
    (h2 : e' + 1 = e) : Inv' x' e' := by
  obtain ⟨hx, he, hJ⟩ := h
  have hJ1 := hJ 1 ⟨(x + {kappa}) / 2, by omega⟩
  refine ⟨by omega, by omega, ?_⟩
  intro k hk
  have h3 : 2 ^ (k + 1) ∣ (x + {kappa}) * 3 := by
    obtain ⟨c, hc⟩ := hk
    exact ⟨c, by rw [show (x + {kappa}) * 3 = 2 * (x' + {kappa}) by omega, hc, pow_succ]; ring⟩
  have h4 : 2 ^ (k + 1) ∣ x + {kappa} :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (by decide)) h3
  have := hJ (k + 1) h4
  omega

/-- The odd macro step keeps the invariant (a linear bound on the valuation suffices). -/
theorem inv_odd {{x e x' e' : ℕ}} (h : Inv' x e) (h1 : {odd_x}) (h2 : {odd_e}) :
    Inv' x' e' := by
  obtain ⟨hx, he, hJ⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  intro k hk
  have hle := Nat.le_of_dvd (by omega) hk
  rcases pow_bound k with hb | hb
  · omega
  · generalize 2 ^ k = P at hle hb
    omega
'''


def _val_inv_lines(V, pn):
    """`J`, the 2-parameter invariant `Inv'` over (x, e), and `Inv` in the translator's
    parameter order."""
    kappa, X0 = V['kappa'], V['X0']
    xn, en = pn[V['ix']], pn[V['ie']]
    return [
        '/-- `J x e`: e exceeds the 2-adic valuation of x + %d. -/' % kappa,
        f'def J (x e : ℕ) : Prop := ∀ k, 2 ^ k ∣ x + {kappa} → k + 1 ≤ e',
        '',
        '/-- The invariant, over (x, e). -/',
        f'abbrev Inv\' (x e : ℕ) : Prop := {X0} ≤ x ∧ 1 ≤ e ∧ J x e',
        '',
        '/-- The invariant region (in the order of the shape\'s registers). -/',
        f'abbrev Inv ({" ".join(pn)} : ℕ) : Prop := Inv\' {xn} {en}',
    ]


def _val_to_lean(F, c, name):
    V = c['val']
    cc = {k: v for k, v in c.items() if k not in ('val', 'kind')}
    src = inspect.getsource(_NL._emit_leaf)
    assert _VAL_HOOK_OLD in src
    orig = _NL._emit_leaf
    exec(src.replace(_VAL_HOOK_OLD, _VAL_HOOK_NEW), _NL.__dict__)
    _NL._VAL_MEM = _val_mem(V)
    # the end state of an even step may leave the polyhedral region (e - 1 = 0): its
    # membership is proved by `inv_even`/`inv_odd`, so the planner's check is dropped
    psrc = textwrap.dedent(inspect.getsource(_NL._Leaf.plan))
    assert _VAL_PLAN_OLD in psrc
    orig_plan = _NL._Leaf.plan
    exec(psrc.replace(_VAL_PLAN_OLD, 'pass'), _NL.__dict__)
    _NL._Leaf.plan = _NL.__dict__.pop('plan')
    try:
        with _nd_fast_boot():
            text = _NL.nd_progress_to_lean(F, cc, name)
    finally:
        _NL._emit_leaf = orig
        _NL._Leaf.plan = orig_plan
        _NL.__dict__.pop('_VAL_MEM', None)
    lines = text.split('\n')
    i = next(k for k, l in enumerate(lines) if l.startswith('abbrev Inv ('))
    pn = lines[i][len('abbrev Inv ('):lines[i].index(' : ℕ)')].split()
    pn = [p.lstrip('_') for p in pn]
    j = next(k for k, l in enumerate(lines) if l.startswith('abbrev Pr '))
    lines = lines[:i - 1] + _val_inv_lines(V, pn) + [''] + [lines[j]] + _val_lemmas(V, pn).split('\n') + lines[j + 1:]
    text = '\n'.join(lines)
    # bootstrap membership
    x0 = [c['boot_state'][r] for r in c['param_regs']]
    old = f'    · exact ⟨{", ".join(map(str, x0))}, rfl, by omega⟩'
    assert old in text, 'boot membership line not found'
    bx, be = x0[V['ix']], x0[V['ie']]
    new = (f'    · refine ⟨{", ".join(map(str, x0))}, rfl, by norm_num, by norm_num, ?_⟩\n'
           f'      intro k hk\n'
           f'      have hle := Nat.le_of_dvd (by norm_num) hk\n'
           f'      rcases pow_bound k with hb | hb\n'
           f'      · omega\n'
           f'      · generalize 2 ^ k = P at hle hb\n'
           f'        omega')
    text = text.replace(old, new)
    text = text.replace('This file was generated by `decider/nd_progress_to_lean.py` from the',
                        'This file was generated by `decider/sz24_progress.py` (valuation-chain invariant\n'
                        '`Inv\'` below) and `decider/nd_progress_to_lean.py` (macro steps) from the')
    return text


# ===========================================================================
# the table
# ===========================================================================
# 1-D rows: ('add', stride, P, M, [(u, steps)])  or  ('mul', stride, P, B, M, [(X, steps)])
#           P: one polynomial per register, coefficients as strings (Fractions)
# N-D rows: ('nd', param_regs, consts, P, rmod, allowed (hex bitmask over the residue
#            vectors in itertools.product order, or None), max_moduli_product,
#            split_gates, boot_t)
#           kind 'ndx': the same, rebuilt with `_lazy_V` and the larger budgets `_KWX`
#           kind 'ndcv': the same, rebuilt with `_lazy_V('cv')` and the budgets `_KWN`
#           kinds 'ndz' / 'ndxz' / 'ndcvz': 'nd' / 'ndx' / 'ndcv' rebuilt with `_int_lp`
# 'val' rows: ('val', px, pe, consts, kappa, X0, [ao, bo, co, do], boot_t, lazy), see above

_TABLE = {
    '[1/105, 10/3, 27/22, 7/2, 33/5, 3/7]': ('add',4,[['1','6'],[],['1','8'],[],[]],3,[[17,17394],[18,19497],[19,21720],[20,24063]]),  # line 1
    '[1/105, 10/3, 9/55, 7/2, 1331/7, 5/11]': ('ndx',[4],{},[[1,-3],[1,-6],[1,-8],[1,-11],[1,-14],[1,-17],[1,-20],[1,-36],[1,-37],[1,-38],[1,-39],[1,-40],[1,-41],[1,-42],[1,-43],[1,-44]],[1],None,1000,False,160),  # line 2
    '[1/105, 10/9, 27/55, 7/2, 6655/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-1],[0,1,-6],[0,1,-14],[0,1,-22],[0,1,-28],[0,1,-36],[0,1,-44],[0,1,-88],[0,1,-89],[0,1,-90],[0,1,-91],[0,1,-92],[0,1,-93],[0,1,-94],[0,1,-95],[0,1,-96],[0,1,-97],[0,1,-98],[0,1,-99],[0,1,-100],[0,1,-101],[0,1,-102],[0,1,-103],[0,1,-104],[0,1,-106]],[1,1],None,3000,False,1592),  # line 3
    '[1/105, 10/99, 11/5, 567/2, 25/3]': ('ndcv',[1,3],{},[[1,0,-4],[0,1,-1],[1,-2,-5],[1,0,-12],[1,0,-16],[0,1,-8],[0,1,-9]],[1,1],None,400,True,178),  # line 4
    '[1/105, 11/3, 6/275, 4375/2, 9/5]': ('ndcv',[2,3],{},[[1,0,-4],[0,1,-1],[1,-2,-5],[1,0,-12],[1,0,-16],[0,1,-8],[0,1,-9]],[1,1],None,400,True,178),  # line 5
    '[1/105, 11/45, 10/11, 567/2, 25/3]': ('ndcv',[1,3],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[1,0,-14],[1,0,-18],[0,1,-8],[0,1,-9]],[1,1],None,400,True,196),  # line 6
    '[1/105, 121/3, 36/143, 5/121, 273/2]': ('nd',[0,4,3],{},[[1,0,0,-4],[0,1,0,-7],[0,0,1,-1],[2,-1,0,-16]],[1,1,1],None,3000,'all',160),  # line 8
    '[1/105, 189/110, 2/3, 35/2, 99/7]': ('ndx',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,3],[0,0,1,-4],[0,1,0,-4]],[1,1,1],None,1000,True,99),  # line 9
    '[1/105, 2/3, 189/110, 35/2, 99/7]': ('ndx',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,3],[0,0,1,-4],[0,1,0,-4]],[1,1,1],None,400,True,99),  # line 10
    '[1/105, 22/45, 5/11, 567/2, 121/3]': ('ndcv',[1,3],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,234),  # line 11
    '[1/105, 22/45, 5/11, 567/2, 25/3]': ('ndcv',[1,3],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[1,0,-14],[1,0,-18],[0,1,-8],[0,1,-9]],[1,1],None,400,True,196),  # line 12
    '[1/105, 22/45, 5/11, 567/2, 55/3]': ('ndcv',[1,3],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,215),  # line 13
    '[1/105, 242/3, 27/143, 5/121, 273/2]': ('nd',[0,3,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-2],[0,0,0,1,-1],[2,0,-1,0,-4],[0,0,1,0,-4],[0,0,1,0,-10]],[1,1,1,1],None,3000,True,33),  # line 14
    '[1/105, 242/3, 9/143, 5/121, 273/2]': ('nd',[0,3,4],{},[[0,1,0,-1],[-1,-3,1,1],[1,3,-1,-1],[1,0,0,-20],[1,-10,0,0]],[1,1,1],None,1000,True,257),  # line 15
    '[1/105, 27/143, 242/3, 5/121, 273/2]': ('nd',[0,2,3,5],{'1': 1},[[1,0,0,0,-2],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[1,-1,0,0,-2],[2,0,-3,0,0],[0,1,0,0,-4]],[1,1,1,1],None,3000,True,53),  # line 17
    '[1/105, 27/55, 10/9, 7/2, 6655/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[0,1,-6],[0,1,-14],[0,1,-22],[0,1,-28],[0,1,-36],[0,1,-44],[0,1,-88],[0,1,-89],[0,1,-90],[0,1,-91],[0,1,-92],[0,1,-93],[0,1,-94],[0,1,-95],[0,1,-96],[0,1,-97],[0,1,-98],[0,1,-99],[0,1,-100],[0,1,-101],[0,1,-102],[0,1,-103],[0,1,-104],[0,1,-106]],[1,1],None,3000,False,1592),  # line 19
    '[1/105, 3/11, 22/75, 4375/2, 9/5]': ('ndcv',[2,3],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,196),  # line 20
    '[1/105, 36/143, 121/3, 5/121, 273/2]': ('nd',[0,4,3],{},[[1,0,0,-4],[0,1,0,-7],[0,0,1,-1],[2,-1,0,-16]],[1,1,1],None,3000,'all',160),  # line 21
    '[1/105, 5/9, 54/55, 7/2, 6655/7]': ('ndx',[0,2],{},[[1,0,-90],[0,1,-46],[-1,2,0],[1,-2,2],[0,1,-47],[0,1,-48],[0,1,-49],[0,1,-50],[0,1,-51],[0,1,-52],[0,1,-53],[0,1,-54]],[1,1],None,300,False,2806),  # line 22
    '[1/105, 54/55, 5/9, 7/2, 6655/7]': ('ndx',[0,1],{},[[1,0,-3],[0,1,-4],[1,-1,2],[-1,1,-2],[0,1,-8],[0,1,-16],[0,1,-24],[0,1,-30],[0,1,-38],[0,1,-46],[0,1,-88],[0,1,-111]],[1,1],None,1000,False,2744),  # line 23
    '[1/105, 6/11, 11/75, 4375/2, 9/5]': ('ndcv',[2,3],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,196),  # line 24
    '[1/105, 9/143, 242/3, 5/121, 273/2]': ('nd',[0,4,3],{},[[1,0,0,-4],[0,1,0,-7],[0,0,1,-1],[2,-1,0,-16]],[1,1,1],None,3000,'all',95),  # line 26
    '[1/105, 9/55, 10/3, 7/2, 1331/7, 5/11]': ('ndx',[4],{},[[1,-3],[1,-5],[1,-8],[1,-11],[1,-14],[1,-17],[1,-20],[1,-36],[1,-37],[1,-38],[1,-39],[1,-40],[1,-41],[1,-42],[1,-43],[1,-44]],[1],None,1000,False,160),  # line 27
    '[1/12, 7/15, 11/3, 27/7, 10/11, 49/2]': ('mul',2,[[],[],[],[],['-49/15','2314/15']],16,3,[[256,224599]]),  # line 34
    '[1/12, 7/15, 27/7, 11/3, 10/11, 49/2]': ('mul',2,[[],['-49/15','2314/15'],[],[],[]],16,3,[[256,185110],[4096,2964702]]),  # line 35
    '[1/12, 9/5, 5/21, 11/3, 14/11, 125/2]': ('add',3,[[],['6','13'],[],[],[]],1,[[6,6184],[7,8299],[8,10724],[9,13459]]),  # line 48
    '[1/135, 25/14, 77/5, 3/49, 2/11, 5/2]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-1],[1,-3,1],[0,1,-12],[0,1,-13],[0,1,-14],[3,-1,-123]],[1,1],None,400,False,400),  # line 49
    '[1/135, 25/77, 14/5, 3/49, 11/2, 5/11]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-1],[1,-3,1],[1,0,-4],[0,1,-12],[0,1,-13],[0,1,-14],[3,-1,-123]],[1,1],None,400,False,338),  # line 61
    '[1/15, 11/49, 63/143, 22/3, 5/11, 39/2]': ('nd',[1,5,0],{'3': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,-1,-3],[0,0,1,-8],[0,0,1,-16],[0,4,-1,-63]],[1,1,1],None,1000,False,368),  # line 69
    '[1/15, 117/77, 7/169, 14/3, 5/7, 33/2]': ('nd',[1,4,0],{'5': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,-1,-3],[0,0,1,-8],[0,0,1,-16],[0,4,-1,-63]],[1,1,1],None,1000,False,368),  # line 70
    '[1/15, 14/3, 117/77, 7/169, 5/7, 33/2]': ('ndxz',[0,1,3,5],{},[[0,-1,0,0,2],[0,1,0,0,-2],[1,0,0,0,-508],[0,1,0,0,-2],[0,0,1,0,-178],[0,0,0,1,-179],[1,-127,0,0,0],[0,-44,1,0,0],[0,-44,0,1,0],[-1,0,3,0,0],[3,0,-8,0,0],[-1,0,0,3,0],[3,0,0,-8,0],[0,0,-1,1,0],[0,0,11,-10,0]],[1,1,1,1],None,300,True,3142),  # line 71
    '[1/15, 140/3, 3/55, 5/49, 143/2, 5/13]': ('nd',[0,3,5],{'1': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-3],[0,1,0,-8],[0,1,0,-16],[4,-1,0,-63]],[1,1,1],None,1000,False,249),  # line 72
    '[1/15, 18/77, 14/39, 65/2, 3993/5]': ('mul',1,[['-2','6'],[],[],['-1','2'],[],[]],2,15,[[64,1905],[128,3825],[256,7665],[512,15345]]),  # line 73
    '[1/15, 2/3, 81/14, 55/2, 7/11, 4/5]': ('ndx',[0,3],{},[[1,0,-1],[0,1,-1],[1,3,-13],[1,0,-11],[1,0,-15],[1,0,-37],[1,0,-38],[1,0,-40],[1,0,-41]],[3,3],'1f0',400,False,310),  # line 74
    '[1/15, 3/49, 242/5, 25/143, 7/11, 65/2]': ('nd',[0,4],{'3': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 89
    '[1/15, 3/49, 25/143, 242/5, 7/11, 65/2]': ('nd',[0,4],{'3': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 90
    '[1/15, 5/21, 132/5, 3/121, 91/2, 3/13]': ('nd',[0,4,5],{'2': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-3],[0,1,0,-8],[0,1,0,-16],[4,-1,0,-63]],[1,1,1],None,1000,False,249),  # line 106
    '[1/15, 5/21, 66/5, 3/121, 343/2, 3/7]': ('ndx',[0,1,4],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-4],[1,0,-1,1],[0,0,1,-8],[0,0,1,-9]],[1,1,1],None,400,True,64),  # line 107
    '[1/15, 5/21, 66/5, 3/1331, 49/2, 3/7]': ('ndx',[0,4],{'2': 1},[[1,0,-57],[0,1,-1],[0,100,0],[11,-10,0],[0,1,-12],[0,1,-48],[0,1,-49],[0,1,-50],[0,1,-51],[0,1,-52],[0,1,-53],[0,1,-54],[0,1,-55]],[1,1],None,300,False,428),  # line 108
    '[1/15, 70/3, 3/55, 5/343, 121/2, 5/11]': ('nd',[0,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-1],[1,0,-1,2],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,1000,True,148),  # line 111
    '[1/15, 70/3, 3/55, 5/49, 1331/2, 5/11]': ('ndx',[0,2,3],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-4],[1,0,-1,1],[0,0,1,-8],[0,0,1,-9]],[1,1,1],None,400,True,64),  # line 112
    '[1/15, 81/14, 2/3, 55/2, 7/11, 4/5]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-1],[1,3,-32],[0,1,-4]],[3,1],'6',400,True,87),  # line 113
    '[1/15, 9/77, 5/169, 98/3, 13/7, 33/2]': ('nd',[0,3],{'5': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 116
    '[1/15, 9/77, 98/3, 5/169, 13/7, 33/2]': ('ndxz',[0,3,5],{},[[0,0,-1,2],[0,0,1,-2],[1,0,0,-330],[0,1,0,-354],[0,0,1,-2],[1,0,-82,0],[0,1,-88,0],[-1,1,0,0],[7,-6,0,0]],[1,1,1],None,300,True,2535),  # line 117
    '[1/15, 98/3, 5/121, 9/91, 11/7, 39/2]': ('nd',[0,3],{'4': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 118
    '[1/15, 98/3, 9/77, 5/169, 13/7, 33/2]': ('nd',[0,3],{'5': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 119
    '[1/1575, 20/21, 15/2, 49/5, 3/49]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-1],[1,-1,5892],[1,0,-4],[2,1,-20]],[1,1],None,1000,False,97),  # line 120
    '[1/1575, 20/21, 15/2, 49/5, 9/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-1],[1,-1,7838],[1,0,-4],[2,1,-16],[2,1,-17],[2,1,-18]],[1,1],None,1000,False,123),  # line 121
    '[1/1575, 4/147, 75/2, 49/5, 3/7]': ('ndx',[3],{},[[1,-5],[1,-10],[1,-12],[1,-40],[1,-42]],[1],None,400,False,147),  # line 122
    '[1/1575, 4/21, 15/2, 2401/5, 3/7]': ('ndx',[3],{},[[1,-22],[1,-32],[1,-33],[1,-34],[1,-35],[1,-36],[1,-37],[1,-38],[1,-39]],[1],None,1000,False,137),  # line 123
    '[1/1575, 4/21, 75/2, 343/5, 3/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-1],[0,1,-2],[0,1,-25]],[1,3],'2',1000,False,132),  # line 124
    '[1/1575, 4/21, 825/2, 49/5, 3/11]': ('ndx',[3,4],{},[[1,0,-15],[0,1,-7],[1,0,-16],[1,0,-17],[1,0,-18]],[1,1],None,1000,False,120),  # line 125
    '[1/18, 105/2, 2/33, 3/25, 121/7, 3/11]': ('nd',[1,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,1,0],[0,-1,1,1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,97),  # line 128
    '[1/18, 175/2, 2/847, 3993/5, 49/11]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-8],[-2,1,-13],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,144),  # line 129
    '[1/18, 175/2, 4/55, 13/5, 33/13, 5/7]': ('nd',[1,4,3],{},[[1,0,0,0],[-1,0,0,3],[0,1,-1,0],[0,0,1,-100],[0,-1,2,0]],[1,1,1],None,1000,False,1064),  # line 130
    '[1/18, 175/2, 8/385, 3/25, 22/7]': ('ndx',[1,3,4],{},[[1,0,0,-1],[0,1,0,-4],[0,0,1,-1],[-1,1,0,-2]],[1,1,1],None,1000,'all',41),  # line 131
    '[1/18, 2/15, 1617/2, 3/121, 5/7, 3/5]': ('nd',[3,4],{'0': 1},[[1,0,-1],[0,1,-1],[1,-1,-6],[0,1,-8],[0,1,-24],[0,1,-25],[0,1,-26]],[1,1],None,1000,False,423),  # line 132
    '[1/18, 2/15, 231/2, 3/49, 25/11, 3/5]': ('nd',[1,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,1,0],[0,-1,1,1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,97),  # line 133
    '[1/18, 2/175, 77/2, 1875/11, 49/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-6],[-3,1,-9],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,288),  # line 134
    '[1/18, 2/175, 847/2, 375/11, 49/5]': ('ndx',[1,2],{},[[1,0,-2],[0,1,-8],[-2,1,-13],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,144),  # line 135
    '[1/18, 2/175, 9317/2, 75/11, 49/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-5],[-2,1,0],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,436),  # line 136
    '[1/18, 35/2, 2/605, 43923/7, 25/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-6],[-3,1,-9],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,288),  # line 140
    '[1/18, 35/2, 28/55, 9/7, 2662/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[1,0,-14]],[3,3],'80',400,False,132),  # line 141
    '[1/18, 35/2, 4/55, 3/125, 11/7, 2/11]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-3],[-2,1,-5],[1,0,-8],[-1,2,-48],[-1,2,-74],[-1,2,-106],[1,0,-9]],[1,6],'3b',400,False,543),  # line 142
    '[1/18, 35/2, 4/55, 3/125, 11/7, 5/11]': ('nd',[1,4],{},[[1,0,-1],[0,1,-3],[-2,1,-7],[0,1,-15],[0,1,-16]],[1,1],None,400,True,117),  # line 143
    '[1/18, 35/2, 4/55, 39/25, 11/7, 5/13]': ('ndx',[1,4,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,0,-13],[-1,0,1,-2]],[1,1,1],None,400,True,114),  # line 144
    '[1/18, 35/2, 4/55, 91/5, 33/7, 5/13]': ('ndx',[1,4,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',4),  # line 145
    '[1/18, 385/2, 4/65, 3/25, 13/7, 5/11]': ('ndx',[1,4,5],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-2],[-1,1,0,-29],[-1,0,1,-13]],[1,1,1],None,400,True,114),  # line 146
    '[1/18, 385/2, 4/65, 7/5, 39/7, 5/11]': ('ndx',[1,3,4],{},[[1,0,0,0],[-1,0,0,1],[0,1,0,-151],[0,0,1,-142],[-75,1,0,0],[-71,0,1,0],[0,-7,8,0],[0,1,-1,0]],[1,1,1],None,300,False,590),  # line 147
    '[1/18, 4/35, 11/5, 325/2, 21/11, 5/13]': ('nd',[1,3,5],{},[[1,0,0,0],[-1,0,0,3],[0,1,-1,0],[0,0,1,-100],[0,-1,2,0]],[1,1,1],None,1000,False,1064),  # line 162
    '[1/18, 4/35, 11/5, 715/2, 21/11, 5/13]': ('ndx',[1,4,5],{},[[1,0,0,0],[-1,0,0,1],[0,1,0,-151],[0,0,1,-142],[-75,1,0,0],[-71,0,1,0],[0,-7,8,0],[0,1,-1,0]],[1,1,1],None,300,False,590),  # line 163
    '[1/18, 4/35, 125/2, 33/5, 7/11, 5/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-3],[-1,1,1],[1,0,-8],[1,0,-12],[1,0,-16],[-1,2,-18],[-1,2,-30],[-1,2,-32],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,190),  # line 164
    '[1/18, 4/35, 143/5, 55/2, 21/11, 5/13]': ('ndx',[1,3,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',4),  # line 165
    '[1/18, 4/35, 275/2, 13/5, 21/13, 5/11]': ('nd',[1,3,4],{},[[1,0,0,0],[-1,0,0,3],[0,1,-1,0],[0,0,1,-100],[0,-1,2,0]],[1,1,1],None,1000,False,1064),  # line 166
    '[1/18, 4/35, 55/2, 143/5, 21/11, 5/13]': ('ndx',[1,3,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',4),  # line 167
    '[1/18, 4/35, 55/2, 3/125, 7/11, 2/7]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-3],[-2,1,-5],[1,0,-8],[-1,2,-48],[-1,2,-74],[-1,2,-106],[1,0,-9]],[1,6],'3b',400,False,543),  # line 168
    '[1/18, 4/35, 55/2, 3/125, 7/11, 5/7]': ('nd',[1,3],{},[[1,0,-1],[0,1,-3],[-2,1,-7],[0,1,-15],[0,1,-16]],[1,1],None,400,True,117),  # line 169
    '[1/18, 4/35, 55/2, 3/25, 7/11, 25/7]': ('nd',[1,3],{},[[1,0,-1],[0,1,-2],[-1,1,-2],[0,1,-10],[0,1,-11]],[1,1],None,400,True,126),  # line 170
    '[1/18, 4/35, 55/2, 39/25, 7/11, 5/13]': ('ndx',[1,3,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,0,-13],[-1,0,1,-2]],[1,1,1],None,400,True,114),  # line 171
    '[1/18, 4/35, 715/2, 11/5, 21/11, 5/13]': ('nd',[1,4,5],{},[[1,0,0,0],[-1,0,0,3],[0,1,-1,0],[0,0,1,-100],[0,-1,2,0]],[1,1,1],None,1000,False,3052),  # line 172
    '[1/18, 4/35, 715/2, 3/25, 7/11, 5/13]': ('ndx',[1,3,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-3],[-1,1,0,-13],[-1,0,1,-29]],[1,1,1],None,400,True,114),  # line 173
    '[1/18, 525/2, 2/33, 3/49, 11/5, 3/11]': ('nd',[2,3],{'0': 1},[[1,0,-1],[0,1,-1],[1,-1,-6],[0,1,-8],[0,1,-24],[0,1,-25],[0,1,-26]],[1,1],None,1000,False,423),  # line 174
    '[1/18, 7/10, 11/2, 8/7, 15/11, 49/3]': ('mul',2,[[],[],[],[],['-49/15','169/15']],16,6,[[256,16257],[4096,262473]]),  # line 175
    '[1/18, 7/10, 8/7, 11/2, 15/11, 49/3]': ('mul',2,[[],[],[],[],['-49/15','169/15']],16,6,[[256,16257],[4096,262473]]),  # line 176
    '[1/18, 875/2, 2/847, 363/5, 49/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-5],[-2,1,0],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,436),  # line 179
    '[1/180, 25/14, 22/5, 3/2, 7/11, 5/3]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[1,0,-10]],[1,1],None,400,True,130),  # line 180
    '[1/180, 25/21, 33/5, 2/3, 7/11, 5/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[1,0,-10]],[1,1],None,400,True,129),  # line 181
    '[1/180, 49/15, 6/7, 625/2, 3/5]': ('ndcv',[2],{},[[1,-4],[1,-5],[1,-32],[1,-33],[1,-34],[1,-35],[1,-36],[1,-37],[1,-38],[1,-39]],[1],None,1000,False,115),  # line 183
    '[1/30, 14/3, 27/77, 5/7, 33/2, 3/5]': ('add',4,[['4','8'],[],[],['3','6'],[]],3,[[17,18417],[18,20580],[19,22863],[20,25266]]),  # line 202
    '[1/30, 14/3, 9/55, 5/7, 1331/2, 5/11]': ('ndcv',[4],{},[[1,-3],[1,-5],[1,-8],[1,-11],[1,-14],[1,-17],[1,-20],[1,-36],[1,-37],[1,-38],[1,-39],[1,-40],[1,-41],[1,-42],[1,-43],[1,-44]],[1],None,1000,False,269),  # line 203
    '[1/30, 14/3, 9/55, 5/7, 1331/2, 7/11]': ('ndcv',[4],{},[[1,-3],[1,-5],[1,-8],[1,-11],[1,-14],[1,-17],[1,-20],[1,-36],[1,-37],[1,-38],[1,-39],[1,-40],[1,-41],[1,-42],[1,-43],[1,-44]],[1],None,1000,False,272),  # line 204
    '[1/30, 147/2, 4/165, 5/7, 3993/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-2],[-5,4,-43]],[1,1],None,400,True,93),  # line 205
    '[1/30, 15/7, 49/33, 16/5, 847/2]': ('mul',1,[['-1','6'],[],[],[],[]],3,5,[[81,1573],[243,4732],[729,14209],[2187,42640]]),  # line 206
    '[1/30, 2/539, 9/35, 847/3, 245/2]': ('mul',4,[['5/4','3/4'],[],[],[],['-1/4','21/4']],81,1,[[6561,89555]]),  # line 207
    '[1/30, 21/2, 8/77, 25/49, 242/3]': ('nd',[1,3],{},[[1,0,-1],[0,1,-1],[-2,3,-4],[1,-1,-1],[0,1,-9],[1,0,-13],[-1,2,-23],[-1,2,-27]],[12,30],'140501400000000000000000000000140501400000000000000000000000140501400000000000000000000000',400,False,439),  # line 208
    '[1/30, 21/2, 8/77, 5/7, 22/3, 2/5]': ('add',4,[[],['1','8'],[],['1','6'],[]],3,[[17,17392],[18,19495],[19,21718],[20,24061]]),  # line 209
    '[1/30, 231/2, 8/91, 5/7, 13/11, 7/3]': ('nd',[1,2,5],{'3': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-4],[-2,0,3,-25],[3,-4,0,-1],[0,-4,3,-7],[0,1,0,-4],[0,1,0,-7],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,3000,False,134),  # line 210
    '[1/30, 27/35, 55/9, 2/11, 1715/2]': ('ndx',[0,2],{},[[1,0,-3],[0,1,-1],[3,-8,-4],[0,1,-4],[0,1,-8],[0,1,-12],[0,1,-15],[0,1,-19],[0,1,-23],[0,1,-44],[0,1,-45],[0,1,-46],[0,1,-47],[0,1,-48],[0,1,-49],[0,1,-50],[0,1,-51],[0,1,-52],[0,1,-53],[0,1,-54]],[1,1],None,3000,False,2665),  # line 211
    '[1/30, 297/35, 5/9, 2/11, 1715/2]': ('ndcv',[1,4],{},[[1,0,-4],[0,1,-3],[-1,1,2],[1,-1,-2],[1,0,-8],[1,0,-16],[1,0,-24],[1,0,-30],[1,0,-38],[1,0,-46],[1,0,-88],[1,0,-111]],[1,1],None,1000,False,2743),  # line 213
    '[1/30, 35/3, 27/77, 2/7, 33/5, 3/2]': ('add',4,[[],[],['1','8'],['1','6'],[]],3,[[17,17393],[18,19496],[19,21719],[20,24062]]),  # line 214
    '[1/30, 35/3, 9/55, 2/7, 1331/2, 5/11]': ('nd',[0,2,4],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-12]],[1,1,1],None,1000,True,127),  # line 215
    '[1/30, 35/9, 27/55, 2/7, 6655/2]': ('ndx',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-3,0,7],[1,0,0,-9],[1,0,0,-13]],[2,1,1],'2',400,True,131),  # line 216
    '[1/30, 4/105, 363/2, 5/11, 1029/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-2],[-5,4,-43]],[1,1],None,400,True,93),  # line 217
    '[1/30, 4/63, 99/2, 5/11, 1029/5]': ('ndx',[1,3],{},[[1,0,-2],[0,1,-3],[-1,0,2],[1,0,-2],[0,1,-4]],[1,1],None,3000,True,53),  # line 218
    '[1/30, 4/77, 63/2, 5/7, 11/3, 49/5]': ('ndx',[2,4],{},[[1,0,-1],[0,1,-2],[-1,1,-55],[1,0,-5],[1,0,-7],[1,0,-11],[1,0,-14],[1,0,-16],[1,0,-20],[1,0,-37],[1,0,-40],[1,0,-43]],[3,6],'900',400,False,778),  # line 219
    '[1/30, 4/77, 91/2, 27/49, 110/13]': ('nd',[0,2,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,0,0,1,-2],[-2,4,-1,1,2],[2,-4,1,-1,-2],[0,0,1,0,-4]],[1,1,1,1],None,400,True,64),  # line 220
    '[1/30, 40/231, 7/2, 15/7, 44/5]': ('ndx',[2,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,3],[0,0,1,-4],[1,0,0,-4]],[1,1,1],None,1000,True,100),  # line 221
    '[1/30, 49/33, 15/7, 16/5, 847/2]': ('mul',1,[['-1','6'],[],[],[],[]],3,5,[[81,1573],[243,4732],[729,14209],[2187,42640]]),  # line 223
    '[1/30, 5/9, 297/35, 2/11, 1715/2]': ('ndcv',[3],{'2': 1},[[1,-780]],[1],None,1000,False,16318),  # line 224
    '[1/30, 63/2, 4/99, 5/7, 3993/5]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-3],[-3,1,0],[0,1,-10],[0,2,-23],[0,2,-25]],[1,1],None,3000,True,329),  # line 225
    '[1/30, 63/2, 8/77, 25/7, 847/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-3,1],[0,1,-4],[0,1,-6],[0,1,-7]],[1,1],None,400,False,63),  # line 226
    '[1/30, 7/2, 40/231, 15/7, 44/5]': ('ndx',[2,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,3],[0,0,1,-4],[1,0,0,-4]],[1,1,1],None,400,True,100),  # line 227
    '[1/30, 77/2, 4/91, 27/49, 130/11]': ('nd',[0,2,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-3],[-3,0,1,0,0]],[3,3,1,1],'1f8',3000,'all',64),  # line 228
    '[1/30, 9/35, 22/3, 5/11, 343/2, 11/7]': ('ndcv',[3],{},[[1,-3],[1,-5],[1,-8],[1,-11],[1,-14],[1,-17],[1,-20],[1,-36],[1,-37],[1,-38],[1,-39],[1,-40],[1,-41],[1,-42],[1,-43],[1,-44]],[1],None,1000,False,272),  # line 229
    '[1/30, 9/35, 22/3, 5/11, 343/2, 5/7]': ('ndcv',[3],{},[[1,-3],[1,-5],[1,-8],[1,-11],[1,-14],[1,-17],[1,-20],[1,-36],[1,-37],[1,-38],[1,-39],[1,-40],[1,-41],[1,-42],[1,-43],[1,-44]],[1],None,1000,False,269),  # line 230
    '[1/30, 9/35, 55/3, 2/11, 343/2, 5/7]': ('ndcv',[3],{},[[1,-3],[1,-5],[1,-8],[1,-11],[1,-14],[1,-17],[1,-20],[1,-36],[1,-37],[1,-38],[1,-39],[1,-40],[1,-41],[1,-42],[1,-43],[1,-44]],[1],None,1000,False,159),  # line 231
    '[1/315, 125/22, 6/5, 21/2, 605/3]': ('mul',2,[[],['-2','3'],[],['-1/4','5/4'],[]],9,1,[[81,551],[729,5006],[6561,45101],[59049,405956]]),  # line 232
    '[1/315, 242/15, 21/11, 625/2, 11/5]': ('ndx',[2,3],{},[[1,0,-10],[0,1,-5],[1,0,-32],[1,0,-33],[1,0,-34],[1,0,-35],[1,0,-36],[1,0,-37],[1,0,-38],[1,0,-39]],[1,1],None,400,False,202),  # line 233
    '[1/315, 242/15, 21/11, 625/2, 3/5]': ('ndx',[2,3],{},[[1,0,-10],[0,1,-4],[1,0,-32],[1,0,-33],[1,0,-34],[1,0,-35],[1,0,-36],[1,0,-37],[1,0,-38],[1,0,-39]],[1,1],None,400,False,199),  # line 234
    '[1/315, 25/143, 66/5, 1/11, 91/2, 11/7]': ('ndxz',[5,1,3],{},[[1,0,0,-83],[0,1,0,0],[0,-1,0,2],[0,0,1,-151],[1,-27,0,0],[0,-51,1,0],[-5,0,3,0],[2,0,-1,0]],[1,1,1],None,1000,True,1173),  # line 235
    '[1/315, 25/77, 1/11, 66/5, 49/2, 11/7]': ('ndx',[0,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,400,True,151),  # line 237
    '[1/315, 25/77, 66/5, 1/11, 49/2, 11/7]': ('ndx',[0,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,400,True,151),  # line 238
    '[1/315, 6/5, 125/22, 21/2, 605/3]': ('mul',2,[[],['-2','3'],[],['-1/4','5/4'],[]],9,1,[[81,551],[729,5006],[6561,45101],[59049,405956]]),  # line 239
    '[1/4, 2/15, 231/2, 3/343, 25/11, 2/5]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-1,0,2],[0,1,-4],[1,2,-12],[1,2,-24],[1,2,-26]],[1,1],None,400,False,181),  # line 248
    '[1/420, 9/22, 10/3, 7/2, 11/5, 3/7]': ('ndx',[2,3],{},[[1,0,-101],[0,1,-1],[0,100,0],[1,-8,0],[0,1,-5]],[1,1],None,300,False,2132),  # line 253
    '[1/45, 11/35, 125/11, 2/5, 21/2, 121/3]': ('mul',2,[[],[],['-49/15','169/15'],[],[]],16,6,[[256,13375],[4096,216327]]),  # line 254
    '[1/45, 11/35, 2/5, 125/11, 21/2, 121/3]': ('mul',2,[['-49/15','169/15'],[],[],[],[]],16,6,[[256,16256],[4096,262472]]),  # line 255
    '[1/45, 14/5, 25/22, 91/2, 33/7, 2/13]': ('nd',[1,4,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',2),  # line 258
    '[1/45, 14/5, 25/77, 3/343, 11/2, 5/11]': ('ndx',[0,1],{},[[1,0,-3],[0,1,-1],[1,-6,7],[1,0,-4],[0,1,-8],[0,1,-9],[2,-1,-106]],[1,1],None,400,False,545),  # line 259
    '[1/45, 14/5, 5/847, 43923/2, 49/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-4],[-3,1,-7],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,299),  # line 260
    '[1/45, 22/35, 1/7, 147/11, 125/2, 11/5]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-3],[1,-1,-4],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,737),  # line 261
    '[1/45, 22/35, 1/7, 147/11, 125/2, 7/5]': ('ndx',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,0,-2,1],[-1,0,2,-1],[0,1,0,-20],[0,1,0,-21],[0,1,0,-22],[0,1,0,-23],[0,1,0,-24]],[1,1,1],None,400,True,119),  # line 262
    '[1/45, 22/35, 147/11, 1/7, 125/2, 11/5]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-3],[1,-1,-4],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,737),  # line 263
    '[1/45, 22/35, 147/11, 1/7, 125/2, 7/5]': ('ndx',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,0,-2,1],[-1,0,2,-1],[0,1,0,-20],[0,1,0,-21],[0,1,0,-22],[0,1,0,-23],[0,1,0,-24]],[1,1,1],None,400,True,119),  # line 264
    '[1/45, 22/35, 3/49, 49/11, 25/2, 11/5]': ('nd',[0,1],{},[[1,0,-2],[0,1,-1],[1,-1,-1]],[1,1],None,3000,'all',17),  # line 265
    '[1/45, 22/35, 3/77, 49/11, 25/2, 7/5]': ('ndz',[0,1,2],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-2,0,1],[1,0,0,-4]],[1,1,1],None,400,True,47),  # line 266
    '[1/45, 22/35, 49/11, 3/49, 25/2, 11/5]': ('nd',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,0],[1,0,-1,2],[0,0,1,-8],[1,0,0,-8],[0,0,1,-9]],[1,1,1],None,400,True,102),  # line 267
    '[1/45, 25/14, 143/2, 22/5, 21/11, 2/13]': ('nd',[1,3,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',2),  # line 268
    '[1/45, 25/14, 22/5, 143/2, 21/11, 2/13]': ('nd',[1,3,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',2),  # line 269
    '[1/45, 25/14, 77/5, 3/343, 2/11, 5/2]': ('ndx',[0,1],{},[[1,0,-3],[0,1,-1],[1,-2,-14],[0,1,-8],[0,1,-9],[2,-1,-106]],[1,1],None,400,False,652),  # line 270
    '[1/45, 25/77, 14/5, 3/343, 11/2, 5/11]': ('ndx',[0,1],{},[[1,0,-3],[0,1,-1],[1,-6,7],[1,0,-4],[0,1,-8],[0,1,-9],[2,-1,-106]],[1,1],None,400,False,545),  # line 280
    '[1/45, 25/77, 26/7, 49/5, 33/13, 7/2]': ('nd',[1,0,4],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,0,-13],[-1,0,1,-2]],[1,1,1],None,400,True,312),  # line 281
    '[1/45, 25/77, 26/7, 91/5, 33/13, 7/2]': ('nd',[1,4,0],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',13),  # line 282
    '[1/45, 25/77, 28/5, 9/2, 6655/3]': ('mul',1,[[],['-7/4','15/4'],[],[],[]],9,1,[[81,1701],[729,15471],[6561,139401],[59049,1254771]]),  # line 283
    '[1/45, 25/77, 49/5, 26/7, 33/13, 7/2]': ('nd',[1,0,4],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,0,-13],[-1,0,1,-2]],[1,1,1],None,400,True,312),  # line 284
    '[1/45, 25/77, 91/5, 26/7, 33/13, 7/2]': ('nd',[1,4,0],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',13),  # line 285
    '[1/45, 28/5, 25/77, 9/2, 6655/3]': ('mul',1,[[],['-7/4','15/4'],[],[],[]],9,1,[[81,1701],[729,15471],[6561,139401],[59049,1254771]]),  # line 287
    '[1/45, 4/35, 77/2, 3/343, 5/11, 7/5]': ('nd',[1,4],{},[[1,0,-1],[0,1,-3],[-1,1,-6]],[1,1],None,1000,'all',60),  # line 289
    '[1/45, 4/35, 77/2, 3/49, 25/11, 7/5]': ('nd',[1,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-2,0,1,1],[0,0,1,-4]],[1,1,1],None,400,True,24),  # line 290
    '[1/45, 4/35, 77/2, 3/49, 5/11, 14/5]': ('nd',[1,4],{},[[1,0,-1],[0,1,-2],[-1,1,-3]],[1,1],None,1000,'all',36),  # line 291
    '[1/45, 42/5, 5/33, 3/49, 121/2, 3/11]': ('nd',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,0],[1,0,-1,1],[0,0,1,-8],[0,0,1,-9]],[1,1,1],None,400,True,100),  # line 292
    '[1/45, 49/11, 22/35, 3/49, 25/2, 11/5]': ('nd',[0,1],{},[[1,0,-2],[0,1,-1],[1,-1,-1]],[1,1],None,3000,'all',17),  # line 293
    '[1/45, 5/154, 16/35, 21/2, 55/3]': ('add',1,[[],['1','6'],[],['2','3','1'],[]],10,[[49,17011],[50,17708],[51,18419],[52,19144]]),  # line 296
    '[1/45, 5/154, 8/35, 147/2, 55/7]': ('add',2,[[],['6','10'],[],['14','15','5'],[]],12,[[59,106600],[60,110206],[61,113872],[62,117598]]),  # line 297
    '[1/45, 5/21, 66/5, 3/121, 49/2, 3/7]': ('nd',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,0],[1,0,-1,1],[0,0,1,-8],[0,0,1,-9]],[1,1,1],None,400,True,100),  # line 298
    '[1/45, 5/539, 22/5, 7203/2, 121/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-4],[-3,1,-7],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,299),  # line 299
    '[1/45, 77/2, 4/35, 3/343, 5/11, 7/5]': ('nd',[1,4],{},[[1,0,-1],[0,1,-3],[-1,1,-6]],[1,1],None,1000,'all',60),  # line 300
    '[1/45, 77/5, 25/14, 3/343, 2/11, 5/2]': ('ndx',[0,1],{},[[1,0,-3],[0,1,-1],[1,-2,-14],[0,1,-8],[0,1,-9],[2,-1,-106]],[1,1],None,400,False,652),  # line 301
    '[1/45, 77/5, 25/91, 22/7, 39/11, 7/2]': ('nd',[1,5,0],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,3,-1]],[1,1,1],None,1000,'all',3),  # line 302
    '[1/450, 4/21, 33/2, 5/3, 7/11, 2/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[1,0,-10]],[1,1],None,400,True,128),  # line 303
    '[1/450, 4/21, 33/2, 5/3, 7/11, 3/5]': ('ndx',[2,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[1,0,-10],[-3,2,0],[-3,2,-8],[-3,2,-15]],[2,2],'9',400,False,248),  # line 304
    '[1/4725, 4/35, 45/2, 49/3, 5/7]': ('ndcv',[3],{},[[1,-11],[1,-16],[1,-17],[1,-18],[1,-19]],[1],None,1000,False,86),  # line 305
    '[1/4725, 5/33, 18/5, 847/2, 3/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-1,2,-6],[1,-1,-8],[0,1,-70],[0,1,-72],[0,1,-74],[0,1,-76]],[1,1],None,1000,False,525),  # line 306
    '[1/54, 385/2, 4/65, 3/5, 13/7, 5/11]': ('nd',[1,4,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,-3],[-1,0,1,0],[0,0,1,-5]],[1,1,1],None,400,True,43),  # line 317
    '[1/54, 4/35, 715/2, 3/5, 7/11, 5/13]': ('nd',[1,3,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,0],[-1,0,1,-3],[0,1,0,-5]],[1,1,1],None,400,True,43),  # line 333
    '[1/540, 2/21, 99/2, 245/11, 3/7]': ('nd',[0,1,2,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[1,-1,0,0,3]],[1,1,1,1],None,1000,'all',5),  # line 334
    '[1/6, 105/2, 2/33, 3/125, 121/7, 3/11]': ('nd',[2,3],{'0': 1},[[1,0,-1],[0,1,-1],[-1,1,2],[1,0,-12],[1,0,-48],[1,0,-49],[1,0,-50],[1,0,-51],[1,0,-52],[1,0,-53],[1,0,-54],[1,0,-55]],[1,1],None,1000,False,425),  # line 335
    '[1/6, 105/2, 2/33, 3/25, 121/7, 15/11]': ('ndx',[2,3],{'0': 1},[[1,0,-1],[0,1,-1],[-1,1,2],[1,0,-8],[1,0,-32],[1,0,-33],[1,0,-34],[1,0,-35],[1,0,-36]],[1,1],None,64,False,512),  # line 336
    '[1/6, 105/2, 2/33, 3/25, 1331/7, 3/11]': ('ndx',[1,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,1,-3],[0,-1,1,1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,45),  # line 337
    '[1/6, 105/2, 26/33, 3/25, 121/7, 3/13]': ('ndx',[2,3,5],{'0': 1},[[1,0,0,-383],[0,1,0,-382],[0,0,1,-1021],[-1,1,0,1],[1,-1,0,0]],[1,1,1],None,300,False,2841),  # line 338
    '[1/6, 14/15, 429/2, 3/121, 25/13, 3/7]': ('ndx',[4,5,3],{'1': 1},[[1,0,0,-383],[0,1,0,-382],[0,0,1,-1021],[-1,1,0,1],[1,-1,0,0]],[1,1,1],None,300,False,2842),  # line 339
    '[1/6, 14/15, 4719/2, 3/169, 5/11, 3/7]': ('nd',[3,4,5],{'0': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,-1,-3],[0,0,1,-8],[0,0,1,-16],[0,4,-1,-63]],[1,1,1],None,1000,False,246),  # line 340
    '[1/6, 16/35, 5/2, 33/5, 7/11, 25/3]': ('ndx',[0,3],{},[[1,0,-1],[0,1,-1],[1,3,-32],[0,1,-4]],[3,1],'6',400,True,88),  # line 341
    '[1/6, 175/2, 4/847, 3/49, 11/5, 7/11]': ('nd',[1,4],{},[[1,0,-1],[0,1,-4],[-2,1,-5]],[1,1],None,1000,'all',53),  # line 342
    '[1/6, 2/15, 11319/2, 3/121, 5/7, 3/5]': ('nd',[1,3,4],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-7],[0,1,-1,-8]],[1,1,1],None,400,'all',20),  # line 343
    '[1/6, 2/15, 1617/2, 3/121, 65/7, 3/13]': ('nd',[3,4,5],{'0': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-3],[0,1,0,-8],[0,1,0,-16],[4,-1,0,-63]],[1,1,1],None,1000,False,246),  # line 344
    '[1/6, 2/15, 1617/2, 3/1331, 5/7, 3/5]': ('nd',[1,3,4],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,0,-3],[0,1,-1,-2]],[1,1,1],None,1000,'all',19),  # line 345
    '[1/6, 2/15, 231/2, 3/343, 25/11, 3/5]': ('nd',[3,4],{'0': 1},[[1,0,-1],[0,1,-1],[-1,1,2],[1,0,-12],[1,0,-48],[1,0,-49],[1,0,-50],[1,0,-51],[1,0,-52],[1,0,-53],[1,0,-54],[1,0,-55]],[1,1],None,1000,False,425),  # line 346
    '[1/6, 2/15, 231/2, 3/49, 125/11, 3/5]': ('ndx',[1,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,1,-3],[0,-1,1,1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,45),  # line 347
    '[1/6, 2/15, 231/2, 3/49, 25/11, 21/5]': ('ndx',[3,4],{'0': 1},[[1,0,-1],[0,1,-1],[-1,1,2],[1,0,-8],[1,0,-32],[1,0,-33],[1,0,-34],[1,0,-35],[1,0,-36]],[1,1],None,64,False,512),  # line 348
    '[1/6, 2/175, 15125/2, 21/11, 8/3]': ('ndx',[0,3],{'2': 1},[[1,0,-1],[-1,0,3],[0,1,-1],[0,1,-4],[0,1,-7],[0,1,-11],[0,1,-15],[0,1,-16]],[64,4],'2080',3000,False,292),  # line 349
    '[1/6, 2/1925, 2401/2, 15/7, 44/3]': ('add',2,[[],['4','15'],['4','14','5'],[],[]],8,[[39,61937],[40,65125],[41,68393],[42,71741]]),  # line 350
    '[1/6, 2/385, 625/2, 21/5, 1210/3]': ('add',2,[[],['4','15'],[],['4','14','5'],[]],4,[[19,16820],[20,18605],[21,20480],[22,22445]]),  # line 351
    '[1/6, 2625/2, 2/33, 3/49, 11/5, 3/11]': ('nd',[1,2,3],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-7],[0,1,-1,-8]],[1,1,1],None,400,'all',20),  # line 352
    '[1/6, 35/2, 4/605, 3/25, 121/7, 5/11]': ('nd',[1,4],{},[[1,0,-1],[0,1,-4],[-2,1,-5]],[1,1],None,1000,'all',41),  # line 353
    '[1/6, 4/175, 77/2, 3/49, 25/11, 7/5]': ('ndx',[0,2],{},[[1,0,-1],[0,1,-1],[0,1,-8],[0,1,-9]],[1,1],None,400,True,70),  # line 354
    '[1/6, 4/175, 847/2, 3/49, 5/11, 7/5]': ('ndx',[0,2],{},[[1,0,-1],[0,1,-1],[0,1,-8],[0,1,-9]],[1,1],None,400,True,90),  # line 355
    '[1/6, 5/2, 16/35, 33/5, 7/11, 25/3]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-1],[1,3,-13],[1,0,-11],[1,0,-15],[1,0,-37],[1,0,-38],[1,0,-40],[1,0,-41]],[3,3],'1f0',400,False,311),  # line 357
    '[1/6, 525/2, 2/33, 3/343, 11/5, 3/11]': ('nd',[1,2,3],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,0,-3],[0,1,-1,-2]],[1,1,1],None,1000,'all',19),  # line 358
    '[1/6, 525/2, 2/33, 3/49, 143/5, 3/13]': ('nd',[2,3,5],{'0': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-3],[0,1,0,-8],[0,1,0,-16],[4,-1,0,-63]],[1,1,1],None,1000,False,246),  # line 359
    '[1/6, 525/2, 26/33, 3/49, 11/5, 3/13]': ('nd',[2,3,5],{'0': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-3],[0,1,0,-8],[0,1,0,-16],[4,-1,0,-63]],[1,1,1],None,1000,False,246),  # line 360
    '[1/60, 9/14, 22/3, 5/2, 7/11, 14/5]': ('nd',[2,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,761),  # line 363
    '[1/60, 9/14, 22/3, 5/2, 7/11, 21/5]': ('ndx',[2,4],{},[[1,0,-94],[0,1,-227],[-9,4,0],[5,-2,0]],[1,1],None,300,False,1160),  # line 364
    '[1/60, 9/14, 22/3, 5/2, 7/11, 22/5]': ('nd',[2,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,770),  # line 365
    '[1/60, 9/14, 22/3, 5/2, 7/11, 3/5]': ('ndx',[2,4],{},[[1,0,-70],[0,1,-149],[-2,1,0],[5,-2,0]],[1,1],None,300,False,778),  # line 366
    '[1/60, 9/14, 22/3, 5/2, 7/11, 33/5]': ('nd',[2,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,435),  # line 367
    '[1/60, 9/14, 22/3, 5/2, 7/11, 9/5]': ('ndx',[2,4],{},[[1,0,-19],[0,1,-248],[-13,1,0],[22,-1,0]],[1,1],None,300,False,1349),  # line 368
    '[1/630, 25/33, 21/5, 2/3, 11/7, 5/2]': ('nd',[3,0],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,3393),  # line 369
    '[1/630, 4/33, 15/2, 7/3, 11/5, 2/7]': ('ndx',[2,3],{},[[1,0,-101],[0,1,-1],[0,100,0],[1,-8,0],[0,1,-5]],[1,1],None,300,False,2130),  # line 370
    '[1/9, 3/10, 385/3, 5/343, 4/11, 3/2]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-1,0,2],[0,1,-4],[1,2,-12],[1,2,-24],[1,2,-26]],[1,1],None,400,False,182),  # line 376
    '[1/9, 3/35, 110/3, 5/1331, 49/2, 3/7]': ('nd',[0,4],{},[[1,0,-2],[0,1,-1],[0,-1,2],[1,0,-4]],[1,1],None,400,True,61),  # line 377
    '[1/90, 10/7, 7/605, 43923/2, 5/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,225),  # line 378
    '[1/90, 11/245, 10/11, 7203/2, 5/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,225),  # line 379
    '[1/90, 1372/15, 3/49, 25/2, 3/5]': ('ndcv',[0,3],{},[[1,0,-2],[0,1,-1],[1,-1,-8],[0,1,-8],[0,1,-32],[0,1,-33],[0,1,-34],[0,1,-35],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39]],[1,1],None,400,False,225),  # line 380
    '[1/90, 196/15, 3/7, 625/2, 3/5]': ('ndcv',[0,2],{},[[1,0,-1],[0,1,-1],[1,-1,11866],[1,0,-4]],[1,1],None,400,True,66),  # line 381
    '[1/90, 196/15, 3/7, 625/2, 7/5]': ('ndcv',[0,2],{},[[1,0,-1],[0,1,-1],[1,-1,11866],[1,0,-4]],[1,1],None,400,True,68),  # line 382
    '[1/90, 21/2, 8/99, 5/7, 363/5]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[0,1,-12],[0,1,-18],[0,1,-26],[0,1,-60],[0,1,-61],[0,1,-62],[0,1,-63],[0,1,-64],[0,1,-65],[0,1,-66],[0,1,-67],[0,1,-68]],[1,1],None,3000,False,319),  # line 383
    '[1/90, 22/245, 5/11, 7203/2, 11/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,245),  # line 384
    '[1/90, 22/245, 5/11, 7203/2, 5/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,225),  # line 385
    '[1/90, 25/21, 33/5, 2/3, 7/11, 21/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,760),  # line 386
    '[1/90, 25/21, 33/5, 2/3, 7/11, 25/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,753),  # line 387
    '[1/90, 25/21, 33/5, 2/3, 7/11, 33/2]': ('nd',[4,0],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,769),  # line 388
    '[1/90, 25/21, 33/5, 2/3, 7/11, 5/2]': ('ndx',[0,4],{},[[1,0,-19],[0,1,-149],[-2,1,0],[22,-1,0],[3,-1,-15],[3,-1,-19]],[1,1],None,300,False,777),  # line 389
    '[1/90, 25/21, 33/5, 2/3, 7/11, 55/2]': ('nd',[3,0],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,524),  # line 390
    '[1/90, 35/2, 4/77, 3/49, 11/5, 2/11]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-2],[-1,1,-4],[1,0,-8],[-1,2,-32],[-1,2,-50],[1,0,-9],[-1,2,-54]],[1,1],None,400,False,458),  # line 391
    '[1/90, 35/2, 8/275, 3/7, 605/3]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[1,-3,6],[0,1,-5],[0,1,-10],[0,1,-14],[0,1,-19],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39],[0,1,-40],[0,1,-41],[0,1,-42],[0,1,-43],[0,1,-44]],[1,1],None,3000,False,1848),  # line 392
    '[1/90, 385/2, 4/91, 3/7, 13/11, 7/5]': ('nd',[1,2,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,-2],[-1,0,1,-1],[0,0,1,-6]],[1,1,1],None,400,True,71),  # line 393
    '[1/90, 4/21, 33/2, 25/3, 7/11, 2/5]': ('ndx',[2,4],{},[[1000,-925,0],[-1000,969,0],[0,1,-5000]],[2,1],'1',1000,False,34598),  # line 395
    '[1/90, 4/21, 33/2, 5/3, 7/11, 14/5]': ('nd',[2,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,428),  # line 396
    '[1/90, 4/21, 33/2, 5/3, 7/11, 2/5]': ('ndx',[2,4],{},[[100,-38,0],[-100,47,0],[0,1,-1000]],[1,1],None,1000,False,27280),  # line 397
    '[1/90, 4/21, 33/2, 5/3, 7/11, 22/5]': ('nd',[2,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,1168),  # line 398
    '[1/90, 4/21, 33/2, 5/3, 7/11, 33/5]': ('ndx',[2,4],{},[[1,0,-70],[0,1,-149],[-2,1,0],[5,-2,0]],[1,1],None,300,False,769),  # line 399
    '[1/90, 4/21, 33/2, 5/3, 7/11, 6/5]': ('nd',[2,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,4229),  # line 400
    '[1/90, 4/21, 33/2, 5/3, 7/11, 9/5]': ('ndx',[2,3],{'0': 4},[[1,0,-126],[0,1,-298],[-9,4,0],[5,-2,0]],[1,1],None,300,False,1952),  # line 401
    '[1/90, 4/35, 1/7, 231/2, 25/11, 7/5]': ('ndx',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,True,177),  # line 402
    '[1/90, 4/35, 1/7, 2541/2, 5/11, 7/5]': ('ndx',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-2],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,True,220),  # line 403
    '[1/90, 4/35, 231/2, 1/7, 25/11, 7/5]': ('ndx',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,True,177),  # line 404
    '[1/90, 4/35, 2541/2, 1/7, 5/11, 7/5]': ('ndx',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-2],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,True,220),  # line 405
    '[1/90, 4/77, 35/2, 3/49, 11/5, 2/11]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-2],[-1,1,-4],[1,0,-8],[-1,2,-32],[-1,2,-50],[1,0,-9],[-1,2,-54]],[1,1],None,400,False,458),  # line 406
    '[1/90, 4/77, 455/2, 3/7, 11/13, 7/5]': ('nd',[1,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,-2],[-1,0,1,-1],[0,0,1,-5]],[1,1,1],None,400,True,41),  # line 407
    '[1/90, 5/7, 14/605, 43923/2, 5/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,225),  # line 408
    '[1/90, 5/7, 14/605, 43923/2, 7/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,245),  # line 409
    '[1/90, 8/175, 55/2, 3/11, 245/3]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[1,-3,6],[0,1,-5],[0,1,-10],[0,1,-14],[0,1,-19],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39],[0,1,-40],[0,1,-41],[0,1,-42],[0,1,-43],[0,1,-44]],[1,1],None,3000,False,1848),  # line 410
    '[1/90, 8/63, 33/2, 5/11, 147/5]': ('ndx',[2,3],{},[[1,0,-2],[0,1,-1],[0,1,-4],[0,1,-12],[0,1,-18],[0,1,-26],[0,1,-60],[0,1,-61],[0,1,-62],[0,1,-63],[0,1,-64],[0,1,-65],[0,1,-66],[0,1,-67],[0,1,-68]],[1,1],None,3000,False,319),  # line 411
    '[1/90, 98/15, 3/7, 3125/2, 3/5]': ('mul',6,[[],[],['32/9','40/9'],[]],64,3,[[4096,73034]]),  # line 412
    '[1/90, 98/15, 3/7, 3125/2, 7/5]': ('mul',6,[[],[],['32/9','40/9'],[]],64,3,[[4096,73047]]),  # line 413
    '[1/90, 98/15, 3/7, 6875/2, 3/11]': ('ndcv',[2,4],{},[[1,0,-4],[0,1,-1],[1,0,-32],[1,0,-34],[1,0,-35],[1,0,-36],[1,0,-38]],[4,1],'d',1000,False,420),  # line 414
    '[1/90, 98/15, 3/7, 6875/2, 7/11]': ('ndcv',[2,4],{},[[1,0,-4],[0,1,-1],[1,0,-32],[1,0,-34],[1,0,-35],[1,0,-36],[1,0,-38]],[4,1],'d',1000,False,427),  # line 415
    '[10/3, 1/385, 3/245, 26411/2, 25/7]': ('ndcv',[3,4],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,196),  # line 416
    '[10/3, 1/490, 3/605, 102487/2, 5/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,225),  # line 417
    '[100/63, 7/22, 27/2, 11/5, 14/3]': ('ndx',[1,2],{},[[1,0,-9],[0,1,-2],[-1,3,-13],[1,-1,-15]],[1,1],None,400,True,48),  # line 432
    '[100/63, 7/22, 27/2, 11/5, 22/3]': ('ndx',[1,2],{},[[1,0,-6],[0,1,-2],[-2,3,-2],[1,-1,-6]],[1,1],None,400,True,48),  # line 433
    '[100/63, 7/22, 27/2, 11/5, 7/3]': ('ndx',[1,2],{},[[1,0,-6],[0,1,-2],[-2,3,-2],[1,-1,-6]],[1,1],None,400,True,45),  # line 434
    '[11/105, 10/3, 243/55, 7/2, 55/7]': ('ndx',[0,2],{},[[1,0,-5],[0,1,-5],[-2,3,-12],[1,-1,-3],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,True,192),  # line 435
    '[11/105, 10/3, 27/22, 49/2, 12/7]': ('ndx',[0,2],{},[[1,0,-9],[0,1,-8],[-1,1,-4],[3,-2,-14],[0,1,-28],[14,-8,-105],[0,1,-29],[0,1,-30],[0,1,-31],[0,1,-32],[0,1,-33],[0,1,-34]],[1,1],None,400,False,299),  # line 436
    '[11/105, 10/3, 27/22, 49/2, 44/7]': ('ndx',[0,2],{},[[1,0,-5],[0,1,-4],[-1,1,-3],[3,-2,-7],[0,1,-24],[12,-7,-90],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,500),  # line 437
    '[11/105, 10/3, 27/22, 49/2, 6/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-5],[-4,3,-12],[2,-1,0],[1,0,-9],[0,1,-25],[1,0,-16],[-5,4,-60]],[1,1],None,400,False,540),  # line 438
    '[11/105, 10/3, 27/22, 49/2, 66/7]': ('ndx',[0,2],{},[[1,0,-5],[0,1,-5],[-1,1,-5],[3,-2,-6],[8,-5,-60]],[1,1],None,400,False,702),  # line 439
    '[11/105, 10/3, 27/2695, 49/2, 3/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-3],[0,1,-8],[1,0,-6],[0,1,-13],[1,0,-10],[0,1,-25],[1,0,-20],[-5,4,-48],[-5,4,-56],[1,0,-21],[-5,4,-63]],[1,2],'1',400,False,1534),  # line 440
    '[11/105, 10/3, 81/539, 7/2, 9/7]': ('add',2,[['4','3'],[],['8','12','4'],[],[]],2,[[14,3660],[15,4160],[16,4692],[17,5256]]),  # line 441
    '[11/105, 13/3, 18/143, 5/169, 2541/2]': ('nd',[0,3,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,0,1,0,5465],[1,0,0,-1,0],[-1,-5,1,2,1],[1,5,-1,-2,-1],[0,0,1,0,-5]],[1,1,1,1],None,400,True,28),  # line 442
    '[11/105, 15/22, 4/3, 49/2, 135/7]': ('ndxz',[0,2],{},[[1,-1,-1],[-1,1,4],[0,1,-10]],[3,3],'8c',1000,True,151),  # line 443
    '[11/105, 15/22, 4/3, 49/2, 198/7]': ('ndxz',[0,2],{},[[1,-1,-1],[-1,1,4],[0,1,-10]],[3,3],'8c',1000,True,164),  # line 444
    '[11/105, 15/22, 4/3, 49/2, 99/49]': ('ndxz',[0,2],{},[[1,-1,-1],[-1,1,4],[0,1,-10]],[3,3],'8c',1000,True,138),  # line 445
    '[11/105, 15/22, 8/3, 35/2, 99/5]': ('mul',2,[[],[],['-2','3'],['-1','2'],[]],9,1,[[81,601],[729,5461],[6561,49201],[59049,442861]]),  # line 446
    '[11/105, 18/143, 13/3, 5/169, 2541/2]': ('nd',[0,1,3,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[1,-1,0,0,0],[-1,2,-5,1,1],[1,-2,5,-1,-1],[0,0,0,1,-4]],[1,1,1,1],None,400,True,27),  # line 447
    '[11/105, 2/3, 567/55, 5/2, 231/5]': ('ndcv',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-8],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,400,False,684),  # line 448
    '[11/105, 2/3, 567/55, 5/2, 63/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-4],[1,0,-10],[0,1,-7],[0,1,-15]],[1,1],None,400,False,20813),  # line 449
    '[11/105, 20/3, 27/77, 91/2, 55/13]': ('ndx',[2,3,5],{},[[1,0,0,-4],[0,1,0,-6],[0,0,1,-6],[-5,3,0,-6],[0,1,0,-30],[1,0,0,-12],[1,0,0,-13]],[1,1,1],None,3000,True,178),  # line 450
    '[11/105, 20/3, 3/22, 7/2, 891/7]': ('add',2,[['9','10'],[],['5','8','2'],[],[]],2,[[13,7353],[14,8478],[15,9683],[16,10968]]),  # line 451
    '[11/105, 20/3, 81/55, 35/2, 3/5]': ('ndcv',[0,2],{},[[1,0,-25],[0,1,-8],[-1,4,-8]],[1,1],None,400,False,180),  # line 452
    '[11/105, 243/55, 10/3, 7/2, 55/7]': ('ndx',[0,2],{},[[1,0,-5],[0,1,-5],[-2,3,-12],[1,-1,-3],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,True,192),  # line 453
    '[11/105, 27/1925, 14/3, 25/2, 3/5]': ('ndcv',[2,3],{},[[1,0,-3],[0,1,-1],[1,-2,-6],[0,1,-6],[0,1,-10],[0,1,-20],[0,1,-21]],[1,1],None,400,False,1534),  # line 454
    '[11/105, 27/55, 10/3, 35/2, 63/5]': ('ndcv',[2,3],{},[[1,0,-1],[0,1,-1],[0,1,-3],[1,0,-5],[0,1,-5],[1,0,-8],[0,1,-12],[3,-4,-18],[-1,2,0],[0,1,-13],[3,-4,-19]],[1,1],None,400,False,196),  # line 455
    '[11/105, 4/3, 15/22, 49/2, 135/7]': ('ndxz',[0,2],{},[[1,0,-2955],[0,1,-2951],[-1,1,4],[1,-1,-1]],[3,3],'84',300,True,35407),  # line 456
    '[11/105, 4/3, 15/22, 49/2, 198/7]': ('ndxz',[0,2],{},[[1,0,-2955],[0,1,-2951],[-1,1,4],[1,-1,-1]],[3,3],'84',1000,True,38358),  # line 457
    '[11/105, 4/3, 15/22, 49/2, 99/49]': ('ndxz',[0,2],{},[[1,0,-2955],[0,1,-2951],[-1,1,4],[1,-1,-1]],[3,3],'84',300,True,32456),  # line 458
    '[11/105, 45/22, 80/3, 7/2, 3/7]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-1],[0,1,-6],[0,1,-16],[0,1,-20],[1,0,-10],[1,0,-25],[1,0,-26]],[1,1],None,144,False,537),  # line 459
    '[11/105, 5/66, 16/5, 21/2, 25/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-1],[-1,1,-1],[3,-2,-16],[3,-2,-22],[3,-2,-46],[3,-2,-56]],[1,6],'6',400,False,3201),  # line 460
    '[11/105, 5/66, 2401/11, 6/7, 121/2]': ('ndx',[0,1],{},[[1,0,-8],[0,1,-8],[-2,3,-23],[1,-1,-7]],[3,2],'3c',400,True,138),  # line 461
    '[11/105, 567/55, 2/3, 5/2, 231/5]': ('ndcv',[1,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-8],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,400,False,681),  # line 462
    '[11/105, 567/55, 2/3, 5/2, 63/5]': ('ndcv',[1,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-5],[0,0,1,-7],[0,0,1,-15]],[1,1,1],None,400,False,9169),  # line 463
    '[11/105, 567/55, 2/3, 65/2, 77/13]': ('ndcv',[1,2,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-6],[0,0,0,1,-15],[-2,-3,-2,1,2],[2,3,2,-1,-2],[0,0,1,0,-12],[0,0,1,0,-13]],[1,1,1,1],None,400,False,733),  # line 464
    '[11/105, 63/110, 4/3, 5/2, 99/5]': ('ndcv',[0,3],{},[[1,0,-6],[0,1,-1],[0,1,-4],[0,1,-6],[1,0,-8],[0,1,-8],[2,-3,-20],[2,-3,-28],[2,-3,-40],[0,1,-9],[1,0,-34],[1,0,-35],[1,0,-36]],[1,1],None,400,False,548),  # line 465
    '[11/105, 81/275, 14/3, 5/2, 9/5]': ('add',2,[['4','3'],[],[],['8','12','4'],[]],2,[[14,3660],[15,4160],[16,4692],[17,5256]]),  # line 466
    '[11/105, 81/55, 20/3, 35/2, 3/5]': ('ndx',[0,1],{},[[1,0,-9],[0,1,-8],[-1,2,-8],[-1,2,-20],[-1,2,-22]],[1,1],None,3000,False,122),  # line 467
    '[11/1575, 343/33, 10/7, 9/2, 7/3]': ('ndx',[2,1],{},[[1,0,-1],[0,1,-1],[0,1,-6],[0,1,-14],[0,1,-22],[0,1,-28],[0,1,-36],[0,1,-44],[0,1,-88],[0,1,-89],[0,1,-90],[0,1,-91],[0,1,-92],[0,1,-93],[0,1,-94],[0,1,-95],[0,1,-96],[0,1,-97],[0,1,-98],[0,1,-99],[0,1,-100],[0,1,-101],[0,1,-102],[0,1,-103],[0,1,-104],[0,1,-106]],[1,1],None,3000,False,160258),  # line 468
    '[11/1575, 6/7, 343/55, 25/2, 7/5]': ('ndx',[1,2],{},[[1,0,-14],[0,1,-214],[-7,1,0],[1,0,-30],[1,0,-31]],[1,1],None,300,False,175840),  # line 469
    '[11/315, 125/22, 6/5, 21/2, 10/3]': ('ndcv',[1,3],{},[[1,0,-1],[0,1,-1],[2,-5,5],[0,1,-5],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,268),  # line 470
    '[11/315, 125/33, 12/5, 21/2, 5/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-1],[-1,2,0],[1,-1,-2],[0,1,-6],[0,1,-9],[1,0,-35],[-3,7,-35],[1,0,-36],[1,0,-37],[-3,7,-43]],[1,1],None,400,False,233),  # line 471
    '[11/315, 125/33, 2/5, 63/2, 25/7]': ('ndx',[1,3],{},[[1,0,-2],[0,1,-1],[-2,3,12],[0,1,-5],[0,1,-7],[0,1,-15],[1,0,-28],[1,0,-29],[1,0,-36]],[1,1],None,400,False,164),  # line 472
    '[11/315, 125/33, 4/5, 63/2, 5/7]': ('ndx',[1,3],{},[[1,0,-2],[0,1,-1],[-1,2,3],[0,1,-6],[0,1,-9],[0,1,-15],[1,0,-35],[-3,7,-21],[1,0,-36],[1,0,-37]],[1,1],None,400,False,61),  # line 473
    '[11/315, 125/33, 6/5, 63/2, 5/3]': ('ndx',[1,3],{},[[1,0,-2],[0,1,-1],[0,1,-5],[0,1,-8],[0,1,-15],[3,-7,-15],[-1,3,-2],[3,-7,-16]],[1,1],None,3000,False,145),  # line 474
    '[11/315, 175/22, 4/5, 3/2, 275/3]': ('ndcv',[1,3],{},[[1,0,-7],[0,1,-1],[1,-3,-8],[1,0,-24],[1,0,-28],[1,0,-32],[0,1,-8],[0,1,-9]],[1,1],None,400,True,248),  # line 475
    '[11/315, 2/5, 375/77, 21/2, 77/3]': ('add',5,[[],['30','385/2','675/2'],[],[],['11','30']],2,[[9,177502]]),  # line 476
    '[11/315, 2/5, 375/77, 63/2, 5/3]': ('add',3,[[],['14','53/2','27/2'],[],['4','4'],[]],10,[[49,67648],[50,70378],[51,73162],[52,76000]]),  # line 477
    '[11/315, 2/5, 875/33, 9/2, 77/3]': ('ndcv',[1,3],{},[[1,0,-6],[0,1,-2],[0,1,-4],[0,1,-8],[2,-7,-36],[2,-7,-40]],[1,1],None,1000,False,325),  # line 478
    '[11/315, 3/22, 625/11, 14/5, 121/2]': ('add',2,[['8','21'],[],[],['8','32','28'],[]],4,[[19,41678],[20,46111],[21,50768],[22,55649]]),  # line 479
    '[11/315, 375/77, 2/5, 21/2, 77/3]': ('add',5,[[],['30','385/2','675/2'],[],[],['11','30']],2,[[9,177502]]),  # line 480
    '[11/315, 375/77, 2/5, 63/2, 5/3]': ('add',3,[[],['14','53/2','27/2'],[],['4','4'],[]],10,[[49,67648],[50,70378],[51,73162],[52,76000]]),  # line 481
    '[11/315, 375/77, 4/5, 21/2, 5/3]': ('ndcv',[1,3],{},[[1,0,-1],[0,1,-1],[0,1,-6],[0,1,-10],[0,1,-21],[4,-5,-19]],[1,2],'2',400,False,489),  # line 482
    '[11/315, 375/77, 6/5, 21/2, 5/3]': ('add',3,[[],['10','53/2','27/2'],[],['4','4'],[]],10,[[49,67642],[50,70372],[51,73156],[52,75994]]),  # line 483
    '[11/315, 4/5, 375/77, 21/2, 5/3]': ('ndcv',[1,3],{},[[1,0,-1],[0,1,-1],[0,1,-6],[0,1,-10],[0,1,-21],[4,-5,-19]],[1,2],'2',400,False,489),  # line 484
    '[11/315, 6/5, 125/22, 21/2, 10/3]': ('ndcv',[1,3],{},[[1,0,-1],[0,1,-1],[2,-5,5],[0,1,-5],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,268),  # line 485
    '[11/315, 6/5, 125/33, 63/2, 5/3]': ('ndx',[1,4],{},[[1,0,-4],[0,1,-9]],[1,1],None,400,False,82),  # line 486
    '[11/315, 6/5, 375/77, 21/2, 5/3]': ('add',3,[[],['10','53/2','27/2'],[],['4','4'],[]],10,[[49,67642],[50,70372],[51,73156],[52,75994]]),  # line 487
    '[11/315, 6/5, 625/77, 7/2, 25/7]': ('ndx',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-11]],[1,1,1],None,400,False,185),  # line 488
    '[11/315, 6/5, 625/77, 7/2, 55/7]': ('ndx',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-10]],[1,1,1],None,400,False,118),  # line 489
    '[11/315, 625/77, 2/5, 21/2, 25/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-1],[-2,3,-1],[1,-1,-3],[1,0,-40],[-5,8,-40],[1,0,-41],[1,-1,-4],[1,0,-42],[1,0,-43],[-5,8,-42]],[1,1],None,1000,False,436),  # line 490
    '[11/315, 625/77, 2/5, 21/2, 55/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-1],[-2,3,-6],[1,-1,-6],[1,0,-40],[-5,8,-40],[1,0,-41],[-5,8,-44]],[1,1],None,1000,False,209),  # line 491
    '[11/315, 625/77, 6/5, 7/2, 25/7]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-2],[-1,1,-3],[4,-3,-3],[0,1,-40],[0,1,-41],[-1,1,-4],[0,1,-42],[0,1,-43]],[1,1],None,1000,False,343),  # line 492
    '[11/315, 625/77, 6/5, 7/2, 55/7]': ('ndx',[0,1],{},[[1,0,-4],[0,1,-5],[-1,1,-7],[4,-3,-11],[0,1,-40],[0,1,-41]],[1,1],None,1000,False,311),  # line 493
    '[11/315, 875/33, 2/5, 9/2, 77/3]': ('ndcv',[1,3],{},[[1,0,-6],[0,1,-2],[0,1,-4],[0,1,-8],[2,-7,-36],[0,1,-9]],[1,1],None,1000,False,325),  # line 494
    '[11/420, 63/5, 25/77, 2/3, 25/2]': ('ndcv',[0,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[0,1,-9],[0,1,-20],[0,1,-21],[0,1,-22]],[1,1],None,400,False,898),  # line 495
    '[11/420, 63/5, 25/77, 2/3, 77/2]': ('ndcv',[0,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[0,1,-9],[0,1,-20],[0,1,-21],[0,1,-22]],[1,1],None,400,False,974),  # line 496
    '[11/630, 175/2, 4/77, 3/5, 4/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[0,1,-9],[0,1,-20],[0,1,-21],[0,1,-22]],[1,1],None,400,False,905),  # line 497
    '[11/630, 175/2, 4/77, 3/5, 77/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[0,1,-9],[0,1,-20],[0,1,-21],[0,1,-22]],[1,1],None,400,False,981),  # line 498
    '[11/630, 28/5, 25/77, 3/2, 25/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[0,1,-9],[0,1,-20],[0,1,-21],[0,1,-22]],[1,1],None,400,False,899),  # line 499
    '[11/630, 28/5, 25/77, 3/2, 77/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[0,1,-9],[0,1,-20],[0,1,-21],[0,1,-22]],[1,1],None,400,False,975),  # line 500
    '[112/45, 21/22, 5/2, 11/7, 6/5]': ('nd',[0,2,3,4],{},[[1,0,0,0,-4],[0,1,0,0,-4],[0,0,1,0,-1],[0,0,0,1,-1],[1,1,-1,-1,-7]],[1,1,1,1],None,1000,True,115),  # line 501
    '[1323/50, 33/2, 4/77, 5/3, 7/5]': ('ndxz',[2,4],{},[[1,0,-21],[0,1,-9],[-1,4,0],[7,-16,0]],[1,1],None,300,True,74),  # line 502
    '[14/15, 1/147, 11/3, 99/2, 5/11, 21/5]': ('nd',[2,3],{'1': 1},[[1,0,-2],[0,1,-1],[1,0,-5],[1,0,-8],[1,1,-16],[1,-1,-16],[1,-1,-18]],[1,1],None,1000,False,232),  # line 546
    '[14/15, 1/147, 99/2, 11/3, 5/11, 21/5]': ('nd',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-8],[0,1,0,-12],[0,1,0,-16],[4,-1,0,-16],[6,-1,2,-38],[0,1,0,-17],[0,1,0,-18],[4,-1,0,-18],[0,1,0,-19]],[1,1,1],None,1000,False,266),  # line 547
    '[14/15, 1/3, 1/605, 99/7, 125/2, 3/5]': ('ndcv',[0,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,0,-1,0],[1,0,0,-4],[1,0,0,-5]],[1,1,1],None,400,True,60),  # line 584
    '[14/15, 1/3, 3/110, 693/2, 5/7, 2/11]': ('add',10,[[],[],[],['1','12'],['1','2']],1,[[4,2819],[5,4323],[6,6147],[7,8291]]),  # line 589
    '[14/15, 1/3, 3/110, 693/2, 5/7, 3/11]': ('add',10,[[],[],[],['1','12'],['1','2']],1,[[4,2771],[5,4263],[6,6075],[7,8207]]),  # line 590
    '[14/15, 1/363, 1/5, 275/7, 27/2, 5/3]': ('ndcv',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,0,-1,0],[1,0,0,-4],[1,0,0,-5]],[1,1,1],None,400,True,60),  # line 593
    '[14/15, 1/363, 11/35, 25/7, 9/2, 5/3]': ('nd',[4,0],{},[[1,0,-1],[0,1,-3],[-2,1,-7],[0,1,-15],[0,1,-16]],[1,1],None,400,True,111),  # line 594
    '[14/15, 1/363, 275/7, 1/5, 27/2, 5/3]': ('ndcv',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,0,-1,0],[1,0,0,-4],[1,0,0,-5]],[1,1,1],None,400,True,60),  # line 595
    '[14/15, 1/6, 4719/2, 3/169, 5/11, 3/7]': ('nd',[3,4,5],{'0': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,-1,-3],[0,0,1,-8],[0,0,1,-16],[0,4,-1,-63]],[1,1,1],None,1000,False,246),  # line 624
    '[14/15, 1/66, 63/2, 11/3, 25/7, 2/11]': ('ndcv',[1,3],{},[[1,0,-1],[0,1,-1],[1,0,-4],[0,1,-4],[1,0,-7],[1,0,-10],[-3,2,-4],[-3,2,-5]],[1,1],None,400,False,441),  # line 647
    '[14/15, 1/66, 63/2, 11/3, 5/7, 10/11]': ('ndx',[3,4],{},[[1,0,-479],[0,1,-196],[-2,5,0],[9,-20,0]],[1,1],None,300,False,1967),  # line 648
    '[14/15, 1/66, 63/2, 11/3, 5/7, 21/11]': ('nd',[4,3],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,577),  # line 649
    '[14/15, 1/66, 63/2, 11/3, 5/7, 3/11]': ('ndx',[1,3],{},[[1,0,-92],[0,1,-202],[-2,1,0],[5,-2,0]],[1,1],None,300,False,770),  # line 650
    '[14/15, 1/66, 63/2, 11/3, 5/7, 4/11]': ('nd',[4,2],{'0': 2},[[1,0,-3],[0,1,-2],[-2,1,-10],[3,-1,-30],[3,-1,-34]],[1,1],None,400,False,1542),  # line 651
    '[14/15, 1/66, 63/2, 11/3, 5/7, 6/11]': ('ndx',[3,4],{},[[1,0,-104],[0,1,-52],[-3,8,0],[1,-2,0],[-1,3,-24],[-1,3,-36]],[1,1],None,300,False,442),  # line 652
    '[14/15, 1/66, 63/2, 11/9, 5/7, 2/11]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[-2,1,-2],[1,0,-8],[1,0,-20]],[1,1],None,400,True,236),  # line 653
    '[14/15, 1/66, 63/2, 11/9, 5/7, 3/11]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[1,0,-4],[1,0,-8],[0,1,-6],[0,1,-10],[1,-3,-4],[1,-3,-10],[1,-3,-16]],[1,1],None,400,False,262),  # line 654
    '[14/15, 1/66, 63/2, 121/3, 5/7, 3/11]': ('ndx',[3,4],{},[[-895,1000,0],[995,-1000,0],[1,0,-30000]],[1,2],'1',1000,False,176100),  # line 656
    '[14/15, 1/66, 63/2, 77/3, 5/7, 2/11]': ('mul',2,[[],['3/4','5/4'],[],['-11/4','15/4'],[]],5,6,[[125,1454],[625,7385],[3125,37066],[15625,185497]]),  # line 657
    '[14/15, 1/66, 63/2, 77/3, 5/7, 3/11]': ('mul',2,[[],['3/4','5/4'],[],['-7/4','11/4'],[]],5,6,[[125,1063],[625,5373],[3125,26933],[15625,134743]]),  # line 658
    '[14/15, 1/66, 9/2, 77/3, 5/7, 14/11]': ('mul',4,[[],[],[],['-10','12'],['-3','5']],3,1,[[27,2577],[81,8467],[243,26345],[729,80187]]),  # line 660
    '[14/15, 1/66, 9/2, 77/3, 5/7, 15/11]': ('mul',4,[[],[],[],['-10','12'],['-3','5']],3,1,[[27,2589],[81,8483],[243,26365],[729,80211]]),  # line 661
    '[14/15, 1/66, 9/2, 77/3, 5/7, 2/121]': ('mul',4,[[],[],[],['-7','9'],['1','1']],3,1,[[27,2547],[81,8291],[243,25699],[729,78099]]),  # line 662
    '[14/15, 1/66, 9/2, 77/3, 5/7, 3/121]': ('mul',4,[[],[],[],['-7','24'],['0','3']],3,1,[[9,2229],[27,7279],[81,22589],[243,68679]]),  # line 663
    '[14/15, 1/66, 9/2, 77/3, 5/7, 4/11]': ('mul',4,[[],[],[],['-7','24'],['0','3']],3,1,[[9,2253],[27,7311],[81,22629],[243,68727]]),  # line 664
    '[14/15, 1/726, 63/2, 11/3, 5/7, 2/11]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-2],[1,-2,-2],[1,0,-8],[0,1,-10],[0,1,-14],[0,1,-20],[2,-3,-29],[2,-3,-31],[2,-3,-33]],[1,1],None,400,False,338),  # line 665
    '[14/15, 1/726, 9/2, 77/3, 5/7, 3/11]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-2],[1,-2,0],[1,0,-8],[1,0,-16],[0,1,-20]],[1,1],None,400,True,490),  # line 666
    '[14/15, 11/21, 1/605, 9/7, 25/2, 3/5]': ('nd',[4,0],{},[[1,0,-1],[0,1,-3],[-2,1,-7],[0,1,-15],[0,1,-16]],[1,1],None,1000,True,111),  # line 671
    '[14/15, 18/77, 11/6, 125/11, 77/2]': ('mul',2,[['1/2','9/2'],['-1/2','9/2'],[],[],[]],9,1,[[81,2548],[729,22960],[6561,206668],[59049,1860040]]),  # line 678
    '[14/15, 3/154, 25/2, 121/5, 56/11]': ('ndxz',[4,1],{},[[1,0,-1],[0,1,-187],[-23,1,0]],[3,9],'3de00',1000,True,1903),  # line 679
    '[14/15, 3/154, 25/2, 121/5, 60/11]': ('ndxz',[1,4],{},[[1,0,-189],[0,1,-1],[1,-9,0]],[12,3],'490490492',300,True,2080),  # line 680
    '[14/15, 5/66, 1/5, 1925/2, 3/7, 2/11]': ('add',10,[[],[],[],['1','12'],['1','2']],1,[[4,2819],[5,4323],[6,6147],[7,8291]]),  # line 726
    '[14/15, 5/66, 1/5, 1925/2, 3/7, 5/11]': ('add',10,[[],[],[],['1','12'],['1','2']],1,[[4,2771],[5,4263],[6,6075],[7,8207]]),  # line 727
    '[14/15, 5/66, 1925/2, 1/5, 3/7, 2/11]': ('add',10,[[],[],[],['1','12'],['1','2']],1,[[4,2819],[5,4323],[6,6147],[7,8291]]),  # line 728
    '[14/15, 5/66, 1925/2, 1/5, 3/7, 5/11]': ('add',10,[[],[],[],['1','12'],['1','2']],1,[[4,2771],[5,4263],[6,6075],[7,8207]]),  # line 729
    '[14/15, 5/66, 275/2, 7/5, 3/7, 2/11]': ('add',10,[[],[],[],['2','24'],['1','4']],1,[[3,3123],[4,5443],[5,8403],[6,12003]]),  # line 730
    '[14/15, 5/66, 7/5, 275/2, 3/7, 2/11]': ('add',10,[[],[],[],['2','24'],['1','4']],1,[[3,3123],[4,5443],[5,8403],[6,12003]]),  # line 731
    '[14/15, 5/66, 7/5, 275/2, 3/7, 5/11]': ('add',5,[[],[],[],['2','12'],['1','2']],1,[[4,1403],[5,2153],[6,3063],[7,4133]]),  # line 732
    '[14/15, 63/22, 3125/2, 11/7, 3/5]': ('nd',[0,1,3,4],{},[[1,0,0,0,-31],[0,1,0,0,-1],[0,0,1,0,-105],[0,0,0,1,-1],[1,0,0,-1,-30],[-3,-2,1,0,2],[3,2,-1,0,-2],[0,1,0,0,-20],[0,1,0,0,-21],[0,1,0,0,-22]],[1,1,1,1],None,400,False,728),  # line 737
    '[14/15, 63/22, 625/2, 11/7, 14/5]': ('ndx',[2,3],{},[[1,0,-7],[0,1,-1],[-1,3,0],[1,-1,-8],[0,1,-5]],[1,1],None,400,True,32),  # line 738
    '[14/15, 63/22, 625/2, 11/7, 6/5]': ('ndx',[2,3],{},[[1,0,-10],[0,1,-1],[1,-1,-14],[0,1,-4]],[1,1],None,400,True,14),  # line 739
    '[14/15, 7/3, 3/110, 99/2, 5/7, 2/11]': ('add',10,[[],[],[],['2','24'],['1','4']],1,[[3,3123],[4,5443],[5,8403],[6,12003]]),  # line 774
    '[14/15, 7/3, 3/110, 99/2, 5/7, 3/11]': ('add',5,[[],[],[],['2','12'],['1','2']],1,[[4,1403],[5,2153],[6,3063],[7,4133]]),  # line 775
    '[14/15, 7/66, 9/2, 77/3, 5/7, 2/11]': ('ndx',[4,3],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2597),  # line 797
    '[14/15, 9/22, 21875/2, 11/7, 2/5]': ('nd',[0,1,3,4],{},[[1,0,0,0,-32],[0,1,0,0,-1],[0,0,1,0,-70],[0,0,0,1,-1],[1,0,0,-1,-31],[-2,-1,1,0,2],[2,1,-1,0,-2],[0,1,0,0,-20],[0,1,0,0,-21],[0,1,0,0,-22]],[1,1,1,1],None,400,False,723),  # line 798
    '[14/15, 9/22, 21875/2, 11/7, 3/11]': ('nd',[0,1,3,4],{},[[1,0,0,0,-36],[0,1,0,0,-1],[0,0,1,0,-75],[0,0,0,1,-1],[1,0,0,-1,-78],[-2,-1,1,0,1],[2,1,-1,0,-1],[0,1,0,0,-20],[0,1,0,0,-21],[0,1,0,0,-22]],[1,1,1,1],None,400,False,743),  # line 799
    '[14/15, 9/22, 27625/2, 11/7, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-1],[1,-1,0,0,-6],[0,0,-1,1,0],[0,0,1,-1,0],[-1,2,-1,0,4],[1,-2,1,0,-4],[-1,2,0,0,-8],[-1,2,0,0,-12],[-1,2,0,0,-13]],[1,1,1,1],None,400,False,146),  # line 800
    '[14/15, 9/22, 4375/2, 11/7, 3/11]': ('ndx',[2,3],{},[[1,0,-4],[0,1,-1],[-1,3,-3],[1,-1,-7]],[1,1],None,400,True,14),  # line 801
    '[14/15, 9/22, 4375/2, 11/7, 4/5]': ('ndx',[2,3],{},[[1,0,-4],[0,1,-1],[-1,3,-2],[1,-1,-8]],[1,1],None,400,True,9),  # line 802
    '[14/15, 9/22, 625/2, 11/7, 154/5]': ('ndx',[2,3],{},[[1,0,-9],[0,1,-3],[-1,3,-20],[2,-3,-23]],[1,1],None,400,True,79),  # line 803
    '[14/15, 9/22, 625/2, 11/7, 242/5]': ('ndx',[2,3],{},[[1,0,-11],[0,1,-4],[-1,3,-27],[2,-3,-30]],[1,1],None,400,True,111),  # line 804
    '[14/15, 9/22, 625/2, 11/7, 3/25]': ('ndx',[2,3],{},[[1,0,-5],[0,1,-1],[-1,3,-6],[2,-3,-9]],[1,1],None,400,True,30),  # line 805
    '[14/15, 9/22, 625/2, 11/7, 63/5]': ('ndx',[2,3],{},[[1,0,-9],[0,1,-3],[-1,3,-20],[2,-3,-23]],[1,1],None,400,True,76),  # line 806
    '[14/15, 9/22, 625/2, 11/7, 98/5]': ('ndx',[2,3],{},[[1,0,-7],[0,1,-2],[-1,3,-13],[2,-3,-16]],[1,1],None,400,True,47),  # line 807
    '[14/15, 9/22, 625/2, 11/7, 99/5]': ('ndx',[2,3],{},[[1,0,-11],[0,1,-4],[-1,3,-27],[2,-3,-30]],[1,1],None,400,True,108),  # line 808
    '[14/15, 9/22, 8125/2, 11/7, 21/13]': ('ndx',[2,3,5],{},[[1,0,0,-7],[0,1,0,-2],[0,0,1,-1],[-2,3,1,7],[2,-3,-1,-7],[0,1,0,-4]],[1,1,1],None,400,True,17),  # line 809
    '[14/15, 9/22, 8125/2, 11/7, 33/13]': ('ndx',[2,3,5],{},[[1,0,0,-9],[0,1,0,-3],[0,0,1,-2],[-2,3,1,7],[2,-3,-1,-7],[0,1,0,-4]],[1,1,1],None,400,True,30),  # line 810
    '[14/15, 9/242, 175/2, 11/7, 12/11]': ('nd',[1,4],{},[[1,0,-42],[0,1,-2],[0,1,-10],[0,1,-14],[0,1,-22],[0,1,-23],[0,1,-24]],[5,5],'7000',400,False,648),  # line 811
    '[14/15, 9/77, 1250/7, 11/2, 49/11]': ('ndx',[0,2],{},[[1,0,-2],[0,1,-8],[-1,1,-13],[4,-1,-2],[1,0,-6]],[1,1],None,400,True,37),  # line 812
    '[14/15, 9/847, 50/7, 11/2, 147/11]': ('mul',2,[[],[],['0','30'],[],['-2','60']],3,1,[[9,3112],[27,9376],[81,28168],[243,84544]]),  # line 813
    '[14/45, 1/1694, 5/7, 891/2, 5/3]': ('ndcv',[1,4],{},[[1,0,-4],[0,1,-1],[0,1,-8],[2,-3,-20],[2,-3,-40],[0,1,-9],[2,-3,-41]],[1,1],None,400,False,187),  # line 814
    '[14/45, 1/1694, 5/7, 891/2, 7/3]': ('ndcv',[1,4],{},[[1,0,-4],[0,1,-1],[0,1,-8],[2,-3,-20],[2,-3,-40],[0,1,-9],[2,-3,-41]],[1,1],None,400,False,205),  # line 815
    '[14/45, 1/18, 297/2, 25/33, 3/7]': ('ndx',[2,3],{},[[1,0,-4],[0,1,-2],[1,0,-6],[1,0,-9],[1,0,-15],[1,0,-75],[1,0,-77],[1,0,-78],[1,0,-80],[1,0,-83]],[1,1],None,1000,False,507),  # line 816
    '[14/45, 1323/2, 11/63, 5/7, 3/11]': ('ndx',[1,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,-7],[0,1,-1,-8],[1,0,0,-8],[-1,2,0,-30],[1,0,0,-9]],[1,1,1],None,400,False,62),  # line 817
    '[14/45, 27/22, 375/2, 11/7, 2/5]': ('ndx',[0,1,3,4],{},[[1,0,0,0,-22],[0,1,0,0,-1],[0,0,1,0,-83],[0,0,0,1,-1],[1,0,0,-1,-21],[-3,-1,1,0,4],[3,1,-1,0,-4],[0,1,0,0,-20],[0,1,0,0,-21]],[1,1,1,1],None,3000,False,519),  # line 818
    '[14/45, 27/22, 375/2, 11/7, 3/5]': ('nd',[0,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-4,-1,1,4],[4,1,-1,-4],[0,0,1,-4],[0,1,0,-12],[0,1,0,-13]],[1,1,1],None,400,True,67),  # line 819
    '[14/45, 27/77, 50/7, 11/2, 49/11]': ('nd',[1,4],{},[[1,0,-16],[0,1,-1],[0,1,-5],[0,1,-8],[0,1,-13],[0,1,-14]],[3,3],'22',400,False,159),  # line 820
    '[14/45, 550/49, 1/847, 9/2, 7/3]': ('ndx',[1,4],{},[[1,0,-22],[0,1,-1],[1,-3,-30],[0,1,-8],[0,1,-9],[2,-1,-106]],[1,1],None,400,False,361),  # line 821
    '[15/2, 1/539, 4/33, 7/27, 11/5, 3/11]': ('nd',[2,3],{},[[1,0,-3],[0,1,-1],[1,-1,-6]],[1,1],None,1000,'all',60),  # line 822
    '[154/15, 9/182, 2125/2, 13/11, 3/17]': ('nd',[2,3,4,6],{},[[1,0,0,0,-5],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-1],[1,-1,0,0,-6],[0,-1,1,0,0],[0,1,-1,0,0],[-1,2,0,-1,4],[1,-2,0,1,-4],[-1,0,2,0,-8],[-1,0,2,0,-12],[-1,0,2,0,-13]],[1,1,1,1],None,400,False,146),  # line 835
    '[154/15, 9/686, 125/2, 7/11, 3/5]': ('ndx',[2,3],{},[[1,0,-4],[0,1,-2],[-1,1,0],[4,-3,-11],[-1,2,-24],[-1,2,-25],[-1,2,-27]],[1,1],None,400,False,243),  # line 836
    '[16/105, 5/6, 77/2, 3/7, 98/11]': ('ndxz',[2,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-13],[0,-1,1,-23],[1,0,0,-4],[1,0,0,-5]],[1,1,1],None,400,True,85),  # line 837
    '[16/15, 1/14, 3/2, 77/3, 5/11, 9/7]': ('ndcv',[0,2],{},[[1,0,-1],[0,1,-1],[1,3,-32],[0,1,-4]],[3,1],'6',400,True,88),  # line 838
    '[16/15, 3/154, 35/2, 11/5, 15/7]': ('nd',[0,3],{},[[1,0,-20],[0,1,-4],[-1,3,3]],[1,1],None,400,False,151),  # line 839
    '[16/15, 3/154, 35/2, 11/5, 75/7]': ('ndcv',[3,4],{'0': 7},[[1,0,-4],[0,1,-6],[-2,3,-12],[1,-1,-3],[0,1,-32],[0,1,-33],[0,1,-34],[8,-9,-6],[0,1,-35],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39]],[1,1],None,400,False,250),  # line 840
    '[175/18, 14/55, 3993/2, 3/7, 2/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-3],[-1,2,-11],[5,-3,-1],[1,0,-8],[1,-1,-16],[1,-1,-18],[1,-1,-19]],[1,1],None,400,False,417),  # line 841
    '[175/18, 14/55, 3993/2, 3/7, 5/3]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-3],[-1,2,-11],[7,-3,0],[1,0,-10],[1,-1,-20]],[1,1],None,400,False,431),  # line 842
    '[175/18, 2/55, 27951/2, 3/7, 5/11]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-3],[-2,3,-8],[1,-1,-1]],[1,1],None,400,True,40),  # line 843
    '[175/18, 4/77, 363/2, 9/5, 2/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-2],[-1,3,-7],[3,-2,0],[1,0,-10],[1,0,-16],[-1,4,-20],[1,-2,-24],[1,-2,-25]],[1,1],None,400,False,571),  # line 844
    '[175/18, 77/2, 28/55, 3/7, 25/3]': ('ndxz',[1,4],{},[[1,0,-181],[0,1,-49],[-1,4,0],[7,-25,0]],[1,1],None,300,True,534),  # line 845
    '[175/54, 4/55, 77/2, 9/7, 5/3]': ('nd',[4,1],{},[[1,0,-1],[0,1,-8],[-3,1,-8],[5,-1,-6],[1,0,-8],[1,0,-9]],[1,1],None,400,True,70),  # line 846
    '[175/54, 77/2, 4/55, 9/7, 5/3]': ('ndx',[1,4],{},[[1,0,-94],[0,1,-21],[-1,5,0],[6,-25,0]],[1,1],None,300,False,186),  # line 847
    '[18/35, 1/110, 75/2, 11/5, 7/3, 5/11]': ('mul',2,[[],['0','8'],[],[],['1','1']],8,6,[[512,7770],[4096,62046],[32768,496226]]),  # line 854
    '[18/35, 1/33, 10/39, 143/2, 1029/11]': ('mul',1,[['-2','6'],[],['-1','2'],[],[],[]],2,15,[[64,1905],[128,3825],[256,7665],[512,15345]]),  # line 859
    '[18/35, 10/33, 7/6, 1331/7, 35/2]': ('mul',2,[['1/2','9/2'],['-1/2','9/2'],[],[],[]],9,1,[[81,2548],[729,22960],[6561,206668],[59049,1860040]]),  # line 864
    '[18/35, 25/132, 14/3, 11/7, 9/2]': ('ndcv',[0,3],{},[[1,0,-2],[0,1,-2],[1,-3,2],[0,1,-4],[0,1,-6],[0,1,-8],[0,1,-9]],[1,1],None,400,False,125),  # line 865
    '[18/35, 5/33, 7/3, 11/2, 5/7, 45/11]': ('ndz',[3,4],{},[[-1,1,1],[2,-1,-2],[1,0,-3],[0,1,-2]],[3,1],'1',1000,'all',17),  # line 866
    '[18/35, 5/429, 7/3, 11/49, 975/2]': ('nd',[0,1,2,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[1,-1,0,0,0],[-1,2,1,-5,1],[1,-2,-1,5,-1],[0,0,1,0,-4]],[1,1,1,1],None,400,True,27),  # line 867
    '[18/35, 5/66, 28/3, 11/2, 63/11]': ('ndx',[2,4],{},[[1,0,-15],[0,1,-1],[0,1,-6],[0,1,-9],[0,1,-12],[0,1,-15],[0,1,-30]],[1,1],None,400,False,545),  # line 868
    '[18/35, 5/66, 49/3, 22/49, 9/2]': ('ndcv',[0,3],{},[[1,0,-1],[0,1,-6],[-2,1,-4],[3,-1,-1],[0,1,-21],[0,1,-23]],[1,1],None,400,False,98),  # line 869
    '[18/385, 125/14, 121/2, 7/3, 6/11]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-3],[1,0,-4],[0,1,-5],[1,0,-5],[0,1,-8],[1,0,-9],[0,1,-15],[3,-4,-9],[-1,2,-5],[3,-4,-10]],[1,1],None,400,False,143),  # line 870
    '[189/50, 28/33, 77/2, 5/7, 3/5]': ('ndx',[2,4],{},[[1,0,-1],[0,1,-1],[-7,25,0],[1,-1,0],[1,0,-10],[1,0,-14],[1,0,-20],[-1,4,-16],[-1,4,-17]],[1,1],None,300,False,570),  # line 873
    '[189/50, 35/33, 4/3, 11/7, 15/2]': ('nd',[0,1,3,4],{},[[1,0,0,0,-10],[0,1,0,0,-3],[0,0,1,0,-1],[0,0,0,1,-1],[0,-3,1,0,11],[1,2,-1,-1,-19]],[1,1,1,1],None,1000,False,49),  # line 874
    '[189/50, 77/2, 28/33, 5/7, 3/5]': ('ndxz',[2,4],{},[[1,0,-1],[0,1,-1],[-7,25,0],[1,-1,0],[1,0,-20]],[1,1],None,300,True,131),  # line 875
    '[2/105, 243/2, 55/3, 7/605, 3/5]': ('ndx',[1,4],{},[[1,0,-9],[0,1,-1],[1,-1,-36],[1,-1,-50],[0,1,-3],[0,1,-4],[1,-1,-52]],[1,1],None,1000,False,199),  # line 876
    '[2/105, 27/2, 55/3, 49/6655, 3/5]': ('ndx',[2,4],{},[[1,0,-3],[0,1,-3],[-1,1,-3],[3,-2,-1],[0,1,-12],[0,1,-13],[0,2,-35],[0,1,-22],[0,2,-47],[0,2,-49],[0,1,-25],[0,1,-26]],[1,1],None,400,True,169),  # line 877
    '[2/105, 275/9, 81/2, 7/55, 3/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-2],[-1,2,-3],[2,-3,-5],[0,1,-18],[0,1,-22],[0,1,-23]],[1,1],None,400,True,204),  # line 878
    '[2/105, 3/22, 25/2, 77/5, 48/11]': ('add',2,[[],[],['2','10'],[],[]],1,[[4,661],[5,1026],[6,1471],[7,1996]]),  # line 879
    '[2/105, 5/66, 2401/2, 33/7, 4/11]': ('ndx',[1,4],{},[[1,0,-4],[0,1,-4],[-1,1,-4],[3,-2,-19],[3,-2,-46],[3,-2,-56]],[1,6],'6',400,False,4856),  # line 880
    '[2/105, 55/3, 2025/2, 7/55, 3/5]': ('ndx',[2,4],{},[[1,0,-6],[0,1,-4],[-2,3,-3],[1,-1,-5],[0,1,-18],[0,1,-21],[0,1,-22],[0,1,-25],[0,1,-27]],[1,1],None,400,True,111),  # line 881
    '[2/105, 55/3, 243/2, 7/605, 3/5]': ('nd',[2,3],{},[[1,0,-4],[0,1,-5],[-1,1,-3],[4,-3,-9],[1,0,-25],[1,0,-26]],[1,1],None,400,True,661),  # line 882
    '[2/105, 55/3, 405/2, 7/605, 3/5]': ('ndcv',[2,4],{},[[1,0,-5],[0,1,-4],[-1,2,-9],[1,-1,-8],[0,1,-18],[0,1,-40],[0,1,-41]],[1,1],None,400,False,323),  # line 883
    '[2/105, 81/2, 275/9, 7/55, 3/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-2],[-1,2,-3],[2,-3,-5],[0,1,-20],[0,1,-24],[0,1,-25]],[1,1],None,400,True,204),  # line 884
    '[2/105, 81/2, 55/3, 49/605, 3/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-4],[-1,1,-3],[3,-2,-4]],[1,1],None,400,True,29),  # line 885
    '[2/105, 81/2, 55/3, 7/605, 21/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-4],[-1,1,-6],[4,-3,-8],[2,-1,-40],[2,-1,-42]],[1,1],None,400,False,388),  # line 886
    '[2/105, 81/2, 55/3, 7/605, 3/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-4],[-1,1,-3],[4,-3,-5],[0,1,-25],[0,1,-33],[0,1,-39],[0,1,-41]],[1,1],None,400,False,323),  # line 887
    '[2/105, 81/2, 55/3, 7/605, 33/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-4],[-1,1,-6],[3,-2,-5]],[1,1],None,400,True,89),  # line 888
    '[2/15, 1/18, 1617/2, 3/121, 5/7, 3/5]': ('nd',[3,4],{'0': 1},[[1,0,-1],[0,1,-1],[1,-1,-6],[0,1,-8],[0,1,-24],[0,1,-25],[0,1,-26]],[1,1],None,1000,False,423),  # line 945
    '[2/15, 1/294, 1089/2, 7/3, 5/11, 2/7]': ('ndcv',[0,3,4],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-2],[-5,0,3,-6],[7,0,-1,-11],[0,1,0,-8],[0,1,0,-12],[0,1,0,-16],[4,-3,0,-16],[4,-3,0,-28],[4,-3,0,-40],[0,1,0,-17],[0,1,0,-18],[0,1,0,-19]],[1,1,2],'1',1000,False,455),  # line 969
    '[2/15, 1/294, 1089/2, 7/3, 5/11, 3/7]': ('ndcv',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-4],[1,-1,0,-3],[-1,0,1,-15],[1,0,0,-6]],[1,1,1],None,1000,True,224),  # line 970
    '[2/15, 1/294, 99/2, 7/3, 25/11, 2/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[-1,1,2],[0,1,-4],[0,1,-6],[0,1,-9],[1,0,-20]],[1,1],None,400,True,252),  # line 971
    '[2/15, 1/294, 99/2, 7/3, 25/11, 3/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[-1,1,0],[2,-1,0],[0,1,-4],[0,1,-8],[1,0,-20]],[1,1],None,400,True,223),  # line 972
    '[2/15, 1/294, 99/2, 77/3, 5/11, 2/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-3],[-2,1,-1],[0,1,-9],[1,0,-12],[1,0,-20],[-3,2,-26],[-3,2,-31],[-3,2,-33]],[1,4],'2',400,False,617),  # line 973
    '[2/15, 1/294, 99/2, 77/3, 5/11, 3/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-3],[-2,1,3],[0,1,-4],[0,1,-9],[1,0,-10],[1,0,-14],[1,0,-20],[-3,2,-30],[-3,2,-35]],[1,4],'8',400,False,533),  # line 974
    '[2/15, 1/4, 231/2, 3/343, 25/11, 2/5]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-1,0,2],[0,1,-4],[1,2,-12],[1,2,-24],[1,2,-26]],[1,1],None,400,False,181),  # line 982
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 10/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35],[3,-1,-36]],[1,1],None,3000,False,1584),  # line 984
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 15/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2607),  # line 985
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 2/49]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2052),  # line 986
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 2/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2597),  # line 987
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 3/49]': ('ndx',[2,3],{'1': 1},[[1,0,-496],[0,1,-211],[-2,5,0],[7,-16,0]],[1,1],None,300,False,3178),  # line 988
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 4/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-2,1,-6],[1,0,-10],[3,-1,-30],[3,-1,-34],[3,-1,-37]],[1,1],None,3000,False,2221),  # line 989
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 6/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2116),  # line 990
    '[2/15, 1/42, 1089/2, 7/3, 5/11, 9/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,1376),  # line 991
    '[2/15, 1/42, 1089/2, 7/9, 5/11, 2/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-2],[-4,1,-1],[0,1,-9],[1,0,-6],[1,0,-10],[-3,1,-13],[-3,1,-14],[-3,1,-15]],[1,4],'6',400,False,325),  # line 992
    '[2/15, 1/42, 1089/2, 7/9, 5/11, 3/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-2],[0,1,-4],[0,1,-8],[1,0,-6],[1,0,-10],[-3,1,-4],[-3,1,-8],[-3,1,-16]],[1,1],None,400,False,395),  # line 993
    '[2/15, 1/42, 99/2, 7/3, 25/11, 10/7]': ('nd',[3,4],{},[[1,0,-2],[0,1,-2],[-1,1,-10],[1,0,-10],[3,-2,-24],[3,-2,-32],[3,-2,-35],[3,-2,-36]],[1,1],None,1000,False,1363),  # line 995
    '[2/15, 1/42, 99/2, 7/3, 25/11, 15/7]': ('nd',[3,2],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2472),  # line 996
    '[2/15, 1/42, 99/2, 7/3, 25/11, 2/49]': ('ndx',[3,4],{},[[1,0,-8],[0,1,-103],[-9,2,0],[13,-1,0],[1,0,-10],[1,0,-11]],[1,1],None,300,False,2773),  # line 997
    '[2/15, 1/42, 99/2, 7/3, 25/11, 2/7]': ('nd',[3,2],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2462),  # line 998
    '[2/15, 1/42, 99/2, 7/3, 25/11, 22/7]': ('ndxz',[1,4],{},[[1,0,-56],[0,1,-68],[-1,1,0],[4,-3,0]],[1,1],None,300,True,480),  # line 999
    '[2/15, 1/42, 99/2, 7/3, 25/11, 3/49]': ('nd',[3,2],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,1018),  # line 1000
    '[2/15, 1/42, 99/2, 7/3, 25/11, 4/7]': ('nd',[3,4],{},[[1,0,-2],[0,1,-2],[-1,1,-10],[1,0,-10],[3,-2,-24],[3,-2,-32],[3,-2,-35],[3,-2,-37]],[2,2],'d',1000,False,1910),  # line 1001
    '[2/15, 1/42, 99/2, 7/3, 25/11, 6/7]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-4],[-1,1,-11],[3,-2,-3]],[1,1],None,1000,False,1818),  # line 1002
    '[2/15, 1/42, 99/2, 7/3, 25/11, 9/7]': ('nd',[3,4],{},[[1,0,-2],[0,1,-2],[-1,1,-10],[1,0,-10],[3,-2,-24],[3,-2,-32],[3,-2,-35]],[2,2],'d',1000,False,1180),  # line 1003
    '[2/15, 1/42, 99/2, 7/9, 25/11, 2/7]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[-1,1,1],[1,0,-8],[1,0,-14],[1,0,-20],[-3,4,-24],[-3,4,-32],[1,0,-21],[1,0,-23],[-3,4,-36]],[1,1],None,400,False,253),  # line 1004
    '[2/15, 1/42, 99/2, 77/3, 5/11, 15/7]': ('ndz',[3,4],{},[[1,0,-2],[-4,1,3]],[4,4],'200',1000,'all',17),  # line 1005
    '[2/15, 1/42, 99/2, 77/3, 5/11, 2/7]': ('ndz',[3,4],{},[[1,0,-2],[-4,1,3]],[4,4],'200',576,'all',16),  # line 1006
    '[2/15, 1/42, 99/2, 77/3, 5/11, 3/49]': ('ndxz',[3,4],{},[[-4,1,5],[1,0,-2],[0,1,-3]],[4,4],'800',2000,'all',3),  # line 1007
    '[2/15, 1/42, 99/2, 77/3, 5/11, 4/7]': ('ndxz',[3,4],{},[[-4,1,5],[1,0,-1],[0,1,-3]],[4,4],'4840',2000,'all',3),  # line 1008
    '[2/15, 1/6, 11319/2, 3/121, 5/7, 3/5]': ('nd',[1,3,4],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-7],[0,1,-1,-8]],[1,1,1],None,400,'all',20),  # line 1013
    '[2/15, 1/6, 1617/2, 3/121, 65/7, 3/13]': ('nd',[3,4,5],{'0': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-3],[0,1,0,-8],[0,1,0,-16],[4,-1,0,-63]],[1,1,1],None,1000,False,246),  # line 1014
    '[2/15, 1/6, 1617/2, 3/1331, 5/7, 3/5]': ('nd',[1,3,4],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,0,-3],[0,1,-1,-2]],[1,1,1],None,1000,'all',19),  # line 1015
    '[2/15, 11/42, 1089/2, 7/3, 5/11, 2/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,1000,False,587),  # line 1073
    '[2/15, 11/42, 9/2, 77/3, 25/11, 3/7]': ('ndxz',[3,4],{},[[1,0,-2],[-2,1,-1]],[4,2],'21',2000,'all',64),  # line 1074
    '[2/15, 3/14, 25/2, 7/5, 192/7]': ('add',2,[[],[],['2','14'],[]],1,[[4,925],[5,1436],[6,2059],[7,2794]]),  # line 1077
    '[2/15, 99/14, 6875/2, 7/11, 14/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-1],[-1,2,0],[2,-3,-13]],[1,1],None,400,True,43),  # line 1110
    '[2/15, 99/14, 6875/2, 7/11, 22/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-1],[-1,2,0],[2,-3,-10]],[1,1],None,400,True,30),  # line 1111
    '[2/15, 99/14, 6875/2, 7/11, 3/25]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-1],[-1,2,0],[2,-3,-7]],[1,1],None,400,True,27),  # line 1112
    '[2/315, 1/22, 625/2, 33/5, 28/11]': ('add',2,[[],['4','14','5'],[],[],['4','15']],8,[[39,61937],[40,65125],[41,68393],[42,71741]]),  # line 1113
    '[2/315, 125/6, 121/2, 63/11, 2/3]': ('ndx',[1,3],{},[[1,0,-4],[0,1,-2],[-2,3,-3],[1,-1,-5],[1,0,-35],[1,0,-36]],[1,1],None,400,False,207),  # line 1114
    '[2/315, 3/22, 625/2, 77/5, 4/11]': ('add',2,[[],[],[],['4','26','28'],['4','21']],4,[[19,41216],[20,45625],[21,50258],[22,55115]]),  # line 1115
    '[2/45, 1/14, 3267/2, 35/11, 8/7]': ('ndx',[0,2],{'1': 1},[[1,0,-1],[-1,0,3],[0,1,-1],[0,1,-4],[0,1,-7],[0,1,-11],[0,1,-15],[0,1,-16]],[64,4],'2080',3000,False,292),  # line 1116
    '[2/45, 1/154, 49/33, 75/7, 99/2]': ('mul',4,[['5/4','3/4'],[],['-1/4','21/4'],[],[]],81,1,[[6561,89555]]),  # line 1117
    '[2/45, 1/98, 55/2, 567/11, 25/3]': ('ndcv',[1,3],{},[[1,0,-6],[0,1,-1],[1,-3,-9],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,288),  # line 1118
    '[2/45, 1/98, 605/2, 189/11, 25/3]': ('ndcv',[1,3],{},[[1,0,-8],[0,1,-2],[1,-2,-13],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,144),  # line 1119
    '[2/45, 1/98, 6655/2, 63/11, 25/3]': ('ndcv',[1,3],{},[[1,0,-5],[0,1,-1],[1,-2,0],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,436),  # line 1120
    '[2/45, 49/33, 1/154, 75/7, 99/2]': ('mul',4,[['5/4','3/4'],[],['-1/4','21/4'],[],[]],81,1,[[6561,89555]]),  # line 1121
    '[22/105, 27/10, 245/2, 5/11, 9/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-2],[-2,3,-5],[1,-1,-2],[0,1,-15],[0,1,-16],[0,1,-17]],[1,1],None,400,True,198),  # line 1136
    '[22/105, 27/10, 539/2, 5/11, 9/7]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-1],[2,-1,-6],[0,1,-4],[1,0,-15],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,True,136),  # line 1137
    '[22/105, 297/10, 245/2, 5/11, 2/7]': ('ndcv',[2,3],{},[[1,0,-1],[0,1,-2],[0,1,-5],[1,0,-5],[0,1,-8],[1,0,-9],[0,1,-15],[3,-4,-9],[-1,2,-12],[3,-4,-10]],[1,1],None,400,False,6789),  # line 1138
    '[22/105, 297/10, 539/2, 5/11, 2/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[1,0,-5],[0,1,-5],[1,0,-8],[0,1,-9],[1,0,-15],[-4,3,-9],[2,-1,-5],[-4,3,-10]],[1,1],None,400,False,171),  # line 1139
    '[225/14, 49/27, 1/105, 2/5, 35/2]': ('nd',[2,3],{},[[1,0,-1],[0,1,-1],[1,-6,13],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,345),  # line 1142
    '[225/28, 7/33, 8/3, 11/5, 15/2]': ('ndx',[0,2],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,22),  # line 1143
    '[225/28, 7/33, 8/3, 11/5, 21/2]': ('ndx',[0,2],{},[[1,0,-7],[0,1,-2],[-1,2,-1],[1,-1,-13]],[1,1],None,400,True,47),  # line 1144
    '[25/126, 27/35, 22/3, 7/11, 9/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-2],[-1,3,-19],[2,-3,-16],[0,1,-25],[0,1,-26]],[1,1],None,400,False,225),  # line 1146
    '[25/126, 33/2, 4/55, 21/11, 22/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-3,1],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,153),  # line 1147
    '[25/126, 4/15, 99/2, 7/121, 5/3]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[3,-4,-4],[0,1,-8],[1,0,-15],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,True,147),  # line 1148
    '[25/126, 4/165, 539/2, 3/7, 5/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[-1,2,-3],[1,-1,-4],[1,0,-18],[1,0,-40],[1,0,-41],[1,0,-42],[1,0,-43],[1,0,-44],[1,0,-45],[1,0,-46]],[1,1],None,400,False,397),  # line 1149
    '[25/126, 4/55, 33/2, 21/11, 22/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-3,1],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,153),  # line 1150
    '[25/126, 4/55, 99/2, 7/11, 22/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-3,-11],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,153),  # line 1151
    '[25/126, 44/15, 27/2, 7/11, 5/3]': ('ndx',[1,2,3,4],{},[[1,0,0,0,-10],[0,1,0,0,-4],[0,0,1,0,-1],[0,0,0,1,-1],[1,0,-3,0,-16],[0,-1,0,3,1],[0,1,0,-3,-1]],[1,1,1,1],None,200,True,58),  # line 1152
    '[25/126, 99/2, 4/15, 7/121, 5/3]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[3,-4,-4],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,147),  # line 1153
    '[25/126, 99/2, 4/55, 7/11, 22/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-3,-11],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,153),  # line 1154
    '[25/18, 22/35, 1029/2, 3/11, 15/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-3],[-2,3,-7],[1,-1,-2],[-1,2,-10],[1,-1,-16],[1,-1,-17]],[1,1],None,400,False,24413),  # line 1155
    '[25/18, 22/35, 1029/2, 3/11, 25/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-3],[-2,3,-16],[1,-1,0]],[1,1],None,400,True,57),  # line 1156
    '[25/18, 22/35, 1029/2, 3/11, 5/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-3],[-2,3,-7],[1,-1,0],[1,0,-8],[1,0,-9]],[1,1],None,400,True,61),  # line 1157
    '[25/18, 22/35, 1029/2, 3/11, 55/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-3],[-2,3,-4],[1,-1,-2]],[1,1],None,400,True,29),  # line 1158
    '[25/18, 22/35, 11319/2, 3/11, 2/3]': ('ndx',[1,3],{},[[1,0,-2],[0,1,-3],[-1,2,-14],[5,-3,0],[1,0,-10],[1,-1,-20],[1,-1,-21]],[1,1],None,400,False,423),  # line 1159
    '[25/18, 22/35, 11319/2, 3/11, 2/7]': ('ndx',[1,3],{},[[1,0,-2],[0,1,-3],[-1,2,-6],[1,-1,0],[1,0,-8],[-1,2,-8],[1,-1,-18]],[4,1],'4',200,False,172),  # line 1160
    '[25/18, 22/35, 539/2, 3/11, 20/3]': ('nd',[1,2],{},[[1,0,-2],[0,1,-42],[1,0,-10],[1,0,-14],[1,0,-22],[1,0,-23],[1,0,-24]],[5,5],'421000',400,False,648),  # line 1161
    '[25/18, 297/35, 2/5, 7/11, 175/2]': ('add',2,[['7','11','4'],[],[],[],['3','4']],6,[[29,39508],[30,42189],[31,44958],[32,47815]]),  # line 1162
    '[25/18, 297/35, 2/5, 7/11, 275/2]': ('add',2,[['2','5','4'],[],[],[],['1','4']],6,[[29,37674],[30,40293],[31,43000],[32,45795]]),  # line 1163
    '[25/18, 297/35, 4/5, 7/11, 55/2]': ('add',2,[['2','9','20'],[],[],[],['1','4']],6,[[29,37557],[30,40172],[31,42875],[32,45666]]),  # line 1164
    '[25/18, 4/35, 539/2, 3/49, 14/11]': ('ndx',[1,2,4],{},[[1,0,0,-1],[0,1,0,-5],[0,0,1,-15],[-1,0,1,-37],[1,0,0,-10],[1,0,0,-16],[1,0,0,-24],[1,0,0,-25],[1,0,0,-26],[1,0,0,-27],[1,0,0,-28],[1,0,0,-29]],[1,1,1],None,400,False,663),  # line 1165
    '[25/18, 539/2, 22/35, 3/11, 20/3]': ('ndx',[1,2],{},[[1,0,-2],[0,1,-42],[1,0,-10],[1,0,-14],[1,0,-22],[1,0,-23],[1,0,-24]],[5,5],'421000',400,False,648),  # line 1166
    '[25/18, 539/2, 4/35, 3/49, 14/11]': ('ndx',[1,2,4],{},[[1,0,0,-1],[0,1,0,-5],[0,0,1,-15],[-1,0,1,-37],[1,0,0,-10],[1,0,0,-16],[1,0,0,-24],[1,0,0,-25],[1,0,0,-26],[1,0,0,-27],[1,0,0,-28],[1,0,0,-29]],[1,1,1],None,400,False,663),  # line 1167
    '[25/252, 22/7, 49/55, 3/11, 49/2]': ('add',3,[['2','7/2','9/2'],['2','4'],[],[],[]],10,[[49,69389],[50,72230],[51,75128],[52,78083]]),  # line 1168
    '[25/252, 22/7, 49/55, 3/11, 55/2]': ('add',3,[['2','7/2','9/2'],['2','4'],[],[],[]],10,[[49,73114],[50,76106],[51,79158],[52,82270]]),  # line 1169
    '[25/252, 49/55, 22/7, 3/11, 49/2]': ('add',3,[['2','7/2','9/2'],['2','4'],[],[],[]],10,[[49,69389],[50,72230],[51,75128],[52,78083]]),  # line 1170
    '[25/252, 49/55, 22/7, 3/11, 55/2]': ('add',3,[['2','7/2','9/2'],['2','4'],[],[],[]],10,[[49,73114],[50,76106],[51,79158],[52,82270]]),  # line 1171
    '[25/54, 66/35, 343/2, 3/11, 5/7]': ('ndx',[1,3],{},[[1,0,-2],[0,1,-4],[-2,3,-11],[1,-1,0],[-1,2,-30]],[1,1],None,400,False,243),  # line 1172
    '[25/63, 1/30, 99/5, 2/3, 7/11, 5/2]': ('ndx',[0,4],{},[[1,0,-15],[0,1,-135],[-4,1,0],[22,-1,0]],[1,1],None,300,False,1132),  # line 1177
    '[25/63, 1/55, 154/5, 891/2, 7/3]': ('ndcv',[1,4],{},[[1,0,-4],[0,1,-1],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-24],[2,-3,-40],[0,1,-9],[2,-3,-41]],[1,1],None,400,False,249),  # line 1178
    '[25/63, 14/55, 242/7, 3/2, 245/3]': ('mul',2,[[],['-2','60'],[],[],['0','30']],3,1,[[9,3112],[27,9376],[81,28168],[243,84544]]),  # line 1181
    '[25/63, 14/55, 7986/7, 3/2, 7/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-3],[-1,2,-14],[5,-3,0],[1,0,-10],[1,-1,-20],[1,-1,-21]],[1,1],None,400,False,425),  # line 1182
    '[25/63, 143/7, 2/55, 49/2, 3/13, 7/11]': ('nd',[1,4],{'2': 2},[[1,0,-2],[0,1,-2],[-2,3,-6],[1,-1,-3],[0,1,-20],[0,1,-21]],[1,1],None,400,True,377),  # line 1183
    '[25/63, 2/55, 143/7, 49/2, 3/13, 7/11]': ('nd',[1,4],{'2': 2},[[1,0,-2],[0,1,-2],[-2,3,-6],[1,-1,-3],[0,1,-20],[0,1,-21]],[1,1],None,400,True,377),  # line 1184
    '[25/63, 242/7, 14/55, 3/2, 245/3]': ('mul',2,[[],['-2','60'],[],[],['0','30']],3,1,[[9,3112],[27,9376],[81,28168],[243,84544]]),  # line 1185
    '[25/63, 242/7, 49/55, 3/121, 77/2]': ('ndx',[0,1,2],{},[[1,0,0,-18],[0,1,0,-3],[0,0,1,-5],[1,-1,0,-57],[0,1,0,-24],[0,1,0,-25],[0,1,0,-26],[0,1,0,-27],[0,1,0,-28],[0,1,0,-29]],[1,1,1],None,400,False,621),  # line 1186
    '[25/63, 27/55, 14/5, 11/7, 245/2]': ('ndx',[0,1,2],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,30),  # line 1187
    '[25/63, 3/55, 686/5, 11/49, 25/2]': ('nd',[0,1,2],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-24],[0,1,0,-25],[0,1,0,-26],[0,1,0,-27],[0,1,0,-28],[0,1,0,-29]],[1,1,1],None,400,False,382),  # line 1188
    '[25/63, 3/55, 686/5, 11/7, 175/2]': ('ndx',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[3,0,-1,-1],[0,0,1,-4],[0,0,1,-8],[0,0,1,-16],[0,0,1,-20]],[1,1,1],None,400,True,148),  # line 1189
    '[25/63, 3/605, 686/5, 11/7, 25/2]': ('nd',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-2],[3,0,-1,-2]],[1,1,1],None,1000,'all',29),  # line 1190
    '[25/63, 351/55, 14/5, 11/13, 65/2]': ('add',2,[['1','4','16'],[],[],['1','5','4'],[],['1','4']],6,[[29,37557],[30,40172],[31,42875],[32,45666]]),  # line 1191
    '[25/63, 49/55, 242/7, 3/121, 77/2]': ('ndx',[0,1,2],{},[[1,0,0,-18],[0,1,0,-3],[0,0,1,-5],[1,-1,0,-57],[0,1,0,-24],[0,1,0,-25],[0,1,0,-26],[0,1,0,-27],[0,1,0,-28],[0,1,0,-29]],[1,1,1],None,400,False,621),  # line 1192
    '[25/63, 91/55, 702/5, 11/13, 5/2]': ('nd',[0,1,5],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-8],[3,-1,0,-2],[-2,-1,3,2],[2,1,-3,-2]],[1,1,1],None,400,True,22),  # line 1193
    '[25/693, 49/10, 6/7, 33/2, 14/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[1,-3,2],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,152),  # line 1194
    '[25/693, 6/7, 49/10, 33/2, 14/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[1,-3,2],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,152),  # line 1195
    '[27/10, 1/1617, 14/3, 77/2, 75/7]': ('mul',2,[[],[],[],['-2','3'],['-1/4','5/4']],9,1,[[81,551],[729,5006],[6561,45101],[59049,405956]]),  # line 1200
    '[27/10, 4/63, 77/2, 5/7, 98/11]': ('ndx',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,79),  # line 1205
    '[27/10, 5/1617, 14/3, 77/2, 6/7]': ('ndcv',[0,3],{},[[1,0,-5],[0,1,-3],[-3,2,-1],[2,-1,-8],[1,0,-20]],[1,1],None,1000,False,241),  # line 1206
    '[27/10, 5/21, 4/33, 847/2, 6/7]': ('nd',[0,4],{},[[1,0,-3],[0,1,-1],[1,-1,-23],[1,0,-25],[1,0,-26]],[5,1],'1e',3000,False,57),  # line 1207
    '[27/35, 1/429, 50/3, 11/25, 273/2]': ('nd',[0,2,5],{},[[1,0,0,-4],[0,1,0,-7],[0,0,1,-1],[2,-1,0,-16]],[1,1,1],None,3000,'all',124),  # line 1223
    '[27/35, 25/66, 14/3, 11/7, 245/2]': ('ndcv',[0,1],{},[[1,0,-5],[0,1,-16],[-3,2,-27],[2,-1,-2]],[1,1],None,400,False,145),  # line 1231
    '[27/35, 25/66, 14/3, 11/7, 63/2]': ('ndcv',[0,1],{},[[1,0,-3],[0,1,-12],[-3,2,-27],[7,-3,-12]],[1,1],None,400,False,105),  # line 1232
    '[27/35, 25/99, 22/5, 7/11, 605/2]': ('ndx',[0,1,2],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,30),  # line 1233
    '[27/35, 5/132, 14/3, 22/7, 21/2]': ('ndcv',[0,3],{},[[1,0,-1],[0,1,-2],[2,-3,4],[0,1,-4],[0,1,-5],[0,1,-8],[0,1,-17],[0,1,-19],[0,1,-20]],[2,2],'e',1000,False,216),  # line 1234
    '[27/35, 5/132, 28/3, 11/7, 21/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-2],[1,-3,4],[0,1,-5],[0,1,-8],[0,1,-20]],[1,1],None,400,False,232),  # line 1235
    '[27/35, 5/132, 28/3, 11/7, 35/2]': ('ndcv',[0,3],{},[[1,0,-6],[0,1,-3],[1,-3,1],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,70),  # line 1236
    '[27/35, 5/66, 14/3, 11/7, 105/2]': ('ndcv',[0,1],{},[[1,0,-3],[0,1,-8],[-4,3,-44],[2,-1,0]],[1,1],None,400,False,182),  # line 1238
    '[27/35, 5/66, 14/3, 11/7, 1225/2]': ('ndcv',[0,3],{},[[1,0,-6],[0,1,-6],[2,-3,2],[0,1,-12],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,135),  # line 1239
    '[27/35, 5/66, 14/3, 11/7, 189/2]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-8],[-1,1,-13],[2,-1,-2],[0,1,-30]],[1,1],None,400,False,280),  # line 1240
    '[27/35, 5/66, 14/3, 11/7, 245/2]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-8],[-1,1,-13],[2,-1,-2],[0,1,-30]],[1,1],None,400,False,292),  # line 1241
    '[27/35, 5/66, 14/3, 11/7, 441/2]': ('ndcv',[0,3],{},[[1,0,-2],[0,1,-4],[-1,3,-30],[2,-3,0],[0,1,-40],[0,1,-41],[0,1,-42],[0,1,-43],[0,1,-44],[0,1,-45],[0,1,-46],[0,1,-47]],[1,1],None,400,False,419),  # line 1242
    '[27/35, 5/66, 14/3, 11/7, 525/2]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-6],[-3,2,-15],[3,-1,-3],[0,1,-19]],[1,1],None,400,False,152),  # line 1243
    '[27/35, 5/66, 14/3, 11/7, 81/2]': ('ndcv',[0,1],{},[[1,0,-3],[0,1,-8],[-4,3,-44],[2,-1,0]],[1,1],None,400,False,171),  # line 1244
    '[27/35, 55/18, 24/5, 7/11, 5/2]': ('ndx',[0,3],{'1': 1,'2': 1},[[1,0,-29],[0,1,-15],[-1,2,-1],[1,-1,-14]],[1,1],None,3000,True,89),  # line 1245
    '[27/385, 25/21, 22/3, 7/11, 363/2]': ('nd',[0,2,4],{},[[1,0,0,-8],[0,1,0,-1],[0,0,1,-3],[1,0,-1,-11],[0,1,0,-4]],[1,1,1],None,400,True,82),  # line 1248
    '[27/5, 1/147, 5/33, 2/3, 77/2, 25/7]': ('mul',2,[[],['-49/15','169/15'],[],[],[]],16,1,[[256,13375],[4096,216327]]),  # line 1249
    '[27/50, 55/21, 44/3, 7/11, 15/2]': ('ndxz',[0,2,3],{'1': 1},[[1,0,0,-247],[0,1,0,-1],[0,0,1,-238],[1,-61,0,0],[0,-59,1,0],[-7,0,8,0],[1,0,-1,0]],[1,12,1],'6',300,True,1564),  # line 1250
    '[27/50, 55/21, 44/3, 7/11, 9/2]': ('nd',[0,1,3,4],{},[[1,0,0,0,-5],[0,1,0,0,-3],[0,0,1,0,-1],[0,0,0,1,-1],[1,1,-1,-1,-5]],[1,1,1,1],None,1000,True,72),  # line 1251
    '[27/70, 4/165, 539/2, 5/7, 3/5]': ('ndcvz',[3,4],{},[[1,0,-2],[0,1,-1],[-1,3,-4],[1,-2,-1],[0,1,-9],[0,1,-14],[0,1,-25]],[1,1],None,3000,True,246),  # line 1252
    '[275/63, 1/20, 33/5, 14/11, 75/2]': ('ndxz',[2,4],{},[[-1,0,1],[1,0,-1],[1,0,-1],[0,1,-1047],[-523,1,0]],[13,13],'1fffffffffffffffffffffffffffffffffffdffffff',300,True,2498),  # line 1253
    '[275/63, 49/22, 12/7, 9/5, 7/2]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-1],[-2,3,0],[3,-1,-7],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,True,38),  # line 1254
    '[275/63, 7/10, 297/5, 2/11, 25/2]': ('ndx',[1,4],{},[[1,0,-6],[0,1,-2],[-1,3,-2],[1,-1,-14]],[1,1],None,400,True,27),  # line 1255
    '[275/63, 7/10, 297/5, 2/11, 35/2]': ('ndx',[1,4],{},[[1,0,-7],[0,1,-4],[-2,3,0],[1,-1,-11]],[1,1],None,400,True,65),  # line 1256
    '[275/63, 77/10, 24/7, 3/11, 7/2]': ('ndx',[0,1],{},[[1,0,-3],[0,1,-1],[-1,2,-2],[2,-1,-11],[0,1,-8],[0,1,-10]],[1,1],None,400,True,43),  # line 1257
    '[28/15, 1/363, 9/8, 55/7, 21/2]': ('add',3,[['1'],[],['4','3'],[],['4','4','1']],4,[[19,3908],[20,4292],[21,4694],[22,5114]]),  # line 1276
    '[28/15, 21/22, 5525/2, 11/7, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-1],[0,0,1,0,-2],[0,0,0,1,-2],[-1,3,0,0,-6],[1,-1,0,0,-8],[0,0,-1,1,0],[0,0,1,-1,0],[0,1,-1,0,1],[0,-1,1,0,-1]],[1,1,1,1],None,400,False,29),  # line 1285
    '[28/15, 27/49, 1/18, 55/2, 9/11]': ('nd',[0,2,3,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-3],[1,0,-2,0,2],[0,1,0,0,-4],[0,1,0,0,-7],[0,1,0,0,-12],[0,1,3,0,-24],[0,1,3,0,-27],[0,1,0,0,-13],[0,1,3,0,-31],[0,1,0,0,-14]],[1,1,1,1],None,400,False,179),  # line 1286
    '[28/15, 3/154, 1715/2, 11/49, 2/11]': ('ndx',[0,3],{},[[1,0,-10],[0,1,-7],[-7,2,-8],[4,-1,-1],[1,0,-12],[1,0,-15],[-5,3,-100]],[1,1],None,400,False,468),  # line 1287
    '[28/15, 3/154, 245/2, 11/7, 20/11]': ('ndx',[1,4],{},[[1,0,-16],[0,1,-1],[0,1,-6],[0,1,-9],[0,1,-12],[0,1,-15],[0,1,-30]],[1,1],None,400,False,745),  # line 1288
    '[28/15, 3/154, 245/2, 11/7, 70/11]': ('ndx',[1,4],{},[[1,0,-9],[0,1,-1],[0,1,-5],[0,1,-7],[0,1,-9],[0,1,-11],[0,1,-20]],[1,1],None,400,False,564),  # line 1289
    '[28/15, 3/154, 4375/2, 11/5, 2/11]': ('nd',[1,4],{},[[1,0,-1],[0,1,-2],[-1,3,-7],[1,-1,-1],[0,1,-5],[1,1,-24],[0,1,-10],[1,1,-28],[0,1,-25]],[1,1],None,400,False,535),  # line 1290
    '[28/15, 3/154, 875/2, 11/5, 4/11]': ('nd',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,0,-58],[0,0,1,-4],[0,0,1,-8],[0,0,1,-16],[0,0,1,-17],[0,0,1,-18],[0,0,1,-19]],[1,1,1],None,400,False,1222),  # line 1291
    '[28/15, 3/1694, 25/2, 11/5, 12/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-8],[-3,1,-8],[5,-1,-6],[1,0,-8],[1,0,-9]],[1,1],None,400,True,254),  # line 1292
    '[28/15, 3/22, 5525/2, 121/7, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-1],[0,0,1,0,-2],[0,0,0,1,-2],[-1,3,0,0,-2],[1,-2,0,0,-5],[0,0,-1,1,0],[0,0,1,-1,0],[-1,4,-1,0,3],[1,-4,1,0,-3]],[1,1,1,1],None,400,False,41),  # line 1293
    '[28/15, 35/6, 3/5, 11/2, 3/7, 15/11]': ('val',1,4,{'2': 1},4,20,[2,2,1,1],128,None),  # line 1294
    '[28/15, 35/6, 3/5, 77/2, 3/7, 5/11]': ('val',1,4,{'2': 1},2,20,[3,3,1,1],220,None),  # line 1295
    '[28/15, 5/3, 21/10, 11/2, 5/7, 15/11]': ('val',2,4,{'1': 1},4,20,[2,2,1,1],128,None),  # line 1296
    '[28/15, 5/3, 21/10, 77/2, 5/7, 3/11]': ('val',2,4,{'1': 1},2,20,[3,3,1,1],220,None),  # line 1297
    '[28/15, 63/22, 1105/2, 11/7, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-1],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,0],[2,-1,0,0,-4],[0,0,-1,1,0],[0,0,1,-1,0],[-1,2,-1,0,2],[1,-2,1,0,-2],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,48),  # line 1298
    '[28/15, 81/343, 1/6, 55/2, 3/11]': ('ndx',[2,3,4],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-2],[1,-2,0,-1],[1,0,0,-8],[1,0,0,-16],[1,0,0,-20]],[1,1,1],None,400,True,192),  # line 1303
    '[28/15, 9/154, 35/2, 11/5, 50/11]': ('nd',[2,3],{},[[1,0,-733],[0,1,-7479],[-1,1,-16297]],[8,1],'a8',1000,False,32658),  # line 1304
    '[28/15, 9/22, 1105/2, 11/7, 21/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,-2],[4,-3,0,0,-6],[0,0,-1,1,0],[0,0,1,-1,0],[-5,2,1,0,4],[5,-2,-1,0,-4]],[1,1,1,1],None,400,False,69),  # line 1305
    '[28/15, 9/22, 1105/2, 11/7, 33/221]': ('nd',[0,3,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-3],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,-2],[4,-3,0,0,-13],[0,0,-1,1,0],[0,0,1,-1,0],[-4,2,1,0,4],[4,-2,-1,0,-4]],[1,1,1,1],None,400,False,96),  # line 1306
    '[28/15, 9/22, 1105/2, 11/91, 33/17]': ('nd',[2,3,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-3],[0,0,1,0,-6],[0,0,0,1,-5],[-1,1,0,0,-2],[4,-3,0,0,-13],[-1,-1,1,0,0],[1,1,-1,0,0],[-5,2,0,1,4],[5,-2,0,-1,-4]],[1,1,1,1],None,1000,False,115),  # line 1307
    '[28/45, 35/22, 27/2, 11/7, 22/3]': ('ndx',[1,3],{},[[1,0,-6],[0,1,-2],[-2,3,-2],[1,-1,-6]],[1,1],None,400,True,48),  # line 1309
    '[28/45, 35/22, 27/2, 11/7, 35/3]': ('ndx',[1,3],{},[[1,0,-6],[0,1,-2],[-2,3,-2],[1,-1,-6]],[1,1],None,400,True,45),  # line 1310
    '[28/45, 35/22, 27/2, 11/7, 55/3]': ('ndx',[1,3],{},[[1,0,-7],[0,1,-3],[-2,3,-9],[1,-1,-6],[-1,2,-24],[-1,2,-26]],[1,1],None,400,False,161),  # line 1311
    '[28/45, 5/22, 189/2, 11/7, 10/11]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-1,2,0],[1,-1,-10]],[1,1],None,400,True,25),  # line 1312
    '[28/45, 5/22, 189/2, 11/7, 10/3]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-2,3,-4],[1,-1,-6]],[1,1],None,400,True,39),  # line 1313
    '[28/45, 5/22, 189/2, 11/7, 15/11]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-1,3,-6],[1,-1,-8]],[1,1],None,400,True,19),  # line 1314
    '[28/45, 5/22, 189/2, 11/7, 2/3]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,21),  # line 1315
    '[28/45, 5/22, 189/2, 11/7, 25/11]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-2,3,0],[1,-1,-8]],[1,1],None,400,True,37),  # line 1316
    '[28/45, 5/22, 189/2, 11/7, 25/3]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-2,3,-14],[1,-1,-4],[-1,2,-24],[-1,2,-26]],[1,1],None,400,False,146),  # line 1317
    '[28/45, 5/22, 189/2, 11/7, 4/11]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[1,-1,-12],[0,1,-4],[0,1,-5]],[1,1],None,400,True,29),  # line 1318
    '[28/45, 5/22, 189/2, 11/7, 4/3]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-1,2,-2],[1,-1,-8]],[1,1],None,400,True,27),  # line 1319
    '[28/45, 5/22, 189/2, 11/7, 5/11]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-1,2,-1],[1,-1,-6]],[1,1],None,400,True,19),  # line 1320
    '[28/45, 5/22, 189/2, 11/7, 5/33]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,19),  # line 1321
    '[28/45, 5/22, 189/2, 143/7, 5/13]': ('ndx',[1,4,5],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[-2,3,0,-5],[1,-1,0,-4],[-4,6,-1,7],[4,-6,1,-7]],[1,1,1],None,400,True,46),  # line 1322
    '[28/45, 5/22, 2457/2, 11/7, 5/13]': ('ndx',[1,3,5],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[-2,3,0,-5],[1,-1,0,-4],[-2,3,-1,4],[2,-3,1,-4]],[1,1,1],None,400,True,33),  # line 1323
    '[297/70, 1/165, 2/3, 55/2, 63/11]': ('ndx',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,1,3],[0,1,0,-4],[0,0,1,-4]],[1,1,1],None,1000,True,99),  # line 1324
    '[3/8, 112/15, 1/33, 55/7, 21/2]': ('add',3,[['2'],[],[],['3','3'],['1','3','3']],1,[[6,801],[7,1047],[8,1326],[9,1638]]),  # line 1329
    '[308/15, 1/147, 9/8, 5/11, 33/2]': ('add',3,[['2'],[],['5','3'],['1','1','1'],[]],4,[[19,3912],[20,4296],[21,4698],[22,5118]]),  # line 1333
    '[35/18, 1375/2, 8/77, 3/5, 7/3]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,5,0],[1,-3,0],[1,0,-10],[1,0,-16],[1,0,-30]],[1,1],None,300,False,120),  # line 1334
    '[35/18, 27/55, 24/5, 11/7, 5/2]': ('ndx',[2,1,3,4],{},[[1,0,0,0,-22],[0,1,0,0,-1],[0,0,1,0,-83],[0,0,0,1,-1],[1,0,0,-1,-21],[-3,-1,1,0,4],[3,1,-1,0,-4],[0,1,0,0,-20],[0,1,0,0,-21]],[1,1,1,1],None,3000,False,520),  # line 1335
    '[35/18, 28/55, 2541/2, 3/7, 5/11]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-2],[-1,3,-7],[2,-3,-4],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,True,94),  # line 1336
    '[35/18, 28/55, 363/2, 9/7, 2/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-2],[-1,3,-7],[3,-2,0],[1,0,-10],[1,0,-16],[-1,4,-20],[1,-2,-24],[1,-2,-25]],[1,1],None,400,False,571),  # line 1337
    '[35/18, 605/2, 4/77, 27/5, 7/3]': ('nd',[1,4],{},[[1,0,-3],[0,1,-2],[-1,4,-26]],[1,1],None,1000,False,140),  # line 1338
    '[35/18, 8/55, 3773/2, 3/7, 5/3]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,5,0],[1,-3,0],[1,0,-10],[1,0,-16],[1,0,-30],[-1,6,-24],[-1,6,-27]],[1,1],None,300,False,453),  # line 1339
    '[35/3, 1/70, 9/55, 16/7, 363/2]': ('mul',1,[['-1','6'],[],[],[],[]],3,5,[[81,1573],[243,4732],[729,14209],[2187,42640]]),  # line 1340
    '[35/54, 12/55, 33/2, 3/7, 10/11]': ('add',1,[[],['1','4'],[],[],['1','1']],15,[[104,87049],[105,88726],[106,90419],[107,92128]]),  # line 1348
    '[35/54, 12/55, 77/2, 3/7, 10/11]': ('add',1,[[],['1','4'],[],[],['1','1']],15,[[104,54394],[105,55442],[106,56500],[107,57568]]),  # line 1349
    '[35/6, 1/110, 28/5, 11/2, 3/7, 10/11]': ('nd',[4,3],{},[[1,0,-2],[0,1,-1],[-2,1,0],[0,1,-8],[0,1,-24],[3,-1,-36],[-24,13,-74]],[1,1],None,1000,False,1268),  # line 1378
    '[35/6, 1/110, 28/5, 11/2, 3/7, 14/11]': ('ndx',[3,4],{},[[1,0,-149],[0,1,-70],[-2,5,0],[1,-2,0]],[1,1],None,300,False,605),  # line 1379
    '[35/6, 1/110, 28/5, 11/2, 3/7, 25/11]': ('nd',[4,1],{'2': 2},[[1,0,-3],[0,1,-2],[-2,1,-10],[3,-1,-30],[3,-1,-34]],[1,1],None,400,False,1966),  # line 1380
    '[35/6, 1/110, 28/5, 11/2, 3/7, 35/11]': ('ndx',[3,4],{},[[1,0,-480],[0,1,-196],[-2,5,0],[9,-20,0]],[1,1],None,300,False,1977),  # line 1381
    '[35/6, 1/110, 28/5, 11/2, 3/7, 6/11]': ('nd',[4,3],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,1000,False,596),  # line 1382
    '[35/6, 1/110, 28/5, 11/2, 9/7, 5/11]': ('ndcv',[0,3],{},[[1,0,-1],[0,1,-1],[1,0,-4],[0,1,-4],[1,0,-7],[0,1,-7],[1,0,-10],[-3,2,-4],[-3,2,-5]],[1,1],None,400,False,443),  # line 1383
    '[35/6, 1/110, 28/5, 77/2, 3/7, 2/11]': ('mul',2,[[],[],[],['-1','2'],['3/4','1/4']],5,6,[[125,722],[625,3657],[3125,18342],[15625,91777]]),  # line 1384
    '[35/6, 1/110, 28/5, 77/2, 3/7, 5/11]': ('mul',2,[[],[],[],['-2','3'],['3/4','1/4']],5,6,[[125,1113],[625,5669],[3125,28475],[15625,142531]]),  # line 1385
    '[35/6, 1/110, 4/5, 77/2, 3/7, 35/11]': ('mul',4,[[],[],[],['-8','9'],['0','1']],3,1,[[27,2497],[81,8225],[243,25617],[729,78001]]),  # line 1386
    '[35/6, 1/110, 4/5, 77/2, 3/7, 6/11]': ('mul',4,[[],[],[],['-8','9'],['0','1']],3,1,[[27,2509],[81,8241],[243,25637],[729,78025]]),  # line 1387
    '[35/6, 1/1210, 28/5, 11/2, 3/7, 5/11]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-2],[1,-2,-2],[1,0,-8],[0,1,-10],[0,1,-14],[0,1,-20],[2,-3,-29],[2,-3,-31],[2,-3,-33]],[1,1],None,400,False,340),  # line 1388
    '[35/6, 1/1210, 4/5, 77/2, 3/7, 5/11]': ('ndcv',[1,4],{'2': 1},[[1,0,-4],[0,1,-2],[1,-2,-4],[0,1,-8],[0,1,-12],[0,1,-16],[2,-3,-32],[0,1,-17],[0,1,-18],[2,-3,-34],[0,1,-19],[2,-3,-36]],[1,1],None,100,False,578),  # line 1389
    '[35/6, 12155/2, 8/1001, 3/5, 2/17]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[1,-1,0,0,-1],[0,-1,1,0,0],[0,1,-1,0,0],[2,-2,0,-1,1],[-2,2,0,1,-1],[1,0,0,0,-5],[1,0,0,0,-8],[1,0,0,0,-15]],[1,1,1,1],None,400,False,97),  # line 1449
    '[35/6, 12155/2, 8/1001, 3/5, 7/17]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,-1,1,0,0],[0,1,-1,0,0],[2,-2,0,-1,1],[-2,2,0,1,-1],[1,0,0,0,-7],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,46),  # line 1450
    '[35/6, 12155/2, 8/77, 3/5, 2/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[1,-1,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-5],[1,0,0,0,-8],[1,0,0,0,-15]],[1,1,1,1],None,400,False,97),  # line 1451
    '[35/6, 12155/2, 8/77, 3/5, 7/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,0,-1,1,0],[0,0,1,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-7],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,46),  # line 1452
    '[35/6, 133705/2, 4/77, 3/5, 2/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[3,-2,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,1],[-2,1,1,0,-1],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,51),  # line 1453
    '[35/6, 133705/2, 4/77, 3/5, 7/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[4,-3,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,1],[-2,1,1,0,-1]],[1,1,1,1],None,400,False,29),  # line 1454
    '[35/6, 1375/2, 8/77, 3/25, 2/3]': ('ndx',[2,4],{},[[1,0,-102],[0,1,-24],[-1,5,0],[1,-4,0]],[1,1],None,300,False,108),  # line 1455
    '[35/6, 1375/2, 8/77, 3/25, 7/3]': ('nd',[2,4],{},[[1,0,-3],[0,1,-1],[-1,5,-8]],[1,1],None,1000,False,33),  # line 1456
    '[35/6, 1375/3, 27/77, 2/25, 3/2]': ('ndx',[2,4],{},[[1,0,-102],[0,1,-24],[-1,5,0],[1,-4,0]],[1,1],None,300,False,109),  # line 1457
    '[35/6, 2431/2, 56/55, 3/7, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-3],[0,0,1,0,-3],[0,0,0,1,-3],[-1,1,0,0,-4],[5,-3,0,0,-2],[0,0,-1,1,0],[0,0,1,-1,0],[2,0,-1,0,1],[-2,0,1,0,-1],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,76),  # line 1458
    '[35/6, 2431/2, 56/715, 3/7, 5/17]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-3],[0,0,1,0,-3],[0,0,0,1,-3],[-1,1,0,0,-4],[5,-3,0,0,-2],[0,-1,1,0,0],[0,1,-1,0,0],[2,0,0,-1,1],[-2,0,0,1,-1],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,76),  # line 1459
    '[35/6, 26741/2, 28/55, 3/7, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-5],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,-8],[7,-3,0,0,-4],[0,0,-1,1,0],[0,0,1,-1,0],[1,0,-1,0,1],[-1,0,1,0,-1],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,61),  # line 1460
    '[35/6, 275/2, 40/231, 3/5, 7/3]': ('nd',[2,4],{},[[1,0,-1],[0,1,-1],[-1,4,-2]],[1,1],None,3000,False,39),  # line 1461
    '[35/6, 28/55, 26741/2, 3/7, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-5],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,-8],[7,-3,0,0,-4],[0,0,-1,1,0],[0,0,1,-1,0],[1,0,-1,0,1],[-1,0,1,0,-1],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,61),  # line 1462
    '[35/6, 28/605, 1331/2, 3/7, 15/11]': ('nd',[3,4],{},[[1,0,-3],[0,1,-7],[-1,1,-6],[4,-3,-3],[-1,1,-10],[-1,1,-12]],[1,1],None,400,False,6088),  # line 1463
    '[35/6, 28/605, 1331/2, 3/7, 35/11]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-6],[-1,1,-6],[3,-2,-2],[1,0,-30],[1,0,-31],[1,0,-32],[1,0,-33]],[1,1],None,400,True,229),  # line 1464
    '[35/6, 28/605, 1331/2, 3/7, 6/11]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-6],[-1,1,-6],[3,-2,-2],[1,0,-30],[1,0,-31],[1,0,-32],[1,0,-33]],[1,1],None,400,True,234),  # line 1465
    '[35/6, 3/385, 4/5, 121/2, 150/11]': ('ndxz',[1,4],{'0': 2},[[1,0,-385],[0,1,-1],[1,-48,0]],[1,3],'2',1000,True,4232),  # line 1490
    '[35/6, 3/385, 4/5, 121/2, 75/121]': ('ndxz',[1,4],{'0': 2},[[1,0,-385],[0,1,-1],[1,-48,0]],[1,3],'2',300,True,3462),  # line 1491
    '[35/6, 3/385, 4/5, 121/2, 875/11]': ('ndxz',[1,4],{'0': 2},[[1,0,-385],[0,1,-1],[1,-48,0]],[1,3],'2',1000,True,3847),  # line 1492
    '[35/6, 3/385, 8/5, 77/2, 75/7]': ('mul',2,[[],[],[],['-2','3'],['-1','2']],9,1,[[81,601],[729,5461],[6561,49201],[59049,442861]]),  # line 1493
    '[35/6, 4/55, 11011/2, 51/7, 2/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[3,-2,0,0,-1],[-2,1,-1,1,0],[2,-1,1,-1,0],[2,-1,-1,0,1],[-2,1,1,0,-1],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,66),  # line 1524
    '[35/6, 4/55, 11011/2, 51/7, 5/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-4],[1,0,0,0,-4],[1,0,0,0,-6],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,3000,False,95),  # line 1525
    '[35/6, 4/55, 187187/2, 3/7, 2/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[3,-2,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,1],[-2,1,1,0,-1],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,51),  # line 1526
    '[35/6, 4/55, 187187/2, 3/7, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[4,-3,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,1],[-2,1,1,0,-1]],[1,1,1,1],None,400,False,29),  # line 1527
    '[35/6, 4/55, 65219/2, 3/7, 2/121]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-3],[-2,3,-8],[1,-1,0]],[1,1],None,400,'all',11),  # line 1528
    '[35/6, 4/55, 847/2, 663/7, 5/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[4,-3,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[5,-3,-1,0,2],[-5,3,1,0,-2]],[1,1,1,1],None,400,False,39),  # line 1529
    '[35/6, 4/605, 121121/2, 3/7, 2/13]': ('ndx',[3,4,5],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-6],[2,-1,0,-1],[3,-1,-2,2],[-3,1,2,-2],[1,0,0,-8],[1,0,0,-30],[1,0,0,-31],[1,0,0,-32],[1,0,0,-34]],[1,1,1],None,400,True,239),  # line 1530
    '[35/6, 4/605, 121121/2, 3/7, 5/13]': ('ndx',[3,4,5],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-6],[5,-3,0,-2],[3,-1,-2,2],[-3,1,2,-2],[1,0,0,-30],[1,0,0,-31],[1,0,0,-32],[1,0,0,-33]],[1,1,1],None,400,True,165),  # line 1531
    '[35/6, 4/605, 9317/2, 3/7, 10/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-8],[5,-3,-2],[1,0,-30]],[1,1],None,400,True,213),  # line 1532
    '[35/6, 4/605, 9317/2, 3/7, 2/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-4],[5,-3,-2],[1,0,-8],[1,0,-24],[1,0,-30],[1,0,-31],[1,0,-32],[1,0,-33],[1,0,-34]],[1,1],None,400,True,239),  # line 1533
    '[35/6, 4/605, 9317/2, 3/7, 25/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-8],[3,-2,0],[1,0,-24],[1,0,-25],[1,0,-31]],[1,1],None,400,True,114),  # line 1534
    '[35/6, 4/605, 9317/2, 3/7, 25/3]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-12],[7,-3,-4],[2,-1,-24],[2,-1,-26]],[1,1],None,400,False,353),  # line 1535
    '[35/6, 4/605, 9317/2, 3/7, 4/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-8],[2,-1,-2],[2,-1,-24],[2,-1,-27],[-1,1,-9]],[1,1],None,400,False,161),  # line 1536
    '[35/6, 4/605, 9317/2, 3/7, 5/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-4],[3,-2,-2],[0,1,-30],[1,0,-30],[1,0,-31],[1,0,-32],[1,0,-33]],[1,1],None,400,True,165),  # line 1537
    '[35/6, 4/605, 9317/2, 3/7, 5/3]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-8],[3,-1,0],[1,0,-7],[1,0,-10],[2,-1,-24],[-1,1,-9],[2,-1,-28]],[1,1],None,400,False,259),  # line 1538
    '[35/6, 4/605, 9317/2, 3/7, 5/33]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-1,1,-6],[5,-2,0],[1,0,-7],[1,0,-10],[-1,1,-10],[2,-1,-24],[2,-1,-27]],[1,1],None,400,False,259),  # line 1539
    '[35/6, 4/605, 9317/2, 39/7, 5/13]': ('ndx',[1,4,5],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-6],[5,-3,0,-2],[7,-3,-2,4],[-7,3,2,-4],[1,0,0,-30],[1,0,0,-31],[1,0,0,-32],[1,0,0,-33]],[1,1,1],None,400,True,211),  # line 1540
    '[35/6, 55/2, 8/77, 663/5, 7/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,0,-1,1,0],[0,0,1,-1,0],[4,-5,-1,0,2],[-4,5,1,0,-2],[1,0,0,0,-7],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,67),  # line 1545
    '[35/6, 56/165, 539/2, 3/7, 5/3]': ('ndxz',[3,4],{},[[1,0,-2],[0,1,-1],[-1,4,0],[1,-2,0],[1,0,-4],[0,1,-5],[1,0,-20]],[1,1],None,300,True,39),  # line 1546
    '[35/6, 56/55, 2431/2, 3/7, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-3],[0,0,1,0,-3],[0,0,0,1,-3],[-1,1,0,0,-4],[5,-3,0,0,-2],[0,0,-1,1,0],[0,0,1,-1,0],[2,0,-1,0,1],[-2,0,1,0,-1],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,76),  # line 1547
    '[35/6, 56/715, 2431/2, 3/7, 5/17]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-3],[0,0,1,0,-3],[0,0,0,1,-3],[-1,1,0,0,-4],[5,-3,0,0,-2],[0,-1,1,0,0],[0,1,-1,0,0],[2,0,0,-1,1],[-2,0,0,1,-1],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,76),  # line 1548
    '[35/6, 605/2, 4/77, 663/5, 7/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[4,-3,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[5,-3,-1,0,2],[-5,3,1,0,-2]],[1,1,1,1],None,400,False,39),  # line 1551
    '[35/6, 6655/3, 9/77, 2/55, 21/2]': ('ndx',[0,4],{},[[1,0,-273],[0,1,-95],[-13,50,0],[7,-20,0]],[2,1],'2',1000,False,1322),  # line 1552
    '[35/6, 7/110, 4/5, 77/2, 3/7, 2/11]': ('ndx',[4,3],{},[[1,0,-1],[0,1,-1],[-2,1,-9],[1,0,-10],[3,-1,-30],[3,-1,-34]],[1,1],None,3000,False,2621),  # line 1574
    '[35/6, 715/2, 8/1001, 51/5, 7/17]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,-1,1,0,0],[0,1,-1,0,0],[4,-5,0,-1,2],[-4,5,0,1,-2],[1,0,0,0,-7],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,67),  # line 1605
    '[35/6, 715/2, 8/77, 51/5, 2/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[1,-1,0,0,-1],[-1,1,-1,1,0],[1,-1,1,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-5],[1,0,0,0,-8],[1,0,0,0,-15]],[1,1,1,1],None,400,False,137),  # line 1606
    '[35/6, 715/2, 8/77, 51/5, 7/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,1,-2,1,0],[0,-1,2,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-7],[1,0,0,0,-12],[1,0,0,0,-13],[1,0,0,0,-14]],[1,1,1,1],None,400,False,67),  # line 1607
    '[35/6, 7865/2, 4/77, 51/5, 2/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[3,-2,0,0,-1],[-2,1,-1,1,0],[2,-1,1,-1,0],[2,-1,-1,0,1],[-2,1,1,0,-1],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,66),  # line 1608
    '[35/6, 7865/2, 4/77, 51/5, 7/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-3],[4,-3,0,0,-1],[-1,1,-2,1,0],[1,-1,2,-1,0],[2,-1,-1,0,1],[-2,1,1,0,-1]],[1,1,1,1],None,400,False,39),  # line 1609
    '[35/6, 8/275, 847/2, 3/7, 4/11]': ('nd',[0,2,3,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[1,1,-1,1,-3]],[1,1,1,1],None,1000,True,64),  # line 1615
    '[35/6, 8/55, 1001/2, 51/7, 2/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[1,-1,0,0,-1],[-1,1,-1,1,0],[1,-1,1,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-5],[1,0,0,0,-8],[1,0,0,0,-15],[-1,3,0,0,-12],[1,-1,0,0,-3],[-1,3,0,0,-13]],[1,1,1,1],None,400,False,137),  # line 1616
    '[35/6, 8/55, 1001/2, 51/7, 5/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,1,-2,1,0],[0,-1,2,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-7],[1,0,0,0,-12],[-1,3,0,0,-12],[1,0,0,0,-13],[-1,3,0,0,-14]],[1,1,1,1],None,400,False,67),  # line 1617
    '[35/6, 8/55, 17017/2, 3/7, 2/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[1,-1,0,0,-1],[0,0,-1,1,0],[0,0,1,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-5],[1,0,0,0,-8],[1,0,0,0,-15],[-1,3,0,0,-12],[1,-1,0,0,-3],[-1,3,0,0,-13]],[1,1,1,1],None,400,False,97),  # line 1618
    '[35/6, 8/55, 17017/2, 3/7, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,0,-1,1,0],[0,0,1,-1,0],[2,-2,-1,0,1],[-2,2,1,0,-1],[1,0,0,0,-7],[1,0,0,0,-12],[-1,3,0,0,-12],[1,0,0,0,-13],[-1,3,0,0,-14]],[1,1,1,1],None,400,False,46),  # line 1619
    '[35/6, 8/55, 77/2, 663/7, 5/221]': ('nd',[1,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-2],[2,-3,0,0,0],[0,0,-1,1,0],[0,0,1,-1,0],[4,-5,-1,0,2],[-4,5,1,0,-2],[1,0,0,0,-7],[1,0,0,0,-12],[-1,3,0,0,-12],[1,0,0,0,-13],[-1,3,0,0,-14]],[1,1,1,1],None,400,False,67),  # line 1620
    '[35/6, 9/55, 16/5, 11/7, 245/2]': ('ndx',[0,3],{},[[1,0,-4],[0,1,-2],[-1,2,-2],[2,-3,-10]],[1,1],None,400,True,46),  # line 1621
    '[35/6, 9/55, 224/5, 11/7, 5/2]': ('nd',[0,3],{},[[1,0,-5],[0,1,-1],[-1,3,0],[2,-3,-12],[0,1,-5],[-1,2,-8],[-1,2,-22],[-1,2,-23]],[5,3],'492',400,False,300),  # line 1622
    '[35/6, 9/55, 9317/3, 2/77, 15/2]': ('ndx',[0,4],{},[[1,0,-273],[0,1,-95],[-13,50,0],[7,-20,0]],[2,1],'2',300,False,1322),  # line 1623
    '[350/9, 6/605, 1/147, 121/2, 3/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-22],[-5,1,-20],[1,0,-8],[1,0,-9]],[1,1],None,400,False,361),  # line 1624
    '[36/35, 1/429, 25/3, 11/25, 273/2]': ('nd',[0,3,5],{'2': 2},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-1,1,-4,3]],[1,1,1],None,1000,True,127),  # line 1625
    '[36/35, 5/22, 10829/2, 11/3, 5/221]': ('nd',[1,3,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-5],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,-5],[3,-2,0,0,-4],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,3],[-2,1,1,0,-3]],[1,1,1,1],None,400,False,45),  # line 1626
    '[4/105, 1/2662, 9/2, 605/3, 14/5]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-4],[2,-1,2],[0,1,-12],[0,1,-24],[0,1,-25],[0,1,-26]],[1,1],None,144,True,195),  # line 1627
    '[4/105, 27/2, 55/3, 49/605, 3/5]': ('ndx',[2,4],{},[[1,0,-3],[0,1,-3],[-1,1,-2],[4,-3,-4]],[1,1],None,400,True,23),  # line 1628
    '[4/105, 81/2, 55/3, 7/605, 3/5]': ('ndx',[2,4],{},[[1,0,-4],[0,1,-4],[-1,1,-1],[4,-3,-11],[0,1,-24],[0,1,-32],[0,1,-38],[0,1,-41]],[1,1],None,400,True,108),  # line 1629
    '[4/105, 891/2, 5/3, 7/55, 3/25]': ('ndcv',[2,4],{},[[1,0,-4],[0,1,-1],[1,-1,-13],[0,1,-4],[0,1,-5],[0,1,-9],[0,1,-20],[1,-2,-3]],[1,1],None,400,False,356),  # line 1630
    '[4/135, 9/14, 25/2, 7/5, 20/7]': ('add',3,[[],[],['2','15'],[]],2,[[7,8422],[8,10969],[9,13852],[10,17071]]),  # line 1631
    '[4/135, 99/14, 25/2, 7/11, 22/5]': ('add',3,[[],['2'],['6','3'],[],['6','3']],2,[[11,2294],[12,2660],[13,3053],[14,3473]]),  # line 1632
    '[4/15, 1/126, 33/2, 49/3, 5/11, 2/7]': ('ndx',[3,4],{},[[1000,-925,0],[-1000,969,0],[0,1,-5000]],[2,1],'1',1000,False,34598),  # line 1671
    '[4/15, 1/126, 33/2, 7/3, 5/11, 10/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,428),  # line 1672
    '[4/15, 1/126, 33/2, 7/3, 5/11, 2/7]': ('ndx',[3,4],{},[[1,0,-70],[0,1,-149],[-2,1,0],[5,-2,0]],[1,1],None,300,False,776),  # line 1673
    '[4/15, 1/126, 33/2, 7/3, 5/11, 22/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,1168),  # line 1674
    '[4/15, 1/126, 33/2, 7/3, 5/11, 33/7]': ('ndx',[3,4],{},[[1,0,-70],[0,1,-149],[-2,1,0],[5,-2,0]],[1,1],None,300,False,769),  # line 1675
    '[4/15, 1/126, 33/2, 7/3, 5/11, 6/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,4229),  # line 1676
    '[4/15, 1/126, 33/2, 7/3, 5/11, 9/7]': ('ndx',[2,3],{'0': 4},[[1,0,-298],[0,1,-126],[-2,5,0],[7,-16,0]],[1,1],None,300,False,1952),  # line 1677
    '[4/15, 1/1386, 21/2, 11/3, 5/7, 2/11]': ('ndx',[3,4],{},[[1,0,-101],[0,1,-1],[0,100,0],[1,-8,0],[0,1,-5]],[1,1],None,300,False,2130),  # line 1679
    '[4/15, 1/154, 147/2, 11/3, 5/7, 9/11]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-1],[1,-1,-55],[0,1,-5],[0,1,-7],[0,1,-9],[0,1,-11],[0,1,-14],[0,1,-16],[0,1,-19],[0,1,-37],[0,1,-40],[0,1,-43]],[6,3],'10080',400,False,778),  # line 1681
    '[4/15, 1/154, 39/2, 343/9, 110/13]': ('nd',[0,2,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,0,0,1,-2],[-2,-1,4,1,2],[2,1,-4,-1,-2],[0,1,0,0,-4]],[1,1,1,1],None,400,True,64),  # line 1682
    '[4/15, 1/294, 1/5, 385/2, 9/11, 5/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-6,24],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,595),  # line 1738
    '[4/15, 1/294, 1/5, 4235/2, 3/11, 5/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-6,24],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,757),  # line 1739
    '[4/15, 1/294, 385/2, 1/5, 9/11, 5/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-6,24],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,595),  # line 1740
    '[4/15, 1/294, 4235/2, 1/5, 3/11, 5/3]': ('ndcv',[1,3],{},[[1,0,-2],[0,1,-1],[1,-6,24],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,757),  # line 1741
    '[4/15, 1/3, 1/490, 231/2, 25/11, 3/5]': ('ndcv',[2,3],{},[[1,0,-2],[0,1,-1],[1,-6,24],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,595),  # line 1742
    '[4/15, 1/3, 1/490, 2541/2, 5/11, 3/5]': ('ndcv',[2,3],{},[[1,0,-2],[0,1,-1],[1,-6,24],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,757),  # line 1743
    '[4/15, 1/42, 33/2, 539/3, 5/11, 2/7]': ('ndx',[2,3],{},[[1,0,-101],[0,1,-1],[0,100,0],[1,-8,0],[0,1,-5]],[1,1],None,300,False,593),  # line 1750
    '[4/15, 1/42, 99/2, 7/3, 5/11, 6/7]': ('mul',4,[[],[],[],['0','3'],['-2','8']],3,1,[[9,1142],[27,3638],[81,11174],[243,33830]]),  # line 1753
    '[4/15, 1/588, 33/2, 7/3, 5/11, 2/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[1,0,-10],[-3,2,0],[-3,2,-10],[-3,2,-15]],[1,2],'2',400,False,380),  # line 1773
    '[4/15, 1/588, 33/2, 7/3, 5/11, 3/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[-2,1,0],[4,-1,0],[0,1,-4],[1,0,-10],[-3,2,-13],[-3,2,-15]],[1,1],None,400,False,321),  # line 1774
    '[4/15, 1/84, 33/2, 7/3, 5/11, 2/7]': ('ndx',[3,4],{},[[1,0,-15],[0,1,-271],[-8,1,0],[43,-1,0]],[1,1],None,300,False,2016),  # line 1802
    '[4/15, 1/84, 33/2, 7/3, 5/11, 22/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,742),  # line 1803
    '[4/15, 1/84, 33/2, 7/3, 5/11, 33/7]': ('ndx',[3,4],{},[[1,0,-15],[0,1,-271],[-8,1,0],[43,-1,0]],[1,1],None,300,False,2006),  # line 1804
    '[4/15, 1/84, 33/2, 7/3, 5/11, 9/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,1707),  # line 1805
    '[4/15, 1/882, 33/2, 7/3, 5/11, 2/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[1,0,-10]],[1,1],None,400,True,128),  # line 1806
    '[4/15, 1/882, 33/2, 7/3, 5/11, 3/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[1,0,-10],[-3,2,0],[-3,2,-8],[-3,2,-15]],[2,2],'9',400,False,248),  # line 1807
    '[4/15, 1/98, 143/3, 33/2, 35/11, 3/13]': ('nd',[2,3,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[0,-1,3,-1],[0,1,0,-8],[0,1,0,-12],[0,1,0,-16],[4,-1,0,-16],[12,-3,0,-64],[0,1,0,-17],[0,1,0,-18],[12,-3,0,-74],[0,1,0,-19]],[1,1,1],None,1000,False,135),  # line 1808
    '[4/15, 1/98, 27/2, 77/3, 5/11, 3/5]': ('ndcv',[2,3],{},[[1,0,-3],[0,1,-1],[1,-1,1],[0,1,-8],[0,1,-12],[0,1,-16],[2,-1,-18],[2,-1,-30],[0,1,-17],[0,1,-18],[0,1,-19],[2,-1,-32]],[1,1],None,400,False,190),  # line 1809
    '[4/15, 1/98, 33/2, 143/3, 35/11, 3/13]': ('nd',[2,3,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[0,-1,3,-1]],[1,1,1],None,1000,False,135),  # line 1810
    '[4/15, 1/98, 33/2, 7/27, 5/11, 2/5]': ('ndx',[2,3],{},[[1,0,-3],[0,1,-1],[1,-2,-14],[0,1,-8],[0,1,-9],[2,-1,-82],[2,-1,-106]],[1,1],None,400,False,651),  # line 1811
    '[4/15, 1/98, 33/2, 7/27, 5/11, 3/5]': ('nd',[2,3],{},[[1,0,-3],[0,1,-1],[1,-2,-7],[1,0,-15],[1,0,-16]],[1,1],None,400,True,117),  # line 1812
    '[4/15, 11/21, 99/8, 35/11, 33/2]': ('add',3,[['1'],[],['2','3'],['2','4','2'],[]],2,[[13,1723],[14,1981],[15,2257],[16,2551]]),  # line 1813
    '[4/15, 11/84, 33/2, 7/3, 5/11, 2/7]': ('ndx',[3,4],{},[[1,0,-70],[0,1,-149],[-2,1,0],[5,-2,0]],[1,1],None,300,False,752),  # line 1814
    '[4/15, 3/14, 275/2, 49/5, 50/77]': ('nd',[0,4],{},[[1,0,-35],[0,1,-18]],[3,1],'6',3000,False,178),  # line 1829
    '[4/15, 33/14, 275/2, 1547/11, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-2,3,0,0,-4],[1,-1,0,0,-3],[0,0,-1,1,0],[0,0,1,-1,0],[-3,5,-1,0,2],[3,-5,1,0,-2]],[1,1,1,1],None,400,False,39),  # line 1831
    '[4/15, 33/14, 3575/2, 119/11, 2/221]': ('nd',[3,2,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-4],[1,0,0,0,-4],[1,0,0,0,-6],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,3000,False,66),  # line 1832
    '[4/15, 33/14, 3575/2, 119/11, 3/221]': ('nd',[3,2,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-4],[1,0,0,0,-4],[1,0,0,0,-6],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,3000,False,95),  # line 1833
    '[4/15, 33/14, 5/2, 7/11, 22/5, 2/49]': ('ndz',[2,3],{'1': 1,'4': 2},[[1,0,-1],[0,1,-1],[2,-1,0]],[1,1],None,1000,'all',25),  # line 1834
    '[4/15, 33/14, 55/2, 7/121, 2/5, 2/11]': ('ndxz',[2,4],{},[[1,0,-1],[0,1,-1],[-2,1,1],[4,-1,-2]],[1,1],None,400,True,255),  # line 1835
    '[4/15, 33/14, 60775/2, 7/11, 2/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-2,3,0,0,-1],[1,-1,0,0,-3],[0,0,-1,1,0],[0,0,1,-1,0],[-1,2,-1,0,1],[1,-2,1,0,-1]],[1,1,1,1],None,400,False,21),  # line 1836
    '[4/15, 33/14, 60775/2, 7/11, 3/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-2,3,0,0,-4],[1,-1,0,0,-3],[0,0,-1,1,0],[0,0,1,-1,0],[-1,2,-1,0,1],[1,-2,1,0,-1]],[1,1,1,1],None,400,False,29),  # line 1837
    '[4/15, 35/3, 21/10, 77/2, 5/7, 3/11]': ('val',2,4,{'1': 1},4,20,[2,2,1,1],135,None),  # line 1838
    '[4/15, 35/6, 21/5, 77/2, 3/7, 5/11]': ('val',1,4,{'2': 1},4,20,[2,2,1,1],135,None),  # line 1839
    '[4/15, 9/1078, 245/2, 11/5, 10/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[1,-3,-11],[0,1,-5],[0,1,-7],[0,1,-15]],[1,1],None,400,False,153),  # line 1879
    '[4/15, 9/1078, 35/2, 77/5, 10/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[1,-3,1],[0,1,-5],[0,1,-7],[0,1,-15]],[1,1],None,400,False,153),  # line 1880
    '[4/15, 9/11858, 35/2, 11/5, 15/7]': ('add',3,[[],[],[],['7','19/2','9/2'],['4','4']],10,[[49,75109],[50,78141],[51,81233],[52,84385]]),  # line 1881
    '[4/15, 9/11858, 35/2, 11/5, 4/7]': ('add',3,[[],[],[],['7','19/2','9/2'],['4','4']],10,[[49,71284],[50,74163],[51,77099],[52,80092]]),  # line 1882
    '[4/15, 9/14, 605/2, 7/5, 50/77]': ('nd',[2,4],{},[[1,0,-733],[0,1,-11036],[-1,1,-24882]],[8,1],'a8',1000,False,32658),  # line 1883
    '[4/15, 9/154, 245/2, 11/5, 50/11]': ('ndcv',[2,3],{},[[1,0,-733],[0,1,-9624],[-1,1,-21461]],[8,1],'a8',1000,False,32658),  # line 1884
    '[4/15, 9/154, 35/2, 11/5, 220/7]': ('nd',[0,3],{},[[1,0,-5],[0,1,-1],[-2,3,-1],[4,-3,-25],[1,1,-26]],[1,1],None,400,False,173),  # line 1885
    '[4/15, 9/154, 35/2, 11/5, 825/7]': ('nd',[0,3],{},[[1,0,-5],[0,1,-1],[-2,3,-1],[4,-3,-25],[1,1,-26]],[1,1],None,400,False,181),  # line 1886
    '[4/15, 9/98, 275/2, 7/25, 10/11]': ('ndx',[1,3,4],{},[[1,0,0,-5],[0,1,0,-1],[0,0,1,-15],[0,-1,1,-37],[0,1,0,-8],[0,1,0,-14],[0,1,0,-24],[0,1,0,-25],[0,1,0,-26],[0,1,0,-27],[0,1,0,-28],[0,1,0,-29]],[1,1,1],None,400,False,663),  # line 1887
    '[4/315, 25/6, 9317/2, 3/11, 5/3]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-3],[0,1,-4],[1,0,-5],[1,0,-8],[4,-1,-3],[0,1,-25],[-5,2,-10],[1,0,-9]],[1,1],None,400,False,77),  # line 1893
    '[4/45, 1/14, 55/2, 7/25, 9/11, 5/3]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-1],[0,1,-8],[0,1,-9]],[1,1],None,400,True,70),  # line 1896
    '[4/45, 1/14, 605/2, 7/25, 3/11, 5/3]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-1],[0,1,-8],[0,1,-9]],[1,1],None,400,True,90),  # line 1897
    '[4/45, 1/42, 1089/2, 7/33, 15/7]': ('ndx',[2,3],{},[[1,0,-101],[0,1,-1],[0,100,0],[1,-8,0],[0,1,-5]],[1,1],None,300,False,1894),  # line 1898
    '[4/45, 1/42, 99/2, 7/3, 5/11, 2/7]': ('nd',[3,4],{},[[1,0,-2],[0,1,-2],[-1,1,-10],[1,0,-10],[3,-2,-24],[3,-2,-32],[3,-2,-35],[3,-2,-36]],[1,1],None,1000,False,1849),  # line 1899
    '[4/45, 1/42, 99/2, 7/33, 75/7]': ('ndz',[3,4],{},[[1,0,-1],[0,1,-1]],[4,8],'560000',1000,'all',21),  # line 1900
    '[4/45, 245/22, 27/2, 11/7, 22/3]': ('ndx',[1,3],{},[[1,0,-6],[0,1,-2],[-2,3,-2],[1,-1,-6]],[1,1],None,400,True,48),  # line 1905
    '[4/45, 27/14, 55/2, 7/5, 50/11]': ('ndx',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,True,79),  # line 1906
    '[4/45, 297/14, 25/2, 7/11, 14/5]': ('add',2,[[],[],['20','39','20'],[],['3','4']],6,[[29,39390],[30,42067],[31,44832],[32,47685]]),  # line 1907
    '[4/45, 297/14, 25/2, 7/11, 22/5]': ('add',2,[[],[],['3','9','20'],[],['1','4']],6,[[23,23716],[24,25803],[25,27978],[26,30241]]),  # line 1908
    '[4/45, 297/14, 5/2, 7/11, 28/5]': ('add',2,[[],[],['7','11','4'],[],['3','4']],6,[[29,39509],[30,42190],[31,44959],[32,47816]]),  # line 1909
    '[4/45, 297/14, 5/2, 7/11, 44/5]': ('add',2,[[],[],['2','5','4'],[],['1','4']],6,[[29,37675],[30,40294],[31,43001],[32,45796]]),  # line 1910
    '[4/45, 297/14, 65/2, 7/11, 14/13]': ('add',2,[[],[],['7','11','4'],[],['3','4'],['13','28','16']],6,[[29,39390],[30,42067],[31,44832],[32,47685]]),  # line 1911
    '[4/45, 297/14, 65/2, 7/11, 22/13]': ('add',2,[[],[],['2','5','4'],[],['1','4'],['1','4','16']],6,[[29,37558],[30,40173],[31,42876],[32,45667]]),  # line 1912
    '[4/45, 3/14, 1375/2, 7/5, 20/11]': ('ndx',[1,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,-1,3,-3],[0,1,0,-4],[0,1,0,-8],[0,1,0,-16],[0,1,0,-20]],[1,1,1],None,400,True,131),  # line 1913
    '[4/45, 55/14, 297/2, 7/11, 10/3]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,2,-5],[1,-1,-8]],[1,1],None,400,True,35),  # line 1914
    '[4/45, 55/14, 297/2, 7/11, 2/3]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,21),  # line 1915
    '[4/45, 55/14, 297/2, 7/11, 25/3]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-2,3,0],[1,-1,-8],[-1,2,-16],[-1,2,-24],[-1,2,-26]],[1,1],None,400,False,265),  # line 1916
    '[4/45, 55/14, 297/2, 7/11, 25/7]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,3,-8],[1,-1,-12]],[1,1],None,400,True,29),  # line 1917
    '[4/45, 55/14, 297/2, 7/11, 4/3]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,2,-2],[1,-1,-8]],[1,1],None,400,True,27),  # line 1918
    '[4/45, 55/14, 297/2, 7/11, 5/21]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,3,-2],[1,-1,-6],[0,1,-5]],[1,1],None,400,True,32),  # line 1919
    '[4/45, 55/14, 297/2, 7/11, 5/3]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-2,3,-2],[1,-1,-4]],[1,1],None,400,True,29),  # line 1920
    '[4/45, 55/14, 297/2, 7/11, 5/7]': ('ndx',[1,4],{},[[1,0,-3],[0,1,-1],[-1,3,0],[1,-1,-8],[0,1,-5]],[1,1],None,400,True,32),  # line 1921
    '[4/45, 55/14, 297/2, 91/11, 5/13]': ('nd',[1,3,5],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[-1,2,0,-4],[1,-1,0,-6],[-3,7,-2,4],[3,-7,2,-4]],[1,1,1],None,400,True,39),  # line 1922
    '[4/45, 55/14, 3861/2, 7/11, 2/13]': ('nd',[1,4,5],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[-1,2,0,-1],[1,-1,0,-6],[-1,3,-2,2],[1,-3,2,-2]],[1,1,1],None,400,True,21),  # line 1923
    '[4/45, 55/14, 3861/2, 7/11, 5/13]': ('nd',[1,4,5],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[-1,2,0,-4],[1,-1,0,-6],[-1,3,-2,2],[1,-3,2,-2]],[1,1,1],None,400,True,29),  # line 1924
    '[44/105, 5/66, 49/2, 3/7, 20/3]': ('ndcv',[3,4],{},[[1,0,-7],[0,1,-1],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[1,0,-34],[1,0,-35],[1,0,-36]],[1,1],None,400,False,554),  # line 1929
    '[45/8, 4/21, 5/33, 77/5, 15/2]': ('add',3,[['1'],[],[],['2','3'],['2','4','2']],1,[[6,421],[7,553],[8,703],[9,871]]),  # line 1934
    '[49/2475, 121/21, 10/11, 9/2, 11/3]': ('ndcv',[1,2],{},[[1,0,-3],[0,1,-1],[-1,2,-2],[2,-3,-3],[0,1,-16],[-1,2,-8],[-1,2,-10]],[1,1],None,400,False,1810),  # line 1935
    '[49/2475, 121/21, 10/11, 9/2, 7/3]': ('ndcv',[0,2],{},[[1,0,-2],[0,1,-2],[-1,1,-3],[4,-3,-3],[0,1,-16],[0,1,-17],[-1,1,-4]],[1,1],None,400,False,137),  # line 1936
    '[49/2475, 121/21, 2/11, 45/2, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[-1,2,-6],[1,-1,-4],[0,1,-16],[1,0,-25],[0,1,-17],[-1,2,-8],[0,1,-18],[4,-5,-22],[0,1,-19],[-1,2,-9]],[1,1],None,400,False,175),  # line 1937
    '[49/2475, 2/11, 121/21, 45/2, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[0,1,-16],[4,-5,-24],[-1,2,-6],[0,1,-17],[-1,2,-8],[0,1,-19]],[1,1],None,400,False,175),  # line 1938
    '[49/2475, 6/11, 121/35, 25/2, 11/5]': ('ndx',[0,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-6],[0,0,1,-8],[0,0,1,-10]],[1,1,1],None,1000,True,93),  # line 1939
    '[49/2475, 6/11, 121/35, 25/2, 7/5]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-2],[-1,1,-3],[4,-3,-4],[8,-5,-112],[8,-5,-135],[8,-5,-137]],[1,1],None,1000,False,531),  # line 1940
    '[49/450, 11/2, 4/21, 45/11, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[0,1,-8],[1,0,-10],[0,1,-12],[1,0,-16],[0,1,-16],[4,-5,-24],[-1,2,-6],[0,1,-17],[-1,2,-8],[0,1,-19]],[1,1],None,400,False,176),  # line 1941
    '[49/450, 33/2, 4/21, 15/11, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[3,-4,-4],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,194),  # line 1942
    '[49/450, 33/2, 4/35, 25/11, 7/5]': ('ndx',[2,3,4],{},[[1,0,0,-1],[0,1,0,-14],[0,0,1,-1]],[1,1,1],None,1000,True,114),  # line 1943
    '[49/450, 33/2, 4/77, 5/11, 4/3]': ('add',3,[[],['7','19/2','9/2'],['4','4'],[],[]],10,[[49,71284],[50,74163],[51,77099],[52,80092]]),  # line 1944
    '[49/450, 33/2, 4/77, 5/11, 77/3]': ('add',3,[[],['7','19/2','9/2'],['4','4'],[],[]],10,[[49,75109],[50,78141],[51,81233],[52,84385]]),  # line 1945
    '[49/450, 363/2, 4/35, 5/11, 7/5]': ('ndx',[1,4],{},[[1,0,-77],[0,1,-140],[-5,3,0],[2,-1,0]],[1,1],None,300,False,663),  # line 1946
    '[49/450, 4/21, 11/2, 45/11, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[-1,2,-6],[1,-1,-4],[0,1,-16],[1,0,-25],[0,1,-17],[-1,2,-8],[0,1,-18],[4,-5,-22],[0,1,-19],[-1,2,-9]],[1,1],None,400,False,176),  # line 1947
    '[49/450, 4/21, 33/2, 15/11, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[3,-4,-4]],[1,1],None,128,'all',56),  # line 1948
    '[49/450, 4/21, 55/2, 9/11, 7/3]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[-2,3,-1],[1,-1,-3],[1,0,-16],[-5,8,-20],[1,0,-17],[1,-1,-4],[1,0,-18],[-5,8,-22],[1,0,-19]],[1,1],None,400,False,154),  # line 1949
    '[49/450, 4/21, 605/2, 3/11, 7/3]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-2],[-4,3,-2],[2,-1,-6],[1,0,-16],[-5,4,-20],[1,0,-17],[1,0,-18],[-5,4,-22],[1,0,-19]],[1,1],None,400,False,191),  # line 1950
    '[49/450, 4/21, 99/2, 5/11, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[3,-4,-4],[1,0,-15],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,True,194),  # line 1951
    '[49/450, 4/77, 33/2, 5/11, 4/3]': ('add',3,[[],['7','19/2','9/2'],['4','4'],[],[]],10,[[49,71284],[50,74163],[51,77099],[52,80092]]),  # line 1952
    '[49/450, 4/77, 33/2, 5/11, 77/3]': ('add',3,[[],['7','19/2','9/2'],['4','4'],[],[]],10,[[49,75109],[50,78141],[51,81233],[52,84385]]),  # line 1953
    '[49/450, 99/2, 4/21, 5/11, 7/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[3,-4,-4],[0,1,-8],[0,1,-12],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,194),  # line 1954
    '[5/12, 27/245, 77/3, 4/11, 21/2]': ('mul',2,[['1','680'],[],[],['8/3','340/3'],[]],4,1,[[16,32640],[64,130560],[256,522240],[1024,2088960]]),  # line 1955
    '[5/12, 27/245, 847/3, 2/11, 21/2]': ('mul',2,[['1','680'],[],[],['8/3','340/3'],[]],4,1,[[16,43520],[64,174080],[256,696320],[1024,2785280]]),  # line 1956
    '[5/12, 539/3, 27/605, 2/7, 33/2]': ('mul',2,[['1','680'],[],[],[],['8/3','340/3']],4,1,[[16,43520],[64,174080],[256,696320],[1024,2785280]]),  # line 1957
    '[5/12, 77/3, 27/245, 4/11, 21/2]': ('mul',2,[['1','680'],[],[],['8/3','340/3'],[]],4,1,[[16,32640],[64,130560],[256,522240],[1024,2088960]]),  # line 1958
    '[5/18, 1372/55, 363/2, 3/7, 5/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-2],[-1,3,-7],[2,-3,-1],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,64,True,69),  # line 1960
    '[5/18, 196/55, 363/2, 9/7, 2/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-2],[-1,3,-7],[3,-2,0],[1,0,-10],[1,0,-16],[-1,4,-20],[1,-2,-24],[1,-2,-25]],[1,1],None,400,False,571),  # line 1961
    '[5/18, 44/35, 147/2, 27/11, 5/7]': ('ndx',[1,3],{},[[1,0,-1],[0,1,-2],[-1,3,-7],[2,-3,-1],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,True,47),  # line 1963
    '[5/18, 44/35, 1617/2, 9/11, 5/7]': ('nd',[0,2,4],{},[[1,0,0,-2],[0,1,0,-2],[0,0,1,-6],[-3,0,2,-5],[7,0,-3,-17],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,False,211),  # line 1964
    '[5/18, 44/35, 17787/2, 3/11, 5/7]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-2],[-1,3,-5],[1,-2,-2],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,True,135),  # line 1965
    '[5/18, 77/2, 48/35, 3/7, 14/11]': ('nd',[0,2,3,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[0,0,-1,1,-8]],[1,1,1,1],None,400,True,38),  # line 1966
    '[5/3, 1/385, 6/245, 26411/2, 15/7]': ('ndcv',[3,4],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,215),  # line 1975
    '[5/3, 1/385, 6/245, 26411/2, 25/7]': ('ndcv',[3,4],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,196),  # line 1976
    '[5/3, 1/385, 6/245, 26411/2, 9/7]': ('ndcv',[3,4],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[2,-3,-42],[2,-3,-43]],[1,1],None,400,False,234),  # line 1977
    '[5/3, 1/490, 6/605, 102487/2, 3/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,245),  # line 1978
    '[5/3, 1/490, 6/605, 102487/2, 5/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-2,1,-8],[1,0,-8],[1,0,-9]],[1,1],None,400,True,225),  # line 1979
    '[5/6, 1/25, 231/5, 3/343, 4/11, 5/2]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-1,0,2],[0,1,-4],[1,2,-12],[1,2,-24],[1,2,-26]],[1,1],None,400,False,182),  # line 2041
    '[5/6, 1/490, 44/5, 7/2, 9/11, 5/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[-1,1,2],[0,1,-4],[0,1,-6],[0,1,-9],[1,0,-20]],[1,1],None,400,True,254),  # line 2050
    '[5/6, 1/490, 44/5, 77/2, 3/11, 2/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[0,1,-9],[1,0,-10],[1,0,-14],[1,0,-20],[-3,2,-30],[-3,2,-35]],[1,4],'8',400,False,537),  # line 2051
    '[5/6, 1/490, 44/5, 77/2, 3/11, 5/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[-2,1,1],[0,1,-4],[0,1,-6],[0,1,-9],[1,0,-12],[1,0,-20],[-3,2,-26],[-3,2,-31],[-3,2,-33]],[1,4],'2',400,False,484),  # line 2052
    '[5/6, 1/490, 484/5, 7/2, 3/11, 5/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-2],[-5,3,-1],[6,-1,-2],[0,1,-4],[0,1,-8],[0,1,-12],[0,1,-18],[1,0,-20]],[1,1],None,400,True,291),  # line 2053
    '[5/6, 1/70, 44/5, 7/2, 9/11, 25/7]': ('ndx',[3,4],{},[[1,0,-7],[0,1,-217],[-4,1,0],[31,-1,0],[1,0,-10]],[1,1],None,300,False,5947),  # line 2097
    '[5/6, 1/70, 44/5, 7/2, 9/11, 5/7]': ('nd',[3,1],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2464),  # line 2098
    '[5/6, 1/70, 44/5, 7/2, 9/11, 55/7]': ('ndx',[3,4],{},[[1,0,-206],[0,1,-218],[-1,1,0],[4,-3,0]],[1,1],None,300,False,1845),  # line 2099
    '[5/6, 1/70, 44/5, 7/2, 9/11, 6/7]': ('nd',[3,1],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2475),  # line 2100
    '[5/6, 1/70, 44/5, 77/2, 3/11, 15/7]': ('ndxz',[3,4],{},[[-4,1,3],[1,0,-1],[0,1,-1]],[4,4],'80a0',2000,'all',1),  # line 2101
    '[5/6, 1/70, 44/5, 77/2, 3/11, 22/7]': ('ndxz',[3,4],{},[[-4,1,3],[1,0,-1],[0,1,-1]],[4,4],'400',2000,'all',22),  # line 2102
    '[5/6, 1/70, 484/5, 7/2, 3/11, 22/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-1],[-2,1,-9],[1,0,-10],[3,-1,-30],[3,-1,-34]],[1,1],None,3000,False,2623),  # line 2104
    '[5/6, 1/70, 484/5, 7/2, 3/11, 25/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-2,1,-6],[1,0,-10],[3,-1,-30],[3,-1,-34],[3,-1,-37]],[1,1],None,3000,False,4417),  # line 2105
    '[5/6, 1/70, 484/5, 7/2, 3/11, 5/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2599),  # line 2106
    '[5/6, 1/70, 484/5, 7/2, 3/11, 55/7]': ('nd',[3,4],{},[[1,0,-2],[0,1,-3],[-2,1,-3],[0,1,-9],[0,1,-25],[3,-1,-35],[-21,11,-87]],[2,2],'2',1000,False,1594),  # line 2107
    '[5/6, 1/70, 484/5, 7/2, 3/11, 6/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2610),  # line 2108
    '[5/6, 11/70, 4/5, 77/2, 9/11, 5/7]': ('ndxz',[2,4],{},[[0,1,-2],[2,-1,-10]],[1,1],None,1000,True,156),  # line 2109
    '[5/6, 11/70, 44/5, 77/2, 3/11, 5/7]': ('mul',4,[[],[],[],['0','1'],['-8','9']],3,1,[[27,2497],[81,8225],[243,25617],[729,78001]]),  # line 2110
    '[5/6, 11/70, 484/5, 7/2, 3/11, 5/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,1000,False,589),  # line 2111
    '[5/6, 16/315, 77/2, 3/11, 4/3]': ('add',2,[[],[],[],['1','4','4'],['1','3']],2,[[15,3661],[16,4161],[17,4693],[18,5257]]),  # line 2112
    '[5/6, 16/35, 77/2, 3/49, 98/11]': ('nd',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,-1,1,0],[0,1,0,-8],[0,1,0,-10]],[1,1,1],None,400,True,66),  # line 2113
    '[5/6, 196/55, 26741/2, 3/7, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-5],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,-5],[3,-2,0,0,-4],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,3],[-2,1,1,0,-3]],[1,1,1,1],None,400,False,45),  # line 2114
    '[5/6, 2/1925, 2401/2, 33/7, 4/3]': ('add',2,[[],['4','21'],[],[],['4','26','28']],4,[[19,41216],[20,45625],[21,50258],[22,55115]]),  # line 2115
    '[5/6, 2/35, 49/2, 3/7, 320/3]': ('add',2,[[],[],[],['2','14']],1,[[4,925],[5,1436],[6,2059],[7,2794]]),  # line 2116
    '[5/6, 2/385, 49/2, 33/7, 80/3]': ('add',2,[[],[],[],['2','10'],[]],1,[[4,661],[5,1026],[6,1471],[7,1996]]),  # line 2117
    '[5/6, 3/1925, 2401/3, 22/7, 9/2]': ('add',2,[['8','21'],[],[],[],['8','32','28']],4,[[19,41678],[20,46111],[21,50768],[22,55649]]),  # line 2130
    '[5/6, 3/385, 2401/3, 22/7, 21/2]': ('add',2,[['5','6'],[],[],[],['5','9','2']],4,[[19,6961],[20,7687],[21,8449],[22,9247]]),  # line 2131
    '[5/6, 3/385, 2401/3, 22/7, 231/2]': ('add',2,[[],[],[],['5','6'],['1','6','4']],2,[[13,3278],[14,3782],[15,4322],[16,4898]]),  # line 2132
    '[5/6, 3/385, 2401/3, 242/7, 21/2]': ('add',2,[['5','6'],[],[],[],['10','21','8']],4,[[19,6961],[20,7687],[21,8449],[22,9247]]),  # line 2133
    '[5/6, 392/165, 539/2, 3/7, 5/3]': ('ndxz',[3,4],{},[[1,0,-2],[0,1,-1],[-1,4,0],[1,-2,0],[1,0,-4],[0,1,-5],[1,0,-20]],[1,1],None,300,True,45),  # line 2135
    '[5/6, 4/175, 3773/2, 3/7, 28/11]': ('nd',[1,2,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,3,-3],[1,0,0,-4],[1,0,0,-6],[1,0,0,-8],[1,0,0,-10],[1,0,0,-16],[1,2,0,-60],[1,2,0,-62],[1,0,0,-17],[1,0,0,-18],[1,0,0,-19]],[1,1,1],None,400,False,566),  # line 2136
    '[5/6, 44/245, 3773/2, 3/11, 10/3]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,2,0],[1,-1,-10],[-1,2,-24],[-1,2,-26],[-1,2,-28]],[1,1],None,400,False,157),  # line 2140
    '[5/6, 44/245, 3773/2, 3/11, 10/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-2,3,-4],[1,-1,-6],[0,1,-30],[0,1,-31],[0,1,-32]],[1,1],None,400,True,108),  # line 2141
    '[5/6, 44/245, 3773/2, 3/11, 2/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4],[0,1,-8],[0,1,-24],[0,1,-30],[0,1,-31],[0,1,-32],[0,1,-33],[0,1,-34]],[1,1],None,400,True,239),  # line 2142
    '[5/6, 44/245, 3773/2, 3/11, 25/3]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-2,3,0],[1,-1,-8],[-1,2,-24],[-1,2,-26],[1,-1,-9]],[1,1],None,400,False,253),  # line 2143
    '[5/6, 44/245, 3773/2, 3/11, 25/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-2,3,-14],[1,-1,-4],[0,1,-30],[0,1,-31]],[1,1],None,400,True,146),  # line 2144
    '[5/6, 44/245, 3773/2, 3/11, 35/3]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,3,-6],[1,-1,-8],[0,1,-10],[-1,2,-24],[-1,2,-26],[-1,2,-29]],[1,1],None,400,False,234),  # line 2145
    '[5/6, 44/245, 3773/2, 3/11, 4/3]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[1,-1,-12],[0,1,-4],[0,1,-7],[0,1,-10],[-1,2,-30]],[1,1],None,400,False,253),  # line 2146
    '[5/6, 44/245, 3773/2, 3/11, 4/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,2,-2],[1,-1,-8]],[1,1],None,400,True,27),  # line 2147
    '[5/6, 44/245, 3773/2, 3/11, 5/21]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4],[0,1,-10],[0,1,-24],[0,1,-30],[0,1,-31],[0,1,-32],[0,1,-33],[0,1,-34]],[1,1],None,400,True,234),  # line 2148
    '[5/6, 44/245, 3773/2, 3/11, 5/3]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,2,-1],[1,-1,-6],[0,1,-10],[0,1,-30],[0,1,-32],[0,1,-34]],[1,1],None,400,True,234),  # line 2149
    '[5/6, 44/245, 3773/2, 39/11, 5/13]': ('ndx',[1,3,5],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-1],[-1,1,0,-4],[4,-3,0,-1],[6,-4,-1,7],[-6,4,1,-7],[1,0,0,-30],[1,0,0,-31],[1,0,0,-32],[1,0,0,-33]],[1,1,1],None,400,True,270),  # line 2150
    '[5/6, 44/245, 49049/2, 3/11, 5/13]': ('ndx',[3,4,5],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[-2,3,0,-5],[1,-1,0,-4],[-2,3,-1,4],[2,-3,1,-4],[0,1,0,-30],[0,1,0,-31],[0,1,0,-32],[0,1,0,-33]],[1,1,1],None,400,True,209),  # line 2151
    '[5/6, 44/35, 10829/2, 9/11, 5/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-1],[0,0,1,0,-2],[0,0,0,1,-2],[-1,3,0,0,-2],[1,-2,0,0,-5],[0,0,-1,1,0],[0,0,1,-1,0],[-1,4,-1,0,3],[1,-4,1,0,-3]],[1,1,1,1],None,400,False,41),  # line 2152
    '[5/6, 44/35, 41503/2, 3/11, 2/49]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-2],[-1,1,0],[4,-3,-8]],[1,1],None,400,'all',11),  # line 2153
    '[5/6, 44/35, 7/2, 3/11, 22/7, 10/3]': ('ndz',[1,3],{},[[1,0,-1],[-1,2,-1],[1,-1,1]],[1,8],'80',1000,'all',101),  # line 2154
    '[5/6, 484/245, 343/2, 3/11, 5/7]': ('ndx',[3,4],{},[[1,0,-6],[0,1,-2],[-2,3,-2],[1,-1,-6],[0,1,-30],[0,1,-31],[0,1,-32],[0,1,-33]],[1,1],None,400,True,229),  # line 2155
    '[5/6, 539/2, 2/35, 3/7, 80/33]': ('add',2,[[],[],[],['2','10'],['1','4','8']],1,[[4,661],[5,1026],[6,1471],[7,1996]]),  # line 2161
    '[5/6, 539/2, 392/165, 3/7, 5/3]': ('ndxz',[3,4],{},[[1,0,-2],[0,1,-1],[-1,4,0],[1,-2,0],[1,0,-4],[0,1,-5],[1,0,-20]],[1,1],None,300,True,45),  # line 2162
    '[5/6, 539/2, 56/605, 3/7, 4/3]': ('mul',2,[[],[],[],['-1/3','28/3'],['5/3','4/3']],25,3,[[625,7394],[15625,184894]]),  # line 2163
    '[5/6, 7/2, 44/35, 3/11, 22/7, 10/3]': ('nd',[1,3],{},[[1,0,-4],[0,1,-3],[1,-1,-9],[-1,2,-1]],[2,2],'8',3000,True,1334),  # line 2167
    '[5/6, 7007/2, 1156/35, 3/17, 5/143]': ('nd',[3,4,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-1,2,0,0,-5],[1,-1,0,0,-7],[0,-1,1,0,0],[0,1,-1,0,0],[-1,-1,0,2,3],[1,1,0,-2,-3]],[1,1,1,1],None,400,False,45),  # line 2177
    '[5/6, 7007/2, 68/35, 9/17, 5/143]': ('nd',[3,4,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-1],[-1,2,0,0,-5],[1,-1,0,0,-7],[0,-1,1,0,0],[0,1,-1,0,0],[-1,-1,0,4,3],[1,1,0,-4,-3]],[1,1,1,1],None,400,False,41),  # line 2178
    '[5/6, 77/2, 16/315, 3/11, 4/3]': ('add',2,[[],[],[],['1','4','4'],['1','3']],2,[[15,3661],[16,4161],[17,4693],[18,5257]]),  # line 2179
    '[5/6, 77/2, 16/35, 3/49, 98/11]': ('nd',[0,3,4],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-3],[0,-1,1,0],[0,1,0,-8],[0,1,0,-10]],[1,1,1],None,400,True,66),  # line 2180
    '[5/6, 77/2, 16/35, 3/7, 245/33]': ('nd',[2,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-3],[0,-1,1,-5],[0,1,0,-2],[0,1,0,-6],[1,0,0,-5],[3,1,0,-43],[3,1,0,-44]],[1,9,1],'180',1000,False,200),  # line 2181
    '[5/6, 77/2, 8/385, 3/7, 196/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-1],[-1,1,-3],[7,-3,-59],[1,0,-32],[1,0,-33],[1,0,-34],[1,0,-35],[1,0,-36],[1,0,-37],[1,0,-38],[1,0,-39]],[1,1],None,400,False,339),  # line 2182
    '[5/6, 8/245, 41503/2, 3/11, 5/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-2],[-2,3,-8],[1,-1,-3]],[1,1],None,400,True,16),  # line 2183
    '[5/6, 8/35, 539/2, 3/343, 14/11]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-1],[-1,2,-3],[7,-2,-38],[1,0,-12],[1,0,-15],[1,0,-27],[1,0,-48],[1,0,-61],[1,0,-74],[1,0,-77]],[1,1],None,400,False,769),  # line 2184
    '[5/6, 8/35, 539/2, 3/49, 98/11]': ('ndx',[1,2,4],{},[[1,0,0,-1],[0,1,0,-5],[0,0,1,-22],[-1,0,1,-47],[1,0,0,-5],[1,0,0,-8],[1,0,0,-12],[1,0,0,-15],[1,0,0,-28],[1,0,0,-29],[1,0,0,-30],[1,0,0,-31],[1,0,0,-32],[1,0,0,-33],[1,0,0,-34]],[1,1,1],None,400,False,327),  # line 2185
    '[5/6, 8/385, 77/2, 3/7, 196/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-1],[-1,1,-3],[7,-3,-59],[1,0,-32],[1,0,-33],[1,0,-34],[1,0,-35],[1,0,-36],[1,0,-37],[1,0,-38],[1,0,-39]],[1,1],None,400,False,339),  # line 2186
    '[5/6, 88/245, 3773/2, 3/11, 5/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,2,-1],[2,-3,-5],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,True,51),  # line 2187
    '[5/6, 88/245, 847/2, 3/11, 4/3]': ('mul',2,[[],[],[],['5/3','4/3'],['-1/3','28/3']],25,3,[[625,7394],[15625,184894]]),  # line 2188
    '[5/6, 99/245, 3773/3, 2/11, 15/2]': ('ndx',[3,4],{},[[1,0,-7],[0,1,-4],[-2,3,0],[1,-1,-11],[-1,2,-24],[-1,2,-26],[-1,2,-28]],[1,1],None,400,False,155),  # line 2190
    '[5/6, 99/245, 3773/3, 2/11, 9/2]': ('ndx',[3,4],{},[[1,0,-6],[0,1,-2],[-1,3,-2],[1,-1,-14],[0,1,-10],[-1,2,-30]],[1,1],None,400,False,251),  # line 2191
    '[5/6, 99/35, 176/5, 7/11, 55/2]': ('ndx',[0,4],{},[[1,0,-4],[0,1,-2],[-1,2,-2],[2,-3,-10]],[1,1],None,400,True,46),  # line 2192
    '[5/6, 99/35, 7/3, 2/11, 5/7, 15/2]': ('nd',[4,1],{},[[1,0,-4],[0,1,-4],[1,-1,-9],[-1,2,-2]],[4,2],'11',3000,True,1447),  # line 2193
    '[5/6, 99/35, 7/3, 2/11, 5/7, 45/2]': ('ndz',[3,4],{},[[-1,1,1],[2,-1,-2],[1,0,-3],[0,1,-2]],[3,1],'1',1000,'all',14),  # line 2194
    '[5/9, 1/35, 242/7, 49/143, 3/11, 91/2]': ('nd',[0,4],{'1': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 2203
    '[5/9, 1/35, 49/143, 242/7, 3/11, 91/2]': ('nd',[0,4],{'1': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 2204
    '[5/9, 1/77, 147/65, 10/7, 11/5, 91/2]': ('ndxz',[0,1,3],{},[[1,0,0,-153],[0,1,0,-1],[0,0,1,-177],[1,-38,0,0],[0,-44,1,0],[-1,0,1,0],[5,0,-4,0]],[1,12,1],'6',300,True,1893),  # line 2205
    '[5/9, 147/55, 1/91, 10/7, 13/5, 77/2]': ('nd',[3,4,0],{'1': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,-1,-3],[0,0,1,-8],[0,0,1,-16],[0,4,-1,-63]],[1,1,1],None,1000,False,368),  # line 2206
    '[5/9, 49/143, 1/35, 242/7, 3/11, 91/2]': ('nd',[0,4],{'1': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 2209
    '[50/63, 7/55, 54/5, 11/2, 25/11]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-6],[-1,1,-14],[3,-1,-2]],[1,1],None,400,True,28),  # line 2211
    '[50/63, 7/55, 54/5, 11/2, 35/11]': ('ndx',[0,1],{},[[1,0,-4],[0,1,-7],[-1,1,-11],[3,-2,0]],[1,1],None,400,True,66),  # line 2212
    '[56/15, 21/22, 1105/2, 11/7, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-1],[0,0,1,0,-3],[0,0,0,1,-3],[-1,2,0,0,-3],[1,-1,0,0,-4],[0,0,-1,1,0],[0,0,1,-1,0],[0,2,-1,0,1],[0,-2,1,0,-1]],[1,1,1,1],None,400,False,36),  # line 2213
    '[56/15, 27/49, 1/6, 55/2, 9/11]': ('nd',[0,3,4],{},[[1,0,0,-3],[0,1,0,-1],[0,0,1,-1],[1,-2,0,-1],[0,1,0,-8],[0,1,0,-9]],[1,1,1],None,400,False,506),  # line 2214
    '[56/45, 21/22, 125/2, 11/7, 3/5]': ('nd',[0,2,3,4],{},[[1,0,0,0,-3],[0,1,0,0,-6],[0,0,1,0,-1],[0,0,0,1,-1],[0,1,0,-1,-15],[-3,0,1,0,8],[3,0,-1,0,-8],[1,0,0,0,-5],[0,0,1,1,-9]],[1,1,1,1],None,400,False,59),  # line 2215
    '[56/45, 21/22, 25/2, 11/7, 6/5]': ('ndxz',[1,2,4],{'0': 1},[[1,0,0,-1],[0,1,0,-139],[0,0,1,-104],[-34,1,0,0],[-26,0,1,0],[0,-7,10,0],[0,1,-1,0]],[12,1,1],'6',300,True,743),  # line 2216
    '[56/45, 21/22, 25/2, 11/7, 9/5]': ('nd',[0,2,3,4],{},[[1,0,0,0,-3],[0,1,0,0,-4],[0,0,1,0,-1],[0,0,0,1,-1],[-3,0,1,0,12],[2,1,-1,-1,-14]],[1,1,1,1],None,1000,False,51),  # line 2217
    '[56/45, 5/22, 189/2, 11/7, 5/3]': ('ndx',[1,3],{},[[1,0,-3],[0,1,-1],[-1,2,-1],[2,-3,-5]],[1,1],None,400,True,11),  # line 2218
    '[567/50, 35/33, 2/3, 11/7, 15/2]': ('ndxz',[0,2,4],{'1': 1},[[1,0,0,-115],[0,1,0,-1],[0,0,1,-104],[1,-28,0,0],[0,-26,1,0],[-5,0,6,0],[1,0,-1,0]],[1,12,1],'6',300,True,846),  # line 2219
    '[63/10, 1/66, 14/3, 121/2, 5/7, 3/11]': ('nd',[1,3],{},[[1,0,-4],[0,1,-6],[7,-3,18],[-2,1,-13]],[1,1],None,1000,False,1087),  # line 2236
    '[63/10, 2/33, 102487/2, 5/7, 10/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-5,3,-13],[2,-1,0]],[1,1],None,400,True,43),  # line 2243
    '[63/10, 2/33, 102487/2, 5/7, 14/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-5,3,-10],[2,-1,0]],[1,1],None,400,True,30),  # line 2244
    '[63/10, 2/33, 102487/2, 5/7, 3/121]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-4],[-5,3,-7],[2,-1,0]],[1,1],None,400,True,27),  # line 2245
    '[63/10, 2431/2, 28/33, 5/7, 3/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-1,2,0,0,-4],[1,-1,0,0,0],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,2],[-2,1,1,0,-2],[1,0,0,0,-6],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,48),  # line 2246
    '[63/10, 2431/2, 28/429, 5/7, 3/17]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-1,2,0,0,-4],[1,-1,0,0,0],[0,-1,1,0,0],[0,1,-1,0,0],[2,-1,0,-1,2],[-2,1,0,1,-2],[1,0,0,0,-6],[1,0,0,0,-8],[1,0,0,0,-9]],[1,1,1,1],None,400,False,48),  # line 2247
    '[63/10, 25/231, 14/3, 11/2, 12/11]': ('nd',[0,3],{},[[1,0,-979],[0,1,-10041],[-1,1,-21813]],[8,1],'a8',1000,False,43694),  # line 2248
    '[63/10, 28/33, 2431/2, 5/7, 3/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-1,2,0,0,-4],[1,-1,0,0,0],[0,0,-1,1,0],[0,0,1,-1,0],[2,-1,-1,0,2],[-2,1,1,0,-2],[1,0,0,0,-6],[1,0,0,0,-8],[-1,2,0,0,-8],[1,0,0,0,-9],[-1,2,0,0,-9]],[1,1,1,1],None,400,False,3830),  # line 2249
    '[63/10, 28/363, 1331/2, 5/7, 3/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-6],[-5,2,-8],[7,-2,0],[1,0,-6],[1,0,-8],[4,-1,-18],[4,-1,-23],[4,-1,-25]],[1,1],None,400,False,143),  # line 2250
    '[63/10, 4/363, 9317/2, 5/7, 2/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-5,3,-5],[2,-1,0],[1,0,-8],[-1,1,-10],[4,-1,-24],[4,-1,-27]],[1,1],None,400,False,47),  # line 2267
    '[63/10, 4/363, 9317/2, 5/7, 3/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-3,2,-4],[2,-1,-1],[1,0,-8],[-1,1,-10],[4,-1,-25],[-1,1,-11]],[1,1],None,400,False,58),  # line 2268
    '[63/10, 4/363, 9317/2, 5/7, 3/5]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-3],[-5,3,-11],[7,-2,0],[1,0,-4],[1,0,-7],[1,0,-10],[4,-1,-30]],[1,1],None,400,False,58),  # line 2269
    '[63/10, 5/231, 112/3, 11/2, 3/11]': ('nd',[2,4],{},[[1,0,-1],[0,1,-2],[-1,3,-7],[1,-1,-1],[0,1,-5],[1,1,-13],[1,1,-24],[0,1,-10],[1,1,-28],[0,1,-25]],[1,1],None,400,False,537),  # line 2270
    '[63/10, 5/231, 56/3, 11/2, 9/11]': ('nd',[0,3],{},[[1,0,-6],[0,1,-2],[-1,2,0],[2,-3,-10],[2,-1,-36],[2,-3,-18],[2,-3,-40]],[1,1],None,400,False,364),  # line 2271
    '[63/10, 5/2541, 4/3, 11/2, 45/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-7],[-3,1,-8],[5,-1,-6],[1,0,-8],[1,0,-9]],[1,1],None,400,True,248),  # line 2272
    '[63/20, 35/33, 8/3, 11/7, 15/2]': ('ndx',[0,3],{},[[1,0,-7],[0,1,-1],[1,-1,-16],[0,1,-4]],[1,1],None,400,True,31),  # line 2281
    '[63/20, 35/33, 8/3, 11/7, 21/2]': ('ndx',[0,3],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,22),  # line 2282
    '[63/20, 5/33, 56/3, 11/7, 15/2]': ('ndx',[0,3],{},[[1,0,-7],[0,1,-4],[-2,3,-14],[1,-1,-7],[-1,2,-24],[-1,2,-26],[-1,2,-28]],[1,1],None,400,False,196),  # line 2283
    '[63/20, 5/33, 56/3, 11/7, 3/2]': ('ndx',[0,3],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,22),  # line 2284
    '[63/20, 5/33, 56/3, 11/7, 9/2]': ('ndx',[0,3],{},[[1,0,-6],[0,1,-2],[-1,2,-4],[1,-1,-10]],[1,1],None,400,True,41),  # line 2285
    '[7/15, 1/21, 132/7, 3/121, 65/2, 3/13]': ('nd',[0,4,5],{'3': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,-1,0,-3],[0,1,0,-8],[0,1,0,-16],[4,-1,0,-63]],[1,1,1],None,1000,False,249),  # line 2353
    '[7/15, 1/42, 1089/7, 2/3, 5/11, 15/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2609),  # line 2390
    '[7/15, 1/42, 1089/7, 2/3, 5/11, 33/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-1],[-2,1,-9],[1,0,-10],[3,-1,-30],[3,-1,-34]],[1,1],None,3000,False,2622),  # line 2391
    '[7/15, 1/42, 1089/7, 2/3, 5/11, 49/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-4],[-2,1,-6],[1,0,-10],[3,-1,-30],[3,-1,-34],[3,-1,-37]],[1,1],None,3000,False,4416),  # line 2392
    '[7/15, 1/42, 1089/7, 2/3, 5/11, 7/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2598),  # line 2393
    '[7/15, 1/42, 1089/7, 2/3, 5/11, 77/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-3],[-2,1,-3],[0,1,-9],[0,1,-25],[3,-1,-35],[-21,11,-87]],[2,2],'2',1000,False,1593),  # line 2394
    '[7/15, 1/42, 1089/7, 2/9, 5/11, 7/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-3,1,-4],[0,1,-9],[1,0,-10],[-3,1,-13],[-3,1,-14],[-3,1,-15]],[1,4],'6',400,False,326),  # line 2395
    '[7/15, 1/42, 99/7, 2/3, 25/11, 15/2]': ('nd',[0,2],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2474),  # line 2397
    '[7/15, 1/42, 99/7, 2/3, 25/11, 49/2]': ('ndx',[0,4],{},[[1,0,-7],[0,1,-162],[-1,1,0],[31,-1,0],[3,-2,-30],[3,-2,-34],[3,-2,-37]],[1,1],None,300,False,3793),  # line 2398
    '[7/15, 1/42, 99/7, 2/3, 25/11, 7/2]': ('nd',[0,2],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,2463),  # line 2399
    '[7/15, 1/42, 99/7, 2/3, 25/11, 77/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-2],[-1,1,-10],[1,0,-10],[3,-2,-24],[3,-2,-32],[3,-2,-35]],[2,2],'d',400,False,1844),  # line 2400
    '[7/15, 1/42, 99/7, 2/9, 25/11, 7/2]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[-1,1,1],[1,0,-8],[1,0,-20],[-3,4,-32],[1,0,-21],[1,0,-23],[-3,4,-36]],[1,1],None,400,False,254),  # line 2401
    '[7/15, 1/42, 99/7, 22/3, 5/11, 15/2]': ('ndz',[0,4],{},[[1,0,-2],[-4,1,3]],[4,4],'200',1000,'all',19),  # line 2402
    '[7/15, 1/42, 99/7, 22/3, 5/11, 49/2]': ('ndxz',[0,4],{},[[-4,1,-2],[1,0,-1],[0,1,-6]],[4,4],'4040',2000,'all',29),  # line 2403
    '[7/15, 1/42, 99/7, 22/3, 5/11, 7/2]': ('ndz',[0,4],{},[[1,0,-2],[-4,1,3]],[4,4],'200',576,'all',17),  # line 2404
    '[7/15, 1/49, 66/7, 3/1331, 25/2, 7/5]': ('nd',[0,4],{},[[1,0,-2],[0,1,-1],[0,-1,2],[1,0,-4]],[1,1],None,400,True,61),  # line 2410
    '[7/15, 1/84, 1089/7, 2/3, 5/11, 7/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-2],[-5,3,-1],[6,-1,-2],[0,1,-4],[0,1,-8],[1,0,-20]],[1,1],None,400,True,290),  # line 2423
    '[7/15, 1/84, 99/7, 2/3, 25/11, 7/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-1],[-1,1,2],[0,1,-4],[1,0,-20]],[1,1],None,400,True,253),  # line 2424
    '[7/15, 1/84, 99/7, 22/3, 5/11, 3/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[0,1,-9],[1,0,-20],[-3,2,-30],[-3,2,-35]],[1,4],'8',400,False,538),  # line 2425
    '[7/15, 1/84, 99/7, 22/3, 5/11, 7/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-3],[-2,1,-1],[0,1,-9],[1,0,-20],[-3,2,-26],[-3,2,-31],[-3,2,-33]],[1,4],'2',400,False,618),  # line 2426
    '[7/15, 1089/28, 8/3, 5/11, 21/2]': ('ndx',[0,4],{},[[1,0,-7],[0,1,-2],[-1,2,-1],[1,-1,-13]],[1,1],None,400,True,47),  # line 2433
    '[7/15, 11/3, 18/77, 5/2, 15/11, 21/5]': ('nd',[0,4],{},[[1,0,-4],[0,1,-4],[1,-1,-9],[-1,2,-2]],[2,2],'1',3000,True,1489),  # line 2441
    '[7/15, 11/3, 18/77, 5/2, 7/11, 21/5]': ('nd',[0,4],{},[[1,0,-4],[0,1,-4],[1,-1,-9],[-1,2,-2]],[2,2],'1',3000,True,1464),  # line 2442
    '[7/15, 11/3, 18/77, 5/2, 7/11, 63/5]': ('nd',[0,4],{},[[1,0,-4],[0,1,-3],[1,-1,-9],[-1,2,-2]],[6,3],'21b0d',3000,True,964),  # line 2443
    '[7/15, 11/42, 1089/7, 2/3, 5/11, 7/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,1000,False,588),  # line 2444
    '[7/15, 18/77, 11/3, 5/2, 7/11, 21/5]': ('nd',[0,1],{},[[1,0,-4],[0,1,-4],[1,-1,-9],[-1,2,-2]],[4,2],'11',3000,True,1448),  # line 2458
    '[7/15, 18/77, 11/3, 5/2, 7/11, 63/5]': ('ndz',[0,4],{},[[1,0,-1],[-1,2,-2],[1,-1,1]],[1,12],'1',1000,'all',304),  # line 2459
    '[7/15, 18/847, 2662/3, 5/2, 21/5]': ('ndx',[0,4],{},[[1,0,-4],[0,1,-7],[-1,1,-11],[3,-2,0],[2,-1,-24],[2,-1,-28]],[1,1],None,400,False,156),  # line 2460
    '[7/15, 18/847, 2662/3, 5/2, 9/5]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-6],[-1,1,-14],[3,-1,-2],[1,0,-10],[2,-1,-30]],[1,1],None,400,False,252),  # line 2461
    '[7/15, 2/3, 99/14, 5/11, 33/2, 21/5]': ('ndxz',[0,4],{},[[1,0,-511],[0,1,-970],[-9,10,0],[2,-1,0]],[2,4],'b0',4,False,1888200),  # line 2462
    '[7/15, 22/3, 27/154, 5/11, 1089/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[-1,3,-48],[1,-1,-8],[0,1,-32],[0,1,-33],[0,1,-34],[0,1,-35],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39]],[1,1],None,400,False,313),  # line 2463
    '[7/15, 22/3, 3/539, 12005/2, 121/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-4],[-2,1,-7],[1,0,-8],[-3,2,-40],[1,0,-9],[-3,2,-42],[-3,2,-43]],[1,1],None,400,False,234),  # line 2464
    '[7/15, 22/3, 81/1925, 5/2, 9/5]': ('add',2,[['4','3'],[],[],[],['8','12','4']],2,[[14,3660],[15,4160],[16,4692],[17,5256]]),  # line 2465
    '[7/15, 22/3, 81/77, 5/121, 363/2]': ('nd',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-3],[1,0,-1,-4],[0,0,1,-8],[0,0,1,-10]],[1,1,1],None,400,True,54),  # line 2466
    '[7/15, 220/21, 1/7, 5/121, 9/2, 7/3]': ('ndx',[0,4],{'2': 1},[[1,0,-57],[0,1,-1],[0,100,0],[11,-10,0],[0,1,-12],[0,1,-48],[0,1,-49],[0,1,-50],[0,1,-51],[0,1,-52],[0,1,-53],[0,1,-54],[0,1,-55]],[1,1],None,300,False,767),  # line 2467
    '[7/15, 220/21, 5/121, 1/7, 9/2, 7/3]': ('ndx',[1,4],{},[[1,0,-156],[0,1,0],[0,-1,1],[1,-78,0]],[1,1],None,300,False,611),  # line 2468
    '[7/15, 27/154, 22/3, 5/11, 1089/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[-1,3,-48],[1,-1,-8],[0,1,-32],[0,1,-33],[0,1,-34],[0,1,-35],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39]],[1,1],None,400,False,313),  # line 2473
    '[7/15, 27/77, 242/3, 5/121, 363/2]': ('ndx',[0,2,3],{},[[1,0,0,-31],[0,1,0,-2],[0,0,1,-5],[1,-1,0,-47],[0,1,0,-5],[0,1,0,-8],[0,1,0,-12],[0,1,0,-15],[0,1,0,-28],[0,1,0,-29],[0,1,0,-30],[0,1,0,-31],[0,1,0,-32],[0,1,0,-33],[0,1,0,-34]],[1,1,1],None,400,False,399),  # line 2475
    '[7/15, 3/1078, 16/3, 55/2, 9/5]': ('add',2,[[],[],['1','21'],[],['1','18','28']],4,[[19,40604],[20,44981],[21,49582],[22,54407]]),  # line 2476
    '[7/15, 3/154, 16/3, 55/2, 6/5]': ('add',2,[[],[],['1','6'],[],['1','7','2']],4,[[19,6613],[20,7321],[21,8065],[22,8845]]),  # line 2477
    '[7/15, 3/154, 16/3, 605/2, 6/5]': ('add',2,[[],[],['1','6'],[],['2','13','8']],4,[[19,6613],[20,7321],[21,8065],[22,8845]]),  # line 2478
    '[7/15, 3/154, 16/33, 55/2, 6/5]': ('add',2,[['5','6'],[],[],[],[]],10,[[39,28083],[40,29523],[41,30999],[42,32511]]),  # line 2479
    '[7/15, 3/539, 22/3, 12005/2, 121/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-4],[-2,1,-7],[1,0,-8],[1,0,-9]],[1,1],None,400,True,234),  # line 2480
    '[7/15, 4/3, 81/35, 5/8, 9/2]': ('add',4,[['4','15'],[],[],[]],1,[[7,2950],[8,3819],[9,4800],[10,5893]]),  # line 2484
    '[7/15, 81/1925, 22/3, 5/2, 9/5]': ('add',2,[['4','3'],[],[],[],['8','12','4']],2,[[14,3660],[15,4160],[16,4692],[17,5256]]),  # line 2492
    '[7/15, 81/35, 4/3, 5/8, 9/2]': ('add',4,[['4','15'],[],[],[]],1,[[7,2950],[8,3819],[9,4800],[10,5893]]),  # line 2493
    '[7/15, 81/77, 22/3, 5/121, 363/2]': ('nd',[0,1,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[1,0,-1,-4],[0,0,1,-8],[0,0,1,-10]],[1,1,1],None,400,True,54),  # line 2494
    '[7/15, 9/143, 11/3, 50/11, 13/7, 33/2]': ('nd',[0,2,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[2,-1,0,1],[0,1,0,-5],[0,1,0,-8],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,1000,False,80),  # line 2495
    '[7/15, 9/539, 2662/3, 5/11, 99/2]': ('nd',[0,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[3,-1,0,-1],[0,1,0,-4],[0,1,0,-6],[0,1,0,-8],[0,1,0,-10],[0,1,0,-16],[0,1,2,-60],[0,1,2,-62],[0,1,0,-17],[0,1,0,-18],[0,1,0,-19]],[1,1,1],None,400,False,579),  # line 2496
    '[7/15, 9/539, 2662/3, 5/121, 9/2]': ('nd',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,0,1,-24],[0,0,1,-25],[0,0,1,-26],[0,0,1,-27],[0,0,1,-28],[0,0,1,-29]],[1,1,1],None,400,False,382),  # line 2497
    '[7/15, 99/14, 2/3, 5/11, 33/2, 21/5]': ('ndxz',[4,1],{},[[1,0,-4],[0,1,-4],[1,-1,-9],[-1,2,-2]],[4,2],'aa',3000,True,1195),  # line 2502
    '[7/270, 9/2, 88/21, 5/11, 7/3]': ('add',1,[[],['6','4'],[],[],['1','1']],15,[[74,14251],[75,14631],[76,15016],[77,15406]]),  # line 2508
    '[7/30, 1/847, 16/21, 33/2, 35/11]': ('add',1,[[],['2','3','1'],[],[],['1','6']],10,[[49,17011],[50,17708],[51,18419],[52,19144]]),  # line 2509
    '[7/30, 1/847, 8/21, 99/2, 35/3]': ('add',2,[[],['14','15','5'],[],[],['6','10']],12,[[59,106600],[60,110206],[61,113872],[62,117598]]),  # line 2510
    '[7/30, 11/2, 80/21, 3/11, 20/3]': ('ndcv',[1,3],{},[[1,0,-1],[0,1,-4],[1,0,-10],[0,1,-7],[0,1,-15]],[1,1],None,400,False,20814),  # line 2511
    '[7/30, 11/2, 80/21, 3/11, 70/3]': ('ndcv',[1,3,4],{},[[1,0,0,-1],[0,1,0,-8],[0,0,1,-1],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,False,685),  # line 2512
    '[7/30, 11/3, 405/14, 2/11, 105/2]': ('ndcv',[0,3,4],{},[[1,0,0,-1],[0,1,0,-8],[0,0,1,-1],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,False,683),  # line 2513
    '[7/30, 11/3, 405/14, 2/11, 45/2]': ('ndcv',[0,3],{},[[1,0,-1],[0,1,-4],[1,0,-10],[0,1,-7],[0,1,-15]],[1,1],None,400,False,20812),  # line 2514
    '[7/30, 12/77, 297/2, 5/9, 2/5]': ('ndx',[0,1],{},[[1,0,-10],[0,1,-7],[-7,2,-8],[4,-1,-1],[1,0,-12],[1,0,-15],[-5,3,-100]],[1,1],None,400,False,468),  # line 2515
    '[7/30, 12/77, 3993/2, 5/11, 4/5]': ('nd',[0,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,1,-58],[0,1,0,-16],[0,1,0,-20]],[1,1,1],None,400,False,1222),  # line 2516
    '[7/30, 12/77, 43923/2, 5/11, 2/5]': ('ndx',[2,3],{},[[1,0,-2],[0,1,-1],[1,0,-5],[1,0,-25],[1,5,-100],[1,0,-26],[1,5,-104]],[1,1],None,144,False,535),  # line 2517
    '[7/30, 12/77, 99/2, 5/3, 44/5]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-16],[1,0,-6],[1,0,-9],[1,0,-12],[1,0,-15],[1,0,-30]],[1,1],None,400,False,745),  # line 2518
    '[7/30, 12/77, 99/2, 5/3, 66/5]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-9],[1,0,-7],[1,0,-11],[1,0,-20]],[1,1],None,400,False,564),  # line 2519
    '[7/30, 121/2, 6/77, 25/11, 24/5]': ('ndz',[2,3],{'0': 1,'4': 2},[[0,1,-1],[-1,0,8],[1,0,-2]],[12,1],'124',1000,'all',6),  # line 2520
    '[7/30, 121/2, 6/77, 25/11, 308/5]': ('ndxz',[2,3],{},[[1,0,-1],[0,1,-189],[-9,1,0]],[3,12],'eef000',300,True,2080),  # line 2521
    '[7/30, 121/3, 15/77, 4/11, 135/2]': ('ndz',[0,3],{'1': 1,'4': 2},[[0,1,-1],[-1,0,8],[1,0,-2]],[12,1],'124',1000,'all',21),  # line 2522
    '[7/30, 121/3, 15/77, 4/11, 693/2]': ('ndxz',[0,3],{},[[1,0,-1],[0,1,-186],[-9,1,0]],[3,9],'3de00',300,True,2043),  # line 2523
    '[7/30, 121/3, 18/77, 10/121, 9/2]': ('ndcv',[0,4],{},[[1,0,-1],[0,1,-6],[-2,1,-4],[3,-1,-1],[0,1,-21],[0,1,-23]],[1,1],None,400,False,98),  # line 2524
    '[7/30, 1331/2, 40/63, 3/11, 7/3]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-9],[1,0,-3],[1,0,-5],[0,1,-12],[1,0,-8],[-5,2,-30],[-5,2,-32],[-5,2,-34],[1,0,-9]],[1,1],None,400,False,10125),  # line 2525
    '[7/30, 14641/3, 9/35, 10/11, 15/2]': ('ndx',[0,2],{},[[1,0,-100],[0,1,-3],[0,1,-5],[0,1,-12],[3,-2,-27]],[18,3],'8',1000,False,62192),  # line 2526
    '[7/30, 15/77, 121/3, 4/11, 135/2]': ('ndxz',[0,3],{},[[1,0,-1],[0,1,-187],[-23,1,0]],[3,9],'3de00',300,True,1869),  # line 2527
    '[7/30, 15/77, 121/3, 4/11, 693/2]': ('ndz',[0,3],{},[[1,0,-1],[0,1,-1],[-1,0,10]],[3,9],'3de00',1000,'all',20),  # line 2528
    '[7/30, 16/21, 33/2, 5/121, 14/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[-1,1,-6],[4,-3,-2],[0,1,-40],[0,1,-41]],[1,1],None,1000,False,167),  # line 2529
    '[7/30, 16/21, 33/2, 5/121, 4/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[-1,1,-3],[3,-2,-2],[0,1,-12],[0,1,-20],[2,-1,-14],[0,1,-40],[8,-5,-40],[0,1,-41],[0,1,-42],[0,1,-43],[8,-5,-42]],[1,1],None,1000,False,211),  # line 2530
    '[7/30, 16/21, 363/2, 15/11, 2/3]': ('ndcv',[1,2],{},[[1,0,-3],[0,1,-2],[-2,3,-4],[1,-1,-5],[0,1,-20],[4,-5,-8],[4,-5,-20],[4,-5,-22]],[1,2],'1',400,False,187),  # line 2531
    '[7/30, 16/21, 605/2, 3/11, 35/3]': ('ndcv',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-13],[0,-1,1,-12]],[1,1,1],None,1000,False,115),  # line 2532
    '[7/30, 16/21, 99/2, 5/11, 35/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[3,-5,-13],[0,1,-4],[0,1,-7],[-1,2,0],[0,1,-16],[-1,2,-4]],[1,1],None,3000,False,89),  # line 2533
    '[7/30, 16/21, 99/2, 5/11, 77/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[-1,2,-4],[2,-3,0],[1,-1,-6],[0,1,-16],[-1,2,-6],[0,1,-17],[4,-5,-23]],[1,4],'3',400,False,67),  # line 2534
    '[7/30, 16/63, 55/2, 3/11, 4/3]': ('add',2,[[],[],['1','4','4'],[],['1','3']],2,[[15,3661],[16,4161],[17,4693],[18,5257]]),  # line 2535
    '[7/30, 16/77, 33/2, 5/11, 44/3]': ('ndcv',[0,1],{},[[1,0,-13],[0,1,-2],[-1,3,8],[1,0,-24],[1,0,-25],[1,0,-26],[1,0,-27],[1,0,-28],[1,0,-29]],[1,1],None,400,False,95),  # line 2536
    '[7/30, 16/77, 33/2, 5/11, 77/3]': ('nd',[0,1],{},[[1,0,-20],[0,1,-4],[-1,3,3]],[1,1],None,400,False,151),  # line 2537
    '[7/30, 16/77, 33/2, 5/11, 847/3]': ('ndcv',[0,1],{},[[1,0,-19],[0,1,-4],[-1,3,-27],[1,-2,-29]],[1,1],None,1000,False,412),  # line 2538
    '[7/30, 162/35, 22/3, 5/11, 9/2]': ('ndcv',[0,2,4],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[1,0,-1,-4],[1,-2,0,2],[0,0,1,-4]],[1,1,1],None,400,True,45),  # line 2539
    '[7/30, 176/21, 3/2, 5/11, 154/3]': ('add',1,[[],['4','4','1'],[],[],['2','2']],10,[[49,15051],[50,15658],[51,16277],[52,16908]]),  # line 2540
    '[7/30, 176/21, 39/2, 5/11, 35/13]': ('add',1,[[],['5','5','1'],[],[],['2','2'],['7','9','3']],10,[[49,15251],[50,15862],[51,16485],[52,17120]]),  # line 2541
    '[7/30, 176/21, 99/2, 5/11, 7/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[-2,3,-3],[1,-1,-3],[4,-5,-23]],[2,4],'2',400,False,325),  # line 2542
    '[7/30, 18/77, 121/3, 10/121, 9/2]': ('ndcv',[0,4],{},[[1,0,-1],[0,1,-6],[-2,1,-4],[3,-1,-1],[0,1,-21],[0,1,-23]],[1,1],None,400,False,98),  # line 2543
    '[7/30, 18/77, 44/3, 5/2, 99/5]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-15],[1,0,-6],[1,0,-9],[1,0,-12],[1,0,-15],[1,0,-30]],[1,1],None,400,False,545),  # line 2544
    '[7/30, 2/231, 14641/2, 15/11, 4/5]': ('ndx',[1,2],{},[[1,0,-4],[0,1,-4],[-1,1,-4],[3,-2,-19],[3,-2,-46],[3,-2,-56]],[1,6],'6',400,False,4856),  # line 2545
    '[7/30, 20/231, 121/2, 3/11, 28/3]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-7],[1,0,-4],[1,0,-6],[1,0,-8],[-3,2,-40],[1,0,-9],[0,1,-34],[0,1,-35],[0,1,-36]],[1,1],None,400,False,554),  # line 2546
    '[7/30, 22/3, 162/35, 5/11, 9/2]': ('ndcv',[0,2,4],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[1,0,-1,-4],[1,-2,0,2],[0,0,1,-4]],[1,1,1],None,400,True,45),  # line 2547
    '[7/30, 22/3, 27/175, 25/11, 9/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-2],[5,-7,1],[0,1,-4],[0,1,-10],[0,1,-11],[0,1,-12]],[1,1],None,1000,False,122),  # line 2548
    '[7/30, 22/3, 27/77, 5/11, 1089/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[-1,3,-30],[2,-3,0],[0,1,-32],[0,1,-33],[0,1,-34],[0,1,-35],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39]],[1,1],None,400,False,419),  # line 2549
    '[7/30, 22/3, 27/77, 5/11, 81/2]': ('ndx',[0,3],{},[[1,0,-1],[0,1,-8]],[1,6],'4',400,False,48),  # line 2550
    '[7/30, 22/3, 81/77, 5/11, 539/2]': ('ndcv',[0,1,4],{},[[1,0,0,-571],[0,1,0,-1],[0,0,1,-423],[1,-71,0,0],[0,-52,1,0],[-2,0,3,0],[3,0,-4,0],[0,1,0,-4]],[1,1,1],None,16,True,1318),  # line 2551
    '[7/30, 22/3, 81/77, 5/11, 847/2]': ('nd',[0,4],{},[[1,0,-4],[0,1,-5],[-2,3,-28],[7,-10,43]],[1,1],None,1000,False,420),  # line 2552
    '[7/30, 22/3, 81/77, 5/11, 99/2]': ('ndx',[0,4],{},[[1,0,-219],[0,1,-159],[-2,3,0],[3,-4,0]],[1,1],None,300,False,654),  # line 2553
    '[7/30, 22/3, 9/77, 5/11, 405/2]': ('ndcv',[0,2],{'1': 4},[[1,0,-3],[0,1,-5],[-1,3,-18],[2,-3,-3],[0,1,-15],[3,-5,3]],[1,1],None,1000,False,229),  # line 2554
    '[7/30, 242/3, 27/175, 5/11, 9/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[-1,1,-11],[3,-2,-3]],[1,1],None,1000,False,152),  # line 2555
    '[7/30, 243/35, 55/3, 2/11, 35/2]': ('ndcv',[2,4],{},[[1,0,-5],[0,1,-5],[-1,1,-3],[3,-2,-12],[1,0,-24],[1,0,-25],[1,0,-26],[1,0,-27],[1,0,-28],[1,0,-29]],[1,1],None,400,True,191),  # line 2556
    '[7/30, 27/14, 44/3, 25/121, 3/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-1],[-1,2,-2],[2,-3,-1],[0,1,-8],[0,1,-15],[0,1,-16]],[1,1],None,400,True,82),  # line 2557
    '[7/30, 27/14, 44/3, 5/11, 231/2]': ('ndcv',[0,4],{},[[1,0,-7],[0,1,-5],[-1,2,-11],[2,-3,-13]],[1,1],None,400,False,118),  # line 2558
    '[7/30, 27/14, 44/3, 5/11, 45/2]': ('ndcv',[0,4],{},[[1,0,-6],[0,1,-4],[-1,2,-8],[2,-3,-12]],[1,1],None,400,False,101),  # line 2559
    '[7/30, 27/77, 22/3, 5/11, 1089/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[-1,3,-30],[2,-3,0],[0,1,-32],[0,1,-33],[0,1,-34],[0,1,-35],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39]],[1,1],None,400,False,419),  # line 2560
    '[7/30, 27/77, 22/3, 5/11, 81/2]': ('ndcv',[0,1],{},[[1,0,-3],[0,1,-8],[-4,3,-44],[2,-1,0]],[1,1],None,400,False,171),  # line 2561
    '[7/30, 297/14, 4/3, 25/11, 21/2]': ('ndcv',[0,4],{},[[1,0,-7],[0,1,-1],[1,-4,-7],[0,1,-4],[0,2,-15]],[1,1],None,400,False,123),  # line 2562
    '[7/30, 297/2, 12/77, 5/9, 2/5]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-14],[1,0,-5],[1,0,-7],[1,0,-10]],[1,1],None,400,False,632),  # line 2563
    '[7/30, 297/5, 75/77, 2/9, 5/2]': ('ndcv',[0,3],{},[[1,0,-1],[0,1,-14]],[1,1],None,400,False,408),  # line 2564
    '[7/30, 3/77, 16/35, 55/2, 14/11]': ('add',2,[['5','6'],[],[],[],[]],10,[[39,28083],[40,29523],[41,30999],[42,32511]]),  # line 2565
    '[7/30, 32/21, 33/2, 5/11, 21/5]': ('ndx',[2,3],{},[[1,0,-4],[0,1,-15],[1,0,-7],[1,0,-10]],[1,1],None,400,False,373),  # line 2566
    '[7/30, 3267/14, 4/3, 5/11, 21/2]': ('ndcv',[0,4],{},[[1,0,-7],[0,1,-2],[-1,3,-7],[1,-2,-7],[0,1,-15]],[1,1],None,400,False,134),  # line 2567
    '[7/30, 33/2, 16/175, 5/11, 4/5]': ('add',2,[[],['1','4','4'],[],[],['1','3']],2,[[15,3661],[16,4161],[17,4693],[18,5257]]),  # line 2568
    '[7/30, 33/2, 16/77, 5/11, 44/3]': ('ndcv',[0,1,3],{},[[1,0,0,-1],[0,1,0,-3],[0,0,1,-28],[-1,1,0,-15],[1,0,0,-4]],[6,1,1],'16',1000,False,1449),  # line 2569
    '[7/30, 33/2, 16/77, 5/11, 77/3]': ('ndcv',[1,3],{},[[1,0,-4],[0,1,-60]],[1,1],None,400,False,361),  # line 2570
    '[7/30, 33/2, 16/77, 5/11, 847/3]': ('nd',[1,4],{},[[1,0,-1],[0,1,-1],[-2,3,-19],[5,-7,21]],[1,1],None,1000,False,193),  # line 2571
    '[7/30, 33/2, 32/21, 5/11, 21/5]': ('ndx',[2,3],{},[[1,0,-4],[0,1,-15],[1,0,-7],[1,0,-10]],[1,1],None,400,False,373),  # line 2572
    '[7/30, 33/2, 32/77, 5/11, 77/3]': ('ndcvz',[0,1,4],{},[[1,0,0,-1],[0,1,0,-688],[0,0,1,-546],[-68,1,0,0],[-54,0,1,0],[0,-3,4,0],[0,4,-5,0],[1,0,0,-4]],[1,1,1],None,1000,True,1522),  # line 2573
    '[7/30, 33/2, 4/77, 5/11, 80/3]': ('ndcv',[1,2],{'0': 4},[[1,0,-3],[0,1,-5],[-1,3,-18],[2,-3,-3],[0,1,-15],[3,-5,3]],[1,1],None,1000,False,234),  # line 2574
    '[7/30, 33/2, 8/175, 25/11, 14/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[5,-7,-1],[0,1,-4],[0,1,-6],[0,2,-25],[0,2,-27]],[1,1],None,1000,False,99),  # line 2575
    '[7/30, 33/2, 8/77, 25/11, 154/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-2,3,-3],[1,-1,-1],[0,2,-25],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,True,61),  # line 2576
    '[7/30, 33/2, 8/77, 25/11, 22/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-2,3,-3],[1,-1,-2],[0,2,-25],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,True,90),  # line 2577
    '[7/30, 33/2, 8/77, 25/11, 242/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-2,3,-8],[1,-1,-1],[1,0,-12],[1,0,-15],[1,0,-28],[-8,14,-105],[1,0,-29],[1,0,-30],[1,0,-31],[1,0,-32],[1,0,-33],[1,0,-34]],[1,1],None,400,False,334),  # line 2578
    '[7/30, 33/2, 8/77, 25/11, 847/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[1,0,-4],[1,0,-7],[0,1,-6],[1,0,-10],[0,2,-15],[1,0,-13],[0,1,-15],[1,0,-25],[-7,12,-77],[1,0,-27],[-7,12,-81],[1,0,-29],[-7,12,-83]],[2,3],'30',400,False,501),  # line 2579
    '[7/30, 33/2, 8/77, 5/11, 9317/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[2,-3,9],[0,1,-4],[1,0,-5],[0,1,-7],[1,0,-8],[0,1,-10],[0,1,-13],[0,1,-16],[0,1,-19],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39],[0,1,-40],[0,1,-41],[0,1,-42],[0,1,-43],[0,1,-44]],[1,1],None,400,False,436),  # line 2580
    '[7/30, 363/2, 16/35, 5/11, 21/5]': ('ndx',[1,2],{'0': 4},[[1,0,-7],[0,1,-6],[-4,3,-8],[2,-1,-12],[-5,4,-48],[-5,4,-51]],[1,1],None,400,False,377),  # line 2581
    '[7/30, 363/2, 8/175, 5/11, 14/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-2],[-1,1,-10],[3,-2,-4]],[1,1],None,1000,False,123),  # line 2582
    '[7/30, 363/2, 8/175, 5/11, 4/3]': ('nd',[1,4],{},[[1,0,-2],[0,1,-4],[-1,1,-11],[3,-2,-3]],[1,1],None,1000,False,209),  # line 2583
    '[7/30, 363/2, 8/35, 5/11, 147/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-2],[0,1,-4],[0,1,-6],[1,0,-3],[0,1,-10],[1,0,-6],[0,1,-20],[1,0,-12],[-4,3,-75],[1,0,-13],[-4,3,-77]],[1,1],None,400,False,619),  # line 2584
    '[7/30, 363/2, 8/35, 65/11, 21/13]': ('ndx',[1,2,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-2],[-3,2,0,-4],[0,1,0,-25],[0,1,0,-30],[1,0,0,-12],[1,0,0,-13]],[1,1,1],None,3000,True,244),  # line 2585
    '[7/30, 3993/2, 8/175, 5/11, 7/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-3],[-7,3,-4],[3,-1,-6],[1,0,-12],[1,0,-13],[1,0,-14]],[1,1],None,400,True,151),  # line 2586
    '[7/30, 4/21, 33275/2, 3/11, 2/5]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-3],[-1,1,-7],[3,-2,-6]],[1,1],None,1000,False,82),  # line 2587
    '[7/30, 40/21, 1331/2, 3/121, 7/11]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-9],[1,0,-3],[0,1,-11],[1,0,-5],[0,1,-19],[1,0,-8],[-4,1,-17],[1,0,-9],[-4,1,-19]],[1,2],'2',400,False,1681),  # line 2588
    '[7/30, 40/63, 121/2, 9/11, 7/3]': ('ndx',[1,2,3],{},[[1,0,0,-17],[0,1,0,-1],[0,0,1,-1],[1,-3,0,-167]],[1,1,1],None,144,'all',273),  # line 2589
    '[7/30, 40/63, 1331/2, 3/11, 7/3]': ('ndx',[2,4],{},[[1,0,-1],[0,1,-9],[1,0,-3],[1,0,-5],[0,1,-12],[1,0,-8],[-5,2,-24],[1,0,-9],[-5,2,-31]],[1,3],'1',3000,False,10125),  # line 2590
    '[7/30, 405/14, 11/3, 2/11, 105/2]': ('ndcv',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-8],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,400,False,680),  # line 2591
    '[7/30, 405/14, 11/3, 2/11, 45/2]': ('ndcv',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-5],[0,0,1,-7],[0,0,1,-15]],[1,1,1],None,400,False,9168),  # line 2592
    '[7/30, 44/3, 18/77, 5/2, 99/5]': ('ndx',[2,3],{'1': 1},[[1,0,-2],[0,1,-14],[1,0,-4],[1,0,-7],[1,0,-10],[1,0,-13],[1,0,-24],[1,0,-25],[1,0,-26],[1,0,-27],[1,0,-28],[1,0,-29]],[1,1],None,400,False,553),  # line 2593
    '[7/30, 45/154, 121/3, 2/11, 63/2]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-6],[1,0,-4],[1,0,-6],[1,0,-8],[-3,2,-40],[1,0,-9],[0,1,-34],[0,1,-35],[0,1,-36]],[1,1],None,400,False,547),  # line 2594
    '[7/30, 45/77, 1375/3, 2/25, 3/2]': ('ndcv',[0,3],{},[[1,0,-1],[0,1,-14]],[1,1],None,400,False,408),  # line 2595
    '[7/30, 45/77, 6655/3, 2/11, 9/2]': ('ndx',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-2],[0,-1,1,-34],[1,0,0,-16],[1,0,0,-20]],[1,1,1],None,144,False,746),  # line 2596
    '[7/30, 45/77, 73205/3, 2/11, 3/2]': ('ndx',[0,3],{},[[1,0,-2],[0,1,-1],[1,0,-25],[1,5,-100],[1,0,-26],[1,5,-104]],[1,1],None,144,False,536),  # line 2597
    '[7/30, 4719/2, 8/35, 5/11, 21/13]': ('ndx',[2,3,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-13],[0,0,1,0,-2],[0,0,0,1,-20],[-2,-1,-2,1,1],[2,1,2,-1,-1]],[1,1,1,1],None,100,False,111),  # line 2598
    '[7/30, 484/3, 9/77, 5/11, 363/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[4,-5,-4],[0,1,-7],[0,1,-10],[0,1,-12],[0,1,-20],[0,1,-21],[0,1,-22],[0,1,-23],[0,1,-24]],[1,1],None,1000,False,126),  # line 2599
    '[7/30, 484/3, 9/77, 5/11, 847/2]': ('ndx',[0,4],{},[[1,0,-433],[0,1,-320],[-2,3,0],[3,-4,0]],[1,1],None,300,False,1216),  # line 2600
    '[7/30, 484/3, 9/77, 5/11, 99/2]': ('nd',[0,4],{},[[1,0,-4],[0,1,-5],[-5,7,-35],[3,-4,9]],[1,1],None,1000,False,196),  # line 2601
    '[7/30, 5/231, 14641/5, 6/11, 25/2]': ('ndx',[0,1],{},[[1,0,-8],[0,1,-8],[-2,3,-23],[1,-1,-7]],[3,2],'3c',400,True,138),  # line 2602
    '[7/30, 5/231, 16/7, 33/2, 49/11]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-1,1,-1],[3,-2,-16],[3,-2,-22],[3,-2,-46],[3,-2,-56]],[1,6],'6',400,False,3201),  # line 2603
    '[7/30, 5324/3, 9/35, 5/11, 3/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-3],[-1,1,-7],[4,-3,-1]],[1,1],None,1000,False,93),  # line 2604
    '[7/30, 55/3, 243/35, 2/11, 35/2]': ('ndcv',[2,4],{},[[1,0,-5],[0,1,-5],[-1,1,-3],[3,-2,-12],[1,0,-24],[1,0,-25],[1,0,-26],[1,0,-27],[1,0,-28],[1,0,-29]],[1,1],None,400,True,191),  # line 2605
    '[7/30, 55/3, 27/77, 4/11, 231/2]': ('ndcv',[2,4],{},[[1,0,-4],[0,1,-4],[1,0,-5],[1,0,-9],[1,0,-16],[-5,8,-60],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,601),  # line 2606
    '[7/30, 55/3, 27/77, 4/11, 33/2]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-2],[0,1,-4],[1,0,-5],[1,0,-9],[1,0,-16],[-5,8,-60],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,937),  # line 2607
    '[7/30, 55/3, 27/77, 4/11, 363/2]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-3],[0,1,-4],[1,0,-5],[1,0,-8],[1,0,-12],[1,0,-15],[1,0,-28],[-8,14,-105],[1,0,-29],[1,0,-30],[1,0,-31],[1,0,-32],[1,0,-33],[1,0,-34]],[1,1],None,400,False,267),  # line 2608
    '[7/30, 55/3, 27/77, 4/11, 847/2]': ('ndcv',[2,4],{},[[1,0,-3],[0,1,-4],[1,0,-4],[1,0,-7],[1,0,-10],[1,0,-13],[1,0,-24],[-7,12,-90],[1,0,-25],[1,0,-26],[1,0,-27],[1,0,-28],[1,0,-29]],[1,1],None,400,False,430),  # line 2609
    '[7/30, 6/77, 121/2, 25/11, 24/5]': ('ndxz',[2,3],{},[[1,0,-1],[0,1,-189],[-9,1,0]],[3,9],'3de00',300,True,1891),  # line 2610
    '[7/30, 6/77, 121/2, 25/11, 308/5]': ('ndxz',[2,3],{},[[1,0,-1],[0,1,-187],[-23,1,0]],[3,9],'3de00',1000,True,2093),  # line 2611
    '[7/30, 8/21, 1/7, 605/2, 3/11, 7/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-2],[0,1,-4],[1,0,-5],[0,1,-5],[1,0,-8],[0,1,-9],[1,0,-15],[-4,3,-12],[-2,1,-6],[-2,1,-7]],[1,1],None,400,False,197),  # line 2612
    '[7/30, 8/21, 1287/2, 5/11, 35/13]': ('ndcv',[1,4,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[-1,2,0,-6],[2,-3,0,-7],[-2,2,1,1],[2,-2,-1,-1]],[1,1,1],None,400,False,59),  # line 2613
    '[7/30, 8/21, 605/2, 1/7, 3/11, 7/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-2],[0,1,-4],[1,0,-5],[0,1,-5],[1,0,-8],[0,1,-9],[1,0,-15],[-4,3,-12],[-2,1,-6],[-2,1,-7]],[1,1],None,400,False,197),  # line 2614
    '[7/30, 8/21, 605/2, 3/11, 245/3]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-2],[-3,2,-2],[2,-1,-10],[-4,3,-21]],[1,1],None,400,False,217),  # line 2615
    '[7/30, 8/21, 605/2, 39/11, 35/13]': ('ndcv',[1,2,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-2],[-1,2,0,-6],[2,-3,0,-4],[-11,10,3,6],[11,-10,-3,-6],[3,-4,0,-18]],[1,1,1],None,400,False,228),  # line 2616
    '[7/30, 8/21, 7865/2, 3/11, 35/13]': ('ndcv',[2,4,5],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[-3,2,0,-4],[2,-1,0,-6],[2,-2,1,1],[-2,2,-1,-1],[-4,3,0,-18]],[1,1,1],None,400,False,163),  # line 2617
    '[7/30, 8/21, 99/2, 1/7, 5/11, 7/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[1,0,-6],[0,1,-7],[1,0,-10],[0,1,-13],[3,-4,-17],[-1,2,-2],[-1,2,-6]],[1,6],'22',400,False,111),  # line 2618
    '[7/30, 8/21, 99/2, 25/121, 2/3]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[-1,2,-2],[2,-3,-1],[0,1,-8],[0,1,-15],[0,1,-16]],[1,1],None,400,True,81),  # line 2619
    '[7/30, 8/21, 99/2, 5/11, 1/7, 7/3]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[1,0,-6],[0,1,-7],[1,0,-10],[0,1,-13],[3,-4,-17],[-1,2,-2],[-1,2,-6]],[1,6],'22',400,False,111),  # line 2620
    '[7/30, 8/21, 99/2, 5/11, 14/9]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[-1,2,-6],[2,-3,-4],[3,-4,-18],[3,-4,-19]],[1,1],None,400,False,134),  # line 2621
    '[7/30, 8/21, 99/2, 5/11, 20/3]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[-1,2,-6],[2,-3,-4],[3,-4,-18],[3,-4,-19]],[1,1],None,400,False,137),  # line 2622
    '[7/30, 8/21, 99/2, 5/11, 22/15]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[-1,2,-2],[2,-3,0],[1,0,-14],[0,1,-15],[0,1,-16]],[1,1],None,400,True,68),  # line 2623
    '[7/30, 8/21, 99/2, 5/11, 4/9]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[1,0,-6],[0,1,-6],[1,0,-9],[0,1,-12],[3,-4,-18],[-1,2,-2],[-1,2,-6]],[1,1],None,400,False,85),  # line 2624
    '[7/30, 8/21, 99/2, 65/11, 35/13]': ('ndcv',[1,2,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[-1,2,0,-6],[2,-3,0,-7],[-2,2,1,1],[2,-2,-1,-1]],[1,1,1],None,400,False,78),  # line 2625
    '[7/30, 8/231, 1375/2, 3/5, 7/3]': ('ndxz',[2,4],{},[[1,0,-262],[0,1,-86],[-3,10,0],[1,-3,0]],[1,1],None,300,True,491),  # line 2626
    '[7/30, 8/63, 297/2, 5/11, 7/3]': ('ndx',[4,1],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,10131),  # line 2627
    '[7/30, 8/63, 55/2, 9/11, 21/5]': ('ndx',[2,4],{},[[1,0,-404],[0,1,-219],[-1,2,0],[7,-12,0]],[1,1],None,300,False,2157),  # line 2628
    '[7/30, 8/63, 605/2, 3/11, 4/5]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-4],[-1,1,-11],[3,-2,-3]],[1,1],None,1000,False,181),  # line 2629
    '[7/30, 8/63, 605/2, 9/11, 7/3]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-2],[0,1,-4],[1,0,-4],[1,0,-7],[0,1,-6],[1,0,-12],[-3,2,-15],[1,0,-13],[1,0,-14]],[1,1],None,1000,False,147),  # line 2630
    '[7/30, 8/63, 6655/2, 3/11, 7/3]': ('ndx',[2,4],{},[[1,0,-11],[0,1,-27],[-7,3,-4],[3,-1,-6],[1,0,-12],[-5,3,-30],[1,0,-13],[-5,3,-31],[-5,3,-34],[1,0,-14]],[1,1],None,3000,False,137),  # line 2631
    '[7/30, 8/63, 99/2, 15/11, 7/3]': ('ndcv',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-4],[0,-1,2,-9]],[1,1,1],None,400,False,73),  # line 2632
    '[7/30, 8/77, 33/2, 5/11, 9317/3]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-1],[2,-3,9],[0,1,-4],[1,0,-5],[0,1,-7],[1,0,-8],[0,1,-10],[0,1,-13],[0,1,-16],[0,1,-19],[0,1,-36],[0,1,-37],[0,1,-38],[0,1,-39],[0,1,-40],[0,1,-41],[0,1,-42],[0,1,-43],[0,1,-44]],[1,1],None,400,False,436),  # line 2633
    '[7/30, 80/21, 11/2, 3/11, 20/3]': ('ndcv',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-5],[0,0,1,-7],[0,0,1,-15]],[1,1,1],None,400,False,9170),  # line 2634
    '[7/30, 80/21, 11/2, 3/11, 70/3]': ('ndcv',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-8],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,400,False,682),  # line 2635
    '[7/30, 80/21, 11/2, 39/11, 35/13]': ('ndcv',[0,1,3,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-6],[0,0,0,1,-15],[-2,-3,-2,1,2],[2,3,2,-1,-2],[0,0,1,0,-12],[0,0,1,0,-13]],[1,1,1,1],None,400,False,734),  # line 2636
    '[7/30, 80/21, 143/2, 3/11, 35/13]': ('ndcv',[0,1,3,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-6],[0,0,0,1,-15],[-2,-3,-2,1,2],[2,3,2,-1,-2],[0,0,1,0,-12],[0,0,1,0,-13]],[1,1,1,1],None,400,False,734),  # line 2637
    '[7/30, 81/14, 22/3, 5/121, 21/2]': ('ndcv',[1,4],{},[[1,0,-4],[0,1,-1],[1,-2,-18],[1,1,-40],[1,1,-41],[0,1,-2]],[1,1],None,1000,False,209),  # line 2638
    '[7/30, 81/14, 22/3, 5/121, 9/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-2],[-1,1,-3],[4,-3,-3],[0,1,-20],[2,-1,-14],[0,1,-40],[0,1,-41],[0,1,-42],[0,1,-43]],[1,1],None,1000,False,291),  # line 2639
    '[7/30, 81/14, 242/3, 10/11, 3/2]': ('ndcv',[0,2],{},[[1,0,-3],[0,1,-2],[-2,3,-4],[1,-1,-5],[0,1,-20],[4,-5,-20],[4,-5,-22]],[1,2],'1',400,False,188),  # line 2640
    '[7/30, 81/77, 22/3, 5/11, 539/2]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-7],[-5,2,-16],[7,-2,0]],[1,1],None,400,False,47),  # line 2641
    '[7/30, 81/77, 22/3, 5/11, 847/2]': ('ndcv',[0,1],{},[[1,0,-2],[0,1,-15],[-2,1,-28],[3,-1,-13]],[1,1],None,1000,False,310),  # line 2642
    '[7/30, 81/77, 22/3, 5/11, 99/2]': ('ndcv',[0,1],{},[[1,0,-5],[0,1,-24],[-2,1,-25],[7,-2,-7]],[1,1],None,400,False,180),  # line 2643
    '[7/30, 88/21, 117/2, 25/11, 7/13]': ('ndcv',[1,4,5],{},[[1,0,0,-7],[0,1,0,-1],[0,0,1,-3],[-2,0,3,-3],[1,0,-1,-10],[-2,12,-1,5],[2,-12,1,-5]],[1,1,1],None,400,False,52),  # line 2644
    '[7/30, 88/21, 27/2, 25/11, 7/3]': ('ndcv',[1,4],{},[[1,0,-10],[0,1,-1],[1,-3,-35],[0,1,-4],[0,1,-6],[0,1,-7]],[1,1],None,400,True,52),  # line 2645
    '[7/30, 88/21, 275/2, 3/55, 7/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[0,1,-5],[1,0,-5],[0,1,-8],[1,0,-9],[0,1,-15],[1,-2,-16],[1,-2,-17]],[1,1],None,400,False,13183),  # line 2646
    '[7/30, 88/21, 297/2, 5/11, 7/3]': ('ndcv',[1,4],{},[[1,0,-3],[0,1,-1],[-1,2,0],[2,-3,-7]],[1,1],None,400,'all',11),  # line 2647
    '[7/30, 88/21, 9/2, 25/11, 14/3]': ('ndcv',[1,4],{},[[1,0,-8],[0,1,-1],[1,-4,-8],[0,1,-4],[0,2,-15]],[1,1],None,400,False,124),  # line 2648
    '[7/30, 88/63, 27/2, 5/11, 7/3]': ('add',10,[[],['24','355','1350'],[],['3','20'],['1','10']],2,[[9,187644]]),  # line 2649
    '[7/30, 88/63, 9/2, 5/11, 22/3]': ('add',10,[[],['4','85','450'],[],['3','20'],['2','10']],2,[[9,188189]]),  # line 2650
    '[7/30, 891/14, 2/3, 5/11, 231/2]': ('add',1,[['4','4','1'],[],[],[],['2','2']],10,[[49,15050],[50,15657],[51,16276],[52,16907]]),  # line 2651
    '[7/30, 9/35, 14641/3, 10/11, 15/2]': ('ndx',[0,2],{},[[1,0,-100],[0,1,-3],[0,1,-5],[0,1,-12],[3,-2,-27]],[18,3],'8',1000,False,62192),  # line 2652
    '[7/30, 9/35, 5324/3, 5/11, 3/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-3],[-1,1,-7],[3,-2,-6]],[1,1],None,1000,False,83),  # line 2653
    '[7/30, 9/77, 484/3, 5/11, 363/2]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-8],[-1,1,-8],[3,-2,-2]],[1,1],None,400,False,224),  # line 2654
    '[7/30, 9/77, 484/3, 5/11, 847/2]': ('nd',[0,4],{},[[1,0,-4],[0,1,-5],[-5,7,-35],[3,-4,9]],[1,1],None,1000,False,208),  # line 2655
    '[7/30, 9/77, 484/3, 5/11, 99/2]': ('ndx',[0,4],{},[[1,0,-433],[0,1,-320],[-2,3,0],[3,-4,0]],[1,1],None,300,False,1152),  # line 2656
    '[7/30, 9/77, 8/35, 275/2, 7/11]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-1],[-1,3,-5],[1,-2,-2],[0,1,-8],[0,1,-9],[0,1,-13],[0,1,-15]],[1,2],'2',400,False,56),  # line 2657
    '[7/30, 968/21, 117/2, 5/11, 7/13]': ('ndcv',[1,4,5],{},[[1,0,0,-7],[0,1,0,-2],[0,0,1,-3],[-1,3,0,-9],[1,-2,0,-5],[-2,6,-1,5],[2,-6,1,-5]],[1,1,1],None,400,False,56),  # line 2658
    '[7/30, 968/21, 27/2, 5/11, 7/3]': ('ndcv',[1,4],{},[[1,0,-10],[0,1,-2],[1,-2,-28],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,56),  # line 2659
    '[7/30, 968/21, 9/2, 5/11, 14/3]': ('ndcv',[1,4],{},[[1,0,-8],[0,1,-2],[-1,3,-6],[1,-2,-8],[0,1,-15]],[1,1],None,400,False,135),  # line 2660
    '[7/30, 968/21, 9/2, 5/11, 22/3]': ('ndcv',[1,4],{},[[1,0,-3],[0,1,-1],[-1,2,-1],[2,-3,-5],[0,1,-8],[0,1,-15],[-1,2,-3],[-1,2,-6],[-1,2,-7]],[1,1],None,400,False,2529),  # line 2661
    '[7/30, 99/2, 12/77, 5/3, 44/5]': ('ndx',[2,3],{'0': 1},[[1,0,-2],[0,1,-18],[1,0,-4],[1,0,-7],[1,0,-10],[1,0,-13],[1,0,-24],[1,0,-25],[1,0,-26],[1,0,-27],[1,0,-28],[1,0,-29]],[1,1],None,1000,False,740),  # line 2662
    '[7/30, 99/2, 176/21, 5/11, 7/3]': ('nd',[1,4],{},[[1,0,-2],[0,1,-1],[7,-9,-9]],[1,1],None,1000,False,73),  # line 2663
    '[7/45, 1/847, 10/7, 891/2, 25/3]': ('nd',[1,4],{},[[1,0,-4],[0,1,-1],[4,-5,-56]],[1,1],None,400,True,61),  # line 2668
    '[7/45, 1/847, 10/7, 891/2, 5/3]': ('ndcv',[1,4],{},[[1,0,-4],[0,1,-1],[0,1,-8],[2,-3,-20],[2,-3,-40],[0,1,-9],[2,-3,-41]],[1,1],None,400,False,187),  # line 2669
    '[7/45, 1/847, 20/7, 297/2, 25/3]': ('ndcv',[1,4],{},[[1,0,-3],[0,1,-1],[0,1,-9],[0,1,-13],[0,1,-17],[4,-5,-43],[4,-5,-75],[0,1,-19],[4,-5,-81]],[1,2],'2',400,False,132),  # line 2670
    '[7/45, 125/847, 44/5, 3/2, 55/3]': ('mul',2,[[],['1','680'],[],[],['8/3','340/3']],4,1,[[16,43521],[64,174081],[256,696321],[1024,2785281]]),  # line 2673
    '[7/45, 25/231, 22/5, 81/2, 5/3]': ('mul',1,[['1','2'],[],[],[],['1','1']],2,5,[[32,663],[64,1335],[128,2679],[256,5367]]),  # line 2675
    '[7/45, 25/539, 2662/5, 3/11, 25/2]': ('ndx',[0,1,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[3,-1,0,-2],[0,1,0,-16],[0,1,0,-17],[0,1,0,-18],[0,1,0,-19]],[1,1,1],None,400,True,110),  # line 2676
    '[7/45, 3/77, 10/7, 891/2, 25/3]': ('ndcv',[1,4],{},[[1,0,-4],[0,1,-1],[1,-2,-7],[1,0,-14],[1,0,-18],[0,1,-8],[0,1,-9]],[1,1],None,400,True,234),  # line 2677
    '[7/45, 44/5, 125/847, 3/2, 55/3]': ('mul',2,[[],['1','680'],[],[],['8/3','340/3']],4,1,[[16,43521],[64,174081],[256,696321],[1024,2785281]]),  # line 2678
    '[7/450, 33/2, 8/21, 5/11, 21/5]': ('ndx',[2,3],{},[[1,0,-2],[0,1,-3],[0,1,-4],[0,1,-6],[0,1,-14],[0,1,-15],[0,2,-31]],[1,1],None,400,False,458),  # line 2679
    '[7/60, 11/3, 54/35, 10/11, 35/2]': ('add',3,[['8','29/2','27/2'],[],[],[],['9','12']],10,[[49,199781]]),  # line 2680
    '[7/60, 11/3, 54/35, 20/11, 3/2]': ('add',3,[['14','53/2','27/2'],[],['4','4'],[],[]],10,[[49,67650],[50,70380],[51,73164],[52,76002]]),  # line 2681
    '[7/60, 22/3, 27/77, 10/11, 33/2]': ('ndcv',[0,4],{},[[1,0,-1],[0,1,-2],[2,-3,4],[0,1,-4],[0,1,-5],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,1000,False,216),  # line 2682
    '[7/60, 22/3, 54/35, 10/11, 3/2]': ('add',3,[['14','53/2','27/2'],[],['4','4'],[],[]],10,[[49,67650],[50,70380],[51,73164],[52,76002]]),  # line 2683
    '[7/60, 22/3, 54/35, 5/11, 35/2]': ('add',3,[['17','53/2','27/2'],[],[],[],['9','12']],10,[[49,199781]]),  # line 2684
    '[7/60, 22/3, 54/35, 5/11, 9/2]': ('add',1,[['20','17/2','3/2'],[],[],[],['10','4']],10,[[49,23913],[50,24849],[51,25803],[52,26775]]),  # line 2685
    '[7/60, 27/14, 121/7, 20/11, 7/2]': ('ndx',[0,2],{},[[1,0,-4],[0,1,-2],[-2,3,-3],[1,-1,-5],[1,0,-35],[1,0,-36]],[1,1],None,400,False,208),  # line 2686
    '[7/60, 27/77, 22/3, 10/11, 33/2]': ('ndcv',[0,4],{},[[1,0,-1],[0,1,-2],[2,-3,4],[0,1,-4],[0,1,-5],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,1000,False,216),  # line 2687
    '[7/60, 27/77, 44/3, 5/11, 33/2]': ('ndcv',[0,2],{},[[1,0,-2],[0,1,-2],[1,-3,4],[0,1,-5],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,232),  # line 2688
    '[7/60, 27/77, 44/3, 5/11, 77/2]': ('ndcv',[0,4],{},[[1,0,-6],[0,1,-3],[1,-3,1],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,70),  # line 2689
    '[7/60, 44/3, 27/77, 5/11, 33/2]': ('ndcv',[0,2],{},[[1,0,-2],[0,1,-2],[1,-3,4],[0,1,-5],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,232),  # line 2690
    '[7/60, 44/3, 27/77, 5/11, 77/2]': ('ndcv',[0,4],{},[[1,0,-6],[0,1,-3],[1,-3,1],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,70),  # line 2691
    '[7/60, 44/3, 54/35, 5/11, 3/2]': ('add',3,[['14','53/2','27/2'],[],['4','4'],[],[]],10,[[49,67650],[50,70380],[51,73164],[52,76002]]),  # line 2692
    '[7/60, 44/3, 9/77, 5/11, 231/2]': ('add',1,[['11','15/2','5/2'],[],[],[],['3','3']],14,[[69,41422],[70,42617],[71,43829],[72,45058]]),  # line 2693
    '[7/60, 44/3, 9/77, 5/11, 27/2]': ('add',1,[['11','15/2','5/2'],[],[],[],['3','3']],14,[[69,38936],[70,40060],[71,41200],[72,42356]]),  # line 2694
    '[7/60, 45/77, 121/3, 2/11, 63/2]': ('ndcv',[0,2],{},[[1,0,-7],[0,1,-1],[1,-3,-8],[1,0,-24],[1,0,-28],[1,0,-32],[0,1,-8],[0,1,-9]],[1,1],None,400,True,247),  # line 2695
    '[7/60, 54/35, 11/3, 10/11, 35/2]': ('add',3,[['8','29/2','27/2'],[],[],[],['9','12']],10,[[49,199781]]),  # line 2696
    '[7/60, 54/35, 11/3, 20/11, 3/2]': ('add',3,[['14','53/2','27/2'],[],['4','4'],[],[]],10,[[49,67650],[50,70380],[51,73164],[52,76002]]),  # line 2697
    '[7/60, 54/35, 22/3, 10/11, 3/2]': ('add',3,[['14','53/2','27/2'],[],['4','4'],[],[]],10,[[49,67650],[50,70380],[51,73164],[52,76002]]),  # line 2698
    '[7/60, 54/35, 22/3, 5/11, 35/2]': ('add',3,[['17','53/2','27/2'],[],[],[],['9','12']],10,[[49,199781]]),  # line 2699
    '[7/60, 54/35, 22/3, 5/11, 9/2]': ('add',1,[['19','17/2','3/2'],[],[],[],['10','4']],10,[[49,23907],[50,24843],[51,25797],[52,26769]]),  # line 2700
    '[7/60, 54/35, 44/3, 5/11, 3/2]': ('add',3,[['14','53/2','27/2'],[],['4','4'],[],[]],10,[[49,67650],[50,70380],[51,73164],[52,76002]]),  # line 2701
    '[7/60, 9/77, 44/3, 5/11, 231/2]': ('add',1,[['11','15/2','5/2'],[],[],[],['3','3']],14,[[69,41422],[70,42617],[71,43829],[72,45058]]),  # line 2702
    '[7/60, 9/77, 44/3, 5/11, 27/2]': ('add',1,[['11','15/2','5/2'],[],[],[],['3','3']],14,[[69,38936],[70,40060],[71,41200],[72,42356]]),  # line 2703
    '[7/90, 11/2, 24/35, 15/11, 35/3]': ('add',5,[[],['30','385/2','675/2'],[],['11','30'],[]],2,[[9,177503]]),  # line 2704
    '[7/90, 11/2, 24/35, 45/11, 2/3]': ('add',3,[[],['14','53/2','27/2'],['4','4'],[],[]],10,[[49,67649],[50,70379],[51,73163],[52,76001]]),  # line 2705
    '[7/90, 11/2, 40/21, 9/11, 35/3]': ('ndcv',[1,2],{},[[1,0,-6],[0,1,-2],[1,0,-10],[0,1,-4],[1,0,-18],[0,1,-8],[2,-7,-36],[2,-7,-40]],[1,1],None,1000,False,326),  # line 2706
    '[7/90, 121/2, 40/21, 3/11, 35/3]': ('ndcv',[2,4],{},[[1,0,-2],[0,1,-6],[0,1,-10],[1,0,-4],[0,1,-18],[1,0,-8],[-7,2,-36],[-7,2,-38],[-7,2,-40]],[1,1],None,400,False,365),  # line 2707
    '[7/90, 121/2, 8/21, 45/11, 2/5]': ('ndx',[1,2],{},[[1,0,-4],[0,1,-2],[-1,2,1],[0,1,-6],[1,0,-12],[0,1,-9],[1,0,-18],[1,0,-35],[1,0,-36],[1,0,-37],[-3,7,-25]],[1,1],None,400,False,59),  # line 2708
    '[7/90, 125/21, 11/5, 18/11, 25/2]': ('ndcv',[0,1],{},[[1,0,-2],[0,1,-4],[-1,1,-11],[2,-1,-5],[0,1,-28],[0,1,-29],[0,1,-36]],[1,1],None,400,False,157),  # line 2709
    '[7/90, 125/21, 121/5, 18/11, 5/2]': ('ndcv',[0,1],{},[[1,0,-2],[0,1,-4],[2,-1,1],[0,1,-35],[0,1,-36],[0,1,-37]],[1,1],None,400,False,60),  # line 2710
    '[7/90, 125/21, 22/5, 9/11, 25/2]': ('ndcv',[0,1],{},[[1,0,-2],[0,1,-4],[-1,1,-11],[2,-1,-5],[0,1,-28],[0,1,-29],[0,1,-36]],[1,1],None,400,False,157),  # line 2711
    '[7/90, 125/21, 242/5, 3/11, 25/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[-1,1,-14],[3,-2,0]],[1,1],None,400,False,169),  # line 2712
    '[7/90, 16/35, 11/2, 15/11, 14/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[-2,3,-6],[1,-1,-6],[1,0,-40],[-5,8,-40],[1,0,-41],[-5,8,-44]],[1,1],None,1000,False,210),  # line 2713
    '[7/90, 16/35, 11/2, 15/11, 4/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[-2,3,-1],[1,-1,-3],[1,0,-20],[1,0,-40],[0,1,-28],[1,0,-41],[1,0,-42],[1,0,-43]],[1,1],None,1000,True,437),  # line 2714
    '[7/90, 16/35, 33/2, 5/11, 14/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-2,3,-6],[1,-1,-6],[1,0,-40],[-5,8,-40],[1,0,-41],[-5,8,-44]],[1,1],None,1000,False,177),  # line 2715
    '[7/90, 16/35, 33/2, 5/11, 4/5]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-2,3,-1],[1,-1,-3],[1,0,-20],[1,0,-40],[0,1,-28],[1,0,-41],[1,0,-42],[1,0,-43]],[1,1],None,1000,True,379),  # line 2716
    '[7/90, 16/35, 55/2, 3/11, 14/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[-2,3,-8],[1,-1,-6],[1,0,-40],[-5,8,-40],[1,0,-41],[-5,8,-44]],[1,1],None,1000,False,234),  # line 2717
    '[7/90, 16/35, 55/2, 3/11, 4/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[-2,3,-2],[1,-1,-3],[1,0,-12],[1,0,-20],[-1,2,-14],[1,0,-40],[-5,8,-40],[1,0,-41],[1,0,-42],[1,0,-43],[-5,8,-42]],[1,1],None,1000,False,288),  # line 2718
    '[7/90, 20/77, 121/2, 3/11, 28/3]': ('ndcv',[1,2],{},[[1,0,-8],[0,1,-1],[1,-3,-8],[1,0,-24],[1,0,-28],[1,0,-32],[0,1,-8],[0,1,-9]],[1,1],None,400,True,254),  # line 2719
    '[7/90, 24/35, 11/2, 15/11, 35/3]': ('add',5,[[],['30','385/2','675/2'],[],['11','30'],[]],2,[[9,177503]]),  # line 2720
    '[7/90, 24/35, 11/2, 45/11, 2/3]': ('add',3,[[],['14','53/2','27/2'],['4','4'],[],[]],10,[[49,67649],[50,70379],[51,73163],[52,76001]]),  # line 2721
    '[7/90, 24/35, 33/2, 15/11, 2/3]': ('add',3,[[],['14','53/2','27/2'],['4','4'],[],[]],10,[[49,67649],[50,70379],[51,73163],[52,76001]]),  # line 2722
    '[7/90, 24/35, 99/2, 5/11, 2/3]': ('add',3,[[],['14','53/2','27/2'],['4','4'],[],[]],10,[[49,67649],[50,70379],[51,73163],[52,76001]]),  # line 2723
    '[7/90, 3/77, 16/7, 55/2, 49/11]': ('add',2,[[],[],['1','18','28'],[],['1','21']],4,[[19,40604],[20,44981],[21,49582],[22,54407]]),  # line 2724
    '[7/90, 33/2, 16/35, 5/11, 14/5]': ('ndx',[2,3,4],{},[[1,0,0,-1],[0,1,0,-18],[0,0,1,-2]],[1,1,1],None,400,False,261),  # line 2725
    '[7/90, 33/2, 16/35, 5/11, 4/5]': ('ndx',[2,3,4],{},[[1,0,0,-1],[0,1,0,-7],[0,0,1,-1],[0,1,0,-10]],[1,1,1],None,400,False,329),  # line 2726
    '[7/90, 33/2, 24/35, 15/11, 2/3]': ('add',3,[[],['14','53/2','27/2'],['4','4'],[],[]],10,[[49,67649],[50,70379],[51,73163],[52,76001]]),  # line 2727
    '[7/90, 33/2, 8/77, 15/11, 77/3]': ('ndx',[1,2],{},[[1,0,-2],[0,1,-1],[2,-5,6],[0,1,-4],[1,0,-10],[0,1,-7],[0,1,-13]],[2,6],'10',400,False,133),  # line 2728
    '[7/90, 33/5, 625/14, 2/11, 25/2]': ('ndcv',[0,3,4],{},[[1,0,0,-1],[0,1,0,-11],[0,0,1,-1]],[1,1,1],None,400,False,184),  # line 2729
    '[7/90, 33/5, 625/14, 2/11, 35/2]': ('ndcv',[0,3,4],{},[[1,0,0,-1],[0,1,0,-10],[0,0,1,-1]],[1,1,1],None,400,False,117),  # line 2730
    '[7/90, 40/21, 11/2, 9/11, 35/3]': ('ndcv',[1,2],{},[[1,0,-6],[0,1,-2],[1,0,-10],[0,1,-4],[1,0,-18],[0,1,-8],[2,-7,-36],[0,1,-9]],[1,1],None,1000,False,326),  # line 2731
    '[7/90, 40/21, 121/2, 3/11, 35/3]': ('ndcv',[2,4],{},[[1,0,-2],[0,1,-6],[0,1,-10],[1,0,-4],[0,1,-18],[1,0,-8],[-7,2,-36]],[1,1],None,1000,False,365),  # line 2732
    '[7/90, 55/2, 8/175, 3/11, 4/3]': ('ndcv',[1,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-2],[1,-3,0,6],[0,1,0,-6],[0,1,0,-11],[0,1,0,-25],[0,1,0,-26]],[1,1,1],None,400,False,1186),  # line 2733
    '[7/90, 625/14, 11/5, 6/11, 25/2]': ('ndcv',[0,1],{},[[1,0,-2],[0,1,-2],[-1,1,-3],[4,-3,-3],[0,1,-40],[0,1,-41],[-1,1,-4],[0,1,-42],[0,1,-43]],[1,1],None,1000,False,395),  # line 2734
    '[7/90, 625/14, 11/5, 6/11, 35/2]': ('ndcv',[1,4],{},[[1,0,-1],[0,1,-4],[1,1,-41],[-5,3,-35],[1,0,-3],[-5,3,-44]],[2,1],'2',1000,False,310),  # line 2735
    '[7/90, 625/14, 22/5, 3/11, 25/2]': ('ndcv',[0,1],{},[[1,0,-2],[0,1,-2],[-1,1,-3],[4,-3,-3],[0,1,-40],[0,1,-41],[0,1,-42],[0,1,-43]],[1,1],None,1000,False,395),  # line 2736
    '[7/90, 625/14, 22/5, 3/11, 35/2]': ('ndcv',[0,1],{},[[1,0,-4],[0,1,-5],[-1,1,-7],[4,-3,-11],[0,1,-40],[0,1,-41]],[1,1],None,1000,False,364),  # line 2737
    '[7/90, 625/14, 33/5, 2/11, 25/2]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-2],[-2,3,-6],[1,-1,-3],[1,0,-40],[-5,8,-40],[1,0,-41],[1,-1,-4],[1,0,-42],[1,0,-43],[-5,8,-42]],[1,1],None,1000,False,342),  # line 2738
    '[7/90, 625/14, 33/5, 2/11, 35/2]': ('ndcv',[1,4],{},[[1,0,-5],[0,1,-4],[-2,3,-18],[1,-1,-7],[1,0,-40],[1,0,-41]],[1,1],None,1000,False,310),  # line 2739
    '[7/90, 8/175, 55/2, 3/11, 4/3]': ('ndcv',[1,2],{},[[1,0,-1],[0,1,-1],[1,-3,16],[0,1,-4],[1,0,-10],[0,1,-8],[1,0,-14],[0,1,-20],[5,-2,-200],[0,1,-21],[0,1,-22],[0,1,-23],[0,1,-24]],[1,1],None,3000,False,1183),  # line 2740
    '[7/90, 8/21, 11/2, 45/11, 4/5]': ('ndx',[1,2],{},[[1,0,-2],[0,1,-1],[-2,3,12],[0,1,-5],[1,0,-8],[0,1,-7],[1,0,-14],[0,1,-15],[1,0,-28],[1,0,-29],[1,0,-36]],[1,1],None,400,False,165),  # line 2741
    '[7/90, 8/21, 121/2, 45/11, 2/5]': ('ndx',[1,2,3],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,2,0,-1],[1,0,0,-10],[1,0,0,-16],[1,0,0,-35],[2,0,7,-78]],[1,1,1],None,400,False,209),  # line 2742
    '[7/90, 8/21, 55/2, 9/11, 4/5]': ('ndx',[1,2],{},[[1,0,-2],[0,1,-1],[-1,2,-2],[1,-1,-10],[0,1,-15],[1,0,-28],[1,0,-29],[1,0,-36]],[1,1],None,400,False,219),  # line 2743
    '[7/90, 8/21, 605/2, 3/11, 4/5]': ('ndx',[1,2],{},[[1,0,-2],[0,1,-1],[-1,2,-2],[1,-1,-10],[0,1,-15],[1,0,-28],[1,0,-29],[1,0,-30],[1,0,-31],[1,0,-32],[1,0,-33],[1,0,-34]],[1,1],None,400,False,167),  # line 2744
    '[7/90, 8/77, 33/2, 15/11, 77/3]': ('ndx',[1,2],{},[[1,0,-2],[0,1,-1],[2,-5,6],[0,1,-4],[1,0,-10],[0,1,-7],[0,1,-13]],[2,6],'10',400,False,133),  # line 2745
    '[7/90, 8/77, 99/2, 5/11, 22/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[1,-3,5],[0,1,-5],[1,0,-12],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,206),  # line 2746
    '[7/90, 8/77, 99/2, 5/11, 77/3]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[1,-3,3],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,111),  # line 2747
    '[7/90, 88/21, 9/2, 5/11, 35/3]': ('add',7,[[],['468','910','441'],[],['31','28'],['15','14']],1,[[6,110806],[7,144273],[8,182150]]),  # line 2748
    '[7/90, 88/21, 9/2, 5/11, 77/3]': ('add',7,[[],['295','721','441'],[],['25','28'],['13','14']],1,[[5,76221],[6,104354],[7,136897],[8,173850]]),  # line 2749
    '[7/90, 9/2, 88/21, 5/11, 35/3]': ('ndcv',[1,4],{},[[1,0,-273527],[0,1,-1042],[0,100,0],[1,-100,0]],[1,1],None,4,True,1359290),  # line 2750
    '[7/90, 9/2, 88/21, 5/11, 77/3]': ('ndx',[1,4],{},[[1,0,-6],[0,1,-2],[3,-11,-2],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,3000,False,246),  # line 2751
    '[7/90, 99/2, 24/35, 5/11, 2/3]': ('add',3,[[],['14','53/2','27/2'],['4','4'],[],[]],10,[[49,67649],[50,70379],[51,73163],[52,76001]]),  # line 2752
    '[7/90, 99/2, 8/77, 5/11, 22/3]': ('ndcv',[1,2],{},[[1,0,-2],[0,1,-1],[1,-3,5],[0,1,-5],[1,0,-12],[0,1,-9],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,False,206),  # line 2753
    '[7/90, 99/2, 8/77, 5/11, 77/3]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[1,-3,3],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,111),  # line 2754
    '[77/135, 75/14, 22/5, 3/11, 35/2]': ('add',1,[['2','1'],['4','4'],[],[],[]],15,[[102,53354],[103,54392],[104,55440],[105,56498]]),  # line 2755
    '[77/135, 75/14, 6/5, 3/11, 35/2]': ('add',1,[['2','1'],['4','4'],[],[],[]],15,[[102,84975],[103,86632],[104,88305],[105,89994]]),  # line 2756
    '[77/15, 1/3, 3/70, 198/7, 5/11, 7/2]': ('add',10,[['1','2'],[],[],[],['1','12']],1,[[4,2820],[5,4324],[6,6148],[7,8292]]),  # line 2818
    '[77/15, 1/42, 99/7, 2/3, 25/11, 7/2]': ('ndx',[1,4],{},[[1,0,-1],[0,1,-1],[-5,3,-1],[7,-1,-3],[1,0,-4],[1,0,-10],[-3,2,-5]],[1,1],None,400,False,442),  # line 2821
    '[77/15, 1/42, 99/7, 2/3, 5/11, 15/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,1000,False,595),  # line 2822
    '[77/15, 1/42, 99/7, 2/3, 5/11, 21/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-1],[-2,1,0],[0,1,-8],[0,1,-24],[3,-1,-36],[-24,13,-74]],[1,1],None,1000,False,1267),  # line 2823
    '[77/15, 1/42, 99/7, 2/3, 5/11, 33/2]': ('ndx',[1,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-10],[-2,-3,1,-9]],[1,1,1],None,1000,False,530),  # line 2824
    '[77/15, 1/42, 99/7, 2/3, 5/11, 49/2]': ('ndx',[0,2],{'3': 2},[[1,0,-3],[0,1,-2],[-2,1,-10],[3,-1,-30],[3,-1,-34]],[1,1],None,400,False,1965),  # line 2825
    '[77/15, 1/42, 99/7, 2/3, 5/11, 77/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,1000,False,588),  # line 2826
    '[77/15, 1/42, 99/7, 2/9, 5/11, 7/2]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[-2,1,-2],[1,0,-8],[1,0,-20]],[1,1],None,400,True,237),  # line 2827
    '[77/15, 1/42, 99/7, 22/3, 5/11, 3/2]': ('mul',2,[['3/4','1/4'],[],[],[],['-1','2']],5,6,[[125,723],[625,3658],[3125,18343],[15625,91778]]),  # line 2828
    '[77/15, 1/42, 99/7, 22/3, 5/11, 7/2]': ('mul',2,[[],['3/4','5/4'],[],[],['-11/4','15/4']],5,6,[[125,1455],[625,7386],[3125,37067],[15625,185498]]),  # line 2829
    '[77/15, 1/84, 99/7, 2/3, 5/11, 7/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-1],[-7,3,-1],[4,-1,-7],[1,0,-20]],[1,1],None,400,False,339),  # line 2854
    '[77/15, 11/42, 9/7, 22/3, 5/11, 3/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-1],[-2,1,-9],[1,0,-10],[3,-1,-30],[3,-1,-34]],[1,1],None,3000,False,2622),  # line 2888
    '[77/15, 11/42, 9/7, 22/3, 5/11, 7/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-10],[3,-1,-24],[3,-1,-35]],[1,1],None,3000,False,2598),  # line 2889
    '[77/15, 2366/3, 9/143, 5/91, 33/2]': ('ndx',[0,3,4],{},[[1,0,0,-1],[0,1,0,-9],[0,0,1,-15],[-9,1,0,0],[42,-1,0,0],[-15,0,1,0],[68,0,-1,0],[0,-3,2,0],[0,5,-3,0]],[1,1,1],None,300,False,48),  # line 2903
    '[77/15, 27/98, 44/3, 5/11, 9/2]': ('nd',[0,3,4,1],{},[[1,0,0,0,-10],[0,1,0,0,-3],[0,0,1,0,-1],[0,0,0,1,-1],[0,-3,1,0,11],[1,2,-1,-1,-19]],[1,1,1,1],None,1000,False,430),  # line 2904
    '[77/15, 3/154, 25/7, 4/5, 3773/2]': ('ndxz',[0,1],{},[[1,0,-1],[0,1,-187],[-23,1,0]],[3,9],'3de00',300,True,1869),  # line 2906
    '[77/15, 3/154, 25/7, 4/5, 735/2]': ('ndz',[0,1],{},[[1,0,-1],[0,1,-1],[-1,0,10]],[3,9],'3de00',1000,'all',20),  # line 2907
    '[77/15, 3094/3, 27/2431, 5/7, 3/2]': ('nd',[0,3,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-1],[4,-3,0,0,0],[0,0,-1,1,0],[0,0,1,-1,0],[-1,2,-2,0,1],[1,-2,2,0,-1],[0,1,0,0,-5],[0,1,0,0,-8],[0,1,0,0,-15]],[1,1,1,1],None,400,False,98),  # line 2908
    '[77/15, 5/42, 1/5, 550/7, 3/11, 7/2]': ('add',10,[['1','2'],[],[],[],['1','12']],1,[[4,2820],[5,4324],[6,6148],[7,8292]]),  # line 2936
    '[77/15, 5/42, 11/5, 50/7, 3/11, 7/2]': ('add',10,[['1','4'],[],[],[],['2','24']],1,[[3,3124],[4,5444],[5,8404],[6,12004]]),  # line 2937
    '[77/15, 5/42, 50/7, 11/5, 3/11, 7/2]': ('add',10,[['1','4'],[],[],[],['2','24']],1,[[3,3124],[4,5444],[5,8404],[6,12004]]),  # line 2938
    '[77/15, 5/42, 550/7, 1/5, 3/11, 7/2]': ('add',10,[['1','2'],[],[],[],['1','12']],1,[[4,2820],[5,4324],[6,6148],[7,8292]]),  # line 2939
    '[77/15, 6/91, 24167/3, 5/143, 21/2]': ('ndx',[0,4,3],{},[[1,0,0,-1],[0,1,0,-9],[0,0,1,-15],[-9,1,0,0],[42,-1,0,0],[-15,0,1,0],[68,0,-1,0],[0,-3,2,0],[0,5,-3,0]],[1,1,1],None,1000,False,1174),  # line 2950
    '[77/15, 7/3, 3/110, 18/11, 5/7, 11/2]': ('add',10,[['1','4'],[],[],['2','24'],[]],1,[[3,3124],[4,5444],[5,8404],[6,12004]]),  # line 2951
    '[77/15, 9/1183, 48334/3, 5/11, 3/2]': ('ndx',[0,4,5],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-3],[-1,1,0,-2],[3,-2,0,-1],[-2,3,-1,2],[2,-3,1,-2],[0,1,0,-8],[0,1,0,-30],[0,1,0,-31],[0,1,0,-32],[0,1,0,-34]],[1,1,1],None,400,True,240),  # line 2952
    '[77/15, 9/28, 275/7, 2/11, 147/2]': ('mul',2,[['-2','60'],[],['0','30'],[],[]],3,1,[[9,3111],[27,9375],[81,28167],[243,84543]]),  # line 2953
    '[77/15, 9/91, 3718/3, 5/143, 21/2]': ('ndx',[0,3,4],{},[[1,0,0,-1],[0,1,0,-15],[0,0,1,-9],[-15,1,0,0],[68,-1,0,0],[-9,0,1,0],[42,0,-1,0],[0,-3,5,0],[0,2,-3,0]],[1,1,1],None,300,False,48),  # line 2959
    '[77/15, 99/28, 8/3, 5/11, 21/2]': ('ndx',[0,4],{},[[1,0,-7],[0,1,-1],[1,-1,-16],[0,1,-4],[0,1,-8],[0,1,-9]],[1,1],None,400,True,64),  # line 2960
    '[77/15, 99/28, 8/3, 5/11, 33/2]': ('ndx',[0,4],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4],[0,1,-8],[0,1,-30],[0,1,-31],[0,1,-32],[0,1,-33],[0,1,-34]],[1,1],None,400,True,240),  # line 2961
    '[77/30, 16/21, 99/2, 5/11, 7/5]': ('ndx',[1,4],{},[[1,0,-2],[0,1,-1],[3,-4,-11],[0,1,-4],[0,1,-5],[0,1,-9],[0,1,-20],[-1,2,-5],[-1,2,-8],[-1,2,-9]],[1,4],'1',400,False,130),  # line 2962
    '[77/30, 176/21, 9/2, 5/11, 7/3]': ('ndx',[1,4],{},[[1,0,-8],[0,1,-1],[1,-4,-8],[0,1,-4],[0,1,-8],[0,1,-19]],[2,8],'80',400,False,187),  # line 2963
    '[77/30, 27/14, 44/3, 5/121, 3/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-1],[-1,2,-3],[2,-3,-1],[0,1,-8],[0,1,-10],[0,1,-16],[0,1,-30],[0,1,-31]],[1,1],None,400,False,176),  # line 2964
    '[77/30, 297/14, 4/3, 5/11, 21/2]': ('ndcv',[0,4],{},[[1,0,-7],[0,1,-1],[1,-2,-13],[0,1,-4],[0,1,-5],[0,1,-8],[0,1,-15]],[1,1],None,400,False,79),  # line 2965
    '[77/30, 297/35, 20/7, 5/11, 7/2]': ('ndx',[0,2],{'3': 1},[[1,0,-1],[0,1,-1],[-3,2,0],[2,-1,-3],[0,1,-20],[0,1,-24],[0,1,-28],[2,-1,-10],[-4,3,-12],[-4,3,-14]],[1,1],None,200,False,6791),  # line 2966
    '[77/30, 297/35, 44/7, 5/11, 7/2]': ('ndx',[0,3,4],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-3],[-3,0,2,0],[2,0,-1,-2],[0,-1,0,1],[0,1,0,-1],[1,0,0,-12],[-4,0,3,-15],[1,0,0,-13]],[1,1,1],None,400,False,171),  # line 2967
    '[77/30, 8/21, 1/7, 55/2, 3/11, 7/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[-3,2,0],[3,-1,-6],[0,1,-12],[1,0,-15]],[1,1],None,400,True,233),  # line 2968
    '[77/30, 8/21, 275/2, 3/55, 7/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-1],[0,1,-5],[1,0,-5],[0,1,-8],[1,0,-9],[0,1,-15],[1,-2,-16],[1,-2,-17]],[1,1],None,400,False,506),  # line 2969
    '[77/30, 8/21, 55/2, 1/7, 3/11, 7/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[-3,2,0],[3,-1,-6],[0,1,-12],[1,0,-15]],[1,1],None,400,True,233),  # line 2970
    '[77/30, 8/21, 99/2, 5/121, 2/3]': ('ndcv',[1,4],{},[[1,0,-2],[0,1,-1],[-1,2,-3],[2,-3,-1],[0,1,-8],[0,1,-10],[0,1,-16],[0,1,-30],[0,1,-31]],[1,1],None,400,False,175),  # line 2971
    '[77/30, 88/21, 117/2, 5/11, 7/13]': ('ndcv',[1,4,5],{},[[1,0,0,-7],[0,1,0,-1],[0,0,1,-3],[-1,0,2,-5],[1,0,-1,-10],[0,2,-1,1],[0,-2,1,-1],[0,1,0,-12],[0,1,0,-13],[0,1,0,-14]],[1,1,1],None,400,False,76),  # line 2972
    '[77/30, 88/21, 27/2, 5/11, 7/3]': ('ndcv',[1,4],{},[[1,0,-10],[0,1,-1],[1,-4,-12],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,76),  # line 2973
    '[77/30, 88/21, 9/2, 5/11, 14/3]': ('ndcv',[1,4],{},[[1,0,-8],[0,1,-1],[1,-2,-14],[0,1,-4],[0,1,-5],[0,1,-8],[0,1,-15]],[1,1],None,400,False,80),  # line 2974
    '[77/30, 88/21, 9/2, 5/11, 22/3]': ('ndcv',[1,4],{},[[1,0,-3],[0,1,-1],[-1,2,-1],[2,-3,-5],[0,1,-8],[0,1,-15],[-1,2,-3],[-1,2,-6],[-1,2,-7]],[1,1],None,400,False,2529),  # line 2975
    '[77/30, 88/21, 9/2, 5/11, 49/3]': ('ndcv',[1,4],{},[[1,0,-11],[0,1,-2],[1,-2,-17],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,68),  # line 2976
    '[77/30, 88/21, 9/2, 5/11, 7/3]': ('ndcv',[1,4],{},[[1,0,-6],[0,1,-1],[1,-2,-8],[0,1,-4],[0,1,-7],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,76),  # line 2977
    '[77/45, 25/14, 1452/5, 3/11, 5/2]': ('ndx',[0,1],{},[[1,0,-2],[0,1,-3],[-2,1,0],[7,-3,-5],[0,1,-16],[0,1,-17],[0,1,-18],[0,1,-19]],[1,1],None,400,True,78),  # line 2978
    '[77/45, 27/14, 275/7, 2/11, 49/2]': ('nd',[0,1],{},[[1,0,-1],[0,1,-16],[1,-1,6092],[1,0,-13],[1,0,-14]],[3,3],'88',400,False,158),  # line 2979
    '[77/90, 125/14, 44/5, 3/11, 5/2]': ('ndcv',[0,1],{},[[1,0,-2],[0,1,-1],[-1,2,-3],[2,-3,-1],[0,1,-30],[0,1,-31]],[1,1],None,400,False,248),  # line 2980
    '[77/90, 8/21, 9/2, 5/11, 35/3]': ('add',1,[[],['7','11/2','1/2'],[],[],['1','1']],42,[[209,111616],[210,112675],[211,113739],[212,114808]]),  # line 2981
    '[77/90, 8/21, 9/2, 5/11, 77/3]': ('add',1,[[],['6','9/2','1/2'],[],[],['1','1']],42,[[209,110776],[210,111831],[211,112891],[212,113956]]),  # line 2982
    '[77/90, 8/35, 275/2, 3/11, 2/5]': ('ndx',[1,2],{},[[1,0,-1],[0,1,-2],[-3,2,-1],[2,-1,-3],[1,0,-10],[1,0,-16],[1,0,-30],[1,0,-31]],[1,1],None,400,False,247),  # line 2983
    '[77/90, 9/2, 8/21, 5/11, 35/3]': ('add',1,[[],['7','11/2','1/2'],[],[],['1','1']],42,[[209,111616],[210,112675],[211,113739],[212,114808]]),  # line 2984
    '[77/90, 9/2, 8/21, 5/11, 77/3]': ('add',1,[[],['6','9/2','1/2'],[],[],['1','1']],42,[[209,110776],[210,111831],[211,112891],[212,113956]]),  # line 2985
    '[8/105, 5/6, 539/2, 3/7, 98/11]': ('ndx',[2,3,4],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-4],[0,-1,1,-2],[1,0,0,-4]],[1,1,1],None,400,True,77),  # line 2986
    '[8/105, 9/10, 77/2, 5/7, 98/11]': ('ndx',[0,1,2,4],{},[[1,0,0,0,-1],[0,1,0,0,-2],[0,0,1,0,-1],[0,0,0,1,-15],[0,0,-1,1,-34],[1,0,0,0,-5],[0,0,1,0,-4]],[1,1,1,1],None,64,True,110),  # line 2987
    '[8/15, 3/1078, 245/2, 11/5, 10/7]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[1,-3,5],[0,1,-5],[1,0,-12],[0,1,-8],[0,1,-20]],[1,1],None,400,False,206),  # line 2998
    '[8/15, 3/1078, 245/2, 11/5, 15/7]': ('ndcv',[2,3],{},[[1,0,-1],[0,1,-2],[-5,2,-4],[4,-1,-13],[1,0,-12],[1,0,-13],[1,0,-14]],[1,1],None,400,False,111),  # line 2999
    '[8/15, 3/1078, 35/2, 77/5, 15/7]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-1],[2,-5,6],[0,1,-4],[1,0,-10],[0,1,-7],[0,1,-13]],[2,6],'10',400,False,133),  # line 3000
    '[8/15, 3/14, 55/2, 7/5, 50/77]': ('nd',[0,4],{},[[1,0,-7],[0,1,-6],[1,0,-25],[1,0,-41],[1,0,-43],[1,0,-45],[1,0,-47]],[2,4],'40',400,False,839),  # line 3001
    '[8/15, 3/154, 35/2, 11/5, 20/7]': ('ndcv',[0,3],{},[[1,0,-7],[0,1,-1],[-1,2,0],[1,-1,-11],[1,0,-25]],[1,1],None,400,False,235),  # line 3002
    '[8/15, 3/154, 35/2, 11/5, 375/7]': ('ndcv',[0,3],{},[[1,0,-11],[0,1,-1],[-1,2,-17],[4,-3,-127]],[1,1],None,1000,False,375),  # line 3003
    '[8/15, 3/154, 35/2, 11/5, 90/7]': ('ndcv',[0,3],{},[[1,0,-7],[0,1,-1],[-1,3,-5],[2,-3,-14]],[1,1],None,400,False,52),  # line 3004
    '[8/15, 33/14, 12155/2, 7/11, 2/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-4,3,0,0,0],[2,-1,0,0,-2],[0,0,-1,1,0],[0,0,1,-1,0],[-2,2,-1,0,1],[2,-2,1,0,-1],[1,0,0,0,-4],[-1,1,0,0,-4]],[1,1,1,1],None,400,False,30),  # line 3005
    '[8/15, 33/14, 12155/2, 7/11, 3/221]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-3,2,0,0,0],[2,-1,0,0,-2],[0,0,-1,1,0],[0,0,1,-1,0],[-2,2,-1,0,1],[2,-2,1,0,-1],[-1,1,0,0,-3]],[1,1,1,1],None,400,False,46),  # line 3006
    '[8/15, 33/14, 55/2, 1547/11, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-3,2,0,0,0],[2,-1,0,0,-2],[0,0,-1,1,0],[0,0,1,-1,0],[-5,4,-1,0,2],[5,-4,1,0,-2],[-1,1,0,0,-3]],[1,1,1,1],None,400,False,67),  # line 3007
    '[8/15, 33/14, 715/2, 119/11, 2/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-4,3,0,0,0],[2,-1,0,0,-2],[1,-1,-1,1,0],[-1,1,1,-1,0],[-2,2,-1,0,1],[2,-2,1,0,-1],[1,0,0,0,-4],[-1,1,0,0,-4]],[1,1,1,1],None,400,False,43),  # line 3008
    '[8/15, 33/14, 715/2, 119/11, 3/221]': ('nd',[2,3,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-3,2,0,0,0],[2,-1,0,0,-2],[1,0,-2,1,0],[-1,0,2,-1,0],[-2,2,-1,0,1],[2,-2,1,0,-1],[-1,1,0,0,-3]],[1,1,1,1],None,400,False,67),  # line 3009
    '[8/15, 35/6, 3/5, 77/2, 3/7, 5/11]': ('val',1,4,{'2': 1},2,20,[3,3,2,2],268,None),  # line 3010
    '[8/15, 5/3, 21/10, 77/2, 5/7, 3/11]': ('val',2,4,{'1': 1},2,20,[3,3,2,2],268,None),  # line 3011
    '[8/3, 1/50, 3/14, 11/2, 35/11, 9/5]': ('mul',2,[[],[],[],[],['-49/15','169/15']],16,1,[[256,16257],[4096,262473]]),  # line 3012
    '[8/45, 33/14, 275/2, 7/11, 4/5]': ('nd',[0,1,2,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[1,-3,1,-1,4]],[1,1,1,1],None,1000,True,62),  # line 3013
    '[8/45, 33/14, 275/2, 7/11, 6/5]': ('ndxz',[1,2,3],{'0': 1},[[1,0,0,-1],[0,1,0,-213],[0,0,1,-205],[-53,1,0,0],[-51,0,1,0],[0,-7,8,0],[0,1,-1,0]],[12,1,1],'6',300,True,1339),  # line 3014
    '[8/45, 33/14, 275/2, 7/11, 9/5]': ('nd',[0,1,2,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-2],[1,-3,1,-1,3]],[1,1,1,1],None,1000,True,47),  # line 3015
    '[8/45, 33/14, 275/2, 7/11, 9/7]': ('nd',[1,2,3],{},[[1,0,0,-1],[0,1,0,-7],[0,0,1,-2],[0,-1,3,-6],[0,1,-1,-10]],[1,1,1],None,128,'all',48),  # line 3016
    '[8/45, 5/14, 429/2, 7/11, 4/91]': ('mul',2,[[],['7/3','32/3'],[],[],['0','32'],['-5/3','176/3']],4,1,[[16,2470],[64,9894],[256,39590],[1024,158374]]),  # line 3017
    '[8/45, 5/14, 99/2, 7/33, 4/7]': ('mul',2,[[],['7/3','128/3'],[],[],['0','32']],4,1,[[16,2470],[64,9894],[256,39590],[1024,158374]]),  # line 3018
    '[81/10, 1/21, 2/3, 77/2, 5/11, 4/7]': ('ndcv',[1,2],{},[[1,0,-1],[0,1,-1],[1,3,-32],[0,1,-4]],[3,1],'6',400,True,87),  # line 3019
    '[81/35, 25/66, 14/3, 11/7, 35/2]': ('ndcv',[0,1],{},[[1,0,-7],[0,1,-24],[-5,2,-13],[7,-2,-1]],[1,1],None,400,False,32),  # line 3021
    '[81/35, 5/66, 14/3, 11/7, 175/2]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-7],[-5,2,-16],[7,-2,0]],[1,1],None,400,False,47),  # line 3022
    '[81/35, 5/66, 14/3, 11/7, 245/2]': ('ndcv',[0,4],{'1': 7},[[1,0,-2],[0,1,-4],[-2,3,-15],[1,-1,-12],[8,-9,-6]],[1,1],None,1000,False,188),  # line 3023
    '[81/385, 7/15, 22/3, 5/11, 363/2]': ('ndx',[0,1,2,3],{},[[1,0,0,0,-6],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[1,0,-1,0,-16],[0,1,0,0,-5],[0,0,1,0,-4]],[1,1,1,1],None,400,True,117),  # line 3024
    '[88/105, 1/66, 5/2, 33/5, 28/11]': ('ndx',[2,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,0,1,3],[0,1,0,-4],[0,0,1,-4]],[1,1,1],None,1000,True,100),  # line 3025
    '[88/105, 33/26, 595/2, 13/11, 3/17]': ('nd',[2,3,4,6],{},[[1,0,0,0,-3],[0,1,0,0,-3],[0,0,1,0,-1],[0,0,0,1,-3],[-1,0,2,0,-3],[1,0,-1,0,-4],[-1,1,0,0,0],[1,-1,0,0,0],[0,0,2,-1,1],[0,0,-2,1,-1]],[1,1,1,1],None,400,False,36),  # line 3026
    '[88/315, 7/10, 33/2, 5/11, 4/5]': ('mul',2,[[],['7/3','62/3'],[],[],['0','62']],4,1,[[16,5615],[64,22479],[256,89935],[1024,359759]]),  # line 3027
    '[9/10, 1/1029, 55/3, 7/25, 2/11, 3/2]': ('ndx',[0,3],{},[[1,0,-2],[0,1,-1],[1,-3,1],[0,1,-12],[0,1,-13],[0,1,-14],[3,-1,-123]],[1,1],None,400,False,400),  # line 3029
    '[9/10, 1/126, 22/3, 7/2, 5/11, 10/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,3223),  # line 3059
    '[9/10, 1/126, 22/3, 7/2, 5/11, 15/7]': ('ndx',[3,4],{},[[1,0,-136],[0,1,-315],[-9,4,0],[5,-2,0]],[1,1],None,300,False,1990),  # line 3060
    '[9/10, 1/126, 22/3, 7/2, 5/11, 22/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,3236),  # line 3061
    '[9/10, 1/126, 22/3, 7/2, 5/11, 3/7]': ('ndx',[3,4],{},[[1,0,-15],[0,1,-271],[-8,1,0],[43,-1,0]],[1,1],None,300,False,2018),  # line 3062
    '[9/10, 1/126, 22/3, 7/2, 5/11, 9/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,3212),  # line 3063
    '[9/10, 1/147, 143/2, 22/3, 35/11, 2/13]': ('nd',[2,3,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[0,-1,3,-1],[0,1,0,-8],[0,1,0,-12],[0,1,0,-16],[4,-1,0,-16],[12,-3,0,-64],[0,1,0,-17],[0,1,0,-18],[12,-3,0,-74],[0,1,0,-19]],[1,1,1],None,1000,False,104),  # line 3064
    '[9/10, 1/147, 22/3, 143/2, 35/11, 2/13]': ('nd',[2,3,4,5],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-2],[1,-1,0,0,1],[-3,2,-1,3,-4]],[1,1,1,1],None,1000,False,98),  # line 3065
    '[9/10, 1/147, 55/3, 7/125, 2/11, 3/2]': ('ndx',[0,3],{},[[1,0,-3],[0,1,-1],[1,-2,-14],[0,1,-8],[0,1,-9],[2,-1,-82],[2,-1,-106]],[1,1],None,400,False,652),  # line 3066
    '[9/10, 1/588, 22/3, 7/2, 5/11, 3/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[1,0,-10]],[1,1],None,400,True,130),  # line 3125
    '[9/10, 1/84, 22/3, 7/2, 5/11, 10/7]': ('ndx',[3,4],{},[[1,0,-19],[0,1,-248],[-13,1,0],[22,-1,0]],[1,1],None,300,False,1357),  # line 3144
    '[9/10, 1/84, 22/3, 7/2, 5/11, 15/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,1160),  # line 3145
    '[9/10, 1/84, 22/3, 7/2, 5/11, 22/7]': ('ndx',[3,4],{},[[1,0,-70],[0,1,-149],[-2,1,0],[5,-2,0]],[1,1],None,300,False,770),  # line 3146
    '[9/10, 1/84, 22/3, 7/2, 5/11, 3/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,778),  # line 3147
    '[9/10, 1/84, 22/3, 7/2, 5/11, 33/7]': ('ndx',[3,4],{},[[1,0,-126],[0,1,-297],[-9,4,0],[5,-2,0]],[1,1],None,300,False,1534),  # line 3148
    '[9/10, 1/84, 22/3, 7/2, 5/11, 9/7]': ('nd',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,754),  # line 3149
    '[9/10, 1/882, 22/3, 7/2, 5/11, 3/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[0,1,-4],[1,0,-10],[-3,2,0],[-3,2,-10],[-3,2,-15]],[1,2],'2',400,False,382),  # line 3151
    '[9/10, 1/924, 14/3, 11/2, 5/7, 3/11]': ('nd',[4,3],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,3394),  # line 3152
    '[9/10, 1001/2, 68/21, 5/17, 15/143]': ('nd',[3,4,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-5],[0,0,1,0,-5],[0,0,0,1,-3],[-5,2,0,0,-3],[3,-1,0,0,-8],[0,-1,1,0,0],[0,1,-1,0,0],[-5,1,0,2,4],[5,-1,0,-2,-4]],[1,1,1,1],None,400,False,115),  # line 3153
    '[9/10, 1001/2, 68/21, 5/17, 51/143]': ('nd',[3,4,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-7,3,0,0,0],[3,-1,0,0,-8],[0,-1,1,0,0],[0,1,-1,0,0],[-5,1,0,2,4],[5,-1,0,-2,-4]],[1,1,1,1],None,400,False,69),  # line 3154
    '[9/10, 1001/2, 68/21, 5/187, 15/13]': ('nd',[3,4,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-6],[0,0,1,0,-5],[0,0,0,1,-3],[-2,1,0,0,-2],[7,-3,0,0,-13],[1,-1,0,1,0],[-1,1,0,-1,0],[-7,2,1,0,4],[7,-2,-1,0,-4]],[1,1,1,1],None,400,False,115),  # line 3155
    '[9/10, 1001/2, 68/231, 5/17, 15/13]': ('nd',[3,4,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-3],[0,0,1,0,-5],[0,0,0,1,-3],[-5,0,2,0,-3],[3,0,-1,0,-8],[-1,1,0,0,0],[1,-1,0,0,0],[-5,0,1,2,4],[5,0,-1,-2,-4]],[1,1,1,1],None,400,False,115),  # line 3156
    '[9/10, 1001/2, 68/231, 5/17, 51/13]': ('nd',[3,4,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-7,0,3,0,0],[3,0,-1,0,-8],[-1,1,0,0,0],[1,-1,0,0,0],[-5,0,1,2,4],[5,0,-1,-2,-4]],[1,1,1,1],None,400,False,69),  # line 3157
    '[9/10, 11/126, 22/3, 7/2, 5/11, 3/7]': ('ndx',[3,4],{},[[1,0,-70],[0,1,-149],[-2,1,0],[5,-2,0]],[1,1],None,300,False,754),  # line 3158
    '[9/10, 22/21, 2401/2, 5/11, 110/7]': ('ndx',[3,4],{},[[1,0,-9],[0,1,-3],[-1,3,-20],[2,-3,-23]],[1,1],None,400,True,79),  # line 3169
    '[9/10, 22/21, 2401/2, 5/11, 242/7]': ('ndx',[3,4],{},[[1,0,-7],[0,1,-2],[-1,3,-13],[2,-3,-16]],[1,1],None,400,True,47),  # line 3170
    '[9/10, 22/21, 2401/2, 5/11, 3/49]': ('ndx',[3,4],{},[[1,0,-5],[0,1,-1],[-1,3,-6],[2,-3,-9]],[1,1],None,400,True,30),  # line 3171
    '[9/10, 22/21, 2401/2, 5/11, 45/7]': ('ndx',[3,4],{},[[1,0,-11],[0,1,-4],[-1,3,-27],[2,-3,-30]],[1,1],None,400,True,108),  # line 3172
    '[9/10, 22/21, 2401/2, 5/11, 50/7]': ('ndx',[3,4],{},[[1,0,-11],[0,1,-4],[-1,3,-27],[2,-3,-30]],[1,1],None,400,True,111),  # line 3173
    '[9/10, 22/21, 2401/2, 5/11, 99/7]': ('ndx',[3,4],{},[[1,0,-9],[0,1,-3],[-1,3,-20],[2,-3,-23]],[1,1],None,400,True,76),  # line 3174
    '[9/10, 22/21, 31213/2, 5/11, 15/13]': ('ndx',[3,4,5],{},[[1,0,0,-9],[0,1,0,-3],[0,0,1,-2],[-2,3,1,7],[2,-3,-1,-7]],[1,1,1],None,400,'all',8),  # line 3175
    '[9/10, 22/21, 31213/2, 5/11, 33/13]': ('ndx',[3,4,5],{},[[1,0,0,-7],[0,1,0,-2],[0,0,1,-1],[-2,3,1,7],[2,-3,-1,-7]],[1,1,1],None,400,'all',4),  # line 3176
    '[9/10, 22/21, 75803/2, 5/11, 3/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,2,0,0,-1],[1,-1,0,0,-6],[0,0,-1,1,0],[0,0,1,-1,0],[-1,2,-1,0,4],[1,-2,1,0,-4],[-1,2,0,0,-12],[-1,2,0,0,-13]],[1,1,1,1],None,400,False,146),  # line 3177
    '[9/10, 25/1617, 14/3, 77/2, 6/7]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-1],[1,-3,2],[0,1,-5],[0,1,-7],[0,1,-15]],[1,1],None,400,False,152),  # line 3178
    '[9/10, 25/231, 98/3, 11/2, 12/11]': ('ndcv',[0,3],{},[[1,0,-979],[0,1,-12918],[-1,1,-28719]],[8,1],'a8',1000,False,43694),  # line 3179
    '[9/10, 44/147, 343/2, 5/11, 33/7]': ('ndx',[3,4],{},[[1,0,-6],[0,1,-2],[1,-1,-38],[0,1,-4],[0,1,-8],[0,1,-9]],[1,1],None,400,True,69),  # line 3184
    '[9/10, 44/147, 3773/2, 5/11, 2/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,2,-2],[1,-1,-4],[0,1,-8],[1,-1,-8],[1,-1,-10],[-1,4,-27]],[1,1],None,400,False,54),  # line 3185
    '[9/10, 44/147, 3773/2, 5/11, 3/5]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-1,3,-2],[1,-1,-4],[0,1,-4],[0,1,-7],[0,1,-10],[1,-1,-8],[-1,4,-30],[1,-1,-9]],[1,1],None,400,False,114),  # line 3186
    '[9/10, 44/147, 3773/2, 5/11, 3/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[-2,3,-2],[1,-1,-3],[1,0,-12],[0,1,-9]],[1,1],None,400,True,72),  # line 3187
    '[9/10, 44/21, 1547/2, 5/11, 15/221]': ('nd',[0,4,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-3],[0,0,1,0,-2],[0,0,0,1,-2],[0,0,-1,1,0],[0,0,1,-1,0],[-4,2,1,0,4],[4,-2,-1,0,-4],[1,0,0,0,-4],[0,1,0,0,-4],[0,1,0,0,-8],[2,-1,0,0,-10],[-1,2,0,0,0]],[1,1,1,1],None,400,False,96),  # line 3188
    '[9/10, 44/21, 1547/2, 5/11, 33/221]': ('nd',[3,4,5,6],{},[[1,0,0,0,-2],[0,1,0,0,-2],[0,0,1,0,-2],[0,0,0,1,-2],[-1,1,0,0,-2],[4,-3,0,0,-6],[0,0,-1,1,0],[0,0,1,-1,0],[-5,2,1,0,4],[5,-2,-1,0,-4]],[1,1,1,1],None,400,False,69),  # line 3189
    '[9/10, 44/21, 1547/2, 5/143, 15/17]': ('nd',[0,4,5,6],{},[[1,0,0,0,-3],[0,1,0,0,-3],[0,0,1,0,-3],[0,0,0,1,-2],[0,-1,1,0,0],[0,1,-1,0,0],[-4,2,0,1,4],[4,-2,0,-1,-4],[1,0,0,0,-4],[0,1,0,0,-4],[0,1,0,0,-8],[2,-1,0,0,-10],[-1,2,0,0,0]],[1,1,1,1],None,400,False,96),  # line 3190
    '[9/10, 49049/2, 34/21, 5/17, 3/143]': ('nd',[3,4,5,6],{},[[1,0,0,0,-5],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[-1,3,0,0,-2],[1,-1,0,0,-8],[0,-1,1,0,0],[0,1,-1,0,0],[-1,-1,0,2,4],[1,1,0,-2,-4]],[1,1,1,1],None,400,False,30),  # line 3191
    '[9/10, 55/21, 2/3, 7/11, 33/2, 3/49]': ('ndz',[0,3],{'2': 1,'4': 2},[[1,0,-1],[0,1,-1],[2,-1,0]],[1,1],None,1000,'all',24),  # line 3197
    '[9/10, 55/21, 22/3, 7/121, 3/2, 3/11]': ('ndxz',[0,4],{},[[1,0,-2],[-2,1,1],[4,-1,-2]],[1,1],None,1000,True,256),  # line 3198
    '[9/10, 77/2, 16/21, 5/7, 14/55]': ('nd',[0,1,3,4],{},[[1,0,0,0,-1],[0,1,0,0,-1],[0,0,1,0,-1],[0,0,0,1,-1],[0,0,-1,1,-5],[0,1,0,0,-6]],[3,1,3,1],'15e',400,True,33),  # line 3222
    '[9/10, 88/147, 343/2, 5/11, 3/7]': ('ndx',[3,4],{},[[1,0,-9],[0,1,-1],[1,-1,-58],[0,1,-4],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,True,120),  # line 3228
    '[9/140, 22/5, 25/33, 14/11, 55/2]': ('ndcv',[0,3],{},[[1,0,-3],[0,1,-2],[1,-3,3],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,126),  # line 3229
    '[9/140, 22/5, 50/33, 7/11, 25/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-2],[1,-3,2],[0,1,-4],[0,1,-6],[0,1,-8],[0,1,-9]],[1,1],None,400,False,125),  # line 3230
    '[9/140, 25/33, 22/5, 14/11, 55/2]': ('ndcv',[0,3],{},[[1,0,-3],[0,1,-2],[1,-3,3],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,126),  # line 3231
    '[9/140, 25/33, 44/5, 7/11, 55/2]': ('ndcv',[0,3],{},[[1,0,-2],[0,1,-2],[1,-3,-2],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,198),  # line 3232
    '[9/140, 44/5, 25/33, 7/11, 55/2]': ('ndcv',[0,3],{},[[1,0,-2],[0,1,-2],[1,-3,-2],[0,1,-5],[0,1,-8],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,198),  # line 3233
    '[9/140, 50/33, 22/5, 7/11, 25/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-2],[1,-3,2],[0,1,-4],[0,1,-6],[0,1,-8],[0,1,-9]],[1,1],None,400,False,125),  # line 3234
    '[9/140, 8/15, 77/2, 5/11, 4/7]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-1],[-4,3,-4],[3,-1,-22],[1,0,-25],[1,0,-26]],[1,1],None,400,False,329),  # line 3235
    '[9/140, 88/15, 25/2, 7/11, 3/5]': ('ndx',[2,4],{},[[1,0,-73],[0,1,-15],[0,1,-15],[1,-3,-28]],[1,1],None,3000,False,109),  # line 3236
    '[9/20, 1/42, 44/3, 7/2, 5/11, 3/7]': ('nd',[3,4],{},[[1,0,-2],[0,1,-2],[-1,1,-10],[1,0,-10],[3,-2,-24],[3,-2,-32],[3,-2,-35],[3,-2,-36]],[1,1],None,1000,False,1851),  # line 3239
    '[9/20, 245/33, 8/3, 11/7, 21/2]': ('ndx',[0,3],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,22),  # line 3244
    '[9/20, 539/5, 55/21, 2/11, 75/2]': ('mul',2,[['-2','60'],[],[],['0','30'],[]],3,1,[[9,3111],[27,9375],[81,28167],[243,84543]]),  # line 3245
    '[9/20, 55/21, 539/5, 2/11, 75/2]': ('mul',2,[['-2','60'],[],[],['0','30'],[]],3,1,[[9,3111],[27,9375],[81,28167],[243,84543]]),  # line 3246
    '[9/20, 55/21, 7546/5, 2/11, 5/2]': ('ndx',[0,3],{},[[1,0,-2],[0,1,-3],[-1,2,-14],[5,-3,0],[1,0,-10],[1,-1,-20],[1,-1,-21]],[1,1],None,400,False,424),  # line 3247
    '[9/20, 55/21, 88/3, 7/11, 15/2]': ('ndx',[0,4],{},[[1,0,-7],[0,1,-3],[-2,3,-1],[1,-1,-10]],[1,1],None,400,True,63),  # line 3248
    '[9/20, 55/21, 88/3, 7/11, 3/2]': ('ndx',[0,4],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4]],[1,1],None,400,True,22),  # line 3249
    '[9/20, 55/21, 88/3, 7/11, 9/2]': ('ndx',[0,4],{},[[1,0,-6],[0,1,-2],[-1,2,-4],[1,-1,-10]],[1,1],None,400,True,41),  # line 3250
    '[9/35, 1/150, 55/3, 2/5, 7/11, 3/2]': ('nd',[1,4],{},[[1,0,-1],[0,1,-1],[-1,1,-9]],[1,1],None,1000,False,637),  # line 3276
    '[9/35, 1/150, 55/3, 2/5, 7/11, 33/2]': ('ndx',[0,4],{},[[1,0,-10],[0,1,-152],[-9,4,0],[19,-1,0],[3,-1,-15],[3,-1,-19]],[1,1],None,300,False,1533),  # line 3277
    '[9/35, 1/150, 55/3, 2/5, 7/11, 35/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,760),  # line 3278
    '[9/35, 1/150, 55/3, 2/5, 7/11, 55/2]': ('nd',[1,4],{},[[1,0,-1],[0,1,-1],[-1,1,-9]],[1,1],None,1000,False,629),  # line 3279
    '[9/35, 1/150, 55/3, 2/5, 7/11, 9/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,753),  # line 3280
    '[9/35, 1/1650, 55/3, 2/5, 7/11, 3/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-101],[-8,1,0],[101,-1,0],[1,0,-5]],[1,1],None,300,False,2131),  # line 3281
    '[9/35, 1/180, 55/3, 2/5, 7/11, 3/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-1],[-5,3,-4],[6,-1,-1],[0,1,-4],[1,0,-10]],[1,1],None,400,True,117),  # line 3282
    '[9/35, 1/1815, 1/7, 154/3, 25/2, 7/5]': ('ndcv',[2,4],{},[[1,0,-4],[0,1,-1],[1,-3,-3],[1,0,-18],[1,0,-19],[1,0,-20]],[1,1],None,400,True,141),  # line 3283
    '[9/35, 1/1815, 154/3, 1/7, 25/2, 7/5]': ('ndcv',[2,4],{},[[1,0,-4],[0,1,-1],[1,-3,-3],[1,0,-18],[1,0,-19],[1,0,-20]],[1,1],None,400,True,141),  # line 3284
    '[9/35, 1/300, 55/3, 2/5, 7/11, 3/2]': ('ndx',[0,4],{},[[1,0,-1],[0,1,-1],[-2,1,3],[0,1,-4],[1,0,-10]],[1,1],None,400,True,129),  # line 3295
    '[9/35, 1/33, 11/169, 50/3, 13/5, 21/2]': ('nd',[0,2],{'5': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 3296
    '[9/35, 1/33, 50/3, 11/169, 13/5, 21/2]': ('nd',[0,2],{'5': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 3298
    '[9/35, 1/363, 10/3, 11/125, 7/2, 3/7]': ('ndx',[3,4],{},[[1,0,-3],[0,1,-1],[1,-2,-14],[0,1,-8],[0,1,-9],[2,-1,-82],[2,-1,-106]],[1,1],None,400,False,653),  # line 3299
    '[9/35, 1/3993, 10/3, 11/25, 7/2, 3/7]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-1],[1,-3,1],[0,1,-12],[0,1,-13],[0,1,-14],[3,-1,-123]],[1,1],None,400,False,401),  # line 3311
    '[9/35, 1/429, 50/3, 11/25, 273/2]': ('nd',[0,3,5],{'2': 2},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[-1,1,-3,3]],[1,1,1],None,1000,True,127),  # line 3314
    '[9/35, 1/4719, 110/3, 1/5, 91/2, 5/13]': ('ndxz',[3,4,5],{},[[1,0,0,-83],[0,1,0,0],[0,-1,0,2],[0,0,1,-151],[1,-27,0,0],[0,-51,1,0],[-5,0,3,0],[2,0,-1,0]],[1,1,1],None,300,True,1173),  # line 3344
    '[9/35, 1/5, 1/2541, 110/3, 49/2, 5/7]': ('ndcv',[3,4],{},[[1,0,-4],[0,1,-1],[1,-3,-3],[1,0,-18],[1,0,-19],[1,0,-20]],[1,1],None,400,True,141),  # line 3345
    '[9/35, 1/90, 55/3, 2/5, 7/11, 3/2]': ('nd',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,3247),  # line 3374
    '[9/35, 1/90, 55/3, 2/5, 7/11, 35/2]': ('ndx',[0,4],{},[[1,0,-102],[0,1,-202],[-9,5,0],[11,-4,0],[-21,11,-18],[-21,11,-42]],[1,1],None,300,False,1250),  # line 3375
    '[9/35, 1/90, 55/3, 2/5, 7/11, 55/2]': ('nd',[0,4],{},[[1,0,-1],[0,1,-2],[-2,1,-8],[1,0,-5],[3,-1,-12],[3,-1,-20]],[1,1],None,1000,False,3235),  # line 3376
    '[9/35, 1/90, 55/3, 2/5, 7/11, 9/2]': ('ndx',[0,4],{},[[1,0,-102],[0,1,-202],[-9,5,0],[11,-4,0],[-21,11,-18],[-21,11,-42]],[1,1],None,300,False,1241),  # line 3377
    '[9/35, 10/33, 14/3, 11/4, 3/7, 3/2]': ('ndxz',[0,3],{},[[1,0,-1],[0,1,-1],[-1,4,-2],[1,-2,1]],[1,1],None,400,True,256),  # line 3382
    '[9/35, 11/90, 55/3, 2/5, 7/11, 3/2]': ('nd',[1,4],{},[[1,0,-1],[0,1,-1],[-1,1,-9]],[1,1],None,1000,False,613),  # line 3402
    '[9/35, 13/121, 1/39, 50/3, 11/5, 21/2]': ('nd',[0,2],{'4': 1},[[1,0,-3],[0,1,-4],[-1,1,-10],[3,-2,-8]],[1,1],None,1000,False,173),  # line 3405
    '[9/35, 13/33, 5/3, 242/5, 7/13, 15/2]': ('nd',[0,3,4],{},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[2,0,-1,1],[0,0,1,-4],[0,0,1,-7],[0,0,1,-12],[0,0,1,-13],[0,0,1,-14]],[1,1,1],None,1000,False,80),  # line 3406
    '[9/35, 25/132, 14/3, 22/7, 21/2]': ('ndcv',[0,4],{},[[1,0,-3],[0,1,-2],[1,-3,3],[0,1,-5],[0,1,-7],[0,1,-15]],[1,1],None,400,False,244),  # line 3415
    '[9/35, 25/132, 28/3, 11/7, 21/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-2],[1,-3,-2],[0,1,-5],[0,1,-7],[0,1,-15]],[1,1],None,400,False,198),  # line 3416
    '[9/35, 25/1452, 14/3, 11/7, 35/2]': ('add',3,[['2','7/2','9/2'],[],[],[],['2','4']],10,[[49,73114],[50,76106],[51,79158],[52,82270]]),  # line 3417
    '[9/35, 25/1452, 14/3, 11/7, 9/2]': ('add',3,[['2','7/2','9/2'],[],[],[],['2','4']],10,[[49,69389],[50,72230],[51,75128],[52,78083]]),  # line 3418
    '[9/35, 25/363, 98/3, 11/49, 21/2]': ('ndx',[0,2,4],{},[[1,0,0,-18],[0,1,0,-5],[0,0,1,-3],[1,0,-1,-57],[0,0,1,-8],[0,0,1,-14],[0,0,1,-24],[0,0,1,-25],[0,0,1,-26],[0,0,1,-27],[0,0,1,-28],[0,0,1,-29]],[1,1,1],None,144,False,621),  # line 3423
    '[9/35, 25/66, 14/3, 11/7, 2695/2]': ('ndcv',[0,3],{},[[1,0,-4],[0,1,-4],[1,-1,-7],[1,-2,1],[0,1,-6],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,134),  # line 3424
    '[9/35, 25/66, 14/3, 11/7, 693/2]': ('ndcv',[0,3],{},[[1,0,-4],[0,1,-4],[1,-1,-7],[1,-2,1],[0,1,-6],[0,1,-12],[0,1,-13],[0,1,-14]],[1,1],None,400,False,129),  # line 3425
    '[9/35, 5/132, 28/3, 11/7, 105/2]': ('add',1,[['11','15/2','5/2'],[],[],['3','3'],[]],14,[[69,41422],[70,42617],[71,43829],[72,45058]]),  # line 3427
    '[9/35, 5/132, 28/3, 11/7, 27/2]': ('add',1,[['11','15/2','5/2'],[],[],['3','3'],[]],14,[[69,38936],[70,40060],[71,41200],[72,42356]]),  # line 3428
    '[9/35, 5/33, 14/3, 1573/2, 147/143]': ('mul',2,[[],[],[],['2','16'],['0','64'],['-5/3','176/3']],4,1,[[16,4003],[64,16035],[256,64163],[1024,256675]]),  # line 3431
    '[9/35, 5/66, 196/3, 11/7, 147/2]': ('ndcv',[0,1],{},[[1,0,-1],[0,1,-8],[-1,1,-8],[3,-2,-2]],[1,1],None,400,False,224),  # line 3434
    '[9/35, 5/66, 196/3, 11/7, 245/2]': ('ndx',[0,3],{},[[1,0,-433],[0,1,-320],[-2,3,0],[3,-4,0]],[1,1],None,300,False,1216),  # line 3435
    '[9/35, 5/66, 196/3, 11/7, 63/2]': ('nd',[0,3],{},[[1,0,-4],[0,1,-5],[-5,7,-35],[3,-4,9]],[1,1],None,1000,False,196),  # line 3436
    '[9/35, 5/66, 8/55, 847/2, 5/7]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-2],[-2,1,-2],[7,-3,-1],[1,0,-8],[1,0,-9],[1,0,-13],[1,0,-15]],[2,1],'2',400,False,56),  # line 3437
    '[9/35, 55/6, 16/5, 7/11, 605/2]': ('ndx',[0,4],{},[[1,0,-4],[0,1,-2],[-1,2,-2],[2,-3,-10]],[1,1],None,400,True,46),  # line 3445
    '[9/35, 55/6, 3773/3, 2/77, 15/2]': ('ndx',[0,3],{},[[1,0,-273],[0,1,-95],[-13,50,0],[7,-20,0]],[2,1],'2',300,False,1322),  # line 3446
    '[9/35, 65/33, 1274/3, 11/91, 15/2]': ('ndx',[0,2,5],{},[[1,0,0,-1],[0,1,0,-15],[0,0,1,-9],[-15,1,0,0],[68,-1,0,0],[-9,0,1,0],[42,0,-1,0],[0,-3,5,0],[0,2,-3,0]],[1,1,1],None,1000,False,48),  # line 3447
    '[9/385, 1/30, 98/3, 5/49, 99/2]': ('ndcv',[0,3,4],{},[[1,0,0,-1],[0,1,0,-2],[0,0,1,-1],[1,-1,0,3],[0,0,1,-4]],[1,1,1],None,400,True,65),  # line 3453
    '[9/385, 14/5, 125/6, 121/2, 10/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-5],[-4,3,-12],[5,-3,-6],[-5,4,-60]],[1,1],None,400,False,1861),  # line 3454
    '[9/385, 14/5, 175/33, 77/2, 55/7]': ('mul',3,[[],[],[],['-13','30'],['-1','6']],15,1,[[225,9817],[3375,147517],[50625,2213017]]),  # line 3455
    '[9/385, 14/5, 25/6, 1331/2, 10/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-8],[-3,2,-3],[2,-1,-5],[1,0,-14]],[1,1],None,1000,True,58),  # line 3456
    '[9/385, 25/6, 14/5, 1331/2, 10/11]': ('ndx',[3,4],{},[[1,0,-1],[0,1,-8],[-3,2,-3],[2,-1,-5],[1,0,-14]],[1,1],None,1000,True,58),  # line 3457
    '[9/385, 25/6, 98/5, 11/2, 20/11]': ('ndcv',[0,3],{},[[1,0,-3],[0,1,-2],[1,0,-4],[1,0,-6],[0,1,-5],[1,0,-8],[0,1,-7],[1,0,-12],[0,1,-10],[0,1,-14],[1,0,-14],[1,0,-27],[-5,6,-9],[1,0,-29]],[8,1],'a8',400,False,385),  # line 3458
    '[9/385, 275/21, 22/5, 77/2, 35/11]': ('mul',3,[[],[],[],['-1','6'],['-13','30']],15,1,[[225,9817],[3375,147517],[50625,2213017]]),  # line 3459
    '[9/385, 50/7, 49/6, 11/2, 28/11]': ('ndcv',[0,2],{},[[1,0,-3],[0,1,-2],[1,0,-4],[1,0,-6],[0,1,-8],[1,0,-8],[1,0,-12],[0,1,-14],[1,0,-14],[1,0,-27],[-5,6,-9],[1,0,-29]],[8,1],'a8',400,False,385),  # line 3460
    '[9/5, 1/539, 10/33, 7/9, 121/2, 5/11]': ('nd',[0,3],{},[[1,0,-2],[0,1,-1],[1,-1,-1]],[1,1],None,3000,'all',17),  # line 3461
    '[9/70, 1/3993, 25/3, 242/5, 21/2]': ('ndz',[0,4],{},[[1,0,-4],[0,1,-8],[2,-1,2],[0,1,-12],[0,1,-24],[0,1,-25],[0,1,-26]],[1,1],None,400,True,186),  # line 3466
    '[9/70, 1/3993, 4/3, 605/2, 21/5]': ('ndx',[2,4],{},[[1,0,-1],[0,1,-2],[2,-1,2],[0,1,-12],[0,1,-24],[0,1,-25],[0,1,-26]],[1,1],None,144,True,215),  # line 3467
    '[9/70, 11/5, 125/21, 28/11, 35/2]': ('mul',2,[['-34/7','8784/7'],[],[],['-2/7','2928/7'],[]],22,1,[[484,936325]]),  # line 3468
    '[9/70, 11/5, 50/21, 28/11, 35/2]': ('mul',3,[['-13','15'],[],[],['-1','3'],[]],15,1,[[225,4899],[3375,73749],[50625,1106499]]),  # line 3469
    '[9/70, 125/21, 11/5, 28/11, 35/2]': ('mul',2,[['-34/7','8784/7'],[],[],['-2/7','2928/7'],[]],22,1,[[484,936325]]),  # line 3470
    '[9/70, 125/21, 22/5, 14/11, 35/2]': ('mul',2,[['-34/7','8784/7'],[],[],['-2/7','2928/7'],[]],22,1,[[484,936325]]),  # line 3471
    '[9/70, 125/21, 44/5, 7/11, 35/2]': ('mul',2,[['-34/7','8784/7'],[],[],['-2/7','2928/7'],[]],22,1,[[484,936325]]),  # line 3472
    '[9/70, 130/33, 22627/2, 7/13, 3/17]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-5],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-6],[2,-1,0,0,-1],[-1,0,1,0,0],[1,0,-1,0,0],[2,-1,0,-1,4],[-2,1,0,1,-4],[0,-1,2,0,-12],[0,-1,2,0,-13]],[1,1,1,1],None,400,False,146),  # line 3473
    '[9/70, 1375/6, 2/5, 7/11, 275/2]': ('ndcv',[2,4],{},[[1,0,-2],[0,1,-1],[-1,2,-2],[2,-3,-3],[0,1,-12],[3,-4,-15],[0,1,-13],[0,1,-14]],[1,1],None,400,False,84),  # line 3474
    '[9/70, 17303/2, 170/33, 7/17, 3/13]': ('nd',[2,4,5,6],{},[[1,0,0,0,-1],[0,1,0,0,-5],[0,0,1,0,-1],[0,0,0,1,-1],[-1,1,0,0,-6],[2,-1,0,0,-1],[-1,0,0,1,0],[1,0,0,-1,0],[2,-1,-1,0,4],[-2,1,1,0,-4]],[1,1,1,1],None,400,False,30),  # line 3475
    '[9/70, 2/15, 16807/2, 5/7, 21/5]': ('nd',[3],{},[[1,-2407]],[1],None,1000,False,16424),  # line 3476
    '[9/70, 2/15, 16807/2, 5/7, 4/5]': ('nd',[3],{},[[1,-3332]],[1],None,1000,False,22346),  # line 3477
    '[9/70, 2/15, 16807/2, 5/7, 6/5]': ('nd',[3],{},[[1,-4080]],[1],None,1000,False,27676),  # line 3478
    '[9/70, 22/5, 125/21, 14/11, 35/2]': ('mul',2,[['-34/7','48/7'],[],[],['-2/7','16/7'],[]],22,1,[[484,5109],[10648,112557],[234256,2476413]]),  # line 3479
    '[9/70, 22/5, 25/21, 14/11, 35/2]': ('mul',3,[['-10','12'],[],[],['-1','3'],[]],11,1,[[121,2811],[1331,31125],[14641,342579]]),  # line 3480
    '[9/70, 22/5, 25/33, 7/11, 3025/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[1,-2,3],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,428),  # line 3481
    '[9/70, 22/5, 25/33, 7/11, 3993/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[1,-2,3],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,440),  # line 3482
    '[9/70, 22/5, 50/21, 14/11, 35/2]': ('mul',3,[['-13','15'],[],[],['-1','3'],[]],15,1,[[225,4899],[3375,73749],[50625,1106499]]),  # line 3483
    '[9/70, 22/5, 625/21, 7/11, 25/2]': ('ndcv',[0,1,4],{},[[1,0,0,-5],[0,1,0,-1],[0,0,1,-1],[1,0,-1,-4],[0,1,0,-4],[0,3,1,-25],[0,3,1,-26],[0,3,1,-27]],[1,1,1],None,400,False,52),  # line 3484
    '[9/70, 25/33, 22/5, 7/11, 3025/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[1,-2,3],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,428),  # line 3485
    '[9/70, 25/33, 22/5, 7/11, 3993/2]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-4],[1,-2,3],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,440),  # line 3486
    '[9/70, 25/33, 539/5, 2/11, 605/2]': ('ndx',[3,4],{},[[1,0,-2],[0,1,-3],[1,-1,-54],[0,1,-4],[0,1,-27],[0,1,-29]],[1,8],'a8',400,False,384),  # line 3487
    '[9/70, 25/6, 847/3, 4/11, 21/2]': ('mul',1,[[],[],[],['1','100'],['0','350']],7,1,[[49,28582],[343,200082],[2401,1400582]]),  # line 3488
    '[9/70, 275/2, 4/33, 7/11, 242/7]': ('ndcv',[2,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[0,1,-6],[1,0,-5],[0,1,-8],[0,1,-12],[0,1,-14],[0,1,-27],[1,0,-7],[1,0,-10],[1,0,-12],[6,-5,3],[0,1,-29]],[1,8],'a8',400,False,386),  # line 3489
    '[9/70, 275/7, 49/33, 2/11, 847/2]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-3],[1,-1,-54],[0,1,-4],[0,1,-27],[0,1,-29]],[1,8],'a8',400,False,384),  # line 3490
    '[9/70, 4/15, 2401/2, 5/49, 3/5]': ('ndx',[0,2],{},[[1,0,-2],[0,1,-1],[1,1,-19]],[1,1],None,128,'all',89),  # line 3491
    '[9/70, 4/15, 275/2, 7/605, 3/5]': ('ndcv',[2,4],{},[[1,0,-2],[0,1,-1],[-1,2,-6],[1,-1,-5],[0,1,-16],[4,-5,-20],[0,1,-17],[-1,2,-8],[0,1,-18],[4,-5,-22],[0,1,-19]],[1,1],None,400,False,147),  # line 3492
    '[9/70, 4/165, 539/2, 5/7, 21/5]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[-1,3,-8],[1,-2,-3],[0,1,-15],[0,1,-16],[0,1,-17]],[1,1],None,1000,True,169),  # line 3493
    '[9/70, 4/165, 539/2, 5/7, 9/5]': ('ndcv',[3,4],{},[[1,0,-2],[0,1,-1],[-1,3,-12],[1,-2,-3],[1,-2,-15]],[1,1],None,1000,False,91906),  # line 3494
    '[9/70, 4/165, 539/2, 65/7, 3/13]': ('ndx',[2,4,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-2],[-1,3,0,-11],[1,0,0,-13],[1,0,0,-19],[0,1,0,-15],[1,0,0,-30],[1,0,0,-31],[1,0,0,-32],[1,0,0,-33]],[1,1,1],None,3000,True,277),  # line 3495
    '[9/70, 4/165, 7007/2, 5/7, 3/13]': ('ndx',[3,4,5],{},[[1,0,0,-2],[0,1,0,-1],[0,0,1,-1],[-1,3,0,-11],[1,0,0,-4],[1,0,0,-13],[1,0,0,-19],[0,1,0,-15],[1,0,0,-30],[1,0,0,-31],[1,0,0,-32],[1,0,0,-33]],[1,1,1],None,3000,True,219),  # line 3496
    '[9/70, 4/33, 275/2, 7/11, 242/7]': ('ndcv',[2,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[0,1,-6],[1,0,-5],[0,1,-8],[0,1,-12],[0,1,-14],[0,1,-27],[1,0,-7],[1,0,-10],[1,0,-12],[6,-5,3],[0,1,-29]],[1,8],'a8',400,False,386),  # line 3497
    '[9/70, 4/33, 55/2, 7/11, 3993/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[1,-2,3],[0,1,-4],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,253),  # line 3498
    '[9/70, 4/33, 55/2, 7/11, 484/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[1,-2,3],[0,1,-4],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,246),  # line 3499
    '[9/70, 44/5, 125/21, 7/11, 35/2]': ('mul',2,[['-34/7','48/7'],[],[],['-2/7','16/7'],[]],22,1,[[484,5109],[10648,112557],[234256,2476413]]),  # line 3500
    '[9/70, 44/5, 25/21, 7/11, 35/2]': ('mul',3,[['-10','12'],[],[],['-1','3'],[]],11,1,[[121,2811],[1331,31125],[14641,342579]]),  # line 3501
    '[9/70, 44/5, 50/21, 7/11, 35/2]': ('mul',3,[['-13','15'],[],[],['-1','3'],[]],15,1,[[225,4899],[3375,73749],[50625,1106499]]),  # line 3502
    '[9/70, 50/21, 11/5, 28/11, 35/2]': ('mul',3,[['-13','15'],[],[],['-1','3'],[]],15,1,[[225,4899],[3375,73749],[50625,1106499]]),  # line 3503
    '[9/70, 50/21, 22/5, 14/11, 35/2]': ('mul',3,[['-13','15'],[],[],['-1','3'],[]],15,1,[[225,4899],[3375,73749],[50625,1106499]]),  # line 3504
    '[9/70, 50/21, 44/5, 7/11, 35/2]': ('mul',3,[['-13','15'],[],[],['-1','3'],[]],15,1,[[225,4899],[3375,73749],[50625,1106499]]),  # line 3505
    '[9/70, 55/2, 4/33, 7/11, 3993/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[1,-2,3],[0,1,-4],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,253),  # line 3506
    '[9/70, 55/2, 4/33, 7/11, 484/5]': ('ndcv',[2,4],{},[[1,0,-1],[0,1,-1],[1,-2,3],[0,1,-4],[0,1,-6],[0,1,-8],[0,1,-10],[0,1,-12],[0,1,-14],[0,1,-24],[0,1,-25],[0,1,-26],[0,1,-27],[0,1,-28],[0,1,-29]],[1,1],None,400,False,246),  # line 3507
    '[9/70, 55/2, 8/33, 49/11, 22/7]': ('ndx',[2,4],{},[[1,0,-1],[0,1,-1],[-2,3,-3],[1,-1,-1],[0,2,-25],[1,0,-16],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,True,85),  # line 3508
    '[9/70, 605/2, 2/33, 7/11, 8/35]': ('ndxz',[2,4],{},[[1,0,-123],[0,1,-126],[-1,1,-1],[1,-1,3]],[6,6],'40040000',300,True,1211),  # line 3509
    '[9/70, 625/21, 22/5, 7/11, 25/2]': ('ndcv',[0,1,4],{},[[1,0,0,-5],[0,1,0,-1],[0,0,1,-1],[1,0,-1,-4],[0,1,0,-4],[0,3,1,-25],[0,3,1,-26],[0,3,1,-27]],[1,1,1],None,400,False,52),  # line 3510
    '[9/70, 625/33, 22/5, 7/11, 33/2]': ('ndcv',[0,2],{},[[1,0,-7],[0,1,-24],[-5,2,-13],[7,-2,-1]],[1,1],None,400,False,32),  # line 3511
    '[9/70, 7/15, 32/7, 5/2, 21/5]': ('nd',[2],{},[[1,-3648]],[1],None,1000,False,28327),  # line 3512
    '[9/70, 7/15, 32/7, 5/2, 6/5]': ('ndx',[2],{},[[1,-2407]],[1],None,1000,False,18835),  # line 3513
    '[9/70, 7/15, 80/7, 5/2, 14/5]': ('ndx',[2,3],{},[[1,0,-1],[0,1,-2],[1,1,-16],[1,0,-3],[0,1,-5],[1,0,-25],[1,0,-29],[1,0,-36],[1,0,-40],[1,0,-66],[1,0,-67],[1,0,-68],[1,0,-69],[1,0,-70],[1,0,-71],[1,0,-72],[1,0,-73],[1,0,-74],[1,0,-75],[1,0,-76]],[1,1],None,400,False,620),  # line 3514
    '[9/70, 77/5, 125/33, 4/11, 55/2]': ('ndcv',[3,4],{},[[1,0,-1],[0,1,-2],[0,1,-4],[1,0,-5],[1,0,-9],[1,0,-16],[-5,8,-60],[1,0,-17],[1,0,-18],[1,0,-19]],[1,1],None,400,False,1109),  # line 3515
    '[9/70, 88/15, 25/2, 7/11, 22/5]': ('ndcv',[2,4],{},[[1,0,-3],[0,1,-1],[1,-3,-12],[0,1,-4],[0,1,-5],[0,1,-8],[0,1,-15]],[1,1],None,200,False,108),  # line 3516
    '[9/70, 88/15, 5/2, 7/11, 44/5]': ('ndcv',[0,4],{},[[1,0,-2],[0,1,-1],[1,0,-4],[0,1,-4],[0,1,-6],[1,0,-8],[0,1,-12],[3,-4,-15],[-1,3,-2],[0,1,-13],[0,1,-14]],[1,1],None,400,False,85),  # line 3517
    '[9/70, 968/15, 25/2, 7/11, 3/5]': ('ndcv',[0,4],{},[[1,0,-3],[0,1,-2],[-2,3,-6],[1,-1,-2],[0,1,-14]],[3,4],'44',400,False,75),  # line 3518
    '[9/8, 28/15, 1/33, 275/7, 21/2]': ('nd',[3,4],{'0': 1},[[1,0,-1],[0,1,-1],[1,-3,-10]],[1,1],None,3000,False,105),  # line 3519
    '[9/8, 28/15, 1/33, 55/7, 63/2]': ('add',3,[['1'],[],['4','3'],[],['4','6','3']],1,[[6,765],[7,981],[8,1224],[9,1494]]),  # line 3520
    '[9/8, 28/15, 1/363, 55/7, 21/2]': ('add',3,[['1'],[],['4','3'],[],['4','4','1']],2,[[11,1484],[12,1724],[13,1982],[14,2258]]),  # line 3521
    '[9/8, 308/15, 1/147, 5/11, 33/2]': ('add',3,[['2'],[],['5','3'],['1','1','1'],[]],2,[[11,1488],[12,1728],[13,1986],[14,2262]]),  # line 3522
    '[99/35, 1/39, 5/121, 10/3, 13/5, 21/2]': ('nd',[1,3,0],{'4': 1},[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1],[0,1,-1,-3],[0,0,1,-8],[0,0,1,-16],[0,4,-1,-63]],[1,1,1],None,1000,False,368),  # line 3530
    '[99/35, 25/44, 8/5, 7/3, 15/2]': ('ndx',[0,1],{},[[1,0,-3],[0,1,-1],[-1,2,-3],[1,-1,-4],[0,1,-8],[0,1,-30],[0,1,-31],[0,1,-32],[0,1,-33],[0,1,-34]],[1,1],None,400,True,240),  # line 3548
    '[99/35, 5/121, 1/39, 10/3, 13/5, 21/2]': ('ndxz',[0,2,4],{},[[1,0,0,-330],[0,1,0,-178],[0,0,1,0],[0,0,-1,1],[1,0,-165,0],[0,1,-89,0],[-1,2,0,0],[7,-12,0,0]],[1,1,1],None,300,True,2071),  # line 3558
    '[99/35, 5/132, 49/3, 2/7, 45/2]': ('ndcv',[0,4],{},[[1,0,-7],[0,1,-1],[1,-3,-8],[1,0,-24],[0,1,-8],[0,1,-9]],[1,1],None,400,True,247),  # line 3559
    '[99/35, 5/6, 176/5, 7/11, 55/2]': ('ndx',[0,4],{},[[1,0,-4],[0,1,-2],[-1,2,-2],[2,-3,-10]],[1,1],None,400,True,46),  # line 3560
    '[99/35, 5/6, 7/3, 2/11, 5/7, 15/2]': ('ndz',[1,4],{},[[0,1,-1],[-1,1,1],[2,-1,-2]],[1,1],None,1000,'all',3),  # line 3561
    '[99/35, 5/6, 7/3, 2/11, 5/7, 45/2]': ('ndxz',[3,4],{},[[1,0,-3],[-1,1,1],[2,-1,-2]],[1,1],None,1000,'all',14),  # line 3562
    '[99/35, 5/6, 7/3, 2/11, 6/7, 15/2]': ('ndz',[1,4],{},[[0,1,-1],[-1,1,1],[2,-1,-2]],[1,1],None,1000,'all',3),  # line 3563
    '[99/35, 5/66, 26411/3, 2/7, 3/2]': ('ndx',[0,2],{},[[1,0,-2],[0,1,-1],[1,0,-25],[1,0,-30],[1,0,-35],[1,0,-36]],[1,1],None,144,True,1848),  # line 3564
    '[99/35, 5/66, 3773/3, 2/7, 9/2]': ('nd',[3,4],{},[[1,0,-6],[0,1,-2],[-1,2,0],[2,-3,-10],[2,-3,-40]],[1,1],None,400,False,363),  # line 3565
    '[99/35, 5/66, 9317/3, 2/121, 3/2]': ('ndcv',[0,2],{},[[1,0,-1],[0,1,-14]],[1,1],None,400,False,408),  # line 3566
    '[99/35, 7/5, 55/21, 2/3, 7/11, 35/2]': ('val',3,0,{'2': 1},4,20,[2,2,1,1],127,None),  # line 3568
    '[99/35, 77/15, 5/7, 2/3, 5/11, 35/2]': ('val',2,0,{'3': 1},4,20,[2,2,1,1],127,None),  # line 3570
    '[99/70, 125/21, 22/3, 7/11, 15/2]': ('ndx',[0,4],{},[[1,0,-2],[0,1,-3],[-2,1,0],[7,-3,-7],[1,0,-15],[1,0,-16]],[1,1],None,400,False,148),  # line 3571
    '[99/70, 125/77, 4/11, 7/3, 33/2]': ('ndx',[0,1,4],{},[[1,0,0,-2],[0,1,0,-4],[0,0,1,-1],[-5,3,0,-1],[2,-1,0,-1],[0,0,-1,1],[0,0,1,-1],[0,1,0,-20],[1,0,0,-12],[-4,3,0,-18],[1,0,0,-13]],[1,1,1],None,400,False,171),  # line 3572
    '[99/70, 5/66, 49/3, 2/7, 45/2]': ('ndcv',[3,4],{},[[1,0,-6],[0,1,-1],[0,1,-4],[0,1,-6],[0,1,-8],[2,-3,-40],[0,1,-9],[1,0,-34],[1,0,-35],[1,0,-36]],[1,1],None,400,False,547),  # line 3573
    '[99/70, 7/165, 4/3, 5/2, 63/5]': ('ndcv',[0,4],{},[[1,0,-6],[0,1,-1],[0,1,-4],[0,1,-6],[1,0,-8],[0,1,-8],[2,-3,-10],[2,-3,-18],[2,-3,-40],[0,1,-9],[1,0,-34],[1,0,-35],[1,0,-36]],[1,1],None,400,False,548),  # line 3574
    '[99/70, 8/15, 25/2, 7/11, 21/5]': ('add',1,[[],[],['13','29/2','7/2'],[],['1','1']],24,[[119,65821],[120,66914],[121,68016],[122,69127]]),  # line 3575
    '[99/70, 8/15, 25/2, 7/11, 22/5]': ('add',1,[[],[],['3','9/2','7/2'],[],['1','1']],24,[[119,64501],[120,65583],[121,66674],[122,67774]]),  # line 3576
    '[99/70, 8/15, 25/2, 7/11, 33/5]': ('add',1,[[],[],['6','15/2','7/2'],[],['1','1']],24,[[119,64861],[120,65946],[121,67040],[122,68143]]),  # line 3577
    '[99/70, 8/15, 275/2, 7/11, 3/7]': ('ndx',[2,4],{},[[1,0,-2],[0,1,-1],[0,1,-4],[0,1,-5],[1,0,-5],[0,1,-8],[1,0,-9],[0,1,-15],[3,-4,-6],[3,-4,-9],[-1,3,-10]],[1,3],'1',400,False,31),  # line 3578
    '[99/70, 8/55, 25/2, 7/3, 33/5]': ('ndcv',[1,2],{},[[1,0,-1],[0,1,-6],[-2,1,-8],[7,-2,-5],[1,0,-12],[1,0,-13],[1,0,-14]],[1,1],None,400,False,76),  # line 3579
    '[99/70, 8/55, 25/2, 7/3, 6/5]': ('ndcv',[1,2],{},[[1,0,-1],[0,1,-3],[-5,3,-4],[2,-1,-1],[1,0,-8],[1,0,-15],[2,-1,-3],[2,-1,-6],[2,-1,-7]],[1,1],None,400,False,2529),  # line 3580
}

if __name__ == '__main__':
    holdouts = parse_file('holdout/sz24_3580.txt')
    print(f'running sz24_progress on {len(holdouts)} holdouts')
    print()
    holdouts2 = []
    for F in holdouts:
        result = sz24_progress(F)
        if result is not None:
            print(f'{unparse_line(F)}, NON-HALT: {result}')
        else:
            holdouts2.append(F)
    print()
    print(f'{len(holdouts2)} holdouts remaining')
    print()
    for F in holdouts2:
        print(unparse_line(F))
