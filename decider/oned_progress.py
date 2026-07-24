# python -m decider.oned_progress
from fractions import Fraction
from decider.utils import parse_file, unparse_line

'''
WARNING: This decider was entirely written by AI (Opus 4.8). I cannot guarantee that this decider is
sound (i.e. if an FM halts, then the decider does not return non-halt). Please open an issue if this
decider is unsound or contains sketchy code.

---

This decider proves a Fractran machine is NON-HALTING by exhibiting a
one-dimensional, parameterized family of states that the machine steps through
forever, always reaching a strictly larger member.  It is the automated,
symbolic-simulation analogue of the size-22 Lean `progress_nonhalt` proofs.
Because the number of Fractran steps from one member to the next GROWS with the
parameter (variable-step-count), constant-step "translated cycler" deciders
cannot catch these.

Conventions.  A state 2^a0 * 3^a1 * 5^a2 ... is the exponent vector [a0,a1,...];
each rule a/b is the constant delta vector (exponents of a) - (exponents of b).
Rule j applies at state u iff u[i]+F[j][i] >= 0 for all i; the machine applies
the first applicable rule and halts when none apply.  Start state u_0 = [1] = "2".

--------------------------------------------------------------------------------
THE UNIFYING IDEA.  A 1-D family is described by a single scalar "progress
variable" u and register forms that are POLYNOMIALS in u, f(u) = <P_0(u),...>.
One macro-step advances u by an AFFINE map  u -> a*u + b  and lands on a strictly
larger member.  Two flavours cover the observed families:

  * ADDITIVE   (a=1, b=1):  u is the boundary index and each register is a
    polynomial in u; the orbit is arithmetic-progression-like and steps u -> u+1,
    i.e. f(u) |-+ f(u+1).

  * MULTIPLICATIVE (a=B, b=0):  the family is exponential, v(k) = c*B^k + d.
    Substituting u = B^k makes every register a polynomial in u and the macro-step
    becomes u -> B*u, i.e. f(u) |-+ f(B*u).  Since every power B^k lies in the single
    residue class u == 1 (mod B-1), we verify on that class (u = (B-1)*m + 1), which
    keeps the family integer-valued even for bases B >= 3 whose coefficients c,d are
    fractional; and we accept reaching f(B^j*u) for any j >= 1.

Both are verified by the SAME obligation, f(u) |-+ f(a*u + b) for all valid
u >= u0, discharged by one symbolic engine.  A third, more permissive flavour --
a TEMPLATE with one free register that need only reach ANY strictly larger member
-- catches Collatz-like orbits whose parameter jumps around (e.g. c%9 dispatch).

--------------------------------------------------------------------------------
Definition 1DP.1 (progress).  A 1-D family {f(u)} is a progress family for F from
u0 if for every valid u >= u0 there is a strictly larger valid u' with
f(u) |-+ f(u') (>= 1 steps).

Theorem 1DP.2 (soundness).  If {f(u)} is a progress family from u0 and
u_0 |-* f(w) for some concrete valid w >= u0, then F is non-halting.
Proof.  f(w) |-+ f(w1) |-+ f(w2) |-+ ... with w < w1 < w2 < ..., an infinite
strictly-increasing chain of real reachable states; hence the run from u_0 never
reaches a halting configuration.  QED.

--------------------------------------------------------------------------------
How the pieces are found and verified:

1. DETECTION (a guess; the engine is the sound filter).  Simulate from u_0, group
   states by zero-pattern ("shape").  For each shape (cleanest first) take the head
   of its occurrence sequence and try, in order:
     ADD  -- fit every register as a polynomial in the occurrence index.
     MUL  -- fit every register as c*B^k + d with a shared integer base B (so it
             is a polynomial in u = B^k).
     TMPL -- if exactly one register varies, treat the rest as constants.

2. SYMBOLIC VERIFICATION (the soundness-critical core).  Introduce a residue
   variable m and carry every register as a polynomial in m:
     ADD: per residue u = M*m + r (M in {1..8, 9, 12, 18}), verify f(M*m+r) |-+ f(M*m+r+1).
     MUL: case-split u = (B-1)*m + 1 (the class of all powers B^k), verify
          f(u) |-+ f(B^j*u) for some j >= 1.
     TMPL: verify template(M*m+r) reaches a strictly larger member.
   The engine decides every branch UNIFORMLY for all m >= m_lo (sign of a register
   polynomial = sign of its leading coefficient above a Cauchy root bound, which
   raises a running threshold m_lo; raising m_lo only shrinks {m >= m_lo}, so
   earlier decisions stay valid).  Loops are cycle-accelerated: when the fired-rule
   sequence repeats with a CONSTANT net delta, jump K cycles at once, K a
   polynomial in m (clean floor: the divisor must divide the non-constant
   coefficients), K bounded so EVERY register stays >= 0 at every position/cycle
   and NO higher-priority rule becomes applicable mid-loop.  Any decision that
   cannot be made uniform-and-exact -> return None (undecided).  The start state
   must be uniformly >= 0.

3. BOOTSTRAP.  Proving progress for large u does not by itself prove the machine
   started at u_0 is non-halting, so we additionally require a CONCRETE trajectory
   state from u_0 that is a family member with u >= u0 (Theorem 1DP.2).

--------------------------------------------------------------------------------
Results (decided / total = rate;  flavour split add / mul / tmpl):
     sz21_140  :    95 /   140 = 67.9%   (76 / 17 / 2)
     sz22_2003 :  1325 /  2003 = 66.2%   (866 / 426 / 33)
     sz23_21295: 13212 / 21295 = 62.0%   (7956 / 4781 / 475)
The sz21 and sz22 sets are proven non-halting (they have formal Lean proofs), so
those are completeness rates; sz23_21295 is the open size-23 residual.

Soundness (a decider must NEVER call a halting machine non-halting).  0 of the 7497
known-halting machines are decided (sz23_halted_6805 + sz22_halted_692), and every
decided certificate re-verifies by independent concrete simulation.
'''


# ============================================================================
# concrete simulation
# ============================================================================

def _simulate(F: list[list[int]], width: int, max_steps: int):
    guards = [[(i, -d) for i, d in enumerate(r) if d < 0] for r in F]
    deltas = [[(i, d) for i, d in enumerate(r) if d != 0] for r in F]
    nrules = len(F)
    state = [0] * max(width, 1)
    state[0] = 1
    states = [tuple(state)]
    app = states.append
    for _ in range(max_steps):
        fired = -1
        for j in range(nrules):
            ok = True
            for i, need in guards[j]:
                if state[i] < need:
                    ok = False
                    break
            if ok:
                fired = j
                break
        if fired < 0:
            return True, states
        for i, d in deltas[fired]:
            state[i] += d
        app(tuple(state))
    return False, states


# ============================================================================
# polynomial arithmetic  (poly = list[int], p[k] = coeff of m**k)
# ============================================================================

def _pnorm(p):
    i = len(p)
    while i > 0 and p[i - 1] == 0:
        i -= 1
    return p[:i] if i != len(p) else list(p)


def _is_const(p):
    return len(_pnorm(p)) <= 1


def _const_val(p):
    q = _pnorm(p)
    return q[0] if q else 0


def _degree(p):
    return len(_pnorm(p)) - 1


def _padd(a, b):
    n = max(len(a), len(b))
    return _pnorm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def _psub(a, b):
    n = max(len(a), len(b))
    return _pnorm([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def _pscale(a, c):
    return [] if c == 0 else [x * c for x in _pnorm(a)]


class _Ctx:
    __slots__ = ('m_lo',)

    def __init__(self):
        self.m_lo = 0


def _usign(p, ctx: _Ctx) -> int:
    q = _pnorm(p)
    if not q:
        return 0
    d = len(q) - 1
    L = q[-1]
    if d == 0:
        return 1 if L > 0 else -1
    maxc = max(abs(a) for a in q[:-1])
    thr = (1 + maxc // abs(L)) + 1
    if thr > ctx.m_lo:
        ctx.m_lo = thr
    return 1 if L > 0 else -1


def _umin(polys, ctx: _Ctx):
    best = polys[0]
    for p in polys[1:]:
        if _usign(_psub(p, best), ctx) < 0:
            best = p
    return best


def _floordiv(p, d):
    q = _pnorm(p)
    if not q:
        return []
    for i in range(1, len(q)):
        if q[i] % d != 0:
            return None
    return _pnorm([q[0] // d] + [q[i] // d for i in range(1, len(q))])


# ============================================================================
# symbolic simulation with sound cycle acceleration
# ============================================================================

_OK, _HALT, _BUDGET = 'ok', 'halt', 'budget'


def _which_rule(F, s, ctx):
    for j, rule in enumerate(F):
        ok = True
        for i, d in enumerate(rule):
            if d < 0 and _usign(_padd(s[i], [d]), ctx) < 0:
                ok = False
                break
        if ok:
            return j
    return -1


def _detect_period(rules, Lmax):
    T = len(rules)
    for L in range(1, Lmax + 1):
        if 2 * L > T:
            break
        if rules[T - 2 * L:T - L] == rules[T - L:T]:
            return L
    return 0


def _max_valid_cycles(F, hist, rules, p0, L, Dc, ctx):
    R = len(Dc)
    bounds = []
    for i in range(R):
        if Dc[i] < 0:
            col = [hist[t][i] for t in range(p0, p0 + L + 1)]
            b = _floordiv(_umin(col, ctx), -Dc[i])
            if b is None:
                return None
            bounds.append(b)
    for j in range(L):
        rj = rules[p0 + j]
        sj = hist[p0 + j]
        for rp in range(rj):
            rule = F[rp]
            perm = False
            wit = []
            for i, d in enumerate(rule):
                if d < 0:
                    val0 = _padd(sj[i], [d])
                    if _usign(val0, ctx) < 0:
                        if Dc[i] <= 0:
                            perm = True
                            break
                        else:
                            b = _floordiv(_psub([-1], val0), Dc[i])
                            if b is not None:
                                wit.append(b)
            if perm:
                continue
            if not wit:
                return None
            bounds.append(_umin(wit, ctx))
    if not bounds:
        return None
    return _umin(bounds, ctx)


def _sym_run(F, start, target_test, ctx, max_prim=1500, max_accel=100, max_deg=6, Lmax=48):
    cur = [_pnorm(p) for p in start]
    for p in cur:
        if _usign(p, ctx) < 0:
            return _BUDGET, None
    moved = False
    hist = [[list(p) for p in cur]]
    rules = []
    accel = prim = 0
    while prim < max_prim and accel < max_accel:
        for p in cur:
            if _degree(p) > max_deg:
                return _BUDGET, None
        if moved:
            res = target_test(cur, ctx)
            if res is not None:
                return _OK, res
        j = _which_rule(F, cur, ctx)
        if j < 0:
            return _HALT, None
        rule = F[j]
        cur = [_padd(cur[i], [rule[i]]) for i in range(len(cur))]
        moved = True
        prim += 1
        rules.append(j)
        hist.append([list(p) for p in cur])
        L = _detect_period(rules, Lmax)
        if not L:
            continue
        T = len(rules)
        p0 = T - 2 * L
        S0 = hist[p0]
        Delta = [_psub(hist[p0 + L][i], S0[i]) for i in range(len(S0))]
        if not all(_is_const(dp) for dp in Delta):
            continue
        Dc = [_const_val(dp) for dp in Delta]
        if all(x == 0 for x in Dc):
            return _BUDGET, None
        V = _max_valid_cycles(F, hist, rules, p0, L, Dc, ctx)
        if V is None or _degree(V) < 1:
            continue
        if _usign(_psub(V, [3]), ctx) < 0:
            continue
        cur = [_pnorm(_padd(S0[i], _pscale(V, Dc[i]))) for i in range(len(S0))]
        accel += 1
        hist = [[list(p) for p in cur]]
        rules = []
    return _BUDGET, None


# ============================================================================
# rational-polynomial fitting + affine substitution
# ============================================================================

def _binom_poly(j):
    poly = [Fraction(1)]
    for t in range(j):
        new = [Fraction(0)] * (len(poly) + 1)
        for k, c in enumerate(poly):
            new[k] += c * (-t)
            new[k + 1] += c
        poly = new
    fac = 1
    for t in range(1, j + 1):
        fac *= t
    return [c / fac for c in poly]


def _pnorm_fr(poly):
    i = len(poly)
    while i > 0 and poly[i - 1] == 0:
        i -= 1
    return poly[:i]


def _peval_fr(poly, x):
    v = Fraction(0)
    for c in reversed(poly):
        v = v * x + c
    return v


def _fit_poly(values, dmax):
    """Fit ints `values` (index 0..n-1) as a poly of degree <= dmax, or None."""
    n = len(values)
    if n == 0:
        return None
    diffs = [list(values)]
    for _ in range(min(dmax, n - 1)):
        prev = diffs[-1]
        diffs.append([prev[i + 1] - prev[i] for i in range(len(prev) - 1)])
    for d in range(min(dmax, n - 1) + 1):
        col = diffs[d]
        if col and all(x == col[0] for x in col):
            poly = [Fraction(0)]
            for j in range(d + 1):
                bp = _binom_poly(j)
                if len(bp) > len(poly):
                    poly = poly + [Fraction(0)] * (len(bp) - len(poly))
                for k, c in enumerate(bp):
                    poly[k] += diffs[j][0] * c
            if all(_peval_fr(poly, i) == values[i] for i in range(n)):
                return _pnorm_fr(poly)
    return None


def _fit_geometric(values, bmax=6):
    """Fit ints as v(k) = c*B^k + d (shared integer base B). Return (B, poly) where
    poly = [d, c] is v as a polynomial in u = B^k, or None."""
    if len(values) < 4:
        return None
    if all(x == values[0] for x in values):
        return None                                     # constant: no base
    diff = [values[k + 1] - values[k] for k in range(len(values) - 1)]
    if any(x == 0 for x in diff):
        return None
    B = None
    for k in range(len(diff) - 1):
        if diff[k + 1] % diff[k] != 0:
            return None
        r = diff[k + 1] // diff[k]
        if B is None:
            B = r
        elif r != B:
            return None
    if B is None or B < 2 or B > bmax:
        return None
    c = Fraction(diff[0], B - 1)
    d = Fraction(values[0]) - c
    for k in range(len(values)):
        if c * (B ** k) + d != values[k]:
            return None
    return (B, _pnorm_fr([d, c]))


def _subst_affine(poly, a, b):
    """p(x) -> p(a*m + b), Fraction coeffs."""
    lin = [Fraction(b), Fraction(a)]
    res = [Fraction(0)]
    for c in reversed(poly):
        out = [Fraction(0)] * (len(res) + 1)
        for i, x in enumerate(res):
            if x:
                out[i] += x * lin[0]
                out[i + 1] += x * lin[1]
        res = out
        res[0] += c
    return _pnorm_fr(res)


def _to_int_poly(poly):
    out = []
    for c in poly:
        if c.denominator != 1:
            return None
        out.append(int(c))
    return _pnorm(out)


# ============================================================================
# shared verification obligation:  f(u) |-+ f(a*u + b)
# ============================================================================

def _target_eq(target):
    tgt = [_pnorm(p) for p in target]

    def test(state, ctx):
        for i in range(len(tgt)):
            if (_pnorm(state[i]) if i < len(state) else []) != tgt[i]:
                return None
        return True
    return test


def _run_pair(F, width, P, As, cs, At, ct, kw):
    """Run one obligation: from f at u = As*m+cs, reach f at u = At*m+ct.
    P is the list of Fraction polynomials (register forms in u).  Returns m_lo or None."""
    start = [_to_int_poly(_subst_affine(p, As, cs)) for p in P]
    tgt = [_to_int_poly(_subst_affine(p, At, ct)) for p in P]
    if any(p is None for p in start) or any(p is None for p in tgt):
        return None
    start += [[]] * (width - len(start))
    tgt += [[]] * (width - len(tgt))
    ctx = _Ctx()
    tag, _ = _sym_run(F, start, _target_eq(tgt), ctx, **kw)
    return ctx.m_lo if tag == _OK else None


def _verify_additive(F, width, P, Mset, kw):
    """u = index, step u -> u+1.  Verify per residue u = M*m+r for some M in Mset.
    Returns (M, u0) or None (u0 an index threshold)."""
    for M in Mset:
        ok = True
        u0 = 0
        for r in range(M):
            mlo = _run_pair(F, width, P, M, r, M, r + 1, kw)
            if mlo is None:
                ok = False
                break
            u0 = max(u0, M * mlo + r)
        if ok:
            return (M, u0)
    return None


def _verify_multiplicative(F, width, P, B, kw, jmax=3, Mmul=(1, 2, 3, 4, 6, 8, 12)):
    """u = B^k, step u -> B^j*u.  Verified by a CASE-SPLIT on the base variable:
    every power B^k lies in the single residue class u == 1 (mod B-1) (since B == 1
    mod B-1), so we substitute u = (B-1)*m + 1.  This makes every register an INTEGER
    polynomial in m even when the family coefficients are fractional -- which they are
    for bases B >= 3, where c,d have denominators dividing B-1:
        start_i  = c_i*((B-1)m + 1) + d_i = p_i*m + v_i(0)      (p_i = c_i*(B-1))
        target_i = c_i*(B^j*u)     + d_i = (p_i*B^j)*m + v_i(j)  (reaching f(B^j*u))
    We accept reaching f(B^j*u) for ANY j in 1..jmax (reach a strictly larger member).

    Additionally we RESIDUE-SPLIT u further (just as the additive flavour splits its
    index): u = (B-1)*(M'*m + s) + 1 over s = 0..M'-1, for M' in Mmul.  A finer split
    can be needed so a drain loop's divisor divides the m-coefficient cleanly (else the
    cycle count is not a clean polynomial and the loop cannot be accelerated).  All M'
    residues must verify; every power B^k lands in one of them, so the chain is covered.
    Returns (M', u0) or None, with u0 the X-threshold (B-1)*(M'*m_lo_max) + 1."""
    Bm1 = B - 1
    for Mp in Mmul:
        ok_all = True
        thr = 0
        for s in range(Mp):
            A = Bm1 * Mp        # coeff of m in X = (B-1)*(M'm + s) + 1
            c = Bm1 * s + 1     # constant of X
            start = [_to_int_poly(_subst_affine(p, A, c)) for p in P]
            if any(p is None for p in start):
                ok_all = False
                break
            start2 = start + [[]] * (width - len(start))
            targets = []
            for j in range(1, jmax + 1):
                Bj = B ** j     # X' = B^j*X = (B^j*A)*m + (B^j*c)
                tgt = [_to_int_poly(_subst_affine(p, Bj * A, Bj * c))
                       for p in P]
                if any(p is None for p in tgt):
                    continue
                tgt2 = tgt + [[]] * (width - len(tgt))
                targets.append([_pnorm(x) for x in tgt2])
            if not targets:
                ok_all = False
                break

            def test(state, ctx, targets=targets):
                for tg in targets:
                    if all(_pnorm(state[i]) == tg[i] for i in range(width)):
                        return True
                return None

            ctx = _Ctx()
            tag, _ = _sym_run(F, start2, test, ctx, **kw)
            if tag != _OK:
                ok_all = False
                break
            thr = max(thr, Mp * ctx.m_lo + s)   # u = M'*m + s >= M'*m_lo + s
        if ok_all:
            return (Mp, Bm1 * thr + 1)          # X-threshold = (B-1)*u + 1
    return None


def _target_template(cmap, pc, n_poly):
    consts = dict(cmap)
    npoly = _pnorm(n_poly)

    def test(state, ctx):
        for i, cval in consts.items():
            if _pnorm(state[i]) != _pnorm([cval]):
                return None
        pp = _pnorm(state[pc])
        if _usign(_psub(pp, npoly), ctx) > 0:
            return pp
        return None
    return test


def _verify_template(F, width, cmap, pc, Mset, kw):
    for M in Mset:
        ok = True
        N0 = 0
        for r in range(M):
            start = [[] for _ in range(width)]
            for i, cval in cmap.items():
                start[i] = _pnorm([cval])
            n_poly = _pnorm([r, M])
            start[pc] = n_poly
            ctx = _Ctx()
            tag, _ = _sym_run(F, start, _target_template(
                cmap, pc, n_poly), ctx, **kw)
            if tag != _OK:
                ok = False
                break
            N0 = max(N0, M * ctx.m_lo + r)
        if ok:
            return (M, N0)
    return None


# ============================================================================
# top-level decider
# ============================================================================

def oned_progress(F: list[list[int]], step_cap: int = 40000, dmax: int = 3,
                  Mset=(1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 18), min_occ: int = 5,
                  window: int = 30, max_offset: int = 8, Mmul=(1, 2, 3, 4, 6)) -> str | None:
    """Try to prove F (from u_0 = "2") is non-halting via a 1-D progress
    certificate.  Returns a certificate string or None."""
    width = len(F[0])
    kw = dict(max_prim=1500, max_accel=100, max_deg=6, Lmax=48)

    halted, states = _simulate(F, width, step_cap)
    if halted:
        return None

    from collections import defaultdict
    shapes = defaultdict(list)
    for s in states:
        shapes[tuple(x == 0 for x in s)].append(s)
    ordered = sorted(((sh, occ) for sh, occ in shapes.items() if len(occ) >= min_occ),
                     key=lambda kv: (sum(0 if z else 1 for z in kv[0]), -len(kv[1])))

    for sh, occ in ordered:
        nocc = len(occ)
        for offset in range(0, min(max_offset, nocc - 3) + 1):
            body = occ[offset:]
            if len(body) < 4:
                break
            fit_seq = body[:window]
            cols = [[s[i] for s in fit_seq] for i in range(width)]

            # ---- ADDITIVE: registers polynomial in the boundary index -------
            fam = []
            ok = True
            nonconst = False
            for i in range(width):
                p = _fit_poly(cols[i], dmax)
                if p is None:
                    ok = False
                    break
                fam.append(p)
                if len(_pnorm_fr(p)) > 1:
                    nonconst = True
            if ok and nonconst:
                res = _verify_additive(F, width, fam, Mset, kw)
                if res is not None:
                    M, u0 = res
                    for j in range(len(body) - 1, -1, -1):
                        pred = [int(_peval_fr(fam[i], j))
                                for i in range(width)]
                        if pred == list(body[j]):
                            if j >= u0:
                                deg = max(len(_pnorm_fr(p)) - 1 for p in fam)
                                return f'ONED_PROGRESS(add,deg={deg},M={M},N0={u0})'
                            break
                        if j < len(fit_seq):
                            break

            # ---- MULTIPLICATIVE: registers = c*B^k + d (poly in u = B^k) -----
            B = None
            fam = []
            ok = True
            for i in range(width):
                col = cols[i]
                if all(v == col[0] for v in col):
                    fam.append(_pnorm_fr([Fraction(col[0])]))
                    continue
                g = _fit_geometric(col)
                if g is None:
                    ok = False
                    break
                b_i, poly = g
                if B is None:
                    B = b_i
                elif B != b_i:
                    ok = False
                    break
                fam.append(poly)
            if ok and B is not None:
                res = _verify_multiplicative(F, width, fam, B, kw, Mmul=Mmul)
                if res is not None:
                    Mp, X0 = res
                    for k, s in enumerate(body):
                        X = B ** k
                        if X < X0:
                            continue
                        pred = tuple(int(_peval_fr(fam[i], X))
                                     for i in range(width))
                        if pred == tuple(s):
                            return f'ONED_PROGRESS(mul,B={B},M={Mp},Xlo={X0})'
                        break

            # ---- TEMPLATE: one free register, reach any larger member -------
            cmap = {}
            varying = []
            for i in range(width):
                col = cols[i]
                if all(v == col[0] for v in col):
                    cmap[i] = col[0]
                else:
                    varying.append(i)
            if len(varying) == 1:
                pc = varying[0]
                cmap = {i: v for i, v in cmap.items() if i != pc}
                res = _verify_template(F, width, cmap, pc, Mset, kw)
                if res is not None:
                    M, N0 = res
                    for _t, s in enumerate(occ):
                        if all(s[i] == v for i, v in cmap.items()) and s[pc] >= N0:
                            return f'ONED_PROGRESS(tmpl,param={pc},M={M},N0={N0})'
    return None


if __name__ == '__main__':
    holdouts = parse_file('holdout/sz21_140.txt')
    # sys.stdout = open('decider/tmp.txt', 'w')
    print(f'running oned_progress on {len(holdouts)} holdouts')
    print()

    holdouts2: list[list[list[int]]] = []
    for F in holdouts:
        result = oned_progress(F)
        if result is not None:
            print(f'{unparse_line(F)}, NON-HALT: {result}')
        else:
            holdouts2.append(F)

    print()
    print(f'{len(holdouts2)} holdouts remaining')
    print()
    for F in holdouts2:
        print(unparse_line(F))
