# python -m decider.nd_progress
import itertools
from collections import defaultdict
from fractions import Fraction
from math import gcd, isqrt, lcm
from time import time
from decider.utils import parse_file, unparse_line

"""
WARNING: This decider was entirely written by AI (Opus 4.8). I cannot guarantee that this decider is
sound (i.e. if an FM halts, then the decider does not return non-halt). Please open an issue if this
decider is unsound or contains sketchy code.

---

nd_progress.py — N-D Progress Certificate decider for FRACTRAN non-halting (N in {2,3}).

Pure Python — no sympy, no z3; runs on Python 3.9 and 3.12;
the entry point is a module-level function, so it works under multiprocessing.

--------------------------------------------------------------------------------
WHAT IT PROVES.  Non-halting via a parameterized INVARIANT REGION — the automated
analogue of the size-22 Lean `progress_nonhalt` proofs.  A canonical family C(x)
places N in {2,3} parameters x = (x_0,...,x_{N-1}) into the N *varying* registers of
a fixed zero-pattern "shape" (all other registers 0).  The certificate is a polyhedron
P of small-integer linear inequalities on x such that:

    for every x in P,  C(x)  [F]|-+  (some member of P)

i.e. from any point of the region the machine reaches, in >= 1 steps, another state of
the same shape whose parameters are again in P.  P closed under this macro-step + P
nonempty + reachable  =>  an infinite run, hence non-halting.  A concrete BOOTSTRAP
(a real trajectory state 2 |-* member-of-P) attaches the argument to the start state.

Because the number of FRACTRAN steps per macro-step GROWS with the parameters, this
catches machines that constant-step "translated cycler" deciders cannot.

--------------------------------------------------------------------------------
KEY FACT that keeps verification decidable.  Within ONE macro-step every register
value, every loop count and every branch condition is AFFINE (degree 1) in x.  The
exponential / non-integer-ratio / alternating BEHAVIOUR is emergent from *iterating*
the affine map on the region — the certificate itself stays linear.  So verification
needs only EXACT RATIONAL LINEAR ARITHMETIC over a polyhedron (Fourier–Motzkin), plus
on-demand region splitting; residue splits and region-shrinking are discovered
automatically.

SOUNDNESS DISCIPLINE (the soundness-critical engine, `verify_region` / `verify_config`):
  * every sign/branch decision is made UNIFORMLY over the current region via the exact
    LP oracle; when a sign is not uniform we SPLIT the region into {g >= 0} and
    {g <= -1} (exhaustive over integers) and verify BOTH — never guess;
  * loops are cycle-accelerated to S0 + V*Dc, where V is the uniform max cycle count
    keeping EVERY register >= 0 and EVERY higher-priority rule inapplicable at every
    position/cycle (a clean floor; if a drain divisor is not clean we raise a residue
    modulus).  We land at cycle V, never V+1 — so acceleration cannot skip a halt (it
    only jumps cycles where the fired rule keeps applying, then single-steps the exit);
  * a net-zero cycle over >= 1 steps is a genuine infinite loop => success; any
    decision that cannot be made cleanly => undecided (never optimistic);
  * rational relaxation is sound for the ">= 0" facts we conclude (rational-feasible
    superset of the integer points), and the integer {g <= -1} split branch keeps the
    case analysis exhaustive over the actual integer parameters.

--------------------------------------------------------------------------------
RESULTS (decided / total; combined 1DPC ∪ NDPC, where 1DPC is the sibling 1-D decider):

    set                     1DPC (1-D)        1DPC ∪ NDPC        NDPC adds
    sz21_140                 95 (67.9%)       140  (100.0%)        +45
    sz22_2003              1325 (66.2%)      1979  ( 98.8%)       +654
    sz23_21233 (open)     13212 (62.2%)     20441  ( 96.3%)      +7229

  sz21 and sz22 are Lean-proven non-halting, so those are COMPLETENESS rates (each
  decision is cross-checked against a formal proof).  sz23_21233 is the open size-23
  residual; there NDPC alone decides 7229 / 8021 = 90.1% of the 1DPC residual.
  Within sz22, recall on the `progress_nonhalt` (2-variable invariant-set) class the
  method targets is 97%.

SOUNDNESS (a decider must NEVER call a halting machine non-halting):
  * 0 / 7559 known-halting machines decided (sz22_halted_692 + sz23_halted_6867).
  * 0 false positives against the 62 sz23 machines discovered to halt AFTER this ran
    (the halted set grew 6805 -> 6867); none is in the decided set.
  * every emitted certificate independently re-verified by plain concrete simulation.

--------------------------------------------------------------------------------
STRUCTURE (this file, in three sections):
  1. LP oracle       — exact rational Fourier–Motzkin feasibility / implication.
  2. Engine          — region-splitting symbolic simulation with sound cycle
                       acceleration, automatic residue split (NeedModulus) and region
                       shrink (NeedAssume).  The soundness-critical core.
  3. Decider         — detect canonical shapes, fit the affine self-map, discover the
                       region from its eigenstructure + register differences, verify
                       with the engine, and find a concrete bootstrap.  Plus a
                       human-readable certificate renderer (`render_cert`).

USAGE.
    nd_progress(F) -> "ND_PROGRESS(cert)" | None
        F is a list of int DELTA vectors: state 2^a0*3^a1*5^a2... is [a0,a1,...] and a
        rule a/b is (exponents of a) - (exponents of b); rule j fires at state u iff
        u[i]+F[j][i] >= 0 for all i; the first applicable rule fires; start state = 2.
    render_cert(cert[, prog]) -> a human-readable rendering of the invariant region.
"""


# ===========================================================================
# 1. LP ORACLE — exact rational linear arithmetic (Fourier–Motzkin)
# ===========================================================================

FEAS = 'feasible'
INFEAS = 'infeasible'
UNKNOWN = 'unknown'

_MAX_CONSTRAINTS = 4000     # FM working-set cap (per elimination round)


def _norm(L, strict):
    """Divide an affine form by the gcd of its coefficients (keeps the same
    solution set for >=0 / >0).  Returns (tuple(L), strict) for hashing."""
    g = 0
    for a in L:
        g = gcd(g, a)
    if g > 1:
        L = [a // g for a in L]
    return (tuple(L), strict)


def _dedup(cons):
    """Remove duplicate / trivially-true constraints.  Returns list or None if a
    constant contradiction is present (=> infeasible)."""
    seen = set()
    out = []
    for L, st in cons:
        key = _norm(list(L), st)
        L2, st2 = list(key[0]), key[1]
        # all-zero variable part?
        if all(a == 0 for a in L2[:-1]):
            c = L2[-1]
            if st2:
                if c <= 0:
                    return None            # c > 0 with c <= 0: contradiction
            else:
                if c < 0:
                    return None            # c >= 0 with c < 0: contradiction
            continue                       # trivially true; drop
        if key in seen:
            continue
        seen.add(key)
        out.append((L2, st2))
    return out


def feasible(constraints, nvars):
    """Return FEAS / INFEAS / UNKNOWN for the rational feasibility of `constraints`
    over `nvars` variables via Fourier-Motzkin elimination."""
    cons = [(list(L), bool(st)) for L, st in constraints]
    cons = _dedup(cons)
    if cons is None:
        return INFEAS
    for k in range(nvars):
        Z, P, Ng = [], [], []
        for L, st in cons:
            if L[k] > 0:
                P.append((L, st))
            elif L[k] < 0:
                Ng.append((L, st))
            else:
                Z.append((L, st))
        newc = list(Z)
        for Lp, sp in P:
            ap = Lp[k]
            for Ln, sn in Ng:
                an = -Ln[k]                # positive
                # combine an*Lp + ap*Ln  (cancels x_k)
                comb = [an * Lp[i] + ap * Ln[i] for i in range(nvars + 1)]
                comb[k] = 0
                newc.append((comb, sp or sn))
        cons = _dedup(newc)
        if cons is None:
            return INFEAS
        if len(cons) > _MAX_CONSTRAINTS:
            return UNKNOWN
    # all vars eliminated; _dedup already caught constant contradictions
    for L, st in cons:
        c = L[-1]
        if st:
            if c <= 0:
                return INFEAS
        else:
            if c < 0:
                return INFEAS
    return FEAS


def implies_ge0(constraints, nvars, L):
    """True iff `constraints` (rationally) imply  L >= 0  (SOUND for integer pts).
    Returns True / False; on FM overflow returns False (conservative)."""
    negL = [-a for a in L]
    # add L < 0  (i.e. -L > 0)
    test = list(constraints) + [(negL, True)]
    r = feasible(test, nvars)
    return r == INFEAS


def implies_le_neg1(constraints, nvars, L):
    """True iff constraints imply L < 0 over rationals (=> L <= -1 over integers).
    Tests infeasibility of Phi ∧ {L >= 0}."""
    test = list(constraints) + [(list(L), False)]      # add L >= 0
    r = feasible(test, nvars)
    return r == INFEAS


def region_feasible(constraints, nvars):
    return feasible(constraints, nvars) == FEAS


# affine-form helpers ------------------------------------------------------

def const_form(c, nvars):
    return [0] * nvars + [c]


def var_form(k, nvars):
    L = [0] * (nvars + 1)
    L[k] = 1
    return L


def add(a, b):
    return [a[i] + b[i] for i in range(len(a))]


def sub(a, b):
    return [a[i] - b[i] for i in range(len(a))]


def scale(a, c):
    return [x * c for x in a]


def is_const(L):
    return all(a == 0 for a in L[:-1])


# ===========================================================================
# 2. ENGINE — region-splitting symbolic simulation (soundness-critical)
# ===========================================================================

# outcome tags
OK = 'ok'
HALT = 'halt'
BUDGET = 'budget'


class NeedSplit(Exception):
    """Raised when a decision is ambiguous over the current region; carries the
    affine form g on which the caller must split ({g>=0} vs {g<=-1}).  BOTH sub-
    regions are then verified (genuine case analysis)."""
    __slots__ = ('g',)

    def __init__(self, g):
        self.g = g


class NeedAssume(Exception):
    """Raised when the engine wants to SHRINK the invariant region P by adding a
    lower-bound assumption g >= 0 (rather than case-split).  This is the 2-D
    analog of the 1-D engine raising `m_lo`: we prove the certificate only for
    the sub-region {g >= 0} and require the bootstrap to land there.  Sound
    because the concrete orbit's parameters grow past any constant bound.
    Propagates to the top, which augments P and restarts verification."""
    __slots__ = ('g',)

    def __init__(self, g):
        self.g = g


class NeedModulus(Exception):
    """Raised when a drain loop's divisor `r` does not divide the m-coefficients
    of a register base, so its accelerated cycle count is not a clean affine form.
    Carries {var_index: factor} — the top level multiplies that parameter's
    residue-split modulus by `factor` (making the coefficient divisible) and
    restarts.  The 2-D analog of 1DPC choosing a residue split that divides the
    drain divisor cleanly."""
    __slots__ = ('need',)

    def __init__(self, need):
        self.need = need


class Budget:
    __slots__ = ('prim', 'accel', 'configs',
                 'max_prim', 'max_accel', 'max_configs')

    def __init__(self, max_prim=4000, max_accel=300, max_configs=6000):
        self.prim = 0
        self.accel = 0
        self.configs = 0
        self.max_prim = max_prim
        self.max_accel = max_accel
        self.max_configs = max_configs


# ---------------------------------------------------------------------------
# uniform decisions over the current region (raise NeedSplit when ambiguous)
# ---------------------------------------------------------------------------

def decide_ge0(Phi, nvars, g):
    """True if g>=0 uniformly, False if g<=-1 uniformly, else NeedSplit(g)."""
    if implies_ge0(Phi, nvars, g):
        return True
    if implies_le_neg1(Phi, nvars, g):
        return False
    raise NeedSplit(g)


def prove_ge0(Phi, nvars, g):
    """Non-splitting: True iff g>=0 provably uniform, else False."""
    return implies_ge0(Phi, nvars, g)


def uniform_zero(Phi, nvars, L):
    """True iff L == 0 for all points of Phi (L>=0 and -L>=0)."""
    return implies_ge0(Phi, nvars, L) and implies_ge0(Phi, nvars, scale(L, -1))


def umin_forms(forms, Phi, nvars):
    """Uniform minimum of a nonempty list of affine forms over Phi.  May raise
    NeedSplit (pairwise comparisons)."""
    best = forms[0]
    for f in forms[1:]:
        # if f < best somewhere ambiguous -> NeedSplit; else pick uniformly
        if decide_ge0(Phi, nvars, sub(best, f)):   # best - f >= 0  => f <= best
            best = f
    return best


def clean_floor(L, r):
    """Affine form for floor(L(x)/r) for all integer x, or None if r does not
    divide every non-constant coefficient of L.  r > 0."""
    assert r > 0
    for a in L[:-1]:
        if a % r != 0:
            return None
    # // is floor for the const
    return [a // r for a in L[:-1]] + [L[-1] // r]


def clean_floor_or_modulus(L, r):
    """Like clean_floor but, when r does not divide some m-coefficient a_k, raise
    NeedModulus asking to scale param k's modulus by r/gcd(r,a_k) so that the
    coefficient becomes divisible."""
    need = {}
    for k, a in enumerate(L[:-1]):
        if a % r != 0:
            need[k] = r // gcd(r, a)
    if need:
        raise NeedModulus(need)
    return [a // r for a in L[:-1]] + [L[-1] // r]


# ---------------------------------------------------------------------------
# symbolic step primitives
# ---------------------------------------------------------------------------

def analyze_rule(F, regs, Phi, nvars, j):
    """Return 'app', 'inapp', or raise NeedSplit for rule j over region Phi."""
    ambiguous = None
    for i, delta in enumerate(F[j]):
        if delta < 0:
            g = add(regs[i], const_form(delta, nvars))    # regs[i] + delta
            if implies_le_neg1(Phi, nvars, g):
                return 'inapp'                             # guard uniformly fails
            if not implies_ge0(Phi, nvars, g):
                if ambiguous is None:
                    ambiguous = g
    if ambiguous is not None:
        raise NeedSplit(ambiguous)
    return 'app'


def which_rule_sym(F, regs, Phi, nvars):
    """Index of the uniformly-first applicable rule, or -1 if uniformly halted.
    May raise NeedSplit."""
    for j in range(len(F)):
        r = analyze_rule(F, regs, Phi, nvars, j)
        if r == 'app':
            return j
        # 'inapp' -> continue to next rule
    return -1


def detect_period(rules, Lmax):
    T = len(rules)
    for L in range(1, Lmax + 1):
        if 2 * L > T:
            break
        if rules[T - 2 * L:T - L] == rules[T - L:T]:
            return L
    return 0


def compute_V(F, hist, rules, p0, L, Dc, Phi, nvars):
    """Uniform max cycle count V (affine form) keeping every register >= 0 and
    every higher-priority rule inapplicable at every position/cycle, or None if
    it cannot be certified as a clean affine bound.  May raise NeedSplit."""
    R = len(Dc)
    bounds = []
    # (A) non-negativity of every draining register at every position/cycle
    for i in range(R):
        if Dc[i] < 0:
            col = [hist[t][i] for t in range(p0, p0 + L + 1)]
            base_i = umin_forms(col, Phi, nvars)
            b = clean_floor_or_modulus(
                base_i, -Dc[i])   # may raise NeedModulus
            bounds.append(b)
    # (B) higher-priority rules stay inapplicable at every sub-position/cycle.
    #     A CLEAN uniform witness always exists (which_rule already found one when
    #     it fired rj), so we only collect coords that are uniformly < 0; ambiguous
    #     or non-negative coords are simply skipped (never split here).
    for j in range(L):
        rj = rules[p0 + j]
        state_j = hist[p0 + j]
        for rp in range(rj):
            rule = F[rp]
            perm = False
            wit = []
            for i, d in enumerate(rule):
                if d < 0:
                    val0 = add(state_j[i], const_form(
                        d, nvars))   # state_j[i]+d
                    if implies_le_neg1(Phi, nvars, val0):          # clean witness
                        if Dc[i] <= 0:
                            perm = True                            # stays < 0 forever
                            break
                        neg = sub(const_form(-1, nvars), val0)     # |val0|-1
                        b = clean_floor(neg, Dc[i])
                        if b is not None:
                            wit.append(b)
            if perm:
                continue
            if not wit:
                return None                # can't certify rp stays inapplicable cleanly
            bounds.append(umin_forms(wit, Phi, nvars))
    if not bounds:
        return None
    return umin_forms(bounds, Phi, nvars)


# ---------------------------------------------------------------------------
# one symbolic step (pure: raises NeedSplit or returns a new config)
# ---------------------------------------------------------------------------

CONTINUE = 'continue'


def do_step(F, regs, hist, rules, Phi, nvars, target_test, moved, bud, Lmax):
    """Perform one symbolic transition from (regs,hist,rules).  Returns
    (status, regs', hist', rules') where status in {OK, HALT, BUDGET, CONTINUE}.
    Pure w.r.t. inputs (no mutation); raises NeedSplit on ambiguity."""
    nregs = len(regs)
    # degree is always 1 (affine); nothing to guard there.
    if moved and target_test(regs, Phi):
        return OK, regs, hist, rules
    if bud.prim >= bud.max_prim or bud.accel >= bud.max_accel:
        return BUDGET, regs, hist, rules
    j = which_rule_sym(F, regs, Phi, nvars)
    if j < 0:
        return HALT, regs, hist, rules
    rule = F[j]
    newregs = [add(regs[i], const_form(rule[i], nvars)) for i in range(nregs)]
    newhist = hist + [newregs]
    newrules = rules + [j]
    bud.prim += 1

    # try to accelerate a detected loop
    Lp = detect_period(newrules, Lmax)
    if Lp:
        T = len(newrules)
        p0 = T - 2 * Lp
        S0 = newhist[p0]
        Delta = [sub(newhist[p0 + Lp][i], S0[i]) for i in range(nregs)]
        if all(is_const(dp) for dp in Delta):
            Dc = [dp[-1] for dp in Delta]
            if all(x == 0 for x in Dc):
                return OK, newregs, newhist, newrules   # net-zero cycle => loop forever
            V = compute_V(F, newhist, newrules, p0, Lp, Dc, Phi, nvars)
            if V is not None and not is_const(V):
                # accelerate a genuine scaling loop (V grows with the params).  We
                # jump to cycle V (the last valid cycle), which requires V >= 3 so
                # we land strictly past the 2 observed cycles.  If V >= 3 is not
                # provable, SHRINK the invariant (assume V >= 3) rather than peel
                # the boundary one value at a time.
                gate = sub(V, const_form(3, nvars))
                if prove_ge0(Phi, nvars, gate):
                    jumped = [add(S0[i], scale(V, Dc[i]))
                              for i in range(nregs)]
                    bud.accel += 1
                    return CONTINUE, jumped, [jumped], []
                raise NeedAssume(gate)
    return CONTINUE, newregs, newhist, newrules


# ---------------------------------------------------------------------------
# region-splitting driver
# ---------------------------------------------------------------------------

def verify_config(F, regs, hist, rules, Phi, nvars, target_test, moved, bud, Lmax, depth=0):
    """Verify the obligation from the current config, splitting the region as
    needed.  Returns True iff this config AND all its region-splits reach a
    target member (or a net-zero cycle) without halting / running out of budget."""
    bud.configs += 1
    if bud.configs > bud.max_configs:
        return False
    # SOUNDNESS: distinguish "provably empty" from "feasibility unknown".  An empty
    # region is vacuously verified; but if the LP oracle overflows (UNKNOWN) we do
    # NOT know the region is empty, so we must NOT vacuously succeed — fail instead.
    st = feasible(Phi, nvars)
    if st == INFEAS:
        return True                     # provably empty region: vacuously verified
    if st == UNKNOWN:
        return False                    # cannot certify feasibility -> cannot verify
    while True:
        try:
            status, regs, hist, rules = do_step(
                F, regs, hist, rules, Phi, nvars, target_test, moved, bud, Lmax)
        except NeedSplit as e:
            g = e.g
            neg = scale(g, -1)
            # g <= -1  <=>  -g-1 >= 0
            neg[-1] -= 1
            left = verify_config(F, regs, hist, rules, Phi + [(list(g), False)],
                                 nvars, target_test, moved, bud, Lmax, depth + 1)
            if not left:
                return False
            return verify_config(F, regs, hist, rules, Phi + [(neg, False)],
                                 nvars, target_test, moved, bud, Lmax, depth + 1)
        if status == OK:
            return True
        if status == HALT or status == BUDGET:
            return False
        moved = True                                       # took a real step


# ---------------------------------------------------------------------------
# public entry point
# ---------------------------------------------------------------------------

def _compose(q, subst, nvars):
    """Compose affine form q (over N param SLOTS) with a substitution `subst`
    (list of N affine forms over the working variables) -> affine form over the
    working variables:  q(subst_0, ..., subst_{N-1})."""
    comp = const_form(q[-1], nvars)
    for k in range(nvars):
        comp = add(comp, scale(subst[k], q[k]))
    return comp


def _translate_assumption(g, moduli, residues):
    """Translate an assumption g(m) >= 0 (over the residue variables m, where the
    actual param x_k = M_k*m_k + r_k) into an equivalent integer constraint H(x)>=0
    over the actual params.  m_k = (x_k - r_k)/M_k; multiply through by L=prod(M_k)."""
    n = len(moduli)
    L = 1
    for M in moduli:
        L *= M
    H = [0] * (n + 1)
    const = g[-1] * L
    for k in range(n):
        # g[k]*m_k = g[k]*(x_k - r_k)/M_k ; times L
        f = L // moduli[k]
        H[k] = g[k] * f
        const -= g[k] * f * residues[k]
    H[-1] = const
    # normalize by gcd
    gg = 0
    for a in H:
        gg = gcd(gg, a)
    if gg > 1:
        H = [a // gg for a in H]
    return H


def _verify_residue(F, width, param_regs, P, nvars, param_subst, zero_regs,
                    Lmax, max_prim, max_accel, max_configs):
    """Verify the obligation for ONE residue substitution `param_subst` (a list
    of N affine forms giving each actual param as M_k*m_k + r_k) under invariant
    P (constraints over the actual params).  Returns 'ok', 'fail', or ('assume', g)
    where g is an affine form over the m-variables to be assumed (>= 0)."""
    # start state C over the m-variables
    regs = [const_form(0, nvars) for _ in range(width)]
    for k, pr in enumerate(param_regs):
        regs[pr] = list(param_subst[k])
    # initial region Phi = P composed with the substitution (over m)
    Phi = [(_compose(q, param_subst, nvars), False) for q in P]
    st = feasible(Phi, nvars)
    if st == INFEAS:
        return 'ok'                          # provably empty residue: vacuously true
    if st == UNKNOWN:
        return 'fail'                        # cannot certify feasibility -> fail

    def target_test(cur, Phi):
        for i in zero_regs:
            if not uniform_zero(Phi, nvars, cur[i]):
                return False
        reached = [cur[pr]
                   for pr in param_regs]      # actual x' as forms over m
        for q in P:                                   # closure: q(x') >= 0
            if not implies_ge0(Phi, nvars, _compose(q, reached, nvars)):
                return False
        return True

    bud = Budget(max_prim, max_accel, max_configs)
    try:
        ok = verify_config(F, regs, [list(regs)], [], Phi, nvars,
                           target_test, False, bud, Lmax)
    except NeedAssume as e:
        return ('assume', list(e.g))
    except NeedModulus as e:
        return ('modulus', dict(e.need))
    return 'ok' if ok else 'fail'


def verify_region(F, width, param_regs, region, nvars, moduli=None, Lmax=48,
                  max_prim=4000, max_accel=300, max_configs=6000, max_restart=30,
                  max_moduli_product=48):
    """Prove: for all x in the invariant region P, C(x) [F]|-+ (member of P),
    which proves non-halting (progress_nonhalt).

    param_regs : register indices carrying the N parameters (len N).
    region     : list of affine forms over the N params, each meaning ">= 0".
    moduli     : per-parameter residue-split moduli (x_k = M_k*m_k + r_k); every
                 residue combo is verified, so the union covers all params.  A
                 finer split lets a drain loop's divisor divide the m-coefficient
                 cleanly (the 2-D analog of 1DPC's residue split).

    Returns the FINAL invariant P (list of affine forms over the params, including
    any region-shrinking assumptions) on success, or None.
    """
    if moduli is None:
        moduli = [1 for _ in range(nvars)]
    moduli = list(moduli)
    zero_regs = [i for i in range(width) if i not in param_regs]
    P = [list(q) for q in region]
    MAX_MODULUS = 64

    def _prod(ms):
        p = 1
        for m in ms:
            p *= m
        return p

    def _ret(ok):
        return {'ok': ok, 'P': P if ok else None, 'moduli': list(moduli)}

    for _restart in range(max_restart):
        Phi0 = [(list(q), False) for q in P]
        if not region_feasible(Phi0, nvars):
            return _ret(False)
        restart_needed = False
        failed = False
        for residues in itertools.product(*[range(M) for M in moduli]):
            subst = []
            for k in range(nvars):
                f = const_form(residues[k], nvars)
                f[k] = moduli[k]                     # M_k*m_k + r_k
                subst.append(f)
            res = _verify_residue(F, width, param_regs, P, nvars, subst, zero_regs,
                                  Lmax, max_prim, max_accel, max_configs)
            if res == 'ok':
                continue
            if res == 'fail':
                failed = True
                break
            if res[0] == 'modulus':
                for k, fac in res[1].items():
                    moduli[k] *= fac
                    if moduli[k] > MAX_MODULUS:
                        return _ret(False)
                if _prod(moduli) > max_moduli_product:
                    return _ret(False)
                restart_needed = True
                break
            # ('assume', g): fold into P (over actual params) and restart
            P = P + [_translate_assumption(res[1], moduli, residues)]
            restart_needed = True
            break
        if failed:
            return _ret(False)
        if not restart_needed:
            return _ret(True)                        # all residues verified
    return _ret(False)

# ===========================================================================
# concrete simulation (integer exponent vectors) — used only for detection and
# to find the concrete bootstrap; the symbolic engine below is the sound filter.
# ===========================================================================


def _simulate(F, width, max_steps):
    """Run from the start state 2 = [1,0,...] for up to max_steps, applying the first
    applicable rule each step.  Returns (halted, states) with states the trajectory."""
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


def _simulate2(F, width, step_cap, record=True):
    """Adapter: the detector expects a dict with 'halted' and 'states'."""
    halted, states = _simulate(F, width, step_cap)
    return {'halted': halted, 'states': states}


# ===========================================================================
# 3. DECIDER — detection, region discovery, bootstrap, readable rendering
# ===========================================================================


# ---------------------------------------------------------------------------
# detection helpers
# ---------------------------------------------------------------------------

def gather_shapes(states, min_occ=6):
    by = defaultdict(list)
    for t, s in enumerate(states):
        by[tuple(x == 0 for x in s)].append((t, s))
    out = [(sh, occ) for sh, occ in by.items() if len(occ) >= min_occ]
    out.sort(key=lambda kv: (sum(0 if z else 1 for z in kv[0]), -len(kv[1])))
    return out


def varying_regs(occ, width):
    seq = [s for _, s in occ]
    return [i for i in range(width) if any(s[i] != seq[0][i] for s in seq)]


# ---------------------------------------------------------------------------
# region discovery
# ---------------------------------------------------------------------------

def _reduce(v):
    g = 0
    for a in v:
        g = gcd(g, a)
    return tuple(a // g for a in v) if g > 1 else tuple(v)


def convex_hull(points):
    """2-D convex hull (monotone chain) on integer points; returns hull vertices
    CCW.  points: list of (x,y)."""
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lower = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def tight_ineq(direction, pts, nvars):
    """affine form  [a0..a_{n-1}, c]  for  direction . x >= min_pts(direction . x)."""
    vals = [sum(direction[k] * p[k] for k in range(nvars)) for p in pts]
    c = -min(vals)
    return list(direction) + [c]


# --- exact rational linear algebra for fitting the affine self-map ----------

def _solve(M, rhs):
    """Solve the square system M x = rhs over Fractions; return x or None."""
    n = len(M)
    A = [list(M[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if A[r][col] != 0), None)
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [A[r][k] - f * A[col][k] for k in range(n + 1)]
    return [A[i][n] for i in range(n)]


def _independent(rows, u):
    """True iff u is linearly independent of the given rows (Fraction rows)."""
    M = [list(r) for r in rows] + [list(u)]
    # row-reduce, check rank == len(M)
    m, ncol = len(M), len(u)
    rank = 0
    for col in range(ncol):
        piv = next((r for r in range(rank, m) if M[r][col] != 0), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        pv = M[rank][col]
        M[rank] = [x / pv for x in M[rank]]
        for r in range(m):
            if r != rank and M[r][col] != 0:
                f = M[r][col]
                M[r] = [M[r][k] - f * M[rank][k] for k in range(ncol)]
        rank += 1
    return rank == m


def fit_affine_map(pts, nvars, tail=12):
    """Fit v' = A v + b exactly from consecutive canonical points (last `tail`
    pairs, to skip transients).  Returns (A rows, b) over Fractions, or None."""
    if len(pts) < nvars + 2:
        return None
    pairs = [(pts[i], pts[i + 1]) for i in range(len(pts) - 1)][-tail:]
    U = [[Fraction(v) for v in inp] + [Fraction(1)] for inp, _ in pairs]
    chosen, basis = [], []
    for idx, u in enumerate(U):
        if _independent(basis, u):
            basis.append(u)
            chosen.append(idx)
        if len(chosen) == nvars + 1:
            break
    if len(chosen) < nvars + 1:
        return None
    M = [U[c] for c in chosen]
    A, b = [], []
    for i in range(nvars):
        rhs = [Fraction(pairs[c][1][i]) for c in chosen]
        sol = _solve(M, rhs)
        if sol is None:
            return None
        A.append(sol[:nvars])
        b.append(sol[nvars])
    for inp, out in pairs:                              # verify on all tail pairs
        for i in range(nvars):
            if sum(A[i][j] * inp[j] for j in range(nvars)) + b[i] != out[i]:
                return None
    return A, b


def _clear_int(vec):
    """Fraction vector -> reduced integer tuple (or None if all zero)."""
    d = 1
    for x in vec:
        d = lcm(d, x.denominator)
    iv = [int(x * d) for x in vec]
    if all(v == 0 for v in iv):
        return None
    g = 0
    for v in iv:
        g = gcd(g, v)
    return tuple(v // g for v in iv)


def eigen_directions_2d(A):
    """Left-eigenvector directions of the 2x2 fitted map A (rational eigenvalues
    only).  These are the natural invariant-coupling directions: along a left-
    eigenvector w, the quantity w·x evolves by a 1-D affine map, so w·x >= const
    is the closed half-plane the orbit lives in."""
    a, b = A[0]
    c, d = A[1]
    tr, det = a + d, a * d - b * c
    disc = tr * tr - 4 * det
    if disc < 0:
        return []
    num, den = disc.numerator, disc.denominator
    sn, sd = isqrt(num), isqrt(den)
    if sn * sn != num or sd * sd != den:
        return []                                       # irrational eigenvalues
    s = Fraction(sn, sd)
    out = []
    for lam in ((tr + s) / 2, (tr - s) / 2):
        w = (c, lam - a)
        if w == (0, 0):
            w = (lam - d, b)
        iv = _clear_int(w)
        if iv:
            out.append(iv)
            out.append(tuple(-x for x in iv))
    return out


def hull_normals(pts):
    dirs = []
    hull = convex_hull(pts)
    H = len(hull)
    for i in range(H):
        p, q = hull[i], hull[(i + 1) % H]
        dx, dy = q[0] - p[0], q[1] - p[1]
        for n in ((-dy, dx), (dy, -dx)):
            if n != (0, 0):
                dirs.append(_reduce(n))
    return dirs


def smart_directions(pts, nvars):
    """Ranked coupling directions: eigenvectors of the fitted map (2-var), then
    register differences, then small ratios, then hull edges, then a brute set."""
    dirs = []
    fit = fit_affine_map(pts, nvars)
    if fit is not None and nvars == 2:
        dirs += eigen_directions_2d(fit[0])
    for i in range(nvars):                              # register differences x_i - x_j
        for j in range(nvars):
            if i < j:
                a = [0] * nvars
                a[i] = 1
                a[j] = -1
                dirs.append(tuple(a))
                dirs.append(tuple(-x for x in a))
    for i in range(nvars):                              # small ratios k*x_i - x_j
        # and x_i - k*x_j (coeff-k on either side)
        for j in range(nvars):
            if i != j:
                for k in (2, 3):
                    a = [0] * nvars
                    a[i] = k
                    a[j] = -1
                    dirs.append(tuple(a))
                    b = [0] * nvars
                    b[i] = 1
                    b[j] = -k
                    dirs.append(tuple(b))
    if nvars == 2:
        dirs += hull_normals(pts)
    rng = range(-2, 3) if nvars >= 3 else range(-3, 4)
    dirs += [tuple(c) for c in itertools.product(rng, repeat=nvars) if any(c)]
    out, seen = [], set()
    for d in dirs:
        r = _reduce(d)
        if sum(1 for x in r if x != 0) == 1 and max(r) == 1 and min(r) == 0:
            continue                                    # positivity, covered separately
        if max(abs(x) for x in r) > 7:
            continue
        if r not in seen:
            seen.add(r)
            out.append(r)
    return out


def candidate_regions_nd(pts, nvars):
    """Yield candidate regions: positivity + a single ranked coupling, then
    positivity + pairs of the top couplings.  Eigenvector/difference couplings
    come first so the working region is usually found among the first few tries.

    Positivity offsets are the OBSERVED MINIMUMS (x_k >= min_obs), not >= 0: the
    invariant usually needs registers nonzero/large enough for the opening rules
    to fire, and a start-state guard bound is resolved by SPLIT (whose x_k=0 branch
    would fail) rather than by the acceleration ASSUME mechanism.  Tightening to
    the observed minimum is sound (the bootstrap is an observed point, hence >=
    min_obs) and matches the growing orbit."""
    lo = [min(p[k] for p in pts) for k in range(nvars)]
    pos = [[1 if k == i else 0 for k in range(
        nvars)] + [-lo[i]] for i in range(nvars)]
    maxcoord = max(max(abs(v) for v in p) for p in pts) if pts else 1
    off_cap = 2 * maxcoord + 50
    # a startup transient contaminates the tight offset (e.g. reg2-reg3 collapses to
    # >=1 when the family needs >=3); fit each coupling on the STABLE TAIL, skipping a
    # leading transient.  This coincides with the all-points offset when there is no
    # transient, and is the correct (tighter) offset when there is one — sound because
    # the bootstrap is a family point, hence on the tail, and growing families map into
    # the tighter region.  So we use the tail offset only (no candidate-count blowup).
    skip = min(3, len(pts) // 5)
    src = pts[skip:] if skip and len(pts) - skip >= 4 else pts
    couplings, seen = [], set()
    for d in smart_directions(pts, nvars):
        q = tight_ineq(d, src, nvars)
        if abs(q[-1]) > off_cap:
            continue
        if tuple(q) not in seen:
            seen.add(tuple(q))
            couplings.append(q)
    NS = 26
    K = 8
    for q in couplings[:NS]:
        yield pos + [q]
    for i in range(min(len(couplings), K)):
        for j in range(i + 1, min(len(couplings), K)):
            yield pos + [couplings[i], couplings[j]]


# ---------------------------------------------------------------------------
# bootstrap
# ---------------------------------------------------------------------------

def in_region(point, P):
    for q in P:
        if sum(q[k] * point[k] for k in range(len(point))) + q[-1] < 0:
            return False
    return True


def find_bootstrap(occ, param_regs, P):
    """Earliest concrete canonical orbit state whose params lie in the final P."""
    for t, s in occ:
        pt = [s[r] for r in param_regs]
        if in_region(pt, P):
            return (t, list(s))
    return None


# ---------------------------------------------------------------------------
# top-level decider
# ---------------------------------------------------------------------------

def _decide_2d(F, width, step_cap=40000, min_occ=6, max_shapes=4,
               nvar_set=(2, 3), engine_kw=None, max_regions=80, time_budget=300.0):
    t_start = time()
    if engine_kw is None:
        # fail-fast budget for detection; genuine certs verify in <150 configs, so
        # a low config cap makes wrong regions cheap.  moduli-product 64 catches
        # mod-7^2=49 dispatches (e.g. #1429, #1258).
        engine_kw = dict(max_prim=2500, max_accel=200, max_configs=300,
                         max_restart=12, max_moduli_product=64)
    sim = _simulate2(F, width, step_cap)
    if sim['halted']:
        return None
    shapes = gather_shapes(sim['states'], min_occ=min_occ)
    tried_shapes = 0
    for sh, occ in shapes:
        vr = varying_regs(occ, width)
        if len(vr) not in nvar_set:
            continue
        tried_shapes += 1
        if tried_shapes > max_shapes:
            break
        nvars = len(vr)
        param_regs = vr
        pts = [tuple(s[r] for r in param_regs) for _, s in occ]
        ncand = 0
        # reuse discovered residue-split across regions
        moduli_hint = [1] * nvars
        for region in candidate_regions_nd(pts, nvars):
            ncand += 1
            if ncand > max_regions or (time_budget > 0 and time() - t_start > time_budget):
                break
            res = verify_region(F, width, param_regs, region, nvars,
                                moduli=list(moduli_hint), **engine_kw)
            # thread discovered moduli forward, but never past the product cap
            cap = engine_kw.get('max_moduli_product', 48)
            cand_hint = [max(moduli_hint[k], res['moduli'][k])
                         for k in range(nvars)]
            prod = 1
            for m in cand_hint:
                prod *= m
            if prod <= cap:
                moduli_hint = cand_hint
            if not res['ok']:
                continue
            P, moduli = res['P'], res['moduli']
            boot = find_bootstrap(occ, param_regs, P)
            if boot is None:
                continue
            return {'shape': sh, 'param_regs': param_regs, 'nvars': nvars,
                    'P': P, 'moduli': moduli, 'region0': region,
                    'boot_t': boot[0], 'boot_state': boot[1]}
    return None


# ---------------------------------------------------------------------------
# human-readable certificate rendering (shows the N-D region as inequalities)
# ---------------------------------------------------------------------------
_LETTERS = 'abcdefghijklmnop'


def _simplify_region(P, nvars):
    """Drop inequalities implied by the others (for readable display only); the
    stored/verified region is unchanged.  Greedy removal keeps the feasible set
    identical (each removed constraint is implied by those that remain)."""
    result = [list(q) for q in P]
    i = 0
    while i < len(result):
        others = [(list(result[j]), False)
                  for j in range(len(result)) if j != i]
        if others and implies_ge0(others, nvars, result[i]):
            result.pop(i)
        else:
            i += 1
    return result


def _fmt_ineq(coeffs, names):
    """Render an affine form [c_0,...,c_{n-1}, k] meaning Σ c_i·name_i + k ≥ 0 as a
    readable inequality LHS ≥ RHS (negatives moved to the right)."""
    pos, neg = [], []
    for i, c in enumerate(coeffs[:-1]):
        if c > 0:
            pos.append((c, names[i]))
        elif c < 0:
            neg.append((-c, names[i]))
    k = coeffs[-1]
    if k > 0:
        pos.append((k, None))
    elif k < 0:
        neg.append((-k, None))

    def term(c, nm):
        if nm is None:
            return str(c)
        return nm if c == 1 else f'{c}·{nm}'
    L = ' + '.join(term(c, nm) for c, nm in pos) or '0'
    R = ' + '.join(term(c, nm) for c, nm in neg) or '0'
    return f'{L}  ≥  {R}'


def render_cert(cert, prog=None):
    """A human-readable rendering of an NDPC certificate, showing the invariant
    2-D (or 3-D) region as linear inequalities over named registers."""
    if cert is None:
        return 'UNDECIDED'
    width = len(cert['boot_state'])
    reg_name = [_LETTERS[i] for i in range(width)]
    pregs = cert['param_regs']
    pnames = [reg_name[r] for r in pregs]
    nvars = cert['nvars']

    # canonical family vector: param registers show their letter, others 0
    fam = []
    for i in range(width):
        fam.append(reg_name[i] if i in pregs else '0')
    fam_str = '⟨' + ', '.join(fam) + '⟩'
    prime_pow = '·'.join(f'{p}^{fam[i]}' for i, p in
                         zip(range(width), [2, 3, 5, 7, 11, 13, 17][:width]))

    lines = []
    if prog:
        lines.append(f'N-D Progress Certificate for {prog}')
    lines.append(f'  registers: ' +
                 ', '.join(f'{reg_name[i]}=reg{i}' for i in range(width)) +
                 f'   (state = {prime_pow})')
    lines.append(f'  canonical family  C({", ".join(pnames)}) = {fam_str}')
    lines.append(f'  invariant region P = {{ {fam_str} :')
    for q in _simplify_region(cert['P'], nvars):
        lines.append(f'        {_fmt_ineq(q, pnames)}')
    lines.append('  }')
    if any(m != 1 for m in cert['moduli']):
        splits = ', '.join(f'{pnames[k]} mod {cert["moduli"][k]}'
                           for k in range(nvars) if cert['moduli'][k] != 1)
        lines.append(f'  (verified per residue class: {splits})')
    lines.append(
        '  progress (verified): for every point of P, the machine reaches')
    lines.append(
        '        another member of P in ≥ 1 steps  ⇒  P is closed, so from')
    lines.append('        any member the run is infinite (non-halting).')
    boot = cert['boot_state']
    bootv = '⟨' + ', '.join(str(x) for x in boot) + '⟩'
    lines.append(
        f'  bootstrap: 2  ⊢*  {bootv} ∈ P   (reached at step {cert["boot_t"]})')
    return '\n'.join(lines)

# ===========================================================================
# public entry point (module-level; multiprocessing-friendly)
# ===========================================================================


def nd_progress(F, step_cap=40000, time_budget=300.0):
    """Prove F (started from 2) is non-halting via an N-D progress certificate.
    Returns a certificate string "ND_PROGRESS(...)" or None (undecided)."""
    width = len(F[0])
    cert = _decide_2d(F, width, step_cap=step_cap, time_budget=time_budget)
    if cert is None:
        return None
    return f"ND_PROGRESS({cert!r})"


if __name__ == '__main__':
    holdouts = parse_file('holdout/sz21_140.txt')
    # sys.stdout = open('decider/tmp.txt', 'w')
    print(f'running nd_progress on {len(holdouts)} holdouts')
    print()

    holdouts2: list[list[list[int]]] = []
    for F in holdouts:
        result = nd_progress(F)
        if result is not None:
            print(f'{unparse_line(F)}, NON-HALT: {result}')
        else:
            holdouts2.append(F)

    print()
    print(f'{len(holdouts2)} holdouts remaining')
    print()
    for F in holdouts2:
        print(unparse_line(F))
