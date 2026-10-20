# python -m decider.ndr_progress
import itertools
from fractions import Fraction
from math import ceil, floor, gcd, lcm
from time import time

from decider.nd_progress import (BUDGET, CONTINUE, HALT, INFEAS, OK, UNKNOWN, Budget,
                                 NeedAssume, NeedModulus, NeedSplit, _compose, _simulate2,
                                 _translate_assumption, add, candidate_regions_nd, compute_V,
                                 const_form, detect_period, feasible, gather_shapes,
                                 implies_ge0, implies_le_neg1, in_region, is_const,
                                 prove_ge0, region_feasible, scale, sub, tight_ineq,
                                 uniform_zero, varying_regs, verify_config, which_rule_sym)
from decider.utils import parse_file, unparse_line

"""
WARNING: This decider was entirely written by AI (Claude). It extends `nd_progress`, whose
soundness-critical engine it reuses; see the warning there.

---

EXPERIMENTAL.  N-D progress certificates with RESIDUE-RESTRICTED invariant regions.

`nd_progress` proves  for every x in P,  C(x) |-+ C(x') with x' in P,  where P is a
polyhedron and every residue class x_k = M_k*m_k + r_k is verified.  Many machines
only stay in an invariant set that also constrains residues (e.g. "c = 2 mod 3",
"a odd"): the classes outside it halt or leave the shape.  Here the invariant is

    P_R = { x in P : (x_0 mod rmod_0, ..., x_{N-1} mod rmod_{N-1}) in R }

for a set R ('allowed') of residue vectors.  The verification split `moduli` is a
multiple of `rmod` (a macro-step may dispatch on c mod 9 while the invariant only
needs c mod 3).  Only the classes whose reduction lies in R are verified, and a run
is accepted only when it reaches a family member whose parameters lie in P AND whose
residue vector mod `rmod` is UNIFORMLY (for every m of the branch) a member of R.  A
family member with a residue outside R is simply passed through (the run continues).
If the residue of a reached member is not uniform, the moduli are refined
(NeedModulus) so that it becomes uniform.  R starts as the residues seen on the
trajectory (or as everything), and a class whose verification fails is removed from
it; every removal restarts the verification of all classes.

Soundness is the same argument as `nd_progress`: P_R is closed under the macro-step
(every class in R is verified to reach P_R in >= 1 steps, in the final pass, against
the final P, rmod and R), and the bootstrap is a concrete trajectory state in P_R.

Other differences from `nd_progress`:
  * N = 1 is allowed (one varying register; the region is an interval).
  * Shapes that occur only 4-5 times within the step cap are tried too (fast-growing
    families are rare on the trajectory).
  * Candidate regions: positivity alone first; if the stable tail of the orbit lies
    in a proper affine subspace, its equalities are added to every candidate first.
  * Regions and residue candidates are interleaved, with a per-shape time share.
  * The gate V >= 3 of an accelerated loop: `nd_progress` always shrinks the region
    to {V >= 3} (NeedAssume).  When V couples several parameters this can diverge
    (c >= 2d+4, c >= 3d+2, c >= 5d+1, ...), so after a failure that involved such an
    assumption the candidate is retried with `verify_config_r`, which splits on the
    gate instead ({V >= 3} accelerates, {V <= 2} single-steps).

The certificate is the `nd_progress` one plus 'rmod' and 'allowed' (None: no
restriction); `nd_progress_to_lean.py` translates both kinds.
"""


def _lift(allowed, old, new):
    """Residue vectors mod `new` whose reduction mod `old` lies in `allowed`."""
    out = set()
    for r in itertools.product(*[range(M) for M in new]):
        if tuple(r[k] % old[k] for k in range(len(old))) in allowed:
            out.add(r)
    return out


# ---------------------------------------------------------------------------
# engine variant: a loop-count gate that couples several parameters is split on
# ---------------------------------------------------------------------------

def _single_var(g):
    return sum(1 for a in g[:-1] if a != 0) <= 1


def do_step_r(F, regs, hist, rules, Phi, nvars, target_test, moved, bud, Lmax, ev=None,
              split_all=False):
    """`nd_progress.do_step`, except for the gate V >= 3 of an accelerated loop.
    `do_step` shrinks the invariant to {V >= 3} (NeedAssume) whenever the gate is not
    provable.  That is the right move when V >= 3 is a lower bound on one parameter
    (the orbit grows past it), but when V couples several parameters the orbit can
    stay near the boundary forever and the shrinking never converges.  So here:
      * V >= 3 provable           -> accelerate (as in `do_step`);
      * V <= 2 provable           -> do not accelerate: keep single-stepping (the loop
                                     exits within two more cycles);
      * one-parameter gate        -> NeedAssume (as in `do_step`), unless `split_all`;
      * otherwise                 -> NeedSplit on the gate ({V >= 3} / {V <= 2}).
    Single-stepping is always sound, and the split is exhaustive over the integers."""
    nregs = len(regs)
    if moved and target_test(regs, Phi):
        if ev is not None:
            ev.extend(('step', r) for r in rules)
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
    Lp = detect_period(newrules, Lmax)
    if Lp:
        T = len(newrules)
        p0 = T - 2 * Lp
        S0 = newhist[p0]
        Delta = [sub(newhist[p0 + Lp][i], S0[i]) for i in range(nregs)]
        if all(is_const(dp) for dp in Delta):
            Dc = [dp[-1] for dp in Delta]
            if all(x == 0 for x in Dc):
                if ev is not None:
                    ev.extend(('step', r) for r in newrules[:p0])
                    ev.append(('loop', newrules[p0:p0 + Lp]))
                return OK, newregs, newhist, newrules
            V = compute_V(F, newhist, newrules, p0, Lp, Dc, Phi, nvars)
            if V is not None and not is_const(V):
                gate = sub(V, const_form(3, nvars))
                if prove_ge0(Phi, nvars, gate):
                    jumped = [add(S0[i], scale(V, Dc[i])) for i in range(nregs)]
                    bud.accel += 1
                    if ev is not None:
                        ev.extend(('step', r) for r in newrules[:p0])
                        ev.append(('accel', newrules[p0:p0 + Lp], Dc, V))
                    return CONTINUE, jumped, [jumped], []
                if not implies_le_neg1(Phi, nvars, gate):
                    if _single_var(gate) and not split_all:
                        raise NeedAssume(gate)
                    raise NeedSplit(gate)
    return CONTINUE, newregs, newhist, newrules


class _Budget(Budget):
    """`nd_progress.Budget` plus a wall-clock deadline (None: none).  Splitting on
    loop gates can build deep case analyses whose LP calls grow with the depth, so
    `verify_config_r` gives up when the deadline has passed."""
    __slots__ = ('deadline',)

    def __init__(self, max_prim, max_accel, max_configs, deadline=None):
        super().__init__(max_prim, max_accel, max_configs)
        self.deadline = deadline


def verify_config_r(F, regs, hist, rules, Phi, nvars, target_test, moved, bud, Lmax, depth=0,
                    node=None, ev=None, split_all=False):
    """`nd_progress.verify_config` driving `do_step_r` (same proof-tree format)."""
    bud.configs += 1
    if bud.configs > bud.max_configs:
        return False
    if getattr(bud, 'deadline', None) is not None and time() > bud.deadline:
        return False
    st = feasible(Phi, nvars)
    if st == INFEAS:
        if node is not None:
            node['kind'] = 'empty'
        return True
    if st == UNKNOWN:
        return False
    while True:
        try:
            status, regs, hist, rules = do_step_r(
                F, regs, hist, rules, Phi, nvars, target_test, moved, bud, Lmax, ev, split_all)
        except NeedSplit as e:
            g = e.g
            neg = scale(g, -1)
            neg[-1] -= 1
            lnode = rnode = None
            if node is not None:
                lnode, rnode = {}, {}
                node.update(kind='split', g=list(g), ge=lnode, le=rnode)
            if not verify_config_r(F, regs, hist, rules, Phi + [(list(g), False)], nvars,
                                   target_test, moved, bud, Lmax, depth + 1, lnode,
                                   None if ev is None else list(ev), split_all):
                return False
            return verify_config_r(F, regs, hist, rules, Phi + [(neg, False)], nvars,
                                   target_test, moved, bud, Lmax, depth + 1, rnode,
                                   None if ev is None else list(ev), split_all)
        if status == OK:
            if node is not None:
                node.update(kind='leaf', events=ev, end=regs)
            return True
        if status == HALT or status == BUDGET:
            return False
        moved = True


def _verify_residue_r(F, width, param_regs, P, nvars, subst, zero_regs, consts, rmod,
                      allowed, Lmax, max_prim, max_accel, max_configs, out=None,
                      split_gates=False, deadline=None):
    regs = [const_form(consts.get(i, 0), nvars) for i in range(width)]
    for k, pr in enumerate(param_regs):
        regs[pr] = list(subst[k])
    Phi = [(_compose(q, subst, nvars), False) for q in P]
    st = feasible(Phi, nvars)
    if st == INFEAS:
        if out is not None:
            out['kind'] = 'empty'
        return 'ok'
    if st == UNKNOWN:
        return 'fail'

    def target_test(cur, Phi):
        for i in zero_regs:
            f = cur[i] if i not in consts else add(cur[i], const_form(-consts[i], nvars))
            if not uniform_zero(Phi, nvars, f):
                return False
        reached = [cur[pr] for pr in param_regs]
        for q in P:
            if not implies_ge0(Phi, nvars, _compose(q, reached, nvars)):
                return False
        if allowed is None:
            return True
        need = {}
        res = []
        for k in range(nvars):
            M = rmod[k]
            f = reached[k]
            for j in range(nvars):
                if f[j] % M:
                    fac = M // gcd(M, f[j])
                    need[j] = need.get(j, 1) * fac // gcd(need.get(j, 1), fac)
            res.append(f[-1] % M)
        if need:
            raise NeedModulus(need)
        return tuple(res) in allowed

    bud = _Budget(max_prim, max_accel, max_configs, deadline)
    try:
        if split_gates:
            ok = verify_config_r(F, regs, [list(regs)], [], Phi, nvars, target_test, False,
                                 bud, Lmax, node=out, ev=None if out is None else [],
                                 split_all=split_gates == 'all')
        else:
            ok = verify_config(F, regs, [list(regs)], [], Phi, nvars, target_test, False,
                               bud, Lmax, node=out, ev=None if out is None else [])
    except NeedAssume as e:
        return ('assume', list(e.g))
    except NeedModulus as e:
        return ('modulus', dict(e.need))
    return 'ok' if ok else 'fail'


def verify_region_r(F, width, param_regs, region, nvars, rmod, allowed, consts=None,
                    Lmax=48, max_prim=2500, max_accel=200, max_configs=300, max_restart=24,
                    max_moduli_product=64, record=False, split_gates=False,
                    max_multi_assume=3, deadline=None):
    """Like `nd_progress.verify_region`, with a residue restriction: `allowed` is a set
    of residue vectors mod `rmod` (or None: no restriction).  The verification split
    `moduli` starts at `rmod` and may be refined (NeedModulus); it is always a multiple
    of `rmod`, and only the classes whose reduction mod `rmod` is allowed are verified.

    When a class fails, it is excluded from the invariant: `rmod` is refined to the
    current `moduli` (if coarser) and the class removed from `allowed`.  With
    `allowed=None` the first failure excludes that class from the full set.

    `split_gates` selects the engine variant `verify_config_r` (True: split gates that
    couple several parameters; 'all': split every gate).  The result records
    whether the invariant was shrunk by an assumption coupling several parameters
    ('multi_assume'), the case where that variant can help; more than
    `max_multi_assume` such assumptions are taken as a sign that the shrinking
    diverges, and the attempt fails.  Past the wall-clock `deadline` (if given) the
    attempt fails."""
    consts = consts or {}
    rmod = list(rmod)
    moduli = list(rmod)
    zero_regs = [i for i in range(width) if i not in param_regs]
    P = [list(q) for q in region]
    allowed = None if allowed is None else set(allowed)
    trees = {}
    multi_assume = 0

    def _ret(ok):
        res = {'ok': ok, 'P': P if ok else None, 'moduli': list(moduli), 'rmod': list(rmod),
               'allowed': None if allowed is None else sorted(allowed),
               'multi_assume': multi_assume > 0}
        if record:
            res['trees'] = trees if ok else None
        return res

    for _restart in range(max_restart):
        if not region_feasible([(list(q), False) for q in P], nvars):
            return _ret(False)
        if allowed is not None and not allowed:
            return _ret(False)
        if deadline is not None and time() > deadline:
            return _ret(False)
        restart = False
        trees = {}
        for residues in itertools.product(*[range(M) for M in moduli]):
            if allowed is not None and \
                    tuple(residues[k] % rmod[k] for k in range(nvars)) not in allowed:
                continue
            subst = []
            for k in range(nvars):
                f = const_form(residues[k], nvars)
                f[k] = moduli[k]
                subst.append(f)
            out = {} if record else None
            res = _verify_residue_r(F, width, param_regs, P, nvars, subst, zero_regs,
                                    consts, rmod, allowed, Lmax, max_prim, max_accel,
                                    max_configs, out, split_gates, deadline)
            if res == 'ok':
                if record:
                    trees[tuple(residues)] = out
                continue
            if res == 'fail':
                full = itertools.product(*[range(M) for M in moduli])
                if allowed is None:
                    allowed = set(full)
                elif rmod != moduli:
                    allowed = _lift(allowed, rmod, moduli)
                rmod = list(moduli)
                allowed.discard(tuple(residues))
                restart = True
                break
            if res[0] == 'modulus':
                for k, fac in res[1].items():
                    moduli[k] *= fac
                prod = 1
                for M in moduli:
                    prod *= M
                if max(moduli) > 64 or prod > max_moduli_product:
                    return _ret(False)
                restart = True
                break
            if not _single_var(res[1]):
                if multi_assume >= max_multi_assume:
                    return _ret(False)          # the shrinking is diverging
                multi_assume += 1
            P = P + [_translate_assumption(res[1], moduli, residues)]
            restart = True
            break
        if not restart:
            return _ret(True)
    return _ret(False)


def _boot(occ, param_regs, consts, res):
    allowed = None if res['allowed'] is None else set(map(tuple, res['allowed']))
    return find_bootstrap_r(occ, param_regs, res['P'], consts, res['rmod'], allowed)


def find_bootstrap_r(occ, param_regs, P, consts, rmod, allowed):
    for t, s in occ:
        if any(s[i] != consts.get(i, 0) for i in range(len(s)) if i not in param_regs):
            continue
        pt = [s[r] for r in param_regs]
        if not in_region(pt, P):
            continue
        if allowed is not None and \
                tuple(pt[k] % rmod[k] for k in range(len(pt))) not in allowed:
            continue
        return (t, list(s))
    return None


_MODS = (2, 3, 4, 5, 6, 8, 9, 10, 12)


def residue_candidates(pts, nvars, max_prod=36):
    """Moduli vectors under which the observed points miss some residue classes,
    most promising first.  Per coordinate, the moduli with the smallest fraction of
    residues seen are preferred (ties: the smaller modulus)."""
    out = []
    seen = set()

    def push(ms):
        ms = tuple(ms)
        p = 1
        for M in ms:
            p *= M
        if p <= max_prod and ms not in seen and any(M > 1 for M in ms):
            seen.add(ms)
            out.append(ms)

    n = len(pts)
    per = []
    for k in range(nvars):
        lst = []
        for M in _MODS:
            if n < M + 2:
                break
            S = {p[k] % M for p in pts}
            if len(S) < M:
                lst.append((len(S) / M, M))
        lst.sort()
        per.append([M for _, M in lst[:2]])
    push([lst[0] if lst else 1 for lst in per])
    for k in range(nvars):
        for M in per[k]:
            push([M if j == k else 1 for j in range(nvars)])
    push([lst[-1] if lst else 1 for lst in per])
    for k, l in itertools.combinations(range(nvars), 2):
        for M in (2, 3, 4):
            if n < M * M + 2:
                break
            if len({(p[k] % M, p[l] % M) for p in pts}) < M * M:
                push([M if j in (k, l) else 1 for j in range(nvars)])
                break
    return out


def affine_hull(pts, nvars):
    """A basis of the integer affine equalities  e(x) = 0  (e = [c_0..c_{N-1}, c])
    satisfied by every point (exact rational elimination)."""
    ncol = nvars + 1
    A = [[Fraction(v) for v in p] + [Fraction(1)] for p in pts]
    piv, rk = [], 0
    for c in range(ncol):
        p = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[rk], A[p] = A[p], A[rk]
        pv = A[rk][c]
        A[rk] = [x / pv for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][k] - f * A[rk][k] for k in range(ncol)]
        piv.append(c)
        rk += 1
    out = []
    for fc in range(ncol):
        if fc in piv:
            continue
        v = [Fraction(0)] * ncol
        v[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            v[pc] = -A[i][fc]
        if all(x == 0 for x in v[:-1]):
            continue
        d = 1
        for x in v:
            d = lcm(d, x.denominator)
        iv = [int(x * d) for x in v]
        g = 0
        for x in iv:
            g = gcd(g, x)
        out.append([x // g for x in iv])
    return out


def _ratio_bounds(lo, hi, qmax=3, cmax=7):
    """(p, q) with p/q <= lo maximal and (p', q') with p'/q' >= hi minimal, over
    q <= qmax and coefficients <= cmax (None where no such fraction exists).
    `lo` and `hi` are non-negative Fractions."""
    best_lo = best_hi = None
    for q in range(1, qmax + 1):
        p = floor(lo * q)
        if 0 < p <= cmax and (best_lo is None or Fraction(p, q) > Fraction(*best_lo)):
            best_lo = (p, q)
        p = ceil(hi * q)
        if 0 < p <= cmax and (best_hi is None or Fraction(p, q) < Fraction(*best_hi)):
            best_hi = (p, q)
    return best_lo, best_hi


def ratio_cones(tail, nvars):
    """For each pair of parameters (i, j), the two small-coefficient lines through
    (about) the origin that bracket the ratios x_j / x_i seen on the tail:
    q*x_j - p*x_i >= c  and  p'*x_i - q'*x_j >= c', with tight offsets."""
    out = []
    for i, j in itertools.combinations(range(nvars), 2):
        rs = [Fraction(p[j], p[i]) for p in tail if p[i] > 0]
        if len(rs) < 3 or any(p[i] <= 0 or p[j] <= 0 for p in tail):
            continue
        blo, bhi = _ratio_bounds(min(rs), max(rs))
        pair = []
        for b, sign in ((blo, 1), (bhi, -1)):
            if b is None:
                continue
            d = [0] * nvars
            d[j], d[i] = sign * b[1], -sign * b[0]
            pair.append(tight_ineq(d, tail, nvars))
        if len(pair) == 2:
            out.append(pair)
    return out


def _regions(pts, nvars, tail):
    """Candidate regions.  If the stable tail of the orbit lies in a proper affine
    subspace (and has enough points to say so), its equalities are added to every
    candidate first; then the candidates without them."""
    eqs = affine_hull(tail, nvars) if len(tail) >= nvars + 3 else []
    eqc = [q for e in eqs for q in (e, [-x for x in e])]
    lo = [min(p[k] for p in pts) for k in range(nvars)]
    pos = [[1 if k == i else 0 for k in range(nvars)] + [-lo[i]] for i in range(nvars)]
    base = [pos]
    if nvars >= 2:
        cones = [pos + c for c in ratio_cones(tail, nvars)]
        if len(cones) > 1:
            cones.append(pos + [q for c in ratio_cones(tail, nvars) for q in c])
        base = itertools.chain(base, cones, candidate_regions_nd(pts, nvars))
    if not eqc:
        yield from base
        return
    base = list(base)
    for r in base:
        yield r + eqc
    yield from base


def _shapes(states, min_occ, min_occ_rare):
    """Shapes as in `gather_shapes` (fewest non-zero registers first, then the most
    occurrences), but down to `min_occ_rare` occurrences: fast-growing families occur
    only a few times within the step cap, and their shapes are often the cleanest.
    Among shapes with equally many non-zero registers, those with >= min_occ
    occurrences come first."""
    sh = gather_shapes(states, min_occ=min_occ_rare)
    sh.sort(key=lambda kv: (sum(0 if z else 1 for z in kv[0]), len(kv[1]) < min_occ,
                            -len(kv[1])))
    return sh


def ndr_progress_cert(F, step_cap=40000, time_budget=300.0, min_occ=6, min_occ_rare=4,
                      max_shapes=8, nvar_set=(1, 2, 3), max_regions=60, shape_frac=0.4,
                      record=True, engine_kw=None, grace=60.0):
    """Try to prove F (from u_0 = "2") non-halting with a (residue-restricted) N-D
    progress certificate.  Returns the certificate (with the proof trees if `record`)
    or None.  The search stops starting new candidates after `time_budget` seconds of
    wall time (0: no limit); a candidate still running `grace` seconds later fails."""
    width = len(F[0])
    t_start = time()
    if engine_kw is None:
        engine_kw = dict(max_prim=2500, max_accel=200, max_configs=300, max_restart=24,
                         max_moduli_product=64)
    if time_budget > 0:
        engine_kw = dict(engine_kw, deadline=t_start + time_budget + grace)
    sim = _simulate2(F, width, step_cap)
    if sim['halted']:
        return None
    tried = 0
    for sh, occ in _shapes(sim['states'], min_occ, min_occ_rare):
        vr = varying_regs(occ, width)
        if len(vr) not in nvar_set:
            continue
        tried += 1
        if tried > max_shapes:
            break
        nvars = len(vr)
        param_regs = vr
        consts = {i: occ[0][1][i] for i in range(width) if i not in vr and occ[0][1][i]}
        pts = [tuple(s[r] for r in param_regs) for _, s in occ]
        skip = min(3, len(pts) // 5)
        tail = pts[skip:] if skip and len(pts) - skip >= 4 else pts
        mods = [None] + residue_candidates(tail, nvars)
        t_shape = time()
        ncand = 0
        for region, ms in ((r, ms) for r in _regions(pts, nvars, tail) for ms in mods):
            ncand += 1
            now = time()
            if ncand > max_regions * len(mods) or (time_budget > 0 and (
                    now - t_start > time_budget or now - t_shape > shape_frac * time_budget)):
                break
            if ms is None:
                rmod, allowed = [1] * nvars, None
            else:
                rmod = list(ms)
                allowed = {tuple(p[k] % ms[k] for k in range(nvars)) for p in tail}
            res = verify_region_r(F, width, param_regs, region, nvars, rmod, allowed,
                                  consts=consts, record=record, **engine_kw)
            if not res['ok'] and res['multi_assume']:
                res = verify_region_r(F, width, param_regs, region, nvars, rmod, allowed,
                                      consts=consts, record=record, split_gates=True,
                                      **engine_kw)
            if not res['ok']:
                continue
            boot = _boot(occ, param_regs, consts, res)
            if boot is None:
                # the region shrank past every member seen on the trajectory: avoid
                # the one-parameter assumptions too
                res = verify_region_r(F, width, param_regs, region, nvars, rmod, allowed,
                                      consts=consts, record=record, split_gates='all',
                                      **engine_kw)
                if not res['ok']:
                    continue
                boot = _boot(occ, param_regs, consts, res)
                if boot is None:
                    continue
            P, rmod = res['P'], res['rmod']
            allowed = None if res['allowed'] is None else set(map(tuple, res['allowed']))
            cert = {'shape': sh, 'param_regs': param_regs}
            if consts:
                cert['consts'] = consts
            cert.update({'nvars': nvars, 'P': P, 'moduli': res['moduli'], 'rmod': rmod,
                         'allowed': None if allowed is None else sorted(allowed),
                         'region0': region, 'boot_t': boot[0], 'boot_state': boot[1]})
            if record:
                cert['trees'] = res['trees']
            return cert
    return None


def cert_str(cert):
    if cert is None:
        return None
    keys = ('shape', 'param_regs', 'consts', 'nvars', 'P', 'moduli', 'rmod', 'allowed',
            'region0', 'boot_t', 'boot_state')
    return f"NDR_PROGRESS({ {k: cert[k] for k in keys if k in cert}!r})"


def ndr_progress(F, **kw):
    return cert_str(ndr_progress_cert(F, record=False, **kw))


if __name__ == '__main__':
    holdouts = parse_file('holdout/sz21_140.txt')
    print(f'running ndr_progress on {len(holdouts)} holdouts')
    print()
    holdouts2 = []
    for F in holdouts:
        result = ndr_progress(F)
        if result is not None:
            print(f'{unparse_line(F)}, NON-HALT: {result}')
        else:
            holdouts2.append(F)
    print()
    print(f'{len(holdouts2)} holdouts remaining')
    print()
    for F in holdouts2:
        print(unparse_line(F))
