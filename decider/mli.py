#!/usr/bin/env python3
# Original source: https://github.com/sligocki/etc/blob/a4343177e489c0c0e8d50f95615b171d652fcde1/fractran/mask_lin_invar.py
# Some details have been modified to make this decider compatible with utils.py
# Masked Linear Invariant (MLI)

from collections import defaultdict
from dataclasses import dataclass

import sys
import z3

from utils import parse_file, unparse_line


@dataclass(frozen=True)
class DecideResult:
    infinite: bool
    weights: list[list[int]]
    num_rules: int
    protector_rule: int
    violator_rule: int
    gate_register: int
FAILED_RESULT = DecideResult(False, [], -1, -1, -1, -1)


def min_vals(rule: list[int]) -> list[int]:
    """Min values required in order to apply this rule."""
    return [max(0, -x) for x in rule]

def dot(xs, ys):
    assert len(xs) == len(ys), (xs, ys)
    return z3.Sum([v * c for v, c in zip(xs, ys)])

def decide_specific(prog: list[list[int]], start_state: list[int], safe_regs: dict[int, int], p_idx: int, v_idx: int, gate_var: int) -> DecideResult:
    num_rules = len(prog)
    num_vars = len(prog[0])
    requirements = [min_vals(trans) for trans in prog]

    # We currently only allow safe registers that have requirement = 1.
    # TODO: Support requirement > 1, but this is not trivial. I think it requires
    # more complex restrictions on the start_state valuations.
    safe_regs = {r for r in safe_regs if safe_regs[r] == 1}

    # Max/min values of the gate register upon activating the violator rule.
    gate_max = requirements[p_idx][gate_var] - 1
    gate_min = requirements[v_idx][gate_var]

    if not (gate_min == 0 == gate_max):
        # We currently only support the situation where P requires exactly 1 gate_var
        # (and V 0) so that we can ensure that if P did not apply and V did, that gate_var = 0.
        # TODO: This can probably be softened a bit to allow requirements[p_idx][gate_var] to
        # have any positive value by modifying the "buffer" logic below.
        return FAILED_RESULT

    s = z3.Solver()
    S1 = [z3.Int(f"S1_{i}") for i in range(num_vars)]
    S2 = [z3.Int(f"S2_{i}") for i in range(num_vars)]

    # S1 Constraints (The Floor)
    # S1 never decreases and starts >= 1
    # Therefore, at any point in the future it will have value >= 1
    s.add(dot(S1, start_state) >= 1)
    for i in range(num_rules):
        s.add(dot(S1, prog[i]) >= 0) # S1 never decreases

    # S2 Constraints (The Ceiling)
    # S2 is also always >= 1, but the reasoning is slightly more complicated.
    # It starts >= 1 and does not decrease except for one (violator) rule.
    # After that violator rule applies, we show that S2 >= S1 >= 1.
    s.add(dot(S2, start_state) >= 1)
    # S2 is non-decreasing on all rules except the violator rule.
    for i in range(num_rules):
        if i != v_idx:  # No constraint on the "violator" rule
            s.add(dot(S2, prog[i]) >= 0) # Others non-decreasing

    # When S2 > 0, it is impossible for the program to halt because it must
    # have positive values in some "safe" registers that guarantee that a
    # rule will always apply.
    # We guarantee this by requiring all weights to be <= 0 for unsafe registers
    # which means that if S2 > 0, at least one safe register must be positive.
    for i in range(num_vars):
        if i not in safe_regs:
            s.add(S2[i] <= 0)

    # Constraints for when violator rule applies.
    # The goal here is to prove that after the violator rule applies, S2 >= S1.
    # In order to prove this we require:
    #   A) S2 >= S1 before the violator rule applies (in other words, all components
    #      of S2 >= S1 except for the gate_var (which will be 0 when violator gate applies)).
    #   B) S2 . x >= S1 . x where x = requiremens[v] +

    # The Gating Constraint (S2 must stay >= S1 after the drop)
    # We enforce S2 >= S1 on all vars except the gate_var (which is 0).
    for i in range(num_vars):
        if i != gate_var:
            s.add(S2[i] >= S1[i])

    # We require that S2 >= S1 directly after applying the violator rule.
    # Here we consider the min state after (`min_after`).
    # If it is larger in any register other than `gate_var` (which is 0)
    # then the above check ensures that will only make S2 - S1 bigger.
    min_before = requirements[v_idx]
    min_after = [min_before[i] + prog[v_idx][i]
                    for i in range(num_vars)]
    S1_after = dot(S1, min_after)
    S2_after = dot(S2, min_after)
    s.add(S2_after >= S1_after)

    if s.check() == z3.sat:
        m = s.model()
        S1 = [m[v].as_long() for v in S1]
        S2 = [m[v].as_long() for v in S2]
        return DecideResult(True, [S1, S2], num_rules, p_idx, v_idx, gate_var)
    else:
        return FAILED_RESULT

def decide_full(prog: list[list[int]], start_state: list[int]) -> DecideResult:
    """Decide using full program (no prefixes)"""
    num_rules = len(prog)
    num_vars = len(prog[0])
    requirements = [min_vals(trans) for trans in prog]

    # Identify "safe" registers
    # A register is safe if it ALONE guarantees a rule triggers (req has only 1 non-zero entry).
    # We also require that it only appears once in that denominator (25/3 is good, but 25/9 is not).
    # TODO: Support safe registers with active_vars[0][1] > 1
    safe_vals = defaultdict(list)
    for req in requirements:
        active_regs = [(i,x) for i, x in enumerate(req) if x > 0]
        if len(active_regs) == 1:
            (reg_num, req) = active_regs[0]
            safe_vals[reg_num].append(req)
    # Map from register to min_value such that if that register has a value >= min_value,
    # then it is guaranteed at least one rule will apply.
    safe_regs = {n: min(vals) for (n, vals) in safe_vals.items()}


    # Find S1 (Floor) and S2 (Ceiling) where S2 drops ONLY on 'Violator', protected by 'Protector'.
    for v_idx in range(num_rules):       # Violator Rule Index
        for p_idx in range(v_idx):       # Protector Rule Index (Must have higher priority)
            # Check Compatibility between protector and violator rules.
            #   Every requirement for P (except for one requirement on a "gate register" being >= 1)
            #   must also be requirements for V.
            #   Furthermore, P must come before V.
            # Thus, we will know that any time V applies the gate register = 0 b/c
            # otherwise P (or an earlier rule) would have applied.

            # Find set of requirements for P that do not have exactly the same requirement for V.
            req_diffs = [k for k in range(num_vars)
                         if requirements[p_idx][k] > requirements[v_idx][k]]
            if len(req_diffs) != 1:
                # There exist multiple registers whose requirements differ, we can't be sure exactly
                # which difference caused V to fire and P not to, so move on.
                continue
            (gate_var,) = req_diffs
            # If we made it to this point, then we have found a valid pair of protector and violator rules.

            res = decide_specific(prog, start_state, safe_regs, p_idx, v_idx, gate_var)
            if res.infinite:
                return res

    return FAILED_RESULT

def decide_pre(prog: list[list[int]], start_state: list[int]) -> DecideResult:
    """Try MLI on all "prefixes" of this program."""
    for n in range(2, len(prog) + 1):
        # We consider all prefixes of the program. If any prefix is infinite,
        # the rest of the rules don't matter.
        pre_prog = prog[:n]
        res = decide_full(pre_prog, start_state)
        if res.infinite:
            return res
    return FAILED_RESULT

def init_sim(prog: list[list[int]], init_steps: int) -> list[int]:
    state = [1] + [0] * (len(prog[0]) - 1)
    for _ in range(init_steps):
        for trans in prog:
            new_state = [i+j for i, j in zip(state, trans)]
            if min(new_state) >= 0:
                state = new_state
                break
        else:
            # return None  # This is from the source, and it's kind of a bug.
            assert False, 'init_sim halted'
    return state

def decide(prog: list[list[int]], init_steps: int) -> DecideResult:
    state = init_sim(prog, init_steps)
    return decide_pre(prog, state)


holdouts=parse_file('../holdout/sz20_29.txt')
#sys.stdout=open('tmp.txt','w')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]]=[]
for prog in holdouts:
    result=decide(prog,1000)
    if result.infinite:
        print(f'{unparse_line(prog)}, NON-HALT: {result}')
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2: print(unparse_line(prog))
