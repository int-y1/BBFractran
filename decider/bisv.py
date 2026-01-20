import sys
import z3
from utils import parse_file, unparse_line

'''
This is an implementation of Beeping Integer Spanning Vectors using Z3. BISV is a stronger version
of ISV. See Theorem BISV.3 for the main idea.

---

In graph_search2.py, read the following: Basic definitions.

You may find isv.py helpful to read, since ISV is a simpler and weaker version of BISV.

For info on the Z3 API, read:
https://microsoft.github.io/z3guide/programming/Z3%20Python%20-%20Readonly/Introduction
You may skip these sections: Machine Arithmetic, Bit Tricks.

---

Definition BISV.1. Let c, d in N^J. Let k in N. Say that (k, c, d) is a probable-halt-certificate if
it satisfies:
* Define "beep" to be the next instruction used for u_k. That is, u_k |- u_k + F[beep].
* Define u2 := u_k + sum_{j=0}^{J-1} c[j]*F[j]. Warning: u2 is in Z^I.
* u2[i] >= 0 for all i in {0, 1, ..., I-1}.
* "beep" is the next instruction used for u2. That is, u2 |- u2 + F[beep].
* d[beep] = 1. That is, the beep instruction is used one last time.
* Define u3 := u_k + sum_{j=0}^{J-1} d[j]*F[j]. Warning: u3 is in Z^I.
* u3[i] >= 0 for all i in {0, 1, ..., I-1}.
* u3 |- halt.

Lemma BISV.2. Let k in N. Suppose u_0 |-* u_k. If F is halting, then there exist c, d in N^J such
that (k, c, d) is a probable-halt-certificate.
Proof. Let u_x be the last state to use F[beep], i.e. u_x |- u_x + F[beep] and F[beep] is not used
later. Since u_k |- u_k + F[beep], it follows that x >= k, and so u_k |-* u_x. Let u_y be the last
state, i.e. u_y |- halt. In summary, u_0 |-* u_k |-* u_x |-* u_y |- halt.
Define c in N^J as follows: c[j] is the number of times the instruction F[j] is used in u_k |-* u_x.
Define d in N^J as follows: d[j] is the number of times the instruction F[j] is used in u_x |-* u_y.
We show that (k, c, d) is a probable-halt-certificate:
* u2 = u_x, because by the definition of c, u_x = u_k + sum_{j=0}^{J-1} c[j]*F[j].
* min(u_x) >= 0, because u_x is a Fractran state that appeared naturally.
* u_x |- u_x + F[beep], by definition of u_x.
* d[beep] = 1, by definition of u_x.
* u3 = u_y, because by the definition of d, u_y = u_x + sum_{j=0}^{J-1} d[j]*F[j].
* min(u_y) >= 0, because u_y is a Fractran state that appeared naturally.
* u_y |- halt, by definition of u_y.
QED.

Theorem BISV.3. Let k in N. Suppose u_0 |-* u_k. If there does not exist c, d in N^J such that
(k, c, d) is a probable-halt-certificate, then F is non-halting.
Proof. By contradiction of Lemma BISV.2.
Note: The code searches up to k <= 1000. This should get almost all possible FMs.

TODO: When Z3 says "z3.unsat", F is non-halting and the certificate is (u1, beep, unsat_core).
However, unsat_core is hard to read.

TODO: If F is halting, every fraction will beep one last time. Maybe I can write another decider
that uses this fact.
'''


def bisv_z3(prog: list[list[int]], u1: list[int], beep: int) -> str | None:
    maxidx = len(prog[0])

    s = z3.Solver()
    s.set("unsat_core", True)
    c = [z3.Int(f'c_{j}') for j in range(len(prog))]
    d = [z3.Int(f'd_{j}') for j in range(len(prog))]
    u2 = [z3.Int(f'u2_{i}') for i in range(maxidx)]
    u3 = [z3.Int(f'u3_{i}') for i in range(maxidx)]
    assumptions = []  # for s.unsat_core()

    # Let c, d in N^J.
    for j in range(len(prog)):
        s.add(c[j] >= 0)
    for j in range(len(prog)):
        s.add(d[j] >= 0)
    # u2 := u_k + sum_{j=0}^{J-1} c[j]*F[j]. In this function, u1 = u_k.
    for i in range(maxidx):
        s.add(u2[i] == u1[i]+sum(c[j]*prog[j][i] for j in range(len(prog))))
    # u2[i] >= 0 for all i in {0, 1, ..., I-1}.
    for i in range(maxidx):
        s.add(u2[i] >= 0)
    # "beep" is the next instruction used for u2.
    for f in prog[:beep]:
        tmp = []
        for i, v in enumerate(f):
            if v >= 0:
                continue
            tmp.append(u2[i]+v < 0)
        assumptions.append(z3.Or(*tmp))
    for i, v in enumerate(prog[beep]):
        if v >= 0:
            continue
        assumptions.append(u2[i]+v >= 0)
    # d[beep] = 1.
    s.add(d[beep] == 1)
    # Define u3 := u_k + sum_{j=0}^{J-1} d[j]*F[j].
    for i in range(maxidx):
        s.add(u3[i] == u2[i]+sum(d[j]*prog[j][i] for j in range(len(prog))))
    # u3[i] >= 0 for all i in {0, 1, ..., I-1}.
    for i in range(maxidx):
        s.add(u3[i] >= 0)
    # u3 |- halt.
    for f in prog:
        tmp = []
        for i, v in enumerate(f):
            if v >= 0:
                continue
            tmp.append(u3[i]+v < 0)
        assumptions.append(z3.Or(*tmp))

    s_check = s.check(assumptions)
    # assert s_check != z3.unknown, "z3 couldn't determine sat/unsat"
    if s_check == z3.unsat:
        return f'BISV(u1={u1}, beep={prog[beep]}, unsat_core={list(s.unsat_core())})'

    # for debugging the probable-halt-certificate. this doesn't prove infinite.
    if 0:
        if s_check == z3.sat:
            m = s.model()
            mc = tuple(m[cj].as_long() for cj in c)
            md = tuple(m[dj].as_long() for dj in d)
            return f'DEBUG(u1={u1}, c={mc}, d={md})'

    return None


def bisv(prog: list[list[int]], limit: int = 1000) -> str | None:
    """ find (u1, beep) to use in bisv_z3 """
    maxidx = len(prog[0])

    # run steps
    cand_u1: list[None | list[int]] = [None]*len(prog)
    u = [1]+[0]*(maxidx-1)
    for _ in range(limit):
        for j, f in enumerate(prog):
            for e0, e1 in zip(u, f):
                if e0+e1 < 0:
                    break
            else:
                cand_u1[j] = list(u)
                for i in range(maxidx):
                    u[i] += f[i]
                break
        else:
            return None  # halted, shouldn't happen

    for beep in range(len(prog)):
        u1 = cand_u1[beep]
        if u1 is None:
            continue
        result = bisv_z3(prog, u1, beep)
        if result is not None:
            return result

    return None


def bsearch(prog: list[list[int]], limit: int = 1000) -> str | None:
    """ get the minimal certificate. intended for researching this decider. """
    out = bisv(prog, limit)
    if out is None:
        return out
    lo = 0
    hi = limit
    while lo < hi:
        mid = (lo+hi)//2
        out = bisv(prog, mid)
        if out is None:
            lo = mid+1
        else:
            hi = mid
    return bisv(prog, hi)


holdouts = parse_file('../holdout/sz20_6.txt')
# sys.stdout = open('tmp.txt', 'w')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]] = []
for prog in holdouts:
    result = bisv(prog, 1000)
    # result = bsearch(prog)
    if result is not None:
        print(f'{unparse_line(prog)}, NON-HALT: {result}')
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2:
    print(unparse_line(prog))
