# python -m decider.isv
import sys
import z3
from decider.utils import parse_file, unparse_line

'''
This is an implementation of Integer Spanning Vectors using Z3. See Theorem ISV.3 for the main idea.

---

In graph_search2.py, read the following: Basic definitions.

For info on the Z3 API, read:
https://microsoft.github.io/z3guide/programming/Z3%20Python%20-%20Readonly/Introduction
You may skip these sections: Machine Arithmetic, Bit Tricks.

---

Definition ISV.1. Let c in N^J. Let k in N. Say that (k, c) is a probable-halt-certificate if it
satisfies:
* Define v := u_k + sum_{j=0}^{J-1} c[j]*F[j]. Warning: v is in Z^I.
* v[i] >= 0 for all i in {0, 1, ..., I-1}.
* v |- halt.

Lemma ISV.2. Let k in N. Suppose u_0 |-* u_k. If F is halting, then there exists c in N^J such that
(k, c) is a probable-halt-certificate.
Proof. Let u_x be the last non-halting state, that is, u_0 |-* u_k |-* u_x |- halt. Define c in N^J
as follows: c[j] is the number of times the instruction F[j] is used in u_k |-* u_x. Then
u_x = u_k + sum_{j=0}^{J-1} c[j]*F[j]. min(u_x) >= 0 because u_x is a Fractran state that appeared
naturally. Lastly, u_x |- halt. Therefore, (k, c) is a probable-halt-certificate. QED.

Theorem ISV.3. Let k in N. Suppose u_0 |-* u_k. If there does not exist c in N^J such that
(k, c) is a probable-halt-certificate, then F is non-halting.
Proof. By contradiction of Lemma ISV.2.
Note: The code tries k = 0 and k = 1000. I have to keep k = 1000 because it can solve hundreds of
size-22 FMs.
'''


def isv(F: list[list[int]], steps: int) -> str | None:
    J = len(F)
    I = len(F[0])

    # run steps to compute u_k
    u = [1]+[0]*(I-1)
    for _ in range(steps):
        for inst in F:
            for e0, e1 in zip(u, inst):
                if e0+e1 < 0:
                    break
            else:
                for i in range(I):
                    u[i] += inst[i]
                break
        else:
            return None  # halted, shouldn't happen

    s = z3.Solver()
    c = [z3.Int(f'c_{j}') for j in range(J)]
    v = [z3.Int(f'v_{i}') for i in range(I)]

    # Let c in N^J.
    for j in range(J):
        s.add(c[j] >= 0)
    # Define v := u_k + sum_{j=0}^{J-1} c[j]*F[j].
    for i in range(I):
        s.add(v[i] == u[i]+sum(c[j]*F[j][i] for j in range(J)))
    # v[i] >= 0 for all i in {0, 1, ..., I-1}.
    for i in range(I):
        s.add(v[i] >= 0)
    # v |- halt.
    for inst in F:
        tmp = []
        for i, e in enumerate(inst):
            if e >= 0:
                continue
            tmp.append(v[i]+e < 0)
        s.add(z3.Or(*tmp))

    if s.check() == z3.unsat:
        return f'ISV({steps})'

    # for debugging the probable-halt-certificate. this doesn't prove infinite.
    if 0:
        if s.check() == z3.sat:
            m = s.model()
            m2 = tuple(m[ci].as_long() for ci in c)
            return f'DEBUG(u={u}, c={m2})'

    return None


def bsearch(F: list[list[int]], limit: int = 1000) -> str | None:
    """ get the minimal certificate. intended for researching this decider. """
    out = isv(F, 0)
    if out is not None:
        return out
    out = isv(F, limit)
    if out is None:
        return out
    lo = 0
    hi = limit
    while lo < hi:
        mid = (lo+hi)//2
        out = isv(F, mid)
        if out is None:
            lo = mid+1
        else:
            hi = mid
    return isv(F, hi)


holdouts = parse_file('holdout/sz20_902.txt')
# sys.stdout = open('decider/tmp.txt', 'w')
print(f'running isv on {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]] = []
for F in holdouts:
    result = isv(F, 0)
    if result is None:
        result = isv(F, 1000)
    # result = bsearch(F)
    if result is not None:
        print(f'{unparse_line(F)}, NON-HALT: {result}')
    else:
        holdouts2.append(F)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for F in holdouts2:
    print(unparse_line(F))
