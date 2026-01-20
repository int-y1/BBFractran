import sys
import z3
from utils import parse_file, unparse_line

'''
This is an implementation of Linear Combination using Z3. See Definition LC.2 and Theorem LC.5 for
the main idea.

---

In graph_search2.py, read the following: Basic definitions.

For info on the Z3 API, read:
https://microsoft.github.io/z3guide/programming/Z3%20Python%20-%20Readonly/Introduction
You may skip these sections: Machine Arithmetic, Bit Tricks.

---

Definition LC.1. Let i in {0, 1, ..., I-1}. Say that i is "usable" if the following holds:
* There exists an instruction F[j] where F[j][i] = -1, and F[j][*] >= 0 elsewhere.

Definition LC.2. Let c in Z^I. Say that c is a certificate if it satisfies:
* c ⋅ u_0 > 0, where "⋅" is the dot product.
* For all i in {0, 1, ..., I-1}, if c[i] > 0 then i is usable.
* c ⋅ F[j] >= 0 for all instructions F[j] (j in {0, 1, ..., J-1}).
Note: The first condition may be changed to c ⋅ u_100 > 0. However, in practice, this decided very
few extra FMs.

Lemma LC.3. Let c in Z^I be a certificate. Suppose u_0 |-* u_k. Then c ⋅ u_k > 0.
Proof. Firstly, c ⋅ u_0 > 0. Secondly, since c ⋅ F[j] >= 0 for all instructions F[j], we have
c ⋅ u_0 <= c ⋅ u_1 <= ... <= c ⋅ u_k. The result follows. QED.

Lemma LC.4. Let c in Z^I be a certificate. Suppose c ⋅ u > 0. Then F does not halt on u (i.e.
"u |- halt" is false).
Proof. Note that c in Z^I, u in N^I, and c ⋅ u > 0. Therefore, there exists an index i such that
c[i] > 0 and u[i] > 0. c[i] > 0 means that i is usable. Therefore, there is an instruction that can
be used, and F does not halt on u. QED.

Theorem LC.5. Let c in Z^I be a certificate. Then F does not halt (i.e. "u_0 |-* halt" is false).
Proof. Use induction with Lemma LC.3 and Lemma LC.4.
'''


def lin_comb2(prog: list[list[int]]) -> str | None:
    maxidx = len(prog[0])
    usable = [0]*maxidx
    for tmp in prog:
        use2 = [i for i in range(maxidx) if tmp[i] < -1]
        use1 = [i for i in range(maxidx) if tmp[i] == -1]
        if not use2 and len(use1) == 1:
            usable[use1[0]] = 1

    s = z3.Solver()
    c = [z3.Int(f'c_{i}') for i in range(maxidx)]

    # c ⋅ u_0 > 0. It simplifies to c[0] > 0.
    s.add(c[0] > 0)
    # For all i in {0, 1, ..., I-1}, if c[i] > 0 then i is usable.
    for i in range(maxidx):
        if not usable[i]:
            s.add(c[i] <= 0)
    # c ⋅ F[j] >= 0 for all instructions F[j].
    for f in prog:
        s.add(sum(ci*fi for ci, fi in zip(c, f)) >= 0)

    if s.check() == z3.sat:
        m = s.model()
        m2 = tuple(m[ci].as_long() for ci in c)
        # Theorem LC.5 is applicable
        return f'LIN_COMB2{m2}'

    return None


holdouts = parse_file('../holdout/sz19_84.txt')
# sys.stdout=open('tmp.txt','w')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]] = []
for prog in holdouts:
    result = lin_comb2(prog)
    if result is not None:
        print(f'{unparse_line(prog)}, NON-HALT: {result}')
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2:
    print(unparse_line(prog))
