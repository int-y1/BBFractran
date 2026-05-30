# python -m decider.bp
import sys
import z3
from itertools import permutations
from decider.utils import parse_file, unparse_line

'''
This is an implementation of Beeping Permutation using Z3. BP is an extended version of BISV.

---

In graph_search2.py, read the following: Basic definitions.

You may find isv.py and bisv.py helpful to read, since ISV and BISV are simpler and weaker versions.

For info on the Z3 API, read:
https://microsoft.github.io/z3guide/programming/Z3%20Python%20-%20Readonly/Introduction
You may skip these sections: Machine Arithmetic, Bit Tricks.

---

Definition BP.1. Let k in N. Let p = [p[0], p[1], ..., p[P-1]] be an ordered P-tuple of distinct
elements of {0, 1, ..., J-1}. Note: 0 <= P <= J. Let c[0], c[1], ..., c[P] in N^J. Say that
(k, p, c[0], c[1], ..., c[P]) is a probable-halt-certificate if it satisfies:
* Define u[0] := u_k.
* Let j in {0, 1, ..., J-1} \ p. Then c[j2][j] = 0 for all j2 in {0, 1, ..., P}. (Every value of j
  represents the unused instruction F[j].)
* Let j2 in {0, 1, ..., P-1}. For each value of j2:
  * Define u[j2+1] := u[j2] + sum_{j=0}^{J-1} c[j2][j]*F[j]. Warning: u[j2+1] is in Z^I.
  * u[j2+1][i] >= 0 for all i in {0, 1, ..., I-1}.
  * p[j2] is the next instruction used for u[j2+1]. That is, u[j2+1] |- u[j2+1] + F[p[j2]].
  * c[j2+1][p[j2]] = 1 and c[> j2+1][p[j2]] = 0. That is, F[p[j2]] is used one last time.
* Let j2 := P. For this value of j2:
  * Define u[j2+1] := u[j2] + sum_{j=0}^{J-1} c[j2][j]*F[j]. Warning: u[j2+1] is in Z^I.
  * u[j2+1][i] >= 0 for all i in {0, 1, ..., I-1}.
  * u[j2+1] |- halt.
Note: P = 0 is needed so that there is a probable-halt-certificate when u_k |- halt.

this definition is longer than Definition BISV.1, and probably more tedious.
hopefully there are no bugs in this probable-halt-certificate.


Lemma BP.2. Let k in N. Suppose u_0 |-* u_k. If F is halting, then there exist
p, c[0], c[1], ..., c[P] such that (k, p, c[0], c[1], ..., c[P]) is a probable-halt-certificate.
Proof. ???

this might be true, but looks very annoying to prove.
the proof should be an extension of Lemma BISV.2.


Theorem BP.3. Let k in N. Suppose u_0 |-* u_k. If there does not exist p, c[0], c[1], ..., c[P] such
that (k, p, c[0], c[1], ..., c[P]) is a probable-halt-certificate, then F is non-halting.
Proof. By contradiction of Lemma BP.2.

looks like i need to try all e*J! values of p, and get z3.unsat for all of them.
every holdout will get a readable probable-halt-certificate.
however, a non-halting fm won't get a readable proof.

---

Here are some interesting FMs related to BP.

In Theorem BP.3, k = 0 is usually strong enough. Here are the size 22 FMs that required k > 0:
```
[1/30, 21/2, 28/33, 5/7, 44/5] k=8
[1/30, 44/21, 33/2, 5/11, 28/5] k=8
[2/15, 9/14, 715/2, 7/11, 22/91] k=7
[4/15, 3/14, 275/2, 7/11, 363/5] k=6
[4/15, 3/98, 605/2, 7/5, 14/11] k=2
[5/18, 4/35, 847/2, 3/7, 6/11] k=2
[5/18, 539/2, 4/55, 3/11, 6/7] k=2
[5/6, 4/105, 11011/2, 3/11, 2/13] k=2
[5/6, 4/35, 539/2, 3/11, 605/7] k=6
[5/6, 539/2, 4/35, 3/11, 605/7] k=6
[5/6, 7007/2, 4/165, 3/7, 2/13] k=2
[7/15, 3146/3, 9/455, 5/11, 3/2] k=3
[7/15, 9/385, 3718/3, 5/13, 3/2] k=3
[9/10, 1001/2, 2/21, 5/11, 22/65] k=7
[9/10, 2/21, 1001/2, 5/11, 22/65] k=7
```

I didn't find any FMs that BP can't prove non-halting, but BISV can prove non-halting.

Here are the size 21 FMs that BP can't prove non-halting, but MLI can prove non-halting:
```
[1/15, 14/3, 9/77, 5/7, 33/2, 1/11]
[1/15, 9/77, 14/3, 5/7, 33/2, 1/11]
[9/35, 1/33, 10/3, 11/5, 21/2, 1/7]
```
I found 35 size 22 FMs that BP can't prove non-halting, but MLI can prove non-halting. In all of
these, when the last instruction is removed, BP was able to prove non-halting.
'''


def bisv_z3(F: list[list[int]], s, u, c, p: tuple[int, ...]) -> str | None:
    J = len(F)
    I = len(F[0])
    P = len(p)

    assumptions = []

    # Let j in {0, 1, ..., J-1} \ p. Then c[j2][j] = 0 for all j2 in {0, 1, ..., P}.
    for j in range(J):
        if j in p:
            continue
        for j2 in range(len(c)):
            assumptions.append(c[j2][j] == 0)
    # Let j2 in {0, 1, ..., P-1}.
    for j2 in range(P):
        # p[j2] is the next instruction used for u[j2+1].
        for inst in F[:p[j2]]:
            tmp = []
            for i, e in enumerate(inst):
                if e >= 0:
                    continue
                tmp.append(u[j2+1][i]+e < 0)
            assumptions.append(z3.Or(tmp))
        for i, e in enumerate(F[p[j2]]):
            if e >= 0:
                continue
            assumptions.append(u[j2+1][i]+e >= 0)
        # c[j2+1][p[j2]] = 1 and c[> j2+1][p[j2]] = 0.
        assumptions.append(c[j2+1][p[j2]] == 1)
        for j3 in range(j2+2, len(c)):
            assumptions.append(c[j3][p[j2]] == 0)

    s_check = s.check(assumptions)
    # for debugging the probable-halt-certificate. this doesn't prove infinite.
    if 0:
        if s_check == z3.sat:
            m = s.model()
            mu = [[m[u[j2][i]].as_long() for i in range(I)]
                  for j2 in range(P+2)]
            mc = [[m[c[j2][j]].as_long() for j in range(J)]
                  for j2 in range(P+1)]
            print(F)
            print(p)
            print(mu)
            print(mc)
            print()
    return s_check


def bp(F: list[list[int]], k: int = 1000) -> str | None:
    """ Attempt Theorem BP.3 with k. Try all p, c[0], c[1], ..., c[P]. """
    J = len(F)
    I = len(F[0])

    # get u_k
    uk = [1]+[0]*(I-1)
    for _ in range(k):
        for inst in F:
            for e0, e1 in zip(uk, inst):
                if e0+e1 < 0:
                    break
            else:
                for i in range(I):
                    uk[i] += inst[i]
                break
        else:
            return None  # halted, shouldn't happen

    for P in range(J+1):
        # set up z3. only insert inequalities that use P but don't use p. this makes z3 run faster,
        # but i'm not sure why. maybe creating lots of "z3.Solver()" is slow?
        s = z3.Solver()
        u = [[z3.Int(f'u{j2}_{i}') for i in range(I)] for j2 in range(P+2)]
        c = [[z3.Int(f'c{j2}_{j}') for j in range(J)] for j2 in range(P+1)]

        # Let c[0], c[1], ..., c[P] in N^J.
        for j2 in range(P+1):
            for j in range(J):
                s.add(c[j2][j] >= 0)
        # Define u[0] := u_k.
        for i in range(I):
            s.add(u[0][i] == uk[i])
        # Shared conditions for j2 in {0, 1, ..., P-1} and j2 = P.
        for j2 in range(P+1):
            # Define u[j2+1] := u[j2] + sum_{j=0}^{J-1} c[j2][j]*F[j].
            for i in range(I):
                s.add(u[j2+1][i] == u[j2][i] + sum(c[j2][j]*F[j][i]
                      for j in range(J)))
            # u[j2+1][i] >= 0 for all i in {0, 1, ..., I-1}.
            for i in range(I):
                s.add(u[j2+1][i] >= 0)
        # Let j2 := P. u[j2+1] |- halt.
        j2 = P
        for inst in F:
            tmp = []
            for i, e in enumerate(inst):
                if e >= 0:
                    continue
                tmp.append(u[j2+1][i]+e < 0)
            s.add(z3.Or(tmp))

        for p in permutations(range(J), P):
            result = bisv_z3(F, s, u, c, p)
            assert result != z3.unknown
            if result == z3.sat:
                return None  # failed to use Theorem BP.3

    return f'BP(k={k}, uk={uk})'  # Theorem BP.3 succeeded


def bsearch(F: list[list[int]], limit: int = 1000) -> str | None:
    """ get the minimal certificate. intended for researching this decider. """
    out = bp(F, 0)
    if out is not None:
        return out
    out = bp(F, limit)
    if out is None:
        return out
    lo = 0
    hi = limit
    while lo < hi:
        mid = (lo+hi)//2
        out = bp(F, mid)
        if out is None:
            lo = mid+1
        else:
            hi = mid
    return bp(F, hi)


if __name__ == '__main__':
    holdouts = parse_file('holdout/sz21_345.txt')
    # sys.stdout = open('decider/tmp.txt', 'w')
    print(f'running bp on {len(holdouts)} holdouts')
    print()

    holdouts2: list[list[list[int]]] = []
    for F in holdouts:
        result = bp(F, 1000)
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
