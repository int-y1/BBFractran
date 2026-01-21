import sys
from itertools import product
from utils import parse_file, unparse_line

'''
This is an implementation of Power Difference Limit Mod. The main idea is similar to
graph_search2.py, and the main difference is the definition of compress_n.

Note: This decider only generates a certificate for n > |max(F)| + |min(F)|. This keeps the decider
simple.

---

In graph_search2.py, read the following:
Basic definitions, Definition PLM.1, Definition PLM.2, Lemma PLM.3.

---

Definition PDLM.1 (compress_n). Let n >= 1. Let u in N^I be a Fractran state. Let p be a ranking of
u. That is, {p[0], p[1], ..., p[I-1]} = {0, 1, ..., I-1} and u[p[0]] <= u[p[1]] <= ... <= u[p[I-1]].
If there is a tie u[p[i]] = u[p[i+1]], tiebreak with p[i] < p[i+1].
Let f be a mapping from N to {0, 1, ..., 2*n-1} according to Definition PLM.2 and Lemma PLM.3.
Define compress_n(u) to be a list of I pairs:
* The 1st pair is (f(u[p[0]]), p[0]).
* The i'th pair is (f(u[p[i-1]]-u[p[i-2]]), p[i-1])
Note: compress_n(u) is in ({0, 1, ..., 2*n-1} X {0, 1, ..., I-1})^I.
Note: Tiebreaking only matters from a practical perspective. It will make the graph search faster.

Definition PDLM.2 (G_n). Let n >= 1. Define the directed graph G_n = (V_n, E_n) as follows:
* V_n = ({0, 1, ..., 2*n-1} X {0, 1, ..., I-1})^I U {halt}.
* Suppose u |- v. Then E_n contains the edge from compress_n(u) to compress_n(v).
* Suppose u |- halt. Then E_n contains the edge from compress_n(u) to halt.
Note: This is similar to Definition PLM.5.

Note PDLM.2b. The hardest part of the code is constructing edges from compress_n(u) to
compress_n(v). It is highly recommended to only support n > |max(F)| + |min(F)| (see Lemma PDLM.6).

Lemma PDLM.3. Suppose u_0 |-* halt. Let n >= 1. G_n contains a path from compress_n(u_0) to halt.
Proof. Similar proof as Lemma PLM.6.

Theorem PDLM.4 (Power Difference Limit Mod). Let n >= 1. Suppose G_n does not contain a path from
compress_n(u_0) to halt. Then F is non-halting (i.e. "u_0 |-* halt" is false).
Proof. By contradiction of Lemma PDLM.3.
Note: u_0 could be changed to u_100. However, the decider strength stays the same, since you can
increase n until u_0 to u_100 all have 1 next instruction.

Lemma PDLM.5. Let n >= -min(F) (in other words, n + min(F) >= 0). Suppose
compress_n(u) = compress_n(u'). Then F will apply the same instruction to u and u'.
Proof. Similar proof as Lemma PLM.8. The statement "If u[i] < n, then u[i] = u'[i]" is still true,
but the explanation is much more detailed (and tedious).

Lemma PDLM.6. Let n > |max(F)| + |min(F)|. Suppose u |- v. If u[i] - u[j] >= n, then
v[i] - v[j] > 0.
Proof. In the worst case, v[i] = u[i] - |min(F)| and v[j] = u[j] + |max(F)|. The inequality
v[i] - v[j] > 0 will still hold.
Note: The requirement "n > |max(F)| + |min(F)|" makes the code easier to write. The ranking p will
be more stable and easier to work with.
'''


def graph_search3(F: list[list[int]], EXP_LIM: int) -> str | None:
    I = len(F[0])

    # Lemma PDLM.5: guarantee that the same inst is always used
    # Lemma PDLM.6: guarantee that 1 inst doesn't change order by much
    max_e = 0
    min_e = 0
    for inst in F:
        for e in inst:
            max_e = max(max_e, e)
            min_e = min(min_e, e)
    if EXP_LIM < abs(max_e)+abs(min_e)+1:
        return None

    # graph theory stuff
    u0 = []
    for i in range(1, I):
        u0 += [0, i]
    u0 += [1, 0]
    q = [tuple(u0)]  # initially, q only contains compress_n(u_0)
    vis = set(q)
    while q:
        uu = q.pop()
        # get representatives of uu=compress_n(u)
        u0 = []
        for i in range(I):
            if uu[i*2] < EXP_LIM:
                u0.append([uu[i*2]])
            else:
                u0.append([uu[i*2], uu[i*2]+EXP_LIM])
            u0.append([uu[i*2+1]])
        for u1 in product(*u0):
            u = [0]*I
            u[u1[1]] = u1[0]
            for i in range(1, I):
                u[u1[i*2+1]] = u[u1[i*2-1]]+u1[i*2]
            # u is a representative of uu
            for inst in F:
                for e0, e1 in zip(u, inst):
                    if e0+e1 < 0:
                        break
                else:
                    # use inst, find vv=compress_n(v)
                    vv = []
                    value0 = 0
                    for value1, i in sorted((e[0]+e[1], i) for i, e in enumerate(zip(u, inst))):
                        tmp = value1-value0
                        while tmp >= 2*EXP_LIM:
                            tmp -= EXP_LIM
                        vv += [tmp, i]
                        value0 = value1
                    vv = tuple(vv)
                    if vv not in vis:
                        vis.add(vv)
                        q.append(vv)
                    break
            else:
                return None  # found a path from compress_n(u_0) to halt

    # Theorem PDLM.4 is applicable
    return f'GRAPH_SEARCH3({EXP_LIM})'


holdouts = parse_file('../holdout/sz20_279.txt')
# sys.stdout = open('tmp.txt', 'w')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]] = []
for F in holdouts:
    for EXP_LIM in range(1, 13):
        result = graph_search3(F, EXP_LIM)
        if result is not None:
            print(f'{unparse_line(F)}, NON-HALT: {result}')
            break
    else:
        holdouts2.append(F)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for F in holdouts2:
    print(unparse_line(F))
