import sys
from itertools import product
from utils import parse_file, unparse_line

'''
This is an implementation of Power Limit Mod. See Theorem PLM.7 for the main idea.

Note: This decider only generates a certificate for n >= -min(F). This keeps the decider simple.

---

Basic definitions:
* N = {0, 1, 2, ...}.
* Z = {..., -2, -1, 0, 1, 2, ...}.
* F is a Fractran program in vector representation. F is a J by I matrix with entries in Z.
  * F contains J instructions, indexed from F[0] to F[J-1].
  * Each instruction has length I. That is, F only uses the first I primes. The primes are
    indexed from F[*][0] to F[*][I-1].
  * min(F) is the minimum element of F. This is usually negative.
  * max(F) is the maximum element of F. This is usually positive.
* u, v represent a Fractran state. A Fractran state is a vector in N^I.
  * u_0 represents the initial Fractran state [1, 0, 0, ...] in N^I.
  * u_k represents the Fractran state after k iterations of F. The initial state is k = 0.
* u |- v means that 1 iteration of F will turn u into v.
  * u |-* v means that >= 0 iterations of F will turn u into v.
  * u |- halt means that u will halt after 1 iteration of F.
  * u |-* halt means that u will halt after >= 0 iterations of F.

---

Definition PLM.1 (AP). Define the set AP(a, d) to be {a+d*i | i in N}. In other words, AP(a, d) is
the set of terms in an arithmetic progression.

Definition PLM.2 (Exp). Let n >= 1. Define Exp(n) to be these 2*n sets:
  AP(0, 0), AP(1, 0), ..., AP(n-1, 0)
  AP(n, n), AP(n+1, n), ..., AP(2*n-1, n)
Note: AP(*, 0) contains 1 element, and could be considered degenerate.
Note: In the code, these 2*n sets are represented as an integer between 0 and 2*n-1.

Example PLM.2b. Exp(3) consists of these 6 sets:
{0}, {1}, {2}, {3, 6, 9, ...}, {4, 7, 10, ...}, {5, 8, 11, ...}

Lemma PLM.3. Let n >= 1. Exp(n) partitions N. (https://en.wikipedia.org/wiki/Partition_of_a_set)
Proof. Left as an exercise to the reader. (This looks like a tedious homework problem.)

Definition PLM.4 (compress_n). Let n >= 1. Let u in N^I be a Fractran state. Define compress_n(u) to
be a vector {0, 1, ..., 2*n-1}^I. Each element of u gets mapped to {0, 1, ..., 2*n-1} using
Definition PLM.2. Also, define compress_n(halt) = halt.

Definition PLM.5 (G_n). Let n >= 1. Define the directed graph G_n = (V_n, E_n) as follows:
* V_n = {0, 1, ..., 2*n-1}^I U {halt}.
* Suppose u |- v. Then E_n contains the edge from compress_n(u) to compress_n(v).
* Suppose u |- halt. Then E_n contains the edge from compress_n(u) to halt.

Note PLM.5b. The hardest part of the code is constructing edges from compress_n(u) to compress_n(v).
Here are the cases you will need to consider:
* Exponents that are <n have 1 choice, and are easy to handle.
* Exponents that are >=n can have 1 or more choices:
  * The 1st choice is to stay >=n. This is always allowed.
  * The 2nd choice is to drop to <n. The exponent must decrease and cross the gap.
  * The 3rd choice is to drop to <0. This does not occur for n >= -min(F). See Lemma PLM.8 for more.

Lemma PLM.6. Suppose u_0 |-* halt. Let n >= 1. G_n contains a path from compress_n(u_0) to halt.
Proof. Let the path to halt be u_0 |- u_1 |- ... |- u_k |- halt. There is an edge from
compress_n(u_i) to compress_n(u_{i+1}), and an edge from compress_n(u_k) to halt. QED.

Theorem PLM.7 (Power Limit Mod). Let n >= 1. Suppose G_n does not contain a path from
compress_n(u_0) to halt. Then F is non-halting (i.e. "u_0 |-* halt" is false).
Proof. By contradiction of Lemma PLM.6.
Note: u_0 could be changed to u_100. However, the decider strength stays the same, since you can
increase n until u_0 to u_100 all have 1 next instruction.

Lemma PLM.8. Let n >= -min(F) (in other words, n + min(F) >= 0). Suppose
compress_n(u) = compress_n(u'). Then F will apply the same instruction to u and u'.
Proof. Take a look at each exponent u[i]:
* If u[i] < n, then u[i] = u'[i]. This exponent will make the same set of instructions unavailable
  for both u and u'.
* If u[i] >= n, then u'[i] >= n as well. Since n + min(F) >= 0, no instruction will make u[i]
  negative. Therefore, this exponent will not make any instructions unavailable.
Both u and u' have the same set of available instructions. The result follows. QED.
Note: For n >= -min(F), the 3rd choice from Note PLM.5b becomes impossible.
'''


def graph_search2(F: list[list[int]], EXP_LIM: int) -> str | None:
    I = len(F[0])

    # Lemma PLM.8: guarantee that the same inst is always used
    for inst in F:
        for e in inst:
            if e+EXP_LIM < 0:
                return None  # EXP_LIM is too small, please retry with a bigger value for EXP_LIM

    # graph theory stuff
    q = [tuple([1]+[0]*(I-1))]  # initially, q only contains compress_n(u_0)
    vis = set(q)
    while q:
        u = q.pop()  # this is compress_n(u)
        for inst in F:
            for e0, e1 in zip(u, inst):
                if e0+e1 < 0:
                    break
            else:
                # use inst, find all possible compress_n(v)
                v_choices = []
                for e0, e1 in zip(u, inst):
                    e = e0+e1
                    while e >= 2*EXP_LIM:
                        e -= EXP_LIM
                    if e < EXP_LIM and e0 >= EXP_LIM:
                        v_choices.append([e, e+EXP_LIM])
                    else:
                        v_choices.append([e])
                # add to queue
                for v in product(*v_choices):
                    if v in vis:
                        continue
                    vis.add(v)
                    q.append(v)
                break
        else:
            return None  # found a path from compress_n(u_0) to halt

    # Theorem PLM.7 is applicable
    return f'GRAPH_SEARCH2({EXP_LIM})'


holdouts = parse_file('../holdout/sz19_231.txt')
# sys.stdout = open('tmp.txt', 'w')
print(f'running graph_search2 on {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]] = []
for F in holdouts:
    for EXP_LIM in range(1, 13):
        result = graph_search2(F, EXP_LIM)
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
