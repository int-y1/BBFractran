import sys
#sys.stdout=open('tmp.txt','w')
from itertools import product
from utils import parse_file, unparse_line

'''
idea of graph_search2 (Power Limit Mod)


* EXP_LIM is the exponent limit
* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* do a graph search, but limit the exponents to 2*EXP_LIM different groups
  * split into 2 groups, <EXP_LIM and >=EXP_LIM
  * split into EXP_LIM groups, the groups are mod EXP_LIM
  * (the code used the numbers 0,1,...,2*EXP_LIM-1 to represent these groups)
* if halting never occurs, the program runs forever
'''
def graph_search2(prog,EXP_LIM):
    maxidx=len(prog[0])
    # graph theory stuff
    q=[tuple([1]+[0]*(maxidx-1))]
    vis=set(q)

    # guarantee that the same inst is always used
    for tmp in prog:
        for e in tmp:
            if e+EXP_LIM<0: return None

    while q:
        u=q.pop()
        for inst in prog:
            for e0,e1 in zip(u,inst):
                if e0+e1<0: break
            else:
                # inst matches, get next states
                v0=[]
                for e0,e1 in zip(u,inst):
                    r0=e0+e1
                    while r0>=2*EXP_LIM: r0-=EXP_LIM
                    if r0<EXP_LIM and e0>=EXP_LIM: v0.append([r0,r0+EXP_LIM])
                    else: v0.append([r0])
                # add to queue
                for v in product(*v0):
                    if v in vis: continue
                    vis.add(v)
                    q.append(v)
                break
        else:
            return None

    return f'GRAPH_SEARCH2({EXP_LIM})'

holdouts=parse_file('../holdout/sz19_231.txt')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2=[]
for prog in holdouts:
    for EXP_LIM in range(1,13):
        result=graph_search2(prog,EXP_LIM)
        if result is not None:
            print(f'{unparse_line(prog)}, NON-HALT: {result}')
            break
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2: print(unparse_line(prog))
