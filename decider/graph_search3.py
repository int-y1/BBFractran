import sys
#sys.stdout=open('tmp.txt','w')
from itertools import product
from utils import parse_file, unparse_line

'''
idea of graph_search3 (Power Difference Limit Mod)


* EXP_LIM is the exponent limit
* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* partition the natural numbers into 2*EXP_LIM groups
  * {0}, {1}, ..., {EXP_LIM-1}
  * {EXP_LIM*k+0, k>=1}, {EXP_LIM*k+1, k>=1}, ..., {EXP_LIM*k+(EXP_LIM-1), k>=1}
  * (the code uses the numbers 0,1,...,2*EXP_LIM-1 to represent these groups)
* suppose there are n primes used. represent each state using 2*n numbers like this:
  * use a 2*EXP_LIM group
  * mention a prime
  * repeat until all primes are mentioned
  * (there are (2*EXP_LIM)^n * n! possible states)
* do a graph search
* if halting never occurs, the program runs forever

todo: this is a confusing description. describe it better
'''
def graph_search3(prog: list[list[int]],EXP_LIM: int) -> str|None:
    maxidx=len(prog[0])
    # graph theory stuff
    u=[]
    for i in range(1,maxidx): u+=[0,i]
    u+=[1,0]
    q=[tuple(u)]
    vis=set(q)

    # guarantee that the same inst is always used
    # also guarantee that 1 inst doesn't change order by much
    min_e=0
    max_e=0
    for tmp in prog:
        for e in tmp:
            min_e=min(min_e,e)
            max_e=max(max_e,e)
    if EXP_LIM < abs(min_e)+abs(max_e)+1: return None

    while q:
        uu=q.pop()
        u0=[]
        for i in range(maxidx):
            if uu[i*2]<EXP_LIM: u0.append([uu[i*2]])
            else: u0.append([uu[i*2],uu[i*2]+EXP_LIM])
            u0.append([uu[i*2+1]])
        for u1 in product(*u0):
            u=[0]*maxidx
            u[u1[1]]=u1[0]
            for i in range(1,maxidx): u[u1[i*2+1]]=u[u1[i*2-1]]+u1[i*2]
            # finished calculating u
            for inst in prog:
                for e0,e1 in zip(u,inst):
                    if e0+e1<0: break
                else:
                    # inst matches, get next state
                    vv=[]
                    value0=0
                    for value1,i in sorted((e[0]+e[1],i) for i,e in enumerate(zip(u,inst))):
                        tmp=value1-value0
                        while tmp>=2*EXP_LIM: tmp-=EXP_LIM
                        vv+=[tmp,i]
                        value0=value1
                    vv=tuple(vv)
                    if vv not in vis:
                        vis.add(vv)
                        q.append(vv)
                    break
            else:
                return None

    return f'GRAPH_SEARCH3({EXP_LIM})'

holdouts=parse_file('../holdout/sz20_279.txt')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]]=[]
for prog in holdouts:
    for EXP_LIM in range(1,13):
        result=graph_search3(prog,EXP_LIM)
        if result is not None:
            print(f'{unparse_line(prog)}, NON-HALT: {result}')
            break
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2: print(unparse_line(prog))
