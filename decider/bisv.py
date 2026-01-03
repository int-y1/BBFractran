import sys
import z3
from utils import parse_file, unparse_line

'''
bisv (Beeping Integer Spanning Vectors + Z3)
this is a stronger version of the "integer spanning vectors" decider

* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* let u1 be any state reached by the fm
* let fraction_beep be the next fraction to be used for u1
* use z3 to find integer coefficients c_0, c_1, c_2, ... and d_0, d_1, d_2, ... where
  * every c_j >= 0
  * u2 = u1 + sum(c_j * fraction_j)
  * every element of u2 is >= 0
  * fraction_beep is the next fraction to be used for u2 (u2 always exists, because c_j = 0 results in u2 = u1)
  * every d_j >= 0
  * d_beep = 1 (the beep fraction is used for the last time)
  * u3 = u2 + sum(d_j * fraction_j)
  * every element of u3 is >= 0
  * u3 does not trigger any fraction
* if z3 says "z3.unsat", the program is non-halt and the certificate is (u1, beep, unsat_core).
  * TODO: unsat_core is hard to read
'''
def bisv_z3(prog: list[list[int]],u1: list[int],beep: int) -> str|None:
    maxidx=len(prog[0])

    s=z3.Solver()
    s.set("unsat_core", True)
    c=[z3.Int(f'c_{j}') for j in range(len(prog))]
    d=[z3.Int(f'd_{j}') for j in range(len(prog))]
    u2=[z3.Int(f'u2_{i}') for i in range(maxidx)]
    u3=[z3.Int(f'u3_{i}') for i in range(maxidx)]
    assumptions=[]  # for s.unsat_core()

    # every c_j >= 0
    for j in range(len(prog)): s.add(c[j]>=0)
    # u2 = u1 + sum(c_j * fraction_j)
    for i in range(maxidx): s.add(u2[i]==u1[i]+sum(c[j]*prog[j][i] for j in range(len(prog))))
    # every element of u2 is >= 0
    for i in range(maxidx): s.add(u2[i]>=0)
    # fraction_beep is the next fraction to be used for u2
    for f in prog[:beep]:
        tmp=[]
        for i,v in enumerate(f):
            if v>=0: continue
            tmp.append(u2[i]+v<0)
        assumptions.append(z3.Or(*tmp))
    for i,v in enumerate(prog[beep]):
        if v>=0: continue
        assumptions.append(u2[i]+v>=0)
    # every d_j >= 0
    for j in range(len(prog)): s.add(d[j]>=0)
    # d_beep = 1
    s.add(d[beep]==1)
    # u3 = u2 + sum(d_j * fraction_j)
    for i in range(maxidx): s.add(u3[i]==u2[i]+sum(d[j]*prog[j][i] for j in range(len(prog))))
    # every element of u3 is >= 0
    for i in range(maxidx): s.add(u3[i]>=0)
    # u3 does not trigger any fraction
    for f in prog:
        tmp=[]
        for i,v in enumerate(f):
            if v>=0: continue
            tmp.append(u3[i]+v<0)
        assumptions.append(z3.Or(*tmp))

    s_check=s.check(assumptions)
    #assert s_check!=z3.unknown, "z3 couldn't determine sat/unsat"
    if s_check==z3.unsat:
        return f'BISV(u1={u1}, beep={prog[beep]}, unsat_core={list(s.unsat_core())})'

    if 0:  # for debugging. this doesn't prove infinite.
        if s_check==z3.sat:
            m=s.model()
            mc=tuple(m[cj].as_long() for cj in c)
            md=tuple(m[dj].as_long() for dj in d)
            return f'DEBUG(u1={u1}, c={mc}, d={md})'

    return None

# find (u1, beep) to use in bisv_z3
def bisv(prog: list[list[int]],limit: int=1000) -> str|None:
    maxidx=len(prog[0])

    # run steps
    cand_u1: list[None|list[int]]=[None]*len(prog)
    u=[1]+[0]*(maxidx-1)
    for _ in range(limit):
        for j,f in enumerate(prog):
            for e0,e1 in zip(u,f):
                if e0+e1<0: break
            else:
                cand_u1[j]=list(u)
                for i in range(maxidx): u[i]+=f[i]
                break
        else:
            return None  # halted, shouldn't happen

    for beep in range(len(prog)):
        u1=cand_u1[beep]
        if u1 is None: continue
        result=bisv_z3(prog,u1,beep)
        if result is not None: return result

    return None

# get the minimal certificate. intended for researching this decider.
def bsearch(prog: list[list[int]],limit: int=1000) -> str|None:
    out=bisv(prog,limit)
    if out is None: return out
    lo=0
    hi=limit
    while lo<hi:
        mid=(lo+hi)//2
        out=bisv(prog,mid)
        if out is None: lo=mid+1
        else: hi=mid
    return bisv(prog,hi)

holdouts=parse_file('../holdout/sz20_6.txt')
#sys.stdout=open('tmp.txt','w')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]]=[]
for prog in holdouts:
    result=bisv(prog,1000)
    #result=bsearch(prog)
    if result is not None:
        print(f'{unparse_line(prog)}, NON-HALT: {result}')
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2: print(unparse_line(prog))
