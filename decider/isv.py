import sys
#sys.stdout=open('tmp.txt','w')
import z3
from utils import parse_file, unparse_line

'''
isv (Integer Spanning Vectors + Z3)
this is a stronger version of the original "spanning vectors" decider

* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* use z3 to find integer coefficients c_0, c_1, c_2, ... where
  * every c_j >= 0
  * s_final = u + sum(c_j * fraction_j), where u is any state reached by the fm (initially, u=[1, 0, 0, ...])
  * every element of s_final is >= 0
  * s_final does not trigger any fraction
* if z3 says "z3.unsat", the program is non-halt
'''
def isv(prog,steps):
    maxidx=len(prog[0])

    # run steps
    u=[1]+[0]*(maxidx-1)
    for _ in range(steps):
        for f in prog:
            for e0,e1 in zip(u,f):
                if e0+e1<0: break
            else:
                for i in range(maxidx): u[i]+=f[i]
                break
        else:
            return None  # halted, shouldn't happen

    s=z3.Solver()
    c=[z3.Int(f'c_{j}') for j in range(len(prog))]
    sfinal=[z3.Int(f's_final_{i}') for i in range(maxidx)]

    for j in range(len(prog)): s.add(c[j]>=0)
    for i in range(maxidx): s.add(sfinal[i]==u[i]+sum(c[j]*prog[j][i] for j in range(len(prog))))
    for i in range(maxidx): s.add(sfinal[i]>=0)
    for f in prog:
        tmp=[]
        for i,v in enumerate(f):
            if v>=0: continue
            tmp.append(sfinal[i]+v<0)
        s.add(z3.Or(*tmp))

    if s.check()==z3.unsat:
        return f'ISV({steps})'

    if 0:  # for debugging. this doesn't prove infinite.
        if s.check()==z3.sat:
            m=s.model()
            m2=tuple(m[ci].as_long() for ci in c)
            return f'DEBUG(u={u}, c={m2})'

    return None

# get the minimal certificate. intended for researching this decider.
def bsearch(prog,limit=1000):
    out=isv(prog,0)
    if out is not None: return out
    out=isv(prog,limit)
    if out is None: return out
    lo=0
    hi=limit
    while lo<hi:
        mid=(lo+hi)//2
        out=isv(prog,mid)
        if out is None: lo=mid+1
        else: hi=mid
    return isv(prog,hi)

holdouts=parse_file('../holdout/sz20_902.txt')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2=[]
for prog in holdouts:
    result=isv(prog,0)
    if result is None: result=isv(prog,1000)
    #result=bsearch(prog)
    if result is not None:
        print(f'{unparse_line(prog)}, NON-HALT: {result}')
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2: print(unparse_line(prog))
