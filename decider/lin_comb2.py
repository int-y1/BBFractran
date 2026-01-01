import sys
#sys.stdout=open('tmp.txt','w')
import z3
from utils import parse_file, unparse_line

'''
idea of lin_comb2 (Linear Combination + Z3)

* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* use z3 to find coefficients c_a, c_b, c_c, c_d, ... that satisfy
  * c_a > 0, starting number is positive
  * if sum(i*c_i) > 0, a fraction can be used
  * for each fraction, sum(i*c_i) stays the same or increases
* if coefficients exist, the program is non-halt, and the certificate is LIN_COMB(c_a, c_b, c_c, c_d, ...)
'''
def lin_comb2(prog: list[list[int]]) -> str|None:
    maxidx=len(prog[0])
    usable=[0]*maxidx
    for tmp in prog:
        use2=[i for i in range(maxidx) if tmp[i]<-1]
        use1=[i for i in range(maxidx) if tmp[i]==-1]
        if not use2 and len(use1)==1: usable[use1[0]]=1
    if not usable[0]: return None

    s=z3.Solver()
    c=[z3.Int(f'c_{i}') for i in range(maxidx)]

    s.add(c[0]>0)
    for i in range(1,maxidx):
        if not usable[i]: s.add(c[i]<=0)
    for f in prog:
        s.add(sum(ci*fi for ci,fi in zip(c,f))>=0)

    if s.check()==z3.sat:
        m=s.model()
        m2=tuple(m[ci].as_long() for ci in c)
        return f'LIN_COMB2{m2}'

    return None

holdouts=parse_file('../holdout/sz19_84.txt')
print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2: list[list[list[int]]]=[]
for prog in holdouts:
    result=lin_comb2(prog)
    if result is not None:
        print(f'{unparse_line(prog)}, NON-HALT: {result}')
    else:
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2: print(unparse_line(prog))
