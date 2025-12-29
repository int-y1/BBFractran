import sys
#sys.stdout=open('tmp.txt','w')
from itertools import product
from utils import parse_file, unparse_line

'''
idea of lin_comb

* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* find coefficients c_a, c_b, c_c, c_d, ... that satisfy
  * c_a > 0, starting number is positive
  * if sum(i*c_i) > 0, a fraction can be used
  * for each fraction, sum(i*c_i) stays the same or increases
* if coefficients exist, the program is non-halt, and the certificate is LIN_COMB(c_a, c_b, c_c, c_d, ...)
'''

def lin_comb(prog,EXP_LIM):
    maxidx=len(prog[0])
    usable=[0]*maxidx
    for tmp in prog:
        use2=[i for i in range(maxidx) if tmp[i]<-1]
        use1=[i for i in range(maxidx) if tmp[i]==-1]
        if not use2 and len(use1)==1: usable[use1[0]]=1
    if not usable[0]: return '?'

    c0=[list(range(1,EXP_LIM+1))]
    for i in range(1,maxidx):
        if usable[i]: c0.append(list(range(-EXP_LIM,EXP_LIM+1)))
        else: c0.append(list(range(-EXP_LIM,1)))
    for c in product(*c0):
        # every inst should be >=0
        for tmp in prog:
            if sum(i*j for i,j in zip(c,tmp))<0: break
        else:
            return str(c)

    return '?'

# clean up holdouts
holdouts=parse_file('../holdout/sz17_162.txt')

print(f'attempt to solve {len(holdouts)} holdouts')
print()

holdouts2=[]
for prog in holdouts:
    for EXP_LIM in range(1,7):
        result=lin_comb(prog,EXP_LIM)
        if result!='?':
            print(f'{unparse_line(prog)}, NON-HALT: LIN_COMB{result}')
            break
    else:
        #print('  holdout',prog)
        holdouts2.append(prog)

print()
print(f'{len(holdouts2)} holdouts remaining')
print()
for prog in holdouts2: print(unparse_line(prog))
