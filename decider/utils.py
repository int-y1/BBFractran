from sympy import factorint,prime,primepi

# In: An FM in the format '[x/x, x/x, x/x]' where each 'x' is a positive integer.
# Out: An FM in vector representation. All vectors have the same length.
def parse_line(li: str) -> list[list[int]]:
    # extract list of numbers
    assert li.count('[')==1, "can't find start of fm"
    assert li.count(']')==1, "can't find end of fm"
    li=li[li.index('[')+1:li.index(']')]
    assert len(li)>0, "fm can't be empty"
    prog: list[tuple[int,int]]=[]
    for f in li.split(','):
        i,j=f.strip().split('/')
        prog.append((int(i),int(j)))
    # convert to vector representation
    prog2: list[list[int]]=[]
    maxidx=0
    for i,j in prog:
        f: list[int]=[]
        for p,cnt in factorint(i).items():
            p=primepi(p)-1
            maxidx=max(maxidx,p)
            while len(f)<=maxidx: f.append(0)
            f[p]+=cnt
        for p,cnt in factorint(j).items():
            p=primepi(p)-1
            maxidx=max(maxidx,p)
            while len(f)<=maxidx: f.append(0)
            f[p]-=cnt
        prog2.append(f)
    for f in prog2:
        while len(f)<=maxidx: f.append(0)
        assert len(f)==maxidx+1  # this should always succeed
    return prog2

# In: A path to a file. The file should contain FMs parseable by parse_line.
# Out: A list of FMs in vector representation.
def parse_file(file: str) -> list[list[list[int]]]:
    progs=[]
    with open(file) as f:
        for li in f.read().split('\n'):
            if li.count('[')!=1 or li.count(']')!=1: continue
            progs.append(parse_line(li))
    return progs

# The inverse of parse_line.
# format=0 is the format '[x/x, x/x, x/x]' where each 'x' is a positive integer.
# format=1 is vector representation, as a pretty-printed string.
# format=2 is vector representation, in C++ format.
# In: An FM in vector representation.
# Out: An FM as a string.
def unparse_line(prog: list[list[int]],format: int=0) -> str:
    if format==0:
        out=[]
        for f in prog:
            f1=1
            f2=1
            for i,e in enumerate(f):
                if e>0: f1*=prime(i+1)**e
                if e<0: f2*=prime(i+1)**(-e)
            out.append(f'{f1}/{f2}')
        return '['+', '.join(out)+']'
    elif format==1:
        return '\n'.join(' '.join(map(lambda i:f'{i: 2d}',f)) for f in prog)
    elif format==2:
        return '{{'+'},{'.join(','.join(map(str,f)) for f in prog)+'}}'
    else:
        assert False, 'unknown format'
