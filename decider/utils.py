from sympy import factorint, prime, primepi


def parse_line(li: str) -> list[list[int]]:
    """
    :param li: An FM in the format `[x/x, x/x, x/x]` where each `x` is a positive integer.
    :return: An FM in vector representation. All vectors have the same length.
    """
    # extract list of numbers
    assert li.count('[') == 1, "can't find start of fm"
    assert li.count(']') == 1, "can't find end of fm"
    li = li[li.index('[')+1:li.index(']')]
    assert len(li) > 0, "fm can't be empty"
    fm: list[tuple[int, int]] = []
    for f in li.split(','):
        f1, f2 = f.strip().split('/')
        fm.append((int(f1), int(f2)))
    # convert to vector representation
    F: list[list[int]] = []
    I = 0
    for f1, f2 in fm:
        inst: list[int] = []
        for p, e in factorint(f1).items():
            p = primepi(p)-1
            I = max(I, p+1)
            while len(inst) < I:
                inst.append(0)
            inst[p] += e
        for p, e in factorint(f2).items():
            p = primepi(p)-1
            I = max(I, p+1)
            while len(inst) < I:
                inst.append(0)
            inst[p] -= e
        F.append(inst)
    for inst in F:
        while len(inst) < I:
            inst.append(0)
        assert len(inst) == I  # this should always succeed
    return F


def parse_file(file: str) -> list[list[list[int]]]:
    """
    :param file: A path to a file. The file should contain FMs parseable by `parse_line`.
    :return: A list of FMs in vector representation.
    """
    Fs = []
    with open(file) as f:
        for li in f.read().split('\n'):
            if li.count('[') != 1 or li.count(']') != 1:
                continue
            Fs.append(parse_line(li))
    return Fs


def unparse_line(F: list[list[int]], format: int = 0) -> str:
    """
    The inverse of `parse_line`.

    :param F: An FM in vector representation.
    :param format:
        0 is the format `[x/x, x/x, x/x]` where each `x` is a positive integer.
        1 is vector representation, as a pretty-printed string.
        2 is vector representation, in C++ format.
    :return: An FM as a string.
    """
    if format == 0:
        fm = []
        for inst in F:
            f1 = 1
            f2 = 1
            for i, e in enumerate(inst):
                if e > 0:
                    f1 *= prime(i+1)**e
                if e < 0:
                    f2 *= prime(i+1)**(-e)
            fm.append(f'{f1}/{f2}')
        return '['+', '.join(fm)+']'
    elif format == 1:
        return '\n'.join(' '.join(map(lambda i: f'{i: 2d}', inst)) for inst in F)
    elif format == 2:
        return '{{'+'},{'.join(','.join(map(str, inst)) for inst in F)+'}}'
    else:
        assert False, 'unknown format'
