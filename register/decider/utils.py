

def get_fractran_row(sz: int, pos: list[int | None], neg: list[int | None]) -> list[int]:
    pos = [i for i in pos if i is not None]
    neg = [i for i in neg if i is not None]
    assert not (set(pos) & set(neg)), "pos and neg have a common element"
    inst = [0]*sz
    for i in pos:
        inst[i] += 1
    for i in neg:
        inst[i] -= 1
    return inst


def parse_line(li: str) -> list[list[int]]:
    """
    :param li: An RM in the typical format.
    :return: An FM in vector representation. All vectors have the same length.

    In this function, the input RM and output FM will halt in the same number of steps.
    The downside is that the output FM is unoptimized. Use parse_line_opt to get a better output FM.

    This function (informally) proves MBB(n) <= BBf(14*n).
    Warning: The RM must have <=26 instructions and <=10 registers.
    """
    # extract RM
    tokens = [t for t in li.split() if '_' in t]
    assert len(tokens) == 1, "can't find rm"
    li = tokens[0]
    insts = li.split('_')
    n = len(insts)
    # get columns (i.e. fractran primes) ready
    to_col = {chr(ord('A')+i): i for i in range(n)}
    for r in sorted(set(i[0] for i in insts)):
        scratch = len(to_col)
        to_col[r] = scratch
    scratch = len(to_col)
    to_col['*'] = None
    # create fm
    F: list[tuple[int, int]] = []
    for i, inst in zip([chr(ord('A')+i) for i in range(n)], insts):
        if len(inst) == 3:
            c, op, n = inst
            assert '0' <= c <= '9', 'malformed rm'
            assert op == '+', 'malformed rm'
            assert 'A' <= n <= 'Z' or n == '*', 'malformed rm'
            n_col = scratch if n == i else to_col[n]
            same = n == i
            if same:
                scratch += 1
            F.append(get_fractran_row(
                scratch, [to_col[c], n_col], [to_col[i]]))
            if same:  # add mirror instruction
                F.append(get_fractran_row(
                    scratch, [to_col[c], to_col[n]], [scratch-1]))
        elif len(inst) == 4:
            c, op, n, m = inst
            assert '0' <= c <= '9', 'malformed rm'
            assert op == '-', 'malformed rm'
            assert 'A' <= n <= 'Z' or n == '*', 'malformed rm'
            assert 'A' <= m <= 'Z' or m == '*', 'malformed rm'
            n_col = scratch if n == i else to_col[n]
            m_col = scratch if m == i else to_col[m]
            same = n == i or m == i
            if same:
                scratch += 1
            F.append(get_fractran_row(
                scratch, [n_col], [to_col[c], to_col[i]]))
            F.append(get_fractran_row(
                scratch, [m_col], [to_col[i]]))
            if same:  # add mirror instruction
                F.append(get_fractran_row(
                    scratch, [to_col[n]], [to_col[c], scratch-1]))
                F.append(get_fractran_row(
                    scratch, [to_col[m]], [scratch-1]))
        else:
            assert False, 'malformed rm'
    for inst in F:
        while len(inst) < scratch:
            inst.append(0)
        assert len(inst) == scratch  # this should always succeed
    return F


def parse_line_opt(li: str) -> list[list[int]]:
    """
    :param li: An RM in the typical format.
    :return: An FM in vector representation. All vectors have the same length.

    In this function, the input RM and output FM are both halting or both non-halting.
    The output FM is optimized.

    Warning: If the RM has an infinite increment loop, this function will throw.
    Warning: The RM must have <=26 instructions and <=10 registers.
    """
    # extract RM
    tokens = [t for t in li.split() if '_' in t]
    assert len(tokens) == 1, "can't find rm"
    li = tokens[0]
    insts = li.split('_')
    n = len(insts)

    assert False, 'tell the author to finish coding this'


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
