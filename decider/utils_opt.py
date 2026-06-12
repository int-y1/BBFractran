import z3


def optimize(F: list[list[int]], lim: int = 100) -> list[list[int]]:
    """
    WARNING: EXPERIMENTAL

    Find forced fraction uses in F.

    For this FM [8/3, 21/10, 49/2, 5/343, 3/7]:
    * 21/10 cannot simplify to 28/5 (denominator would change and the FM's behaviour would change).
    * 3/7 can simplify to 8/7 (denominator stayed the same).

    :param F: An FM in vector representation.
    :param lim: Check up to this many forced fraction uses.
    :return: An optimized FM.
    """
    J = len(F)
    I = len(F[0])

    F2 = []
    for j in range(J):
        s = z3.Solver()
        v = [z3.Int(f'v_{i}') for i in range(I)]
        for i in range(I):
            s.add(v[i] >= 0)
        # F[j] is the instruction used for v
        for inst in F[:j]:
            tmp = []
            for i, e in enumerate(inst):
                if e >= 0:
                    continue
                tmp.append(v[i]+e < 0)
            s.add(z3.Or(*tmp))
        for i, e in enumerate(F[j]):
            if e >= 0:
                continue
            s.add(v[i]+e >= 0)

        # find forced next instruction(s)
        denom = {i: F[j][i] for i in range(I) if F[j][i] < 0}
        diff = [0]*I
        best_diff = [0]*I
        go = True
        go2 = 0
        while go and go2 < lim:
            go = False
            for j2 in range(J):
                # check if F[j]+diff could use F[j2]
                tmp = []
                for i, e in enumerate(F[j2]):
                    if e >= 0:
                        continue
                    tmp.append(v[i]+F[j][i]+diff[i]+e >= 0)
                s_check = s.check(tmp)
                if s_check == z3.unsat:
                    continue
                assert s_check == z3.sat

                # check if F[j]+diff must use F[j2]
                tmp = []
                for i, e in enumerate(F[j2]):
                    if e >= 0:
                        continue
                    tmp.append(v[i]+F[j][i]+diff[i]+e < 0)
                s_check = s.check(z3.Or(*tmp))
                if s_check == z3.unsat:
                    diff = [e0+e1 for e0, e1 in zip(diff, F[j2])]
                    denom2 = {i: F[j][i]+diff[i]
                              for i in range(I) if F[j][i]+diff[i] < 0}
                    if denom == denom2:
                        best_diff = diff
                    go = True
                    go2 += 1
                else:
                    assert s_check == z3.sat
                break
        F2.append([e0+e1 for e0, e1 in zip(F[j], best_diff)])
    return F2
