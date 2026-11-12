# python -m register.decider.simple
import sys
from decider.graph_plm import graph_plm
from decider.graph_pdlm import graph_pdlm
from decider.oned_progress import oned_progress
from decider.nd_progress import nd_progress
from decider.ndr_progress import ndr_progress
from register.decider.utils import parse_file

'''
A script that runs all RM holdouts on a Fractran decider.
'''


def run_decider(F: list[list[int]]) -> str | None:
    result = None
    for EXP_LIM in range(1, 13):
        result = graph_plm(F, EXP_LIM) if result is None else result
    for EXP_LIM in range(1, 13):
        result = graph_pdlm(F, EXP_LIM) if result is None else result
    # result = oned_progress(F) if result is None else result
    # result = nd_progress(F) if result is None else result
    # result = ndr_progress(F) if result is None else result
    return result


if __name__ == '__main__':
    holdouts = parse_file('register/holdout/sz7_9831.txt')
    # sys.stdout = open('register/decider/tmp_simple_sz6.txt', 'w')
    print(f'running simple.py on {len(holdouts)} holdouts')
    print()

    holdouts2: list[str] = []
    for rm, F in holdouts:
        result = run_decider(F)
        if result is not None:
            print(f'{rm}, NON-HALT: {result}')
        else:
            holdouts2.append(rm)

    print()
    print(f'{len(holdouts2)} holdouts remaining')
    print()
    for rm in holdouts2:
        print(rm)
