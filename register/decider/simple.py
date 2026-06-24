# python -m register.decider.simple
import sys
from decider.graph_search2 import graph_search2 as plm
from decider.graph_search3 import graph_search3 as pdlm
# from decider.isv import isv  # TODO: is ISV useless for RMs?
from register.decider.utils import parse_file

'''
A script that runs all RM holdouts on a Fractran decider.
'''


def run_decider(F: list[list[int]]) -> str | None:
    result = None
    for EXP_LIM in range(1, 13):
        result = plm(F, EXP_LIM) if result is None else result
    for EXP_LIM in range(1, 13):
        result = pdlm(F, EXP_LIM) if result is None else result
    return result


if __name__ == '__main__':
    holdouts = parse_file('register/holdout/tmp_sz6.txt', opt=False)
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
