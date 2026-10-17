# python -m other.gen_lean_ndpc
import os
from decider.nd_progress import nd_progress_cert
from decider.nd_progress_to_lean import nd_progress_to_lean
from decider.utils import parse_file, unparse_line
from other.gen_lean import fm_to_summary


def fm_to_lean_file(holdout_file, holdout_number, F):
    filename = f'{holdout_file.capitalize()}_{holdout_number}.lean'
    cert = nd_progress_cert(F, time_budget=0)
    assert cert is not None, f'no cert for {unparse_line(F)}'
    proof = nd_progress_to_lean(F, cert, f'{holdout_file.capitalize()}_{holdout_number}')
    return filename, proof

SIZE = 23
if SIZE == 23:
    holdout_directory = 'Size23_ndpc'
    holdouts_before = parse_file(f'holdout/sz23_8021.txt')
    holdouts_after = parse_file(f'holdout/sz23_694.txt')
    holdout_file = f'Sz23_{len(holdouts_before) - len(holdouts_after)}'  # mock filename, doesn't really exist
else:
    assert False, 'unsupported SIZE'

os.makedirs(f'other/lean/{holdout_directory}', exist_ok=True)
holdouts_avoid = set(str(F) for F in holdouts_after)
holdouts = [F for F in holdouts_before if str(F) not in holdouts_avoid]
assert len(holdouts) == len(holdouts_before) - len(holdouts_after)
summary1 = []
summary2 = []

for Fi, F in enumerate(holdouts):
    filename, proof = fm_to_lean_file(holdout_file, Fi+1, F)
    with open(f'other/lean/{holdout_directory}/{filename}', 'w', encoding='utf-8') as f:
        f.write(proof)
    s1, s2 = fm_to_summary(holdout_directory, holdout_file, Fi+1, F)
    summary1.append(s1)
    summary2.append(s2)

with open(f'other/lean/{holdout_directory}Summary.lean', 'w', encoding='utf-8') as f:
    f.write(''.join(summary1+summary2))
