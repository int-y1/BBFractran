# python -m other.gen_lean_rm_1dpc
import os
from decider.oned_progress import oned_progress_cert
from decider.oned_progress_to_lean import oned_progress_to_lean
from register.decider.utils import parse_file
from other.gen_lean import fm_to_summary


def fm_to_lean_file(holdout_file, holdout_number, F01):
    filename = f'{holdout_file.capitalize()}_{holdout_number}.lean'
    cert = oned_progress_cert(F01[1])
    assert cert is not None, f'no cert for {F01[0]}'
    proof = oned_progress_to_lean(F01[1], cert, f'{holdout_file.capitalize()}_{holdout_number}')
    return filename, proof

SIZE = 8
if SIZE == 8:
    holdout_directory = 'Size8RM_1dpc'
    holdouts_before = parse_file(f'register/holdout/sz8_11140.txt')
    holdouts_after = parse_file(f'register/holdout/sz8_404.txt')
    holdout_file = f'Sz8RM_{len(holdouts_before) - len(holdouts_after)}'  # mock filename, doesn't really exist
else:
    assert False, 'unsupported SIZE'

os.makedirs(f'other/lean/{holdout_directory}', exist_ok=True)
holdouts_avoid = set(F01[0] for F01 in holdouts_after)
holdouts = [F01 for F01 in holdouts_before if F01[0] not in holdouts_avoid]
assert len(holdouts) == len(holdouts_before) - len(holdouts_after)
summary1 = []
summary2 = []

for Fi, F01 in enumerate(holdouts):
    filename, proof = fm_to_lean_file(holdout_file, Fi+1, F01)
    with open(f'other/lean/{holdout_directory}/{filename}', 'w', encoding='utf-8') as f:
        f.write(proof)
    s1, s2 = fm_to_summary(holdout_directory, holdout_file, Fi+1, F01[1])
    summary1.append(s1)
    summary2.append(s2)

with open(f'other/lean/{holdout_directory}Summary.lean', 'w', encoding='utf-8') as f:
    f.write(''.join(summary1+summary2))
