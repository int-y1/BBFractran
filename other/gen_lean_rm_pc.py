# python -m other.gen_lean_rm_pc
import os
from decider.nd_progress import nd_progress_cert
from decider.nd_progress_to_lean import nd_progress_to_lean
from decider.oned_progress import oned_progress_cert
from decider.oned_progress_to_lean import oned_progress_to_lean
from other.gen_lean import fm_to_summary
from register.decider.utils import parse_file

# all settings
if 0:
    holdouts_before = parse_file(f'register/holdout/sz8_11140.txt')
    holdouts_after = parse_file(f'register/holdout/sz8_404.txt')
    progress_cert = oned_progress_cert
    progress_to_lean = oned_progress_to_lean
if 1:
    holdouts_before = parse_file(f'register/holdout/sz8_404.txt')
    holdouts_after = parse_file(f'register/holdout/sz8_6.txt')
    progress_cert = lambda F: nd_progress_cert(F, time_budget=0)
    progress_to_lean = nd_progress_to_lean

holdout_directory = 'Size8RM_pc'
holdout_file = f'Sz8RM_{len(holdouts_before) - len(holdouts_after)}'  # mock filename, doesn't really exist


def fm_to_lean_file(holdout_file, holdout_number, F01):
    filename = f'{holdout_file.capitalize()}_{holdout_number}.lean'
    cert = progress_cert(F01[1])
    assert cert is not None, f'no cert for {F01[0]}'
    proof = progress_to_lean(F01[1], cert, f'{holdout_file.capitalize()}_{holdout_number}')
    return filename, proof


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
