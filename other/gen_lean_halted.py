# python -m other.gen_lean_halted
import os
from decider.utils import parse_line, unparse_line


def fm_to_lean_file(holdout_file, holdout_number, F, steps):
    I = len(F[0])
    assert I <= 26, 'alphabet is not big enough'

    # build the fm match definition
    fm_match = []
    for inst in F:
        s0 = ', '.join(chr(ord('a')+i) +
                       (f'+{-inst[i]}' if inst[i] < 0 else '') for i in range(I))
        s1 = ', '.join(chr(ord('a')+i) +
                       (f'+{inst[i]}' if inst[i] > 0 else '') for i in range(I))
        fm_match.append(f'⟨{s0}⟩ => some ⟨{s1}⟩')

    filename = f'{holdout_file.capitalize()}_{holdout_number}.lean'
    proof_template = f'''import BBfLean.FM

/-!
# {holdout_file} #{holdout_number}: {unparse_line(F, 0)}

Vector representation:
```
{unparse_line(F, 1)}
```

This Fractran program halts in {steps} steps.

Author: (replace this with the author of the proof)
-/

namespace {holdout_file.capitalize()}_{holdout_number}

def Q := {' × '.join('ℕ' for _ in range(I))}
def c₀ : Q := ⟨{', '.join('1' if i == 0 else '0' for i in range(I))}⟩
def fm : Q → Option Q := fun q ↦ match q with
  | {(chr(10)+'  | ').join(fm_match)}
  | _ => none

theorem fm_haltsIn : haltsIn fm c₀ {steps} := by
  sorry
'''
    return filename, proof_template


def fm_to_summary(holdout_directory, holdout_file, holdout_number, F, steps):
    I = len(F[0])

    # build the fm match definition
    fm_match = []
    for inst in F:
        s0 = ', '.join(chr(ord('a')+i) +
                       (f'+{-inst[i]}' if inst[i] < 0 else '') for i in range(I))
        s1 = ', '.join(chr(ord('a')+i) +
                       (f'+{inst[i]}' if inst[i] > 0 else '') for i in range(I))
        fm_match.append(f'⟨{s0}⟩ => some ⟨{s1}⟩')

    return f'''import BBfLean.{holdout_directory}.{holdout_file.capitalize()}_{holdout_number}
''', f'''
theorem haltsIn{holdout_number} : haltsIn (Q := {' × '.join('ℕ' for _ in range(I))}) (fun q ↦ match q with
  | {(chr(10)+'  | ').join(fm_match)}
  | _ => none) ⟨{', '.join('1' if i == 0 else '0' for i in range(I))}⟩ {steps} := {holdout_file.capitalize()}_{holdout_number}.fm_haltsIn
'''


holdout_directory = 'Size22Halted'
os.makedirs(f'other/lean/{holdout_directory}', exist_ok=True)
holdout_file = 'sz22_halted_692'
holdouts = []
with open(f'holdout/{holdout_file}.txt') as f:
    for li in f.read().strip().split('\n'):
        li1, li2 = li.rsplit(maxsplit=1)
        holdouts.append([parse_line(li1), int(li2)])

summary1 = []
summary2 = []

for Fi, F12 in enumerate(holdouts):
    F, steps = F12
    if steps < 10**9:
        continue
    filename, proof_template = fm_to_lean_file(holdout_file, Fi+1, F, steps)
    with open(f'other/lean/{holdout_directory}/{filename}', 'w', encoding='utf-8') as f:
        f.write(proof_template)
    s1, s2 = fm_to_summary(holdout_directory, holdout_file, Fi+1, F, steps)
    summary1.append(s1)
    summary2.append(s2)

with open(f'other/lean/{holdout_directory}Summary.lean', 'w', encoding='utf-8') as f:
    f.write(''.join(summary1+summary2))
