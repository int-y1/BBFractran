# python -m other.gen_lean
import os
from decider.utils import parse_file, unparse_line


def fm_to_lean_file(holdout_file, holdout_number, F):
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

TODO: After the proof compiles without any errors, replace this paragraph with one of:
* This Fractran program doesn't halt.
* This Fractran program halts.
* This Fractran program may be a Cryptid. (If possible, add an explanation of whether the program is more likely to halt or not halt. Your explanation should be 2 to 5 sentences.)

Author: (replace this with the author of the proof)
Tokens used: (replace this with the number of tokens you used)
-/

namespace {holdout_file.capitalize()}_{holdout_number}

def Q := {' × '.join('ℕ' for _ in range(I))}
def c₀ : Q := ⟨{', '.join('1' if i == 0 else '0' for i in range(I))}⟩
def fm : Q → Option Q := fun q ↦ match q with
  | {(chr(10)+'  | ').join(fm_match)}
  | _ => none

-- TODO: Prove 1 of these theorems. If the program is a Cryptid, you should instead prove as many rules as possible, and explain whether the program is more likely to halt or not halt.
theorem nonhalt : ¬halts fm c₀ := by
  sorry

theorem halts_thm : halts fm c₀ := by
  sorry
'''
    return filename, proof_template


def fm_to_summary(holdout_directory, holdout_file, holdout_number, F):
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
theorem nonhalt{holdout_number} : ¬halts (Q := {' × '.join('ℕ' for _ in range(I))}) (fun q ↦ match q with
  | {(chr(10)+'  | ').join(fm_match)}
  | _ => none) ⟨{', '.join('1' if i == 0 else '0' for i in range(I))}⟩ := {holdout_file.capitalize()}_{holdout_number}.nonhalt
'''


holdout_directory = input('Enter holdouts directory (e.g. "Size21"): ').strip()
os.makedirs(f'other/lean/{holdout_directory}', exist_ok=True)
holdout_file = input('Enter holdouts list (e.g. "sz21_345"): ').strip()
holdouts = parse_file(f'holdout/{holdout_file}.txt')
holdout_min, holdout_max = map(int, input(
    f'Enter min and max holdout numbers to generate (e.g. enter "1 {len(holdouts)}" to generate all): ').split())

summary1 = []
summary2 = []

for Fi, F in enumerate(holdouts):
    if not (holdout_min <= Fi+1 <= holdout_max):
        continue
    filename, proof_template = fm_to_lean_file(holdout_file, Fi+1, F)
    with open(f'other/lean/{holdout_directory}/{filename}', 'w', encoding='utf-8') as f:
        f.write(proof_template)
    s1, s2 = fm_to_summary(holdout_directory, holdout_file, Fi+1, F)
    summary1.append(s1)
    summary2.append(s2)

with open(f'other/lean/{holdout_directory}Summary.lean', 'w', encoding='utf-8') as f:
    f.write(''.join(summary1+summary2))
