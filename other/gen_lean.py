# python -m other.gen_lean
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

TODO: After finishing the proof, replace this paragraph with one of:
* This Fractran program doesn't halt.
* This Fractran program halts.
-/

def Q := {' × '.join('ℕ' for _ in range(I))}
def c₀ : Q := ⟨{', '.join('1' if i == 0 else '0' for i in range(I))}⟩
def fm : Q → Option Q := fun q ↦ match q with
  | {(chr(10)+'  | ').join(fm_match)}
  | _ => none

theorem nonhalt : ¬halts fm c₀ := by
  sorry
'''
    return filename, proof_template


holdout_file = input('Enter holdouts list (e.g. "sz21_345"): ').strip()
holdout_number = int(
    input('Enter holdout number (e.g. from 1 to 345) to generate, or 0 to generate all holdouts: '))

holdouts = parse_file(f'holdout/{holdout_file}.txt')

for Fi, F in enumerate(holdouts):
    if holdout_number > 0 and Fi != holdout_number-1:
        continue
    filename, proof_template = fm_to_lean_file(holdout_file, Fi+1, F)
    with open(f'other/lean/{filename}', 'w', encoding='utf-8') as f:
        f.write(proof_template)
