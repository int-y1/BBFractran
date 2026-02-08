# BBFractran

Busy beaver for Fractran

<https://en.wikipedia.org/wiki/FRACTRAN>

<https://wiki.bbchallenge.org/wiki/Fractran>

## To-do list

Write a decider that can prove these 7 FMs to be non-halting:
```
[20/3, 9/35, 1/20, 49/2, 3/7]
[63/10, 121/2, 2/33, 5/7, 10/11]
[63/10, 121/2, 2/33, 5/7, 14/11]
[9/10, 343/2, 22/21, 5/11, 3/7]
[9/35, 20/3, 1/20, 49/2, 3/7]
[99/35, 4/5, 5/6, 7/11, 55/2]
[99/35, 5/6, 4/5, 7/11, 55/2]
```

This decider would make "Petri net + FAST" redundant.

I have no idea what this decider would look like.

---

Write a script that reads a holdouts list and creates Lean files with `sorry` proofs. For example, if the input is `sz20_6.txt`, the 6 output files will look something like <https://github.com/int-y1/proofs/tree/master/BBfLean/Size20>.

I will work on this soon.

---

Enumerate sz23.

---

Using Lean, prove that the sz22 champion `[1/12, 9/10, 14/3, 11/2, 5/7, 3/11]` halts in 114613926700260640237968442298168949531348819453104518623702295 steps.

I'm not planning to work on this.
