# BBFractran

Busy beaver for Fractran

<https://en.wikipedia.org/wiki/FRACTRAN>

<https://wiki.bbchallenge.org/wiki/Fractran>

## To-do list

Write a new decider. The decider should satisfy these requirements:

* When given a Fractran program in `sz22_2003_unofficial.txt`, the decider must return either "halt", "non-halt", or "undecided".
* When given a Fractran program in `sz22_halted_689.txt`, the decider must return either "halt" or "undecided". In particular, the decider must not return "non-halt".
* The decider must decide at least 5% of holdouts in `sz22_2003_unofficial.txt` (i.e. return "halt" or "non-halt").
* The decider must take at most 1 hour per holdout when run on reasonable hardware.

There are deciders in `decider/*.py`. However, these deciders won't decide any holdouts in `sz22_2003_unofficial.txt`. You will have to either strengthen an existing decider or write a new decider from scratch.

(TODO: see if AI can write a decider)

---

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

Enumerate sz23.

---

Using Lean, prove that the sz22 champion `[1/12, 9/10, 14/3, 11/2, 5/7, 3/11]` halts in 114613926700260640237968442298168949531348819453104518623702295 steps.

I'm not planning to work on this.
