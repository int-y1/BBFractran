# BBFractran

Busy beaver for Fractran

<https://en.wikipedia.org/wiki/FRACTRAN>

<https://wiki.bbchallenge.org/wiki/Fractran>

## To-do list

Work more on register machines (see `register/`).

---

Write a new decider. The decider should satisfy these requirements:

* When given a Fractran program in `sz22_2003.txt`, the decider must return either "halt", "non-halt", or "undecided".
* When given a Fractran program in `sz22_halted_692.txt` or `sz23_halted_6867.txt`, the decider must return either "halt" or "undecided". In particular, the decider must not return "non-halt".
* The decider must return "non-halt" on at least 5% of holdouts in `sz22_2003.txt`, or return "halt" on at least 1 holdout.
* The decider must take at most 1 hour per holdout when run on reasonable hardware.

There are deciders in `decider/*.py`. However, these deciders won't decide any holdouts in `sz22_2003.txt`. You will have to either upgrade an existing decider or write a new decider from scratch.

(Note: Claude Opus 4.8 wrote a new decider `oned_progress.py`. Let's try again on an unofficial holdouts list.)
