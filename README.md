# BBFractran

Busy beaver for Fractran

<https://en.wikipedia.org/wiki/FRACTRAN>

<https://wiki.bbchallenge.org/wiki/Fractran>

## To-do list

Enumerate sz23.

---

Look at Minsky machines.

---

Write a new decider. The decider should satisfy these requirements:

* When given a Fractran program in `sz22_2003_unofficial.txt`, the decider must return either "halt", "non-halt", or "undecided".
* When given a Fractran program in `sz22_halted_689.txt`, the decider must return either "halt" or "undecided". In particular, the decider must not return "non-halt".
* The decider must return "non-halt" on at least 5% of holdouts in `sz22_2003_unofficial.txt`, or return "halt" on at least 1 holdout.
* The decider must take at most 1 hour per holdout when run on reasonable hardware.

There are deciders in `decider/*.py`. However, these deciders won't decide any holdouts in `sz22_2003_unofficial.txt`. You will have to either upgrade an existing decider or write a new decider from scratch.

(Note: Claude Opus 4.6 was unable to write a new decider after a few tries. Let's try again in a few years...)
