# Holdouts lists

`champions.txt` is a list of champions by increasing order. All of these machines halt. The size 20 and 21 champions have not been proven yet.

Each holdouts list is stored in a file called `sz(x)_(y).txt`, where `(x)` is the program size and `(y)` is the number of holdouts.

## Size 17

* `sz17_162.txt` (Oct 31, 2025): From an early enumeration attempt.

The 162 holdouts were proved non-halting on Nov 4, 2025.

## Size 18

* `sz18_183.txt` (Nov 4, 2025): Direct output from `fractran20251107`.

The 183 holdouts were proved non-halting by the "Power Limit" decider on Nov 8, 2025.

## Size 19

* `sz19_3362.txt` (Nov 7, 2025): Direct output from `fractran20251107`.
* `sz19_231.txt` (Nov 8, 2025): After applying the "Power Limit" decider.
* `sz19_84.txt` (Nov 8, 2025): After applying the "Power Limit Mod" decider.
* `sz19_48.txt` (Nov 8, 2025): After applying the "Linear Combination" decider.
* `sz19_3.txt` (Nov 13, 2025): After applying the "Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438558242388312165)

The 3 holdouts were proved non-halting manually: [holdout 1](https://discord.com/channels/960643023006490684/1438019511155691521/1438564506216304763), [holdout 2](https://discord.com/channels/960643023006490684/1438019511155691521/1438584617085960323), [holdout 3](https://discord.com/channels/960643023006490684/1438019511155691521/1438580955773276160).

## Size 20

* `sz20_1827.txt` (Nov 13, 2025): Direct output from `fractran20251113`.
* `sz20_902.txt` (Nov 13, 2025): After applying the "Power Limit Mod" and "Linear Combination" decider. (Warning: this file used vector representation)
* `sz20_279.txt` (Nov 13, 2025): After applying the "Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438559507579011194)
* `sz20_34.txt` (Nov 14, 2025): After applying the "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438996636389998773)

34 holdouts remain.

## Size 21

* `sz21_9427.txt` (Nov 16, 2025): Direct output from `fractran20251117`. This enumeration attempt also produced `sz19_48.txt` and `sz20_902.txt`.
* `sz21_783.txt` (Nov 16, 2025): After applying the "Spanning Vectors" and "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1439725735211303003)
* `sz21_760.txt` (Nov 16, 2025): After running all machines to 10^11 steps ([link 1](https://discord.com/channels/960643023006490684/1438019511155691521/1439759182587891894), [link 2](https://discord.com/channels/960643023006490684/1438019511155691521/1440851396864905241)). 3 machines took 31957632 steps to halt, and this was the record.
* `sz21_587.txt` (Nov 25, 2025): TODO, create this file. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1442928279995809882)

587 holdouts remain.

## Size 22

Might take 11 days to create. TODO, run `fractran20251117` on a stronger computer.
