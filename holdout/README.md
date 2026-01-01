# Holdouts lists

`champions.txt` is a list of champions by increasing order. All of these machines halt. Champions of size 20 and greater have not been proven yet. The champions of size 22 might be replaced by a better champion.

Each holdouts list is stored in a file called `sz(x)_(y).txt`, where `(x)` is the program size and `(y)` is the number of holdouts.

TODO: `SPAN_VEC_MASKED` made progress on size 19 and above. In particular, it might solve 3/3 of sz19, 23/29 of sz20, 205/602 of sz21, 2634/10441 of sz22. However, as of Dec 15, 2025, the holdouts lists have not been finalized yet.

## Errata

* Dec 11, 2025: `sz21_783.txt` is incorrect. See `sz21_798.txt` for the correct version.
* Dec 11, 2025: `sz21_760.txt` is incorrect. See `sz21_775.txt` for the correct version.
* Dec 11, 2025: `sz21_587.txt` is incorrect. See `sz21_602.txt` for the correct version.
* Dec 27, 2025: Removed vector representation from `sz20_1827.txt` and `sz20_902.txt`.

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
* `sz20_902.txt` (Nov 13, 2025): After applying the "Power Limit Mod" and "Linear Combination" decider.
* `sz20_279.txt` (Nov 13, 2025): After applying the "Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438559507579011194)
* `sz20_34.txt` (Nov 14, 2025): After applying the "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438996636389998773)
* `sz20_29.txt` (Dec 6, 2025): Convert to [Petri net](https://en.wikipedia.org/wiki/Petri_net), apply [FAST](https://lsv.ens-paris-saclay.fr/Software/fast/), and remove those that are infinite (i.e. non-halting). [link](https://discord.com/channels/960643023006490684/1438019511155691521/1447069110541484146)

29 holdouts remain.

## Size 21

* `sz21_9427.txt` (Nov 16, 2025): Direct output from `fractran20251116`. This enumeration attempt also produced `sz19_48.txt` and `sz20_902.txt`.
* `sz21_798.txt` (Dec 11, 2025): After applying the "Spanning Vectors" and "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448740671077748847)
* `sz21_775.txt` (Dec 11, 2025): After running all machines to 10^9 steps ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1448784141788250183) and consider only sz21 machines). 3 machines took 31957632 steps to halt, and this was the record. (TODO: Run all machines in `sz21_798.txt` to 10^11 steps)
* `sz21_602.txt` (Dec 11, 2025): Convert to [Petri net](https://en.wikipedia.org/wiki/Petri_net), apply [FAST](https://lsv.ens-paris-saclay.fr/Software/fast/), and remove those that are infinite (i.e. non-halting). ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1442928279995809882), but 15 machines were added)
* `sz21_597.txt` (Dec 22, 2025): After applying the "Power Difference Limit Mod" decider with higher parameters. (The strategy is the same as `sz22_9829.txt`.)
* `sz21_553.txt` (Dec 31, 2025): After applying the "Integer Spanning Vectors" decider.

553 holdouts remain.

## Size 22

* `sz22_91123.txt` (Dec 9, 2025): Direct output from `fractran20251116`.
* `sz22_11130.txt` (Dec 11, 2025): After applying the "Spanning Vectors" and "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448729669263163596)
* `sz22_10458.txt` (Dec 11, 2025): After running all machines to 10^9 steps ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1448806255261913199)).
* `sz22_10441.txt` (Dec 11, 2025): After removing 17 halting machines ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1450232568988307467)).
  * See `sz22_halted_689.txt` for a list of machines that took more than 10000 steps to halt (672 machines from [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448784141788250183), 17 machines from [link](https://discord.com/channels/960643023006490684/1438019511155691521/1450232568988307467)). The format of each line is `<machine> <steps to halt>`.
* `sz22_9829.txt` (Dec 21, 2025): After applying the "Power Difference Limit Mod" decider with higher parameters. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1452353731449327820)
* `sz22_8352.txt` (Dec 31, 2025): After applying the "Integer Spanning Vectors" decider.

8352 holdouts remain.

## Size 23

Not needed yet. Size 22 still needs to be explored further.

Benchmark info for `fractran20251116` on my laptop: sz19 in 895s, sz20 in 4880s, sz21 in 30343s, sz22 in 172468s. sz23 might take 12 days.
