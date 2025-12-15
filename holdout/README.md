# Holdouts lists

`champions.txt` is a list of champions by increasing order. All of these machines halt. Champions of size 20 and greater have not been proven yet. The champions of size 22 might be replaced by a better champion.

Each holdouts list is stored in a file called `sz(x)_(y).txt`, where `(x)` is the program size and `(y)` is the number of holdouts.

## Errata

* Dec 11, 2025: `sz21_783.txt` is incorrect. See `sz21_798.txt` for the correct version.
* Dec 11, 2025: `sz21_760.txt` is incorrect. See `sz21_775.txt` for the correct version.
* Dec 11, 2025: `sz21_587.txt` is incorrect. See `sz21_602.txt` for the correct version.

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

The 3 holdouts were proved non-halting using "Masked Spanning Vectors" decider.

## Size 20

* `sz20_1827.txt` (Nov 13, 2025): Direct output from `fractran20251113`.
* `sz20_902.txt` (Nov 13, 2025): After applying the "Power Limit Mod" and "Linear Combination" decider. (Warning: this file used vector representation)
* `sz20_279.txt` (Nov 13, 2025): After applying the "Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438559507579011194)
* `sz20_34.txt` (Nov 14, 2025): After applying the "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438996636389998773)
* `sz20_29.txt` (Dec 6, 2025): Convert to [Petri net](https://en.wikipedia.org/wiki/Petri_net), apply [FAST](https://lsv.ens-paris-saclay.fr/Software/fast/), and remove those that are infinite (i.e. non-halting). [link](https://discord.com/channels/960643023006490684/1438019511155691521/1447069110541484146)
* `sz20_6.txt` (Dec 15, 2025): After applying the "Masked Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1450186709420609537)

6 holdouts remain.

## Size 21

* `sz21_9427.txt` (Nov 16, 2025): Direct output from `fractran20251116`. This enumeration attempt also produced `sz19_48.txt` and `sz20_902.txt`.
* `sz21_798.txt` (Dec 11, 2025): After applying the "Spanning Vectors" and "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448740671077748847)
* `sz21_775.txt` (Dec 11, 2025): After running all machines to 10^9 steps ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1448784141788250183) and consider only sz21 machines). 3 machines took 31957632 steps to halt, and this was the record. (TODO: Run all machines in `sz21_798.txt` to 10^11 steps)
* `sz21_602.txt` (Dec 11, 2025): Convert to [Petri net](https://en.wikipedia.org/wiki/Petri_net), apply [FAST](https://lsv.ens-paris-saclay.fr/Software/fast/), and remove those that are infinite (i.e. non-halting). ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1442928279995809882), but 15 machines were added)
* `sz21_394.txt` (Dec 15, 2025): After applying the "Masked Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1450186709420609537)

394 holdouts remain.

## Size 22

* `sz22_91123.txt` (Dec 9, 2025): Direct output from `fractran20251116`.
* `sz22_11130.txt` (Dec 11, 2025): After applying the "Spanning Vectors" and "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448729669263163596)
* `sz22_10458.txt` (Dec 11, 2025): After running all machines to 10^9 steps ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1448806255261913199)). 3 machines took 31957632 steps to halt, and this was the record.
* `sz22_10441.txt` (Dec 12, 2025): After running all machines using accelerated `shift-sim` ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1449113470221156575), [link](https://discord.com/channels/960643023006490684/1438019511155691521/1449145769637712125)). 2 machines tie with longest runtime > 10^62.
* `sz22_7777.txt` (Dec 15, 2025): After applying the "Masked Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1450186709420609537)

7777 holdouts remain.

## Size 23

Not needed yet. Size 22 still needs to be explored further.

Benchmark info for `fractran20251116` on my laptop: sz19 in 895s, sz20 in 4880s, sz21 in 30343s, sz22 in 172468s. sz23 might take 12 days.
