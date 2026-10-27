# Holdouts lists

`champions.txt` is a list of champions by increasing order. All of these machines halt. The 2 champions of size 22 are probviously champions, but have not been proven yet. The 4 champions of size 23 are probviously champions, but have not been proven yet. The 2 champions of size 24 could be replaced by a better champion.

Each holdouts list is stored in a file called `sz(x)_(y).txt`, where `(x)` is the program size and `(y)` is the number of holdouts.

TODO:

* A new decider "Beeping Integer Spanning Vectors" (BISV) made progress on size 20 and above. In particular, it might solve 6/6 of sz20 (no Lean proofs needed), 142/345 of sz21, and 2321/5682 of sz22. However, as of Jan 23, 2026, this decider hasn't been reviewed / reproduced by the bbchallenge community. Please open an issue if you find a bug.
* A new decider "Beeping Permutation" (BP) is a stronger version of BISV. In particular, it might solve 6/6 of sz20 (no Lean proofs needed), 205/345 of sz21, and 3679/5682 of sz22. However, as of Jan 23, 2026, this decider hasn't been reviewed / reproduced by the bbchallenge community. Please open an issue if you find a bug.

## Errata / File changes

* Dec 11, 2025: `sz21_783.txt` is incorrect. See `sz21_798.txt` for the correct version.
* Dec 11, 2025: `sz21_760.txt` is incorrect. See `sz21_775.txt` for the correct version.
* Dec 11, 2025: `sz21_587.txt` is incorrect. See `sz21_602.txt` for the correct version.
* Dec 27, 2025: Removed vector representation from `sz20_1827.txt` and `sz20_902.txt`.
* Jul 23, 2026: `sz21_140_unofficial.txt` was renamed to `sz21_140.txt`.
* Jul 23, 2026: `sz22_2003_unofficial.txt` was renamed to `sz22_2003.txt`.
* Oct 13, 2026: `sz23_8021_unofficial.txt` was renamed to `sz23_8021.txt`.
* Oct 13, 2026: `sz24_85726_unofficial.txt` was renamed to `sz24_85726.txt`.
* Oct 16, 2026: A soundness bug in the "N-Dimensional Progress Certificates" decider was found and fixed.
  * `sz23_703_unofficial.txt` was renamed to `sz23_703.txt`.
  * `sz23_694_unofficial.txt` was renamed to `sz23_694.txt`.
  * `sz23_13_unofficial.txt` was renamed to `sz23_13.txt`.
  * `sz24_10838_unofficial.txt` was removed. This holdouts list was technically correct, but not reproducible. (More precisely, all solved machines can get a Lean proof, but heavy changes to `nd_progress*.py` were needed to generate the proofs.)

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

On Nov 13, 2025, the 3 holdouts were proved non-halting manually: [holdout 1](https://discord.com/channels/960643023006490684/1438019511155691521/1438564506216304763), [holdout 2](https://discord.com/channels/960643023006490684/1438019511155691521/1438584617085960323), [holdout 3](https://discord.com/channels/960643023006490684/1438019511155691521/1438580955773276160).

On Jan 1, 2026, the 3 holdouts can be solved automatically by the "Masked Linear Invariant" decider.

## Size 20

* `sz20_1827.txt` (Nov 13, 2025): Direct output from `fractran20251113`.
* `sz20_902.txt` (Nov 13, 2025): After applying the "Power Limit Mod" and "Linear Combination" decider.
* `sz20_279.txt` (Nov 13, 2025): After applying the "Spanning Vectors" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438559507579011194)
* `sz20_34.txt` (Nov 14, 2025): After applying the "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1438996636389998773)
* `sz20_29.txt` (Dec 6, 2025): Convert to [Petri net](https://en.wikipedia.org/wiki/Petri_net), apply [FAST](https://lsv.ens-paris-saclay.fr/Software/fast/), and remove those that are infinite (i.e. non-halting). [link](https://discord.com/channels/960643023006490684/1438019511155691521/1447069110541484146)
* `sz20_6.txt` (Jan 1, 2026): After applying the "Masked Linear Invariant" decider.

The 6 holdouts were proved non-halting with a formal Lean proof. [link](https://github.com/int-y1/proofs/tree/master/BBfLean)

## Size 21

* `sz21_9427.txt` (Nov 16, 2025): Direct output from `fractran20251116`. This enumeration attempt also produced `sz19_48.txt` and `sz20_902.txt`.
* `sz21_798.txt` (Dec 11, 2025): After applying the "Spanning Vectors" and "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448740671077748847)
* `sz21_775.txt` (Dec 11, 2025): After running all machines to 10^9 steps ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1448784141788250183) and consider only sz21 machines). 3 machines took 31957632 steps to halt, and this was the record.
  * See `sz21_halted_23.txt` for a list of machines that halted. The format of each line is `<machine> <steps to halt>`.
* `sz21_602.txt` (Dec 11, 2025): Convert to [Petri net](https://en.wikipedia.org/wiki/Petri_net), apply [FAST](https://lsv.ens-paris-saclay.fr/Software/fast/), and remove those that are infinite (i.e. non-halting). ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1442928279995809882), but 15 machines were added)
* `sz21_597.txt` (Dec 22, 2025): After applying the "Power Difference Limit Mod" decider with higher parameters. (The strategy is the same as `sz22_9829.txt`.)
* `sz21_553.txt` (Dec 31, 2025): After applying the "Integer Spanning Vectors" decider.
* `sz21_345.txt` (Jan 1, 2026): After applying the "Masked Linear Invariant" decider.
* `sz21_140.txt` (Jan 24, 2026): After applying the "Beeping Permutation" decider. (See warning above about BP.)

On Mar 25, 2026, the 140 holdouts were proved non-halting by prompting Claude Opus 4.6 for Lean proofs. See <https://github.com/int-y1/proofs/blob/master/BBfLean/Size21Summary.lean>.

## Size 22

* `sz22_91123.txt` (Dec 9, 2025): Direct output from `fractran20251116`.
* `sz22_11130.txt` (Dec 11, 2025): After applying the "Spanning Vectors" and "Power Difference Limit Mod" decider. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448729669263163596)
* `sz22_10458.txt` (Dec 11, 2025): After running all machines to 10^9 steps ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1448806255261913199)).
* `sz22_10441.txt` (Dec 11, 2025): After removing 17 halting machines ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1450232568988307467)).
  * See `sz22_halted_689.txt` for a list of machines that took more than 10000 steps to halt (672 machines from [link](https://discord.com/channels/960643023006490684/1438019511155691521/1448784141788250183), 17 machines from [link](https://discord.com/channels/960643023006490684/1438019511155691521/1450232568988307467)). The format of each line is `<machine> <steps to halt>`.
* `sz22_9829.txt` (Dec 21, 2025): After applying the "Power Difference Limit Mod" decider with higher parameters. [link](https://discord.com/channels/960643023006490684/1438019511155691521/1452353731449327820)
* `sz22_8352.txt` (Dec 31, 2025): After applying the "Integer Spanning Vectors" decider.
* `sz22_5682.txt` (Jan 1, 2026): After applying the "Masked Linear Invariant" decider.
* `sz22_2003.txt` (Jan 24, 2026): After applying the "Beeping Permutation" decider. (See warning above about BP.)
* `sz22_3.txt` (Apr 3, 2026): After prompting Claude Opus 4.6 for Lean proofs. See <https://github.com/int-y1/proofs/blob/master/BBfLean/Size22Summary.lean>.
  * See `sz22_halted_692.txt` (Apr 5, 2026) for a list of machines that took more than 10000 steps to halt (689 machines from `sz22_halted_689.txt`, 3 new machines found by Claude Opus 4.6). The format of each line is `<machine> <steps to halt>`.

3 holdouts remain. These 3 holdouts are the [Fenrir family](https://wiki.bbchallenge.org/wiki/Fractran#Fenrir).

## Size 23

* `sz23_790335.txt` (May 29, 2026): Direct output from `fractran20251116` (13.4 hours on 95 threads) and `fractran20260416` (13.2 hours on 88 threads). Both enumerators agreed.
* `sz23_94367.txt` (May 31, 2026): After applying the "Integer Spanning Vectors" decider up to `ISV(1000)`, and the "Power Difference Limit Mod" decider up to `GRAPH_PDLM(12)`.
* `sz23_29250.txt` (May 31, 2026): After applying the "Beeping Permutation" decider up to k = 1000. (See warning above about BP.)
* `sz23_29188.txt` (Jun 1, 2026): After applying the "Power Difference Limit Mod" decider up to `GRAPH_PDLM(24)`. (There were 6 machines decided by `GRAPH_PDLM(24)`.)
* `sz23_28100.txt` (Jun 1, 2026): After applying `bp_prefix`, an improved version of "Beeping Permutation". (See warning above about BP.)
* `sz23_21320.txt` (Jun 1, 2026): After simulating machines until halt. ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1510804448090521650)) (Thanks @Shawn Ligocki for simulating the machines)
  * See `sz23_halted_6780.txt` for a list of machines that halted.
* `sz23_21295.txt` (Jun 2, 2026): After simulating machines until halt. ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1511579969825013811)) (Thanks @Shawn Ligocki for simulating the machines)
  * See `sz23_halted_6805.txt` for a list of machines that halted.
* `sz23_21233.txt` (Jul 10, 2026): After simulating machines until halt. ([link](https://discord.com/channels/960643023006490684/1438019511155691521/1525198083363967136)) (First found by Opus 4.8. Thanks @Shawn Ligocki for strengthening the simulator and verifying the results.)
  * See `sz23_halted_6867.txt` for a list of machines that halted.
* `sz23_8021.txt` (Jul 23, 2026): After applying the "1D Progress Certificates" decider.
  * Oct 13, 2026: All 13212 1DPC certificates were verified in Lean 4.33.0-rc1 in ~32 core-hours. This holdouts list became official. (Oct 27, 2026: All certificates were reverified in Lean 4.36.0-rc1.)
* `sz23_703.txt` (Jul 25, 2026): After applying the "N-Dimensional Progress Certificates" decider with a time budget of 300s.
* `sz23_694.txt` (Jul 25, 2026): After applying the "N-Dimensional Progress Certificates" decider with a time budget of 3600s.
  * Oct 16, 2026: All 7327 NDPC certificates were verified in Lean 4.33.0-rc1 in ~30 core-hours. This holdouts list became official. (Oct 27, 2026: All certificates were reverified in Lean 4.36.0-rc1.)
* `sz23_159.txt` (Oct 27, 2026): After applying the "N-Dimensional Residue Progress Certificates" decider with a time budget of 3600s. 15 machines exceeded the time budget. All 535 NDRPC certificates were verified in Lean 4.36.0-rc1.
* `sz23_13.txt` (Aug 4, 2026): After prompting Claude Opus 4.8 / 5 for Lean proofs of `sz23_694.txt`. See <https://github.com/int-y1/proofs/blob/master/BBfLean/Size23Summary.lean>. If all 13 holdouts are proved non-halting, BBf(23) would be solved.

TODO: Find a machine in `sz23_790335.txt`, not in `sz23_halted_6867.txt`, and halts. I don't expect this to be possible. If this machine exists, this is either a breakthrough or a bug in my pipeline. (TODO: Try simulating each machine to 10^9 steps.)

## Size 24

* `sz24_6733785.zip` (Aug 30, 2026): Direct output from `fractran20260818` (~7790 core-hours). Uncompressed size is 253507201 bytes. For reference, `fractran20260818` produced `sz23_790335.txt` in ~1170 core-hours.
* `sz24_945600.zip` (Sep 4, 2026): After applying the "Integer Spanning Vectors" decider up to `ISV(1000)`, and the "Power Difference Limit Mod" decider up to `GRAPH_PDLM(12)`.
* `sz24_298146.txt` (Sep 6, 2026): After applying `bp_prefix`, an improved version of "Beeping Permutation". (See warning above about BP.)
* `sz24_231444.txt` (Sep 6, 2026): After applying @Shawn Ligocki's simulator `shift-sim-all` with 100000 steps. 66689 halted and 13 were infinite.
  * See `sz24_halted_66689.txt` for a list of machines that halted.
* `sz24_231432.txt` (Sep 12, 2026): After applying @Shawn Ligocki's simulator further.
  * See `sz24_halted_66689_to_66701.txt` for the 12 machines that halted.
* `sz24_85726.txt` (Sep 12, 2026): After applying the "1D Progress Certificates" decider.
  * Oct 13, 2026: All 145706 certificates were verified in Lean 4.33.0-rc1 in ~314 core-hours. This holdouts list became official. (Oct 27, 2026: All certificates were reverified in Lean 4.36.0-rc1.)
* `sz24_10678.txt` (Oct 16, 2026): After applying the "N-Dimensional Progress Certificates" decider with a time budget of 300s.
* `sz24_10572.txt` (Oct 16, 2026): After applying the "N-Dimensional Progress Certificates" decider with a time budget of 3600s. 15 machines exceeded the time budget.
  * Oct 16, 2026: All 75154 NDPC certificates were verified in Lean 4.33.0-rc1 in ~270 core-hours. This holdouts list became official. (Oct 27, 2026: All certificates were reverified in Lean 4.36.0-rc1.)
* `sz24_3580.txt` (Oct 27, 2026): After applying the "N-Dimensional Residue Progress Certificates" decider with a time budget of 3600s. 213 machines exceeded the time budget. All 6992 NDRPC certificates were verified in Lean 4.36.0-rc1.

The latest holdouts list is `sz24_3580.txt`. Helpful files for further investigation:

* `sz24_2245_eqv_3580_unofficial.txt` (Oct 27, 2026): Programs in `sz24_3580.txt` grouped into 2245 equivalence classes. Each line is `<machine> <equivalence class>`. Machines in an equivalence class are either all halting or all non-halting. It is ok to treat this file as correct. This file is `unofficial` because there is no automatic way to reproduce this file.
* `sz24_2002_hydra_unofficial.txt` (Oct 27, 2026): Hydra-like programs found in `sz24_3580.txt`. Warning: Do not treat this file as accurate. There could be false positives and false negatives.

TODO: Simulate `[2/15, 1/6, 441/2, 11/3, 25/7, 6/11]` ([BMO](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) #12) to halt. This machine should beat the current BBf(24) champion.
