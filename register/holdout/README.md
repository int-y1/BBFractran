# Holdouts lists

Each holdouts list is stored in a file called `sz(x)_(y).txt`, where `(x)` is the program size and `(y)` is the number of holdouts.

## Errata / File changes

(none so far)

## Size 6

* `sz6_44.txt` (Nov 8, 2026): Direct output from `rm20261108` using `USE_RESULTS=nullopt`.
* No holdouts (Nov 8, 2026): After applying the "Power Difference Limit Mod" decider. Only `GRAPH_PDLM(3)` was used.

MBB(6) = 49.

## Size 7

* `sz7_9831.txt` (Nov 8, 2026): Direct output from `rm20261108` using `USE_RESULTS={{6,49}}`.
* No holdouts (Nov 8, 2026): After applying the "Power Difference Limit Mod" decider. Only `GRAPH_PDLM(3)` was used.

MBB(7) = 231.

## Size 8

* `sz8_2940547.zip` (Nov 10, 2026): Direct output from `rm20261108` using `USE_RESULTS={{7,231}}`.
* `sz8_11140.txt` (Nov 11, 2026): After applying the "Power Difference Limit Mod" decider. Only `GRAPH_PDLM(3)` and `GRAPH_PDLM(4)` were used. PDLM with higher limits didn't work.
