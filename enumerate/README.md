# Fractran enumerators

## Build instructions

Currently, only Windows is supported. Sorry, Linux users.

These commands will build and run the program. `ac_old` requires GMP to be installed. `ac` does not require GMP.

```
./ac_old fractran20251107
./ac fractran20251113
./ac fractran20251116
```

The program will write to 2 locations:

* stderr will show information to help with debugging the enumerator.
* The file `fractran.txt` contains the output of the enumeration. This file is intended to be studied further or shared.

## Explanation of `fractran20251113`

To enumerate all fractran programs of size `sz`, make sure to reset `busy` (final step count) and `champions` (list of champion machines), then call `enumerate(sz,1,v)`.

`enumerate` is a recursive function that works like this:

1. Generate a fraction.
2. After a fraction is generated, call `solve` to see if the fractran program should get a new fraction.
3. If `solve` returns false, add a new fraction and start again with 1.

`solve` has 3 main objectives:

* Return true/false (true = don't add a new fraction, false = add a new fraction).
* If the fractran program is a champion, update `busy` and `champions`.
* Create a list of holdouts (fractran programs with unknown halting status).

`solve` has a big pipeline of deciders. I used `cnt` to keep track of how many fractran programs entered each step. Here are the `cnt` stats for size 20:

* 1022509799484 programs entered "check for x/1".
* 921412893707 programs entered "check if program can be made complete".
  * Calculate the size increase so that the program satisfies these conditions: (1) the program must have x/2. (2) every prime in a numerator must be in a denominator. (3) every prime in a denominator must be in a numerator (except 2, because 2 is the starting prime).
  * Technically, this decider will remove champions if BBf(sz) = BBf(sz-1). In practice, only sz=3 and sz=4 are affected.
  * This decider is the biggest time saver in the pipeline, and only 0.74% made it to the next decider.
* 6858432983 programs entered "check if columns 2,3,... are in nonincreasing order".
  * Define a function that maps (0, 1, -1, 2, -2, 3, -3, ...) to (0, 1, 2, 3, 4, 5, 6, 7, ...). So if a column is [-1, -1, 1, 0, 2], it would be mapped to [2, 2, 1, 0, 3]. Then check if the columns are nonincreasing, by lexicographic order.
  * This decider removes a lot of equivalent holdouts.
* 6607255035 programs entered "check for covered denominator".
  * If the last fraction is x/(k*y), make sure x'/y doesn't appear earlier.
* 4423692512 programs entered "translated cycler + direct simulation". The step limit is 10^4.
* 139922 programs entered "power limit mod".
* 1827 programs entered the holdout list. This is available as `sz20_1827.txt`.

The pipeline order only matters if you're optimizing for speed. For example, you can move "power limit mod" to the 1st step and it should generate the same champions and holdouts list, albeit more slowly.

## Explanation of `fractran20251116`

It's like `fractran20251113` with these additions:

* Multithreading is added. See `THREADS`.
* A new decider `lin_comb` is added to the `solve` pipeline.
* `enumerate` is made more efficient. See the new parameter `newcol`. Essentially, I moved a part of "check if program can be made complete" into `enumerate`.
