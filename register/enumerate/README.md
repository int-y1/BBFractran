# Register machine enumerators

## Build instructions

Currently, only Windows is supported. Sorry, Linux users.

These commands will build and run the program.

```
./ac rm
./ac rm20261108
./ac rm20261113
```

The program will produce output here:

* stderr will show information to help with debugging the enumerator.
* The file `tmp.txt` contains the output of the enumeration. This file is intended to be studied further or shared.
* The files `tmp_sz*_step.txt` (or `tmp_sz*_reg.txt`) contain the top champions for each size.

## Explanation of `rm`

TODO: fill this in later.

## Explanation of `rm20261108`

* Get the top 100 champions.

## Explanation of `rm20261113`

* Add a PDLM decider.
* Improve champion tiebreaking.
