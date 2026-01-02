# Fractran deciders

Some deciders use [Z3](https://github.com/Z3Prover/z3). You may need to `pip install z3-solver` to run these deciders.

List of deciders:

* Power Limit Mod (`graph_search2.py`).
  * The certificate `GRAPH_SEARCH2(x)` represents a cap of `x` and a mod value of `x`.
* Power Difference Limit Mod (`graph_search3.py`).
  * The certificate `GRAPH_SEARCH3(x)` represents a cap of `x` and a mod value of `x`.
* Linear Combination (`lin_comb.py` and `lin_comb2.py`).
  * The certificate `LIN_COMB(c_2, c_3, c_5, c_7, ...)` represents coefficients to use on each prime.
  * `lin_comb2.py` is a faster version that uses Z3 to find the coefficients.
* Integer Spanning Vectors (`isv.py`).
  * The certificate `ISV(x)` represents running for `x` steps, and using this state as the starting state.
* Masked Linear Invariant (`mli.py`).
  * See [sligocki/etc/fractran/mask_lin_invar.py](https://github.com/sligocki/etc/blob/main/fractran/mask_lin_invar.py) for more details.
