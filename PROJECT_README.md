# Verification of Halide's Bounds Inference Engine

This project (my semester UROP) is a formal verification of [Halide](https://halide-lang.org "Halide Homepage")'s bounds inference engine, in order to discover bugs and to query the tightness of the current implementation.


## Background

Halide is a domain-specific language for image processing that was developed at MIT, as joint by Andrew Adams and Jonathan Ragan-Kelley. It relies on a bounds inference engine to infer the minimum and maximum possible indexes into arrays, in order to place bounds on the amount of memory needed to allocate for any intermediate buffers, as well as for the bounds of the output buffer (among other uses). 


## Interval Analysis

The existing system makes use of interval analysis, but in a symbolic representation that allows for affine arithmetic to still be utilized. For example, in many interval arithmetic systems:
```
bounds(a) = [0, 10]
bounds(a - a) = [-10, 10]
```
This bound is not necessarily incorrect, but it is not tight. Halide's symbolic algebra system allows for simplifcation of the above computation to produce the tighter bounds of `[0, 0]`.

An important note: some expressions (i.e. runtime inputs) can be unbounded, which are denote as having a lower bound of `-\inf` or an upper bound of `\inf`.

### Correctness 

The intent of the bounds inference engine is to produce the tightest bounds possible, while still being correct. Condition for "correct" is, quite simply:
Given an operation `Op` and a set of arguments `args`, the bounds of `Op(args)` is correct if and only if, for all `a \in bounds(args)` (where `bounds(args)` is the set of all combinations of possible values within the bounds of each element of `args`), `Op(args).min <= Op(a) <= Op(args).max`. 


## Formal Verification

The bounds inference engine mostly deals with Halide's integer (and boolean) types, so this project focused only on those inference rules. The majority of rules are proven correct (or bugs were found and corrected) using [z3](https://github.com/Z3Prover/z3), but some division rules needed to be proved in [Coq](https://github.com/coq/coq).

### z3

The operations that we analyzed using z3 include: `add`, `and`, `not`, `or`, `div` (some cases), `equals`, `geq`, `gt`, `leq`, `lt`, `max`, `min`, `mod`, `mul`, `neq`, `select` (if-then-else), `shift_left`, `shift_right`, and `sub`. This code is available in the [checks](./checks) directory. Bugs were discovered via z3 in `mod`, `div`, and `shift_left`, and can be found in the [bugs](./bugs) directory. These are discussed further below. There is additionally a `shift_right` bug that has not been added to Halide because it relies on semantics that are currently in flux, regarding the expected output of overflowing shift operations.

There is a small amount of boiler-plate code in [src](./src) and [include](./include), in order to set up a slightly nicer interface for dealing with repeated bounds queries.

Note: Halide semantics and z3 semantics are *not* the same, so had to be encoded. The shift code got a little complicated, because overflow is undefined in signed integers (with `> 16` bits), but is defined behavior for unsigned integers and signed integers with smaller bitwidths. Division and modulus by `0` also has weird semantics in Halide, as both are designed to equal `0`.

### Coq

As stated above, only some division rules needed to be formally verified in Coq. These are commented out in [checks/div.cpp](checks/div.cpp) because they never ran to completion. They are formally verified in [coq/Interval.v](coq/Interval.v), which can be compiled by:
```
cd coq
make
```
This formal verification process also allowed us to discover a precondition on two of the rules that could be loosened, as Halide division by `0` semantics had changes since the original code authors wrote that portion of code. 

Note: VSCoq (or perhaps my Coq installation) had some import difficulties, so one of the theorems that exists in the standard Coq library was copy-pasted into that file without a proof. Some other theorems were copy-pasted with full proofs because Coq imports is either broken, or I don't know it well enough to fix this issue. If any staff member is reading this, and knows the fix, I'd greatly appreciate being told! Thanks.


## Bugs (and new rules)

The following bugs have been patched in Halide's main directory. Note that the `_` symbol is used where that value can either be an infinity or a concrete value, but is not required by the inference rule.

- Division of a bounded interval by a symbolic interval: [Halide PR #5331](https://github.com/halide/Halide/pull/5331) verified in [bugs/div-check.cpp](bugs/div-check.cpp). The original code (likely a copy-paste typo) was:
    ```
    interval.max = max(-a.max, a.min);
    ```
    while the bug fix is:
    ```
    interval.max = max(-a.min, a.max);
    ```
    This is due to the fact that division can, at worst, decrease magnitude or change the sign of a value.

- Modulus `a % [_, 0]`, where the right hand operand is unsigned could produce the interval `[0, UINT_MAX]`, which is not a tight bound. The correct bound is `[0, 0]`, and this has been reflected in [Halide PR #5350](https://github.com/halide/Halide/pull/5350).

- Division by a signed integer with bounds of `[_, 0]` or `[0, _]` was not properly simplied based on the semantic that divide by `0` is equal to `0`, and could produce an unbounded interval. This bug fix is in [Halide PR #5407](https://github.com/halide/Halide/pull/5407/files). This bug was not discovered using z3, but on inspection of preconditions while using Coq.

- Additional rules that were found while verifying `lt`, `gt`, `leq`, `geq`, `equals` and `neq`. All new rules were verified with z3. These were not bugs necessarily, but produced tighter boolean for certain cases where one operand is unbounded. These additional rules are found in [Halide PR #5438](https://github.com/halide/Halide/pull/5438). Most importantly, this rule produced a tighter bound on a test case than the expected value.

- A shift left rule had insufficient preconditions for the resultant bounds. In Halide, `a << b` is defined as `a * 2^b`, regardless of the sign of `a` or `b`. z3 produced regression tests and verified the replacement `shift_left` rules that are in [Halide PR #5477](https://github.com/halide/Halide/pull/5477). 


## Conclusion and Next Steps

Formal verification has proven incredibly useful for Halide's Term Rewriting Systems, both in the bounds inference engine and in the general simplification system (see my group's OOPSLA paper [here](http://design.cs.iastate.edu/splash20/oopsla20/oopsla20main-p148-p.pdf)!). As in that work, we intend to synthesize additional bounds inference rules, after generating a proper grammar for the rewrite rules. That is the next step in this work.

