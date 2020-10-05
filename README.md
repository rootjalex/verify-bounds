# verify-bounds
Verification of Halide bounds inference engine

## To run:
Replace **z3_dir>** in the `Makefile` with the directory of your z3 installation.

To verify a specific operation, run:
```
make op.out
./op.out
```
e.g.
```
make add.out
./add.out
```