#pragma once

#include "z3++.h"
#include <string>

enum Operation {
    Add = 0,
    Sub,
    Div,
    Mul,
    Mod
};

std::string OpToString(Operation op);

z3::expr generate_op(Operation op, z3::expr &i, z3::expr &j);

// i / j in Halide semantics (i / 0 == 0)
z3::expr halide_div(z3::expr &i, z3::expr &j);

// i % j in Halide semantics (i % 0 == 0)
z3::expr halide_mod(z3::expr &i, z3::expr &j);

// z3::abs is broken
z3::expr z3_abs(z3::expr &i);
