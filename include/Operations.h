#pragma once

#include "z3++.h"
#include <string>

enum Operation {
    Add = 0,
    Sub,
    Div,
    Mul
};

std::string OpToString(Operation op);

z3::expr generate_op(z3::context &context, Operation op, z3::expr &i, z3::expr &j);

// i / j in Halide semantics
z3::expr halide_div(z3::context &context, z3::expr &i, z3::expr &j);

// z3::abs is broken
z3::expr z3_abs(z3::expr &i);
