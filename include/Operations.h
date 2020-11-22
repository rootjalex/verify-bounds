#pragma once

#include "z3++.h"
#include <string>

enum Operation {
    Add = 0,
    Sub,
    Div,
    Mul,
    Mod,
    Min,
    Max
};

std::string OpToString(Operation op);

z3::expr generate_op(Operation op, z3::expr &i, z3::expr &j);

// i / j in Halide semantics (i / 0 == 0)
z3::expr halide_div(z3::expr &i, z3::expr &j);

// i % j in Halide semantics (i % 0 == 0)
z3::expr halide_mod(z3::expr &i, z3::expr &j);

// z3::abs is broken
z3::expr z3_abs(z3::expr &i);

inline z3::expr ui_shift_left(const z3::expr &a, const z3::expr &b) {
    return z3::ite(b < 0, z3::lshr(a, b * -1), z3::shl(a, b));
}

inline z3::expr uint_shift_left(const z3::expr &a, const z3::expr &b) {
    return z3::shl(a, b);
}

// same as regular uint shift left
inline z3::expr iu_shift_left(const z3::expr &a, const z3::expr &b) {
    return z3::shl(a, b);
}

inline z3::expr int_shift_left(const z3::expr &a, const z3::expr &b) {
    return z3::ite(b < 0, z3::ashr(a, b * -1), z3::shl(a, b));
}

inline z3::expr count_set_bits(const z3::expr &i, size_t bits) {
    z3::expr count = i.ctx().bv_val(0, bits);
    z3::expr temp = i;
    for (int i = 0; i < bits; i++) {
        count = count + (z3::lshr(temp, i) & 0x1);
    }
    return count;
}