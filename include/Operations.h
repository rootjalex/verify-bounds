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
    return z3::ite(b < 0, z3::ashr(a, b * -1), ite(a >= 0, z3::shl(a, b), a * z3::shl(1, b)));
}

inline z3::expr left_shift(const z3::expr &a, const z3::expr &b, bool aIsUint, bool bIsUint) {
    if (aIsUint && bIsUint) {
        return uint_shift_left(a, b);
    } else if (!aIsUint && bIsUint) {
        return iu_shift_left(a, b);
    } else if (aIsUint && !bIsUint) {
        return ui_shift_left(a, b);
    } else {
        // !aIsUint && !bIsUint
        return int_shift_left(a, b);
    }
}

// expects UNSIGNED bit vectors
// in Halide: uint >> uint : logical shift right
inline z3::expr uint_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::lshr(a, b);
}

// in Halide: int >> uint : arithmetic shift right
inline z3::expr mixed_iu_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::ashr(a, b);
}

// in Halide: uint >> int : unsure if well-defined? not tested in correctness/bitwise_ops.cpp
inline z3::expr mixed_ui_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::ite(b < 0, z3::shl(a, -1 * b), z3::lshr(a, b));
}

// in Halide:
//   int >> int (pos) : arithmetic shift right
//   int >> int (neg) : shift left
inline z3::expr int_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::ite(b < 0, z3::shl(a, -1 * b), z3::ashr(a, b));
}

inline z3::expr count_set_bits(const z3::expr &i, size_t bits) {
    z3::expr count = i.ctx().bv_val(0, bits);
    z3::expr temp = i;
    for (int i = 0; i < bits; i++) {
        count = count + (z3::lshr(temp, i) & 0x1);
    }
    return count;
}