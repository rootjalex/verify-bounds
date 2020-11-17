#include "Interval.h"
#include "Check.h"

#define NBITS 8
// TODO: need framework for doing bv intervals

// expects UNSIGNED bit vectors
// in Halide: uint >> uint : logical shift right
z3::expr uint_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::lshr(a, b);
}

// in Halide: int >> uint : arithmetic shift right
z3::expr mixed_iu_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::ashr(a, b);
}

// in Halide: uint >> int : unsure if well-defined? not tested in correctness/bitwise_ops.cpp
z3::expr mixed_ui_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::ite(b < 0, z3::shl(a, -1 * b), z3::lshr(a, b));
}

// in Halide:
//   int >> int (pos) : arithmetic shift right
//   int >> int (neg) : shift left
z3::expr int_shift_right(const z3::expr &a, const z3::expr &b) {
    return z3::ite(b < 0, z3::shl(a, -1 * b), z3::ashr(a, b));
}

struct ShiftParams {
    bool isUpperBounded = false;
    bool isLowerBounded = false;
    bool isUint = false;
    const z3::expr &upper;
    const z3::expr &lower;
};

void apply_shift_params(const z3::expr &i, z3::solver &solver, ShiftParams &a_params) {
    if (a_params.isUint) {
        if (a_params.isUpperBounded) {
            solver.add(z3::ule(i, a_params.upper));
        }
        if (a_params.isLowerBounded) {
            solver.add(z3::uge(i, a_params.lower));
        }
    } else {
        if (a_params.isUpperBounded) {
            solver.add(i <= a_params.upper);
        }
        if (a_params.isLowerBounded) {
            solver.add(i >= a_params.lower);
        }
    }
}

z3::expr count_set_bits(const z3::expr &i) {
    z3::expr count = i.ctx().bv_val(0, NBITS);
    z3::expr temp = i;
    for (int i = 0; i < NBITS; i++) {
        count = count + (z3::lshr(temp, i) & 0x1);
    }
    return count;

    // uncomment this for NBITS=32
    // courtesy of https://graphics.stanford.edu/~seander/bithacks.html
    // const z3::expr mask0 = i.ctx().bv_val(0x55555555u, NBITS);
    // const z3::expr mask1 = i.ctx().bv_val(0x33333333u, NBITS);
    // const z3::expr mask2 = i.ctx().bv_val(0xF0F0F0Fu, NBITS);
    // const z3::expr mask3 = i.ctx().bv_val(0x1010101u, NBITS);
    // z3::expr temp0 = i - (z3::lshr(i, 1) & mask0);
    // z3::expr temp1 = (temp0 & mask1) + (z3::lshr(temp0, 2) & mask1);
    // z3::expr temp2 = z3::lshr(((temp1 + z3::lshr(temp1, 4) & mask2) * mask3), 24);
    // return temp2;
}

// no overflow for i >> j
void disallow_overflow(const z3::expr &i, const z3::expr &j, const z3::expr &res, bool aIsUint, z3::solver &solver) {
    z3::expr jneg = (j < 0);
    z3::expr bad_bit_count = (count_set_bits(i) != count_set_bits(res));
    // sign change on an integer is overflow, the false can be optimized out
    z3::expr sign_change = (aIsUint) ? (i.ctx().bool_val(false)) : ((i > 0) && res < 0);
    // overflow only UB for Int(32) and Int(64)
    solver.add(!(!aIsUint && jneg && (bad_bit_count || sign_change)));
}

void check_shift_right(ShiftParams &a_params, ShiftParams &b_params, bool isUpperBounded, bool isUint,
                        const z3::expr &bound, z3::solver &solver, z3::context &context) {
    
    const z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr i = context.bv_const("i", NBITS);
    z3::expr j = context.bv_const("j", NBITS);
    if (b_params.isUint) {
        solver.add(z3::ult(j, NBITS));
    } else {
        solver.add(j < NBITS);
        solver.add(j > -NBITS);
    }

    apply_shift_params(i, solver, a_params);
    apply_shift_params(j, solver, b_params);

    z3::expr res(context);
    if (a_params.isUint && b_params.isUint) {
        res = uint_shift_right(i, j);
    } else if (!a_params.isUint && b_params.isUint) {
        res = mixed_iu_shift_right(i, j);
    } else if (a_params.isUint && !b_params.isUint) {
        res = mixed_ui_shift_right(i, j);
    } else {
        // !a_params.isUint && !b_params.isUint
        res = int_shift_right(i, j);
    }

    // disallow overflow if b can be negative
    if(!b_params.isUint) {
        disallow_overflow(i, j, res, /* aIsUint */a_params.isUint, solver);
    }

    // check if possible for result to be out of range
    if (isUpperBounded) {
        if (isUint) {
            solver.add(z3::ugt(res, bound));
        } else {
            solver.add(res > bound);
        }
    } else {
        if (isUint) {
            solver.add(z3::ult(res, bound));
        } else {
            solver.add(res < bound);
        }
    }

    z3::check_result ans = solver.check();
    if (ans == z3::unsat) {
        // std::cout << solver.to_smt2() << std::endl;
        std::cout << "proved" << std::endl;
    } else if(ans == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else {
        // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();
        std::cout << model << std::endl;

        // print a
        std::cout << "[";
        if (a_params.isLowerBounded) {
            std::cout << model.eval(a_params.lower);
        } else {
            std::cout << "_";
        }
        std::cout << ", ";
        if (a_params.isUpperBounded) {
            std::cout << model.eval(a_params.upper);
        } else {
            std::cout << "_";
        }

        std::cout << "] >> [";

        // print b
        if (b_params.isLowerBounded) {
            std::cout << model.eval(b_params.lower);
        } else {
            std::cout << "_";
        }
        std::cout << ", ";
        if (b_params.isUpperBounded) {
            std::cout << model.eval(b_params.upper);
        } else {
            std::cout << "_";
        }
        
        std::cout << "] = ";

        // print calculated bounds
        if (isUpperBounded) {
            std::cout << "[_, " << model.eval(bound) << "]" << std::endl;
        } else {
            std::cout << "[" << model.eval(bound) << ", _]" << std::endl;
        }

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " >> ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
}

/*
b_interval.is_bounded()
bool b_max_ok_positive = can_prove(b_interval.max >= 0 &&
                        b_interval.max < t.bits());
a_interval.has_lower_bound()
can_prove(a_interval.min >= 0) && b_max_ok_positive

Note: nothing is known about the types of a or b
must try:
    int >> int
    uint >> int
    uint >> uint
    int >> uint
*/
// [48, _] >> [-124, 5] = [1, _] (48 >. 5)
// 64 >> -2 = 0
void test_pos_int_lb_rshift_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] >> [b0, b1] && b1 >= 0 && b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    solver.add(a0 >= 0); // a is an integer

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(b0 <= b1);
    // treat b like an integer
    solver.add(b1 >= 0);
    solver.add(b1 < NBITS);

    // interval.min = a_interval.min >> b_interval.max;
    z3::expr emin = int_shift_right(a0, b1);
    disallow_overflow(a0, b1, emin, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=false, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_pos_uint_lb_rshift_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[a0, _] >> [b0, b1] && b1 >= 0 && b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS); // a is unsigned

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);

    // treat b like an integer
    solver.add(b0 <= b1);
    solver.add(b1 >= 0);
    solver.add(b1 < NBITS);

    // interval.min = a_interval.min >> b_interval.max;
    z3::expr emin = mixed_ui_shift_right(a0, b1);
    disallow_overflow(a0, b1, emin, /* aIsUint */true, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=true, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */true, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_pos_uint_lb_rshift_uint() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[a0, _] >> u[b0, b1] && b1 >= 0 && b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS); // a is unsigned

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // treat b as unsigned
    solver.add(z3::ule(b0, b1));
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));

    // interval.min = a_interval.min >> b_interval.max;
    z3::expr emin = uint_shift_right(a0, b1);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=true, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */true, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_pos_int_lb_rshift_uint() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] >> u[b0, b1] && b1 >= 0 && b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    solver.add(a0 >= 0); // a is an integer

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // treat b as unsigned
    solver.add(z3::ule(b0, b1));
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));

    // interval.min = a_interval.min >> b_interval.max;
    z3::expr emin = mixed_iu_shift_right(a0, b1);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=false, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}


/*
b_interval.is_bounded()
bool b_max_ok_negative =
    !b_interval.max.type().is_uint() &&
    can_prove(b_interval.max < 0 && b_interval.max > -t.bits());
a_interval.has_lower_bound()
can_prove(a_interval.min < 0) && b_max_ok_negative

Note: a and b must be signed, only one case:
    int >> int
*/
void test_unk_int_lb_rshift_possibly_neg_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] >> [b0, b1] && b1 < 0 && b1 > -t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    // a is an integer
    solver.add(a0 < 0);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(b0 <= b1);
    // treat b like an integer
    solver.add(b1 < 0);
    solver.add(b1 > -NBITS);

    // interval.min = a_interval.min << abs(b_interval.max);
    z3::expr emin = int_shift_right(a0, b1);
    disallow_overflow(a0, b1, emin, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=false, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

/*
b_interval.is_bounded()
a_interval.has_lower_bound()
bool b_min_ok_positive = can_prove(b_interval.min >= 0 &&
                                    b_interval.min < t.bits());
bool b_max_ok_positive = can_prove(b_interval.max >= 0 &&
                                    b_interval.max < t.bits());

Note: nothing is known about the types of a or b
must try:
    int >> int
    uint >> int
    uint >> uint
    int >> uint
*/
void test_unk_int_lb_rshift_pos_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] >> [b0, b1] && b1, b0 >= 0 && b0, b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // treat b as signed
    solver.add(b0 <= b1);
    solver.add(b1 >= 0);
    solver.add(b1 <= NBITS);
    solver.add(b0 >= 0);
    solver.add(b0 <= NBITS);

    // interval.min = min(a_interval.min >> b_interval.min,
    //                    a_interval.min >> b_interval.max);
    z3::expr temp_min = int_shift_right(a0, b0);
    z3::expr temp_max = int_shift_right(a0, b1);
    z3::expr emin = ite(temp_min < temp_max, temp_min, temp_max); // min()

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=false, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_unk_uint_lb_rshift_pos_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[a0, _] >> [b0, b1] && b1, b0 >= 0 && b0, b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // treat b as signed
    solver.add(b0 <= b1);
    solver.add(b1 >= 0);
    solver.add(b1 <= NBITS);
    solver.add(b0 >= 0);
    solver.add(b0 <= NBITS);

    // interval.min = min(a_interval.min >> b_interval.min,
    //                    a_interval.min >> b_interval.max);
    z3::expr temp_min = mixed_ui_shift_right(a0, b0);
    z3::expr temp_max = mixed_ui_shift_right(a0, b1);
    z3::expr emin = ite(z3::ult(temp_min, temp_max), temp_min, temp_max); // min()

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=true, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */true, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_unk_uint_lb_rshift_pos_uint() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[a0, _] >> u[b0, b1] && b1, b0 >= 0 && b0, b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // treat b as unsigned
    solver.add(z3::ule(b0, b1));
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));

    // interval.min = min(a_interval.min >> b_interval.min,
    //                    a_interval.min >> b_interval.max);
    z3::expr temp_min = uint_shift_right(a0, b0);
    z3::expr temp_max = uint_shift_right(a0, b1);
    z3::expr emin = ite(z3::ult(temp_min, temp_max), temp_min, temp_max); // min()

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=true, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */true, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_unk_int_lb_rshift_pos_uint() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] >> u[b0, b1] && b1, b0 >= 0 && b0, b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // treat b as unsigned
    solver.add(z3::ule(b0, b1));
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));

    // interval.min = min(a_interval.min >> b_interval.min,
    //                    a_interval.min >> b_interval.max);
    z3::expr temp_min = mixed_iu_shift_right(a0, b0);
    z3::expr temp_max = mixed_iu_shift_right(a0, b1);
    z3::expr emin = ite(temp_min < temp_max, temp_min, temp_max); // min()

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=false, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}


/*
b_interval.is_bounded()
bool b_min_ok_negative =
    !b_interval.min.type().is_uint() &&
    can_prove(b_interval.min < 0 && b_interval.min > -t.bits());
bool b_max_ok_negative =
    !b_interval.max.type().is_uint() &&
    can_prove(b_interval.max < 0 && b_interval.max > -t.bits());
a_interval.has_lower_bound()
b_min_ok_negative && b_max_ok_negative

Note: b must be signed, only two cases:
    int >> int
    uint >> int

*/
void test_unk_int_lb_rshift_neg_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] >> [b0, b1] && b0, b1 < 0 && b0, b1 > -t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(b0 <= b1);
    // b is signed
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);
    solver.add(b1 < 0);
    solver.add(b1 > -NBITS);

    /*
    interval.min = min(a_interval.min << abs(b_interval.min),
                        a_interval.min << abs(b_interval.max));
    */
    z3::expr temp_min = int_shift_right(a0, b0);
    z3::expr temp_max = int_shift_right(a0, b1);
    z3::expr emin = ite(temp_min < temp_max, temp_min, temp_max); // min()
    disallow_overflow(a0, b0, temp_min, /* aIsUint */false, solver);
    disallow_overflow(a0, b1, temp_max, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=false, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_unk_uint_lb_rshift_neg_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[a0, _] >> [b0, b1] && b0, b1 < 0 && b0, b1 > -t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(b0 <= b1);
    // b is signed
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);
    solver.add(b1 < 0);
    solver.add(b1 > -NBITS);

    /*
    interval.min = min(a_interval.min << abs(b_interval.min),
                        a_interval.min << abs(b_interval.max));
    */
    z3::expr temp_min = mixed_ui_shift_right(a0, b0);
    z3::expr temp_max = mixed_ui_shift_right(a0, b1);
    z3::expr emin = ite(z3::ult(temp_min, temp_max), temp_min, temp_max); // min()
    // uints allowed to overflow

    // a is uint, b is int
    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=true, .upper=zero, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */false, /* isUint */true, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}


/*
b_interval.is_bounded()
bool b_min_ok_positive = can_prove(b_interval.min >= 0 &&
                            b_interval.min < t.bits());
a_interval.has_upper_bound()
can_prove(a_interval.max >= 0) && b_min_ok_positive

Note: type of b is irrelevant, it is always pos
must try:
    int >> uint
    uint >> uint
*/
void test_possibly_pos_int_ub_rshift_uint() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] >> u[b0, b1] && b0 >= 0 && b0 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(a1 >= 0); // a is an integer

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(z3::ule(b0, b1));
    // b is signed
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));

    // interval.max = a_interval.max >> b_interval.min;
    z3::expr emax = mixed_iu_shift_right(a1, b0);
    // the above can't overflow because b0 is strictly positive
    // disallow_overflow(a1, b0, emax, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=false, .upper=a1, .lower=zero};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */true, /* isUint */false, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_possibly_pos_uint_ub_rshift_uint() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[_, a1] >> u[b0, b1] && b0 >= 0 && b0 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(z3::uge(a1, 0)); // a is unsigned

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(z3::ule(b0, b1));
    // b is signed
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));

    // interval.max = a_interval.max >> b_interval.min;
    z3::expr emax = uint_shift_right(a1, b0);
    // the above can't overflow because b0 is strictly positive
    // disallow_overflow(a1, b0, emax, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=true, .upper=a1, .lower=zero};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */true, /* isUint */true, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}


/*
b_interval.is_bounded()
bool b_min_ok_negative =
    !b_interval.min.type().is_uint() &&
    can_prove(b_interval.min < 0 && b_interval.min > -t.bits());
a_interval.has_upper_bound()
can_prove(a_interval.max < 0) && b_min_ok_negative

Note: a is neg, must be signed. b must also be signed
must try:
    int >> int
*/
void test_neg_int_ub_rshift_possibly_neg_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1 (-)] >> [b0, b1] && b0 < 0 && b0 > -t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(a1 < 0); // a is signed

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b is signed
    solver.add(b0 <= b1);
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);

    // interval.max = a_interval.max << abs(b_interval.min);
    z3::expr emax = int_shift_right(a1, b0);
    disallow_overflow(a1, b0, emax, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=false, .upper=a1, .lower=zero};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */true, /* isUint */false, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

/*
b_interval.is_bounded()
bool b_min_ok_positive = can_prove(b_interval.min >= 0 &&
                            b_interval.min < t.bits());
bool b_max_ok_positive = can_prove(b_interval.max >= 0 &&
                                    b_interval.max < t.bits());
a_interval.has_upper_bound()
b_min_ok_positive && b_max_ok_positive

Note: a type is unknown, but b is strictly noneg (ignore int case)
must try:
    int >> uint
    uint >> uint
*/
void test_int_ub_rshift_pos_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] >> u[b0, b1] && b0, b1 >= 0 && b0, b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b is unsigned
    solver.add(z3::ule(b0, b1));
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));

    /*
    interval.max = max(a_interval.max >> b_interval.max,
                        a_interval.max >> b_interval.min);
    */
    z3::expr temp_max = mixed_iu_shift_right(a1, b1);
    z3::expr temp_min = mixed_iu_shift_right(a1, b0);
    z3::expr emax = ite(temp_max > temp_min, temp_max, temp_min); // max()
    // the above can't overflow because b is strictly nonnegative

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=false, .upper=a1, .lower=zero};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */true, /* isUint */false, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_uint_ub_rshift_pos_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[_, a1] >> u[b0, b1] && b0, b1 >= 0 && b0, b1 < t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);

    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b is unsigned
    solver.add(z3::ule(b0, b1));
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));

    /*
    interval.max = max(a_interval.max >> b_interval.max,
                        a_interval.max >> b_interval.min);
    */
    z3::expr temp_max = uint_shift_right(a1, b1);
    z3::expr temp_min = uint_shift_right(a1, b0);
    z3::expr emax = ite(z3::ugt(temp_max, temp_min), temp_max, temp_min); // max()
    // the above can't overflow because b is strictly nonnegative

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=true, .upper=a1, .lower=zero};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=true, .upper=b1, .lower=b0};

    // output is lower bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */true, /* isUint */true, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

/*
b_interval.is_bounded()
bool b_min_ok_negative =
    !b_interval.min.type().is_uint() &&
    can_prove(b_interval.min < 0 && b_interval.min > -t.bits());
bool b_max_ok_negative =
    !b_interval.max.type().is_uint() &&
    can_prove(b_interval.max < 0 && b_interval.max > -t.bits());
a_interval.has_upper_bound()
b_min_ok_negative && b_max_ok_negative

Note: a type is unknown, but b is stictly signed
must try:
    int >> int
    uint >> int
*/
void test_unk_int_ub_rshift_neg_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] >> [b0, b1] && b0, b1 < 0 && b0, b1 > -t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b is signed
    solver.add(b0 <= b1);
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);
    solver.add(b1 < 0);
    solver.add(b1 > -NBITS);

    /*
    interval.max = max(a_interval.max << abs(b_interval.max),
                        a_interval.max << abs(b_interval.min));
    */
    z3::expr temp_min = int_shift_right(a1, b0);
    z3::expr temp_max = int_shift_right(a1, b1);
    z3::expr emax = ite(temp_min > temp_max, temp_min, temp_max); // max()
    disallow_overflow(a1, b0, temp_min, /* aIsUint */false, solver);
    disallow_overflow(a1, b1, temp_max, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=false, .upper=a1, .lower=zero};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is upper bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */true, /* isUint */false, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_unk_uint_ub_rshift_neg_int() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[_, a1] >> [b0, b1] && b0, b1 < 0 && b0, b1 > -t.bits()" << std::endl;

    z3::context context;
    z3::solver solver(context);
    z3::expr zero = context.bv_val(0x0ull, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b is signed
    solver.add(b0 <= b1);
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);
    solver.add(b1 < 0);
    solver.add(b1 > -NBITS);

    /*
    interval.max = max(a_interval.max << abs(b_interval.max),
                        a_interval.max << abs(b_interval.min));
    */
    z3::expr temp_min = mixed_ui_shift_right(a1, b0);
    z3::expr temp_max = mixed_ui_shift_right(a1, b1);
    z3::expr emax = ite(z3::ugt(temp_min, temp_max), temp_min, temp_max); // max()
    // disallow_overflow(a1, b0, temp_min, /* aIsUint */false, solver);
    // disallow_overflow(a1, b1, temp_max, /* aIsUint */false, solver);

    // both are integers for this test
    ShiftParams a_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=true, .upper=a1, .lower=zero};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=true, .isUint=false, .upper=b1, .lower=b0};

    // output is upper bounded and integer
    check_shift_right(a_params, b_params, /* isUpperBounded */true, /* isUint */true, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv) {
    test_pos_int_lb_rshift_int(); // this one takes a very long time with NBITS=32
    // test_pos_uint_lb_rshift_int(); // bug
    test_pos_uint_lb_rshift_uint();
    test_pos_int_lb_rshift_uint();
    test_unk_int_lb_rshift_possibly_neg_int();
    test_unk_int_lb_rshift_pos_int();
    test_unk_uint_lb_rshift_pos_int();
    test_unk_uint_lb_rshift_pos_uint();
    test_unk_int_lb_rshift_pos_uint();

    test_unk_int_lb_rshift_neg_int(); // this one takes a very long time with NBITS=32
    // test_unk_uint_lb_rshift_neg_int(); // bug
    
    test_possibly_pos_int_ub_rshift_uint();
    test_possibly_pos_uint_ub_rshift_uint();
    test_neg_int_ub_rshift_possibly_neg_int(); // this one takes a very long time with NBITS=32
    test_int_ub_rshift_pos_int();
    test_uint_ub_rshift_pos_int();

    test_unk_int_ub_rshift_neg_int(); // bug?
    // test_unk_uint_ub_rshift_neg_int(); // bug
}