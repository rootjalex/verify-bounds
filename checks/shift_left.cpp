#include "Interval.h"
#include "Check.h"
#include "Operations.h"

#define NBITS 8

// TODO: need framework for doing bv intervals


// don't let i << j overflow
void disallow_overflow(const z3::expr &i, const z3::expr &j, const z3::expr &res, bool iIsUint, bool jIsUint, z3::solver &solver) {
    z3::expr jpos = (jIsUint || (j >= 0));
    z3::expr pos_bit_count = (count_set_bits(i, NBITS) != count_set_bits(res, NBITS)) && (iIsUint || (i >= 0));
    z3::expr i_sign_mask = z3::ashr((i & (1 << (NBITS-1))), NBITS);
    z3::expr j_sign_mask = z3::ashr((j & (1 << (NBITS-1))), NBITS);
    z3::expr extend_i = concat(i_sign_mask, i);
    z3::expr extend_j = concat(j_sign_mask, j);
    uint32_t mask = 0xffffffff >> (32 - (NBITS)); // mask of NBITS 1s, which is INT_MIN for NBITS
    z3::expr int_min = i.ctx().bv_val(mask, NBITS * 2);
    z3::expr neg_overflow = (iIsUint) ? (i.ctx().bool_val(false)) : (left_shift(extend_i, extend_j, iIsUint, jIsUint) < int_min);
    // sign change on an integer is overflow, the false can be optimized out
    z3::expr sign_change = (iIsUint) ? (i.ctx().bool_val(false)) : ((i > 0) && res < 0);
    solver.add(!(jpos && (pos_bit_count || sign_change || neg_overflow)));
}

void check_shift_left(bool isUpperBound, const z3::expr &a_bound, const z3::expr &b_bound,
                        bool aIsUint, bool bIsUint, const z3::expr &bound, z3::solver &solver, z3::context &context) {

    const z3::expr zero = context.bv_val(0x0ull, NBITS);
    z3::expr i = context.bv_const("i", NBITS);
    z3::expr j = context.bv_const("j", NBITS);
    solver.add(j < NBITS); // otherwise UB

    if (isUpperBound) {
        if (!aIsUint) {
            solver.add(i <= a_bound);
        } else {
            solver.add(z3::ule(i, a_bound));
        }
        if (!bIsUint) {
            solver.add(j <= b_bound);
        } else {
            solver.add(z3::ule(j, b_bound));
        }
    } else {
        if (!aIsUint) {
            solver.add(i >= a_bound);
        } else {
            solver.add(z3::uge(i, a_bound));
        }
        if (!bIsUint) {
            solver.add(j >= b_bound);
        } else {
            solver.add(z3::uge(j, b_bound));
        }
    }

    z3::expr res(context);
    if (aIsUint && bIsUint) {
        res = uint_shift_left(i, j);
    } else if (!aIsUint && bIsUint) {
        res = iu_shift_left(i, j);
    } else if (aIsUint && !bIsUint) {
        res = ui_shift_left(i, j);
    } else {
        // !aIsUint && !bIsUint
        res = int_shift_left(i, j);
    }

    disallow_overflow(i, j, res, aIsUint, bIsUint, solver);

    if (isUpperBound) {
        // if possible to be more than our max, that's bad
        if (!aIsUint) {
            solver.add(res > bound);
        } else {
            solver.add(z3::ugt(res, bound));
        }
    } else {
        // if possible to be less than our min, that's bad
        if (!aIsUint) {
            solver.add(res < bound);
        } else {
            solver.add(z3::ult(res, bound));
        }
    }
    
    z3::check_result ans = solver.check();
    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        if (isUpperBound) {
            std::cout << "[_, " << model.eval(a_bound) << "] << ";
            std::cout << "[_, " << model.eval(b_bound) << "]" << std::endl;
            std::cout << "Resultant bounds: [_, " << model.eval(bound) << "]" << std::endl;
        } else {
            std::cout << "[" << model.eval(a_bound) << ", _] << ";
            std::cout << "[" << model.eval(b_bound) << ", _]" << std::endl;
            std::cout << "Resultant bounds: [" << model.eval(bound) << ", _]" << std::endl;
        }

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " << ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
}

void test_lower_bound_lshift_nonneg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] << u[b0, _] && b0 >= 0 && b0 < t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    // b is unsigned because strictly non-neg
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));
    bool aIsUint = false;
    bool bIsUint = true;

    // interval.min = a_interval.min << b_interval.min;
    z3::expr emin = iu_shift_left(a0, b0);
    disallow_overflow(a0, b0, emin, aIsUint, bIsUint, solver);

    check_shift_left(false, a0, b0, aIsUint, bIsUint, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_uint_lower_bound_lshift_nonneg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[a0, _] << u[b0, _] && b0 >= 0 && b0 < t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    // b is unsigned because strictly non-neg
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, NBITS));
    bool aIsUint = true;
    bool bIsUint = true;

    // interval.min = a_interval.min << b_interval.min;
    z3::expr emin = uint_shift_left(a0, b0);
    // overflow is not UB for uints

    check_shift_left(false, a0, b0, aIsUint, bIsUint, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

/*
else if (a_interval.has_lower_bound() &&
            b_interval.has_lower_bound() &&
            !b_interval.min.type().is_uint() &&
            can_prove(b_interval.min < 0 &&
                        b_interval.min > -t.bits())) {
    interval.min = a_interval.min >> abs(b_interval.min);
}
*/
void test_nonneg_lower_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0(+), _] << [b0, _] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    solver.add(a0 >= 0);

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);

    // interval.min = a_interval.min >> abs(b_interval.min);
    z3::expr emin = z3::ashr(a0, b0 * -1);
    // overflow not possible with right shift

    check_shift_left(false, a0, b0, aIsUint, bIsUint, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_uint_lower_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[a0, _] << [b0, _] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    solver.add(a0 >= 0);

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);

    // interval.min = a_interval.min >> abs(b_interval.min);
    z3::expr emin = z3::ashr(a0, b0 * -1);
    // overflow not possible with right shift

    check_shift_left(false, a0, b0, aIsUint, bIsUint, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_neg_lower_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0(-), _] << [b0, _] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    solver.add(a0 >= 0);

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);

    // interval.min = a_interval.min >> abs(b_interval.min);
    z3::expr emin = z3::ashr(a0, b0 * -1);
    // overflow not possible with right shift

    check_shift_left(false, a0, b0, aIsUint, bIsUint, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}


void test_upper_bound_lshift_nonneg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] << u[_, b1] && b1 >= 0 && b1 < t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a1 = context.bv_const("a1", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b1 >= 0 && b1 < t.bits()
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));
    bool aIsUint = false;
    bool bIsUint = true;

    // interval.max = a_interval.max << b_interval.max;
    z3::expr emax = z3::shl(a1, b1);       // lower bound
    disallow_overflow(a1, b1, emax, aIsUint, bIsUint, solver);

    check_shift_left(true, a1, b1, aIsUint, bIsUint, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_uint_upper_bound_lshift_nonneg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[_, a1] << u[_, b1] && b1 >= 0 && b1 < t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a1 = context.bv_const("a1", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b1 >= 0 && b1 < t.bits()
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, NBITS));
    bool aIsUint = true;
    bool bIsUint = true;

    // interval.max = a_interval.max << b_interval.max;
    z3::expr emax = z3::shl(a1, b1);       // lower bound
    disallow_overflow(a1, b1, emax, aIsUint, bIsUint, solver);

    check_shift_left(true, a1, b1, aIsUint, bIsUint, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] << [_, b1] && b1 < 0 && b1 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a1 = context.bv_const("a1", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b1 < 0 && b1 > -t.bits()
    solver.add(b1 < 0);
    solver.add(b1 > -NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    // interval.max = a_interval.max >> abs(b_interval.max);
    z3::expr emax = z3::lshr(a1, b1 * -1);       // lower bound
    // impossible to overflow with right shift

    check_shift_left(true, a1, b1, aIsUint, bIsUint, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_uint_upper_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test u[_, a1] << [_, b1] && b1 < 0 && b1 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a1 = context.bv_const("a1", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    // b1 < 0 && b1 > -t.bits()
    solver.add(b1 < 0);
    solver.add(b1 > -NBITS);
    bool aIsUint = true;
    bool bIsUint = false;

    // interval.max = a_interval.max >> abs(b_interval.max);
    z3::expr emax = z3::lshr(a1, b1 * -1);       // lower bound
    // impossible to overflow with right shift

    check_shift_left(true, a1, b1, aIsUint, bIsUint, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv) {
    test_lower_bound_lshift_nonneg();
    test_nonneg_lower_bound_lshift_neg();
    test_neg_lower_bound_lshift_neg();
    test_upper_bound_lshift_nonneg();
    test_upper_bound_lshift_neg();

    test_uint_lower_bound_lshift_nonneg();
    // uint version for test_neg_lower_bound_lshift_neg() is not possible (no neg uints)
    test_uint_upper_bound_lshift_nonneg();
    test_uint_upper_bound_lshift_neg();
}