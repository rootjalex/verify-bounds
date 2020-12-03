#include "Interval.h"
#include "Check.h"
#include "Operations.h"
#include <vector>

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

void check_shift_left(ShiftParams &a_params, ShiftParams &b_params, bool isUpperBound,
                        const z3::expr &bound, z3::solver &solver, z3::context &context) {
    
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

    z3::expr res = left_shift(i, j, /* aIsUint */a_params.isUint, /* bIsUint */ b_params.isUint);
    disallow_overflow(i, j, res, /* aIsUint */a_params.isUint, /* bIsUint */ b_params.isUint, solver);

    if (isUpperBound) {
        if (a_params.isUint) {
            solver.add(z3::ugt(res, bound));
        } else {
            solver.add(res > bound);
        }
    } else {
        if (a_params.isUint) {
            solver.add(z3::ult(res, bound));
        } else {
            solver.add(res < bound);
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

        std::cout << a_params.toString(model);
        std::cout << " << ";
        std::cout << b_params.toString(model) << std::endl;
        std::cout << "Resultant bounds: [";
        if (isUpperBound) {
            std::cout << "_, " << model.eval(bound);
        } else {
            std::cout << model.eval(bound) << ", _";
        }
        std::cout << "]" << std::endl;

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " << ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
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
            // solver.add(j > 0);
            solver.add(j >= b_bound);
        } else {
            solver.add(z3::uge(j, b_bound));
        }
    }

    z3::expr res = left_shift(i, j, aIsUint, bIsUint);

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

/*
else if (a_interval.has_lower_bound() &&
            b_interval.has_lower_bound() &&
            !b_interval.min.type().is_uint() &&
            can_prove(b_interval.min < 0 &&
                        b_interval.min > -t.bits())) {
    interval.min = a_interval.min >> abs(b_interval.min);
}
*/
void bug_lower_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Original for [a0, _] << [b0, _] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);

    // interval.min = a_interval.min >> abs(b_interval.min);
    z3::expr emin = z3::ashr(a0, b0 * -1);
    // overflow not possible with right shift

    check_shift_left(false, a0, b0, aIsUint, bIsUint, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void fix_pos_lower_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Fix for [a0(+), _] << [b0, _] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    // added
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

void fix_neg_full_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Fix for [a0(-), _] << [b0, b1] && b0 < 0 && b0 > -t.bits() && b1 <= 0" << std::endl;
    
    z3::context context;
    z3::solver solver(context);
    z3::expr unb = context.bv_const("unb", NBITS); // used for default unbounded arg

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    // can_prove(a_interval.min < 0)
    solver.add(a0 < 0);

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    // solver.add(b0 < 0);
    // solver.add(b0 > -NBITS);
    // can_prove(b_interval.max <= 0)
    solver.add(b1 <= 0);

    // interval.min = a_interval.min;
    z3::expr emin = a0;

    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=aIsUint, .upper=unb, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=bIsUint, .upper=b1, .lower=unb};

    check_shift_left(a_params, b_params, /*isUpperBound*/false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void fix_neg_full_bound_lshift_possibly_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Fix for [a0(-), _] << [b0, b1] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);
    z3::expr unb = context.bv_const("unb", NBITS); // used for default unbounded arg

    z3::expr a0 = context.bv_const("a0", NBITS);
    // z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    // can_prove(a_interval.min < 0)
    solver.add(a0 < 0);

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    // solver.add(b0 < 0);
    // solver.add(b0 > -NBITS);

    // interval.min = a_interval.min;
    z3::expr temp_shift = left_shift(a0, b1, aIsUint, bIsUint);
    disallow_overflow(a0, b1, temp_shift, aIsUint, bIsUint, solver);
    z3::expr emin = ite(temp_shift < a0, temp_shift, a0);

    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=aIsUint, .upper=unb, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=true, .isLowerBounded=false, .isUint=bIsUint, .upper=b1, .lower=unb};

    check_shift_left(a_params, b_params, /*isUpperBound*/false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void fix_pos_full_bound_lshift_ub_nonpos() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Fix for [a0(+), _] << [_, _]" << std::endl;
    
    z3::context context;
    z3::solver solver(context);
    z3::expr unb = context.bv_const("unb", NBITS); // used for default unbounded arg

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    // can_prove(a_interval.min >= 0 && b_interval.max <= 0)
    solver.add(a0 >= 0);
    // solver.add(b1 <= 0);

    // interval.min = make_zero(t);
    z3::expr emin = context.bv_val(0, NBITS);

    ShiftParams a_params = {.isUpperBounded=false, .isLowerBounded=true, .isUint=aIsUint, .upper=unb, .lower=a0};
    ShiftParams b_params = {.isUpperBounded=false, .isLowerBounded=false, .isUint=bIsUint, .upper=unb, .lower=unb};

    check_shift_left(a_params, b_params, /*isUpperBound*/false, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv) {
    // [-125, _] << [-7, _] |-> -66 << -1 = -33
    bug_lower_bound_lshift_neg();
    fix_pos_lower_bound_lshift_neg();
    fix_neg_full_bound_lshift_neg();
    fix_neg_full_bound_lshift_possibly_neg();
    fix_pos_full_bound_lshift_ub_nonpos();
}