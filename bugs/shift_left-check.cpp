#include "Interval.h"
#include "Check.h"
#include "Operations.h"

#define NBITS 8

// TODO: need framework for doing bv intervals

// don't let i << j overflow
void disallow_overflow(const z3::expr &i, const z3::expr &j, const z3::expr &res, bool iIsUint, bool jIsUint, z3::solver &solver) {
    z3::expr jpos = (jIsUint || (j >= 0));
    z3::expr bad_bit_count = (count_set_bits(i, NBITS) != count_set_bits(res, NBITS));
    // sign change on an integer is overflow, the false can be optimized out
    z3::expr sign_change = (iIsUint) ? (i.ctx().bool_val(false)) : ((i > 0) && res < 0);
    solver.add(!(jpos && (bad_bit_count || sign_change)));
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

void fix_neg_lower_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Fix for [a0(-), _] << [b0, _] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);
    bool aIsUint = false;
    bool bIsUint = false;

    // added
    solver.add(a0 < 0);

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    solver.add(b0 < 0);
    solver.add(b0 > -NBITS);

    // interval.min = a_interval.min >> abs(b_interval.min);
    z3::expr emin = a0;
    // overflow not possible with right shift

    check_shift_left(false, a0, b0, aIsUint, bIsUint, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv) {
    bug_lower_bound_lshift_neg();
    fix_pos_lower_bound_lshift_neg();
    fix_neg_lower_bound_lshift_neg();
}