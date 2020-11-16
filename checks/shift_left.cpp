#include "Interval.h"
#include "Check.h"

#define NBITS 64

// TODO: need framework for doing bv intervals

// expects bit vectors
z3::expr shift_left(const z3::expr &a, const z3::expr &b) {
    return z3::ite(b < 0, z3::lshr(a, b * -1), z3::shl(a, b));
}

void check_shift_left(bool isUpperBound, const z3::expr &a_bound, const z3::expr &b_bound,
                        const z3::expr &bound, z3::solver &solver, z3::context &context) {

    const z3::expr mask = context.bv_val(0x7fffffff00000000ull, NBITS);
    const z3::expr zero = context.bv_val(0x0ull, NBITS);
    const z3::expr min_bv = context.bv_val(INT_MIN, NBITS);
    const z3::expr max_bv = context.bv_val(INT_MAX, NBITS);

    z3::expr i = context.bv_const("i", NBITS);
    solver.add(i >= min_bv && i <= max_bv); // no overflow
    solver.add((i & mask) == zero); // no overflow
    
    z3::expr j = context.bv_const("j", NBITS);
    solver.add(j < 32); // otherwise overflow

    if (isUpperBound) {
        solver.add(i <= a_bound);
        solver.add(j <= b_bound);
    } else {
        solver.add(a_bound <= i);
        solver.add(b_bound <= j);
    }

    z3::expr res = shift_left(i, j);
    solver.add(res >= min_bv && res <= max_bv); // no overflow
    solver.add((res & mask) == zero);

    if (isUpperBound) {
        // if possible to be more than our max, that's bad
        solver.add(res > bound);
    } else {
        // if possible to be less than our min, that's bad
        solver.add(res < bound);
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
    std::cout << "Test [a0, _] << [b0, _] && b0 >= 0 && b0 < t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr mask = context.bv_val(0x7fffffff00000000ull, NBITS);
    z3::expr zero = context.bv_val(0x0ull, NBITS);
    z3::expr min_bv = context.bv_val(INT_MIN, NBITS);
    z3::expr max_bv = context.bv_val(INT_MAX, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    solver.add(a0 >= min_bv && a0 <= max_bv); // no overflow
    solver.add((a0 & mask) == zero); // no overflow
    // solver.add(z3::uge(a0, INT_MIN) && z3::ule(a0, INT_MAX)); // restrict to 32-bit integers
    z3::expr b0 = context.bv_const("b0", NBITS);
    solver.add(z3::uge(b0, 0));
    solver.add(z3::ult(b0, 32));

    // interval.min = a_interval.min << b_interval.min;
    z3::expr emin = z3::shl(a0, b0);       // lower bound
    // solver.add(z3::uge(emin, INT_MIN) && z3::ule(emin, INT_MAX)); // no overflow
    solver.add(emin >= min_bv && emin <= max_bv); // no overflow
    solver.add((emin & mask) == zero); // no overflow

    check_shift_left(false, a0, b0, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_lower_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] << [b0, _] && b0 < 0 && b0 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr mask = context.bv_val(0x7fffffff00000000ull, NBITS);
    z3::expr zero = context.bv_val(0x0ull, NBITS);
    z3::expr min_bv = context.bv_val(INT_MIN, NBITS);
    z3::expr max_bv = context.bv_val(INT_MAX, NBITS);

    z3::expr a0 = context.bv_const("a0", NBITS);
    solver.add(a0 >= min_bv && a0 <= max_bv); // no overflow
    solver.add((a0 & mask) == zero); // no overflow

    z3::expr b0 = context.bv_const("b0", NBITS);

    // can_prove(b_interval.min < 0 && b_interval.min > -t.bits()))
    solver.add(b0 < 0);
    solver.add(b0 > -32);

    // interval.min = a_interval.min >> abs(b_interval.min);
    z3::expr emin = z3::lshr(a0, b0 * (-1)); // lower bound

    check_shift_left(false, a0, b0, emin, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bound_lshift_nonneg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] << [_, b1] && b1 >= 0 && b1 < t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr mask = context.bv_val(0x7fffffff00000000ull, NBITS);
    z3::expr zero = context.bv_val(0x0ull, NBITS);
    z3::expr min_bv = context.bv_val(INT_MIN, NBITS);
    z3::expr max_bv = context.bv_val(INT_MAX, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(a1 >= min_bv && a1 <= max_bv); // no overflow
    solver.add((a1 & mask) == zero); // no overflow

    z3::expr b1 = context.bv_const("b1", NBITS);
    // b1 >= 0 && b1 < t.bits()
    solver.add(z3::uge(b1, 0));
    solver.add(z3::ult(b1, 32));

    // interval.max = a_interval.max << b_interval.max;
    z3::expr emax = z3::shl(a1, b1);       // lower bound
    solver.add(emax >= min_bv && emax <= max_bv); // no overflow
    solver.add((emax & mask) == zero); // no overflow

    check_shift_left(true, a1, b1, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bound_lshift_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] << [_, b1] && b1 < 0 && b1 > -t.bits()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr mask = context.bv_val(0x7fffffff00000000ull, NBITS);
    z3::expr zero = context.bv_val(0x0ull, NBITS);
    z3::expr min_bv = context.bv_val(INT_MIN, NBITS);
    z3::expr max_bv = context.bv_val(INT_MAX, NBITS);

    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(a1 >= min_bv && a1 <= max_bv); // no overflow
    solver.add((a1 & mask) == zero); // no overflow

    z3::expr b1 = context.bv_const("b1", NBITS);
    // b1 < 0 && b1 > -t.bits()
    solver.add(b1 < 0);
    solver.add(b1 > -32);

    // interval.max = a_interval.max >> abs(b_interval.max);
    z3::expr emax = z3::lshr(a1, b1 * -1);       // lower bound
    solver.add(emax >= min_bv && emax <= max_bv); // no overflow
    solver.add((emax & mask) == zero); // no overflow

    check_shift_left(true, a1, b1, emax, solver, context);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv) {
    test_lower_bound_lshift_nonneg();
    test_lower_bound_lshift_neg();
    test_upper_bound_lshift_nonneg();
    test_upper_bound_lshift_neg();
}