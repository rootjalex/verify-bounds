#include "Interval.h"
#include "Check.h"


void test_mod_unsigned_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test <any> % bounded unsigned Mod" << std::endl;
    z3::context context;
    z3::solver solver(context);
    // need to write this manually to use bit vectors (unsigned)
    z3::expr a0 = context.bv_const("a0", 32);
    z3::expr a1 = context.bv_const("a1", 32);
    solver.add(z3::uge(a1, a0));

    z3::expr b0 = context.bv_const("b0", 32);
    z3::expr b1 = context.bv_const("b1", 32);
    solver.add(z3::uge(b1, b0));
    
    z3::expr emin = context.bv_val(0, 32);
    z3::expr emax = max(emin, b1 - 1);

    z3::expr i = context.bv_const("i", 32);
    z3::expr j = context.bv_const("j", 32);

    // fully bounded
    solver.add(z3::uge(a0, i)); // a0 <= i
    solver.add(z3::uge(i, a1)); // i <= a1
    solver.add(z3::uge(b0, j)); // b0 <= j
    solver.add(z3::uge(j, b1)); // j <= b1
    solver.add(b0 == b1 && b1 == 0);

    z3::expr res = ite(j != 0, z3::urem(i, j), context.bv_val(0, 32)); // unsigned remainder

    // we just care about the upper bound tightness
    solver.add(res == emax);

    z3::check_result ans = solver.check();

    if (ans == z3::unsat) {
        std::cout << " NOT tight." << std::endl;
    } else if (ans == z3::unknown) {
        std::cout << " Unknown." << std::endl;
    } else {
        std::cout << " Tight." << std::endl;
    }

    std::cout << "-------------------" << std::endl;
}


void test_mod_unsigned_bounded_fix_zero() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test <any> % bounded unsigned 0 Mod fix" << std::endl;
    z3::context context;
    z3::solver solver(context);
    // need to write this manually to use bit vectors (unsigned)
    z3::expr a0 = context.bv_const("a0", 32);
    z3::expr a1 = context.bv_const("a1", 32);
    solver.add(z3::uge(a1, a0));

    z3::expr b0 = context.bv_const("b0", 32);
    z3::expr b1 = context.bv_const("b1", 32);
    solver.add(z3::uge(b1, b0));
    
    z3::expr emin = context.bv_val(0, 32);
    z3::expr emax = ite(b1 == 0, context.bv_val(0, 32), b1 - 1);
    
    max(emin, b1 - 1);

    z3::expr i = context.bv_const("i", 32);
    z3::expr j = context.bv_const("j", 32);

    // fully bounded
    solver.add(z3::uge(a0, i)); // a0 <= i
    solver.add(z3::uge(i, a1)); // i <= a1
    solver.add(z3::uge(b0, j)); // b0 <= j
    solver.add(z3::uge(j, b1)); // j <= b1
    solver.add(b0 == b1 && b1 == 0);

    z3::expr res = ite(j != 0, z3::urem(i, j), context.bv_val(0, 32)); // remainder

    // we just care about the upper bound tightness
    solver.add(res == emax);

    z3::check_result ans = solver.check();

    if (ans == z3::unsat) {
        std::cout << " NOT tight." << std::endl;
    } else if (ans == z3::unknown) {
        std::cout << " Unknown." << std::endl;
    } else {
        std::cout << " Tight." << std::endl;
    }

    std::cout << "-------------------" << std::endl;
}


void test_mod_unsigned_bounded_fix_nonzero() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test <any> % bounded unsigned not 0 Mod fix" << std::endl;
    z3::context context;
    z3::solver solver(context);
    // need to write this manually to use bit vectors (unsigned)
    z3::expr a0 = context.bv_const("a0", 32);
    z3::expr a1 = context.bv_const("a1", 32);
    solver.add(z3::uge(a1, a0));

    z3::expr b0 = context.bv_const("b0", 32);
    z3::expr b1 = context.bv_const("b1", 32);
    solver.add(z3::uge(b1, b0));
    
    z3::expr emin = context.bv_val(0, 32);
    z3::expr emax = ite(b1 == 0, context.bv_val(0, 32), b1 - 1);
    
    max(emin, b1 - 1);

    z3::expr i = context.bv_const("i", 32);
    z3::expr j = context.bv_const("j", 32);

    // fully bounded
    solver.add(z3::uge(a0, i)); // a0 <= i
    solver.add(z3::uge(i, a1)); // i <= a1
    solver.add(z3::uge(b0, j)); // b0 <= j
    solver.add(z3::uge(j, b1)); // j <= b1

    z3::expr res = ite(j != 0, z3::urem(i, j), context.bv_val(0, 32)); // remainder

    // we just care about the upper bound tightness
    solver.add(res == emax);

    z3::check_result ans = solver.check();

    if (ans == z3::unsat) {
        std::cout << " NOT tight." << std::endl;
    } else if (ans == z3::unknown) {
        std::cout << " Unknown." << std::endl;
    } else {
        std::cout << " Tight." << std::endl;
    }

    std::cout << "-------------------" << std::endl;
}



int main(int argc, char** argv)
{
    test_mod_unsigned_bounded();
    test_mod_unsigned_bounded_fix_zero();
    test_mod_unsigned_bounded_fix_nonzero();
}