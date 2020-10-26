#include "Interval.h"
#include "Check.h"

#define NBITS 32

// TODO: need framework for doing bv intervals
void test_not_upper_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test ~a (unknown) upper bounded" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a1 = context.bv_const("a1", NBITS);

    // no upper bound
    z3::expr emin = ~a1;
    
    z3::expr i = context.bv_const("i", NBITS);
    solver.add(i <= a1);

    z3::expr res = ~i;
    
    // if possible to be less than our min or more than our max, BAD
    solver.add(res < emin);
    
    z3::check_result ans = solver.check();
    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "! [_, " << model.eval(a1);
        std::cout << "]" << std::endl;

        std::cout << "Resultant bounds: [" << model.eval(emin) << ", _]" << std::endl;

        std::cout << "Contradiction: ~";
        std::cout << model.eval(i);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}

void test_not_lower_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test ~a (unknown) lower bounded" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);

    // no lower bound
    z3::expr emax = ~a0;
    
    z3::expr i = context.bv_const("i", NBITS);
    solver.add(i >= a0);

    z3::expr res = ~i;
    
    // if possible to be less than our min or more than our max, BAD
    solver.add(res > emax);
    
    z3::check_result ans = solver.check();
    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "! [" << model.eval(a0);
        std::cout << ", _]" << std::endl;

        std::cout << "Resultant bounds: [_, " << model.eval(emax) << "]" << std::endl;

        std::cout << "Contradiction: ~";
        std::cout << model.eval(i);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv) {
    test_not_upper_bounded();
    test_not_lower_bounded();
}