#include "Interval.h"
#include "Check.h"

#define NBITS 32

// TODO: need framework for doing bv intervals
void test_integer_or_lower_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [int] a (unknown) lower bounded & b (unknown) lower bounded" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);

    // no upper bound
    z3::expr emin = ite(a0 > b0, b0, a0); // want signed min (int)
    
    z3::expr i = context.bv_const("i", NBITS);
    z3::expr j = context.bv_const("j", NBITS);
    solver.add(a0 <= i);
    solver.add(b0 <= j);

    z3::expr res = i | j;
    
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

        std::cout << "[" << model.eval(a0);
        std::cout << ", _] ";
        std::cout << "&";
        std::cout << " [" << model.eval(b0);
        std::cout << ", _]" << std::endl;

        std::cout << "Resultant bounds: [" << model.eval(emin) << ", _]" << std::endl;

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " & ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}


void test_uninteger_or_lower_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [uint] a (unknown) lower bounded & b (unknown) lower bounded" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr b0 = context.bv_const("b0", NBITS);

    // no upper bound
    z3::expr emin = ite(z3::ugt(a0, b0), a0, b0); // want unsigned max (uint)
    
    z3::expr i = context.bv_const("i", NBITS);
    z3::expr j = context.bv_const("j", NBITS);
    solver.add(z3::uge(i, a0));
    solver.add(z3::uge(j, b0));

    z3::expr res = i | j;
    
    // if possible to be less than our min or more than our max, BAD
    solver.add(z3::ult(res, emin));
    
    z3::check_result ans = solver.check();
    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "[" << model.eval(a0);
        std::cout << ", _] ";
        std::cout << "&";
        std::cout << " [" << model.eval(b0);
        std::cout << ", _]" << std::endl;

        std::cout << "Resultant bounds: [" << model.eval(emin) << ", _]" << std::endl;

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " & ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv) {
    test_integer_or_lower_bounded();
    test_uninteger_or_lower_bounded();
}