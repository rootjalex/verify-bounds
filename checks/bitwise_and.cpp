#include "Interval.h"
#include "Check.h"

#define NBITS 32

// TODO: need framework for doing bv intervals
void test_unknown_and_pos_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test a (unknown) bounded & b (>= 0) bounded" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(a1 >= a0);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(b0 >= 0);
    solver.add(b1 >= b0);

    z3::expr emin = context.bv_val(0, NBITS);      // lower bound
    z3::expr emax = b1;               // upper bound

    z3::expr i = context.bv_const("i", NBITS);
    z3::expr j = context.bv_const("j", NBITS);
    solver.add(a0 <= i && i <= a1); // a0 <= i <= a1
    solver.add(b0 <= j && j <= b1); // b0 <= j <= b1

    z3::expr res = i & j;
    
    // if possible to be less than our min or more than our max, BAD
    solver.add(res < emin || res > emax);
    
    z3::check_result ans = solver.check();
    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "Resultant bounds: [" << model.eval(emin);
        std::cout << ", " << model.eval(emax) << "]";

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " & ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}

void test_pos_and_pos_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test a (>= 0) bounded & b (>= 0) bounded" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(a0 >= 0);
    solver.add(a1 >= a0);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(b0 >= 0);
    solver.add(b1 >= b0);

    z3::expr emin = context.bv_val(0, NBITS);       // lower bound
    z3::expr emax = min(a1, b1);                    // upper bound

    z3::expr i = context.bv_const("i", NBITS);
    z3::expr j = context.bv_const("j", NBITS);
    solver.add(a0 <= i && i <= a1); // a0 <= i <= a1
    solver.add(b0 <= j && j <= b1); // b0 <= j <= b1

    z3::expr res = i & j;
    
    // if possible to be less than our min or more than our max, BAD
    solver.add(res < emin || res > emax);
    
    z3::check_result ans = solver.check();
    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "Resultant bounds: [" << model.eval(emin);
        std::cout << ", " << model.eval(emax) << "]";

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " & ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}


void test_unknown_and_unknown_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [int] a (unknown) bounded & b (unknown) bounded" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    z3::expr a0 = context.bv_const("a0", NBITS);
    z3::expr a1 = context.bv_const("a1", NBITS);
    solver.add(a1 >= a0);
    z3::expr b0 = context.bv_const("b0", NBITS);
    z3::expr b1 = context.bv_const("b1", NBITS);
    solver.add(b1 >= b0);

    // no lower bound
    z3::expr emax = ite(a1 > b1, a1, b1); // want signed max (int)
    
    z3::expr i = context.bv_const("i", NBITS);
    z3::expr j = context.bv_const("j", NBITS);
    solver.add(a0 <= i && i <= a1); // a0 <= i <= a1
    solver.add(b0 <= j && j <= b1); // b0 <= j <= b1

    z3::expr res = i & j;
    
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

        std::cout << "[" << model.eval(a0);
        std::cout << ", " << model.eval(a1) << "] ";
        std::cout << "&";
        std::cout << " [" << model.eval(b0);
        std::cout << ", " << model.eval(b1) << "]" << std::endl;

        std::cout << "Resultant bounds: [_, " << model.eval(emax) << "]" << std::endl;

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " & ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}


int main(int argc, char** argv) {
    test_unknown_and_pos_bounded();
    test_pos_and_pos_bounded();
    test_unknown_and_unknown_bounded();
}