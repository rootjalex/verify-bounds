#pragma once

#include "z3++.h"
#include "Interval.h"

template<typename BinaryPredicate>
void check_equality_type(Interval *a, Interval *b,
                z3::solver &solver, z3::context &context,
                z3::expr &emin, z3::expr &emax,
                BinaryPredicate &pred) {
    z3::expr i = context.int_const("i");
    z3::expr j = context.int_const("j");
    apply_interval(solver, a, i);
    apply_interval(solver, b, j);

    z3::expr res = pred.equality(i, j);

    // we want res to be neither of them (this would prove the rule false)
    solver.add(res != emin && res != emax);
    
    z3::check_result ans = solver.check();
    if(ans == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (ans == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "[" << model.eval(a->GetLower()) << ", " << model.eval(a->GetUpper()) << "]" << std::endl;
        std::cout << "[" << model.eval(b->GetLower()) << ", " << model.eval(b->GetUpper()) << "]" << std::endl;

        std::cout << "Resultant bounds: [";
        std::cout << model.eval(emin) << ", " << model.eval(emax);
        std::cout << "]" << std::endl;

        std::cout << "Contradiction: ";
        std::cout << model.eval(i) << pred.str << model.eval(j) << " is " << model.eval(res) << std::endl;
    }
    delete a;
    delete b;
}

template<typename BinaryPredicate>
void check_equality_case(Interval *a, Interval *b,
                z3::solver &solver, z3::context &context,
                z3::expr &emin, z3::expr &emax,
                BinaryPredicate &pred) {
    z3::expr i = context.int_const("i");
    z3::expr j = context.int_const("j");
    apply_interval(solver, a, i);
    apply_interval(solver, b, j);

    // z3::expr res = pred.equality(i, j);

    // we want res to be neither of them (this would prove the rule false)
    solver.add(emin && !emax);
    
    z3::check_result ans = solver.check();
    if(ans == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (ans == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "[" << model.eval(a->GetLower()) << ", " << model.eval(a->GetUpper()) << "]" << std::endl;
        std::cout << "[" << model.eval(b->GetLower()) << ", " << model.eval(b->GetUpper()) << "]" << std::endl;

        std::cout << "Resultant bounds: [";
        std::cout << model.eval(emin) << ", " << model.eval(emax);
        std::cout << "]" << std::endl;

        // std::cout << "Contradiction: ";
        // std::cout << model.eval(i) << pred.str << model.eval(j) << " is " << model.eval(res) << std::endl;
    }
}
