#include "Interval.h"

z3::expr make_not(z3::expr &e) {
    return ite(
            e, // is_one(e)
            e.ctx().bool_val(false),
            ite(
                e, // is_one(e)
                e.ctx().bool_val(true),
                !e)); // base case (not statically known) (not reachable via z3)
}

void test_boolean_not() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test boolean !a" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval e("e", context, solver);

    z3::expr res = !e.inner;

    z3::expr emin = make_not(e.upper);
    z3::expr emax = make_not(e.lower);

    // binary choice
    solver.add(res != emin && res != emax);
    
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

        std::cout << "Contradiction: !";
        std::cout << model.eval(e.inner);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}

int main(void) {
    test_boolean_not();
}