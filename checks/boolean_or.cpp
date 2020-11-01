#include "Interval.h"

z3::expr make_or(z3::expr &a, z3::expr &b) {
    return ite(
            a, // is_one(a)
            a,
            ite(
                b, // is_one(b)
                b,
                ite(
                    !a, // is_zero(a)
                    b,
                    ite(
                        !b, // is_zero(b)
                        a,
                        a || b)))); // base case (not statically known) (not reachable via z3)
}

void test_boolean_or() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test boolean a || b" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval a("a", context, solver);
    Bool_Interval b("b", context, solver);

    z3::expr res = a.inner || b.inner;

    z3::expr emin = make_or(a.lower, b.lower);
    z3::expr emax = make_or(a.upper, b.upper);

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

        std::cout << "Contradiction: ";
        std::cout << model.eval(a.inner);
        std::cout << " && ";
        std::cout << model.eval(b.inner);
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
}

int main(void) {
    test_boolean_or();
}