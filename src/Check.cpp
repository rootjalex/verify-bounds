#include "Check.h"

void check(z3::context &context, Operation op, Interval *a, 
            Interval *b, Bound &e0, Bound &e1) {

    z3::expr i = context.int_const("i");
    z3::expr j = context.int_const("j");
    z3::solver solver(context);

    apply_interval(solver, a, i);
    apply_interval(solver, b, j);

    z3::expr res = generate_op(op, i, j);

    if (e0.type != Unbounded && e1.type != Unbounded) {
        solver.add((res < e0.expr) || (res > e1.expr));
    } else if (e0.type != Unbounded) {
        solver.add(res < e0.expr);
    } else if (e1.type != Unbounded) {
        solver.add(res > e1.expr);
    }

    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
        std::cout << "Operation: ";
        std::cout << a->ToStringSymbolic();
        std::cout << " " << OpToString(op) << " ";
        std::cout << b->ToStringSymbolic() << std::endl;
        std::cout << " = [ " << e0.ToStringSymbolic() << ", " << e1.ToStringSymbolic() << " ]" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
        std::cout << "Operation: ";
        std::cout << a->ToStringSymbolic();
        std::cout << " " << OpToString(op) << " ";
        std::cout << b->ToStringSymbolic() << std::endl;
        std::cout << " = [ " << e0.ToStringSymbolic() << ", " << e1.ToStringSymbolic() << " ]" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "Operation: ";
        std::cout << a->ToString(model);
        std::cout << " " << OpToString(op) << " ";
        std::cout << b->ToString(model) << std::endl;
        std::cout << " = [ " << e0.ToStringSymbolic(true) << ", " << e1.ToStringSymbolic(true) << " ]" << std::endl;

        std::cout << "Resultant bounds: [";
        if (e0.expr) {
            std::cout << model.eval(e0.expr);
        } else {
            std::cout << "_";
        }
        std::cout << ", ";
        if (e1.expr) {
            std::cout << model.eval(e1.expr);
        } else {
            std::cout << "_";
        }
        std::cout << "]" << std::endl;

        std::cout << "Contradiction: ";
        std::cout << model.eval(i);
        std::cout << " " << OpToString(op) << " ";
        std::cout << model.eval(j);
        std::cout << " = " << model.eval(res) << std::endl;
    }
}

z3::check_result check_bound(z3::context &context, Operation op, Interval *a, 
            Interval *b, Bound &bound) {

    z3::expr i = context.int_const("i");
    z3::expr j = context.int_const("j");
    z3::solver solver(context);

    apply_interval(solver, a, i);
    apply_interval(solver, b, j);

    z3::expr res = generate_op(op, i, j);

    solver.add(res == bound.expr);

    z3::check_result ans = solver.check();
    return ans;
}

void print_tightness(z3::context &context, Operation op, Interval *a, 
            Interval *b, Bound &bound) {

    z3::check_result res = check_bound(context, op, a, b, bound);
    if (res == z3::unsat) {
        std::cout << " NOT tight." << std::endl;
    } else if (res == z3::unknown) {
        std::cout << " Unknown." << std::endl;
    } else {
        std::cout << " Tight." << std::endl;
    }
}



void check_tightness(z3::context &context, Operation op, Interval *a, 
            Interval *b, Bound &e0, Bound &e1)  {
    
    if (e0.type != Unbounded) {
        std::cout << "Checking lower bound tightness...";
        print_tightness(context, op, a, b, e0);
    }

    if (e1.type != Unbounded) {
        std::cout << "Checking upper bound tightness...";
        print_tightness(context, op, a, b, e1);
    }

    delete a;
    delete b;
}
