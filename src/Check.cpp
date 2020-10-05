#include "Check.h"

void check(z3::context &context, Operation op, Interval *a, 
            Interval *b, Bound &e0, Bound &e1) {

    z3::expr i = context.int_const("i");
    z3::expr j = context.int_const("j");
    z3::solver solver(context);

    apply_interval(solver, a, i);
    apply_interval(solver, b, j);

    z3::expr res = generate_op(context, op, i, j);

    if (e0.type != Unbounded && e1.type != Unbounded) {
        solver.add((res < *e0.expr) || (res > *e1.expr));
    } else if (e0.type != Unbounded) {
        solver.add(res < *e0.expr);
    } else if (e1.type != Unbounded) {
        solver.add(res > *e1.expr);
    }

    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
        std::cout << "Operation: ";
        std::cout << a->ToStringSymbolic();
        std::cout << " " << OpToString(op) << " ";
        std::cout << b->ToStringSymbolic() << std::endl;
        std::cout << " = [ " << e0.ToStringSymbolic() << ", " << e1.ToStringSymbolic() << " ]" << std::endl; 
    } else {
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "Operation: ";
        std::cout << a->ToString(model);
        std::cout << " " << OpToString(op) << " ";
        std::cout << b->ToString(model) << std::endl;
        std::cout << " = [ " << e0.ToStringSymbolic(true) << ", " << e1.ToStringSymbolic(true) << " ]" << std::endl;

        std::cout << "Resultant bounds: [";
        if (e0.expr) {
            std::cout << model.eval(*e0.expr);
        } else {
            std::cout << "_";
        }
        std::cout << ", ";
        if (e1.expr) {
            std::cout << model.eval(*e1.expr);
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


// void check(z3::context &context, Operation op, Interval *a, 
//             Interval *b, z3::expr &e0, z3::expr &e1) {

//     z3::expr i = context.int_const("i");
//     z3::expr j = context.int_const("j");
//     z3::solver solver(context);

//     apply_interval(solver, a, i);
//     apply_interval(solver, b, j);

//     z3::expr res = generate_op(context, op, i, j);

//     solver.add((res < e0) || (res > e1));

//     if(solver.check() == z3::unsat) {
//         std::cout << "proved" << std::endl;
//         std::cout << "Operation: ";
//         std::cout << a->ToStringSymbolic();
//         std::cout << " " << OpToString(op) << " ";
//         std::cout << b->ToStringSymbolic() << std::endl;
//         std::cout << " = [ " << e0 << ", " << e1 << " ]" << std::endl; 
//     } else {
//         std::cout << "failed to prove" << std::endl;
//         z3::model model = solver.get_model();

//         std::cout << "Operation: ";
//         std::cout << a->ToString(model);
//         std::cout << " " << OpToString(op) << " ";
//         std::cout << b->ToString(model) << std::endl;
//         std::cout << " = [ " << e0 << ", " << e1 << " ]" << std::endl; 

//         std::cout << "Resultant bounds: [" << model.eval(e0) << ", " << model.eval(e1) << "]" << std::endl;

//         std::cout << "Contradiction: ";
//         std::cout << model.eval(i);
//         std::cout << " " << OpToString(op) << " ";
//         std::cout << model.eval(j);
//         std::cout << " = " << model.eval(res) << std::endl;
//      }
// }
