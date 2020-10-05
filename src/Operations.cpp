#include "Operations.h"

std::string OpToString(Operation op) {
    switch (op) {
        case Operation::Add: {
            return "+";
        }
        case Operation::Sub: {
            return "-";
        }
        case Operation::Mul: {
            return "*";
        }
        case Operation::Div: {
            return "/";
        }
        default: {
            std::cerr << "Could not identify Operation in OpToString()!" << std::endl;
            return "OP";
        }
    }
}


z3::expr generate_op(z3::context &context, Operation op, z3::expr &i, z3::expr &j) {
    switch (op) {
        case Operation::Add: {
            return i + j;
        }
        case Operation::Sub: {
            return i - j;
        }
        case Operation::Mul: {
            return i * j;
        }
        case Operation::Div: {
            return halide_div(context, i, j);
        }
        default: {
            std::cerr << "Could not identify Operation in generate_op()!" << std::endl;
        }
    }
}

z3::expr halide_div(z3::context &context, z3::expr &i, z3::expr &j) {
    return ite(
                j == 0, 
                    context.int_val(0), 
                    ite(
                        j < 0,
                        (i + (i % j)) / j,
                        i / j
                    )
                );
}