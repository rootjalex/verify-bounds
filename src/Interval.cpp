#include "Interval.h"

z3::expr &Interval::GetLower() {
    return lower->expr;
}

z3::expr &Interval::GetUpper() {
    return upper->expr;
}

std::string Interval::ToString(z3::model &m) {
    std::string str = "[ " + lower->ToString(m) + ", " + upper->ToString(m);
    
    if (type == Point) {
        str += (", (" + lower->ToString(m) + "==" + upper->ToString(m) + ") ");
    } else if (type == NotPoint) {
        str += (", (" + lower->ToString(m) + "<" + upper->ToString(m) + ") ");
    }

    str += " ]";
    return str;
}

std::string Interval::ToStringSymbolic() {
    std::string str = "[ " + lower->ToStringSymbolic() + ", " + upper->ToStringSymbolic();

    if (type == Point) {
        str += (", ((" + lower->ToStringSymbolic() + ")==(" + upper->ToStringSymbolic() + ")) ");
    } else if (type == NotPoint) {
        str += (", ((" + lower->ToStringSymbolic() + ")<" + upper->ToStringSymbolic() + ")) ");
    }

    str += " ]";
    return str;
}

void apply_interval(z3::solver &solver, Interval *interval, z3::expr &variable) {
    apply_restriction(solver, interval->upper);
    apply_restriction(solver, interval->lower);
    apply_bound(solver, variable, interval->upper);
    apply_bound(solver, variable, interval->lower);

    // definition of interval
    solver.add(interval->lower->expr <= interval->upper->expr);

    switch(interval->type) {
        case IntervalType::Unknown: {
            return;
        }
        case IntervalType::Point: {
            solver.add(interval->lower->expr == interval->upper->expr);
            return;
        }
        case IntervalType::NotPoint: {
            solver.add(interval->lower->expr < interval->upper->expr);
            return;
        }
        default: {
            std::cerr << "Could not identify interval type in apply_interval()!" << std::endl;
        }
    }
}

Interval *MakeInterval(z3::context &context, std::string name, IntervalType type, 
                        Restriction lrest, BoundType ltype,
                        Restriction urest, BoundType utype) {

    Interval *interval = new Interval();

    std::string lname = name + "0";
    std::string uname = name + "1";
    
    z3::expr lower = context.int_const(lname.c_str());

    z3::expr upper = context.int_const(uname.c_str());
    
    interval->lower = new Bound(lrest, ltype, lower);
    interval->upper = new Bound(urest, utype, upper);
    interval->type = type;
    return interval;
}


Bool_Interval::Bool_Interval(std::string name, z3::context &context, z3::solver &solver)
    : lower(context.bool_const((name + "0").c_str())), upper(context.bool_const((name + "1").c_str())), inner(context.bool_const(name.c_str())) {

    // if lower is true then upper is true
    solver.add(ite(lower, upper, context.bool_val(true)));
    // if upper is false then lower is false
    solver.add(ite(!upper, !lower, context.bool_val(true)));

    // can be at most upper and at least lower
    solver.add(inner == upper || inner == lower);
}
