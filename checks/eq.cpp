#include "z3++.h"
#include <string>

#include "Interval.h"
#include "Equality.h"

struct EqPredicate {
    z3::expr equality(z3::expr &i, z3::expr &j) {
        return i == j;
    }
    std::string str = "==";
};

static EqPredicate GlobalEqPred;


void test_eq_trivial() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test trivial eq bound" << std::endl;

    z3::context context;
    z3::solver solver(context);

    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    z3::expr emin = (a0 == b0);
    z3::expr emax = (a0 == b0);

    check_equality_type(a, b, solver, context, emin, emax, GlobalEqPred);
    std::cout << "-------------------" << std::endl;
}

void test_eq_non_trivial() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test non-trivial bounded eq" << std::endl;

    z3::context context;
    z3::solver solver(context);

    Interval *a = MakeInterval(context, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = context.bool_val(false);
    // interval.max = a.min <= b.max && b.min <= a.max;
    z3::expr emax = (a0 <= b1 && b0 <= a1);

    check_equality_type(a, b, solver, context, emin, emax, GlobalEqPred);
    std::cout << "-------------------" << std::endl;
}

void test_eq_new() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test neg =?= pos" << std::endl;

    z3::context context;
    z3::solver solver(context);

    Interval *a = MakeInterval(context, "a", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded,
        Negative, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Unknown,
        Positive, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = context.bool_val(false);
    z3::expr emax = context.bool_val(false);

    check_equality_type(a, b, solver, context, emin, emax, GlobalEqPred);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bounded_eq_lower_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] == [b0, _]" << std::endl;

    z3::context context;
    z3::solver solver(context);

    Interval *a = MakeInterval(context, "a", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr b0 = b->GetLower();
    z3::expr a1 = a->GetUpper();

    z3::expr emin = context.bool_val(false);
    // interval.max = (a.max >= b.min);
    z3::expr emax = (a1 >= b0);

    check_equality_type(a, b, solver, context, emin, emax, GlobalEqPred);
    std::cout << "-------------------" << std::endl;
}


int main(void) {
    test_eq_trivial();
    test_eq_non_trivial();
    test_eq_new();
    test_upper_bounded_eq_lower_bounded();
}