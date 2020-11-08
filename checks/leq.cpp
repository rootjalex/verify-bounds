#include "z3++.h"
#include <string>

#include "Interval.h"
#include "Equality.h"

struct LeqPredicate {
    z3::expr equality(z3::expr &i, z3::expr &j) {
        return i <= j;
    }
    std::string str = "<=";
};

static LeqPredicate GlobalLeqPred;


void test_leq_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded <= bounded" << std::endl;

    z3::context context;
    z3::solver solver(context);

    Interval *a = MakeInterval(context, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    /*
    interval.min = Cmp::make(a.max, b.min);
    interval.max = Cmp::make(a.min, b.max);
    */
    z3::expr emin = a1 <= b0;
    z3::expr emax = a0 <= b1;

    check_equality_type(a, b, solver, context, emin, emax, GlobalLeqPred);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bound_leq_lower_bound() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [_, a1] <= [b0, _]" << std::endl;

    z3::context context;
    z3::solver solver(context);

    Interval *a = MakeInterval(context, "a", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();

    /*
    interval.min = Cmp::make(a.max, b.min);
    */
    z3::expr emin = a1 <= b0;
    z3::expr emax = context.bool_val(true);

    check_equality_type(a, b, solver, context, emin, emax, GlobalLeqPred);
    std::cout << "-------------------" << std::endl;
}

void test_lower_bound_leq_upper_bound() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test [a0, _] <= [_, b1]" << std::endl;

    z3::context context;
    z3::solver solver(context);

    Interval *a = MakeInterval(context, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);

    Interval *b = MakeInterval(context, "b", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a0 = a->GetLower();
    z3::expr b1 = b->GetUpper();

    /*
    interval.max = Cmp::make(a.min, b.max);
    */
    z3::expr emin = context.bool_val(false);
    z3::expr emax = a0 <= b1;

    check_equality_type(a, b, solver, context, emin, emax, GlobalLeqPred);
    std::cout << "-------------------" << std::endl;
}

int main(void) {
    test_leq_bounded();
    test_upper_bound_leq_lower_bound();
    test_lower_bound_leq_upper_bound();
}