#include "Interval.h"
#include "Check.h"

void test_bad_div() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bad Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::NotPoint, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown, 
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = min(-a1, a0);
    z3::expr emax = max(-a1, a0);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_bad_div_fix() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test fix to bad Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::NotPoint, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown, 
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = min(-a1, a0);
    z3::expr emax = max(-a0, a1);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv)
{
    test_bad_div();
    test_bad_div_fix();
}