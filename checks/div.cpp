#include "Interval.h"
#include "Check.h"

void test_bounded_pos_unbounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded positive / unbounded Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NonNegative, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown, 
        NoRestriction, Unbounded, // lower bound
        NoRestriction, Unbounded); // upper bound

    z3::expr a1 = a->GetUpper();

    z3::expr emin = -a1;
    z3::expr emax = a1;

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_bounded_neg_unbounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded negative / unbounded Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, LowerBound, // lower bound
        NonPositive, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown, 
        NoRestriction, Unbounded, // lower bound
        NoRestriction, Unbounded); // upper bound

    z3::expr a0 = a->GetLower();

    z3::expr emin = a0;
    z3::expr emax = -a0;

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv)
{
    test_bounded_pos_unbounded();
    test_bounded_neg_unbounded();
}