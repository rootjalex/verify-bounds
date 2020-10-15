#include "Interval.h"
#include "Check.h"

void test_single_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test single point Max" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    z3::expr emin = max(a0, b0);
    z3::expr emax = max(a0, b0);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Max, a, b, e0, e1);
    check_tightness(c, Operation::Max, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_not_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test single point Max" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = max(a0, b0);
    z3::expr emax = max(a1, b1);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Max, a, b, e0, e1);
    check_tightness(c, Operation::Max, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv)
{
    // these should be trivially true
    test_single_point();
    test_not_point();
}
