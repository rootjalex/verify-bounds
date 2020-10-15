#include "Interval.h"
#include "Check.h"

void test_single_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test single point Add" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Point, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = a0 + b0;
    z3::expr emax = a1 + b1;

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Add, a, b, e0, e1);
    check_tightness(c, Operation::Add, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded Add" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::NotPoint, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::NotPoint, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = a0 + b0;
    z3::expr emax = a1 + b1;

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Add, a, b, e0, e1);
    check_tightness(c, Operation::Add, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test upper bounded Add" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown, 
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin(c); // not used
    z3::expr emax = a1 + b1;

    Bound e0(NoRestriction, BoundType::Unbounded, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Add, a, b, e0, e1);
    check_tightness(c, Operation::Add, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_lower_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test lower bounded Add" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = a0 + b0;
    z3::expr emax(c); // not used

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::Unbounded, emax);

    check(c, Operation::Add, a, b, e0, e1);
    check_tightness(c, Operation::Add, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}


int main(int argc, char** argv)
{
    test_single_point();
    test_bounded();
    test_upper_bounded();
    test_lower_bounded();
}