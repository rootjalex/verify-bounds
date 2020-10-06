#include "Interval.h"
#include "Check.h"

void test_single_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test single point Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Point, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    z3::expr emin = a0 * b0;
    z3::expr emax = a0 * b0;

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_b_zero() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test b 0 a unbounded Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, Unbounded, // lower bound
        NoRestriction, Unbounded); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        IsZero, LowerBound, // lower bound
        IsZero, UpperBound); // upper bound

    z3::expr emin = c.int_val(0);
    z3::expr emax = c.int_val(0);

    Bound e0(IsZero, LowerBound, emin);
    Bound e1(IsZero, UpperBound, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_b_pos_a_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test b >= 0 a bounded Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NonNegative, LowerBound, // lower bound
        NonNegative, UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr bp = b->GetLower();

    z3::expr emin = a0 * bp;
    z3::expr emax = a1 * bp;

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}


void test_b_neg_a_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test b <= 0 a bounded Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NonPositive, LowerBound, // lower bound
        NonPositive, UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr bn = b->GetLower();

    z3::expr emin = a1 * bn;
    z3::expr emax = a0 * bn;

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_b_pos_a_upperbounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test b >= 0 a upperbounded Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, Unbounded, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NonNegative, LowerBound, // lower bound
        NonNegative, UpperBound); // upper bound

    z3::expr a1 = a->GetUpper();
    z3::expr bp = b->GetLower();

    z3::expr emin(c); // not used
    z3::expr emax = a1 * bp;

    Bound e0(NoRestriction, Unbounded, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_b_neg_a_upperbounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test b <= 0 a upperbounded Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, Unbounded, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NonPositive, LowerBound, // lower bound
        NonPositive, UpperBound); // upper bound

    z3::expr a1 = a->GetUpper();
    z3::expr bn = b->GetLower();

    z3::expr emin = a1 * bn;
    z3::expr emax(c); // not used

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, Unbounded, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_b_point_a_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test b0 == b1 a bounded Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr bp = b->GetLower();

    z3::expr emin = z3::ite(bp >= 0, a0 * bp, a1 * bp);
    z3::expr emax = z3::ite(bp >= 0, a1 * bp, a0 * bp);

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}


void test_both_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test both bounded Mul" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::NotPoint, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::NotPoint, 
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = min(min(min(a0 * b0, a0 * b1), a1 * b0), a1 * b1);
    z3::expr emax = max(max(max(a0 * b0, a0 * b1), a1 * b0), a1 * b1);

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Mul, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}


int main(int argc, char** argv)
{
    test_single_point();
    test_b_zero();
    test_b_pos_a_bounded();
    test_b_neg_a_bounded();
    test_b_pos_a_upperbounded();
    test_b_neg_a_upperbounded();
    test_b_point_a_bounded();
    test_both_bounded();
}