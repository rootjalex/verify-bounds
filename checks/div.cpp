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
    check_tightness(c, Operation::Div, a, b, e0, e1);
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
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_point_unbounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test point / unbounded Div" << std::endl;
    z3::context c;

    Interval *a = MakeInterval(c, "a", IntervalType::Point,
        NoRestriction, LowerBound, // lower bound
        NoRestriction, UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown,
        NoRestriction, Unbounded, // lower bound
        NoRestriction, Unbounded); // upper bound

    z3::expr a0 = a->GetLower();

    z3::expr emin = -z3_abs(a0);
    z3::expr emax = z3_abs(a0);

    Bound e0(NoRestriction, LowerBound, emin);
    Bound e1(NoRestriction, UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_bounded_unbounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded / unbounded Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::NotPoint,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();

    z3::expr emin = min(-a1, a0);
    z3::expr emax = max(-a0, a1);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_single_points() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test single points Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    z3::expr emin = halide_div(a0, b0);
    z3::expr emax = halide_div(a0, b0);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_bounded_single_pos() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded / single pos point Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        Positive, BoundType::LowerBound, // lower bound
        Positive, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr bp = b->GetLower();

    z3::expr emin = halide_div(a0, bp);
    z3::expr emax = halide_div(a1, bp);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_lower_bounded_single_pos() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test lower bounded / single pos point Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        Positive, BoundType::LowerBound, // lower bound
        Positive, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr bp = b->GetLower();

    z3::expr emin = halide_div(a0, bp);
    z3::expr emax(c); // not used

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::Unbounded, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bounded_single_pos() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test upper bounded / single pos point Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        Positive, BoundType::LowerBound, // lower bound
        Positive, BoundType::UpperBound); // upper bound

    z3::expr a1 = a->GetUpper();
    z3::expr bp = b->GetLower();

    z3::expr emin(c); // not used
    z3::expr emax = halide_div(a1, bp);

    Bound e0(NoRestriction, BoundType::Unbounded, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_bounded_single_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded / single neg point Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        Negative, BoundType::LowerBound, // lower bound
        Negative, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr bn = b->GetLower();

    z3::expr emin = halide_div(a1, bn);
    z3::expr emax = halide_div(a0, bn);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_lower_bounded_single_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test lower bounded / single neg point Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        Negative, BoundType::LowerBound, // lower bound
        Negative, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr bn = b->GetLower();

    z3::expr emin(c); // not used
    z3::expr emax = halide_div(a0, bn);

    Bound e0(NoRestriction, BoundType::Unbounded, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_upper_bounded_single_neg() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test upper bounded / single neg point Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        Negative, BoundType::LowerBound, // lower bound
        Negative, BoundType::UpperBound); // upper bound

    z3::expr a1 = a->GetUpper();
    z3::expr bn = b->GetLower();

    z3::expr emin = halide_div(a1, bn);
    z3::expr emax(c); // not used

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::Unbounded, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}


void test_bounded_single_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test bounded / single (?) point Div" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point, 
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr a1 = a->GetUpper();
    z3::expr b0 = b->GetLower();

    z3::expr emin = ite(b0 > 0, halide_div(a0, b0), halide_div(a1, b0));
    z3::expr emax = ite(b0 > 0, halide_div(a1, b0), halide_div(a0, b0));

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Div, a, b, e0, e1);
    check_tightness(c, Operation::Div, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}


int main(int argc, char** argv)
{
    test_bounded_pos_unbounded();
    test_bounded_neg_unbounded();
    test_point_unbounded();
    test_bounded_unbounded();
    // NONE complete
    // test_bounded_single_pos();
    // test_lower_bounded_single_pos();
    // test_upper_bounded_single_pos();
    // test_bounded_single_neg();
    // test_lower_bounded_single_neg();
    // test_upper_bounded_single_neg();
    // test_bounded_single_point();
}