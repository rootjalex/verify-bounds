#include "Interval.h"
#include "Check.h"

void test_single_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test single point Mod" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    z3::expr emin = halide_mod(a0, b0);
    z3::expr emax = halide_mod(a0, b0);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Mod, a, b, e0, e1);
    check_tightness(c, Operation::Mod, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_pos_lower_mod_unbounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test pos lower bounded % unbounded Mod" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NonNegative, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown,
        NoRestriction, BoundType::Unbounded, // lower bound
        NoRestriction, BoundType::Unbounded); // upper bound

    z3::expr a1 = a->GetUpper();

    z3::expr emin = c.int_val(0);
    z3::expr emax = a1; // can't make bigger

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Mod, a, b, e0, e1);
    check_tightness(c, Operation::Mod, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_mod_pos_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test <any> % pos bounded Mod" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown,
        Positive, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr b1 = b->GetUpper();

    z3::expr emin = c.int_val(0);
    z3::expr emax = b1 - 1;

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Mod, a, b, e0, e1);
    check_tightness(c, Operation::Mod, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

void test_mod_bounded() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test <any> % bounded Mod" << std::endl;
    z3::context c;
    Interval *a = MakeInterval(c, "a", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    Interval *b = MakeInterval(c, "b", IntervalType::Unknown,
        NoRestriction, BoundType::LowerBound, // lower bound
        NoRestriction, BoundType::UpperBound); // upper bound

    z3::expr b0 = b->GetLower();
    z3::expr b1 = b->GetUpper();

    z3::expr emin = c.int_val(0);
    z3::expr emax = max(max(c.int_val(0), b1 - 1), -1 - b0);

    Bound e0(NoRestriction, BoundType::LowerBound, emin);
    Bound e1(NoRestriction, BoundType::UpperBound, emax);

    check(c, Operation::Mod, a, b, e0, e1);
    check_tightness(c, Operation::Mod, a, b, e0, e1);
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv)
{
    test_single_point();
    test_pos_lower_mod_unbounded();
    test_mod_pos_bounded();
    test_mod_bounded();
}
