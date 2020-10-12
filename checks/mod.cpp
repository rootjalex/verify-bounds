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
    std::cout << "-------------------" << std::endl;
}

int main(int argc, char** argv)
{
    test_single_point();
}