#pragma once

#include "z3++.h"
#include <string>

enum BoundType {
    Unbounded = 0,
    UpperBound,
    LowerBound
};

enum Restriction {
    NoRestriction = 0,
    IsZero,
    NonPositive,
    NonNegative,
};

struct Bound {
    Restriction restriction;
    BoundType type;
    z3::expr *expr;
    Bound(Restriction _restriction, BoundType _type, z3::expr *_expr)
        : restriction(_restriction), type(_type), expr(_expr) {}
    std::string ToString(z3::model &m);
    std::string ToStringSymbolic(bool print=false);
};


void apply_bound(z3::solver &solver, z3::expr &variable, Bound *bound);

void apply_restriction(z3::solver &solver, Bound *bound);