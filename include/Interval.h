#pragma once

#include "Bound.h"
#include "z3++.h"
#include <string>

enum IntervalType {
    Unknown = 0,
    Point,
    NotPoint
};


struct Interval {
    Bound *upper, *lower;
    IntervalType type;
    Interval(IntervalType _type, Bound *_lower, Bound *_upper)
        : type(_type), lower(_lower), upper(_upper) {}
    Interval() : upper(nullptr), lower(nullptr) {}
    std::string ToString(z3::model &m);
    std::string ToStringSymbolic();
    z3::expr GetLower();
    z3::expr GetUpper();
};


void apply_interval(z3::solver &solver, Interval *interval, z3::expr &variable);


Interval *MakeInterval(z3::context &context, std::string name, IntervalType type, 
                        Restriction lrest, BoundType ltype,
                        Restriction urest, BoundType utype);