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
    ~Interval() { delete upper; delete lower; }
    std::string ToString(z3::model &m);
    std::string ToStringSymbolic();
    z3::expr &GetLower();
    z3::expr &GetUpper();
};

struct Bool_Interval {
    z3::expr lower, upper;
    z3::expr inner;
    Bool_Interval(std::string name, z3::context &context, z3::solver &solver);
};

void apply_interval(z3::solver &solver, Interval *interval, z3::expr &variable);


Interval *MakeInterval(z3::context &context, std::string name, IntervalType type, 
                        Restriction lrest, BoundType ltype,
                        Restriction urest, BoundType utype);

struct ShiftParams {
    bool isUpperBounded = false;
    bool isLowerBounded = false;
    bool isUint = false;
    const z3::expr &upper;
    const z3::expr &lower;
    std::string toString(z3::model &model) {
        std::string s = (isUint) ? "u" : "";
        s += "[";
        if (isLowerBounded) {
            s += model.eval(lower).to_string();
        } else {
            s += "_";
        }
        s += ", ";
        if (isUpperBounded) {
            s += model.eval(upper).to_string();
        } else {
            s += "_";
        }
        s += "]";
        return s;
    }
};

inline void apply_shift_params(const z3::expr &i, z3::solver &solver, ShiftParams &a_params) {
    if (a_params.isUint) {
        if (a_params.isUpperBounded) {
            solver.add(z3::ule(i, a_params.upper));
        }
        if (a_params.isLowerBounded) {
            solver.add(z3::uge(i, a_params.lower));
        }
    } else {
        if (a_params.isUpperBounded) {
            solver.add(i <= a_params.upper);
        }
        if (a_params.isLowerBounded) {
            solver.add(i >= a_params.lower);
        }
    }
}