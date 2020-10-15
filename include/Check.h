#pragma once

#include "z3++.h"
#include <string>
#include <iostream>
#include "Bound.h"
#include "Interval.h"
#include "Operations.h"


void check(z3::context &context, Operation op, Interval *a, 
            Interval *b, Bound &e0, Bound &e1);

// will deallocate a and b
void check_tightness(z3::context &context, Operation op, Interval *a, 
            Interval *b, Bound &e0, Bound &e1);

// void check(z3::context &context, Operation op, Interval *a, 
//             Interval *b, z3::expr &e0, z3::expr &e1);