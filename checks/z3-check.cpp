#include "z3++.h"

int main(int argc, char** argv)
{
    z3::context c;
    z3::expr a = c.int_const("a");
    z3::expr b = z3::abs(a);
}