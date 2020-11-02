#include "Interval.h"

void check_select(Bool_Interval cond, Interval *a, Interval *b, z3::solver &solver, z3::context &context, z3::expr &bound, bool isMin) {
    z3::expr i = context.int_const("i");
    z3::expr j = context.int_const("j");
    apply_interval(solver, a, i);
    apply_interval(solver, b, j);

    z3::expr res = ite(cond.inner, i, j);

    if (isMin) {
        solver.add(res < bound);
    } else {
        solver.add(res > bound);
    }

    z3::check_result ans = solver.check();
    if(solver.check() == z3::unsat) {
        std::cout << "proved" << std::endl;
    } else if (solver.check() == z3::unknown) {
        std::cout << "ERROR: z3 unable to prove or disprove" << std::endl;
    } else { // sat
        std::cout << "failed to prove" << std::endl;
        z3::model model = solver.get_model();

        std::cout << "Resultant bounds: [";
        if (isMin) {
            std::cout << model.eval(bound) << ", _";
        } else {
            std::cout << "_, " << model.eval(bound);
        }
        std::cout << "]" << std::endl;

        std::cout << "Contradiction: select(";
        std::cout << model.eval(cond.inner) << ", ";
        std::cout << model.eval(i) << ", ";
        std::cout << model.eval(j) << ")";
        std::cout << " = " << model.eval(res) << std::endl;
    }
    std::cout << "-------------------" << std::endl;
    delete a;
    delete b;
}

void test_select_min_lower_equal() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's min a.min.same_as(b.min)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    // a.min.same_as(b.min)
    solver.add(a0 == b0);

    z3::expr emin = a0;
    
    check_select(cond, a, b, solver, context, emin, true);
}

void test_select_min_cond_single_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's min cond.is_single_point()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    // cond.is_single_point()
    solver.add(cond.lower == cond.upper);

    /*
    interval.min = select(cond.min, a.min, b.min);
    */
    z3::expr emin = ite(cond.lower, a0, b0);
    
    check_select(cond, a, b, solver, context, emin, true);
}

void test_select_min_cond_known_all() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's min is_zero(cond.min) && is_one(cond.max)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    // is_zero(cond.min) && is_one(cond.max)
    solver.add(!cond.lower && cond.upper);

    // interval.min = Interval::make_min(a.min, b.min);
    z3::expr emin = ite(a0 < b0, a0, b0);
    
    check_select(cond, a, b, solver, context, emin, true);
}

void test_select_min_cond_upper_true() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's min is_one(cond.max)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    // is_one(cond.max)
    solver.add(cond.upper);

    /*
    string var_name = unique_name('t');
    Expr var = Variable::make(t, var_name);
    interval.min = Interval::make_min(select(cond.min, var, b.min), var);
    interval.min = Let::make(var_name, a.min, interval.min);
    */
    z3::expr temp = ite(cond.lower, a0, b0);
    z3::expr emin = ite(temp < a0, temp, a0);
    
    check_select(cond, a, b, solver, context, emin, true);
}

void test_select_min_cond_lower_false() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's min is_zero(cond.min)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    // is_zero(cond.min)
    solver.add(!cond.lower);

    /*
    string var_name = unique_name('t');
    Expr var = Variable::make(t, var_name);
    interval.min = Interval::make_min(select(cond.max, a.min, var), var);
    interval.min = Let::make(var_name, b.min, interval.min);
    */
    z3::expr temp = ite(cond.upper, a0, b0);
    z3::expr emin = ite(temp < b0, temp, b0);
    
    check_select(cond, a, b, solver, context, emin, true);
}

void test_select_min_cond_unknown() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's min else{}" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::LowerBound,
        NoRestriction, BoundType::Unbounded);
    
    z3::expr a0 = a->GetLower();
    z3::expr b0 = b->GetLower();

    /*
    string a_var_name = unique_name('t'), b_var_name = unique_name('t');
    Expr a_var = Variable::make(t, a_var_name);
    Expr b_var = Variable::make(t, b_var_name);
    interval.min = Interval::make_min(select(cond.min, a_var, b_var),
                                        select(cond.max, a_var, b_var));
    interval.min = Let::make(a_var_name, a.min, interval.min);
    interval.min = Let::make(b_var_name, b.min, interval.min);
    */
    z3::expr op_max = ite(cond.upper, a0, b0);
    z3::expr op_min = ite(cond.lower, a0, b0);
    z3::expr emin = ite(op_min < op_max, op_min, op_max);
    
    check_select(cond, a, b, solver, context, emin, true);
}

void test_select_max_upper_equal() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's max a.max.same_as(b.max)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    // a.max.same_as(b.max)
    solver.add(a1 == b1);

    /*
    interval.max = a.max;
    */
    z3::expr emax = a1;
    
    check_select(cond, a, b, solver, context, emax, false);
}

void test_select_max_cond_single_point() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's max cond.is_single_point()" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    // cond.is_single_point()
    solver.add(cond.lower == cond.upper);

    /*
    interval.max = select(cond.min, a.max, b.max);
    */
    z3::expr emax = ite(cond.lower, a1, b1);
    
    check_select(cond, a, b, solver, context, emax, false);
}

void test_select_max_cond_known_all() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's max is_zero(cond.min) && is_one(cond.max)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    // is_zero(cond.min) && is_one(cond.max)
    solver.add(!cond.lower && cond.upper);

    /*
    interval.max = Interval::make_max(a.max, b.max);
    */
    z3::expr emax = ite(a1 > b1, a1, b1);
    
    check_select(cond, a, b, solver, context, emax, false);
}

void test_select_max_cond_upper_true() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's max is_one(cond.max)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    // is_one(cond.max)
    solver.add(cond.upper);

    /*
    string var_name = unique_name('t');
    Expr var = Variable::make(t, var_name);
    interval.max = Interval::make_max(select(cond.min, var, b.max), var);
    interval.max = Let::make(var_name, a.max, interval.max);
    */
    z3::expr temp = ite(cond.lower, a1, b1);
    z3::expr emax = ite(temp > a1, temp, a1);
    
    check_select(cond, a, b, solver, context, emax, false);
}

void test_select_max_cond_lower_false() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's max is_zero(cond.min)" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    // is_zero(cond.min)
    solver.add(!cond.lower);

    /*
    string var_name = unique_name('t');
    Expr var = Variable::make(t, var_name);
    interval.max = Interval::make_max(select(cond.max, a.max, var), var);
    interval.max = Let::make(var_name, b.max, interval.max);
    */
    z3::expr temp = ite(cond.upper, a1, b1);
    z3::expr emax = ite(temp > b1, temp, b1);
    
    check_select(cond, a, b, solver, context, emax, false);
}

void test_select_max_cond_unknown() {
    std::cout << "-------------------" << std::endl;
    std::cout << "Test select's max else{}" << std::endl;
    
    z3::context context;
    z3::solver solver(context);

    Bool_Interval cond("cond", context, solver);
    Interval *a = MakeInterval(context, "a", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);

    Interval *b = MakeInterval(context, "b", IntervalType::Point,
        NoRestriction, BoundType::Unbounded,
        NoRestriction, BoundType::UpperBound);
    
    z3::expr a1 = a->GetUpper();
    z3::expr b1 = b->GetUpper();

    /*
    string a_var_name = unique_name('t'), b_var_name = unique_name('t');
    Expr a_var = Variable::make(t, a_var_name);
    Expr b_var = Variable::make(t, b_var_name);
    interval.max = Interval::make_max(select(cond.min, a_var, b_var),
                                        select(cond.max, a_var, b_var));
    interval.max = Let::make(a_var_name, a.max, interval.max);
    interval.max = Let::make(b_var_name, b.max, interval.max);
    */
    z3::expr op_max = ite(cond.upper, a1, b1);
    z3::expr op_min = ite(cond.lower, a1, b1);
    z3::expr emax = ite(op_min > op_max, op_min, op_max);
    
    check_select(cond, a, b, solver, context, emax, false);
}

int main(void) {
    test_select_min_lower_equal();
    test_select_min_cond_single_point();
    test_select_min_cond_known_all();
    test_select_min_cond_upper_true();
    test_select_min_cond_lower_false();
    test_select_min_cond_unknown();
    test_select_max_upper_equal();
    test_select_max_cond_single_point();
    test_select_max_cond_known_all();
    test_select_max_cond_upper_true();
    test_select_max_cond_lower_false();
    test_select_max_cond_unknown();
}