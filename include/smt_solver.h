#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H
#include "z3++.h"
#include <string>
#include <iostream>
class smt_solver {
    public:
        z3::check_result check(const std::string& filename);
};
#endif