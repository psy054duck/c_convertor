#include "smt_solver.h"

z3::check_result smt_solver::check(const std::string& filename, double timeout) {
    int ret_code = system(("python z3reader.py " + filename + " " + std::to_string(timeout)).c_str());
    z3::check_result res = z3::unknown;
    switch (ret_code) {
        case -1: res = z3::sat;     break;
        case 0 : res = z3::unsat;   break;
        default: res = z3::unknown; break;
    }
    return res;
}