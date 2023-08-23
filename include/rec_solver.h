#ifndef REC_SOLVER_H
#define REC_SOLVER_H
#include "z3++.h"
#include <map>

typedef std::map<z3::expr, z3::expr> rec_ty;
typedef std::map<z3::expr, z3::expr> closed_form_ty;

class rec_solver {
    private:
        z3::context& z3ctx;
        rec_ty rec_eqs;
        rec_ty res;
        z3::expr ind_var;
    public:
        rec_solver(rec_ty& rec_eqs, z3::expr var, z3::context& z3ctx);
        rec_solver(z3::context& z3ctx): z3ctx(z3ctx), ind_var(z3ctx) {}
        void set_eqs(std::map<z3::expr, z3::expr>& rec_eqs);
        void set_ind_var(z3::expr var);
        void simple_solve();
        closed_form_ty get_res() const;
        void expr_solve(z3::expr);
};
#endif