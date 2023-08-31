#ifndef REC_SOLVER_H
#define REC_SOLVER_H
#include "z3++.h"
#include <map>
#include <set>

typedef std::map<z3::expr, z3::expr> rec_ty;
typedef std::map<z3::expr, z3::expr> closed_form_ty;
typedef std::pair<z3::expr_vector, z3::expr_vector> initial_ty;

class rec_solver {
    private:
        z3::context& z3ctx;
        rec_ty rec_eqs;
        rec_ty res;
        z3::expr ind_var;
        // initial_ty initial_values;
        z3::expr_vector initial_values_k;
        z3::expr_vector initial_values_v;
    public:
        rec_solver(rec_ty& rec_eqs, z3::expr var, z3::context& z3ctx);
        rec_solver(z3::context& z3ctx): z3ctx(z3ctx), ind_var(z3ctx.int_const("n0")), initial_values_k(z3ctx), initial_values_v(z3ctx) {}
        void set_eqs(rec_ty& rec_eqs);
        void add_initial_values(z3::expr_vector k, z3::expr_vector v);
        void set_ind_var(z3::expr var);
        void simple_solve();
        closed_form_ty get_res();
        void expr_solve(z3::expr);
        void apply_initial_values();
};
#endif