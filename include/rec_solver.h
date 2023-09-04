#ifndef REC_SOLVER_H
#define REC_SOLVER_H
#include "z3++.h"
#include <map>
#include <set>
#include <fstream>

struct ExprCmp {
    bool operator()(const z3::expr& lhs, const z3::expr& rhs) const {
        return lhs.to_string() < rhs.to_string();
    }
};

typedef std::map<z3::expr, z3::expr, ExprCmp> rec_ty;
typedef std::map<z3::expr, z3::expr, ExprCmp> closed_form_ty;
typedef std::pair<z3::expr_vector, z3::expr_vector> initial_ty;

class rec_solver {
    private:
        z3::context& z3ctx;
        rec_ty rec_eqs;
        closed_form_ty res;
        z3::expr ind_var;
        // initial_ty initial_values;
        z3::expr_vector initial_values_k;
        z3::expr_vector initial_values_v;
        std::vector<z3::expr> conds;
        std::vector<rec_ty> exprs;
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
        void print_recs();
        void _format();
        void rec2file();
        void _rec2file(std::ofstream& out);
        std::vector<z3::expr> parse_expr(z3::expr e);
        std::vector<z3::expr> parse_cond(z3::expr);
        bool is_ite_free(z3::expr e);
        bool implies(z3::expr e1, z3::expr e2);
        std::string z3_infix(z3::expr e);
        void file2z3();
        void _file2z3(const std::string& filename);
        void print_res();
        void solve();
};
#endif