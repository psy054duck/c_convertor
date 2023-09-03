#include "rec_solver.h"
#include <iostream>
#include <numeric>

static void combine_vec(z3::expr_vector& vec1, const z3::expr_vector& vec2) {
    for (z3::expr e : vec2) {
        vec1.push_back(e);
    }
}

bool is_simple_rec(z3::func_decl func_decl, z3::expr rhs) {
    if (rhs.is_numeral() || rhs.is_const()) return true;

    auto args = rhs.args();
    auto kind = rhs.decl().decl_kind();
    bool is_all_simple_rec = true;
    for (auto e : args) {
        if (!is_simple_rec(func_decl, e)) {
            is_all_simple_rec = false;
            break;
        }
    }
    if (kind == Z3_OP_ADD || kind == Z3_OP_MUL || kind == Z3_OP_SUB) {
        return is_all_simple_rec;
        // return std::all_of(args.begin(), args.end(), [func_decl](z3::expr e) { return is_simple_rec(func_decl, e); });
    } else {
        return func_decl.id() == rhs.decl().id() && is_all_simple_rec;
        // return func_decl.id() == rhs.decl().id() && std::all_of(args.begin(), args.end(), [func_decl](z3::expr e) { return is_simple_rec(func_decl, e); });
    }
    return true;
}

void rec_solver::set_ind_var(z3::expr var) {
    ind_var = var;
}

z3::expr_vector find_all_app_of_decl(z3::func_decl func, z3::expr e, z3::context& z3ctx) {
    z3::expr_vector res(z3ctx);
    auto args = e.args();
    auto kind = e.decl().decl_kind();
    if (kind == Z3_OP_ADD || kind == Z3_OP_MUL || kind == Z3_OP_SUB) {
        for (auto arg : args) {
            combine_vec(res, find_all_app_of_decl(func, arg, z3ctx));
        }
    } else if (func.id() == e.decl().id()) {
        res.push_back(e);
    }
    return res;
}

z3::expr coeff_of(z3::expr e, z3::expr term, z3::context& z3ctx) {
    auto kind = e.decl().decl_kind();
    auto args = e.args();
    z3::expr res = z3ctx.int_val(0);
    if (kind == Z3_OP_ADD) {
        for (auto arg : args) {
            res = res + coeff_of(arg, term, z3ctx);
        }
    } else if (kind == Z3_OP_SUB) {
        assert(args.size() == 2);
        res = coeff_of(args[0], term, z3ctx) - coeff_of(args[1], term, z3ctx);
    } else if (kind == Z3_OP_MUL) {
        int i = 0;
        for (i = 0; i < args.size(); i++) {
            if ((args[i] == term).simplify().is_true()) break;
        }
        if (i != args.size()) {
            res = z3ctx.int_val(1);
            for (int j = 0; j < args.size(); j++) {
                if (j == i) continue;
                res = res * args[j];
            }
        }
    } else if ((e == term).simplify().is_true()) {
        res = z3ctx.int_val(1);
    }
    return res.simplify();
}

bool is_one_stride_simple_rec(z3::expr lhs, z3::expr rhs) {
    assert(lhs.decl().arity() == 1);
    z3::expr lhs_arg = lhs.arg(0);
}

rec_solver::rec_solver(rec_ty& eqs, z3::expr var, z3::context& z3ctx): z3ctx(z3ctx), ind_var(z3ctx), initial_values_k(z3ctx), initial_values_v(z3ctx) {
    set_eqs(eqs);
    set_ind_var(var);
}

void rec_solver::set_eqs(rec_ty& eqs) {
    for (auto r : eqs) {
        // std::cout << r.first.to_string() << " = " << r.second.to_string() << "\n";
        rec_eqs.insert_or_assign(r.first, r.second);
    }
    // rec_eqs = eqs;
}

void rec_solver::simple_solve() {
    res.clear();
    for (auto& func_eq : rec_eqs) {
        z3::expr func = func_eq.first;
        z3::expr eq = func_eq.second;
        if (is_simple_rec(func.decl(), eq)) {
            z3::expr_vector all_app = find_all_app_of_decl(func.decl(), eq, z3ctx);
            z3::expr linear_part = z3ctx.int_val(0);
            for (auto app : all_app) {
                linear_part = linear_part + coeff_of(eq, app, z3ctx)*app;
                // std::cout << coeff_of(eq, app, z3ctx) << std::endl;
            }
            z3::expr const_term = (eq - linear_part).simplify();
            if (all_app.size() == 1 && coeff_of(eq, all_app[0], z3ctx) == 1) {
                auto func_decl = func.decl();
                z3::expr closed = func_decl(0) + ind_var*const_term;
                res.insert_or_assign(func_decl(ind_var), closed.simplify());
            }
        }
    }
    // apply_initial_values();
}

void rec_solver::expr_solve(z3::expr e) {
    // std::cout << e.to_string() << std::endl;
    z3::expr_vector all_apps(z3ctx);
    z3::solver solver(z3ctx);
    
    for (auto& i : rec_eqs) {
        solver.add(i.first == i.second);
    }
    // std::cout << solver.to_smt2() << "\n";
    z3::expr_vector ind_vars(z3ctx);
    z3::expr_vector ind_varps(z3ctx);
    z3::expr_vector zeros(z3ctx);
    ind_vars.push_back(ind_var);
    ind_varps.push_back(ind_var + 1);
    zeros.push_back(z3ctx.int_val(0));
    z3::expr ep = e.substitute(ind_vars, ind_varps);
    z3::expr d = z3ctx.int_const("_d");
    solver.push();
    solver.add(ep == e + d);
    // std::cout << solver.to_smt2(); << "\n"
    auto check_res = solver.check();
    bool solved = false;
    if (check_res == z3::sat) {
        // std::cout << "hhhhh\n";
        z3::model m = solver.get_model();
        z3::expr instance_d = m.eval(d);
        solver.pop();
        solver.push();
        solver.add(ep != e + instance_d);
        auto check_res = solver.check();
        if (check_res == z3::unsat) {
            z3::expr closed = e.substitute(ind_vars, zeros) + instance_d*ind_var;
            res.insert_or_assign(e, closed);
            solved = true;
        }
        solver.pop();
    } else {
        solver.pop();
    }
    if (!solved) {
        solver.push();
        solver.add(ep == d);
        auto check_res = solver.check();
        if (check_res == z3::sat) {
            z3::model m = solver.get_model();
            z3::expr instance_d = m.eval(d);
            solver.pop();
            solver.add(ep != instance_d);
            auto check_res = solver.check();
            // std::cout << solver.get_model() << "\n";
            if (check_res == z3::unsat) {
                res.insert_or_assign(e, instance_d);
            }
        }
    }
}

closed_form_ty rec_solver::get_res() {
    return res;
}

void rec_solver::add_initial_values(z3::expr_vector k, z3::expr_vector v) {
    int size = k.size();
    for (int i = 0; i < size; i++) {
        bool found = false;
        for (int j = 0; j < initial_values_k.size(); j++) {
            z3::expr diff = (initial_values_k[j] - k[i]).simplify();
            if (diff.is_numeral() && diff.get_numeral_int64() == 0) {
                found = true;
                break;
            }
        }
        if (!found) {
            initial_values_k.push_back(k[i]);
            initial_values_v.push_back(v[i]);
        }
    }
}

void rec_solver::apply_initial_values() {
    for (auto& r : res) {
        r.second = r.second.substitute(initial_values_k, initial_values_v);
    }
}

void rec_solver::rec2file() {

}

void rec_solver::print_recs() {
    for (auto r : rec_eqs) {
        std::cout << r.first.to_string() << " = " << r.second.to_string() << "\n";
    }
}
