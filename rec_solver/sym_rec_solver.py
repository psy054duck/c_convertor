from .PRS.prs_solver import solve_sym, solve_sym_str, solve_recurrence_expr
# from .PRS.mathematica_manipulation import session
import z3
import sympy as sp
import fire
from .PRS.closed_form_class import ClosedForm

def pretty_solve_and_print(filename):
    n = z3.Int('n')
    res, variables, initial_symbols = solve_sym(filename)
    var_mapping = {var: [] for var in variables}
    len_longest_closed_form = max(len(str(case[0])) if not isinstance(case[0], tuple) else max(len(str(case[0][0])), len(str(case[0][1]))) for case in res)
    template_closed_form = '%%-%ds' % (len_longest_closed_form + 1)
    if isinstance(res, tuple):
        cs, closed_forms = res
        for c, closed in zip(cs, closed_forms):
            for i, cl in enumerate(closed):
                for j, var_closed in enumerate(cl):
                    if j != len(cl) - 1:
                        print('%s = %s if %d <= n && n %% %d = %d' % (str(variables[j]) + '(n)', cl[j], c, len(closed), i))
        return

    for case in res:
        if len(case) == 2:
            closed_form, condition = case
            try:
                condition = z3.simplify(condition)
            except:
                pass
            first_elements, remaining = closed_form
            for i, e in enumerate(first_elements):
                print('%-60s if n = %d && %s' % (e, i, condition))
                for j, var_closed in enumerate(e):
                    var_mapping[variables[j]].append((var_closed, z3.And(condition, n == i)))
            for i, e in enumerate(remaining):
                period = len(remaining)
                print('%-60s if %d <= n && n %% %d = %d && %s' % (e, len(first_elements), period, i, condition))
                for j, var_closed in enumerate(e):
                    var_mapping[variables[j]].append((var_closed, z3.And(condition, n >= len(first_elements), n % period == i)))
                # print('hhh')
        elif len(case) == 4:
            closed_form, condition, k, mid_len = case
            condition = z3.simplify(condition)
            first_elements_before_k, elements_before_k, mid_k_elements, mid_closed_form, first_elements_after_k, elements_after_k = closed_form
            for i, e in enumerate(first_elements_before_k):
                print('%-60s if n = %d && %s' % (e, i, condition))
                for j, var_closed in enumerate(e):
                    var_mapping[variables[j]].append((var_closed, z3.And(condition, n == i)))
            for i, e in enumerate(elements_before_k):
                period = len(elements_before_k)
                print('%-60s if %d <= n < %s && n %% %d = %d && %s' % (e, len(first_elements_before_k), k, period, i, condition))
                for j, var_closed in enumerate(e):
                    var_mapping[variables[j]].append((var_closed, z3.And(condition, n >= len(first_elements_before_k), n < k, n % period == i)))
            for i, e in enumerate(mid_k_elements):
                print('%-60s if n = %s+%d && %s' % (e, k, i, condition))
                for j, var_closed in enumerate(e):
                    var_mapping[variables[j]].append((var_closed, z3.And(condition, n == i)))
            if mid_closed_form is not None:
                for i, e in enumerate(mid_closed_form):
                    period = len(mid_closed_form)
                    print('%-60s if %s + %d <= n < %s + %d && n %% %d = %d && %s' % (e, k, len(mid_k_elements), k, mid_len, period, i, condition))
                    for j, var_closed in enumerate(e):
                        var_mapping[variables[j]].append((var_closed, z3.And(condition, n >= len(first_elements_before_k), n < k, n % period == i)))
            for i, e in enumerate(first_elements_after_k):
                print('%-60s if n = %s+%d+%d && %s' % (e, k, mid_len, i, condition))
                for j, var_closed in enumerate(e):
                    var_mapping[variables[j]].append((var_closed, z3.And(condition, n == k+i)))
            for i, e in enumerate(elements_after_k):
                period = len(elements_after_k)
                n_s = sp.Symbol('n', integer=True)
                from sympy.parsing.sympy_parser import parse_expr
                import re
                k_s = parse_expr(re.sub(r'(\w+)/(\w+)', r'floor((\1)/(\2))', str(k)))
                m = e.subs(n_s, n_s - k_s)
                print('%-60s if %s+%d+%d <= n && (n - (%s)) %% %d = %d && %s' % (m, k, mid_len, len(first_elements_after_k), k, period, i, condition))
                for j, var_closed in enumerate(e):
                    var_mapping[variables[j]].append((var_closed.subs(n_s, n_s-k_s), z3.And(condition, n >= k+len(first_elements_after_k), (n-k) % period == i)))

def solve_file(filename, ind_var):
    index = sp.Symbol(ind_var, integer=True)
    res = solve_sym(filename, index)
    if isinstance(res, tuple):
        closed, variables, initial_symbols = res
        return ClosedForm(closed, variables, initial_symbols, z3.Int(ind_var)).to_z3()
    else:
        return ClosedForm.list2z3(res)


if __name__ == '__main__':
    # fire.Fire(main)
    # fire.Fire(pretty_solve_and_print)
    # pretty_solve_and_print('../temp/rec.txt')
    pretty_solve_and_print('test.txt')
# session.terminate()
