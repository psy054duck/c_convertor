import z3
import re
import sympy as sp
sim = z3.Then('ctx-simplify', 'unit-subsume-simplify')
class ClosedForm:
    def __init__(self, res, variables, initial_symbols, n):
        self.variables = variables
        self.initial_symbols = initial_symbols
        var_mapping = {var: [] for var in variables}
        if isinstance(res, tuple):
            cs, closed_forms = res
            for i, k in enumerate(cs):
                for p, closed in enumerate(closed_forms[i]):
                    period = len(closed_forms[i])
                    for j, var_closed in enumerate(closed):
                        try:
                            var_mapping[variables[j]].append((var_closed, z3.And(int(cs[i]) <= n, n < int(cs[i+1]), n % period == p)))
                        except:
                            var_mapping[variables[j]].append((var_closed, z3.And(int(cs[-1]) <= n, n % period == p)))
            self.var_mapping = var_mapping
        else:
            for case in res:
                if len(case) == 2:
                    closed_form, condition = case
                    condition = z3.simplify(condition)
                    first_elements, remaining = closed_form
                    for i, e in enumerate(first_elements):
                        for j, var_closed in enumerate(e):
                            var_mapping[variables[j]].append((var_closed, z3.And(condition, n == i)))
                    for i, e in enumerate(remaining):
                        period = len(remaining)
                        for j, var_closed in enumerate(e):
                            var_mapping[variables[j]].append((var_closed, z3.And(condition, n >= len(first_elements), n % period == i)))
                        # print('hhh')
                elif len(case) == 4:
                    # closed_form, condition, k = case
                    closed_form, condition, k, mid_len = case
                    self.k = k
                    condition = z3.simplify(condition)
                    # first_elements_before_k, elements_before_k, first_elements_after_k, elements_after_k = closed_form
                    first_elements_before_k, elements_before_k, mid_k_elements, mid_closed_form, last_k_elements, last_closed_form = closed_form
                    for i, e in enumerate(first_elements_before_k):
                        for j, var_closed in enumerate(e):
                            var_mapping[variables[j]].append((var_closed, condition and n == i))
                    for i, e in enumerate(elements_before_k):
                        period = len(elements_before_k)
                        for j, var_closed in enumerate(e):
                            var_mapping[variables[j]].append((var_closed, z3.And(condition, n >= len(first_elements_before_k), n < k, n % period == i)))
                    for i, e in enumerate(last_k_elements):
                        for j, var_closed in enumerate(e):
                            var_mapping[variables[j]].append((var_closed, z3.And(condition, n == k+i)))
                    for i, e in enumerate(last_closed_form):
                        period = len(last_closed_form)
                        from sympy.parsing.sympy_parser import parse_expr
                        k_s = parse_expr(re.sub(r'(\w+)/(\w+)', r'floor((\1)/(\2))', str(k)))
                        n_s = sp.Symbol('n', integer=True)
                        for j, var_closed in enumerate(e):
                            var_mapping[variables[j]].append((var_closed.subs(n_s, n_s - k_s), z3.And(condition, n >= k+len(last_k_elements), (n - k) % period == i)))
                else:
                    print(len(case))
                    print(case)
                    print('*'*10)
        self.var_mapping = var_mapping

    def to_z3(self):
        res = {}
        for var in self.variables:
            if str(var) == 'constant': continue
            var_closed_form = self.var_mapping[var]
            if len(var_closed_form) > 1:
                res[var] = self._expr_to_z3(var_closed_form[-1][0])
                for closed_form, cond in var_closed_form[:-1]:
                    res[var] = z3.If(z3.simplify(z3.And(*sim(cond)[0])), self._expr_to_z3(closed_form), res[var])
                    # print(closed_form, cond)
            else:
                closed_form, _ = var_closed_form[0]
                res[var] = self._expr_to_z3(closed_form)
        # for var in res:
        #     if str(var) == 's':
        #         print(z3.simplify(z3.substitute(res[var], *[(z3.Int('s'), z3.IntVal(-3)), (z3.Int('n'), z3.IntVal(6))])))
        ret = {z3.Int('%s' % var): z3.IntVal(closed) if isinstance(closed, int) else closed for var, closed in res.items()}
        return ret

    def _expr_to_z3(self, expr):
        if isinstance(expr, int): return z3.IntVal(expr)
        exec('n = z3.Int("n")')
        for var in self.variables:
            exec('%s = z3.Int("%s")' % (var, var))
        for var in self.initial_symbols:
            exec('%s = z3.Int("%s")' % (var, var))
        # print(type(re.sub(r'(\d)/', r'z3\.IntVal(\1)/', str(expr)))
        from z3 import And, Or, Not
        expr = str(expr).replace('floor', 'z3.ToInt')
        res = eval('%s' % re.sub(r'/(\d+)', r'/z3.RealVal(\1)', expr))
        return res
            # If(cond, )