import z3
import re
import sympy as sp
from . import utils
from functools import reduce
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

    @classmethod
    def list2z3(cls, l):
        ret = {utils.to_z3(k): utils.to_z3(v) for k, v in l}
        return ret
        
    
    def to_z3(self):
        res = {}
        for var in self.variables:
            if str(var) == 'constant': continue
            var_closed_form = self.var_mapping[var]
            if len(var_closed_form) > 1:
                # res[var] = self._expr_to_z3(var_closed_form[-1][0])
                res[var] = self.ep2z3(var_closed_form[-1][0])
                for closed_form, cond in var_closed_form[:-1]:
                    # res[var] = z3.If(z3.simplify(z3.And(*sim(cond)[0])), self._expr_to_z3(closed_form), res[var])
                    res[var] = z3.If(z3.simplify(z3.And(*sim(cond)[0])), self.ep2z3(closed_form), res[var])
                    # print(closed_form, cond)
            else:
                closed_form, _ = var_closed_form[0]
                # res[var] = self._expr_to_z3(closed_form)
                res[var] = self.ep2z3(closed_form)
        # for var in res:
        #     if str(var) == 's':
        #         print(z3.simplify(z3.substitute(res[var], *[(z3.Int('s'), z3.IntVal(-3)), (z3.Int('n'), z3.IntVal(6))])))
        ret = {z3.Int('%s' % var): z3.IntVal(closed) if isinstance(closed, int) else closed for var, closed in res.items()}
        return ret

    def pow_to_mul(self, expr):
        """
        Convert integer powers in an expression to Muls, like a**2 => a*a.
        """
        pows = list(expr.atoms(sp.Pow))
        if any(not e.is_Integer for b, e in (i.as_base_exp() for i in pows)):

            raise ValueError("A power contains a non-integer exponent")
        #repl = zip(pows, (Mul(*list([b]*e for b, e in i.as_base_exp()), evaluate=False) for i in pows))
        repl = zip(pows, (sp.Mul(*[b]*e, evaluate=False) for b,e in (i.as_base_exp() for i in pows)))
        return expr.subs(repl), list(repl)

    def sp2z3(self, expr):
        if isinstance(expr, int):
            return expr
        elif isinstance(expr, sp.Symbol):
            name = expr.name
            sym_z3 = z3.Int(name)
            return sym_z3
        elif isinstance(expr, sp.Pow):
            b, e = expr.as_base_exp()
            if b == -1:
                e_z3 = self.sp2z3(e)
                return z3.If(e_z3 % 2 == 0, 1, -1)
            elif len(e.free_symbols) > 0:
                raise ValueError("A power contains a non-integer exponent")
            else:
                return reduce(lambda x, y: x*y, [self.sp2z3(b)]*e, 1)
        elif isinstance(expr, sp.Add):
            args = expr.args
            return sum([self.sp2z3(arg) for arg in args])
        elif isinstance(expr, sp.Rational):
            numerator, denominator = expr.numerator, expr.denominator
            numerator_z3 = self.sp2z3(numerator)
            denominator_z3 = self.sp2z3(denominator)
            return numerator_z3/denominator_z3
        elif isinstance(expr, sp.Mul):
            args = expr.args
            return reduce(lambda x, y: x*y, [self.sp2z3(arg) for arg in args], 1)
        else:
            raise ValueError("%s: %s not supported yet" % (expr, type(expr)))

    def my_factor(self, expr):
        if not isinstance(expr, sp.Add):
            return expr
        args = expr.args
        denominators = [sp.fraction(arg)[1] for arg in args]
        divisor = sp.lcm_list(denominators)
        return sp.simplify(expr*divisor), divisor
    # print(my_factor(e))
    def ep2z3(self, expr):
        expr = sp.expand(expr)
        if isinstance(expr, sp.Add):
            num, den = self.my_factor(expr)
            # num_poly = num.as_poly(*num.free_symbols)
            # if num_poly is not None:
            #     num = sp.factor(num_poly, deep=True)
            #     print(sp.factor_list(num_poly))
            #     print(num)
            num_z3 = self.sp2z3(num)
            den_z3 = self.sp2z3(den)
            res = num_z3/den_z3
        else:
            res = self.sp2z3(expr)
        return res

        # def _expr_to_z3(self, expr):
        #     if isinstance(expr, int): return z3.IntVal(expr)
        #     if isinstance(expr, sp.Pow):
        #         b, e = expr.as_base_exp()
        #         if b == -1:
        #             return z3.If(e % 2 == 1)
        # if isinstance(expr, int): return z3.IntVal(expr)
        # expr, repl = utils.pow_to_mul(expr)
        # exec('n = z3.Int("n")')
        # for var in self.variables:
        #     exec('%s = z3.Int("%s")' % (var, var))
        # for var in self.initial_symbols:
        #     exec('%s = z3.Int("%s")' % (var, var))
        # # print(type(re.sub(r'(\d)/', r'z3\.IntVal(\1)/', str(expr)))
        # from z3 import And, Or, Not
        # expr_str = str(expr)
        # for k, v in repl:
        #     expr_str = expr_str.replace(str(k), str(v))
        # expr = expr_str.replace('floor', 'z3.ToInt')
        # res = eval('%s' % re.sub(r'/(\d+)', r'/z3.RealVal(\1)', expr))
        # return res
            # If(cond, )