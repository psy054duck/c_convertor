import functools
import sympy as sp
import z3

def round_interval(interval):
    if interval.is_empty:
        return interval
    if isinstance(interval, sp.FiniteSet):
        max_v, min_v = max(interval), min(interval)
        return sp.Interval(min_v, max_v, left_open=False, right_open=False)

    left = sp.floor(interval.left) if interval.left > 0 else sp.ceiling(interval.left)
    right = sp.floor(interval.right) if interval.right > 0 else sp.ceiling(interval.right)
    left_open = not interval.contains(left)
    right_open = not interval.contains(right)
    return sp.Interval(left, right, left_open=left_open, right_open=right_open)

def my_simplify(e, n):
    res = to_sympy(to_exponential_polynomial(e), n)
    return res
def to_sympy(e, n):
    """Convert an exponential polynomial in the form of a list of terms into expression"""
    return sum(t[0]*t[1]**n for t in e)

def next_element(A, x0, conds):
    num_pieces = len(conds)
    for j in range(num_pieces):
        if conds[j].evaluate({sp.Symbol('_PRS_x%d' % i): x0[i] for i in range(len(x0))}):
            return A[j]*x0
    else:
        return A[num_pieces]*x0

def next_element_by_index(A, v, index):
    if index == len(A):
        return A[-1]*v
    else:
        return A[index]*v

def cauchy_bnd(e, n):
    if e.is_number:
        return 1
    poly = e.as_poly(gens=[n])
    a_n = poly.LC()
    tmp = poly
    max_ratio = 0
    while tmp != 0:
        a_i = tmp.LC()
        degree = tmp.degree(gen=n)
        tmp = tmp - a_i*n**degree
        max_ratio = max(max_ratio, abs(a_i//a_n) + 1)
    return max_ratio

def ath_term(A, x0, v, a):
    x = x0
    for i in range(a):
        for j in range(len(v)):
            if v[j].dot(x) >= 0:
                x = A[j]*x
                break
        else:
            x = A[-1]*x
    return x

def _eval_expand_linear(self, *, force=True, **hints):
    if not force:
        return self
    base = sp.expand(self.args[0])
    expo = sp.expand(self.args[1])
    if len(expo.free_symbols) == 0:
        return self
    n = list(expo.free_symbols)[0]
    coeff = expo.coeff(n)
    constant = sp.simplify(expo - coeff*n)
    return (base**constant)*(base**coeff)**n

sp.Pow._eval_expand_linear = _eval_expand_linear

def my_expand(e):
    return sp.expand(sp.expand(e, linear=True, power_base=False), linear=True, power_base=False)

def combine_pow(t):
    t = sp.expand(t)
    powers = list(t.atoms(sp.Pow))
    exponentials = [power for power in powers if len(power.args[1].free_symbols) != 0]
    coeff = sp.simplify(t / functools.reduce(lambda x, y: x*y, exponentials))
    if len(exponentials) > 1:
        for exponential in exponentials:
            n = (exponential.args[1].free_symbols)[0]
            exp_coeff = exponential.args[1].coeff(n)
            coeff *= exponential.args[0]**exp_coeff
            coeff = simplify(coeff)
    return t

def _split_exponential_polynomial_term(e):
    """'e' is assumed to be poly*base**(a*n + c)
    return (poly*base**c, base**a)"""
    powers = list(e.atoms(sp.Pow))
    exponentials = [power for power in powers if len(power.args[1].free_symbols) != 0]
    if len(exponentials) != 0:
        poly = e
        final_base = 1
        for power in exponentials:
            base = power.args[0]
            expo = power.args[1]
            n = list(expo.free_symbols)[0]
            coeff = expo.coeff(n)
            constant = sp.simplify(expo - coeff*n)
            poly = poly / power * base**constant
            final_base = final_base * base**coeff
        return poly, final_base
    else:
        return e, 1

def simplify_ep(e):
    """'e' is assumed to be a list of (poly, base), which represents poly*base**n"""
    bases = {}
    for t in e:
        bases.setdefault(t[1], 0)
        bases[t[1]] += t[0]
    return [(bases[b], b) for b in bases]


def to_exponential_polynomial(e):
    if my_expand(e) == 0: return []
    tmp = sp.Symbol('__tmp')
    expanded_e = my_expand(e)
    expanded_e += tmp
    if not isinstance(expanded_e, sp.Add):
        raise TypeError('Add is expected but %s is given' % type(expanded_e))
    splited = [_split_exponential_polynomial_term(t) for t in expanded_e.args]
    splited = simplify_ep(splited)
    splited = [(t[0] - tmp, t[1]) if t[1] == 1 else t for t in splited]
    try:
        splited.remove((0, 1))
    except:
        pass
    return list(splited)

def strict2non(formula):
    begin_with_not = False
    res = formula
    if z3.is_not(formula):
        formula = formula.children()[0]
        begin_with_not = True
    # if not (is_le(formula) or is_lt(formula) or is_le(formula) or is_ge(formula)):
    #     return Not(formula)

    if not begin_with_not and (z3.is_le(formula) or z3.is_ge(formula)):
        res = formula

    if z3.is_le(formula):
        if begin_with_not:
            res = formula.children()[0] >= formula.children()[1] + 1
        else:
            res = formula

    if z3.is_ge(formula):
        if begin_with_not:
            res = formula.children()[0] <= formula.children()[1] - 1
        else:
            res = formula

    if z3.is_lt(formula):
        if begin_with_not:
            res = formula.children()[0] >= formula.children()[1] + 1
        else:
            res = formula.children()[0] <= formula.children()[1] - 1
    if z3.is_gt(formula):
        if begin_with_not:
            res = formula.children()[0] <= formula.children()[1] - 1
        else:
            res = formula.children()[0] >= formula.children()[1] + 1
    return z3.simplify(res, arith_lhs=True)


def mk_begin_with_z3(a):
    return str(a).replace('Not', 'z3.Not').replace('And', 'z3.And').replace('Or', 'z3.Or').replace('True', 'z3.BoolVal(True)')
    
def simplify_index_seq(seq):
    if len(seq) == 1: return seq
    last_seg = seq[-1]
    prefix = []
    for seg in seq[:-1]:
        prefix.extend(list(reversed(seg[0]))*seg[1])
    prefix.extend(list(reversed(last_seg)))
    reversed_prefix = list(reversed(prefix))
    i = 0
    while i < len(reversed_prefix):
        if reversed_prefix[i] != last_seg[i % len(last_seg)]:
            break
        i += 1
    end = len(reversed_prefix) - i
    if end != 0:
        S_1 = prefix[:end]
        if all(c == S_1[0] for c in S_1):
            return [([S_1[0]], len(S_1)), list(reversed((prefix + list(reversed(last_seg)))[end:end+len(last_seg)]))]
        return [(list(reversed(prefix[:end])), 1), list(reversed((prefix + list(reversed(last_seg)))[end:end+len(last_seg)]))]
    return [list(reversed(prefix[:len(last_seg)]))]

if __name__ == '__main__':
    n = sp.Symbol('n')
    poly = n**2 + 3*n + 4
    print(cauchy_bnd(poly, n))
    exit(0)
    print(to_exponential_polynomial(0))
    # e = n**2*((-1)**n/4 + 3*n/2) - sp.Rational(1, 4)
    e = -(-1)**n
    e = -(sp.Rational(1, 3))**(sp.Rational(-1, 5)*n)
    ep = to_exponential_polynomial(e)
    print(ep)