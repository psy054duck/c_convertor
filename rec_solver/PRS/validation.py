from functools import reduce
import sympy as sp
from .utils import to_exponential_polynomial, cauchy_bnd, my_simplify, round_interval

def validate(closed_form, conds, pattern, n):
    reversed_pattern = list(reversed(pattern))
    num_pieces = len(conds) + 1
    mapping = {i: {j for j in range(len(reversed_pattern)) if reversed_pattern[j] == i} for i in range(num_pieces)}
    res = []
    for i in range(num_pieces):
        proved = reduce(set.union, [mapping[j] for j in range(i)], set())
        try:
            cond = conds[i]
        except IndexError:
            complete = mapping[i].union(proved)
            res.append((complete == set(range(len(pattern))) and len(mapping[i].intersection(proved)) == 0, 99999999999999999999))
            break
        t = mapping[i]
        f = set(range(len(pattern))) - mapping[i] - proved
        res_validate = cond.validate(t, f, len(pattern), n, closed_form)
        res.extend(res_validate)
    return res
    #     if not cond.validate(t, f, len(pattern), n, closed_form):
    #         return False
    # return True

def exhaust_pattern(A, x0, conds, pattern):
    '''Only be invoked when the recurrence is proven to not follow "pattern" ultimately.'''
    num_pieces = len(conds)
    i = 0
    x = [x0]
    res = []
    k = len(pattern)
    while True:
        for j in range(num_pieces):
            if conds[j].evaluate({sp.Symbol('_PRS_x%d' % i): x[-1][i] for i in range(len(x0))}):
                res.append(j)
                x.append(A[j]*x[-1])
                break
        else:
            res.append(num_pieces)
            x.append(A[num_pieces]*x[-1])
        if res[-1] != pattern[i % k]:
            return i + 1, x[-1]
        i += 1

def ep_ge_0(e, n, strict=False):
    transformed = to_exponential_polynomial(e)
    inf_bnd = 9999999999999999999999999999999
    e = my_simplify(e, n)
    if isinstance(e, int) or isinstance(e, float) or e.is_number:
        res = e > 0 if strict else e >= 0
        if res:
            return res, -1
        else:
            return res, 0
    p = e.as_poly(n)
    if p is not None:
        if p.degree() <= 4:
            if strict:
                solution = sp.solveset(e > 0, domain=sp.S.Reals)
            else:
                solution = sp.solveset(e >= 0, domain=sp.S.Reals)
            non_negative = sp.Interval(0, sp.oo, left_open=False)
            intersect = solution.intersection(non_negative)
            intersect = round_interval(intersect)
            if isinstance(intersect, sp.FiniteSet):
                return False, max(intersect) + 1
            if intersect.is_empty:
                return False, 0
            if intersect == non_negative:
                return True, -1
            elif sp.LC(p) > 0:
                j = intersect.left + 1 if intersect.left_open else intersect.left
                return False, 0
            else:
                j = intersect.right if intersect.right_open else intersect.right + 1
                return False, j

    if any(t[1] < 0 for t in transformed):
        even = ep_ge_0(e.subs(n, 2*n), n)
        odd = ep_ge_0(e.subs(n, 2*n + 1), n)
        if not even[0] and not odd[0]:
            return False, min(2*even[0], 2*odd[0] + 1)
        if not even[0]:
            return even
        if not odd[0]:
            return odd
        return True, -1
        # return ep_ge_0(e.subs(n, sp.Integer(2)*n), n) and ep_ge_0(e.subs(n, sp.Integer(2)*n + sp.Integer(1)), n)
    if any(t[1] < 1 for t in transformed):
        return ep_ge_0(10**n*e, n)
    if len(transformed) == 0:
        return True, -1
    pos, neg = rearrange(transformed, n)
    if len(pos) == 0 and len(neg) > 0:
        return ep_ge_0_finite(e, n, inf_bnd, strict=strict)
    u = max(cauchy_bnd(t[0], n) for t in transformed)
    if len(pos) > 0 and len(neg) == 0:
        return ep_ge_0_finite(e, n, u, strict=strict)
    b_pos = max(t[1] for t in pos)
    pos_index = [t[1] for t in pos].index(b_pos)
    b_neg = max(t[1] for t in neg)
    if b_pos < b_neg:
        return ep_ge_0_finite(e, n, inf_bnd, strict=strict)
    r = sum(sp.Poly(t[0], gens=n) for t in neg).degree()
    if r is sp.S.NegativeInfinity:
        r = 0
    mac = sp.series((b_pos/b_neg)**n, x=n, x0=0, n=r+2)
    mac = mac.removeO()
    u_p = cauchy_bnd(pos[pos_index][0].subs(n, u)*mac + len(neg)*sum(t[0] for t in neg), n)
    return ep_ge_0_finite(e, n, max(u, u_p), strict=strict)

def ep_ge_0_finite(e, n, bnd, strict=False):
    if strict:
        cmp = lambda x, y: x > y
    else:
        cmp = lambda x, y: x >= y
    for i in range(bnd + 1):
        if not cmp(e.subs(n, i), 0):
            return False, i
    return True, -1

def rearrange(e, n):
    """'e' is assumed to be a list of exponential polynomial terms"""
    pos, neg = [], []
    for t in e:
        poly = sp.poly(t[0], gens=n)
        lc = sp.LC(poly, gens=n)
        if lc > 0: pos.append(t)
        elif lc < 0: neg.append(t)
    return pos, neg

if __name__ =='__main__':
    n = sp.Symbol('n')
    close = sp.Matrix([[n], [1]])
    conds = [PolyCondition(n - 50, strict=True)]
    validate(close, conds, [1], n)
    # A = [sp.Matrix([[1, 1], [0, 1]]), sp.Matrix([[1, 2], [0, 1]])]
    # x0 = sp.Matrix([0, 1])
    # from condition import PolyCondition
    # _PRS_x0, _PRS_x1 = sp.symbols('_PRS_x0 _PRS_x1')
    # conds = [PolyCondition(50 - _PRS_x0, strict=True)]
    # res = exhaust_pattern(A, x0, conds, [0])
    # print(res)
    # n = sp.Symbol('n')
    # # e = 0.2**n + 0.3**n + .4**n + n**2 + 100*n
    # e = -n**2 + 2
    # res = ep_ge_0(e, n)
    # print(res)
    # from closed_form import _closed_form
    # from rand_instance import generate_instance
    # from guess import guess_pattern
    # A, x0, v = generate_instance(num_var=2, num_pieces=3, seed=None)
    # A = [sp.Matrix([[1, 2], [-1, 4]]),
    #      sp.Matrix([[3, 5], [-sp.Rational(6, 5), 8]]),
    #      sp.Matrix([[70, 3], [141, 7]])]
    # j, xj, pattern = guess_pattern(A, x0, v, 10)
    # close = _closed_form(A, x0, pattern)
    # validate(close, v, pattern)
