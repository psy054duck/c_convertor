from operator import index
# from utils import closed_form2mod
from numpy import SHIFT_INVALID, matrix
import sympy as sp
import z3
import functools
import random
from itertools import product

from sympy.utilities.iterables import connected_components
from .guess import guess_pattern
from .utils import my_expand, my_simplify, next_element, next_element_by_index, strict2non, mk_begin_with_z3, simplify_index_seq
from .validation import validate
from .condition import PolyCondition

# DEFAULT_MATH_TOOL = 'mathematica'
DEFAULT_MATH_TOOL = 'sympy'

if DEFAULT_MATH_TOOL == 'mathematica':
    from wolframclient.evaluation.kernel import localsession
    from .mathematica_manipulation import matrix2mathematica, matrix_power_mathematica, matrix_mul

def jordan_cell_power(jc, n):
        N = jc.shape[0]
        l = jc[0, 0]
        for i in range(N):
                for j in range(N-i):
                        bn = sp.binomial(n, i)
                        if isinstance(bn, sp.binomial):
                                bn = bn._eval_expand_func()
                        jc[j, i+j] = l**(n-i)*bn if l != 0 else 0


def matrix_power_sympy(M, n):
        P, jordan_cells = M.jordan_cells()
        for j in jordan_cells:
                jordan_cell_power(j, n)
        a = P
        b = sp.diag(*jordan_cells)
        c = P.inv()
        return P*sp.diag(*jordan_cells)*P.inv()

def matrix_power(M, n, methods=DEFAULT_MATH_TOOL):
    if methods == 'sympy':
        return matrix_power_sympy(M, n)
    else:
        return matrix_power_mathematica(M, n)

# def simplify_index_seq(seq):
#     if len(seq) == 2 and len(seq[0][0]) == 2 and seq[0][1] == 2:
#         return [([seq[0][0][1]], 1), ([seq[0][0][0]], 1), seq[-1]]
#     return seq

def matrix2transitions(A, order):
    var_vec = sp.Matrix(order)
    transitions = []
    for a in A:
        transition_mat = a*var_vec
        constant = sp.Symbol('constant')
        transitions.append({var: transition_mat[i].subs({constant: 1}) for i, var in enumerate(order) if str(var) != 'constant'})
    return transitions

def solve_rec_expr(transitions, x0, conds, order, n):
    res = solve_poly_recurrence_expr(transitions, x0, conds, order, n, degr=2)
    if len(res) == 0:
        res = solve_poly_recurrence_expr(transitions, x0, conds, order, n, degr=3)
    return res

# def solve_poly_recurrence_expr(A, x0, conds, order, n):
def solve_poly_recurrence_expr(transitions, x0, conds, order, n, degr=3):
    X = [var for var in order if str(var) != 'constant']
    # transitions = matrix2transitions(A, order)
    ks_polynomials = vec_space_d(X, x0, transitions, degr)
    inits = {var: x0[i] for i, var in enumerate(order) if str(var) != 'constant'}
    res = []
    for k, polynomials in ks_polynomials:
        for p in polynomials:
            if p == sp.Integer(1): continue
            res_p = solve_poly_rec(k, p, transitions, n, inits)
            res.append(res_p)
    return res

def gen_poly_template(X, d):
    index_cnt = 1
    monomials = {sp.Integer(1)}
    for i in range(d):
        monomials_pair = set(product(X, monomials))
        monomials = monomials.union(set(x*y for x, y in monomials_pair))
    monomials = list(monomials)
    coeffs = sp.symbols('a:%d' % len(monomials), Real=True)
    res = sum([a*m for a, m in zip(coeffs, monomials)])
    return res.as_poly(*X), list(coeffs), monomials

def get_transition_degr(transition, X):
    return max([tran.as_poly(*X).total_degree() for tran in transition.values()])

def get_max_transitions_degr(transitions, X):
    return max([get_transition_degr(tran, X) for tran in transitions])

def vec_space_d(X, inits, transitions, d):
    poly_template, coeffs, monomials = gen_poly_template(X, d)
    possible_k = None
    matrices = []
    d_p = get_max_transitions_degr(transitions, X)
    _, _, complete_monomials = gen_poly_template(X, d*d_p)
    num_higher_monomials = len(complete_monomials) - len(monomials)
    for tran in transitions:
        poly_prime = poly_template.as_expr().subs(tran, simultaneous=True).as_poly(*X)
        coords = [mono.as_expr().subs(tran, simultaneous=True).as_poly(*X) for mono in monomials]
        # M = sp.Matrix([[coord.coeff_monomial(mono) for mono in monomials] for coord in coords]).T
        M = sp.Matrix([[coord.coeff_monomial(mono) for mono in complete_monomials] for coord in coords]).T
        matrices.append(M)

    for M in matrices:
        M_upper = M[:num_higher_monomials, :]
        M_lower = M[num_higher_monomials:, :]
        if possible_k is None:
            possible_k = set(M_lower.eigenvals().keys())
        else:
            possible_k = possible_k.intersection(M_lower.eigenvals().keys())

    ret = []
    for k in possible_k:
        all_coeffs = []
        for tran in transitions:
            poly_prime = poly_template.as_expr().subs(tran, simultaneous=True).as_poly(*X)
            # poly_coeffs = poly_prime.coeffs()
            rem = poly_prime - k*poly_template
            rem_coeffs = rem.coeffs()
            all_coeffs.extend(rem_coeffs)
        res, _ = sp.linear_eq_to_matrix(all_coeffs, *coeffs)
        basis = res.nullspace()
        basis_instances = []
        for vec in basis:
            instance = poly_template.subs({c: v for v, c in zip(vec, coeffs)}, simultaneous=True)
            numerator, _ = sp.fraction(sp.factor(instance))
            basis_instances.append(numerator)
        # symbolic_baiss = [(vec.T * Matrix(coeffs))[0] for vec in basis]
        if len(basis_instances) != 0:
            ret.append((k, basis_instances))
    all_coeffs = []
    const_dummy_symbol = sp.Symbol('aaaaa0', real=True)
    coeffs.append(const_dummy_symbol)
    for tran in transitions:
        poly_prime = poly_template.as_expr().subs(tran, simultaneous=True).as_poly(*X)
        rem = poly_prime - poly_template - const_dummy_symbol
        rem_coeffs = rem.coeffs()
        all_coeffs.extend(rem_coeffs)
    res, _ = sp.linear_eq_to_matrix(all_coeffs, *coeffs)
    basis = res.nullspace()
    basis_instances = []
    for vec in basis:
        instance = poly_template.subs({c: v for v, c in zip(vec, coeffs)}, simultaneous=True)
        numerator, _ = sp.fraction(sp.factor(instance))
        basis_instances.append(numerator)
    if len(basis) != 0:
        ret.append((sp.Integer(1), basis_instances))
    print(ret)
    return ret

def solve_poly_rec(k, p, transitions, _n, inits):
    # _n = sp.Symbol('n', integer=True)
    if k != 1:
        if k == 0:
            if sp.simplify(p.subs(inits, simultaneous=True) == 0):
                return (p, 0)
            else:
                return (p, sp.Piecewise((0, _n >= 1), (p.subs(inits, simultaneous=True), True)))
        elif sp.simplify(p.subs(inits, simultaneous=True)) == 0:
            return (p, 0)
            # return (p, k**_n*sp.simplify(p.subs(inits, simultaneous=True)))
        else:
            return (p, sp.simplify(p.subs(inits, simultaneous=True))*k**_n)
            # return (1, 1)
    else:
        cs = [sp.simplify(p.subs(tran, simultaneous=True) - p) for tran in transitions]
        if all([c == cs[0] for c in cs]):
            c = cs[0]
            return (p, sp.simplify(p.subs(inits, simultaneous=True)) + _n*c)


def symbolic_closed_form_linear(A, x0, conds, order, n, bnd=100):
    rename = {order[i]: sp.Symbol('_PRS_x%d' % i) for i in range(len(order))}
    sat = z3.Solver()
    qe = z3.Then('qe', 'ctx-solver-simplify')
    Phi = False
    v0 = sp.ones(x0.shape[0], x0.shape[1])
    initial_symbols = []
    # random_list = [11, 12]
    initial_index_map = {}
    sim = z3.Tactic('ctx-solver-simplify')
    for i, v in enumerate(x0):
        if v.is_symbol and v.name != 'constant':
            initial_symbols.append(v)
            v0[i] = 4
            initial_index_map[str(v)] = i
            # v0[i] = random.randint(1, 10)
            # v0[i] = random_list[i]
            # v0[i] = 100
            # v0[i] =1000 
        else:
            v0[i] = x0[i]
    is_all_initialized = False
    if len(initial_symbols) == 0:
        is_all_initialized = True
    symbols = initial_symbols + [n]
    for var in symbols:
        exec('z3%s = z3.Int("z3%s")' % (var, var))
    # z3vars = [sp.Symbol('z3%s' % s) for s in initial_symbols]
    completed = False
    res = []
    k_index = 0
    while not completed:
        cs, closed_forms, index_seq = closed_form(A, v0, conds, order, n, bnd=bnd)
        if is_all_initialized:
            res = (cs, closed_forms)
            return res
        index_seq = simplify_index_seq(index_seq)
        # print(index_seq)
        if len(index_seq) == 1:
            need_k = False
            pattern = index_seq[0]
            part, admit_power_of_0 = _closed_form_all(A, x0, pattern, n)
            phi_z3, phi_z3_first, _ = _gen_phi(part, admit_power_of_0, A, conds, x0, pattern, order, initial_symbols, n)
            if len(phi_z3_first) == 0:
                phi_z3_str = 'And(%s)' % (', '.join(str(p) for p in phi_z3))
                q = eval('z3.ForAll(z3n, z3.Implies(z3n >= 0, %s))' % mk_begin_with_z3(phi_z3_str))
            else:
                phi_z3_str = 'And(%s)' % (', '.join(str(p) for p in phi_z3))
                phi_z3_first_str = 'And(%s)' % (', '.join(str(p) for p in phi_z3_first))
                q = eval('z3.And(z3.ForAll(z3n, z3.Implies(z3n >= 1, %s)), %s)' % (mk_begin_with_z3(phi_z3_str), mk_begin_with_z3(phi_z3_first_str)))
            if admit_power_of_0:
                first_k = []
            else:
                first_k = _compute_first_k(A, x0, pattern)
            part = (first_k, part)
        else:
            need_k = True
            # assert(len(index_seq) == 2)
            if len(index_seq) == 3:
                first, mid, mid_len, last = index_seq[0][0], index_seq[1][0], index_seq[1][1], index_seq[-1]
            elif len(index_seq) == 2:
                first, mid, mid_len, last = index_seq[0][0], None, 0, index_seq[-1]
            else:
                raise Exception('len(index_seq) should be 2 or 3')
            first_closed_form, first_admit_power_of_0 = _closed_form_all(A, x0, first, n)
            assert(len(first_closed_form) == 1)
            k = sp.Symbol('k', integer=True)
            initial_mid_k = first_closed_form[0].subs(n, k)
            if mid is not None:
                mid_closed_form, mid_admit_power_of_0 = _closed_form_all(A, initial_mid_k, mid, n)
                mid_closed_form = [c.subs(n, n-k) for c in mid_closed_form]
                initial_k = mid_closed_form[0].subs(n, k+mid_len)
            else:
                initial_k = initial_mid_k
                mid_admit_power_of_0 = True
                mid_closed_form = None
            last_closed_form, last_admit_power_of_0 = _closed_form_all(A, initial_k, last, n)
            # last_closed_form = [c.subs(n, n-(k+mid_len)) for c in last_closed_form]
            phi_1, first_phi_1, _ = _gen_phi(first_closed_form, first_admit_power_of_0, A, conds, x0, first, order, initial_symbols, n)
            phi_2, first_phi_2, last_phi_2 = _gen_phi(last_closed_form, last_admit_power_of_0, A, conds, initial_k, last, order, initial_symbols, n, need_k=True)
            if mid is not None:
                phi_3, first_phi_3, last_phi_1 = _gen_phi(mid_closed_form, mid_admit_power_of_0, A, conds, initial_mid_k, mid, order, initial_symbols, n)
            phi_1_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in phi_1)
            phi_2_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in phi_2)
            if mid is not None:
                phi_3_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in phi_3)
                last_phi_1_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in last_phi_1)
            else:
                last_phi_1_str = 'True'
                phi_3_str = 'True'
            last_phi_2_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in last_phi_2)
            if len(first_phi_1) != 0:
                first_phi_1_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in first_phi_1)
            else:
                first_phi_1_str = True
            if len(first_phi_2) != 0:
                first_phi_2_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in first_phi_2)
            else:
                first_phi_2_str = True
            if mid is not None and len(first_phi_3) != 0:
                first_phi_3_str = 'z3.And(%s)' % ', '.join(mk_begin_with_z3(p) for p in first_phi_3)
            else:
                first_phi_3_str = True
            k = z3.Int('k')
            phi = []
            period_first = len(first) if not first_admit_power_of_0 else 0
            period_mid = len(mid) if not mid_admit_power_of_0 else 0
            period_last = len(last) if not last_admit_power_of_0 else 0
            # q = eval('z3.And(k >= 1, %s, %s, %s, %s, %s, z3.ForAll(z3n, z3.And(z3.Implies(z3.And(%d <= z3n, z3n < k-1), %s), z3.Implies(z3.And(k + %d <= z3n, z3n < k+%d-1), %s), z3.Implies(z3n >= k+%d, %s))))' % (first_phi_1_str, first_phi_2_str, first_phi_3_str, last_phi_1_str, last_phi_2_str, period_first, phi_1_str, period_mid, mid_len, phi_3_str, mid_len, phi_2_str))
            q = eval('z3.And(k >= 1, %s, %s, %s, z3.ForAll(z3n, z3.And(z3.Implies(z3.And(%d <= z3n, z3n < k), %s), z3.Implies(z3.And(k + %d <= z3n, z3n < k+%d), %s), z3.Implies(z3n >= 0, %s))))' % (first_phi_1_str, first_phi_2_str, first_phi_3_str, period_first, phi_1_str, period_mid, mid_len, phi_3_str, phi_2_str))
            # q = eval('z3.And(k >= 1, %s, %s, %s, z3.ForAll(z3n, z3.And(z3.Implies(z3.And(%d <= z3n, z3n < k), %s), z3.Implies(z3.And(k + %d <= z3n, z3n < k+%d), %s), z3.Implies(z3n >= k + %d, %s))))' % (first_phi_1_str, first_phi_2_str, first_phi_3_str, period_first, phi_1_str, period_mid, mid_len, phi_3_str, mid_len, phi_2_str))
            first_k_elements = []
            last_k_elements = []
            mid_k_elements = []
            if not first_admit_power_of_0: 
                first_k_elements = _compute_first_k(A, x0, first)
            if not last_admit_power_of_0:
                last_k_elements = _compute_first_k(A, initial_k, last)
            if not mid_admit_power_of_0:
                mid_k_elements = _compute_first_k(A, initial_mid_k, mid)
            part = (first_k_elements, first_closed_form, mid_k_elements, mid_closed_form, last_k_elements, last_closed_form)

        if len(initial_symbols) == 0:
            return [(part, z3.BoolVal(True), int(index_seq[0][1]), int(index_seq[1][1]))]
        # print(q)
        qe_phi = qe(q)[0]
        # print(qe_phi)
        if len(qe_phi) != 0:
            phi_z3 = eval('z3.And(%s)' % (', '.join([mk_begin_with_z3(s) for s in qe_phi])))
        else:
            phi_z3 = True
        condition = phi_z3
        if phi_z3 is True:
            res.append((part, z3.BoolVal(True)))
        else:
            k = z3.Int("k")
            sim = z3.Then('ctx-simplify', 'ctx-solver-simplify', 'tseitin-cnf')
            phi_z3_with_k = z3.And(*sim(phi_z3)[0])
            phi_z3_with_k = z3.simplify(phi_z3_with_k, som=True, arith_lhs=True, sort_sums=True)
            phi_z3_with_k = sim(phi_z3_with_k)[0]
            new_list = []
            for conjunct in phi_z3_with_k:
                need_inv = False
                transformed = strict2non(conjunct)
                if z3.is_lt(transformed) or z3.is_le(transformed) or z3.is_ge(transformed) or z3.is_gt(transformed):
                    lhs, rhs = transformed.children()
                    for addant in lhs.children():
                        if z3.is_mul(addant):
                            factors = addant.children()
                            if k in factors:
                                coef = factors[0].as_long() # assume the first one child is the coeff of k
                                if coef < 0:
                                    need_inv = True
                    if need_inv:
                        new_lhs = -lhs
                        new_rhs = -rhs
                        if z3.is_lt(transformed):
                            transformed = new_lhs > new_rhs
                        elif z3.is_le(transformed):
                            transformed = new_lhs >= new_rhs
                        elif z3.is_gt(transformed):
                            transformed = new_lhs < new_rhs
                        else:
                            transformed = new_lhs <= new_rhs
                new_list.append(transformed)
            phi_z3_with_k = z3.And(*new_list)
            phi_z3_with_k = z3.simplify(phi_z3_with_k, som=True, arith_lhs=True, sort_sums=True, local_ctx=True)
            phi_z3_with_k = z3.Tactic('propagate-ineqs')(phi_z3_with_k)[0]
            equalities = [phi for phi in phi_z3_with_k if z3.is_eq(phi)]
            phi_z3_with_k = z3.And(*phi_z3_with_k)
            if not any('k' in str(eq.children()[0]) for eq in equalities):
                for eq in equalities:
                    lhs, rhs = eq.children()
                    phi_z3_with_k = z3.substitute(phi_z3_with_k, (lhs, rhs))
            phi_z3_with_k = z3.simplify(z3.And(phi_z3_with_k, k >= 1), som=True, arith_lhs=True, sort_sums=True, local_ctx=True)
            phi_z3_with_k = z3.Tactic('propagate-ineqs')(phi_z3_with_k)[0]
            phi_z3_with_k = z3.And(*phi_z3_with_k)
            phi_z3_with_k = z3.Tactic('propagate-ineqs')(phi_z3_with_k)[0]
            phi_z3_with_k = [phi for phi in phi_z3_with_k if 'k' in str(phi)]
            only_eq = [phi for phi in phi_z3_with_k if z3.is_eq(phi) and 'k' in str(phi)]
            phi_z3_with_k = only_eq
            if need_k:
                assert(len(phi_z3_with_k) == 1)
                phi_z3_with_k = phi_z3_with_k[0]
                lhs, rhs = phi_z3_with_k.children()[0], phi_z3_with_k.children()[1]
                k_res = sp.solve(sp.parsing.sympy_parser.parse_expr(str(lhs - rhs), evaluate=False), sp.parsing.sympy_parser.parse_expr('k'))
                k_res = z3.IntVal(0) + eval(str(k_res[0]))
                k_res = z3.simplify(k_res)
                mapping = [(z3.Var(i, z3.IntSort()), z3.Int('%s' % initial)) for i, initial in enumerate(initial_symbols)]
                k_interpreted = z3.substitute(k_res, mapping)
                k_interpreted = z3.substitute(k_interpreted, [(z3.Int('z3'+str(s)), z3.Int(str(s))) for s in initial_symbols])
                import re
                k_s = sp.parse_expr(re.sub(r'(\w+)/(\w+)', r'floor((\1)/(\2))', str(k_interpreted)))
                phi_z3 = z3.substitute(phi_z3, (k, k_res))
                k_replaced_part = []
                for component in part:
                    new_tuple = component
                    if component is not None:
                        # new_tuple = tuple(c.subs({sp.Symbol('k', integer=True): parse_expr(str(k_interpreted))}) for c in component)
                        new_tuple = tuple(c.subs({sp.Symbol('k', integer=True): k_s}) for c in component)
                    k_replaced_part.append(new_tuple)
                k_replaced_part = tuple(k_replaced_part)
                phi_without_z3 = sim(z3.substitute(phi_z3, [(z3.Int('z3'+str(s)), z3.Int(str(s))) for s in initial_symbols]))[0]
                res.append((k_replaced_part, z3.And(*phi_without_z3), k_interpreted, mid_len))
                k_index += 1
            else:
                condition_without_z3 = sim(z3.substitute(phi_z3, [(z3.Int('z3'+str(s)), z3.Int(str(s))) for s in initial_symbols]))[0]
                res.append((part, z3.And(*condition_without_z3)))
        Phi = z3.Or(Phi, phi_z3)
        z3vars = [z3.Int('z3%s' % s) for s in initial_symbols]
        if sat.check(z3.Not(Phi)) == z3.sat:
            m = sat.model()
            for var in z3vars:
                # index = ['z3'+str(v) for v in order].index(str(var))
                index = initial_index_map[str(var)[2:]]
                if m[var] is not None:
                    v0[index] = m[var].as_long()
        else:
            completed = True
    return res

def _compute_first_k(A, x0, pattern):
    cur_x = x0
    res = []
    for p in reversed(pattern):
        res.append(cur_x)
        cur_x = A[p]*cur_x
    return res

def _gen_phi(closed_form, admit_power_of_0, A, conds, x0, pattern, order, initial_symbols, n, need_k=False):
    symbols = initial_symbols + [n]
    phi = []
    phi_first = []
    period = len(pattern)
    phi_last = []
    e = pattern[-1]
    if e == len(conds):
        for cond in conds:
            phi_last.append(cond.neg().subs({order[p]: x0[p] for p in range(len(order))}))
    else:
        for cond in conds[:e]:
            phi_last.append(cond.neg().subs({order[p]: x0[p] for p in range(len(order))}))
        phi_last.append(conds[e].subs({order[p]: x0[p] for p in range(len(order))}))
    for i, e in enumerate(reversed(pattern)):
        part_i = closed_form[i]
        if e == len(conds):
            for cond in conds:
                phi.append(cond.neg().subs({order[p]: part_i[p].subs(n, period*n + i) for p in range(len(order))}))
        else:
            for cond in conds[:e]:
                phi.append(cond.neg().subs({order[p]: part_i[p].subs(n, period*n + i) for p in range(len(order))}))
            phi.append(conds[e].subs({order[p]: part_i[p].subs(n, period*n + i) for p in range(len(order))}))
    phi_z3 = [p.subs({sym: sp.Symbol('z3%s' % sym, integer=True) for sym in symbols + [sp.Symbol('n')]}) for p in phi]
    for var in symbols:
        exec('z3%s = z3.Int("z3%s")' % (var, var))
    z3vars = [z3.Int('z3%s' % s) for s in symbols]
    phi_z3_str = mk_begin_with_z3('And(%s)' % ', '.join(str(p) for p in phi_z3))
    if not admit_power_of_0:
        cur_x = x0
        for i, e in enumerate(reversed(pattern)):
            if e == len(conds):
                for cond in conds:
                    phi_first.append(cond.neg().subs({order[p]: cur_x[p] for p in range(len(order))}))
            else:
                for cond in conds[:e]:
                    phi_first.append(cond.neg().subs({order[p]: cur_x[p] for p in range(len(order))}))
                phi_first.append(conds[e].subs({order[p]: cur_x[p] for p in range(len(order))}))
            cur_x = A[e]*cur_x
    phi_z3_first = [p.subs({sym: sp.Symbol('z3%s' % sym, integer=True) for sym in symbols + [sp.Symbol('n')]}) for p in phi_first]
    phi_z3_last = [p.subs({sym: sp.Symbol('z3%s' % sym, integer=True) for sym in symbols + [sp.Symbol('n')]}) for p in phi_last]
        # phi_z3_first_str = mk_begin_with_z3('And(%s)' % ', '.join(str(p) for p in phi_z3_first))
    return phi_z3, phi_z3_first, phi_z3_last
        # q_str = 'z3.And(z3.ForAll(z3n, z3.Implies(z3n >= 1, %s)), %s)' % (phi_z3_str, phi_z3_first_str)
    # return phi, phi_first
    


def closed_form(A, x0, conds, order, n, bnd=100):
    rename = {order[i]: sp.Symbol('_PRS_x%d' % i) for i in range(len(order))}
    conds = [cond.subs(rename) for cond in conds]
    a = 1
    cs = [0]
    closed_forms = []
    start = True
    seq = []
    x = []
    index_sequence = []
    while a < bnd + 1:
        a *= 2
        c, xc, pattern, others, seq, x = guess_pattern(A, x0, conds, a, seq, x)
        if pattern is None: continue
        if len(others) != 0:
            if all([others[-1] == p for p in others]):
                l_others = len(others)
                others = [others[-1]]
                index_sequence.append((others, l_others))
            else:
                index_sequence.append((others, 1))
        if c != 0:
            res, admit_power_of_0 = _closed_form_all(A, x0, others, n)
            if res[0].subs(n, 0) != x0:
                cs.append(cs[-1] + 1)
                closed_forms.append([x0])
                res = [t.subs(n, n+1) for t in res]
                c = c - 1
            shiftment = len(res) - (cs[-1] % len(res))
            shifted_res = [t.subs(n, n - cs[-1]) for t in res]
            shifted_res = shifted_res[shiftment:] + shifted_res[:shiftment]
            closed_forms.append(shifted_res)
            cs.append(cs[-1] + c)
        res, admit_power_of_0 = _closed_form_all(A, xc, pattern, n)
        if res[0].subs(n, 0) != xc:
            cs.append(cs[-1] + 1)
            closed_forms.append([xc])
            res = [t.subs(n, n+1) for t in res]
        res_validate = validate(res, conds, pattern, n)
        shiftment = len(res) - (cs[-1] % len(res))
        shifted_res = [t.subs(n, n - cs[-1]) for t in res]
        shifted_res = shifted_res[shiftment:] + shifted_res[:shiftment]
        closed_forms.append(shifted_res)
        if all(p[0] for p in res_validate):
            index_sequence.append(pattern)
            return cs, closed_forms, index_sequence
        else:
            start = min(p[1] for p in res_validate if not p[0]) - 1
            index_sequence.append((pattern, (start+1)//len(pattern)))
            r = start % len(res)
            x0 = res[r].subs(n, start)
            # x0 = res.subs(n, cs[-1] + start)
            x0 = next_element(A, x0, conds)
            cs.append(cs[-1] + start + 1)
            seq = []
            x = []

def _closed_form_all(A, x0, pattern, n):
    dim = A[0].shape[0]
    connected_components = _connected_components(A)
    closed_forms = [sp.zeros(dim, 1) for _ in range(len(pattern))]
    first_num_elements = [sp.zeros(dim, 1) for _ in range(len(pattern))]
    admit_power_of_0 = True
    for m in closed_forms: m[-1, 0] = 1
    for component in connected_components:
        component_matrix = [_extract_matrix(a, component) for a in A]
        component_x0 = _extract_vec(x0, component)
        part_closed_form, part_admit_power_of_0 = _closed_form(component_matrix, component_x0, pattern, n)
        for closed, r in zip(closed_forms, part_closed_form):
            for map_i, i in enumerate(component):
                closed[i, 0] = r[map_i, 0]
        if not part_admit_power_of_0:
            admit_power_of_0 = False
    return closed_forms, admit_power_of_0

def _extract_matrix(a, component):
    dim = a.shape[0]
    extended_component = component + [dim-1]
    new_dim = len(component) + 1
    new_m = sp.zeros(new_dim)
    new_m[-1, -1] = 1
    for map_i, i in enumerate(component):
        for map_j, j in enumerate(extended_component):
            new_m[map_i, map_j] = a[i, j]
    return new_m

def _extract_vec(v, component):
    new_v = sp.zeros(len(component)+1, 1)
    new_v[-1, 0] = 1
    for map_i, i in enumerate(component):
        new_v[map_i, 0] = v[i, 0]
    return new_v

def _connected_components(A):
    dim = A[0].shape[0]
    computed = set()
    components = []
    adjacency_m = _construct_adjacency(A)
    for i in range(dim-1):
        if i in computed: continue
        cur_component = {i}
        for j in range(dim-1):
            if j in computed: continue
            if adjacency_m[i, j] != 0:
                cur_component.add(j)
            if adjacency_m[j, i] != 0:
                cur_component.add(j)
        computed = computed.union(cur_component)
        components.append(sorted(list(cur_component)))
    #TODO a dummy connected components
    return [list(range(dim-1))]
    return components

def _construct_adjacency(A):
    dim = A[0].shape[0]
    res = sp.zeros(dim)
    for a in A:
        for i in range(dim-1):
            for j in range(dim-1):
                if a[i, j] != 0 or a[j, i] != 0:
                    res[i, j] = 1
    return res

def _closed_form(A, x0, pattern, n):
    dim = A[0].shape[0]
    num = len(pattern)
    m = _rearrange_matrix(A, pattern)
    shifted = sp.eye(m.shape[0])
    m_n = matrix_power(m, num)
    m_n = matrix_power(m_n, n)
    res = [m_n]
    shifted = m_n
    for i in range(1, num):
        shifted = matrix_mul(m, shifted)
        res.append(shifted)
    admit_power_of_0 = True
    if m_n.subs(n, 0) != sp.eye(m_n.shape[0]):
        admit_power_of_0 = False
        # cur_x = x0
        # for a in reversed(pattern):
        #     first_num_elements.append(cur_x)
        #     cur_x = A[a]*cur_x
    res = [S(i, num, dim)*t.subs(n, (n-i)/num, simultaneous=True)*extend_x0(x0, 0, num, dim) for i, t in enumerate(res)]
    return res, admit_power_of_0

def S(which, num, dim):
    l = [0]*which + [1] + [0]*(num - which - 1)
    return sp.Matrix([[i*sp.eye(dim) for i in l]])

def extend_x0(x0, which, num, dim):
    extended_x0 = x0.row_insert(0, sp.zeros(dim*(which), 1))
    extended_x0 = extended_x0.row_insert(len(extended_x0), sp.zeros(dim*(num-which-1), 1))
    # extended_x0 = x0.row_insert(len(x0), sp.zeros(dim*(num - 1), 1))
    return extended_x0

# def _selector(k, n):
#     '''Compute the closed form for sequence defined by
# f(0) = 1,
# f(1) = ... = f(k-1) = 0,
# f(n+k) = f(n)'''
#     f = sp.Function('f')
#     inits = {f(0): 1}
#     inits.update({f(i): 0 for i in range(1, k)})
#     return sp.rsolve(f(n+k) - f(n), f(n), inits)

def _rearrange_matrix(A, pattern):
    dim = A[0].shape[0]
    num = len(pattern)
    m = sp.Matrix([[sp.zeros(dim)]*(num - 1) + [A[pattern[0]]]])
    pattern = list(reversed(pattern))
    for i in range(num-1):
        l = [sp.zeros(dim)]*i + [A[pattern[i]]] + [sp.zeros(dim)]*(num - i - 1)
        m = m.row_insert(m.shape[0], sp.Matrix([l]))
    return m


if __name__ == '__main__':
    A = [sp.Matrix([[1, 2], [-1, 4]]),
         sp.Matrix([[3, 5], [-sp.Rational(6, 5), 8]]),
         sp.Matrix([[70, 3], [141, 7]])]
    A = [sp.Matrix([[1, 0, 1], [0, -1, 0], [0, 0, 1]]), sp.Matrix([[1, 0, 2], [0, -1, 0], [0, 0, 1]])]
    x0 = sp.Matrix([[0], [1], [1]])
    v = [sp.Matrix([[0, 1, 0]])]
    n = sp.Symbol('n')
    x1, x2, x3 = sp.symbols('x1 x2 x3')
    j, xj, close = closed_form(A, x0, [PolyCondition(x2)], [x1, x2, x3], n, 6)
    print(close)
