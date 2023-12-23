import sympy as sp
from sympy.core import symbol
from sympy.utilities.iterables import strongly_connected_components
from .condition import And, PolyCondition, ModCondition, TrueCondition, NondetCondition
from .closed_form import closed_form, symbolic_closed_form_linear, solve_rec_expr
# from .old_parser import parse
from .parser import parse
import os
import time

def is_linear_transition(transition):
    variables = transition.keys()
    for _, exp in transition.items():
        for v1 in variables:
            for v2 in variables:
                diff_v = sp.diff(exp, v1, v2)
                if sp.simplify(diff_v) != 0:
                    return False
    return True

def is_poly_transition(transition):
    for _, exp in transition.items():
        free_symbols = exp.free_symbols
        if not exp.is_polynomial(free_symbols):
            return False
    return True


def trans2matrix(transition, var_order):
    matrix = sp.eye(len(var_order))
    for i, v in enumerate(var_order):
        matrix[i, :] = exp2vec(transition[v], var_order)
    return matrix

def exp2vec(exp, var_order):
    cur_exp = exp
    vec = sp.zeros(1, len(var_order))
    for i, v in enumerate(var_order[:-1]):
        coeff = cur_exp.coeff(v)
        vec[i] = coeff
        cur_exp = cur_exp - coeff*v
    const_dummy = sp.Symbol('constant')
    vec[-1] = cur_exp if cur_exp != const_dummy else 1
    return vec

def solve(filename):
    with open(filename) as fp:
        recurrence = fp.read()
        res = solve_str(recurrence)
        return res


def solve_str(recurrence: str):
    cond, x0, A, variables, index = parse(recurrence)
    start = time.time()
    res = closed_form(A, x0, cond, variables, index, bnd=999999999999)
    # print(sp.expand(res[1][0].subs(index, 5)))
    # for i in range(6, 12):
    #     print(sp.expand(res[1][1].subs(index, i)))
    end = time.time()
    if res is None:
        return None
    return res, variables, index, end - start

def solve_sym_str(recurrence: str):
    cond, x0, str_transitions, variables, index = parse(recurrence)
    if any([c is NondetCondition for c in cond]):
        raise Exception('Contains Nondterministic Branches')
    sp_transitions = [{sp.Symbol(v): e for v, e in trans.items()} for trans in str_transitions]
    initial_symbols = []
    for i, v in enumerate(x0):
        if v.is_symbol and v.name != 'constant':
            initial_symbols.append(v)
    if all(is_linear_transition(trans) for trans in sp_transitions):
        A = [trans2matrix(tran, variables) for tran in sp_transitions]
        res = symbolic_closed_form_linear(A, x0, cond, variables, index, bnd=99999999)
    elif cond[0] == sp.true or isinstance(cond[0], TrueCondition): # if there are non-linear transition while the recurrence is non-conditional
        transition = sp_transitions[0]
        layered_transition = transition_layers(transition, index)
        assert(all([len(x) == 1 for x in layered_transition]))
        closed_form = {}
        for trans in layered_transition:
            v = list(trans.keys())[0]
            f = sp.Function('f')
            rec = f(index + 1) - (trans[v].subs({v: f(index)} | closed_form))
            init_value = x0[variables.index(v)]
            closed = sp.rsolve(rec, f(index), {f(0): init_value})
            closed_form[v] = closed
        m = sp.zeros(len(variables), 1)
        const_dummy = sp.Symbol('constant')
        for i, v in enumerate(variables):
            if v != const_dummy:
                m[i] = closed_form[v]
            else:
                m[i] = 1
        res = ([0], [[m]])
    return res, variables, initial_symbols

def transition_layers(transition, index):
    const_dummy = sp.Symbol('constant')
    dependencies = {v: set(transition[v].free_symbols) - {const_dummy, index} for v in transition if v is not const_dummy}
    V = list(set(transition.keys()) - {const_dummy})
    E = []
    for v1, neighbors in dependencies.items():
        for v2 in neighbors:
            E.append((v1, v2))
    components = strongly_connected_components((V, E))
    ret = []
    for c in components:
        ret.append({v: transition[v] for v in c})
    return ret

def solve_recurrence_expr(recurrence):
    conds, x0, str_transitions, variables, index = parse(recurrence)
    sp_transitions = [{sp.Symbol(v): e for v, e in trans.items()} for trans in str_transitions]
    # if all(is_linear_transition(trans) for trans in sp_transitions):
    #     A = [trans2matrix(tran, variables) for tran in sp_transitions]
    if all(is_poly_transition(trans) for trans in sp_transitions):
        return solve_rec_expr(sp_transitions, x0, conds, variables, index)
    else:
        raise Exception('Non-poly Case Not Yet Implemented')

def solve_sym(filename):
    with open(filename) as fp:
        recurrence = fp.read()
        try:
            res = solve_sym_str(recurrence)
        except:
            res = solve_recurrence_expr(recurrence)
        return res