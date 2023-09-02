import sympy as sp
from sympy.core import symbol
from .condition import And, PolyCondition, ModCondition
from .closed_form import closed_form, symbolic_closed_form
from .parser import parse
import os
import time

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
    cond, x0, A, variables, index = parse(recurrence)
    initial_symbols = []
    for i, v in enumerate(x0):
        if v.is_symbol and v.name != 'constant':
            initial_symbols.append(v)
    res = symbolic_closed_form(A, x0, cond, variables, index, bnd=99999999)
    return res, variables, initial_symbols

def solve_sym(filename):
    with open(filename) as fp:
        recurrence = fp.read()
        res = solve_sym_str(recurrence)
        return res