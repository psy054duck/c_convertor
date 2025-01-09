# from old_rec_solver.sym_rec_solver import pretty_solve_and_print, solve_file
# from rec_solver.PRS.mathematica_manipulation import session
import time
import z3
import fire
import sys
from functools import reduce
from sympy.core.function import AppliedUndef
sys.path.append('./rec_solver')
from rec_solver import solve_file
from rec_solver.core.closed_form import MultiFuncClosedForm, ExprClosedForm, SymbolicClosedForm, PiecewiseClosedForm
from rec_solver.core.utils import to_z3

def main(filename, inv_var):
    out_filename = "tmp/closed.smt2"
    closed = solve_file(filename)
    solver = z3.Solver()
    closed_dict = closed.sympify()
    apps = reduce(set.union, [k.atoms(AppliedUndef) | v.atoms(AppliedUndef) for k, v in closed_dict.items()])
    remove_func_mapping = {f: f.name for f in apps}
    new_closed_dict = {k.subs(remove_func_mapping, simultaneous=True): v.subs(remove_func_mapping, simultaneous=True) for k, v in closed_dict.items()}
    for k, e in new_closed_dict.items():
        solver.add(to_z3(k) == to_z3(e))
    with open(out_filename, 'w') as fp:
        fp.write(solver.to_smt2())
    # print(closed.to_z3())

if __name__ == '__main__':
    fire.Fire(main)
    # fire.Fire(pretty_solve_and_print)
    # pretty_solve_and_print('rec_solver/test.txt')
    # pretty_solve_and_print('examples_rec/test3.txt')
    # pretty_solve_and_print('temp/rec.txt')
    # pretty_solve_and_print('temp/copy_some.txt')
    # pretty_solve_and_print('temp/test4.txt')
    # pretty_solve_and_print('temp/test6.txt')
    # session.terminate()
