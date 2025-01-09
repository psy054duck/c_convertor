from PRS.prs_solver import solve
from PRS.mathematica_manipulation import session
import fire
import utils

def main(filename):
    closed_form, var_order, index, _= solve(filename)
    for var in var_order[:-1]:
        lcm, rhs = utils.closed_form2z3(closed_form, var_order, var, index)
        if lcm != 1:
            print('%s(n) == (%s)/%d' % (var, rhs, lcm))
        else:
            print('%s(n) == %s' % (var, rhs))
    session.terminate()

if __name__ == '__main__':
    fire.Fire(main)