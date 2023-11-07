from rec_solver.sym_rec_solver import pretty_solve_and_print, solve_file
# from rec_solver.PRS.mathematica_manipulation import session
import time
import z3
import fire


def main(filename):
    out_filename = "tmp/closed.smt2"
    closed = solve_file(filename)
    solver = z3.Solver()
    for k, e in closed.items():
        solver.add(k == e)
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
