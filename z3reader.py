import z3
import fire

def main(filename):
    f = z3.parse_smt2_file(filename)
    # solver = z3.Then('ctx-solver-simplify', 'smt').solver()
    solver = z3.Solver()
    solver.add(f)
    # print(solver)
    # solver.add(z3.Int('N_0_0') == z3.Int('i'))
    # for e in solver.assertions():
    #     print(z3.simplify(e))
    # print(solver.check())
    # print(solver.model())
    res = solver.check()
    # print(res)
    if res == z3.sat:
        exit(-1)
    elif res == z3.unsat:
        exit(0)
    else:
        exit(1)


if __name__ == '__main__':
    fire.Fire(main)