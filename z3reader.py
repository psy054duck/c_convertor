import z3

def main():
    f = z3.parse_smt2_file('tmp/tmp0_path_0.smt2')
    solver = z3.Solver()
    solver.add(f)
    # print(solver)
    for e in solver.assertions():
        print(z3.simplify(e))
    print(solver.check())
    print(solver.model())


if __name__ == '__main__':
    main()