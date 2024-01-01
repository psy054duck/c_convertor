import z3
import fire

DEBUG = False

def add_lemma(solver):
    dummy1, dummy2 = z3.Ints('dummy1 dummy2')
    dummies = [dummy1, dummy2]
    solver.add(z3.ForAll(dummies, z3.Implies(z3.Or(dummy1 == dummy2, dummy1 == 0), dummy1*dummy2 == dummy1*dummy1)))
    solver.add(z3.ForAll(dummies, z3.Implies(z3.And(z3.Not(z3.And(dummy2 >= 1, dummy1 - dummy2 <= -2)), dummy2 >= 0, z3.Not(dummy2 <= dummy1)), z3.Or(dummy2 == dummy1 + 1, dummy1 < 0))))
    body = dummy1*(1 + 2*dummy1*dummy1 + 3*dummy1)
    solver.add(z3.ForAll(dummies, 6*(body/6) == body))
    body = dummy1*dummy1*(1 + dummy1*dummy1 + 2*dummy1)
    solver.add(z3.ForAll(dummies, 4*(body/4) == body))
    body = -1*dummy1 + 6*dummy1*dummy1*dummy1*dummy1*dummy1 + 10*dummy1*dummy1*dummy1 + 15*dummy1*dummy1*dummy1*dummy1
    solver.add(z3.ForAll(dummies, 30*(body/30) == body))
    body = -1*dummy1*dummy1+ 2*dummy1*dummy1*dummy1*dummy1*dummy1*dummy1 + 5*dummy1*dummy1*dummy1*dummy1 + 6*dummy1*dummy1*dummy1*dummy1*dummy1
    solver.add(z3.ForAll(dummies, 12*(body/12) == body))
    body = dummy1*(1 + dummy1)
    solver.add(z3.ForAll(dummies, 2*(body/2) == body))

def main(filename, timeout):
    f = z3.parse_smt2_file(filename)
    # solver = z3.Then('ctx-solver-simplify', 'smt').solver()
    basic_solver = z3.Solver()
    lemma_solver = z3.Solver()
    basic_solver.set('timeout', int(timeout)//2)
    lemma_solver.set('timeout', int(timeout)//2)
    basic_solver.add(f)
    lemma_solver.add(f)
    add_lemma(lemma_solver)
    # print(solver)
    # solver.add(z3.Int('N_0_0') == z3.Int('i'))
    if DEBUG:
        for e in basic_solver.assertions():
            print(z3.simplify(e))
    # print(solver.check())
    # print(solver.model())
    res = basic_solver.check()
    if DEBUG:
        print(res)
    if res == z3.unknown:
        res = lemma_solver.check()
    if DEBUG:
        print(res)

    if res == z3.sat:
        exit(-1)
    elif res == z3.unsat:
        exit(0)
    else:
        exit(1)


if __name__ == '__main__':
    fire.Fire(main)