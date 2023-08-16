#include "z3++.h"
#include <iostream>

int main() {
    z3::context c;
    z3::expr i = c.int_const("i");
    z3::expr x = c.int_const("x");
    z3::expr y = c.int_const("y");
    z3::expr xp = c.int_const("xp");
    z3::expr yp = c.int_const("yp");
    z3::expr ip = c.int_const("ip");

    z3::tactic t(c, "ctx-solver-simplify");
    z3::expr e = z3::ite(i % 2 == 0, x + 1, x) + z3::ite(i % 2 == 0, y, y + 1) == i;
    z3::goal g(c);
    z3::params p(c);
    // p.set("pull_cheap_ite", true);
    p.set("hoist_ite", true);
    // g.add(e);
    // std::cout << t(g) << std::endl;
    // std::cout << t.help() << std::endl;
    std::cout << e.simplify(p) << std::endl;

    // z3::solver s(c);

    // s.add(xp == z3::ite(i % 2 == 0, x + 1, x));
    // s.add(yp == z3::ite(i % 2 == 0, y, y + 1));
    // s.add(ip == i + 1);

    // s.check();
    // z3::model m = s.get_model();
    // z3::expr e = x + y;
    // z3::expr ep = xp + yp;
    // z3::expr k = c.int_const("k");
    // z3::expr b = c.int_const("b");
    // s.push();
    // s.add(m.eval(ep) == m.eval(e) + b);
    // s.check();
    // z3::model m2 = s.get_model();
    // // std::cout << m2 << std::endl;
    // // std::cout << "k == " << m2.eval(k) << std::endl;
    // std::cout << "b == " << m2.eval(b) << std::endl;
    // s.pop();
    // s.add(m.eval(ep) != m.eval(e) + m2.eval(b));
    // std::cout << s.check() << std::endl;

    // z3::solver s(c);
    // z3::expr conjecture = (x + y > 0);
    // s.add(conjecture);
    // if (s.check() == z3::sat) {
    //     std::cout << s.get_model() << std::endl;
    // }
}