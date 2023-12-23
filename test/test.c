#include <stdbool.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "brs2.c", 10, "reach_error"); }
extern void abort(void);
// void assume_abort_if_not(bool cond);
 void assume_abort_if_not(int cond) {
   if(!cond) {abort();}
 }
// void __VERIFIER_assert(bool cond) __attribute__((const)) { if(!(cond)) { ERROR: {reach_error();abort();} } }
void __VERIFIER_assert(bool cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int(void);
extern int __VERIFIER_nondet_uint(void);

int f(int z) {
  return z + 2;
}

int main() {
    unsigned a, b;
    unsigned x, y, u, v;
    a = __VERIFIER_nondet_uint();
    b = __VERIFIER_nondet_uint();
    assume_abort_if_not(a >= 1);  //infinite loop if remove
    assume_abort_if_not(b >= 1);

    assume_abort_if_not(a <= 65535);
    assume_abort_if_not(b <= 65535);

    x = a;
    y = b;
    u = b;
    v = 0;

    while (1) {
        if (!(x != y))
            break;

        while (1) {
            if (!(x > y))
                break;
            x = x - y;
            v = v + u;
        }

        while (1) {
            if (!(x < y))
                break;
            y = y - x;
            u = u + v;
        }
    }

    // __VERIFIER_assert(u*y + v*y == a*b);
    __VERIFIER_assert(x == y);

    //x == gcd(a,b)
    //u + v == lcm(a,b)
    return 0;
}
