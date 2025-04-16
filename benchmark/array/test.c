extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "Addition01-2.c", 3, "reach_error"); }

/*
 * Recursive implementation integer addition.
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */

void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        {reach_error();}
    }
    return;
}
extern int __VERIFIER_nondet_int(void);

#define N 10000
int a[N];
int main() {
    for (int i = 0; i < N; i++) {
        a[i] = i + 1;
    }
    for (int i = 0; i < N; i++) {
        __VERIFIER_assert(a[i] > i);
    }
}
