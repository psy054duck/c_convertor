// extern void abort(void);
// extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
// void reach_error() { __assert_fail("0", "count_up_down-1.c", 3, "reach_error"); }
// 
// void __VERIFIER_assert(int cond) {
//   if (!(cond)) {
//     ERROR: {reach_error();abort();}
//   }
//   return;
// }
#include <stdbool.h>
extern unsigned int __VERIFIER_nondet_uint(void);
extern int __VERIFIER_nondet_int(void);
extern void assert(bool);
#define __VERIFIER_assert(x) assert(x)
#define S 1000

int main() {
  int a[S] = {};
  for (int i = 0; i < S; i++) {
    a[i] = i;
  }
  for (int i = 0; i < S; i++) {
    assert(a[i] == i);
  }
}