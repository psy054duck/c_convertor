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
#define S 1

int main()
{
  // int N = __VERIFIER_nondet_uint();
  int N = S;
  int a[N];
  int i = 0;
  int x = 0;
  int x0 = x;
  for (i = 0; i < S; i++) {
    a[i] = i + 1;
    a[i] = i;
  }
  // a[0] = 2;
  // assert(a[0] == 2);
  for (i = 0; i < S; i++) {
    assert(a[i] == i + 1);
  }
  // assert(a[i-1] == i-1);
  // assert(a[S - 1] == S );
  // for (i = 0; i < S; i++) {
  //   if (i < 50)
  //     x++;
  //   else
  //     x+=2;
  // }
  // // assert(x == x0 + 150);
  // // assert(x == x0 + 151);
  // x = x0;
  // for (i = 0; i < S; i++) {
  //   x++;
  //   // assert(x == i + 1);
  // }
  // for (i = 0; i < S; i++) {
  //   a[i] = i + 1;
  // }
  // assert(a[0] == 1);
  // assert(a[i - 1] == i - 1);
  // for (int i = 0; i < S; i++) {
  //   assert(a[i] == i );
  // }
  // assert(i == S + 1);
	return 0;
}
