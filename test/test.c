#include <stdbool.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "brs2.c", 10, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(bool cond) __attribute__((const)) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned int size);

#define N 10000
	// int a[N];
	// int b[N];
	// int c[N];
	// int d[N];
struct _S
{
 int n;
};
typedef struct _S S;
int main()
{
S a[N];
S b[N];
S c[N];
 int i;
 // for(i = 0; i < 1000000; i++)
 // {
 //  int v;
 //         v = __VERIFIER_nondet_int();
 //  a[i].n= v;
 //  v = __VERIFIER_nondet_int();
 //  b[i].n = v;
 // }
 for(int i = 0; i < N; i++)
 {
  c[i].n = a[i].n + b[i].n;
  // c[i] = a[i] + b[i];
 }
 for(int i = 0; i < N; i++)
 {
  __VERIFIER_assert(c[i].n == a[i].n + b[i].n);
  // __VERIFIER_assert(c[i] == a[i] + b[i]);
 }
 return 0;
}