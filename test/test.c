#include <stdbool.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "brs2.c", 10, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(bool cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned int size);

#define N 10000
	// int a[N];
	// int b[N];
	// int c[N];
	// int d[N];
int main()
{
	int a[N];
	for (int i = 0; i != N; i++) {
		a[i] = i;
	}
	for (int i = 0; i != N; i++) {
		__VERIFIER_assert(a[i] == i);
	}
	// N = __VERIFIER_nondet_int();
	// if(N <= 0) return 1;
	// assume_abort_if_not(N <= 2147483647/sizeof(int));

	// int i;
	// long long sum[1];
	// int *a = malloc(sizeof(int)*N);
	// int *b = malloc(sizeof(int)*N);

	return 1;
}