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
	int i;
	int sum[1];
	// int *a = malloc(sizeof(int)*N);
	// int *b = malloc(sizeof(int)*N);
	int a[N];
	int b[N];

	sum[0] = 0;
	for(i=0; i<N; i++)
	{
		a[i] = 1;
	}

	for(i=0; i<N; i++)
	{
		b[i] = 1;
	}

	for(i=0; i<N; i++)
	{
		sum[0] = sum[0] + a[i];
	}

	for(i=0; i<N; i++)
	{
		sum[0] = sum[0] + b[i];
	}

	__VERIFIER_assert(sum[0] <= 2*N);
	return 1;
}