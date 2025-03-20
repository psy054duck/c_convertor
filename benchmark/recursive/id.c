extern unsigned int __VERIFIER_nondet_uint(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "id_o100.c", 4, "reach_error"); }

unsigned int id(unsigned int x) {
  if (x<=0) return 0;
  return id(x-1) + 1;
}
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        {reach_error();}
    }
    return;
}

int main(void) {
  unsigned int input = __VERIFIER_nondet_uint();
  unsigned int result = id(input);
  __VERIFIER_assert(result == input);
}

