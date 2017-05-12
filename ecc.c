#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

#define N 5

typedef bool CODE[N];

//codes 0 and 1 are initialized in main below
CODE code0;
CODE code1;

CODE* encode(bool b) {
  if (b) return &code1;
  else return &code0;
}

//Hamming distance between c and d
int hamming(CODE c, CODE d) {
  int sum = 0;
  for (int i=0; i < N; i++) {
    sum += c[i]^d[i];
  }
  return sum;
}

bool decode(CODE c) {
  int d0 = hamming(code0, c);
  int d1 = hamming(code1, c);

  if (d0 < d1) { return 0; }
  else if (d0 > d1) { return 1; }
  else assert(0); //decoding failed
}

bool nondet_bit(void); //nondeterministically generate a bit
unsigned int nondet_uint(void); //nondeterministically generate an unsigned int

//channel model
CODE channel;
CODE* syndrome(CODE c) {
  //copy code c into channel
  for (int i = 0; i < N; i++) {
    channel[i] = c[i];
  }
  //apply syndrome
  for (int n = 1; n <= N/2; n++) {
    unsigned int i = nondet_uint();
    assume (i < N);
    channel[i] = nondet_bit();
  }
  return &channel;
}

int main(void) {
  //initialize codes 0 and 1
  for (int i = 0; i < N; i++) {
    code0[i] = 0;
    code1[i] = 1;
  }
  //\forall b, decode(*syndrome(*encode(b))) == b
  bool b1 = nondet_bit();
  bool b2 = decode(*syndrome(*encode(b1)));
  assert (b1 == b2);
}


