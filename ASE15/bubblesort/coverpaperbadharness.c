#include <stdio.h>
#include <stdlib.h>
#include "sort.h"

int mutant_covered;

int a[MAX_ITEMS];
int ref[MAX_ITEMS];

int nondet_int();

int main () {
  int i, v, prev;
  int s = nondet_int();
  __CPROVER_assume((s > 0) && (s <=MAX_ITEMS));
  for (i = 0; i < s; i++) {
    v = nondet_int();
    printf ("LOG: ref[%d] = %d\n", i, v);
    ref[i] = v;
    a[i] = v;
  }
  sort(a, s);
  prev = a[0];
  printf ("LOG: checking %d\n", v);
  for (i = 0; i < s; i++) {
    printf ("LOG: a[%d] = %d\n", i, a[i]);
    assert (a[i] >= prev);
    prev = a[i];
  }
  assert (!mutant_covered);
}
