#include <stdio.h>
#include <stdlib.h>
#include "sort.h"

int a[SIZE];
int ref[SIZE];

int nondet_int();

int main () {
  int i, v, count, qcount, prev;
  int s = nondet_int();
  __CPROVER_assume((s > 0) && (s <=SIZE));
  for (i = 0; i < s; i++) {
    v = nondet_int();
    ref[i] = v;
    a[i] = v;
  }
  sort(a, s);
  v = nondet_int();
  count = 0;
  qcount = 0;
 /* MUTANT (rep_const) */  prev = a[-1];
  for (i = 0; i < s; i++) {
    if (ref[i] == v) {
      count++;
    }
    if (a[i] == v) {
      qcount++;
    }
    assert (a[i] >= prev);
    prev = a[i];
  }
  assert (count == qcount);
}
