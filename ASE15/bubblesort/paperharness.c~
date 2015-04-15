#include <stdio.h>
#include <stdlib.h>
#include "quicksort.h"

int a[MAX_ITEMS];
int ref[MAX_ITEMS];

int nondet_int();

int main () {
  int i, v, count, qcount, prev;
  int s = nondet_int();
  __CPROVER_assume((s > 0) && (s <=MAX_ITEMS));
  for (i = 0; i < s; i++) {
    v = nondet_int();
    printf ("LOG: ref[%d] = %d\n", i, v);
    ref[i] = v;
    a[i] = v;
  }
  quick_sort(a, s);
  v = nondet_int();
  count = 0;
  qcount = 0;
  prev = a[0];
  printf ("LOG: checking %d\n", v);
  for (i = 0; i < s; i++) {
    printf ("LOG: a[%d] = %d\n", i, a[i]);
    if (ref[i] == v) {
      count++;
    }
    if (a[i] == v) {
      qcount++;
    }
    assert (a[i] >= prev);
    prev = a[i];
  }
  printf ("LOG: ref count = %d\n",count);
  printf("LOG: sorted count = %d\n", qcount);
  assert (count == qcount);
}
