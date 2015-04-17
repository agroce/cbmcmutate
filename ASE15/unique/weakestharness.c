#include "merge_sorted_nodups.h"

int nondet_int();

int main () {
  int a[SIZE];
  int b[SIZE];

  int i, v;

  int asize = nondet_int();
  int bsize = nondet_int();
  __CPROVER_assume (asize >= 0);
  __CPROVER_assume (bsize >= 0);
  __CPROVER_assume (asize <= SIZE);
  __CPROVER_assume (bsize <= SIZE);

  printf ("LOG: asize = %d, bsize = %d\n", asize, bsize);

  for (i = 0; i < asize; i++) {
    v = nondet_int();
    __CPROVER_assume((i == 0) || (v >= a[i-1]));
    printf ("LOG: a[%d] = %d\n", i, v);
    a[i] = v;
  }

  for (i = 0; i < bsize; i++) {
    v = nondet_int();
    __CPROVER_assume((i == 0) || (v >= b[i-1]));
    printf ("LOG: b[%d] = %d\n", i, v);
    b[i] = v;
  }

  int c[SIZE*2];
  int csize;

  csize = merge_sorted_nodups(a, asize, b, bsize, c);

  printf ("LOG: csize = %d\n", csize);

  assert (csize <= (asize + bsize));
  //assert (((asize == 0) && (bsize == 0)) || (csize >= 1));

  int i1, i2;

  i1 = nondet_int();
  i2 = nondet_int();
  __CPROVER_assume(i1 >= 0);
  __CPROVER_assume(i2 >= 0);
  __CPROVER_assume(i1 < csize);
  __CPROVER_assume(i2 < csize);
  __CPROVER_assume(i1 != i2);

  printf ("LOG: c[%d] = %d, c[%d] = %d\n", i1, c[i1], i2, c[i2]);

  assert(c[i1] != c[i2]);

  v = nondet_int();
  __CPROVER_assume (v >= 0);
  __CPROVER_assume (v < asize);

  v = a[v];
  int found = 0;
  for (i = 0; i < csize; i++) {
    if (c[i] == v) {
      found = 1;
      break;
    }
  }
  assert (found == 1);

  v = nondet_int();
  __CPROVER_assume (v >= 0);
  __CPROVER_assume (v < bsize);

  v = b[v];
  found = 0;
  for (i = 0; i < csize; i++) {
    if (c[i] == v) {
      found = 1;
      break;
    }
  }
  assert (found == 1);
}
