#include "merge_sorted_nodups.h"

int nondet_int();

int mutant_covered = 0;

int main () {
  int a[SIZE];
  int b[SIZE];

  int i, j, v;

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

  __CPROVER_assume (csize <= (asize + bsize));
  __CPROVER_assume (((asize == 0) && (bsize == 0)) || (csize >= 1));

  int i1, i2;

  for (i1 = 0; i1 < csize; i1++) {
    for (i2 = 0; i2 < csize; i2++) {

      printf ("LOG: c[%d] = %d, c[%d] = %d\n", i1, c[i1], i2, c[i2]);
      
      __CPROVER_assume((i1 == i2) || (c[i1] != c[i2]));
      __CPROVER_assume(!(i1 < i2) || (c[i1] <= c[i2]));
    }
  }

  int found;
  
  for (j = 0; j < asize; j++) {

    v = a[j];
    
    printf ("LOG: a check: v = %d\n", v);
    
    found = 0;
    for (i = 0; i < csize; i++) {
      if (c[i] == v) {
	found = 1;
	break;
      }
    }
    __CPROVER_assume (found == 1);
  }
    
  for (j = 0; j < bsize; j++) {
    v = b[j];

    printf ("LOG: b check: v = %d\n", v);

    found = 0;
    for (i = 0; i < csize; i++) {
      if (c[i] == v) {
	found = 1;
	break;
      }
    }
    __CPROVER_assume (found == 1);
  }

  for (j = 0; j < csize; j++) {

    v = c[j];
    
    printf ("LOG: c check: v = %d\n", v);
    
    
    found = 0;
    for (i = 0; i < asize; i++) {
      if (a[i] == v) {
	found = 1;
	break;
      }
    }
    
    for (i = 0; (!found) && (i < bsize); i++) {
      if (b[i] == v) {
	found = 1;
	break;
      }
    }
    __CPROVER_assume (found == 1);
  }
  assert (!mutant_covered);
}
