#include "sortarray.h"

int acc = -1;

index_t ind[MAX_ITEMS];
value_t val[MAX_ITEMS];

value_t a(index_t n) {
  /* printf ("LOG: acc = %d, looking up %u\n", acc, n); */
  int i;
  for (i = 0; i <= acc; i++) {
    if (ind[i] == n) {
      /* printf ("LOG: found %u with val %d\n", n, val[i]); */
      return val[i];
    }
  }
  value_t v = nondet_value();
  __CPROVER_assume(v >= 0);
  __CPROVER_assume(v < (MAX_ITEMS+1));
  for (i = 0; i <= acc; i++) {
    /* printf ("LOG: COMPARING to %d (a[%u] = %d)\n", i, ind[i], val[i]); */
    if (ind[i] < n) {
      __CPROVER_assume(v >= val[i]);
    } else {
      __CPROVER_assume(v <= val[i]);
    }
  }
  acc = acc + 1;
  assert(acc < MAX_ITEMS);
  /* printf("LOG: a[%u] = %d\n", n, v); */
  val[acc] = v;
  ind[acc] = n;
  return v;
}

