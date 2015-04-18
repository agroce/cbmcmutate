#include "sortarray.h"

int nondet_int();

int main() {
  int i;
  index_t tind[MAX_ITEMS];
  value_t tval[MAX_ITEMS];
  for (i = 0; i < MAX_ITEMS; i++) {
    tind[i] = nondet_index();
    tval[i] = a(tind[i]);
  }
  int v1 = nondet_int();
  int v2 = nondet_int();
  __CPROVER_assume((v1 >= 0) && (v1 < MAX_ITEMS));
  __CPROVER_assume((v2 >= 0) && (v2 < MAX_ITEMS));
  if (tind[v1] <= tind[v2]) {
    assert (tval[v1] <= tval[v2]);
  } else {
    assert (tval[v1] >= tval[v2]);
  }
  assert (a(tind[v1]) == tval[v1]);
  assert (a(tind[v2]) == tval[v2]);
}
