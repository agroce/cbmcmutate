#include "sortarray.h"
#include "binsearch.h"

int main () {
  index_t s = nondet_index();
  __CPROVER_assume(s > 0);
  value_t k = nondet_value();
  int found;
  index_t bret = binsearch(k, s, &found);
  if (found == 1)
    assert (a(bret) == k);
  else {
    assert (found == 0);
    assert (bret == 0);
    index_t i = nondet_index();
    __CPROVER_assume ((i < s) && (i >= 0));
    assert (a(i) != k);
  }
}
