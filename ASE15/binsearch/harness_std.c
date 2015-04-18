#include "sortarray.h"
#include "binsearch_std.h"

int main () {
  index_t s = nondet_index();
  __CPROVER_assume(s > 0);
  value_t k = nondet_value();
  long bret = binsearch(k, s);
  if (bret != -1)
    assert (a(bret) == k);
  else {
    index_t i = nondet_index();
    __CPROVER_assume ((i < s) && (i >= 0));
    assert (a(i) != k);
  }
}
