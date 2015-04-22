#include "merge_sorted_nodups.h"

int merge_sorted_nodups(int a[], int asize, int b[], int bsize, int c[]) {
  int apos = 0, bpos = 0, cpos = -1, csize = 0;
  while ((apos < asize) || (bpos < bsize)) {
    if ((apos < asize) && ((bpos >= bsize) || (a[apos] < b[bpos]))) {
 /* MUTANT (rep_const) */      if ((cpos == 0) || (c[cpos] != a[apos])) {
	c[++cpos] = a[apos];
	csize++;
      }
      apos++;
    } else {
      if ((cpos == -1) || (c[cpos] != b[bpos])) {
	c[++cpos] = b[bpos];
	csize++;
      }
      bpos++;      
    }
  }
  return csize;
}
