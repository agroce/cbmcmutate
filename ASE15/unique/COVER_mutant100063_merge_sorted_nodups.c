int mutant_covered = 0;

#include "merge_sorted_nodups.h"

int merge_sorted_nodups(int a[], int asize, int b[], int bsize, int c[]) {
  int apos = 0;
  int bpos = 0;
  int cpos = -1;
  int csize = 0;
  while ((apos < asize) || (bpos < bsize)) {
    printf ("LOG: apos = %d, bpos = %d, cpos = %d\n", apos, bpos, cpos);
    if ((apos < asize) && ((bpos >= bsize) || (a[apos] < b[bpos]))) {
      if ((cpos == -1) || (c[cpos] != a[apos])) {
	printf ("LOG: PUTTING a[%d]=%d in c\n", apos, a[apos]);
	c[++cpos] = a[apos];
	csize++;
      }
      apos++;
    } else {
  mutant_covered = 1;
 /* MUTANT (rep_const) */      if ((cpos == 1) || (c[cpos] != b[bpos])) {
	printf ("LOG: PUTTING b[%d]=%d in c\n", bpos, b[bpos]);
	c[++cpos] = b[bpos];
	csize++;
      }
      bpos++;      
    }
  }
  return csize;
}
