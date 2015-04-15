#include "merge_sorted_nodups_cov.h"

int cov0 = 0;
int cov1 = 0;
int cov2 = 0;
int cov3 = 0;
int cov4 = 0;
int cov5 = 0;
int cov6 = 0;

int merge_sorted_nodups(int a[], int asize, int b[], int bsize, int c[]) {
  int apos = 0;
  int bpos = 0;
  int cpos = -1;
  int csize = 0;
  while ((apos < asize) || (bpos < bsize)) {
    if (!cov0) {
      cov0 = 1;
      total++;
    }
    printf ("LOG: apos = %d, bpos = %d, cpos = %d\n", apos, bpos, cpos);
    if ((apos < asize) && ((bpos >= bsize) || (a[apos] < b[bpos]))) {
      if (!cov1) {
	cov1 = 1;
	total++;
      }
      if ((cpos == -1) || (c[cpos] != a[apos])) {
	if (!cov2) {
	  cov2 = 1;
	  total++;
	}
	printf ("LOG: PUTTING a[%d]=%d in c\n", apos, a[apos]);
	c[++cpos] = a[apos];
	csize++;
      } else {
	if (!cov3) {
	  cov3 = 1;
	  total++;
	}
      }
      apos++;
    } else {
      if (!cov4) {
	cov4 = 1;
	total++;
      }
      if ((cpos == -1) || (c[cpos] != b[bpos])) {
	if (!cov5) {
	  cov5 = 1;
	  total++;
	}
	printf ("LOG: PUTTING b[%d]=%d in c\n", bpos, b[bpos]);
	c[++cpos] = b[bpos];
	csize++;
      } else {
	if (!cov6) {
	  cov6 = 1;
	  total++;
	}
      }
      bpos++;      
    }
  }
  return csize;
}
