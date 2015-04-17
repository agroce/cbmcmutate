int mutant_covered = 0;

int total_covered = 0;

int covered[17];

#include "merge_sorted_nodups.h"

int merge_sorted_nodups(int a[], int asize, int b[], int bsize, int c[]) {
  if (!covered[0]) {covered[0] = 1; total_covered += 1;}
  int apos = 0;
  if (!covered[1]) {covered[1] = 1; total_covered += 1;}
  int bpos = 0;
  if (!covered[2]) {covered[2] = 1; total_covered += 1;}
  int cpos = -1;
  if (!covered[3]) {covered[3] = 1; total_covered += 1;}
  int csize = 0;
 mutant_covered = 1;
 if (!covered[4]) {covered[4] = 1; total_covered += 1;}
 /* MUTANT (rep_op) */  while ((apos < asize) || (bpos > bsize)) {
    if (!covered[5]) {covered[5] = 1; total_covered += 1;}
    printf ("LOG: apos = %d, bpos = %d, cpos = %d\n", apos, bpos, cpos);
    if (!covered[6]) {covered[6] = 1; total_covered += 1;}
    if ((apos < asize) && ((bpos >= bsize) || (a[apos] < b[bpos]))) {
      if (!covered[7]) {covered[7] = 1; total_covered += 1;}
      if ((cpos == -1) || (c[cpos] != a[apos])) {
	printf ("LOG: PUTTING a[%d]=%d in c\n", apos, a[apos]);
	c[++cpos] = a[apos];
	csize++;
      if (!covered[8]) {covered[8] = 1; total_covered += 1;}
      }
      if (!covered[9]) {covered[9] = 1; total_covered += 1;}
      apos++;
    if (!covered[10]) {covered[10] = 1; total_covered += 1;}
    } else {
      if (!covered[11]) {covered[11] = 1; total_covered += 1;}
      if ((cpos == -1) || (c[cpos] != b[bpos])) {
	printf ("LOG: PUTTING b[%d]=%d in c\n", bpos, b[bpos]);
	c[++cpos] = b[bpos];
	csize++;
      if (!covered[12]) {covered[12] = 1; total_covered += 1;}
      }
      if (!covered[13]) {covered[13] = 1; total_covered += 1;}
      bpos++;      
    if (!covered[14]) {covered[14] = 1; total_covered += 1;}
    }
  if (!covered[15]) {covered[15] = 1; total_covered += 1;}
  }
  if (!covered[16]) {covered[16] = 1; total_covered += 1;}
  return csize;
}
