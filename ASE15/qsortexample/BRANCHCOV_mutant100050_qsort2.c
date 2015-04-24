int __covered0;
int __covered1;
int __covered2;
int __covered3;
int mutant_covered = 0;

int total_covered = 0;

#include "sort.h"

void quickSort( int a[], int l, int r)
{

  printf ("LOG: quicksort called with l=%d, r=%d\n", l, r); 
  int j;

  if ( l < r ) {
      if (!__covered0) {__covered0 = 1; total_covered += 1;}
      // divide and conquer
      j = partition( a, l, r);
      quickSort( a, l, j-1);
      quickSort( a, j+1, r);
    }
  
}



int partition( int a[], int l, int r) {
  int pivot, i, j, t;
  pivot = a[l];
  i = l;
  j = r+1;
  
  while(1)
    {
      do {
	if (!__covered1) {__covered1 = 1; total_covered += 1;}
	++i;
      } while( i <= r && a[i] <= pivot );
      do {
 mutant_covered = 1;
 if (!__covered2) {__covered2 = 1; total_covered += 1;}
 /* MUTANT (rep_op) */	++j;
      } while( a[j] > pivot );
      if ( i >= j ) {
	if (!__covered3) {__covered3 = 1; total_covered += 1;}
	break;
      }
      t = a[i];
      a[i] = a[j];
      a[j] = t;
    }
  t = a[l];
  a[l] = a[j];
  a[j] = t;
  return j;
}


void sort(int a[], unsigned int size) {
  quickSort(a, 0, size-1);
}
