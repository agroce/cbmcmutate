#include "sort.h"

void quickSort( int a[], int l, int r)
{

  printf ("LOG: quicksort called with l=%d, r=%d\n", l, r); 
  int j;

  if( l < r ) 
    {
      // divide and conquer
      j = partition( a, l, r);
      quickSort( a, l, j-1);
      quickSort( a, j+1, r);
    }
  
}



int partition( int a[], int l, int r) {
  int pivot, i, j, t;
  pivot = a[l];
  i = l; j = r+1;
  
  while( 1)
    {
 /* MUTANT (rep_op) */      do --i; while( i <= r && a[i] <= pivot );
      do --j; while( a[j] > pivot );
      if( i >= j ) break;
      t = a[i]; a[i] = a[j]; a[j] = t;
    }
  t = a[l]; a[l] = a[j]; a[j] = t;
  return j;
}


void sort(int a[], unsigned int size) {
  quickSort(a, 0, size-1);
}
