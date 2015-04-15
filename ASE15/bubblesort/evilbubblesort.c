#include "sort.h"

void mysort(int a[], unsigned int size) {
  int i, j, temp;
  for (i = 0; i < size; i++) {
    for (j = i; j < size; j++) {
      if (a[i] > a[j]) {
	printf ("LOG: swapping a[%d]=%d with a[%d]=%d\n", i, a[i], j, a[j]);
	temp = a[i];
	a[i] = a[j];
	a[j] = temp;
      }
    }
  }
  if (a[0] > 0) {
    a[0]--;
  }
}
