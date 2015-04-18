#include "limits.h"
#include "stdlib.h"
#include "stdio.h"

typedef short value_t;

int main () {
  value_t* a;
  long size = 2;
  int done = 0;
  printf ("size of data type = %u\n", sizeof(value_t));
  while (!done) {
    size = (size * 1.5);
    a = malloc(size * sizeof(value_t));
    if (a != 0) {
      printf ("malloc of size %ld ok\n", size);
      if (size > INT_MAX) {
	printf ("bigger than INT_MAX (%d)!\n", INT_MAX);
      }
      if (size > UINT_MAX) {
	printf ("bigger than UINT_MAX (%u)!\n", UINT_MAX);
      }
      free(a);
    } else {
      printf ("malloc of size %ld failed\n", size);
      done = 1;
    }
  }
}
