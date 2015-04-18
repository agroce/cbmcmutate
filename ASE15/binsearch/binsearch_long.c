#include "sortarray.h"

index_t binsearch(value_t key, index_t size, int* found) {
  long low = 0;
  long high = size - 1;
  
  while (low <= high) {
    long mid = ((unsigned long)low + (unsigned long)high) >> 1;
    value_t midVal = a(mid);

    if (midVal < key)
      low = mid + 1;
    else if (midVal > key)
      high = mid - 1;
    else {
      (*found) = 1;
      return mid; // key found
    }
  }
  (*found) = 0;
  return 0;  // key not found.
}
