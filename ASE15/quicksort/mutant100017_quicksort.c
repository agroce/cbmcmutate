#include "quicksort.h"

void quick_sort (int *a, int n) {
    int i, j, p, t;
    if (n < 2)
        return;
 /* MUTANT (rep_const) */    p = a[n / ((2)-1)];
    for (i = 0, j = n - 1;; i++, j--) {
        while (a[i] < p)
            i++;
        while (p < a[j])
            j--;
        if (i >= j)
            break;
        t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
    quick_sort(a, i);
    quick_sort(a + i, n - i);
}
