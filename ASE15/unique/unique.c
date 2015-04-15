int nondet_int();

int main () {
  int a[SIZE];
  int i, j, v;

  for (i = 0; i < SIZE; i++) {
    v = nondet_int();
    printf ("LOG: a[%d] = %d\n", i, v);
    a[i] = v;
  }
  
  for (i = 0; i < SIZE; i++) {
    for (j = i+1; j < SIZE; j++) {
      __CPROVER_assume(a[i] != a[j]);
    }
  }

  assert(0);
  // Make sure a is unique values at this point
  //code_needing_unique();
}
