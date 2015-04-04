#include <stdio.h>
#include <stdlib.h>
#include "avltree.h"

int nondet_int();

int main(void)
{
  int v, i, c, b;
  int present = 0;

  int val = nondet_int();

  printf("searching for %d\n", val);

  struct node* root = nnil;

  for (i = 0; i < MAX_ITEMS; i++) {
    v = nondet_int();
    c = nondet_int();
    if (c > 0) {
      printf ("LOG %d: insert(%d)\n", i, v);
      insert (&root, v);
      if (v == val) {
	present = 1;
      }
    } else {
      printf ("LOG %d: delete(%d)\n", i, v);
      delete (&root, v);
      if (v == val) {
	present = 0;
      }
    }
    b = balance(root);
    assert ((b >= -1) && (b <= 1));
  }

  if (present) {
    assert (query(root, val) != 0);
  } else {
    assert (query(root, val) == 0);
  }
}
