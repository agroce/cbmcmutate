#include <stdio.h>
#include <stdlib.h>
#include "doublelinked.h"

int ref[MAX_ITEMS];

int nondet_int();

int main () {
  struct node * head = NULL;
  struct node * pos = NULL;
  int i, v, index, count, lcount, curr;
  int s = nondet_int();
  __CPROVER_assume((s > 0) && (s <=MAX_ITEMS));

  for (i = 0; i < s; i++) {
    v = nondet_int();
    printf ("LOG: ref[%d] = %d\n", i, v);
    ref[i] = v;
    head = insert_node(&head, v);
  }
  v = nondet_int();
  count = 0;
  printf ("LOG: checking %d\n", v);
  for (i = 0; i < s; i++) {
    if (ref[i] == v) {
      count++;
    }
  }
  printf ("LOG: ref count = %d\n",count);
  pos = head;
  lcount = 0;
  curr = head->data;
  if (curr == v) {
    printf ("LOG: head (%d) = %d\n", head->data, v);
    lcount++;
  }
  for (i = 1; i < s; i++) {
    printf ("LOG: moving to next item\n");
    pos = pos->next;
    assert(pos->data >= curr);
    curr = pos->data;
    if (curr == v) {
      printf ("LOG: this data (%d) = %d\n", pos->data, v);
      lcount++;
    }
  }
  printf("LOG: list count = %d\n", lcount);
  assert (count == lcount);
}
