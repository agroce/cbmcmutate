#include <stdio.h>
#include <stdlib.h>
#include "avltree.h"

#define MAX_VAL 32
int main(void)
{
  int x;
  struct node *root = nnil;
 
  srand(time(0));
 
  for (x = 0; x < 10 * MAX_VAL; x++) {
    // random insertion and deletion
    if (rand()&1)insert(&root, rand()%MAX_VAL);
    else delete(&root, rand()%MAX_VAL);
 
    verify(root);
  }
 
  puts("Tree is:");
  show_tree(root, 0, 0);
 
  puts("\nQuerying values:");
  for (x = 0; x < MAX_VAL; x++) {
    struct node *p = query(root, x);
    if (p)printf("%2d found: %p %d\n", x, p, p->payload);
  }
 
  for (x = 0; x < MAX_VAL; x++) {
    delete(&root, x);
    verify(root);
  }
 
  puts("\nAfter deleting all values, tree is:");
  show_tree(root, 0, 0);
 
  return 0;
}
