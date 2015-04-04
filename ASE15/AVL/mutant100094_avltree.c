#include <stdlib.h>
#include <stdio.h>
#include "avltree.h"

struct node dummy = { 0, 0, {&dummy, &dummy} };
struct node *nnil = &dummy;

struct node *new_node(int value)
{
  struct node *n = calloc(1, sizeof *n);
  *n = (struct node) { value, 1, {nnil, nnil} };
  return n;
}

int max(int a, int b) { return a > b ? a : b; }

void set_height(struct node *n) {
  n->height = 1 + max(n->kid[0]->height, n->kid[1]->height);
}
 
int balance(struct node *n) {
  return n->kid[0]->height - n->kid[1]->height;
}
 
// rotate a subtree according to dir; if new root is nil, old root is freed
struct node * rotate(struct node **rootp, int dir)
{
  struct node *old_r = *rootp, *new_r = old_r->kid[dir];
 
  if (nnil == (*rootp = new_r))
    free(old_r);
  else {
    old_r->kid[dir] = new_r->kid[!dir];
    set_height(old_r);
    new_r->kid[!dir] = old_r;
  }
  return new_r;
}
 
void adjust_balance(struct node **rootp)
{
  struct node *root = *rootp;
  int b = balance(root)/2;
  if (b) {
    int dir = (1 - b)/2;
    if (balance(root->kid[dir]) == -b)
      rotate(&root->kid[dir], !dir);
    root = rotate(rootp, dir);
  }
  if (root != nnil) set_height(root);
}
 
// find the node that contains value as payload; or returns 0
struct node *query(struct node *root, int value)
{
  return root == nnil
    ? 0
    : root->payload == value
    ? root
    : query(root->kid[value > root->payload], value);
}
 
void insert(struct node **rootp, int value)
{
  struct node *root = *rootp;
 
  if (root == nnil)
    *rootp = new_node(value);
  else if (value != root->payload) { // don't allow dup keys
    insert(&root->kid[value > root->payload], value);
    adjust_balance(rootp);
  }
}
 
void delete(struct node **rootp, int value)
{
  struct node *root = *rootp;
  if (root == nnil) return; // not found
 
  // if this is the node we want, rotate until off the tree
  if (root->payload == value)
 /* MUTANT (rep_op) */    if (nnil == (root = rotate(rootp, balance(root) > 0)))
      return;
 
  delete(&root->kid[value > root->payload], value);
  adjust_balance(rootp);
}

 
