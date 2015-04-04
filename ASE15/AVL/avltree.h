#ifndef AVLTREE_H
#define AVLTREE_H

struct node {
  int payload;
  int height;
  struct node * kid[2];
} ; 
// internally, nnil is the new nul

extern struct node dummy;
extern struct node *nnil;

void insert(struct node **rootp, int value);

void delete(struct node **rootp, int value);

int balance(struct node *n);

struct node *query(struct node *root, int value);
 

#endif
