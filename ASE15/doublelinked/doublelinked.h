/* Doubly Linked List insertion sort */
#include<stdio.h>
#include<stdlib.h>
 
#ifndef DOUBLELINKED_H
#define DOUBLELINKED_H
struct node {
  int data;
  struct node* next;
  struct node* prev;
};

struct node *insert_node(struct node **head, int value);
#endif

