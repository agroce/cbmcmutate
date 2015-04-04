/* Doubly Linked List insertion sort */
#include <stdio.h>
#include <stdlib.h>
#include "doublelinked.h"

struct node *insert_node( struct node **head, int value )
{
  struct node *new_node = NULL;
  struct node *cur_node = NULL;
  int found; /* 1 means found a place to insert the new node in, 0 means not*/
  new_node = (struct node *)malloc(sizeof(struct node));
  if(new_node == NULL)
    {
      printf("memory problem\n");
      assert(0);
    }
  new_node->data = value;
  /* If the first element */
  if (*head == NULL)
    {
      new_node->next = new_node->prev = new_node;
      *head = new_node;
    }
  else if (new_node->data < (*head)->data)
    {
      new_node->next = *head;
      new_node->prev = (*head)->prev;
      (*head)->prev = new_node;
      *head = new_node;
      (*head)->prev->next = *head;
    }
  else
    {
      cur_node = *head;
      found = 0;
      do
	{
 /* MUTANT (rep_op) */	  if( new_node->data == cur_node->data )
	    {
	      found = 1;
	      break;
	    }
	  else
	    {
	      //				last_node = cur_node;
	      cur_node = cur_node->next;
	    }
	}
      while ( cur_node != *head );
      /* We got the right place to insert our node */
      if( found == 1 )
	{
	  new_node->next = cur_node;
	  new_node->prev = cur_node->prev;
	  cur_node->prev->next = new_node;
	  cur_node->prev = new_node;
	}
      /* Insert at the tail of the list */
      else
	{
	  new_node->next = *head;
	  new_node->prev = (*head)->prev;
	  (*head)->prev->next = new_node;
	  (*head)->prev = new_node;
	}
    }
  return *head;
}

  	
