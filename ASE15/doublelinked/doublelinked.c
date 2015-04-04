/* Doubly Linked List insertion sort */
#include <stdio.h>
#include <stdlib.h>
#include <doublelinked.h>

struct node *insert_node( struct node *head, int *value )
{
  struct node *new_node = NULL;
  struct node *cur_node = NULL;
  struct node *last_node = NULL;
  int found; /* 1 means found a place to insert the new node in, 0 means not*/
  new_node = (struct node *)malloc(sizeof(struct node));
  if(new_node == NULL)
    {
      printf("memory problem\n");
    }
  new_node->number = *value;
  /* If the first element */
  if (head == NULL)
    {
      new_node->next = new_node->prev = NULL;
      head = new_node;
    }
  else if (new_node->number < head->number)
    {
      new_node->next = head;
      head->prev = new_node;
      head = new_node;
      head->prev = NULL;
    }
  else
    {
      cur_node = head;
      found = 0;
      while (( cur_node != NULL ) && ( found == 0 ))
	{
	  if( new_node->number < cur_node->number )
	    {
	      found = 1;
	    }
	  else
	    {
	      last_node = cur_node;
	      //cur_node = cur_node->next;
	    }
	}
      /* We got the right place to insert our node */
      if( found == 1 )
	new_node->next = cur_node;
      /* Insert at the tail of the list */
      else
	{
	  last_node->next = new_node;
	  new_node->prev = last_node;
	  cur_node->prev = new_node;
	  cur_node->next = NULL;
	  cur_node = new_node;
	}
    }
  return head;
} 
