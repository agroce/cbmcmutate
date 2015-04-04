#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "fake.h"
#include "rcu.h"

#ifndef STACKROUTE_H
#define STACKROUTE_H
/*
 * Maintain a stack of address-to-interface mappings.  These can be
 * pushed or popped.  Emulate free() by setting a flag.
 */

/* Keep route entries simple with integer address and interface identifier. */
struct route_entry {
	struct route_entry *next;
	int address;
	int interface;
	int freed;
};

struct route_entry *route_head;
struct route_entry route_entry_1;
struct route_entry route_entry_2;
DEFINE_SPINLOCK(route_lock);

struct route_entry *route_head = &route_entry_1;
struct route_entry route_entry_1 = {
	.next = &route_entry_2,
	.address = 1,
	.interface = 11,
	.freed = 0,
};
struct route_entry route_entry_2 = {
	.next = NULL,
	.address = 2,
	.interface = 22,
	.freed = 0,
};

int lookup(int address);

void insert(int address, int interface);

int delete(void);

#endif
