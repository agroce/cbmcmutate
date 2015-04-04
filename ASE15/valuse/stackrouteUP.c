/*
 * stackrouteUP.c: Like stackroute.c, but single-threaded.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2015 Paul E. McKenney, IBM Corporation.
 */

#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "fake.h"
#include "rcu.h"

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

/* Do a lookup and cache the result. */
int lookup(int address)
{
	struct route_entry *rep;
	int ret;

	rcu_read_lock();
	for (rep = route_head; rep != NULL; rep = rep->next) {
		if (rep->address == address) {
			ret = rep->interface;
			BUG_ON(rep->freed);
			rcu_read_unlock();
			return ret;
		}
	}
	rcu_read_unlock();
	return -1;
}

/* Insert a new route entry. */
void insert(int address, int interface)
{
	struct route_entry *rep = malloc(sizeof(*rep));

	BUG_ON(!rep);
	rep->address = address;
	rep->interface = interface;
	rep->freed = 0;
	spin_lock(&route_lock);
	rep->next = route_head;
	route_head = rep;
	spin_unlock(&route_lock);
}

/* Delete the first route entry, returning zero if the list was empty. */
int delete(void)
{
	struct route_entry *rep;

	spin_lock(&route_lock);
	if (route_head == NULL) {
		spin_unlock(&route_lock);
		return 0;
	}
	rep = route_head;
	route_head = rep->next;
	spin_unlock(&route_lock);
	synchronize_rcu();
	rep->freed = 1;  /* Model the act of freeing. */
	return 1;
}

void *thread_reader(void *arg)
{
	(void)lookup(1);
	BUG_ON(lookup(2) != 22);
	BUG_ON(lookup(3) != -1);
	(void)lookup(1);
	return NULL;
}

void *thread_updater(void *arg)
{
	delete();
	return NULL;
}

/* Woefully inadequate test. */
int main(int argc, char *argv[])
{
	if (IS_ENABLED(DYNAMIC)) {
		route_head = NULL;
		insert(2, 22);
		insert(1, 11);
	}

	(void)thread_reader(NULL);
	BUG_ON(lookup(1) != 11);
	(void)thread_updater(NULL);
	if (IS_ENABLED(FORCE_FAILURE_1) && route_head != NULL)
		route_head->freed = 1;
	(void)thread_reader(NULL);
	if (IS_ENABLED(FORCE_FAILURE_2))
		BUG_ON(lookup(2) != 42);

	assert_no_rcu_read_lock();
	return 0;
}
