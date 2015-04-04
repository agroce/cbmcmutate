/*
 * ptxrouteUP.c: Like ptxroute.c, but single-threaded
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

/* Keep route entries simple with integer address and interface identifier. */
struct route_entry {
	struct list_head next;
	int address;
	int interface;
	int freed;
};

struct list_head route_head;
struct route_entry route_entry_1;
struct route_entry route_entry_2;
struct route_entry *route_cache;
DEFINE_SPINLOCK(route_lock);

struct list_head route_head = {
	.next = &route_entry_1.next,
	.prev = &route_entry_2.next,
};
struct route_entry route_entry_1 = {
	.next.prev = &route_head,
	.next.next = &route_entry_2.next,
	.address = 1,
	.interface = 11,
	.freed = 0,
};
struct route_entry route_entry_2 = {
	.next.prev = &route_entry_1.next,
	.next.next = &route_head,
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
	rep = rcu_dereference(route_cache);
	if (rep != NULL && rep->address == address) {
		ret = rep->interface;
		BUG_ON(rep->freed);
		rcu_read_unlock();
		return ret;
	}
	list_for_each_entry_rcu(rep, &route_head, next) {
		if (rep->address == address) {
			ret = rep->interface;
			rcu_assign_pointer(route_cache, rep);
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
	list_add_rcu(&rep->next, &route_head);
	spin_unlock(&route_lock);
}

/* Delete an existing route entry, returning zero if it was not there. */
int delete(int address)
{
	struct route_entry *rep;

	spin_lock(&route_lock);
	list_for_each_entry_rcu(rep, &route_head, next) {
		if (rep->address == address) {
			list_del_rcu(&rep->next);
			spin_unlock(&route_lock);
			if (IS_ENABLED(FORCE_FAILURE_3)) {
				if (ACCESS_ONCE(route_cache) == rep)
					rcu_assign_pointer(route_cache, NULL);
			}
			synchronize_rcu();
			if (IS_ENABLED(FORCE_FAILURE_1)) {
			} else if (IS_ENABLED(FORCE_FAILURE_2)) {
				if (ACCESS_ONCE(route_cache) == rep) {
					rcu_assign_pointer(route_cache, NULL);
					synchronize_rcu();
				}
			} else {
				if (ACCESS_ONCE(route_cache) == rep)
					rcu_assign_pointer(route_cache, NULL);
				synchronize_rcu();
			}
			rep->freed = 1;  /* Model the act of freeing. */
			return 1;
		}
	}
	spin_unlock(&route_lock);
	return 0;
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
	delete(1);
	return NULL;
}

/* Woefully inadequate test. */
int main(int argc, char *argv[])
{
	if (IS_ENABLED(DYNAMIC)) {
		INIT_LIST_HEAD(&route_head);
		insert(1, 11);
		insert(2, 22);
	}

	(void)thread_reader(NULL);
	BUG_ON(lookup(1) != 11);
	(void)thread_updater(NULL);
	if (IS_ENABLED(FORCE_FAILURE_1))
		route_entry_2.freed = 1;
	(void)thread_reader(NULL);
	if (IS_ENABLED(FORCE_FAILURE_2))
		BUG_ON(lookup(2) != 42);

	assert_no_rcu_read_lock();
	return 0;
}
