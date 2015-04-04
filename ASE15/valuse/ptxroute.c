/*
 * ptxroute.c: Demonstrate bug in my first use of RCU in DYNIX/ptx.
 *	Also demonstrate alleged fixes.
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
 * DYNIX/ptx's TCP/IP routing table extended the 1980s BSD practice.
 * The BSD's of that time used a simple linear linked list to implement the
 * routing table, but with an additional pointer to the routing entry used
 * by the last routing lookup.  The idea was that applications tended to
 * send network packets in bursts, so that the list-search overhead would
 * be amortized over all packets in that burst.
 *
 * DYNIX/ptx took the then-controversial approach of using a hash table in
 * place of the linked list, but retained the pointer to the last routing
 * lookup that was used.  This last-used pointer was maintained on a
 * per-bucket basis.  And yes, use of a hash table is now commonplace, but
 * back then it earned Ken Dove and I a couple of papers.  (Both entitled
 * "Efficient Demultiplexing of Incoming TCP Packets", for whatever that
 * might be worth.)
 *
 * And the first DYNIX/ptx data structure that I converted to RCU was the
 * TCP/IP routing table.  However, my first attempt was buggy, and that bug
 * is recreated here.  (In the original, Jan-Simon Pendry fixed the bug.
 * And his fix appeared to me to be correct, despite his having no idea
 * what RCU was or how it worked.  I was suitably impressed.)
 *
 * However, a hash table is nothing more than an array of linked lists,
 * so for simplicity, this code goes back to the BSD approach.  So,
 * get our your 1980s costumes, watch a 1980s movie, and then enjoy this
 * computer-programming blast from the past!
 *
 * Your mission, should you decide to accept, is to find the bug that
 * Jan-Simon found and fix it.  There are several possible fixes.
 * No fair asking Jan-Simon!  For one thing, it is entirely possible that
 * his fix was incorrect.  I honestly don't recall exactly what the
 * fix was.  ;-)
 */

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
	pthread_t tr1;
	pthread_t tr2;
	pthread_t tu;

	if (IS_ENABLED(DYNAMIC)) {
		INIT_LIST_HEAD(&route_head);
		insert(1, 11);
		insert(2, 22);
	}

	if (pthread_create(&tr1, NULL, thread_reader, NULL))
		abort();
	if (pthread_create(&tr2, NULL, thread_reader, NULL))
		abort();
	if (pthread_create(&tu, NULL, thread_updater, NULL))
		abort();

	if (pthread_join(tr1, NULL))
		abort();
	if (pthread_join(tr2, NULL))
		abort();

	assert_no_rcu_read_lock();
	return 0;
}
