#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "fake.h"
#include "rcu.h"
#include "stackroute.h"


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
	if (!IS_ENABLED(FORCE_FAILURE_1)) {
		synchronize_rcu();
	}
	rep->freed = 1;  /* Model the act of freeing. */
	return 1;
}
