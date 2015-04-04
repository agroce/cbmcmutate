/*
 * stackroute.c: Like stackptxroute.c, but avoid the cache.
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
 */

#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "fake.h"
#include "rcu.h"
#include "stackroute.h"

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
	pthread_t tr1;
	pthread_t tr2;
	pthread_t tu;

	if (IS_ENABLED(DYNAMIC)) {
		route_head = NULL;
		insert(2, 22);
		insert(1, 11);
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
