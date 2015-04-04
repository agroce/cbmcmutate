/*
 * Litmus test for correct RCU operation.
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
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright IBM Corporation, 2015
 *
 * Author: Paul E. McKenney <paulmck@linux.vnet.ibm.com>
 */

#include "fake.h"
#include "rcu.h"

int r_x;
int r_y;

int x;
int y;

void *thread_reader(void *arg)
{
	rcu_read_lock();
	r_x = x;
#ifdef FORCE_FAILURE_READER
	rcu_read_unlock();
	rcu_read_lock();
#endif
	r_y = y;
	rcu_read_unlock();
	return NULL;
}

void *thread_update(void *arg)
{
	x = 1;
#ifndef FORCE_FAILURE_GP
	synchronize_rcu();
#endif
	y = 1;
	return NULL;
}

int main(int argc, char *argv[])
{
	pthread_t tr;

	if (pthread_create(&tr, NULL, thread_reader, NULL))
		abort();
	(void)thread_update(NULL);
	if (pthread_join(tr, NULL))
		abort();

	BUG_ON(r_y != 0 && r_x != 1);
	return 0;
}
