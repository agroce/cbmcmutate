/*
 * "Fake" definitions to scaffold a Linux-kernel UP environment.
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
#include <linux/rcupdate.h>
#include "mutant100184_tiny.c"

/* Just say "no" to memory allocation. */
void kfree(const void *p)
{
}

/* Just say "no" to rcu_barrier() and friends. */
void wait_rcu_gp(call_rcu_func_t crf)
{
}

/*
 * Definitions to emulate CPU, interrupts, and scheduling.
 *
 * There is a cpu_lock, when held, the corresponding thread is running.
 * An irq_lock indicates that the corresponding thread has interrupts
 *	masked, perhaps due to being in an interrupt handler.  Acquire
 *	cpu_lock first, then irq_lock.  You cannot disable interrupts
 *	unless you are running, after all!
 * An nmi_lock indicates that the corresponding thread is in an NMI
 *	handler.  You cannot acquire either cpu_lock or irq_lock while
 *	holding nmi_lock.
 */

#ifdef CBMC
int cpu_lock;
int irq_lock;
int nmi_lock;
#else
pthread_mutex_t cpu_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t irq_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t nmi_lock = PTHREAD_MUTEX_INITIALIZER;
#endif

void fake_acquire_cpu(void)
{
#ifdef CBMC
	if (__sync_fetch_and_add(&cpu_lock, 1))
		SET_NOASSERT();
#else
	if (pthread_mutex_lock(&cpu_lock))
		exit(-1);
#endif
	rcu_idle_exit();
}

void fake_release_cpu(void)
{
	rcu_idle_enter();
#ifdef CBMC
	(void)__sync_fetch_and_sub(&cpu_lock, 1);
#else
	if (pthread_mutex_unlock(&cpu_lock))
		exit(-1);
#endif
	if (need_softirq) {
		need_softirq = 0;
//		rcu_process_callbacks(NULL); /* cbmc recurses. */
	}
}

void cond_resched(void)
{
	fake_release_cpu();
	fake_acquire_cpu();
}

static int __thread local_irq_depth;

void local_irq_save(unsigned long flags)
{
	if (!local_irq_depth++) {
#ifdef CBMC
		if (__sync_fetch_and_add(&irq_lock, 1))
			SET_NOASSERT();
#else
		if (pthread_mutex_lock(&irq_lock))
			exit(-1);
#endif
	}
}

void local_irq_restore(unsigned long flags)
{
	if (!--local_irq_depth) {
#ifdef CBMC
		(void)__sync_fetch_and_sub(&irq_lock, 1);
#else
		if (pthread_mutex_unlock(&irq_lock))
			exit(-1);
#endif
	}
}

/*
 * Code under test.
 */

int x;
int y;

int __unbuffered_cnt;
int __unbuffered_tpr_x;
int __unbuffered_tpr_y;

void rcu_reader(void)
{
	rcu_read_lock();
	__unbuffered_tpr_x = x;
#ifdef FORCE_FAILURE
	rcu_read_unlock();
	cond_resched();
	rcu_read_lock();
#endif
	__unbuffered_tpr_y = y;
	rcu_read_unlock();
}

void *thread_update(void *arg)
{
	fake_acquire_cpu();

	x = 1;
#ifndef FORCE_FAILURE_2
	synchronize_rcu();
#endif
	y = 1;

	fake_release_cpu();
#ifndef RUN
	// Instrumentation for CPROVER
	asm("sync ");
	__unbuffered_cnt++;
#endif
}

void *thread_process_reader(void *arg)
{
	fake_acquire_cpu();

	rcu_reader();

	fake_release_cpu();
#ifndef RUN
	// Instrumentation for CPROVER
	asm("sync ");
	__unbuffered_cnt++;
#endif
}

#ifdef RUN

/* Actually run the test. */
int main(int argc, char *argv[])
{
	pthread_t tu;
	pthread_t tpr;

	rcu_idle_enter();
	if (pthread_create(&tu, NULL, thread_update, NULL))
		abort();
	if (pthread_create(&tpr, NULL, thread_process_reader, NULL))
		abort();
	if (pthread_join(tu, NULL))
		abort();
	if (pthread_join(tpr, NULL))
		abort();
	assert(__unbuffered_tpr_y == 0 || __unbuffered_tpr_x == 1 ||
	       CK_NOASSERT());

	return 0;
}

#else

/* Formally verify the test. */
int main(int argc, char *argv[])
{
	__CPROVER_ASYNC_0: thread_update(0);
	__CPROVER_ASYNC_1: thread_process_reader(0);
	__CPROVER_assume(__unbuffered_cnt == 2);
	assert(__unbuffered_tpr_y == 0 || __unbuffered_tpr_x == 1);

	return 0;
}

#endif
