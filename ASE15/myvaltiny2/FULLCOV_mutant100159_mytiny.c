int mutant_covered = 0;

int total_covered = 0;

int covered[146];

/*
 * Read-Copy Update mechanism for mutual exclusion, the Bloatwatch edition.
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
 * Copyright IBM Corporation, 2008
 *
 * Author: Paul E. McKenney <paulmck@linux.vnet.ibm.com>
 *
 * For detailed explanation of Read-Copy Update mechanism see -
 *		Documentation/RCU
 */
#include "fake.h"

#include <linux/completion.h>
#include <linux/interrupt.h>
#include <linux/notifier.h>
#include <linux/rcupdate.h>
#include <linux/kernel.h>
#include <linux/export.h>
#include <linux/mutex.h>
#include <linux/sched.h>
#include <linux/types.h>
#include <linux/init.h>
#include <linux/time.h>
#include <linux/cpu.h>
#include <linux/prefetch.h>
#include <linux/ftrace_event.h>

#include "rcu.h"

/* Forward declarations for tiny_plugin.h. */
struct rcu_ctrlblk;
static void __rcu_process_callbacks(struct rcu_ctrlblk *rcp);
static void rcu_process_callbacks(struct softirq_action *unused);
static void __call_rcu(struct rcu_head *head,
void (*func)(struct rcu_head *rcu),
struct rcu_ctrlblk *rcp);

static long long rcu_dynticks_nesting = DYNTICK_TASK_EXIT_IDLE;

#include "tiny_plugin.h"

/* Common code for rcu_idle_enter() and rcu_irq_exit(), see kernel/rcu/tree.c. */
static void rcu_idle_enter_common(long long newval)
{
	__CPROVER_atomic_begin(); if (!covered[0]) {covered[0] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (newval) {
		__CPROVER_atomic_begin(); if (!covered[1]) {covered[1] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		RCU_TRACE(trace_rcu_dyntick(TPS("--="),
rcu_dynticks_nesting, newval));
		__CPROVER_atomic_begin(); if (!covered[2]) {covered[2] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		rcu_dynticks_nesting = newval;
		__CPROVER_atomic_begin(); if (!covered[3]) {covered[3] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		return;
	__CPROVER_atomic_begin(); if (!covered[4]) {covered[4] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[5]) {covered[5] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(trace_rcu_dyntick(TPS("Start"),
				    __CPROVER_atomic_begin(); if (!covered[6]) {covered[6] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
				    rcu_dynticks_nesting, newval));
	__CPROVER_atomic_begin(); if (!covered[7]) {covered[7] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (IS_ENABLED(CONFIG_RCU_TRACE) && !is_idle_task(current)) {
		__CPROVER_atomic_begin(); if (!covered[8]) {covered[8] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		struct task_struct *idle __maybe_unused = idle_task(smp_processor_id());

		__CPROVER_atomic_begin(); if (!covered[9]) {covered[9] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		RCU_TRACE(trace_rcu_dyntick(TPS("Entry error: not idle task"),
					    __CPROVER_atomic_begin(); if (!covered[10]) {covered[10] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
					    rcu_dynticks_nesting, newval));
		__CPROVER_atomic_begin(); if (!covered[11]) {covered[11] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		ftrace_dump(DUMP_ALL);
		__CPROVER_atomic_begin(); if (!covered[12]) {covered[12] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		WARN_ONCE(1, "Current pid: %d comm: %s / Idle pid: %d comm: %s",
			  __CPROVER_atomic_begin(); if (!covered[13]) {covered[13] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
			  current->pid, current->comm,
			  idle->pid, idle->comm); /* must be idle task! */
	__CPROVER_atomic_begin(); if (!covered[14]) {covered[14] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	rcu_sched_qs(); /* implies rcu_bh_inc() */
	__CPROVER_atomic_begin(); if (!covered[15]) {covered[15] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	barrier();
	__CPROVER_atomic_begin(); if (!covered[16]) {covered[16] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_dynticks_nesting = newval;
}

/*
 * Enter idle, which is an extended quiescent state if we have fully
 * entered that mode (i.e., if the new value of dynticks_nesting is zero).
 */
void rcu_idle_enter(void)
{
	__CPROVER_atomic_begin(); if (!covered[17]) {covered[17] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;
	__CPROVER_atomic_begin(); if (!covered[18]) {covered[18] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	long long newval;

	__CPROVER_atomic_begin(); if (!covered[19]) {covered[19] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[20]) {covered[20] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	WARN_ON_ONCE((rcu_dynticks_nesting & DYNTICK_TASK_NEST_MASK) == 0);
	__CPROVER_atomic_begin(); if (!covered[21]) {covered[21] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if ((rcu_dynticks_nesting & DYNTICK_TASK_NEST_MASK) == DYNTICK_TASK_NEST_VALUE) {
		__CPROVER_atomic_begin(); if (!covered[22]) {covered[22] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		newval = 0;
	__CPROVER_atomic_begin(); if (!covered[23]) {covered[23] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	else {
		__CPROVER_atomic_begin(); if (!covered[24]) {covered[24] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		newval = rcu_dynticks_nesting - DYNTICK_TASK_NEST_VALUE;
	__CPROVER_atomic_begin(); if (!covered[25]) {covered[25] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[26]) {covered[26] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_idle_enter_common(newval);
	__CPROVER_atomic_begin(); if (!covered[27]) {covered[27] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);
}
EXPORT_SYMBOL_GPL(rcu_idle_enter);

/*
 * Exit an interrupt handler towards idle.
 */
void rcu_irq_exit(void)
{
	__CPROVER_atomic_begin(); if (!covered[28]) {covered[28] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;
	__CPROVER_atomic_begin(); if (!covered[29]) {covered[29] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	long long newval;

	__CPROVER_atomic_begin(); if (!covered[30]) {covered[30] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[31]) {covered[31] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	newval = rcu_dynticks_nesting - 1;
	__CPROVER_atomic_begin(); if (!covered[32]) {covered[32] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	WARN_ON_ONCE(newval < 0);
	__CPROVER_atomic_begin(); if (!covered[33]) {covered[33] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_idle_enter_common(newval);
	__CPROVER_atomic_begin(); if (!covered[34]) {covered[34] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);
}
EXPORT_SYMBOL_GPL(rcu_irq_exit);

/* Common code for rcu_idle_exit() and rcu_irq_enter(), see kernel/rcu/tree.c. */
static void rcu_idle_exit_common(long long oldval)
{
	__CPROVER_atomic_begin(); if (!covered[35]) {covered[35] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (oldval) {
		__CPROVER_atomic_begin(); if (!covered[36]) {covered[36] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		RCU_TRACE(trace_rcu_dyntick(TPS("++="),
					    __CPROVER_atomic_begin(); if (!covered[37]) {covered[37] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
					    oldval, rcu_dynticks_nesting));
		__CPROVER_atomic_begin(); if (!covered[38]) {covered[38] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		return;
	__CPROVER_atomic_begin(); if (!covered[39]) {covered[39] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[40]) {covered[40] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(trace_rcu_dyntick(TPS("End"), oldval, rcu_dynticks_nesting));
	__CPROVER_atomic_begin(); if (!covered[41]) {covered[41] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (IS_ENABLED(CONFIG_RCU_TRACE) && !is_idle_task(current)) {
		__CPROVER_atomic_begin(); if (!covered[42]) {covered[42] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		struct task_struct *idle __maybe_unused = idle_task(smp_processor_id());

		__CPROVER_atomic_begin(); if (!covered[43]) {covered[43] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		RCU_TRACE(trace_rcu_dyntick(TPS("Exit error: not idle task"),
oldval, rcu_dynticks_nesting));
		__CPROVER_atomic_begin(); if (!covered[44]) {covered[44] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		ftrace_dump(DUMP_ALL);
		__CPROVER_atomic_begin(); if (!covered[45]) {covered[45] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		WARN_ONCE(1, "Current pid: %d comm: %s / Idle pid: %d comm: %s",
			  __CPROVER_atomic_begin(); if (!covered[46]) {covered[46] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
			  current->pid, current->comm,
			  idle->pid, idle->comm); /* must be idle task! */
	__CPROVER_atomic_begin(); if (!covered[47]) {covered[47] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
}

/*
 * Exit idle, so that we are no longer in an extended quiescent state.
 */
void rcu_idle_exit(void)
{
	__CPROVER_atomic_begin(); if (!covered[48]) {covered[48] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;
	__CPROVER_atomic_begin(); if (!covered[49]) {covered[49] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	long long oldval;

	__CPROVER_atomic_begin(); if (!covered[50]) {covered[50] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[51]) {covered[51] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	oldval = rcu_dynticks_nesting;
	__CPROVER_atomic_begin(); if (!covered[52]) {covered[52] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	WARN_ON_ONCE(rcu_dynticks_nesting < 0);
	__CPROVER_atomic_begin(); if (!covered[53]) {covered[53] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (rcu_dynticks_nesting & DYNTICK_TASK_NEST_MASK) {
		__CPROVER_atomic_begin(); if (!covered[54]) {covered[54] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		rcu_dynticks_nesting += DYNTICK_TASK_NEST_VALUE;
	__CPROVER_atomic_begin(); if (!covered[55]) {covered[55] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	else {
		__CPROVER_atomic_begin(); if (!covered[56]) {covered[56] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		rcu_dynticks_nesting = DYNTICK_TASK_EXIT_IDLE;
	__CPROVER_atomic_begin(); if (!covered[57]) {covered[57] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[58]) {covered[58] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_idle_exit_common(oldval);
	__CPROVER_atomic_begin(); if (!covered[59]) {covered[59] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);
}
EXPORT_SYMBOL_GPL(rcu_idle_exit);

/*
 * Enter an interrupt handler, moving away from idle.
 */
void rcu_irq_enter(void)
{
	__CPROVER_atomic_begin(); if (!covered[60]) {covered[60] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;
	__CPROVER_atomic_begin(); if (!covered[61]) {covered[61] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	long long oldval;

	__CPROVER_atomic_begin(); if (!covered[62]) {covered[62] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[63]) {covered[63] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	oldval = rcu_dynticks_nesting;
	__CPROVER_atomic_begin(); if (!covered[64]) {covered[64] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_dynticks_nesting++;
	__CPROVER_atomic_begin(); if (!covered[65]) {covered[65] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	WARN_ON_ONCE(rcu_dynticks_nesting == 0);
	__CPROVER_atomic_begin(); if (!covered[66]) {covered[66] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_idle_exit_common(oldval);
	__CPROVER_atomic_begin(); if (!covered[67]) {covered[67] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);
}
EXPORT_SYMBOL_GPL(rcu_irq_enter);

#if defined(CONFIG_DEBUG_LOCK_ALLOC) || defined(CONFIG_RCU_TRACE)

/*
 * Test whether RCU thinks that the current CPU is idle.
 */
bool notrace __rcu_is_watching(void)
{
	__CPROVER_atomic_begin(); if (!covered[68]) {covered[68] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	return rcu_dynticks_nesting;
}
EXPORT_SYMBOL(__rcu_is_watching);

#endif /* defined(CONFIG_DEBUG_LOCK_ALLOC) || defined(CONFIG_RCU_TRACE) */

/*
 * Test whether the current CPU was interrupted from idle.  Nested
 * interrupts don't count, we must be running at the first interrupt
 * level.
 */
static int rcu_is_cpu_rrupt_from_idle(void)
{
	__CPROVER_atomic_begin(); if (!covered[69]) {covered[69] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	return rcu_dynticks_nesting <= 1;
}

/*
 * Helper function for rcu_sched_qs() and rcu_bh_qs().
 * Also irqs are disabled to avoid confusion due to interrupt handlers
 * invoking call_rcu().
 */
static int rcu_qsctr_help(struct rcu_ctrlblk *rcp)
{
	__CPROVER_atomic_begin(); if (!covered[70]) {covered[70] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(reset_cpu_stall_ticks(rcp));
	__CPROVER_atomic_begin(); if (!covered[71]) {covered[71] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (rcp->rcucblist != NULL && rcp->donetail != rcp->curtail) {
		__CPROVER_atomic_begin(); if (!covered[72]) {covered[72] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		rcp->donetail = rcp->curtail;
		__CPROVER_atomic_begin(); if (!covered[73]) {covered[73] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		return 1;
	__CPROVER_atomic_begin(); if (!covered[74]) {covered[74] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}

	__CPROVER_atomic_begin(); if (!covered[75]) {covered[75] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	return 0;
}

/*
 * Record an rcu quiescent state.  And an rcu_bh quiescent state while we
 * are at it, given that any rcu quiescent state is also an rcu_bh
 * quiescent state.  Use "+" instead of "||" to defeat short circuiting.
 */
void rcu_sched_qs(void)
{
	__CPROVER_atomic_begin(); if (!covered[76]) {covered[76] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;

	__CPROVER_atomic_begin(); if (!covered[77]) {covered[77] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[78]) {covered[78] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (rcu_qsctr_help(&rcu_sched_ctrlblk) + rcu_qsctr_help(&rcu_bh_ctrlblk)) {
		__CPROVER_atomic_begin(); if (!covered[79]) {covered[79] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		raise_softirq(RCU_SOFTIRQ); 
	__CPROVER_atomic_begin(); if (!covered[80]) {covered[80] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[81]) {covered[81] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);
}

/*
 * Record an rcu_bh quiescent state.
 */
void rcu_bh_qs(void)
{
	__CPROVER_atomic_begin(); if (!covered[82]) {covered[82] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;

	__CPROVER_atomic_begin(); if (!covered[83]) {covered[83] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[84]) {covered[84] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (rcu_qsctr_help(&rcu_bh_ctrlblk)) {
		__CPROVER_atomic_begin(); if (!covered[85]) {covered[85] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		raise_softirq(RCU_SOFTIRQ);
	__CPROVER_atomic_begin(); if (!covered[86]) {covered[86] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[87]) {covered[87] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);
}

/*
 * Check to see if the scheduling-clock interrupt came from an extended
 * quiescent state, and, if so, tell RCU about it.  This function must
 * be called from hardirq context.  It is normally called from the
 * scheduling-clock interrupt.
 */
void rcu_check_callbacks(int user)
{
	__CPROVER_atomic_begin(); if (!covered[88]) {covered[88] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(check_cpu_stalls());
	__CPROVER_atomic_begin(); if (!covered[89]) {covered[89] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (user || rcu_is_cpu_rrupt_from_idle()) {
		__CPROVER_atomic_begin(); if (!covered[90]) {covered[90] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		rcu_sched_qs();
	__CPROVER_atomic_begin(); if (!covered[91]) {covered[91] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	else if (!in_softirq()) {
		__CPROVER_atomic_begin(); if (!covered[92]) {covered[92] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		rcu_bh_qs();
	__CPROVER_atomic_begin(); if (!covered[93]) {covered[93] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[94]) {covered[94] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (user) {
		__CPROVER_atomic_begin(); if (!covered[95]) {covered[95] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		rcu_note_voluntary_context_switch(current);
	__CPROVER_atomic_begin(); if (!covered[96]) {covered[96] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
}

/*
 * Invoke the RCU callbacks on the specified rcu_ctrlkblk structure
 * whose grace period has elapsed.
 */
static void __rcu_process_callbacks(struct rcu_ctrlblk *rcp)
{
	__CPROVER_atomic_begin(); if (!covered[97]) {covered[97] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	const char *rn = NULL;
	__CPROVER_atomic_begin(); if (!covered[98]) {covered[98] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	struct rcu_head *next, *list;
	__CPROVER_atomic_begin(); if (!covered[99]) {covered[99] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;
	__CPROVER_atomic_begin(); if (!covered[100]) {covered[100] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(int cb_count = 0);

	/* If no RCU callbacks ready to invoke, just return. */
	__CPROVER_atomic_begin(); if (!covered[101]) {covered[101] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (&rcp->rcucblist == rcp->donetail) {
		__CPROVER_atomic_begin(); if (!covered[102]) {covered[102] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		RCU_TRACE(trace_rcu_batch_start(rcp->name, 0, 0, -1));
		__CPROVER_atomic_begin(); if (!covered[103]) {covered[103] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		RCU_TRACE(trace_rcu_batch_end(rcp->name, 0,
!!ACCESS_ONCE(rcp->rcucblist),
need_resched(),
is_idle_task(current),
false));
		__CPROVER_atomic_begin(); if (!covered[104]) {covered[104] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		return;
	__CPROVER_atomic_begin(); if (!covered[105]) {covered[105] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}

	/* Move the ready-to-invoke callbacks to a local list. */
	__CPROVER_atomic_begin(); if (!covered[106]) {covered[106] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[107]) {covered[107] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(trace_rcu_batch_start(rcp->name, 0, rcp->qlen, -1));
	__CPROVER_atomic_begin(); if (!covered[108]) {covered[108] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	list = rcp->rcucblist;
	__CPROVER_atomic_begin(); if (!covered[109]) {covered[109] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcp->rcucblist = *rcp->donetail;
	__CPROVER_atomic_begin(); if (!covered[110]) {covered[110] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	*rcp->donetail = NULL;
	__CPROVER_atomic_begin(); if (!covered[111]) {covered[111] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	if (rcp->curtail == rcp->donetail) {
 /* MUTANT (del_stmt) */ /* 		rcp->curtail = &rcp->rcucblist; */ 
	__CPROVER_atomic_begin(); if (!covered[112]) {covered[112] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[113]) {covered[113] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcp->donetail = &rcp->rcucblist;
	__CPROVER_atomic_begin(); if (!covered[114]) {covered[114] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);

	/* Invoke the callbacks on the local list. */
	__CPROVER_atomic_begin(); if (!covered[115]) {covered[115] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(rn = rcp->name);
	__CPROVER_atomic_begin(); if (!covered[116]) {covered[116] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	while (list) {
		__CPROVER_atomic_begin(); if (!covered[117]) {covered[117] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		next = list->next;
		__CPROVER_atomic_begin(); if (!covered[118]) {covered[118] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		prefetch(next);
		__CPROVER_atomic_begin(); if (!covered[119]) {covered[119] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		debug_rcu_head_unqueue(list);
		__CPROVER_atomic_begin(); if (!covered[120]) {covered[120] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		local_bh_disable();
		__CPROVER_atomic_begin(); if (!covered[121]) {covered[121] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		__rcu_reclaim(rn, list);
		__CPROVER_atomic_begin(); if (!covered[122]) {covered[122] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		local_bh_enable();
		__CPROVER_atomic_begin(); if (!covered[123]) {covered[123] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		list = next;
		__CPROVER_atomic_begin(); if (!covered[124]) {covered[124] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
		RCU_TRACE(cb_count++);
	__CPROVER_atomic_begin(); if (!covered[125]) {covered[125] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	}
	__CPROVER_atomic_begin(); if (!covered[126]) {covered[126] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(rcu_trace_sub_qlen(rcp, cb_count));
	__CPROVER_atomic_begin(); if (!covered[127]) {covered[127] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(trace_rcu_batch_end(rcp->name,
cb_count, 0, need_resched(),
is_idle_task(current),
false));
}

static void rcu_process_callbacks(struct softirq_action *unused)
{
	__CPROVER_atomic_begin(); if (!covered[128]) {covered[128] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	__rcu_process_callbacks(&rcu_sched_ctrlblk);
	__CPROVER_atomic_begin(); if (!covered[129]) {covered[129] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	__rcu_process_callbacks(&rcu_bh_ctrlblk);
}

/*
 * Wait for a grace period to elapse.  But it is illegal to invoke
 * synchronize_sched() from within an RCU read-side critical section.
 * Therefore, any legal call to synchronize_sched() is a quiescent
 * state, and so on a UP system, synchronize_sched() need do nothing.
 * Ditto for synchronize_rcu_bh().  (But Lai Jiangshan points out the
 * benefits of doing might_sleep() to reduce latency.)
 *
 * Cool, huh?  (Due to Josh Triplett.)
 *
 * But we want to make this a static inline later.  The cond_resched()
 * currently makes this problematic.
 */
void synchronize_sched(void)
{
	__CPROVER_atomic_begin(); if (!covered[130]) {covered[130] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_lockdep_assert(!lock_is_held(&rcu_bh_lock_map) &&
!lock_is_held(&rcu_lock_map) &&
!lock_is_held(&rcu_sched_lock_map),
"Illegal synchronize_sched() in RCU read-side critical section");
	__CPROVER_atomic_begin(); if (!covered[131]) {covered[131] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	cond_resched();
}
EXPORT_SYMBOL_GPL(synchronize_sched);

/*
 * Helper function for call_rcu() and call_rcu_bh().
 */
static void __call_rcu(struct rcu_head *head,
void (*func)(struct rcu_head *rcu),
struct rcu_ctrlblk *rcp)
{
	__CPROVER_atomic_begin(); if (!covered[132]) {covered[132] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	unsigned long flags;

	__CPROVER_atomic_begin(); if (!covered[133]) {covered[133] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	debug_rcu_head_queue(head);
	__CPROVER_atomic_begin(); if (!covered[134]) {covered[134] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	head->func = func;
	__CPROVER_atomic_begin(); if (!covered[135]) {covered[135] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	head->next = NULL;

	__CPROVER_atomic_begin(); if (!covered[136]) {covered[136] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_save(flags);
	__CPROVER_atomic_begin(); if (!covered[137]) {covered[137] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	*rcp->curtail = head;
	__CPROVER_atomic_begin(); if (!covered[138]) {covered[138] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcp->curtail = &head->next;
	__CPROVER_atomic_begin(); if (!covered[139]) {covered[139] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	RCU_TRACE(rcp->qlen++);
	__CPROVER_atomic_begin(); if (!covered[140]) {covered[140] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	local_irq_restore(flags);
}

/*
 * Post an RCU callback to be invoked after the end of an RCU-sched grace
 * period.  But since we have but one CPU, that would be after any
 * quiescent state.
 */
void call_rcu_sched(struct rcu_head *head, void (*func)(struct rcu_head *rcu))
{
	__CPROVER_atomic_begin(); if (!covered[141]) {covered[141] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	__call_rcu(head, func, &rcu_sched_ctrlblk);
}
EXPORT_SYMBOL_GPL(call_rcu_sched);

/*
 * Post an RCU bottom-half callback to be invoked after any subsequent
 * quiescent state.
 */
void call_rcu_bh(struct rcu_head *head, void (*func)(struct rcu_head *rcu))
{
	__CPROVER_atomic_begin(); if (!covered[142]) {covered[142] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	__call_rcu(head, func, &rcu_bh_ctrlblk);
}
EXPORT_SYMBOL_GPL(call_rcu_bh);

void __init rcu_init(void)
{
	__CPROVER_atomic_begin(); if (!covered[143]) {covered[143] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	open_softirq(RCU_SOFTIRQ, rcu_process_callbacks);

	__CPROVER_atomic_begin(); if (!covered[144]) {covered[144] = 1; total_covered += 1;} __CPROVER_atomic_end(); 
	rcu_early_boot_tests();
}
