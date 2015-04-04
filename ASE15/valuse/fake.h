/*
 * "Fake" declarations to scaffold a Linux-kernel SMP environment.
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

#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/time.h>
#include <pthread.h>
#include <assert.h>
#include <poll.h>


/* Definitions taken from the Linux kernel. */
#ifndef FAKE_H
#define FAKE_H

#define __force

#undef offsetof
#ifdef __compiler_offsetof
#define offsetof(TYPE,MEMBER) __compiler_offsetof(TYPE,MEMBER)
#else
#define offsetof(TYPE, MEMBER) ((size_t) &((TYPE *)0)->MEMBER)
#endif

#define container_of(ptr, type, member) ({			\
	const typeof( ((type *)0)->member ) *__mptr = (ptr);	\
	(type *)( (char *)__mptr - offsetof(type,member) );})

/*
 * Getting something that works in C and CPP for an arg that may or may
 * not be defined is tricky.  Here, if we have "#define CONFIG_BOOGER 1"
 * we match on the placeholder define, insert the "0," for arg1 and generate
 * the triplet (0, 1, 0).  Then the last step cherry picks the 2nd arg (a one).
 * When CONFIG_BOOGER is not defined, we generate a (... 1, 0) pair, and when
 * the last step cherry picks the 2nd arg, we get a zero.
 */
#define __ARG_PLACEHOLDER_1 0,
#define config_enabled(cfg) _config_enabled(cfg)
#define _config_enabled(value) __config_enabled(__ARG_PLACEHOLDER_##value)
#define __config_enabled(arg1_or_junk) ___config_enabled(arg1_or_junk 1, 0)
#define ___config_enabled(__ignored, val, ...) val

/*
 * IS_ENABLED(CONFIG_FOO) evaluates to 1 if CONFIG_FOO is set to 'y' or 'm',
 * 0 otherwise.
 *
 */
#define IS_ENABLED(option) \
	(config_enabled(option) || config_enabled(option##_MODULE))

#ifndef __maybe_unused
# define __maybe_unused         /* unimplemented */
#endif

/* Optimization barrier */
/* The "volatile" is due to gcc bugs */
#define barrier() __asm__ __volatile__("": : :"memory")

/**
 * struct callback_head - callback structure for use with RCU and task_work
 * @next: next update requests in a list
 * @func: actual update function to call after the grace period.
 */
struct callback_head {
	struct callback_head *next;
	void (*func)(struct callback_head *head);
};
#define rcu_head callback_head

typedef _Bool bool;

enum {
	false	= 0,
	true	= 1
};

typedef signed char s8;
typedef unsigned char u8;

typedef signed short s16;
typedef unsigned short u16;

typedef signed int s32;
typedef unsigned int u32;

typedef signed long long s64;
typedef unsigned long long u64;

#define USHRT_MAX	((u16)(~0U))
#define SHRT_MAX	((s16)(USHRT_MAX>>1))
#define SHRT_MIN	((s16)(-SHRT_MAX - 1))
#define INT_MAX		((int)(~0U>>1))
#define INT_MIN		(-INT_MAX - 1)
#define UINT_MAX	(~0U)
#define LONG_MAX	((long)(~0UL>>1))
#define LONG_MIN	(-LONG_MAX - 1)
#define ULONG_MAX	(~0UL)
#define LLONG_MAX	((long long)(~0ULL>>1))
#define LLONG_MIN	(-LLONG_MAX - 1)
#define ULLONG_MAX	(~0ULL)
#define SIZE_MAX	(~(size_t)0)

#define U8_MAX		((u8)~0U)
#define S8_MAX		((s8)(U8_MAX>>1))
#define S8_MIN		((s8)(-S8_MAX - 1))
#define U16_MAX		((u16)~0U)
#define S16_MAX		((s16)(U16_MAX>>1))
#define S16_MIN		((s16)(-S16_MAX - 1))
#define U32_MAX		((u32)~0U)
#define S32_MAX		((s32)(U32_MAX>>1))
#define S32_MIN		((s32)(-S32_MAX - 1))
#define U64_MAX		((u64)~0ULL)
#define S64_MAX		((s64)(U64_MAX>>1))
#define S64_MIN		((s64)(-S64_MAX - 1))

#define smp_mb() __sync_synchronize()
int noassert;
#define SET_NOASSERT() do { noassert = 1; smp_mb(); } while (0)
#define CK_NOASSERT() ({ smp_mb(); noassert; })
#define BUG_ON(condition) assert(!(condition) || CK_NOASSERT())
#define WARN_ON(condition) assert(!(condition) || CK_NOASSERT())
#define WARN_ONCE(condition, format...) assert(!(condition) || CK_NOASSERT())
#define WARN_ON_ONCE(condition)	assert(!(condition) || CK_NOASSERT())

#define prefetch(next) do { } while (0)

#define preempt_disable() do { } while (0)
#define preempt_enable() do { } while (0)
#define preempt_disable_notrace() do { } while (0)
#define preempt_enable_notrace() do { } while (0)
#define local_bh_disable() do { } while (0)
#define local_bh_enable() do { } while (0)

#define ACCESS_ONCE(x) (*(volatile typeof(x) *)&(x))

#define smp_store_release(p, v) \
do { \
	barrier(); \
	ACCESS_ONCE(*p) = (v); \
} while (0)

#define smp_load_acquire(p) \
do { \
	typeof(*p) ___p1 = ACCESS_ONCE(*p); \
	\
	barrier(); \
	___p1; \
} while (0)

#define rcu_assign_pointer(p, v) smp_store_release(&p, (v))

#define READ_ONCE(x) ACCESS_ONCE(x)
#define WRITE_ONCE(x, val) do { ACCESS_ONCE(x) = (val); } while (0)

#ifdef CBMC
typedef int spinlock_t;
#define SPINLOCK_INITIALIZER 0
#else
typedef pthread_mutex_t spinlock_t;
#define SPINLOCK_INITIALIZER PTHREAD_MUTEX_INITIALIZER
#endif


#define DEFINE_SPINLOCK(name) spinlock_t name = SPINLOCK_INITIALIZER;

void spin_lock(spinlock_t *l)
{
#ifdef CBMC
	if (__sync_fetch_and_add(l, 1))
		exit(0);
#else
	if (pthread_mutex_lock(l))
		exit(-1);
#endif
}

void spin_unlock(spinlock_t *l)
{
#ifdef CBMC
	(void)__sync_fetch_and_sub(l, 1);
#else
	if (pthread_mutex_unlock(l))
		exit(-1);
#endif
}
#endif
