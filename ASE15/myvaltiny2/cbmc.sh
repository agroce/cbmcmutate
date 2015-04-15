# need cbmc v5.0
cbmc -I . -DRUN -DCBMC fake.c
# Can add "--mm pso" or "--arch powerpc" for some variety.
# -DFORCE_FAILURE to force failure (split RCU read-side critical section)
# -DFORCE_FAILURE_2 to omit grace period (verification succeeds, tiny!)
# -DFORCE_FAILURE_DYNTICKS to force failure (misnest idle dynticks)
# -DFORCE_FAILURE_IRQ to force failure (misnest irq dynticks)
# -DFORCE_FAILURE_IRQ_BOGUS for dynticks self-repair (verification succeeds)
# -DFORCE_FAILURE_IRQ_BOGUS_2 for dynticks self-repair (verification succeeds)
# -DCBMC_ORDERING_BUG to do unsynchronized accesses to noassert
