
CBMC=~/code/cbmc-cbmc-5.8/src/cbmc/cbmc
NAMIFY=~/code/cbmc-cbmc-5.8/namify.py


.PHONY: avl
avl:
	$(CBMC) -DMAX_ITEMS=2 AVL/harness.c --unwind 2 --smt2
	mv tmp avl.smt2
	$(NAMIFY) avl.smt2 avl-named.smt2
	z3 -smt2 avl-harness-named.smt2 > avl-named.cores

.PHONY: quicksort
quicksort:
	$(CBMC) -DMAX_ITEMS=2 quicksort/harness.c --unwind 2 --smt2
	mv tmp quicksort.smt2
	$(NAMIFY) quicksort.smt2 quicksort-named.smt2
	z3 -smt2 quicksort-named.smt2 > quicksort-named.cores

.PHONY: bmh
bmh:
	$(CBMC) -DTSIZE=1 -DPSIZE=1 -DCSIZE=1 BMH/harness.c --unwind 2 --smt2
	mv tmp bmh.smt2
	$(NAMIFY) bmh.smt2 bmh-named.smt2
	z3 -smt2 bmh-named.smt2 > bmh-named.cores


clean:
	rm -f *.smt2 tmp
