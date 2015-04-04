BINDIR=/home/paulmck/paper.archive/scalability/PlumbersMacho2013/Validation/bin
export PATH=$BINDIR:$PATH
echo PATH: $PATH

echo goto-cc -o $1.goto -I . $1.c
goto-cc -o $1.goto -I . $1.c

echo goto-instrument --mm power $1.goto $1_power.goto
goto-instrument --mm power $1.goto $1_power.goto

nthreads=`grep __CPROVER_ASYNC_ $1.c | wc -l`
nthreads=`expr $nthreads + 1`

echo satabs --prefix-first --concurrency --full-inlining --max-threads $nthreads $1_power.goto
satabs --prefix-first --concurrency --full-inlining --max-threads $nthreads $1_power.goto
