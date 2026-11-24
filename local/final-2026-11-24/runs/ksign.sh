#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r8
P=2147483629
ls kt4_++--_$P.sing ks5_*_$P.sing | xargs -P 2 -I{} bash -c "ulimit -v 2500000; /usr/bin/time -f 'TIME %e s MEM %M KB' timeout 14400 Singular -q {} > {}.out 2>&1"
grep -h RESULT kt4_*_$P.sing.out ks5_*_$P.sing.out > /home/kevxhk/work/runs/ksign_$P.results 2>&1
echo ALLDONE >> /home/kevxhk/work/runs/ksign_$P.results
