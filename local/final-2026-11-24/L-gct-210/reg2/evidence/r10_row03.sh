#!/bin/bash
# round 10: the col-first double deformations with second row 0 -> 3 (missing in round 9): lift/Gram + 15x15 minors (seed 5, private tmp files)
G=/home/kevxhk/work/L-gct-210/reg2/gb; L=/home/kevxhk/work/L-gct-210/reg2/evidence/logs; cd $G; ulimit -v 1000000
for spec in "22_2_11 col,0,1" "22_2_00 col,0,2"; do set -- $spec
  ( echo "# $(date -u +%H:%M) cmd: python3 -I lift_gram.py $1 row,0,3 - 0 3 row,1 3 defo2=$2"; timeout 1500 python3 -I lift_gram.py $1 row,0,3 - 0 3 row,1 3 defo2=$2 ) > $L/r10_lift_double_$1_row,0,3.log 2>&1
  ( echo "# $(date -u +%H:%M) cmd: python3 -I gen_rank_defo.py $1 row 0 3 15 30 5 defo2=$2"; timeout 1500 python3 -I gen_rank_defo.py $1 row 0 3 15 30 5 defo2=$2 ) > $L/r10_double_$1_0_3.log 2>&1
done
echo DONE >> $L/r10_double_$1_0_3.log
