#!/bin/bash
# round 10: exact 16x16-minor certificates on the leftover lines s = s0 (x t) of the (ii-g) curve family 211g1 (row 0 -> 1), s0 in Q(w)
# (leftovers of r10_g1_row01_minors.log = the 5-minor run).  Uses the fixed greedy_num (row normalisation, exact omega reduction).
G=/home/kevxhk/work/L-gct-210/reg2/gb; L=/home/kevxhk/work/L-gct-210/reg2/evidence/logs; cd $G; ulimit -v 1000000
n=1
for s0 in "w" "-1" "0" "w+1" "w-1" "(w-1)/3"; do n=$((n+1))
  ( echo "# $(date -u +%H:%M) cmd: python3 -I gen_rank_defo.py 211g1 row 0 1 16 30 2$n fix=s:$s0"; timeout 900 python3 -I gen_rank_defo.py 211g1 row 0 1 16 30 2$n "fix=s:$s0" ) > $L/r10_g1_left_$n.log 2>&1
done
echo DONE > $L/r10_g1_left_done.txt
