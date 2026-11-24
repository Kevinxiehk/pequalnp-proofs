#!/bin/bash
# round 10: 16x16-minor certificates on the six non-degenerate quadratic leftover components of 211g1 (row 0 -> 1): rels w^2+w+1 and q(s,w),
# minors selected at an on-locus numerical point (w = exp(2 pi i/3), s = a root of q).
G=/home/kevxhk/work/L-gct-210/reg2/gb; L=/home/kevxhk/work/L-gct-210/reg2/evidence/logs; cd $G; ulimit -v 1000000
n=0
while IFS='|' read -r q v; do n=$((n+1)); q=$(echo $q | sed 's/\*\*/^/g'); v=$(echo $v | tr -d ' ()')
  ( echo "# $(date -u +%H:%M) cmd: python3 -I gen_rank_defo.py 211g1 row 0 1 16 30 3$n \"$q\" num=s:$v"; timeout 900 python3 -I gen_rank_defo.py 211g1 row 0 1 16 30 3$n "$q" "num=s:$v" ) > $L/r10_g1_quad_$n.log 2>&1
done < /home/kevxhk/work/L-gct-210/reg2/evidence/g1_quad_points.txt
echo DONE > $L/r10_g1_quad_done.txt
