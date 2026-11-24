#!/bin/bash
# lines with dim K = 1 and q0(k,k) = 0 identically: L'' contains k (rank B_c = 7) -> reduced charts Gr(3,6), Singular std over QQ (proof grade).
cd /home/kevxhk/work/L-gct-210/stage2
for C in "$@"; do
  echo "== $C $(date -u +%H:%M:%S)"
  ENGINE=sing MSV=2000000 timeout 1500 python3 -I r16_F2col_K2.py r16/cache_$C.pkl 0 "" 2>&1 | grep -E "subfamily|kernel vector|q0\(k,k\)|eliminating|Rabinowitsch|NONUNIT|FAILED|RESULT" | cut -c1-200
done
echo "ALL DONE $(date -u +%H:%M:%S)"
