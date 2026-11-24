#!/bin/bash
# Survivor runs of the R2 tree (NOTES-stage2 R16): K2 = kernel-reduced charts Gr(3,6) on a hyperplane; V4 = full Gr(4,8) on a line / point.
# input lines on stdin: "K2 CACHE SUBS" or "V4 RUL FIX"
cd /home/kevxhk/work/L-gct-210/stage2
P=2147483629
while read T A B; do
  [ -z "$T" ] && continue
  echo "######## $T $A $B $(date -u +%H:%M:%S)"
  if [ "$T" = K2 ]; then MSV=2000000 timeout 2400 python3 -I r16_F2col_K2.py $A $P "$B" 2>&1 | grep -E "kernel vector|q0\(k,k\)|eliminating|Rabinowitsch|NONUNIT|FAILED|RESULT" | cut -c1-250
  else MSV=2000000 timeout 2400 python3 -I r13_F2col_v4_fx.py $A $P "$B" 2>&1 | grep -E "rank-jump|dim T_1|Rabinowitsch|NONUNIT|parameter ideal|FAILED|RESULT" | cut -c1-250; fi
done
echo "SURV DONE $(date -u +%H:%M:%S)"
