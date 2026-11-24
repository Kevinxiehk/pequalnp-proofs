#!/bin/bash
# big-slot driver (stage3, ST3-DLT0D): dim Delta = 0 with the function-of-h reduction. Each chart: ulimit 4 GB, timeout 1500 s (< 30 min).
# usage: run_dlt0d.sh P  (P = 32003 triage, or 0 = exact over Q with slimgb). s1: 6 charts; s0: chart h_0 = 1 (the minor hinge forces h_0 != 0), 6 charts.
cd /home/kevxhk/work/L-gct-210/stage3/r24
P=$1
for CH in S1 B1 S2 B2 AC BC; do f=$(python3 -I dlt0d.py $CH $P s1 0); bash -c "ulimit -v 4000000; timeout 1500 Singular -q $f" 2>&1 | grep -E "DLT0D|halt" | sed "s/^/s1 $CH: /" >> dlt0d_$P.log || echo "s1 $CH: TIMEOUT" >> dlt0d_$P.log; done
for K in 0; do for CH in S1 B1 S2 B2 AC BC; do f=$(python3 -I dlt0d.py $CH $P s0 $K); bash -c "ulimit -v 4000000; timeout 1500 Singular -q $f" 2>&1 | grep -E "DLT0D|halt" | sed "s/^/s0 K$K $CH: /" >> dlt0d_$P.log || echo "s0 K$K $CH: TIMEOUT" >> dlt0d_$P.log; done; done
