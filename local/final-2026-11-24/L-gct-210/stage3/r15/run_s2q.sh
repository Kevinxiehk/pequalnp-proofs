#!/bin/sh
# LEMMA S2 over Q (char 0) with slimgb: parallel case (a-charts 2, 3; chart 1 done: s2q_par1.log), then non-parallel (3 a-charts).
# One job, 2 GB cap, sequential.
cd /home/kevxhk/work/L-gct-210/stage3/r15
ulimit -v 2000000
for f in s2l_par2_qs s2l_par3_qs s2l_neq1_qs s2l_neq2_qs s2l_neq3_qs; do timeout 1200 /usr/bin/time -f "$f %e s %M KB" Singular -q $f.sing; done
