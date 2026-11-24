#!/bin/sh
# Round 19: sigma = 0 part of the column-element follow-up, exact over Q: (1) plain colel charts J = 0..4, I = 0,1; (2) stratum (II) proper on the
# column-element locus, J = 2, I = 0, the 64 charts c0 c1 c2 in {0,1,3,4}.
cd /home/kevxhk/work/L-gct-210/stage3/r16
ulimit -v 900000
for I in 0 1; do for J in 0 1 2 3 4; do f=$(python3 -I st2_bigQ.py colel s0 $I $J slimgb 0); timeout 300 Singular -q $f 2>&1 | grep ST2Q; done; done
for c0 in 0 1 3 4; do for c1 in 0 1 3 4; do for c2 in 0 1 3 4; do
  f=$(python3 -I st2_bigQ.py colel s0 0 2 slimgb 0 $c0 $c1 $c2); echo "c=$c0$c1$c2 $(timeout 300 Singular -q $f 2>&1 | grep ST2Q)"
done; done; done
