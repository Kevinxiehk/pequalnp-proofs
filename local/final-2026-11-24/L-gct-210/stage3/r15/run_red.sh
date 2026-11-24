#!/bin/sh
# (alpha1) |supp W| = 2 reduced K_f systems (c1), (c3): all Gr charts x {w, c3}, char 0 (q) and P1 (p), plus calibrations d2, line.
cd /home/kevxhk/work/L-gct-210/stage3/r15
ulimit -v 1000000
for P in 0 2147483629; do for c in c1 c3; do for ch in 0 1 2; do for iso in w c; do
  f=$(python3 -I s2red.py $c $ch $iso $P)
  timeout 300 Singular -q $f
done; done; done; done
for P in 0 2147483629; do for c in c1 c3; do for cal in d2 d3 line; do
  f=$(python3 -I s2red.py $c 0 w $P $cal); echo "CAL $cal P=$P"; timeout 300 Singular -q $f
done; done; done
