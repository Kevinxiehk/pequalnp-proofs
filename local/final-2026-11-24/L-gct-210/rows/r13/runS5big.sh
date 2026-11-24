#!/bin/bash
# big-slot extras (round 14): support-4 case G and the nine support-5 cases, mod P1 = 2147483629; each: Singular -q FILE > FILE.out
cd /home/kevxhk/work/L-gct-210/rows/r13
for f in c4_G2 c5_P2 c5_P3 c5_P4 c5_P5 c5_PP c5_S23 c5_G4 c5_R4 c5_R5; do /usr/bin/time -f "%e s %M KB" Singular -q $f.sing > $f.big.out 2>&1; done
