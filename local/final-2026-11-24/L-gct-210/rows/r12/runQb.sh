#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r12
for f in qbA qbC0 qbC1; do (ulimit -v 1000000; /usr/bin/time -f "%e s %M KB" timeout 1500 Singular -q $f.sing > $f.out 2>&1); echo "$f: $(grep -v redefin $f.out | grep -E 'BRED|after|halt|KB|rror' | tr '\n' ' ')" >> kQb.out; done
echo DONE >> kQb.out
