#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r12
for f in tBz2 tBq0 tBz2q tBi0 tBiz2; do (ulimit -v 1500000; /usr/bin/time -f "%e s %M KB" timeout 1200 Singular -q $f.sing > $f.out 2>&1); echo "$f: $(grep -v redefin $f.out | grep -E 'gauge|KGEN|halt|KB|rror' | tr '\n' ' ')" >> kBpar.out; done
echo ALLDONE >> kBpar.out
