#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r12
for k in 0 2 3; do (ulimit -v 1500000; /usr/bin/time -f "%e s %M KB" timeout 1200 Singular -q tBp$k.sing > tBp$k.out 2>&1); echo "chart m$k: $(grep -v redefin tBp$k.out | grep -E 'gauge|KGEN|after|halt|KB|rror' | tr '\n' ' ')" >> kBpar.out; done
echo ALLDONE >> kBpar.out
