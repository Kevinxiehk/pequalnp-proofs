#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r12
while pgrep -f "[r]unBU23.sh" > /dev/null; do sleep 10; done
for f in P2_U2_0 P2_U2_1 P3_U2_0 P3_U2_1; do (ulimit -v 1500000; /usr/bin/time -f "%e s %M KB" timeout 900 Singular -q $f.sing > $f.out 2>&1); echo "$f: $(grep -v redefin $f.out | grep -E 'gauge|KGEN|halt|KB|rror' | tr '\n' ' ')" >> kBU23.out; done
echo ALLDONE-U2 >> kBU23.out
