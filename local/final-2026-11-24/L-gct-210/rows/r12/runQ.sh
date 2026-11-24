#!/bin/bash
# exact char-0 runs (round 13); each capped at 1 GB, 25 min
cd /home/kevxhk/work/L-gct-210/rows/r12
for f in "$@"; do (ulimit -v 1000000; /usr/bin/time -f "%e s %M KB" timeout 1500 Singular -q $f.sing > $f.out 2>&1); echo "$f: $(grep -v redefin $f.out | grep -E 'gauge|KGEN|after|halt|KB|rror' | tr '\n' ' ')" >> kQ.out; done
echo "DONE $*" >> kQ.out
