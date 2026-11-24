#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r12
while pgrep -f "Singular -q s_ff.sin[g]" > /dev/null; do sleep 5; done
for c in p q; do (ulimit -v 1000000; /usr/bin/time -f "%e s %M KB" timeout 1200 Singular -q s_$c.sing > s_$c.out 2>&1); done
