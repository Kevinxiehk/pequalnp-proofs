#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r12
for f in x_p_1 x_p_-1 x_q_1 x_q_-1; do (ulimit -v 1000000; /usr/bin/time -f "%e s %M KB" timeout 900 Singular -q $f.sing > $f.out 2>&1); echo "$f: $(grep -v redefin $f.out | grep -E 'C21G|after|halt|KB' | tr '\n' ' ')" >> runx.log; done
echo ALLDONE >> runx.log
