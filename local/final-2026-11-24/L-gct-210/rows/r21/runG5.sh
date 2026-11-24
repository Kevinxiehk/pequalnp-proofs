#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r21
run(){ s=$(date -u +%H:%M); /usr/bin/time -f "%e s %M KB" python3 -I /home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py 480 10800 Singular -q $2 > $1.out 2>&1; echo "$1 (start $s, end $(date -u +%H:%M)) | $(tr -s '\n' ' ' < $1.out | cut -c1-600)" >> kR2.out; }
run G5F1 g5_1.sing; run G5F2 g5_2.sing; run G5F3 g5_3.sing
echo G5DONE >> kR2.out
