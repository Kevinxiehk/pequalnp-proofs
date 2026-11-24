#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r21
run(){ s=$(date -u +%H:%M); /usr/bin/time -f "%e s %M KB" python3 -I /home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py 500 10800 Singular -q $2 > $1.out 2>&1; echo "$1 (start $s, end $(date -u +%H:%M)) | $(tr -s '\n' ' ' < $1.out | cut -c1-600)" >> kR2.out; }
run F5R2 f5r2.sing &
run F4R2 f4r2.sing &
wait; echo ALLDONE >> kR2.out
