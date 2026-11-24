#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r21
run(){ s=$(date -u +%H:%M:%S); /usr/bin/time -f "%e s %M KB" python3 -I /home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py 480 10800 Singular -q $2 > $1.out 2>&1; echo "$1 (start $s, end $(date -u +%H:%M:%S)) | $(tr -s '\n' ' ' < $1.out | cut -c1-400)" >> kR2C.out; }
for x in "$@"; do run $x $x.sing; done
echo "DONE $*" >> kR2C.out
