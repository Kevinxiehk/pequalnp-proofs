#!/bin/bash
# round 20 pool runs: two at a time, RSS cap 500 MB, 3 h timeout each; queue W4P, W5P, then W4Q, W5Q.  Log: kW.out
cd /home/kevxhk/work/L-gct-210/rows/r18
CAP=/home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py
run(){ name=$1; file=$2; s=$(date -u +%H:%M); /usr/bin/time -f "%e s %M KB" python3 -I $CAP 500 10800 Singular -q $file > $name.pool.out 2>&1; echo "$name (start $s, end $(date -u +%H:%M)) | $(grep -v '^$' $name.pool.out | grep -E 'SMW|after|RSSCAP|KB|halt|rror' | tr '\n' ' ')" >> kW.out; }
( run W4P w4_2147483629.sing; run W4Q w4_0.sing ) &
( run W5P w5_2147483629.sing; run W5Q w5_0.sing ) &
wait
echo ALLDONE >> kW.out
