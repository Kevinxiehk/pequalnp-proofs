#!/bin/bash
# round 10 target 3: exact check of the remaining case (iv) of Lemma SK3, four echelon charts, Singular over Q
cd /home/kevxhk/work/L-gct-210/reg2; L=/home/kevxhk/work/L-gct-210/reg2/evidence/logs; ulimit -v 1000000
for ch in D C B A; do
  ( echo "# $(date -u +%H:%M) cmd: python3 -I sk3_exact.py $ch"; timeout 900 /usr/bin/time -f "TIME %e s MEM %M KB" python3 -I sk3_exact.py $ch ) > $L/r10_sk3_$ch.log 2>&1
done
echo DONE > $L/r10_sk3_done.txt
