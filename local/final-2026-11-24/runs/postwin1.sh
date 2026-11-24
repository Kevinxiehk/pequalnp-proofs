#!/bin/bash
# after Lean window 1 closes: R9-SUMQ5 at P1 for the remaining five-column patterns (normal pool, sequential, 2 GB cap)
until grep -q "window: CLOSED" /home/kevxhk/work/runs/leanwindow1.log 2>/dev/null; do sleep 30; done
cd /home/kevxhk/work/L-gct-210/rows/r8/orb; P=2147483629
for SG in +---- ++--- +++-- ++++- +++++; do
  if grep -q RESULT sq5_${SG}_$P.out 2>/dev/null; then echo "$(date -u +%T) $SG already: $(grep RESULT sq5_${SG}_$P.out)"; continue; fi
  python3 -I sumq.py $SG sq5_${SG}_$P.sing $P > /dev/null
  (ulimit -v 2000000; /usr/bin/time -f "%e s %M KB" timeout 7200 nice Singular -q sq5_${SG}_$P.sing > sq5_${SG}_$P.out 2>&1)
  echo "$(date -u +%T) $SG: $(grep RESULT sq5_${SG}_$P.out) $(tail -1 sq5_${SG}_$P.out)"
done
echo "$(date -u +%T) ALLDONE"
