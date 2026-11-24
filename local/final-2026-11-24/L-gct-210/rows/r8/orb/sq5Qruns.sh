#!/bin/bash
# R9-SUMQ5: five active columns, summed cubic (relaxation), all six sign patterns, sequential.  usage: sq5runs.sh P TIMEOUT
cd /home/kevxhk/work/L-gct-210/rows/r8/orb; P=0; TO=${1:-3600}
for SG in ----- +---- ++--- +++-- ++++- +++++; do
  python3 -I sumq.py $SG sq5Q_${SG}.sing $P > /dev/null
  (ulimit -v 2000000; /usr/bin/time -f "%e s %M KB" timeout $TO nice Singular -q sq5Q_${SG}.sing > sq5Q_${SG}.out 2>&1)
  echo "$SG: $(grep RESULT sq5Q_${SG}.out) $(tail -1 sq5Q_${SG}.out)"
done
