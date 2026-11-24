#!/bin/bash
# R9-SUMQ5: five active columns, summed cubic (relaxation), all six sign patterns, sequential.  usage: sq5runs.sh P TIMEOUT
cd /home/kevxhk/work/L-gct-210/rows/r8/orb; P=$1; TO=${2:-3600}
for SG in ----- +---- ++--- +++-- ++++- +++++; do
  python3 -I sumq.py $SG sq5_${SG}_$P.sing $P > /dev/null
  (ulimit -v 2000000; /usr/bin/time -f "%e s %M KB" timeout $TO nice Singular -q sq5_${SG}_$P.sing > sq5_${SG}_$P.out 2>&1)
  echo "$SG: $(grep RESULT sq5_${SG}_$P.out) $(tail -1 sq5_${SG}_$P.out)"
done
