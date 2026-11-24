#!/bin/bash
# rows R10-SUMQ5-note: the five-column summed-cubic patterns need the big slot (7 GB); one at a time, interleaving with bigq2 via the shared slot
O=/home/kevxhk/work/L-gct-210/rows/r8/orb
for SG in +---- ++--- +++-- ++++- +++++; do
  echo "$(date -u +%T) SUMQ5 $SG start"
  ( cd $O && python3 -I sumq.py $SG sq5_${SG}_2147483629.sing 2147483629 > /dev/null && /home/kevxhk/work/tools/bigslot.sh sh -c "ulimit -v 7000000; /usr/bin/time -f '%e s %M KB' timeout 10800 Singular -q sq5_${SG}_2147483629.sing" ) > $O/sq5big_${SG}.out 2>&1
  echo "$(date -u +%T) SUMQ5 $SG end: $(grep -h RESULT $O/sq5big_${SG}.out | tail -1) $(tail -1 $O/sq5big_${SG}.out)"
done
echo "$(date -u +%T) ALLDONE"
