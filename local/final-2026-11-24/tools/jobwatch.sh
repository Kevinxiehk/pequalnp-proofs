#!/bin/bash
# local job events: C1 cases/target hits, Groebner verdicts (R6-1, VF-B, DC3), lease failures
T=/home/kevxhk/.claude/jobs/174da61c/tmp; W=/home/kevxhk/work
touch $T/c1/S.log $T/c1/N.log $T/beat.log
tail -n0 -F $T/c1/S.log $T/c1/N.log $T/beat.log 2>/dev/null | grep --line-buffered -E "TARGET HIT|UNCONFIRMED|^CASE|NO SEED|Traceback|Error|BEAT FAILED" &
prev=$(grep -lE "RESULT|EXIT|error|halt" $T/r61/*.out $T/vfb/m*.out $T/vfb/c*.out $W/runs/dc3/*.log 2>/dev/null | sort | tr '\n' ' ')
while true; do
  cur=$(grep -lE "RESULT|EXIT|error|halt" $T/r61/*.out $T/vfb/m*.out $T/vfb/c*.out $W/runs/dc3/*.log 2>/dev/null | sort | tr '\n' ' ')
  for f in $cur; do case " $prev " in *" $f "*) ;; *) echo "FINISHED $(basename $f): $(grep -E 'RESULT|after saturation|dim|EXIT|TIME|error' $f | tr '\n' ' ' | cut -c1-300)";; esac; done
  prev=$cur; sleep 60
done
