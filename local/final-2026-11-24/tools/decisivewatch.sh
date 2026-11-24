#!/bin/bash
# DECISIVE events only: completed big-slot jobs (with verdicts), census CANDIDATE, NONUNIT verdicts, lease failures
W=/home/kevxhk/work; L=$W/L-gct-210; T=/home/kevxhk/.claude/jobs/174da61c/tmp
seen=$(mktemp)
scan() {
  grep -hE " end:| end: |ALLDONE|LEAN WINDOW (start|end)|lean exit code|EXTRA LEAN[A-Z0-9_]* start" $W/runs/bigq3_driver.log $W/runs/st2f2col_driver.log $W/runs/reg2conic_driver.log $W/runs/st2crossfx_driver.log $W/runs/d3aQ_driver.log $W/runs/defsbuild.log 2>/dev/null
  grep -H "CANDIDATE saved" $L/reg2/census_e_q/*.log 2>/dev/null
  grep -H "verdict=NONUNIT" $W/runs/dc3p45/*.manifest 2>/dev/null
  grep -H "NONUNIT" $W/runs/dc3p45cut/*.cutlog $L/rows/r8/orb/sq5big_*.out 2>/dev/null
  grep -H "BEAT FAILED" $T/beat.log 2>/dev/null
  grep -H "" $L/rows/r18/kW.out 2>/dev/null
  grep -H "" $L/rows/r21/kR2C.out $L/rows/r21/kPG.out 2>/dev/null
  grep -H "ST2-R1COFSING end" $W/runs/st2f2col_driver.log 2>/dev/null
}
scan | sort > $seen
while true; do
  sleep 60
  scan | sort > $seen.new
  comm -13 $seen $seen.new | cut -c1-300
  mv $seen.new $seen
done
