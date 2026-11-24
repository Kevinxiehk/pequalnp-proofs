#!/bin/bash
# coordinator tick every 210 s: PR check, fork sync, helper STATUS lines, queue entries, lease
W=/home/kevxhk/work; L=$W/L-gct-210; qseen=$(wc -l < $W/QUEUE.md)
while true; do
  pr=$($W/tools/dupcheck.sh 2>&1 | grep -v "dupcheck done" | tr '\n' ';'); pr=${pr:-none}
  fk=$($W/tools/sync.sh 2>&1 | tr '\n' ' ' | cut -c1-140)
  st=""
  for r in verify2 verifyfl rows stage2 stage3 reg2 leanfl leanzbf ncol; do
    s=$(grep '^STATUS' $L/NOTES-$r.md 2>/dev/null | tail -1 | cut -c1-170); st="$st
  [$r] ${s:-no STATUS yet}"
  done
  qn=$(wc -l < $W/QUEUE.md); qnew=""; [ $qn -gt $qseen ] && qnew=$(tail -n $((qn-qseen)) $W/QUEUE.md | tr '\n' ';'); qseen=$qn
  lease=$(tail -1 /home/kevxhk/.claude/jobs/174da61c/tmp/beat.log)
  br=$(cd /home/kevxhk/code/coord-L-gct-210 && git fetch -q origin coord-L-gct-210 2>/dev/null && o=$(cat /home/kevxhk/.claude/jobs/174da61c/tmp/coord_seen.sha 2>/dev/null) && n=$(git rev-parse origin/coord-L-gct-210) && if [ "$o" != "$n" ]; then c=$(git diff --name-only $o $n | grep -v "^local/" | wc -l); echo $n > /home/kevxhk/.claude/jobs/174da61c/tmp/coord_seen.sha; [ $c -gt 0 ] && echo "BRANCH UPDATE: $c non-local files"; fi)
  echo "TICK $(date -u +%H:%M) | PR on L_gct_210: $pr | fork: $fk | lease: $lease | new queue: ${qnew:-none}${br:+ | $br}$st"
  sleep 210
done
