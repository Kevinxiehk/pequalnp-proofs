#!/bin/bash
# like runlog.sh, but enforces a RESIDENT-memory cap (RSSKB, default 500000 kB) with a watchdog; virtual cap 1.3 GB (msolve needs ~1 GB VM to start)
# usage: runlog_rss.sh DIR TIMEOUT LOG
ulimit -v ${ULIM:-1300000}
cap=${RSSKB:-500000}
for f in $1/*.ms; do
  o=${f%.ms}.out; rm -f "$o"; t0=$(date +%s.%N)
  msolve -g 2 -t 1 -f "$f" -o "$o" >/dev/null 2>&1 & pid=$!
  killed=""; maxr=0; start=$(date +%s)
  while kill -0 $pid 2>/dev/null; do
    r=$(awk '/VmRSS/{print $2}' /proc/$pid/status 2>/dev/null); r=${r:-0}
    [ "$r" -gt "$maxr" ] && maxr=$r
    if [ "$r" -gt "$cap" ]; then kill $pid; killed="RSSCAP"; break; fi
    if [ $(( $(date +%s) - start )) -ge $2 ]; then kill $pid; killed="TIMEOUT"; break; fi
    sleep 0.3
  done
  wait $pid 2>/dev/null; rc=$?
  t1=$(date +%s.%N)
  if [ -n "$killed" ]; then v=$killed
  elif [ $rc -ne 0 ] || [ ! -s "$o" ] || [ "$o" -ot "$f" ]; then v="FAILED rc=$rc"
  elif sed -n '/#---/,$p' "$o" | tail -n +2 | grep -q '^\[1\]'; then v=UNIT
  else n=$(grep -o 'length of basis: *[0-9]*' "$o" | grep -o '[0-9]*$'); v="NONUNIT($n)"; fi
  printf "%s %s %.1fs maxRSS=%dMB\n" "$(basename $f)" "$v" "$(echo "$t1 - $t0" | bc)" $((maxr/1024)) >> $3
done
echo DONE >> $3
