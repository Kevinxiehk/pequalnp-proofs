#!/bin/bash
# usage: runlog.sh DIR TIMEOUT LOG  -> sequential msolve (1 thread) on DIR/*.ms; verdict lines appended to LOG.
# Stale-safe (COMPUTE-ERRATA E-STALE-OUTPUT): the output is deleted before each run; a missing or older output, or rc != 0, is FAILED.
ulimit -v ${ULIM:-8000000}
for f in $1/*.ms; do
  o=${f%.ms}.out; rm -f "$o"; t0=$(date +%s.%N)
  timeout $2 msolve -g 2 -t 1 -f "$f" -o "$o" >/dev/null 2>&1; rc=$?
  t1=$(date +%s.%N)
  if [ $rc -eq 124 ]; then v=TIMEOUT
  elif [ $rc -ne 0 ] || [ ! -s "$o" ] || [ "$o" -ot "$f" ]; then v="FAILED rc=$rc"
  elif sed -n '/#---/,$p' "$o" | tail -n +2 | grep -q '^\[1\]'; then v=UNIT
  else n=$(grep -o 'length of basis: *[0-9]*' "$o" | grep -o '[0-9]*$'); v="NONUNIT($n)"; fi
  printf "%s %s %.1fs\n" "$(basename $f)" "$v" "$(echo "$t1 - $t0" | bc)" >> $3
done
echo DONE >> $3
