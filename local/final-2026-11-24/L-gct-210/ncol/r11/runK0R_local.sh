#!/bin/bash
# local (pool) part of the RESTRICTED K0 classification: the (1,1) sub-case charts (small), exact over Q by default.
# Resumable (jobs11/<id>.verdict); ULIM virtual KB (default 500000), JT seconds (default 900), CH (default 0).
cd "$(dirname "$0")"; mkdir -p jobs11
ULIM=${ULIM:-500000}; JT=${JT:-900}; CH=${CH:-0}
joblist() {
  for SH in b22 a3; do
    if [ $SH = a3 ]; then CH11="0,0 0,1 0,3 3,0 3,3 3,4"; else CH11="0,0 0,1 0,2 0,4 4,0 4,4"; fi
    for c in $CH11; do for QC in 3 1 6; do echo "${SH}_11_${c/,/_}_Q$QC $SH 11:$c $QC"; done; done
  done
}
joblist | while read id sh chart qc; do
  v=jobs11/${id}_ch$CH.verdict; [ -f $v ] && continue
  python3 -I k0r.py $sh $chart $qc jobs11/${id}_ch$CH.sing $CH
  t0=$(date +%s); r=$( (ulimit -v $ULIM; timeout $JT Singular -q jobs11/${id}_ch$CH.sing 2>&1) | grep -E 'VERDICT|halt|error' | tr '\n' ' '); t1=$(date +%s)
  if echo "$r" | grep -q VERDICT; then echo "$id $r" > $v; else echo "$(date -u +%H:%M) $id ch$CH FAILED/TIMEOUT ($r) $((t1-t0))s" >> K0R11_failed.log; fi
  echo "$(date -u +%H:%M) $id ch$CH ${r:-TIMEOUT} $((t1-t0))s" >> K0R11.log
done
echo "DONE $(date -u +%H:%M)" >> K0R11.log
