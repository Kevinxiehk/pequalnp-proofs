#!/bin/bash
# NCOL-K0Q driver, REWRITTEN 07:25 UTC round 11 (general CONJECTURE K0 is FALSE, NOTES-ncol R11.7): RESTRICTED K0 classification.
# Find all 2-dim zero-row column-centred level S with e = 1 and ZERO-FREE defect line m of the a3 shape (m0=m1=m2) or the b22 shape
# (m0=m1, m2=m3).  Big-slot part = the r_a = 2 Pluecker charts (a_i,a_j) [r_b = 2 by the swap a <-> b, which preserves m], orbit
# representatives under the shape symmetry (a3: S3 x S2 -> {0,1},{0,3},{3,4}; b22: <(01),(23),(02)(13)> -> {0,1},{0,2},{0,4}), x 7 charts
# of (Q2,Q3).  The (1,1) charts are small and run in the pool (runK0R_local.sh).  Generator k0r.py, Singular std over Q (exact).
# Per job: VERDICT 1 = no such S in that chart; VERDICT 0 = members exist, DIM/VDIM printed, reduced GB in jobs/<id>_ch0.gb.
# Resumable: a job is skipped if jobs/<id>_ch$CH.verdict exists.  Env: ULIM (virtual KB, default 8000000), JT (s/job, default 3600), CH.
cd "$(dirname "$0")"; mkdir -p jobs
ULIM=${ULIM:-8000000}; JT=${JT:-3600}; CH=${CH:-0}
joblist() {
  # (the (1,1) sub-case is DONE exactly in the pool: NOTES-ncol R11.14/R11.16, so no (1,1) jobs here)
  # then the r_a = 2 Pluecker charts: b22 then a3; the chart with both pivots inside a shape class first
  for SH in b22 a3; do
    if [ $SH = a3 ]; then PC="0,1 0,3 3,4"; else PC="0,1 0,2 0,4"; fi
    for p in $PC; do for QC in 0 1 2 3 4 5 6; do echo "r_${SH}_P${p/,/_}_Q$QC $SH P:$p $QC"; done; done
  done
}
joblist | while read id sh chart qc; do
  v=jobs/${id}_ch$CH.verdict; [ -f $v ] && continue
  python3 -I k0r.py $sh $chart $qc jobs/${id}_ch$CH.sing $CH
  t0=$(date +%s); r=$( (ulimit -v $ULIM; timeout $JT Singular -q jobs/${id}_ch$CH.sing 2>&1) | grep -E 'VERDICT|halt|error' | tr '\n' ' '); t1=$(date +%s)
  if echo "$r" | grep -q VERDICT; then echo "$id $r" > $v; else echo "$(date -u +%H:%M) $id FAILED/TIMEOUT ($r) after $((t1-t0))s" >> K0Q_failed.log; fi
  echo "$(date -u +%H:%M) $id ch$CH ${r:-TIMEOUT} $((t1-t0))s" >> K0Q.log
done
echo "DONE $(date -u +%H:%M)" >> K0Q.log
