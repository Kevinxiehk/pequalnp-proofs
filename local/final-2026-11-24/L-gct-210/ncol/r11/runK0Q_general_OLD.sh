#!/bin/bash
# NCOL-K0Q driver (round 11): CONJECTURE K0 over Q.  Jobs = (chart (0,1) of Gr(2,10) [covers r_a = 2 or, by a<->b, r_b = 2]) x (7 charts of
# (Q2,Q3) in P^6) x (Rabinowitsch index I in {0, 2}: classes {0,1} and {2,3,4} under the chart stabiliser) + (sub-case (1,1)) x (3 charts) x
# (I in {0, 1}: classes {0} and {1,2,3,4} under the stabiliser of the chart a_0 = 1).  K0 <=> every job prints VERDICT 1 (unit over Q).
# Resumable: a job is skipped if jobs/<id>.verdict exists.  Env: ULIM (virtual KB, default 8000000), JT (per-job seconds, default 3600),
# CH (characteristic, default 0 = Q; use a prime only for triage).
cd "$(dirname "$0")"; mkdir -p jobs
ULIM=${ULIM:-8000000}; JT=${JT:-3600}; CH=${CH:-0}
joblist() {
  # most decisive first: the small (1,1) product sub-case (where the e = 1 census found products), then the generic chart (0,1),
  # Q2-charts (d2 != 0, the generic e = 1 situation) before Q3-charts, and I = 2 (only m_2 may vanish) before I = 0
  for LC in 0 1 2; do for I in 1 0; do echo "s11_L${LC}_I${I} k0q_11.py $LC $I"; done; done
  for QC in 0 1 2 3 4 5 6; do for I in 2 0; do echo "c01_Q${QC}_I${I} k0q.py 0,1 $QC $I"; done; done
}
joblist | while read id gen args; do
  v=jobs/${id}_ch$CH.verdict; [ -f $v ] && continue
  python3 -I $gen $args jobs/${id}_ch$CH.sing $CH
  t0=$(date +%s); r=$( (ulimit -v $ULIM; timeout $JT Singular -q jobs/${id}_ch$CH.sing 2>&1) | grep -E 'VERDICT|halt|error' | tr '\n' ' ')
  rc=$?; t1=$(date +%s)
  if echo "$r" | grep -q VERDICT; then echo "$id $r" > $v; else echo "$id FAILED/TIMEOUT ($r) after $((t1-t0))s" >> K0Q_failed.log; fi
  echo "$(date -u +%H:%M) $id ch$CH ${r:-TIMEOUT} $((t1-t0))s" >> K0Q.log
done
echo "DONE $(date -u +%H:%M)" >> K0Q.log
