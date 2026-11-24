#!/bin/sh
# Round 19: BIG-SLOT driver -- unified stratum (II)/(III) system, sub-case dim Delta = 2 (NOTES-stage3 secs. 37-39):
#   "H-plane + zero-column-sum x*" + "x* has a SECOND nonzero column" (Rabinowitsch u3 r_{I2,J2} = 1; chart r_{I,J} = 1).
#   UNIT on all 16 charts (8 symmetry orbits x 2 sigma-charts) <=> every solution has x* supported in ONE column (column element).
# Usage: sh run_twocol.sh P [TIMEOUT_S] [VMEM_KB]   (P = 0 exact over Q with slimgb [proof grade]; P = 2147483629 = triage at P1 with std)
cd /home/kevxhk/work/L-gct-210/stage3/r16
P=${1:-0}; TO=${2:-3600}; VM=${3:-6000000}
ALG=slimgb; [ "$P" != "0" ] && ALG=std
while read I J I2 J2; do for S in s1 s0; do
  f=$(python3 -I st2_bigQ.py twocol $S $I $J $ALG $P $I2 $J2)
  echo "=== twocol $S $I$J $I2$J2 P=$P start $(date -u +%H:%M)" >> twocol_$P.log
  ( ulimit -v $VM; timeout $TO /usr/bin/time -f "time %e s, max %M KB" Singular -q $f 2>&1 | grep -v redefining ) >> twocol_$P.log 2>&1
done; done < twocol_reps.txt
