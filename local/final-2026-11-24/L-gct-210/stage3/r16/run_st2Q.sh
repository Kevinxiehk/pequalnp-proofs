#!/bin/sh
# Round 17: DRIVER for COMPUTE-stage3 item 14(a) -- (PR3) stratum (II), dim Delta = 2, EXACT over Q (slimgb; never modStd).
# Usage:  sh run_st2Q.sh MODE CHARTLIST [TIMEOUT_S] [VMEM_KB]
#   MODE = lin (x*-linear relaxation; unit => chart closed) | full | cal (calibration, must be NON-unit)
#   CHARTLIST = "s1:00 s1:01 ..." (sigma-chart : x*-chart I J), or "all" = the 20 charts {s1,s0} x {0,1} x {0..4}
# One Singular process per chart, sequential; results appended to st2Q_<MODE>.log as "ST2Q mode schart IJ alg: dim .. unit .. time ..".
cd /home/kevxhk/work/L-gct-210/stage3/r16
MODE=$1; LIST=$2; TO=${3:-3600}; VM=${4:-6000000}
if [ "$LIST" = "all" ]; then LIST=""; for s in s1 s0; do for i in 0 1; do for j in 0 1 2 3 4; do LIST="$LIST $s:$i$j"; done; done; done; fi
if [ "$MODE" = "cal" ]; then LIST="s1:00"; fi
for c in $LIST; do
  s=${c%%:*}; ij=${c##*:}; i=$(echo $ij | cut -c1); j=$(echo $ij | cut -c2)
  f=$(python3 -I st2_bigQ.py $MODE $s $i $j slimgb)
  echo "=== $MODE $s $i$j start $(date -u +%H:%M)" >> st2Q_$MODE.log
  ( ulimit -v $VM; timeout $TO /usr/bin/time -f "time %e s, max %M KB" Singular -q $f 2>&1 | grep -v redefining ) >> st2Q_$MODE.log 2>&1
  echo "=== $MODE $s $i$j end $(date -u +%H:%M)" >> st2Q_$MODE.log
done
