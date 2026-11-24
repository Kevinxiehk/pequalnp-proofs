#!/bin/bash
# pair (r,k), all 13 charts, hinge HV (default t-free: no hinge). prints dim/vdim/unit and t-projection
cd /home/kevxhk/work/L-gct-210/stage3/r22
r=$1; k=$2; HV=$3
rest=$(python3 -I -c "r,k=$r,$k; print(' '.join(str(i) for i in range(4) if i not in (r,k)))"); set -- $rest; l=$1; n=$2
gl=$(python3 -I -c "print({0:3,1:3,2:0,3:0}[$l])"); gn=$(python3 -I -c "print({0:3,1:3,2:0,3:0}[$n])")
for j in 0 1 2 3 4; do for p in xl xn v; do
  [ $p = xl ] && [ $j = $gl ] && continue; [ $p = xn ] && [ $j = $gn ] && continue
  f=$(python3 -I famB.py $r $k $p$j $HV); res=$(bash -c "ulimit -v 500000; timeout 90 Singular -q $f" 2>&1 | grep -E "famB|t-proj|^PT|E\[" | tr '\n' ' ' | cut -c1-260)
  echo "$p$j: ${res:-TIMEOUT}"
done; done
