#!/bin/bash
# for each pair and chart: test with hinge t != 0 (HV=t). unit = no third element for t != 0 in that chart.
cd /home/kevxhk/work/L-gct-210/stage3/r22
for pr in "0 1" "0 2" "0 3" "2 3"; do set -- $pr; r=$1; k=$2
  rest=$(python3 -I -c "r,k=$r,$k; print(' '.join(str(i) for i in range(4) if i not in (r,k)))"); set -- $rest; l=$1; n=$2
  gl=$(python3 -I -c "print({0:0,1:0,2:3,3:0}[$l])"); gn=$(python3 -I -c "print({0:0,1:0,2:3,3:0}[$n])")
  out="pair ($r,$k):"
  for j in 0 1 2 3 4; do for p in xl xn v; do
    [ $p = xl ] && [ $j = $gl ] && continue; [ $p = xn ] && [ $j = $gn ] && continue
    f=$(python3 -I kn2_fam.py $r $k $p$j t); res=$(bash -c "ulimit -v 500000; timeout 120 Singular -q $f" 2>&1 | grep -o "unit [01]")
    out="$out $p$j:${res:-T}"
  done; done
  echo "$out" | sed 's/unit 1/U/g; s/unit 0/N/g'
done
