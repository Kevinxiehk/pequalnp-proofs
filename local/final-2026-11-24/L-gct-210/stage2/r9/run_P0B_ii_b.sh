#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/stage2/r9
comps=("r2*F0+2*F0+F3,r1+1" "r2*F0+2*F0-F3,r1+1" "r2*F0-F0+F3,r1" "r2*F0-F0-F3,r1" "2*r2*F0+F0+F3,r1-r2" "2*r2*F0+F0-F3,r1-r2")
n=6
for c in "${comps[@]}"; do
  e=$(echo "$c" | sed "s/F0/d0/g; s/F3/d3/g"); f=Dir_D04_P0_B_ii_compB${n}.sing
  sed "s/^ideal I=PI;/ideal I=PI,$e;/" Dir_D04_P0_B_ii_c0_v123.sing > $f
  echo "== P0_B_ii comp$n [$e] $(date -u +%H:%M:%S)"; TMO=400 ./elim.sh $f 60 2>&1 | sed -n '/ELIM/,$p' | grep -v "^sec" | tr '\n' ' ' | sed 's/   */ /g'; echo
  n=$((n+1))
done
echo DONE
