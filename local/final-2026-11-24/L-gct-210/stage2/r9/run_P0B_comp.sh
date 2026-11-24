#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/stage2/r9
comps=("r1*F0+2*F0+F3,r2+1" "r1*F0+2*F0-F3,r2+1" "r1*F0-F0+F3,r2" "r1*F0-F0-F3,r2" "r2*F0+2*F0+F3,r1+1" "r2*F0+2*F0-F3,r1+1" "r2*F0-F0+F3,r1" "r2*F0-F0-F3,r1" "2*r2*F0+F0+F3,r1-r2" "2*r2*F0+F0-F3,r1-r2")
for case in i ii; do
 if [ $case = i ]; then A=f0; B=f3; else A=d0; B=d3; fi
 n=2
 for c in "${comps[@]}"; do
  e=$(echo "$c" | sed "s/F0/$A/g; s/F3/$B/g")
  f=Dir_D04_P0_B_${case}_comp${n}.sing
  sed "s/^ideal I=PI;/ideal I=PI,$e;/" Dir_D04_P0_B_${case}_c0_v123.sing > $f
  echo "== P0_B_$case comp$n [$e] $(date -u +%H:%M:%S)"; TMO=300 ./elim.sh $f 60 2>&1 | sed -n '/ELIM/,$p' | grep -v "^sec" | tr '\n' ' ' | sed 's/   */ /g'; echo
  n=$((n+1))
 done
done
echo DONE
