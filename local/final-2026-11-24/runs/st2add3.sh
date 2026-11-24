#!/bin/bash
# stage2 ST2-S7' addendum 3 (P0_B case ii components) + ST2-B-IND-direct, 3 in parallel
cd /home/kevxhk/work/L-gct-210/stage2/r9
export TMO=10800
one() { ./elim.sh $1 60 > /home/kevxhk/work/runs/st2_${1%.sing}.log 2>&1; echo "EXIT $?" >> /home/kevxhk/work/runs/st2_${1%.sing}.log; }
export -f one
printf "%s\n" Dir_D04_P0_B_ii_comp2.sing Dir_D04_P0_B_ii_comp3.sing Dir_D04_P0_B_ii_comp4.sing Dir_D04_P0_B_ii_comp5.sing Dir_D04_P0_B_ii_compB10.sing Dir_D04_P0_B_ii_compB11.sing Dir_FP0d_c0_v123.sing Dir_FQ0d_c0_v123.sing | xargs -P 3 -I{} bash -c 'one {}'
echo ALLDONE > /home/kevxhk/work/runs/st2add3.done
