#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2/r9
export TMO=10800
jobs_list() {
  for s in Dir_D04_Q0_B_i_c0_v123.sing Dir_D04_Q0_B_ii_c0_v123.sing Dir_D04_P0_B_ii_c0_v123.sing Dir_D04_P0_A_i_c0_v123.sing; do echo "elim $s"; done
  for t in Q0_A_3 Q0_B_2 Q0_B_3 P0_A_3 P0_B_2 P0_B_3; do echo "d003 $t"; done
}
one() { set -- $1; if [ "$1" = elim ]; then ./elim.sh $2 60 > /home/kevxhk/work/runs/st2s7_${2%.sing}.log 2>&1; else ./run_d003.sh $2 > /home/kevxhk/work/runs/st2s7_d003_$2.log 2>&1; fi; echo "EXIT $?" >> /home/kevxhk/work/runs/st2s7_${2%.sing}.log; }
export -f one
jobs_list | xargs -P 3 -I{} bash -c 'one "{}"'
echo ALLDONE > /home/kevxhk/work/runs/st2s7.done
