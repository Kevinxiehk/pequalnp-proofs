#!/bin/bash
# after Lean window 1 closes: stage2 ST2-ELIM-msolve (seconds each; msolve needs ~1.5 GB virtual)
until grep -q "window: CLOSED" /home/kevxhk/work/runs/leanwindow1.log 2>/dev/null; do sleep 30; done
cd /home/kevxhk/work/L-gct-210/stage2
for f in r9/Dir_D04_P0_B_ii_comp3.sing r9/Dir_D04_P0_B_ii_comp4.sing r9/Dir_D04_P0_B_ii_comp5.sing r9/Dir_D04_P0_B_ii_compB10.sing r9/Dir_D04_P0_B_ii_compB11.sing r9/Dir_D003_Q0_B_3_c0_v123.sing r9/Dir_D003_P0_B_3_c0_v123.sing; do
  echo "== $f $(date -u +%T)"; ( ulimit -v 2000000; timeout 3600 python3 -I r11_elim_msolve.py $f 2147483629 ) 2>&1 | tail -15
done
echo "ALLDONE $(date -u +%T)"
