#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
for f in r9/FO2J_charts_crossC1_k4.sing r9/FO2J_charts_D04Pa_sg0_k4.sing r9/FO2J_charts_S2s_k4.sing; do
  echo "== $f $(date -u +%H:%M:%S)"; timeout 3000 python3 -I r11_charts_msolve.py $f 4 2147483629 2
done
echo "ALL DONE $(date -u +%H:%M:%S)"
