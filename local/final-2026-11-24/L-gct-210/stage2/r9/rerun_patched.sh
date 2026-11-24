#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
for f in crossC1 K33 crossA D003ptA D003ptB D04Pa_sg0 D04Pa S2s; do
  echo "== $f $(date -u +%H:%M:%S)"; timeout 1500 python3 -I r11_charts_msolve.py r9/FO2J_charts_${f}_k4.sing 4 2147483629 1 2>&1 | grep -E "forms|RESULT|NONUNIT" | head -4
done
echo "== D04Pasym_sat param $(date -u +%H:%M:%S)"; timeout 2500 python3 -I r11_charts_msolve.py r9/FO2J_charts_D04Pasym_sat_k4.sing 4 2147483629 1 sg 2>&1 | grep -E "forms|RESULT|NONUNIT" | head -40
echo "ALL DONE $(date -u +%H:%M:%S)"
