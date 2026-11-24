#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
while pgrep -f "run_msolve_charts.s[h]" >/dev/null; do sleep 10; done
echo "== D04Pasym (sg affine + tau chart) $(date -u +%H:%M:%S)"
timeout 3000 python3 -I r11_charts_msolve.py r9/FO2J_charts_D04Pasym_k4.sing 4 2147483629 2 sg
echo "DONE $(date -u +%H:%M:%S)"
