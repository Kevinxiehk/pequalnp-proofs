#!/bin/bash
# Re-verification of every msolve verdict with the hardened drivers (rational coefficients cleared, stale outputs impossible, missing = FAILED).
cd /home/kevxhk/work/L-gct-210/stage2
P=2147483629
run(){ echo "== $1 $(date -u +%H:%M:%S)"; shift; "$@" 2>&1 | grep -E "forms|RESULT|NONUNIT|FAILED|rational|bad prime|Error" | head -6; }
run D003A_onlyF0_negcal timeout 600 python3 -I r11_charts_msolve_fx.py r9/FO2J_charts_D003A_onlyF0.sing 4 $P 1
for f in D003A crossC1 K33 crossA D003ptA D003ptB D04Pa_sg0 D04Pa S2s tworowN; do run $f timeout 1500 python3 -I r11_charts_msolve_fx.py r9/FO2J_charts_${f}_k4.sing 4 $P 1; done
run tworowI_s1 env GAUSS=1 SQRTM1=629208553 timeout 900 python3 -I r11_charts_msolve_fx.py r9/FO2J_charts_tworowI_k4.sing 4 $P 1
run tworowI_s2 env GAUSS=1 SQRTM1=1518275076 timeout 900 python3 -I r11_charts_msolve_fx.py r9/FO2J_charts_tworowI_k4.sing 4 $P 1
run isoSpecA env GAUSS=1 SQRTM1=629208553 SQRT3=59644493 timeout 1200 python3 -I r11_charts_msolve_fx.py r9/FO2J_charts_isoSpecA_k4.sing 4 $P 1
run D04Pasym_sat_modp timeout 2400 python3 -I r11_charts_msolve_fx.py r9/FO2J_charts_D04Pasym_sat_k4.sing 4 $P 1 sg
run D04Pasym_sat_char0_affine env NOTAU=1 timeout 2400 python3 -I r11_charts_msolve_fx.py r9/FO2J_charts_D04Pasym_sat_k4.sing 4 0 1 sg
run D3A_modp timeout 2400 python3 -I r14_D3A_fx.py $P
run D3A_char0 timeout 2400 python3 -I r14_D3A_fx.py 0
echo "ALL DONE $(date -u +%H:%M:%S)"
