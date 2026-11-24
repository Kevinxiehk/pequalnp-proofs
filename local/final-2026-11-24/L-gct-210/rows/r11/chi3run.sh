#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r11
while pgrep -f "Singular -q chi3_1.sin[g]" > /dev/null; do sleep 5; done
for K0 in 0 1; do (ulimit -v 1500000; /usr/bin/time -f "%e s %M KB" timeout 1800 Singular -q chi3_$K0.sing > chi3_${K0}_long.out 2>&1); done
