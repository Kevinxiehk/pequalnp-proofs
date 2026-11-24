#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2/r9
for f in FO2J_charts_S2s_k4.sing FO2J_charts_crossC1_k4.sing; do
  ( ulimit -v 2500000; /usr/bin/time -f "TIME %e s MEM %M KB" timeout 10800 Singular -q $f > /home/kevxhk/work/runs/st2_${f%.sing}.log 2>&1; echo "EXIT $?" >> /home/kevxhk/work/runs/st2_${f%.sing}.log )
done
