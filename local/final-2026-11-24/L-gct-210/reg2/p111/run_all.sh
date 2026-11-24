#!/bin/bash
cd /home/kevxhk/work/L-gct-210/reg2/p111; ulimit -v 1000000
while read S; do timeout 900 python3 -I inc111.py $S; done < reps.txt > /home/kevxhk/work/L-gct-210/reg2/evidence/logs/r11_inc111.log 2>&1
echo DONE >> /home/kevxhk/work/L-gct-210/reg2/evidence/logs/r11_inc111.log
