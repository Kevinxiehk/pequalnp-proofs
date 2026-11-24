#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
for c in 0 1 2; do for n in 0 1 2 3 4 5; do python3 -I p2_mine.py $c $n 4; timeout 600 Singular -q p2mine_${c}_${n}_4.sing; done; done > p2mine.log 2>&1
for c in 0 1; do python3 -I p2_mine.py $c 3 2; timeout 600 Singular -q p2mine_${c}_3_2.sing; done >> p2mine.log 2>&1
echo done >> p2mine.log
