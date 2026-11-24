#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r11
ulimit -v 2500000
for iv in 0 1 2 3 4 5; do for inn in 0 1 2 3 4 5; do python3 -I alpha0s3_mine.py $iv $inn 4; timeout 300 Singular -q a0s3mine_${iv}_${inn}_4.sing; done; done > a0s3mine.log 2>&1
for iv in 0 3; do python3 -I alpha0s3_mine.py $iv 1 2; timeout 300 Singular -q a0s3mine_${iv}_1_2.sing; done >> a0s3mine.log 2>&1
echo done >> a0s3mine.log
