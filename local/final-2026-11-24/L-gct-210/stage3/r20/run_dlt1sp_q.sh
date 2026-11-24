#!/bin/sh
cd /home/kevxhk/work/L-gct-210/stage3/r20
ulimit -v 950000
for XI in 00 01 02; do f=$(python3 -I dlt1sp.py 0 $XI 0); timeout 600 Singular -q $f 2>&1 | grep DLT1SP; done
f=$(python3 -I dlt1sp.py 1 x 0); timeout 900 Singular -q $f 2>&1 | grep DLT1SP
