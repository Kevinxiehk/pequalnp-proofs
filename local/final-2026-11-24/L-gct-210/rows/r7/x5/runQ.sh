#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r7/x5
ulimit -v 2500000
for ch in 11 10 01 00; do timeout 900 Singular -q x5Q_$ch.sing > x5Q_$ch.out 2>&1; done
echo QDONE
