#!/bin/bash
cd /home/kevxhk/work/L-gct-210/leanfl/sing10
ulimit -v 500000
for f in c3_*.sing; do echo "== $f"; timeout 900 Singular -q $f 2>&1 | tail -6; done
echo ALLDONE
