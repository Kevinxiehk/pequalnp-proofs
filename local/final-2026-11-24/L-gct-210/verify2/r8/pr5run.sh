#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verify2/r8/pr5
for f in $(ls pr5_*.sing | grep -v CAL) $(ls pr5_*_CAL.sing); do timeout 600 /usr/bin/Singular -q $f 2>&1 | grep -E "RES|NGEN|error|halt" | tr '\n' ' '; echo " [$f]"; done
echo PR5RUN_DONE
