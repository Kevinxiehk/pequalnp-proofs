#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verify2/r8/x5
for f in x5i_*[0-9].sing x5i_*_CAL.sing; do timeout 600 /usr/bin/Singular -q $f 2>&1 | grep -E "RES|NGEN|error|halt" || echo "$f TIMEOUT/none"; done
echo X5RUN_DONE
