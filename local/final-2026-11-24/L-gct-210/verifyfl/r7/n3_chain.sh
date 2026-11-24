#!/bin/bash
# [T22]: all 96 N-cases (each with the three S-cells) via n3_case.py; m = $1, p = 2147483629; order: cheap rho = 0, 1 first, rho = 2 last
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r7
M=$1
for ci in $(seq ${2:-95} -1 ${3:-0}); do
  timeout 3000 python3 -I n3_case.py 2147483629 $M $ci n3 1200 ${NTMO:-120} 2>&1 | grep -E "VERDICT|Error|error|Traceback" || echo "VERDICT n3 case $ci m=$M: TIMEOUT/FAIL"
done
echo N3_DONE
