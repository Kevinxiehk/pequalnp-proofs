#!/bin/bash
# [T22] via gen_n3g: N-cases START..END (descending) for m = $1; 2.5 GB, single thread; do not edit while running
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r9
M=$1; mkdir -p n3g
for ci in $(seq ${2:-65} -1 ${3:-0}); do
  timeout 3000 python3 -I n3g_case.py 2147483629 $M $ci n3g 1200 ${NTMO:-600} 2>&1 | grep -E "VERDICT|Error|Traceback" || echo "VERDICT n3g case $ci m=$M: TIMEOUT/FAIL"
done
echo N3G_DONE
