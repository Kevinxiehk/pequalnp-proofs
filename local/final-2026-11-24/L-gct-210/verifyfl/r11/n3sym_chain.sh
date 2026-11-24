#!/bin/bash
# SYM-M [T22]: N-cases START..END descending for chart $1; 2.5 GB, single thread.  DO NOT EDIT WHILE RUNNING.
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r11
C=$1; mkdir -p n3sym
for ci in $(seq ${2:-95} -1 ${3:-0}); do
  timeout 2400 python3 -I n3sym_case.py 2147483629 $C $ci n3sym 900 ${NTMO:-300} 2>&1 | grep -E "VERDICT" || echo "VERDICT n3sym $C case $ci: TIMEOUT/FAIL"
done
echo N3SYM_DONE
