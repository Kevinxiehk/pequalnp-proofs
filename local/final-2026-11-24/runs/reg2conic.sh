#!/bin/bash
# reg2 REG2-CONIC-DD primary: omega_e0 on the (2,2|2) conic double deformation, 4 GB, 1 h box, big slot (after Lean window 2)
G=/home/kevxhk/work/L-gct-210/reg2/gb
echo "$(date -u +%T) REG2 conic DD start"
( cd $G && /home/kevxhk/work/tools/bigslot.sh sh -c "ulimit -v 4500000; timeout 3600 python3 -I omega_e0.py 22conic row,0,1 0 row,1 3 defo2=row,1,0" ) > $G/../evidence/logs/r10_conic_omega_e0_big.log 2>&1
echo "$(date -u +%T) REG2 conic DD end: exit $? $(tail -2 $G/../evidence/logs/r10_conic_omega_e0_big.log | tr '\n' ' ' | cut -c1-200)"
