#!/bin/bash
# round-15 pool chain b (chart B, piece IV of case 0): waits for chain15
cd /home/kevxhk/work/L-gct-210/verifyfl/r12
while kill -0 531786 2>/dev/null; do sleep 5; done
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
run 1800 python3 -I t0_cell.py 2147483629 B 0 t0 600 ab:z1,ab:z2,ab:0,z1:ab,z1:z1,z1:z2,z1:0,z2:ab,z2:z1,z2:z2,z2:0,0:ab,0:z1,0:z2,0:0
run 1800 python3 -I t0b_cell.py 2147483629 B 0 t0 600 ab:ab:z1,ab:ab:z2,ab:ab:0
echo "$(date -u +%T) chain15b done" >> chain13.log
