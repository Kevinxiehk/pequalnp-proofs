#!/bin/bash
# round-13 pool chain d, one job at a time (<= 2.5 GB, single thread): radical S-cells (R13.4)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad
run() { echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout 2400 python3 -I "$@") >> chain13.out 2>&1; }
for d in 01 02 12; do run radcell.py 2147483629 A 0 t0c $d rad/A0_t0c_$d 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done
run radcell.py 2147483629 A 0 t0b ab:ab:z1 rad/A0_t0b_ababz1 600
run radcell.py 2147483629 A 0 pc P2/ab:z1:0/- rad/A0_pc_P2_abz10 600
run radcell.py 2147483629 A 0 t0c ne rad/A0_t0c_ne 600
echo "$(date -u +%T) chain13d done" >> chain13.log
