#!/bin/bash
# rational radical cells rc6 (w(tau)) + rc7 (chi_3) for the piece-IV leftovers and the P2 sample (one job at a time, <= 2.5 GB)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
run 1800 env RCS=6,7 python3 -I radcell3.py 2147483629 A 0 t0c 01 rad/w_A0_t0c_01 900 t0/t0c_A_c0_01_None_N.ms.gb
run 1800 env RCS=6,7 python3 -I radcell3.py 2147483629 A 0 pc P2/z1:z1:z1/- rad/w_A0_pc_P2_z1z1z1 600
for d in 02 12; do run 1800 env RCS=6,7 python3 -I radcell3.py 2147483629 A 0 t0c $d rad/w_A0_t0c_$d 900 t0/t0c_A_c0_${d}_None_N.ms.gb; done
echo "$(date -u +%T) chain16 done" >> chain13.log
