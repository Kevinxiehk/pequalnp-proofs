#!/bin/bash
# round-14 pool chain d (one job at a time, <= 2.5 GB)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad b0
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
# (a) rc0 of t0c-01 with the neutral-column permanent equations (R14.4)
run 1800 env RCS=0 PERM34=1 python3 -I radcell3p.py 2147483629 A 0 t0c 01 rad/p_A0_t0c_01 600 t0/t0c_A_c0_01_None_N.ms.gb
# (e) symbolic [T31] B0, chart A
run 1800 python3 -I b0sym_run.py 2147483629 2 b0/A_R2 600
# (a') the other piece-IV leftovers with perm34, all radical cells
for d in 02 12; do run 1800 env PERM34=1 python3 -I radcell3p.py 2147483629 A 0 t0c $d rad/p_A0_t0c_$d 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done
echo "$(date -u +%T) chain14d done" >> chain13.log
