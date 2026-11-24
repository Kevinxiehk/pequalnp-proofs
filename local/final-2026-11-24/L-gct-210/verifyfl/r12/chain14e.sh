#!/bin/bash
# round-14 pool chain e (one job at a time, <= 2.5 GB): staged refinement via the open radical chart {r_3 != 0}
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
run 1800 env RCS=4,5 python3 -I radcell3.py 2147483629 A 0 t0c 01 rad/o_A0_t0c_01 600 t0/t0c_A_c0_01_None_N.ms.gb
echo "$(date -u +%T) chain14e done" >> chain13.log
