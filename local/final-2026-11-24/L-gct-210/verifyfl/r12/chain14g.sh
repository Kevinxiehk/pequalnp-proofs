#!/bin/bash
# round-14 pool chain g: rc4 of t0c-01 with a 25-min stage timeout (job <= 30 min)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
run 1800 env RCS=4 python3 -I radcell3.py 2147483629 A 0 t0c 01 rad/o2_A0_t0c_01 1500 t0/t0c_A_c0_01_None_N.ms.gb
echo "$(date -u +%T) chain14g done" >> chain13.log
