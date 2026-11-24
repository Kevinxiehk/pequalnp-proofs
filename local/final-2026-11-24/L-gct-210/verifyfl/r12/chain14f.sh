#!/bin/bash
# round-14 pool chain f: rc0 of t0c-01 with gam0 (CONDITIONAL on rc4 being UNIT; R14.6)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
run 1500 env RCS=0 GAM0=1 python3 -I radcell3g.py 2147483629 A 0 t0c 01 rad/g_A0_t0c_01 600 t0/t0c_A_c0_01_None_N.ms.gb
echo "$(date -u +%T) chain14f done" >> chain13.log
