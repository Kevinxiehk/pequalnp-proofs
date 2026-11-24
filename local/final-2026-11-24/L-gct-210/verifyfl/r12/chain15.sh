#!/bin/bash
# round-15 pool chain (one job at a time, <= 2.5 GB, <= 30 min per job).  Waits for chain14g (rc4 of t0c-01).
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad
while kill -0 528460 2>/dev/null; do sleep 5; done
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
# open-chart cover of each piece: rc0..rc3 with gam = 0 (radcell3g), rc5 (radcell3), rc4 last (radcell3, long stages)
for d in 02 12; do
  run 1800 env RCS=0,1,2,3 GAM0=1 python3 -I radcell3g.py 2147483629 A 0 t0c $d rad/g_A0_t0c_$d 600 t0/t0c_A_c0_${d}_None_N.ms.gb
  run 1800 env RCS=5 python3 -I radcell3.py 2147483629 A 0 t0c $d rad/o_A0_t0c_$d 600 t0/t0c_A_c0_${d}_None_N.ms.gb
done
for d in 02 12; do run 1800 env RCS=4 python3 -I radcell3.py 2147483629 A 0 t0c $d rad/o2_A0_t0c_$d 1500 t0/t0c_A_c0_${d}_None_N.ms.gb; done
echo "$(date -u +%T) chain15 done" >> chain13.log
