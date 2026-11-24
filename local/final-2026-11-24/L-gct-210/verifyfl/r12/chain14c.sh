#!/bin/bash
# round-14 pool chain c (one job at a time, <= 2.5 GB): waits for the s = 5 pilot (PID 453541)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad b0
while kill -0 453541 2>/dev/null; do sleep 5; done
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
# (a) rc0 of t0c-01 split by the position of r (R14.2)
for rs in v3 v4 gen; do run 1500 env RCS=0 RSPLIT=$rs python3 -I radcell3r.py 2147483629 A 0 t0c 01 rad/r_A0_t0c_01 600 t0/t0c_A_c0_01_None_N.ms.gb; done
# (e) symbolic [T31] B0, chart A
run 1800 python3 -I b0sym_run.py 2147483629 2 b0/A_R2 600
# (b) P2 / P1 pieces through the radical cells (fine stages)
for it in P2/z1:z1:z1/- P2/ab:z1:0/- P1a/z1:z1:z1/- P1b/z1:z1:z1/-; do
  tag=$(echo $it | tr '/:' '__'); run 1200 python3 -I radcell3.py 2147483629 A 0 pc $it rad/pc_A0_$tag 300
done
echo "$(date -u +%T) chain14c done" >> chain13.log
