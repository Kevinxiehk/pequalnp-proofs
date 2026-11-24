#!/bin/bash
# round-14 pool chain b (one job at a time, <= 2.5 GB): waits for the running radcell3 t0c-01 (PID 442955)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad symdc
while kill -0 442955 2>/dev/null; do sleep 5; done
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
# (f) pilot: SYM-M [DC3] for |supp m| = 5 (covers EVERY m), chart 0, all 220 cases, 60 s each
run 3000 python3 -I symdc_run.py 2147483629 5 0 3 symdc run timeout=60
# (b) P2 / P1 pieces through the radical cells (fine stages), cheap charts first
for it in P2/z1:z1:z1/- P2/ab:z1:0/- P1a/z1:z1:z1/- P1b/z1:z1:z1/-; do
  tag=$(echo $it | tr '/:' '__'); run 1200 python3 -I radcell3.py 2147483629 A 0 pc $it rad/pc_A0_$tag 300
done
echo "$(date -u +%T) chain14b done" >> chain13.log
