#!/bin/bash
# round-13 pool chain, one job at a time (<= 2.5 GB, single thread).  Waits for sym_cut3 A0 (PID 389758).
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p fine pc
while kill -0 389758 2>/dev/null; do sleep 5; done
run() { echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout 2400 python3 -I "$@") >> chain13.out 2>&1; }
# (1) piece IV, A case 0, D = 0 pieces: S-cell 0 with the radical equations (R13.1); S-cells 1, 2 were UNIT already for 01, 02
for d in 01 02; do for r in r1 r2; do run anycell.py 2147483629 gen_t22t0c "A,0,$d" 0 $r fine/t0c_A0_${d}_s0$r 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done; done
# (2) piece IV, pieces 12 and ne: all S-cells (S-cell 0 radical)
for d in 12 ne; do
  for r in r1 r2; do run anycell.py 2147483629 gen_t22t0c "A,0,$d" 0 $r fine/t0c_A0_${d}_s0$r 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done
  for s in 1 2; do run anycell.py 2147483629 gen_t22t0c "A,0,$d" $s - fine/t0c_A0_${d}_s$s 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done
done
# (3) pieces P2 / P1a / P1b, A case 0: a first sample of u-triples
run pc_cell.py 2147483629 A 0 pc 600 P2/z1:z1:z1/-,P2/ab:z1:0/-,P1a/z1:z1:z1/-,P1b/z1:z1:z1/-,P2/ab:ab:ab/ne
echo "$(date -u +%T) chain13 done" >> chain13.log
