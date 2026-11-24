#!/bin/bash
# round-13 pool chain c, one job at a time (<= 2.5 GB, single thread)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p fine pc sc4
run() { echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout 2400 python3 -I "$@") >> chain13.out 2>&1; }
# (1) radical S-cell 0 (R13.1) for the piece-IV leftovers of A case 0 (S-cells 1, 2 of 01, 02 are UNIT already)
for d in 01 02; do for r in r1 r2; do run anycell.py 2147483629 gen_t22t0c "A,0,$d" 0 $r fine/t0c_A0_${d}_s0$r 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done; done
# (2) first sample of the pieces P2 / P1a / P1b
run pc_cell.py 2147483629 A 0 pc 600 P2/z1:z1:z1/-,P2/ab:z1:0/-,P1a/z1:z1:z1/-,P1b/z1:z1:z1/-
# (3) piece-IV leftovers 12, ne
for d in 12 ne; do
  for r in r1 r2; do run anycell.py 2147483629 gen_t22t0c "A,0,$d" 0 $r fine/t0c_A0_${d}_s0$r 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done
  for s in 1 2; do run anycell.py 2147483629 gen_t22t0c "A,0,$d" $s - fine/t0c_A0_${d}_s$s 600 t0/t0c_A_c0_${d}_None_N.ms.gb; done
done
echo "$(date -u +%T) chain13c done" >> chain13.log
