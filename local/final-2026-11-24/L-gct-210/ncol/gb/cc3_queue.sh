#!/bin/bash
# CC3 exact runs (NOTES-ncol R2.7): 24 orbit charts x 3 primes, then the D = 2 calibration (must be NON-unit).  1 core, ULIM per msolve run.
cd /home/kevxhk/work/L-gct-210/ncol/gb
export ULIM=${ULIM:-8000000}
./runlog_big.sh cc3d2_orb_P1 600 cc3d2_orb_P1.log
for d in cc3d4_orb_P1 cc3d4_orb_2147483497 cc3d4_orb_2147483077; do ./runlog_big.sh $d 3600 $d.big.log; done
