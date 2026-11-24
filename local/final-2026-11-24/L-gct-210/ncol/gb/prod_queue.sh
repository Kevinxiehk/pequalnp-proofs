#!/bin/bash
# (PROD) test (NOTES-ncol R3.3): no column-centred 3x5 level space of dim 4 outside product type  <=>  the Pluecker charts of orbit types
# 0123, 0125, 0128 of Gr(4,10) (equations P_2, P_3 only; S5 x Z2 symmetric system) are UNIT.  Calibration: dim-3 charts (must be NON-unit).
# Projective (all charts up to the symmetry), no saturation: UNIT at P1 = proof in char 0 (RED-p).
cd /home/kevxhk/work/L-gct-210/ncol/gb
export ULIM=${ULIM:-8000000}
./runlog_big.sh free3_orb_P1 600 free3_orb_P1.log
./runlog_big.sh prod_P1 7200 prod_P1.log
