#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r21
until grep -q "^DONE r2c5" kR2C.out; do sleep 5; done
./runR2C.sh pl4fR_p pl5R_G4_5f_p bq5R_P2_z3_p bq5aR_P2_z3_p smcR5_p pl5R_R4_p pl5R_R5_p bq5R_P2_A_p bq5aR_P2_A_p
