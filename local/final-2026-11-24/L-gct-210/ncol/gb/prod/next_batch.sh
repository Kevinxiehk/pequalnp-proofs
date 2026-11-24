#!/bin/bash
# after the P1 batch: core A = calibration (only-d2 / only-d3a, chart 01_01_01 contains the exact point of R3.5 for only-d2), then prime 2;
# core B = prime 3.
cd /home/kevxhk/work/L-gct-210/ncol/gb/prod
( ../runlog.sh calrun 600 calrun.log; ../runlog.sh e2orb_2147483497 900 e2orb_2147483497.log ) &
( ../runlog.sh e2orb_2147483077 900 e2orb_2147483077.log ) &
wait
