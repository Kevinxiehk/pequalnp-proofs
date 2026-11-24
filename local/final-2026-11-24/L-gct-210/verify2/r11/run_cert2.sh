#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r11
ulimit -v 2500000
( python3 -I rr_p21111aa_rank.py 1 > cert_aa_c1.log 2>&1; python3 -I rr_p21111aa_rank.py 0 > cert_aa_c0.log 2>&1 ) &
( python3 -I rr_p21111iso_rank.py 1 > cert_iso_c1.log 2>&1; python3 -I rr_p21111iso_rank.py 0 > cert_iso_c0.log 2>&1 ) &
wait; echo done > cert2_done.flag
