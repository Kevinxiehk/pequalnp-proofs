#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
( timeout 1700 python3 -I rr_gen_rank.py BBdef1 15 40 11 > rank_BBdef1.log 2>&1; timeout 900 python3 -I rr_gen_rank.py BBdef1x 15 30 11 > rank_BBdef1x.log 2>&1 ) &
( timeout 1700 python3 -I rr_gen_rank.py BBdef2 15 40 11 > rank_BBdef2.log 2>&1; timeout 900 python3 -I rr_gen_rank.py BBdef2x 15 30 11 > rank_BBdef2x.log 2>&1 ) &
wait; echo done > bbminors_done.flag
