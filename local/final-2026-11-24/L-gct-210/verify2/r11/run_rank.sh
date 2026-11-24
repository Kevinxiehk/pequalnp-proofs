#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r11
ulimit -v 2500000
python3 -I rr_gen_rank.py blockall 15 40 7 > rank_blockall.log 2>&1 &
python3 -I rr_gen_rank.py dblock 15 40 7 > rank_dblock.log 2>&1 &
wait; echo done > rank_done.flag
