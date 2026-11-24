#!/bin/bash
# verify2 r11: re-run reg2's lift+Gram certificates (copies with private /tmp names), two at a time, 2.5 GB each
cd /home/kevxhk/work/L-gct-210/verify2/r11
ulimit -v 2500000
( python3 -I rr_p2211_rank.py 1 > cert_p2211_c1.log 2>&1; python3 -I rr_p2211_rank.py 0 > cert_p2211_c0.log 2>&1 ) &
( python3 -I rr_pblock_rank_all.py > cert_pblock_all.log 2>&1; python3 -I rr_pdblock_rank.py > cert_pdblock.log 2>&1 ) &
wait; echo ALLDONE > cert_done.flag
