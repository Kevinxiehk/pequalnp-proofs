#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
until grep -q "ALL DONE" r20/r1red.log; do sleep 30; done
for C in 97f34f926218 75f3d47cd9d9 baca663e2863 17dc07201935 9881b981b0a9 05809a23902d e33cc406d551 ad0a91b6ba10 29c73249bd89; do timeout 900 python3 -I r20_lineexc_mc.py r16/cache_$C.pkl 2>&1 | cut -c1-300; done
echo "ALL DONE $(date -u +%H:%M:%S)"
