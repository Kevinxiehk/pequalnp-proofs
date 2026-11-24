#!/bin/bash
# recursive kernel bound + exact exceptional points on every remaining line (R1 lines, R2 line (0,0,0)).
cd /home/kevxhk/work/L-gct-210/stage2
for C in 9881b981b0a9 05809a23902d ad0a91b6ba10 97f34f926218 29c73249bd89 75f3d47cd9d9 baca663e2863 e33cc406d551 0d3623f0f596; do
  echo "######## $C $(date -u +%H:%M:%S)"; timeout 1800 python3 -I r21_chain.py r16/cache_$C.pkl 2>&1 | cut -c1-300
done
echo "ALL DONE $(date -u +%H:%M:%S)"
