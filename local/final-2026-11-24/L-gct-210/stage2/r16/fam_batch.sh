#!/bin/bash
# setup + kernel analysis for a list of R2 subfamilies (FIXPAR strings as arguments). Ruling from $RUL (default R2), Z basis from $ZBASIS.
cd /home/kevxhk/work/L-gct-210/stage2
RUL=${RUL:-R2}
for F in "$@"; do
  echo "######## $RUL $F ZBASIS=$ZBASIS $(date -u +%H:%M:%S)"
  out=$(timeout 2400 python3 -I r16_F2col_setup.py $RUL 2147483629 "$F" 2>&1)
  echo "$out" | grep -E "rank-jump|dim T_1|complement valid|denominators|explicit Z" | cut -c1-300
  C=$(echo "$out" | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1)
  [ -z "$C" ] && { echo "SETUP FAILED"; continue; }
  echo "cache $C"
  timeout 2400 python3 -I r16_Kauto.py $C 2>&1 | grep -v "^fix" | cut -c1-400
done
echo "BATCH DONE $(date -u +%H:%M:%S)"
