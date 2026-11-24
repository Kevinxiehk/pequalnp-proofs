#!/bin/bash
ulimit -v 1000000
cd /home/kevxhk/work/L-gct-210/stage3/r14
for f in a1s3_[pm][pm][pm][pm]_[012]_*.sing; do
  python3 -I to_modp.py $f modp/$f > /dev/null || { echo "$f CONVERSION FAILED"; continue; }
  echo "$f : $(timeout 120 Singular -q modp/$f 2>&1 | grep RESULT)"
done
echo DONE
