#!/bin/bash
ulimit -v 2500000
for p in 65521 2147483629 2147483497; do
 for c in C3b C3c C12ab C12ac; do
  for m in FULL LEVEL; do timeout 900 python3 -I gen9.py $p $c $m 1; done
 done
done
