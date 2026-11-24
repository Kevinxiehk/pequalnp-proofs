#!/bin/bash
ulimit -v 2500000
for pat in M Q0 P0; do for cho in A B; do for case in i ii; do
 f=Dir_D04_${pat}_${cho}_${case}_c0_v123.sing
 python3 -I ../r9_direct.py D04_${pat}_${cho}_${case} 0 123 > $f
 echo "== $f $(date -u +%H:%M:%S)"; timeout 900 Singular -q $f 2>&1 | head -3
done; done; done
echo "ALL DONE $(date -u +%H:%M:%S)"
