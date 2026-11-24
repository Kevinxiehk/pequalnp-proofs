#!/bin/bash
ulimit -v 2500000
for fam in P0_B_i P0_B_ii P0_A_i; do
 f=Dir_D04_${fam}_c0_v123.sing
 python3 -I ../r9_direct.py D04_${fam} 0 123 > $f
 echo "== $f $(date -u +%H:%M:%S)"; ./elim.sh $f 60 2>&1 | sed -n '/ELIM/,$p' | head -40
done
echo "ALL DONE $(date -u +%H:%M:%S)"
