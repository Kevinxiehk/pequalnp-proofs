#!/bin/bash
# NCOL-HCONJ-B (ncol round 8, spec ncol/r8/HBIG-SPEC.txt): H-conjecture types b22/b23, 4 families sequentially
cd /home/kevxhk/work/L-gct-210/ncol/r8 || exit 1
for a in 'b22 2' 'b22 0' 'b23 2' 'b23 0'; do echo "== hconjB $a start $(date -u +%T)"; ULIM=8000000 CT=600 timeout 7200 ./hiter3.sh $a 6; echo "== hconjB $a end rc=$? $(date -u +%T)"; done
