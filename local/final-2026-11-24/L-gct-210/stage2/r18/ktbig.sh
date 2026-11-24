#!/bin/bash
# BIG SLOT: proof-grade Singular std over QQ for the Kt systems that exceed 120 s (R2 lines (1,0,0), (1,0,1), (0,1,1), (0,0,1)).
# Restartable: systems already [1] (recorded in r18/ktbig_done.txt as "CACHE j0:i:a-b-c") are skipped.
cd /home/kevxhk/work/L-gct-210/stage2
touch r18/ktbig_done.txt
run(){ C=$1; L=""
  for x in $(echo "$2" | tr ';' ' '); do grep -qx "$C $x" r18/ktbig_done.txt || L="$L;$x"; done; L=${L#;}
  [ -z "$L" ] && { echo "== $C: all systems already [1]"; return; }
  echo "== $C ($(echo "$L" | tr ';' '\n' | wc -l) systems) $(date -u +%H:%M:%S)"
  SYSLIST="$L" LOGUNIT=1 ENGINE=sing STO=3600 MSV=6000000 timeout 36000 python3 -I r18_Kt2.py r16/cache_$C.pkl 0 2>&1 | while read l; do
    case "$l" in UNIT*) echo "$C ${l#UNIT }" >> r18/ktbig_done.txt;; *TIMEOUT*|*NONUNIT*|*FAILED*|RESULT*) echo "$l";; esac; done; }
run f9b8fe0eac09 "0:1:0-1-5;0:1:0-1-6;1:1:0-1-5;1:1:0-1-6"
run 9a05094bcabd "0:1:0-1-5;0:1:0-1-6;0:1:0-3-5;0:1:0-3-6;1:1:0-1-5;1:1:0-1-6;1:1:0-3-5;1:1:0-3-6"
run 698f1aa37be6 "0:1:0-2-5;0:1:0-2-6;0:1:0-3-5;0:1:0-3-6;0:1:0-4-5;0:1:0-4-6;1:1:0-2-5;1:1:0-2-6;1:1:0-3-5;1:1:0-3-6;1:1:0-4-5;1:1:0-4-6;1:6:0-1-3;1:6:0-1-4"
run f309f7a3a7bc "0:1:0-1-3;0:1:0-1-5;0:1:0-1-6;0:1:0-3-5;0:1:0-3-6;0:1:0-4-6;0:1:0-5-6;0:1:1-4-6;0:1:1-5-6;1:1:0-1-3;1:1:0-1-5;1:1:0-1-6;1:1:0-3-5;1:1:0-3-6;1:1:0-4-6;1:1:0-5-6;1:1:1-5-6"
echo "ALL DONE $(date -u +%H:%M:%S)"
