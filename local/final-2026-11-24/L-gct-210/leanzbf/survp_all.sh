#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/leanzbf
for c in "00012 00012 -1" "00012 01102 1" "00012 10102 1" "00012 11002 1" "00112 00112 -1" "00112 01002 1" "00112 10002 1" "00112 11002 1" "00122 00122 -1" "01112 01112 -1" "01122 01122 -1" "01222 01222 -1"; do
  set -- $c
  t="$1_$2_$([ "$3" = "1" ] && echo p || echo m)"
  echo "== $c"; timeout 1200 python3 -I gen_survp.py $1 $2 $3 survp_out/$t.txt 2>&1 | tail -3
done
echo DONE
