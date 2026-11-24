#!/bin/bash
# whole rho = 2 case at the N level, v2 (round 18): skips items already N-UNIT in the case log; the D != 0 items use the light 'nl'
# presentation (never the adjugate 'ne'); every python driver runs under an outer rsscap (600 MB) besides the 550 MB cap on msolve.
# usage: ./case_nlevel2.sh CI   (appends to nlam/case_<CI>.log)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; CI=$1; LOG=nlam/case_$CI.log
done_item() { grep -q "VERDICT nlam A c$CI $1 $2: N-UNIT" $LOG 2>/dev/null; }
run() { python3 -I rsscap.py 600 900 python3 -I nlam.py A $CI "$@" 2>&1 | grep -E "VERDICT|RSSCAP" | sed "s#^RSSCAP#VERDICT nlam A c$CI $1 $2: DRIVER-CAP RSSCAP#" >> $LOG; }
for a in ab z1 z2 0; do for b in ab z1 z2 0; do for c in ab z1 z2 0; do
  [ "$a:$b:$c" = "ab:ab:ab" ] && continue
  done_item t0b $a:$b:$c || run t0b $a:$b:$c 120
done; done; done
for d in 01 02 12 nl; do done_item t0c $d || run t0c $d 300; done
for pc in P1a P1b P2; do
  for a in ab z1 z2 0; do for b in ab z1 z2 0; do for c in ab z1 z2 0; do
    [ "$a:$b:$c" = "ab:ab:ab" ] && continue
    done_item pc $pc/$a:$b:$c/- || run pc $pc/$a:$b:$c/- mu 120
  done; done; done
  for d in nl 01 02 12; do done_item pc $pc/ab:ab:ab/$d || run pc $pc/ab:ab:ab/$d mu 300; done
done
echo "DONE case $CI (v2) $(date -u +%T)" >> $LOG
