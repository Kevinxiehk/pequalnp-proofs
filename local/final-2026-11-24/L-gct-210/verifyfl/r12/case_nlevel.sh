#!/bin/bash
# N-level decision of a whole rho = 2 case (chart A): piece IV (t0b triples + t0c det split) with the lambda-words, pieces P1a, P1b, P2 with mu.
# usage: ./case_nlevel.sh CI   (log: nlam/case_<CI>.log)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; CI=$1
for a in ab z1 z2 0; do for b in ab z1 z2 0; do for c in ab z1 z2 0; do
  [ "$a:$b:$c" = "ab:ab:ab" ] && continue
  timeout 900 python3 -I nlam.py A $CI t0b $a:$b:$c 120 2>&1 | grep VERDICT
done; done; done
for d in 01 02 12 ne; do timeout 1500 python3 -I nlam.py A $CI t0c $d 300 2>&1 | grep VERDICT; done
for pc in P1a P1b P2; do
  for a in ab z1 z2 0; do for b in ab z1 z2 0; do for c in ab z1 z2 0; do
    [ "$a:$b:$c" = "ab:ab:ab" ] && continue
    timeout 600 python3 -I nlam.py A $CI pc $pc/$a:$b:$c/- mu 120 2>&1 | grep VERDICT
  done; done; done
  for d in ne 01 02 12; do timeout 900 python3 -I nlam.py A $CI pc $pc/ab:ab:ab/$d mu 300 2>&1 | grep VERDICT; done
done
echo "DONE case $CI $(date -u +%T)"
