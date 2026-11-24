#!/bin/bash
# case A class-reduced sweep: nS nF CLSLIST ; for each CLS, hinge list (|F| = 0: h on each class rep / every S column for deg), x*-charts + ka = 1
cd /home/kevxhk/work/L-gct-210/stage3/r24
nS=$1; nF=$2; shift 2
for CLS in "$@"; do
  if [ $nF -gt 0 ]; then HL="-"; elif [ $CLS = deg ]; then HL=$(seq -s ' ' -f 'h%g' 0 $((nS-1))); else HL="h0 h1"; fi
  for HG in $HL; do
    out="nS=$nS nF=$nF CLS=$CLS hinge=$HG:"
    for XI in 00 01 02 03 04 10 11 12 13 14 ka1; do
      if [ $XI = ka1 ]; then f=$(python3 -I eqtA_cls.py $nS $nF 1 00 0 $HG $CLS); else f=$(python3 -I eqtA_cls.py $nS $nF 0 $XI 0 $HG $CLS); fi
      r=$(bash -c "ulimit -v 500000; timeout 60 Singular -q $f" 2>&1 | grep -o "unit [01]\|halt")
      case "$r" in "unit 1") v=U;; "unit 0") v=N;; halt) v=M;; *) v=T;; esac
      out="$out $XI:$v"
    done
    echo "$out"
  done
done
