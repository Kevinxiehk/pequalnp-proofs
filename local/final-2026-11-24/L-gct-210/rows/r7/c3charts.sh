#!/bin/bash
# R7/R8 generic-h charts WITH THE FIBRE FIXED: sigma(h)_1 = c for c = 0..N (N+1 = nact+1 distinct values: complete cover, since on each
# fibre line every chosen column coordinate of h vanishes at most once).  usage: c3charts.sh CASE P NPAR TIMEOUT [ENGINE]
# ENGINE = msolve (default) or singular.  cwd rows/r7; outputs c3_CASE_P/summary.txt.  A plane is excluded iff ALL (chart, c) are UNIT.
CASE=$1; P=$2; NPAR=${3:-8}; TO=${4:-7200}; ENG=${5:-msolve}; SL=${6:-0}   # SL > 0 only for the B3 calibration
case $CASE in B) N=4;; C) N=5;; B3) N=3;; esac
D=c3_${CASE}_${P}_s$SL; mkdir -p $D; cd $D
python3 -I -c "
import itertools
for c in itertools.combinations_with_replacement('012',$N):
    for v in range($N+1): print(''.join(c),v)" > jobs.txt
run1(){ CH=$1; V=$2; CASE=$3; P=$4; TO=$5; ENG=$6; SL=$7; F=${CASE}_${CH}_f$V
  python3 -I ../x4c2.py $P $CASE $CH $F $SL $V > /dev/null
  if [ $ENG = msolve ]; then
    ( ulimit -v 2500000; /usr/bin/time -f "%e s %M KB" timeout $TO msolve -g 2 -t 1 -f $F.ms -o $F.gb ) > $F.log 2>&1
    if [ -s $F.gb ]; then if grep -q "^\[1\]:" $F.gb; then echo "$CH $V UNIT $(tail -1 $F.log)"; else echo "$CH $V NONUNIT $(grep 'length of basis' $F.gb) $(tail -1 $F.log)"; fi
    else echo "$CH $V TIMEOUT/ERROR $(tail -1 $F.log)"; fi
  else
    ( ulimit -v 2500000; /usr/bin/time -f "%e s %M KB" timeout $TO Singular -q $F.sing ) > $F.out 2>&1
    echo "$CH $V $(grep X4C2 $F.out | sed 's/.*: //') $(tail -1 $F.out)"
  fi; }
export -f run1
cat jobs.txt | xargs -P $NPAR -L 1 bash -c 'run1 $0 $1 '"$CASE $P $TO $ENG $SL" > summary.txt
echo done >> summary.txt
