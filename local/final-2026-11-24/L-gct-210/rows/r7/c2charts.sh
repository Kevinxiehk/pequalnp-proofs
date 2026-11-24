#!/bin/bash
# R7 generic-h chart cover for R6-1 cases B / C (and calibration B3).  usage: c2charts.sh CASE P NPAR TIMEOUT_SEC
# optional 5th argument SLICE = number of random affine slices (calibration B3: 5; B, C: 0).
# cwd rows/r7; outputs c2_CASE_P_sSLICE/summary.txt (one line per chart: UNIT / NONUNIT / TIMEOUT).  Memory cap 2.5 GB per job.
CASE=$1; P=$2; NPAR=${3:-8}; TO=${4:-7200}; SL=${5:-0}
case $CASE in B) N=4;; C) N=5;; B3) N=3;; esac
D=c2_${CASE}_${P}_s$SL; mkdir -p $D; cd $D
python3 -I -c "
import itertools
for c in itertools.combinations_with_replacement('012',$N): print(''.join(c))" > charts.txt
run1(){ CH=$1; CASE=$2; P=$3; TO=$4; SL=$5
  python3 -I ../x4c2.py $P $CASE $CH ${CASE}_$CH $SL > /dev/null
  ( ulimit -v 2500000; /usr/bin/time -f "%e s %M KB" timeout $TO msolve -g 2 -t 1 -f ${CASE}_$CH.ms -o ${CASE}_$CH.gb ) > ${CASE}_$CH.log 2>&1
  if [ -s ${CASE}_$CH.gb ]; then if grep -q "^\[1\]:" ${CASE}_$CH.gb; then echo "$CH UNIT $(tail -1 ${CASE}_$CH.log)"; else echo "$CH NONUNIT $(grep 'length of basis' ${CASE}_$CH.gb) $(tail -1 ${CASE}_$CH.log)"; fi
  else echo "$CH TIMEOUT/ERROR $(tail -1 ${CASE}_$CH.log)"; fi; }
export -f run1
cat charts.txt | xargs -P $NPAR -I{} bash -c "run1 {} $CASE $P $TO $SL" > summary.txt
echo done >> summary.txt
