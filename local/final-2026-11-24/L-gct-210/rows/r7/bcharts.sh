#!/bin/bash
# R7-B-charts: full Rabinowitsch chart cover of R6-1 case B up to the S_4 symmetry of the active columns (126 multisets of
# coordinate indices 0..5, one per active column).  usage: bcharts.sh P NPAR TIMEOUT_SEC    (cwd: rows/r7; outputs bch_P/)
P=$1; NPAR=${2:-20}; TO=${3:-7200}
mkdir -p bch_$P; cd bch_$P
python3 -I - <<PY > charts.txt
import itertools
for c in itertools.combinations_with_replacement('012345',4): print(''.join(c))
PY
run1(){ CH=$1; P=$2; TO=$3
  python3 -I ../../gb/x4gen.py $P B B_$CH $CH > /dev/null
  ( ulimit -v 4000000; /usr/bin/time -f "%e s" timeout $TO msolve -g 2 -t 1 -f B_$CH.ms -o B_$CH.gb ) > B_$CH.log 2>&1
  if [ -s B_$CH.gb ]; then if grep -q "^\[1\]:" B_$CH.gb; then echo "$CH UNIT $(tail -1 B_$CH.log)"; else echo "$CH NONUNIT $(grep 'length of basis' B_$CH.gb) $(tail -1 B_$CH.log)"; fi
  else echo "$CH TIMEOUT/ERROR $(tail -1 B_$CH.log)"; fi; }
export -f run1
cat charts.txt | xargs -P $NPAR -I{} bash -c "run1 {} $P $TO" > summary.txt
echo done >> summary.txt
