#!/bin/bash
# R7-C1: dimension of the S_5 charts (single strongly level matrices, all 5 columns nonzero). usage: runC1.sh P TIMEOUT (cwd rows/r7/s5)
P=$1; TO=${2:-7200}
for CH in 00000 00001 00011 00012 00112; do
  python3 -I ../../gb/x4gen.py $P A A_${CH}_$P $CH > /dev/null; python3 -I ms2sing.py A_${CH}_$P.ms A_${CH}_$P.sing "S5 chart $CH p=$P"
  (ulimit -v 2500000; timeout $TO Singular -q A_${CH}_$P.sing > A_${CH}_$P.out 2>&1) &
done; wait; cat A_*_$P.out
