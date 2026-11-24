#!/bin/bash
# R7-X4K and R7-T3 driver: usage kruns.sh P TIMEOUT_SEC  (cwd rows/r7/t3). Runs NC = 3 (calibration), 4, 5 and the 3-column type check in parallel.
P=$1; TO=${2:-14400}
for NC in 3 4 5; do python3 -I x4k.py $P $NC k${NC}_$P.sing > /dev/null; (ulimit -v 4000000; timeout $TO Singular -q k${NC}_$P.sing > k${NC}_$P.out 2>&1) & done
python3 -I t3gen.py $P t3_$P.sing > /dev/null; (ulimit -v 4000000; timeout $TO Singular -q t3_$P.sing > t3_$P.out 2>&1) &
wait; grep -h RESULT k*_$P.out t3_$P.out
