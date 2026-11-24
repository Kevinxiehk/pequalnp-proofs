#!/bin/bash
# R9-Q5: quaternion formulation of (PL) on five active columns, all six sign patterns.  usage: q5runs.sh P TIMEOUT (cwd rows/r8/orb)
P=$1; TO=${2:-14400}
for SG in +++++ ++++- +++-- ++--- +---- -----; do python3 -I quat5.py $SG q5_${SG}_$P.sing $P > /dev/null; done
for SG in +++++ ++++- +++-- ++--- +---- -----; do (ulimit -v 2000000; timeout $TO Singular -q q5_${SG}_$P.sing > q5_${SG}_$P.out 2>&1); done
grep -h RESULT q5_*_$P.out
