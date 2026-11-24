#!/bin/bash
# R8-K4sign / R8-K5sign driver.  usage: ksruns.sh P TIMEOUT   (cwd rows/r8).  4 columns: the three remaining sign patterns, with the
# derived trace equations (Lemma TR) and deg <= 3 (relaxation); 5 columns: all six sign patterns, deg <= 3.  Singular, ~0.6-1 GB each.
P=$1; TO=${2:-14400}
for SG in ++++ ++-- ----; do python3 -I x4ks.py $P 4 $SG 3 kt4_${SG}_$P.sing tr > /dev/null; done
for SG in +++++ ++++- +++-- ++--- +---- -----; do python3 -I x4ks.py $P 5 $SG 3 ks5_${SG}_$P.sing > /dev/null; done
ls kt4_*_$P.sing ks5_*_$P.sing | xargs -P 9 -I{} bash -c "ulimit -v 2500000; timeout $TO Singular -q {} > {}.out 2>&1"
grep -h RESULT kt4_*_$P.sing.out ks5_*_$P.sing.out
