#!/bin/bash
ulimit -v 2000000
cd /home/kevxhk/work/L-gct-210/stage3/r14
for f in ../r13/shapeS_p3_0 ../r13/shapeS_p3_1 ../r13/shapeS_p3_2 ../r13/shapeS_0 ../r13/shapeS_1 ../r13/shapeS_2 ../r13/alpha0_W4n_0145 ../r13/alpha0_W4n_0235 ../r13/alpha0_W4n_1234 ../r13/alpha0_W4_cal2 $(ls ../r13/a0small_s3_v*_n*.sing | sed 's/.sing$//') $(ls ../r13/a0P2_*.sing | sed 's/.sing$//'); do
  b=$(basename $f); python3 -I to_modp.py $f.sing modp/$b.sing > /dev/null || { echo "$b CONVERSION FAILED"; continue; }
  r=$(timeout 300 Singular -q modp/$b.sing 2>&1 | grep -E 'RESULT|SHAPE_S|CALIBRATION' | grep -v '^G' | head -1)
  echo "$b : $r"
done
echo DONE
