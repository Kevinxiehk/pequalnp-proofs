#!/bin/bash
ulimit -v 1500000
cd /home/kevxhk/work/L-gct-210/stage3/r14
for sg in $(python3 -I -c "import itertools; print(' '.join(''.join(p) for p in itertools.product('+-',repeat=4)))"); do for fc in 0 1 2; do for nc in w c3; do
  python3 -I alpha1_s3.py $sg $fc $nc > /dev/null
  f=a1s3_$(echo $sg | tr '+-' 'pm')_${fc}_${nc}.sing
  echo "$(timeout 300 Singular -q $f 2>&1 | grep RESULT)"
done; done; done
echo DONE
