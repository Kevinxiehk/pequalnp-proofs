#!/bin/bash
# rerun RED-p items that did not finish (halt) after both workers are done
cd /home/kevxhk/work/L-gct-210/rows/r12
until [ $(grep -c "ALLDONE worker" kSP1.out) -ge 2 ]; do sleep 10; done
grep -v "dim -1 unit 1" kSP1.out | grep "^sq3=" | while read line; do
  s3=$(echo "$line" | sed 's/.*sq3=\([-0-9]*\).*/\1/'); ri=$(echo "$line" | sed 's/.* i=\([-0-9]*\).*/\1/'); eps=$(echo "$line" | sed 's/.*eps=\([-0-9]*\).*/\1/')
  cj=$(echo "$line" | sed 's/.*cj=\([01]\).*/\1/'); es=$(echo "$line" | sed 's/.*es=\([+-]\).*/\1/'); k=$(echo "$line" | sed 's/.* k=\([02]\).*/\1/'); gc=$(echo "$line" | sed 's/.*gc=\([0-3]\).*/\1/')
  python3 -I kgen.py S$es 2147483629 $k cc tSP1_fix.sing $eps $gc num=$s3,$ri cj=$cj > /dev/null
  r=$(ulimit -v 1000000; /usr/bin/time -f "%es %MKB" timeout 1500 Singular -q tSP1_fix.sing 2>&1 | grep -v redefin | grep -E 'gauge|KGEN|strongly|rror|halt|KB' | tr '\n' ' ')
  echo "RERUN sq3=$s3 i=$ri eps=$eps cj=$cj es=$es k=$k gc=$gc | $r" >> kSP1.out
done
echo "ALLDONE fix" >> kSP1.out
