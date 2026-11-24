#!/bin/bash
# special isolated two-column kernels: 8 points x 2 kernels (ES), charts m0 (covers m1 via a<->b, ES -> -ES) and m2 (covers m3, m4), cc and cs.
cd /home/kevxhk/work/L-gct-210/rows/r12
rm -f kS.out; START=$(date +%s)
for PR in "2147482621 152957997 110870171" "2147475601 27292408 303123450" "1001197 5748 77124"; do
 set -- $PR; P=$1; R3=$2; RI=$3
 for s3 in $R3 -$R3; do for ri in $RI -$RI; do for eps in 1 -1; do for es in + -; do
  if [ $eps = 1 ] && [ $es = + ]; then gc=1; else gc=0; fi
  for md in cc; do for k in 0 2; do
   python3 -I kgen.py S$es $P $k $md tS.sing $eps $gc num=$s3,$ri > /dev/null
   r=$(ulimit -v 500000; timeout 300 Singular -q tS.sing 2>&1 | grep -v redefin | grep -E 'gauge|KGEN|after|strongly|rror' | tr '\n' ' ')
   echo "eps=$eps sq3=$s3 i=$ri es=$es t=$(( $(date +%s)-START ))s | $r" >> kS.out
  done; done
 done; done; done; done
done
echo ALLDONE >> kS.out
