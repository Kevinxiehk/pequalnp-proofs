#!/bin/bash
# one root choice (sq3, i) per prime (Galois conjugates follow from the number-field statement); 8 runs per prime: eps x e-sign x chart
cd /home/kevxhk/work/L-gct-210/rows/r12
START=$(date +%s)
for PR in "2147482621 152957997 110870171" "2147475601 27292408 303123450" "1001197 5748 77124"; do
 set -- $PR; P=$1; s3=$2; ri=$3
 for eps in 1 -1; do for es in + -; do
  if [ $eps = 1 ] && [ $es = + ]; then gc=1; else gc=0; fi
  for k in 0 2; do
   if grep -q "P=$P eps=$eps es=$es k=$k " kS2.out 2>/dev/null; then continue; fi
   if [ $P = 2147482621 ] && grep -q "eps=$eps sq3=$s3 i=$ri es=$es .*chart m$k " kS.out 2>/dev/null; then echo "P=$P eps=$eps es=$es k=$k | (from kS.out) $(grep "eps=$eps sq3=$s3 i=$ri es=$es .*chart m$k " kS.out | cut -d'|' -f2)" >> kS2.out; continue; fi
   python3 -I kgen.py S$es $P $k cc tS2.sing $eps $gc num=$s3,$ri > /dev/null
   r=$(ulimit -v 500000; timeout 400 Singular -q tS2.sing 2>&1 | grep -v redefin | grep -E 'gauge|KGEN|after|strongly|rror' | tr '\n' ' ')
   echo "P=$P eps=$eps es=$es k=$k t=$(( $(date +%s)-START ))s | $r" >> kS2.out
  done
 done; done
done
echo ALLDONE >> kS2.out
