#!/bin/bash
# RED-p cover of the 16 geometric special points (x 2 e-signs) at P1 = 2147483629: charts m0 and m2 (full); gauge chosen by gsel.py
# (determinant nonzero mod P1; kgen prints it again).  Two workers: argument W = 0/1 takes alternate items.
cd /home/kevxhk/work/L-gct-210/rows/r12
P=2147483629; R3=59644493; RI=629208553; W=$1; n=0
for s3 in $R3 -$R3; do for ri in $RI -$RI; do for eps in 1 -1; do for cj in 0 1; do for es in + -; do for k in 0 2; do
  n=$((n+1)); [ $((n % 2)) = $W ] || continue
  gc=$(python3 -I gsel.py $P $s3 $ri $eps $cj $es)
  python3 -I kgen.py S$es $P $k cc tSP1_$W.sing $eps $gc num=$s3,$ri cj=$cj > /dev/null
  r=$(ulimit -v 900000; timeout 900 Singular -q tSP1_$W.sing 2>&1 | grep -v redefin | grep -E 'gauge|KGEN|strongly|rror|halt' | tr '\n' ' ')
  echo "sq3=$s3 i=$ri eps=$eps cj=$cj es=$es k=$k gc=$gc | $r" >> kSP1.out
done; done; done; done; done; done
echo "ALLDONE worker $W" >> kSP1.out
