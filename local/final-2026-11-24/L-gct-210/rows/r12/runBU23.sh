#!/bin/bash
# primes 2 and 3 for family B and the special line U (after runU.sh)
cd /home/kevxhk/work/L-gct-210/rows/r12
while pgrep -f "[r]unU.sh" > /dev/null; do sleep 10; done
for T in P2 P3; do for f in ${T}_B0g0 ${T}_B0g1 ${T}_B2g0 ${T}_B2g1 ${T}_Bi0 ${T}_Bi2 ${T}_U0g0 ${T}_U0g1 ${T}_Ui0 ${T}_U1g0 ${T}_U1g1 ${T}_Ui1 ${T}_U2g0 ${T}_U2g1 ${T}_Ui2; do
 (ulimit -v 1500000; /usr/bin/time -f "%e s %M KB" timeout 900 Singular -q $f.sing > $f.out 2>&1); echo "$f: $(grep -v redefin $f.out | grep -E 'gauge|KGEN|halt|KB|rror' | tr '\n' ' ')" >> kBU23.out; done; done
echo ALLDONE >> kBU23.out
