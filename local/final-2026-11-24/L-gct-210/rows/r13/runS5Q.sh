#!/bin/bash
# exact over Q(i) versions of the support-5 sub-cases settled mod P1 (rows round 15); 0.45 GB / 900 s each
cd /home/kevxhk/work/L-gct-210/rows/r13
while pgrep -f "[r]unS5G4b.sh" > /dev/null; do sleep 10; done
run(){ name=$1; cs=$2; shift; shift; python3 -I case5.py 0 $cs q5_$name.sing "$@" > /dev/null; r=$(ulimit -v 450000; /usr/bin/time -f "%es %MKB" timeout 900 Singular -q q5_$name.sing 2>&1 | grep -E "plane stage|CASE5|after|KB|halt|rror" | tr '\n' ' '); echo "Q $name | $r" >> kS5Q.out; }
run P4_A P4 STAGED
run P4_z5 P4 SUBZ=5
run PP_A PP STAGED
run PP_z5 PP SUBZ=5
run P3_A P3 STAGED
run P3_z4 P3 SUBZ=4 STAGED
run P3_z45 P3 SUBZ=4,5
run P2_z3 P2 SUBZ=3 STAGED
run P2_z34 P2 SUBZ=3,4 STAGED
run P2_z345 P2 SUBZ=3,4,5
run P2_A P2 STAGED
echo ALLDONE >> kS5Q.out
