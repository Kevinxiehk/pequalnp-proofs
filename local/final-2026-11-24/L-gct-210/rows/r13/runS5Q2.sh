#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r13
run(){ name=$1; cs=$2; shift; shift; python3 -I case5.py 0 $cs q5_$name.sing "$@" > /dev/null; r=$(ulimit -v 450000; /usr/bin/time -f "%es %MKB" timeout 900 Singular -q q5_$name.sing 2>&1 | grep -E "plane stage|CASE5|after|KB|halt|rror" | tr '\n' ' '); echo "Q $name | $r" >> kS5Q.out; }
run P2_z3 P2 SUBZ=3 STAGED
run P2_z34 P2 SUBZ=3,4 STAGED
run P2_z345 P2 SUBZ=3,4,5
run P2_A P2 STAGED
echo ALLDONE >> kS5Q.out
