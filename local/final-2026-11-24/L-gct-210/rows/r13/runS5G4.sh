#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r13
while pgrep -f "[r]unS5sub.sh" > /dev/null; do sleep 10; done
P=2147483629
python3 -I case5.py $P G4 s5_G4_Af.sing STAGED FAM > /dev/null; r=$(ulimit -v 450000; /usr/bin/time -f "%es %MKB" timeout 1200 Singular -q s5_G4_Af.sing 2>&1 | grep -E "plane stage|CASE5|after|KB|halt|rror" | tr '\n' ' '); echo "G4_A_FAM | $r" >> kS5sub.out
echo ALLDONE-G4 >> kS5sub.out
