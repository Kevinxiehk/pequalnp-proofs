#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r13
while pgrep -f "[r]unS5G4.sh" > /dev/null; do sleep 10; done
P=2147483629
python3 -I case5.py $P G4 s5_G4_z5f.sing SUBZ=5 FAM > /dev/null; r=$(ulimit -v 450000; /usr/bin/time -f "%es %MKB" timeout 1200 Singular -q s5_G4_z5f.sing 2>&1 | grep -E "plane stage|CASE5|after|KB|halt|rror" | tr '\n' ' '); echo "G4_z5_FAM | $r" >> kS5sub.out
echo ALLDONE-G4b >> kS5sub.out
