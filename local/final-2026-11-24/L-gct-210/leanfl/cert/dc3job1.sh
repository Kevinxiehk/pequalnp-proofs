#!/bin/bash
cd /home/kevxhk/work/L-gct-210/leanfl/cert
export TL=60
awk 'NR%2==1' dc3_pick.txt | while read f tm; do
  echo "== $f msolve $tm"
  ./liftms.sh dc3/$f dc3/${f%.ms} 2>&1 | grep -E "^lift|^time|error|halt" | sed 's|^lift [^:]*:|lift:|'
done
echo DC3JOB1 DONE
