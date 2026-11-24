#!/bin/bash
# run the K_0-fixed systems for the explicit members (ncol/r11/kfix), one core, 0.5 GB virtual, resumable
cd "$(dirname "$0")/kfix"
for f in f_*.sing; do o=${f%.sing}.out; [ -s $o ] && continue
  (ulimit -v 500000; timeout 300 Singular -q $f > $o 2>&1); r=$(grep -E 'VERDICT|halt|error' $o | head -1); echo "${f%.sing} ${r:-TIMEOUT} | $(grep KCAL $o | cut -c1-40)" >> ../kfix.log
done; echo DONE >> ../kfix.log
