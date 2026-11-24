#!/bin/bash
cd "$(dirname "$0")"; : > res.log
for I in 2 3 4; do for J in 2 3 4; do python3 -I ../b23_11.py C "$I;$J" 32003 j_C$I$J.sing
  r=$( (ulimit -v 500000; timeout 300 Singular -q j_C$I$J.sing 2>&1) ); echo "C$I$J $(echo "$r" | grep -E 'STD|halt' | head -1)" >> res.log; done; done; echo DONE >> res.log
