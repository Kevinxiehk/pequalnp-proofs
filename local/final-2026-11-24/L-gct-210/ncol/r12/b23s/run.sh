#!/bin/bash
cd "$(dirname "$0")"; : > res.log
for I in 2 3 4; do for J in 2 3 4; do for c1 in Z H; do for c2 in Z H; do for c3 in Z H; do for c4 in Z H; do
  code=$c1$c2$c3$c4; n=C${I}${J}_$code; python3 -I ../b23_11.py C "$I;$J" 0 j_$n.sing $code
  r=$( (ulimit -v 500000; timeout 300 Singular -q j_$n.sing 2>&1) ); echo "$r" > j_$n.out; echo "$n $(echo "$r" | grep STD | cut -d' ' -f4-) $(echo "$r" | grep -c '^COMP')" >> res.log
done; done; done; done; done; done; echo DONE >> res.log
