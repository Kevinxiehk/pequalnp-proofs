#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
for j in 1 2; do for c in 1 0; do echo "== JROW $j chart $c"; timeout 1700 python3 -I rr_p2211def_rank.py $c $j 2>&1 | grep -E 'pivot|Error|error' | cut -c1-330; done; done > bbdef.log
echo done >> bbdef.log
