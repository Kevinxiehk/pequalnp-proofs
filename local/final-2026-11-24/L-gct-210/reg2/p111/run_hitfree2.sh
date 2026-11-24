#!/bin/bash
# round 11: exact incidence-split emptiness test (incpat.py) for the CE-1 hit-free line patterns; sequential, 1 core, < 1 GB
cd /home/kevxhk/work/L-gct-210/reg2/p111; ulimit -v 1000000; L=/home/kevxhk/work/L-gct-210/reg2/evidence/logs/r11_incpat_hitfree2.log
: > $L
while IFS="|" read -r r c; do echo "== pattern rows[$r] cols[$c]  $(date -u +%H:%M)" >> $L; CASETMO=90 timeout 1500 python3 -I incpat.py "$r" "$c" >> $L 2>&1; done < hitfree_args2.txt
echo DONE >> $L
