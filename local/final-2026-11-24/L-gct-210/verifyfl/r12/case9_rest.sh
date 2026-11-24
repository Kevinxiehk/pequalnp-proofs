#!/bin/bash
# case 9: K-level for the IV1 items whose N-system is non-unit (rho1cell, old S-cells), then the Q1a/Q1b pieces at the N level
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; LOG=nlam1/case_9_rest.log
for x in "ab:ab:ab AA" "ab:ab:ab AB" "ab:ab:ab BA" "ab:ab:0 AA" "ab:0:ab AA"; do
  set -- $x; u=$(echo $1 | tr -d ':')
  python3 -I rsscap.py 600 1500 python3 -I rho1cell.py A 9 IV1 $1 - $2 r1c/A9_IV1_${u}_$2 300 nlam1/A_c9_IV1_${u}_x_$2.ms.gb 2>&1 | grep -E "VERDICT|RSSCAP|scell" >> $LOG
done
python3 -I rsscap.py 650 7000 python3 -I nlam1.py A 9 120 Q1a,Q1b 2>&1 | grep -E "VERDICT|SUMMARY|RSSCAP" >> $LOG
echo "DONE case9_rest $(date -u +%T)" >> $LOG
