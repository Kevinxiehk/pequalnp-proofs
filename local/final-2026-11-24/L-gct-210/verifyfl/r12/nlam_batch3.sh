#!/bin/bash
# big-slot batch 3 (round 18): case 9 (rho = 1) items beyond the pool cap: Q2 items with >= 2 'ab' charts and the D-split (N level, cap 2.4 GB),
# the Q1a/Q1b D-split items (N level), and the IV1 words whose N-system is non-unit (K level, rho1cell, old S-cells).
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; export NLAM_CAP=${NLAM_CAP:-2400}
Q2="Q2/ab:ab:z1/-,Q2/ab:ab:z2/-,Q2/ab:ab:0/-,Q2/ab:z1:ab/-,Q2/ab:z2:ab/-,Q2/ab:0:ab/-,Q2/z1:ab:ab/-,Q2/z2:ab:ab/-,Q2/0:ab:ab/-,Q2/ab:ab:ab/nl,Q2/ab:ab:ab/01,Q2/ab:ab:ab/02,Q2/ab:ab:ab/12"
timeout 9000 python3 -I nlam1.py A 9 1500 Q2 $Q2
Q1="Q1a/ab:ab:ab/01,Q1a/ab:ab:ab/02,Q1a/ab:ab:ab/12,Q1b/ab:ab:ab/01,Q1b/ab:ab:ab/02,Q1b/ab:ab:ab/12"
timeout 6000 python3 -I nlam1.py A 9 1500 Q1a,Q1b $Q1
for x in "ab:ab:ab AA" "ab:ab:0 AA" "ab:0:ab AA"; do set -- $x; u=$(echo $1 | tr -d ':')
  timeout 3000 python3 -I rho1cell.py A 9 IV1 $1 - $2 r1c/big_A9_IV1_${u}_$2 1500 nlam1/A_c9_IV1_${u}_x_$2.ms.gb; done
echo "DONE nlam_batch3 $(date -u +%T)"
