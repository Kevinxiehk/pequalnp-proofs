#!/bin/bash
# D00-3 non-PROP families (NOTES-stage2 R9-6 / COMPUTE-stage2 S7'): eliminate the 60 t's, print the parameter locus where Omega = C^5 can hold.
# usage: run_d003.sh [LIST of family tags]   (default: all 18)   one Singular process per family; run several copies on disjoint lists.
cd /home/kevxhk/work/L-gct-210/stage2/r9
L=${@:-"M_A_1 M_A_2 M_A_3 M_B_1 M_B_2 M_B_3 Q0_A_1 Q0_A_2 Q0_A_3 Q0_B_1 Q0_B_2 Q0_B_3 P0_A_1 P0_A_2 P0_A_3 P0_B_1 P0_B_2 P0_B_3"}
for t in $L; do f=Dir_D003_${t}_c0_v123.sing; echo "== $t $(date -u +%H:%M:%S)"; ./elim.sh $f 60 2>&1 | sed -n '/LEVEL\|ELIM/,$p' | head -60; done
echo "DONE $(date -u +%H:%M:%S)"
