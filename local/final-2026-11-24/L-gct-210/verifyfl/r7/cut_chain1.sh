#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r7
python3 -I cut_cell.py 2147483629 m12m3 0 ab ab cut/A_m12m3_p29_piv0
python3 -I cut_cell.py 2147483497 m12m3 0 ab ab cut/A_m12m3_p97_piv0
python3 -I cut_cell.py 2147483497 m12m3 1 ab ab cut/A_m12m3_p97_piv1
echo CUT1_DONE
