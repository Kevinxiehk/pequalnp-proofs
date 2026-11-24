#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r7
python3 -I cut_cell.py 2147483629 m11m2 0 ab ab cut/A_m11m2_p29_piv0
python3 -I cut_cell.py 2147483629 m11m2 1 ab ab cut/A_m11m2_p29_piv1
python3 -I cut_cell.py 2147483629 iso 0 ab ab cut/A_iso_p29_piv0
echo CUT2_DONE
