#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r13
ulimit -v 2000000
( for m in neq par; do for a in 0 1 2; do timeout 1500 Singular -q s2m_${m}_${a}_P1.sing 2>&1 | grep S2MINE || echo "S2MINE-P1 $m $a TIMEOUT/ERR"; done; done; timeout 900 Singular -q s2m_cal_0_P1.sing 2>&1 | grep S2MINE || echo "S2MINE-P1 cal 0 TIMEOUT/ERR" ) > s2_P1.log 2>&1 &
( for m in neq par; do for a in 0 1 2; do timeout 1700 Singular -q s2m_${m}_${a}.sing 2>&1 | grep S2MINE || echo "S2MINE-Q $m $a TIMEOUT/ERR"; done; done ) > s2_Q.log 2>&1 &
wait; echo done > s2_done.flag
