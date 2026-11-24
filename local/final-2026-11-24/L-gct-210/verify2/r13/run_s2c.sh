#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r13
ulimit -v 2000000
( for f in s2c_neq_2_p s2c_neq_3_p s2c_par_1_p s2c_par_2_p s2c_par_3_p s2c_cal_1_p; do /usr/bin/time -f "$f %e s %M KB" timeout 1500 Singular -q $f.sing 2>&1 | grep -E 'S2CHI| s ' || echo "$f TIMEOUT/ERR"; done ) > s2c_P1.log 2>&1 &
( for f in s2c_par_1_q s2c_neq_1_q s2c_par_2_q s2c_neq_2_q s2c_par_3_q s2c_neq_3_q; do /usr/bin/time -f "$f %e s %M KB" timeout 1700 Singular -q $f.sing 2>&1 | grep -E 'S2CHI| s ' || echo "$f TIMEOUT/ERR"; done ) > s2c_Q.log 2>&1 &
wait; echo done > s2c_done.flag
