#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r13
ulimit -v 2000000
echo "S2CHI par achart 1 char 0: dim -1 unit 1   (slimgb, 88.7 s, 179 MB)" > s2slim.log
for f in s2c_par_2_q_slim s2c_par_3_q_slim s2c_neq_1_q_slim s2c_neq_2_q_slim s2c_neq_3_q_slim; do /usr/bin/time -f "$f %e s %M KB" timeout 1700 Singular -q $f.sing >> s2slim.log 2>&1 || echo "$f TIMEOUT/ERR" >> s2slim.log; done
echo done >> s2slim.log
