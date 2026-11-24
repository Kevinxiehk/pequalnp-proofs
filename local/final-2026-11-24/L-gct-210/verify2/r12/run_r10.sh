#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
R=/home/kevxhk/work/L-gct-210/rows/r10
( /usr/bin/time -f "%e s %M KB" timeout 1700 Singular -q $R/extIIQ.sing > rr_extIIQ.out 2>&1; /usr/bin/time -f "%e s %M KB" timeout 1700 Singular -q $R/extIQ.sing > rr_extIQ.out 2>&1 ) &
( /usr/bin/time -f "%e s %M KB" timeout 1700 Singular -q $R/chi2Q.sing > rr_chi2Q.out 2>&1 ) &
wait; echo done > r10_done.flag
