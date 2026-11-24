#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r11
ulimit -v 2500000
S=/home/kevxhk/work/L-gct-210/stage3/r13
( /usr/bin/time -f "%e s %M KB" timeout 1500 Singular -q $S/alpha0_W4n_0145.sing > a0W4_0145.out 2>&1; /usr/bin/time -f "%e s %M KB" timeout 1500 Singular -q $S/alpha0_W4n_1234.sing > a0W4_1234.out 2>&1 ) &
( /usr/bin/time -f "%e s %M KB" timeout 1500 Singular -q $S/alpha0_W4n_0235.sing > a0W4_0235.out 2>&1 ) &
wait; echo done > a0_done.flag
