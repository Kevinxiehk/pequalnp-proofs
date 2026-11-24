#!/bin/bash
cd /home/kevxhk/work/L-gct-210/leanfl/cert
M=/home/kevxhk/work/L-gct-210/verify2/r18/pt2_P2147483629/01_01_01.ms
V=$(head -1 $M | tr -d ' \r'); C=$(sed -n 2p $M | tr -d ' \r')
ulimit -v 500000
for alg in std slimgb; do
/usr/bin/time -f "time %e s maxrss %M KB" timeout 300 Singular -q --no-rc <<SING
ring R=$C,($V),dp;
execute("ideal E=" + read("pt2.eqs") + ";");
system("--ticks-per-sec",1000); int t0=timer;
ideal G = $alg(E);
printf("pt2 $alg: ms %s size %s", timer-t0, size(G));
quit;
SING
done
( time msolve -f $M -o /tmp/pt2.msout -g 2 -t 1 ) 2>&1 | grep real; cat /tmp/pt2.msout | grep -v "^#"
