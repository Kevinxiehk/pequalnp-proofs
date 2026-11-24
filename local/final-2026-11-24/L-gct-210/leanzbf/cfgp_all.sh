#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/leanzbf
for f in cfg_out/*.txt; do
  t=$(basename $f .txt); a=${t:0:5}; b=${t:6:5}; e=${t:12:1}; [ "$e" = "p" ] && eps=1 || eps=-1
  timeout 600 python3 -I gen_cfgp.py $a $b $eps cfgp_out/$t.txt 2>&1 | tail -1
done
echo DONE
