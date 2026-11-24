#!/bin/bash
# leanfl compile chain (detached): FLk (guard-fixed v32), then the small test Tps2, then FLl if Tps2 compiled.
L=/home/kevxhk/work/L-gct-210/leanfl
cd /home/kevxhk/work/L-gct-210/lean/fl || exit 1
/home/kevxhk/work/tools/leancheck FLk.lean > $L/FLk3.log 2>&1
cd $L || exit 1
/home/kevxhk/work/tools/leancheck Tps2.lean > $L/Tps2.log 2>&1
if grep -q "lean exit code: 0" $L/Tps2.log; then
  cd /home/kevxhk/work/L-gct-210/lean/fl && /home/kevxhk/work/tools/leancheck FLl.lean > $L/FLl.log 2>&1
fi
echo "chain done $(date -u +%T)" > $L/chain.done
