#!/bin/bash
# LEAN WINDOW 1: take the shared slot right after the running big job, pause long jobs, compile the queued Lean files back to back,
# resume, then restart the T22H driver (cases 7..0).
W=/home/kevxhk/work; L=$W/L-gct-210; PROJ=/home/kevxhk/code/pequalnp-proofs-2/lean
export PATH=$HOME/.elan/bin:$PATH
exec 9>$W/tools/leanslot.lock
echo "window: waiting for slot $(date -u +%T)"; flock 9; echo "window: OPEN $(date -u +%T)"
$W/tools/leanwindow.sh pause
comp() {  # comp FILE LOG [THEOREMNAME]
  local f=$1 log=$2 tmp=$(mktemp -d)
  cp $f $tmp/check.lean
  local n=$(grep -oE '^theorem PEqualNP\.Outside\.L_[a-z0-9_]+' $f | head -1 | cut -d' ' -f2); [ -n "$n" ] && printf '\n#print axioms %s\n' $n >> $tmp/check.lean
  ( cd $PROJ && /usr/bin/time -f "== time %e s, peak memory %M KB" timeout 2400 lake env lean $tmp/check.lean ) > $log 2>&1; local rc=$?
  echo "== lean exit code: $rc" >> $log; rm -rf $tmp; echo "window: $(basename $f) exit $rc $(grep -c ': error' $log) errors $(date -u +%T)"; return $rc
}
comp $L/lean/fl/FLk.lean $L/leanfl/FLk_w1.log
if comp $L/leanfl/Tps2.lean $L/leanfl/Tps2_w1.log; then comp $L/lean/fl/FLl.lean $L/leanfl/FLl_w1.log; else echo "window: Tps2 failed, FLl skipped"; fi
comp $L/lean/zbf/R4b.lean $L/leanzbf/R4b_w1.log
$W/tools/leanwindow.sh resume
flock -u 9
echo "window: CLOSED $(date -u +%T)"
nohup nice -n 10 $W/runs/t22h2.sh > $W/runs/t22h2_driver.log 2>&1 &
echo "window: T22H driver (cases 7..0) restarted $(date -u +%T)"
