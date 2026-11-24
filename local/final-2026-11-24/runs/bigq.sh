#!/bin/bash
# Big-memory slot sequencer (coordinator). Ordered to finish (SL_m) for m12m3 first, then a Lean window, then iso, then m11m2.
# Every big step runs through bigslot.sh (shared lock with Lean compiles, long jobs paused meanwhile).
W=/home/kevxhk/work; L=$W/L-gct-210; R7=$L/verifyfl/r7; R8=$L/verifyfl/r8
log() { echo "$(date -u +%T) $*"; }
decided() { grep -qE "VERDICT.* case $2( |$).*m=$1 " $R7/n3_chain_$1.log $W/runs/t22h_${1}_c$2.log 2>/dev/null; }
t22() {  # t22 M C
  if decided $1 $2; then log "skip T22 $1 case $2 (decided)"; return; fi
  log "T22 $1 case $2 start"
  ( cd $R7 && $W/tools/bigslot.sh sh -c "ulimit -v 8000000; MSOLVE_THREADS=4 timeout 11000 python3 -I n3_case.py 2147483629 $1 $2 n3q 10800 3600" ) > $W/runs/t22h_${1}_c$2.log 2>&1
  log "T22 $1 case $2 end: $(grep -h VERDICT $W/runs/t22h_${1}_c$2.log | tail -1)"
}
t31b() {  # t31b K M
  log "T31B $1 $2 start"
  ( cd $R8 && $W/tools/bigslot.sh sh -c "ulimit -v 8000000; MSOLVE_THREADS=4 timeout 11000 python3 -I t31e_stages.py $1 2147483629 $2 012 t31/Q_${1}_$2 'Z;Z0;Z1;Z2;Z01;Z012' 10800" ) > $W/runs/t31b_${1}_$2.log 2>&1
  log "T31B $1 $2 end: $(grep -h VERDICT $W/runs/t31b_${1}_$2.log | tail -1)"
}
leanwin() {  # compile the files each Lean helper lists in <role>/window_files.txt (one path per line, # = comment)
  log "LEAN WINDOW start"
  ( exec 9>$W/tools/leanslot.lock; flock 9; $W/tools/leanwindow.sh pause
    export PATH=$HOME/.elan/bin:$PATH
    for role in leanfl leanzbf; do
      [ -s $L/$role/window_files.txt ] || continue
      for f in $(grep -v '^#' $L/$role/window_files.txt); do
        [ -f "$f" ] || continue
        tmp=$(mktemp -d); cp "$f" $tmp/check.lean
        n=$(grep -oE '^theorem PEqualNP\.Outside\.L_[a-z0-9_]+' "$f" | head -1 | cut -d' ' -f2); [ -n "$n" ] && printf '\n#print axioms %s\n' "$n" >> $tmp/check.lean
        lg=$L/$role/$(basename "$f" .lean)_w$(date -u +%H%M).log
        ( cd /home/kevxhk/code/pequalnp-proofs-2/lean && /usr/bin/time -f "== time %e s, peak memory %M KB" timeout 2400 lake env lean $tmp/check.lean ) > $lg 2>&1
        echo "== lean exit code: $?" >> $lg; rm -rf $tmp; log "  $role $(basename $f): $(tail -1 $lg), $(grep -c ': error' $lg) errors -> $lg"
      done
    done
    $W/tools/leanwindow.sh resume )
  log "LEAN WINDOW end"
}
# 1. m12m3: T22 case 9 piece al != 0 (1 thread, 10 GB), then the symmetry-needed cases 5 4 1 0
log "T22 m12m3 case 9 (al != 0) start"
( cd $R7 && $W/tools/bigslot.sh sh -c "ulimit -v 10000000; MSOLVE_THREADS=1 timeout 11000 python3 -I n3_case_split.py 2147483629 m12m3 9 n3s 10800 7200 alne" ) > $W/runs/t22h_m12m3_c9_alne.log 2>&1
log "T22 m12m3 case 9 (al != 0) end: $(grep -h VERDICT $W/runs/t22h_m12m3_c9_alne.log | tail -1)"
# 1b. rows (PL) 5 columns: summed-cubic pattern ----- without the 2 GB cap
log "SUMQ5 ----- (big slot) start"
( cd $L/rows/r8/orb && $W/tools/bigslot.sh sh -c "ulimit -v 7000000; /usr/bin/time -f '%e s %M KB' timeout 10800 Singular -q sq5_-----_2147483629.sing" ) > $L/rows/r8/orb/sq5big_-----.out 2>&1
log "SUMQ5 ----- end: $(grep -h RESULT $L/rows/r8/orb/sq5big_-----.out | tail -1)"
for C in 5 4 1 0; do t22 m12m3 $C; done
# 2. m12m3: T31 split B pieces
for K in E0 E11 E12 E13; do t31b $K m12m3; done
# 3. Lean window 2
leanwin
# 4. iso, then m11m2
for C in 9 5 4 1 0; do t22 iso $C; done
for K in E0 E11 E12 E13; do t31b $K iso; done
leanwin
for C in 9 5 4 1 0; do t22 m11m2 $C; done
log "ALLDONE"
