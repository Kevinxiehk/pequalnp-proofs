#!/bin/bash
# Big-memory slot scheduler v3 (coordinator, 2026-11-23 23:20 UTC). Replaces bigq2.sh, sumq5big.sh, m0alpha.sh, p5bt22big.sh
# (which competed for the slot in random order). One ordered list; pass 1 time-boxes every Groebner job at 1 h, pass 2 reruns
# the undecided ones with 3 h. Every job skips itself when any of its logs already holds a verdict, so a restart is cheap.
W=/home/kevxhk/work; L=$W/L-gct-210; R7=$L/verifyfl/r7; R8=$L/verifyfl/r8; R9=$L/verifyfl/r9; O=$L/rows/r8/orb
log() { echo "$(date -u +%T) $*"; }
DEC='VERDICT.*: (UNIT|NONUNIT)|RESULT SUMQ.*unit [01]|RESULT cross family|RESULT F2col'
decided() { grep -qsE "$DEC" "$@"; }
big() {  # big LOGFILE DIR CMD...
  local lg=$1 d=$2; shift 2
  ( cd "$d" && $W/tools/bigslot.sh sh -c "$*" ) > "$lg" 2>&1
}
endline() { echo "$(grep -hE "VERDICT|RESULT SUMQ" "$1" | tail -1) $(grep -h ' KB$' "$1" | tail -1)"; }
t22g() {  # [T22] cell for m0 = p5b (n3g driver)
  local C=$1 TB=$2 P=$3 lg=$W/runs/p5bt22_c$1_p$3.log
  if decided $W/runs/p5bt22_c$C.log $W/runs/p5bt22_c${C}_p*.log; then log "skip p5b T22 cell $C (decided)"; return; fi
  log "p5b T22 cell $C pass $P start (box $TB s)"
  big $lg $R9 "ulimit -v 10000000; MSOLVE_THREADS=1 timeout $((TB+300)) python3 -I n3g_case.py 2147483629 p5b $C n3g $TB $((TB*2/3))"
  log "p5b T22 cell $C pass $P end: $(endline $lg)"
}
m0a() {  # [T31] split A (alpha) KT chart for m0
  local I=$1 TB=$2 P=$3 lg=$W/runs/m0alpha_$1_p$3.log
  if decided $W/runs/m0alpha_$I*.log; then log "skip M0 alpha chart $I (decided)"; return; fi
  log "M0 alpha chart $I pass $P start (box $TB s)"
  big $lg $R9 "ulimit -v 10000000; MSOLVE_THREADS=1 timeout $((TB+300)) python3 -I ../r8/t31e_stages.py M0K:$I 2147483629 p5b 0 m0/Q_alphaK_$I 'Z1;Z2;Z12' $TB"
  log "M0 alpha chart $I pass $P end: $(endline $lg)"
}
dc3() {  # [DC3] hard cell for m0
  local I=$1 TB=$2 P=$3 lg=$W/runs/dc3p45cut/p5b_hard_i$1_p$3.log
  if decided $W/runs/dc3p45cut/p5b_hard_i$I.log $W/runs/dc3p45cut/p5b_hard_i${I}_p*.log; then log "skip DC3 p5b hard cell $I (decided)"; return; fi
  log "DC3 p5b hard cell $I pass $P start (box $TB s)"
  big $lg $R8 "ulimit -v 10000000; MSOLVE_THREADS=1 timeout $((TB+300)) python3 -I dc_cut.py 2147483629 p5b 3 $I /home/kevxhk/work/runs/dc3p45cut/p5b_i$I $TB"
  log "DC3 p5b hard cell $I pass $P end: $(endline $lg)"
}
sq5() {  # rows' five-column summed-cubic pattern
  local SG=$1 TB=$2 P=$3 lg=$O/sq5big_$1_p$3.out
  if decided $O/sq5big_$SG.out $O/sq5big_${SG}_p*.out; then log "skip SUMQ5 $SG (decided)"; return; fi
  log "SUMQ5 $SG pass $P start (box $TB s)"
  ( cd $O && python3 -I sumq.py $SG sq5_${SG}_2147483629.sing 2147483629 > /dev/null )
  big $lg $O "ulimit -v 7000000; /usr/bin/time -f '%e s %M KB' timeout $TB Singular -q sq5_${SG}_2147483629.sing"
  log "SUMQ5 $SG pass $P end: $(endline $lg)"
}
t22() {  # [T22] symmetry-needed case for a line m (n3 driver)
  local M=$1 C=$2 TB=$3 P=$4 lg=$W/runs/t22h_$1_c$2_p$4.log
  if grep -qsE "VERDICT.* case $C( |$).*m=$M .*(UNIT|NONUNIT)" $R7/n3_chain_$M.log $W/runs/t22h_${M}_c$C*.log; then log "skip T22 $M case $C (decided)"; return; fi
  log "T22 $M case $C pass $P start (box $TB s)"
  big $lg $R7 "ulimit -v 8000000; MSOLVE_THREADS=4 timeout $((TB+300)) python3 -I n3_case.py 2147483629 $M $C n3q $TB $((TB/3))"
  log "T22 $M case $C pass $P end: $(endline $lg)"
}
st2x() {  # stage2 ST2-F2COL-v2 (b): the 3 cross-type ruling charts of F2col that crash msolve at 2 GB
  local TB=$1 P=$2 lg=$L/stage2/r9/cross3_big_p$2.log
  if decided $L/stage2/r9/cross3_big_p*.log; then log "skip ST2 cross-type 3 charts (decided)"; return; fi
  log "ST2 cross-type 3 charts pass $P start (box $TB s)"
  big $lg $L/stage2 "MSV=6000000 CHARTS='2-3-4-7 2-3-5-7 2-4-5-7' timeout $TB python3 -I r13_crosscharts_sat2.py 2147483629 1"
  log "ST2 cross-type 3 charts pass $P end: $(grep -h 'RESULT cross\|NONUNIT\|FAILED' $lg | tail -2 | tr '\n' ' ')"
}
symc() {  # verifyfl VF-SYM-SPLIT: symbolic-m [DC3] generic rank-2 cells, piece vartheta(Z_0) != 0 (sym_cut2.py ne)
  local C=$1 PIV=$2 TB=$3 P=$4 lg=$W/runs/symcut2_$1$2_ne_p$4.log
  if decided $W/runs/symcut2_${C}${PIV}_ne_p*.log; then log "skip SYM DC3 ne $C$PIV (decided)"; return; fi
  log "SYM DC3 ne $C$PIV pass $P start (box $TB s)"
  big $lg $L/verifyfl/r11 "ulimit -v 10000000; MSOLVE_THREADS=1 timeout $TB python3 -I sym_cut2.py 2147483629 $C $PIV ne sc2/Q_${C}${PIV}_ne"
  log "SYM DC3 ne $C$PIV pass $P end: $(endline $lg)"
}
extras() {  # run injected jobs: lines "ID|DIR|LOG|ULIMIT_KB|BOX_S|CMD" in runs/bigq_extra.txt, once each (IDs recorded in runs/bigq_extra.done); IDs LOW_* only with "extras low"
  local F=$W/runs/bigq_extra.txt D=$W/runs/bigq_extra.done mode=${1:-hi} budget=${2:-999999} t0=$(date +%s)
  [ -s $F ] || return 0; touch $D
  while IFS='|' read -r id dir lg ul box cmd; do
    [ -z "$id" ] && continue; case "$id" in \#*) continue;; esac
    grep -qx "$id" $D && continue
    case "$id" in LOW_*) [ "$mode" = low ] || continue;; esac
    [ $(( $(date +%s) - t0 )) -ge $budget ] && { log "EXTRA budget ${budget}s used; rest deferred"; break; }
    echo "$id" >> $D
    log "EXTRA $id start (box $box s)"
    big $lg $dir "ulimit -v $ul; timeout $box $cmd"
    log "EXTRA $id end: $(grep -hE 'VERDICT|RESULT|unit|UNIT|NONUNIT' $lg | tail -1 | cut -c1-200) $(tail -1 $lg | cut -c1-120)"
  done < <(cat $F)
}
leanwin() {
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
        ( cd /home/kevxhk/code/pequalnp-proofs-2/lean && /usr/bin/time -f "== time %e s, peak memory %M KB" timeout 3600 lake env lean $tmp/check.lean ) > $lg 2>&1
        echo "== lean exit code: $?" >> $lg; rm -rf $tmp; log "  $role $(basename $f): $(tail -1 $lg), $(grep -c ': error' $lg) errors -> $lg"
      done
    done
    $W/tools/leanwindow.sh resume )
  log "LEAN WINDOW end"
}
# 0. the running SUMQ5 ----- (started by bigq2.sh at 23:05 with a 3 h box) keeps the slot until it ends
H=168503; ps -o args= -p $H 2>/dev/null | grep -q 'sq5_-----_' || H=
if [ -n "$H" ]; then log "waiting for SUMQ5 ----- (bigslot pid $H)"; while kill -0 $H 2>/dev/null; do sleep 20; done; log "SUMQ5 ----- end: $(endline $O/sq5big_-----.out)"; fi
# PASS 1 (1 h boxes): interleave the (SL_m0) pieces with rows' (PL) patterns; Lean window 2 early
pass() {
  local TB=$1 P=$2
  [ $P = 1 ] && [ -z "$SKIPWIN1" ] && leanwin
  { [ $P = 1 ] && [ -n "$SKIPST2X" ]; } || st2x $TB $P; { [ $P = 1 ] && [ -n "$SKIPSYMC" ]; } || { symc A 0 $TB $P; symc A 1 $TB $P; symc B 0 $TB $P; symc B 1 $TB $P; }   # pass 1: superseded by SYMDC3V2 extras
  { [ $P = 1 ] && [ -n "$SKIPC12" ]; } || t22g 12 $TB $P; dc3 13 $TB $P
  [ $P = 1 ] && leanwin   # window 3 (compiles are ~10 min per file, so windows can be frequent)
  extras hi 14400
  sq5 +---- $TB $P; t22g 11 $TB $P; dc3 4 $TB $P
  extras hi 10800
  sq5 ++--- $TB $P; t22g 2 $TB $P; dc3 10 $TB $P
  extras hi 10800
  sq5 +++-- $TB $P; dc3 2 $TB $P; sq5 ++++- $TB $P; dc3 1 $TB $P
  extras hi 10800
  sq5 +++++ $TB $P; dc3 0 $TB $P; t22g 1 $TB $P; t22g 0 $TB $P
  [ $P = 2 ] && sq5 ----- $TB $P
  [ $P = 1 ] && { m0a 0 $TB $P; m0a 1 $TB $P; m0a x $TB $P; }   # cross-check only: stage3 closed (alpha1) supp 2/4 at P1 (23:39)
  extras
  extras low
  [ $P = 2 ] && for C in 5 4 1 0; do t22 m12m3 $C $TB $P; done   # sample line: low value now that SYM-M covers |supp m| <= 3
}
pass 3600 1
leanwin
# PASS 2 (3 h boxes) for everything still undecided
pass 10800 2
leanwin
log "ALLDONE (B1 / iso / m11m2 to be scheduled after verifyfl's round 10)"
