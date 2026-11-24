#!/bin/bash
# Big-memory slot sequencer v2 (coordinator, 22:35 UTC). Replaces bigq.sh after its running step (m12m3 case 9 al!=0).
# Order: (PL) ----- ; T22 m12m3 5 4 1 0 ; [DC3] p5b hard cells ; Lean window 2 ; T31 B1 m12m3 (9) ; iso T22 + T31 B1 ; window 3 ; m11m2 T22
W=/home/kevxhk/work; L=$W/L-gct-210; R7=$L/verifyfl/r7; R8=$L/verifyfl/r8
log() { echo "$(date -u +%T) $*"; }
decided() { grep -qE "VERDICT.* case $2( |$).*m=$1 " $R7/n3_chain_$1.log $W/runs/t22h_${1}_c$2.log 2>/dev/null; }
big() {  # big LOGFILE DIR CMD...   (runs CMD in DIR inside the big slot)
  local lg=$1 d=$2; shift 2
  ( cd "$d" && $W/tools/bigslot.sh sh -c "$*" ) > "$lg" 2>&1
}
t22() {
  if decided $1 $2; then log "skip T22 $1 case $2 (decided)"; return; fi
  log "T22 $1 case $2 start"
  big $W/runs/t22h_${1}_c$2.log $R7 "ulimit -v 8000000; MSOLVE_THREADS=4 timeout 11000 python3 -I n3_case.py 2147483629 $1 $2 n3q 10800 3600"
  log "T22 $1 case $2 end: $(grep -h VERDICT $W/runs/t22h_${1}_c$2.log | tail -1)"
}
t31b1() {  # t31b1 M X I
  log "T31 B1 $1 x$2 om$3 start"
  big $W/runs/t31b1_${1}_x$2_om$3.log $R8 "ulimit -v 10000000; MSOLVE_THREADS=1 timeout 11000 python3 -I t31e_stages.py B1:$2:$3 2147483629 $1 0 t31/Q_B1_${1}_x$2_om$3 'Z;Z3;Z1;Z31' 10800"
  log "T31 B1 $1 x$2 om$3 end: $(grep -h VERDICT $W/runs/t31b1_${1}_x$2_om$3.log | tail -1)"
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
        ( cd /home/kevxhk/code/pequalnp-proofs-2/lean && /usr/bin/time -f "== time %e s, peak memory %M KB" timeout 2400 lake env lean $tmp/check.lean ) > $lg 2>&1
        echo "== lean exit code: $?" >> $lg; rm -rf $tmp; log "  $role $(basename $f): $(tail -1 $lg), $(grep -c ': error' $lg) errors -> $lg"
      done
    done
    $W/tools/leanwindow.sh resume )
  log "LEAN WINDOW end"
}
# 1. rows (PL) 5 columns: summed-cubic pattern ----- without the 2 GB cap
log "SUMQ5 ----- (big slot) start"
big $L/rows/r8/orb/sq5big_-----.out $L/rows/r8/orb "ulimit -v 7000000; /usr/bin/time -f '%e s %M KB' timeout 10800 Singular -q sq5_-----_2147483629.sing"
log "SUMQ5 ----- end: $(grep -h RESULT $L/rows/r8/orb/sq5big_-----.out | tail -1)"
# 2. m12m3 T22 symmetry-needed cases
for C in 5 4 1 0; do t22 m12m3 $C; done
# 3. [DC3] for m0 = (1,1,1,1,-4): the 6 hard cells (Lemma PFC chain)
for I in 13 4 10 2 1 0; do
  log "DC3 p5b hard cell $I start"
  big $W/runs/dc3p45cut/p5b_hard_i$I.log $R8 "ulimit -v 10000000; MSOLVE_THREADS=1 timeout 11000 python3 -I dc_cut.py 2147483629 p5b 3 $I /home/kevxhk/work/runs/dc3p45cut/p5b_i$I 10800"
  log "DC3 p5b hard cell $I end: $(grep -hE 'VERDICT|UNIT|NONUNIT' $W/runs/dc3p45cut/p5b_hard_i$I.log | tail -1)"
done
# 4. Lean window 2
leanwin
# 5. T31 split B1 for m12m3 (split A and B0 are done)
for X in 0 1 2; do for I in 1 2 3; do t31b1 m12m3 $X $I; done; done
# 6. iso
for C in 9 5 4 1 0; do t22 iso $C; done
for X in 0 1 2; do for I in 1 2 3; do t31b1 iso $X $I; done; done
leanwin
# 7. m11m2 T22
for C in 9 5 4 1 0; do t22 m11m2 $C; done
log "ALLDONE"
