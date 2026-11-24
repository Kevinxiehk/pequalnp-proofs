#!/bin/bash
# leancompile.sh FILE TIMEOUT_S [EXTRA_NAMES] : EXTRA_NAMES = comma-separated declarations to #print axioms as well (e.g. TC5_final); one Lean compile like a window step (copy to tmp, #print axioms for a final L_ theorem), summary line last.
f=$1; to=${2:-3600}; export PATH=$HOME/.elan/bin:$PATH
tmp=$(mktemp -d); cp "$f" $tmp/check.lean
n=$(grep -oE '^theorem PEqualNP\.Outside\.L_[a-z0-9_]+' "$f" | head -1 | cut -d' ' -f2); [ -n "$n" ] && printf '\n#print axioms %s\n' "$n" >> $tmp/check.lean
for x in $(echo "${3:-}" | tr ',' ' '); do printf '\n#print axioms %s\n' "$x" >> $tmp/check.lean; done
lg=$(mktemp)
( cd /home/kevxhk/code/pequalnp-proofs-2/lean && /usr/bin/time -f "== time %e s, peak memory %M KB" timeout $to lake env lean $tmp/check.lean ) > $lg 2>&1; rc=$?
cat $lg; rm -rf $tmp
echo "== LEAN SUMMARY $(basename $f): lean exit code $rc, $(grep -c ': error' $lg) errors, $(grep -c 'declaration uses' $lg) sorry-warnings, $(grep -h '== time' $lg | tail -1)"
rm -f $lg
