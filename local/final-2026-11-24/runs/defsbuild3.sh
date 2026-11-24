#!/bin/bash
# Generic rebuild of PEqualNP.Defs after upstream adds Defs modules: build each imported PEqualNP.Defs.* module whose .olean is missing,
# one at a time (memory), then PEqualNP.Defs. Never builds Mathlib (aborts if lake starts to). Runs inside bigslot.sh.
export PATH=$HOME/.elan/bin:$PATH
cd /home/kevxhk/code/pequalnp-proofs-2/lean
mods=$(grep "^import PEqualNP.Defs\." PEqualNP/Defs.lean | sed 's/import //' | while read m; do [ -f .lake/build/lib/lean/$(echo $m | tr . /).olean ] || echo $m; done)
for m in $mods PEqualNP.Defs; do
  echo "$(date -u +%T) build $m"
  /usr/bin/time -f "   %e s %M KB" timeout 900 lake build $m > /tmp/defsb3_$$.log 2>&1; rc=$?
  tail -2 /tmp/defsb3_$$.log
  if grep -iqE "(building|built|compiling) Mathlib" /tmp/defsb3_$$.log; then echo "ABORT: lake tried to build Mathlib"; rm -f /tmp/defsb3_$$.log; exit 3; fi
  rm -f /tmp/defsb3_$$.log
  [ $rc -ne 0 ] && { echo "$(date -u +%T) DEFS BUILD3 FAILED at $m rc=$rc"; exit $rc; }
done
echo "$(date -u +%T) DEFS BUILD3 end: exit 0"
