#!/bin/bash
# Rebuild PEqualNP.Defs after upstream fb44ea9 (+3 Defs modules SplitCount/HeptadCover/ReadK, additive; toolchain/manifest unchanged since 2026-11-23).
# One module at a time to cap memory. Runs inside bigslot.sh. Never builds Mathlib (cache complete; abort if lake starts building Mathlib).
export PATH=$HOME/.elan/bin:$PATH
cd /home/kevxhk/code/pequalnp-proofs-2/lean
for m in PEqualNP.Defs.SplitCount PEqualNP.Defs.HeptadCover PEqualNP.Defs.ReadK PEqualNP.Defs; do
  echo "$(date -u +%T) build $m"
  /usr/bin/time -f "   %e s %M KB" timeout 900 lake build $m > /tmp/defsb2_$$.log 2>&1; rc=$?
  tail -3 /tmp/defsb2_$$.log
  if grep -q "Mathlib\." /tmp/defsb2_$$.log && grep -qiE "building|built" /tmp/defsb2_$$.log && grep -iE "(building|built) Mathlib" /tmp/defsb2_$$.log >/dev/null; then echo "ABORT: lake tried to build Mathlib"; rm -f /tmp/defsb2_$$.log; exit 3; fi
  rm -f /tmp/defsb2_$$.log
  [ $rc -ne 0 ] && { echo "$(date -u +%T) DEFS BUILD2 FAILED at $m rc=$rc"; exit $rc; }
done
echo "$(date -u +%T) DEFS BUILD2 end: exit 0"
