#!/bin/bash
# Rebuild PEqualNP.Defs after upstream f3e69b7 (+6 new Defs modules, additive). One module at a time to cap memory. Runs inside bigslot.sh.
export PATH=$HOME/.elan/bin:$PATH
cd /home/kevxhk/code/pequalnp-proofs-2/lean
for m in CarriedProduct CleanedNonEdge MergeCost SyntacticMultilinear TopForm TopFormNames; do
  echo "$(date -u +%T) build PEqualNP.Defs.$m"
  /usr/bin/time -f "   %e s %M KB" timeout 1800 lake build PEqualNP.Defs.$m 2>&1 | tail -3
done
echo "$(date -u +%T) build PEqualNP.Defs"; /usr/bin/time -f "   %e s %M KB" timeout 1800 lake build PEqualNP.Defs 2>&1 | tail -3
echo "$(date -u +%T) DEFS BUILD end: exit ${PIPESTATUS[0]}"
