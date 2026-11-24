#!/bin/bash
# big-slot batch 2 (round 18): the open P2 items of A case 0 at the N level (mu); if an item is not N-UNIT, its rank split r1 / r2 (R18.1).
# Each msolve call capped at NLAM_CAP (default 2400 MB) and its timeout; verdict lines in the log.
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; export NLAM_CAP=${NLAM_CAP:-2400}
for it in ab:ab:z1/- ab:ab:z2/- ab:ab:0/- ab:z1:ab/- ab:z2:ab/- ab:0:ab/- z1:ab:ab/- z2:ab:ab/- 0:ab:ab/- ab:ab:ab/nl ab:ab:ab/01 ab:ab:ab/02 ab:ab:ab/12; do
  out=$(timeout 2000 python3 -I nlam.py A 0 pc P2/$it mu 1500 2>&1 | grep VERDICT); echo "$out"
  if ! echo "$out" | grep -q "N-UNIT"; then
    for r in r1 r2; do timeout 2000 python3 -I nlam.py A 0 pc P2/$it mu p2=$r 1500 2>&1 | grep VERDICT; done
  fi
done
echo "DONE nlam_batch2 $(date -u +%T)"
