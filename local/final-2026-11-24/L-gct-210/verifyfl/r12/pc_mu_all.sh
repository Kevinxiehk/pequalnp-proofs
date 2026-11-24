#!/bin/bash
# all items of P1a, P1b, P2 (A case 0) at N-level with the mu junk removal + early two-column Rabinowitsch (R17.5); capped msolve calls
cd /home/kevxhk/work/L-gct-210/verifyfl/r12
for pc in P1a P1b P2; do
  for a in ab z1 z2 0; do for b in ab z1 z2 0; do for c in ab z1 z2 0; do
    [ "$a:$b:$c" = "ab:ab:ab" ] && continue
    timeout 600 python3 -I nlam.py A 0 pc $pc/$a:$b:$c/- mu 120 2>&1 | grep VERDICT
  done; done; done
  for d in ne 01 02 12; do timeout 900 python3 -I nlam.py A 0 pc $pc/ab:ab:ab/$d mu 300 2>&1 | grep VERDICT; done
done
echo "DONE pc_mu_all $(date -u +%T)"
