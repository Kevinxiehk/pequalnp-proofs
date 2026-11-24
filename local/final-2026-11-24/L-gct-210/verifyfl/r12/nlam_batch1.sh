#!/bin/bash
# big-slot batch (round 17): the generic all-'ab' N-level items of A case 0 that exceed the 550 MB pool cap; each msolve call capped at
# NLAM_CAP (default 2400 MB) and its own timeout; verdict lines in the log.
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; export NLAM_CAP=${NLAM_CAP:-2400}
timeout 3000 python3 -I nlam.py A 0 t0c nl perm 1500
for pc in P1a P1b; do for d in nl 01 02 12; do timeout 2000 python3 -I nlam.py A 0 pc $pc/ab:ab:ab/$d mu 1500; done; done
echo "DONE nlam_batch1 $(date -u +%T)"
