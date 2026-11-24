#!/bin/bash
# round 18: the open P2 items of A case 0 at the N level with mu + the rank split r1 / r2 (R18.1); driver capped at 600 MB
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; LOG=nlam/p2open_c0.log
for it in ab:ab:z1/- ab:ab:z2/- ab:ab:0/- ab:z1:ab/- ab:z2:ab/- ab:0:ab/- z1:ab:ab/- z2:ab:ab/- 0:ab:ab/- ab:ab:ab/nl ab:ab:ab/01 ab:ab:ab/02 ab:ab:ab/12; do
  for r in r1 r2; do
    python3 -I rsscap.py 600 900 python3 -I nlam.py A 0 pc P2/$it mu p2=$r 300 2>&1 | grep -E "VERDICT|RSSCAP" | sed "s|^RSSCAP|VERDICT nlam A c0 pc P2/$it p2=$r: DRIVER-CAP RSSCAP|" >> $LOG
  done
done
echo "DONE p2open $(date -u +%T)" >> $LOG
