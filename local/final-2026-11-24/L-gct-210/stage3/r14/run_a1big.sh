#!/bin/bash
# (alpha1) supp 2 (sign patterns up to global sign and the column swaps 0<->1, 2<->3) and supp 4 (up to global sign and S_4 on columns 0..3)
ulimit -v 2000000
cd /home/kevxhk/work/L-gct-210/stage3/r14
for sg in ++++ ++-+ ++-- +-++ +--+ +---; do for fc in 0 1 2; do
  f=$(python3 -I alpha1_gen.py 2 $sg $fc); echo "$(timeout 900 Singular -q $f 2>&1 | grep -E 'RESULT|halt') [$f]"
done; done
for sg in ++++ +++- ++--; do for fc in 0 1 2; do
  f=$(python3 -I alpha1_gen.py 4 $sg $fc); echo "$(timeout 900 Singular -q $f 2>&1 | grep -E 'RESULT|halt') [$f]"
done; done
echo DONE
