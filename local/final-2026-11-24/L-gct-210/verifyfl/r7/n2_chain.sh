#!/bin/bash
# [T31] stage a (Zs, Y_1, Y_2) via the staged subsystem cut, all cells, three m, p = 2147483629
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r7
for M in m12m3 m11m2 iso; do for c in 0 1 2 3 4 5; do
  python3 -I subcut.py n2 2147483629 $M $c a n2/${M}_c$c "0;0,1;0,2;0,1,2" timeout=900 2>&1 | grep -E "VERDICT|Error|error"
done; done
echo N2_DONE
