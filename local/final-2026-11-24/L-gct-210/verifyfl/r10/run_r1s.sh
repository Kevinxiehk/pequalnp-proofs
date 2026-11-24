#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r10
for vc in w c3; do for sc in 0 1 2; do
  for spec in "0" "1/w" "1/c3" "2/w,w" "2/w,c3" "2/c3,w" "2/c3,c3"; do
    nz=${spec%%/*}; nch=""; [ "$spec" != "0" ] && nch="/${spec#*/}"
    k="M0RS:$vc/$nz/$sc$nch"
    r=$(timeout 900 python3 -I ../r8/t31e_stages.py "$k" 2147483629 p5b 0 m0/r1s_$(echo $k | tr ':/,' '___') "Z;Z1;Z2;Z12" 800 2>&1 | grep VERDICT)
    echo "$k: $r"
  done
done; done
echo R1S_DONE
