#!/bin/bash
cd /home/kevxhk/work/L-gct-210/leanfl/cert
for f in /home/kevxhk/work/L-gct-210/verify2/r18/pt2_P2147483629/01_01_01.ms:pt2 /home/kevxhk/work/L-gct-210/rows/r7/c3_B3_2147483629_s4/B3_000_f0.ms:b3 /home/kevxhk/work/L-gct-210/verify2/vf/run/own_2147483629_A2_chart13.ms:vfA2 /home/kevxhk/work/L-gct-210/stage3/gb/fc_FULL_2147483629_00001.ms:fc1 /home/kevxhk/work/L-gct-210/verifyfl/r12/symdc/symdc_s5_c0_p2147483629_k3_rho0_piv029_imgnone_x.ms:symdc29; do
  ./liftms.sh ${f%%:*} ${f##*:} 2>&1 | grep -E "^lift|^time|error|halt|Command" ; ls -l ${f##*:}.cof 2>/dev/null | awk '{print "cof bytes", $5}'
done
echo SWEEP1 DONE
