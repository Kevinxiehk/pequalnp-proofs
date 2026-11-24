#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r12
while pgrep -f "[r]unQ.sh q_B0g0" > /dev/null; do sleep 10; done
./runQ.sh q_U0g0 q_U0g1 q_U0h0 q_U0i q_U1g0 q_U1g1 q_U1h0 q_U1i q_U2g0 q_U2g1 q_U2h0 q_U2i
./runQ.sh q_S+_1_0 q_S+_1_2 q_S-_1_0 q_S-_1_2 q_S+_-1_0 q_S+_-1_2 q_S-_-1_0 q_S-_-1_2
