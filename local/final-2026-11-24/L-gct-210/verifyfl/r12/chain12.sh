#!/bin/bash
# round-12 pool chain (one job at a time, <= 2.5 GB): after the det split -> rho = 1 piece IV (A10) -> iso test (A0 generic) -> sym_cut3 A0
cd /home/kevxhk/work/L-gct-210/verifyfl/r12
while ps aux | grep -q "[t]0c_cell.py 2147483629 A 0"; do sleep 5; done
echo "$(date -u +%T) start t1 A10" >> chain12.log
(ulimit -v 2500000; MSOLVE_THREADS=1 timeout 1500 python3 -I t1_cell.py 2147483629 A 10 t1 300 > t1_A10.log 2>&1)
echo "$(date -u +%T) start iso A0 ab:ab:ab,z1:z1:z1" >> chain12.log
(ulimit -v 2500000; MSOLVE_THREADS=1 timeout 1500 python3 -I iso_cell.py 2147483629 A 0 iso 300 ab:ab:ab,z1:z1:z1 > iso_A0.log 2>&1)
echo "$(date -u +%T) start sym_cut3 A0" >> chain12.log
mkdir -p sc3; (ulimit -v 2500000; SYMTMO=1500 MSOLVE_THREADS=1 timeout 1700 python3 -I sym_cut3.py 2147483629 A 0 sc3/A0 > sc3/A0.log 2>&1)
echo "$(date -u +%T) chain done" >> chain12.log
