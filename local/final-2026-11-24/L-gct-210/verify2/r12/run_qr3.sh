#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2000000
( timeout 1700 python3 -I qr3_fo2.py iso > qr3_iso.log 2>&1; timeout 1700 python3 -I qr3_fo2.py aa > qr3_aa.log 2>&1 ) &
( timeout 1700 python3 -I qr3_fo2.py ab > qr3_ab.log 2>&1 ) &
wait; echo done > qr3_done.flag
