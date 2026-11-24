#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/leanzbf
timeout 900 python3 -I gen_e5.py 00012 00012 -1 034 013 000 010 e5_out/00012_00012_m.txt
timeout 900 python3 -I gen_e5.py 00012 01102 1 014 046 100 110 e5_out/00012_01102_p.txt
timeout 900 python3 -I gen_e5.py 00012 10102 1 014 037 000 010 e5_out/00012_10102_p.txt
timeout 900 python3 -I gen_e5.py 00012 11002 1 013 013 000 011 e5_out/00012_11002_p.txt
timeout 900 python3 -I gen_e5.py 01112 01112 -1 014 013 000 010 e5_out/01112_01112_m.txt
timeout 900 python3 -I gen_e5.py 00122 00122 -1 023 013 000 010 e5_out/00122_00122_m.txt
timeout 900 python3 -I gen_e5.py 00112 00112 -1 024 013 000 010 e5_out/00112_00112_m.txt
timeout 900 python3 -I gen_e5.py 00112 01002 1 014 034 100 101 e5_out/00112_01002_p.txt
timeout 900 python3 -I gen_e5.py 00112 10002 1 014 034 000 010 e5_out/00112_10002_p.txt
timeout 900 python3 -I gen_e5.py 00112 11002 1 012 013 000 011 e5_out/00112_11002_p.txt
timeout 900 python3 -I gen_e5.py 01122 01122 -1 013 013 000 010 e5_out/01122_01122_m.txt
echo DONE
