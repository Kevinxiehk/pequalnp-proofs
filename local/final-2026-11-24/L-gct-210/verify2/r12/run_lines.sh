#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
L() { tag=$1; shift; timeout 1200 python3 -I rr_oe0_line.py "$@" > oel_$tag.log 2>&1; echo "$tag: $(grep -m1 'pivot sets cover' oel_$tag.log | sed 's/.*COVSIZE//') | $(grep -c 'NON-unit in \[\]' oel_$tag.log) pivot sets all-unit | $(grep VERDICT oel_$tag.log | cut -c1-90)"; }
L 213_c3 213def none 4 col,4 2 "3*u2^2+2*u2+3;2*u1+u2+1" "u1=-0.3333333333333333-0.4714045207910317j;u2=-0.3333333333333333+0.9428090415820634j"
L 213_c5 213def none 4 col,4 2 "u1^2+u1+1;u2" "u1=-0.5+0.8660254037844386j;u2=0"
L 213_c6 213def none 4 col,4 2 "u1+1;u2" "u1=-1;u2=0"
L 213_c7 213def none 4 col,4 2 "u1;u2" "u1=0;u2=0"
L 213_c9 213def none 4 col,4 2 "u2^2+2*u2+3;u1-1" "u1=1;u2=-1+1.4142135623730951j"
L 213_c10 213def none 4 col,4 2 "u1-1;u2+1" "u1=1;u2=-1"
L 213_c11 213def none 4 col,4 2 "u1-1;u2-1" "u1=1;u2=1"
L A1_sp1 11121A1 col,4,3 3 col,3 2 "s-1" "s=1"
L A1_sm1 11121A1 col,4,3 3 col,3 2 "s+1" "s=-1"
timeout 1500 python3 -I rr_omega_e0.py 22_2 row,0,1 0 row,1 4 > oe0_22_2_np4.log 2>&1; echo "22_2 npiv4: $(grep -m1 'pivot sets cover' oe0_22_2_np4.log | sed 's/.*COVSIZE//') | $(grep VERDICT oe0_22_2_np4.log | cut -c1-90)"
echo done
