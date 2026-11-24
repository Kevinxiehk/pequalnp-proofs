#!/bin/bash
# vf_rc4_guarded.sh PIECE (02|12): run verifyfl's rc4 big-slot job for t0c-PIECE only if VFRAD_A0_01_RC4 ended "VERDICT radcell3 ...: OK"
# (verifyfl 05:52: if t0c-01's rc4 fails at 10 GB, hold 02/12 and switch cuts). Run from verifyfl/r12.
P=$1; G=/home/kevxhk/work/runs/vf_rad_A0_01_rc4.log
if grep -h "VERDICT radcell3" $G 2>/dev/null | tail -1 | grep -q ": OK"; then
  exec env RCS=4 RAB=1 MSOLVE_THREADS=1 python3 -I radcell3t.py 2147483629 A 0 t0c $P rad/big_A0_t0c_${P}R 3000 t0/t0c_A_c0_${P}_None_N.ms.gb
fi
echo "HELD $(date -u +%T): VFRAD_A0_01_RC4 did not end OK ($(grep -h 'VERDICT' $G 2>/dev/null | tail -1 | cut -c1-150)); t0c-$P rc4 not run"
