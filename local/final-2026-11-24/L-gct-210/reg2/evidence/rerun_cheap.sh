#!/bin/bash
# Re-runs every cheap exact certificate quoted in the RESULT blocks of NOTES-reg2.md (rounds 3-9) with its output SAVED under
# reg2/evidence/logs/<name>.log (verify2 round 12: evidence must point to saved logs + scripts).  Sequential, 1 core, each run < 1 GB.
R=/home/kevxhk/work/L-gct-210/reg2; G=$R/gb; L=$R/evidence/logs
ulimit -v 1500000
run(){ name=$1; dir=$2; shift 2; ( cd $dir; echo "# $(date -u +%F' '%H:%M) cwd=$dir cmd: $*"; timeout 1500 "$@" ) > $L/$name.log 2>&1; echo "$name exit=$? $(date -u +%H:%M)" >> $L/_index.txt; }
: > $L/_index.txt
# ---- round 3
run r3_gen_s4            $G python3 -I gen_s4.py
run r3_special_D         $R python3 -I dr211_special.py D
run r3_special_S4pt      $R python3 -I dr211_special.py S4pt
run r3_special_S4        $R python3 -I dr211_special.py S4
run r3_special_s+1       $R python3 -I dr211_special.py pt 1,1,-2,0,1,-1,0,0,1,1,1,-3
run r3_special_s-1       $R python3 -I dr211_special.py pt 1,-1,0,0,1,1,-2,0,1,1,1,-3
run r3_p312_special      $R python3 -I p312_special.py
run r3_p33_cert          $R python3 -I p33_cert.py
# ---- round 4
run r4_el_exact          $R python3 -I el_exact.py
for f in "321a 16 25 2" "213 16 40 5" "3111 16 25 2" "2121V0 16 40 2" "2121Vni 16 40 2" "2121Vnii 16 40 2" "2121Vnii_s0 16 40 2" "2121Vnii_xinf 16 40 2" "11121A1 16 40 2" "11121B1 16 40 2" "11121B2 16 40 2"; do
  set -- $f; run r4_gen_rank_$1 $G python3 -I gen_rank.py $f
done
for m in 321 213 3111 21111; do run r4_nc_cert_$m $R python3 -I nc_cert.py $m; done
run r4_nc_cert_11121new  $R python3 -I nc_cert.py 11121 new
# ---- round 5
for f in "2211BB 15 30 2" "2211BD 16 40 2" "21111ACC 16 30 2" "21111ACD 16 30 2" "21111aa 15 30 2" "21111aa_x0 15 30 2" "21111iso 15 30 2" "21111ab 16 40 2" "21111II 16 30 2"; do
  set -- $f; run r5_gen_rank_$1 $G python3 -I gen_rank.py $f
done
run r5_p2211_rank_1      $G python3 -I p2211_rank.py 1
run r5_p2211_rank_0      $G python3 -I p2211_rank.py 0
run r5_p2211_pts         $R python3 -I p2211_pts.py bd
run r5_p21111aa_rank_1   $G python3 -I p21111aa_rank.py 1
run r5_p21111x0          $R python3 -I p21111x0.py
run r5_p21111iso_rank    $G python3 -I p21111iso_rank.py 1
run r5_p21111_pts_aa     $R python3 -I p21111_pts.py
run r5_p21111_pts_iso    $R python3 -I p21111_pts.py iso
run r5_p21111_pts_II     $R python3 -I p21111_pts.py II
run r5_nc_cert_1111pt    $R python3 -I nc_cert.py 1111pt
# ---- round 6
run r6_blockfam          $G python3 -I blockfam.py
run r6_block_exact       $R python3 -I block_exact.py 1 1
run r6_pblock_rank_all   $G python3 -I pblock_rank_all.py 1
run r6_pblock_rank_iso   $G python3 -I pblock_rank.py 1
run r6_gen_rank_blockall $G python3 -I gen_rank.py blockall 15 30 2
run r6_gen_rank_blockiso $G python3 -I gen_rank.py blockiso 15 30 2
run r6_block_iso_a0      $R python3 -I block_iso_a0.py
run r6_rankone_exact     $R python3 -I rankone_exact.py
run r6_blockfam2         $G python3 -I blockfam2.py
run r6_dblock_exact      $R python3 -I dblock_exact.py 1 1
run r6_pdblock_rank      $G python3 -I pdblock_rank.py 1
run r6_gen_rank_dblock   $G python3 -I gen_rank.py dblock 15 40 4
run r6_gen_rank_dblock_b0 $G python3 -I gen_rank.py dblock_b0 15 30 2
run r6_second_gen_BB     $R python3 -I second_gen.py BB
run r6_second_gen_BBpts  $R python3 -I second_gen.py BBpts
# ---- round 7
run r7_p2211def_1_1      $G python3 -I p2211def_rank.py 1 1
run r7_p2211def_1_2      $G python3 -I p2211def_rank.py 1 2
run r7_p2211def_0_1      $G python3 -I p2211def_rank.py 0 1
run r7_p2211def_0_2      $G python3 -I p2211def_rank.py 0 2
for f in BBdef1 BBdef2 BBdef1x BBdef2x; do run r7_gen_rank_$f $G python3 -I gen_rank.py $f 15 30 2; done
run r7_bbdef_pts         $R python3 -I bbdef_pts.py
run r7_gen_bb_om_1       $G python3 -I gen_bb_om.py 1
run r7_gen_bb_om_0       $G python3 -I gen_bb_om.py 0
# ---- round 8
for spec in "22_2 row,0,1 0 row,1" "211iii row,0,2 0 row,1" "2121V0 col,4,3 3 col,3" "11121A1 col,4,3 3 col,3" "213def none 4 col,4"; do
  set -- $spec; run r8_omega_e0_$1 $G python3 -I omega_e0.py $spec 4
done
run r8_res_2121V0_s-1    $G python3 -I gen_rank_defo.py 2121V0 col 4 3 16 30 2 "s+1"
run r8_res_211iii        $G python3 -I gen_rank_defo.py 211iii row 0 2 16 30 2 "m4^2-3*m4+3;m3+m4-3"
run r8_res_213defu3      $G python3 -I gen_rank.py 213defu3 16 30 2
run r8_curve22_00        $G python3 -I gen_rank_defo.py 22_2_00 row 0 1 15 30 2
run r8_curve22_11        $G python3 -I gen_rank_defo.py 22_2_11 row 0 1 15 30 2
run r8_line22_01         $G python3 -I gen_rank_defo.py 22_2_01 row 0 1 16 30 2
run r8_def22_curve       $R python3 -I def22_curve.py
run r8_omega_321a        $G python3 -I gen_rank_defo.py 321a col 4 3 16 30 2 fix=p:omega
run r8_omega_2121Vnii    $G python3 -I gen_rank_defo.py 2121Vnii col 4 3 16 30 2 fix=p:omega
run r8_omega_11121B1     $G python3 -I gen_rank_defo.py 11121B1 col 4 3 16 30 2 fix=p:omega
run r8_omega_Vnii_s0     $G python3 -I gen_rank_defo.py 2121Vnii col 4 3 16 30 2 fix=p:omega,s:0
run r8_omega_Vnii_s-1    $G python3 -I gen_rank_defo.py 2121Vnii col 4 3 16 30 2 fix=p:omega,s:-1
run r8_conic_22_row10    $G python3 -I gen_rank_defo.py 22_2 row 1 0 16 30 2 "3*m3^2-2*m3*m4+3*m4^2-2*m3-2*m4+3"
run r8_conic_BD_row10    $G python3 -I gen_rank_defo.py 2211BD row 1 0 16 30 2 "v1^2+v1*v2+v2^2+v1+v2+1"
# ---- round 9
run r9_lift_sigma2       $G python3 -I lift_gram.py 211ii col,0,2 b2:0,c2:0 0 2 row,0 3
run r9_minors_sigma2     $G python3 -I gen_rank_defo.py 211ii col 0 2 15 30 2 fix=b2:0,c2:0 "2*b3*c3+b3+c3+2"
run r9_point_sigma2      $G python3 -I certify_defo.py 211ii col 0 2 b2:0,c2:0,b3:1,c3:-1 1/3
run r9_lift_sigma3_c2    $G python3 -I lift_gram.py 211ii_c2 col,0,3 b3:0,c3:0 0 3 row,0 3
run r9_minors_sigma3_c2  $G python3 -I gen_rank_defo.py 211ii_c2 col 0 3 15 30 2 fix=b3:0,c3:0 "b2*c1+2*b2+2*c1+1"
run r9_d_col_minors      $G python3 -I gen_rank_defo.py 211d col 0 2 15 30 2 fix=b2:0,b3:omega
run r9_d_col_lift        $G python3 -I lift_gram.py 211d col,0,2 b2:0 0 2 row,0 2
run r9_d_row1            $G python3 -I gen_rank_defo.py 211d row 0 1 16 30 2 fix=b2:-1 "b3^2+1"
run r9_d_row2            $G python3 -I gen_rank_defo.py 211d row 0 2 16 30 2 fix=b2:-1 "b3^2+1"
for spec in "22_2_11 row 0 1 defo2=col,0,1" "22_2_11 row 0 2 defo2=col,0,1" "22_2_00 row 0 1 defo2=col,0,2" "22_2_00 row 0 2 defo2=col,0,2"; do
  set -- $spec; run r9_double_$1_$3_$4 $G python3 -I gen_rank_defo.py $1 $2 $3 $4 15 30 2 $5
done
echo ALLDONE >> $L/_index.txt
