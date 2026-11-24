## ROUND 11 RESULT (current, ~03:15 UTC) -- R31 chain complete as Lean text for one configuration; R31Hyp reduced to R31CfgAll
- Target 1 (window 3): no logs yet (R9d / R12s_combo expected 03:30-05:00). Window-4 rule unchanged: R9f if R9d and the
  r6_9b part of R12s_combo pass, else R8c. R12s_combo (copied at its turn) now holds all round-10/11 blocks (16172 lines).
- Target 2 (R31 setup etc., all untested, all in R12s_combo before t3_trans):
  r11_3 typeII_weights, jsq_sign; r11_4 pairDual, ann2_dep; r11_5 dual_eq_pairDual, e3_final, e3_a, e3_b ((E3) from
  ann23_exists); r11_6 stest_vanish_gen + blk_finrank_rel / blockSpace_finrank_rel / ell_ne_gen (generalised (E2) for
  d = 5); r11_7 r31_setup (R31Canon data + X_123 = 0 -> kappa3, f13, c2, c3, j, s, M2, M3 with weights, indicator
  relations, (E1) via t2_split, n** relation, both (E3) facts); r11_8 canon_patterns; r11_9 f13_cases_* (66 allowed
  patterns per sign = verify2's 132); r11_10 R31CfgAll and r31_of_cfgall : R31CfgAll -> R31Hyp.
- Target 3 (DFS generator): leanzbf/gen_cfg.py; ONE configuration end to end in r11_2 (01222/22001/eps -1): 3 E-lemmas,
  3 wrappers (r11_1 bridge = stest_vanish + lifting + weights), DFS cfg lemma, inst lemma (setup outputs -> cfg).
  Generator handles 3-, 1- and 0-factor d = 4 triples; gen_all.py over the 120 killed configurations: first 24 all
  generated except the 3 that need d = 5 triples (exactly the 3 found by r3_minS2).
- d = 5: needed only for 3 configurations (part 2, s12 00012, eps +1); generic core r11_6 written, bridge5 / dot5 still to do.
- Remaining for R31Hyp: R31CfgAll = case split (canon_patterns x f13_cases x s) closed by inst lemmas for the 120 killed
  configurations (+ 3 with d = 5) and (E5) for the 12 survivors (stest_affine with family parameters).
- SIZE: ~45-57 KB per configuration as generated (1.2 MB for the first 21); R31 by this route is several MB unless
  compressed (context bundling, identity-position bases, shared literals: maybe 3-4x), i.e. well above 512 KiB.

## ROUND 10 RESULT (current, ~02:30 UTC) -- R31: transport + canonical form + E-lemma machinery; GEN pieces; window-3 file extended
- Target 1 (window 3): no logs yet at writing time. Window-4 rule: R9f if R9d and the r6_9b part of R12s_combo pass (compact
  t3_trans), otherwise R8c (verified r6_9 + slim r6_7g). Expected full compile 45-65 min, ask for 90 min, peak 7-9 GB.
- Target 2 (R31), all inserted into R12s_combo.lean before t3_trans (window-3 file 2, 14685 lines; guard of new blocks OK):
  r10_1 colPerm transport (dotL_comp, typeCl_perm, PIIBody + piiBody_perm, pairII_perm, pairI_perm, vecPerm, zf_perm,
  exists_sort_perm via Tuple.sort). r10_3 canonical choice: R31Canon (= R31Hyp for data whose class function f (1 = Q-class,
  2 = B-class, 0 = mixed) is MONOTONE, i.e. verify2's sorted s12), cls_exists, r31_of_canon : R31Canon -> R31Hyp.
  eps_2 needs NO conjugation: per-configuration lemmas take an abstract j with j*j = -1 (Q(i) data, i -> j, identities by
  linear_combination P * hj), exactly as in the T1 lemmas. E-lemmas (per configuration and column triple S, d = dim K_S = 4):
  from 'perm(T(x)) = 0 on ker z' (z = n**|K_S in the K_S basis) to 'z = 0' or 'z proportional to a factor' (2x2 minors = the
  linear DFS cut). Generic cores: r10_4 cub3_cases (+ three_factor_gen, lin_minor), r10_8 cub1_cases (+ qsec_one,
  qsec_no_kernel), r10_6 cub0_zero (+ sum3_idx, cubic_no_plane_idx, sec_no_kernel). Generators gen_e3.py (r10_5: 3 samples
  in R12s_combo), gen_e0.py, gen_e1.py; exact data leanzbf/r3_export_p*.txt. Volume: r3_minS.py (greedy S removal with
  identical DFS outcome) keeps about 1/3 of the 1169 cubics and very few 0-factor ones (parts 0-3: 47/138, 96/240, 96/231,
  51/153; 0-factor kept 7, 11, 1, 6). d = 5 (31 cubics, all 1-factor) is needed (DFS without them: 7 survivors instead of 4 in
  part 2) and needs a generalised stest_vanish (designed, handover). Remaining R31 steps: handover section 0000000.
- Target 3 (GEN, nothing new from stage2): r10_2 (SR) no_single_row / gen_no_single_row from zero-free column annihilators
  (fk_col, gen_col_ann); gen_tri_param = stage2 (GEN-tri) / section 7: for a triangular pair with row-zero witnesses
  x3, x4, x5 in X_12 (dim 2), every x in X_12 has kappa'^j_i x_ij = c_i zeta_j (i = 3,4,5), c3 + c4 + c5 = 0, zeta_j =
  kappa'^j_4 x3_4j (with dep3_of_finrank2, col3).

## ROUND 9 RESULT (current, 01:35 UTC) -- dispatch-level generic lemma (full file 2.01 -> 1.57 MB), R3-1 steps 1-2, GEN scope
- Target 2: r9_1.txt (status3, ratio_eq, stest_glob = stest_gen in global coordinates) + leanzbf/gen_t3d2.py -> r6_9b.txt (t3_trans,
  same statement: 9-way rcases per point, one-line F_m, compact certificates, passing leaves call stest_glob with the pattern data,
  so the 98 t3p_* lemmas disappear). r6_9b 669 KB replaces r6_9 611 KB + r6_7g 412 KB. lemB prunes 'simp [facts] at hD'
  (r7_1 286 -> 198 KB). New full candidate R9f.lean (26385 lines, 1.57 MB, no sorry, guard plain+namespace OK).
- Target 3: r9_2 ann23_exists (the fifth annihilator n** of the lambda = 3 pair (2,3), outside span(f2-f3, g*)), r9_3 tauMap +
  stest_vanish (the (E2) core: perm vanishes on the whole tau-subspace H once dim H <= 3 contains the image of blkL(S)).
  Open design point for the DFS: verify2 works with CANONICAL configurations (column permutations); Lean needs a column-permutation
  WLOG. First part written: r9_4 colPerm, pm_colPerm, lev_colPerm, finrank_colPerm, rowsZeroS_colPerm; still needed: ZF / PairII /
  TypeCl transport and the choice of the canonical permutation; then generated per-(configuration, S) lemmas from verify2's data.
- Target 4: scope written (STATUS block 'TARGET 4 SCOPE'): ~3400 lines, five statements for stage2 to re-derive exactly.
- Target 1: full-compile estimate for R9f: R3e ~2.5 min + r4..r6_6 incl. repaired t1_IIi ~12-15 min + r6_9b ~20-30 min + lemB 3-10
  min + rest ~5 min = 45-65 min (ask for a 90 min timeout); peak memory probably 7-9 GB (R6t_stub peaked at 6.8 GB).
- Window 3 list: R9d.lean, R12s_combo.lean (stest_gen, t1p slim, R31 lemmas r8_2..r8_4, r9_2..r9_4, stest_glob, compact t3_trans).

## ROUND 8 RESULT (current, 01:22 UTC) -- generic S-test core lemma (R7c 2.47 -> 2.01 MB as R8c); R31Hyp certificate analysis
- Target 2: r8_1.txt stest_gen = ONE generic homogeneous S-test core lemma (data A, M, pi, pj, lambda certificates Lr/La with the
  identity hid checked at the call site by simp only + ring, weights W, point x0; row sums, lift via stest_lift3 and the kappa scaling
  of the permanent proved once). leanzbf/gen_slim.py: all 10 t1p_* and 98 t3p_* lemmas regenerated as slim instances with UNCHANGED
  names/signatures (r6_1g 42 KB vs 85 KB, r6_7g 412 KB vs 833 KB; data self-checked numerically, gen_slim_chk.py). Full candidate
  R8c.lean (30467 lines, 2.01 MB, no sorry, guard plain+namespace OK). Remaining size: r6_9 611 KB, r6_7g 412 KB, R3e 291 KB,
  r7_1 286 KB, r6_4 132 KB.
- Target 3 (R31Hyp): (E2) makes the elimination over n** finite (n**|K_S proportional to a linear factor of the n**-free cubic
  c_S, or 0), = verify2's r3_exact DFS. Experiment (leanzbf/r3_variant.py): with only 3-factor certificates 77 of 132 configurations
  survive the DFS, with 3- and 1-factor certificates 39, with all certificates 12 -> the 0-factor (smooth plane section) certificates
  are essential. Lean route: the three completeness lemmas are WRITTEN (untested): three_factor_plane (r8_2), cubic_no_plane (r8_3:
  Jacobian certificate x_k^4 = sum A_ki d_i g; binary quadratic normal derivative has a zero over C), quad_no_plane (r8_4: inverse
  certificate x = N grad q(x)); still to do: the R3-1 setup (I_3^perp = span(A0) + C n**, n** from the 3-dim annihilator space of the
  lambda = 3 pair (2,3)), (E2) via stest_blk (perm3 vanishes on K_S cap ker(n**|K_S) when the six local relations have rank 6), the
  generated DFS per configuration, and (E5) = stest_affine with symbolic parameters.
- Window 3 (list: R9d.lean, R10s_slim.lean incl. r8_2..r8_4) not yet run.

## ROUND 7 RESULT (current, 00:55 UTC) -- T1 COMPLETE as Lean text (T1Hyp proved); window 2: r6_9 VERIFIED, rest of r4..r6 VERIFIED except t1_IIi (repaired)
New blocks lean/zbf/ (not yet compiled; window-3 file R9d.lean tests all of them):
 r7_1 (leanzbf/gen_lemB.py) lemB: purely combinatorial on the six class Finsets; from the two transversal hypotheses of T3Rest2 and the
   class witnesses: every column has one of the four types of orientation 1 {(C,C,C),(C,Q,Q),(Q,C,B),(B,B,C)} or every column one of
   orientation 2 {(C,C,C),(C,B,B),(Q,Q,C),(B,C,Q)} (defs Orient1/Orient2). 26 Hall cases, per-case B1 lists, witness refutations.
 r7_2 f1_alg, f1_alg2 (the cyclic F1 algebra for the two orientations; certificates checked numerically / with sympy, lcfind.py),
   sum_three_parts, sum_scale, sum_one_eq.
 r7_3 (gen_bridge.py) orient1_noT0, orient2_noT0: orientation + no (C,C,C) column -> False (witness types give omega = j c',
   omega2 = j c''; class sums; typeII_J for the three pairs).
 r7_4 def T3F2 (orientation + a (C,C,C) column) + t3rest2_of_t3f2 + t1_of_t3f2.
 r7_5 (gen_aff.py) a3p_o1, a3p_o2: affine cube-test cores via stest_affine on S = (T1,T2,T3) resp. (T0,U2,U3) (pair-12 transversals;
   found by running stage2's own cube test on the lemB leaves: orientation 1 is killed entirely by S = (T1,T2,T3), orientation-2 F2 by
   S = (T0,U2,U3), orientation-2 F1 is the cyclic cube family -> f1_alg2).
 r7_6 s_transfer_aff, typeII_aff, typeII_ite_aff, ksum_half.  r7_7 (gen_aw.py) wrappers a3w_o1, a3w_o2, t3f2_proof : T3F2 and
   t1_proof : T1Hyp.
Full candidate R7c.lean (mk9.py): final theorem = old statement /\ T2Hyp /\ T2ppHyp /\ T1Hyp; 38051 lines, 2.47 MB, no sorry,
 guard plain + own-namespace OK (only the size cap fails).
WINDOW 2: R7s_t3.lean exit 0, 0 errors (921 s): generated t3_trans (305 leaves) + T3Rest/T3Rest2 VERIFIED.
 R6t_stub.lean COMPILED except the generated dispatch t1_IIi (4 errors, all heartbeat timeouts at 1e7): r4_* (T2, T2''),
 r5_*, r6_0, the 10 generated t1p_* core lemmas, r6_2 swap lemmas, r6_3, generated wrappers, r6_5, r6_6 (typeII_J, stest_affine) and 3
 sample generated t3p_* lemmas all elaborated without error. Repairs: tauto -> iffA..iffE (r6_3) in gen_t1d.py + 4e7 heartbeats;
 'simp [..] at e' contradictions -> 'exact absurd e (mul_ne_zero ..)' (gen_t1d.py, gen_t3d.py); heartbeat limits for lemB, bridges,
 wrappers (gen_t3d.py later reverted to the verified text; gen_t1d.py keeps the simp forms of the verified leaves).
 Window-3 list: R9d.lean (r6_3, r6_4 with repaired t1_IIi, r6_6, ALL r7 blocks full; verified r6_5/r6_9 stubbed) and R9c.lean (all 98
 generated t3p_* core lemmas). Still never compiled: r7_* (all new), t1_IIi after repair, 95 of the 98 t3p_* lemmas.

## ROUND 6 RESULT (current, 23:50 UTC) -- (II,II,I) proof written in full (generated); T1 reduced to (II,II,II) and then (draft) to F1 + F2
Nothing of this round is compiled yet (window 2 compiles R6t_stub.lean, then R7s_t3.lean). New blocks in lean/zbf/:
 r6_0 stest_lift3' + jsq_ne. r6_1 = 10 GENERATED core pattern lemmas t1p_* (leanzbf/gen_t1p.py): one per consistent local pattern of
   rule R; exact M, point x0, permanent certificate P(j) = A + Bj + Cj^2 reduced with j^2 = -1 to a^2 + b^2 != 0.
 r6_2 typeCl_swap, pairI_swap, pairII_swap: the pair type does not depend on the order of the two rows.
 r6_3 corner_of_not, c23_side, side_cancel, typeII_ite, s_transfer (generic move from global data to the rr/cc S-test frame).
 r6_4 = GENERATED wrappers t1pw_* (now via s_transfer) + dispatch t1_IIi (leanzbf/gen_t1d.py): (II,II,I) is impossible; 81 leaves,
   10 call a wrapper, 71 die by a ratio contradiction (j = +-1, c'^2 = 0, 2cc' = 0, 2 omega c = 0, j = eps).
 r6_5 T1Rest3 + t1rest2_of_rest3 + t1_of_rest3 : T1Rest3 -> T1Hyp. (I,II,II) and (II,I,II) by relabelling (pairII_swap, set3_rot):
   T1 now needs ONLY the all-Type-II triples.
 r6_6 c7_split, typeII_J (Type II L^-constant: (K_B + K'_Q2)(omega + c) = c, i.e. the stage2 normal form y = (-1 + eps i)/2; needed
   for the cube test and T1'), unit_split (omega = +-j c'), stest_affine (the cube test as a lemma, via R3e's zbf_ufd; for F2).
 r6_7 = GENERATED (II,II,II) core lemmas t3p_* (leanzbf/gen_t3p.py): 98 lemmas (one per passing pattern and corner sign; all used
   by t3_trans), 833 KB -- NOT in R6a/stub except the 3
   samples r6_7s.txt (template test). Passing patterns = exactly the 98 numerically passing ones; the 14 failing = exact skips.
 r6_9 = GENERATED (II,II,II) dispatch t3_trans (leanzbf/gen_t3d.py, 305 leaves, exact certificates) + def T3Rest + t1_of_t3rest :
   T3Rest -> T1Hyp (T3Rest = all-Type-II triples where EVERY pair-12 transversal has one of the 26 non-passing patterns)
   + def T3Rest2 + t1_of_t3rest2 : T3Rest2 -> T1Hyp, where T3Rest2 also uses the row order (r1, r3, r2): its configurations are
   EXACTLY F1 + F2 (exact pattern count, t1_iii8.py). 8079 lines, needs all of r6_7; not in R6a or R6t_stub; tested in window 2 by
   R7s_t3.lean (all else stubbed); R7t_stub.lean = R6t_stub + r6_7 statements + r6_9 (window-3 candidate).
 (II,II,II) dispatch data (leanzbf/t1_iii3..7.py, exact patterns): 52560 label configurations (up to eps), 780 = F1 + F2 need T1'
   resp. the cube test; of the 51780 others 34980 pass on every pair-12 transversal, 15720 after a one-point replacement, 600 after a
   two-point replacement, 480 only after a row reorder (all rescued by the order (r1, r3, r2), t1_iii8.py). On F only 4 patterns
   occur (t1_iii9.py). Next: Lemma B (class structure of F1/F2), F1 via typeII_J + t1p_alg, F2 via stest_affine.
Files: R6t_stub.lean (9004 lines, 500 KB, guard clean; window-2 file 1), R7s_t3.lean (13074 lines; window-2 file 2), R6a.lean =
 R3e + rounds 4-6 without r6_7/r6_9 (12328 lines, 655 KB; final theorem: old statement /\ T2Hyp /\ T2ppHyp /\ (T1Rest3 -> T1Hyp)), R6b.lean = everything (33443 lines,
 2.10 MB; final conjunct (T3Rest2 -> T1Hyp)), R7t_stub.lean = window-3 candidate (1.21 MB). All guard clean except the size cap.
 Pre-compile fix: subst e1/e2/e3 -> subst κ' / κ2' / κ3'.

## ROUND 5 RESULT (current, 22:48 UTC) -- T1 reduced to configurations with >= 2 Type II pairs (Lean text, not yet compiled)
New blocks lean/zbf/r5_1..r5_7: stest_lift3 (generic K_S lift lemma), t1_iii_local + t1_III (T1 for three Type I pairs, uniform
column triple), t1_one_II (exactly one Type II pair impossible), T1Rest2 + t1_of_rest2 : T1Rest2 -> T1Hyp, corner_unique, rule_R.
Files: R5a.lean (R4c + r5_1..r5_6, 8447 lines, guard OK; final theorem also carries (T1Rest2 -> T1Hyp)), R5t_stub.lean (stub of all
new blocks r4_1..r4_7, r5_1..r5_7), FrameR5.lean (481 KB, guard OK). Window-2 list: R5t_stub.lean, R4c.lean.
Screen [numerical + exact data]: (II,II,I)-type configurations all die by the simple S-test with an explicit rule (20 exact local
patterns, leanzbf/t1_gen_data.log) -> generator next; (II,II,II): 1560 raw configurations need the cube test / T1'.

## ROUND 4 RESULT (current, 22:22 UTC) -- T2 and T2'' formalized; window-1 compile: 6 local errors, repaired, awaiting window 2
Files (lean/zbf/): r4_1..r4_6 (new blocks), R4c.lean = R3e + r4_1..r4_6 (7827 lines, 381 KB, project guard OK; final placeholder
theorem PEqualNP.Outside.L_gct_210 : round-3 statement AND T2Hyp AND T2ppHyp), R4t_stub.lean (old proofs sorry'd + r4_1..r4_7),
FrameR4.lean (guard-compliant Frame210 kit + R4c ZBF + bridge, 448 KB, guard OK). Last fully compiling file: R3e.lean (round 3).
Window 1 (22:19, 15 s per file, 7.7 GB): R4c 6 errors, stub 7 (the 7th in gen_lin) -- ALL in supporting lemmas, none in the main
proofs: (1) t2_partition: sign in a linear_combination; (2) blkL needed `noncomputable`; (3)-(6) `rintro x ⟨h1, h2⟩` on a ⊓-membership
gives h2 : x ∈ ↑(ker f) (set coercion), so `rw [LinearMap.mem_ker] at h2` fails (ell_ne_of_small, t2_stest, span_classes,
t2pp_stest; gen_lin) -- replaced by `replace h2 := LinearMap.mem_ker.mp h2`. t2_proof, t2pp_proof, typeI_nf, typeII_nf,
gen_vec_core, gen_vec_A, t2_gen_vec, t2_alg, t2pp_alg, hyper_core, hyper_top, loc_rel, GEN-0 (gen0_typeI) etc. elaborated with
NO error. Still unchecked: the remainders of the four blocks behind errors (3)-(6) (reviewed by hand). Window 2 list written.
 status of the S2 chain after window 2 (if green): T2Hyp, T2ppHyp are THEOREMS (t2_proof, t2pp_proof); S2 / S2* need only
 T1Hyp and R31Hyp (s2_noT2, s2_star_noT2).

# NOTES-leanzbf (role: leanzbf; start 16:38, budget 2 h -> ends ~18:38)
## ROUND 2 RESULT (final, 19:42) -- file lean/zbf/Zbf11.lean (5227 lines, 256 KB) = Zbf.lean (round 1) + round-2 sections
leancheck: lean exit code 0; axioms [propext, Classical.choice, Quot.sound]; format quotes/hash/import/banned/comments all 0.
Checker sanity test (19:32): the same file with one deliberately false lemma appended gives exactly ONE error (that lemma) and
exit code 1 (lean/zbf/sanity.log) -- so "exit 0" really means every declaration of the file was checked.
Snapshots of every compiling state: Zbf2_v1..v5_ok, Zbf3_v1..v3_ok, Zbf4_v1_ok, ..., Zbf11_v1_ok (.lean, same folder; Zbf11 = current).
Combined file with the Frame210 kit: lean/zbf/FrameZbf2.lean (6604 lines, 323 KB; log frame2.log): COMPILES (exit 0, axioms ok,
format 0) = Frame210 kit (MethodCeiling, Helpers.Minc, Helpers.RankOne, Kit086, F210) + the whole ZBF210 namespace of Zbf11 +
bridge ZBF210.lev_iff_F210 + the final theorem. (The round-1 files Zbf.lean / FrameZbf.lean are unchanged.)
No sorry, no axiom, NO REMAINING EXPLICIT-HYPOTHESIS HOLE in targets (1)-(4). EVERYTHING BELOW IS COMPILED unless marked NOT DONE.
 target                         | status   | Lean name(s)                         | remarks
 (1) Theorem N3'                | COMPILED | n3prime                              | unconditional. b 3x3, pm b != 0, pm (b + eta) = pm b on V0 => finrank V0 <= 3.
     Corollary N3'-L            | COMPILED | n3prime_L_full                       | unconditional (any n, any 3x3 block with ell(u0) = 1).
     (also the whole chain R0 -> ZBF -> ThB -> Lemma C at an ARBITRARY base point b: BLev, lemmaC_genB, lemmaC_col_genB, ...)
 (2) C4                         | COMPILED | c4                                   | unconditional; valid for every dim L (pair minimal for Lemma C,
                                |          |                                      | a_r = a_r' = 1); NEW PROOF, shorter than the paper's (STATUS 19:00).
 (3) C7 / C7''                  | COMPILED | c7_final   (statement about L only)  | Lev 5 L, r != r', finrank L = finrank X_{rr'} + 7, row ranks >= 4  ==>
     Type I / Type II           |          | c7_rows_ind, c7_rows_full, c7_rows   | EXISTS annihilator data kappa, kappa', nu, nu' (the two relations of I^)
                                |          | (for ANY annihilator data)           | such that, IF kappa and kappa' have no zero entry, the points
                                |          | c7_types, c7_sep (combinatorics)     | (rho_m, rho'_m) = (nu_m/kappa_m, nu'_m/kappa'_m) are of Type I or II:
                                |          | c7_tau, c7_pair_x, c7_pair_thB       | exists a, b separated in both coordinates with sigma_a = sigma_b, and every
                                |          | c7_lift, c7_hI, second_relation,     | column m sits at P_a (omega_m = omega_a), at P_b (omega_m = -omega_a) or
                                |          | fk_annihilator, dot_zero_of_row      | at the corner (rho_a, rho'_b) with sigma_a != 0, omega_m^2 = -omega_a^2,
                                |          |                                      | sigma_corner^2 = -sigma_a^2, omega_a sigma_a + omega_m sigma_corner = 0.
                                |          |                                      | (Type I = no column at the corner; Type II = some column at the corner.)
 (4) (P), (G1), (G2)            | COMPILED | rows_submodular, cells_submodular,   | (P): submodularity + rank formulas; (G1): rows_disjoint_bound,
                                |          | rows_rank, cells_rank, rows_inj_bound,| rows_inj_bound; (G2): stage3_G2 (with rows relabelled by rho).
                                |          | rows_disjoint_bound, dS_*, stage3_G2 |
 (5) Theorem G                  | PARTLY   | pm_mask_sum, pm_mask_zero,           | COMPILED: the generalised Laplace identity (sum over row sets A of
                                |          | pm_mask_factor, thG_term, thG_masked | size m and column sets of products of complementary minors of two
                                |          | perp_bound, rank_one_bound           | elements of L^ = n! C(n,m) c1^(n-m) c2^m), and the linear-algebra
                                |          |                                      | core of the inequality (A, B in C^N with dot pairing a.b = f(a) g(b)
                                |          |                                      | on A x B  =>  dim A + dim B <= N + 1). NOT DONE: assembling these
                                |          |                                      | into rho_k + rho_(5-k) <= C(5,k)^2 + 1 (index bookkeeping over
                                |          |                                      | pairs (A,T)) and dim K_2 >= 5.
NOT DONE inside (3) (none of it is needed for the classification statement): (i) condition (c) of C7' (sigma != 0 for two columns
 at the same point), hence "sigma_0 != 0" in Type I; (ii) the normalisations c = 1/(K_1 - K_2), sigma_0 = -K_2 (1 + c) and the final
 tau-relations on L of NOTES-stage2 section 3 (they follow from sum kappa = sum kappa' = 1 and sum nu + sum nu' = 0, all available
 as conjuncts of c7_final); (iii) the case of zero entries in kappa / kappa' (excluded by hypothesis, as in the paper's C7'').
NO PAPER STEP FAILED in round 2. Remarks for the authors of the paper proofs:
 - C7'': the Lean proof uses exactly the corrected form of (d) (pair separated by both rho and rho' => omega_j + omega_l = 0 AND
   sigma_j = sigma_l); the classification needs only (a), (b), (d) and omega != 0; condition (c) and "at most 2 points per
   anti-diagonal" are not needed as separate steps (the three-point case is excluded directly by 2 omega_a = 0).
 - C7'' does NOT need a_r = a_r' = 1 beyond: both row ranks >= 4 (used only to show rho, rho' non-constant) -- c7_rows_full shows the
   classification for ANY two independent relations with rho, rho' non-constant on a minimal pair.
 - C4 and N3': Lean proofs differ from the paper proofs (see STATUS 18:45, 19:00); the paper statements are confirmed.

## ROUND 2 API guide (additions; namespace PEqualNP.Gct.ZBF210)
 BLev b kappa L                  : kappa != 0 and pm (c b + t) = kappa c^n for all c, t in L   (level space at base point b)
 blev_of_lev, blev_of_const      : Lev n L -> BLev J n! L;   (pm b != 0, pm (b + eta) = pm b on V0) -> BLev b (pm b) V0
 lemmaC_genB hL r1 r2 hr         : BLev b kappa L (n = m+2) -> finrank L <= finrank (rowsZero L r1 r2) + (2m+1);  lemmaC_col_genB (columns)
 n3prime b V0 hb h               : finrank V0 <= 3            n3prime_weak : <= 4 (short proof, Lemma C only)
 n3prime_L_full hL r c u0 hu0 h0 : r c : alpha + Fin 3 = Fin n, u0 in blockSpace L r c with ell(u0) = 1 ->
                                   finrank (blockSpace L r c cap ker ell) <= 3 + finrank (colsOff L c)
 rowsZeroS L S, cellsZero L K    : L cap {rows in S = 0}, L cap {cells in K = 0} (Finset S, Finset K); mem_rowsZeroS, mem_cellsZero
 rows_submodular L S S'          : dim X_S + dim X_S' <= dim X_{S cap S'} + dim X_{S cup S'};   cells_submodular likewise
 rows_rank L S r                 : dim X_S = dim X_{S + r} + dim row_r(X_S);   cells_rank L K : dim L = dim cellsZero + dim (L.map (cellProj K))
 rows_disjoint_bound, rows_inj_bound : (G1)-type bounds when X_{S cup S'} = 0 / X_{S + c} = 0
 dS L rho S := finrank (rowsZeroS L (S.map rho));  dS_submodular, dS_inj_bound, dS_disjoint_bound, stage3_G2 (statement of (G2))
 blev_line, blev_mix, blev_rows  : mixed-coefficient identities at base point b
 maskAT A T u, thG_masked, thG_term : Theorem G identity (masked matrices; thG_term identifies a term with a product of two blk's)
 Bx r p x j q                    : 3x3 subpermanent of x on rows != r, r.succAbove p and columns != j, j.succAbove q
 thA5 hL r p x hx c t ht         : ThA for n = 5:  sum_j sum_q (c + t(r,j)) (c + t(r',j.succAbove q)) Bx r p x j q = 0   (x in X_{rr'})
 row_onto hL e hrank v           : finrank row_e(L) >= m+1 (n = m+2) -> every v in C^n is gamma 1 + row_e(t), t in L   (row_e(L^) = C^n)
 c4_left / c4_right              : t in L with row r' = 0 (resp. row r = 0): its row r (resp. r') is in the left (right) kernel of B_x
 c4_cols                         : B_x[j0,l0] != 0 and pair minimal -> L contains t with row r = any prescribed vector supported on {j0,l0}
 c4 hL r p hmin ha ha' x hx j0 q0: Bx r p x j0 q0 = 0      (hmin: finrank L = finrank (rowsZero L r r') + 7; ha, ha': row ranks = 4)
 dotL kappa z = sum_m z m * kappa m (linear in z); dotL_single, dotL_two, dotL_comb; dual_eq_dotL (every functional is a dotL)
 relM alpha beta z = dotL alpha z.1 - dotL beta z.2;  relP alpha beta z = dotL alpha z.1 + dotL beta z.2  (functionals on C^n x C^n)
 fk_annihilator hL r             : exists kappa, (forall t in L, dotL kappa (row_r t) = 0) and dotL kappa 1 = 1      (any level space)
 second_relation                 : minimal pair, f1 vanishing on I^ with f1 v1 != 0 -> exists g vanishing on I^ and on v1, g != 0
 c7_lift                         : minimal pair, f1, f2 vanishing on I^ and independent (f1 v1 != 0, f1 v2 = 0, f2 v2 != 0) ->
                                   every z with f1 z = f2 z = 0 is (c + row_r t, c + row_r' t), t in L   (I^ = ker f1 cap ker f2; dim count)
 c7_hI                           : the lifting localised to a column pair {j,l}, with ell = <kappa, z_1>, landing in pairSpace L r r' j l
 dot_zero_of_row                 : row rank >= 4 and mu annihilates row_e(L) and 1 -> mu = 0
 c7_pair_thB                     : ThB for the pair T = {j,l}: (ell = 0 on Pi_T) or (exists k, q_T = k ell^2 on Pi_T)
 c7_tau / c7_pair_x              : pair criterion (a), (b), (d) of C7' (tau-coordinates / original coordinates), by explicit test vectors
 c7_sep, c7_types rho rho' omega : plane combinatorics of C7'' for ANY index type
 c7_rows                         : classification given the lifting hypothesis hI;   c7_rows_full : given annihilator data (S1)-(S3),
                                   zero-free kappa, omega, and rho, rho' non-constant;   c7_rows_ind : same with (row ranks >= 4 and
                                   "(nu,nu') is not a multiple of (kappa,-kappa')") instead of non-constancy
 c7_final hL r r' hr hmin ha ha' : the statement about L only (existence of the data + classification when kappa, kappa' zero-free)
 dotD, perp_bound A B h          : A, B in C^N with sum_m b m * a m = 0 on A x B -> finrank A + finrank B <= N
 rank_one_bound A B f g h        : sum_m b m * a m = f a * g b on A x B (f linear) -> finrank A + finrank B <= N + 1   (core of ThG)
 Final placeholder theorem PEqualNP.Outside.L_gct_210_zbf (Zbf11.lean): R0 + Lemma C (rows, columns) + N3' + C4.

## RESULT (final, 17:40) -- ONE FILE, EVERYTHING BELOW IS COMPILED (no sketch, no hole, no failure)
File: /home/claude/work/L-gct-210/lean/zbf/Zbf.lean  (2015 lines, 97 KB; backups Zbf_v1..v9_ok.lean, v9 = current; log last.log)
leancheck: lean exit code 0; axioms [propext, Classical.choice, Quot.sound]; format quotes/hash/import/banned/comments all 0;
12 warnings (deprecated if_pos/if_neg, unused simp args). "statement verbatim: False" as expected (placeholder theorem).
Also: /home/claude/work/L-gct-210/lean/zbf/FrameZbf.lean = Frame210.lean (Kit + F210, its last theorem removed) + the whole
ZBF210 namespace + bridge ZBF210.lev_iff_F210 (Iff.rfl) + the same final theorem: compiles (exit 0, 164 KB, log frame.log), so the
P_k tools of Frame210 and the ZBF tools can be used together in one file (no name clashes).
Self-contained: imports Mathlib + PEqualNP.Defs only, does NOT need the Kit / Frame210 (R0 is proved by scaling + a polynomial
identity, so no P_k bridge is used). Namespace PEqualNP.Gct.ZBF210. Final placeholder theorem
  PEqualNP.Outside.L_gct_210_zbf : for L with the gap hypothesis:  (forall c, t in L: sum_f prod_i (c + t(i, f i)) = 120 c^5)
     AND (forall rows r1 != r2: finrank L <= finrank (rowsZero L r1 r2) + 7) AND (same for columns, colsZero).

| target | status | Lean names |
| 1. R0  perm(cJ + t) = n! c^n (any n), gap form 120 c^5; perm(u + s x) independent of s; FK | COMPILED | lev_scale, lev_scale_emb, lev_line, lev_line_const, lev_FK, lev_FK_row, lev_FK_block |
| 2. ZBF perm(u) = perm(u[S,Z^c]) perm(u[S^c,Z]) over a zero block (general index types; finset form; 1+k and 2+m instances) | COMPILED | perm_sum_block, perm_submatrix_equiv, perm_zero_block, perm_zero_block', pm_zero_block, pm_zero_block_sets, exists_block_equivs, pm_zero_of_big_block |
| 3. UFD replacement by a LINE lemma, both cases of chief's (ZBF) | COMPILED | poly_const_of_mul, line_const, ufd_unit_ne, ufd_unit, ufd_zero, zbf_prod, zbf_ufd, zbf_zero, zbf_lineality (GZ-a) |
| 4a. Theorem B: (B1) q_T = kappa ell^2, dim Pi <= 2, dim U_T <= 2 + dim L_{rr'}; trichotomy B1 / B2 / q0 | COMPILED | thB_quad, thB_ker, thB_img, thB_dim, thB_cases, thB_pair (equiv-free form for rows r1 != r2, columns c1 != c2) |
| 4b. Lemma C in verify2's GENERAL form, for every n = m+2: dim L <= dim(L cap {rows r,r' = 0}) + 2n-3; rows and columns; n = 5: + 7; dim 9 => >= 2 | COMPILED | lemmaC_gen, lemmaC_col_gen, lemmaC, lemmaC_col, lemmaC_nine |
| 4c. N3: every 3x3 level space has dim <= 3 (test of the tools; 230 lines instead of L094's 1650) | COMPILED | n3 (+ n3_alg, n3_row, n3_col, ...) |
| extra: Laplace expansion along one row / two rows (derived from ZBF + row linearity) | COMPILED | pm_row_expand, pm_laplace_row, pm_laplace_two |
| extra: CA2 by the DIRECT Laplace argument (coordinator note b), general and full form | COMPILED | ca2, ca2_full |
| extra: Theorem A (affine isotropy u_r^T B_x u_r' = 0) | COMPILED | thA |
| extra: SR (single-row lemma of stage3) | COMPILED | single_row_SR |
| extra: all mixed Taylor coefficients: coefficient of s^m of perm(u + s v), u, v in L^ (row-subset form of Theorem G's identity) | COMPILED | mix, pm_line_expand, lev_mix, lev_mix_hat |
| extra (17:40): C1 pigeonhole, row projections <= n-1, block witness lemma (generalises SR, gives stage3's D2), C2-type corollaries of ThB, column versions of CA2 / ThA, polarization in "rows A from x, the others from u" form | COMPILED | rows_pigeon, row_proj_le, zbf_witness, zbf_witness', q0_isotropic_bound, thB_img_or, thB_Bx, blk_tr, ca2_col, thA_col, mix_eq_sum_pm, lev_mix_pm, lev_rows |
NOT done (not attempted, so no information about their correctness): Theorem G in subpermanent-product form and the rho_k
inequality; C4/C7; N3'; column versions of SR / thB_pair / lev_rows (obtain by lev_tr + the row versions, as lemmaC_col_gen,
ca2_col, thA_col do); the converse of R0.

### Did any paper step fail to formalize?  NO.
R0, ZBF incl. the UFD step, ThB (B1 and the trichotomy), Lemma C (general 2n-3 form), ThA, CA2 (direct Laplace form), SR, GZ-a, N3
all went through; I found no wrong or incomplete step. Remarks on where the Lean proof differs from the paper:
 (i) UFD is not needed anywhere. Case ell != 0 on U: for u0 in U with ell = 1 and v in U cap ker ell, f_1(u0 + s v) f_2(u0 + s v) = n!
     for all s, so each factor is a constant polynomial in s (degree count in C[s]); homogeneity gives f_i = f_i(u0) ell^deg where
     ell != 0, and one more "polynomial vanishing off s = 0" argument gives it where ell = 0. Case ell = 0 on U: if f(a) != 0 and
     g(b) != 0, restrict f g = 0 to the line through a, b (C[s] is a domain). Both are a few lines (ufd_unit, ufd_zero).
 (ii) ThB: the kernel of U_T -> 2x2 block is identified WITHOUT FK: block zero => q = 0 = kappa ell^2 => ell = 0 (thB_ker).
 (iii) Lemma C: in "pick j with (n_r)_j != 0, l with (n_r')_l != 0 and T containing j, l" the case j = l needs a second column
     (any other one); handled by exists_col_perm. The annihilators n_r are avoided: with A = {t in L : row r' = 0}, the map
     (gamma, a) -> gamma 1 + a_r is onto C^n by a dimension count (row_surj), which gives the column j (exists_col).
 (iv) N3 is proved by a shorter route than chief's three cases: Lemma C (rows, columns) at n = 3 gives directly a nonzero
     single-row element in every row and a nonzero single-column element in every column as soon as dim L >= 4; then the
     relation x_rj y_rj = 0 (one explicit 3x3 identity, 9 cases generated by lean/zbf/py/gen_n3.py) and the pigeonhole.
 (v) P_1..P_5 = 0 are never used; lev_mix replaces them (coefficient of s^m of perm(u + s x) vanishes for m >= 1).

## API guide (namespace PEqualNP.Gct.ZBF210; `open Finset`)
Conventions: matrices are t : Fin n x Fin n -> C, entry t (i, j).
- pm u := (Matrix.of fun i j => u (i, j)).permanent;  pm_perm : pm u = sum_sigma prod_i u (i, sigma i);  pm_emb : = sum over
  embeddings f of prod_i u (i, f i) (the gap's form);  pm_tr : pm (fun p => u (p.2, p.1)) = pm u.
- blk rho kappa u := permanent of the block (fun i j : m => u (rho i, kappa j)), m any Fintype (rho, kappa : m -> Fin n need not be
  injective);  blk_smul, blk_unit (m = Unit: the entry), blk_two (m = Fin 2: q0 of blockProj), blk_zero_col, polyLine_blk.
- Lev n L := forall t in L, sum_{f : Fin n -> Fin n embedding} prod_i (1 + t (i, f i)) = n!   (same definition as F210.Lev);
  lev_five L hL : Lev 5 L from the gap hypothesis;  lev_tr : Lev n (L.map (trE n)) (transpose; trE_apply).
- L^ = CJ (+) L is modelled by PAIRS w = (c, t) : C x (Fin n x Fin n -> C), ell w = w.1, hat n w = fun p => w.1 + w.2 p (linear).
R0:   lev_scale hL c t ht : pm (fun p => c + t p) = n! * c ^ n          lev_scale_emb : the same as the embedding sum
      lev_line hL c s t x ht hx : pm (fun p => c + t p + s * x p) = n! * c ^ n     lev_line_const : = pm (fun p => c + t p)
      lev_FK hL c t ht (h : pm (fun p => c + t p) = 0) : c = 0       lev_FK_row (a zero row of cJ + t)   lev_FK_block (FK block)
ZBF:  r c : alpha (+) beta = Fin n (equivalences). ROWS r (inl a), COLUMNS c (inr b) carry the zero block:
      pm_zero_block u r c (h : forall a b, u (r (inl a), c (inr b)) = 0) :
          pm u = blk (r o inl) (c o inl) u * blk (r o inr) (c o inr) u
      (Matrix versions perm_zero_block', and perm_zero_block for the block rows r (inr b) x columns c (inl a).)
      pm_zero_block_sets u S Z eS eZ h : finset form, S x Z zero, eS : S = Z^c, eZ : S^c = Z any equivalences
      (exists_block_equivs S Z (S.card + Z.card = n) gives them). Ready-made equivalences:
        sa e : Fin k (+) Unit = Fin (k+1)   (inl b -> e.succAbove b, inr -> e;  sa_inl, sa_inr)
        e2m m : Fin 2 (+) Fin m = Fin (m+2) (inl 0 -> 0, inl 1 -> 1; e2m_inl0, e2m_inl1, e2m_inr); compose with a permutation
        from exists_perm2 r1 r2 (r1 != r2) : exists rho, rho 0 = r1 and rho 1 = r2  to reach any two rows / columns.
      blockSpace L r c : Submodule of pairs = {w | w.2 in L and forall a b, w.1 + w.2 (r (inl a), c (inr b)) = 0} (= U_{S,Z});
      mem_blockSpace (Iff.rfl);  blockSpace_finrank_ge : finrank L + 1 <= finrank (blockSpace L r c) + card alpha * card beta.
UFD:  zbf_prod hL r c w hw : blkA (hat n w) * blkB (hat n w) = n! * w.1 ^ n
      zbf_ufd hL r c u0 hu0 (h0 : u0.1 = 1) w hw : blkA (hat n w) = blkA (hat n u0) * w.1 ^ card alpha  and  the same for B
      zbf_zero (hn : n != 0) hL r c (hU : forall w in U, w.1 = 0) : (forall w in U, blkA (hat n w) = 0) or (forall w in U, blkB .. = 0)
      zbf_lineality : blkA, blkB are unchanged under w -> w + x, x in U with x.1 = 0 (GZ-a).
      Abstract versions for any module V, U : Submodule, ell linear, f g : V -> C with PolyLine f, PolyLine g (polynomial along
      every line): ufd_unit (f g = k ell^N on U, k != 0, f homogeneous of degree df, u0 in U, ell u0 = 1 => f = f(u0) ell^df on U),
      ufd_zero (f g = 0 on U => f = 0 on U or g = 0 on U), line_const, poly_const_of_mul (P Q = nonzero constant => P constant).
ThB:  for r c : Fin 2 (+) beta = Fin n (rows r (inl 0), r (inl 1); columns T = {c (inl 0), c (inl 1)}), u0 in U, u0.1 = 1:
      thB_quad : q0 (blockProj r c u0) != 0 and forall w in U, q0 (blockProj r c w) = q0 (blockProj r c u0) * w.1 ^ 2
      thB_img  : finrank (U.map (blockProj r c)) <= 2          thB_dim : finrank U <= 2 + finrank (rowsZero L (r (inl 0)) (r (inl 1)))
      thB_cases (no u0): (exists u0 in U, u0.1 = 1) or (ell = 0 on U and (q0 = 0 on the image or the complementary block perm = 0 on U))
      thB_pair hL r1 r2 c1 c2 (r1 != r2) (c1 != c2) u0 (hu0 : u0 in pairSpace L r1 r2 c1 c2) (u0.1 = 1) : the same three facts for
      pairSpace L r1 r2 c1 c2 = {w | w.2 in L and forall j != c1, c2: w.1 + w.2 (r1, j) = 0 and w.1 + w.2 (r2, j) = 0}  (n = m + 2).
LC:   rowsZero L r1 r2 := L inf ker (rowMap r1) inf ker (rowMap r2) (mem_rowsZero), colsZero likewise (mem_colsZero).
      lemmaC_gen (hL : Lev (m+2) L) r1 r2 (r1 != r2) : finrank L <= finrank (rowsZero L r1 r2) + (2 * m + 1)     [2n - 3]
      lemmaC_col_gen (columns);  lemmaC, lemmaC_col (n = 5, + 7);  lemmaC_nine (finrank L = 9 => both >= 2).
Laplace: pm_laplace_row u e : pm u = sum_j u (e, j) * blk e.succAbove j.succAbove u            (u : Fin (k+1) x Fin (k+1) -> C)
      pm_laplace_two u r p : pm u = sum_j sum_q u (r, j) * u (r.succAbove p, j.succAbove q) *
                                  blk (r.succAbove o p.succAbove) (j.succAbove o q.succAbove) u   (second row r' = r.succAbove p)
CA2:  ca2 (hk : k != 0) hL e xi (xi in L) (row e of xi zero) c t (t in L) : sum_j (c + t (e, j)) * blk e.succAbove j.succAbove xi = 0
      (G(xi) is orthogonal to the row-e projection of L^, any a_e);   ca2_full (hrank : m + 1 <= finrank (L.map (rowMap e))) :
      forall j, blk e.succAbove j.succAbove xi = 0   (all (n-1) x (n-1) subpermanents of xi vanish when a_e = 1).
ThA:  thA (hk : k != 0) hL r p x (x in L) (rows r and r.succAbove p of x zero) c t (t in L) :
      sum_j sum_q (c + t (r, j)) * (c + t (r.succAbove p, j.succAbove q)) * blk (..) (..) x = 0        (n = k + 2 >= 3)
SR:   single_row_SR hL a j x (x in L) (column j of x supported at row a) (x (a, j) != 0) c t (t in L)
      (forall b, c + t (a.succAbove b, j) = 0) : c = 0 and blk a.succAbove j.succAbove t = 0.
Mixed coefficients: mix m u x := sum_sigma sum_{A, |A| = m} (prod_{a in A} x (a, sigma a)) * prod_{a in A^c} u (a, sigma a);
      pm_line_expand : pm (u + s . x) = sum_{m <= n} s^m * mix m u x;   lev_mix (1 <= m <= n) : mix m (cJ + t) x = 0 for t, x in L;
      lev_mix_hat : mix m (c1 J + t1) (c2 J + t2) = n! * (C(n,m) * c1^(n-m) * c2^m)   (Theorem G's identity, row-subset form).
      mix_eq_sum_pm : mix m u x = sum_{A, |A| = m} pm (fun p => if p.1 in A then x p else u p)   (rows A from x, the others from u);
      lev_mix_pm : that sum is 0 for u = cJ + t, t, x in L, 1 <= m <= n;
      lev_rows hL R (R nonempty) x (x in L, x zero outside the rows R) c t : pm (fun p => if p.1 in R then x p else c + t p) = 0
      (perm[x_R; u_{R^c}] = 0: stage3's S12, first part; CA2 and ThA are the cases |R| = n-1, n-2 after Laplace).
Witness: zbf_witness (n != 0) hL r c x (x in U, x.1 = 0) (card beta != 0) (blkB (hat n x) != 0) : ell = 0 on U and blkA = 0 on U;
      zbf_witness' the same with the roles of the two blocks exchanged.  (SR: beta = Unit. D2: the 2x2 block q_T(x) != 0.)
More ThB: q0_isotropic_bound (q0 = 0 on P => finrank P <= 2); thB_img_or : dim Pi_T <= 2 or type B2;
      thB_Bx (card beta != 0) x in U, x.1 = 0 : complementary block perm of x is 0, or the block is of type q0.
Rows: row_proj_le : finrank (L.map (rowMap r)) <= m + 1 (n = m+2);  rows_pigeon : finrank L <= finrank (rowsZero L r1 r2) +
      finrank (L.map (rowMap r1)) + finrank (L.map (rowMap r2)).   Columns: blk_tr, ca2_col, thA_col (via lev_tr).
Linear algebra helpers: rank_nullity L f : finrank L = finrank (L inf ker f) + finrank (L.map f) (any finite-dim V);
      b_perp_bound (polar form of q0 on C^4), finrank_sup_one, one_not_mem_row, poly_zero_of_ne, poly_top, poly_coeff_zero, poly_coeff_eq.
Practical: leancheck takes 30-80 s for this file. Traps met: Polynomial.eval_finsetSum / finsetSum_coeff (new names),
 Lemma instances at (m := 1) produce Fin (1 + 2), which omega treats as a different atom from Fin 3 -- give the `have` its type.

STATUS 16:50: read BRIEF, NOTES-lean, NOTES-chief secs 2-4, Frame210. Plan: self-contained file Zbf.lean (no Kit needed):
 pm = Matrix.permanent of the pair-function; R0 by scaling + polynomial identity (no P_5 bridge needed); ZBF from
 Mathlib's sumCongrHom range lemma (same shape as det_fromBlocks_zero); UFD step replaced by a LINE lemma
 (P*Q = nonzero constant in C[s] => P constant) giving f_1 = k ell^|S| on U directly, and the domain property along lines for the ell = 0 case.
STATUS 17:00: Zbf.lean compiles (840 lines): R0, ZBF, UFD replacement, ThB(B1), Lemma C (general form, rows, n = 5). Backup Zbf_v1_ok.lean.
 Next: column version (transpose), general n (2n-3), Laplace along a row + CA2 by the direct Laplace argument, ThB trichotomy.
STATUS 17:17: Zbf.lean (1560 lines) compiles with, in addition: Lemma C for general n = m+2 (dim L <= dim L_{rr'} + 2n-3, rows and
 columns, lemmaC_gen / lemmaC_col_gen), dim-9 corollary lemmaC_nine, ThB trichotomy thB_cases, Laplace along a row pm_laplace_row and
 along two rows pm_laplace_two (both derived from ZBF + row linearity), CA2 by the direct Laplace argument (ca2, ca2_full), Theorem A
 (thA), GZ-a lineality (zbf_lineality), SR single-row lemma (single_row_SR), and N3 (3x3 level => dim <= 3, theorem n3) proved from
 Lemma C + one explicit 3x3 identity. Backups Zbf_v1..v4_ok.lean. No paper step failed so far.
STATUS 17:30: Zbf.lean v6 (1832 lines) compiles; adds lev_mix / lev_mix_hat (all mixed coefficients), thB_pair (equiv-free ThB),
 pm_zero_block_sets (finset ZBF), FK block lemma. RESULT table and API guide written above.
STATUS 17:40: FINAL. Zbf.lean v9 (2015 lines) and FrameZbf.lean both compile (exit 0, standard axioms, format 0). Added since 17:30:
 zbf_witness(') (D2/SR in general form), rows_pigeon, row_proj_le, thB_img_or, thB_Bx, q0_isotropic_bound, column versions ca2_col,
 thA_col, and mix_eq_sum_pm / lev_mix_pm / lev_rows. All four targets of the task are COMPILED; no paper step failed.
 Best next Lean steps: (1) C4 (needs the classification of symmetric zero-diagonal C of rank 2 with z_1^T C z_2 = 0 on a codim-2
 space); (2) Theorem G in subpermanent form (needs the generalised Laplace expansion grouping sigma by sigma(A)); (3) n = 4 testbed
 L-gct-091 with lemmaC_gen (m := 2): dim L >= 6 forces a nonzero 2-row element for every row pair and a 2-column element for every
 column pair.

## ROUND 2 (start 17:48, budget 2 h -> ends ~19:48); file lean/zbf/Zbf2.lean = Zbf.lean + new sections (same namespace)
STATUS 17:58 (round 2): Zbf2.lean v1 compiles. NEW: the whole chain R0 -> ZBF/UFD -> ThB -> Lemma C now also for an ARBITRARY BASE POINT b
 (BLev b kappa L := kappa != 0 and pm(c b + t) = kappa c^n for t in L; blev_of_const from "pm(b + t) = pm b != 0 on L"):
 zbf_prodB, zbf_ufdB, zbf_zeroB, thB_quadB/kerB/imgB/dimB, lemmaC_genB, lemmaC_col_genB. Consequence: Steps 1-2 of N3' are replaced by
 Lemma C at n = 3 for the base point b (n3p_row, n3p_col), and N3' is reduced to the explicit hypothesis N3Core (= Steps 3-4 of
 stage3 sec. 10: dim V_0 = 4 exactly, a nonzero single-row element in every row and a single-column element in every column => False):
 theorem n3prime_of_core (hcore : N3Core) b V0 (pm b != 0) (pm(b + eta) = pm b on V0) : finrank V0 <= 3.
STATUS 18:20 (round 2): Zbf2.lean v5 compiles (3112 lines, exit 0, standard axioms, format 0; snapshots Zbf2_v1..v5_ok.lean). Added since 17:58:
 - n3prime_L (Corollary N3'-L, for any n = |alpha| + 3, CONDITIONAL on the statement of N3' passed as hypothesis hN3):
   finrank (blockSpace L r c inf ker fst) <= 3 + finrank (colsOff L c)   [= dim{t in L : t[rr';T^c] = 0} <= 3 + m^T].
 - n3prime_weak (UNCONDITIONAL): perm(b) != 0, perm(b + eta) = perm(b) on V0  =>  finrank V0 <= 4  (Lemma C at the base point b for
   the three row pairs + independence of the three single-row spaces). So only "4 is impossible" (= N3Core) is missing for N3'.
 - (P): rowsZeroS L S (X_S), rows_submodular (d_S + d_S' <= d_{S cap S'} + d_{S cup S'}), rows_rank (rank-nullity for one more row),
   rowsZeroS_empty/_pair/_mono/_insert; same for arbitrary CELL sets: cellsZero, cells_submodular, cells_rank.
   (G1): rows_disjoint_bound, rows_inj_bound.  (G2): stage3_G2 (concrete, rows relabelled by a permutation rho of Fin 5, dS L rho S).
 - Theorem G, identity part: pm_mask_sum (generalised Laplace along a row set A: pm u = sum_T pm (maskAT A T u)), pm_mask_zero
   (|T| != |A| gives 0), pm_mask_factor / thG_term (the term is perm(v[A,T]) * perm(u[A^c,T^c])), thG_masked
   (sum_{|A| = m} sum_T ... = n! C(n,m) c1^(n-m) c2^m). The rho_k inequalities are NOT done.
 - base-point versions of the polarization identities: blev_line, blev_mix, blev_rows.
STATUS 18:45 (round 2): *** THEOREM N3' IS FULLY PROVED IN LEAN (unconditional), and so is Corollary N3'-L. ***
 File lean/zbf/Zbf3.lean (= Zbf2.lean + N3' sections; 4060 lines; exit 0; axioms propext/Classical.choice/Quot.sound; format 0;
 snapshots Zbf3_v1..v3_ok.lean). The final theorem PEqualNP.Outside.L_gct_210_zbf now also contains N3' in definition-free form:
   forall b V0, (sum_{f : Fin 3 emb Fin 3} prod_i b(i, f i)) != 0 -> (forall eta in V0, perm(b + eta) = perm(b)) -> finrank V0 <= 3.
 Names: n3prime (N3'), n3prime_L_full (N3'-L: finrank (blockSpace L r c inf ker fst) <= 3 + finrank (colsOff L c), any n = |alpha|+3).
 THE LEAN PROOF IS NOT THE PAPER PROOF (no step of the paper's Steps 1-4 was contradicted; they were bypassed):
  Steps 1-2 -> Lemma C at the base point b (lemmaC_genB, n = 3): if dim V0 >= 4 every row carries a nonzero single-row element x_r
     and every column a nonzero single-column element y_j (n3p_row, n3p_col); reduce to dim V0 = 4 (exists_sub_finrank).
  Steps 3-4 -> explicit algebra (n3core_of_alg, n3alg). W(r,j) := x_r(r,j), Y(i,j) := y_j(i,j). Bad b W Y := perm(b) != 0 and
     perm(b + D_alpha W + Y D_beta) = perm(b) for all alpha, beta, rows of W and columns of Y nonzero. K := {(alpha,beta) :
     D_alpha W = Y D_beta} has dim >= 6 - 4 = 2 (relMap). Three coefficient lemmas at canonical positions (bad_X1c: two cells
     E_00, E_01 in V0 are impossible [= the content of the paper's Step 3]; bad_X3c: two single-entry rows of W in different columns
     are impossible [= paper's 4(c)]; bad_X4c: a single-entry row r0 at column j0 forces W_il Y_i'm = 0 on the complementary 2x2
     block [= the leading form of 4(e)]), each proved by Moebius extraction of coefficients of the multi-affine polynomial
     (certificates generated and numerically checked by lean/zbf/py/gen_alg.py, gen_n3p.py), transported to arbitrary positions by
     row/column permutations and transposition (bad_rel, bad_tr, bad_X1, bad_XX, bad_X4). Structure: take k^0, k^1, k^2 in K nonzero
     with alpha-coordinate r equal to 0 for k^r; n3_SE2 (a row c with alpha_c != 0 in two elements whose zero sets cover the other two
     rows is single-entry, with the matching column of Y a multiple of e_c), n3_block (a single-entry row c and an element of K with
     alpha_c = 0 and both other coordinates nonzero is impossible), n3_XX (two single-entry rows are impossible); a 9-atom
     propositional case analysis finishes (checked by brute force in gen_n3p.py before compiling).
 Also: N3' with the weaker bound 4 has a 20-line proof (n3prime_weak) and N3Core / N3Alg remain in the file as named statements.
STATUS 19:00 (round 2): *** C4 IS FULLY PROVED IN LEAN (unconditional) *** : lean/zbf/Zbf4.lean (4313 lines, 210 KB, exit 0,
 axioms ok, format 0; snapshot Zbf4_v1_ok.lean). Statement `c4`: Lev 5 L, rows r != r' = r.succAbove p,
 finrank L = finrank (rowsZero L r r') + 7 (pair minimal for Lemma C; any dim L, not only 9), finrank row_r(L) = finrank row_r'(L) = 4
 (a_r = a_r' = 1)  ==>  for all x in X_{rr'}, all j0, q0 : Bx r p x j0 q0 = 0 (the 3x3 subpermanent of x on the other three rows and
 the columns other than j0, j0.succAbove q0).
 THE LEAN PROOF IS NOT THE PAPER PROOF (no classification of C = a b^T + b a^T, no maximal isotropic subspaces, no mu, beta):
   suppose B_x[T] != 0, T = {j0, l0}. (i) ZBF witness (zbf_witness) for rows {r,r'} x columns T^c: ell = 0 on U_T, so U_T in L and
   dim U_T >= dim L - 5. (ii) c4_right (ThA + row_r(L^) = C^5): every t in L with row r = 0 has row r' in the right kernel of B_x;
   so an element of U_T whose row r vanishes has row r' = 0 on T (B_x[T] != 0 and its row r' is supported on T): it lies in X.
   Hence row r maps U_T ONTO C^T (dim U_T - dim X >= 2): e_j0, e_l0 in row_r(L). (iii) c4_left: N := row_r(L cap {row r' = 0})
   (dim = dim L - 4 - dim X = 3) is in the left kernel of B_x, and e_j0, e_l0 are independent modulo that kernel (B_x[j0,l0] != 0,
   zero diagonal). So dim row_r(L) >= 5 > 4. Contradiction.  No paper step failed; the paper proof was simply not needed.
STATUS 19:20 (round 2): Zbf6.lean compiles (4614 lines; snapshot Zbf6_v1_ok.lean). C7/C7'' formalized modulo ONE explicit hypothesis
 (c7_rows, hypothesis hI): c7_pair_thB (ThB => pair alternative), c7_tau / c7_pair_x (pair criterion (a),(b),(d) of C7' by explicit test
 vectors z*, z_0, z_0 + z*; no division), c7_sep / c7_types (plane combinatorics => Type I / II, general index type). The corrected form of
 (d) in C7'' (omega_j + omega_l = 0 AND sigma_j = sigma_l) is what the Lean proof derives and uses. RESULT table + API guide for round 2
 are at the top of this file. Next (time permitting): derive hI from the dimension count (c7_lift).
STATUS 19:36 (round 2): Zbf10.lean compiles (5177 lines, 253 KB; snapshots Zbf7..Zbf10_v1_ok). C7/C7'' is now COMPLETE with no
 explicit-hypothesis hole: c7_lift (dimension count: I^ = L.map(row pair) + C(1,1) has dim 8 = dim of the space cut out by two independent
 relations), c7_hI, c7_rows_full, c7_rows_ind (non-constancy of rho, rho' from row ranks >= 4 + independence), fk_annihilator and
 second_relation (existence of the annihilator data via Mathlib's Submodule.exists_dual_map_eq_bot_of_notMem), c7_final (statement
 about L only). The final placeholder theorem now also contains C4. Checker sanity test passed (a deliberately false lemma is rejected).
 FrameZbf2.lean (Frame210 kit + current ZBF210 namespace + bridge lev_iff_F210 + final theorem) assembled; compile result below.
STATUS 19:36 (cont.): FrameZbf2.lean COMPILES (exit 0, axioms ok, format 0; 6554 lines, 320 KB; log lean/zbf/frame2.log): the P_k tools of
 Frame210 (namespaces MethodCeiling, Helpers.Minc, Helpers.RankOne, Kit086, F210) and all ZBF210 results of rounds 1-2 coexist in one file.
STATUS 19:42 (round 2, FINAL): Zbf11.lean (5227 lines, 256 KB) and FrameZbf2.lean (6604 lines, 323 KB) both compile: exit 0, axioms
 [propext, Classical.choice, Quot.sound], format counts 0. Added since 19:36: dotD, perp_bound, rank_one_bound (linear-algebra core of the
 ThG inequality). Round-2 targets: (1) N3' + N3'-L COMPILED; (2) C4 COMPILED; (3) C7/C7'' COMPILED (c7_final); (4) (P),(G1),(G2) COMPILED;
 (5) ThG identity + rank-one bound COMPILED, the rho_k / K_2 inequalities NOT assembled. No paper step failed.
 Best next steps for a continuation: (a) ThG: define A_k(u) on the index type {(A,T)} and combine thG_masked + pm_mask_factor +
 rank_one_bound (generalise rank_one_bound from Fin N to a Fintype index); (b) Type I / II normal forms of stage2 section 3 from c7_final
 (sum kappa = sum kappa' = 1, sum nu + sum nu' = 0 are available as conjuncts); (c) T0 / T1 / T2 of stage2 (triples) on top of zbf_prod for
 3x2 blocks and n3prime_L_full; (d) column versions of c4 / c7 by transposition (lev_tr, as done for lemmaC_col_gen).

## ROUND 3 (start 19:55, budget 2 h -> ends ~21:55); files lean/zbf/R3a.lean, R3b.lean, ... (R3x = Zbf11 + new sections)
NEW MECHANICAL RULES ADOPTED: namespace is now PEqualNP.Outside.L_gct_210_aux.ZBF (was PEqualNP.Gct.ZBF210); no line begins with add_
 (the six `add_mem' := by` fields were joined to the preceding carrier line with `; `); final theorem last. leancheck guard line: 0 / 0.
STATUS 20:02 (round 3): R3a.lean (= Zbf11 renamed) and R3b.lean compile (exit 0, axioms ok, format 0, guard 0/0). Target (1) DONE:
 rowsZero_tr, map_tr_row, tr_min (transposition transport); c4_col (C4 for column pairs); TypeCl / MinPairCl / MinPairNF (Prop-valued
 defs packaging the classification); c7_final_cl (rows), c7_final_col (columns, by transposition); c7_nf + minPair_nf (NORMAL FORM in
 tau-coordinates: with Q_a = {m : rho'_m = rho'_a}, Q_b = {m : rho_m = rho_b}: for all t in L
 sum_{m in Q_b} kappa_m t(r,m) + sum_{m in Q_a} kappa'_m t(r',m) = 0; in Type I, Q_b = C^c, Q_a = C: the weighted partial sums over C
 agree; in Type II these are the cells Q_3, Q_2 of stage2 section 3); c7_rows_nf, c7_cols_nf.
STATUS 20:11 (round 3): R3c.lean compiles (exit 0, axioms ok, format 0, guard 0/0; snapshot R3c_ok.lean). Target (2), first layer:
 zbf_cases (general alternative: (blk_1 = k ell^|alpha|, blk_2 = k' ell^|beta|, k k' = n!) or (ell = 0 on U and one block permanent
 vanishes on U)); t0 (= T0 for a row triple x column triple, Fin 3 + Fin 2); t2_cubic (the T2 cubic 2t(t a1 + a1 a2 + a1 a3 - a2 a3));
 t2_core (a linear form whose kernel lies in the zero set of that cubic has no a1, a2, a3 coefficient -- elementary proof by test
 points, no irreducibility theory); t2pp_cubic, t2pp_core (the T2'' cubic contains NO hyperplane, for any j != 1; so n**|K_S = 0);
 t1p_alg (T1': the six equations of the cyclic Type II triple have no solution, for ANY i with i^2 = -1, i.e. both signs eps;
 certificates checked first with exact arithmetic, lean/zbf/py/chk_t1p.py); rowsZeroS_single(_finrank); s2_count (X_123 = 0 and
 dim L_i = 5 force (2,2,2) or (2,2,3) up to order).  The STRUCTURAL parts of T2 / T2'' (I_3^perp = N_12 + N_13 + C n**, K_S) are NOT
 formalized.
STATUS 20:25 (round 3): R3d.lean, R3e.lean compile (exit 0, axioms ok, format 0, guard 0/0; snapshots R3d_ok, R3e_ok).
 R3d: ZF (a_r = 1 with zero-free FK annihilator), PairI / PairII (Type I / II predicates built on TypeCl), pair_I_or_II (every minimal
 pair of ZF rows is of Type I or II; from c7_final_cl), T1Hyp, TripleStmt, T2Hyp, T2ppHyp, R31Hyp (PRECISE STATEMENTS of T1, T2, T2'',
 R3-1 as Props -- they are hypotheses, not proved), s2_core, s2 (Corollary S2: X_ijk = 0 forces exactly two minimal pairs sharing a row,
 both of Type II, third pair of dimension 3), s2_star (S2*: with R3-1, X_ijk != 0 for every triple of ZF rows).
 R3e: blk_row_scale; t1_identity (stage 3, section 7: CA2 => identity (T1), for ANY row set S not containing e: if x in L is supported
 on the rows S and xi in L has row e = 0, a_e = 1, then every 4x4 subpermanent of the matrix (rows of x on S, rows of xi elsewhere),
 row e deleted, vanishes; |S| = 2 is stage3's X_a X_b Xi_c Xi_d = 0 in A_4; applied to xi = xi_1 + xi_2 it gives Q_x R_c R_d = 0).
STATUS 20:42 (round 3, STOPPED by coordinator: change of plan, move to the local session). LAST COMPILING STATE = lean/zbf/R3e.lean
 (= R3e_ok.lean; 5914 lines, 290,918 bytes; exit 0, axioms ok, guard 0/0, format 0; 50 s - 2.5 min per compile).
 Handover written: handover/HANDOVER-leanzbf.md (compile instructions, every proved theorem by layer with sources, explicit hypotheses
 T1Hyp / T2Hyp / T2ppHyp / R31Hyp, guard status, next targets with the unwritten plan for Theorem G, tricks and traps, file map).
 Not started / not finished in round 3: full T2, T2'' (only their algebraic cores), GEN-2, stage-3 MIN-A / TV / MIN-B / N1, Theorem G
 inequality (plan only, no Lean written).

## ROUND 4 (local machine; start 19:48 UTC by this machine clock, about 1-1.5 h -> ends ~21:00). Base: lean/zbf/R3e.lean (last compiling state). New files R4a.lean, ...
Plan: (0) guard: placeholder theorem renamed to PEqualNP.Outside.L_gct_210 so the full project guard passes on the test file;
 (1) T2 / T2'' / R3-1 common first half by a PRIMAL argument (no I_3, no duals): nu, mu, kappa (row-1 parts of the two pair relations
 and the FK annihilator) are all orthogonal to row_1(X_23), which has dim >= dim X_23 - dim X_123 >= 3, so they span <= 2 dims;
 hence the two pair partitions of row 1 coincide; (2) GEN-0 (stage2 R2-2, verified): in GEN a Type I block has 2 or 3 columns;
 (3) then the second half of T2 (lifting for row triples, K_S test, t2_core).
STATUS 19:49: round 4 started; read TEAM-RULES, BRIEF (UPDATE 11), handover, NOTES-verify2 RESULT 1-5; guard script read
 (R3e fails only on the placeholder theorem name; FrameZbf2 fails on add_mem / Gct namespaces).
STATUS 20:14: R4b.lean (= R3e + r4_1 + r4_2, 6554 lines, 321 KB) queued for the Lean slot (project guard passes: placeholder theorem
 renamed PEqualNP.Outside.L_gct_210). New: t2_dep / t2_partition / t2_split (T2 first half, primal), ZFc, dot_zero_of_col,
 row_rel_zero, col_rel_zero, lone_rel, gen0_typeI, gen0_pairI (GEN-0), and the T2 second-half machinery: blkL (L cap zero block),
 ell_ne_of_small (dim blkL <= 3 => ell != 0 on the block space), stest_blk (then perm_3 = 0 on blkL, via t0), hyper_core
 (3-dim H in C^4 with the T2 cubic vanishing => H contains {x0 = 0}, via t2_core), t2_alg (perm identity), t2_stest (the K_S test),
 span_classes. KEY SIMPLIFICATION of T2's end: the S-tests put (kappa2_q)^-1 e_q - (kappa2_s)^-1 e_s into row_2(X_13) for all q ~ s;
 these span 3 dims, but dim X_13 = 2. No n**, no I_3^perp needed.
STATUS 20:24: R4b now also contains r4_3 = fk_unique, exists_perm3 / exists_equiv3 (equivs Fin 3 + Fin 2 = Fin 5 through given
 distinct triples), sum_supp3, sum_C_supp3, typeI_nf (Type I normal form: kappa' = +-f kappa on the two classes, and
 sum_C kappa t_r = sum_C kappa' t_r' on L), t2_gen_vec (one S-test => generator in row_2(X_13)), and t2_proof : T2Hyp (FULL T2,
 no hypothesis). Final placeholder theorem now = old statement AND T2Hyp (so leancheck prints the axioms of t2_proof).
 Waiting for the Lean slot (leanfl compiles FLk / Tps). Also prepared lean/zbf/FrameR4.lean (Frame210 kit with namespaces renamed to
 PEqualNP.Outside.L_gct_210_aux.{MethodCeiling,Helpers.Minc,Helpers.RankOne,Kit086,F210} + the R4b ZBF namespace + Bridge.lev_iff_F210
 + final theorem; 406 KB): project guard passes; compile only after R4b is green.
PLAN T2'' (next): same primal framework. S-types (C = Q3 = Type I block, D = Q1 + Q2): (A) {p in Q3, q in Q1, s in Q2}: the T2''
 cubic has no hyperplane (t2pp_core) => dim(blkL) = 4, so all of K_S lifts; (B) {p in C; q, s in Q2} and (C) {p, p' in C; q in Q2}:
 cubic = -2t x (quadric) => {t = 0} lifts (t2_core-type lemma needed for these two cubics). Row-2 generators e_q - e_s then connect
 all of D (pairs Q1-Q2 and Q2-Q2) and all of C, so they span |C| - 1 + |D| - 1 = 3 dims inside row_2(X_13) (dim 2): contradiction,
 exactly as in t2_proof (span_classes). Needs: Type II normal form lemma (analogue of typeI_nf, from TypeCl with corner).
 T2'' refinement (checked numerically, leanzbf/chk_t2pp.py): S-types (B) {p in C; q, s in Q2} and (C) {q in Q2; p, p' in C} have
 EXACTLY the T2 shape (tau_i = (t, a_i, -t - a_i), kappa ratios d (1,-1,-1)), so t2_stest applies verbatim (only the derivation of
 the local relations changes: row 3 uses the Type II relation sum_B tau_1 + sum_Q2 tau_3 = 0). Type (A) {p in C, q in Q1, s in Q2}:
 identity d2 c k_p k_q k_s perm(x) = (a2 - a1) t (t - j (t - a3)) - a3 (t (a1 + a2) + 2 a1 a2) with kappa3 = (-c, c j, c) kappa,
 j^2 = -1; t2pp_core + hyper_top (in r4_4) => all of K_S lifts. Prepared: typeII_nf, hyper_top (r4_4.txt).
STATUS 21:31: coordinator note (R4b starved of RAM, compile windows from ~22:30): I stopped my starved R4b run (48 min wall, RSS
 0.3 GB, no output) to free RAM/slot; R4b.lean is unchanged and ready for the window (= R3e + r4_1..r4_4; final placeholder theorem
 = old statement AND T2Hyp). NEW TEST FILE for the window: lean/zbf/R4t_stub.lean (3250 lines, 159 KB) = R3e with every OLD theorem
 proof replaced by sorry (statements identical; all defs kept; R3e itself compiled with standard axioms in round 3) + ALL new blocks
 r4_1..r4_5 with full proofs; final theorem True. It checks only the new parts, fast; axioms line will show sorryAx by design (old
 parts), so only the error list matters. Then R4b (full) and FrameR4 (guard-compliant kit + ZBF) as the real checks.
STATUS 21:38: wrote r4_5 (t2pp_alg) and r4_6 = T2'' COMPLETE in Lean text (not yet compiled): sum_C_three, loc_rel (local relations
 at a column triple), gen_vec_core (S-test generator from local relations; S-types (B), (C) of T2''), t2pp_stest (S-type (A):
 hyper_top + t2pp_core => all of K_S lifts), gen_vec_A, t2pp_proof : T2ppHyp (B = Type II class of b' = Type I class up to
 complement by t2_split; row-2 generators: pairs in B via (C), Q2-Q2 via (B), Q1-Q2 via (A), Q1-Q1 as differences; span_classes
 => 3 <= dim row_2(X_13) <= 2). FILES FOR THE 22:30 WINDOW (all guard-checked where applicable):
  1. lean/zbf/R4t_stub.lean (3984 lines, 194 KB): old proofs = sorry (statements identical), ALL new blocks r4_1..r4_6 in full. FAST.
  2. lean/zbf/R4c.lean (7826 lines, 381 KB; project guard OK): R3e + r4_1..r4_6; final placeholder theorem = old statement AND
     T2Hyp AND T2ppHyp (axioms line then covers t2_proof, t2pp_proof). Supersedes R4b.
  3. lean/zbf/FrameR4.lean (9208 lines, 448 KB < 512 KiB; project guard OK): guard-compliant Frame210 kit + R4c's ZBF + bridge.
 If T2 and T2'' compile, S2 / S2* depend only on T1Hyp (exact 3108-configuration check) and R31Hyp (exact 1800-configuration check).
STATUS 21:45: WINDOW REQUEST (replaces "retry R4b"): compile in this order
  (1) lean/zbf/R4t_stub.lean  (4119 lines; old proofs sorry'd; new r4_1..r4_7 incl. GEN-lin (gen_lin, ker_prop, polyLine_lin))
  (2) lean/zbf/R4c.lean       (7826 lines; full; r4_1..r4_6; final theorem includes T2Hyp AND T2ppHyp)
  (3) lean/zbf/FrameR4.lean   (9208 lines; full + guard-compliant kit)
 I fix errors from (1) before (2)/(3) if the window allows a second pass. Pre-compile review fixes applied: no `decide` with
 metavariables, no multi-location rw with missing patterns, vector-literal facts by defeq instead of simp, mem_ker explicit.
DESIGN NOTE (next round) T1Hyp in Lean: all three pairs minimal + X_123 = 0. In the blkL framework: for a column triple S, the
 local relations (row sums, three pair relations restricted to S) cut K_S; with all three pairs minimal and X_123 = 0, dim(L cap
 {rows 1-3 supported in S}) >= 9 - 6 = 3 always, and if the six local functionals are independent on C^{3xS} then K_S itself is
 <= 3-dim, so EVERY point of K_S lifts (equality of dims) and ell != 0 on the block space unless dim = 4 (impossible); stest_blk then
 makes perm_3 vanish on all of K_S, and one exact point with perm_3 != 0 (stage2 t5/t10 certificates) is a contradiction. Per
 configuration: one S, one rational/Gaussian point, one perm evaluation -- generate the Lean case split by script (3108 cases, up to
 symmetry fewer); the six cyclic Type II triples are t1p_alg. R31Hyp: same pattern with verify2's r3_exact certificates.
STATUS 21:50: window 1 list written (leanzbf/window_files.txt): R4t_stub.lean then R4c.lean. Not calling leancheck myself.
STATUS 22:23: window-1 errors repaired (see ROUND 4 RESULT at top); window-2 list = R4t_stub.lean, R4c.lean.
STATUS 22:35: round 5 started. Plan: generic lift lemma stest_lift3 (3-param K_S + one exact point with perm != 0 => False), then T1 for (I,I,I) (uniform S: three columns of distinct (C12,C13)-types; local pattern checked: perm = -4 at (A,B,D) = (1,1,0), leanzbf/t1_iii.py), then other type combos via generated certificates.
STATUS 22:37: r5_1..r5_4 written: stest_lift3 (generic: 3-parameter K_S + one exact point with perm != 0 => False), t1_iii_local, two_val_*, xor_nonconst, comb_pqs, pair_local, t1_III (T1 when all three pairs are Type I; uniform column triple from the (C12,C13)-type square), T1Rest + t1_of_rest : T1Rest -> T1Hyp. Files: lean/zbf/R5a.lean (R4c + r5, 8318 lines, guard OK; final thm adds (T1Rest -> T1Hyp)), lean/zbf/R5t_stub.lean (4608 lines). Window-2 list updated: R5t_stub.lean, R4c.lean.
STATUS 22:45: r5_5/r5_6: corner_sq, sq_ratio, sq_contra, typeI_ratio, t1_one_II (a T1 triple with exactly ONE Type II pair is impossible by ratio consistency alone: the corner ratio squares to -c^2, but a product of two Type I ratios has constant square), T1Rest2 (only configurations with >= 2 Type II pairs) and t1_of_rest2 : T1Rest2 -> T1Hyp. R5a.lean (8445 lines, guard OK) final theorem now carries (T1Rest2 -> T1Hyp). R5t_stub.lean rebuilt (4733 lines). Running leanzbf/t1_enum.py (all configurations, simple S-test screen) to plan the >= 2 Type II cases.
STATUS 22:44: T1 configuration screen [numerical; leanzbf/t1_enum.py, all raw configurations, Type I classes up to complement,
 float rank + random points]: (I,I,I) 210/210 killed by the simple S-test; exactly one Type II pair: 0 consistent configurations
 (= t1_one_II); (I,II,II), (II,I,II), (II,II,I): 5880 each, ALL killed by the simple S-test; (II,II,II): 105120, of which 103560
 killed and 1560 not (these need stage2's cube test with ell != 0 on Pi_S, or T1' for the cyclic family; cf. stage2: 32 canonical
 survivors of the kernel test, 26 killed by the cube test, 6 cyclic killed by T1').
 UNIFORM RULE for (II,II,I) [numerical, leanzbf/t1_rules2.py]: S = {p in Q1^12 (corner), q in Q2^12, s in Q3^12} with C23
 non-constant on S passes the simple S-test in ALL 5880 configurations, and such S always exists (if C23 were constant on every
 transversal it would be constant). 40 local patterns (20 up to complementing C23; leanzbf/t1_patterns.py) -> next round: generate
 one stest_lift3 instance per pattern (M, x0, perm certificate over Q(j), j^2 = -1) by script; needs a corner_unique lemma
 (all corner columns of a Type II pair share kappa'/kappa, from TypeCl's last clause) for option B (two corners of pair 13 in S).
 Also built lean/zbf/FrameR5.lean (guard-compliant kit + R5a, 481 KB < 512 KiB, guard OK).
STATUS 22:47: r5_7 (corner_unique: all corner columns of a Type II pair share kappa'/kappa; rule_R: existence of the (II,II,I) column triple) added to R5t_stub.lean (4781 lines) only.
STATUS 22:50: EXACT data for the (II,II,I) generator (leanzbf/t1_gen_data.py, Gaussian-rational arithmetic, log t1_gen_data.log):
 under rule R (p corner of pair 12, q in Q2^12, s in Q3^12, p in C23 normalised, C23 splitting S) there are exactly 20 locally
 consistent patterns (pair-13 labels at (p,q,s), C23 sides, signs eps12, eps13); in ALL 20 the six local relations have rank 6
 (3 free tau-positions listed) and an explicit integer point gives perm(tau/w) != 0 (values like -4, +-32, +-32i, 3+-i). So
 T1 for (II,II,I) = 20 stest_lift3 instances + the dispatch (inconsistent label combinations die by ratio algebra). By row
 relabelling the arrangements (I,II,II), (II,I,II) reduce to it once PairI/PairII for the reversed ordered pair is available
 (needs a small "type is independent of the order of the pair" lemma or a second dispatch). (II,II,II): 1560 raw configurations
 need the cube test; the other 103560 are simple S-tests (rule search not yet done).
STATUS 22:48: round 5 report sent (window 2 pending: R5t_stub.lean, R4c.lean).
STATUS 22:55: round 6 started (target 1: generator for the 20 (II,II,I) patterns).
STATUS 23:00: r6_0 (stest_lift3'), r6_1 (10 generated (II,II,I) core pattern lemmas, leanzbf/gen_t1p.py), r6_2 (typeCl_swap, pairI_swap, pairII_swap = row-order invariance) written; R6t_stub.lean (6180 lines) replaces R5t_stub in the window-2 list. Next: global wrappers + the (II,II,I) dispatch (uniform case analysis: side equations u(m)v(m') = +-u(m')v(m) with v = (jc, c, -c) give 10 consistent leaves, 71 contradictions of 5 kinds).
STATUS 23:06: round 6: r6_0..r6_5 written (generated (II,II,I) proof, swap lemmas, T1Rest3 reduction). Window-2 list = R6t_stub.lean, R4c.lean.
STATUS 23:13: (II,II,II) screen [numerical; leanzbf/t1_iii3.py, t1_iii4.py, t1_bad.py]: of 105120 raw configurations, 103560 are
 killed by the simple S-test; for each of them SOME transversal of the cells of pair 12, 13 or 23 works (102600 already with a pair-12
 transversal), but no simple rule makes ALL candidate triples good (tested: T12; T12 + non-constant 13/23 labels; T12 + T13; any
 transversal + all labels non-constant) -> the (II,II,II) dispatch needs a finer, family-wise rule. The 1560 failures ALL have theta
 imaginary (kappa3/kappa2 ratio pattern rotated by i) and corner sets covering all five columns, in two families:
 F1 = corner sets of the three pairs pairwise DISJOINT (sizes (1,1,3), (1,2,2) and permutations; 600 raw) = the cyclic Type II
 triple of stage2 (killed by T1', i.e. t1p_alg after the J-relations); F2 = pairwise intersections of size 1, 1, 1 or 2, 2, 2
 (sizes (2,2,3) and permutations, (3,3,3); 960 raw) = stage2's cube-test cases. Both need the Type II L^-constant (normal form
 y = (-1 + eps i)/2, stage2 sec. 3, verified r1), not yet in Lean.
STATUS 23:15: r6_6 added (c7_split; typeII_J: for a Type II pair with a corner, (K_b + K'_a)(omega + c) = c, i.e. the L^-constant of the Type II normal relation is c/(omega + c) = (1 - eps i)/2 -- the normal form y = (-1 + eps i)/2 of stage2 sec. 3; checked numerically). Needed for the cube test (family F2) and T1' (family F1). R6t_stub.lean rebuilt (window-2 list unchanged).
STATUS 23:18: (II,II,II) split [numerical, leanzbf/t1_iii5.py]: theta real <=> the three corner sets do NOT cover the 5 columns
 (55680 plainly-killable configurations), theta imaginary <=> they cover (47880 plainly-killable + the 1560 failures F1/F2). In both
 halves the rule "transversal of one pair's cells with the other two labellings non-constant" works for most but not all
 configurations (8160 resp. 10080 exceptions) -> next round: finer family-wise rules (by present column types) or a generated
 per-type dispatch.
STATUS 23:27: (II,II,II) core lemmas GENERATED: leanzbf/gen_t3p.py -> lean/zbf/r6_7.txt (118 lemmas t3p_{lab13}_{p|m}_{lab23},
 15577 lines, 997 KB; same template as r6_1 with the pair-23 relation of Type II). Exact cross-check: the exact generator's passing
 patterns = the 98 numerically passing (l13, l23) patterns of t1_iii6.py; the 14 failing patterns are exactly the exact rank/perm0
 skips. Dispatch analysis [exact patterns, leanzbf/t1_iii7.py, 52560 label configurations up to eps]: 780 = F (no row order works,
 = F1 + F2), 51780 killable: 34980 every pair-12 transversal passes, 15720 some fail but a one-point replacement always fixes,
 600 need a two-point replacement, 480 need a row reorder. -> next round: generated dispatch (estimate several thousand leaves; must
 first shrink with the theta structure: theta real => C13 = C12 sym.diff C23, theta imaginary => C13 = complement of it).
 Window-2 stub now also carries 3 sample t3p lemmas (r6_7s.txt) to test the variant template. Pre-compile fix: subst e1/e2/e3
 -> subst κ' / κ2' / κ3' (explicit eliminated variable) in r5_3, r6_4 and gen_t1d.py. R6t_stub.lean: 9389 lines, 512 KB, guard
 clean; R6a.lean rebuilt (12716 lines, 667 KB).
STATUS 23:32: wrappers refactored through s_transfer (r6_4 2668 -> 2078 lines, dispatch unchanged); unit_split added; stub/R6a rebuilt; ROUND 6 RESULT block and handover 000 rewritten (incl. the (II,II,II) dispatch plan). Window-2 list unchanged: R6t_stub.lean, R4c.lean.
STATUS 23:32: sizing of the (II,II,II) top-level tree (13- and 23-status of the transversal p = m0, q = a, s = b; 729 leaves): 605 ratio-inconsistent (one certificate each), 98 passing (core lemma t3p_*, 52 of the consistent leaves need the unit_split sign split), 26 consistent but not passing (the 14 failing patterns + 12 rank-deficient ones) -> second level.
STATUS 23:41: (II,II,II) top-level dispatch GENERATED (draft, not compiled, not in the stub): leanzbf/gen_t3d.py -> lean/zbf/r6_9.txt,
 theorem t3_trans (7893 lines, 593 KB): for all-Type-II data with shared FK annihilators and ANY pair-12 transversal p (corner),
 q (Q2^12), s (B12), the local 13/23 pattern of (p, q, s) is one of the 26 consistent NON-passing patterns (explicit disjunction).
 Tree: statuses of q, s, then p (pruned after q, s): 305 leaves; ratio equations F_m : X13 = X23 * W_m; corner ratios split by
 unit_split (omega = +-j c'); inconsistent branches die by an exact certificate ((P - Qj) * cross-product of two F's, reduced
 mod j^2 + 1, giving (P^2 + Q^2) c' c'' c = 0; every certificate checked numerically in the generator); passing branches call the
 t3p_* lemma through s_transfer; non-passing branches prove their disjunct. Needs r6_7 (all 118 t3p_*) before it.
STATUS 23:43: r6_9 extended: def T3Rest (all-Type-II triples with X_123 = 0 in which EVERY pair-12 transversal has a non-passing pattern) + t1rest3_of_t3rest + t1_of_t3rest : T3Rest -> T1Hyp. So once r6_7 + r6_9 compile, T1 is reduced to T3Rest (a strictly smaller, verified statement). r6_9: 7981 lines, 601 KB, guard clean.
STATUS 23:46: r6_9 extended again: def T3Rest2 (= T3Rest plus: every transversal of pair 13 in the row order (r1, r3, r2) is non-passing too) + t3rest_of_t3rest2 (second t3_trans application with typeCl_swap for pair 23) + t1_of_t3rest2 : T3Rest2 -> T1Hyp. Exact check (leanzbf/t1_iii8.py): the configurations left by T3Rest are 780 F + 480 rescued by orders 132/231/312/321, so the configurations of T3Rest2 are EXACTLY F1 + F2 (780 up to eps). Window-3 candidate: lean/zbf/R7t_stub.lean (1.24 MB = R6t_stub + r6_7 statements with sorry + r6_9).
STATUS 23:47: R6b.lean assembled (leanzbf/mk7.py: R3e + rounds 4-6 incl. r6_7 + r6_9; 35868 lines, 2.26 MB, guard clean
 except the size cap; final theorem: old statement /\ T2Hyp /\ T2ppHyp /\ (T3Rest2 -> T1Hyp)). F profile for the remaining step
 [leanzbf/t1_iii9.py]: on the 780 F configurations only FOUR non-passing patterns occur on pair-12 transversals:
 ((1,1,3),(1,3,1)), ((1,2,1),(1,1,2)) [240 each] and the fully transversal ((2,1,3),(2,3,1)), ((3,2,1),(3,1,2)) [390 each];
 19 class-size profiles. Next (Lemma B): from the two t3_trans hypotheses of T3Rest2 derive the class structure of F1/F2, then
 typeII_J + t1p_alg (F1) and an affine S-test (F2).
STATUS 23:50: per-declaration heartbeat limits added (set_option maxHeartbeats N in, allowed by the guard: 1e6 for each t1p_/t3p_ core lemma, 2e6 t1_III, 1e7 t1_IIi, 5e7 t3_trans; via the generators + r5_3). All stubs/full files rebuilt: R6t_stub 8900 lines (window-2 file 1), R7t_stub 18822, R6a 12224, R6b 35999; guard plain + own-namespace checks pass on R6a and R6b (leanzbf/guardcheck.mjs); only the size cap fails.
STATUS 23:51: gen_t3p.py no longer emits the 20 duplicate no-corner sign variants: r6_7 = 98 core lemmas (833 KB), every one used by t3_trans, none missing. Rebuilt R6t_stub (8900 lines; sample t3p_323_m_211 -> t3p_323_p_211), R7t_stub (18442 lines, 1.21 MB), R6b (33339 lines, 2.10 MB); guard plain + namespace OK.
STATUS 23:52: coordinator: window 2 opens by 00:05 (after leanfl's two files). Window list CHANGED: R6t_stub.lean, R7s_t3.lean (new, leanzbf/stub2.py: R3e + r4..r6_6 + r6_7 as statements with sorry, r6_9 with full proofs; 13060 lines, 910 KB) replacing R4c.lean (its new blocks r4_1..r4_6 are all inside R6t_stub).
STATUS 23:53: Lemma B sizing [leanzbf/lemB_size.py]: tree p,q,s -> x -> y has 26 / 102 / 46 live nodes (46 complete leaves = F), about 3300 pruned nodes -> generatable next round.
STATUS 23:56: F2 route found: R3e's zbf_ufd already is the cube statement (perm3 = k ell^3 on blockSpace); next round: stest_affine (stest_lift3 with the inhomogeneous right-hand sides c and c*G, G = (1 -+ i)/2 from typeII_J) -- written into handover 000.
STATUS 23:58: r6_6 += stest_affine (the cube test as a lemma: on blockSpace the entries k*hat(w) on S satisfy hM with an affine term N*w.1; two points x0, x1 of the c = 1 slice with different permanents give False via zbf_ufd; proof modelled on stest_lift3, realizability via htop + a scaled w0 from ell_ne_of_small). In R6t_stub (now 9004 lines, 500 KB), so window 2 tests it. Rebuilt R7s_t3 (13074), R7t_stub (18546), R6a (12328, 655 KB), R6b (33443, 2.10 MB); guard plain + namespace OK.
STATUS 00:00: round-6 final report sent to the coordinator (SendMessage). Waiting for the window-2 logs (R6t_stub.lean, R7s_t3.lean).
STATUS 00:01: ROUND 7 started (coordinator targets: 1 repair from window-2 logs, 2 Lemma B generated, 3 F1 via typeII_J + t1p_alg and F2 via stest_affine, 4 generic core lemma to shrink r6_7/r6_9). Window 2 pending (R6t_stub, R7s_t3 after leanfl's files).
STATUS 00:10: Lemma B GENERATED (leanzbf/gen_lemB.py -> lean/zbf/r7_1.txt, 3196 lines): purely combinatorial theorem lemB on the six class Finsets: from the T3Rest2 transversal hypotheses (orders 123 and 132) and the class witnesses, every column has one of the 4 types of orientation 1 {(C,C,C),(C,Q,Q),(Q,C,B),(B,B,C)} or every column one of orientation 2 {(C,C,C),(C,B,B),(Q,Q,C),(B,C,Q)} (defs Orient1/Orient2). Analysis [leanzbf/lemB_an.py]: 26 Hall cases; per case an allowed status list for any column (B1, 27-way split, all prunes by Hall/Hall2 + simp); 22 cases refuted by witness classes (21 by one witness, 1 by two), 4 cases give the orientation (bad allowed statuses refuted by witnesses). No ratio certificates needed. r7_2: f1_alg (F1 = orientation with empty (C,C,C) class: the six equations, i.e. row sums of κ, κ2, κ3 and the three J-relations of typeII_J after the ratio identities omega = j c', omega2 = j c'', are contradictory; certificates checked numerically).
STATUS 00:22: r7_2 += f1_alg2 (orientation 2; certificates by leanzbf/lcfind.py, sympy) + sum_three_parts, sum_scale, sum_one_eq; r7_3 (leanzbf/gen_bridge.py) = orient1_noT0, orient2_noT0: Orient + no (C,C,C) column -> False (witness types give omega = j c', omega2 = j c''; class sums A1..A3; typeII_J for the three pairs; all certificates checked in leanzbf/cert_chk.py); r7_4 = def T3F2 (= T3Rest2 data + orientation + a (C,C,C) column) + t3rest2_of_t3f2 + t1_of_t3f2 : T3F2 -> T1Hyp. So T1 is reduced (Lean text) to F2 alone. Files: R8s_r7.lean (all else stubbed, r7_1..r7_4 full; 8974 lines), R7b.lean (everything, final conjunct T3F2 -> T1Hyp; 37234 lines, 2.42 MB, guard plain+namespace OK). Window 2 is running (R6t_stub log file created 00:20, still empty).
STATUS 00:25: KEY FINDING [leanzbf/f2_stage2chk*.py, stage2's own t6 cube test run on my lemB leaves]: orientation 1 is killed ENTIRELY by the affine (cube) test on S = (T1,T2,T3) = (a', a, b) (ell != 0, perm3 not k ell^3; F1 and F2 alike), and orientation-2 F2 by the affine test on S = (T0, U2, U3) = (t0, a, b); only orientation-2 F1 (the cyclic family) is cube and needs the algebra (f1_alg2, done). Both are pair-12 transversals; local patterns ((2,1,3),(2,3,1)) and ((1,2,1),(1,1,2)) with the J-constants K = (1-j)/2. Next: generated affine core lemmas (stest_affine) + wrappers -> T3F2 provable -> T1 complete (modulo compile).
STATUS 00:30: T1 COMPLETE AS LEAN TEXT (not compiled): r7_5 (leanzbf/gen_aff.py) = affine cube-test core lemmas a3p_o1 (S = (T1,T2,T3), pattern ((2,1,3),(2,3,1))) and a3p_o2 (S = (T0,U2,U3), pattern ((1,2,1),(1,1,2))) via stest_affine (exact M, N in Q(j), two points with different permanents, (a^2+b^2) certificate); r7_6 = s_transfer_aff, typeII_aff (affine pair relation on blockSpace), typeII_ite_aff, ksum_half; r7_7 (leanzbf/gen_aw.py) = wrappers a3w_o1 (orientation 1, any), a3w_o2 (orientation 2 with a (C,C,C) column) using typeII_J for the three pairs (K = (1-j)/2), then t3f2_proof : T3F2 and t1_proof : T1Hyp := t1_of_t3f2 t3f2_proof. Full candidate R7c.lean (leanzbf/mk9.py): final theorem = old statement /\ T2Hyp /\ T2ppHyp /\ T1Hyp (T1 unconditional), 38051 lines, 2.47 MB, no sorry, guard plain+namespace OK (size cap exceeded). Test stub R8s_r7.lean (everything else stubbed, r7_1..r7_7 full; 9789 lines).
STATUS 00:32: window 2 R6t_stub is compiling (started 01:20 local = 00:20 UTC, lean at ~4 GB); the partial log (32 KB flushed) shows NO errors up to file line ~6277, i.e. r4_*, r5_*, r6_0, the 10 generated core lemmas r6_1, r6_2, r6_3 elaborated without error messages so far. Window list file 2 changed to R9s_all.lean (17679 lines: r7_1, r7_2, r7_3, r7_5, r7_6 full, then r6_9 t3_trans full, then r7_4, r7_7 full; everything else stubbed).
STATUS 00:39: WINDOW 2 RESULT R6t_stub.lean (951 s, peak 6.8 GB): only 4 errors, all '(deterministic) timeout ... 10000000 heartbeats' inside the generated dispatch t1_IIi; EVERYTHING ELSE COMPILED: r4_* (T2/T2'' repairs), r5_* (stest_lift3, t1_III, t1_one_II, T1Rest2...), r6_0, the 10 generated core lemmas r6_1, r6_2 (swap lemmas), r6_3, the generated wrappers r6_4, r6_5 (T1Rest3), r6_6 (c7_split, typeII_J, unit_split, stest_affine) and the 3 sample generated (II,II,II) core lemmas r6_7s. Repair (in gen_t1d.py): the 199 'by tauto' side conditions (huge context) replaced by named facts from new tiny lemmas iffA..iffE (r6_3), heartbeats 4e7. Also added heartbeat limits to lemB (2e8), bridges and wrappers (8e6), t3rest2_of_t3f2 (4e6). The second window-2 file actually compiling is R7s_t3.lean (the list edit came after the list was read). Next window list: R6r_t1IIi.lean (small re-test of t1_IIi), R9s_all.lean. Rebuilt R6t_stub (9027), R9s_all (17700), R7c (38080 lines, guard plain+namespace OK).
STATUS 00:40: speed fixes: generated contradiction steps 'simp [hc, ..] at e' replaced by 'exact absurd e (mul_ne_zero ..)' (gen_t1d.py, gen_t3d.py); r6_4/r6_9 regenerated, R6r_t1IIi.lean (5111 lines), R9s_all.lean (17700), R6t_stub (9027), R7c (38080, guard OK) rebuilt. Waiting for R7s_t3 log.
STATUS 00:48: next-window list = R9a.lean (r6_3..r6_6 incl. repaired t1_IIi + r7_1, r7_2, r7_3, r7_5, r7_6 full; 9538 lines) and R9b.lean (r6_9 + r7_4 + r7_7 full; 13726 lines) -- split to keep each under the 60 min timeout. R7s_t3 (old r6_9) still compiling (log at file line ~4004 after 11 min, buffered).
STATUS 00:51: prepared R9c.lean (rest stubbed; r6_6 + ALL 98 generated (II,II,II) core lemmas r6_7 full; for window 4). R31Hyp note: R3-1 needs the unknown fifth annihilator n** (families with parameters delta, al, be, ga) -- the affine machinery (stest_affine) fits the final cube-defect step (E5), but (E4) (no admissible n** in 120 configurations, verify2's 1320 cubic certificates) is a parametric elimination; deferred as instructed.
STATUS 00:53: WINDOW 2 RESULT R7s_t3.lean: exit 0, 0 errors (921 s, 6.5 GB): the generated t3_trans (305 leaves) + T3Rest/T3Rest2 reductions are VERIFIED. gen_t3d.py reverted to the exact verified text (r6_9 identical to the compiled block); gen_t1d.py keeps only the necessary repair (tauto -> iffA..iffE, 4e7 heartbeats; simp forms kept as in the verified leaves). Window-3 list: R9d.lean (r6_3, r6_4 repaired t1_IIi, r6_6, all r7 full; verified r6_5/r6_9 stubbed) and R9c.lean (all 98 t3p_* core lemmas). If both pass, every block of the T1 chain has compiled at least once (piecewise, with stubs for the other blocks).
STATUS 00:53: round-7 final report sent (SubagentHandback).
STATUS 00:58: ROUND 8 started (targets: 1 repair from window-3 logs (window 3 ~02:30-06:00), 2 generic core lemma replacing the 98 t3p_* + 10 t1p_* instances, 3 R31Hyp ((E5) via stest_affine; (E4) formulation), 4 next ZBF hypotheses). Window-3 list unchanged: R9d.lean, R9c.lean.
STATUS 01:01: TARGET 2: generic core lemma stest_gen (lean/zbf/r8_1.txt): the homogeneous S-test for ANY pattern, data = relation matrix A (3 pair relations), M, pi, pj, lambda certificates Lr/La (hypothesis hid: one linear identity per entry, checked at the call site by simp only + ring), weights W (hw1/hw2) and a point x0 with perm((sum M x0)/W) != 0; row sums, the lift (stest_lift3) and the kappa scaling of the permanent are proved once. leanzbf/gen_slim.py regenerates all 10 t1p_* and 98 t3p_* lemmas with UNCHANGED names/signatures as slim instances (r6_1g.txt 42 KB vs 85 KB, r6_7g.txt 412 KB vs 833 KB; data self-checked numerically in gen_slim_chk.py). Full candidate R8c.lean (R3e + all blocks, slim instances; 30467 lines, 2.01 MB vs 2.47 MB; guard plain+namespace OK, no sorry). Window-3 file 2 changed to R10s_slim.lean (stest_gen + all slim instances); R9c.lean (old r6_7) kept as fallback.
STATUS 01:04: TARGET 3 (R31Hyp) analysis. Setting R3-1: I_3^perp = span(A0) + C n**, A0 = the four known functionals (their L^-
 constants y pinned by typeII_J), n** = (0, m2, m3) = the extra annihilator of the non-minimal pair (2,3). J pins only ONE coefficient
 of n** (n**(kappa) = 0, e.g. the -delta ell term), so n** stays in an ~8-dim family: no finite pinning as for typeII_J. BUT (E2)
 makes it finite per S: for each column triple S with ell != 0 on Pi~_S (Pi~_S = span(A0)^perp, n**-INDEPENDENT), with c_S :=
 perm|K_S, either n**|K_S = 0 or c_S vanishes on ker(n**|K_S), i.e. n**|K_S is proportional to a LINEAR FACTOR of the n**-free cubic
 c_S. So n**|K_S ranges over {0} u {finitely many lines}; a DFS over these choices with exact linear algebra replaces the elimination
 (verify2/r3_exact.py does exactly this). The certificates needed per cubic: the factor list and its COMPLETENESS: 3 distinct factors
 (673 cubics: the identity c_S = k l1 l2 l3 suffices; in Lean: a product of three linear forms vanishing on a plane forces one factor
 to vanish there -- elementary), 1 factor x quadric of rank >= 3 (152: rank certificate + 'a rank>=3 quadric does not vanish on a
 plane'), 0 factors (344: smooth plane section -- the hard part in Lean), ell = 0 (151: no condition). Running now: verify2's DFS with
 only the 3-factor certificates (and with 3+1-factor) to see whether the hard 0-factor certificates can be avoided
 (leanzbf/r3_variant.py, logs r3_variant_three_only.log, r3_variant_no_zero.log). (E5) (cube defect on the 12 surviving families) is a
 stest_affine computation with symbolic parameters and a finite case split (delta_h = 0 or not; be = 0 inadmissible).
STATUS 01:12: R31Hyp (E4) certificate experiment [leanzbf/r3_variant.py = verify2/r3_exact.py with the DFS restricted; logs
 r3_variant_three_only.log, r3_variant_no_zero.log]: of the 132 canonical configurations passing (E1), verify2's full DFS leaves 12;
 with ONLY the 3-distinct-factor certificates 77 survive; with 3-factor + (1 factor x rank>=3 quadric) certificates 39 survive. So the
 0-factor certificates (344 cubics, 'smooth plane section') are essential for (E4). Answer to the coordinator's question: J (n**(kappa)
 = 0) pins only one coefficient of n**; the finite reduction comes from (E2) (n**|K_S proportional to a linear factor of the
 n**-FREE cubic c_S, or 0), i.e. exactly verify2's r3_exact data: per S the factor list + completeness certificate (3 factors:
 identity c_S = k l1 l2 l3; 1 factor: rank >= 3 of the cofactor quadric on ker l; 0 factors: a 3-dim rational section that is a smooth
 plane cubic, certified by 'all quartics lie in the Jacobian ideal' -- in Lean this needs a generic lemma 'smooth (Jacobian
 certificate) => no plane on which the cubic vanishes': a binary quadratic (normal derivative on the line) has a nontrivial zero over
 C, where the whole gradient vanishes, contradicting x^4, y^4, z^4 in the Jacobian ideal). Then a generated DFS per configuration with
 exact linear algebra on (m2, m3) and admissibility (E3); the 12 surviving families die by (E5) = stest_affine with symbolic
 parameters and a finite case split. Multi-round project; R31Hyp stays an explicit hypothesis meanwhile.
STATUS 01:13: R31 groundwork r8_2.txt: quad_poly_ne, three_factor_plane (a product of three linear forms vanishing on ker n forces one factor to vanish on ker n; proof via Polynomial.funext on x1 + s(x2 + s x3)) -- the 3-factor completeness step of (E4). Appended to R10s_slim.lean (window-3 file 2) for a first compile.
STATUS 01:15: round-8 report sent (window 3 not yet run).
STATUS 01:17: R31 groundwork r8_3.txt: cubT/gradT (cubic form from a trilinear array), cubT_expand, cubT_tangent, binary_quad_zero (a binary quadratic form has a nontrivial zero over C, via IsAlgClosed.isSquare + exists_quadratic_eq_zero), cubic_no_plane (a cubic with a Jacobian certificate x_k^4 = sum A_ki d_i g does not vanish on any 2-plane w1, w2 with a nonzero 2x2 minor) -- the 0-factor completeness lemma for (E4). Appended to R10s_slim.lean.
STATUS 01:20: R31 groundwork r8_4.txt: quadQ/gradQ, quadQ_expand, quadQ_tangent, quad_no_plane (a nondegenerate ternary quadric, certified by an inverse N with x = N grad q(x), does not vanish on a 2-plane) -- the 1-factor completeness lemma for (E4) (certificates checked with sympy). Appended to R10s_slim.lean. All three completeness types of verify2's r3_exact now have a generic Lean lemma (untested).
STATUS 01:20: round-8 report sent (SubagentHandback); window 3 not yet run.
STATUS 01:21: ROUND 9 started (targets: 1 repair from window-3 logs + plan full R8c compile, 2 dispatch-level generic lemma to shrink r6_9, 3 R31 setup + (E2) via stest_blk + generated DFS step by step, 4 scope GEN-tri / GEN-2 steps 3-4). Note: test stubs contain sorried stub declarations by design; only the full R8c compile with 0 sorry counts.
STATUS 01:28: TARGET 2 (dispatch-level generic lemma): r9_1.txt = status3 (3-way status split), ratio_eq (F_m in one step), stest_glob (stest_gen in GLOBAL coordinates: rows r1 r2 r3, points p q s, kappas; s_transfer inside). leanzbf/gen_t3d2.py regenerates t3_trans (same statement) as r6_9b.txt: one 9-way rcases per point (half the nesting), one-line F_m, compact certificates, passing leaves call stest_glob directly with the pattern data -> the 98 t3p_* lemmas (r6_7/r6_7g) are not needed any more. Sizes: r6_9b 669 KB replaces r6_9 611 KB + r6_7g 412 KB (net -354 KB); lemB prunes switched to 'simp [facts] at hD' (r7_1 286 -> 198 KB). New full candidate R9f.lean (r8_1, r6_1g, r9_1, r6_9b, new r7_1): 26385 lines, 1.57 MB (R8c 2.01, R7c 2.47), guard plain+namespace OK, no sorry. Window-3 list: R9d.lean (new lemB) + R12s_combo.lean (stest_gen, t1p slim, R31 lemmas, stest_glob, compact t3_trans).
STATUS 01:32: R31 step 1 r9_2.txt: ann23_exists -- for a pair (r2, r3) with dim X_23 = 3 and any two dual vectors phi1, phi2 there is a functional phi on rows (r2, r3) killing pi_23(L) and (1,1) (i.e. pi_23(L^)) with phi outside span(phi1, phi2): the fifth annihilator n** (phi1 = f2 - f3, phi2 = g* in the application). Appended to R12s_combo.lean.
STATUS: TARGET 4 SCOPE (GEN-tri / GEN-2 steps 3-4; stage2 R2-2, R2-3, sec. 7). Pieces and rough Lean sizes:
 (a) (SR) no single-row element in GEN (stage3) + column FK annihilators kappa'^j as objects (transpose of our row machinery; R3e
     has lemmaC_col, colsZero) ~300 lines.
 (b) (S2-d)/GEN-tri parametrisation of X_12 for a triangular pair: three lines V_3, V_4, V_5 in the plane, x(c)_ij = c_i zeta_j /
     K'_ij with sum c = 0, zeta from the column annihilators ~500 lines.
 (c) P_1 / P_2 / C4 identities from perm(u + x(c)) = perm(u) on L^: coefficient extraction of a polynomial in c restricted to the
     plane sum c = 0 (independence of c3c4, c3c5, c4c5 resp. the cubic monomials) ~400 lines (our perm-expansion helpers help).
 (d) GEN-tri |Sigma| constraints: |Sigma| = 5 (squarefree algebra), |Sigma| = 2 (addendum), |Sigma| = 3 => s != 0 ~600 lines.
 (e) GEN-2 Step 3 (|Sigma| = 3: perm(u[123;{p,d,e}]) = u_3p q_de(u_1,u_2), product vanishing on V_3 => q_de = 0, isotropy of the
     2x2 block image, U := {u in L^: u[12;de] = 0} has dim exactly 6, columns d, e vanish, contradiction with dim L cap {col d = 0}
     = 5) ~700 lines; Step 4 (|Sigma| = 4: B symmetric 4x4 zero diagonal, Phi = 0 on I^d of codim 2 => rank B = 2 => disjoint
     supports, annihilator shapes per Type I / II incl. the non-onto subcase) ~900 lines.
 Total ~3400 lines hand-written (partly generated for the case splits). Statements stage2 should re-derive EXACTLY for Lean (all
 side conditions, normalisations, signs): (1) (SR) with its precise hypothesis set; (2) the X_12 parametrisation incl. the scaling
 x_5 = x_3 + x_4 and the formula zeta_j := kappa'^j_4 p_j; (3) the exact coefficient formulas P_ii'(u) = perm(u with rows i,i'
 replaced by G_i, G_i') = 0 and the Laplace expansion P_45 = sum_T Q_45[T] perm(u[123;T^c]); (4) GEN-tri |Sigma| = 5 and |Sigma|
 = 2 as explicit linear-algebra statements (no 'squarefree algebra' shorthand); (5) GEN-2 Step 3's claim 'dim U = 6 exactly'
 with the per-type annihilator computation, and Step 4's 'rank B = 2 => B = a b^T + b a^T with disjoint supports' plus the
 per-type annihilator shapes of I^d and the non-onto subcase (Q_2 = {d} or Q_3 = {d}).
STATUS 01:33: R31 step 2 r9_3.txt: tauMap + stest_vanish -- the (E2) core: if the tau-image of blkL(S) lies in a subspace H of the 9-dim tau-space with dim H <= 3 (in the application: the 5 known relations + n**|S, rank 6), then perm(tau/kappa) vanishes on ALL of H (injectivity h0 + dimension => image = H, ell != 0 via ell_ne_of_small, then stest_blk). With the completeness lemmas (r8_2..r8_4) this turns into 'n**|K_S proportional to a linear factor of c_S'. Appended to R12s_combo.lean.
STATUS 01:36: R31 step 3 (symmetry reduction, first part) r9_4.txt: colPerm (column permutation as a linear map), colPerm_inv, colPerm_injective, pm_colPerm (permanent invariance), lev_colPerm (Lev transports), finrank_colPerm, rowsZeroS_colPerm. Still needed for the WLOG: ZF / PairII / TypeCl transport and the canonical-form choice. Appended to R12s_combo.lean (window-3 file 2, now with r9_2..r9_4).
STATUS 01:36: round-9 report sent (SubagentHandback); window 3 not yet run (expected 03:00-06:00).
STATUS 01:37: ROUND 10 started (targets: 1 window-3 repairs + window-4 decision R9f vs R8c, 2 R31 transport of ZF/PairII/TypeCl under colPerm + canonical permutation + generated per-(configuration,S) lemmas, 3 GEN-tri/GEN-2 pieces needing nothing new from stage2: (SR), column annihilators, X_12 parametrisation).
STATUS 01:54: R31 transport + canonical choice + GEN pieces written (untested): r10_1.txt (dotL_comp, typeCl_perm, PIIBody + piiBody_perm, pairII_perm, pairI_perm, vecPerm, zf_perm, exists_sort_perm via Tuple.sort), r10_3.txt (R31Canon = R31Hyp restricted to a MONOTONE class function f of the (r1,r2) Type II data (1 = Q-class, 2 = B-class, 0 = mixed) = stage2/verify2's sorted s12; cls_exists, r31_of_canon : R31Canon -> R31Hyp). Still open for the canonical form: eps_2 = +1 (complex conjugation transport, or generate the eps_2 = -1 half by conjugated data). r10_2.txt GEN: single_row_col / no_single_row ((SR) from zero-free column annihilators), fk_col, gen_col_ann, gen_no_single_row, dep3_of_finrank2, col3, gen_tri_param (X_12 = {x(c)}: kappa'^j_i x_ij = c_i zeta_j, c3 + c4 + c5 = 0, zeta_j = kappa'^j_4 x3_4j, for a triangular pair with the three row-zero witnesses). All three inserted into R12s_combo.lean before t3_trans (window-3 file 2; guard of the new blocks OK).
STATUS 02:00: r3_dump.py (= verify2 r3_exact + per-S record; logs leanzbf/r3_dump_p*.log, data r3_dump_p*.txt): over the 132 configurations with (E1) passed, the cubics have d = dim K_S = 4 except 38 with d = 5 (A0|S of rank 3; all of those have 1 factor). DFS restricted to d = 4 (r3_variant2.py d4only, log r3_variant_d4only.log): part 2 then has 7 survivors instead of 4, so the d = 5 triples ARE needed; stest_vanish (needs dim H <= 3) does not cover them. Fix designed: a generalised stest_vanish with dim H <= m, using an explicit n**-free L^-relation supported on [123; S^c] (exists exactly when rank A0|S = 3) to show dim blkL >= m and dim blockSpace >= m + 1. Eps normalisation: NOT needed -- as in the T1 lemmas, the per-configuration lemmas can take an abstract j with j*j = -1 (ratio on the mixed class = j * Q-ratio, and j3 = +-j2), so Q(i)-data from r3_exact is used with i -> j and identities closed by linear_combination with multiples of hj. r10_4.txt: three_factor_gen (any types), dot4, dot4_add, lin_minor (a linear form vanishing on ker z has all 2x2 minors with z zero = the DFS cut 'z proportional to l'), cub3_cases (3-factor completeness for d = 4). Inserted into R12s_combo.lean (14435 lines).
STATUS 02:01: correction to the previous line: 1169 certified cubics in the 132 configurations, d = 5 for 31 of them (not 38).
STATUS 02:19: R31 E-lemma machinery. r3_export.py (exact per-(config,S) data, r3_export_p*.txt). gen_e3.py -> r10_5.txt: 3-factor E-lemmas (e3_<s12>_<s13>_<p|m>_<S>: from 'perm(T(x)) = 0 on ker z' to 'z proportional to l_i' as 2x2 minors; abstract j, identity by linear_combination P * hj; 3 samples, ~1.3 KB each). r10_6.txt: sum3_idx, cubic_no_plane_idx (cubic_no_plane for any index pair), sec_no_kernel, cub0_zero (0-factor core: one smooth section + Jacobian certificate). r10_8.txt: qsec_one, qsec_no_kernel, cub1_cases (1-factor core: c = l q, q vanishes on ker z by a 4-point coefficient extraction, then the nondegenerate ternary quadric on ker l (three orderings, inverse certificates) gives the contradiction). gen_e0.py (0-factor generator; certificates large, section search). r3_minS.py: greedy minimal S sets keeping the DFS outcome; parts 0/1 keep 47/138 and 96/240 cubics (0-factor: 7 and 11). All new Lean blocks inserted into R12s_combo.lean (14685 lines); guard OK.
STATUS 02:27: round-10 report sent. Still running (own, 2 cores): r3_minS.py part 5 (log leanzbf/r3_minS_p5.log) and r3_minS2.py part 2 (drops d = 5 triples first, to see whether the generalised stest_vanish can be avoided; log leanzbf/r3_minS2_p2.log). gen_e0 sample run stopped (too slow at KEEP=6); retuned to MAXSEC=12, KEEP=2 and the refine now infers cf; gen_e1.py written, not yet run. Window-3 logs not in yet.
STATUS 02:28: ROUND 11 started (targets: 1 window-3 repairs + R9f/R8c decision when logs land ~03:30-05:00; 2 R31 setup lemma (n** + five known relations, (E1) from t2_partition), generalised stest_vanish for d = 5 unless r3_minS2 drops them, E-lemmas for kept triples via retuned gen_e3/gen_e1/gen_e0; 3 per-configuration DFS generator, one configuration end to end in a small test file first).
STATUS 02:40: r11_1.txt (generic: perm3_scale, Emap4, dotMap4, finrank_ker_dot4, h0_of_X123 (X_123 = 0 gives stest_vanish's h0), bridge (stest_vanish + lifting tau(blkL) = E(P tau) + z-kernel + weights -> the E-lemma hypothesis), cub3c (conditional 3-factor core), tau_blk_zero, compl_inr) and r11_2.txt = ONE configuration end to end, generated by leanzbf/gen_cfg.py (s12 01222, s13 22001, eps -1; greedy keeps S = 013, 024, 123): 3 E-lemmas e3_*, 3 wrappers w_* (context -> disjunction of explicit linear equations in M2, M3; per S: rr/cc via exists_equiv3, six restricted relations on blkL, hlift/hzk/hU certificates, bridge, E-lemma, minors -> equations), DFS lemma cfg_01222_22001_m (context + (E3) hypotheses hE3a/hE3b -> False; 15 leaves, each 'M3 in span(1,1_Q13)' or 'M2 in span(1,1_Q12)' by linear_combination). 37 KB. Both inserted into R12s_combo.lean before t3_trans (window 3 copies it at its turn); guard OK. r3_minS final: 453 of 1169 cubics kept (0/1/3-factor: 33/61/359). r3_minS2 (d = 5 first) still keeps d = 5 triples in 3 configurations of part 2: the generalised stest_vanish IS needed.
STATUS 02:51: setup pieces (untested, all in R12s_combo before t3_trans): r11_3 typeII_weights (from PIIBody data + class function f: kappa' = 1/(-1)/j times c*kappa on Q/B/mixed columns, j*j = -1, j independent of the column) and jsq_sign (j3 = j or -j). r11_4 pairDual, pairDual_apply/_single1/_single2, ann2_dep (for a pair (r,r') with dim X = 2 and dim L = 9 any four row-pair functionals killing L are dependent; via dualAnnihilator of the 7-dim image). r11_5 fin4_cases, dual_eq_pairDual, e3_final, e3_a, e3_b: the (E3) refutations. If M3 = alpha + beta 1_Q13, then (n** - alpha F3 - beta G13) is a (1,2)-functional; ann2_dep against F1, F2, G12 forces M2 = b + c 1_Q12 with beta = sg c ((E1): B13 = B12 (sg = -1) or complement (sg = +1)), and then n** = b (F2 - F3) + c (g* - K F3) lies in the span excluded by ann23_exists. e3_b is the same with the rows swapped. So the cfg-lemma hypotheses hE3a / hE3b are dischargeable from ann23_exists with phi1 = pairDual kappa2 (-kappa3), phi2 = g*_J.
STATUS 03:02: SETUP done as Lean text (untested, in R12s_combo before t3_trans): r11_6 (rhoMap, finrank_ker_rho, blk_finrank_rel, blockSpace_finrank_rel, ell_ne_gen, stest_vanish_gen = the generalised (E2) core for d = 5: dim H <= m, blkL >= m via an explicit relation rho supported on [123;S^c] with a nonzero entry, blockSpace >= m+1 when rho also kills J); r11_7 (fk_sum, dot_one_sum, typeII_two_values, ind_sum, typeII_ind (Type II relation in indicator form), e1_of_split ((E1) from t2_split: B13 = B12 or complement), fin3_zero_of, r31_setup: from the R31Canon data + X_123 = 0 it produces kappa3, f13, c2, c3, j, s (+-1), M2, M3 with zero-freeness, FK, both weight laws, both indicator relations, (E1), the n** relation and BOTH (E3) facts (via ann23_exists with phi1 = pairDual kappa2 (-kappa3), phi2 = g*_J, then e3_a / e3_b), plus nonempty f13 classes). r11_2 regenerated with inst_01222_22001_m (setup outputs + concrete f, f13, s -> cfg lemma -> False) and fin5_cases. So for this ONE configuration the chain R31Canon-data -> setup -> inst -> cfg -> False is complete as Lean text; missing for R31Hyp: the dispatch over f (6 monotone patterns) x f13 (E1-allowed) x s, the other 131 cfg lemmas (1-factor/0-factor/d = 5 triples in the generator), and (E5) for the 12 surviving configurations. R12s_combo now 15985 lines.
STATUS 03:06: gen_cfg.py extended to 1-factor and 0-factor triples (E-lemmas via gen_e1/gen_e0 with the h line rewritten to the EE/UU form; wrappers with z = 0 branches; DFS with 1-, 2- or 3-way splits); tested on 01222/10222/+1 (1-factor triple, 47.7 KB). 01222/10222/-1 fails: gen_e0 finds no smooth section among its small candidates (MAXSEC=12) -- widen the search. r3_minS2 (d = 5 triples dropped first) on all parts: exactly 3 configurations need a d = 5 triple (part 2: 00012 with 00102 / 01002 / 10002, eps +1); all others are covered by d = 4 triples, so the d = 5 bridge (Fin 5 basis + stest_vanish_gen) is needed only there. r11_8.txt: canon_vec, canon_patterns (monotone class function with all three values = one of the 6 canonical patterns; for the dispatch); inserted into R12s_combo (16022 lines). SIZE FLAG: the DFS route costs about 40 KB per configuration now (wrapper + E-lemma about 12 KB per kept triple, 453 kept triples); even with context bundling and shared literals the R31 part alone would be well above 1 MB, i.e. several times the 512 KiB cap. If the cap is binding, R31 needs a more compact argument (or certificates checked by a single generic lemma over data vectors).
STATUS 03:08: r11_9.txt (leanzbf/gen_dispatch.py): f13_cases_<P> for the 6 canonical patterns P: the (E1)-allowed class patterns of the (r1,r3) pair (14/14/14/8/8/8 = 66 per sign, 132 in all = verify2's count), by decide over 243 assignments. Inserted into R12s_combo (16131 lines). gen_e0: dense sections (incl. verify2's fallback) tried first; the failing 0-factor row now certifies (9 KB).
STATUS 03:10: r11_10.txt: R31CfgAll (= every explicit R3-1 configuration context with X_123 = 0 is contradictory; exactly the hypotheses of the inst lemmas plus the pattern facts) and r31_canon_of_cfgall / r31_of_cfgall : R31CfgAll -> R31Hyp (via r31_setup and r31_of_canon). So R31Hyp is reduced (as Lean text) to R31CfgAll, which is a finite case analysis: canon_patterns (6) x f13_cases (66 per sign) x s, each closed by an inst lemma (132 configurations; the 12 survivors need (E5)). Inserted into R12s_combo.
STATUS 03:14: window 3 reached my files: R9d compiling since 03:13 (leanzbf/R9d_w0313.log). R12s_combo (16202 lines) frozen now; last change: r11_2 regenerated (inst emitter fix: 'rw [X, hs]' was 'rw [X], hs'; batched simp in wrapper conversions; trivial equations dropped).
STATUS 03:16: r11_11.txt (groundwork for the 3 d = 5 configurations, NOT in any test file yet): dotn, dotn_add, lin_minor_n, qsec_one_n, cub1_cases_n (dimension-generic 1-factor core), Emapn, dotMapn, finrank_ker_dotn, bridge5 (stest_vanish_gen with m = 4, blkL >= 4 and blockSpace >= 5 from an explicit rho supported on [123;S^c] killing J). gen_all: 84 of the first 96+ killed configurations generated without failure so far (only the 3 d = 5 ones fail).
STATUS 03:17: r11_12.txt (groundwork, not in a test): rel_restrict1/2 = one generic step from a full relation on L to its restriction to the column triple S on blkL (replaces compl_inr + six tau_blk_zero + six linear_combination lines per wrapper). Size breakdown of a generated configuration (00012/01112/+1, 56 KB): wrappers 4 x 8.1 KB (binder 1.2, relations 1.9, hlift 1.3, hzk 0.8, hU 1.0, conversion 1.4), DFS 13.9 KB, inst 5 KB, E-lemmas 4.5 KB. Realistic compression (bundled context, rel_restrict, generic inst) about 2x -> ~3 MB for all configurations.
STATUS 03:19: round-11 report sent (handback). R9d still compiling (log empty), R12s_combo not started. gen_all: 116 of 120 killed configurations generated (21 + 95 so far, jobs still running); failures only the 3 d = 5 configurations.
STATUS 03:20: ROUND 12 started (targets: 1 window-3 repairs + R9f/R8c decision; 2 all 132 configurations: inst lemmas + R31CfgAll case split + d = 5 wrappers on bridge5; 3 (E5) for the 12 survivors via stest_affine; 4 small shape-test file: one configuration + setup + dispatch skeleton). 512 KiB cap ignored per Kevin's standing instruction.
STATUS 03:22: target 4: lean/zbf/R13s_shape.lean (leanzbf/mk_shape.py: R12s_combo with every theorem stubbed except r10_1, r10_3, r10_4, r11_1..r11_5, r11_7..r11_10; plus r12_1_shape.txt = the R31CfgAll dispatch with 132 leaves, 1 closed by inst_01222_22001_m, 131 sorry, and r31_hyp_proof : R31Hyp := r31_of_cfgall r31_cfgall). 5715 lines, 0.32 MB; guard OK apart from the stub sorries. leanzbf/gen_dispatch2.py also writes the full dispatch (r12_1_full.txt: 120 inst leaves + 12 e5 leaves).
STATUS 03:26: setup extended (r11_7: typeII_K = the L^-constant of a Type II relation, K*(1+j) = 1, from typeII_J; r31_setup now also outputs sum kappa_i = 1 for i = 1,2,3 and K12*(1+j) = 1, K13*(1+s*j) = 1; r11_10: R31CfgAll gains these five hypotheses -- needed for the J-part of the d = 5 relation rho). gen_dispatch2 updated (d = 5 and survivor leaves receive them). R13s_shape.lean rebuilt with leanzbf/mk_shape2.py (R12s_combo minus the old r10/r11 blocks, all else stubbed, current r10_1, r10_3, r10_4, r11_1..r11_5, r11_7..r11_10 + dispatch shape inserted before t3_trans): 5584 lines, guard OK apart from stub sorries. NOTE: the frozen R12s_combo in window 3 tests the OLD r11_7/r11_10 (without the K outputs).
STATUS 03:28: WINDOW 3 RESULT R9d.lean: lean exit code 0, 0 errors, 879.5 s, peak 4.7 GB (469 sorry warnings = the stubs by design). VERIFIED: r6_3 (iffA..iffE), r6_4 (repaired t1_IIi wrappers), r6_6, r7_1 lemB (simp-prune version), r7_2 f1_alg/f1_alg2, r7_3 bridges, r7_5 affine cores, r7_6, r7_4 T3F2 reductions, r7_7 (t3f2_proof, t1_proof : T1Hyp). R12s_combo compiling since 03:28 (log leanzbf/R12s_combo_w0328.log).
STATUS 03:31: COMPILED MAP (for verify2 / PROOF-MAP; leanzbf/compiled_map.py, tables leanzbf/compiled_map_R9f.txt and compiled_map_R8c.txt): the full candidate R9f.lean has 416 theorems and 71 defs. All 71 defs and 400 theorems occur with IDENTICAL text and a full proof, error-free, in a compiled file: 283 in R3e (round-3 full file), 68 in R6t_stub (window 2: r4_*, r5_*, r6_0, r6_1 t1p cores, r6_2, r6_5, r6_6, ...; r6_3/r6_4 counted only via R9d), 45 in R9d (window 3: r6_3, r6_4 incl. repaired t1_IIi, all r7_* incl. lemB, f1_alg/f1_alg2, bridges, a3p cores, t3f2_proof, t1_proof), 4 more only in R7s_t3 (window 2: T3Rest/T3Rest2 reductions). The 16 not yet compiled in full: stest_gen (r8_1), the 10 slim t1p_* (r6_1g), status3, ratio_eq, stest_glob (r9_1), the compact t3_trans (r6_9b), and the final theorem -- ALL are full in R12s_combo (compiling now). For R8c, 111 theorems would still be uncompiled (stest_gen, 10 slim t1p, 98 slim t3p, the newer-text lemB is not in R8c) -> R9f is the better window-4 file if R12s_combo passes.
STATUS 03:37: d = 5 done as generated Lean: gen_cfg5.py (explicit column equivalence exists_equiv5 (r12_2), the n**-free relation rho = combination of F1..G13 vanishing on S (here G13 - G12 for all three), hrho, hrel, hJ (via sum kappa_i = 1 and K12, K13 from typeII_K), bridge5, E-lemma via gen_e1n.py (dimension-generic cub1_cases_n, a 3-dim nondegenerate subspace of ker l found among pair sums of a kernel basis)); the 3 d = 5 configurations generate (33 KB each). All 120 killed configurations generated (6.0 MB, greedy subsets). r12_3: R31Surv P W eps (one explicit survivor configuration is contradictory); gen_dispatch2 mode surv -> r12_1_surv.txt: r31_cfgall_of_surv and r31_hyp_of_surv (12 R31Surv hypotheses) : R31Hyp. leanzbf/mk_r31.py -> lean/zbf/r12_r31_all.txt (all generic R31 blocks + 120 configurations + dispatch modulo E5): 6.16 MB, 70576 lines, no duplicate names, guard-clean text. verify2's size lever (r20/r3_minkill): generators now pick, among subsets of minimal size (2 or 3), the cheapest by certificate type (3-factor 1, 1-factor 3, 0-factor 7, d = 5 4); regeneration of all 120 running (gen_all3_A/B.log).
STATUS 03:44: WINDOW 3 R12s_combo (log still buffered at 77 KB, 40 errors so far, t3_trans part not reported yet). Errors found and FIXED in the block files: stest_gen (r8_1, also in R9f/R8c!: 'No goals' after field_simp -> drop ring; R9f.lean, R8c.lean, r9f_all.txt, r8c_all.txt patched), quad_poly_ne (r8_2: Polynomial.coeff unknown -> evaluation at 0, 1, -1), Equiv.Perm.apply_inv_self / inv_apply_self do not exist (r9_4, r10_1, r10_3 -> local perm_apply_inv' / perm_inv_apply' via Equiv.apply_symm_apply), fk_col (r10_2: whnf timeout -> explicit rowMap/colMap equation by funext rfl), dual_eq_pairDual (r11_5: Prod.fst_sum + Finset.sum_apply before simp), e3_final/e3_a/e3_b (r11_5: parse error, set literal broken over lines -> one line), finrank_ker_rho (r11_6: show-timeout -> simp [rhoMap]), f13_cases_* (r11_9: Decidable synthesis fails for 5 nested foralls -> fin_cases x5 + decide). Compiled WITHOUT error (first 6100 lines): r10_4..r11_4 incl. the whole one-configuration chain r11_2 (E-lemmas, wrappers via bridge, DFS cfg, inst), r10_2 GEN pieces except fk_col, r10_5..r10_8 cores, r11_1 bridge, r11_3 typeII_weights, r11_4 ann2_dep, r8_3, r8_4, r9_2, r9_3, r6_1g?, (pending: r9_1, r6_9b). setup extended with n**(J) = 0 (hJn) for (E5). Minimal subsets: 357 kept triples (verify2: 336; the 21 differences are configurations whose 2-subset uses a d = 5 triple, we use 3 d = 4 triples), total 5.26 MB (wrappers 2.85, cfg 0.69, inst 0.61, e0 0.60, e3 0.28, e1 0.23). R14s_shape.lean built from FIXED blocks (stub2: R3e + earlier blocks stubbed; full: r8_2, r9_4, r10_1..r10_8, r11_1, r11_3..r11_11, r12_0, r12_2, r12_3, four configurations (3-factor 01222/22001/-1, 0-factor 00012/01012/+1, 1-factor 01112/01102/-1, d = 5 00012/00102/+1), dispatch shape + r31_hyp_proof): 7701 lines, guard OK apart from stub sorries. R9f.lean (patched): guard result above.
STATUS 03:47: test files prepared from FIXED blocks: lean/zbf/R14s_shape.lean (7701 lines; pipeline shape: setup + dispatch skeleton + 4 configurations of all kinds) and lean/zbf/R150_cfg.lean .. R153_cfg.lean (30 configurations each + generic cores, 19-20k lines, 1.5-1.6 MB each; all 120 killed configurations between them). Guard OK apart from stub sorries. lean/zbf/r12_r31_all.txt rebuilt: 5.40 MB, 62006 lines (generic + 120 configurations + dispatch modulo the 12 survivors). Survivor families for (E5): leanzbf/surv_families.txt.
STATUS 03:47: round-12 report sent (handback) while R12s_combo is still compiling (log buffered at 77 KB; t3_trans result pending).
STATUS 03:48: ROUND 13 started (targets: 1 repairs from R12s_combo log + final compiled-map table; 2 (E5) per survivor via stest_affine; 3 wrapper bundling after R14s_shape compiles; 4 check the 21 extra triples against verify2/r20/r3_minkill.log).
STATUS 03:50: target 4 done (leanzbf/extra21_check.txt, chk_sub.py): each of the 21 configurations where verify2's minimal subset has 2 triples uses exactly ONE d = 5 triple (plus a d = 4 one); with our DFS semantics (gen_cfg5 data) all 21 verify2 subsets kill. Regenerated these 21 with gen_cfg5 (d = 5 allowed): 2 triples each, 689 KB instead of 909 KB. Now 336 kept triples (= verify2), cfg_out total 5.04 MB; r12_r31_all.txt rebuilt. 24 configurations now use a d = 5 wrapper (bridge5), so R14s_shape's d = 5 configuration is the critical test.
STATUS 03:51: gen_dispatch2 now reads from cfg_out which inst lemmas take the K arguments (24 configurations: the 3 d = 5-only ones + the 21 re-generated with a d = 5 triple). R14s_shape.lean REBUILT (7605 lines; 01222/22001/-1 now uses a d = 5 triple, so 2 of its 4 configurations test bridge5), R150..R153 rebuilt, r12_r31_all.txt 5.18 MB / 60719 lines. Guard OK apart from stub sorries.
STATUS 03:57: (E5) analysis (leanzbf/e5_an.py, e5_summary.txt): 11 of 12 survivors have a column triple S with a parameter-free cube defect (after eliminating the pivot y whose coefficient is a parameter difference; the pivot = 0 case is inadmissible, refuted by (E3) as checked for 01222/01222/-1); 00012/00012/-1 needs more (d = 5 triples or an n0 split). r13_1.txt (generic, untested): hat_zero_off, rel_hat1, rel_hat2 = the relations of blockSpace elements restricted to S with their J-values. Lean design for e5_<cfg> written into the handover. R12s_combo log now covers ~15000 of 16202 lines: 43 errors, all already fixed (the 3 new ones are the remaining f13_cases); no error inside t3_trans so far.
STATUS 03:57: round-13 report sent (handback) with R12s_combo still compiling (log at ~15000/16202 lines, 43 errors, all fixed in blocks, none in t3_trans so far).
STATUS 03:58: ROUND 14 started (targets: 1 final compiled map + window-4 go/no-go from R12s_combo; 2 (E5): r13_1 + one lemma per survivor, check pivot = 0 -> (E3) for all 11, 00012/00012/-1 via d = 5 triples or n0 split; 3 wrapper bundling after R14s_shape).
STATUS 03:59: WINDOW 3 RESULT R12s_combo.lean: lean exit code 1, 43 errors, 1796.7 s, peak 5.7 GB. ALL errors at lines <= 6143 (r8_1 stest_gen 'No goals', r8_2 quad_poly_ne, r9_4/r10_1/r10_3 nonexistent Equiv.Perm.apply_inv_self, r10_2 fk_col + gen_col_ann, r11_5 dual_eq_pairDual + e3_* parse, r11_6 finrank_ker_rho + 2 dependents, r11_9 the 6 f13_cases) -- all fixed in the block files. The compact t3_trans (r6_9b, lines 6187-16012) and T3Rest/T3Rest2/t3rest_of_t3rest2/t1_of_t3rest2 compiled WITHOUT error -> WINDOW 4 GO for the patched R9f (told the coordinator by SendMessage). FINAL COMPILED MAP (leanzbf/compiled_map_R9f.txt): 414 of the 416 theorems of R9f (and all 71 defs) have compiled in full, error-free, with identical text: R3e 283, R6t_stub 68, R9d 45, R12s_combo 14 (10 slim t1p_*, status3, ratio_eq, stest_glob, compact t3_trans), R7s_t3 4. Not yet: stest_gen (the patched text; the compiled copy failed only because field_simp already closed the goal before the removed ring) and the final theorem (only in the full file).
STATUS 04:00: coordinator confirms WINDOW 4 booked (LEANZBF_R9F after LEANZBF_R14SHAPE, ~06:00-07:30). R9f.lean frozen from now on: no in-place edits; any change goes to R9g.lean + notice.
STATUS 04:06: job e5_search_all (1 core, ulimit 2.5 GB, <= 30 min, log leanzbf/e5_search_all.log): constant-difference search over column triples S, free hat cells F and points x0, x1 in {0,1}^3 for the 11 remaining survivors. 01222/01222/-1 done: S (0,1,2), F (v00, v01, v10), x0 = 0, x1 = e1, perm difference -1, pivot det = p3 - p1, pivot = 0 refuted by hE3a.

## RESULT R14-1 (leanzbf, round 14): (E5) closed for all 12 survivors in generator form; R31Hyp assembled without hypotheses (untested in Lean)
- WINDOW 3: R12s_combo.lean exit 1, 43 errors, all at lines <= 6143 and all fixed in the blocks. The compact t3_trans (r6_9b) and the T3Rest chain are clean, so WINDOW 4 is GO for the patched R9f.lean (frozen; any change goes to R9g.lean).
- FINAL COMPILED MAP (leanzbf/compiled_map_R9f.txt). 414 of the 416 theorems and all 71 defs of R9f have compiled in full, with identical text: R3e 283, R6t_stub 68, R9d 45, R12s_combo 14, R7s_t3 4. Two have not: stest_gen (patched text) and the final theorem. Window 4 covers both.
- (E5) MECHANISM (leanzbf/e5_search.py, log e5_search_all.log). For EVERY one of the 12 survivors the search found the following, 00012/00012/-1 included:
  - a column triple S and three free cells F of the [123;S] block;
  - two points x0, x1 in {0,1}^3 of the lambda = 1 slice, with the other six cells solved from rows, K12, K13 and n** using the pivot det (linear in the family parameters);
  - perm(hat block at x1) - perm(hat block at x0) = delta * c2^-1 c3^-1 prod kappa1(S)^-1, where delta is a NONZERO CONSTANT: -1, j, (j-1)/2 or -(1+j)/2.
  The cube condition makes the permanent constant on the slice, which gives the contradiction. pivot = 0 makes the family E3-inadmissible for all 12, checked on Vmax: M3 in span(1, 1_Q13), so hE3a refutes it, for 10; M2 in span(1, 1_Q12), so hE3b refutes it, for 00012/01102/+1. Vmax is the unique maximal leaf and contains all others (verify2 r3_exact_leaves). 00012/00012/-1 needs neither d = 5 triples nor the n0 split: S = (0,3,4), F = (v00, v01, v10), x1 - x0 = e1, delta = -1, pivot p3 - p1, and pivot = 0 is refuted by hE3a. This matches stage2's hand (E5): family (a) uses S = {p in Q1, q in Q2, s in Q3}.
- LEAN (all generated text passes the generators' internal exact checks: hM certificates mod j^2+1, a Groebner certificate mod (j^2+1, q*q^-1-1), and the leaf combinations):
  - lean/zbf/r14_1.txt: stest_const (perm constant, from stest_affine), perm3_of_eq, stest_const_eval (expanded form).
  - leanzbf/gen_e5.py -> leanzbf/e5_out/<tag>.txt, 12 lemmas e5_<tag>, 11-17 KB each. Hypotheses: cfg context, hJn, parameters p with p_K = pivot, the six values M2/M3 on S, and hq : p_K <> 0. The proof uses exists_equiv3/5, h0_of_X123, rel_hat1/rel_hat2 (r13_1), hM from linear_combination, hy0/hy1 (div_eq_mul_inv, mul_inv, j^-1 = -j), stest_const_eval, and a key linear_combination with -hc, hj and hqi.
  - leanzbf/gen_surv.py (a patch of gen_cfg5) -> leanzbf/surv_out/<tag>.txt. Each survivor DFS lemma closes its surviving leaves with by_cases on the pivot: the E3 leaf when pivot = 0, otherwise e5_<tag> with p := an explicit left inverse of the family. Each file also contains inst_<tag> (with hJn) and surv_<tag> : R31Surv P W eps.
  - lean/zbf/r16_final.txt: theorem r31_hyp_full : R31Hyp := r31_hyp_of_surv surv_... (12).
- TEST FILES (compile only in a window): lean/zbf/R15e5.lean (R14s_shape stubbed + r13_1 + r14_1 + 12 e5 lemmas, 447 KB) and R16surv.lean (adds surv_out + r12_1_surv_stub + r16_final).
STATUS 04:21: (E5): all 12 survivors have a constant-difference certificate; pivot = 0 is (E3)-refuted for all 12. e5_<tag> lemmas generated (leanzbf/e5_out, 196 KB). Survivor DFS generator gen_surv.py running (job surv_gen_all, 1 core, log leanzbf/surv_gen_all.log); R15e5.lean test file built (not compiled: needs a window).
STATUS 05:17: R14s_shape (05:05-05:11): exit 1, 101 errors, all at 4859:87 (f13_cases_00012: fin_cases + decide cannot synthesize Decidable for the big proposition); Lean then STOPPED (maxErrors 100), so lines > 4859 are untested. R9f has no fin_cases / f13_cases -> R9F unaffected, no R9g (told coordinator). Fix: rcases fin3_cases x5 + revert + simp +decide (r11_9, r12_r31_all, gen_dispatch.py); new shape file lean/zbf/R14t_shape.lean. window_files.txt -> R14t_shape.lean, R16surv.lean.
STATUS 05:17: round-14 final report sent (SubagentHandback).
STATUS 05:18: coordinator: R14t_shape queued before R9F (then R15e5, R16surv). Answer: drop R15e5, since R16surv contains it in full (same stubbed base, same r13_1/r14_1/e5_out, placed before surv_out), so any error in an e5 lemma shows up in R16surv at the same place.
STATUS 05:23: round 15. (1) A pool-sized Lean test is impossible: every leancheck imports Mathlib; R14s_shape with ALL theorems stubbed peaked at 5.8 GB. Built lean/zbf/R17lint.lean (R14t_shape stubbed + r13_1 + r14_1 + r15_1 + ONE survivor 01222/01222/-1: e5 lemma, DFS/inst/surv; 320 KB; tests every new construct). Static lint: all Mathlib names used exist in this Mathlib (inv_neg, mul_inv, inv_one, eq_inv_of_mul_eq_one_right, mul_inv_cancel0, inv_ne_zero, Matrix.cons_val_two/three/four, Fin.sum_univ_three/five); the e5 signatures match all 38 survivor call sites (params, pivot position, 6 hm args, hq). (2) Bundling design: 370 used column triples have only 68 local patterns (f|S, f13|S, eps) -> shared pattern wrappers (generic columns, inst-form context) -> no per-config wrappers, no inst layer. r15_1.txt: blk_zero_mem, rel_blk1, rel_blk2 (blkL relations via rel_hat on (0,t)).

## ROUND 15 (leanzbf): wrapper bundling = shared PATTERN WRAPPERS (design + prototype; untested in Lean)
- Observation (leanzbf/patterns.txt): the 370 column triples used (336 in killed configurations, 34 in survivors) have only
  68 local patterns (f|S, f13|S, eps): 64 with d = 4 and 4 with d = 5. The slice relations (rows, K12|S, K13|S), the weights
  u = 1/w and hence the cubic, the E-lemma and the bridge data depend only on the pattern; the exported E bases of different
  instances differ only by a choice of basis. The branch conditions (n**|K_S proportional to a factor) do not depend on that choice, so
  every configuration's DFS still closes with the representative's data (checked by rerunning the DFS).
- Lean design:
  (a) r15_1.txt: blk_zero_mem, rel_blk1, rel_blk2 (the restricted relations on blkL, from rel_hat1/2 at (0, t)).
  (b) leanzbf/gen_pat.py writes pat_out/pw_all.txt: for each d = 4 pattern, the E-lemma pe<typ>_<pat> (renamed from the
      representative) and pw_<pat>, which is generic in the columns S0 S1 S2 (exists_equiv3 with distinctness hypotheses).
      Its context is the inst form (generic f, f13, s, hw2, hw3, hG12, hG13, hn) plus the values f S_k and f13 S_k and
      s = eps. Inside: weight facts from (hw2 S_k).x, indicator facts by `rw [hc_k, ha_k] <;> rfl`, the relations from
      rel_blk1/2, then hlift, hzk, hU and bridge as before. 64 patterns, 0.80 MB (E-lemmas included).
  (c) leanzbf/gen_cfgp.py writes cfgp_out/<tag>.txt: ONLY inst_<tag>, with the same name and signature, so the dispatch is
      unchanged. Its body is the fv/gv facts, the explicit forms of hE3a/hE3b, one pw_ call per kept triple (column
      numerals, `by decide` distinctness, fv/gv facts, hs) and the DFS. Configurations whose minimal subset needs a d = 5
      triple are refused and stay on gen_cfg5. Example: 01222/22001/-1 drops from about 40 KB to 7 KB.
- Expected effect: the per-configuration wrappers (2.73 MB), E-lemmas (1.05 MB) and the inst conversion layer go away, replaced by
  0.80 MB of shared patterns plus about 7 KB per configuration.
STATUS 05:30: round 15: pattern-wrapper prototype written (gen_pat.py: 64 d = 4 patterns, 0.80 MB; gen_cfgp.py: bundled inst_<tag>, 01222/22001/-1 = 7 KB). Job cfgp_all (all 120 configurations, 1 core, log leanzbf/cfgp_all.log) running.
- PROTOTYPE RESULTS (05:35 UTC; Python-side exact checks pass; Lean untested):
  - gen_cfgp: 117 of 120 killed configurations bundled (cfgp_out, 986 KB, about 8.4 KB each). Refused (they need a d = 5 triple):
    00012/00102/+1, 00012/01002/+1, 00012/10002/+1, which keep their gen_cfg5 files. cfgb_out = merged (1.08 MB).
  - gen_survp: the 12 survivors bundled (survp_out, 209 KB instead of 590 KB). Their inst_<tag> derives the explicit
    forms (hw2x, hw3x, hg12x, hg13x, hK12x, hK13x) once, for the e5 call.
  - gen_dispatch2 now takes CFGDIR (default cfg_out); r12_1_surv_b.txt = the dispatch over cfgb_out (120 inst leaves, only 3 with K args).
  - lean/zbf/r12_r31_bund.txt (mk_r31b.py) = the COMPLETE bundled R3-1 block. It holds the generic cores, r13_1/r14_1/r15_1, the
    pattern lemmas, cfgb_out, e5_out, survp_out, r12_1_surv_b and r16_final (r31_hyp_full : R31Hyp): 2.44 MB, 26954 lines.
    For comparison, the unbundled r12_r31_all.txt was 5.18 MB WITHOUT the survivors.
  - Test files: R17lint.lean (now 391 KB) adds r15_pat_test (two patterns + bundled instp_01222_22001_m) and r15_pat_test2
    (two patterns + bundled instp/survp_01222_01222_m) at the END. R19bund.lean (2.58 MB) = R14t_shape stubbed (duplicates
    dropped, mk_bund.py) + the full bundled R3-1 content, i.e. the decisive R3-1 test.
STATUS 05:35: bundling prototype complete. 117/120 configurations + 12 survivors bundled; full bundled R3-1 block r12_r31_bund.txt 2.44 MB (incl. survivors and r31_hyp_full); test files R17lint (391 KB, now includes pattern tests) and R19bund (2.58 MB, full bundled R3-1). Proposed: R19bund in place of R16surv once R14t_shape and R17lint pass.
STATUS 05:35: coordinator: R17lint box 30 min; LEANZBF_R19BUND (90 min, log leanzbf/R19bund_x.log) takes R16surv's slot after R9F; R16surv demoted to LOW_. Plan: when R14t_shape_x.log / R17lint_x.log land, repair generators and rebuild R19bund (mk_r31b + mk_bund) before its turn, or ask to hold it.
STATUS 07:16: coordinator: upstream lemmas may be COPIED (not imported). My survey of the 43 upstream Outside/L_gct_*.lean (main statements): none covers an uncompiled piece of ours (the R3-1 configurations / (E5) are configuration-specific; R9f is 414/416 compiled already). Loosely related: L_gct_111 (sum of row-space dims <= n-1, cf. our lemmaC/single_row_SR), L_gct_142 (even-e_k-vanishing subspace has dim <= 1), L_gct_110 (perm identity on L1 + L2 with disjoint blocks), L_gct_120/121 (rank-one perturbations), L_gct_151-153 (bilinear-form dimension bounds). Waiting for verify2's hit list.
STATUS 07:40: R14t_shape (07:31-07:38): 7 errors, whole file checked; f13_cases fix works; r11_10, r11_11 (but one line), r12_2/r12_3, the 4 configurations incl. d = 5, dispatch shape all compile. FIXED: (a) 6x single-equation branches emitted as anonymous constructor <by linear_combination q0> on an Eq goal -> now (by ...) (generators gen_cfg5, gen_surv, gen_pat fixed; 284 occurrences patched in pat_out, cfg_out, cfgb_out, surv_out, cfg_out_d5alt); (b) omega at r11_11 bridge5: ell_ne_gen ran omega while L was still a metavariable -> ell_ne_gen (L := L). Rebuilt r12_r31_bund.txt (2.44 MB), R19bund.lean (2.58 MB) and R16surv.lean. R17lint (compiling since 07:38) still has the old single-item form in its 4 pattern lemmas if they contain single-equation branches (expected error, already fixed for R19bund).
STATUS 07:45: R17lint (07:38-07:43): 2 errors, everything else compiled: e5_01222_01222_m (hM, hy cell proofs, the key linear_combination), the old survivor pipeline, 4 pattern wrappers (3 x typ 3, 1 x typ 1) with E-lemmas, bundled instp_01222_22001_m and bundled instp/survp_01222_01222_m. FIXED: (1) perm3_of_eq (r14_1, unused): simp only closed the goal before ring -> lemma removed; (2) e5 'have hd : (-1) <> 0' elaborated in Z -> '(delta : C) <> 0' (gen_e5 + 12 e5_out files). Rebuilt r12_r31_bund.txt, R19bund.lean (2.58 MB), R16surv.lean.

## FINAL (work aborted by Kevin)
- R9f.lean (patched) is frozen and not compiled as a whole; 414/416 of its theorems have compiled in full elsewhere.
- R19bund.lean (full bundled R3-1 down to r31_hyp_full) is rebuilt with all R14t_shape/R17lint fixes and not compiled.
- Generators and file list: handover/HANDOVER-leanzbf.md, section "FINAL STATE".
STATUS 08:04: STOPPED 08:04 UTC
