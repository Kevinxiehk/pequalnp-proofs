# HANDOVER-leanzbf (L-gct-210, role leanzbf) -- round 4 update written 2026-11-23 ~21:45 UTC (Kevin's machine); round-3 text below

## 0000000000000. FINAL STATE (work ABORTED by Kevin; read first)
- No jobs running. Nothing compiled after R17lint (07:43 UTC).
- Zero-block / T1 chain: lean/zbf/R9f.lean, the patched version (stest_gen without the trailing ring). FROZEN and NOT yet
  compiled as a whole (window 4 never ran). 414 of its 416 theorems have compiled in full elsewhere
  (leanzbf/compiled_map_R9f.txt); missing are stest_gen (patched) and the final theorem.
- R3-1 (bundled): lean/zbf/r12_r31_bund.txt (2.44 MB) is the full block, with generic cores, r13_1/r14_1/r15_1, the 64 pattern
  lemmas, cfgb_out (117 gen_cfgp + 3 gen_cfg5), e5_out, survp_out, r12_1_surv_b and r16_final (r31_hyp_full : R31Hyp).
  Its test lean/zbf/R19bund.lean (2.58 MB) is rebuilt with every fix from R14t_shape and R17lint and NOT yet compiled.
  The fixes:
  - single-equation branches emitted as `(by ...)`;
  - `ell_ne_gen (L := L)` in r11_11;
  - perm3_of_eq removed from r14_1;
  - `have hd : (delta : C) ne 0` in the e5 lemmas.
- Compiled confirmations:
  - R14t_shape (7 errors, all fixed): the R3-1 machinery, the dispatch shape and the example configurations.
  - R17lint (2 errors, both fixed): an e5 lemma, the old and bundled survivor, 4 pattern wrappers and a bundled configuration.
- Generators (leanzbf/):
  - (E5): e5_search.py, gen_e5.py.
  - Old pipeline: gen_cfg5.py, gen_surv.py.
  - Bundled: gen_pat.py (pattern wrappers), gen_cfgp.py (configurations), gen_survp.py (survivors), gen_dispatch2.py
    (CFGDIR), mk_r31b.py (block), mk_bund.py / mk_e5test.py (test files).
  - Batch scripts: e5_gen_all.sh, surv_gen_all.sh, cfgp_all.sh, survp_all.sh.
- To finish: compile R19bund, then build the final file = R9f (or R9g) chain plus r12_r31_bund with r31_hyp_full in place of
  the R31Hyp hypothesis, then run the guard.

## 000000000000. ROUND 15 STATE (read first; ~05:30 UTC)
- Queue (big slot, in order): TrK0p rerun, FLq2, R14t_shape (log leanzbf/R14t_shape_x.log), R17lint (leanzbf/R17lint_x.log),
  rows SMC5P/SMC4P, R9F (leanzbf/R9f_window4.log), R16surv. R15e5 was dropped.
- R17lint.lean is R14t_shape stubbed plus FULL r13_1, r14_1, r15_1, the e5 lemma and survivor file for 01222/01222/-1, and
  at the END r15_pat_test.txt. That block holds pattern lemmas pe3_012_220_m, pw_012_220_m, pe3_022_201_m, pw_022_201_m and the
  bundled consumer instp_01222_22001_m. It sits last, so errors in it cannot mask the e5/survivor results before it.
- Bundling: see NOTES round 15. leanzbf/patterns.txt, gen_pat.py (pat_out/pw_all.txt), gen_cfgp.py (cfgp_out/,
  batch cfgp_all.sh). Configurations that are REFUSED need d = 5 triples and stay on gen_cfg5. Survivors still use
  gen_surv; to bundle them, give the survivor inst the explicit-form conversions (as the old inst does) plus pw calls.
- Static lint done: every Mathlib name used exists in this Mathlib, and the e5 signatures match all 38 survivor call sites.
- Bundled pipeline (05:35): cfgb_out (117 gen_cfgp + 3 gen_cfg5), survp_out (gen_survp), r12_1_surv_b (CFGDIR=cfgb_out
  gen_dispatch2.py surv ...), r12_r31_bund.txt (mk_r31b.py) = the full R3-1 block, R19bund.lean (mk_bund.py) = its test.
  If R17lint fails in a pattern lemma, fix gen_pat.py (shared code, so one fix covers all 64 patterns), rerun gen_pat, rebuild
  (mk_r31b + mk_bund). If it fails in instp, fix gen_cfgp/gen_survp and rerun cfgp_all.sh/survp_all.sh.

## 00000000000. ROUND 14 STATE (read first; ~04:30 UTC)
- WINDOW 3 done. R12s_combo: exit 1, 43 errors, all at lines <= 6143 and all fixed in the blocks; r6_9b (compact t3_trans)
  is clean. WINDOW 4 = LEANZBF_R9F (lean/zbf/R9f.lean, patched, FROZEN: write R9g.lean for any change and tell the
  coordinator), log leanzbf/R9f_window4.log, which ends with "== LEAN SUMMARY". It runs after LEANZBF_R14SHAPE, roughly
  06:00-07:30 UTC. Final compiled map: leanzbf/compiled_map_R9f.txt (414/416 theorems; missing stest_gen (patched) and
  the final theorem).
- (E5) is solved in generator form for all 12 survivors (RESULT R14-1 in NOTES):
  - leanzbf/e5_search.py: the constant-difference search (S, free cells F, points x0/x1). Log: e5_search_all.log, plus
    e5s_01222_01222_m.log for 01222/01222/-1.
  - leanzbf/gen_e5.py: writes e5_out/<tag>.txt, the lemma e5_<tag>. Usage:
    `python3 -I gen_e5.py s12 s13 eps S F x0 x1 OUT`. Batch script: e5_gen_all.sh.
  - leanzbf/gen_surv.py: survivor DFS lemmas, writes surv_out/<tag>.txt (e3_/w_/cfg_/inst_/surv_<tag>). Batch script:
    surv_gen_all.sh. Each surviving leaf becomes `by_cases hq : pivot = 0`, with the E3 leaf if it is 0 and e5_<tag>
    otherwise.
  - Generic Lean blocks: r13_1 (rel_hat1/2), r14_1 (stest_const, stest_const_eval), r12_1_surv_stub (r31_cfgall_of_surv
    as a sorry stub plus r31_hyp_of_surv), r16_final (r31_hyp_full : R31Hyp).
- Test files (NOT compiled yet; leanzbf/window_files.txt now lists them):
  - R15e5.lean: R14s_shape stubbed, plus r13_1, r14_1 and the 12 e5 lemmas.
  - R16surv.lean: R15e5 plus surv_out, the dispatch stub and r16_final.
  Expected fragile spots:
  - the hy0/hy1 `simp only [div_eq_mul_inv, mul_inv, hJ, inv_neg, inv_one, hw..] <;> ring` cell proofs;
  - Matrix.cons_val_three / cons_val_four;
  - `simpa only [dotL_apply, rowMap_apply, mul_comm]` for the row relations;
  - linear_combination sizes in `key`, which run at maxHeartbeats 4000000.
- For the full file:
  - replace r12_1_surv_stub with the real r12_1_surv;
  - add cfg_out, the R31 generic blocks, e5_out, surv_out, r12_1_surv and r16_final;
  - the T3/T1 chain must use r31_hyp_full where it currently takes R31Hyp as a hypothesis.
- R14s_shape (05:05-05:11): 101 errors, all in f13_cases (fin_cases + decide: Decidable not synthesized); Lean stopped at
  maxErrors (100) at line 4859, so the rest is untested. Fixed (rcases fin3_cases x5 + revert + simp +decide) in r11_9,
  r12_r31_all, gen_dispatch.py; new shape file lean/zbf/R14t_shape.lean. Keep proofs from generating > 100 errors per file
  (maxErrors cannot be raised: only maxHeartbeats options are allowed).
- Wrapper bundling (target 3) waits for R14t_shape's log.

## 0000000000. ROUND 13 NOTES (~03:55 UTC)
- 21 extra triples resolved: verify2's 2-subsets each contain exactly one d = 5 triple (leanzbf/extra21_check.txt); these 21
  configurations are now generated with gen_cfg5 (2 triples each). 336 triples, cfg_out 5.04 MB, 24 configurations use
  bridge5. gen_dispatch2 detects K-argument inst lemmas from cfg_out. R14s_shape, R150..R153, r12_r31_all rebuilt.
- (E5) design (not implemented): for w in blockSpace (u = lambda J + t, zero on [123;S^c]) the weighted entries
  v_ik = kappa_i(S_k) * hat w (r_i, S_k) satisfy: row sums = lambda (FK + sum kappa_i = 1), G12|S(v) = lambda*K12',
  G13|S(v) = lambda*K13' (K' = explicit kappa sums, K'*(1+j) = 1 from typeII_K), n**|S(v) = 0 (hn + hJn). Solve the 6
  relations for 6 entries in terms of 3 free entries + lambda -> the hM of stest_affine (verified, r6_6); the pivot in the
  n** row is a family-parameter expression -> case split on it. zbf_ufd (cube statement, R3e) is what stest_affine uses.
  Then two points (x0, x1) on the lambda = 1 slice with different permanents (polynomial in the family parameters; stage2:
  delta_h != 0 -> vary a_1; delta_h = 0 -> vary c_1). Data: leanzbf/surv_families.txt (families in (M2|M3) coordinates).
- (E5) ANALYSIS DONE (leanzbf/e5_an.py, leanzbf/e5_summary.txt): on the lambda = 1 slice V0 + sum y_e E_e of Pi_S with the
  hyperplane n0 + z.y = 0 (z, n0 linear in the family parameters p), for 11 of the 12 survivors there is a column triple S
  where, after eliminating the pivot y (pivot coefficient = one parameter difference, e.g. p3 - p1), some free direction
  has a CONSTANT nonzero linear coefficient (e.g. (1-i)/2) and no square/cube term: two points differing only there give
  permanents differing by a nonzero constant for every family member. Pivot = 0 is the inadmissible case (e.g. for
  01222/01222/-1, p1 = p3 puts M3 in span(1, 1_Q13): refuted by hE3a). Remaining: 00012/00012/-1 (on its d = 4 triples
  either z = 0 or no constant direction) -- try d = 5 triples / the n0 = 0 vs != 0 split.
- Lean shape planned for one survivor lemma e5_<cfg>: stest_affine with k_ij = kappa_i(S_j) on the 3 free positions and
  kappa_i(S_j) * pivot on the 6 dependent ones (so hM has polynomial coefficients), relations on blockSpace from the new
  generic lemmas rel_hat1 / rel_hat2 / hat_zero_off (lean/zbf/r13_1.txt) with the J-values 1 (FK, sum kappa = 1), K12', K13'
  (typeII_K) and 0 (hJn); hperm via perm3_scale to the (v . u) form, where the difference is the constant above.

## 000000000. ROUND 12 STATE (read first; ~03:50 UTC)
- Window 3: R9d exit 0 (0 errors, 880 s, 4.7 GB). R12s_combo: 40 errors in the first 6100 lines (r10/r11 test blocks, r8_1, r8_2),
  t3_trans part pending at writing time. All errors fixed in the block files (see NOTES STATUS ~03:43): stest_gen 'No goals'
  (r8_1 -- ALSO in R9f/R8c; R9f.lean/R8c.lean/r9f_all.txt/r8c_all.txt patched, R9f guard OK, 0 sorry, 1.57 MB),
  quad_poly_ne, Equiv.Perm.apply_inv_self (does not exist -> perm_apply_inv' in r9_4), fk_col, dual_eq_pairDual, the
  e3_* set-literal parse error, finrank_ker_rho, f13_cases (fin_cases + decide).
- compiled map (leanzbf/compiled_map.py, tables compiled_map_R9f.txt / _R8c.txt): R9f = 416 theorems + 71 defs; all defs and
  400 theorems compiled in full somewhere; the other 16 (stest_gen, slim t1p_*, status3, ratio_eq, stest_glob, compact
  t3_trans, final theorem) are full in R12s_combo. Re-run compiled_map.py with the R12s_combo log path as argument.
- R31 status: all 120 killed configurations generated (leanzbf/cfg_out/, minimal-count then minimal-cost triple subsets,
  357 triples, 5.26 MB); d = 5 via gen_cfg5.py (bridge5, exists_equiv5 in r12_2, gen_e1n.py); setup outputs now include
  sum kappa_i = 1, K12/K13 (typeII_K) and n**(J) = 0 (hJn); R31CfgAll / R31Surv (r12_3) / dispatch (gen_dispatch2.py modes
  shape | full | surv) updated; lean/zbf/r12_r31_all.txt = everything modulo (E5) (rebuild with leanzbf/mk_r31.py after
  regenerating; it predates the hJn change and the minimal subsets).
- Next test: lean/zbf/R14s_shape.lean (stub2 build from FIXED blocks: four configurations of all four kinds + setup +
  dispatch with 128 sorry leaves + r31_hyp_proof). Then a split of r12_r31_all into window-sized files.
- (E5): survivor families in leanzbf/surv_families.txt (surv_an.py): conjugate survivors leave one family of dim 4 in
  (M2|M3), non-conjugate ones dim 6 (both include the known-functional directions). Plan: per survivor one lemma
  'M in family -> False' via stest_affine on stage2's S (parametrise Pi_S by 3 free entries + lambda using the L^-relations
  restricted to S, incl. n**(J) = 0 and K12, K13; two points whose permanents differ, with the delta_h = 0 / != 0 split).

## 00000000. ROUND 11 STATE (read first; ~03:10 UTC)
- Window 3: R12s_combo (copied at its turn, ~03:30-05:00) now carries everything from rounds 10-11, inserted before
  t3_trans: r10_1..r10_6, r10_8, r11_1 (bridge etc.), r11_2 (ONE configuration end to end + inst lemma + fin5_cases),
  r11_3 (typeII_weights, jsq_sign), r11_4 (pairDual, ann2_dep), r11_5 ((E3): dual_eq_pairDual, e3_final, e3_a, e3_b),
  r11_6 (generalised (E2) for d = 5: rhoMap, blk_finrank_rel, blockSpace_finrank_rel, ell_ne_gen, stest_vanish_gen),
  r11_7 (setup: fk_sum, dot_one_sum, typeII_two_values, ind_sum, typeII_ind, e1_of_split, fin3_zero_of, r31_setup).
  Backups: leanzbf/R12s_combo_pre_r10.bak, R12s_combo_pre_r11.bak. 15985 lines.
- R31 chain as Lean text: R31Canon data + X_123 = 0 --r31_setup--> generic context (kappa3, f13, c2, c3, j, s, M2, M3,
  weights, indicator relations, (E1), n** relation, both (E3) facts) --inst_<cfg>--> explicit context --cfg_<cfg>--> False
  (DFS over the kept triples; each triple: wrapper w_<cfg>_<S> = bridge (stest_vanish + lifting) + E-lemma -> linear
  equations in M2, M3; leaves refuted by (E3)). Done for ONE configuration (01222/22001/eps -1).
- Generator leanzbf/gen_cfg.py "<s12>" "<s13>" <eps> OUT: E-lemmas (3-factor own code; 1-factor via gen_e1.gen,
  0-factor via gen_e0.gen with the h line rewritten to the EE/UU matrix form), wrappers, DFS (greedy minimal triple set,
  0/1-factor dropped first), inst lemma. About 40 KB per configuration (too big; next: bundle the context hypotheses into
  one Prop def, share EE/PP/UU literals, drop the 9-case hlift by choosing identity positions).
- Later in round 11: r11_8 canon_patterns, r11_9 f13_cases_* (decide), r11_10 R31CfgAll + r31_of_cfgall (R31Hyp reduced to
  R31CfgAll); r11_11 (NOT in a test yet): dimension-generic 1-factor core (dotn, cub1_cases_n) + bridge5 for the 3 d = 5
  configurations. gen_all.py (chunks of 12): all killed configurations generate except the 3 d = 5 ones; outputs in
  leanzbf/cfg_out/ (about 50 KB each). R12s_combo frozen at 16202 lines when window 3 reached R9d (03:13).
- Still missing for R31Hyp: (1) dispatch lemma R31Canon -> by_contra X_123 -> r31_setup -> case split f (6 monotone
  patterns; prove by decide over vectors), f13 ((E1)-allowed, nonempty classes), s -> inst lemmas; (2) cfg lemmas for all
  132 configurations (d = 5 triples: bridge5 with Fin 5 basis + stest_vanish_gen + rho from A0|S, and dot5 versions of
  lin_minor / cub1_cases -- or remove d = 5 by a better greedy; r3_minS2 shows 3 configurations of part 2 need them);
  (3) (E5) for the 12 surviving configurations via stest_affine. Then r31_of_canon gives R31Hyp and s2_star applies.

## 0000000. ROUND 10 STATE (read first; ~02:25 UTC)
- Window 3 (expected 03:00-06:00): R9d.lean + R12s_combo.lean. R12s_combo now also carries ALL round-10 blocks, inserted
  before t3_trans so they compile early: r10_1 (colPerm transport: dotL_comp, typeCl_perm, PIIBody/pairII_iff/piiBody_perm,
  pairII_perm, pairI_perm, vecPerm, zf_perm, exists_sort_perm), r10_2 (GEN: single_row_col, no_single_row = (SR), fk_col,
  gen_col_ann, gen_no_single_row, dep3_of_finrank2, col3, gen_tri_param = the X_12 parametrisation), r10_3 (R31Canon,
  typeCl_disj, cls_exists, r31_of_canon : R31Canon -> R31Hyp), r10_4 (three_factor_gen, dot4, dot4_add, lin_minor,
  cub3_cases), r10_5 (3 generated 3-factor E-lemmas e3_*), r10_6 (sum3_idx, cubic_no_plane_idx, sec_no_kernel, cub0_zero),
  r10_8 (qsec_one, qsec_no_kernel, cub1_cases). Backup of the pre-round-10 file: leanzbf/R12s_combo_pre_r10.bak.
- Window-4 decision (after window-3 logs): R9f if r6_9b (compact t3_trans in R12s_combo) and R9d pass; else R8c.
- R31 status: canonical form = monotone class function of the (r1,r2) Type II data (sorted cells, as verify2's s12). NO
  conjugation needed for eps_2: per-configuration lemmas take an abstract j with j*j = -1 (Q(i) data with i -> j; identities
  closed by linear_combination P * hj). E-lemma = per (configuration, S) completeness statement on K_S (d = 4):
  hypothesis (z != 0 ->) "perm(T(x)) = 0 on ker z", conclusion z = 0 or z proportional to a factor (as 2x2 minors, the linear
  DFS cut). Generic cores: cub3_cases (3 factors), cub1_cases (1 factor; needs q, its polar Bq, a basis k0,k1,k2 of ker l,
  three orderings each with Q and inverse certificate N), cub0_zero (0 factors; one section b0,b1,b2 + Jacobian certificate
  y_k^4 = sum_m Q_km(y) d_m g, cubic_no_plane_idx handles any kernel direction).
- Generators: leanzbf/gen_e3.py (3-factor, works: r10_5 samples), leanzbf/gen_e0.py (0-factor; section search over small
  {0,+-1} sections, keeps the shortest of the first few smooth ones; certificates can be large). 1-factor generator: TODO.
  Data: leanzbf/r3_export.py -> r3_export_p0..5.txt (exact per-(config,S) data: E basis of K_S, factors, k, u weights).
- Volume reduction: leanzbf/r3_minS.py (greedy: drop S, preferring 0-factor ones, while the DFS outcome is unchanged):
  parts 0/1 keep 47/138 and 96/240 cubics, only 7 resp. 11 of them 0-factor. Use r3_minS_p*.txt to pick the S per config.
- d = 5 (31 cubics, rank A0|S = 3, all 1-factor): needed (DFS without them leaves 7 instead of 4 survivors in part 2).
  stest_vanish (dim H <= 3) does not cover them; needs the generalised version (dim H <= m, an explicit n**-free
  L^-relation supported on [123;S^c] gives dim blkL >= m and dim blockSpace >= m + 1). Check whether r3_minS keeps any.
- Still to build for R31Hyp: (1) setup lemma (n** via ann23_exists, the 5 known relations in tau-coordinates for the canonical
  configuration, (E1) via r4_1's t2_partition), (2) per-S lifting: tau(blkL) inside span of the K_S basis E (left inverse +
  hid-type certificate as in stest_gen), z_e = n**(E_e), stest_vanish -> E-lemma hypothesis, (3) E-lemmas for the kept S,
  (4) per-configuration DFS with leaf refutation via (E3) (m3 in span(1,1_Q13) or m2 in span(1,1_Q12) contradicts
  ann23_exists' phi not in span), (5) the 12 survivors: (E5) via stest_affine, (6) dispatch over f13 (150 cells x 2 signs).

## 000000. ROUND 9 STATE (read first; 01:35 UTC)
- Files: R9f.lean = current full candidate (mk9.py on r9f_all.txt: R3e + r4..r6_0 + r8_1 + r6_1g + r6_2..r6_6 + r9_1 + r6_9b + r7_*),
  1.57 MB. Older candidates R8c (2.01 MB, verified r6_9 + r6_7g) and R7c remain as fallbacks.
- Window-3 list: R9d.lean (all r7 + repaired t1_IIi), R12s_combo.lean (r8_1, r6_1g, r8_2..r8_4, r9_2, r9_3, r9_1, r6_9b).
  If r6_9b fails, R8c's route (verified r6_9 + slim r6_7g, or old r6_7) stays available.
- Generators new this round: gen_t3d2.py (compact t3_trans), gen_lemB.py updated (full simp prunes), gen_slim.py (slim t1p/t3p).
- R31 plan: r9_2 (n**), r9_3 (E2 core), r9_4 (column-permutation transport, part 1); next: ZF/PairII/TypeCl transport + canonical
  permutation choice, per-(configuration, S) generated lemmas from
  verify2/r3_exact.py data (K_S basis, c_S, factor list, certificates), DFS, (E5).

## 00000. ROUND 8 STATE (read first; 01:08 UTC)
- Target 2 done (untested): r8_1.txt stest_gen = ONE generic homogeneous S-test core lemma (data: relation matrix A, M, pi, pj,
  lambda certificates Lr/La with the identity hid checked at the call site by simp only + ring, weights W, point x0). gen_slim.py
  regenerates the 10 t1p_* and 98 t3p_* lemmas as slim instances with UNCHANGED signatures (r6_1g.txt, r6_7g.txt; self-check in
  gen_slim_chk.py). Full candidate R8c.lean (mk9.py on r8c_all.txt: R3e + r4..r6_0 + r8_1 + r6_1g + r6_2..r6_6 + r6_7g + r6_9 + r7_*):
  30467 lines, 2.01 MB. Remaining size hogs: r6_9 611 KB, r6_7g 412 KB, R3e 291 KB, r7_1 286 KB, r6_4 132 KB.
- Window-3 list: R9d.lean (all r7 + repaired t1_IIi), R10s_slim.lean (stest_gen + all slim instances). Fallback R9c.lean (old r6_7).
- R31 groundwork (all in R10s_slim, untested): r8_2 three_factor_plane, r8_3 cubic_no_plane (Jacobian certificate), r8_4
  quad_no_plane (inverse certificate) = the three completeness types of verify2's r3_exact. Next for R31: the R3-1 setup with n**,
  (E2) via stest_blk, a generated DFS per canonical configuration (verify2/r3_exact.py has the exact data; r3_variant.py shows the
  0-factor certificates are needed), (E5) via stest_affine with symbolic family parameters.
- Target 4 (GEN-tri, GEN-2 steps 3-4): stage2 R2-3 is a long hand proof (Laplace along two rows, isotropy of a 2x2 block,
  rank of a symmetric 4x4 B); not started.
- Target 3 (R31Hyp): see NOTES STATUS 01:04 and the r3_variant results; (E4) = finite DFS over the linear factors of the n**-free
  cubics c_S (verify2/r3_exact.py), certificates per cubic; (E5) = stest_affine with symbolic family parameters.

## 0000. ROUND 7 STATE (read first; 00:35 UTC)
- T1 is complete as Lean text: t1_proof : T1Hyp (r7_7) via t1_of_t3f2 t3f2_proof; chain T1Hyp <- T1Rest3 (r6_5) <- T3Rest (r6_9,
  t3_trans) <- T3Rest2 (r6_9, second row order) <- T3F2 (r7_4, lemB r7_1 + F1 bridges r7_3 with f1_alg/f1_alg2 r7_2) <- t3f2_proof
  (affine cores r7_5 + wrappers r7_7). Full candidate: lean/zbf/R7c.lean (old statement /\ T2Hyp /\ T2ppHyp /\ T1Hyp).
- Generators: gen_lemB.py (r7_1), gen_bridge.py (r7_3), gen_aff.py (r7_5), gen_aw.py (r7_7; reuses gen_bridge.py), mk9.py (R7c).
  Certificate checks: leanzbf/cert_chk.py, f2o_emit.py, lcfind.py (sympy, find_lc).
- Window 2 RESULT: R6t_stub.lean compiled with only 4 errors, all heartbeat timeouts inside t1_IIi (everything else of r4..r6_6
  and the 3 sample t3p lemmas compiled). Repairs: tauto side conditions -> iffA..iffE (r6_3) in gen_t1d.py, 4e7 heartbeats; full
  `simp [..] at e` contradictions -> `exact absurd e (mul_ne_zero ..)` in gen_t1d.py and gen_t3d.py; heartbeat limits on lemB (2e8),
  bridges/wrappers (8e6), t3rest2_of_t3f2 (4e6). Second window-2 file is R7s_t3.lean (old r6_9; log leanzbf/R7s_t3_w0036.log).
  Next window list (window_files.txt): R6r_t1IIi.lean (small t1_IIi re-test), R9s_all.lean (all r7 + r6_9).
- Window 2: R7s_t3.lean exit 0 (t3_trans + T3Rest/T3Rest2 VERIFIED); R6t_stub.lean: only t1_IIi failed (heartbeats) -> repaired.
- Window-3 list (window_files.txt): R9d.lean (all r7 + repaired t1_IIi; verified parts stubbed), R9c.lean (98 t3p_* lemmas).
  Older test files R9a/R9b/R9s_all/R8s_r7 are superseded. Full candidate R7c.lean (38080 lines, 2.5 MB): a full compile probably
  needs 50-70 min (t3_trans alone ~15 min, R6t_stub-type parts ~15 min, 98 core lemmas, lemB) -- tell the coordinator before
  putting it into a 60-min window; splitting is not possible (one file), so shrinking/speeding is the lever.
- Remaining for the gap: S2* via R31Hyp (deferred; its last step (E5) is a cube-defect computation that fits stest_affine, but (E4)
  is a parametric elimination over the unknown fifth annihilator n**), and the rest of the GEN chain; size (R7c 2.5 MB vs 512 KiB).
- Shrink idea (target 4, not done): one generic homogeneous core lemma taking the relation/M/lambda matrices as data with a
  decidable coefficient identity; per-pattern lemmas would keep only hy/hperm (field_simp) parts.

## 000. ROUND 6 STATE (read first; 23:50 UTC)
- See NOTES-leanzbf.md ROUND 6 RESULT. Nothing of rounds 4-6 is compiled except as reported for window 1.
- Files (lean/zbf/): R6t_stub.lean = window-2 file 1 (r4..r6_6 + 3 sample t3p lemmas r6_7s); R7s_t3.lean = window-2 file 2
  (leanzbf/stub2.py: all else stubbed, full proof of t3_trans + T3Rest/T3Rest2; replaced R4c.lean, still available);
  R6a.lean = full file without r6_7/r6_9 (650 KB, final conjunct T1Rest3 -> T1Hyp, mk6.py);
  R6b.lean = full file with everything (2.10 MB, final conjunct T3Rest2 -> T1Hyp, mk7.py);
  R7t_stub.lean = window-3 candidate (R6t_stub + r6_7 statements with sorry + r6_9, 1.21 MB) to test the (II,II,II) dispatch.
- Generators (rerun after any interface change; they overwrite r6_1 / r6_4 / r6_7 / r6_9): leanzbf/gen_t1p.py, gen_t1d.py
  (gen_t1d_v1.py = pre-s_transfer version), gen_t3p.py, gen_t3d.py. stub.py builds test stubs.
- After window 2: repair from the R6t_stub log; a systematic error in a t1p_* lemma is fixed in gen_t1p.py AND gen_t3p.py, an error
  in a dispatch leaf in gen_t1d.py AND gen_t3d.py (same idioms: side_cancel / mul_right_cancel₀, simp [hc, ...] at e, s_transfer).
- (II,II,II) status: r6_7 (98 core lemmas t3p_*, all used), r6_9 = t3_trans (any pair-12 transversal of an all-Type-II triple with X_123 = 0
  has one of 26 consistent non-passing patterns; 305 leaves; certificates checked numerically by the generator), T3Rest /
  t1_of_t3rest, T3Rest2 / t1_of_t3rest2 (second row order). T3Rest2's configurations are exactly F1 + F2 (780 label configurations
  up to eps). Remaining: Lemma B (class structure of F1/F2 from the two transversal hypotheses; only 4 patterns occur on F,
  leanzbf/t1_iii9.log), then F1 by typeII_J (r6_6) + t1p_alg (R3e) and F2 by an affine S-test (perm_3 = k ell^3 on Pi_S, ell != 0
  direction; new lemma next to stest_lift3).
- Lemma B sizing (leanzbf/lemB_size.py, exact patterns): a generated tree over the statuses of p, q, s (canonical transversal), then
  the two remaining columns x, y (12-, 13-, 23-status each), pruned by ratio inconsistency (certificates as in t3_trans) and by
  'some transversal passes' (apply the T3Rest2 hypothesis to that transversal; every one of the 26 disjuncts contradicts a
  known status) has 26 nodes after p, q, s, 102 after x and only 46 complete leaves = the F configurations; ~3300 pruned nodes
  (x <-> y symmetry halves it). Leaves then need F1 (typeII_J + t1p_alg) and F2 (affine S-test) with explicit classes.
- stest_affine is WRITTEN (r6_6, in R6t_stub): the cube test as a lemma. F2 route: R3e's zbf_ufd gives the cube statement on blockSpace L r c (pairs (c, t), t in L, 3x2 block of
  cJ + t zero): blk3(hat w) = blk3(hat u0) * w.1^3 for u0 with u0.1 = 1. Needed: stest_affine, modelled on stest_lift3: on
  blockSpace the rows-1-3 entries tau on S satisfy 6 relations with right-hand sides (c, c, c, c G12, c G13, c G23), where
  G = sum_B κ + sum_Q κ' = c/(omega + c) = (1 -+ i)/2 is typeII_J (r6_6); with h0 (X_123 = 0) and dim (C x L) = 10 the map to the
  4-dim affine solution space is bijective; then two points u0 (c = 1) and u0 + v (c = 0 direction) with different perm3 give
  False. F1: typeII_J for the three pairs = the three J-equations of t1p_alg (R3e); the other three are the row sums.
- Heartbeats: generated core lemmas carry set_option maxHeartbeats 1000000 in, t1_III 2e6, t1_IIi 1e7, t3_trans 5e7 (the guard
  allows exactly this per-declaration form; leanzbf/guardcheck.mjs runs the guard's plain + own-namespace checks on a file).
- Size: R6b is 4.1x the 512 KiB cap (Kevin: ignore for now). Biggest items: r6_7 (0.83 MB) and r6_9 (0.6 MB); both could shrink by a
  generic S-test core lemma taking the rational data as arguments.
- R31Hyp (target 4) not started: verify2's certificates are 1320 cubics incl. irreducibility via smooth plane sections -- large.

## 00. ROUND 5 STATE (read first; 22:46 UTC)
- New blocks lean/zbf/r5_1..r5_6 (not yet compiled): stest_lift3 (generic K_S lift: 3 parameters + one exact point with perm != 0
  => False), lam3; t1_iii_local + t1_III (T1 for three Type I pairs; uniform column triple from the (C12,C13) type square,
  comb_pqs; C23 pattern from ratio consistency, two_val_*, xor_nonconst; local relations by pair_local); corner_sq, sq_ratio,
  sq_contra, typeI_ratio, t1_one_II (exactly one Type II pair is impossible); T1Rest, T1Rest2, t1_of_rest, t1rest_of_rest2,
  t1_of_rest2 : T1Rest2 -> T1Hyp (T1 reduced to configurations with >= 2 Type II pairs).
- Files: R5a.lean (R4c + r5_1..r5_6, 8447 lines, guard OK; final theorem adds (T1Rest2 -> T1Hyp)), R5t_stub.lean (stub of all new
  blocks incl. r4_7 GEN-lin), FrameR5.lean (481 KB, guard OK). Window-2 list: R5t_stub.lean, R4c.lean. Next window: R5a/FrameR5.
- Exact generator data for (II,II,I): leanzbf/t1_gen_data.py / .log (20 local patterns, each rank 6 with a nonzero point).
- r5_7 (corner_unique, rule_R) is only in R5t_stub.lean.
- Numerical screen (leanzbf/t1_enum.py, t1_rules2.py, t1_patterns.py): (II,II,I)-type configurations are all killed by the simple
  S-test with the rule S = {corner of pair 12, Q2^12, Q3^12} split by C23 (40 local patterns); (II,II,II): 1560 raw configurations
  need the cube test (ell != 0 part of Pi_S) or T1'. See NOTES round 5.

## 0. ROUND 4 STATE (read first)
- WINDOW 1 (22:19 UTC): R4c.lean 6 errors, R4t_stub.lean 7 (15 s each, 7.7 GB) -- all in supporting lemmas, none in t2_proof /
  t2pp_proof / normal forms / S-tests; repaired 22:21 (sign in t2_partition; `noncomputable def blkL`; after `rintro x ⟨h1, h2⟩` on
  `x ∈ A ⊓ ker f`, h2 is `x ∈ ↑(ker f)`, so use `LinearMap.mem_ker.mp h2`, not `rw ... at h2`). Window-2 list (leanzbf/
  window_files.txt): R4t_stub.lean, R4c.lean. Logs: leanzbf/<name>_w1.log, next _w2.log. Do NOT call leancheck outside windows.
- Last file that COMPILED: lean/zbf/R3e.lean (round 3, standard axioms). Round-4 files are WRITTEN BUT NOT YET COMPILED (the Lean
  slot was starved of RAM; the coordinator runs compiles in dedicated windows from ~22:30 UTC). See NOTES-leanzbf.md, round 4.
- Window files, in this order:
  1. lean/zbf/R4t_stub.lean -- R3e with every OLD theorem proof replaced by `sorry` (statements identical, defs kept) + all new
     blocks r4_1..r4_6 in full. Fast; checks only the new parts (sorryAx in the axioms line is expected; read the error list).
     Rebuild: python3 -I leanzbf/stub.py R3e.lean r4_1.txt ... r4_6.txt R4t_stub.lean (in lean/zbf).
  2. lean/zbf/R4c.lean -- R3e + r4_1..r4_6 (full proofs); final placeholder theorem PEqualNP.Outside.L_gct_210 :
     (round-3 statement) AND T2Hyp AND T2ppHyp, so the axioms line certifies t2_proof and t2pp_proof. Project guard passes.
     Rebuild: python3 -I leanzbf/mk3.py R3e.lean r4_all.txt R4c.lean (r4_all.txt = cat r4_1..r4_6).
  3. lean/zbf/FrameR4.lean -- guard-compliant Frame210 kit (namespaces renamed to PEqualNP.Outside.L_gct_210_aux.{MethodCeiling,
     Helpers.Minc, Helpers.RankOne, Kit086, F210}; PEqualNP.Gct.permPoly is from PEqualNP.Defs and stays) + R4c's ZBF namespace +
     Bridge.lev_iff_F210 + final theorem. 448 KB. Rebuild: python3 -I leanzbf/mkframe.py FrameZbf2.lean R4c.lean FrameR4.lean.
- Round-4 blocks (lean/zbf/r4_1.txt .. r4_6.txt), all on VERIFIED results (ledger 1.3: T2, T2'', GEN-0 verified r1):
  r4_1: t2_dep, t2_partition, t2_split (T2/T2''/R3-1 common first half, PRIMAL proof: nu, mu, kappa are orthogonal to row_1(X_23),
        dim >= dim X_23 - dim X_123 >= 3, so they are dependent; hence the two pair partitions of the shared row coincide);
        ZFc, dot_zero_of_col, row_rel_zero, col_rel_zero, lone_rel, gen0_typeI, gen0_pairI (GEN-0: Type I block has 2 or 3 columns).
  r4_2: exists_perm3, blkMap, blkL (L cap zero 3x2 block), blkL_finrank, ell_ne_of_small, stest_blk, hyper_core, t2_alg, lam4,
        t2_stest (the K_S test of T2 as a reusable lemma), evalPair, span_classes.
  r4_3: fk_unique, exists_equiv3, sum_supp3, sum_C_supp3, typeI_nf (Type I normal form), t2_gen_vec, t2_proof : T2Hyp.
  r4_4: s2_noT2, s2_star_noT2 (S2, S2* without T2Hyp), typeII_nf (Type II normal form), hyper_top.
  r4_5: t2pp_alg.   r4_6: sum_C_three, loc_rel, gen_vec_core, t2pp_stest, gen_vec_A, t2pp_proof : T2ppHyp.
- Proof route of T2 / T2'' in Lean (differs from the paper's n** argument, same statement): for each column triple S = (p,q,s) of
  the right type, either dim(L cap {rows 1-3 supported in S}) <= 3, then ell != 0 on the block space (ell_ne_of_small) and T0
  makes perm_3 vanish there, and t2_core / t2pp_core force the hyperplane {t = 0} (or no hyperplane); or it is 4 = everything.
  Either way the element tau_2 = e_q - e_s (rows 1, 3 zero) exists, i.e. (kappa2_q)^-1 e_q - (kappa2_s)^-1 e_s in row_2(X_13).
  These generators span >= 3 dims (span_classes, dual-annihilator count), but dim X_13 = 2. T2'': S-types (B), (C) are literally
  the T2 test; (A) uses the T2'' cubic; pairs Q1-Q1 come as differences.
- If R4c compiles: s2_noT2 / s2_star_noT2 leave only T1Hyp (3108-configuration exact check) and R31Hyp (1800-configuration exact
  check) as explicit hypotheses of S2 / S2*.
- Guard: the full project guard (outside-guard.mjs imports ...) passes on R4b/R4c/FrameR4 (test files are allowed to carry a
  placeholder statement; leancheck then reports "statement verbatim: False", expected). Never use `rw [h1, h2] at a b` when some
  location lacks a pattern (fails); never start a line with add_; `first | (rw [h]; rfl) | rw [h]` for vector-literal evaluation.
- Next targets: (1) fix whatever the window shows; (2) T1Hyp via a generated S-test per configuration (the blkL framework applies:
  all three pairs minimal => F = E, so K_S = F cap W_S must be killed by a nonzero permanent value); (3) R31Hyp likewise;
  (4) GEN-lin, GEN-tri, GEN-2 Steps 3-4 (verified r1); (5) stage3 Theorem N pieces (N1, N2-X verified).

# HANDOVER-leanzbf (L-gct-210, role leanzbf) -- written 2026-11-23 20:40, for an agent starting cold

Gap: every linear space L of 5x5 complex matrices with perm(J + t) = 120 on L ("level space") has dim <= 8.
My job was to turn the team's hand proofs into compiling Lean 4. Everything below is in ONE self-contained file
(imports `Mathlib` and `PEqualNP.Defs` only). Paths are relative to this workspace (here /home/claude/work/L-gct-210/,
on the other machine cloud/L-gct-210/ on branch coord-L-gct-210).

## 1. How to compile; which file is the base for which

CURRENT FILE: `lean/zbf/R3e.lean` (identical snapshot `lean/zbf/R3e_ok.lean`): 5914 lines, 290,918 bytes, 340 declarations.
Last check (20:24): lean exit code 0; axioms [propext, Classical.choice, Quot.sound]; guard 0 / 0; format counts all 0.
Compile: from the project's `lean/` directory (Mathlib cache built), `lake env lean /path/to/R3e.lean`. To see the axioms,
append `#print axioms PEqualNP.Outside.L_gct_210_zbf` to a COPY (the file itself must not contain `#`). Here I used the
wrapper `/home/claude/tools/leancheck FILE gap.json`, which does exactly that and prints the guard and format counts.
Time: 50 s to 2.5 min wall per run on the shared machine (about 45-50 s CPU, single thread). Memory was not measured.
"statement verbatim: False" from the wrapper is expected: the final theorem is a placeholder, not the gap statement.

Chain of files (each = previous + text inserted before the `end <namespace>` line; all compile):
  Zbf.lean (round 1, 2015 lines) -> Zbf2 -> Zbf3 (N3') -> Zbf4 (C4) -> Zbf5..Zbf10 (C7) -> Zbf11.lean (round 2 final, 5227 lines)
  -> R3a.lean (Zbf11 with namespace renamed + `add_` fix; no new maths) -> R3b (column versions, normal forms)
  -> R3c (T0, algebraic cores, S2 count) -> R3d (S2, S2*) -> R3e (T1 identity) = CURRENT.
Namespace: `PEqualNP.Outside.L_gct_210_aux.ZBF` (`open Finset`). Final theorem (last in file):
`PEqualNP.Outside.L_gct_210_zbf` = R0 + Lemma C (rows, columns) + N3' + C4, each in definition-light form.
`lean/zbf/FrameZbf2.lean` = Frame210 kit + the Zbf11 namespace (OLD namespace names, not guard-compliant; compiles).

## 2. What is proved (Lean name -- informal statement -- paper source). No sorry, no axiom anywhere.

Notation: `pm u` = permanent of u : Fin n x Fin n -> C; `blk rho kappa u` = permanent of the block (rows rho, cols kappa);
`Lev n L` = level space; L^ = CJ + L is modelled by pairs w = (c, t), `hat n w = c + t`, ell(w) = `w.1`;
`rowMap r`, `colMap c` (line projections); `rowsZero L r r'`, `colsZero`, `rowsZeroS L S` (Finset of rows), `cellsZero L K`;
`blockSpace L r c` = U for a zero block (r c : alpha + beta = Fin n; rows inl x cols inr vanish); `dotL kappa z = sum z_m kappa_m`.

Layer A -- foundations (chief sec. 2-3; verify2 round 1)
- lev_scale, lev_scale_emb (R0: pm(c + t) = n! c^n); lev_line, lev_FK, lev_FK_row, lev_FK_block (no zero row/block at ell != 0).
- perm_zero_block, pm_zero_block, pm_zero_block_sets (ZBF: permanent factors over a zero block).
- poly_const_of_mul, line_const, ufd_unit, ufd_zero (elementary replacement of the UFD step, by restriction to lines).
- zbf_prod, zbf_ufd, zbf_zero, zbf_lineality, zbf_witness('), zbf_cases (the ZBF dichotomy: either blk_1 = k ell^|a|,
  blk_2 = k' ell^|b|, k k' = n!, or ell = 0 on U and one block permanent vanishes on U).
- thB_quad, thB_ker, thB_img, thB_dim, thB_cases, thB_pair, thB_img_or, thB_Bx, q0_isotropic_bound (Theorem B).
- lemmaC_gen / lemmaC / lemmaC_col_gen / lemmaC_col / lemmaC_nine (Lemma C in the verifier's general form:
  dim L <= dim(L cap {two rows = 0}) + 2n-3, any level space; n = m+2).
- pm_laplace_row, pm_laplace_two, ca2, ca2_full, ca2_col (zeros' CA2 by direct Laplace), thA, thA_col (Theorem A),
  single_row_SR (stage3 SR), lev_tr (transposition), lev_mix, lev_mix_hat, lev_rows (mixed coefficients).
- n3 (3x3 level => dim <= 3; chief N3), row_proj_le, rows_pigeon, one_not_mem_row, row_onto (row_e(L^) = C^n when a_e = 1).
- The same chain at an ARBITRARY base point b: BLev, blev_of_lev, blev_of_const, zbf_prodB, zbf_ufdB, thB_*B,
  lemmaC_genB, lemmaC_col_genB, blev_line, blev_mix, blev_rows.

Layer B -- N3' (stage3 sec. 10; verify2 round 1)
- n3prime: pm b != 0, pm(b + eta) = pm b on V0 (3x3) => finrank V0 <= 3. n3prime_weak (<= 4, short).
- n3prime_L_full: Corollary N3'-L (any n, any 3x3 block with ell(u0) = 1).
  Lean route differs from the paper: Lemma C at base point b + explicit algebra (Bad, bad_X4c/X3c/X1c, n3alg) with
  machine-generated certificates (lean/zbf/py/gen_alg.py, gen_n3p.py).

Layer C -- pigeonhole and Theorem G pieces (stage3 sec. 16; chief ThG)
- rows_submodular, cells_submodular, rows_rank, cells_rank (P); rows_disjoint_bound, rows_inj_bound (G1);
  dS, dS_submodular, stage3_G2 (G2).
- pm_mask_sum, pm_mask_zero, pm_mask_factor, thG_term, thG_masked (generalised Laplace identity of ThG);
  perp_bound, rank_one_bound (A, B in C^N with a.b = f(a) g(b) on A x B => dim A + dim B <= N + 1).

Layer D -- C4 (chief sec. 4; stage2 sec. 1)
- c4: Lev 5 L, pair (r, r.succAbove p) with finrank L = finrank X + 7 and both row ranks = 4 => every 3x3 subpermanent
  `Bx r p x j0 q0` of every x in X_{rr'} vanishes. Valid for every dim L. c4_col: column version (R3b).
  Proof is NEW and shorter than the paper's (ZBF witness + ThA kernels; helpers thA5, c4_left, c4_right, c4_cols).

Layer E -- C7 / C7'' (chief sec. 4, RP5; stage2 sec. 1-3; verify2 3a)
- c7_pair_thB (ThB for a column pair), c7_tau, c7_pair_x (pair criterion (a), (b), (d) of C7' by test vectors),
  c7_sep, c7_types (plane combinatorics, any index type), c7_lift (I^ = ker of two independent relations; dimension count),
  c7_hI, fk_annihilator, second_relation, dot_zero_of_row, c7_rows, c7_rows_full, c7_rows_ind.
- c7_final: minimal pair with row ranks >= 4 => annihilator data kappa, kappa', nu, nu' exist and, if kappa, kappa' are
  zero-free, the points (rho, rho') are of Type I or II (two points on an anti-diagonal, or plus one corner with
  omega^2 = -c^2, sigma_corner^2 = -sigma^2). Defs TypeCl, MinPairCl, MinPairNF package this.
- c7_final_cl (rows), c7_final_col (columns by transposition; rowsZero_tr, map_tr_row, tr_min).
- c7_nf, minPair_nf, c7_rows_nf, c7_cols_nf: NORMAL FORM in tau-coordinates (stage2 sec. 3): for all t in L,
  sum_{m in Q_b} kappa_m t(r,m) + sum_{m in Q_a} kappa'_m t(r',m) = 0, Q_a = {rho' = rho'_a}, Q_b = {rho = rho_b}.

Layer F -- triples (stage2 sec. 4, 5, 5b; verify2 3b)
- t0: T0 for a row triple x column triple (Fin 3 + Fin 2 block).
- t2_cubic, t2_core: the T2 cubic 2t(t a1 + a1 a2 + a1 a3 - a2 a3); a linear form whose kernel lies in its zero set has
  no a1, a2, a3 coefficient. t2pp_cubic, t2pp_core: the T2'' cubic contains no hyperplane (any j != 1).
- t1p_alg: T1' -- the six equations of the cyclic Type II triple have no solution (any i with i^2 = -1).
- rowsZeroS_single(_finrank), s2_count: X_123 = 0 and dim L_i = 5 force (2,2,2) or (2,2,3) up to order.
- ZF, PairI, PairII, pair_I_or_II; s2_core, s2 (Corollary S2), s2_star (S2*).
  EXPLICIT HYPOTHESES (precise Props, NOT proved): `T1Hyp` (three ZF rows, all pairs minimal => X_123 != 0; the 3,108-
  configuration exact check), `T2Hyp`, `T2ppHyp` (hand proofs; only their algebraic cores above are formalized),
  `R31Hyp` (exception triples, the 1,800-configuration check). s2 takes T1Hyp, T2Hyp, T2ppHyp; s2_star also R31Hyp.

Layer G -- stage 3 start (stage3 sec. 7)
- blk_row_scale; t1_identity: CA2 => identity (T1), for ANY row set S not containing e: x in L supported on rows S,
  xi in L with row e = 0, a_e = 1 => every 4x4 subpermanent of (rows of x on S, rows of xi elsewhere; row e deleted) is 0.

Findings for the paper authors: no step failed. C7'' needs exactly the corrected form of (d) (omega_j + omega_l = 0 AND
sigma_j = sigma_l); condition (c) and "at most two points per anti-diagonal" are not needed. C4 needs no classification
of C = a b^T + b a^T. T1' holds for both signs of i.

## 3. Guard and format status (R3e.lean)

- guard: lines starting with `add_` = 0; namespaces outside PEqualNP.Outside.L_gct_210 = 0; final theorem is last.
  (Structure fields `add_mem'` are written `carrier := {...}; add_mem' := by` on one line. Never start a line with
  `add_zero`, `add_comm`, ... inside a wrapped `rw [...]`.)
- format: no comments, no double quotes, no `#`, no sorry / axiom / native_decide, none of the words instance, structure,
  inductive, macro, syntax, notation, elab, initialize, attribute. `def`, `noncomputable def`, `abbrev` are fine.
- Size 291 KB < 512 KiB, but the cap was declared suspended; the file is not the gap proof anyway.
- Sanity: appending a deliberately false lemma yields exactly one error and exit 1 (lean/zbf/sanity.log, on Zbf10).

## 4. Next targets, in order, with sources and working tricks

1. Finish Theorem G (chief lines 27-35, 119-126). I had the full plan but did NOT write it: index type
   `abbrev IdxG n m := {A : Finset (Fin n) // A.card = m} x {T // T.card = m}` (card = C(n,m)^2 by Fintype.card_prod,
   Fintype.card_finset_len); vectors vecA v (A,T) = pm (maskAT A T (if row in A then v else 1)), vecB u likewise with
   roles swapped; `mask_prod`: vecA * vecB = pm(mask(mix v u)) * (m! (n-m)!) via thG_term with Z = T^c and
   Fintype.equivOfCardEq (cards from Fintype.card_coe, Fintype.card_of_subtype (p := ...), Fintype.card_subtype_compl),
   plus a lemma blk of all-ones = (card)!; pairing = thG_masked after Fintype.sum_prod_type and Finset.sum_subtype;
   then a Fintype-indexed copy of perp_bound / rank_one_bound with hypothesis "f a = 0 -> a perp B" and spans handled by
   Submodule.span_le into kernels. Result: rho_m + rho_(n-m) <= C(n,m)^2 + 1. dim K_2 >= 5 is further work.
2. T2 and T2'' in full (stage2 sec. 4, 5b): missing is the structural part -- I_3 = row-triple image + C(1,1,1) has
   dim = dim L + 1 - dim X_123 (copy the I0 computation of c7_lift with `(rowMap r1).prod ((rowMap r2).prod (rowMap r3))`),
   I_3^perp = N_12 + N_13 + C n**, C12 = C13 up to complement, the kernel K_S, then t2_core / t2pp_core finish.
   Then T1Hyp / R31Hyp by certificates (stage2 t5_triple_all.py, t10_typeII_exact.py; verify2 r3_exact*.py).
3. GEN-2 (stage2 R2-3) and its inputs SR (have single_row_SR), S2-d / GEN-tri, GEN-0, GEN-lin.
4. Stage 3 (sec. 7, 11-16): facts (i), (ii) of the squarefree calculus, Lemma T, MIN-A (rank-16 as hypothesis or
   certificate, stage3/span16_exact.py), TV, MIN-B, plane lemmas, Theorem N1. Work with subpermanents directly
   (`blk`); "P_a P_b P_c P_d = 0 in A_4" = all 4x4 subpermanents vanish. t1_identity applied to xi_1 + xi_2 gives
   Q_x R_c R_d = 0 without polarisation.
5. Normalisations of Type I / II (c = 1/(K_1 - K_2), sigma_0, y = (-1 + eps i)/2) from the sum conditions in c7_final.

Tricks that worked
- Build a new file by inserting text before the `end` line with a small script; compile once per batch; snapshot.
- `linear_combination` with hand or script certificates; check them first with exact Fractions treating every symbol
  (including i, with hi : i*i = -1 as a hypothesis with a coefficient) as independent (py/chk_t1p.py is a template).
- "Hyperplane inside a cubic" statements: instantiate the hypothesis at explicit test points scaled to avoid division
  (e.g. (b2 T, b2 A1, -(aT + b1 A1 + b3 A3), b2 A3)), then `linear_combination`; no irreducibility theory.
- Dimension counts: `rank_nullity L f`, `finrank_sup_vec W v (h : v not in W)`, `Submodule.finrank_mono`, then `omega`.
  Name big submodules as opaque variables: `obtain ⟨I0, hI0⟩ : ∃ I0, I0 = ... := ⟨_, rfl⟩`.
- Existence of annihilating functionals: `Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance`; convert a
  functional to a dot product with `dual_eq_dotL` (uses `pi_eq_sum_univ'`).
- Polynomial-in-s arguments: `polyLine_blk` + `poly_zero_of_ne` (vanishing for all s != 0 => identically 0);
  top coefficient via row scaling `blk_row_scale` (see t1_identity).
- Fin 3 / Fin 5 facts: `revert ...; decide`; `rcases fin3_cases a with rfl | rfl | rfl`; permanents: `permanent_two`,
  `permanent_three` with `simp only [pm, permanent_three, Matrix.of_apply, vec3_0, vec3_1, vec3_2]; ring`.
- Transposition: `lev_tr`, `trE`, `rowsZero_tr`, `map_tr_row`, `tr_min`, `blk_tr`, `Submodule.mem_map_of_mem`.
- Classical sets in statements: quantify over explicit `Finset`s with membership-iff hypotheses; use `classical`
  inside proofs (there is no DecidableEq on C in scope for `if rho m = ...`).

Traps
- `omega` can fail to identify two finrank terms that print identically (one from `rank_nullity`, one from a
  hypothesis; instance paths differ). Fix: `have e : <explicit statement> := rank_nullity L f`, then `clear` the raw one.
- `lemmaC_gen (m := 3)` etc. produce `Fin (3 + 2)`; give the `have` an explicit `Fin 5` type before `omega`.
- `rw` cannot unify higher-order patterns such as `fun p => ?d p.1 * ?w p`: instantiate the lemma with explicit
  arguments and use `exact h.trans (...)`.
- `rw [<- h0]` with h0 : ... = 0 rewrites every 0; use `rw [..., add_zero, ...] at h0; exact h0` instead.
- A `by simp` argument inside `rw [lemma (fun x => by simp)]` runs before unification; pass implicit args (`p := ...`).
- `subst h` with h : a = b eliminates b (replaces it by a); state the equation in the direction you want.
- Renamed Mathlib lemmas: `Polynomial.eval_finsetSum`, `Polynomial.finsetSum_coeff`; `div_mul_cancel₀ a (h : b ≠ 0)`.
- sympy is not installed; plain Python with Fractions (`python3 -I`).

## 5. File map

- lean/zbf/R3e.lean, R3e_ok.lean -- CURRENT (see sec. 1). R3a..R3d(.lean, _ok.lean) -- earlier round-3 states.
- lean/zbf/r3_1.txt .. r3_4.txt -- the round-3 text blocks (R3b = R3a + r3_1, R3c = R3b + r3_2, R3d + r3_3, R3e + r3_4).
- lean/zbf/Zbf.lean, Zbf2.lean .. Zbf11.lean, Zbf*_v*_ok.lean -- rounds 1-2 states (old namespace PEqualNP.Gct.ZBF210).
- lean/zbf/part2a..part2e.txt, part3a.txt, part3b.txt, part4.txt .. part10.txt -- round-2 text blocks.
- lean/zbf/FrameZbf.lean, FrameZbf2.lean -- Frame210 kit + ZBF namespace (round 1 / Zbf11), for use with the P_k tools.
- lean/zbf/py/gen_n3.py, gen_alg.py, gen_n3p.py (certificate generators for N3 / N3'), chk_t1p.py (T1' certificates).
- lean/zbf/*.log -- checker logs (r3a..r3e.log, z11.log, frame2.log, sanity.log).
- NOTES-leanzbf.md -- RESULT tables and API guides of rounds 1-2 (top), full STATUS log, round-3 STATUS lines at the end.
- Mathematics: NOTES-chief.md (sec. 2-4), NOTES-stage2.md, NOTES-stage3.md, NOTES-verify2.md (verifier's repairs).
