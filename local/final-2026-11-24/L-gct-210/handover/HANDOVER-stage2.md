# HANDOVER — stage2 (minimal row pairs / REG1 / the (Q-r) structure), after round 9 (2026-11-23, ~20:40 UTC)

Read first: NOTES-stage2.md RESULT-R9 (top), then sections R9-1 .. R9-6 (end of the file), COMPUTE-stage2.md "ROUND 9 additions".
The round-8 write-up (R8-1..R8-4) and COMPUTE S3'/S7 were missing from the workspace copy and were MERGED at 20:38 from the cloud copy
(/home/kevxhk/code/coord-L-gct-210/cloud/L-gct-210/). The predecessor's full handover (8 rounds; pitfalls, open list O1-O6) is the cloud file
handover/HANDOVER-stage2.md there -- read its sections 3 (OPEN) and 4 (Pitfalls). Note: the predecessor's S7 = (B0a) census (numerical,
not run); my queue label ST2-S7' = the B(dep) exact runs.

## Where things stand
- Object: X = L_r (5-dim space of 4x5 matrices) for a row r with 4-dim projection of a putative 9-dim level space. Tests: (FO-r) (row-r projection
  Omega of T_1(X) must be C^5), FO2 (bound >= 9 needed), (T2) (linear, must be solvable).
- (2,4) block family (rows 1,2 = s_1 e_0, s_2 e_0; rows 3,4 = p, q). Level conditions: R6-1 / COMPUTE S3. Case A: s = 0. Case B: ab = <p',q'>, s != 0.
  * LEMMA PROP (R9-5): rows 1,2 proportional on X with ratio != 1  =>  Omega = C^5 automatically (Case A = ratio -1). (FO-r) is BLIND there.
  * LEMMA N0-W (R9-3): non-PROP Case B, (0,e_m) in Omega  =>  p_m q_m = 0 on W = X cap {column 0 = 0, a = b = 0}.
  * Case B, a, b independent: (FO-r) always fails (R9-1, exact over QQ).
  * Case B, a, b dependent, non-PROP: closed except queued D0-4 families Q0_B, P0_B, P0_A_i and (if still running) D00-3 Q0_B_3, P0_B_3
    (QUEUE ST2-S7'); survivors so far only z = 3 shapes and one point with FO2 bound 8.
  * PROP survivor (S3) (R9-4): single-row parts (2,2), FO2 bound 9, dies only by (T2). => "(FO-r)+FO2 => 3-dim single-row part" is FALSE;
    the structural target must include (T2).

## Tools (all in stage2/)
- r9_direct.py FAMILY CHAR VLIST: Singular script testing (0,e_m) in Omega literally from raw 4x4 permanents (no formulas). Families: FM, FP0d, FQ0d
  (B(ind)), D1M, D0Q, D0P, D00Q/P/M, D04_<pat>_<A|B>_<i|ii>, D003_<pat>_<A|B>_<chart>. Prints LEVEL CHECK (=1) and RESULT (unit or not).
- r9_gen.py: the same via [CRIT] for FP0, FQ0, FM (B(ind)).  r9/elim.sh SCRIPT 60: eliminate the t's, print the parameter locus (closure!).
- r9_check_fam.py, r9_cand.py, r9_cand2.py, r9_S3check.py, r9_N0W_sanity.py, r9_dep_num.py: numerical cross-checks (T_1 tool, FO2, T2).
- Data: r9/cand_D04_MAi_f2.npy (survivor S1).  Logs: r9/*.log.

## Next targets (proposed)
1. PROP family (COMPUTE S8): classify / census PROP (Q-r) solutions; FO2 and (T2) on each. (S3) is the model; is there a PROP solution with
   FO2 >= 9 and (T2) solvable and z <= 2?  Also: is (T2) verified by verify2? (S3)'s death rests on it.
2. Collect the queued ST2-S7' results; any non-PROP survivor with z <= 2 must go through FO2/(T2) (template r9_cand2.py).
3. (B0) (identically vanishing entry) and B2 — untouched this round.
4. Case A of (2,4): FO2 bound 8 is still numerical; the survivor S1 (FO2 = 8) suggests the Case-A mechanism; a proof of FO2 <= 8 there.

## Round 10 addendum (21:22 UTC)
- (T2) is now a stated lemma (NOTES R10-1, verified by verify2); exact tool `stage2/r10_T2exact.py` (no sampling). Do not trust r6_T2.py "solvable".
- (**) <=> 9-dim level space with L_r = X (R10-3): the complete test for a candidate is (T1)-(T5).
- PROP family of Case B classified (R10-2); several members pass (FO-r) + FO2 + (T2) EXACTLY with single-row parts <= 2: the corrected target is false.
- NEW TEST FO2-joint (R10-4/5): L/X common isotropic for all q_m, m in X. Exact kills (all Grassmannian charts, char 0): cand_D003P_l1m1,
  D04-PROP alpha = (1,1,-1,-1) at sg = 2, -3. Numerically it kills all 21 saved candidates incl. the z = 3 ones. Tools: r10_FO2J.py (LM),
  r10_FO2J_alg.py (algebra test), r10_FO2J_exact.py NAME k (sympy + Singular chart script). Next: parameter-symbolic versions; the (3,3) z = 3 family;
  then try to PROVE "every (Q-r) solution fails FO2-joint at D = 9" family by family (this would also close O1, the z = 3 branch).

## Round 11 addendum (22:20 UTC)
- Use msolve for chart tests (r11_charts_msolve.py; mod p on all Grassmannian charts = proof for fixed rational data) and for eliminations
  (r11_elim_msolve.py). Singular char-0 per-chart GB is too slow on hard charts. Mind: msolve needs ~1.5 GB virtual memory (segfaults under 0.5 GB).
- Killed exactly by FO2-joint: X0, D04-PROP (sg = 0, 2, -3; all sg modulo the p-denominator loophole), cross a in C1, K33, (S2) at sg = 2.
- Next: certify the parametric cases in char 0 (or close the loophole with the tau-chart char-0 eliminations certified), the general A of D003-PROP
  (2 parameters over P^2), the (3,3) z = 3 family with parameters, and a structural proof via the single-row forms Bw (R11-3).

## Round 12 addendum (22:44 UTC)
- Case B of (2,4) closed at first order up to dead points (R12-1); verify2's PROP addendum added.
- New explicit family F2col (R12-4) contains every z = 3 shape found; FO2-joint kills its members tested. Next: parametric FO2-joint on F2col
  (P^1 x Gr(3,4)), and prove that z = 3 planes X_ri lie in a 2-column block. Tools: r12_Pcensus2col.py (members), r12_D003num.py, r12_forms_struct.py.

## Round 13 addendum (23:38 UTC)
- msolve mod-p bug: ALWAYS write coefficients reduced mod p (msstr helper) and delete the output file before each call; treat empty output as FAILED.
- F2col rulings parametrised (R13-2); generator r13_F2col.py (pool run ST2-F2COL) / r13_F2col_v2.py (MSV cap, CHARTS list, FAILED count).
- Cross-type ruling: 67/70 charts unit; 3 charts need > 2 GB (queued). Jump locus m_0 = 0 (dim T_1 = 15) is ST2-F2COL job 3.

## Round 14 addendum (00:10 UTC)
- Target 2: two-row planes classified (P = span{e_a m^T, (e_a - e_b) e_k^T}, m_k = 0); SPLIT kills non-isotropic m; FO2-joint kills the isotropic member over
  Q(i) (use env GAUSS=1 SQRTM1=<sqrt(-1) mod p> with r11_charts_msolve.py). Next: the 1-parameter isotropic family; the three-row case rigorously.
- Tools: r14_perm3planes*.py (C4 planes), r14_Pcensus3c.py / r14_Pcensus2row.py (level censuses), r14_tworow.py / r14_tworow_prim.py (two-row exact).
- Target 3 closed (r14_D3A.py, mod p and char 0, 70/70). Use r13_F2col_v3.py (DomainMatrix) for parametric families; v2 is too slow with 4 parameters.

## R15 addendum (round 15, 00:40-02:00 UTC)
- DRIVER BUGS: (1) E-STALE-OUTPUT (coordinator): r13_crosscharts*.py and r11 before 23:33 never deleted c.out. (2) E-MSSTR-RATIONAL (mine): msstr
  truncated non-integer rational coefficients; only r15_iso2row was affected (its runs are VOID). Use ONLY the hardened *_fx.py drivers
  (r15_msstr_fixed.py writer; output deleted before each call, must exist and be newer than the input, else FAILED; RESULT line counts rational polys).
  Re-verification of all fixed-data kills: r15/verify_all.log (all re-confirmed so far; NOTE its run() pipes into `head -6`, which truncated the
  D04Pasym_sat mod-p run after 5 tau-chart lines -- re-run that one without head). msolve needs ~2 GB VIRTUAL memory: never ulimit -v below 2000000.
- F2col R2 (K33-type ruling), exact: common kernel of the B_z is spanned by the constant vector k = e7 - e6; q0(k,k) = (nu+1)(3nu-1)(a1+2a2+2a3-6).
  Kernel kill lemma (rank B_c = 7 => k in L'' => q0(k,k) = 0) + exact cofactors => survivors only on H = {a1+2a2+2a3 = 6}, 4 lines a in
  {(1,0,0),(1,0,1),(1,1,0),(1,1,1)}, and setup-exceptional loci (list in NOTES R15-5). H: reduced chart system Gr(3,7) (r16_F2col_K.py) -- fast.
- NEXT: (i) collect r15/K_R2_H_{modp,char0}.log; proof-grade: Singular std over QQ per chart (the H systems are small); (ii) ST2-R2LINES (queued);
  (iii) exceptional R2 families via r13_F2col_v4_fx.py SETUPONLY=1 with FIXPAR, then r16_Khyp/r16_Kfast, recursively; (iv) exact T_1 rank-drop ideal
  (codim >= 2) -- the v4 rkjump gcd test only covers the hypersurface part; (v) R1: cache via SETUPONLY (started, r15/R1_setup.log), then the same
  kernel analysis; (vi) Z-chart coverage for 2-column F2col: S_3 on columns 2,3,4 + swap 0<->1 (NOT S_4).
- Target 2 three-row (r15_threerow*.py, m free): no clean solution with >= 3 columns (numerical evidence only). Two-row char-0 certificate: queued
  (ST2-TWOROW-CERT); chart A component checks passed before the 600 s timeouts.
- (late R15) JUMP LOCUS: second kernel lemma (NOTES R15-6): survivors only on a1 = -8 (+ Deg, r16_Kjump_deg.py, + a1 = 0). Queued ST2-JUMPK
  (Deg, then reduced charts mod p and Singular-QQ). Chart 3-5-7 FAILS at 2 GB in both the 2-parameter and the a1 = -8 version -> big slot, or eliminate
  the linear conditions q0(k0, L3) = 0 explicitly (Gr(3,8) instead of Gr(3,9)). Cross-type FAILED charts confirmed = 2-3-4-7, 2-3-5-7, 2-4-5-7.
  R1 generic setup died at its timeout (paused time counted) -> ST2-R1SETUP queued with 3 h.

## R16 addendum (round 16, 02:12-03:30 UTC)
- New tools (stage2/): r16_F2col_setup.py (v4 setup with fixed nu / R2inf / explicit ZBASIS, caches in r16/), r16_Kauto.py (kernel kill + exact
  rank-drop locus; also the JUMP-TYPE lemma for nq = 9/10), r16_tree.py (BFS over linear exceptional factors; state r16/tree_R2.json),
  r16_survlist.py (tree -> K2/V4 jobs), r16_F2col_K2.py (q0(k,L3) = 0 eliminated: Gr(3,nq-2)), r16_T1cert.py (T_1 rank-drop certificate, any codim),
  r16_symcut*.py (S_3 symmetry cut), r16_cofinterp.py (exact rank-drop locus for all c by lattice interpolation), r16_cofint_{ms,singp}.py.
- KEY FACTS: (1) every R2 exceptional family (nu = 0, a1 = 0, nu = -1, nu = 1/3, D = 0, and nu = 1, nu = -1/3) has the same kernel structure
  (k = e7 - e6 constant, q0(k,k) a linear form) -> survivors = an H-type plane + 0/1 points + sub-families. (2) T_1-jump families (nq = 9) obey the
  JUMP-TYPE lemma (k forced into L'' through the 3-dim kernels of the single B_z). (3) S_3 on columns 2,3,4 + row-S_3 + column swap: the R2 survivor
  set collapses to finitely many nu-lines (ST2-R2SYMLINES queued) + the S_3-invariant families A and J_A + the nu = 0 slice (the 6 special nu are one
  orbit). (4) T1cert (mod p) finds exactly the codim-2 jumps {nu = 1, a1+a2+a3 = -1} and {nu = -1/3, 4a1 = a2+a3+1}, the images of the nu = 0 / 1/3 jump planes.
  (5) R1 generic: same kernel kill, same H; its common rank-drop locus needs the exact interpolation (ST2-R1COF queued; 4-sample superset = curve + junk).
- NEXT: collect ST2-R2H Singular, R2LINES, R2SYMLINES, JUMPK (FAILED charts (1,4,5), (1,5,6) of the K2 version -> big slot), R1COF, R1H;
  Singular-QQ versions of T1cert (proof grade); the tree at depth 3 (1-parameter families) or, better, the symmetry cut applied inside every family;
  the Deg sets of the jump-type families; the special Z n = (1,0,0,0) members; then R1 through the same pipeline (tree with RUL=R1, symmetry cut).

## R17 addendum (round 17, 03:04-04:10 UTC)
- T1cert in Singular over QQ passes everywhere (generic R2/R1, 18 tree families, jump plane, cross-type): T_1 genericity is PROVED off the
  exceptional hypersurfaces. CLOSED: jump locus, special Z (new big-kernel lemma), cross-type ruling (kernel kill + S_4 cut + 4 RED-p members).
- R2: everything except the 13 cut nu-lines is [E]/lemma/[S]/[RED-p]; the 13 lines are msolve char 0 70/70 [M0]. Singular std over QQ times out on
  many line charts (> 60 s) -> next: a kernel-lemma variant on the lines (they are rank-drop points: B-stack rank < 7, kernel >= 2), or RED-p on a
  proper nu-family.
- R1: generic kill + T1cert done; ST2-R1COF stuck in sympy post-processing -> ST2-R1COF2 (r17_cofinterp2.py, cached dets, Singular minAssGTZ script).
  Then: S_3 cut with pieces H, A, D, RD_lam; lines; Singular/char-0.
- Tools: r17_charts.py (generic Gr(4,nq) runner on any cache; ENGINE=sing with per-chart STO timeout and msolve char-0 fallback), r17_symcut.py
  (general symmetry cut), r17_Kjump_deg.py (Deg for any jump family), r17/t1cert_tree.py, r17/lines_c0.sh, r17/nu0_points*.sh, r17/cross_*.sh.
  Pitfall: pkill/kill patterns that match my own command line kill my shell (exit 144) -- use PID files.

## R18 addendum (round 18, 04:07-05:56 UTC; usage-limit gap 04:25-05:14)
- R2 lines: general kernel bound (r18_linerank.py), exceptional values (r18_lineexc.py), reductions r16_F2col_K2.py (dim K = 1), r18_Kt.py / r18_Kt2.py
  (dim K = 2, k parametrised, SYSLIST re-runs), r18_KU.py (dim K = m-dim isotropic U). Status in RESULT-R18; ST2-KTBIG (43 Singular systems, 6 GB)
  queued; (0,0,0) Singular in r18/seq_small2.sh.
- D003-PROP Case A: big-kernel lemma (r18_D3A_kernel.py, cache r18/cache_D3A.pkl); r18_D3A_deg2.py (fast degeneracy) and r18_T1cert_D3A.py running.
  Then: alpha with a zero coordinate (S_4 / X0), fixed members on the degeneracy set.
- R1: wait for r17/R1_cofinterp2.log (Singular script r14/cache_F2col_05c7df28474c_cofideal.sing), run it, then r18_symcut_nl.py with pieces
  H, A, D, RD components (P0 = lam, EXC = lam*a1*(a1+a2+a3-4)).
- Stopped at the 05:28 memory incident: ST2-TWOROW-CERT (restart later), R2SYMLINES pool chain (redundant).
- Pitfall again: kill patterns matching my own command line (exit 144) -- always write PID lists to a file in a separate command.

## R19 addendum (round 19, 05:56-06:22 UTC)
- r18_Kt3.py (quadratic-field Kt reduction) closes the four kap = 2 R2 lines at proof grade; 12/13 lines done, (0,0,0) via r18_KU.py Singular (in
  r18/seq_small2.sh, paused/resumed by r18/memguard.sh). ktbig.sh made restartable but no longer needed (LOW_ST2KTBIG dropped).
- D003-PROP Case A CLOSED and verified (R19-2/3): r18_D3A_deg3.py (Singular), r18_T1cert_D3A.py, r18_D3A_kernel2.py (alpha_4 = 0 family).
- R1: r19_R1cof_sing.py (Singular, symbolic c) queued as ST2-R1COFSING; then r18_symcut_nl.py with P0 = lam, pieces H (a1+2a2+2a3-6), A (a1),
  D (a1+a2+a3-4), RD components, EXC = lam*a1*(a1+a2+a3-4); then lines/points -> Kt/K2/Kt3-style reductions in Singular.

## R20 addendum (round 20, 06:21-07:07 UTC)
- R1: r20_Ksing_p.py (char-p structure), r20_RDcert.py (Rabinowitsch certificate over Q, lighter than minAssGTZ), r20/r1lines.sh (kernel bound),
  r20/r1red.sh (K2b / Kt3 Singular reductions + RD certificate char 0), r20/r1exc.sh (exceptional lam, 4 combinations). r20_F2col_K2b.py = K2 with
  per-chart Singular timeout and msolve char-0 fallback. r20_kbound_rec.py = recursive kernel bound (undecided on J_A^R1).
- OPEN: J_A^R1 (setup cache r16/cache_ad03c283c2b2.pkl), KU (0,0,0) (r18/seq_small2.sh), R1 families a1 = 0 / D = 0 beyond the cut (the cut uses A, D
  as pieces; A needs its own cut: RD_A = (0,1,1) mod p), and T1cert for the R1 sub-families.
- Idea for KU (0,0,0): q0|K becomes CONSTANT after rescaling the first kernel vector by 1/nu; if the quaternary form is split, the isotropic planes
  form explicit rational (or quadratic-field) rulings -> a Kt3-style explicit U and much smaller charts.

## R21 addendum (round 21, 07:09-07:42 UTC): F2col CLOSED pending verify2's audit
- Tools: r21_rank2.py (rank-2 split), r21_kbound_hyp.py (recursive bound inside a split hyperplane), r21_JA_deg.py (failure sets), r21_chain.py
  (recursive bound on 1-parameter families + exceptional roots + pointwise checks), r21_algpoint.py (sympy, quadratic fields), r21_algpoint_sing.py
  (Singular, any degree), r21_algK2.py (reduced charts at algebraic points), r21_algcharts.py (full charts at algebraic points; slow),
  r21_RDcert2.py (factored-determinant exact RD certificate; seconds).
- F2col table: NOTES "F2COL-TABLE (CONSOLIDATED, R20)" + "F2COL-TABLE (R21 FINAL ROWS)". Everything [S]/[E]/[RED-p]/lemma.
- NEXT: branch 3 B(dep) (runs/st2_elim_msolve.log: comps with empty elimination ideal "[]" are full-dimensional in the parameters -> need the FO2-joint /
  kernel-bound machinery), then the uniform statement: every z = 3 family so far died by one of four linear-algebra lemmas (kernel kill, big kernel,
  jump-type, rank-2 split + recursive bound) -- a candidate uniform proof is "the recursive kernel bound with the (Q-r) forms always closes".

## R22 addendum (round 22, 07:38-08:00 UTC)
- F2col: verify2 audit done; all cited logs now in stage2/r21/redp_logs.log (+ r21/*RESULT.txt, r21/symcut_JA_R1*.log, r21/JA_R1_deg.log).
- r22_genset.py: GENERIC setup from an X-basis spec file (any parameters; QI=True for Q(i) coefficients); r22/mkspec_dir.py builds specs from the
  old Dir_*.sing U-matrices. D04-PROP closed (R22-1); P0_B_i points exact (R22-2).
- Running: r22_kbound_qi.py on r22/cache_iso2row.pkl (isotropic two-row family, Q(i)(t)); next: its exceptional t (exact) and pointwise checks;
  then the two-row classification char-0 certificate (restart ST2-TWOROW-CERT when memory allows) and the three-row classification (exact).

## FINAL (stage2 STOPPED 08:04 UTC, work on L-gct-210 aborted)
- State: see NOTES-stage2 "FINAL STATE" (top). F2col CLOSED (verify2 audit; logs in stage2/r21/redp_logs.log); D003-PROP Case A CLOSED; D04-PROP
  closed in char 0 (audit pending); isotropic two-row family closed (R23-1); B(dep) points exact, eliminations mod p only.
- Open for anyone resuming: two-row classification certificate (r23_tworow_cert.py, big slot line in QUEUE.md), three-row classification, B(dep)
  char-0 eliminations, O1 uniform proof (pattern: a single-row form of rank <= 5 whose kernel is too small for a q0-isotropic plane).
- Tools index: r16_F2col_setup / r16_Kauto / r16_tree / r16_T1cert / r17_charts / r17_symcut / r18_Kt3 / r18_symcut_nl / r20_kbound_rec /
  r21_chain / r21_rank2 / r21_algpoint(_sing) / r21_algK2 / r21_RDcert2 / r22_genset (+ QI) / r23_iso_deg. No jobs running.
