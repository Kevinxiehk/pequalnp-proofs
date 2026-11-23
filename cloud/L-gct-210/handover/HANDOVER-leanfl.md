# HANDOVER-leanfl  (role leanfl; Lean formalization for gap L-gct-210; written 2026-11-23, 20:35 CET)

Paths below are relative to the workspace root (here /home/claude/work/L-gct-210/, on the other machine cloud/L-gct-210/).
Full working notes with every STATUS line: NOTES-leanfl.md (its RESULT section at the top carries the same tables in more detail).

## 0. State in one paragraph
lean/fl/FL.lean = lean/fl/FL.v32.lean : 7451 lines, 341940 bytes, about 400 declarations, NO sorry, NO hypotheses in the final theorem.
It compiles (exit 0) in about 4.5 to 5 minutes wall time for the whole file on the cloud machine (one lean process; the coordinator
measured about 8 GB peak memory on an independent machine); axioms: propext, Classical.choice, Quot.sound only.
The file is a PARTIAL result, not a solution of the gap: its last theorem is PEqualNP.Outside.L_gct_210_fl (Lemma SL + Theorem FL, row
and column form). The gap statement itself (dim <= 8 for every level 5x5 space) is NOT proved. No formalized step failed and no error
was found in any paper proof that was formalized; every deviation is a simplification (list in NOTES-leanfl.md, section Deviations).

## 1. How to compile, and how the file is assembled
Cloud machine: /home/claude/tools/leancheck lean/fl/FL.lean gap.json   (wrapper; at most two compiles at once).
What the wrapper does (reproduce it on any machine where the project repo is built with the Mathlib cache):
  cd <project repo>/lean
  copy FL.lean to a temp file, append one line that prints the axioms of PEqualNP.Outside.L_gct_210_fl, run  lake env lean <temp file>
  then count: lines starting with add_ (must be 0), namespace / end lines outside PEqualNP.Outside.L_gct_210 (must be 0), double quotes,
  hash signs, comment markers, banned words (all must be 0).
The wrapper prints "statement verbatim: False": expected, because the last theorem is the partial theorem, not the gap statement.
Imports: Mathlib and PEqualNP.Defs (nothing from PEqualNP.Defs is actually used). Expect only deprecation warnings (if_pos, if_neg).
Assembly: FL.lean is the byte-exact concatenation (checked with cmp) of the part files in lean/fl/, in this order:
  cat pre.part a.part b.part c.part d1.part e.part f.part g.part h.part j.part k.part o2.part p.part i5.part l2.part m.part n.part
      r1.part r2.part s1.part s2.part s3.part t3.part ds.part x1.part x2.part x3.part y1.part x4.part n1.part n2.part z1.part z2.part
      q1.part r4.part r5.part f1.part g1.part h1.part v.tail > FL.lean
pre.part holds the header (imports, namespace PEqualNP.Outside.L_gct_210_aux.FL, open Finset, noncomputable section); v.tail closes the
section and the namespace and states the final theorem. To add a result: write a new part, insert it before v.tail, recompile the whole
file (there is no incremental build; a new part costs one 5 minute compile). Every FL.vNN.lean (v14 .. v32) is a compiling snapshot.

## 2. What is proved (all compiled, no hypotheses)
Dictionary: M55 = Fin 5 x Fin 5 -> C, M45 = Fin 4 x Fin 5 -> C, V4 = Fin 4 -> C.  "level L" = the gap hypothesis verbatim
(sum over embeddings f of prod_i (1 + t (i, f i)) = 120 for all t in L).
  P4 a N = permanent of the 4x4 matrix "N without column a";  C(Y)_a = P4 a (fun p => 1 + Y p);  pc z1 z2 z3 z4 = 4x4 permanent by columns.
  SLev K    = forall Y in K, forall a, P4 a (1 + Y) = 24           (strongly level, defect 0)
  Lev45 K   = forall Y in K, sum_a P4 a (1 + Y) = 120              (4x5 level)
  DefLine K m = forall Y in K, exists theta, forall a, P4 a (1 + Y) = 24 + theta * m a     (defect line C m)
  defW K = {w : sum_a w a * P4 a (1 + Y) = 0 for all Y in K};  defC K = span{C(Y) : Y in K} (= C(K) + C 1; defect e = finrank defC - 1)
  defL r K = K.comap (del r) inf (defW K).comap (rowP r);  rowMat r w = e_r w^T (5x5);  rowE i u = e_i u^T (4x5);  del r, rowP r, ins r;
  repl i u N = N with row i replaced by u;  col Y j;  rs Y (row sums);  tau, ip, t3, t4, br (explicit 4-term sums on V4).

### Layer A. Final theorem (v.tail) and its direct corollaries (t3.part)
| Lean name | statement | paper source |
| PEqualNP.Outside.L_gct_210_fl | (SLev K -> finrank K <= 3) and (level L containing e_r w^T for all sum-zero w -> finrank L <= 7) and (same with w e_c^T) | NOTES-verifyfl BLUEPRINT S0-S9 |
| LemmaSL | SLev K -> finrank K <= 3 | blueprint S2-S9 (zeros' Lemma SL) |
| TheoremFL_row, TheoremFL_col | Theorem FL with a full free row / column (column by transposition: gap_swap5, trE5, FL_col_of) | blueprint S1, S9 |
| Cor_row, Cor_row7 | SLev of (L cap {row r = 0}) with row r deleted -> finrank L <= finrank (row-r projection) + 3; <= 7 if all row-r sums vanish | blueprint S1 (stage A) |
| LemmaDS (P4_poly, P4_ones, DS_star, DS_i) | level L, row r deletable -> all row-r sums vanish; if the row-r projection has finrank 4 then L cap {row r = 0} is strongly level and finrank L <= 7 | NOTES-chief, Lemma DS |

### Layer B. Blueprint S1-S9 (pre, a .. n, r1, r2, s1-s3 parts)
| S1 | perm5_row, level_row, propR, stageA | Laplace expansion along row r; Prop R |
| S2 | pc_tau, pc_expand, coeffs, P4_eq, P4_c0..P4_c4, P4_cols, sa0..sa4, C1, C2, C34, C2pol, sl_cols | Lemma C (column form of SLev) |
| S3 | Q1, Q4, nondeg, perp_bound, N_iso, N_col_dim, Niso, Ncol1, maxpt, tricho, peel | set-up q, d, N; generic element of N |
| S4 | root4, iso34, root4k, pow4_iso, A1facts, A1, A1b, A1cols, br_w3, G23core, G23, pattern23, LemA2_proof, caseA3, LemA_proof, two_line_pattern | LEMMA A (dim N <= 2), incl. the repaired (2,3) step |
| S5 | ip_phi, tau_phi, ip_col_phi, sum_phi, Bi, Bii, Biii | LEMMA B (isometries B_m = phi m) |
| S6 | S6_active, r3, spv, chart, Uv, lamL, N_coords, Chart, star_cert, Lam_star, Lam_F, singA, pairB, core5, AlgCore_of, HypS6_of, roots5, moments5, caseC_alg, HypS6C_proof, HypS6_proof | type IV does not exist |
| S7 | typeII_ids, IIa_tu, Ps4, Ps4_mul, Ps4_param, ip_Ps4, IIa_pqr, sq_Ps4, HypIIa_proof, S7_elem, S7_step, HypS7alg_of, HypS7_of | type II excluded |
| S8 | col_outer, S8_elem, S8_step1, Qv, Qv_mul, tau_Qv, ip_Qv, S8a, S8b, HypS8_proof | type I excluded |
| S9 | No22, SL_of, FL_of | conclusion |
Stated as hypotheses: NOTHING in the final theorem. The names HypS6, HypS7, HypS8, HypS7alg, HypIIa are Prop-valued definitions (the
exact statements of S6, S7, S8) that are each PROVED (HypS6_proof, HypS7_of with HypS7alg_of and HypIIa_proof, HypS8_proof) and then fed
into No22 / SL_of. Round 1 (FL.v14) had HypS6 and HypS8 as hypotheses; they were discharged in v15-v18.

### Layer C. Defect construction and the e = 1 tools (x1, x2, x3, x4, z1 parts)
| defL_level, defL_deletable, defL_finrank, defL_finrank' | Lev45 K -> defL r K is a 5x5 level space with row r deletable, finrank = finrank K + finrank (defW K) | NOTES-rows Section D, Prop. D (a) |
| defect_conv, defect_conv' | ANY level L, L' = L with row r deleted: finrank L <= finrank L' + finrank (defW L'); finrank L + finrank (defC L') <= finrank L' + 5 | rows Section D, Prop. D (b), normal form R1 |
| defW_finrank, defW_SLev, defW_le, defW_sum | finrank (defW K) + finrank (defC K) = 5; SLev K -> defW K = sumZero 5; defW K <= sumZero 5 | rows Section D |
| LemmaEQ, LemmaEQ_cols | DefLine K m, column permutation pi with m (pi j) != m j -> K cap Fix(pi) strongly level, finrank <= 3; m a != m b -> finrank K <= 3 + rank(Y -> y_a - y_b) | NOTES-verifyfl DI5.1 |
| P4_sym (repl, P4_repl_add, per_stk, per_rows) | sum_a w a * P4 a (repl i u N) = sum_a u a * P4 a (repl i w N) | verifyfl R3.0 (symmetric form) |
| ThmSplit | DefLine K m, sum m = 0, <m,m> != 0, e_i m^T in K -> K cap {<m, row i> = 0} strongly level, finrank K <= 4 | verifyfl R3.1 THEOREM SPLIT |
| ThmSplit_kappa (split_id, split_ker, P4_repl_ones, P4_lin) | same hypotheses -> K cap {all column sums 0} strongly level, finrank <= 3 | R3.1 step (3) |
| ThmFS (rowL, fsMap) | defect space Cs in 1^perp, e_i (x) Cs in K, <,> nondegenerate on Cs -> finrank K <= 3 + finrank Cs | verifyfl R3.2 THEOREM FS |
| LemmaHYP_a, LemmaHYP_b (hyp4, colsumL) | 4-dim subspaces inherit the defect line and are not strongly level; "every 4-dim such space contains some e_i m^T" excludes dim 5 | verifyfl R3.3 |
| HyperplaneLemma, HyperplaneCor | K <= L' level: defC K = defC L' or finrank K <= finrank (defC K) + 2, in the (DI_5; e-1) formulation | NOTES-rows R4.1 |

### Layer D. Zero rows, neutral columns, quadratic conditions (y1, n1, n2, z2, q1, r4, r5, f1, g1, h1 parts)
| LemmaSL3 (Vp_span, Vp_nondeg, Vp_t3, Vp_finrank, SL3_q2, SL3_two, SL3_d2) | SLev K and row i of every Y in K is zero -> finrank K <= 2 (zero-row form of "3x5, all 3x4 column deletions level") | rows R3.8 (case (q,d) = (1,2) by a new short argument) |
| NCOL_S_a (kc1, P4_poly1, kc1_eq, P4_repl2, kc1_formula, split_eig, ncol_lin) | SPLIT hypotheses, m without zero entry -> row i vanishes on N = K cap {<m, row i> = 0}, finrank K <= 3 | rows R4.14 (a) |
| ncol_core, ncol_b1, NCOL_S_b | column sums of the rows != i are equal on supp m; if n is the only zero of m: row i of N supported at n, N cap {row i = 0} strongly level, finrank <= 2 | rows R4.14 (b) |
| NCOL_S_neutral | SPLIT hypotheses and 4 <= finrank K -> exists n, m n = 0 | corollary of R4.14 (a) |
| TC5_sum, TC5_diff, TC5_n2, TC5_n3, TC5_n4, TC5_dd, TC5_normal (uY, dY, e2, Ed, mTC) | DefLine K (e_0 - e_1) <=> for all Y: [u,y_2,y_3,y_4] level and perm(J + [u,u,y_k,y_l]) - perm[d,d,1+y_k,1+y_l] = 24 | verifyfl DI5.2 |
| LemmaZ1 (zE, pc_ones) | DefLine K (e_0 - e_1), z (e_0 - e_1)^T in K -> e2 z = 0 | verifyfl DI5.2, Lemma Z (Z1), first claim only |
| LemmaQB (qA1, qA2, P4_quad, qb_lin, qA1_eq, qA2_eq) | DefLine K m, sum m = 0, m != 0: column sums = kappa m; (a) sum <y_a,y_a> = <s,s> + kappa^2 <m,m>; (b) per column, before centring | verifyfl R4.1 |
| Lev45_quad | (a) for every Lev45 space: total sum 0 and sum <y_a,y_a> = <s,s> + sum of squared column sums | verifyfl R4.1 (a), general e |
| single_row_sum, single_row_perp, single_row_defC | Lev45 K, e_i u^T in K: sum u = 0 and u in defC K; if also e_k u'^T in K with k != i then <u,u'> = 0 | rows R4.2 (a), (b) |
| single_row_t3 | three distinct rows i, k, l with e_i u^T, e_k u'^T, e_l u''^T in K -> sum_j u_j u'_j u''_j = 0 | rows R4.2 (c) |
| FL45 (zrow, one_add_zrow, FL45_core) | Lev45 K and e_i w^T in K for all sum-zero w -> finrank K <= 6 | NEW (4x5 analogue of Theorem FL; uses LemmaSL3) |
| Di_mem, R415_F1, R415_F2 | e_i u^T in K, Y in K: D_i(Y)u in defC K with sum 0; (tau(col_b of Y without row i) * u_b)_b in defC K with sum 0; (u'_b u_b)_b in defC K | rows R4.15 (F1), (F2) |
| SLev_Lev45, DefLine_Lev45, SLev_DefLine | glue between the three level notions | - |

## 3. Guard and format status of FL.lean (= v32)
 - helpers all inside namespace PEqualNP.Outside.L_gct_210_aux.FL; final theorem last; namespace/end lines outside L_gct_210: 0
 - lines beginning with add_: 0 (defW is written as an anonymous-constructor record so that add_mem' is mid-line; simp lists are wrapped
   so that no continuation line starts with add_zero)
 - double quotes 0, hash signs 0, comment markers 0, banned words (sorry, axiom, native_decide, initialize, macro, syntax, notation, elab,
   attribute, instance, structure, inductive) 0. NOTE the banned-word count is a plain substring grep over the whole file: these words
   must not occur even inside identifiers or lemma names.
 - size 341940 bytes, below the 512 KiB cap (the coordinator had waived the cap in any case).
 - the theorem named in the gap (PEqualNP.Outside.L_gct_210 with the verbatim statement) is NOT in the file.

## 4. Next formalization targets, in order
(1) Lemma Z, rest of (Z1) and (Z2) (verifyfl DI5.2). PLANNED IN DETAIL, NOT WRITTEN, NOT COMPILED. Suggested part i1:
    pc_quad: pc (d + t z) (d + t z) a b = pc d d a b + 2 t pc d z a b + t^2 pc z z a b (brute force);
    zE_shift: for Y' = Y + t * zE z: uY Y' = uY Y, dY Y' = dY Y + t z, columns 2, 3, 4 unchanged;
    LemmaZ_raw: TC5_normal at Y and at Y' gives pc (d + t z) (d + t z) (1+y_k) (1+y_l) = pc d d (1+y_k) (1+y_l) for all t; with t = 1, -1:
      pc z z (1+y_k) (1+y_l) = 0 and pc (dY Y) z (1+y_k) (1+y_l) = 0 for the three pairs {k,l} in {2,3,4};
    TC5_dz (bilinear TC5_dd with a scale c): pc d z (1 + c a) (1 + c b) = 4 e2b d z + c (2 <a+b, Edb d z>) + c^2 pc d z a b, where
      e2b d z = (tau d tau z - <d,z>)/2 and Edb d z k = e2b d z - (tau d z_k + tau z d_k)/2 + d_k z_k (checked by hand: constant and
      linear parts); pc_smul1: pc (c d) z a b = c pc d z a b; apply LemmaZ_raw to c * Y for c = 1, -1, 2 and solve the 3x3 system:
      e2b (dY Y) z = 0 (eps(D, zeta) = 0), <y_k + y_l, Edb (dY Y) z> = 0, pc (dY Y) z y_k y_l = 0, <y_k, Edb z z> = 0, pc z z y_k y_l = 0.
    The polarised statements in (z, z') then follow by applying this to z + z' (zeta is a subspace).
(2) Degree-wise conditions (C2'), (C3'), (C4') of DI5.2: same scale trick (apply TC5_normal to c * Y, expand with pc_expand / TC5_dd, use
    roots5 with the nodes 1..5 via inj_succ5).
(3) Theorem TC5 (verifyfl DI5.3: Lemma LAG, Lemma NB, branches P1-P4, with the verifier's simplification of branch (c3)). Large: it needs
    the classification of isotropic / Lagrangian subspaces of C^4; reuse Q1, Q4, nondeg, perp_bound, Vp_* and the Qv coordinates (r1.part).
(4) Theorem TS (verifyfl R3.2'), then Theorem PS / PR-RED / PR3 (verifyfl DI5-R4, R4.3-R4.5): start from LemmaQB, Lev45_quad and the B_m
    isometries ip_phi, tau_phi, Biii.
(5) rows' FL2* (NOTES-rows R3.9), R4.2 (d), R4.3, rest of R4.15: tools P4_repl2, kc1_formula (= Delta_1 u), LemmaSL3, single_row_perp,
    single_row_t3, FL45, Di_mem, R415_F1, R415_F2.
(6) Native 3x5 statement of SL_3 (Laplace expansion of P4 a (1 + Y) along an all-ones row; P4_repl_ones / P4_zero_row are the start).
(7) Round 5-6 items of verifyfl and rows (see their handover files); none was formalized. Check with verify2's notes what is verified
    before formalizing anything from rounds 5-6.

Tactics and tricks that WORKED
 - Polynomial identities: verify numerically first (python3 -I lean/fl/py/chkN.py, random complex points), then one `linear_combination`
   with explicit coefficients. Almost every such step compiled on the first try.
 - Brute-force permanent identities: `simp (config := {decide := true}) only [pc, ..., Fin.sum_univ_four, ite_true, ite_false, add_zero,
   zero_add]` then `ring`. Keep at most about 4 pc expansions per declaration (heartbeat limit); split larger ones (pc_ev2_0..3).
 - "Degree-k part of a polynomial identity": never use limits or derivatives. Show the expression is a polynomial of degree <= 4 in the
   scale s (P4_poly, P4_poly1, P4_quad give explicit coefficients) and that it vanishes at s = 1..5, then roots5 (Vandermonde) gives all
   coefficients 0. For degree <= 2 use three explicit points and a 3x3 linear_combination.
 - Literal indices: `fin5` (case split over Fin 5), sa0..sa4 (a.succAbove k as literals), P4_c0..P4_c4.
 - Atoms: `obtain <c, hc> : exists c : Fin 5 -> C, forall j, expr j = c j := <_, fun j => rfl>` then `simp only [hc]` to hide big terms
   from ring / linear_combination.
 - Dimension counts: helper rank_nullity, Submodule.finrank_mono, Submodule.eq_of_le_of_finrank_le, dual-annihilator lemmas
   (Subspace.finrank_add_finrank_dualCoannihilator_eq) for defW / defC, LinearMap.ker of explicit linear maps (phiRow, colsumL, rowL, zrow).
 - if-then-else: `show` the goal with the literal `if`, then `rw [if_pos rfl]` / `rw [if_neg h]`; lemmas repl_at, repl_ne.
 - Pigeonhole chart in S6: Fintype.exists_ne_map_eq_of_card_lt over Equiv.Perm (Fin 3) (6 special lines > 5 columns).
Things that DID NOT work (and the fix)
 - `exact lemma _ _ _` across pc / P4 arguments that are equal only after unfolding: "(deterministic) timeout at whnf". Fix: first
   `have hc : forall j, col (...) j = ... := fun j => rfl; rw [hc, hc, hc, hc]`, then `exact`.
 - `r.insertNth 0 f p` without motive: type mismatch. Fix: `@Fin.insertNth 4 (fun _ => C) r 0 f p`.
 - `simp only [repl, ...]` followed by `split_ifs`: fragile; use repl_at / repl_ne.
 - `rw` when the goal closes by rfl after the rewrite and another tactic follows ("no goals"): restructure with `show` or `exact`.
 - `where`-syntax for Submodule fields puts add_mem' at the start of a line (guard violation): use `{ carrier := ..., add_mem' := (by ...), ... }`.
 - One declaration with more than about 4 brute-force pc expansions: heartbeat timeout; split it.

## 5. File map (lean/fl/)
 FL.lean                     current state = FL.v32.lean (7451 lines, 341940 bytes, compiles)
 FL.v14 .. FL.v32.lean       compiling snapshots: v14 round 1 (two hypotheses), v18 hypothesis-free SL / FL, v19 DS, v20-v24 defect construction,
                             EQ, SPLIT, HYP, R4.1, SL_3, NCOL-S (a); v25 first guard-compliant (NCOL-S b); v26 FS + DI5.2; v27 QB; v28-v29 R4.2;
                             v30 FL45; v31 R4.15; v32 glue + Lemma Z1.  FL.v2 .. v13: early round-1 states.
 *.part, v.tail              the source of truth (build list in section 1). Not in the build (obsolete): t.part, t2.part, types.part,
                             n.tail, r.tail, t.tail, u.tail, *.bak_v24 (pre-guard versions).
 pre a b c d1 e f g h j k o2 p i5 l2 m n   blueprint S1-S5, S7, S9 and the reductions;  r1 r2  S8;  s1 s2 s3  S6;  t3  SL / FL / corollaries;
 ds  Lemma DS;  x1  Prop. D + Lemma EQ;  x2  SPLIT;  x3  defect dimension, R4.1, HYP;  y1  SL_3;  x4  SPLIT ker kappa;  n1 n2  NCOL-S;
 z1  FS;  z2  TC5 normal form;  q1  QB;  r4 r5  R4.2;  f1  FL45;  g1  R4.15;  h1  glue, NCOL_S_neutral, Lemma Z1.
 FLa .. FLz .lean / .log     test assemblies and their leancheck logs (FLj.log is the log of v32).
 py/chk1 .. chk12.py         numeric checks of the certificates (run with python3 -I);  py/upd_notes.py  one-off notes edit.
 ../../NOTES-leanfl.md       full notes: RESULT tables, API guide, deviations from the paper proofs, STATUS log.
 Paper sources: NOTES-verifyfl.md (BLUEPRINT S0-S11, DI5.0-DI5.6, DI5-R3, DI5-R4, DI5-R5), NOTES-rows.md (Sections D, R3, R4, R5),
 NOTES-chief.md (Lemma DS), NOTES-verify2.md (independent re-derivations: which statements count as verified).
