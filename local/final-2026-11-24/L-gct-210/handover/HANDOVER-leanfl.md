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

## 6. ROUND 4 ADDITIONS (local machine, 19:40-20:50 UTC; supersedes sections 1 and 3 where they differ)
- Paths: workspace /home/kevxhk/work/L-gct-210; compile ONLY with /home/kevxhk/work/tools/leancheck FILE.lean (one machine-wide slot,
  60-min limit; on a memory-starved machine Lean cannot even import Mathlib: check `free -m` - it needs about 8 GB available).
- GUARD FIX: the project guard (outside-guard.mjs, run by leancheck as "project guard") allows at the top level only
  `theorem PEqualNP.Outside.L_gct_210 ...`. v.tail named the theorem ..._fl and was REFUSED. w.tail = same statement under the name
  PEqualNP.Outside.L_gct_210 (a placeholder conjunction SL /\ FL row /\ FL col, NOT the gap statement). Always build with w.tail now.
  FLk.lean = v32 parts + w.tail (guard passes; local compile pending). FLl.lean = FLk + the new parts below.
- Build (current):  PARTS="pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1
  ps ps4 ps5 np3b ncolp ps2 ps3 np3c"; (for p in $PARTS; do cat lean/fl/$p.part; done; cat lean/fl/w.tail) > lean/fl/FLl.lean
- New parts (written and sympy-checked, NOT YET COMPILED at the end of round 4; see the last STATUS of NOTES-leanfl.md):
  ps.part   QBc (QB (b) as a hypothesis so that the part can be tested without q1), phi_onto (finrank (H.map rs) = 3, SLev H =>
            rs and every phi_j map H onto V; extracted from the proof of Bi), pol_alg, PS_pol, PS_f (explicit Riesz vector f in V),
            PS_nf (verifyfl PS (a): z_j = (kappa m_j/4) 1 + m_j phi_j(Y_f), Y_f in H, f = s(Y_f)), np3_col, np3_X, np3_alg (Gram
            certificate C.E = 2 nu (a-b-c)(a-b+c)(a+b-c)), NCOL_P3_core (rows NCOL-P3, H on columns 0,1,2 => m_0 m_1 m_2 = 0).
  ps4.part  sq_prop (m_j^2 X = lam m_j, sum m = 0, m != 0 => X = 0; 32 cases), PS_b_core (PS (b): <f,f> = 3 kappa^2 / 4).
  ps5.part  PS_c_key, PS_c_core (PS (c): finrank K <= 5 in the principal stratum).
  np3b.part NCOL_P3_two_core (H on columns 0,1 => m_0 m_1 = 0), NCOL_P3_one_core (H on column 0 => m_0 = 0).
  ncolp.part phi_colE, rs_colE, sc_key (m_n <f,x> = 0 for every single-column element x e_n^T of H), NCOL_P_core (rows NCOL-P, R5.7
            steps (2)-(4); step (1), "K is strongly level", enters as SLev H).
  ps2.part  QBc_of, ThmPS_a, NCOL_P3, ThmPS_b, ThmPS_c (DefLine wrappers).   ps3.part rs_cperm, DefLine_perm, NCOL_P3_perm.
  np3c.part NCOL_P3_two, NCOL_P3_one, NCOL_P3_two_perm, NCOL_P.
  Quick test: leanfl/Tps2.lean = pre a b c + colsumL snippet + ps ps4 ps5 np3b ncolp + test.tail (no DefLine/LemmaQB needed).
  Likely failure points if a compile reports errors: the `fin_cases ... <;> simp (config := {decide := true}) only [...]` steps
  (phi_colE, rs_colE, sc_key, PS_f's hdec), the 32-case `first | ... ` block of sq_prop, and `exact` steps that rely on defeq of
  col (Z + Y) j with col Z j + col Y j (these are rewritten with rfl-lemmas first).
- Next targets: compile FLl and repair; then PR-RED (R4.4: easy with PS (c)), THEOREM PR3 (R4.5), rows SC1 (R5.6, needs additivity of
  P4 in a column), P51 (R5.11), NCOL2-P (R5.13); and section 4 (1)-(3) of this file (Lemma Z, TC5) which is on the DI_5 route too.
- Compile results of round 4 arrive (after the round) in leanfl/FLk3.log (FLk), leanfl/Tps2.log (new proofs, small file) and
  leanfl/FLl.log (whole file; run only if Tps2 compiled); leanfl/chain.done marks the end of the detached chain leanfl/run_chain.sh.
  PR-RED draft (unfinished, contains a placeholder; keep it out of lean/fl): leanfl/prred.draft.

## 7. ROUND 5 ADDITIONS (21:07- UTC)
- Lean compiles happen only in DEDICATED WINDOWS announced by the coordinator (first ~22:30 UTC). In a window run
  leanfl/run_chain.sh: leancheck FLk.lean (-> leanfl/FLk3.log), then leanfl/Tps2.lean (-> Tps2.log), then FLl.lean if Tps2 passes.
- New parts: sc1a.part (sc1F, rs_col, sc1_polar [25 literal cases, `set_option maxHeartbeats 2000000 in`], sum_ite_ne5),
  sc1b.part (qA2_sum, qA2_defC, SC1 = rows R5.6 for any Lev45 K and any column n), prred.part (rowE_rs, rowE_colsum,
  tau_col_colsum, PR_RED_core = verifyfl R4.4), pr3a.part (iso_triple, pc_neutral3, P4_neutral3), pr3b.part (PR3_step1 =
  verifyfl R4.5 step (1)); ps5 refactored (PS_N0_le, QB_map_rs); np3c gained PrincNS4, PR_RED, PR3_step1_def.
- Build order: ... h1 sc1a sc1b ps ps4 ps5 np3b ncolp prred pr3a pr3b ps2 ps3 np3c + w.tail (FLl.lean, 8688 lines).
- PR3 PLAN for the next round (all tools exist): r1.part's Qv framework (Qv_exists, Qv_V, vperp1_coords, ip_Qv, t3_Qv2, Qv_inj)
  is exactly what R4.5 steps (2)-(4) need. Step (2): apply PS_b_core to Z, Zs and Z + Zs; phi_0 injective on H gives
  Y_{Z+Zs} = Y_Z + Y_Zs, hence <f, f*> = 0; so each centred column z_j - (m_j/4) 1 is orthogonal to v (PR3_step1),
  = Qv v 0 p_j q_j 0 by vperp1_coords, with 4 kap q_j^2 = (3/4) m_j^2 (ip_Qv) and sum_j q_j = sum_j p_j = 0 (Qv_inj), so
  q_j = beta m_j with one sign. Step (3): C_3 on Y = a Z + b Zs via P4_c3 + pc expansion in Qv coordinates (t3_Qv2).
  Step (4): the resulting quadratic form in (kappa, lambda) has rank 3 when <m,m> != 0 (explicit 3x3 determinant), but must
  vanish on the 2-dim N: contradiction.
- T3 / Lemma O3 (rows R8.1): the verified proof goes through SO(3,C) = PSL_2(C) and Choi-matrix ranks; no short elementary
  route was found; formalizing it needs the Ad-parametrisation of SO(3,C), i.e. a separate project.
- UPDATE 21:42: PR3 steps (2)-(4) are now WRITTEN (pr3c PR3_step2, pr3d pc_Qv3 + pr3_alg, pr3e PR3_core; wrapper PR3 in np3c),
  sympy-checked, not compiled. Build: leanfl/build.sh (NEW list ... ps6 pr3c pr3d pr3e ps2 ps3 np3c). pr3c-pr3e need r1.part,
  so they are tested only in FLl. Remaining from the coordinator's list: T3/Lemma O3 (see above), P51, NCOL2-P.

## 8. ROUND 6 ADDITIONS (22:32- UTC)
- Window 1 (22:20): FLk.lean COMPILED (exit 0, standard axioms, peak 6.2 GB): the guard-compliant FL strand is Lean-checked here.
  Tps2: 2 errors only (binder x typed as ℕ in NCOL_P_core; fixed by `∃ (n : Fin 5) (x : V4)`); all other round-4/5 core parts elaborate.
- Window 2 list: leanfl/window_files.txt -> lean/fl/FLm.lean (FLl + round-6 parts). Rebuild all files with leanfl/build.sh
  (variables OLD, NEW, R6). Small tests: leanfl/Tps2.lean (+ p51a), leanfl/Tlz.lean (pre a b c + DefLine/z2/zE + lz lzp p51b).
- New parts: x5a.part (rank1_col, R7.3 step (1) first claim), lz.part (e2b, Edb, pc_F_expand, LZ_pair_alg, LZ_shift, LZ_pair, LemmaZ), lzp.part (zE_add, Ed_pol, pc_pol,
  LemmaZ_pol), p51a.part (cE, cE_sum, P51_rank1), p51b.part (E2v, e3v, E3v, pc_add4, pc_x4, cubic4, P51_deriv4, pair_sq,
  P51_unit), p51c.part (P51_deriv, pw_dim, P51_key, P51_i), p51d.part (two_rel, span2_perp, P51_ii_core, cc_of_single, P51_two,
  P51_two_perm).
- Next: repair from the window-2 log; then NCOL2-P (needs the e = 2 analogue of PS), X5 hand part (rank-one column => orthogonal
  projector onto a non-isotropic line, then B_a = R, B_b = -R on v^perp), TC5 (P1)-(P4) on top of LemmaZ / LemmaZ_pol.

## 9. ROUND 7 ADDITIONS (22:57- UTC)
- Window-2 file is now FLn.lean = FLm + x5b + tc5c (FLm parts unchanged). Build: leanfl/build.sh (R7="x5b tc5c").
- x5b.part: X5_struct, X5_perp (rows R7.3 step (1); certificates leanfl/chk_x5b.py). tc5c.part: X2c, X3c, pc_expand2, pc_dd_scale,
  TC5_deg_pair, TC5_deg_i, TC5_degree (DI5.2 degree-wise conditions; leanfl/chk_tc5c.py).
- TC5 roadmap: (P1) needs LAG (a), (b) [hand proof: zeta cap V = C z0, z1 with tau 1, <z1,z1> = 1; E(z0) = z0^2,
  E(z0,z1) = z0 o (z1 - 1/2); support |supp z0| in {3,4}], the translation of TC5_degree into qbar_j form, and blueprint S4 (A1)
  (in the file as A1/A1b/A1cols); NB = blueprint S5 (Bi/Bii/Biii exist for strongly level 4x5 spaces; NB applies them to the
  neutral columns of Ybar = [u,u,y_2,y_3,y_4]).
- UPDATE: x5c.part (X5_fv, X5_mc: m_c = 0, short argument via span2_perp; needs verify2's confirmation that the shortcut is fine:
  if m_c != 0 then <f_W, v> = 0 for all W in N, so v is orthogonal to the non-isotropic f_Z and the isotropic f_Zs, hence v in C f_Zs).
  Build R7="x5b tc5c x5c"; window_files.txt -> FLn.lean.
- UPDATE: lagcore.part (LAG_core, 16 support cases). To finish LAG (a): from a 2-dim Q-isotropic zeta get z0 (zeta cap V) and z1
  (tau z1 = 1), compute E(z0) = z0^2, E(z0,z1) = z0 o (z1 - 1/2), E(z1) = z1 o (z1 - 1), and apply LAG_core to rule out rank 1.
  Build: R7="x5b tc5c x5c lagcore".

## 10. ROUND 8 ADDITIONS (23:10- UTC)
- FLn.lean (window-2 file) is untouched. Next-window file: lean/fl/FLo.lean = FLn parts + R8 = "lag nbcore nb p1 p1b p1c",
  built by leanfl/build8.sh (does NOT rewrite FLk..FLn). Small test leanfl/Tr8.lean (pre a b c d1 + snippets e2/e2b/Qv/uY-dY/
  span2_perp + lagcore lag nbcore + generic P1 lemmas extracted by leanfl/extract.py), listed as optional 2nd entry of window_files.txt.
- lag.part: tau_Ed, tau_Edb, perp2, LAG_a (Lemma LAG (a), perp form), LAG_b (Lemma LAG (b), only E(z0), E(z0,z1) needed).
- nbcore.part (generic): neutral_pol, neutral_iso, neutral_perp, neutral_zero (q = 3), iso_perp_plane, neutral_zero2 (S contains a
  nondegenerate plane). nb.part (m = e_1 - e_2): mTC_vals/sum/ne, TC5_tau, NB_qbar ((C2')), NB3, NB_plane (Lemma NB), TC5_qbar1
  (qbar_1 = 2 e2(d)).
- p1.part: zE_smul, dY_zE, e2_ip, LAG_line, zeta_span, P1_D, P1_line, P1_nf.  p1b.part: uYL, dYL, mL (linear maps), uY_dY_zero, P1_L
  (dim L'' >= 3), P1_Lfacts, iso_image, P1_van, line_quad, prod_lin (product of two additive functions vanishing on a subspace),
  eps_of, line_exp, P1_rel, P1_aniso, P1_reduce.  p1c.part: chi_pow, iso_quad, L_slev (L'' strongly level), P1_iso (uses A1b of
  j.part), TC5_P1 (final (P1): finrank K >= 5 and two independent zeta vectors => False).
- Certificates: leanfl/chk_nb.py, chk_p1.py, chk_p1b.py, chk_chi.py (all print 0).
- Next: repair FLo from its first compile; then TC5 (P2)-(P4) (NB_plane/NB3 give (P2); (P3) three-line case and (P4) are the long
  branches of DI5.3), and the rest of X5 step (2).
- UPDATE 23:50: p2.part (two_indep, zeta_le_one, Z_of_nbar, rs_le3, no_nbar, TC5_P2 = (P2)); R8 = "lag nbcore nb p1 p1b p1c p2".
  leanfl/closure.py builds leanfl/Tr8full.lean = pre.part + only the FLn blocks the R8 parts need + R8 parts (2775 lines); all parts
  consist only of theorem/def/set_option blocks, so the closure is faithful. window_files.txt: FLn, then (optional) Tr8full.
- UPDATE 23:50: nbl.part (neut_facts, NB_line, line_of_le_one, NB_lines = S5 isotropic-line form of the neutral columns of Nbar,
  input for (P3)/(P4)). R8 = "lag nbcore nb p1 p1b p1c p2 nbl". (P3) blocker: needs the classification of isotropic pairs with
  tau(v v'^2) = tau(v^2 v') = 0 without the bracket hypothesis br v v w w = 0 that the Lean HypIIa carries.
- UPDATE 23:55: nbq.part (pc_full, nbar_tau, nbar_cubic, nbar_quartic, nbar_eqs) = the (P3)/(P4) u-deletion equations of Nbar.
  R8 = "lag nbcore nb p1 p1b p1c p2 nbl nbq". Certificates: leanfl/chk_nbar.py.

## 11. ROUND 9 (23:51- UTC)
- (P3) classification DECIDED (leanfl/sing9, COMPUTE-leanfl.md round 9): related isotropic pairs (tau(v w^2) = tau(v^2 w) = 0, no
  bracket) = 3 chi_1-type pairs (one S_4-orbit) + 4 zero-row pairs, 14 distinct lines; the paper's list misses one chi_1-type pair
  (same orbit, harmless). Lean route without Groebner certificates: y = v o w satisfies 6 y_k^2 - 2 g y_k = const (Newton for v + s w).
- p3a.part (GENERATED by leanfl/gen_rel.py, certificates sympy-checked; regenerate rather than hand-edit): pair_E2, pair_rel.
  p3b.part: ip_ne_of_line, rel_prop, no_triangle, two_equal, three_equal.  p3c.part: cubN, quaN, nbarL, symmetry lemmas, cub_rels,
  cub_two, quart_two, three_rels, fin_le_two, smul_mul_eq, TC5_P3 (dim Nbar <= 2).  p4a.part: nbar_ker, TC5_dims (finrank K >= 5
  => finrank K = 5, q = 2, dim Nbar = 2, zeta != 0: the (P4) configuration).
- build8.sh: R9 = "p3a p3b p3c p4a" appended to FLo; leanfl/Tr9.lean = closure of R9 (prefix FLn parts + R8). Tr8full is FROZEN
  (window 2 compiles it); FLn untouched.
- (P4) not started beyond TC5_dims: branches (N-a), (N-b), (c1), (c2-i..iii), (c3) need D_N analysis, F_v forms, S4 (A1)/(G23),
  LAG(b), (F1)/(F2).
- WINDOW 2 (00:05): FLn.lean compiled in 558 s, peak 6.3 GB, exit 1 with 12 errors ALL in lagcore.part (6 lines): the pattern
  `(pow_eq_zero_iff (by norm_num)).mp (by linear_combination ..)` fails (exponent ?n never assigned: both args are postponed tactic
  blocks). Fixed with `(n := 2)`; the same pattern with a HYPOTHESIS as argument (n.part, d1.part, ...) is fine. Everything else of
  rounds 4-7 is Lean-checked. Tools: leanfl/locate.py (FL* line -> part:line), leanfl/locate2.py (any file: enclosing declaration).
- WINDOW 2 (00:14): Tr8full.lean (all round-8 parts) compiled in 360 s, 13 errors = 12 LAG_core (fixed) + 1 line_of_le_one
  (`have h3 := finrank_span_singleton hne` -- the field is an implicit argument that cannot be inferred; always ascribe the type).
  Fixed in nbl.part and (latent) p4b.part. So rounds 4-8 are Lean-checked modulo these two one-line fixes.
- Window 3 list (leanfl/window_files.txt): lean/fl/FLo.lean (12714 lines, 585 KB, guard 0, no sorry) then leanfl/Tr9.lean.

## 12. ROUND 10 (00:23- UTC)
- Build: leanfl/build8.sh, R10 = "p4c p4d p4e p4f p4g p4h p4i" -> lean/fl/FLp.lean (= FLo + R10) and leanfl/Tr10.lean (closure).
  window_files.txt (window 3): FLp.lean, Tr10.lean.
- p4c: tau_smul, rs_zE, e2_comb/e2b_comb/Ed_comb/Edb_comb, LAG_pair, X3c_line, uY_of_rs, DN_line.  p4d: zE2c, chi_t4, DN_pol,
  DN_on_z, N2_form, P4_Na.  p4e: Mv, Mv_ip, Mv_inj, Fv_nondeg, three_iso_perp.  p4f: X3c_two, uY_of_rs2, qbar_pol, Ed_sub, dY_add,
  dY_sub, P4_Nb_chi.  p4g: X3c_gen2/3, hvec (+ sq/ip/tau), tau_single, Mv_hvec, Mv_ker, Edb_self, Edb_comm, pc_hvec, dY_inj_two.
  p4h: P4_Nb_zero.  p4i: rel_two, P4_k2, P4_k2_conf, mTC_perm, P4_k2_perm, P4_k2_all, P4_c3_Ez, NB_lines', fin_le_one, P4_k3.
- Status of TC5 (P4): k = 2 done; reduced to k = 3 (P4_k3); (c3) with E(z) != 0 done. Open: (c1), (c2-i..iii), (c3) with E(z) = 0.
- UPDATE 01:05: p4j.part (Edb_add_l, kerEdb, DZ_perp, perp_line, c3_Qbar): in (c3) with E(z) = 0, Qbar vanishes on N. Last step
  planned: Qbar(c) = (1/2)(c2 c3 g23 + c2 c4 g24 + c3 c4 g34) is nondegenerate on C^3; slice N by ker colL j (dim >= 2 each, image of
  colL j on N is inside C v_j), prod_lin on c_a c_b = 0 gives elements with a single active column a, pigeonhole gives two different
  single columns a != b, and Qbar of their sum is c_a c_b g_ab != 0. Exact Singular confirmation of the plane fact: COMPUTE r10.
- (c1), (c2): not started; (c1) is the long S8-type branch (n0 in C chi_1 / C chi_3 sub-cases, fourth vector Y_4); (c2) needs the
  closed forms of DI5.3 (c2) (Tbar_j, F_v, F_v' in a, b = l3+l4, l5) and (F1)/(F2).
- UPDATE 01:08: p4k.part (uY_of_rs3, indep3, c3_final, TC5_c3): branch (c3) complete (E(z) != 0: three_iso_perp; E(z) = 0: Qbar = 0
  on N makes u(N) totally isotropic while ker(u) on N is the zeta part). Name clash avoided (P4_c3 exists in b.part).

## 13. ROUND 11 (01:10- UTC): field port (top priority) + TC5 (c2) dispatcher
- FIELD PORT. lean/fl/FLK_field.lean = all of FLk over a field Kf; leanfl/TrK11.lean = closure of the TC5 parts (rounds 7-11) over Kf.
  Both are GENERATED: edit the C parts (lean/fl/*.part) or the porter, then run leanfl/buildK.sh (never edit lean/fl/K/*.part by hand).
  * leanfl/port.py SRC DST "parts" STATE: C -> Kf; abbrev V4/M45/M55 take Kf explicitly; section variables
    {Kf : Type} [Field Kf] [NeZero (2 : Kf)] [NeZero (3 : Kf)] [NeZero (5 : Kf)] (instance-implicit, auto-included);
    lemmas/defs whose explicit arguments do not fix Kf get (X (Kf := Kf)) at every use (except def names inside simp/rw lists and
    unfold lines, and names shadowed by local binders); every linear_combination gets (norm := first | ring1 | field [nzN..])
    (field first when the certificate line has a numeral fraction), every ring becomes (first | ring1 | field [..] | ring_nf);
    declarations using field get set_option maxHeartbeats 800000 in (x4 if they had one).
    Closure binders: [Fact (exists i : Kf, i ^ 2 = -1)] for everything that (transitively) uses Ii (was Complex.I);
    [Fact (forall s : Finset Kf, s.card <= 20 -> exists t, t notin s)] for everything that uses generic_t (was Infinite C).
  * leanfl/port_header.txt: abbrevs, variables, @[simp] nzN / znN (N != 0, 0 != N for 2,3,5 and products), cast_two,
    cast_inj5, cast_succ_ne (replace Nat.cast injectivity facts), Ii, Ii_mul_Ii.
  * leanfl/port_patches.json: exact-text patches applied to the ported text (r3_inj without Complex.im, propR 120 != 0,
    S.card cast, generic_t/generic_pt size hypothesis, Nat.cast_injective / Nat.cast_add_one_ne_zero sites). The porter prints
    PATCH COUNT MISMATCH if a patch stops matching.
  * lean/fl/K/w.tail: SL_FL_field (char-p SL + FL), SL_FL_C (C corollary), final test theorem (both).
  * After a window: python3 -I leanfl/locate2.py lean/fl/FLK_field.lean LOG gives decl + relative line per error; fix in the
    porter/header/patches (or in the C part if the fix is char-free), rerun buildK.sh.
- TC5 (c2): p5e.part (coefL, c2_plane), p5f.part (smul_v_inj, cramer, P4_c2_canon: (c2-i)/(c2-ii) dispatched, (c2-iii) = hypothesis Hiii).

## 14. ROUND 12 (02:06- UTC)
- p5g.part: C1Hyp, C2iiiHyp (Prop-valued hypotheses for the two open (P4) sub-cases), P4_c2_perm (column-permutation transport of
  P4_c2_canon), not_par_symm, sne0_left, TC5_main : C1Hyp -> C2iiiHyp -> DefLine K mTC -> finrank K <= 4 (P4_k3 + parallelism split:
  none parallel -> TC5_c3; one parallel pair -> P4_c2_canon directly or via swap 3 4 / swap 2 4; all parallel -> C1Hyp).
- p5h.part: indep_of_np, sig23, c2iii_zeta (sub-case D_N = zeta of (c2-iii), via L_slev + pattern23), C2iiiLagHyp (remaining Lagrangian
  sub-case), C2iii_of_lag, TC5_main' : C1Hyp -> C2iiiLagHyp -> ... -> finrank K <= 4.
- p5i.part (GENERATED by leanfl/gen_f1.py from leanfl/sing12/*.txt): (F1) as exact ideal membership: F1_vprod, F1_w0..3, F1_zero_row.
- p5j.part: c2iii_zero_row: in (c2-iii) t3 v v w = 0, 3 t4 v v w w = <v,w>^2, and v, w share a zero coordinate.
- Next for (c2-iii) Lagrangian: (Z2) => Ed z orthogonal to v, w => Ed z in C(1,1,1,-3) (frame k0 = 3); (F2) classification of z; the two
  contradictions (z = e_i: D_N cap V = C z_0; z = h/2: perm[z,z,y3,y5] = (3/2) l b). Then (c1).
- Porter: buildK.sh/build8.sh now write window files atomically (*.new + mv) so a rebuild never races a window compile.
- p5k (GENERATED by leanfl/gen_lag.py from sing12/s3_a.txt, s3_b.txt): uconst_0..3; p5l: F2_scalar (steps checked by leanfl/chk_f2.py);
  p5m: pc_smul2, c2iii_h, c2iii_ei; p5n: c2iii_core, C2iiiLag_proof, TC5_of_c1 (TC5 from C1Hyp alone). All untested by Lean so far.
- Speed of the field port: see NOTES RESULT ROUND 12. Stage A (TrK0p = profiled TrK0, FLK_FL) is booked after window 3; the profile
  decides the fix. Split files FLK_SLa..d (closures of SL_of, HypS6, HypS7, HypS8) and FLK_FL are produced by buildK.sh.

## 15. ROUND 13 (03:01- UTC): (c1)
- p5o (GENERATED by leanfl/gen_c1.py from sing13/z_*.txt, integral Singular lifts over Z): noline.
- p5p c1_plane (derived from c2_plane by substitution: coefL1 v u with u = e_k, v k != 0).
- p5q c1_eqs, c1_reduce, C1chiHyp, C1_of_chi, TC5_of_c1chi; p5r C1RHyp, C1chi_of_R, TC5_of_c1R.
- p5s exists_iso_rs; p5t uY_R, c1R_ipv, c1R_cols; p5u c1R_half; p5v (GENERATED by leanfl/gen_s8c.py + gen_s8c_lean.py) c1R_x3c;
  p5w c1R_b, c1R_v2n.
- Open: C1RHyp sub-cases n0 = r v^3 and n0 = p v. Tools: Qv calculus (r1.part: Qv, Qv_mul, ip_Qv, Qv_V, vperp_coords), pc_expand2,
  TC5_deg_i (.2.2.2 = pc(u,y2,y3,y4) = 0), polynomial-in-s extraction via Y0 +- s Z as in c1R_x3c.
- Port speed: TrK0p profile pending (Stage A). prof.py aggregates "X took Ys" lines.
- (round 13, later) p5x (GENERATED by gen_pcqv.py): pc_Qv13; p5y c1R_case_v3; p5z c1R_case_v_u; p5aa (GENERATED by gen_qv12.py):
  pc_Qv12, x3c_Qv12; p5ab exists_rad_rs; p5ac c1R_W, c1R_case_v_final; p5ad C1R_proof, TC5_final (TC5 with no hypotheses).
  All untested by Lean; the FLq rebuild after Stage A is the first compile. If an error appears, locate2.py on FLq and fix in the part
  (or in the generator + rerun it), then build8.sh + buildK.sh.

## 16. ROUND 14 (03:57- UTC): speed fix, FLq rebuild repair
- Speed: the field discharger is now `first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]` (bare
  `simp only [nzs]` cannot close (N : Kf) != 0). TrK0p rerun: 0 errors, 160 s (was 1720 s) = the C rate per line. The old slowness was
  failing discharges inside field/field_simp, not typeclass search.
- FLq rebuild: 7 errors, all heartbeat timeouts in P4_c2_canon (p5f), F1_vprod (p5i), noline (p5o) (the per-declaration budget is eaten
  by the big certificates). Fixed with `set_option maxHeartbeats 4000000 in` in the parts (backups leanfl/bak14/).
  lean/fl/FLq2.lean = FLq + this fix (md5 11b60a129a); FLq.lean kept as compiled (7a1f2e7aca). build8.sh rewrites FLq.lean: to
  regenerate only the Tr files, run its closure.py lines by hand. buildK.sh: TrK11 d34ad9249a (porter x4 -> 16000000 there).
- Stage B proposal: FLK_field.lean (whole SL+FL port, 8012 lines) as one job, then TrK11; split FLK_SL* only as fallback.
- 07:30: FLq2 compiled clean (0 errors, 1418 s); TC5_final and L_gct_210 axioms = propext, Classical.choice, Quot.sound.
  Next: Stage B logs (leanfl/FLK_field_x.log, leanfl/TrK11_x.log); on errors use locate2.py on the file + log, fix in the C part or
  in port.py/port_patches.json, rerun buildK.sh (never build8.sh unless FLq.lean may be rewritten).

## 17. ROUND 15 (07:31-08:04 UTC) -- ABORTED by Kevin
- Certificate pipeline: see NOTES-leanfl.md section CERTIFICATE PIPELINE. Tools in leanfl/cert/: cc34gen.py, runlift.sh, liftms.sh
  (Singular lift of a .ms chart), cof2lean.py / ms2lean.py (cofactors -> Lean theorem over any CommRing, with the P1*G term),
  Tcert.lean (RED-p core + CC34, COMPILED CLEAN 335 s), Tcert2/Tcert3 (cost curve, not compiled), dc3/ (DC3 m12m3 charts + cofactors).
- FLK_field fixes (port_patches.json: spv_inj (Kf := Kf), maxRecDepth on TC5_*; K/w.tail: NeZero 2/3/5 over C; z2.part: Y0_uY/Y1_uY
  char-free TC5_* proofs). Backups in leanfl/bak14/.
- File status (md5): FLq2 11b60a129a COMPILED CLEAN; FLq 7a1f2e7aca (7 timeouts, superseded); FLK_field 4f20faf49e NOT compiled;
  TrK11 6a9f290251 NOT compiled; TrK0p 388ad0fbd3 COMPILED CLEAN; FLK_FL 0d7f568f89, FLK_SLa 3cb27e8b31, FLK_SLb d7621ba33b,
  FLK_SLc 00b35573d2, FLK_SLd 3d17f8830d, TrC0p 465e974927, Tr11 82f261fdf9, Tr13 52065b9244 NOT compiled; Tcert e562ba8db2 COMPILED
  CLEAN; Tcert2 1153b8c1db, Tcert3 079faec787 NOT compiled; kk152.part f1a48f75ec (copy of upstream L_gct_152, not compiled).
- STOPPED 08:04 UTC.
