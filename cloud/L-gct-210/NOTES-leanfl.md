# NOTES-leanfl (role: leanfl; round 1 16:38-18:05, round 2 18:13-19:15, round 3 19:16-)

## RESULT (leanfl, rounds 1-3) -- Lean-checked WITHOUT ANY HYPOTHESIS: LEMMA SL, THEOREM FL (row and column), LEMMA DS, the DEFECT
## CONSTRUCTION (Prop. D / normal form R1), LEMMA EQ, THEOREM SPLIT (both forms), THEOREM FS, LEMMA HYP, the HYPERPLANE LEMMA, LEMMA SL_3,
## THEOREM NCOL-S (a), (b), the TC5 NORMAL FORM (DI5.2), LEMMA QB, R4.2 (a), (b).   Not done: TC5 itself, PS, PR3, FL2*, R4.2 (c),(d), R4.3.
File: /home/claude/work/L-gct-210/lean/fl/FL.lean (the last STATUS line names the current snapshot FL.vNN.lean, its size and the build list).
leancheck: exit 0; axioms propext / Classical.choice / Quot.sound only; format counts all 0; GUARD counts 0/0 (helpers live in
namespace PEqualNP.Outside.L_gct_210_aux.FL, no line begins with add_; adopted in v25). Size is above 300 KB (cap waived by the coordinator).
Final (placeholder-named) theorem, no hypotheses, last declaration of the file:
  theorem PEqualNP.Outside.L_gct_210_fl :
      (forall K : Submodule C (Fin 4 x Fin 5 -> C), SLev K -> finrank K <= 3)                                   [LEMMA SL]
    /\ (forall L, <gap hypothesis verbatim> -> forall r, (forall w, sum w = 0 -> e_r w^T in L) -> finrank L <= 7)      [THEOREM FL, free row]
    /\ (forall L, <gap hypothesis verbatim> -> forall c, (forall w, sum w = 0 -> w e_c^T in L) -> finrank L <= 7)      [THEOREM FL, free column]
All other results are theorems of the namespace PEqualNP.Outside.L_gct_210_aux.FL in the same file. NO formalized step failed and NO
error was found in any of the paper proofs that were formalized (blueprint S1-S9, chief's DS, rows' D / R3.8 / R4.1 / R4.14 / R4.2(a,b),
verifyfl's DI5.1 / DI5.2 / R3.1 / R3.2 / R3.3 / R4.1(QB)).

### Main theorems (Lean names; all COMPILED, no hypotheses)
| paper statement | Lean name (helpers) | statement in Lean terms |
| Lemma SL (strongly level 4x5 => dim <= 3) | LemmaSL | SLev K -> finrank K <= 3 |
| Theorem FL, full free row | TheoremFL_row | level L, rowMat r w in L for all sum-zero w -> finrank L <= 7 |
| Theorem FL, full free column (transposition) | TheoremFL_col (gap_swap5, trE5, FL_col_of) | same with colMat c w |
| Corollary (stage A + SL) | Cor_row, Cor_row7 | SLev ((L inf ker (rowP r)).map (del r)) -> finrank L <= finrank (L.map (rowP r)) + 3; <= 7 if all row-r sums vanish |
| chief's Lemma DS | LemmaDS (P4_poly, P4_ones, DS_star, DS_i) | level L, row r deletable -> all row-r sums vanish; if finrank (L.map (rowP r)) = 4 then L cap {row r = 0} is strongly level and finrank L <= 7 |
| rows' Prop. D (a): defect construction | defL, defL_level, defL_deletable, defL_finrank, defL_finrank' | Lev45 K -> defL r K = K (+) e_r (x) defW K is a 5x5 level space with row r deletable, finrank = finrank K + finrank (defW K) |
| rows' Prop. D (b) / normal form R1 | defect_conv, defect_conv' | ANY level L: finrank L <= finrank L' + finrank (defW L'), L' = L.map (del r); finrank L + finrank (defC L') <= finrank L' + 5 |
| dim W = 4 - e | defW_finrank (dotL, dotL_ker) | finrank (defW K) + finrank (defC K) = 5, defC K = span{C(Y)} = C(L') + C 1 (finrank defC = e + 1) |
| strongly level = defect 0 | defW_SLev, defW_le, defW_sum | SLev K -> defW K = sumZero 5; always defW K <= sumZero 5 |
| verifyfl's Lemma EQ (DI5.1) | LemmaEQ, LemmaEQ_cols | DefLine K m, column permutation pi with m (pi j) != m j -> K cap Fix(pi) strongly level, finrank <= 3; m a != m b -> K cap {col a = col b} strongly level and finrank K <= 3 + rank(Y -> y_a - y_b) |
| verifyfl's THEOREM SPLIT (R3.1) | ThmSplit (repl, P4_repl_add, per_stk, per_rows, P4_sym) | DefLine K m, sum m = 0, <m,m> != 0, e_i m^T in K -> K cap {<m, row i> = 0} strongly level and finrank K <= 4 |
| SPLIT, ker kappa form (step (3) of R3.1) | ThmSplit_kappa (split_id, split_ker, pc_ev, P4_repl_ones, P4_lin) | same hypotheses -> K cap {all column sums 0} strongly level, finrank <= 3 |
| verifyfl's THEOREM FS (R3.2), row form | ThmFS (rowL, fsMap) | defect space Cs inside 1^perp, e_i (x) Cs inside K, <,> nondegenerate on Cs -> K cap {row i perp Cs} strongly level, finrank K <= 3 + finrank Cs |
| verifyfl's Lemma HYP (R3.3) (a), (b) | LemmaHYP_a, LemmaHYP_b (hyp4, colsumL) | (a) H <= K, DefLine K m, finrank H = 4 -> DefLine H m and H not strongly level; (b) if every 4-dim space with defect line C m contains some e_i m^T then no 5-dim space with defect line C m exists |
| rows' Hyperplane Lemma (R4.1) | HyperplaneLemma, HyperplaneCor | (DI_5; e-1) as "finrank (defC K) <= e -> finrank K <= finrank (defC K) + 2"; L' level, finrank (defC L') = e + 1, K <= L' -> defC K = defC L' or finrank K <= finrank (defC K) + 2; if finrank K >= e + 3 then defC K = defC L' |
| rows' Lemma SL_3 (R3.8), zero-row form | LemmaSL3 (Vp_span, Vp_nondeg, Vp_t3, Vp_finrank, SL3_q2, SL3_two, SL3_d2) | SLev K and row i of every Y in K is zero -> finrank K <= 2 |
| rows' Theorem NCOL-S (a) (R4.14) | NCOL_S_a (kc1, P4_poly1, kc1_eq, pc_ev2, P4_repl2, kc1_formula, split_eig, ncol_lin, tau_repl0) | DefLine K m, sum m = 0, <m,m> != 0, e_i m^T in K, m without zero entry -> row i vanishes on N = K cap {<m, row i> = 0} and finrank K <= 3 |
| rows' Theorem NCOL-S (b) | ncol_core, ncol_b1, NCOL_S_b (P4_zero_row') | for all Y in K the column sums of the rows != i are equal on supp m; if n is the only zero of m: row i of N is supported at n, N cap {row i = 0} strongly level of finrank <= 2, = 2 if finrank K = 4 |
| verifyfl's TC5 normal form (DI5.2) | uY, dY, e2, Ed, TC5_sum, TC5_diff, TC5_n2, TC5_n3, TC5_n4, TC5_dd, TC5_normal | the four displayed identities; DefLine K (e_0 - e_1) <=> for all Y in K: (i) [u,y_2,y_3,y_4] level and (ii) perm(J+[u,u,y_k,y_l]) - perm[d,d,1+y_k,1+y_l] = 24 (columns numbered 0..4) |
| verifyfl's Lemma QB (R4.1) | LemmaQB (qA1, qA2, P4_quad, qb_lin, qA1_eq, qA2_eq) | DefLine K m, sum m = 0, m != 0, Y in K -> exists kappa theta2: column sums = kappa m; (a) sum_a <y_a,y_a> = <s,s> + kappa^2 <m,m>; (b) <y_j,y_j> - <s,y_j> - kappa^2 m_j^2 = -(theta2/2) m_j |
| QB (a) for any level 4x5 space; R4.2 (a), (b) | Lev45_quad, single_row_sum, single_row_perp, single_row_defC (rowE) [r4.part: see STATUS for whether it is in the current snapshot] | Lev45 K, Y in K -> total sum 0 and sum_a <y_a,y_a> = <s,s> + sum_a c_a^2; e_i u^T in K -> sum u = 0 and u in defC K; e_i u^T, e_k u'^T in K, i != k -> <u,u'> = 0 |

### Dictionary / API guide
  M55 = Fin 5 x Fin 5 -> C, M45 = Fin 4 x Fin 5 -> C, V4 = Fin 4 -> C.  col Y j (column), rs Y (row sums, linear), tau, ip, t3, t4, br.
  P4 a N        = permanent of the 4x4 matrix "N minus column a" (sum over injective e : Fin 4 -> Fin 5 avoiding a); C(Y)_a = P4 a (1 + Y).
                  P4_cols: P4 a N = pc (col N (a.succAbove 0)) .. (col N (a.succAbove 3)); pc = 4x4 permanent in column form; sa0..sa4
                  turn a.succAbove k into literals; P4_c0..P4_c4 are the literal versions; pc_tau, pc_expand expand pc.
  SLev K        = forall Y in K, forall a, P4 a (1 + Y) = 24            (strongly level = defect 0).
  Lev45 K       = forall Y in K, sum_a P4 a (1 + Y) = 120              (4x5 level: <1, C(Y)> = 120).
  DefLine K m   = forall Y in K, exists theta, forall a, P4 a (1 + Y) = 24 + theta * m a     (defect line C m; sum m = 0, m != 0 are separate hypotheses).
  defW K        = {w : forall Y in K, sum_a w a * P4 a (1 + Y) = 0} = (C(K) + C 1)^perp  (mem_defW is Iff.rfl).
  defC K        = span{C(Y) : Y in K} = C(K) + C 1;   defect e(K) = finrank (defC K) - 1.
  defL r K      = K.comap (del r) inf (defW K).comap (rowP r)      (the space L(L') of rows' Prop. D).
  "row r deletable in L"  :=  forall t in L, sum_a P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120.
  rowMat r w = e_r w^T (5x5), colMat c w, rowE i u = e_i u^T (4x5; the hypotheses "e_i m^T in K" are written with the same lambda),
  del r = delete row r, rowP r = row r, ins r Y = Y with a zero row inserted at r, stk r N w = (N; w), cperm sigma = column permutation.
  repl i u N    = N with row i replaced by u (repl_at, repl_ne, repl_self).  P4_repl_add (additivity in a row), P4_zero_row, P4_zero_row',
                  P4_sym r i w u N: sum_a w a * P4 a (repl i u N) = sum_a u a * P4 a (repl i w N)  (symmetry of Per(l_1..l_4, w)).
  Polynomial tools: P4_poly a B Y (P4 a (B + sY) has degree <= 4 in s), P4_poly1 (same with the constant and linear coefficients explicit:
                  P4 a B and kc1 a B Y = sum_k P4 a (repl k (row k of Y) B), kc1_eq), P4_lin, P4_quad (P4 b (1 + cY) with explicit
                  coefficients qA1, qA2 of c, c^2; closed forms qA1_eq, qA2_eq), roots5 (degree <= 4, five distinct roots => all
                  coefficients 0; used with the nodes 1..5 = inj_succ5), moments5 (Vandermonde, transposed), vdm3, cramer2.
  Explicit permanents: P4_ones (= 24), P4_repl_ones (row i = m, others 1: 6 sum_{j != b} m_j), P4_repl2 (rows y, m, 1, 1: 2 sum_{j != l} y_j m_l).
  phiRow i m Y  = <m, row i of Y>;  colsumL j Y = column sum j;  csL = all column sums;  fsMap i Cs : M45 -> Dual Cs.
  Plane V' = {x in C^4 : tau x = 0, x_i = 0} (zero-row case): Vp_span (two independent vectors span it), Vp_nondeg, Vp_t3, Vp_finrank.
  SL_3 dictionary: a 3x5 space "all of whose 3x4 column deletions are level" corresponds to the 4x5 space of its zero-row extensions
  (Laplace expansion of P4 a (1 + Y) along the all-ones row i); this Laplace step itself is not formalized.
  How to add a result: write a new part file, append it before v.tail in the build list, compile with leancheck (5 min for the whole
  file); never start a line with add_; brute-force identities about pc: simp (config := {decide := true}) only [pc, ..., Fin.sum_univ_four,
  ite_true, ite_false, add_zero, zero_add] then ring (at most ~4 such cases per declaration, else the heartbeat limit is hit);
  avoid `exact` across non-syntactic pc arguments (whnf timeout): first rewrite the columns with a `have hc : forall j, col .. j = .. := fun j => rfl`.

### Blueprint steps S1-S9 (rounds 1-2): all COMPILED, no hypothesis
  S1 Prop R (perm5_row, level_row, propR, stageA); S2 Lemma C (pc_tau, pc_expand, coeffs, C1, C2, C34, C2pol); S3 (Q1, Q4, Niso, peel, maxpt, tricho);
  S4 Lemma A incl. G23 (A1, A1b, A1cols, G23, pattern23, LemA2_proof, caseA3, LemA_proof, two_line_pattern); S5 (Bi, Bii, Biii);
  S6 type IV excluded (HypS6_proof: spv/chart, Uv, lamL, N_coords, star_cert, Lam_star, Lam_F, singA, pairB, core5, AlgCore_of, HypS6_of,
     caseC_alg, HypS6C_proof); S7 type II excluded (typeII_ids, IIa_tu, Ps4*, HypIIa_proof, S7_elem, S7_step, HypS7alg_of, HypS7_of);
  S8 type I excluded (S8_elem, S8_step1, Qv framework, S8a, S8b, HypS8_proof); S9 (No22, SL_of, FL_of).

### Deviations from the paper proofs in rounds 2-3 (all simplifications or re-arrangements; none is a gap in the paper)
 - S8 Steps 2-4 and S6 are done WITHOUT any row permutation: coordinates Qv v a0 a1 a2 a3 = a0 + a1 v + a2 v^2 + a3 v^3 for a "special"
   vector v (tau v = <v,v> = tau(v^3) = 0, v_i^4 = kappa): products are a twisted convolution (Qv_mul), tau and <,> are read off (tau_Qv, ip_Qv).
 - S6 chart: the six special lines are spv pi (pi in Perm(Fin 3)), 6 > 5 columns (pigeonhole), so some special v is proportional to no column
   of the generic element z; then every column is zeta_m U(theta_m), U(theta) = Qv v 0 (-theta^2/2) theta 1 (no "point at infinity").
 - S6 (C3*): one polynomial certificate (star_cert); division by lam_m via the parallelogram law with the generic element (Lam_F).
 - S6 patterns: singleton lines by singA; (2,1,1,1) by pairB; (1^5) by caseC_alg: with w in Lam having four vanishing moments and theta w
   in Lam, the power sums p_j = sum w_n^2 theta_n^j satisfy p_0 = ... = p_4 = 0, hence w = 0 by Vandermonde (replaces the case distinction
   c_0 = 0 / c_0 != 0 and the explicit partial fractions of the blueprint).
 - Lemma DS (i): the limit s -> 0 is replaced by "a polynomial of degree <= 4 vanishing at s = 1..5 vanishes identically" (P4_poly, roots5);
   the same device is used for every "degree-k part" (SPLIT step (3), NCOL-S, QB).
 - Prop. D (b) is proved for every level L (the inequality does not use deletability).
 - THEOREM SPLIT: steps (1), (2) of R3.1 give directly "K cap {<m, row i> = 0} is strongly level" (the form used by rows' R4.14);
   step (3) is the separate lemma split_ker (column sums 0 => <m, row i> = 0).  THEOREM FS is proved in the same row form.
 - LEMMA SL_3, case (q, d) = (1, 2): NEW SHORT ARGUMENT replacing R3.8 (d). With N = span{v(e_a-e_b)^T, w(e_c-e_d)^T}, Y_0 in K, u = s(Y_0):
   C3 at the inactive column e, second difference in the direction w(e_c-e_d)^T: tau(y_a w^2) + tau(y_b w^2) = 0; on the plane V' this is
   gamma_w (<y_a,v> + <y_b,v>) = 0; C2pol with v(e_a-e_b)^T at columns a, b: 2<y_a,v> = <u,v> = 2<y_b,v>; so <u,v> = 0, likewise
   <u,w> = 0, and u = 0 because <,> is nondegenerate on V' = span(v,w). Hence d = 2 forces q = 0 (SL3_d2); q = 2 forces N = 0 (SL3_q2).
 - NCOL-S: D^(1)(Y) m is used in the raw form 2 sum_{j != b} c_j sum_{l != b,j} m_l (kc1_formula) and then in the closed form
   -2 S m_b + 4 c_b m_b - 2 c.m (ncol_core); c.m = 0 is obtained in one stroke by summing the eigenvector relations over b (no case
   distinction "m has a zero / has no zero"), so ncol_b1 holds for every m with <m,m> != 0.
 - QB is stated before centring ((b) as <y_j,y_j> - <s,y_j> - kappa^2 m_j^2 = -(theta2/2) m_j, theta2 = the degree-2 part of thetahat);
   Lev45_quad is the general-e statement (a) with <c,c> = sum of squared column sums.
 - TC5_dd holds for arbitrary a, b (the hypothesis a, b in V of DI5.2 is not needed for that identity).

### Open (not formalized)
 - verifyfl's Theorem TC5 (DI5.3: Lemmas Z, LAG, NB and branches P1-P4), Theorem TS, Theorem PS / PR-RED / PR3 (R4.3-R4.5), round-5 items;
   rows' FL2* (R3.9), R4.2 (c), (d), R4.3; the degree-wise conditions (C2'), (C3'), (C4') of DI5.2; the native 3x5 statement of SL_3.
   Tools that are ready for them: everything in the API guide; for PS the blueprint lemmas ip_phi / tau_phi / Biii (B_j isometries) and
   LemmaQB; for FL2* the pieces P4_repl2, kc1_formula (= Delta_1 u), LemmaSL3, single_row_perp.

### Build recipe (reproduces FL.lean byte for byte; leancheck takes about 5 minutes for the whole file)
  cd lean/fl; cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 [r4] (.part) v.tail > FL.lean
  (rounds 1-2: pre .. n blueprint S1-S9; r1 Qv; r2 S8; s1-s3 S6; t3 SL / FL row + column / corollaries; ds Lemma DS;
   round 3: x1 Prop. D + Lemma EQ; x2 SPLIT; x3 defect dimension + R4.1 + HYP; y1 SL_3; x4 SPLIT ker kappa; n1 NCOL-S (a); n2 NCOL-S (b);
   z1 FS; z2 TC5 normal form; q1 QB; r4 Lev45_quad + R4.2 (a), (b); v.tail final theorem.)
  Snapshots (all compile): FL.v14 (round 1), v15 (S8), v16 (column), v17 (S6 mod (1^5)), v18 (hypothesis-free FL), v19 (DS), v20 (D, EQ, SPLIT),
  v21 (defect dim, R4.1, HYP), v22 (SL_3), v23 (SPLIT kappa), v24 (NCOL-S a), v25 (NCOL-S b, GUARD-COMPLIANT from here on), v26 (FS, DI5.2),
  v27 (QB); later ones in the STATUS lines.  Files *.bak_v24 are the pre-guard versions of the five edited parts.

## RESULT ROUND 1 (superseded by the section above; kept for the per-step table and the round-1 deviations)
## THEOREM FL was Lean-checked modulo TWO explicit hypotheses: HypS6 (blueprint S6, type IV) and HypS8 (S8 Steps 2-4, type I).
File: /home/claude/work/L-gct-210/lean/fl/FL.lean (3091 lines, 136 KB; identical snapshot FL.v14.lean). leancheck: exit 0, axioms
propext / Classical.choice / Quot.sound only, format counts all 0 (no sorry, no comments, no banned words, no quotes, no hash).
Final theorem (helpers in namespace PEqualNP.Gct.FL210):
  theorem PEqualNP.Outside.L_gct_210_fl (H6 : HypS6) (H8 : HypS8)
      (L : Submodule C (Fin 5 x Fin 5 -> C)) (hL : <gap hypothesis verbatim>) (r : Fin 5)
      (hF : forall w : Fin 5 -> C, sum w = 0 -> (fun p => if p.1 = r then w p.2 else 0) in L) : finrank C L <= 7
Lean-checked without any hypothesis: S1 (Prop R), S2 (Lemma C), S3, S4 (LEMMA A: d <= 2, complete, incl. G23), S5 (B-i, B-ii, B-iii),
S7 (TYPE II EXCLUDED, complete, incl. (II-a) and (II-b)), S9 and Stage C modulo the two hypotheses.
NO formalized step failed, and no error was found in the paper proof in the formalized part; the only deviations are simplifications.
NOT Lean-checked (both true according to the blueprint; exact statements below):
  HypS6 : three linearly independent column lines cannot occur with d = 2            (S6: type IV does not exist)
  HypS8 : a rank-one-column N = v (x) Lambda with d = 2 cannot occur when q = 2      (S8: type I; Step 1 is proved, Steps 2-4 open)

### Status per blueprint step
| step | Lean names | status |
| S1 ID1 Laplace expansion of perm_5 along row r | perm5_row (sum_emb_perm, sum_emb_succ, emb4) | COMPILED |
| S1 Prop R (row-r sum 0; all five column deletions level; L = F_r (+) L') | level_row, propR, stageA | COMPILED |
| S2 ID2 perm(J_4 + cZ), general columns, all four coefficients | pc_tau, pc_expand, coeffs, coeffs0, P4_eq, P4_c0..4, P4_cols | COMPILED |
| S2 Lemma C (C1, C2, C3, C4) and (C2pol) | C1, C2, C34, C2pol, sl_cols | COMPILED |
| S3 (Q1) totally isotropic subspace of V has dim <= 1; (Q4) | Q1, Q4 (perp_bound, finrank_sup_one, perp_sup_one, nondeg) | COMPILED |
| S3 Lemma N: columns of N mutually isotropic, column spaces of dim <= 1 | N_iso, N_col_dim, Niso, Ncol1 | COMPILED |
| S3 structure "forms l_m, K, g" | maxpt (generic element z of N whose columns span all column lines), tricho | COMPILED (replaces l_m, K) |
| S4 (P-a)/(P-b): isotropic v with tau(v^3) = tau(v^4) = 0 is 0; v_i^4 = tau(v^4)/4 if tau(v^3) = 0 | root4, iso34, root4k, pow4_iso | COMPILED |
| S4 (A1) g = 1: dim N <= 2; tau(v^3) != 0 => dim <= 1; tau(v^4) != 0 => two inactive columns | A1facts, A1, A1b, A1cols (generic_t, generic_pt) | COMPILED |
| S4 (G23) the (2,3) pattern does not exist (verifyfl's repaired version) | br_w3, G23core, G23, pattern23 | COMPILED |
| S4 (A2) g = 2: dim <= 2 and only the (2,2) pattern occurs | LemA2_proof, two_line_pattern | COMPILED |
| S4 (A3) g >= 3: dim <= 2 | caseA3 (peel, perm_two/three/four) | COMPILED |
| S4 LEMMA A: d <= 2 | LemA_red, LemA_proof | COMPILED, no hypothesis |
| S4 classification of d = 2 | tricho + two_line_pattern + A1b + A1cols (inside No22) | COMPILED in the form needed |
| S5 (B1)-(B3) | ip_phi, tau_phi, ip_col_phi, sum_phi | COMPILED |
| S5 (B-i) q = 3 => N = 0 | Bi | COMPILED |
| S5 (B-ii) q = 2, N != 0 => exists u in S, u != 0, u perp S | Bii | COMPILED |
| S5 (B-iii) b_m in C v_m | Biii | COMPILED |
| S6 preliminary: with d = 2 and three independent column lines all five columns are active | S6_active (cols_zero) | COMPILED |
| S6 type IV does not exist | HypS6 | SKETCHED: hypothesis H6 of the final theorem |
| S7 on N: tau(v w^2) = tau(v^2 w) = 0, [v,v,w,w] = 0 | typeII_ids | COMPILED |
| S7 ID7: E(t,u) -+ E(u,t) factorisations, bracket at a = 0, b^2 = 4, a^2 b = -8 | IIa_tu | COMPILED |
| S7 (II-a): v o v in C w and w o w in C v (incl. the point at infinity, S11) | Ps4, Ps4_mul, Ps4_param, ip_Ps4, IIa_pqr, sq_Ps4, HypIIa_proof | COMPILED |
| S7 (II-b): <u, w^2> = <u, v^2> = 0 from C3 at the inactive column (raw equation; verifyfl's "reader's trap (b)") | S7_elem, S7_step | COMPILED |
| S7 (II-b) conclusion: type II impossible for q = 2 | HypS7alg_of, HypS7_of | COMPILED, no hypothesis |
| S8 explicit elements v (e_a - e_b)^T of N; Step 1: <v^2,u> = <v^2,b_4> = <v^2,b_5> = 0 | col_outer, S8_elem, S8_step1 | COMPILED |
| S8 Steps 2, 3, 4 (type I excluded) | HypS8 | SKETCHED: hypothesis H8 of the final theorem |
| S9 (2,2) impossible; Lemma SL | No22, SL_of | COMPILED (from H6, H8) |
| S9 / Stage C: Theorem FL | FL_of, PEqualNP.Outside.L_gct_210_fl | COMPILED (from Lemma SL) |
FAILED: none.

### Definitions used in the statements
  M55 = Fin 5 x Fin 5 -> C, M45 = Fin 4 x Fin 5 -> C, V4 = Fin 4 -> C.
  P4 a N   = sum over injective e : Fin 4 -> Fin 5 with e k != a for all k of N(0,e 0) N(1,e 1) N(2,e 2) N(3,e 3)
             (= permanent of "N with column a deleted"; perm5_row ties it to the 5x5 permanent, P4_cols to the column form).
  SLev K   = forall Y in K, forall a, P4 a (1 + Y) = 24                                   (strongly level)
  del r    = delete row r (5x5 -> 4x5 via Fin.succAbove), rowP r = row r, rowMat r w = e_r w^T.
  tau, ip, t3, t4, br : explicit 4-term sums for tau(x), <x,y>, tau(xyz), tau(xyzw), and the bracket; col Y m; rs = row-sum map.
  phi m = 2 col_m - rs  (B_m of the blueprint, defined on all of K: no section sigma -> Y(sigma) needed).
  indep v w = (s v + t w = 0 => s = t = 0);  outer v x = v x^T;  cperm sigma = column permutation (SLev_perm: SLev is invariant).
  Ps4 j a0 a1 a2 a3 = a0 chi_0 + a1 chi_1 + a2 chi_2 + a3 chi_3 with j in the role of i (only j*j = -1 is used).
  stageA: SLev (L.map (del r)), SLev ((L inf ker (rowP r)).map (del r)), finrank L <= 4 + finrank ((L inf ker (rowP r)).map (del r)).

### The two open hypotheses (exact Lean: `def HypS6`, `def HypS8` in FL.lean)
  N := K inf ker rs.  "z spanning" := z in N and every column of every Z in N is a multiple of the same column of z (exists: maxpt).
  HypS6 : N strongly level, rs = 0 on N, finrank N = 2, z spanning, three columns a, b, c of z linearly independent, and ALL FIVE
          columns of z nonzero (proved: S6_active)  =>  False.
          (S6; uses N only. Covers type IV = patterns (2,1,1,1), (1^5); the patterns (3,1,1), (2,2,1) are also inside this
           hypothesis -- they are vacuous by the singleton-line argument of S3, which is NOT formalized separately.)
  HypS8 : K strongly level, finrank (K.map rs) = 2, finrank N = 2, Yu in K with u := rs Yu != 0 and u perp S, N inside v (x) C^5 with
          v != 0, tau v = 0, <v,v> = 0, tau(v^3) = 0, sigma a column permutation such that the columns sigma 3, sigma 4 vanish on N,
          and (Step 1, proved) tau(v^2 u) = 0, tau(v^2 b) = 0 for b = phi (sigma 3) Yu and b = phi (sigma 4) Yu  =>  False.
          (S8 Steps 2-4. b_m = phi m Yu is the blueprint's B_m u; for the active columns sigma 0..2 one has b_m in C v by Biii,
           using the elements of N produced by S8_elem.)
  Tools ready for both: Biii (b_m in C v_m), ip_phi / ip_col_phi / sum_phi, C34 and C2pol on K, SLev_perm + sa0..sa4 to put columns in
  standard position (patterns: pattern23, typeII_ids, S7_step), S7_elem (explicit elements of N from finrank N = 2 via `peel`),
  S7_step (coefficient extraction by three evaluations Yu + W, Yu - W, Yu), pow4_iso (v_i^4 = tau(v^4)/4), Q1/Q4, generic_pt,
  and the group-algebra coordinates: Ps4_param (every x in V is Ps4 j 0 p q r), Ps4_mul (entrywise product = convolution on Z/4, so
  all tau(products) become j-free polynomials in p, q, r), tau_Ps4, ip_Ps4, t3_ip_l/r, t4_ip. For S6 the parametrisation v(theta) is
  Ps4 j 0 1 theta (-theta^2/2); for S8, chi_1 = Ps4 j 0 1 0 0 and tau(v^3) = 12 q (p^2 + r^2) in these coordinates.

### Deviations from the write-up (all simplifications; none is a gap in the paper proof)
 - Prop R is proved for every y in L (not only those with row r = 0). rho = 0 by evaluating (5 + c rho) C(c) = 120 at c = -5/rho.
 - Coefficient extraction in Lemma C: evaluation at c = 1, -1, 2, -2.
 - S3/S4 use ONE generic element z of N (maxpt) instead of the forms l_m and the space K. Cases: three independent columns of z
   (caseA3: peel the other two columns), all columns on one line (A1), two lines (LemA2_proof: pattern (2,2) by peeling; patterns
   (2,3)/(3,2) contradict G23 evaluated at z). Singleton lines never need to be discussed. `peel`: finrank N <= 1 + finrank (N inf {col m = 0}).
 - (A1), case tau(v^3) != 0: pointwise x_m^3 = s x_m with s = p_2(x)/2; the support S of the generic element satisfies |S| s = 2 s.
 - (G23) coordinate-free, no WLOG v' = chi_1: v'^3 is isotropic, v perp v'^3 gives v in C v'^3 by (Q4), and
   [v'^3, v'^3, v', v'] = 8 kappa^2, kappa = tau(v'^4)/4 != 0.
 - (B-ii) by a dimension count: if S were nondegenerate and a column z_m of N nonzero, phi_m(K) would have dim 3 inside the
   2-dimensional space z_m^perp cap V.
 - (II-a) is proved in the form "v o v in C w and w o w in C v" (no row permutation, no zeta): coordinates p, q, r; if p1 = 0 or p2 = 0
   the bracket equals 8 r1^2 p2^2 resp. 8 p1^2 r2^2 != 0 (S11's point at infinity); otherwise t = q1/p1, u = q2/p2 and IIa_tu
   (the blueprint's ID7: 4(E(t,u) - E(u,t)) = (u-t)(4 + a^2 b + b^2), 4(E(t,u) + E(u,t)) = a(12 + a^2 b - b^2), a = 0 gives bracket -128)
   yields t^2 u^2 = 4 and 4 + t^4 + 4 t^3 u = 0, hence v o v = -(p1^2 t^3 / p2) w.
 - (II-b): <u, w^2> = 0 from T_e(Yu + W) + T_e(Yu - W) - 2 T_e(Yu) with W = w (e_c - e_d)^T in N; then u perp v, w and (Q4) twice.
 - The blueprint's types I/II/IV are not separate Lean definitions (draft in types.part, unused).

### Practical notes
 - Build: cd lean/fl; cat pre.part a.part b.part c.part d1.part e.part f.part g.part h.part j.part k.part o2.part p.part i5.part l2.part m.part n.part n.tail > FL.lean
   (pre: tools + P4; a: Stage A; b: Lemma C; c: B-i, Q1, Lemma N; d1: B-ii, Q4, B-iii, iso34; e: G23, generic points; f: A1;
    g: peel, maxpt, caseA3, caseLine, LemA_red; h: column permutations, pattern23, LemA2_proof; j: A1b, two_line_pattern, typeII_ids;
    k: A1cols; o2: S6_active; p: S8_elem, S8_step1; i5: tricho, HypS6/7/8, No22, SL_of, FL_of; l2: S7 reduction; m: IIa_tu, Ps4;
    n: proof of (II-a); n.tail: final theorem). This recipe reproduces FL.lean byte for byte.
   leancheck takes 45-170 s depending on load.
 - Lemma C is stated per deleted column m with the other columns m.succAbove 0..3; sa0..sa4 turn these into literals 0..4.
 - omega cannot identify two `finrank (sumZero 4)` atoms whose implicit arguments differ; use le_trans (see Bi).
 - `(Equiv.swap 0 2 * Equiv.swap 1 3) 0` does not elaborate without a type ascription; use a def (swp, swp0..swp4 by decide).
 - `-k * k'` is `(-k) * k'`; prove vector identities pointwise (funext; simp only [Pi.*]; ring / linear_combination).
 - Identities with i: never expand powers of i; keep j with hj : j * j = -1 and use Ps4_mul (certificate (a1 - a3)(b1 - b3) * hj).
 - Snapshots FL.v2 .. FL.v14.lean are all compiling states (v6: Lemma A complete; v9: S7 reduced to (II-a); v11: (II-a) proved;
   v12: HypS6 weakened by S6_active; v14 = final: S8 Step 1 proved and handed to HypS8).

STATUS 16:50: read brief/blueprint; plan = one file lean/fl/FL.lean built from parts (pre.part, a.part, b.part, c.part).
  Stage A (row expansion perm5_row, Prop R, stageA) written, first compile: 3 small errors, fixed, recompiling.
  Stage B part 1 (pc/tau/ip/t3/br, P4 -> column form, pc_expand, Lemma C = C1, C2, C34, C2pol) written, compiling.
STATUS 17:02: Stage A compiles (TA.lean exit 0). Lemma C (C1, C2, C34, C2pol) compiles. FL.lean v2 (adds B-i, Lemma N, Q1, B-ii, Q4, B-iii, types I/II/IV as defs, assembly from 5 hypotheses) compiling.
STATUS 17:03: FL.lean v2 compiles (exit 0, format 0): Stage A, Lemma C, Lemma N, Q1, Q4, B-i, B-ii, B-iii, root4/iso34, assembly from 5 hypotheses. Next: G23 core, generic-point lemmas, A1.
STATUS 17:13: FL.lean v3 compiles (adds root4k, pow4_iso, br_w3, G23core, G23, generic_t, generic_pt). Now A1 (g = 1 case of Lemma A: N inside v (x) C^5 has dim <= 2), compiling.
STATUS 17:19: FL.lean v5 compiles (exit 0): adds A1 (g = 1 case, dim <= 2), peel, maxpt (generic max-support element), perm_two/three, caseA3 (three independent column lines), caseLine, LemA_red: Lemma A reduced to LemA2 (two-line case). Final theorem now takes LemA2 instead of LemA. Next: prove LemA2 via column-permutation transport + G23.
STATUS 17:26: FL.lean v6 compiles (exit 0): LEMMA A (d <= 2) FULLY PROVED (LemA2_proof via column-permutation transport cperm/P4_perm/SLev_perm, pattern23 = G23 on the generic element). Final theorem now needs only HypS6, HypS7, HypS8 (the three cases of (q,d) = (2,2): >= 3 independent column lines / two lines / one line). Compiling v7: A1b (t3 != 0 => dim <= 1), two_line_pattern, typeII_ids, refined HypS7/HypS8.
STATUS 17:31: FL.lean v8 compiles (exit 0, format 0): A1b, A1cols, two_line_pattern, typeII_ids, refined HypS7/HypS8. RESULT section rewritten. Remaining budget used for S8/S7 preparation lemmas.
STATUS 17:37: FL.lean v9 compiles (exit 0, format 0): S7 reduced to the purely algebraic statement HypIIa (S7_elem, S7_step: <u,v^2> = <u,w^2> = 0 from C3 at the inactive column; HypS7_of, HypS7alg_of). Final theorem hypotheses now: HypS6, HypIIa, HypS8.
STATUS 17:41: RESULT rewritten for v9. Final file lean/fl/FL.lean = FL.v9.lean.
STATUS 17:53: FL.lean v11 compiles (exit 0, format 0): HypIIa PROVED (IIa_tu, Ps4 group-algebra coordinates, IIa_pqr, sq_Ps4, HypIIa_proof). S7 complete. Final theorem now has only two hypotheses: HypS6 and HypS8.
STATUS 17:57: FL.lean v12 compiles (exit 0, format 0): S6_active proved and handed to HypS6. Notes final. Remaining open: HypS6 (S6), HypS8 (S8).
STATUS 18:03: FL.lean v14 compiles (exit 0, format 0): S8_elem, S8_step1 proved; HypS8 now = S8 Steps 2-4. Notes final.
STATUS 18:04: done. Final file lean/fl/FL.lean (= FL.v14.lean), leancheck exit 0, format 0. Open: HypS6 (S6), HypS8 (S8 Steps 2-4). Reporting.
STATUS 18:13: ROUND 2 started (coordinator message: discharge HypS8 then HypS6; SL/FL stand-alone; column version). Plan: S8 Steps 2-4 coordinate-free via v-coordinates Qv (basis v, v^2, v^3 with v_i^4 = kappa; twisted convolution), no row permutation.
STATUS 18:20: resumed round 2 after a usage-limit pause; FLr.lean (= v14 + r1.part: Qv framework) compiles. Continuing with HypS8_proof.
STATUS 18:35: FL.lean v15 compiles (exit 0, format 0): HypS8 PROVED (S8 Steps 2-4: Qv framework r1.part, S8a/S8b/HypS8_proof r2.part). Final theorem now has the single hypothesis HypS6. Starting S6 (chart = special vector v avoiding all column lines; Qv coordinates with kap = 1; C3* ; patterns).
STATUS 18:57 (round 2): FL.lean = FL.v16.lean compiles (3818 lines, exit 0, format 0). Added t.part: SL6 (Lemma SL stand-alone, hypothesis HypS6 only), gap_swap5/trE5/FL_col_of (full free COLUMN version by transposition), cor_row / cor_row7 (corollaries of stage A + SL). Final theorem is now the conjunction SL + FL(row) + FL(column), single hypothesis HypS6. Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 t (.part) t.tail. Now writing S6 (chart via 6 special vectors + pigeonhole, U(theta) coordinates, C3* certificate, cases A/B/C).
STATUS 19:08 (round 2): FL.lean = FL.v17.lean compiles (4519 lines, exit 0, format 0). S6 reduced: chart (6 special vectors spv, pigeonhole over Perm(Fin 3)), U(theta) coordinates (Uv, lamL, N_coords), (C3*) certificate (star_cert, Lam_star), extension to all of N (Lam_F), algebraic core (AlgCore) with the singleton patterns (singA) and the (2,1,1,1) pattern (pairB) PROVED (core5, AlgCore_of, HypS6_of). The only remaining hypothesis is HypS6C = pattern (1^5) (theta injective), a pure statement about a submodule Lam of C^5. Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 t2 (.part) u.tail. Now doing pattern (1^5) via Mathlib Vandermonde (det_vandermonde_ne_zero_iff).
STATUS 19:13 (round 2): FL.lean = FL.v18.lean compiles (4759 lines, exit 0, format 0, axioms propext/Classical.choice/Quot.sound): HypS6C PROVED (pattern (1^5): mom3, Lam_ker, vdm3, roots5/moments5 via Matrix.det_vandermonde_ne_zero_iff, caseC_alg, HypS6C_proof). THE FINAL THEOREM HAS NO HYPOTHESES: Lemma SL + Theorem FL (row) + Theorem FL (column). Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 (.part) v.tail. Next: Lemma DS if time permits; then RESULT rewrite and report.
STATUS 19:16: ROUND 3 started (coordinator message: 2 h; targets (1) rows' DEFECT construction / normal form R1, (2) Lemma EQ + THEOREM SPLIT, (3) Lemma HYP, Hyperplane Lemma R4.1, SL_3, NCOL-S, (4) TC5 normal form). Lemma DS (chief; = converse half of R1 in the defect-0 case) is compiling as ds.part on top of v18.
STATUS 19:18: FL.lean = FL.v19.lean compiles (4928 lines, exit 0, format 0): chief's LEMMA DS proved (ds.part: P4_poly, P4_ones, DS_star, DS_i, LemmaDS: deletable row r => all row-r sums vanish; if moreover the row-r projection has dim 4 then L cap {row r = 0} is strongly level and finrank L <= 7). Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds (.part) v.tail. Round 3 next: defect construction (Prop. D), Lemma EQ, Theorem SPLIT.
STATUS 19:28 (round 3): FL.lean = FL.v20.lean compiles (5330 lines, exit 0, format 0). New: x1.part = rows' DEFECT CONSTRUCTION (Lev45, DefLine, defW K = (C(K)+C1)^perp as a submodule, defL r K = K (+) e_r (x) defW K; defL_level, defL_deletable, defL_finrank: finrank = finrank K + finrank (defW K); converse defect_conv: every level L has finrank L <= finrank L' + finrank (defW L'), L' = L.map (del r); defW_SLev: strongly level => defW = sum-zero) and verifyfl's LEMMA EQ (LemmaEQ, LemmaEQ_cols); x2.part = THEOREM SPLIT (ThmSplit: defect line C m, e_i m^T in K, <m,m> != 0 => K cap {<m, row i> = 0} strongly level and finrank K <= 4; via repl / P4_repl_add / per_rows / P4_sym = symmetry of the 5-linear form). Build: cat pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 (.part) v.tail. Compiling x3.part: defC, finrank (defW K) + finrank (defC K) = 5, Hyperplane Lemma R4.1, Lemma HYP (a), (b).
STATUS 19:31 (round 3): FL.lean = FL.v21.lean compiles (5527 lines, exit 0, format 0). New x3.part: dotL (dot product as a map to the dual), defC K = span{C(Y)} (= C(L') + C1), defW_finrank: finrank (defW K) + finrank (defC K) = 5 (so dim W = 4 - e with e + 1 = finrank defC), defect_conv' / defL_finrank' (Prop. D with "4 - e"), HyperplaneLemma + HyperplaneCor (rows R4.1), LemmaHYP_a, LemmaHYP_b (verifyfl R3.3 (a), (b)). Next: SPLIT step (3) (ker kappa form), then SL_3.
STATUS 19:43 (round 3): FL.lean = FL.v22.lean compiles (5933 lines, exit 0, format 0). New y1.part: rows' LEMMA SL_3 in zero-row form (LemmaSL3: a strongly level 4x5 space with a zero row i has finrank <= 2) -- Vp_span/Vp_nondeg/Vp_t3/Vp_finrank (the plane V' = {tau = 0, x_i = 0}), SL3_q2 (q = 2 => N = 0, via Bii), SL3_two (two-line N: NEW SHORT ARGUMENT, C3 at the inactive column + C2pol cross conditions give <u,v> = <u,w> = 0, so u = 0; replaces R3.8(d)), SL3_d2 (d = 2 => q = 0). Compiling x4.part: THEOREM SPLIT in the ker kappa form (ThmSplit_kappa), via pc_ev / P4_repl_ones / P4_lin / split_id / split_ker.
STATUS 19:52 (round 3): FL.lean = FL.v23.lean compiles (6095 lines, exit 0, format 0). New x4.part: THEOREM SPLIT in the ker kappa form (ThmSplit_kappa: K cap {all column sums 0} is strongly level, finrank <= 3), i.e. step (3) of R3.1 (split_ker: column sums 0 => <m, row i> = 0), via pc_ev, P4_repl_ones (P4 b (row i := m, other rows 1) = 6 sum_{j != b} m_j), P4_lin (explicit linear coefficient of P4 b (1 + cY)), split_id (theta <m,m> = mu <m, y^i> in the form (C_b - 24) <m,m> = (D_i m)_b <m, y^i>). Build: ... x1 x2 x3 y1 x4 (.part) v.tail. Compiling n1.part: rows' Theorem NCOL-S (a) (R4.14).
STATUS 19:55 (round 3): FL.lean = FL.v24.lean compiles (6442 lines, 287 KB, exit 0, format 0). New n1.part: rows' THEOREM NCOL-S (a) (R4.14 (a)) PROVED: NCOL_S_a: DefLine K m, sum m = 0, <m,m> != 0, e_i m^T in K, m without zero entry => row i vanishes on N = K cap {<m, row i> = 0} and finrank K <= 3. Tools: kc1 / P4_poly1 / kc1_eq (explicit linear coefficient of P4 a (B + sY) = sum over rows k of P4 a (B with row k := row k of Y)), P4_zero_row, pc_ev2 / P4_repl2 (permanent with rows m, y, 1, 1), kc1_formula (= D^(1)(Y) m in the raw form 2 sum_{j != b} c_j sum_{l != b,j} m_l), split_eig (D_i(Y) m = mu m), ncol_lin (first-order eigenvector condition, by roots5), tau_repl0. Build: ... x1 x2 x3 y1 x4 n1 (.part) v.tail.
STATUS 20:00 (round 3): FL.lean = FL.v25.lean compiles (6593 lines, 295 KB, exit 0, format 0, GUARD 0/0). Guard rules adopted (coordinator message 19:56): helper namespace renamed to PEqualNP.Outside.L_gct_210_aux.FL (pre.part, v.tail), no line begins with add_ (defW rewritten as a structure instance with add_mem' mid-line; simp lists re-wrapped). New n2.part: NCOL-S (b): ncol_core (closed form D b = -2 S m_b + 4 c_b m_b - 2 c.m and the eigenvector relations), ncol_b1 (for every Y in K the column sums of the rows != i are equal on supp m), P4_zero_row', NCOL_S_b (m with exactly one zero n: row i of N is supported at n; N cap {row i = 0} strongly level, finrank <= 2, and = 2 if finrank K = 4). Build: ... x1 x2 x3 y1 x4 n1 n2 (.part) v.tail. Next (coordinator list): Theorem FS (z1.part written), TC5 normal form DI5.2, TC5, QB/PS/PR3, FL2*.
STATUS 20:04 (round 3): FL.lean = FL.v26.lean compiles (6783 lines, 304 KB, exit 0, format 0, guard 0/0). New z1.part: verifyfl's THEOREM FS (R3.2) in row form (ThmFS: defect space Cs inside 1^perp, e_i (x) Cs inside K, <,> nondegenerate on Cs => K cap {row i perp Cs} strongly level and finrank K <= 3 + finrank Cs; fsMap = the map K -> Dual Cs). New z2.part: TC5 NORMAL FORM DI5.2 (uY, dY, e2, Ed; TC5_sum, TC5_diff, TC5_n2/n3/n4 = the four displayed identities, TC5_dd = perm[d,d,1+a,1+b] = 4 e_2(d) + 2<a+b,E(d)> + perm[d,d,a,b] (holds for all a, b), TC5_normal: DefLine K (e_0 - e_1) <=> (i) and (ii)). Build: ... n1 n2 z1 z2 (.part) v.tail. Compiling q1.part: verifyfl's LEMMA QB (R4.1).
STATUS 20:08 (round 3): FL.lean = FL.v27.lean compiles (6932 lines, 315 KB, exit 0, format 0, guard 0/0). New q1.part: verifyfl's LEMMA QB (R4.1): qA1, qA2 (explicit linear and quadratic coefficients of P4 b (1 + cY)), P4_quad, qb_lin (m b' A_k(b) = m b A_k(b') for k = 1, 2, by roots5), qA1_eq, qA2_eq (closed forms), LemmaQB: DefLine K m, sum m = 0, m != 0, Y in K => exists kappa theta2 with column sums = kappa m, (a) sum_a <y_a,y_a> = <s,s> + kappa^2 <m,m>, (b) <y_j,y_j> - <s,y_j> - kappa^2 m_j^2 = -(theta2/2) m_j for all j (the form before centring). Build: ... z1 z2 q1 (.part) v.tail. Compiling r4.part: Lev45_quad (QB (a) for every level 4x5 space), rows' R4.2 (a), (b) (single-row parts lie in the defect space and are pairwise orthogonal).
STATUS 20:10 (round 3): FL.lean = FL.v28.lean compiles (7050 lines, 321 KB, exit 0, format 0, guard 0/0). New r4.part: Lev45_quad (for every level 4x5 space: total sum 0 and sum_a <y_a,y_a> = <s,s> + sum_a c_a^2), rowE, one_add_rowE, one_add_rowE2, single_row_sum, single_row_perp, single_row_defC (rows' R4.2 (a), (b)). RESULT section rewritten. Build: ... z1 z2 q1 r4 (.part) v.tail. Next: R4.2 (c) (r5.part).
STATUS 20:15 (round 3): FL.lean = FL.v29.lean compiles (7106 lines, 325 KB, exit 0, format 0, guard 0/0). New r5.part: rows' R4.2 (c) (single_row_t3: e_i u^T, e_k u'^T, e_l u''^T in a level K with i, k, l distinct => sum_j u_j u'_j u''_j = 0), proved WITHOUT a three-row permanent: additivity in row l + symmetry P4_sym reduce it to sum_b u''_b P4 b (rows 1+u, 1+u', 1, 1) = 0 and P4_repl2. Build: ... q1 r4 r5 (.part) v.tail. Compiling f1.part: FL45 (a 4x5 level space containing a full free row has finrank <= 6; rows' corollary of SL_3 / FL2* (c)).
STATUS 20:21 (round 3): FL.lean = FL.v30.lean compiles (7221 lines, 330 KB, exit 0, format 0, guard 0/0). New f1.part: FL45 (a 4x5 LEVEL space containing the full free row e_i (x) 1^perp has finrank <= 6; = rows' corollary of SL_3 and FL2* corollary (c); the 4x5 analogue of Theorem FL): zrow (zero out row i, linear), one_add_zrow, FL45_core (the deletion vector of (Y with row i := ones) is constant and (5 + rho) g = 120), FL45. Build: ... q1 r4 r5 f1 (.part) v.tail. Compiling g1.part: rows' R4.15 (F1), (F2) (first-order constraints from single-row elements, any e).
