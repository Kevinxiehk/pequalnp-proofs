# NOTES-leanfl (role: leanfl; start 16:38, budget 2 h -> ends 18:38)

## RESULT (leanfl) -- THEOREM FL is Lean-checked modulo TWO explicit hypotheses: HypS6 (blueprint S6, type IV) and HypS8 (S8 Steps 2-4, type I).
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
