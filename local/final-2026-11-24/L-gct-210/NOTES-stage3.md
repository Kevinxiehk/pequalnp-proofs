# NOTES-stage3 (role: stage3; start 14:37, budget 90 min -> ends ~16:07)
## RESULT, ROUND 24 (stage3, STOPPED at abort) -- family B excluded outright (leaf-8 special members all closed mod PFC); case A |S| = 3 |F| = 1
##   no (PR3'); |S| = 4, 5 non-degenerate class cases unit; dim Delta = 0: x* is a function of h (sec. 44)
 (1) [exact over Q(a)] family B (contains the (2,2) and (2,1,1)-B members): pair (2,3) has NO third element for any t (13/13 charts unit) -> excluded.
 (2) [exact over Q] equal t's case A: |S| = 3, |F| = 1 complete (row 2 always a line, no (PR3')); class reduction (G-cut: w two-valued on S) makes
     |S| = 4, |F| = 0 unit in all non-degenerate charts, |S| = 5 partly; the degenerate quadric case (be = 2, h = mu(w)) is open (memory-bound).
 (3) [rigorous] dim Delta = 0: every row of x* is a function of h columnwise (six parameters); exact system queued as ST3-DLT0D, not run.
 (4) Open at abort: generic-member exclusion of leaf-8 configurations only numerical; case A deg, |F| = 2, |S| = 4 |F| = 1; dim Delta = 0;
     common-zero-coordinate lemma (L_gct_111 noted: sum dim Z_i <= 4 reproves SR5/SR2111).

## RESULT, ROUND 23 (stage3, 07:25 UTC) -- the k_N = 2 configuration of leaf 8 (1,1,1,1,0) is CLOSED (M0 excluded, M1 -> free column -> PFC);
##   the round-22 "1-parameter special family" is only two members; case A |S| = 3, |F| = 0 excluded; family B (2-column block) is what is left (sec. 43)
 (1) [EXACT over Q(w), t a ring variable; corrects round 22 in place] the k_N = 2 block family (m = (1,w^2,w,0,0); n_2, n_3 an orthogonal basis of P):
     pair (0,1) has a third element only for t in {0, -1/4, -1/3, 1}; by Round 18 (C) all other members are excluded. Mod symmetry two members
     survive, M0 = {(0,0,0,1,-1), (2,2,2,-3,-3)} and M1 = {(1,1,1,1,-4), (1,1,1,-3,0)}. (The parameter is not removable by symmetry, but this is moot.)
 (2) [exact + rigorous] M0 is IMPOSSIBLE: pair (1,2) forces (r_0 - r_4) (x) e_j (j = 3,4); pair (0,1) forces (r_2 - r_4) (x) e_k (k <= 2: not orthogonal
     to r_0 - r_4, contradiction) or (r_2 - r_4) (x) mbar (sigma_3 coefficient <m, mbar> = 3 != 0, contradiction).
     M1 forces (r_3 - r_4) (x) e_4 (pair (0,1)), then (r_1 - r_4) (x) e_4, (r_0 - r_4) (x) e_4 (pairs (0,3), (1,3) + orthogonality): a free column on
     four rows, so dim L <= 8 by Lemma PFC (given (SL_m0)). => k_N = 2 closed (M1 conditional on PFC, like the rigid and k_N = 4 special members).
 (3) [numerical] special members for (2,2) and (2,1,1) exist; all special members found are block type (3 + 2 column split). (2,1,1) member A lies in the
     k_N = 2 family (already excluded); (2,2) and (2,1,1) member B form ONE family B: m' = (a,a,a,1,-1-3a) (6a^2+3a+1 = 0) on rows 0,1, an orthogonal
     basis of V_Z on rows 2,3. [exact] In family B pair (0,1) has a 2-dim family of "free 2-column block" third elements p (x) e_3 + q (x) e_4
     (rows 2,3,4; s(p) = s(q) = 0, <p,q> = 0) for EVERY t: a genuine block-PFC case, OPEN.
 (4) [exact over Q] equal t's, case A, |S| = 3, |F| = 0: EXCLUDED (row-projection-hinge sweep, 30/30 combinations unit: every solution has all row
     projections 1-dim). |F| = 1: 6/10 charts have row 2 always a line (no (PR3')); 4 charts, |F| = 2 and |S| = 4, 5 open.
 (5) Upstream L_gct_111 => sum_i dim Z_i <= 4 for the single-row parts of any level space (reproves SR5, SR2111 at once; transposed: column
     parts sum <= 4). L_gct_110 is a sufficiency (direct-sum) lemma: it explains the block members but gives no upper bound, so no block-PFC from it.
 (6) Not reached: dim Delta = 0 with U' = W_h explicit; the common-zero-coordinate lemma.

## RESULT, ROUND 22 (stage3, 06:19 UTC) -- equal t's: case B closed by hand, case A |supp d| = 2 empty (exact); leaf-8 "two special members"
##   is FALSE (a new 1-parameter k_N = 2 special family); dim Delta = 0 reduced (sec. 42)
 (1) [rigorous] equal t's, case B (w constant on supp d): e_2(w) = e_3(w) = 0 and W = span(w(w-s), w^2(w-s)) in U'; dim W = 2 forces d = 0, dim W <= 1
     forces w = e_j (coordinate vector) with h = e_j - d and the column element (e_0 - e_1) (x) e_j. The same dichotomy reduces dim Delta = 0 to h = e_j
     (H a free 3-row column) or dim W_h = 2 (U' explicit).
 (2) [EXACT over Q, staged refinement] equal t's, case A, |supp d| = 2: no space at all (all partitions, all x*-charts, both c(x*) cases).
     |supp d| = 3: c(x*) = w o d empty; c(x*) = 0 non-unit, but with h != 0 the x*-support is forced into supp d and an exact 2-plane slice gives only
     degenerate spaces (single-row elements); |supp d| = 4, 5 open.
 (3) [numerical + exact jump check] leaf 8: special members of (1,1,1,1,0) are NOT just the two known ones -- k_N = 2 has a 1-parameter special family
     (m = (1, w^2, w, 0, 0), w^3 = 1; n_2, n_3 any orthogonal basis of {(al,al,al,be,ga) : 3 al + be + ga = 0}); its third elements live in the column blocks
     {0,1,2}, {3,4} (no single free column), so PFC does not apply directly.
     [<< CORRECTED r23 (sec. 43 (D), exact): the members exist for every orthogonal basis, but pair (0,1) has a third element only for
      t in {0, -1/4, -1/3, 1}; all other members are excluded by Round 18 (C). Survivors mod symmetry: TWO members M0, M1 -- not a family. >>]
 (4) Not reached: the common-zero-coordinate lemma.

## RESULT, ROUND 21 (stage3, 05:51 UTC) -- dim Delta = 1 with distinct t's CLOSED for stratum (II) (ka = 1 empty over Q via the 3x4
##   restriction); leaf-8 special k_N = 4 member -> free column on four rows -> PFC (sec. 41)
 (1) [rigorous cuts + EXACT over Q] on the dim-Delta-1 special locus U' = span(d, d o d) vanishes at column j0, so X minus column j0 is a LEVEL
     3x4 space; the rank-one family computation there plus the sigma_2 cross term give s(r_i') = 0, <r_0', d'> = p_3(d), <r_1', d'> = <r_2', d'> = -p_3(d),
     <r_0', d' o d'> = 0. With these cuts the ka = 1 system (c(x*) = d o d) is UNIT over Q (slimgb, 0.8 s). With sec. 40 (E), (H): dim Delta = 1 with
     distinct t's gives only stratum-(III) spaces (r_0 || e_{j0}), never stratum (II) proper.
 (2) [exact over Q, under Lemma PFC] leaf 8, z = (1,1,1,1,0), the special k_N = 4 member W = (e_0-e_1, e_2-e_3, (1,1,-1,-1,0), (1,1,1,1,-4)): the pairs
     (0,1), (0,2), (1,2) force the column elements (e_2-e_4)(x)e_4, (e_1-e_4)(x)e_j, (e_0-e_4)(x)e_j'; column elements in different columns need
     orthogonal vectors (sigma_2 = -<c,c'>), so all lie in column 4: a free column on rows {0,1,2,4} -> dim L <= 8.
 (3) equal t's and dim Delta = 0: rigorous structure (sec. 41 (E), (F)), exact charts > 60 s at P1 even with cuts; numerics without stratum hinges
     give only degenerate spaces (single-row elements). OPEN.

## RESULT, ROUND 20 (stage3, 05:21 UTC; interrupted 04:25-05:15 by the usage limit) -- staged refinement closes the colel sigma = 0 charts:
##   stratum (II) proper has NO point on the column-element locus (exact over Q); dim Delta = 1 reduced to the special locus (sec. 40)
 (1) [EXACT over Q] colel sigma = 0: 14 orbit representatives unit with staged chart refinement, 64/64 by symmetry; with sigma = 1 (64/64): on the
     column-element locus stratum (II) proper is empty. CONDITIONAL THEOREM: ST3-TWOCOL unit over Q => stratum (II) of (PR3') empty (dim Delta = 2) and
     every stratum-(III) space with dim c(H) = 2 carries a column element.
 (2) [rigorous hand proof] dim Delta = 1 with distinct t's forces the special locus (some h_i = e_{j0}; via U' = span(d, d o d), the classification of h,
     and G in U' => g_0 g_1 g_2 = 0). [EXACT over Q, staged refinement] on that locus with c(x*) = 0, r_0 vanishes off column 4: stratum (III) only
     (numerically 6/6 with a column element). Open: c(x*) = d o d (ka = 1, charts time out), t_i = t_k for one pair, dim Delta = 0.
 (3) ST3-TWOCOL-Q-STAGED (r20/staged_twocol.py) appended to QUEUE.md; one unrefined chart over Q > 300 s and > 0.9 GB in the pool.
 (4) CAUTION recorded: a first dim Delta = 1 H-part test was unit only because of a non-WLOG normalisation (fixed; sec. 40 (B)).

## RESULT, ROUND 19 (stage3, 03:36 UTC) -- the column-element route made concrete: exact follow-up done for sigma = 1; big-slot TWOCOL spec
##   queued (decisive run = over Q); (t2) extensions of both X0 shapes fail numerically; circularity bookkeeping (sec. 39)
 (1) [EXACT over Q] on the column-element locus x* = w (x) e_J of the unified system (dim Delta = 2), stratum (II) proper is EMPTY for sigma = 1
     (64/64 hinged charts unit); sigma = 0: 24/64 unit, 40 timed out at 60 s (rerun needed). So "x* is a column element" (ST3-TWOCOL, 16 charts,
     decisive run OVER Q = verify2's route (a)) would give: stratum (II) of (PR3') empty and every stratum-(III) space with dim c(H) = 2 carries a
     column element. Not covered: dim Delta <= 1.
 (2) [rigorous] closed form of the D_3-linear conditions (Phi_pq) and the local-global structure of the x*-linear system (sec. 39 (B)); a full
     hand proof of "injective off the special locus" was NOT reached.
 (3) [numerical] (t2): seeded extension of X0 shape (a) 0/4, shape (b) 0/3 (LM forces g = h = 0): evidence that (t2) dies at the extension step.
 (4) [exact] leaf 8: the special k_N = 4 member (orthogonal basis with disjoint supports) is NOT excluded by the outside-row test (third elements
     exist for every pair, column-4 type) -- needs a PFC-type continuation like the rigid member.
 (5) circularity (target 4): the transposed elements break the circle unless all lie in one column; then Z'_j of L^T has a common zero coordinate.

## RESULT, ROUND 18 (stage3, 02:10 UTC) -- (M3) (X0 core empty) is FALSE numerically (two non-degenerate X0 found); leaf-8 rigid member
##   -> PFC; generic members of all (1,1,1,1,0) configurations excluded; stratum (III) = the r_0 || h_0 part of the stratum-(II) system (sec. 38)
 (1) [numerical, fresh-point verified 2e-13] the (t2) core X0 = Y_ab (+) Y_cd EXISTS without single-row elements, in two shapes: (a) Y_ab contains
     (e_0, -e_0) (dim c(P_a) = 1, one column element (e_a - e_b) (x) e_0); (b) main case dim c = 2, NO column element, column-block shape (Y_ab
     on columns {0,1,4}, Y_cd constant on {0,1,4}). So (t2) is not closed by X0; ST3-X0MAIN (queued 02:05) asked to be CANCELLED (append 02:13).
     "Every (t2)-type structure carries a column element" is false at the X0 level; it can only hold for the stratum-(III) spaces X_re.
 (2) [rigorous] stratum (III) = solutions of the hinge-free "H-plane + zero-column-sum x*" system with r_0 || h_0 (the two kernel lines K_1,
     K_2 of a stratum-(III) space span an H-plane). Targets 1 and 2 are one computation; the special locus gives exactly family (E) (exact).
     Exact cost of "every stratum-(III) defect-<=2 space has h_0 a coordinate vector (=> column element)": r18/st3h.py 'pp' charts (h_0 with two
     nonzero entries), 3 pair-orbits x 2 sigma-charts x 6 x*-charts = 36 charts, each > 110 s and ~1 GB at P1 -> big slot, many hours over Q.
 (3) [exact over Q(i), under Lemma PFC] the leaf-8 rigid member (m = (1,i,-1,-i,0), w = (1,1,1,1,-4)) forces (e_4 - e_l) (x) e_4 in L for l = 0,1,2:
     a free column on four rows -> dim L <= 8. So the 'three m + w' configuration of (1,1,1,1,0) is closed (rigid member conditional on (SL_m0)).
 (4) [numerical] random members of (2,2), k_N = 2, (2,1,1), k_N = 4 of (1,1,1,1,0): outside-row kernel exactly gauge + (c (x) 1) for every
     pair, so X_{rk} is 2-dim: generic members of ALL remaining configurations are excluded in the regime; special members (finite lists) remain.

## RESULT, ROUND 17 (stage3, 01:11 UTC) -- (PR3) and (PR2-split') REFUTED (explicit exact counterexample); corrected (PR3'); (S3-a) route now
##   misses exactly type (t2); the counterexample family is harmless for a 9-dim space (FO2_0 <= 8); stratum (II) special locus empty (sec. 37)
 (1) [EXACT, sympy over Q; independently re-checked by the coordinator] X = span(x_b, x_c, x_d) (0-indexed rows 0..2, columns 0..4),
     x_b = [[-1,0,0,0,0],[1,1,-1,0,0],[0,0,0,0,0]], x_c = [[-1,0,0,0,0],[0,0,0,0,0],[1,0,0,1,-1]], x_d = [[1,0,0,0,0],[rho,0,0,0,0],[-1-rho,0,0,0,0]]
     (rho not in {0,-1}) is a 3-dim LEVEL 3x5 space, row projections (1,2,2), NO single-row element, DEFECT 2; N = X (+) e_3 (x) Z with
     Z = {(-2s-2r, s, s, r, r)} is a 5-dim 4x5 level space violating (PR2-split'). General family by hand: column-0 part + b e_1 (x) (0,y) +
     c e_2 (x) (0,z), s(y) = s(z) = <y,z> = 0, y o z in span(y,z). It lies in stratum (III). (PR3)/(PR2-split') flagged REFUTED in place (rounds
     10, 11, 16 blocks; secs. 30, 31; handover). NAME CLASH: verifyfl's THEOREM PR3 is a different, verified statement -- not affected.
 (2) [numerical, 19 members incl. degenerate] dim T_1(N) in {9, 10}, FO2_0(N) <= 8 everywhere: no member is the L_r of a 9-dim level space;
     NO refutation lead.
 (3) (PR3') := all three row projections EXACTLY 2-dim (strata (I), (II)): open. In (S3-a): type (t0) and (t1) of L_e reduce to (PR3') (one
     excluded L_r suffices; in (t1) take r in the m = 2 pair); type (t2) (two disjoint pairs with m_kl = 2) makes every X_re stratum (III), so
     the (PR2-split') route is dead there; candidates: FO2_0 <= 8 for (t2)-type L_r, the X0 core of sec. 30 (E) (expected dim -3), (Q4).
 (4) [EXACT over Q] stratum (II) on its special locus (some h_i = s e_j): every solution has x* = w (x) e_j, i.e. it is a stratum-(III)
     counterexample -- stratum (II) proper has no point there. [numerical] the x*-linear conditions have full rank at generic H-points, so
     stratum (II) reduces to "rank-drop locus = special locus" (open). Item 14(a) NOT queued: non-unit by construction without row hinges.
 (5) [numerical, in progress] stratum (III) probe: the first solution has p = e_4 and a column element, i.e. the shape of family (1).
 (6) LEAF 8, z = (1,1,1,1,0): Fourier sub-case IMPOSSIBLE in the regime [rigorous]: X_{rk} would be 2-dim (< lam = 3). Configuration
     'three m + w' (k_N = 1 and (3,1)): excluded by the same mechanism whenever m has no zero entry [hand + exact rank loci over Q; R1 charts
     w0/w4 still running]; the single rigid member m = (1,i,-1,-i,0), w = (1,1,1,1,-4) forces column elements in column 4 and is compatible with a
     free column on four rows (exact 7-dim level space) -> Lemma PFC lead. Open: k_N = 2, k_N = 4, (2,2), (2,1,1).
 (7) Item 14(a): generator r16/st2_bigQ.py + driver r16/run_st2Q.sh written and smoke-tested, but NOT queued (non-unit by construction:
     the hinge-free stratum-(II) system contains the counterexample family; the hinged version is ~10^3 jobs). No QUEUE line appended.

## RESULT, ROUND 16 (stage3, 00:36 UTC) -- leaf 8: THREE z-patterns CLOSED (Theorems SR5, SR2111); (PR3): structure of stratum (II),
##   no proof yet (sec. 36)
 (1) THEOREM SR5 [rigorous hand proof + one tiny exact check over Q, calibrated]: NO level space has nonzero single-row elements in all
     five rows (so z = (1,1,1,1,1), (2,1,1,1,1) are impossible; by transposition also for single-column elements). Tools: single-row
     vectors of distinct rows are orthogonal; RANK-ONE FAMILY LEMMA (c (x) m on k rows => e_1..e_k(m) = 0 and every outside single-row
     vector is orthogonal to m^0..m^k); e_1 = e_2 = e_3 = 0 => >= 4 distinct entries; Z22's dim(T o T) = 3 for totally isotropic planes.
 (2) THEOREM SR2111 [hand + 20/20 exact charts over Q, calibrated]: z = (2,1,1,1,0) is impossible.
 (3) Leaf-8 table now: impossible (1,1,1,1,1), (2,1,1,1,1), (2,1,1,1,0) [new], two 2's [Z22], (1,0,0,0,0) [F4b-X]; OPEN (1,1,0,0,0), (1,1,1,0,0),
     (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0) -- the single-row level conditions alone are satisfiable there (Fourier family, orthogonal bases),
     so these need the regime. General cut recorded: z_r + dim sum_{i != r} Z_i <= 4 (Lemma S3-2).
 (4) (PR3) [rigorous formulas + numerics]: closed forms of c, D_2, D_3; stratum (II): on H, D_2 = sum a_i a_k F_ik, D_3 = a_0 a_1 a_2 G, and if [<< REFUTED r17: (PR3)/(PR2-split') are FALSE as stated -- explicit counterexample, sec. 37 (E); only (PR3') (all three row projections EXACTLY 2-dim) survives >>]
     dim c(H) = 2 then U' = c(H) and x* can be taken with zero column sums. The H-part alone is a 4-DIM family (numerical), so it does not cut;
     the full stratum-(II) system is big-slot size (COMPUTE item 14; one P1 run in progress at the end of the round). All 14 stored
     defect-<=2 examples have K_1 = K_2 (= the single-row element) and dim c(X) = 2: they are "stratum (II) with two kernels merged".
     (PR3) needs EXACT char-0 proofs (open hypothesis, non-empty closed variety: RED-p does not apply).
 (5) No uniform argument for z = (2,0,0,0,0) found.
 (6) FOURIER LEMMA [rigorous]: if four rows carry the same single-row vector m (then m = la(zeta^j)), L has NO proper 2-row elements;
     plus a full classification of the single-row configurations of (1,1,1,1,0) (sec. 36 (H)). The full stratum-(II) exact system
     (25 unknowns) exhausts 1.5 GB at P1 in 194 s: big-slot (COMPUTE item 14).
 (7) modStd check (COMPUTE-ERRATA [N]): NONE of my recorded exact verdicts used modStd (STATUS line in sec. 36).

## RESULT, ROUND 15 (stage3, 23:45 UTC) -- (alpha1) |supp W| = 2 and 4 CLOSED (at P1; char 0 except one lemma half) => case (alpha) of [T31]
##   split A for m0 is unit at P1 in every piece (sec. 35)
 (1) LEMMA S2 [parallel half: EXACT over Q and at P1; non-parallel half: at P1 only -- over Q chart a1 timed out (slimgb, 20 min, 1.4 GB), stopped]: if a(x)(1,1,1,1,-2) + b2(x)(e_2-e_4) + b3(x)(e_3-e_4)
     (a != 0, b2, b3 isotropic) has its line's defect in C m0, then b2 = 0, b3 = 0 or b2 = b3. Calibrated: without the open condition
     t2 != t3 the system has a 1-dim solution set (the S2= family, also found numerically: 7/100 hinged starts, all b2 = b3).
 (2) [rigorous hand proof given S2] (alpha1) |supp W| = 4 IMPOSSIBLE: the forms c_j|f^perp are four points of an affine plane; S2
     elements for each pair force (general position / three collinear / one coincidence) W to rank one or two parallel columns, both
     excluded; degenerate configurations give rank-one elements (R8.8).
 (3) [hand given S2 + S-SPEC, + exact] (alpha1) |supp W| = 2 IMPOSSIBLE: the forms sig, gam_2, gam_3 leave only (c1) n_2 = v, n_3 special and
     (c3) n_2 = n_3, v special; their 7-unknown systems on the 3-dim K_f are UNIT: 12/12 over Q and 12/12 at P1 (calibrated: degree-2
     truncation and the S2 line non-unit).
 (4) CONSEQUENCE: all of (alpha) ((alpha0) sec. 33-34, (alpha1) |supp 3| sec. 34, |supp 2, 4| here) is unit at P1 => with verifyfl's (beta)
     (32/32 at P1) split A of [T31] for m0 is covered at P1; char 0 by Lemma RED-p once [DC3], [T22] are in at P1. verifyfl's queued (alpha)
     KT charts become a cross-check. Independent char-0 proof of (alpha): only the non-parallel half of Lemma S2 over Q is missing.
 (5) COMPUTE item 13 (cuts for gen_m0a + update). (PR3): stratification only (sec. 35 (E)); no exact run this round.

## RESULT, ROUND 14 (stage3, 22:50 UTC) -- split A of [T31] for m0: (beta) covered mod P1 by verifyfl; (alpha0) unit at P1 too; (alpha1) open
 (1) verifyfl's (beta) run covers my (beta-2): audited gen_m0a.build_beta (all five columns nonzero, conic charts incl. infinity, correct defect
     encoding). COMBINATION RULE: it is UNIT MOD P1 = 2147483629 with an open condition, hence a char-0 proof only via Lemma RED-p once ALL of
     (alpha) is unit at P1. So: "(beta-2) covered mod P1; char 0 once (alpha0) AND (alpha1) are unit at P1".
 (2) (alpha0) at P1: every piece of sec. 33 rerun in characteristic P1 (S-SPEC 3/3, W4 3/3, supp-3 36/36, P2 18/18, special-W enumeration exact
     over F_P1) -- all UNIT, calibrations as in char 0 (new: P2 truncation non-unit). (alpha0) is therefore unit both in char 0 and at P1.
 (3) [rigorous] independent hand proof that |supp W| = 3 dies already at the quadratic level (A_4^*A_4 = 5 impossible), answering verify2's
     "weak calibration" remark for that case.
 (4) (alpha1) [hand normal form + exact]: A_j = n_j (x) psi_j + eps_j rho e_j (x) f (n_j isotropic, e_j the unit vector of n_j^perp, rho^2 = k);
     |supp W| = 3: ALL 96 systems UNIT over Q(i) and at P1 (calibrated: the quadratic level alone is consistent, numerical solution);
     |supp W| = 2 and 4: 18 + 9 systems running (sec. 34 (G)). If they come out unit, split A for m0 is closed in char 0 for (alpha) and,
     with verifyfl's (beta) at P1 plus (alpha) at P1, (SL_m0)'s [T31-A] is complete at P1.

## RESULT, ROUND 13 (stage3, 22:40 UTC) -- (alpha0) of [T31] split A for m0 IS IMPOSSIBLE (all supports); (beta-2), (alpha1) open
 (1) [rigorous + exact over Q] LEMMA S-SPEC: an element (s/2)(x)(1,1,1,1,-2)^T + b(x)(e_k - e_4)^T (s != 0 in V, b isotropic) whose line has defect
     in C m0 has p_3(b) = 0: b lies on one of the 6 SPECIAL isotropic lines (row permutations of chi_1). [line conditions 0-dimensional, 36
     solutions; with p_3(b) != 0 the unit ideal on all charts.]
 (2) [rigorous] (alpha0) reduces to this "shape S" for every support of W (gauge element mu Z, two linear conditions on s); with S-SPEC:
     every column of W (|supp| = 4), resp. v and the extra directions n_k (|supp| <= 3), are SPECIAL.
 (3) [exact over Q(i), calibrated by a degree-<=2 truncation that stays non-unit] |supp W| = 4: the only admissible W are the three
     configurations of four special lines omitting an opposite pair (exhaustive enumeration incl. repeated lines); for each, the
     9-unknown system is the UNIT ideal. |supp W| = 3: all 36 (v, n_3) systems UNIT. => (alpha0) impossible for |supp W| = 3, 4.
     |supp W| = 2: v drops out -- K contains the plane P2 of (J); all 18 plane systems UNIT. => (alpha0) IMPOSSIBLE (sec. 33 (J)).
 (4) (beta-2): conic coordinates make all conditions rational; WLOG all columns at finite t (6-point orbit argument); moments + degree 3 and
     moments + degree 4 are separately solvable (12/12, 10/12), so no single-block identity -- the exact run (10 variables, degree 12) is too
     heavy here; with verifyfl (COMPUTE item 12).  (alpha1): the shape-S trick falls one dimension short; with verifyfl.

## RESULT, ROUND 12 (stage3, 22:05 UTC) -- [T31] split A for m0 = (1,1,1,1,-4) cut into explicit small cases (sec. 32, COMPUTE item 12)
 (1) [rigorous] LEMMA SA1: in split A (all five columns of Z isotropic) Theta(., Z) == 0 iff Z has a zero column, and then z_4 = 0 (two
     nonzero columns with different m would make s^*g of rank <= 2). So split A = (alpha) Z = [W|0] with LINEAR side conditions
     <b_j(Y), z_j> = 0, plus (beta) all columns nonzero. (Generalises verifyfl's R8.2(ii).)
 (2) [rigorous + exact over Q] (beta) splits by the (u,v)-coordinates of the isotropic columns (span(U,V) totally isotropic in C^5):
     (beta-1) rank-one Z is IMPOSSIBLE (hand reduction to a 7-variable system, unit ideal over Q); left: (beta-2), a maximal isotropic plane.
 (3) [rigorous] normal forms for (alpha): A_j^* z_j = 0, A_j^*A_j = P_1 (j <= 3) of rank <= 1; for P_1 = 0 explicit columns
     y_j = (s + <phi_j,s> n_j)/2, y_4 = -s - (1/2) sum <phi_j,s> n_j with spanning phi's (R8.8's rank-one identity kills the rest).
 (4) [numerical, calibrated] Z-family: every solution has a zero column (55 free starts); hinged test of (beta): calibrations 3/20 and 8/40,
     target (all five columns nonzero) 0/190 -> (beta) empty numerically.  Exact (beta-2) and (alpha) systems are specified for verifyfl (COMPUTE item 12); unreduced (beta) charts are
     too heavy here (msolve segfault at 930 MB, Singular > 3 min / 630 MB).

## RESULT, ROUND 11 (stage3, 21:35 UTC) -- the exceptional space ncdef_d5_e2_k1_s1 is NOT a refutation lead: it belongs to an explicit
##   family that lies in no 9-dim level space (exact for three rational members of its locus, numerical for the stored one), and the whole
##   family reduces to ONE (5,1) question (Lemma PFC). No 8- or 9-dim level space found. (sec. 31)
 (1) [rigorous] ncdef = a member of N(w2,w3) = F_4 (+) C e_2 w2^T (+) C e_3 w3^T (F_4 = free column on four rows), level iff <w2,w3> = 0
     (moment proof). dim T_1 = 10 generically (FO2 bound 7), = 13 on H = {w2 o w3 in span(w2,w3)} (columnwise hyperbola) and on D; the stored
     member lies on H [numerical identification: third singular value of (w2, w3, w2 o w3) = 0].
 (2) [exact over Q] for three rational members of H (two-column w2, and two with four distinct entries): the common null cone K of all q_m
     on T_1/N is a union of five rank-3 quadric surfaces (Krull dim 3, minAssGTZ) => no plane in K => every level space containing these
     members has dim <= 7.  [numerical, calibrated on the 7-dim lift] stored member and random H / D members: K contains no P^3 (no 9-dim
     extension); random H, D: K is a curve (no 8-dim extension).
 (3) [rigorous reduction] LEMMA PFC: a level space containing a free column on four rows has dim <= 8 unless some 5-dim 4x5 level space has
     defect line C(1,1,1,1,-4) (transpose + (Z3) + SL + FK, the mechanism of Theorem FL). This covers the whole ncdef family and the domino
     branch of configuration (II); the remaining (5,1)_{m0} case is in COMPUTE-stage3.md item 10.
 (4) [numerical] queued probes (coordinator, since 21:11): (PR2) 0/133, (PR2-split') 0/155 target starts (calibration rates 1/21 and 13/31):
     evidence for both. (PR2-split') <=> (PR3): a 3-dim 3x5 level space with rows in 2-planes and no single-row element has 3-row defect [<< REFUTED r17: (PR3)/(PR2-split') are FALSE as stated -- explicit counterexample, sec. 37 (E); only (PR3') (all three row projections EXACTLY 2-dim) survives >>]
     >= 3 (generic: 4). The (2,1,0,0)/(2,2,2,2) examples have no common column structure (no classification yet). Fixed-line probe for
     (4,1)/(5,1) with defect line (1,1,1,1,-4): 0/14, but its calibration is weak and line-dependent -> inconclusive.

## RESULT, ROUND 10 (stage3, final 21:15 UTC) -- (PR2) NOT proved; reductions sharpened (one claim corrected); a row-kernel
##   FO2 census excludes every known 5-dim 4x5 space but one as the L_r of a 9-dim level space (sec. 30)
 (1) [rigorous] (S3-a) follows from EITHER (PR2) (L_e: 5-dim 4x5 level, all row projections 2-dim, no single-row element) OR
     (PR2-split') (L_r = X_re (+) e_e Z: 2-dim single-row part, NO other single-row element, all row projections <= 2); pure 4x5 [<< REFUTED r17: (PR3)/(PR2-split') are FALSE as stated -- explicit counterexample, sec. 37 (E); only (PR3') (all three row projections EXACTLY 2-dim) survives >>]
     statements, any defect. CORRECTED: without "no other single-row element" (PR2-split) is FALSE numerically -- 14 level spaces of
     shape single-row (2,1,0,0) / row projections (2,2,2,2) found (fresh-point errors <= 2e-12): exactly the L_r-shape of the mixed
     pattern (2,1,..).
 (2) [rigorous] row-kernel bound: for every level L and row r, y_r = e_r 1^T - J/5 lies in T_1(L_r) and in no level space, so
     dim L <= dim T_1(L_r) - 1; with sigma_2-isotropy, dim L <= FO2_0(L_r) (largest sigma_2-isotropic subspace of T_1(L_r)).
 (3) [numerical census, 60 stored 5-dim 4x5 level spaces] FO2_0 <= 8 for 58; s9 has FO2_0 = 9 but full FO2 8; ncdef_d5_e2_k1_s1 keeps
     FO2 bound 9 (row projections (1,1,2,2)). All fourteen (2,1,0,0)-shape spaces (re-run 21:12, 63 spaces): FO2_0 = 7 (13) or 8 (1), so none is the L_r of a 9-dim (even
     8-dim, for thirteen of them) level space: evidence for (2,1,..). Non-split (5,2) spaces: FO2_0 = 7, 8.
 (4) [rigorous] (t2) core X0 = Y_ab (+) Y_cd in closed form ((X2)-(X4)); expected dimension -3. [numerical, uncalibrated] no (PR2), (t2),
     X0 space found (0/48, 0/64, 0/3); (PR2-split') target 0/32 so far (calibration 13 of 31 starts hit the (2,1,0,0) shape).
 (5) [exact attempts] (t2)/X0 systems (34-36 unknowns) too heavy here (one chart > 9 CPU-min, 1.5 GB); specs: COMPUTE-stage3.md items 8, 9;
     QUEUE.md line S3-PR2probe (calibrated probes, 4 cores x 2 h, ~150 MB each). SP8 does not apply to the mixed patterns (needs z_i = 3).

## RESULT, ROUND 9 (stage3, final 20:35 UTC) -- F4b IS IMPOSSIBLE (Theorem F4b-X, sec. 28), so z = (1,0,0,0,0) is impossible;
##   (S3-a) reduced to a pure 4x5 statement (PR2) (sec. 29 (D)); S3-1: plain LM cannot calibrate (singular solution points, sec. 29 (A))
 (1) [rigorous hand proof, NOT yet verified] MOMENT LEMMA (sec. 28 (M1)-(M4)): for the twisted free column N = Phi (+) C e_e w^T of F4b the
     level conditions read prod_j (1 + <t, v_j>) = 1 + s sum_r t_r mod squares (v_j = column j of the y-rows), and (i)-(iii) become
     POINTWISE column conditions 4 e_4(v_k) = s e_3(v_k), (4 u_k - s(u)) pi_T(v_k) = s u_k e_2(v_k|T) (u = w, p). Hence s != 0, and for
     s = 1 the y-rows are of type C1 (one all-ones column, y_r = e_k0 + u_r with disjoint-support zero-sum u_r) or C3 (explicit, 2 parameters).
     Numerical completeness check (sec. 28 (E)): 12/12 converged starts are C1 or C3, nothing else; s = 0: none.
 (2) [exact: Singular std over Q on all charts; msolve at 3 primes as cross-check] every type is eliminated by the core level conditions
     + (i)-(iii) + the forced non-degeneracy (y_r, g_r) independent (C3 with r1 = b and C1 with u_a, u_b != 0 by LEVEL alone); the C1 run
     contains the free-column case and re-derives Theorem FC independently. Generator calibrated on the exact core M_0. Table: sec. 28 (M5').
 (3) COROLLARY: z = (1,0,0,0,0) impossible (F1, F3, F4a: sec. 26, not yet verified; F4b: here).
 (4) [rigorous reductions + numerical census] every pattern with z_e = 2: (S3-a) <== (PR2) "no 5-dim 4x5 level space without single-row
     elements has all four row projections of dim 2" (lam_re = 3 forces dim pi_r(L_e) = 2); census 50/50 stored 5-dim 4x5 spaces consistent
     (the only all-2 one, clm_p4_d5_defect2_s9, has two single-row elements). Also: any 9-dim level L with a_e = 1, z_e >= 2 contains
     L(L_e) for a (5,2) space L_e unless L_e is a (5,1) space, and dim L <= dim T_1(L(L_e)); census 27/27 (5,2) lifts have dim T_1 = 8.
     For z_e = 1 the first-order bound alone is not enough (dim 9 occurs, sec. 29 (C)).
 (5) S3-1 [numerical]: the known 7-dim lifts are singular points of the sampled level system (Jacobian kernel 11 > tangent dim; linear
     convergence even with slices): random/seeded/planted LM stalls at 1e-5 .. 1e-8, so no LM negative means anything; spec for long runs /
     deflation in COMPUTE-stage3.md item 6. No 8- or 9-dim level space found (none expected to be found by this method as it stands).

## RESULT, ROUND 8 (stage3, 20:31; round stopped early by the coordinator -- see handover/HANDOVER-stage3.md) -- details in section 27
 (1) [exact] + [modular, 3 primes] THEOREM FC: the FREE-COLUMN SUB-FAMILY of F4b (y_a = y_b = y_c = y_d = e_1) is impossible: the system
     "core level + (ii'),(iii')" is the UNIT ideal on all 81 charts (Singular std over Q; msolve at p = 65521, 2147483629, 2147483497);
     calibration "core level only" is NON-unit on all 81 charts at the 3 primes (and M_0 is an exact solution).
 (2) [rigorous] if y_a, y_b, y_c, y_d are pairwise parallel then the core is of free-column type. So F4b is left only with y_r NOT all parallel.
 (3) [rigorous remarks] z = (2,1,..) is a sub-case of the z = 2 structure (S3-a) with one extra single-row element; degree-1 identities.
 (4) COMPUTE-stage3.md corrected (errata A1, A2). [numerical] Newton search for general F4b level cores: inconclusive.

## RESULT, ROUND 7 (stage3, 20:10; final) -- details in section 26; requests for the heavy machine in COMPUTE-stage3.md
 Regime: 9-dim level L, all a_r = 1, all lam >= 3 ("no minimal row pair"), z = vector of the dims of the single-row parts.
 (1) z = (1,0,0,0,0) (exactly one single-row direction) is IMPOSSIBLE in the families F1 (all lam = 3), F3 (lam_ae = 4), F4a (lam_ab = 4,
     lam_cd = 3)  [rigorous hand proofs, NOT yet verified independently].
     F1: Theorem S3-G now needs no side condition (m_ie <= 2 by counting, planes always well defined). F3, F4a: the proof of N2-X applies
     to the pair with lam = 4 (inputs re-derived in the presence of e_e w^T; its step (beta-0) replaced by an isotropy count).
     The only remaining family is F4b (lam_ab = lam_cd = 4): L contains a twisted free column on all five rows plus e_e w^T; the 7-dim
     core M is explicit in ten vectors; (CA2) gives exactly the identities (i)-(iii) of (A5'). NEW: an EXACT 7-dim level space M_0 with
     the shape and all invariants of the F4b core exists (free column (+) cube-root-of-unity block; exact check in Z[omega]); it
     violates (iii) and has dim T_1(M_0) = 8. So F4b cannot be excluded by the level conditions of the core alone. F4b is OPEN.
 (2) THEOREM Z22 [rigorous hand proof, NOT yet verified]: at most ONE row has a 2-dim single-row part (z_d = z_e = 2 is impossible).
     Nondegenerate planes: rows' FL2* + Lemma dim(U o U') >= 2. Degenerate planes: the first four steps of the FL2* proof survive and
     give "X_de is 3-dim with all column sums 0 and dim(U o U') = 2"; a totally isotropic plane has dim(Z o Z) = 3 (excluded); if the
     radical is a line, Lemma DEG (all 3x3 subpermanents vanish identically on X_de) and a short case analysis exclude it.
 (3) (S3-a), z_e = 2: structure sharpened (all 2-row spaces through e are trivial, lam_{rr'} = 2 + m_kl, (Q4) for the four other rows),
     and a precise reason why the missing cyclic identity cannot come from lineality along e_e Z. NOT settled.
 (4) What is left: table in section 26 (D):  F4b;  z = (2,0,0,0,0) = (S3-a);  the z-vectors with single-row elements in several rows
     and at most one entry 2 (not analysed);  rows with a_r >= 2 (outside this regime).
 (5) COMPUTE-stage3.md (asked for by the coordinator): five self-contained computation requests (direct structured searches for
     z_e = 2 and for one single-row element; cores of (S3-a) with the cyclic products and FO2; F4b systems A/B with the
     calibration M_0 and the small exact free-column sub-problem; several single-row rows; exact confirmation of the plane lemmas).

## RESULT, ROUND 6 (stage3, 19:01) -- (S3) settled in its GENERIC single-row case (Theorem S3-G); z_e = 2 and the non-generic cases open. Section 24.
 (1) THEOREM S3-G [rigorous hand proof, NOT yet independently verified]: no 9-dim level space with all a_r = 1 and all lam_{rr'} = 3 has
     exactly one row e with single-row elements, Z_e = C w, and no 2-row element through row e other than e_e w^T. Chain:
     Lemma S3-4 (every L_r, r != e, is V-twisted modulo e_e w^T, so (CA2) polarises to  w . P_k P_l P_m = 0  for all four triples);
     (Q4) for the four other rows (Lemma Q4-gen applied to L_e; hypotheses re-checked);
     THEOREM PL4 (plane lemma "four planes and a line", section 24 (J)): either two planes equal one coordinate plane containing w,
     or everything lies in three columns;  Lemma S3-5 (level conditions of a 3-row space) excludes the first;  the checked L157
     excludes the second (L_e would have a 4-dim column-centred part inside three columns).
 (2) LEMMA S3-2 [rigorous]: Z_i lies in C(L_r) for all r != i (so single-row parts of different rows are orthogonal and
     e_r >= dim sum_{i != r} Z_i); with verifyfl's SPLIT a non-isotropic single-row element forces e_r >= 2 for every other row.
     L_r is "split" in verifyfl's sense iff e_r = 1; e_r = 1 is forced only by z_r = 3, which (H1) excludes: the split theorems do not
     close (S3) by themselves. Landing pairs for all a_r (given the exclusion of (5,1), (6,2), (7,3)): (5,2), (5,3), (5,4); (6,3), (6,4);
     (7,4) -- all allowed by (DI_5).
 (3) z_e = 2 [rigorous structure, NOT settled]: 7-dim core M = L_e (+) e_e Z; (Q4) for the four other rows; for the 4-sets containing e
     only a weakened (Q4). Reduced to ONE missing identity per 4-set, Z . p_kl p_lm p_mk = 0 (a cyclic product), which cannot come from
     lineality along X_{re}; with it the plane lemma of sections 12, 15 would finish.
 (4) Numerical: the plane problem of (1) has solutions only of the types of PL4 (plus w = e_j, excluded by s(w) = 0): 46/46 with one
     vanishing column, 0/38 with none; with w kept away from unit vectors: 48 three-column and 4 type-I solutions out of 52;
     dim T_1 = 8 for all known (4,1)- and (5,2)-based defect-form 7-dim spaces (stage2's first-order test).
     Extension S3-G' (section 24 (L)): Theorem S3-G also holds when one further row carries a proper 2-row element through e (m = 2).
 (5) a_r >= 2 [rigorous remarks, section 24 (G)]: a_r <= 3; (CA2) and every (Q4) hold only modulo an (a_e - 1)-dim space; the
     pigeonhole needs lam >= a_r + a_r' + 1.
 REMAINING (section 25): (S3-a) z_e = 2 (cyclic identity or the weakened plane problem); (S3-c) z_e = 1 with some lam = 4, with proper
 2-row elements through row e, or with several rows carrying single-row elements; (S3-d) an upper bound on e_r; rows with a_r >= 2;
 verification of sections 21 and 24.

## RESULT, ROUND 5 (stage3, 18:11) -- CASE N2 IS IMPOSSIBLE (Theorem N2-X, section 21); (N2-unit) superseded; (S3) not solved (section 22)
 (1) THEOREM N2-X [rigorous hand proof, exact check of the linear algebra, NOT yet independently verified]: the family N2 (one row
     pair with lam_ab = 4) does not occur. Proof by the case structure of the plane lemmas: P_c, P_d, P_e pairwise meet;
     (alpha) non-coplanar: P_a P_b v_0 = 0 for the common vector v_0, so v_0 is e_j or 2-sparse with its conjugate in P_a and P_b, and
     both sub-cases contradict (NT)/independence; (beta) coplanar: (I3) makes V_3 a two-block space, and P_a P_b lies in the
     annihilator K of P_c P_d + P_c P_e + P_d P_e, which is 0, or one-dimensional and not a monomial, or bipartite, or forces all
     five planes into three columns (against the checked L156, since M is 7-dim); all planes equal is killed by the level conditions.
 (2) COROLLARY = THEOREM N: a 9-dim level space with all a_r = 1 and lam_{rr'} >= 3 for all row pairs contains a single-row element
     (by transposition: all b_c = 1, lam^{cc'} >= 3 => single-column element).
 (3) (T1) as posed is moot: (N2-unit) is not the right statement. The generic L_a model of round 4 violates (N2-e); the unit
     configurations are excluded directly. No special position admits a non-unit rho: N2 does not exist at all. (T2) is not needed.
 (4) (T3) = (S3), NOT solved. Landing (section 22): for every row L_r is a (5, e_r) space with 1 <= e_r <= 4 - z_r, and
     z_r <= 2 under (H1) (Lemma S3-1), so:  z_r = 2: (5,1) or (5,2);  z_r = 1: (5,1), (5,2) or (5,3).  With (5,1) excluded the
     landing pairs (5,2), (5,3) are allowed by (DI_5), and no row is deletable in this regime: (S3) is not a consequence of the
     defect inequality. For z_i = 2 the space has again a 7-dim core with all rows in 2-planes (P_i = Z_i); (Q4) for the other four
     rows should follow as in Q4-gen, but for the 4-sets containing i only a weakened (Q4) is available (the restriction is not
     injective); continuing as in section 21 is the plan, not carried out. If all b_c = 1, (SR) puts
     zeros into >= 2 column annihilators: the zero-entry layer of Theorem GEN.
 Evidence: stage3/kcheck.py (exact annihilator dimensions for all six split types and all special planes), k1check.py ((K1), (G2) on
 3000 random instances each), n2_planes*.py (plane
 problem: 75/76 solutions, all inside three columns; 0 solutions with >= 4 columns in 6 + 8 + 9 starts).
 REMAINING (section 23): (V) verification of section 21 and of the N2-part of section 16; (S3); (S2) rows with a_r >= 2.

## RESULT, ROUND 4 (stage3, 17:26) -- family N2 NOT excluded; reduced (conditionally) to rows' defect problem at e = 1. Sections 18-20.
 RIGOROUS (hand proofs; not yet independently verified):
  (a) N2 structure (section 18): twisted form of X_ab, L_a, L_b, F = L_a + L_b (6-dim); the 7-dim core M = sum of all L_r =
      {t in L : t_r in P_r} (same for every r), M inside (+) e_r (x) P_r, L/M = pi_r(L)/P_r 2-dim: N2 has the shape of the minimal
      case, with (Q4) only for the 4-sets containing a,b.
  (b) New identities: (Q5) P_c P_d P_e . U_a U_b = 0 in A_5 for all u in L^ (so W = P_c P_d P_e != 0 is killed by rho_a, rho_b, has
      1^T B_w 1 = 0, and x^T B_w theta(x') is alternating); (E1) T_a T_i . rho_b P_k P_l = 0, T_b T_i . rho_a P_k P_l = 0 for all t in L^.
      Lemma (I3) (a zero-diagonal symmetric B killing a 3-space is a two-block matrix alpha beta^T + beta alpha^T). Consequences:
      P_a P_b P_i != 0 is killed by P_k + P_l, so for P_k != P_l the complement (P_k + P_l)^perp is split and the product
      P_a x P_b x P_i -> A_3 has rank one; all level conditions of the core F follow from the identities.
  (c) CONDITIONAL REDUCTION (N2-h): if rho_a, rho_b are multiples of unit vectors lying in P_c cap P_d cap P_e [(N2-unit)], then they
      are the same e_j, e_j lies in all five planes, kappa^r_j = 0 for all r, L contains a 3-dim space of single-column elements
      Z^j e_j^T (z^j = 3 by FL), and L^j is a transposed (4 + b_j, 1) space (rows' defect form) with an explicit defect line eta:
      b_j = 2 is rows' (6,1) problem [(DI4)], b_j = 1 is a (5,1) space plus one more element [(DI_5) at e = 1 suffices]. So
      (N2-unit) + the defect inequality at e = 1 exclude N2; TC5 covers the two-line defect lines only.
  (d) (S3): in the regime all a_r = 1 every L_r is a (5, e_r) space with 1 <= e_r <= 4 - z_r (rows' R1 + SL); nothing more (section 19).
 NUMERICAL / EXACT EVIDENCE:
  (e) the necessary conditions on L_a alone (level, (Q5 at J), (Qb), alpha_i injective) are CONSISTENT: 8 exact non-degenerate
      solutions from 10 starts, all with rho_b = e_j in P_c cap P_d cap P_e; exact rational model: F is a hyperplane of the 7-dim level
      space Phi = (free column) (+) D (stage3/n2_exact_family.py). So N2 cannot be killed inside the core F; the obstruction must use
      L/M or the defect inequality. No N2-shaped pair occurs in the 12 known spaces.
 CORRECTION: an intermediate draft of (N2-c) claimed "B_w 1 = 0, dim W = 1"; unjustified and removed (dim W = 3 in the model).
 REMAINING (section 20): (T1) prove (N2-unit) [finite algebraic problem on L_a]; (T2) = rows' (5,1) problem for the defect line eta;
  (T3) = (S3) single-row elements with z_r <= 2; (T4) rows with a_r >= 2 and the transposed statements.
 Files: stage3/survey_n2.py, n2_alg.py, n2_algR.py, n2_algQ.py, n2_an.py, n2_exact_family.py (+ logs n2_alg*.log, solutions n2_alg*_sol_*.npy).

## RESULT, ROUND 3 (stage3, 16:38) -- rigorous hand proofs with exact rank checks; sections 14-17; independent verification pending
 (R1) SETTLED. Configuration (II) (twisted partial free column) does not occur: (Q4) holds for a collapsed 4-set as well
      (Lemma Q4-coll, section 14: full expansion of zeros' CA2 on the normal form of L_e), so the plane lemma applies.
 (R2) SETTLED. The minimal case with a column vanishing on M is impossible (section 15): two vanishing columns contradict the checked
      Gct/L156 (3 x q level <= q + 1); one vanishing column: concurrent planes by a support analysis, coplanar planes by a polar
      argument on the quartic prod v_n.  => THEOREM MIN-E: the minimal case does not occur.
 (R3) PARTLY SETTLED. THEOREM N1 (section 16): a 9-dim level space with all a_r = 1 and all lam_{rr'} = 3 contains a single-row element
      (pairs with a 2-dim space of 2-row elements are handled by "injectivity of restriction": in each normal form of L_e the 16
      coordinate products are independent quartics, exact rank 16). If some lam >= 4 (no single-row element) then exactly one
      pair has lam = 4, all others 3, and the configuration is the rigid family N2 -- NOT excluded.
 So Stage 3 ("2-row elements => single-row element") is PROVED for all a_r = 1 except in the family N2. Remaining list: section 17.
 Numerical corroboration of the plane lemmas: 5 columns: 185/191 LM solutions, all with four planes equal to one coordinate plane,
 0/35 with pairwise distinct planes; 4 columns: 190/191 solutions, all with >= 3 equal coordinate planes, 0/46 distinct.
 New scripts: stage3/test_Q4planes.py, test_Q4planes_sep.py, test_Q4planes4.py, span16_m2.py (superseded), q4_m2.py.

## RESULT, ROUND 2 (stage3, 16:03) -- rigorous hand proofs unless marked; details in sections 10-13
 Stage 3 is still not closed, but two of the three round-2 targets are reached:
 A. (O5) PROVED -- THEOREM N3' (section 10): if perm_3 is a nonzero constant on b + V_0 (b any 3x3 matrix, V_0 linear) then dim V_0 <= 3.
    (b = J is Gct/L094.) Proof: cell factorisation + a quadratic-form argument excluding 3-dim spaces with a zero row + a 4-step
    endgame on single-row/single-column elements. Numerics: 0/200 starts find a 4-dim space, 39/72 find 3-dim ones.
    COROLLARY N3'-L: for a B1 block (rows r,r', column pair T): dim{t in L : t[rr';T^c] = 0} <= 3 + m^T, so lam_{rr'} <= 3 + m^T and
    lam_{rr'} >= 4 forces 2-column elements on T and elements of L supported in a 3x2 block.
 B. (O1) MINIMAL CASE REDUCED TO ONE CONFIGURATION (sections 11, 12): with P_i the row planes of M,
    (MIN-A) every 4-set of rows is "collapsed" or the product P_a P_b P_c P_d vanishes in the squarefree algebra (exact rank 16 check);
    (TV)    three 2-planes with vanishing triple product are one coordinate plane span(e_j,e_l);
    (MIN-B) without collapsed 4-set the five planes pairwise meet (concurrent or coplanar);
    (MIN-C) if no column vanishes on M (true when all b_c <= 2) the non-collapsed case is IMPOSSIBLE (complete case analysis:
            common vector of support 3, 2, 1; coplanar two-block types (2,2,1), (2,3,0)).
    Hence: in the regime all a_r = 1, all b_c <= 2, the minimal case survives ONLY as configuration (II): L contains a "twisted partial
    free column" F = {sum c_i e_i rho_i^T : sum c_i = 0} on four rows (rho_i = e_j is S3-B's domino branch, which (L3) hands to the
    deletable-line normal form). (II) is not excluded; it is an exactly testable finite problem (section 13).
 C. (O2) only touched (N3'-L is the new input). Remaining open list: section 13, (R1)-(R5).
 New scripts: stage3/test_N3prime.py, test_O5.py, span16.py, span16b.py, span16_exact.py, test_TV.py, test_blocks.py.

## RESULT, ROUND 1 (stage3, 15:12; everything below is a RIGOROUS hand proof unless marked "empirical"; proofs in sections 1-8)
 Stage 3 is NOT closed, and (after rows' free-line-free 7-dim spaces + coordinator correction) its endpoint cannot be a full free line.
 What is established:
 0. EXACT HYPOTHESES. (H1) = lam >= 3 for all row and column pairs does NOT by itself give 2-row elements: by the pigeonhole (P)
    m_ab >= lam_cd + lam_ce - 4 - a_c, they are forced for all ten pairs if no three rows have a_r = 2 [(H2)] (the pigeonhole
    gives nothing for a triple of rows with a = 2, lam = 3); in particular for
    all a_r = 1 -- exactly the regime in which no line can be deletable (chief's Lemma DS), so there stage 3 must end in a
    contradiction, not in a deletable line.
 1. NEW TOOLS (valid in every level space; tested on 12 spaces, 0 violations):
    (GZ) zero-block dichotomy with lineality + "ell-supporting" blocks; (SR/SC) a single-row element e_a w^T forces, for every
    j in supp w, an FK annihilator of column j vanishing at a (so zero-free column annihilators exclude single-row elements);
    (D2) a 2-row element x has q_T(x) != 0 only on column pairs T whose 3x2 block is ell-supporting of type B2; (D3) under (H1)
    elements vanishing on a relation-free 3x2 block vanish on the two columns; (T1) squarefree-algebra identity
    X_a X_b . pi_c(X_de) . pi_d(X_ce) = 0 in A_4 whenever a_e = 1; (Q0)+(P2T) classification of 2-row elements with vanishing
    2x2 subpermanents into R (single row), D (domino (e_a - e_b) e_j^T), B (2x2 block) and their P_2-incompatibilities.
 2. THEOREM S3-A (Petersen pigeonhole): in ANY level space, ten B-type elements, one per row pair, are linearly independent
    (the block map is an automorphism of the Petersen graph); so dim 9 is impossible in that situation -- a second 9-vs-10 pigeonhole.
 3. THEOREM S3-B: if every row pair of a level space of dim 8 or 9 carries a nonzero 2-row element with Q_x = 0 [(HQ)], then L
    CONTAINS A SINGLE-ROW ELEMENT; the rows without single-row elements form a set N, |N| <= 4, and for |N| >= 3 either all pairs
    in N carry dominoes of ONE column j (dim Z^j >= |N| - 1) or all carry B-type elements.  (This is "2-row => single-row".)
 4. LEMMA T / THEOREM S3-C: for a_c = a_d = a_e = 1, if the three row spaces R_c, R_d, R_e of the 3-row spaces through Y_ab pairwise
    span >= 4 dimensions then Q = 0 on Y_ab; so all a_r = 1 + (H1) + this transversality => single-row element.
 5. THEOREM S3-D (minimal case = all a_r = 1, lam = 3, m = 1, no single-row element): all L_r lie in one 7-dim M inside
    (+) e_i (x) P_i with 2-planes P_i; (HQ) FAILS there, the planes are not pairwise transversal, and with column-(H1) they are of
    "block type" (>= 20 vanishing Pluecker incidences; not all of type (3,2); some P_i contains a unit vector or lies in a
    coordinate hyperplane) -- chief's two-block pattern, now forced.
 6. EMPIRICAL (12 spaces incl. rows' new ones): every 2-row space is spanned by single-row elements and dominoes; (HQ) always holds.
 MINIMAL EXTRA HYPOTHESES for "stage 2 => single-row element": (H2) [follows from (H1) if no three rows have a_r = 2, and from
 stage2's Corollary (T) in the zero-free Type-I regime; otherwise
 needs lam_{rr'} >= a_r + a_r' + 1 from stage 2] and (HQ) [not provable in general: false in the minimal case; holds when no
 triple has >= 2 bad B2 column pairs, or under Lemma T's transversality]. EXACT OPEN STATEMENTS: section 9 (O1-O4).
 Files: stage3/s3lib.py, explore1.py, test_lemmas.py (GZ, SR/SC, D2, S12), sparse_span.py (empirical law), test_p2types.py (P2 table,
 independence), test_T1.py (T1), test_algebra.py (squarefree facts, Petersen count), test_L5.py (incidence case analysis).
STATUS 14:40: read BRIEF, NOTES-chief (all), NOTES-zeros, adversary, rows. Setting up hypotheses H1.. and the 2-row calculus.
STATUS 14:44: lib + example survey done (stage3/s3lib.py, explore1.py). Found: (D2) "dual C2" for 2-row elements (q_T(x) != 0 only on
 column pairs T whose 3x2 block is ell-supporting); pigeonhole m_ab >= lam_cd + lam_ce - 4 - a_c; in the minimal case
 (all a_r = 1, lam = 3, m = 1) all L_r lie in ONE 7-dim M = L_a + L_b with every row projection of M 2-dim. Writing proofs + tests.
STATUS 14:54: coordinator correction read (endpoint = deletable line / defect form, not a full free row). Lemmas GZ, D2, SR/SC, S1/S2
 sanity-tested on 12 level spaces (7 of chief/core.py incl. K + E_0, + 5 of rows' free-line-free 7-dim spaces): 0 violations
 (stage3/test_lemmas.py). Empirical: in all 12 spaces every 2-row space Y_ab is spanned by single-row elements and dominoes
 (stage3/sparse_span.py). Theorem S3-A/B (Petersen pigeonhole) found; writing proofs.

## 1. Hypotheses: what stage 2 gives, exactly (all statements RIGOROUS unless marked)
Notation as chief sec. 4/6: L level, dim 9, L^ = CJ (+) L, perm = 120 ell^5 on L^ (R0). X_S := L cap {rows in S = 0}, d_S := dim X_S;
 d_{r} = 4 + a_r, d_{rr'} = lam_{rr'}; for a row pair {a,b} with complement S = {c,d,e}: Y_ab := X_S = "2-row elements on rows a,b",
 m_ab := dim Y_ab (<= 4, L101); Z_r := {w : e_r w^T in L} (single-row elements, z_r := dim Z_r <= 3 by FL). Upper indices = columns.
 A := Ann(L) (16-dim, contains J); alpha_K := dim(A cap C^K) = |K| - dim pi_K(L) for a set K of cells.
 (H1)  lam_{rr'} >= 3 for all row pairs, lam^{cc'} >= 3 for all column pairs   [= output of stage 2 as stated].
 (P)   PIGEONHOLE (kernel submodularity: X_S cap X_S' = X_{S u S'}, X_S + X_S' inside X_{S cap S'}; same for arbitrary cell sets):
         m_ab = d_{cde} >= lam_cd + lam_ce - 4 - a_c   and   >= lam_cd + a_e - 5;      z_r >= m_{dr} + m_{cr} - lam_ab ({a,b,c,d} = rows != r).
       Under (H1): m_ab >= 1 as soon as the complementary triple contains a row with a = 1 or a >= 3.
       NOT forced when a_c = a_d = a_e = 2 and the lam's are 3. So (H1) alone does not give 2-row elements for all pairs:
 (H2)  [needed extra hypothesis; automatic if all a_r = 1, more generally unless three rows have a_r = 2]:  m_ab >= 1 for all ten row pairs.
       The natural stage-2 statement that would give (H2) in general is  lam_{rr'} >= a_r + a_r' + 1  (pigeonhole C1 gives a_r+a_r'-1).
 (M)   MINIMAL CASE all a_r = 1, all lam = 3, all m = 1, no single-row elements: L_c = X_ac + X_bc inside L_a + L_b, so
       M := L_a + L_b is ONE 7-dim space (independent of the pair) containing every L_r; P_i := pi_i(M) = pi_i(L_r) (all r != i) is
       2-dim, M inside (+)_i e_i (x) P_i (10-dim) in "generic position" (M cap 2 rows = line Y_ab, M cap 3 rows = X_de, M cap 4 rows = L_r),
       L/M (2-dim) maps isomorphically onto pi_i(L)/P_i for every i ("common 2-dim quotient"), and the ten lines Y_ab span <= 7
       dimensions (>= 3 linear dependencies among ten 2-row elements).
 (M3)  3x3-BLOCK ELEMENTS (submodularity for rows R = {r,r'} and columns T): dim{t in L : rows R and columns T vanish}
       >= lam_R + lam^T + dim pi_{RxT}(L) - 9 >= dim pi_{RxT}(L) - 3. So under (H1) every 2x2 block RxT that carries no linear relation
       of L (the generic case) has a nonzero element of L supported in the complementary 3x3 block.

## 2. Lemma GZ (zero-block dichotomy with lineality) and its corollaries  [rigorous; tested on 12 level spaces, 0 violations]
 Let K = S x Z be a block with |S| + |Z| = 5 ("sub-FK"), U_K := {u in L^ : u_K = 0}, f_1(u) := perm(u[S;Z^c]), f_2(u) := perm(u[S^c;Z]),
 so perm = f_1 f_2 on U_K (chief's ZBF). Call K ELL-SUPPORTING if some n in C^K has <n,t> = 0 on L and sum n = 1
 (<=> J_K not in pi_K(L) <=> ell = 0 on U_K <=> ell(u) = <n,u_K> on L^). FK blocks (|S|+|Z| = 6) are always ell-supporting.
 (GZ-a) K not ell-supporting: f_1 = k ell^|S|, f_2 = k' ell^(5-|S|) on U_K, k k' = 120 (UFD). Hence for x in U_K cap L, u in U_K:
        f_i(u + x) = f_i(u): x is a LINEALITY direction of both block permanents on U_K; in particular f_1(x) = f_2(x) = 0 and all
        polarisations D_x f_i vanish on U_K.
 (GZ-b) K ell-supporting: U_K inside L, dim U_K = 9 - dim pi_K(L) >= 10 - |K|, and f_1 = 0 on U_K or f_2 = 0 on U_K.
 Proof: ZBF + UFD (chief sec. 2); ell(u + x) = ell(u); the equivalences are linear algebra (ell|U_K = 0 iff ell is a combination of the
 coordinate forms of K on L^).
 (SR) SINGLE-ROW ELEMENTS. If e_a w^T in L and w_j != 0 then the 4x1 block (rows != a) x {j} is ell-supporting: there is nu in N^j
      (FK annihilator space of column j) with sum nu = 1 and nu_a = 0 [if b_j = 1: kappa'^j_a = 0], and the (a,j)-deletion permanent
      perm_4(t^(aj)) vanishes for every t in L whose column j is supported at row a (in particular on L^j).
      Proof: K = (rows != a) x {j}, f_2(u) = u_aj, x = e_a w^T in U_K cap L, f_2(x) = w_j != 0, so (GZ-a) fails; (GZ-b): f_1 = 0 on U_K.
 (SC) transposed: y e_j^T in L, y_a != 0 => exists n in N_a, sum n = 1, n_j = 0 [a_a = 1: kappa^a_j = 0].
      COROLLARY: if all b_c = 1 and no column annihilator kappa'^c has a zero entry, L has NO single-row element (and dually).
 (D2) 2-ROW ELEMENTS ("dual C2"). x in Y_ab, S = {c,d,e}, T a column pair, q_T(x) := x_aj x_bl + x_al x_bj, K = S x T (3x2).
      If K is not ell-supporting: q_T(x) = 0, and x[ab;T] lies in the radical of q_T on Pi_2 := image of U_K in the 2x2 block [ab;T].
      If q_T(x) != 0 ("T is BAD for the pair ab"): K is ell-supporting and perm(t[cde;T^c]) = 0 for all t in L with t[cde;T] = 0.
      More generally: any linear dependency sum_T c_T f_T = 0 among the ten cubics f_T(u) = perm(u[cde;T^c]) on pi_cde(L^) is supported on
      column pairs T with ell-supporting S x T; Q_x := (q_T(x))_T is such a dependency (s^2-coefficient of perm(u + s x)).
 (D3) FREE BLOCKS (pure linear algebra + H1). dim({t in L : t[cde;T] = 0} / X^T) = 3 + alpha_{cde x T} - lam^T. So if lam^T >= 3 and the
      3x2 block cde x T carries no relation of L (alpha = 0), EVERY t in L vanishing on cde x T vanishes on the whole columns T;
      in particular every 2-row element on rows a,b has zero columns T. Hence: x in Y_ab with column j nonzero forces a nonzero
      relation of L supported on cde x {j,l} for each of the four l != j.
 (S12) for x in Y_ab, u in L^: perm[x_a;x_b;u_c;u_d;u_e] = 0 and perm[x_a;u_b;u_c;u_d;u_e] + perm[u_a;x_b;u_c;u_d;u_e] = 0;
      for x in Y_ab, y in Y_cd (disjoint pairs): G_e(x + y) := (perm_4 of rows a,b,c,d of x+y minus column m)_m lies in pi_e(L^)^perp
      (= 0 if a_e = 1):  sum over splittings T u T' = [5] - m of q_T(x) q_T'(y) = 0 for every column m.

## 3. Classification of 2-row elements with Q_x = 0 and the P_2 table  [rigorous; table checked numerically, stage3/test_p2types.py]
 (Q0) A matrix x supported on rows a,b with q_T(x) = 0 for all ten T is: a single-row matrix; or supported in ONE column; or
      supported in a 2x2 block [ab;jl] with zero 2x2 permanent and four nonzero entries. (Proof: supp x_a = supp x_b =: A; three
      columns in A give rho_j + rho_l = 0 pairwise for rho = x_b/x_a, so rho = 0.) If moreover x is level (sum of entries 0):
        R-type  e_a w^T (sum w = 0),    D-type ("domino")  c (e_a - e_b) e_j^T,    B-type  [[p,q],[r,s]] on [ab;jl], ps + qr = 0 = p+q+r+s.
      B-type elements have NONZERO row sums and column sums (p + q = 0 forces perm = -2pr != 0).
 (P2T) polarised P_2 on L: <t,t'> - R(t).R(t') - C(t).C(t') = 0 (R, C = row/column-sum vectors). Consequences for elements of L:
      (1) D-D on row pairs sharing exactly one row: same column.            (2) D-D on disjoint row pairs: no condition.
      (3) B-B on disjoint row pairs: DISJOINT column pairs.                 (4) B-B on row pairs sharing one row: column pairs MEET.
      (5) D-B on disjoint row pairs: no condition.                          (6) D-B on row pairs sharing exactly one row: IMPOSSIBLE.
      (7) R-type e_r w^T against any t in L:  <w, t_r - C(t)> = 0.

## 4. THEOREM S3-A (Petersen pigeonhole)  [rigorous]
 Let L be ANY level space of 5x5 matrices such that every one of the ten row pairs {a,b} carries a B-type element x^{ab} in L
 (support = a 2x2 block [ab; tau(ab)], four nonzero entries). Then the ten elements are linearly independent: dim L >= 10.
 Proof. By (3) tau maps disjoint pairs to disjoint pairs, by (4) pairs sharing a row to pairs sharing a column (or equal).
 tau is injective: tau(ab) = tau(ac) (b != c; disjoint pairs cannot have equal images) contradicts (3)+(4) for the pair {b,d}
 (d a fourth row): {b,d} is disjoint from {a,c} but meets {a,b}. So tau is a bijection of the 2-subsets of [5] preserving
 disjointness; the four pairs through a row a go to four distinct pairwise meeting pairs, i.e. a star through a column sigma(a)
 (a triangle has only three), sigma is injective (two stars have 7 pairs), so tau(ab) = {sigma(a), sigma(b)}. The cell (a, sigma(b))
 lies in the block of the pair {a,b} only, and x^{ab} is nonzero there: independence. QED
 (For dim 9 this is again a 9-versus-10 pigeonhole. Petersen graph = Kneser graph K(5,2), tau is a graph automorphism.)

## 5. THEOREM S3-B (2-row elements => single-row elements)  [rigorous, conditional on (HQ)]
 (HQ) every row pair {a,b} carries a NONZERO 2-row element x^{ab} in L with Q_{x^{ab}} = 0.
 THEOREM. Let L be a level space with dim L in {8, 9} satisfying (HQ). Let N := set of rows r with Z_r = 0, n := |N|. Then
   (i)   n <= 4: L CONTAINS A SINGLE-ROW ELEMENT e_r w^T;
   (ii)  if n >= 3, then EITHER all pairs inside N carry dominoes in ONE common column j: (e_a - e_b) e_j^T in L for all a,b in N
         (so the single-column space Z^j contains {y e_j^T : supp y in N, sum y = 0}, dim n-1 >= 2), OR all pairs inside N carry
         B-type elements; for n = 4 the block map is tau(P) = sigma(P) or tau(P) = sigma(N - P) for an injection sigma: N -> columns.
 Proof. A pair inside N cannot be R-type, so it is D or B. Two pairs inside N sharing exactly one row have the same type by (6); the
 graph "pairs of N, adjacent if they share one row" is connected for n >= 3, so all D or all B; all D: one column by (1).
 n = 5, all B: dim L >= 10 by S3-A. n = 5, all D: Z^j is the full free column, so dim L <= 7 by Theorem FL (zeros). QED
 By transposition, the column version of (HQ) gives a single-column element.
 WHEN (HQ) HOLDS. Given (H2), (HQ) holds for the pair ab as soon as the number of BAD column pairs T (q_T not identically 0 on
 Y_ab; by (D2) these are ell-supporting 3x2 blocks cde x T of chief's type B2, and by (D3) they carry >= lam^T - 2 >= 1 relations
 of L, one of them with sum 1) is <= max(1, m_ab): the bad q_T sum to P_2 = 0, so one bad pair is none, and e - 1
 quadrics on P^(m-1) have a common zero when e <= m. In particular (HQ) holds if no 3x2 block is ell-supporting, or if the ten
 cubics perm(u[cde;T^c]) restricted to pi_cde(L^) are linearly independent for every row triple.
 COROLLARY (regime all a_r = 1). Let L be 9-dim level with (H1) and all a_r = 1. Then (H2) holds. If moreover (HQ) holds, L has a
 single-row element e_a w^T, hence by (SR) for every j in supp(w) the column annihilator space N^j contains a sum-1 vector vanishing
 at a. Consequently, in the fully generic regime GEN (all a_r = b_c = 1 and all FK annihilators kappa^r, kappa'^c without zero entries)
 where by (SR),(SC),(P2T) there are neither single-row/column elements nor dominoes: (HQ) FAILS -- some row triple cde has >= 2 bad
 column pairs, i.e. L contains 2-row elements x with |column support| >= 3 and ell-supporting B2 blocks cde x T with T inside supp.
 In GEN every x in Y_ab has the form x = sum_j xi_j (kappa'^j_b e_a - kappa'^j_a e_b) e_j^T with <kappa^a o kappa'_b, xi> = 0 =
 <kappa^b o kappa'_a, xi>, q_{jl}(x) = - xi_j xi_l perm(K'[ab;jl]) (K' = matrix of column annihilators), and a bad T = {j,l} (inside
 supp xi, perm(K'[ab;jl]) != 0) means: every u in L^ whose columns j,l are supported on rows a,b has ell(u) = 0.
 [An earlier draft claimed that L then contains elements with columns (h^j_ab, 0) and (0, h^l_ab); that was NOT justified.]

## 6. Empirical law (12 spaces: L080, ex1-3, two s-family members, K + E_0, five of rows' free-line-free 7-dim spaces)
 EVERY 2-row space Y_ab of every test space is SPANNED by R-type elements and dominoes (stage3/sparse_span.py); no B-type element and
 no irreducible 2-row element with Q_x != 0 occurs (elements with Q_x != 0 occur only as sums R + D, e.g. L080). So (HQ) holds in
 all known examples, and the bad blocks of (D2) are always "explained" by sparser elements.

STATUS 15:06: new tool (squarefree-algebra identity T1) + Lemma T (transversality => Q_x = 0) + Theorem S3-C/S3-D proved; T1 tested
 (stage3/test_T1.py, 27 cases, 0 violations; few test objects have a_e = 1 rows away from 2-row elements).

## 7. Squarefree calculus, identity (T1), Lemma T (when is Q_x = 0?)  [rigorous]
 A := C[y_1..y_5]/(y_j^2) (graded, dim A_k = C(5,k)); a row vector v gives V := sum_j v_j y_j in A_1; for rows v_1..v_k the
 coefficients of V_1...V_k in A_k are the k x k subpermanents of the k x 5 matrix (so Q_x = X_a X_b in A_2 for a 2-row x, the
 vector B_x of ThA is X_a X_b X_c in A_3, zeros' cofactor vector G_e is the product of four rows in A_4).
 Facts: (i) w in A_3, v' in A_1: w v' = 0 in A_4  <=>  B v' = 0 for the symmetric zero-diagonal matrix B[j,l] := w_{[5]-{j,l}};
 such a B of rank <= 1 is 0.  (ii) Q in A_2 with Q[T] != 0, T = {j,l}: Q v = 0 in A_3 forces v_m = -(Q[jm] v_l + Q[lm] v_j)/Q[jl]
 for m not in T, so {v : Q v = 0} has dim <= 2.
 (CA2, zeros) a_e = 1  =>  Xi_a Xi_b Xi_c Xi_d = 0 in A_4 for every xi in L_e (the 1x4 blocks {e} x (all but m) are not
       ell-supporting; (GZ-a)).
 (T1) Let x in Y_ab, {c,d,e} the other rows, a_e = 1. Then X_a X_b Xi_c Xi_d = 0 in A_4 for all xi in L_e (s^2-coefficient of
      (CA2) on xi + s x), hence, polarising on the linear space pi_cd(L_e), which contains pi_c(X_de) (+) pi_d(X_ce):
            Q_x . R_c . R_d = 0 in A_4,      R_c := pi_c(X_de), R_d := pi_d(X_ce), R_e := pi_e(X_cd)
      (R_c = row c of the 3-row elements living on rows a,b,c; dim R_c = lam_de - m_ab). Likewise Q_x R_c R_e = 0 if a_d = 1 and
      Q_x R_d R_e = 0 if a_c = 1.  [all five 4x4 subpermanents of the 4x5 matrix (x_a; x_b; v; v') vanish for v in R_c, v' in R_d.]
 LEMMA T. Let a_c = a_d = a_e = 1 and x in Y_ab with Q_x != 0. If dim(R_d + R_e) >= 4 then R_c lies in the <= 2-dim space
      Gamma_x := {v : Q_x v = 0}; same for the other two indices. Consequently, if two of the three sums R_d + R_e, R_c + R_e,
      R_c + R_d have dim >= 4 (say the first two), then R_c + R_d lies in Gamma_x (dim <= 2). In particular:
      if R_c, R_d, R_e pairwise span >= 4 dimensions, then Q = 0 identically on Y_ab.
      Addendum: a 2-plane Pi inside Gamma_x (Q_x Pi = 0, Q_x != 0, x level) lies in a coordinate subspace C^N', |N'| in {3,4}
      (all of Pi vanishes in at least one column), and Q_x is supported on the pairs inside N'.
      Proof: for v in R_c the element Q_x v of A_3 is killed by R_d and R_e (T1), so its matrix B kills a >= 4-dim space, B = 0 (i);
      then (ii). QED
 THEOREM S3-C. Let L be a 9-dim level space with (H1) for rows and all a_r = 1. If for every row triple {c,d,e} the three spaces
      R_c, R_d, R_e pairwise span >= 4 dimensions, then (HQ) holds, hence (S3-B) L contains a single-row element e_r w^T, and the
      set N of rows without single-row elements has |N| <= 4 with the D/B alternative of S3-B on N.
 THEOREM S3-D (the minimal case is a TWO-BLOCK configuration). In the minimal case (M) of sec. 1 [all a_r = 1, lam = 3, m = 1, no
      single-row elements; then R_i = P_i, the 2-plane pi_i(M)]:
      (a) (HQ) fails (S3-B (i)), so by Lemma T some pair of the planes P_1..P_5 is NOT transversal: P_c cap P_d != 0;
          more precisely for every pair ab with Q != 0 on Y_ab either two of P_c, P_d, P_e coincide (= Gamma_x) or at least two of
          the three pairs among them meet nontrivially.
      (b) if also (H1) holds for columns: for EVERY column pair T at least two of the planes P_i contain a nonzero vector vanishing
          on T (dim(M cap X^T) >= lam^T - 2 >= 1 and elements of M have >= 2 nonzero rows), i.e. the Pluecker coordinate pi_T(P_i)
          vanishes for >= 2 rows i: sum_i #{T : pi_T(P_i) = 0} >= 20. For a 2-plane the vanishing pairs are the pairs inside the
          classes of proportional columns (zero columns count with everything), so the average plane has >= 4 vanishing pairs:
          column-class type (3,2) [P_i = span(alpha, beta) with DISJOINT supports of sizes 3 and 2 -- exactly 4], (4,1) [contains
          a unit vector e_j], or a plane inside a coordinate hyperplane. This is chief's "two-block column structure" (C7'', C8),
          now derived for the row planes P_i from (H1) alone; if exactly two planes P_i, P_i' vanish at T then M cap X^T is
          spanned by a 2-row element (gamma^i, gamma^i') built from the block vectors. All five planes of exact type (3,2)
          is impossible: with D_i := the 2-class of P_i (a vertex of the Petersen graph) the count needs |{i : D_i in N[T]}| = 2
          for all ten closed neighbourhoods N[T], i.e. (A + I) n = 2*1, whose only solution is n = 1/2 (A + I has eigenvalues
          4, 2, -1). So some P_i contains a unit vector e_j (then kappa^i_j = 0) or lies in a coordinate hyperplane.

## 8. Further rigorous consequences
 (L1) A LINEAR space Y of 2-row matrices (rows a,b) on which Q = 0 identically and which is level is contained in row a, or in row b,
      or is a line spanned by a D- or B-type element. (Sums R_a + R_b, R + D, R + B, D + D', D + B, B + B' all have a nonzero q_T.)
      Since Y_ab contains Z_a (+) Z_b: if Q = 0 identically on every Y_ab ("strong HQ") then at most ONE row r_0 carries single-row
      elements; with S3-B (dim 8, 9): exactly one, Y_{a r_0} = Z_{r_0} for all a, m_ab = 1 inside N = [5] - r_0, and for all a_r = 1
      + (H1): all lam = 3, z_{r_0} <= 2, and the six elements x^{ab} (a,b in N) lie in the 5-dim L_{r_0}; the B-alternative with
      tau(P) = sigma(P) is impossible (six independent elements), leaving "all dominoes in one column j" or the complementary
      B-pattern tau(P) = sigma(N - P). CAUTION: strong HQ fails in every known example (L080: e_4 w^T + (e_0 - e_4) e_4^T has
      Q != 0), whereas (HQ) holds in all of them; strong HQ is what Lemma T delivers, so Lemma T's transversality hypothesis is a
      genuinely "generic-position" hypothesis and cannot hold in the known 7-dim types.
 (L2) Rows with zero-free column annihilators: if b_j = 1 and kappa'^j has no zero entry for all j, then every 2-row element is
      x = sum_j xi_j (kappa'^j_b e_a - kappa'^j_a e_b) e_j^T and, having no single-row/-column elements, L satisfies: for every pair
      ab with a Q = 0 element, that element is B-type. With S3-A: if all a_r = b_c = 1, all annihilators zero-free and (H1), then
      at least one row pair has NO nonzero Q = 0 element (so >= 2 bad B2 blocks for its triple), and by Lemma T its three spaces
      R_c, R_d, R_e are not pairwise 4-spanning.

 (L4) GRAPHIC FORM OF THE PIGEONHOLE (generalises S3-A when the column annihilators are zero-free). Let all b_j = 1 and all kappa'^j
      zero-free. Every 2-row element on rows a,b has columns x^j = xi_j h^j_ab, h^j_ab = kappa'^j_b e_a - kappa'^j_a e_b =
      kappa'^j_a kappa'^j_b (f_a - f_b), f_i := e_i / kappa'^j_i: for fixed j the vectors h^j_ab form the GRAPHIC matroid of K_5.
      So for a family x^P (P in a set of row pairs) and G_j := {P : column j of x^P != 0} (a graph on the rows), a linear
      dependency sum c_P x^P = 0 is, in every column j, a weighted circulation on G_j: supp(c) cap G_j is BRIDGELESS for every j.
      Hence if dim L = 9 and all ten pairs carry 2-row elements (H2), there is a nonempty set of pairs whose trace on every G_j
      is a union of cycles; in particular some column j is nonzero in x^{ab}, x^{bc}, ..., along a cycle of rows. (B-type elements
      give stars G_j, hence S3-A.)
 (L5) INCIDENCE COUNT (needs b_j = 1 and kappa'^j zero-free for all j, and (H1) for columns). P^{l,j} := pi^j(L^l) has dim
      5 - lam^{jl} <= 2; E_{l,j} := {row pairs ab : h^j_ab in P^{l,j}} has graphic rank <= 2, so it is empty, one pair, two disjoint
      pairs, or (part of) a triangle; when it spans P^{l,j} (two pairs or a triangle) column j of every element of L^l vanishes
      in the rows outside. A 2-row element x in Y_ab with column support C lies in L^l for l not in C, so ab is in E_{l,j} for all
      j in C, l not in C: |C| (5 - |C|) incidences against a total capacity 20 * 3 = 60. If every row pair carries a 2-row element with
      |C| in {2,3} (6 incidences each) the count is tight: every E_{l,j} is a triangle, and a short case analysis per column j
      ((n_2,n_3) = number of supports of size 2, 3 containing j, 3 n_2 + 2 n_3 = 12; (4,0) and (2,3) are impossible, (0,6) forces
      G_j = K_4 or two triangles with a common vertex) shows that ALL ten supports have size exactly 3. So in that regime B-type
      elements can only coexist with 2-row elements having >= 4 nonzero columns. [hand count; the per-column case analysis is
      machine-checked by stage3/test_L5.py: only K_4 (120 labelled solutions) and the bowtie (90) occur, always with n_2 = 0.]
      In the all-K_4 case the supports are C_ab = sigma^{-1}([5] - {a,b}) for a bijection sigma: x^{ab} lives on the 2x3 block
      ab x (complement), the pattern complementary to S3-A's, and P_2 forces for every column e that at least three of the four
      entries kappa'^e_i (i != sigma(e)) coincide.
 COORDINATION with stage2 (their Corollary (T), 15:06): for three rows with a = 1, zero-free annihilators and no Type II minimal
      pair, X_{rr'r''} != 0 -- this is (H2) for the complementary pair WITHOUT needing lam >= 3. So in the zero-free regime the input
      of S3-A, S3-B, (L2), (L4) is available from stage 2 directly; only (D3), Lemma T, S3-C, S3-D use lam >= 3 itself.
 (L3) LINK TO THE DELETABLE-LINE ENDPOINT. In the all-domino branch of S3-B (ii) the column j has z^j >= |N| - 1. For |N| = 4:
      Z^j contains the 3-dim space {y e_j^T : supp y in N, sum y = 0}; z^j = 4 is excluded by FL, so z^j = 3 and b_j <= 2. If b_j = 2
      then pi^j(L) = Z^j, i.e. column j is DECOUPLED (L = L^j (+) Z^j e_j^T) and therefore DELETABLE (G^j(u) is orthogonal to Z^j =
      pi^j(L)): this is exactly rows' defect form with f = 3, dim L' = 6, defect <= 1. If b_j = 1 then kappa'^j = c 1_N + c' e_{r_0}
      (constant on N) and the cofactor vector G^j(u) lies in span(1_N, e_{r_0}) for all u in L^. So the D-branch of stage 3 ends at
      the re-aimed endpoint; the B-branch (|N| = 3, 4) and the hypothesis (HQ) are what separates S3-B from conjecture (D).
      Check on L080 (all ten pairs carry 2-row elements): N = {0,1,2,3}, all six pairs are dominoes in column 4, z^4 = 4 (free column).

## 9. EXACT OPEN STATEMENTS after this work, and the re-aimed endpoint (deletable line / defect form)
 What is PROVED (unconditional lemmas): GZ, SR/SC, D2, D3, S12, Q0, P2T, S3-A, T1, Lemma T, L1. Conditional theorems: S3-B (needs HQ),
 S3-C (needs all a_r = 1 + transversality), S3-D (minimal case).
 (O1) [the core] MINIMAL CASE: five 2-planes P_i in C^5 and a 7-dim level M inside (+) e_i (x) P_i in generic position (sec. 1 (M)),
      extended by 2 dimensions to L with L/M = pi_i(L)/P_i. By S3-D the planes are non-transversal and of block type. Open: derive
      a contradiction (expected route: the block structure makes single rows of M "pendant" in adversary's sense; then ZBF on
      the blocks C_1, C_2 of a plane P_i: rows of M restricted to a class are proportional to one vector).
 (O2) NON-MINIMAL all a_r = 1: some lam >= 4 or m >= 2 or z >= 1. Here (P) gives more elements (m_ab >= lam_cd + lam_ce - 5), and (HQ)
      needs only #bad pairs <= m_ab. Not analysed.
 (O3) rows with a_r >= 2: (H1) does not even give 2-row elements (a = (2,2,2) triples). Needed from stage 2: lam_{rr'} >= a_r + a_r' + 1,
      or a separate treatment (chief C8 types). Not provable from (H1) as stated.
 (O4) (HQ) itself: FALSE in the minimal case (S3-D (a)), true in all known examples. The correct statement to aim at is not (HQ) but
      "bad B2 blocks force block-type planes" (S3-D (b) is the first instance).
 (O5) [auxiliary, for lam >= 4] "N3'": a linear space V_0 of 3x3 matrices such that perm_3 is a nonzero constant on b + V_0 has
      dim <= 3 (chief's N3 is b = J). With (GZ-a) for K = rr' x T^c (type B1) this would give: lam_{rr'} >= 4 => L contains a nonzero
      element supported in the 3x2 block (other rows) x T, for every B1 column pair T. Not proved (chief's N3 argument needs the
      extra case "row r of b has a zero entry").
 RE-AIM (coordinator 14:5x): the endpoint "deletable line + defect bound" relates to this work as follows.
  - In the regime all a_r = 1 = b_c (the regime that (H1) controls best) NO line is deletable in a 9-dim space (chief's Lemma DS:
    deletable + 4-dim projection => dim <= 7). So there conjecture (D) is equivalent to non-existence, and stage 3 must END IN A
    CONTRADICTION, not in a deletable line; S3-A/S3-B/S3-D are steps of exactly this kind (two 9-versus-10 pigeonholes).
  - A deletable row r needs a_r >= 2 and (maximal case) decoupling Z_r = pi_r(L), i.e. z_r = 5 - a_r <= 3. The tools give for a
    decoupled row: (SR) every column j in supp(Z_r) has an FK annihilator vanishing at r, and perm_4(t^(rj)) = 0 on L^j; (7) of P2T:
    Z_r is orthogonal to t_r - C(t), i.e. to the column sums of the other four rows (this is rows' "p_1 in C(L')").
    The pigeonhole (P) gives z_r >= m_{dr} + m_{cr} - lam_ab only; no route to z_r = 5 - a_r was found.
  - For the defect inequality dim L' <= 4 + defect (4x5 level L'): (T1)/(CA2) apply to L' = L_r when a_r = 1 only (defect 0 = SL);
    for a_r >= 2 the analogue is "G_r(xi) in N_r cap 1^perp for xi in L_r" (zeros CA2), so X_a X_b Xi_c Xi_d lies in the (a_r - 1)-dim
    space N_r cap 1^perp instead of vanishing: Lemma T survives with "rank B <= 1" replaced by a bound in terms of a_r - 1. Not done.
STATUS 15:12: RESULT written; sections 1-9 complete; continuing on (O1) for the remaining time.
STATUS 15:16: (L3) link to the deletable-line endpoint and (O5) added; stage2's notes read (their Type I/II triple theorem gives
 X_{rr'r''} != 0, i.e. feeds (H2)). Final report being written.
STATUS 15:24: (L4) graphic pigeonhole, (L5) incidence count, coordination note added; one unjustified sentence of sec. 5 corrected.
STATUS 15:22: final report sent (RESULT at top; open statements O1-O5 in section 9).

# ROUND 2 (start 15:29, budget 75 min -> ends ~16:44)
STATUS 15:38: read UPDATE 5/6, stage2 final notes (S2, S2-c, S2-d), rows RESULT. (O5) = "N3'" PROVED by hand (lineality space of
 perm_3 at any base point with nonzero permanent has dim <= 3); corollary lam_{rr'} <= 3 + m^T for B1 blocks. Writing + testing.

## 10. (O5) PROVED: THEOREM N3' (lineality bound for perm_3 at an arbitrary base point)  [rigorous hand proof; numerics agree]
 THEOREM N3'. Let b be a 3x3 complex matrix with k := perm(b) != 0 and V_0 a linear space of 3x3 matrices with
 perm(b + eta) = k for all eta in V_0. Then dim V_0 <= 3.   (b = J is "3x3 level spaces have dim <= 3", Gct/L094 / chief's N3.)
 Notation: A = C[y_1,y_2,y_3]/(y_j^2), rows u_i -> U_i in A_1, perm(u) = U_1 U_2 U_3 in A_3 = C. (m) Multiplication by U != 0,
 A_1 -> A_2, has determinant -2 u_1 u_2 u_3: injective if U is zero-free, otherwise its kernel is a line (spanned by (u_l,-u_l',0) if
 U has exactly one zero, by e_l if U = u_l e_l).  tau(u_1,u_2,u_3) := U_1 U_2 U_3 (trilinear).
 Proof. Suppose dim V_0 = 4. V := Cb + V_0 (5-dim; b not in V_0 because perm(eta) = 0 on V_0), perm(c b + eta) = k c^3 on V, and every
 u in b + V_0 is again a base point. Z_r := {w : e_r w^T in V_0}, Z^j := {y : y e_j^T in V_0}, V_0^(r) := V_0 cap {row r = 0}.
 Step 1 (cell factorisation, as in chief's N3). Fix a cell (r,j), V' := {u in V : u_r in C e_j} (dim >= 3); perm(u) = u_rj q(u^(rj)) on V'
   (q = 2x2 permanent of the minor, a nondegenerate form on C^4); the kernel of V' -> minor consists of elements supported in column j
   (they have perm = 0, so they lie in V_0). If c != 0 on V': q = k' c^2 (k' != 0) on the image, rank one, so the image has dim <= 2
   and Z^j != 0. If c = 0 on V': u_rj q = 0 on V', so either q = 0 on the image (dim <= 2, Z^j != 0) or u_rj = 0 on V', i.e.
   V' = V_0^(r) has dim >= 3.   Hence for every r:  dim V_0^(r) >= 3  or  Z^j != 0 for j = 1,2,3.
 Step 2 (dim V_0^(r) >= 3 is impossible). Let V'' := V_0^(r), rows i,i' the other two. For a base point u and eta in V'':
   perm(u + s eta) = k + s U_r(H_i U_i' + U_i H_i') + s^2 U_r H_i H_i'. So V'' is totally isotropic for Q_u(eta) := U_r H_i H_i' =
   eta_i^T M_u eta_i' (M_u symmetric, zero diagonal, off-diagonal entries u_rj, det M_u = 2 u_r1 u_r2 u_r3, ker M_u = kernel of (m) for U_r)
   and orthogonal to u' := (u_i,u_i'), where Q_u(u') = k != 0.
   (A) u_r zero-free: Q_u is nondegenerate on C^6, u'^perp is a nondegenerate 5-space, so dim V'' <= 2. Hence for EVERY base point the
       row u_r = b_r + eta_r has a zero entry; the affine space b_r + rho_r(V_0) lies in one coordinate plane, and dim rho_r(V_0) =
       4 - dim V'' <= 1; write rho_r(V_0) = C nu.
   (D) u_r not zero-free: rank M_u = 2, Rad Q_u = ker M_u (+) ker M_u (2-dim), u'^perp / Rad is nondegenerate of dim 3, so
       dim V'' <= 3 with equality iff Rad Q_u inside V''. So dim V'' = 3 and Rad Q_u inside V'' for every base point u.
   (E) If nu != 0: either b_r and nu have exactly one common zero; then for generic s, ker M_u is spanned by (b_l + s nu_l, -(b_l' + s nu_l'));
       if nu is not parallel to b_r two values of s give independent vectors and V'' contains a 4-dim space: contradiction; if
       nu = lambda b_r the base point with s = -1/lambda has a zero row: contradiction. Or b_r, nu in C e_l: again a base point with zero
       row. So nu = 0, V_0 = V'', dim V_0 <= 3: contradiction.
   By transposition the same holds for columns. Hence Z^j != 0 and Z_r != 0 for all r, j.
 Step 3 (z_r = z^j = 1). b_r is not in Z_r (else a base point has a zero row), so z_r <= 2, and the spaces e_r (x) Z_r are independent in
   V_0: (z_1,z_2,z_3) = (1,1,1) or a permutation of (2,1,1). In the latter case (z_1 = 2) C b_1 + Z_1 = C^3 and
   tau(v, w^2, b_3 + s w^3) = 0 for all v in C^3 (coefficient of s_2 in tau(b_1 + z_1, b_2 + s_2 w^2, b_3 + s w^3) = k), i.e.
   W^2 B_3 = W^2 W^3 = 0 in A_2: the kernel of (m) for W^2 would contain the plane span(B_3, W^3). Contradiction. So Z_r = C w^r, Z^j = C y^j.
 Step 4. S_R := span{e_r w^rT}, S_C := span{y^j e_j^T} (3-dim each) lie in the 4-dim V_0, so I := S_R cap S_C has dim >= 2.
   (a) A single-row element e_r w^rT lying in S_C forces y^j in C e_r for j in supp w^r, hence e_j in Z_r, hence w^r = e_j (a single
       cell E_rj in V_0) and y^j = e_r. So dim I = 3 (S_R = S_C) would give V_0 containing E_{r,sigma(r)} for a permutation sigma, and the
       coefficient of s_1 s_2 s_3 in perm(b + sum s_r E_{r,sigma(r)}) is 1: contradiction. So dim I = 2 and V_0 = S_R + S_C.
   (b) In the coordinates alpha of S_R, I is a plane Pi. Column j of t(alpha) = sum alpha_r e_r w^rT must lie in C y^j, so diag(w^r_j)_r has
       rank <= 1 on Pi: at most two of w^1_j, w^2_j, w^3_j are nonzero, and if exactly two (zero at r_0) then e_{r_0} lies in Pi, so by (a)
       w^{r_0} = e_{j_0}, y^{j_0} = e_{r_0}.
   (c) Pi contains at most one unit vector: otherwise (after permuting rows and columns) V_0 = span(E_11, E_22, e_3 w^T, y e_3^T); the
       s_1 s_2-coefficient gives b_33 = w_3 = y_3 = 0, then perm(u) = u_31(u_12 u_23 + u_13 u_22) + u_32(u_11 u_23 + u_13 u_21) and the
       coefficients of s_1, s_2 give (b_32 = w_2 = 0 or b_23 = y_2 = 0) and (b_31 = w_1 = 0 or b_13 = y_1 = 0); the two admissible
       combinations leave perm(u) = b_12 u_31 u_23 resp. b_21 u_32 u_13, which is constant only if it is 0: contradiction.
   (d) Not every column has <= 1 nonzero w^r_j (else w^r = e_{sigma(r)}, excluded in (a)). So some column has exactly two, with its zero
       in row r_0, e_{r_0} in Pi, w^{r_0} = e_{j_0}, y^{j_0} = e_{r_0}; w.l.o.g. r_0 = j_0 = 3. Column 3 has w^3_3 != 0, so by (b), (c) it has
       exactly one nonzero entry: w^1, w^2 lie in span(e_1,e_2); transposed: y^1, y^2 lie in span(e_1,e_2).
       Hence V_0 = C E_33 (+) V_blk with V_blk a 3-dim space of matrices supported in the block [12;12].
   (e) The coefficient of s in perm(b + s E_33 + eta), eta in V_blk, is the 2x2 permanent q(b[12;12] + eta): q vanishes on an affine
       hyperplane of C^4, so its leading form vanishes on the 3-dim V_blk -- impossible for the nondegenerate q.   QED
 Numerics (stage3/test_N3prime.py, Grassmannian chart, scipy LM, 116 s): for 8 base points (J, I, structured, random) 3-dim
 lineality spaces are found for all structured b (39 of 72 starts; none for the two random b, as the parameter count predicts) and
 4-dim ones never (0 of 200 starts, residual floors 0.4 - 7).
 COROLLARY N3'-L (for level spaces; (GZ-a) + N3'). Let L be level (any dim), (r,r') a row pair, T a column pair such that the 2x3 block
 K = {r,r'} x T^c is not ell-supporting (type B1). Then the image of {t in L : t_K = 0} in the 3x3 block [other rows; T^c] is a
 lineality space of perm_3 at a point of permanent k' != 0, so it has dim <= 3; its kernel is Y^T (elements of L supported in the two
 columns T). Hence
        dim {t in L : t[rr';T^c] = 0}  <=  3 + m^T,   in particular   lam_{rr'} <= 3 + m^T   and   alpha_K <= m^T + (9 - dim L)
 (alpha_K = number of independent relations of L supported on K; for dim L = 9: alpha_K <= m^T).
 So a B1 block with lam_{rr'} >= 4 forces 2-COLUMN elements on T, and X_{rr'} cap Y^T (elements supported in the 3x2 block
 (other rows) x T) has dim >= lam_{rr'} - 3. Transposed statement for column pairs. Tested on the 12 spaces (stage3/test_O5.py:
 34 B1 blocks, 0 violations; weak test, most 2x3 blocks of the examples are ell-supporting).
STATUS 15:46: N3' written (section 10). Progress on (O1): exact dichotomy "collapsed 4-set / quadruple products of the planes vanish",
 Lemma TV (three 2-planes with vanishing triple product are one coordinate plane), hence in the non-collapsed case the five planes
 pairwise meet (concurrent or coplanar). Writing section 11.

## 11. (O1) THE MINIMAL CASE: reduction to three rigid configurations  [rigorous; ranks checked exactly, stage3/span16_exact.py]
 Setting (M) of section 1: all a_r = 1, all lam = 3, all m = 1, no single-row element; P_i = pi_i(M) 2-planes; Y_ik = C x^{ik},
 x^{ik} = e_i p_ik^T + e_k p_ki^T with p_ik in P_i nonzero. Products are taken in A = C[y]/(y_j^2) (section 7).
 (TR) TRIANGLES. p_ab || p_ac  <=>  x^{bc} is a combination of x^{ab}, x^{ac}  <=>  p_ba || p_bc  <=>  p_ca || p_cb ("abc is a triangle").
      In a 4-set of rows the number of triangles is 0, 1 or 4 (two force all four). A 4-set with four triangles is COLLAPSED:
      x^{ik} = e_i rho_i^T - e_k rho_k^T for vectors rho_i in P_i (i in the 4-set), i.e. L contains the "twisted partial free column"
      F = {sum_i c_i e_i rho_i^T : sum c_i = 0} (3-dim); levelness of F alone gives: equal sums s(rho_i) = s, <rho_i,rho_k> = s^2,
      P_3 of every three rows = 0, P_4 of the 4x5 matrix (rho_i) = 0.
 (MIN-A) DICHOTOMY. For every 4-set {a,b,c,d} of rows: either it is collapsed, or  P_a P_b P_c P_d = 0 in A_4
      (all five 4x4 subpermanents of every 4x5 matrix with rows v_i in P_i vanish).
      Proof: by (T1) (here pi_cd(L_e) = P_c (+) P_d) the 4-linear map mu(v_a,v_b,v_c,v_d) = V_a V_b V_c V_d vanishes on the six subspaces
      p_ik (x) p_ki (x) P (x) P of the 16-dim tensor space. With 0 or 1 triangle these six subspaces span all 16 dimensions (the marked
      lines can be moved to e_1, e_2, e_1+e_2 by GL_2 in each plane; exact rational rank = 16 in both normal forms; = 11 if collapsed).
 (TV) LEMMA. If P_a, P_b, P_c are 2-planes of C^5 with P_a P_b P_c = 0 in A_3 (all 3x3 subpermanents vanish on the product), then
      P_a = P_b = P_c = span(e_j, e_l) for one column pair.
      Proof: for a 2-plane P the space K(P) = {Q in A_2 : Q P = 0} has dim <= 1 (support of P of size 2, 3: direct; size 4: the
      kernels of two non-proportional zero-free forms on 4 variables are different planes; size 5: Lefschetz). P_a P_b = 0 is
      impossible, so P_a P_b is a line C Q_0, the product map P_a x P_b -> A_2 has rank one, every v_a has a partner v_b != 0 with
      V_a V_b = 0, so by (Q0) every vector of P_a (and of P_b) has support <= 2: P_a = P_b = span(e_j,e_l), Q_0 = y_j y_l, and
      Q_0 P_c = 0 forces P_c = span(e_j,e_l).
 (MIN-B) THEOREM. In the minimal case, if NO 4-set is collapsed then the five planes P_i pairwise meet: P_d cap P_e != 0 for all d, e.
      Hence either (I-alpha) they have a common nonzero vector v_0, or (I-beta) they lie in one 3-dim subspace V_3 of C^5
      (all rows of all elements of M lie in V_3).
      Proof: if P_d cap P_e = 0, every w in P_a P_b P_c is killed by P_d and by P_e (MIN-A for abcd and abce), so its matrix B_w kills
      a 4-dim space and w = 0; by (TV) P_a = P_b = P_c = span(e_j,e_l), so the 3-dim space X_de lives in a 3x2 block; but a 3x2 level
      space has dim <= 2 (L101). Pairwise meeting lines of P^4 are concurrent or coplanar.
 CONSEQUENCE. The minimal case survives only in three rigid configurations:
      (I-alpha) no collapsed 4-set, a common vector v_0 in all P_i, and the 10-dim product space (+) e_i (x) P_i lies in Sing(perm_5)
                (all 4x4 subpermanents vanish on it), so on M only P_1 = P_2 = P_3 = 0 remain;
      (I-beta)  no collapsed 4-set, all P_i inside a 3-space V_3, same Sing(perm_5) property; for triples abc with P_d != P_e the
                products P_a P_b P_c lie in the <= 1-dim space of B with B V_3 = 0, which is nonzero only if V_3^perp is spanned by two
                vectors with disjoint supports (a TWO-BLOCK structure again);
      (II)      a collapsed 4-set: L contains a twisted partial free column F on four rows.
      None of the three is excluded yet. (II) is the natural "deletable column" candidate: for rho_i = e_j it is S3-B's domino branch.
STATUS 15:57: case (I) of section 11 killed under (NZ) by a complete case analysis (section 12): the minimal case forces a collapsed 4-set.

## 12. THEOREM MIN-C: under (NZ) the minimal case has a COLLAPSED 4-set  [rigorous hand proof; expansions checked, stage3/test_blocks.py]
 (NZ) no column vanishes identically on M (equivalently the supports of P_1..P_5 cover all columns). (NZ) holds whenever all b_c <= 2,
      because M inside L^j would give dim L^j = 4 + b_j >= 7.
 (NT) no three planes equal one coordinate plane span(e_j,e_l)  [always true: X_de would be a 3-dim level space in a 3x2 block].
 THEOREM MIN-C. In the minimal case with (NZ), case (I) of section 11 is impossible: some 4-set of rows is collapsed, i.e. L contains
      F = {sum_{i in N_4} c_i e_i rho_i^T : sum c_i = 0}, rho_i in P_i, s(rho_i) = s, <rho_i,rho_k> = s^2, R_i R_k R_l E^2 = 0, R_a R_b R_c R_d = 0.
 Proof. Assume no collapsed 4-set: (Q4) P_a P_b P_c P_d = 0 in A_4 for all 4-sets (MIN-A), and the planes pairwise meet (MIN-B).
 (alpha) CONCURRENT, v_0 in all P_i. V_0^4 = 0 gives |supp v_0| <= 3.
   |supp v_0| = 3: V_0^3 = 6 v_S y_S (S = supp v_0) and V_0^3 P_d = 0 give P_d inside C^S for all d: contradicts (NZ).
   |supp v_0| = 2 = {j,l}, N = other columns: V_0^2 V_c V_d = 0 gives (V_c|N)(V_d|N) = 0 in A_N for c != d; P_i|N = C pi_i|N (dim <= 1); at most two
     restrictions vanish (NT); nonzero restrictions with pairwise zero products have a common support of size 1 (size 2 would need
     pairwise opposite ratios for >= 3 vectors): all P_i inside C^{j,l,m}: contradicts (NZ).
   v_0 = e_j, P_i = C e_j + C pi_i with pi_i != 0 in C^N, N = the other four columns: (Q4) <=> all triple products Pi_b Pi_c Pi_d = 0 in (A_N)_3.
     Let k = max |supp pi_i| (attained at i = 1).
     k = 4 (scale columns: pi_1 = 1_N): Pi_1 Pi_c != 0, so the other three vectors lie in the <= 2-dim space killed by it: pi_2..pi_5 are
       proportional or span a plane G'. Pi_c Pi_d lies in K_1 = ker(Pi_1 .) = {a(y1y2+y3y4) + b(y1y3+y2y4) + c(y1y4+y2y3), a+b+c = 0}
       (nonzero elements have >= 4 nonzero coefficients). U^2 in K_1 forces u = e_m; y_m W in K_1 forces w in C e_m. Direction patterns
       of pi_2..pi_5: (4), (3,1): >= 3 equal unit vectors, against (NT); (2,2): y_m y_m' not in K_1; (2,1,1): excluded by the y_m W rule;
       (1,1,1,1): the vector-valued cubic of G' vanishes, G' = span(e_m,e_m'), and then q(pi_c,pi_d) = 0 for all pairs of four pairwise
       non-proportional vectors, impossible.
     k = 3 (pi_1 = (p_1,p_2,p_3,0)): K_1 consists of Q supported on pairs inside {1,2,3}, so (Pi_c Pi_d)[n4] = pi_cn pi_d4 + pi_c4 pi_dn = 0
       (n = 1,2,3; c != d in 2..5). By (NZ) some pi_c4 != 0; then every other pi_d is proportional to (-pi_c|123, pi_c4) with pi_d4 != 0;
       applying this twice gives pi_c proportional to e_4 and four vectors in C e_4: against (NT).
     k <= 2: read the pi_i as loops/edges on the vertex set N. Three edges forming a path of length 3, a star K_{1,3}, or two disjoint
       edges plus a loop have a nonzero triple product (unique systems of distinct representatives); two parallel edges need q = 0
       (opposite ratios) as soon as a third element exists. So the distinct edge supports lie in a triangle or form a perfect
       matching. Perfect matching {12,34}: no loops, classes of size <= 2 each: only 4 elements. Triangle: the fourth vertex v is touched
       by loops only (<= 2 by (NT)); y_v Pi_b Pi_c = 0 makes the >= 3 other elements pairwise zero-product, hence of equal support:
       three equal loops (against (NT)) or three vectors on one edge with pairwise opposite ratios. Contradiction.
 (beta) COPLANAR, not concurrent: all P_i in a 3-space V_3. All equal: Pi^4 = 0 gives support <= 3 columns, against (NZ). Otherwise
   P_d + P_e = V_3 for some d != e; W_abc = P_a P_b P_c != 0 (TV + NT) is killed by V_3, so V_3 = (alpha,beta)^perp with disjointly
   supported alpha, beta (section 7 (i)), and by (NZ) both blocks have size >= 2:
   type (2,2,1): rows v_i = lam_i h + mu_i h' + nu_i e_5, product = F_220 H^2 H'^2 + F_211 H^2 H' y + F_121 H H'^2 y with F_220 =
     sum_{|S|=2} lam_S mu_{S^c} etc. A row is "pinned" if e_5 in P_i (then (lam,mu) = theta (p_i,q_i), nu free), else free. F_220 = 0 needs
     >= 3 pinned rows in every 4-set, so <= 1 free row; one free row d: the nu_a-coefficients of F_211 give p_b = p_c = 0 for all
     pinned pairs and then F_121 contains lam_d theta_b theta_c q_b q_c != 0. No free row: every triple of the forms l_i = p_i X + q_i Y
     has l_b l_c l_d = A X^3 + B Y^3, which forces all five directions equal, i.e. all planes equal: excluded.
   type (2,3,0): rows v_i = lam_i h + om_i, om_i in V_beta (2-dim, in three columns); the H-component of (Q4) is
     sum_k lam_k tau(om_i, i != k) = 0, tau = polar form of the cubic om_3 om_4 om_5 on V_beta, which has three distinct roots (~ X^3 + Y^3,
     no singular direction, tau(u,w,.) = 0 only for the pair of directions (1,0),(0,1)). Row pinned if h in P_i. A 4-set without
     pinned row has four planes equal to V_beta and then the fifth as well: excluded. Hence every 4-set has >= 2 pinned rows, <= 2 free
     rows; exactly 2 free: tau(om_b^0,.,.) = 0, impossible; exactly 1 free: three pinned directions pairwise of type {(1,0),(0,1)},
     impossible; no free row: h in all P_i, the concurrent case with |supp v_0| = 2.          QED
 Numerical corroboration of the sub-case v_0 = e_j (stage3/test_alpha_ej.py, 14 s): LM on five unit vectors of C^4 with all triple
 products zero converges in 120/120 starts, always to solutions covering <= 3 columns (94 times all five on one coordinate line);
 no solution satisfies (NZ) and (NT). (Corroboration only: LM favours the large components.)
 COROLLARY. In the regime all a_r = 1, all b_c <= 2 (in particular the regime all a = b = 1 in which no line is deletable), the minimal
 case of stage 3 survives only as configuration (II): a twisted partial free column on four rows. For rho_i = e_j this is the
 domino branch of S3-B, where (L3) hands it to the deletable-line normal form.

## 13. Configuration (II) (the only survivor of the minimal case under (NZ)) and the open list after round 2
 (II) N_4 = {a,b,c,d} collapsed, e the fifth row: x^{ik} = e_i rho_i^T - e_k rho_k^T in L, rho_i in P_i. Known (all rigorous):
   (II.1) s(rho_i) = s, <rho_i,rho_k> = s^2, E^2 R_i R_k R_l = 0, R_a R_b R_c R_d = 0 in A_4 (all five 4x4 subpermanents of the 4x5 matrix rho).
   (II.2) For every u in L^ (lineality of F, coefficients of the squarefree polynomial in c on sum c = 0):
          perm(u with row i replaced by rho_i) does not depend on i in N_4; perm(u with two, three or four rows of N_4 replaced by the
          corresponding rho's) = 0.   [for rho_i = e_j this is zeros' free-column reduction]
   (II.3) Either all five 4-sets are collapsed (then rho_e exists as well and L contains the 4-dim "twisted full free column"
          F_5 = {sum_i c_i e_i rho_i^T : sum c = 0}), or N_4 is the only collapsed 4-set; then (Q4) holds for the four 4-sets containing e
          and the planes P_a, P_b, P_c, P_d pairwise meet (P_c cap P_d = 0 would give P_a = P_b = P_e = span(e_j,e_l) by (TV), against (NT)).
   (II.4) If all rho_i are equal (rho_i = v) then v = s e_j (elementary symmetric functions (s,0,0,0,0)): an honest partial free column,
          i.e. S3-B's domino branch: z^j = 3, and by (L3) either b_j = 2 and column j is deletable (rows' normal form, f = 3, dim L' = 6,
          defect <= 1) or b_j = 1.
   (II.5) (II.1) ALONE DOES NOT FORCE rho_i in C e_j. Exact example (level error 7e-14, stage3/twisted.py): iota = (1,w,w^2,0,0)
          (sum 0, iota.iota = 0), rho_1 = e_4 + t_1 iota, rho_2 = e_4 + t_2 iota, rho_3 = rho_4 = rho_5 = e_4: F_5 is a 4-dim level space,
          a "sheared" copy of free column (+) C e_1 iota^T (+) C e_2 iota^T; it contains neither a single-row element nor the full free
          column, and Q_x != 0 for x^{12}. So (II*) needs the planes P_i / (T1) / the 2-dim extension, not only levelness of F.
   OPEN (II*): show rho_i in C e_j for all i (equivalently Q_x = 0 for the elements of F), or exclude the twisted column directly.
   This is an EXACTLY TESTABLE finite problem: unknowns a 4x5 (or 5x5) matrix rho with (II.1) [5 + 6 + ... polynomial equations],
   the planes P_i containing rho_i with (T1)/(Q4), and a 7-dim M.
 REMAINING OPEN LIST (precise):
   (R1) (II*) above  -- the minimal case of stage 3 in the regime all a_r = 1, all b_c <= 2.
   (R2) the minimal case when some column vanishes on M (then b_j >= 3 for that column: outside the regime all b_c <= 2).
   (R3) non-minimal all a_r = 1: some lam >= 4, m >= 2 or z >= 1. New input: Corollary N3'-L (a B1 pair with lam >= 4 forces 2-column
        elements on T and elements supported in a 3x2 block). Not analysed further.
   (R4) rows with a_r >= 2 ((H1) alone gives no 2-row elements for (2,2,2) triples; T1 weakens to "product in N_e cap 1^perp").
   (R5) from single-line elements to a deletable line (z_r = 5 - a_r); only the domino branch (L3) reaches it.
STATUS 15:58: round-2 RESULT written at top; sections 10-13 complete.
STATUS 16:03: (II.5) twisted-column example and the corroboration test added. Final report follows.

# ROUND 3 (start 16:09, budget 75 min -> ends ~17:24)
STATUS 16:10: read stage2 RESULT-R2 (GEN-2, GEN-3, one-zero layer) and rows' Corollary H / Lemma TC. Target (R1): configuration (II*).
STATUS 16:18: (R1) SETTLED: configuration (II) is impossible under (NZ). Mechanism: (Q4) holds for a COLLAPSED 4-set as well (full use of
 zeros' CA2 on the explicit normal form of L_e), so MIN-B / MIN-C apply to every 4-set. Section 14.

## 14. THEOREM MIN-D: THE MINIMAL CASE IS IMPOSSIBLE UNDER (NZ)   [rigorous hand proof; numerical corroboration of the plane lemma]
 LEMMA Q4-coll. In the minimal case, (Q4) P_a P_b P_c P_d = 0 in A_4 holds ALSO for a collapsed 4-set N_4 = {a,b,c,d} (e = fifth row).
 Proof. Write P_i = C rho_i + C sigma_i (i in N_4), F = {sum c_i e_i rho_i^T : sum c = 0} (3-dim, inside the 5-dim L_e), Lam := L_e / F
 (2-dim). For xi in L_e: xi_i = c_i(xi) rho_i + lam_i(xibar) sigma_i with linear forms lam_i on Lam, lam_i != 0 (pi_i(L_e) = P_i), and
 xi -> (c, xibar) embeds L_e as a hyperplane sum_i c_i = nu(xibar) of C^4 x Lam. If all lam_i were proportional, an element with
 xibar in their common kernel would be sum c_i e_i rho_i^T with sum c != 0, and L would contain the single-row elements e_i rho_i^T:
 excluded. So the lam_i span Lam^*, and replacing sigma_i by sigma_i + t_i rho_i (sum t_i lam_i = nu) gives the NORMAL FORM
        L_e = { xi(c,mu) : xi_i = c_i rho_i + lam_i(mu) sigma_i,  c in C^4, sum c = 0,  mu in C^2 }.
 Zeros' (CA2) (a_e = 1):  prod_{i in N_4} (c_i R_i + lam_i(mu) S_i) = 0 in A_4 on this space (R_i, S_i the forms of rho_i, sigma_i).
 Each mu-degree vanishes separately, and a squarefree polynomial in c of degree 2, 3 or 4 that vanishes on sum c = 0 is zero, while
 a linear one has equal coefficients. Hence:  degree 0: R_a R_b R_c R_d = 0;  degree 1: R_{N-k} S_k = 0;  degree 2: R_i R_j S_k S_l = 0;
 degree 4: S_a S_b S_c S_d = 0;  degree 3: Lam_k(mu) theta_k = h(mu) for all k, where theta_k := R_k S_{N-k} and Lam_k := prod_{l != k} lam_l.
 If h != 0 then all theta_k are parallel and all cubics Lam_k proportional, i.e. all lam_k proportional: excluded. So theta_k = 0.
 All 16 products with factors R_i or S_i vanish, i.e. P_a P_b P_c P_d = 0.   QED
 THEOREM MIN-D. Let L be a 9-dim level space with all a_r = 1, all lam_{rr'} = 3, all m_ab = 1 and no single-row element (the
 minimal case). Then some column vanishes identically on M = sum_r L_r (7-dim); in particular b_j >= 3 for that column.
 Equivalently: in the regime all a_r = 1, all b_c <= 2, the minimal case does not occur.
 Proof. (Q4) holds for every 4-set of rows (MIN-A if not collapsed, Lemma Q4-coll if collapsed). MIN-B and the case analysis of
 MIN-C use only (Q4) for all 4-sets, (TV), (NT) and (NZ); they show that (NZ) fails.   QED
 (Section 12's proof is literally the proof of the following PLANE LEMMA: five 2-planes of C^5 with P_a P_b P_c P_d = 0 for all five
 4-sets, whose supports cover all five columns, contain three planes equal to one coordinate plane span(e_j,e_l).)
 Numerical corroboration of the plane lemma (stage3/test_Q4planes.py, test_Q4planes_sep.py; LM on 5 planes, gauge-fixed, every
 column of norm >= 0.45): 185 of 191 starts converge, ALL to configurations with four planes equal to one coordinate plane; with
 the planes forced pairwise distinct (projector distance >= 0.6): 0 of 35 starts, residual floor 0.355. (Corroboration only.)
 CONSEQUENCE for configuration (II) of section 13: it does not occur under (NZ); (R1) is closed. The sheared example (II.5) is not a
 counterexample: it is a 4-dim level space, not the F of a minimal-case L.
STATUS 16:23: (R2) SETTLED as well: the minimal case with a vanishing column is impossible (two vanishing columns: checked L156;
 one: concurrent case by supports, coplanar case by a polar argument). So THE MINIMAL CASE DOES NOT OCCUR AT ALL. Section 15.

## 15. THEOREM MIN-E: the minimal case is impossible (also when a column vanishes on M)   [rigorous hand proof, NOT yet independently verified]
 Setting: minimal case, Z := set of columns vanishing identically on M, N := [5] - Z; all P_i lie in C^N; (Q4), (TV), (NT), MIN-B hold.
 (a) |Z| >= 2 is impossible: M would be a 7-dim level space of 5 x 3 matrices; its transpose is a 3 x 5 level space, and the checked
     Gct/L156 gives dim <= q + 1 = 6.
 (b) |Z| = 1 (N = four columns, the supports of the P_i cover N). Now (Q4) is ONE scalar condition: the 4x4 permanent tau_4 on the
     columns N vanishes on P_a x P_b x P_c x P_d for all 4-sets. MIN-B still holds (for w in P_a P_b P_c the product w v is <beta_w, v> y_N
     with beta_w in C^N; P_d + P_e = C^N would give w = 0): the planes pairwise meet, so they are concurrent or coplanar.
   (b-alpha) CONCURRENT, v_0 in all P_i: tau_4(v_0,v_0,v_0,v_0) = 24 prod v_0n = 0, so |supp v_0| <= 3.
     |supp v_0| = 3 (zero at n_0): tau_4(v_0,v_0,v_0,v_d) = 6 v_{d n_0} prod_{n != n_0} v_0n forces column n_0 to vanish: contradiction.
     |supp v_0| = 2 = {j,l}, {n,n'} the other two columns: tau_4(v_0,v_0,v_c,v_d) = 2 v_0j v_0l q_{nn'}(v_c,v_d), so the restrictions
       r_i of P_i to {n,n'} (dim <= 1, at most two of them zero by (NT)) are pairwise q-orthogonal; three such nonzero vectors are all
       multiples of one unit vector, so a further column vanishes: contradiction.
     v_0 = e_j: P_i = C e_j + C pi_i, pi_i != 0 in C^3 (the other three columns), all 3x3 permanents of triples vanish, supports cover the
       three columns, at most two pi_i on each coordinate line (NT). A zero-free pi_1 is impossible: mult by Pi_1 is an isomorphism
       A_1 -> A_2 in three variables, so pi_2..pi_5 lie in a plane G' (or are proportional) and are pairwise orthogonal for the
       nondegenerate form tau(pi_1,.,.); >= 3 directions or the pattern (2,2) make G' totally isotropic (impossible), (3,1) and (4)
       force u = e_m three times (against (NT)). So all pi_i are loops/edges on three vertices: two distinct edge supports exclude
       loops and force classes of sizes (2,2,1), where the triangle triples give rho = -rho; one edge support leaves <= 2 edges +
       <= 2 loops at the third vertex; no edge: e_1, e_2, e_3 have permanent 1. Contradiction in all cases.
   (b-beta) COPLANAR with >= 3 distinct planes (all P_i in a 3-space V_3; no concurrency assumption needed). If P_d != P_e then
     P_d + P_e = V_3 and (Q4) for abcd, abce gives   (*)  tau_4(p_a,p_b,p_c,.) = 0 on V_3 for all p_i in P_i.
     c_4 := tau_4(v,v,v,v) = 24 prod_n v_n is not identically zero on V_3, and the four forms v_n|V_3 have no common zero.
     Multiplicity pattern of the planes (Pi_1, Pi_2, ... the distinct ones):
       (1,1,1,1,1): (*) for all triples; tau_4(p_a,p_b,.,.) is killed by three distinct planes, so it vanishes; then tau_4(p_a,.,.,.) = 0
                    and tau_4 = 0 on V_3: contradiction.
       (2,1,1,1):   tau_4(p,q,.,.) = 0 on V_3 for p in Pi_1 and q in any plane, so the first polar of c_4 at every p in Pi_1 vanishes:
                    c_4 = A l^4 with l the equation of Pi_1; then all v_n|V_3 are proportional: dim V_3 <= 1. Contradiction.
       (2,2,1):     tau_4(p,q,.,.) = 0 for p in Pi_1, q in Pi_2; with coordinates x, y, z (Pi_1 = {x=0}, Pi_2 = {y=0}):
                    d_y c_4 = a y^3, d_x c_4 = g x^3, d_z c_4 = 0, so c_4 = A x^4 + B y^4 and all four v_n vanish at the vector x = y = 0 of
                    V_3: contradiction.
       (3,1,1):     tau_4(p,p',.,.) = 0 for p, p' in Pi_1: c_4 = x^3 (A x + B y + C z), three of the v_n|V_3 proportional: dim V_3 <= 2.
     With <= 2 distinct planes the configuration is concurrent (b-alpha) (all equal: c_4 = 0 on the plane, a column vanishes).
 THEOREM MIN-E. A 9-dim level space with all a_r = 1 and all lam_{rr'} = 3 has some m_ab >= 2 or a single-row element.
 (Chain of dependencies: (M) of section 1; zeros' CA2; T1; MIN-A [exact rank]; Lemma Q4-coll; TV; NT [L101 for 2 x 3]; MIN-B;
 the plane lemma of section 12 for |Z| = 0; (a) [checked L156]; (b) for |Z| = 1.)
STATUS 16:31: (R3) partly settled: THEOREM N1 -- all a_r = 1 and ALL lam = 3 force a single-row element (the m = 2 pairs are handled by an
 "injectivity of restriction" argument with exact rank checks). The case "some lam >= 4" is reduced to one rigid family. Section 16.

## 16. THEOREM N1 (all lam = 3) and the reduction of the case lam >= 4   [rigorous hand proof + exact rational rank checks; NOT yet verified]
 Setting (G): L level, dim 9, all a_r = 1, lam_{rr'} >= 3 for all row pairs, NO single-row element (z = 0). Elementary facts:
   (G1) Y_ab (+) Y_ae lies in X_cd (the pairs meet in Z_a = 0), so m_ab + m_ae <= lam_cd; pi_c is injective on Y_cd, so
        m_cd <= dim pi_c(L_r) = 5 - lam_{rc} for r not in {c,d}; in particular m <= 2, and m_cd = 2 forces lam_{rc} = lam_{rd} = 3 for the
        three rows r outside {c,d}.
   (G2) lam_ab >= 4 forces m_cd, m_ce, m_de >= 2 (pigeonhole (P)), hence = 2, hence by (G1) ALL OTHER lam are 3. So in (G):
        either all lam = 3 [case N1], or exactly one pair (a,b) has lam_ab in {4,5}, all other lam = 3, m_cd = m_ce = m_de = 2 [case N2].
 CASE N1 (all lam = 3). m in {1,2}; the pairs with m = 2 are pairwise disjoint (G1). P_i := pi_i(L_r) is a 2-plane independent of r
   (pi_i(X_rr') has dim 3 - m_jk; the graph "r ~ r' iff m_jk = 1" on the four rows != i is connected). (NT), (TV) hold as before.
   LEMMA Q4-gen. In case N1, P_a P_b P_c P_d = 0 in A_4 for EVERY 4-set (e = fifth row).
   Proof. (CA2) says the A_4-valued 4-linear map mu vanishes on the diagonal of L_e inside P_a + P_b + P_c + P_d. By the m's of the six
   pairs of the 4-set:
     (t0) all m = 1: MIN-A (0 or 1 triangle) or Lemma Q4-coll (collapsed) -- these used only the structure of L_e.
     (t1) one pair ab with m = 2: Y_ab is the graph of an isomorphism phi: P_a -> P_b; X_ed = Y_ab + C x^{ac} forces
          x^{bc} = (0; phi p_ac; -p_ca), likewise for d. Normal forms of L_e (coordinates in the indicated bases):
            no triangle acd:   xi_a = v + al p_ac + be p_ad, xi_b = phi v, xi_c = al p_ca + ga p_cd, xi_d = be p_da + ga p_dc;
            triangle acd:      xi_a = v + (al+be) p + de w,   xi_b = phi v, xi_c = al q + de s_c,     xi_d = be r + de s_d
                               (zeta = (w;0;s_c;s_d) the fifth element; either w independent of p, or w = 0 after reparametrising).
     (t2) two pairs ab, cd with m = 2:  xi_a = v + de w, xi_b = phi v, xi_c = u + de s, xi_d = psi u.
   In each normal form the 16 products (coordinate of xi_a)(coordinate of xi_b)(coordinate of xi_c)(coordinate of xi_d) are LINEARLY
   INDEPENDENT quartics in the five parameters (exact rational rank 16, stage3/q4_m2.py: four normal forms). So the restriction map
   {4-linear forms} -> {quartics on L_e} is injective and mu = 0.   QED
   THEOREM N1. A 9-dim level space with all a_r = 1 and all lam_{rr'} = 3 CONTAINS A SINGLE-ROW ELEMENT.
   Proof. Otherwise case N1 holds; (Q4) for all 4-sets, (TV), (NT) give MIN-B and the plane lemma: with Z = columns on which all P_i
   vanish, |Z| = 0 is impossible (section 12), |Z| = 1 is impossible (section 15 (b)), |Z| >= 2 is impossible (L_c + L_d is a 7-dim
   level space on three columns; checked L156).   QED
   (MIN-E is the special case "all m = 1".)
 CASE N2 (one pair (a,b) with lam_ab in {4,5}; not excluded). Known: P_c, P_d, P_e, P_a := pi_a(L_c) = pi_a(L_d) = pi_a(L_e), P_b
   are 2-planes; pi_a(L_b) = C rho_a inside P_a and pi_b(L_a) = C rho_b inside P_b are lines (or 0 if lam_ab = 5);
   Y_cd, Y_ce, Y_de are graphs of isomorphisms; X_ab contains Y_cd (+) Y_ce (equality if lam_ab = 4).
   (Q4) holds for the three 4-sets containing a and b (types (t1)/(t2) for L_c, L_d, L_e); for L_a the normal form
   xi_b = de rho_b, xi_c = v + v' + de w, xi_d = phi v, xi_e = chi v' gives (hand computation: the 8 products are independent)
   rho_b . P_c P_d P_e = 0 in A_4, and symmetrically rho_a . P_c P_d P_e = 0 -- weaker than (Q4) for the 4-sets {b,c,d,e}, {a,c,d,e}, so
   the plane lemma does not apply as it stands. N3'-L applies: every B1 column pair T for (a,b) carries an element of X_ab supported
   in the 3x2 block cde x T.
   lam_ab = 5 is impossible: L_a = L_b would be a hyperplane of the 6-dim P_c + P_d + P_e and meet e_c (x) P_c: a single-row element.
   So N2 means lam_ab = 4, X_ab = Y_cd (+) Y_ce = {(v + v'; phi v; chi v')}, L_a = X_ab + C x^{bc}, L_b = X_ab + C x^{ac}, with
   x^{bc} = (rho_b; w), x^{bd} = (rho_b; -phi w), x^{be} = (rho_b; -chi w) and the same with (rho_a, w') for row a (w, w' in P_c).
   Also P_c, P_d, P_e pairwise meet (else three of the planes P_a, P_b, P_. would be one coordinate plane) and P_c P_d P_e != 0.

## 17. STATE OF STAGE 3 AFTER ROUND 3, and the precise remaining list
 PROVED (hand proofs + exact/numerical checks; verification by a second agent pending for sections 12, 14, 15, 16):
   in a 9-dim level space with all a_r = 1 and lam_{rr'} >= 3 for all row pairs [(H1) for rows], EITHER there is a single-row element,
   OR case N2 holds (exactly one pair with lam = 4, all other lam = 3, the three opposite pairs carry 2-dim spaces of 2-row elements).
   In particular: all a_r = 1 and all lam = 3  =>  single-row element (Theorem N1); the minimal case and configuration (II) do not occur.
 REMAINING:
   (S1) CASE N2 (section 16): exclude it or find a single-row element. Tools ready: (Q4) for the three 4-sets containing a,b;
        rho_a P_c P_d P_e = rho_b P_c P_d P_e = 0; Lemma T / (TV); N3'-L (3x2-block elements for every B1 column pair of (a,b)).
   (S2) rows with a_r >= 2: (H1) gives no 2-row elements for (2,2,2) triples; needs stage 2 in the form lam >= a_r + a_r' + 1, and the
        (CA2)-based tools weaken ("product in N_e cap 1^perp"). This is the regime where a deletable line can exist.
   (S3) AFTER a single-row element e_r w^T is found (regime all a_r = 1): by (SR) every column j in supp(w) has an FK annihilator
        vanishing at r, and perm_4(t^(rj)) = 0 on L^j. Turning this into a contradiction (all a = b = 1: no deletable line exists,
        Lemma DS) or into rows' defect normal form (Corollary H: single-row parts <= e, two-row parts <= e + 1) is not done.
   (S4) the column-side statements are the transposes (all b_c = 1, all lam^{cc'} = 3 => single-column element).
STATUS 16:33: round-3 RESULT at top; sections 14-17 written. Remaining time: attempt on N2.
STATUS 16:35: N2 attempted, not closed. Extra rigorous facts for whoever continues (all in the setting of section 16, case N2):
 - pi_ab(L_r) (r = c,d,e) is 3-dim and contains Pi_0 := span{(rho_a,0),(0,rho_b)} = pi_ab(L_a + L_b); L_c is not inside L_a + L_b.
 - if w || w' (the row-c parts of x^{bc}, x^{ac}) then Y_ab contains e_a rho_a^T - lambda e_b rho_b^T (a collapsed triple a,b,c);
   otherwise pi_ab(Y_ab) meets Pi_0 trivially.
 - (T1) for x = (v; phi v) in Y_cd:  V Phi(V) R_a R_b = 0,  V Phi(V) R_a P_e = 0,  V Phi(V) R_b P_e = 0 in A_4 (and the analogues for Y_ce, Y_de).
 - Q := R_a R_b satisfies Q P_c P_d = Q P_c P_e = Q P_d P_e = 0, so Lemma T's algebra applies to Q and the pairwise meeting planes P_c, P_d, P_e.
 - by (L1) Q is not identically 0 on the 2-dim spaces Y_cd, Y_ce, Y_de (they contain no single-row element).
 - P_c = P_d = span(e_j,e_l) is impossible (Y_cd would be a 2-dim level space of 2x2 matrices; L101 gives <= 1).
 - for EVERY column pair T the block ab x T^c carries a relation of L (dim{t in L: t[ab;T^c] = 0} >= lam_ab = 4 > 3). Dichotomy:
   either that block is ell-supporting, or (B1, by N3'-L) X_ab contains a nonzero element supported in the columns T, and then at
   least two of P_c, P_d, P_e contain a nonzero vector supported in T. A count of 2-sparse vectors in three 2-planes (<= 7 pairs T
   per plane, attained only by coordinate planes; three coordinate planes never cover all ten T twice) shows that NOT all ten
   column pairs are B1: at least one block ab x (three columns) is ell-supporting.
 - all relations (n_a, n_b) of L supported on rows a,b satisfy <n_a,rho_a> = 0 = <n_b,rho_b>.
STATUS 16:42: final report follows.

# ROUND 4 (start 16:39, budget 75 min -> ends ~17:54)
STATUS 16:41: read coordinator message, verifyfl round 2 (Lemma EQ, TC5), upstream L156 / L157 / L_gct_215. Target (S1): family N2.
STATUS 16:44: N2 analysis: twisted form and identity (Q5) (section 18, (N2-a)-(N2-c)).
STATUS 16:56: survey: no N2-shaped row pair occurs in the 12 known level spaces or their transposes (stage3/survey_n2.py).
STATUS 17:06: CORRECTION of my 16:44 draft of (N2-c): "B_w 1 = 0 unless kappa^a = kappa^b" and "W is one-dimensional" were NOT justified
 (B_w 1 is only orthogonal to {t_a + t_b : t in L}); removed. New rigorous facts (N2-d)-(N2-f): M = sum of all L_r is 7-dim with all rows
 in the planes P_r; rank-one products P_a P_b P_i; identity (E1).
STATUS 17:16: numerical experiment (N2-g): the necessary conditions on L_a alone DO have non-degenerate solutions; all found ones have
 rho_b = unit vector e_j lying in P_c, P_d, P_e. Conditional reduction (N2-h): such an N2 contains a 3-dim single-column space.

## 18. FAMILY N2: structure, identities, numerical classification of L_a, conditional reduction  [rigorous unless marked; NOT verified]
 Setting: section 16, case N2 (rows a,b with lam_ab = 4, S = {c,d,e}, all other lam = 3, no single-row element, all a_r = 1).
 (N2-a) TWISTED FORM. With V := P_c (2-dim), alpha_c = id, alpha_d = -phi, alpha_e = -chi (isomorphisms V -> P_c, P_d, P_e):
        X_ab = { sum_{i in S} e_i alpha_i(v_i)^T : v_c + v_d + v_e = 0 },      Y_ik = { e_i alpha_i(v)^T - e_k alpha_k(v)^T : v in V },
        L_a  = { mu e_b rho_b^T + sum_S e_i alpha_i(v_i)^T : v_c + v_d + v_e = mu w },   L_b likewise with (lambda, rho_a, w')  (w, w' in V nonzero),
        F := L_a + L_b = { (lambda rho_a; mu rho_b; alpha_c v_c; alpha_d v_d; alpha_e v_e) : sum v_i = mu w + lambda w' } = {t in L : t_a in C rho_a}, dim 6.
        Level conditions of X_ab alone: s o alpha_i = sigma (one form on V for all i); <alpha_i v, alpha_k v'> = sigma(v) sigma(v') +
        g_ik omega(v,v') (omega = area form of V, g_cd - g_ce + g_de = 0); cubic part: see (Q5) at u = J.
        Level conditions of L_a: s(rho_b) = -sigma(w); <rho_b, alpha_i v> = -sigma(w) sigma(v) - c_i omega(v,w), c_c - c_e = g_ce, c_d - c_e = g_de.
 (N2-b) LINEALITY of X_ab in L^: for every u in L^ and v in V, perm(u with row i replaced by alpha_i(v)) is the same for i = c,d,e; and
        (v,v') -> perm(u with rows i,k replaced by alpha_i(v), alpha_k(v')) is SKEW-symmetric (i != k in S)
        [s- and s^2-coefficients of perm(u + s x), x in X_ab, and the coefficient comparison on {v_c + v_d + v_e = 0}].
 (N2-c) IDENTITY (Q5):   P_c P_d P_e . U_a U_b = 0 in A_5   for ALL u in L^   (perm[u_a; u_b; y_c; y_d; y_e] = 0 for all y_i in P_i).
        Proof: s^3-coefficient of perm(u + s x), x in X_ab; a trilinear form on V^3 vanishing on the diagonal of {sum v_i = 0} vanishes
        identically (phi(v_c, v_d, -v_c-v_d) = 0: compare the coefficients of the monomials in (v_c, v_d)).   QED
        Consequences for every w in W := P_c P_d P_e (W != 0, section 16), B_w its symmetric zero-diagonal matrix:
          B_w rho_a = B_w rho_b = 0;    1^T B_w 1 = 0  (u = J: perm_3 vanishes identically on P_c x P_d x P_e);
          B_w 1 is orthogonal to N_ab := {t_a + t_b : t in L}  (which contains rho_a, rho_b);   t_a^T B_w t_b = 0 for t in L.
          With pi_ab(L) = graph of the isomorphism theta: kappa^a-perp / C rho_a -> kappa^b-perp / C rho_b (3-dim spaces), the form
          (x,x') -> x^T B_w theta(x') is ALTERNATING on a 3-dim space, hence degenerate.
        [CORRECTION: an earlier draft claimed B_w 1 = 0 and dim W = 1 in the generic case; that used N_ab = pi_a(L) + pi_b(L), which is
         not known. In the numerical solutions of (N2-g) dim W = 3.]
 (N2-d) THE 7-DIM CORE. M := {t in L : t_r in P_r} is THE SAME 7-dim space for every row r, M = L_a + L_c = sum of all L_r = F + L_i
        (i in S), M lies in (+)_r e_r (x) P_r, and L/M (2-dim) maps isomorphically onto pi_r(L)/P_r for every r.
        Proof: pi_r^{-1}(P_r) has dim (4 + 1) + 2 = 7; L_a + L_c has dim 5 + 5 - 3 = 7 and all rows of L_a and of L_c lie in the planes
        (pi_b(L_a) = C rho_b inside P_b, pi_i(L_k) = P_i because it is 2-dim and contains pi_i(X_ak) = P_i).   QED
        So N2 has the same shape as the minimal case (a 7-dim level space inside the 10-dim (+) e_r (x) P_r), but with (Q4) only for the
        three 4-sets containing a and b.
 (N2-e) TRIPLE PRODUCTS. LEMMA (I3): a nonzero symmetric zero-diagonal 5x5 matrix B has rank >= 2; if B kills a 3-dim space U, then
        U^perp = span(alpha, beta) with DISJOINTLY supported alpha, beta and B is a multiple of alpha beta^T + beta alpha^T.
        [B = x a a^T + y(a b^T + b a^T) + z b b^T on a basis a,b of U^perp; the zero diagonal says that the binary quadric (x,y,z)
         vanishes at the five points (a_j, b_j); it has two distinct roots since rank B = 2.]
        For {i,k,l} = S:   P_a P_b P_i != 0 and is killed by P_k + P_l   [(Q4) for abik, abil; != 0 by (TV): otherwise P_a = P_b = P_i is
        a coordinate plane and the 3-dim X_kl lives in a 3x2 block];   P_a P_k P_l != 0 is killed by P_b, P_b P_k P_l != 0 by P_a;
        rho_b P_k P_l is killed by P_a + P_i, rho_a P_k P_l by P_b + P_i;   W = P_c P_d P_e != 0 is killed by rho_a, rho_b.
        Hence: whenever P_k != P_l, (P_k + P_l)^perp = span(alpha_i, beta_i) is SPLIT (two-block) and the multiplication
        P_a x P_b x P_i -> A_3 has RANK ONE (image C w_{alpha_i beta_i}); if rho_b is zero-free then rho_b P_k P_l != 0 (Lefschetz), so
        P_a meets every P_i (i in S); if rho_b has exactly 3 nonzero entries then again rho_b P_k P_l != 0 [otherwise P_k, P_l lie in
        the coordinate 3-space of supp(rho_b) and are orthogonal for the NONDEGENERATE form (y,y') -> perm_3[rho_b; y; y']].
 (N2-f) IDENTITY (E1) (ThA for X_ai = Y_kl (+) Y_bk, fully polarised):  T_a T_i . rho_b P_k P_l = 0 and T_b T_i . rho_a P_k P_l = 0 in A_5
        for all t in L^ (perm[t_a; rho_b; t_i; y_k; y_l] = 0). Proof: for x = (mu rho_b; alpha_k v_k; alpha_l v_l), v_k + v_l = mu w, the top
        coefficient is mu h(v_k, mu w - v_k) with h(v,v') := perm[t_a; rho_b; t_i; alpha_k v; alpha_l v']; so h(v,v) = 0 and h(v,w) = 0
        for all v, and an alternating form on the 2-dim V with h(.,w) = 0 vanishes.   QED
        At t = J: the sum of all 3x3 subpermanents of [rho_b; y_k; y_l] vanishes for all y_k in P_k, y_l in P_l.
        Together with (Q4), (Qa), (Qb), (Q5 at J) this gives ALL level conditions of F (they are consequences of the identities):
        the level conditions of the core F do not see the obstruction; it must come from L/M.
 (N2-g) NUMERICAL CLASSIFICATION OF L_a  [numerical; stage3/n2_alg.py, n2_algR.py, n2_an.py].  Unknowns alpha_c, alpha_d, alpha_e (5x2 complex
        matrices), rho = rho_b, w. Equations (all exact polynomial identities, no sampling): P_1, P_2 of L_a; (Q5 at J); (E1 at J); (Qb)
        [they imply that L_a is level]; normalisations alpha_c^* alpha_c = I (gauge GL(V)), |rho| = 1.
          - without further constraints: 26/26 random starts converge to exact solutions (residual 1e-15) which are all DEGENERATE
            (alpha_d, alpha_e of rank <= 1, W = 0);
          - with injectivity of alpha_d, alpha_e and w != 0 enforced (slack variables): 10 random starts (seeds 2-5), 8 exact solutions (residual <= 1e-15), 2 not converged.
            ALL of them have the same shape:   rho_b = e_j (a unit vector),   e_j in P_c cap P_d cap P_e,   P_c, P_d, P_e pairwise distinct
            and concurrent (P_i = span(e_j, q_i), q_i off column j, e.g. q_c = e_2 + a e_3, q_d = e_1 + b e_4, q_e = (x_1, x_2, -a x_2, -b x_1)),
            dim W = 3 (= e_j . span(q_k q_l)), common kernel of all B_w = C rho_b. The preimages alpha_i^{-1}(e_j) are in general NOT
            parallel (so X_ab need not contain a domino), and w is not parallel to them.
        So the necessary conditions on L_a alone are consistent, and the observed solution set is a "rank-one inflation of column j".
        EXACT MODEL (rational arithmetic, stage3/n2_exact_family.py):  Phi := (full free column j = 5) (+) D,
            D := { d_c e_c q_c^T + d_d e_d q_d^T + d_e e_e q_e^T },  q_c = e_2 - e_3, q_d = e_1 - e_4, q_e = e_1 - e_2 - e_3 + e_4,
        is a 7-dim LEVEL space; with P_i = span(e_5, q_i), alpha_i(v) = sigma(v) e_5 + d_i(v) q_i (sigma, d_i independent forms on V),
        rho_a, rho_b in C e_5, every space F of the form (N2-a) is a HYPERPLANE of Phi (column 5 of Phi is free with sum zero; F fixes its entry in row a as lambda rho_a^5, lambda = the w'-coordinate of sum v_i), X_ab, L_a,
        L_b are level, and (Qa), (Qb), (Q5 at J), (E1 at J) hold (g_ik = c_i = 0, dim W = 3). So the core F of an N2 configuration
        is realisable; the model shows what N2 would be: L cap Phi = F, a corank-one piece of "free column (+) D".
        A reduced system (only P_1, (Q5 at J), (Qb), injectivity; n2_algQ.py) has many more solution types (rho with 1, 2, 4 nonzero
        entries): it is the P_2/P_3 part of the level conditions of L_a that forces the unit vector.
        CONJECTURE (N2-unit): in case N2, rho_a and rho_b are multiples of unit vectors lying in P_c cap P_d cap P_e.
        (LM finds generic points of the large components only; other components are not excluded by this experiment. Two probes of
         special positions were INCONCLUSIVE within the time limit (stage3/n2_algS.py): P_c = P_d = P_e: 1 start, not converged
         (residual 2e-2, drifting to a degenerate limit); all three planes in one 3-space: no start finished in 100 s.)
 (N2-h) CONDITIONAL REDUCTION  [rigorous, GIVEN (N2-unit)].  Assume rho_b in C e_j, rho_a in C e_j', e_j, e_j' in P_c cap P_d cap P_e. Then
        (1) j = j'  [otherwise P_c = P_d = P_e = span(e_j, e_j') and Y_cd is a 2-dim level space in a 2x2 block; L101 gives <= 1];
        (2) e_j lies in all five planes P_r, hence kappa^r_j = 0 for ALL rows r: ell does not involve column j;
        (3) L contains a 3-DIMENSIONAL space of single-column elements y e_j^T: with v_i0 := alpha_i^{-1}(e_j) the elements of F with
            v_i = tau_i v_i0 are (lambda rho_a^j, mu rho_b^j, tau_c, tau_d, tau_e) e_j^T subject to the two equations
            sum tau_i v_i0 = mu w + lambda w' in V; so z^j >= 3, and z^j = 3 by Theorem FL;
        (4) consequently for every u in L^ column j of the cofactor matrix, c^j(u) = (perm_4(u^(r,j)))_r, lies in the 2-dim space
            (Z^j)^perp = span(1, eta), and perm(u) = <c^j(u), u^j> = 120 ell(u)^5 with ell independent of column j.
        (5) LINK TO THE DEFECT FORM. b_j in {1,2} (1 is never in pi^j(L); Z^j inside pi^j(L)). L' := L^j (dim 4 + b_j >= 5), read as a
            space of 5x4 matrices, is level, and L contains L' (+) Z^j e_j^T; by rows' defect construction (R1, transposed)
            Z^j lies in (C(L') + C1)^perp, so the defect space C(L') lies in the line C eta (mod 1): e(L') <= 1, and e(L') = 0 is
            impossible for dim L' >= 5 (zeros' Lemma SL: strongly level spaces have dim <= 3). Hence:
               (N2-unit)  ==>  L^j is a TRANSPOSED (4 + b_j, 1) SPACE in rows' sense (a level space of 5x4 matrices with
               one-dimensional defect space), b_j in {1,2}, with
               defect line  eta = ( -zeta(w')/rho_a^j, -zeta(w)/rho_b^j, zeta(a_c), zeta(a_d), zeta(a_e) ) mod 1,
            where a_i := alpha_i^{-1}(e_j) and zeta is any linear form on V independent of sigma (sigma(a_i) = 1).
              b_j = 2:  L = L^j (+) Z^j e_j^T is exactly rows' DEFECT NORMAL FORM with a (6,1) space L^j; excluded by rows' conjecture
                        (DI4) "dim L' - e(L') <= 4" (open in general).
              b_j = 1:  L = (L^j (+) Z^j e_j^T) (+) C t_0, where L^j is a (5,1) space, L^j (+) Z^j e_j^T is an 8-dim level space in defect
                        normal form and column j of t_0 is not in Z^j + C1; excluded if no (5,1) space exists (rows' (DI_5) at e = 1,
                        open; numerically 0/12 in rows' searches), otherwise one needs "an 8-dim defect-form space is maximal".
            verifyfl's Theorem TC5 (dim L' <= 4 if the defect line is of two-line type e_r - e_r' mod 1) excludes both cases when eta is
            of that type, e.g. when a_c = a_d = a_e and zeta(w')/rho_a^j + zeta(w)/rho_b^j = -2 zeta(a_c)  [not forced by what is known].
            (Uses zeros' Lemma SL as stated in NOTES-zeros for e >= 1, and the 3-line computation behind rows' R1:
             L' (+) e_r (x) Z level  <=>  Z inside (C(L') + C1)^perp, by homogeneity in Y of sum_k (4-k)! <z, p_k(Y)>.)
        This is the transposed situation of (S3) in its strongest form (a corank-one partial free column in a space with all a_r = 1).
 (N2-i) SURVEY  [numerical]. No row pair of N2 shape (m_cd = m_ce = m_de >= 2 without single-row elements on c,d,e) occurs in any of
        the 12 known level spaces or their transposes (stage3/survey_n2.py).

## 19. (S3) -- what a single-row element gives, and what is missing  [rigorous remarks only]
 Let all a_r = 1 and e_r w^T in L. (i) (SR): every j in supp(w) has b_j >= 1 with a column annihilator nu^j, sum nu^j = 1, nu^j_r = 0;
 U := {t in L : column j supported at row r} = L^j (+) C e_r w^T and perm_4(t^(r,j)) = 0 on U.
 (ii) cofactor form: for u in L^ the r-th cofactor row c_r(u) = (perm_4(u^(r,j)))_j depends only on the rows != r, is orthogonal to Z_r, and
 perm(u) = <c_r(u), u_r> = 120 <kappa^r, u_r>^5. If z_r = 3 then Z_r = 1^perp cap (kappa^r)^perp, c_r(u) = A(u) 1 + B(u) kappa^r and
 (B - 120 ell^4) ell + A s(u_r) = 0 on L^ (A, B quartics in the rows != r): with s(u_r) = 5 ell - (a linear form vanishing on J) this is the
 identity behind rows' defect normal form with e = 1.
 (iii) DEFECT BOUND (rows' R1 applied to L' = L_r, which is a 5-dim 4x5 level space when a_r = 1): Z_r lies in (C(L_r) + C1)^perp, so
 z_r <= 4 - e(L_r), and e(L_r) >= 1 (SL). So in the regime all a_r = 1 EVERY L_r is a (5, e_r) space with 1 <= e_r <= 4 - z_r; rows'
 (DI_5) (dim L' <= 3 + e) would give e_r >= 2, i.e. z_r <= 2 for every row, and z_r = 3 is exactly the (5,1) problem.
 (iv) NOT DONE: a contradiction from a single-row element with z_r <= 2. (SR) gives for every j in supp(w) a column annihilator vanishing
 at r, but with all a_r = 1 nothing known forces a second independent single-row element or a deletable line.

## 20. STATE AFTER ROUND 4 and the precise remaining list
 PROVED so far (hand proofs, exact/numerical checks, independent verification pending): in a 9-dim level space with all a_r = 1 and
 lam_{rr'} >= 3 for all row pairs, EITHER there is a single-row element, OR case N2 holds; in case N2 the structure (N2-a)-(N2-f).
 REMAINING, in order:
   (T1) PROVE (N2-unit): in case N2, rho_a and rho_b are unit vectors in P_c cap P_d cap P_e. Available: (Qa), (Qb), (Q5), (E1), (Q4) for the
        4-sets containing a,b, the split/rank-one structure (N2-e), the level conditions of L_a. A finite problem about three 2-planes,
        two vectors and two lines of V (37 complex unknowns for L_a alone); an exact elimination / primary decomposition of the system
        of n2_alg.py with alpha_d, alpha_e injective would settle it for L_a (expected answer: only the component found numerically).
   (T2) GIVEN (N2-unit): exclude a 9-dim level space with all a_r = 1, kappa^r_j = 0 for all r and z^j = 3 (N2-h). By (N2-h)(5):
        b_j = 2 is rows' (6,1) problem [(DI4)], b_j = 1 is "(5,1) space plus one more element" [(DI_5) at e = 1 suffices]; in both
        cases the defect line eta is explicit, and only the two-line type is proved (TC5).
   (T3) = (S3): a single-row element e_r w^T in the regime all a_r = 1 (section 19).
   (T4) rows with a_r >= 2 (unchanged, (S2) of section 17), and the transposed statements.
STATUS 17:26: exact model of the L_a/F structure found and checked (free column (+) D); (N2-h)(5): (N2-unit) ==> transposed (5,1) space
 in L^j; RESULT ROUND 4 written at the top.
STATUS 17:31: special-position probes (coincident / coplanar planes) inconclusive; notes final. Final report follows.

# ROUND 5 (start 17:38, budget 75 min -> ends ~18:53)
STATUS 17:41: read UPDATE 8 and the coordinator's targets (T1) = prove (N2-unit), (T3) = (S3).
STATUS 17:50: observation: (N2-e) (split complements) is violated by the generic member of the L_a model of (N2-g), and the unit
 configurations themselves are killed by the triple-product argument of section 12. So the right statement is not (N2-unit) but
 "the plane configuration of N2 does not exist". Plane-configuration search (stage3/n2_planes.py): all solutions live in 3 columns.
STATUS 18:04: THEOREM N2-X (case N2 is impossible) proved by hand (section 21); annihilator dimensions checked exactly (stage3/kcheck.py).

## 21. THEOREM N2-X: CASE N2 DOES NOT OCCUR   [rigorous hand proof, exact checks of the linear algebra; NOT yet independently verified]
 Setting: case N2 of section 16 (9-dim level L, all a_r = 1, no single-row element, lam_ab = 4, all other lam = 3; S = {c,d,e}).
 INPUT (all from sections 16, 18, with their proofs):
   (Q4)  P_a P_b P_k P_l = 0 in A_4 for the three pairs {k,l} of S;      (Qb) rho_b P_c P_d P_e = 0 in A_4;
   (Q5J) the sum of all 3x3 subpermanents vanishes identically on P_c x P_d x P_e;   (P2) the P_2-conditions of X_ab (N2-a);
   (NT)  no three of the five planes are equal to one coordinate plane [X_kl, X_bi, X_ab would be level spaces of dim >= 3 in a 3x2 block];
   (NT') P_k = P_l = a coordinate plane is impossible for k,l in S [Y_kl would be a 2-dim level space in a 2x2 block, L101];
   (M7)  M = sum of all L_r is 7-dim with all rows in the planes (N2-d);   checked upstream L156 (a level space of 5x3 matrices has dim <= 6).
 TOOLS: (TV) three 2-planes with zero triple product are one coordinate plane; (K1) K(P) := {Q in A_2 : Q P = 0} has dim <= 1 for a
   2-plane P; (R1) if P_a P_b is one-dimensional then P_a = P_b = span(e_j,e_l) and P_a P_b = C y_j y_l [(TV)'s proof: every vector of
   P_a has a zero-product partner in P_b]; (Q0) Y Y' = 0 in A_2 (y,y' != 0) iff both lie in one C e_j ("D") or y = p e_j + q e_l,
   y' = c(p e_j - q e_l), pq != 0 ("B") -- hence a 2-plane has NO common nonzero zero-product partner, and three or more nonzero
   pairwise zero-product vectors lie on one coordinate line; (G2) {y : Q y = 0} has dim <= 2 for Q != 0 (in A or in A_N);
   (I3) of (N2-e).  By (TV) + (NT) all triple products of the planes are nonzero.
 STEP 0. P_c, P_d, P_e pairwise meet (section 16). So either (alpha) dim(P_c + P_d + P_e) = 4 and the three planes have a common line
   C v_0, or (beta) they lie in a 3-space (dim of the sum <= 3).
 CASE (alpha). (1) P_a P_b v_0 = 0 in A_3: an element w of it is killed by P_d, P_e (v_0 in P_c, (Q4) for abcd, abce) and by P_c
   (v_0 in P_d), i.e. by a 4-dim space, so B_w has rank <= 1 and w = 0.
   (2) y -> V_0 Y maps P_a into K(P_b), so by (K1) some y_a != 0 in P_a has V_0 Y_a = 0; likewise for P_b. By (Q0): either
       (A1) v_0 = e_j and e_j lies in P_a and P_b, or (A2) v_0 = p e_j + q e_l (pq != 0) and v_0^* := p e_j - q e_l lies in P_a and P_b.
   (A1) All five planes are P_r = C e_j + C q_r, q_r != 0 in C^N (N = the other four columns), q_c, q_d, q_e linearly independent.
       The e_j-part of (Q4) says: every triple product of q_a, q_b, q_k, q_l vanishes in (A_N)_3 (nine triples). If q_a q_b != 0 then
       q_c, q_d, q_e lie in {y : q_a q_b y = 0}, of dim <= 2 (G2): contradiction. So q_a q_b = 0:
       D: q_a, q_b in C e_m. Then e_m q_k q_l = 0, i.e. the restrictions of q_c, q_d, q_e to N - m have pairwise zero products; none of
          them is 0 (else P_k = span(e_j,e_m) = P_a = P_b, against (NT)); so they lie on one line C e_n and q_c, q_d, q_e lie in
          span(e_m,e_n): contradiction.
       B: q_a = p e_m + q e_n, q_b = c(p e_m - q e_n). Then e_m q_k q_l = e_n q_k q_l = 0: the restrictions r_k to N - m and t_k to N - n
          are pairwise zero-product. If some r_k = 0 (q_k = e_m, at most one k) then t_k = e_m forces the other two into
          span(e_m,e_n); if no r_k = 0 they lie on one line C e_z and all q_k lie in span(e_m,e_z). Contradiction with independence.
   (A2) T = {j,l}, N' the other three columns, bars = restrictions to N'. (V_0^*)^2 = -2pq y_j y_l and (Q4) give qbar_k qbar_l = 0 for
       the pairs of S (P_i = C v_0 + C q_i). No qbar_i = 0: all on one line C e_n, the sum is 3-dim. Two zero: P_k = P_l. So exactly
       one, P_c = C^T. (Q4) for abcd with y_c = e_j, y_a = v_0^* gives qbar_b qbar_d = 0; likewise qbar_a qbar_d = qbar_a qbar_e =
       qbar_b qbar_e = 0, and (1) gives qbar_a qbar_b = 0 (coefficients at {j,n,n'}). So qbar_a, qbar_b, qbar_d, qbar_e are pairwise
       zero-product with qbar_d, qbar_e != 0: if qbar_a = qbar_b = 0 then P_a = P_b = P_c = C^T (against (NT)); otherwise at least three
       nonzero ones lie on one line C e_n and P_c + P_d + P_e is inside C^T + C e_n. Contradiction.     So (alpha) is impossible.
 CASE (beta). Put S2 := P_c P_d + P_c P_e + P_d P_e in A_2; (Q4) says P_a P_b lies in K(S2) := {Q : Q S2 = 0 in A_4}.
   (beta-0) P_c = P_d = P_e = P. (Qb) with y_c = y_d = y_e = y: B_{Y^3} rho_b = 0; for zero-free y this matrix is invertible, so a column
       vanishes on P. (Q5J): e_3 = 0 identically on P. Two vanishing columns: e_3 = y_1 y_2 y_3 = 0 on P makes P a coordinate plane
       (NT'). Exactly one (column 5): with y = p + t q, e_3(y) = prod(q) sum_l q_l^{-1} prod_{m != l}(t - t_m) = 0 forces every root
       class to have size 2 and q_l' = -q_l in it: P = span(e_1 - e_2, e_3 - e_4) up to a permutation of columns. Then s = 0 on P and
       (P2) says <alpha_i v, alpha_k v> = 0 for i != k: theta = alpha_d alpha_c^{-1} and theta' = alpha_e alpha_c^{-1} are skew for
       <,>|_P = 2 Id, i.e. multiples of Omega, and then alpha_e alpha_d^{-1} = theta' theta^{-1} is a nonzero multiple of Id, not skew.
       Contradiction.
   In the remaining cases two of the planes differ, V_3 := P_c + P_d + P_e is 3-dim, and for a suitable i the nonzero space P_a P_b P_i is
   killed by V_3; by (I3) V_3 = (alpha,beta)^perp with supports A, B disjoint, type (|A|,|B|) in {(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)},
   and P_a P_b P_i = C w, w := w_{alpha beta}. Notation: h = the vector of C^A orthogonal to alpha (|A| = 2), h^* its conjugate, V_B :=
   beta^perp in C^B, Q_beta := sum_{z in B} beta_z y_{B - z} (|B| = 3), M_u := the 3x3 matrix of the form (l,u') -> perm_3[l;u;u'] on C^B.
   Polarity: the symmetric forms on V_3 vanishing on P_k x P_l are span(l_k^2, l_l^2) (l_k = equation of P_k in V_3). Hence:
   (beta-2) three distinct planes: S2 = V_3 V_3.     (beta-1) P_k = P_l = P != P_i: S2 = P V_3.
   ANNIHILATORS (hand computation; exact rational check stage3/kcheck.py):
     K(V_3 V_3):  (1,1): (A_N')_2, N' = the three columns of V_3;   (1,2): H_B^* . C^C (C = the two free columns);   (1,3): C Q_beta;
                  (1,4): 0;   (2,2): C H^* H'^*;   (2,3): 0.
   (beta-2): (1,4), (2,3): P_a P_b = 0, impossible. (1,3), (2,2): P_a P_b is one-dimensional and not a monomial, against (R1).
       (1,2): products Y_a Y_b in H_B^* C^C have no y_u y_v and no y_x y_x' term and no term in the vanishing column m, so P_a, P_b lie in
       C^B + C^C with pairwise zero products of the restrictions to B and to C. If P_a|_B = C^B then P_b = C^C, P_a = C^B and the
       products y_a y_b are not all in H_B^* C^C; so (by symmetry in B, C and in a, b) all four restrictions are lines: P_a = C th_a + C eta_a,
       P_b = C th_b + C eta_b (th in C^B, eta in C^C); th_a eta_b and eta_a th_b in H_B^* C^C force th_a, th_b parallel to h_B^*, and then
       th_a th_b = c (H_B^*)^2 != 0. Contradiction.
       (1,1): Q in (A_N')_2 for all Q in P_a P_b forces the two other columns to vanish on P_a, P_b (if y_a^m != 0, every y_b is
       proportional to one vector): all five planes lie in three columns, M is a 7-dim level space of 5x3 matrices: against L156.
   (beta-1): for Q in P_a P_b and y in P: Q y lies in P_a P_b P_l = C w. If |A| = 1 (alpha = e_m) then w has no y_m, so writing
       Q = Q_N + y_m l we get l y = 0 for all y in P, hence l = 0 (Q0): K is computed inside (A_N)_2 with the scalar pairing.
     (2,3), V_3 = C h + V_B:  P = V_B: K = C Q_beta.  P = C u_0 + C(h + u_1), u_1 not in C u_0: K = 0.  P = C u_0 + C h: K = H^* Lam(u_0),
        Lam(u) := {l in C^B : M_u l in C beta}, which is one-dimensional (M_u invertible for zero-free u; for u = (beta_v,-beta_u,0) one finds
        Lam = C u^*).  So P_a P_b is 0 or one-dimensional and not a monomial: contradiction with (R1).
     (2,2), V_3 = C h + C h' + C e_5:  e_5 not in P: K = C H^* H'^*.  P = C e_5 + C(x h + x' h'), x x' != 0: K = C H^* H'^*.  Both against (R1).
        P = C e_5 + C h: K = H^* . span(H'^*, y_5); the (1,2)-argument above (blocks A and {3,4,5}) gives th_a th_b = c (H^*)^2 != 0.
     (1,1): as in (beta-2): all planes in three columns, against L156.
     (1,4): S2 = P V_3 is a hyperplane of (A_N)_2 = V_3 V_3, so K is one-dimensional; by (R1) P_a = P_b = C^{jl} and y_j y_l is orthogonal
        to P V_3, i.e. y_u z_v + y_v z_u = 0 for y in P, z in V_3 ({u,v} = N - {j,l}); V_3 restricts onto C^{uv}, so P = C^{jl} = P_a = P_b:
        against (NT).
     (1,3), V_3 = V_B + C e_x:  P = V_B or e_x not in P: S2 = (A_B)_2 + y_x V_B = V_3 V_3, K = C Q_beta, against (R1).
        P = C e_x + C u_0: K = C Q_beta + y_x Lam(u_0), dim Lam(u_0) = 1 = C l_0. Let Pbar_a, Pbar_b be the projections to C^B.
        Both 2-dim: Pbar_a Pbar_b = C Q_beta has rank one, so both are one coordinate plane and Q_beta is a monomial: no.
        Pbar_a 2-dim, P_b = C e_x + C eta_b: e_x y_a in K gives Pbar_a inside Lam(u_0): no.
        P_a = C e_x + C eta_a, P_b = C e_x + C eta_b: eta_a, eta_b in C l_0 and l_0^2 in C Q_beta. Either l_0 is zero-free with l_0 = (1/beta_z)_z;
        then M_{u_0} l_0 = c beta reads t_z := beta_z (u_0)_z = -c prod(beta) for all z, and sum t_z = 0 gives u_0 = 0. Or l_0 = e_z;
        then M_{u_0} e_z (zero at z) in C beta forces M_{u_0} e_z = 0, u_0 in C e_z, beta_z = 0. Contradiction.
     (1,2), V_3 = C h_B + C^C:  P = C^C is a coordinate plane (NT').  Otherwise P V_3 = V_3 V_3 (it contains y_x y_x', H_B y_x, H_B y_x' and
        then y_u y_v), K = H_B^* C^C, and the (1,2)-argument of (beta-2) applies.
   So (beta) is impossible as well.                                                                                               QED
 COROLLARY (THEOREM N). A 9-dim level space with all a_r = 1 and lam_{rr'} >= 3 for all row pairs contains a single-row element.
   (Section 16: no single-row element => case N1 or N2; Theorem N1; Theorem N2-X.)  By transposition: all b_c = 1 and all
   lam^{cc'} >= 3 => a single-column element.
 REMARKS. (i) (N2-unit) of section 18 is SUPERSEDED: the generic member of the L_a model of (N2-g) violates (N2-e) (only one of the
   three complements (P_k + P_l)^perp is split), and the unit configurations fall under (alpha)(A1). Sections (N2-h), (T1), (T2) are
   no longer needed. (ii) Only (Q4) for the 4-sets containing a,b, (NT), (NT'), (M7)+L156 are used outside (beta-0); (Qb), (Q5J), (P2)
   are used only in (beta-0). (iii) Consistency with round 4: for the exact model of (N2-g) (q_c = e_2 - e_3, q_d = e_1 - e_4,
   q_e = e_1 - e_2 - e_3 + e_4) the three spaces {y : q_k q_l y = 0} are span(e_2+e_3, e_1+e_4), span(e_2+e_3, e_1-e_4),
   span(e_1+e_4, e_2-e_3), with intersection 0: no plane P_a = C e_5 + C q_a exists, as (alpha)(A1) predicts. The L_a conditions alone
   were consistent only because they do not involve P_a, P_b.
 NUMERICAL CORROBORATION (plane problem: five planes with (Q4), (Qa), (Qb), all ten triple products of norm >= 0.25):
   stage3/n2_planes.py: 75 exact solutions from 76 starts, ALL with every plane inside one coordinate 3-space; with at most one
   vanishing column required: 0 exact solutions from 6 starts (residual floor 7.5e-3); with P_c = P_d != P_e (n2_planesB1.py): 0 from 8;
   the same inside four columns (n2_planesB1c4.py): 0 from 9. (Few starts; corroboration only.)

## 22. (S3) AFTER THEOREM N: where a single-row element lands   [rigorous remarks; (S3) itself is NOT solved]
 Regime: 9-dim level L, all a_r = 1, (H1) for rows. By Theorem N some z_r >= 1.
 (a) For every row r, L_r is a 5-dim level space of 4x5 matrices and L contains L_r (+) e_r (x) Z_r, so (rows' R1) Z_r lies in
     (C(L_r) + C1)^perp:   z_r <= 4 - e_r,   e_r := dim C(L_r) >= 1 (SL).   So L_r is a (5, e_r) space with
        z_r = 3: (5,1);     z_r = 2: (5,1) or (5,2);     z_r = 1: (5,1), (5,2) or (5,3);     z_r = 0: (5,1), ..., (5,4).
     If (5,1) is excluded (the first of the three pairs of UPDATE 8), then z_r <= 2 for every row and the rows with a single-row
     element land on (5,2) [z_r <= 2] or (5,3) [z_r = 1]. BOTH satisfy (DI_5) (5 <= e + 3): (S3) is NOT a consequence of the defect
     inequality for L_r. No row is deletable (pi_r(L) is 4-dim, z_r <= 3), so L is never in defect normal form in this regime: the
     2 + (2 - z_r) or more dimensions of L outside L_r (+) e_r Z_r must be used.
 (b) (SR): e_r w^T in L, j in supp(w) (at least two such columns since s(w) = 0): column j has an annihilator nu^j with nu^j_r = 0,
     sum nu^j = 1, and perm_4(t^(r,j)) = 0 on L^j (+) C e_r w^T. If all b_c = 1 this says kappa'^j_r = 0 for >= 2 columns: the
     column annihilators have zero entries, which is exactly the case left open by Theorem GEN (stage2's "zero-entry" layer).
 (c) cofactor form (section 19 (ii)) for u in L^: c_r(u) is orthogonal to Z_r.
 (d) LEMMA S3-1 [rigorous]. Under (H1) for rows and all a_r = 1:  z_i <= 5 - lam_{ri} <= 2 for all r != i  (e_i Z_i lies in L_r and
     pi_i(L_r) has dim 5 - lam_{ri}). So z_i = 3 does not occur, and the landing list of (a) becomes
        z_i = 2: (5,1) or (5,2);      z_i = 1: (5,1), (5,2) or (5,3).
     If z_i = 2 (Z := Z_i, R := the other four rows): lam_{ri} = 3 and pi_i(L_r) = Z for all r in R, L_r = X_{ri} (+) e_i Z,
     M := sum of all L_r = L_i (+) e_i Z is 7-dim (a level space in rows' defect normal form with L' = L_i, free part Z), every
     pi_r(L_i) =: P_r (r in R) is a 2-plane, and M lies in (+)_{r in R} e_r (x) P_r (+) e_i (x) Z: the SAME shape as the minimal case
     and N2, with P_i := Z. Zeros' (CA2) gives  Xi_a Xi_b Xi_c Xi_d = 0 on L_i  and  Z . X_b X_c X_d = 0 for x in X_{ri} (rows b,c,d = R - r).
 (e) PLAN for z_i = 2 [NOT carried out; first obstacle identified]. If no row of R carries a single-row element, L_i has exactly the
     structure used in Lemma Q4-gen (5-dim in the 8-dim (+)_R e_r (x) P_r, 3-dim row kernels, m in {1,2} on the pairs of R, the pairs
     with m = 2 disjoint), so (Q4) P_a P_b P_c P_d = 0 holds for the 4-set R [not re-checked line by line]. For the 4-sets containing i
     the available space is L_r = X_{ri} (+) e_i Z, and the restriction of trilinear forms on P_b x P_c x P_d to the 3-dim X_{ri} is
     NOT injective: in the generic normal form x = (al p_bc + be p_bd; al p_cb + ga p_cd; be p_db + ga p_dc) the eight coordinate
     products give only seven monomials (al be ga occurs twice), and if some m = 2 the row projection of X_{ri} is only a line. So one
     gets  Z . mu = 0  for mu in a hyperplane of the products P_b P_c P_d (resp. for a line of P_b): a WEAKENED (Q4), of the same kind as
     (Qa)/(Qb) in case N2. The natural continuation is the argument of section 21 with these weakened conditions (the full (Q4) for R
     plays the role of (Q4) for the 4-sets containing a,b). Also to be checked: (NT) and rows of R with single-row elements.
 NOT DONE: a contradiction or a normal form from (a)-(e); the case where all single-row parts are lines (z <= 1).

## 23. STATE AFTER ROUND 5 and the precise remaining list
 PROVED (hand proofs; sections 12, 14-16 verified by verify2, sections 18 and 21 not yet):
   THEOREM N: all a_r = 1 and lam_{rr'} >= 3 for all row pairs  =>  L (9-dim level) contains a single-row element.
 REMAINING:
   (V)  independent verification of section 21 and of the N2-part of section 16 that it uses ((Q4) for the 4-sets containing a,b in
        case N2; (Qb); pairwise meeting; lam_ab = 5 impossible) and of (N2-c)/(N2-d)/(N2-e).
   (S3) all a_r = 1, a single-row element exists: z_r <= 2 (Lemma S3-1); it lands on (5,2)/(5,3) for L_r (given the exclusion of
        (5,1)) and is not settled by (DI_5). Sub-case z_i = 2: carry out the plan of section 22 (e) ((Q4) for the four other rows, weakened
        (Q4) for the 4-sets containing i, then the case analysis of section 21). Sub-case all z <= 1: open; if all b_c = 1 it is the zero-entry layer of GEN.
   (S2) rows with a_r >= 2 (unchanged), and the transposed statements.
STATUS 18:11: sections 21-23 and RESULT ROUND 5 written; proof of N2-X re-read step by step ((R-a)..(R-l) of my checklist), (K1)/(G2)
 re-tested exactly (stage3/k1check.py). (S3) not solved. Final report follows.
STATUS 18:14: Lemma S3-1 (z_i <= 2 under (H1); structure for z_i = 2) and the plan for z_i = 2 added to section 22.
STATUS 18:16: plan for z_i = 2 corrected (the restriction to X_{ri} is not injective: only a weakened (Q4)). Final report follows.

# ROUND 6 (start 18:20, budget 90 min -> ends ~19:50)
STATUS 18:22: read verifyfl's Theorems SPLIT / FS / TS, rows' R1 / H1 / DI_3 / DDI, stage2's first-order test T_1 (R4-6).
STATUS 18:24: T_1 test on rows' defect-form 7-dim spaces: dim T_1 = 8 for all ten (4,1) and all three (5,2) examples (stage3/t1_defect.py).
STATUS 18:33: plane problem for z_e = 1 ("four planes and a line") HAS solutions, all with a vanishing column; two types (section 24 (E)).
STATUS 18:41: weakened plane problem for z_e = 2: my search script is too slow (6.6 ms per evaluation, 148 unknowns): no result.

## 24. ROUND 6: (S3) -- what the split theorems give, the generalised defect form, the cases z_e = 2 and z_e = 1, and a_r >= 2
 Regime unless said otherwise: 9-dim level L, all a_r = 1, lam_{rr'} >= 3 (so z_r <= 2 by Lemma S3-1, and some z_r >= 1 by Theorem N).
 (A) LEMMA S3-2 (defect bookkeeping) [rigorous; uses rows' R1/(H1), zeros' SL, verifyfl's SPLIT and FS, the checked L_gct_215].
   For any 9-dim level L and any row r, L_r is a level space of 4x5 matrices of dim 4 + a_r, e_r := dim C(L_r). Then
   (a) a_r <= 3 (L_gct_215: dim L_r <= 7);  e_r >= 1 (SL);  z_r <= 4 - e_r (R1)  and  z_r <= 5 - a_r.
   (b) Z_i lies in C(L_r) for every r != i  [(H1): e_i w^T is in L_r and p_1(e_i w^T) = -w].  Hence
         sum_{i != r} Z_i  inside  C(L_r)  inside  (Z_r + C1)^perp :
       single-row parts of different rows are mutually orthogonal (also directly from P_2), and e_r >= dim sum_{i != r} Z_i.
   (c) [SPLIT] if e_i w^T is in L and <w,w> != 0, then e_r >= 2 for EVERY r != i (e_r = 1 would make L_r a space with defect line C w
       containing e_i w^T, of dimension 4 + a_r >= 5 > 4).
   (d) [FS] if z_i = 2, <,> is nondegenerate on Z_i and e_r = 2 for some r != i, then C(L_r) = Z_i is carried by row i, and FS gives
       dim L_r <= 5 with equality: L_r cap ker(column sums) is a 3-dim strongly level space and the column sums of L_r fill Z_i.
       No contradiction (5 <= e_r + 3).
   (e) WHEN IS L_r SPLIT? L_r is split in verifyfl's sense (defect LINE C m and some e_i m^T in L_r) iff e_r = 1 and some Z_i != 0, i != r;
       then all single-row elements outside row r are multiples of m, and by (c) m is isotropic. So the split theorems kill exactly
       the configurations with e_r = 1; but e_r = 1 is forced only by z_r = 3, which Lemma S3-1 excludes. Under (H1) nothing known
       bounds e_r from above except e_r <= 4 - z_r. LANDING PAIRS (dim L_r, e_r) for all a_r, assuming (5,1), (6,2), (7,3) excluded
       [then e_r >= a_r + 1]:   a_r = 1: (5,2) [z_r <= 2], (5,3) [z_r <= 1], (5,4) [z_r = 0];   a_r = 2: (6,3) [z_r <= 1], (6,4) [z_r = 0];
       a_r = 3: (7,4) [z_r = 0].  All of them satisfy (DI_5): a single L_r never contradicts the defect inequality; only a deletable
       row does (z_r = 5 - a_r <= 4 - e_r <= 3 - a_r is impossible), and with all a_r = 1 no row is deletable (z_r <= 2 < 4).
 (B) LEMMA S3-3 (generalised defect form of a row with single-row elements) [rigorous]. Let Z := Z_e != 0, R := the other rows,
   U0 := pi_R(L) (dim 9 - z_e). There is a linear map theta: U0 -> C^5/Z with L = {(Y; y_e) : Y in U0, y_e in theta(Y)}, L_e = ker theta. And
   (a) perm(u with row e replaced by z) = 0 for all u in L^, z in Z; i.e. the permanent vanishes identically on the 10-dim linear
       space pi_R(L^) (+) e_e (x) Z, and p_k(Y) lies in Z^perp for all Y in U0, k = 1..4;
   (b) for r in R (a_r = 1): (CA2) on L_r applied to xi + e_e z^T gives   (CZ)  Z . Xi_k Xi_l Xi_m = 0 in A_4 for all xi in L_r ({k,l,m} = R - r).
 (C) THE CASE z_e = 2 [rigorous structure; NOT settled]. Lemma S3-1: lam_{re} = 3, L_r = X_{re} (+) e_e Z, M = L_e (+) e_e Z (7-dim core,
   = {t in L : t_r in P_r} for every r, P_r := pi_r(L_e) for r in R, P_e := Z), L/M 2-dim.
   (C1) (Q4) for R. If z_r = 0 for r in R, then P_a P_b P_c P_d = 0 in A_4. Reason: the proof of Lemma Q4-gen (section 16) uses only
        (CA2) on L_e and the incidence data of the 5-dim space L_e inside the 8-dim (+)_R e_r (x) P_r, all of which hold here: row
        kernels X_{re} of dim 3; two-row parts Y_kl = X_{rr'e} of dim m_kl in {1,2} (m_kl <= dim pi_k(X_{re}) <= 2; >= 1 because
        lam_{rr'} = 2 + m_kl >= 3); the pairs with m = 2 are disjoint (Y_kl (+) Y_km lies in the 3-dim X_{r'e}); no single-row element in
        L_e (used in Q4-coll). [Checked against the text of sections 11, 14, 16; the three normal forms are those verified by verify2.]
   (C2) weakened (Q4) for the 4-sets containing e: W_r := span{X_k X_l X_m : x in X_{re}} (in A_3) is killed by Z + P_r
        [B_w Z = 0 is (CZ); B_w P_r = 0 is the s^3-coefficient of (CA2) on L_e at xi' + s x]. So if W_r != 0 then Z meets P_r, and if
        moreover Z != P_r then (Z + P_r)^perp is split and W_r is one-dimensional (Lemma I3). In the non-triangle normal form
        x = al x^{kl} + be x^{km} + ga x^{lm} the six products p_kl p_lk p_mk, ... and the SUM of the two cyclic products
        p_kl p_lm p_mk + p_km p_lk p_ml span W_r; the full (Q4) would need the two cyclic products separately.
   (C3) If the full (Q4) held for all five 4-sets of (P_a, P_b, P_c, P_d, Z), the plane lemma (sections 12, 15) would exclude z_e = 2:
        (NT) holds for these five planes (three equal to one coordinate plane put X_{re} or X_{rr'} into a 3x2 block), two vanishing
        columns contradict L156 (M is 7-dim). So z_e = 2 is reduced to ONE missing identity per 4-set containing e:
              Z . p_kl p_lm p_mk = 0   (a cyclic product; equivalently Z . p_km p_lk p_ml = 0).
        I found no source for it: (I-3) = (B)(a) polarised over L_e and the identities for X_{lm} only reproduce B_w Z = 0.
   (C4) e(L_e) is 1 or 2. If e(L_e) = 2 then M = L(L_e) is exactly rows' defect construction on a (5,2) space; if e(L_e) = 1 then L_e is
        a (5,1) space. The column sums of L_e lie in C(L_e), so L_e has a column-centred subspace of dim >= 3.
 (D) THE CASE z_e = 1, GENERIC SUB-CASE [rigorous reduction to a plane problem; NOT settled].
   LEMMA S3-4. Let Z_e = C w, fix r in R, {k,l,m} = R - r, and assume lam_{rk} = lam_{rl} = lam_{rm} = 3 and that L has no 2-row element
   on the rows (i,e), i in {k,l,m}, other than e_e w^T. Then Lam_r := pi_klm(L_r) is 4-dim and V-twisted,
        Lam_r = {(alpha_k v_k, alpha_l v_l, alpha_m v_m) : v_k + v_l + v_m = 0}   (alpha_i: V -> pi_i(L_r) isomorphisms, V = C^2),
   and   w . pi_k(L_r) pi_l(L_r) pi_m(L_r) = 0 in A_4.
   Proof. L_r cap {rows k,l,m = 0} = C e_e w^T, so dim Lam_r = 4; pi_i(L_r) has dim 5 - lam_{ri} = 2; Lam_r is the kernel of a surjection
   H = (H_k, H_l, H_m) of the 6-dim sum onto C^2, and ker H_k = pi_klm(X_{rlm}) = pi_klm(C e_e w^T) = 0, so every H_i is invertible:
   alpha_i := H_i^{-1}. (CZ) says that the trilinear map W Y_k Y_l Y_m vanishes on the diagonal of Lam_r, hence identically (the
   injectivity lemma of (N2-c)).   QED
   If all lam = 3, z_r = 0 on R and no proper 2-row element involves row e, then the planes are well defined (pi_k(L_r) = pi_k(L_e) =: P_k
   for all r in R - k: both contain the 2-dim pi_k(X_{rr'}) resp. pi_k(X_{re}) for a pair with m = 1), (Q4) holds for R as in (C1), and
        (Q4-line)   w . P_k P_l P_m = 0 in A_4 for all four triples of R,     s(w) = 0,   all four triple products P_k P_l P_m != 0.
 (E) THE PLANE PROBLEM "FOUR PLANES AND A LINE" [numerical; stage3/s3_planes_line.py, s3_an.py]: four 2-planes with (Q4) and a vector w
   with (Q4-line), all four triple products of norm >= 0.25.
     - all five columns nonzero on the planes: 0 exact solutions from 38 starts (residual floor 5.6e-2);
     - one vanishing column allowed: 46 exact solutions from 51 starts, ALL with a column vanishing on the four planes, of two types:
         type II (11): w = e_j, e_j in all four planes (pairwise distinct, sum 4-dim)  -- impossible for us since s(w) = 0;
         type I (35): two of the planes are EQUAL to one coordinate plane C^T, w is a 2-sparse vector of C^T (so w = e_j - e_l after
                      s(w) = 0), the two other planes meet C^T and do not meet each other.
   CONJECTURE (S3-line): in the generic sub-case of (D), P_k = P_l = C^{j,l} for one pair of rows, w = e_j - e_l (up to scale), and a
   column vanishes on P_a, ..., P_d. [Not excluded by (NT): then m_kl = 1 and pi_e(X_{rr'}) = span(w, p) with p outside C^T, otherwise
   X_{rr'} would be a 3-dim level space in a 3x2 block.] So, unlike N2, the plane identities alone do NOT exclude z_e = 1; the level
   conditions of the 3-row spaces X_{rr'} on the rows k, l, e have to be used.   [NOW PROVED: the conjecture is Theorem PL4 in (J) (with the
   additional three-column outcome, which the search excluded by its column condition); type I is excluded by (H), three columns by (K).]
 (F) FIRST-ORDER TEST [numerical; stage3/t1_defect.py, core_check.py]. For M = L' (+) e_5 (x) (C(L') + C1)^perp built from rows' data:
   dim T_1(M) = 8 for all ten (4,1) examples and all three (5,2) examples (one (6,3) example gives 9 with a marginal gap 7e-8, two give 8).
   So none of the known defect-form 7-dim spaces lies in a 9-dim level space. Structure of the test for M = L' (+) e_e (x) W:
       T_1(M) = { (t_R, t_e) : C'(Y)[t_R] in C(L') + C1  and  <t_e, C(Y)> = -<1, C'(Y)[t_R]>  for all Y in L' }
   (C(Y) = cofactor vector, C' its derivative): t_R must preserve the defect space to first order. None of the three (5,2)-based
   spaces is a valid core for (C): (CA2) fails on at least two of their row kernels (the (4,1) examples s7, s8 satisfy (CA2) on all
   five row kernels, but they have z_e = 3).
 (G) WHAT CHANGES WHEN SOME a_r >= 2 [rigorous remarks].
   (i) a_r <= 3 and b_c <= 3 in any 9-dim level space ((A)(a)); a_r = 3 makes L_r an extremal 7-dim 4x5 level space, of type (7,4) if the
       three pairs of UPDATE 8 are excluded.
   (ii) (CA2) weakens: for xi in L_e the vector G(xi) of 4x4 subpermanents lies in pi_e(L^)^perp, of dim a_e - 1 (it is 0 only for
        a_e = 1). So every (Q4)-type identity holds only modulo an (a_e - 1)-dim space, and the plane lemmas need a new input there.
   (iii) dim L_r = 4 + a_r, lam_{rr'} >= a_r + a_r' - 1 is automatic, and the pigeonhole needs lam_{rr'} >= a_r + a_r' + 1 to produce
        2-row elements (section 1); (H1) lam >= 3 is not enough for three rows with a = 2.
   (iv) Lemma S3-1 generalises: z_i <= dim pi_i(L_r) = 4 + a_r - lam_{ri}; the row planes become spaces of dim 4 + a_r - lam.
   (v) rows with a_r >= 2 are where deletable rows live: row r is deletable iff z_r = 5 - a_r, and then (DI4) applies to L_r.

 (H) LEMMA S3-5 (the candidate configuration of (E), type I, is impossible) [rigorous; level conditions only].
   Let e_e w^T be in L, z_e = 1, and let {k,l}, {r,r'} be complementary pairs of R with lam_{rr'} = 3. If the rows k and l of every element
   of X_{rr'} lie in one coordinate plane C^T, T = {j,l'} (e.g. P_k = P_l = C^T), then w is NOT in C^T.
   Proof. Suppose w in C^T; s(w) = 0 gives w = w_j (e_j - e_l'). X_{rr'} (rows k,l,e) contains e_e w^T and Y_kl, which is a level space in
   a 2x2 block, so m_kl = 1 (>= lam_{re} - 2 >= 1, <= 1 by L101), pi_e(X_{rr'}) = span(w,p) is 2-dim and
   X_{rr'} = C y (+) C e_e w^T (+) C x_3,  x_3 = (x_k; x_l; p). Write pi(.) for the 2x2 permanent of the rows k,l (a quadratic form with
   polar form pi(.,.)), gam(.) := (row k) + (row l) in C^T. For u = a y + b e_e w^T + c x_3:
      P_2(u) = pi(a y + c x) + c^2 s(gam_x) s(p) - <a gam_y + c gam_x, b w + c p>,     P_3(u) = c s'(p) pi(a y + c x),   s'(p) := sum_{n not in T} p_n.
   ab: <gam_y, w> = 0 and s(gam_y) = 0, so gam_y = 0; a^2: pi(y) = 0; hence y is a domino, y = (e_k - e_l) e_j^T (or column l', symmetric).
   ac: pi(y,x) = 0, i.e. x_{kl'} = x_{ll'};  bc: <gam_x, w> = 0, i.e. gam_x = h (e_j + e_l'). Subtracting a multiple of y:
   x_k = x_l = (h/2)(e_j + e_l'), pi(x) = h^2/2. P_1: s(p) = -2h. If h = 0 then x_3 = e_e p^T is a second single-row element: z_e >= 2.
   So h != 0; c^2: h^2/2 - 4h^2 - h(p_j + p_l') = 0 gives p_j + p_l' = -(7/2) h, hence s'(p) = (3/2) h != 0, and then
   P_3 = c^3 s'(p) pi(x) = (3/4) h^3 c^3 != 0. Contradiction.   QED
 (I) TOWARDS THE PLANE LEMMA (PL4) "four planes and a line" [rigorous partial results]. Hypotheses: (Q4) for R, (Q4-line), all
   four triple products nonzero, s(w) = 0 (so w is not a unit vector).
   (PL4-1) For complementary pairs {k,l}, {m,r}: w P_k P_l (in A_3) is killed by P_m + P_r. Hence if P_m and P_r do NOT meet, then
        w P_k P_l = 0, the map y -> W Y sends P_k into K(P_l) (dim <= 1), so w y_k = 0 for some y_k != 0: w = e_j - e_l' is 2-sparse and
        w^* := e_j + e_l' lies in P_k and in P_l. Writing P_i = C w^* + C(tau_i w + qbar_i) (qbar_i in the other three columns):
        qbar_k qbar_l = 0 and tau_k qbar_l + tau_l qbar_k = 0, which leaves exactly three shapes:
          (I)  P_k = P_l = C^{j,l'}  [type I; impossible by Lemma S3-5];
          (D)  P_k = span(w^*, th w + e_n), P_l = span(w^*, -th w + e_n);       (B)  P_k = span(w^*, q), P_l = span(w^*, q^*), q 2-sparse.
   (PL4-2) If all six pairs meet and the planes are concurrent at v_0 = e_j: writing P_r = C e_j + C q_r and w = x e_j + wbar, ALL TEN
        triple products of q_a, q_b, q_c, q_d, wbar vanish in (A_N)_3 (the four of the q's by (Q4), the six with wbar by (Q4-line));
        by the sub-lemmas of sections 12 and 15 either three of these five vectors are multiples of one unit vector e_n, or all five
        lie in two columns. Three q's: against (NT). Two q's and wbar: P_k = P_l = span(e_j,e_n) containing w: impossible by Lemma S3-5.
        All in two columns: the four planes lie in three columns (then L_e is a 5-dim level space of 4x3 matrices, the extremal
        case of L156 -- not excluded here).
   [(PL4) is now PROVED in full: see (J).]
 (J) THEOREM PL4 (four planes and a line) [rigorous hand proof; NOT yet independently verified; consistent with the search (E)].
   Let P_a, P_b, P_c, P_d be 2-planes of C^5 and w != 0 NOT a multiple of a unit vector, with
        (Q4) P_a P_b P_c P_d = 0 in A_4,   (QL) w P_k P_l P_m = 0 in A_4 for the four triples,   (NZ) all four K_r := P_k P_l P_m != 0.
   Then EITHER (type I) two of the planes are equal to one coordinate plane C^T and w lies in C^T,
        OR (3col) the four planes and w lie in one coordinate 3-space.
   Tools: (TV), (K1), (R1), (Q0), (G2), (I3) as in section 21; the annihilator table K(V_3 V_3) of section 21; and
   LEMMA 5V (extracted from the proofs of sections 12 (alpha, v_0 = e_j) and 15 (b-alpha), read without (NT)/(NZ)): five nonzero vectors
   of C^N, |N| = 4, with all ten triple products zero in (A_N)_3: three of them are multiples of one unit vector, or all five lie in a
   coordinate 2-plane.  [k = 4: patterns (4), (3,1) give three equal unit vectors, the others are impossible; k = 3: a fourth-column
   entry gives four vectors on C e_4, otherwise three columns; k <= 2: loops/edges; in three columns the same analysis.]
   Proof. PART 1: some pair does not meet, P_m cap P_r = 0. By (PL4-1) w = p e_j + q e_l' is 2-sparse, w^* lies in P_k and P_l, and
     (P_k, P_l) has shape (I), (D) or (B). Put Q' := Y_m Y_r.
     (D) S_kl := P_k P_l = span(y_T, W^* y_n). (Q4): y_T Q' = 0 kills the coefficients of Q' on the pairs inside N'; W^* y_n Q' = 0 gives
         p Q'[l'v] - q Q'[jv] = 0 for the two v in N' - n; (QL) for (k,m,r): W y_n Q' = 0 gives p Q'[l'v] + q Q'[jv] = 0. So Q' has no term
         in the two columns v, hence these columns vanish on P_m and P_r: two 2-planes in the 3-space C^{j,l',n} meet. Contradiction.
     (B) S_kl contains y_T, W^* y_n, W^* y_n'; (QL) for (k,m,r), (l,m,r) gives W y_n Q' = W y_n' Q' = 0. As in (D): Q' is a multiple of
         y_T, so the three columns of N' vanish on P_m, P_r: P_m = P_r = C^T. Contradiction.
     (I) is type I.
   PART 2: all six pairs meet, so the planes are concurrent or coplanar.
     (2B) concurrent at v_0, not coplanar. If v_0 = e_j: (PL4-2) and Lemma 5V: three q's on one line C e_n contradict (NZ); two q's and
          wbar: type I; all in two columns: (3col). If |supp v_0| >= 2: V_0^2 != 0 and (Q4) gives V_0^2 P_k P_l = 0 for all pairs, so
          V_0^2 Y_k is killed by sum_{l != k} P_l. If all these sums were >= 4-dim, all planes would lie in {y : V_0^2 y = 0} (dim <= 2).
          So three planes are coplanar (say b,c,d in V_3', q_a outside); two of them must coincide, P_c = P_d =: P != P_b, and
          P = {y : V_0^2 y = 0}; then V_0^3 = 0, |supp v_0| = 2, P = C^T. (QL): w y_T Y = 0 for y in P_a, P_b, i.e. wbar qbar_a = wbar qbar_b = 0
          (restrictions to N'; qbar_a, qbar_b != 0). wbar = 0: type I. wbar != 0: qbar_a, qbar_b are parallel and P_a lies in V_3'. Contradiction.
     (2A) coplanar, V_3 := the 3-space containing the planes (if all four are equal to P: P^4 = 0 puts P into three columns, and
          K_r = P^3 != 0 puts w there: (3col)).
       (i) w not in V_3. For distinct P_m, P_r and y spanning their intersection, P_k P_l y is killed by P_m + P_r + C w (4-dim), so it
           vanishes: y = e_n lies in P_k and P_l, or y is 2-sparse and y^* lies in P_k and P_l. y = e_n: all planes contain e_n, and
           (PL4-2)/Lemma 5V give type I or (3col), both with w in V_3. y 2-sparse: V_3 = C^T + C g, g in C^{N'}. If no plane equals C^T, the
           intersection vector t + c g of P_k and P_m (c != 0) must again be a unit vector or 2-sparse with its conjugate in V_3: this
           forces g = e_n (V_3 a coordinate 3-space, so K_r != 0 puts w into V_3) or g^* in C g. If P_m = C^T: (Q4) with y_m = e_j, y_k = y^*
           gives c_l G^2 = 0 = c_k G^2 (P_i = C y^* + C(t_i + c_i g)); G^2 != 0 makes P_k = P_l = P_m = C^T, against (NZ); G^2 = 0 makes g a
           unit vector. Contradiction in all cases.
       (ii) w in V_3. R_w := {r : w in P_r}. If w lies in all four planes: W^4 = 0; |supp w| = 3: W^3 P_k = 0 gives (3col); |supp w| = 2:
           W^2 P_k P_l = 0 makes the restrictions qbar_k pairwise zero-product: two planes equal to C^T (type I; three contradict (NZ))
           or at least three qbar's on one line C e_n: (3col). Otherwise some r_0 is outside R_w, K_{r_0} is killed by V_3 = P_{r_0} + C w,
           V_3 is split (I3); type (1,1) is (3col); assume another type. If a complementary pair {m,r} has m, r outside R_w and
           P_m != P_r, then S_kl V_3 V_3 = 0 and the annihilator table gives a contradiction exactly as in section 21 (beta-2). This
           settles |R_w| = 0 and leaves: |R_w| = 1 with P_b = P_c = P_d = P [B_{Y^3} P_a = 0 for y in P: zero-free y impossible; two
           vanishing columns: (3col); one vanishing column: the column-class argument gives P_a = span(alpha^*, beta^*) or the
           (3,1)-space, both disjoint from P, but coplanar planes meet]; |R_w| = 2 with P_c = P_d = P [W^3 P = 0 and W^2 P P = 0:
           |supp w| = 5 impossible, = 4: P would be an isotropic plane of a nondegenerate 3-space, = 3 or 2: (3col)]; |R_w| = 3
           [W^4 = 0, W^3 P_d = 0: |supp w| = 3 gives (3col); |supp w| = 2: the restrictions of q_r in P_r cap P_d have square zero
           and kill Pbar_d: (3col), or P_a = P_b = P_c = C^T against (NZ)].                                             QED
 (K) THEOREM S3-G (the generic single-row case is impossible) [rigorous given (J), sections 16, 21 tools, checked L157 and L101].
   Let L be a 9-dim level space with all a_r = 1 and ALL lam_{rr'} = 3, with exactly one row e carrying single-row elements, Z_e = C w,
   and such that every 2-row element on the rows (i,e) is a multiple of e_e w^T. Then a contradiction arises; i.e. such L does not exist.
   Proof. By (D): the planes P_k (k in R) are well defined, (Q4) holds for R, (QL) holds (Lemma S3-4), s(w) = 0, and (NZ) holds
   (P_k P_l P_m = 0 would put the 3-dim X_{re} into a 3x2 block). By Theorem PL4:
     type I: P_k = P_l = C^T containing w -- impossible by Lemma S3-5 (lam_{rr'} = 3, z_e = 1).
     (3col): L_e is supported in three columns N_3 and w lies in C^{N_3}. The column sums gam(Y), Y in L_e, lie in C(L_e), which is inside
       C^{N_3} cap 1^perp cap w^perp; <,> is nondegenerate on the 2-dim space C^{N_3} cap 1^perp, which contains w, so gam(L_e) is at most a
       line and K := L_e cap ker(gam) has dim >= 4. The transposes of the elements of K form a level space of 3 x 4 matrices (rows = the
       columns of N_3) with all three row sums zero: the checked L157 gives dim K <= 4 - 1 = 3. Contradiction.     QED
   Exact check of the computation in Lemma S3-5: stage3/s35_check.py (200 random rational points).
   NUMERICAL CORROBORATION of Theorem PL4 (stage3/s3_planes_lineW.py: w kept away from unit vectors, up to two vanishing columns
   allowed): 52 exact solutions from 55 starts; 48 are (3col), 4 are type I; no other type.
 (L) EXTENSION S3-G' [rigorous, same proof; the injectivity statements are hand computations]. Theorem S3-G remains true if ONE row
   i_0 of R carries a proper 2-row element through e with m_{i_0 e} = 2 (pattern (m_ae, m_be, m_ce, m_de) = (2,1,1,1) up to order).
   (1) In Lemma S3-4, Lam_r = ker H with H_i injective iff m_ie = 1; if m_ie = 2 then H_i has rank one. The restriction of trilinear
       forms to Lam_r is injective as long as no H_i vanishes: one rank-one H_k (H_k y_k = h(y_k) u): Lam_r = {(y_k, alpha_l v,
       alpha_m(-v - h(y_k) u))} and the coefficients of s^2 v^a, s t v^a, y^i v^a v^b force T = 0; two rank-one maps have different image
       lines (otherwise pi_m(Lam_r) would be a line) and T(.,.,alpha_m u_k) = T(.,.,alpha_m u_l) = 0 force T = 0; three rank-one maps have
       pairwise different image lines and the eight coordinate products are eight different monomials. So (QL) holds for every triple
       whenever all m_ie <= 2. [For m_ie = 3, H_i = 0 and the restriction is not injective.]
   (2) The planes are well defined for the pattern (2,1,1,1): pi_k(L_r) = pi_k(L_r') whenever the fourth row m of R has m_me = 1
       (pi_k(X_{rr'}) is 2-dim), and every 3-set R - k contains at most one row with m = 2, so the three planes pi_k(L_r) are linked;
       pi_k(L_e) is linked through X_{re} as before. More generally pi_k(L_r) = pi_k(L_e) whenever the pair R - {r,k} has m = 1 (both
       contain the 2-dim pi_k(X_{re})); so the planes are well defined for ANY pattern with all m_ie <= 2 as soon as all six pairs of R
       have m_kl = 1. If some pair of R has m = 2 and two or more rows have m_ie = 2, the identification is NOT proved.
   (3) (Q4) for R, (NZ), Lemma S3-5 and the L157 step do not involve the m_ie.

## 25. STATE AFTER ROUND 6 and the precise remaining list
 PROVED in round 6 (rigorous): Lemma S3-2 (defect bookkeeping, incl. e_r >= 2 for r != i when a non-isotropic e_i w^T exists), Lemma S3-3
 (generalised defect form, (CZ)), the structure (C1)-(C4) for z_e = 2, Lemma S3-4 and the reduction (D) for z_e = 1, remarks (G).
 ALSO PROVED: Theorem PL4 (four planes and a line) and Theorem S3-G (the generic case "one row with z = 1, all lam = 3, no proper
 2-row element through that row" is impossible).
 NOT PROVED: (S3) in general. Precisely:
   (S3-a) z_e = 2: the missing cyclic identity of (C3) (then the plane lemma finishes), or a direct treatment of the weakened problem
          (four planes with full (Q4), Z killing a hyperplane of each triple product); the sub-cases with single-row elements in other
          rows and with triangle normal forms are not written.
   (S3-b) z_e = 1, generic sub-case: SETTLED (Theorem S3-G, section 24 (K)): Theorem PL4 + Lemma S3-5 + the checked L157.
          To be verified independently: (J), (K), Lemma S3-4, Lemma S3-5 and the use of Lemma Q4-gen on L_e.
   (S3-c) z_e = 1 with lam = 4 somewhere; z_e = 1 with two or more rows i having m_ie = 2 [(QL) still holds, the identification of the
          planes is missing] or with some m_ie = 3 [(QL) weakened]; several rows with single-row elements (all z <= 1): not analysed.
   (S3-d) the split theorems apply only if some e_r = 1; an upper bound e_r <= 1 in some configuration would finish it there.
   (S2)   rows with a_r >= 2 ((G)); transposed statements.   (V) verification of sections 21 and 24.
STATUS 18:47: Lemma S3-5 (type I excluded by level conditions) and the partial plane lemma (PL4-1), (PL4-2) added.
STATUS 18:55: THEOREM PL4 proved in full (section 24 (J)); the three-column case is killed by the checked L157; THEOREM S3-G written (K).
STATUS 18:57: Lemma S3-5 computation checked exactly (s35_check.py); remark on the first relaxation of Lemma S3-4 added. Final report follows.
STATUS 19:00: PL4 corroborated numerically (48 three-column + 4 type-I solutions of 52); extension S3-G' (pattern (2,1,1,1)) added. Final report.
STATUS 19:03: remark on further patterns added to (L). Final report follows.

# ROUND 7 (start 19:07, budget 90 min -> ends ~20:37)
STATUS 19:12: read stage2's FO2 (R5-5), rows' FL2* (R3.9) and SL_3, reg2's first-order criterion.
STATUS 19:20: results so far: (i) pattern m_ie = 3 is impossible by counting, the planes are always well defined and (QL) needs only
 m_ie <= 2, so Theorem S3-G holds for ALL configurations with z = (1,0,0,0,0) and all lam = 3; (ii) for z = (1,0,0,0,0) the lam-patterns
 are F1 (all 3), F3 (lam_ae = 4), F4a (lam_ab = 4), F4b (lam_ab = lam_cd = 4); F3 and F4a fall to the proof of N2-X; (iii) two rows with
 z = 2 contradict rows' FL2* unless both single-row planes are degenerate. Section 26.

## 26. ROUND 7: one single-row direction (z = (1,0,0,0,0)), two 2-dim single-row parts, the structure of (S3-a), and what is left
 Regime: 9-dim level L, all a_r = 1, all lam_{rr'} >= 3. Y_jk := 2-row elements on the rows j,k (single-row elements included),
 m_jk := dim Y_jk. COUNTING TOOLS (pure linear algebra, valid with single-row elements):
   (c1) lam_{rr'} >= sum_{i not in {r,r'}} z_i;          (c2) z_i <= 5 - lam_{ri};
   (c3) m_jk - z_j <= dim pi_k(L_r) = 5 - lam_{rk}  for r outside {j,k}  [pi_k is injective on Y_jk / e_j Z_j];
   (c4) m_jk + m_jl - z_j <= lam_{mn}  ({m,n} the two other rows);       (c5) m_jk >= lam_{lm} + lam_{ln} - 5  ({l,m,n} the other rows).
 (A) z = (1,0,0,0,0): Z_e = C w, R the other rows.
   (A1) m_ie <= 2 for i in R  [(c3) with (j,k) = (i,e): m_ie <= 5 - lam_{re} <= 2]. So the pattern "m_ie = 3" of round 6 does not exist.
   (A2) LAM-PATTERNS. lam <= 4 (lam_{rr'} = 5 with r,r' in R would force a single-row element in a third row; lam_{re} <= 4 by (c2)).
        If lam_{ae} = 4 (a in R): (c5) gives m_bc, m_bd, m_cd >= 2 and (c3) makes all other lam equal to 3.   [family F3]
        If lam_{ab} = 4 (a,b in R; {c,d} = R - {a,b}): m_cd, m_ce, m_de >= 2, all other lam are 3 except possibly lam_cd. [F4a: lam_cd = 3;
        F4b: lam_cd = 4.]    Otherwise all lam = 3 [F1].
   (A3) F1 IS IMPOSSIBLE (Theorem S3-G for all of F1). Two additions to section 24 (K), (L):
        - the planes are always well defined: for k in R, on the four rows != k join r, r' when pi_k(X_{rr'}) is 2-dim, i.e. when the
          2-row space of the two remaining rows has m = 1. By (c4) a row j of R cannot have m_je = 2 and m_jl = 2 together, and two pairs
          of R with m = 2 are disjoint; a short check of the possible patterns shows that this graph is connected.
        - (QL) w . P_k P_l P_m = 0 holds for every triple as soon as all m_ie <= 2 (section 24 (L)(1)), which is (A1).
        Then (Q4) for R (Lemma Q4-gen on L_e), Theorem PL4, Lemma S3-5 and the checked L157 apply as in section 24 (K).
   (A4) F3 AND F4a ARE IMPOSSIBLE: the proof of Theorem N2-X (section 21) applies to the pair with lam = 4. Its inputs hold:
        F3 (pair (a,e), S = {b,c,d}): X_ae = Y_bc (+) Y_bd is V-twisted on b,c,d; L_a = X_ae (+) C e_e w^T. For m in S, (CA2) on L_m with
          xi = lam e_e w^T + xi', xi'_e = eps(xi') p_m gives W Xi_a Xi_k Xi_l = 0 and P_m Xi_a Xi_k Xi_l = 0 on Lam_m = pi_akl(L_m); here
          m_ke = 1 ((c4): m_ke + m_kl <= 3) and m_ae <= 2, so the restriction to Lam_m is injective and (Q4) P_a P_e P_k P_l = 0 holds for
          the three pairs {k,l} of S (P_e = pi_e(L_m) = span(w, p), P_a = pi_a(L_m); both independent of m). "(Qb)" is w . P_b P_c P_d = 0
          (Lemma S3-4 for r = a). (Q5J), (NT), (NT'), (M7) + L156 hold as in case N2.
        F4a (pair (a,b), S = {c,d,e}): X_ab = Y_cd (+) C e_e w^T (+) C x^{ce} = {(alpha_c v + lam y_c; alpha_d v; mu w + lam p)}, P_e = span(w,p).
          (Q4) for {a,b,c,d}: Lemma Q4-gen on L_e (type (t1)); for {a,b,c,e} and {a,b,d,e}: as in F3, from (CA2) on L_d, L_c (all three
          H's have rank >= 1 because m_ce = m_de = 2 and m_ae, m_be <= 2). (Qb): rho_b P_c P_d P_e = 0 from (CA2) on L_a (pi_cde(L_a) is a
          hyperplane of the 6-dim sum). (Q5): P_c P_d P_e . U_a U_b = 0 from ThA on X_ab (mu- and lam-parts, hyperplane injectivity).
          (NT), (NT'), (M7) + L156 as before; the planes are well defined by the linking argument of (A3).
        The only step of section 21 that used the V-twisted form of X_ab is (beta-0) (all three planes equal to P = span(e_1 - e_2,
        e_3 - e_4)); it is replaced by a COUNT valid in general: on P the row sums vanish and <,> = 2 Id, so P_2 = -Q with
        Q(x) = sum_{i<k} <x_i, x_k>, a NONDEGENERATE quadratic form on P^3 = C^6 (matrix (J_3 - I) (x) I_2); a level space with its three
        rows in P is totally isotropic, hence of dim <= 3 < 4 = dim X_ab.  (This also re-proves (beta-0) of section 21.)
   (A5) F4b (lam_ab = lam_cd = 4) -- OPEN; exact structure: after normalisation the four proper 2-row elements through e are
        x^{re} = e_r y_r^T + e_e p^T (r in R) with ONE vector p [m_ac >= 1 forces p_a in span(w, p_c)], so L contains the twisted free
        column Phi = {sum_r c_r e_r y_r^T + (sum_r c_r) e_e p^T} on all five rows, the single-row element e_e w^T (w orthogonal to all
        y_r), and M = L_a + L_c = X_ab + X_cd = Phi (+) C e_e w^T (+) C(e_c g_c^T + e_d g_d^T) (+) C(e_a g_a^T + e_b g_b^T); L_e is a
        collapsed 4-set with m_ab = m_cd = 2. Identities: P_a P_b P_c P_d = 0;  y_c, y_d kill P_a P_b P_e;  y_a, y_b kill P_c P_d P_e
        (P_r = span(y_r, g_r), P_e = span(w,p)); moments s(y_r) = s = -s(p), <y_r,y_r'> = s^2 = -<y_r,p>, tau(y_r,y_r',p) = -s^3, ...
        The proof of N2-X does not apply (for the 4-sets {a,b,c,e}, ... only the lines C y_c, ... are available).
   (A5') F4b, WHAT (CA2) GIVES EXACTLY, AND WHY IT IS NOT ENOUGH ALONE [rigorous + one exact example].
        Coordinates on M: m = sum_r c_r x^{re} + mu e_e w^T + ga G_ab + de G_cd (G_ab := e_a g_a^T + e_b g_b^T, G_cd likewise); rows
        a: c_a y_a + ga g_a,  b: c_b y_b + ga g_b,  c: c_c y_c + de g_c,  d: c_d y_d + de g_d,  e: (sum c) p + mu w.
        L_e = {sum c = 0, mu = 0} (dim 5), L_a = {c_a = 0, ga = 0}, ... (dim 5 each), so every L_r lies in M and (CA2) on the five row
        kernels is a statement about M. Expanding in the (linearly independent) monomials:
          (i)   (CA2) on L_e   <=>  P_a P_b P_c P_d = 0 in A_4                       [all 16 products; the monomials ga^i de^j c^.. on
                                                                                      {sum c = 0} are independent];
          (ii)  (CA2) on L_a, L_b  <=>  y_b . P_c P_d P_e = 0,  y_a . P_c P_d P_e = 0  [row b of L_a is only the LINE C y_b];
          (iii) (CA2) on L_c, L_d  <=>  y_d . P_a P_b P_e = 0,  y_c . P_a P_b P_e = 0.
        Nothing more comes from (CA2). In particular the twisted free column N := Phi (+) C e_e w^T satisfies the FULL (Q4) for its five
        row spaces (four lines and one plane):  Y_a Y_b Y_c Y_d = 0  and  Y_k Y_l Y_m . P_e = 0 for the four triples of R.
        LEVEL CONDITIONS OF N in closed form (eps = sum of coefficients, Y_T := prod_{r in T} Y_r for T inside R):
          eps(Y_r) = s = -eps(P);   eps(Y_T) = 0 for |T| >= 2;   eps(Y_T P) = 0 for |T| >= 1;   eps(Y_T W) = 0 for all T (also T empty).
        [sigma_k(m) = sum_{|T|=k} c_T eps(Y_T) + sum_{|T|=k-1} c_T eps(Y_T ((sum c) P + mu W)); non-squarefree monomials c_r c_T (r in T)
         occur only in the second sum.] Example: all y_r equal forces y_r = s e_j (e_2 = e_3 = 0 and all 4-fold products of entries 0).
        FREE-COLUMN SUB-FAMILY y_a = y_b = y_c = y_d = e_1 (s = 1): then p = -e_1 + p', and after the gauge g_a -> g_a + be e_1,
          g_b -> g_b - be e_1 one has g_r = q_r in C^N (N = {2,..,5}) with s(q_r) = 0, <q_a,q_b> = <q_c,q_d> = 0, <q_a + q_b, p'> = 0;
          w, p' in C^N with sum 0.  [g_a = q_a, g_b = ka e_1 + q_b: sigma_2 on Y_ab gives ka = -2 s(q_a), <q_a,q_b> = -s(q_a)^2;
          sigma_2 on G_ab + c x^{de} gives <q_a + q_b, p'> = 0; sigma_2 on G_ab + c x^{ae} gives s(q_a) = 0.]  So M = (free column 1) (+) D
          with D in the columns N (the "free column (+) D" model of round 4), and (i)-(iii) read: all four triple products of
          q_a, q_b, q_c, q_d vanish in (A_N)_3, q_a q_b q_c q_d = 0, and q_a q_b . {w, p'} = q_c q_d . {w, p'} = 0 in (A_N)_3.
        EXACT EXAMPLE M_0 (stage3/f4b_example.py: perm(J + m) = 120 at 900 random points with coefficients in Z[omega], 0 failures):
          y_r = e_1, p = -e_1, w = (0,-1,-1,3,-1), g_a = -g_b = n = (0,1,omega^2,0,omega), g_c = -g_d = n' = (0,1,omega,0,omega^2),
          omega = exp(2 pi i/3).  M_0 is a 7-dim level space with z = (0,0,0,0,1), lam_ab = lam_cd = 4, all other lam = 3, dim (M_0)_r = 5:
          EXACTLY the invariants and the shape of the F4b core. So the level conditions of the core alone do NOT exclude F4b.
          M_0 satisfies (i) but violates (iii) (e_1 . n n w != 0: n^2 w has the coefficient 6 n_2 n_3 at y_2 y_3 y_4), and
          dim T_1(M_0) = 8 (numerical rank, gap 5e-2 / 2e-16), so M_0 lies in no 9-dim level space, in agreement with (iii).
          [In the isotropic structure of M_0 (q_a, q_b on one isotropic line C n of the three columns T, q_c, q_d on the other one),
           (ii) + (iii) force w in C^T with s(w) = sum w_j/n_j = sum w_j/n'_j = 0, a Fourier system: w = 0. So this structure is excluded
           rigorously; the general sub-family is not.]
        NUMERICS (light, this container; LM with finite-difference Jacobians; scripts f4b_core.py, f4b_run.py, f4b_fc.py):
          general core, level conditions only, non-degeneracy hinges: 0 solutions in 7 starts (residual floors 0.03 - 0.14; without the
          hinges 7 of 7 starts converge to degenerate solutions);  free-column sub-family, level only: 1 solution (= M_0) in 19 starts;
          free-column sub-family with (i)-(iii): 0 in 8 starts (floor 0.58). The success rate of plain LM on these systems is low, so
          this is NOT evidence either way; the decisive computations are specified in COMPUTE-stage3.md, item 3.
        EXACT OPEN STATEMENT (F4b): there are no vectors y_a..y_d, p, w, g_a..g_d (independences as in (A5)) and t_1, t_2 such that
          M (+) C t_1 (+) C t_2 is a 9-dim level space with all a_r = 1; necessary: M level, (i), (ii), (iii), and FO2 for M.
 (B) TWO ROWS WITH 2-DIM SINGLE-ROW PARTS [rigorous, uses rows' Theorem FL2*].
   LEMMA. For 2-dim U inside 1^perp and U' = (U + C1)^perp: dim(U o U') >= 2.  [If <= 1, every u' in U' has a u != 0 in U with
   disjoint support; for generic u' this puts u on the columns where U' vanishes, i.e. on {j : e_j in U + C1}; that set has exactly
   two elements j,l, U = span(e_j - 1/5, e_l - 1/5), and then U o U' contains U'.]
   COROLLARY. If z_i = z_i' = 2 for two rows and <,> is nondegenerate on Z_i, then Z_i' = (Z_i + C1)^perp (Lemma S3-2 (b)), L contains
   the split pair e_i (x) Z_i (+) e_i' (x) Z_i', and FL2* gives dim L <= 10 - 2 = 8. So z-vectors with two entries 2 occur at most
   with BOTH planes degenerate (then Z_i and Z_i' share an isotropic vector orthogonal to both).
   (B') THEOREM Z22 [rigorous hand proof, uses rows' FL2* and its proof; NOT yet verified independently; sanity checks stage3/z22_check.py].
        In the regime (9-dim level L, all a_r = 1, all lam >= 3) at most ONE row has a 2-dim single-row part: z_d = z_e = 2 is impossible.
        Notation: U := Z_d, U' := Z_e. Both lie in 1^perp and U is orthogonal to U' (sigma_1, sigma_2 on e_d u^T + e_e u'^T), so
        U' = (U + C1)^perp and U cap U' = rad(U). Three cases: (nd) rad(U) = 0: excluded by FL2* and dim(U o U') >= 2 (part (B)).
        (deg-1) rad(U) = C n a line (n isotropic, s(n) = 0), V_3 := U + U' 3-dim, V_3^perp = span(1, n). (deg-2) U = U' totally isotropic.
        STEP 1 (the first four steps of rows' proof of FL2*, R3.9; they do not use U cap U' = 0). Pi := projection of L to the rows a,b,c;
          its kernel is the 2-row space Y_de, which contains the 4-dim e_d U (+) e_e U' and has dim <= 4 (L101): dim Pi = 5.
          For x = (Y''; a; b) in L (a = row d, b = row e), c := column sums of Y'': the la la'-coefficient of perm(J + x + la e_d u^T +
          la' e_e u'^T), in degree 1 in x, is 4 <c, u o u'> = 0; the la- and la'-coefficients in degree 1 are -6 <u, b + c> = 0 and
          -6 <u', a + c> = 0 [Delta_0 = 6(J - I), (Delta_1)_{jl} = 2(S - c_j - c_l)]. So c(Pi) lies in (U o U')^perp (which contains 1),
          Pi_0 := {c in C1} has codim <= 4 - dim(U o U') in Pi, and over Pi_0: a in U'^perp = U + C1, b in U^perp = U' + C1. Subtracting
          single-row elements, every Y'' in Pi_0 has a unique lift z = (Y''; al 1; be 1) in L; perm(J + z) = (1 + al)(1 + be) G(Y'') = 120
          identically on a linear space forces al = be = 0, and then sigma_1 gives c = 0. Hence
              dim { x in X_de : all column sums of x vanish } >= dim Pi_0 >= 1 + dim(U o U').
          On the other hand lam_de <= 5 - z_e = 3 ((c2)). So dim(U o U') = 2, lam_de = 3, and EVERY x in X_de has x_a + x_b + x_c = 0.
        STEP 2 (deg-2 is impossible). For a totally isotropic plane Z = span(n,h) in 1^perp, dim(Z o Z) = 3: a relation
          x n o n + y n o h + z h o h = 0 factors as l_1(n_j,h_j) l_2(n_j,h_j) = 0 for all j; z_i := l_i(n,h) are nonzero vectors of Z
          with z_1 o z_2 = 0; l_1 || l_2 gives z_1 = 0; otherwise z_1, z_2 have disjoint supports, and a nonzero isotropic vector with
          sum 0 has at least 3 nonzero entries: 6 > 5. So dim(U o U') = 3, against STEP 1.
        STEP 3 (LEMMA DEG, case (deg-1)): every x in X_de has X_a X_b X_c = 0 in A_3 (all ten 3x3 subpermanents vanish).
          Proof. For z in U the element x + e_d z^T lies in L_e, so (CA2) (a_e = 1) gives z . X_a X_b X_c = 0 in A_4; the same with L_d
          and U'. So B := B_{X_a X_b X_c} (symmetric, zero diagonal) kills V_3; its image lies in V_3^perp = span(1, n):
          B = x 1 1^T + y (1 n^T + n 1^T) + z n n^T, and the zero diagonal says x + 2 y n_j + z n_j^2 = 0 for all j. If B != 0 the entries
          of n take at most two values, n = la 1_A + mu 1_B, and s(n) = <n,n> = 0 give 5 la^2 |A|/|B| = 0, n = 0. So B = 0. QED
        STEP 4 (deg-1 is impossible). By (c2) and (c5), lam_{rd} = lam_{re} = 3 and m_bc, m_ac, m_ab >= 1 (r in {a,b,c}): X_de contains
          2-row elements, and by STEP 1 they are t = (e_b - e_c) u^T, t' = (e_c - e_a) v^T, t'' = (e_a - e_b) x^T with u, v, x != 0.
          On X_de (zero column sums) sigma_2 = (1/2) sum_r q(x_r), q(y) := <y,y> - s(y)^2 = -2 e_2(y), a NONDEGENERATE form (I - J).
          (IND) t, t', t'' independent: X_de = {(ga x - be v, al u - ga x, be v - al u)}; sigma_2 = 0 makes S := span(u,v,x) totally
            q-isotropic, so dim S <= 2, and = 2 (dim 1 would make t, t', t'' dependent). Lemma DEG reads (coefficients of al^2 be, ...)
            U^2 V = U^2 X = V^2 U = V^2 X = X^2 U = X^2 V = 0 in A_3. Say u, v independent, x = la u + ka v. If la != 0: U^3 = 0, so u has
            <= 2 nonzero entries and e_2(u) = 0: u = c e_j; then V^2 y_j = 0 and e_2(v) = 0 give v = c' e_l, l != j, and
            q(u,v) = -c c' != 0: contradiction. If ka != 0: the same with u, v exchanged. (The other two labelings are symmetric.)
          (DEP) t, t', t'' dependent: then u || v || x =: y and X_de contains F_y = {c (x) y : c_a + c_b + c_c = 0} (2-dim).
            sigma_2: q(y) = 0; Lemma DEG: c_a c_b c_c Y^3 = 0; so y = e_j and F_y = F is the free column j on the rows a,b,c.
            X_de = F (+) C xi with xi != 0 supported in the columns N != j (subtract its column j, which lies in F). Lemma DEG on
            c (x) e_j + th xi: Xi_a Xi_b Xi_c = 0 and Xi_b Xi_c = Xi_a Xi_c = Xi_a Xi_b =: Q; with xi_c = -xi_a - xi_b this is
            Xi_a^2 = Xi_b^2 = Xi_c^2 = -2Q, hence Xi_r^3 = -2 Xi_r Q = -2 Xi_a Xi_b Xi_c = 0: every xi_r has <= 2 nonzero entries.
            sigma_2 (cross term): sum_r c_r s(xi_r) = 0 on {sum c = 0} and sum_r s(xi_r) = 0 give s(xi_r) = 0 for all r.
            If some xi_r has two nonzero entries (columns k,l), then by Xi_a^2 = Xi_b^2 = Xi_c^2 all three are p_r (e_k - e_l) with
            p_r != 0, and Xi_a^2 = -2 Xi_a Xi_b, Xi_b^2 = -2 Xi_a Xi_b give p_a = -2 p_b, p_b = -2 p_a: p_a = 0. Otherwise every xi_r has
            at most one nonzero entry and sum 0: xi = 0. Contradiction in both cases.                                           QED
        Sanity checks (z22_check.py): the three degree-1 identities of STEP 1 hold EXACTLY on random rational data (Fractions);
        200 random instances: dim(Z o Z) = 3 for totally isotropic Z; no B != 0 in Lemma DEG; generic
        (deg-1) pairs have dim(U o U') = 4. A light LM search for the 7-dim space span(t,t',t'') (+) e_d U (+) e_e U' (deg-1 shape,
        level conditions only) found 0 solutions in 8 starts (deg_small.py; corroboration only).
        COROLLARY of STEP 1 for ANY two rows d, e of a level space L with full split data (e_d U (+) e_e U' inside L, U' = (U + C1)^perp,
        degenerate or not): dim {x in L : rows d, e = 0, all column sums 0} >= dim L - 8 + dim(U o U').
 (C) (S3-a), z_e = 2 -- structure sharpened, NOT settled.
   (C5) Rigidity: for r in R, pi_e(L_r) = Z, so every 2-row space through e is trivial, Y_ke = e_e Z, and X_{rr'} = Y_kl (+) e_e Z:
        lam_{rr'} = 2 + m_kl in {3,4}; the m-pattern on R is (t0), (t1) or (t2) of section 16, and (Q4) holds for R in all three.
   (C6) X_{re} is a 3-row level space with a deletable row in the 4x5 space L_r = X_{re} (+) e_e Z: its 3-row defect space lies in
        U' := (Z + C1)^perp (rows' R1 one floor down), and it is not strongly level (SL_3): 1 <= e_3(X_{re}) <= 2. Column sums of L_e lie in U'.
   (C7) WHY THE CYCLIC IDENTITY DOES NOT COME FROM LINEALITY: perm(u + s e_e z^T) is linear in s, so the single-row elements give exactly
        "Z . U_a U_b U_c U_d = 0 on L^" and its polarisations; every identity that is cubic in the planes P_k, P_l, P_m of one triple
        and involves Z is a polynomial identity on X_{re} (the only elements of L with rows in these three planes and row r = 0
        are X_{re} + e_e Z), so it only sees the restriction of the trilinear form to the diagonal of X_{re}, whose kernel is the
        cyclic difference. FO2 adds quadratic conditions on the 2-dim quotient L/M (rows outside the planes); to use them one needs
        M explicitly. Not done.
   (C8) If a second row has a single-row part of dim 2: (B). If e(L_e) = 1: L_e is a (5,1) space.
   (C9) ANSWER to "is e_e (x) Z part of a split pair inside L?": never a full one -- a second row carrying U' = (Z + C1)^perp (or any
        2-dim single-row part) is excluded by Theorem Z22 ((B')). A second row can at most carry ONE vector w' of U' (z = (2,1,..));
        then (w' in row d) for all x in L:  x_d + c(x) lies in U' + C1,  <w', x_e + c(x)> = 0,  <c(x), u o w'> = 0 for u in Z  (c = column sums of the other three
        rows; the degree-1 identities of (B') STEP 1), which is not enough to run the FL2* argument. OPEN.
 (D) WHAT IS LEFT of "no 9-dim level space with all a_r = 1 and lam >= 3", by the vector z (sorted; z_i <= 2, at most ... by (c1),(c2)):
   z = 0:                 impossible (Theorem N = N1 + N2-X).
   z = (1,0,0,0,0):       F1, F3, F4a impossible ((A3), (A4));   F4b OPEN ((A5), (A5'): core shape realisable (M_0), identities (i)-(iii)).
   z = (2,0,0,0,0):       OPEN = (S3-a): missing cyclic identity / weakened plane problem ((C), section 24 (C)).
   two entries 2:         IMPOSSIBLE (Theorem Z22, (B) + (B'): FL2* in the nondegenerate case, a count and Lemma DEG otherwise).
   z = (1,1,*,*,*), (2,1,*,*,*) with one entry 2 at most: OPEN, not analysed (for two rows e, e' with z = 1 one has
                          W W' . P_k P_l = 0 for the pairs of the other three rows; the single-row vectors are pairwise orthogonal).
   Besides: rows with a_r >= 2 (reg2), the transposed statements, and the verification of sections 21, 24, 26.
STATUS 19:25 (round 7): section 26 written: z = (1,0,0,0,0) impossible in F1, F3, F4a; FL2* corollary; structure of (S3-a); table (D).
STATUS 19:31: COMPUTE-stage3.md written (requests for the 24-core machine).
STATUS 19:58: F4b: (CA2) gives exactly (i)-(iii); exact level space M_0 of F4b-core shape found (violates (iii), dim T_1 = 8); F4b stays OPEN.
STATUS 20:02: Lemma DEG for the degenerate two-plane case added (section 26 (B')).
STATUS 20:10: THEOREM Z22 proved (two rows with 2-dim single-row parts are impossible, degenerate planes included). Final report of round 7.

## 27. ROUND 8 (stopped early): the free-column sub-family of F4b by exact computation; parallel y_r; z = (2,1,..)
 (A) THEOREM FC [exact; scripts stage3/gb/gbl.py, fc_gen.py, fc_exact.py]. Free-column sub-family of F4b (section 26 (A5')): y_r = e_1,
     p = -e_1 + p', and q_a, q_b, q_c, q_d, w, p' zero-sum vectors of C^N (N = columns 2..5), q_r != 0, w != 0. Unknowns: 3 free
     coordinates per vector. CHARTS: by the S_4-symmetry of the columns N, (q_a)_1 = 1; (q_c)_i = 1 and w_i = 1 for i in {1,2,3} (scalings of
     (q_c,q_d) and of w); q_b != 0 and q_d != 0 by Rabinowitsch variables on coordinate i in {1,2,3}; gauge p'_i = 0 at the chart
     coordinate of w (p' -> p' + al w): 81 charts. Equations: LEVEL = all 123 coefficients (in c_a..c_d, mu, ga, de) of perm(J + m) - 120,
     generated mechanically from the 5x5 permanent; IDENT23 = LEVEL + q_a q_b . {w, p'} = q_c q_d . {w, p'} = 0 in (A_N)_3; FULL = IDENT23 +
     the four triple products of the q's + q_a q_b q_c q_d.
       [modular] msolve -g 2, p = 65521, 2147483629, 2147483497: LEVEL non-unit on 81/81 charts (17-22 basis elements, finite solution
                 sets, p' = 0 in every printed basis); IDENT23 unit on 81/81; FULL unit on 81/81.   (about 20 s per mode and prime)
       [exact]   Singular std over Q (integer coefficients recovered with the modulus 2^127 - 1, all |coeff| < 10^9 asserted):
                 IDENT23 unit on 81/81 charts (16 s), FULL unit on 81/81 charts (12 s). Exact calibration: M_0 solves LEVEL
                 (f4b_example.py); the exact std of LEVEL with dim/vdim on all charts did not finish in 100 s (not needed).
     CONSEQUENCE: no F4b space has y_a = y_b = y_c = y_d (up to scaling). REMARK: in all LEVEL solutions seen p' lies in C w, so M contains
     the FULL free column 1; then Theorem FL applied to the transposed space also excludes them (independent confirmation).
 (B) [rigorous] PARALLEL y_r ARE OF FREE-COLUMN TYPE. Let y_r = la_r y. If s != 0: all la_r are equal, y_r = y, and eps(Y_T) = 0 (|T| = 2,3,4)
     give e_2(y) = e_3(y) = e_4(y) = 0; (i) gives Y^4 = 0, i.e. y has >= 2 zero entries; so y = s e_j. If s = 0: e_1 = .. = e_4 = 0 and Y^4 = 0
     (two zero entries, so e_5 = 0) give y = 0. Hence with (A): in F4b the vectors y_a, y_b, y_c, y_d are NOT all parallel.
 (C) [rigorous remarks, not verified] z = (2,1,..): let z_d = 2 (U := Z_d), e_e w'^T in L. Counting ((c2)): lam_{rd} = 3 and pi_d(L_r) = U for
     every r != d, so L_r = X_{rd} (+) e_d U and M_d := L_d (+) e_d U (7-dim) contains every L_r: this is exactly the structure of (S3-a),
     with the extra single-row element e_e w'^T inside L_d and w' in U' = (U + C1)^perp. Degree-1 identities of 26 (B') STEP 1 for x in L,
     c = column sums of the rows a,b,c:  <c, u o w'> = 0,  x_e + c in U^perp = U' + C1,  <w', x_d + c> = 0.  For x in X_de: (CA2) on L_e and
     L_d gives that B_{X_a X_b X_c} kills U + C w'; if w' is not in U its image lies in span(1, k) (k in U', <k,w'> = 0, s(k) = 0), so
     X_a X_b X_c = 0 on X_de unless k is two-valued (k proportional to |B| 1_A - |A| 1_B). NOT pursued further.
 (D) [numerical, inconclusive] stage3/f4b_newton.py (holomorphic LM with analytic Jacobian for the general F4b core, level only):
     without non-degeneracy constraints 19 of 28 starts converge, all to degenerate cores; with Rabinowitsch non-degeneracy 0 of 8
     (residual floor 2e-3 .. 5e-3). No conclusion.
STATUS 20:31 (round 8): Theorem FC (exact), parallel case, errata applied; round stopped by the coordinator; handover written.


# ROUND 9 (start 20:45 UTC, Kevin's machine; budget ~90 min). Targets: (1) F4b; (2) S3-1 (seeded extension, calibrated at dim 7);
#  (3) z = (2,0,0,0,0) and mixed patterns. Note: handover/HANDOVER-stage3.md was never written (the round-8 stop came first).
STATUS 20:50: read TEAM-RULES, BRIEF (UPDATE 11), COMPUTE-stage3, ERRATA A1/A2, coordinator's S3-1 calib (0/40 random starts at dim 7).
 Idea for F4b: the level conditions of the twisted free column N are MOMENT conditions (generating function prod_j (1 + <t, v_j>) mod t^2,
 v_j = column j of (y_a..y_d)); combined with (i)-(iii) they give pointwise conditions on each column. Working it out.

## 28. ROUND 9: F4b via MOMENTS. The twisted free column is rigid (types C1, C3), then exact elimination of each type
 Setting = section 26 (A5), (A5'): F4b core M = Phi (+) C e_e w^T (+) C G_ab (+) C G_cd, Phi = {sum_r c_r e_r y_r^T + (sum c) e_e p^T},
 N := Phi (+) C e_e w^T (level, inside L). Necessary identities (i)-(iii) of (A5'). Write v_j := (y_aj, y_bj, y_cj, y_dj) in C^4
 (column j of the y-rows), t = (t_a..t_d), and compute in the ring C[t, t_u]/(t_a^2, .., t_u^2) ("mod squares"), pi_B(v) := prod_{r in B} v_r.
 (M1) GENERATING FUNCTION [rigorous]. For any rows x_1..x_k (k x 5 matrix with columns x_.j): eps(X_1 .. X_k) = coefficient of t_1..t_k in
      prod_j (1 + sum_i t_i x_ij) (mod squares): each column contributes at most one row.   The level conditions of N (closed form of
      (A5'), re-derived: sigma_k = sum_T c_T eps(Y_T) + sum_T c_T eps(Y_T ((sum c) P + mu W)); the monomials c_r^2 c_T' and mu c_T are
      unique) are exactly:  s(y_r) = s, s(p) = -s, s(w) = 0, eps(Y_T) = 0 (|T| >= 2), eps(Y_T P) = 0 (|T| >= 1), eps(Y_T W) = 0 (all T); i.e.
           Pi(t)   := prod_j (1 + <t,v_j>)              = 1 + s (t_a + t_b + t_c + t_d)          (mod squares)
           Pi_u(t) := prod_j (1 + <t,v_j> + t_u u_j)   = 1 + s sum_r t_r + s(u) t_u              for u = w (s(u) = 0) and u = p (s(u) = -s).
 (M2) POINTWISE FORM OF (i)-(iii) [rigorous]. The 4x4 subpermanent of rows R, columns [5] - k, is [t_R] Pi(t) (1 + <t,v_k>)^{-1}; with
      (1 + <t,v>)^{-1} = sum_B (-1)^|B| |B|! pi_B(v) t_B and (1 + <t,v>)^{-2} = sum_B (-1)^|B| (|B|+1)! pi_B(v) t_B this gives
        (Y4)  Y_a Y_b Y_c Y_d = 0 in A_4   <=>   4 e_4(v_k) = s e_3(v_k)                                        for every column k;
        (YU)  Y_T U = 0 in A_4 (|T| = 3)    <=>   (4 u_k - s(u)) pi_T(v_k) = s u_k e_2(v_k restricted to T)        for every k, T, u in {w,p}.
      (Y4) is part of (i); (YU) for the four 3-sets T is part of (ii) + (iii) (y_a, y_b kill Y_c Y_d {W,P}; y_c, y_d kill Y_a Y_b {W,P}).
      Numerical check of the formula: stage3/r9/mom_check.py (error < 1e-14).
 (M3) LEMMA s != 0 [rigorous]. Suppose s = 0. Then (M1) says: ALL multilinear moments m_B = sum_j pi_B(v_j) vanish (B nonempty), and
      sum_j u_j pi_B(v_j) = 0 for all B (u = w, p). (Y4): e_4(v_k) = 0; (YU): every column in supp(w) + supp(p) has >= 2 zero y-coordinates.
      V := span{pi_B : B in R} (vectors indexed by columns, pi_empty = 1) is orthogonal to the independent w, p, so dim V <= 3, and
      U := span(y_r) (inside 1^perp, <1,1> != 0) has dim <= 2. dim U = 1: y_r = la_r y, (Y4) gives y_k^4 = 0: y = 0.  dim U = 2, with
      <y_r, y_r'> = m_rr' = 0 (r != r'):  nondegenerate form on U: impossible for four pairwise orthogonal nonzero vectors spanning U.
      Rank 1 (radical C n): three y_r are multiples of n; s(n) = <n,n> = sum n_j^3 = 0 (m_B, |B| = 3) forces >= 4 nonzero entries of n;
      by (Y4) the fourth y vanishes on these columns, has sum 0, so it is 0.  Totally isotropic: V = U + C1, span(w,p) = V^perp = U, so every
      column of supp(U) has >= 2 zero y-coordinates; writing Y = A [n; h], the zero set of v_k is ONE class of parallel rows of A, of size >= 2;
      class sizes (3,1), (2,1,1) make one y vanish identically; (2,2) gives n', h' in U with disjoint supports, each isotropic with sum 0,
      hence with >= 3 nonzero entries: 6 > 5.  So s != 0; scale s = 1.
 (M4) CLASSIFICATION FOR s = 1 [rigorous]. Call a column THIN if v_k has <= 1 nonzero coordinate, FAT otherwise.
      (YU) for u = w: a column with w_k != 0 is thin (4 pi_T = e_2 on all four T forces v = (3/4)1 if all coordinates are nonzero, which
      violates (Y4), and is impossible with 1 or 2 zero coordinates).  Fat columns (by (Y4), (YU) for u = p): either v_k = (1,1,1,1) with
      p_k = -1, or v_k has exactly two nonzero coordinates and p_k = 0 (three nonzero coordinates are impossible). w != 0, s(w) = 0 give
      >= 2 thin columns, so f := #fat <= 3, and the thin columns contribute prod_r (1 + sig_r t_r) to Pi. Matching Pi = 1 + sum t_r
      degree by degree (the product of f <= 3 linear factors has no t_R term) leaves exactly:
        C1: f = 1, v_k0 = (1,1,1,1), sig = 0:  y_r = e_k0 + u_r, the u_r supported on the other four columns with PAIRWISE DISJOINT supports and
            s(u_r) = 0; p = -e_k0 + p', s(p') = 0, <p',u_r> = 0; w_k0 = 0, <w,u_r> = 0.   (At most two u_r are nonzero; two nonzero ones live on
            two columns each, and then p' is in C w.)  All u_r = 0 is the free-column sub-family (Theorem FC).
        C3: f = 3: columns k0: (1,1,1,1), k1: (-c, y, 0, 0), k2: (-c, -y, 0, 0) (coordinates (a, r1, ., .)), the two thin columns j, l: (c,0,0,0)
            each, w = e_j - e_l, p = -e_k0 (mod w), c y != 0; r1 in {b, c} up to the symmetry of F4b (dihedral group of the pairing {ab|cd}).
      (f = 0, 2 and the other f = 1, 3 patterns die on the degree-1, -2 or -3 coefficients.) Numerical check that C1 and C3 satisfy
      level(N), (Y4), (YU): r9/mom_check.py (all residuals <= 7e-14; a perturbed p fails).
 (M5) EXACT ELIMINATION OF EVERY TYPE [scripts r9/gen9.py (mod p, msolve), r9/exact9.py (Singular std over Q)]. Common normal form:
      k0 = column 0, y_r = e_0 + u_r, p = -e_0 + p', w_0 = 0; gauge G_ab + be (x^{ae} - x^{be}) makes g_a0 = 0 (likewise g_c0 = 0); charts
      g_{a,i} = 1, g_{c,k} = 1 (i, k = 1..4). NON-DEGENERACY (from (A5): (y_r, g_r) independent): with nd = 1 a Rabinowitsch variable makes the
      minor of (y_b, g_b) on the columns (0, i_b) invertible (y_b0 = 1, so these four minors vanish only if g_b is a multiple of y_b), same for
      d: 16 more charts. Equations LEVEL = all coefficients of perm(J + m) - 120 in (c_a..c_d, mu, ga, de), FULL = LEVEL + (i), (ii), (iii).
      CALIBRATION (r9/calib_gen9.py): the exact M_0 (omega realised in F_p) satisfies all 178 LEVEL polynomials of case C1G at p = 65521,
      2147483629, 2147483497 and violates 12 of the 100 FULL ones ((iii) fails on M_0).
      Results so far:   C3 (r1 = b): LEVEL alone UNIT on 16/16 charts (exact over Q; msolve 3 primes);   C1 two nonzero u's in the same pair
      (C12ab): LEVEL alone UNIT 16/16 (exact over Q; msolve 3 primes);   C3 (r1 = c): FULL + nd UNIT 256/256 at p = 65521 (without nd: 8
      non-unit charts, all with g_b = g_d = 0, i.e. P_b, P_d lines: degenerate);  C12ac, C1G: running.
STATUS 20:12 (UTC; my first round-9 STATUS line "20:50" was local time UTC+1 -- the round started 19:45 UTC): section 28 written:
 moment lemma (s != 0) and classification C1/C3 of the F4b twisted free column [rigorous]; exact eliminations: C3b, C12ab (LEVEL unit, Q),
 C3c, C12ac (FULL+nd unit at 2 primes so far), C1G over Q running (66/192 charts unit). S3-1 seeded driver r9/s3seed.py written (calibrating).
 (M5') RESULTS (complete; records in stage3/r9/exact_*.txt, logs run_all.log, run_nd.log, run_exact*.log, gb/ex_*.sing.out):
      case                      system           charts   Singular std over Q        msolve mod p (65521, 2147483629, 2147483497)
      C3, r1 = b   (C3b)        LEVEL only        16      UNIT 16/16                 UNIT 16/16 at all 3 primes (also FULL)
      C1, u_a,u_b != 0 (C12ab)  LEVEL only        16      UNIT 16/16                 UNIT 16/16 at all 3 primes (also FULL)
      C3, r1 = c   (C3c)        FULL + nd        256      UNIT 256/256 (3.7 s)       UNIT 256/256 at all 3 primes
      C1, u_a,u_c != 0 (C12ac)  FULL + nd        256      UNIT 256/256 (4.1 s)       UNIT 256/256 at all 3 primes
      C1, u_a arbitrary (C1G)   FULL + nd        192      UNIT 192/192 (*)           cross-check at p = 2147483629 running
      (*) 191 charts by plain chart std (<= 8 s each); chart 11113 (iw=1, ia=1, ic=1, ib=1, id=3) exceeded 90 s and was closed by its
          STRATIFIED version (chart index = first nonzero coordinate / minor; the stratum lies inside the chart, so "original or stratified
          system unit" for every chart tuple covers all points): UNIT in 0.1 s.
      C1G has u_b = u_c = u_d = 0 and u_a FREE (u_a = 0 allowed), so it contains the free-column sub-family: an independent re-derivation of
      Theorem FC (section 27) with g_a..g_d NOT pre-reduced by hand. C1G uses the S_4 symmetry of columns 1..4 to put the chart of g_a on
      column 1 (all data of C1G are S_4-equivariant). Without nd, C3c, C12ac, C1G have non-unit charts, ALL with g_b = g_d = 0 (P_b, P_d
      lines), i.e. outside F4b.  Unit ideal over Q = no solution over C (Nullstellensatz; integer generators), so these are PROOFS.
 THEOREM F4b-X [rigorous hand proof (M1)-(M4) + exact computation (M5'); NOT yet independently verified]: the family F4b does not occur.
   Inputs: the F4b normal form of section 26 (A5) (re-checked this round: the single vector p comes from dim X_ab = 4, dim X_cd = 4 and
   m_ac >= 1 with dim X_bd = 3; (y_r, g_r) independent because g_b in C y_b would make G_ab - k x^{be} a 2-row element on (a,e), m_ae >= 3,
   against (A1); w, p independent; y_r != 0), the identities (i)-(iii) of (A5') (from (CA2); monomial independence on {sum c = 0} re-checked),
   the moment lemma (M1)-(M4) and the exact eliminations (M5').
 COROLLARY [same status]: z = (1,0,0,0,0) is IMPOSSIBLE in the regime (9-dim level, all a_r = 1, all lam >= 3): F1, F3, F4a (section 26 (A3),
   (A4)) and F4b (above). Table 26 (D) now: z = 0 impossible (Theorem N, verified); z = (1,0,0,0,0) impossible; two entries 2 impossible
   (Theorem Z22); OPEN: z = (2,0,0,0,0) = (S3-a), and the patterns with single-row elements in >= 2 rows and at most one entry 2.
STATUS 20:15: F4b closed (Theorem F4b-X, sec. 28: moment lemma + exact Q eliminations, all charts unit); S3-1 calibrations running.

## 29. ROUND 9: S3-1 calibration diagnosis; (S3-a) and (2,1,..) reduced to "dim T_1(L(L')) <= 8 for (5,2) spaces" + (DI_5)
 (A) S3-1, WHY THE CALIBRATIONS FAIL [numerical; scripts r9/s3seed.py, s3diag.py, s3diag2.py; solver = rows/clm.py, residual P_1..P_5 at
     N = 2 x #monomials points].
     - coordinator: random holomorphic LM, dim 7 (q = 2, k = 5): 0/40, best 2.1e-5.
     - seeded from a random 6-dim subspace of a known 7-dim lift + a random vector: 0/2 (floors 3.5e-6, 2.2); + a vector of T_1(S): 0/1 (1.3e-5).
     - planted at distance 0.03 from a known 7-dim lift ((4,1) seeds): floors 5.2e-7, 3.7e-7 after 250 iterations (no "hit" at 1e-7).
     - from a 1e-3 perturbation of a known lift (clm_p4_d4_defect1_s24): the Jacobian of the sampled system at the seed (4620 x 126) has a
       numerical kernel of dim 11; LM returns to residual 7.9e-9 and stalls; with 11 random linear slices through the seed the solution is
       isolated but LM converges only LINEARLY (distance x 0.6 per 8 iterations, residual proportional to distance).
     CONCLUSION: the known 7-dim level spaces with single-row parts are SINGULAR (non-reduced) points of the sampled level system: the
     Jacobian kernel is larger than the tangent space of the solution set, so Newton/LM converge only linearly near them and stall at
     1e-5 .. 1e-8 depending on the start. A residual threshold 1e-8 rejects true solutions; plain-LM negatives at dim 8, 9 mean nothing
     (in line with TEAM-RULES). What would work: (a) many more iterations with a trend criterion (residual decreasing geometrically) and
     an algebraic confirmation; (b) deflation (augment the system by J(z) v = 0, random normalisation of v) to restore quadratic convergence;
     (c) target the exact structural reductions instead (below). Spec for the heavy machine: COMPUTE-stage3.md item 6 (added).
 (B) (S3-a) AND EVERY PATTERN WITH A 2-DIM SINGLE-ROW PART [rigorous reduction, from section 24 (C4) and Lemma S3-1]. If z_e = 2 in the
     regime, M = L_e (+) e_e Z is level, L_e is a 4x5 level space of dim 5 with defect e(L_e) in {1, 2} (>= 1 by Lemma SL, <= 2 because
     Z lies in (C(L_e) + C1)^perp and is 2-dim). e(L_e) = 1: L_e is a (5,1) space -- excluded iff rows' (DI_5) holds for (5,1).
     e(L_e) = 2: M = L(L_e) EXACTLY (rows' lift), and L inside T_1(M) (first-order condition) gives  9 <= dim L <= dim T_1(L(L_e)).
     (If row e of M is deletable, y_e = e_e 1^T - J/5 lies in T_1(M) but not in L (P_2(y_e) != 0), so even 10 <= dim T_1 would be needed;
     I use only the plain inequality.) Hence:
         (S3-a) and all patterns (2, *, ...)  <==  [no (5,1) space]  AND  [dim T_1(L(L')) <= 8 for every (5,2) space L'],
     where for (S3-a) only (5,2) spaces WITHOUT single-row elements matter (z_r = 0 for r in R).
     CENSUS [numerical, r9/t1_c52.py]: all 27 stored (5,2) spaces (rows/c52_*.npy, clm_p4_d5_defect2_*.npy) have dim T_1(L(L')) = 8 with
     a clean gap (2e-2 vs 1e-16): 3 without single-row elements (c52_rand_242, c52_seedns_33, c52_seedns_39 -- the census's C = V_S,
     |S| = 3 type), 15 split u = (1,1,0,0), 9 split u = (2,0,0,0).  So the second condition holds on every known example.
     PROPOSED TARGET: prove dim T_1(L(L')) = 8 for (5,2) spaces L' without single-row elements, using the census LAW (C = V_S, |S| = 3,
     two neutral = deletable columns, so L' with a neutral column deleted is a 5-dim 4x4 level space, a maximal one) -- or use the
     extra (S3-a) structure (CA2), (Q4) for R, the m_kl normal forms (t0)/(t1)/(t2) of section 16.
STATUS 20:21: F4b closed (exact Q + mod p cross-checks); S3-1 calibration diagnosed (singular solution points, linear LM convergence); (S3-a) reduced to T_1 of (5,2) lifts + (DI_5), census 27/27 T_1 = 8.
 (C) z_e = 1 PROBE [numerical, r9/t1_mixed.py]. For a row with z_e = 1, M6 = L_e (+) C e_e w^T is level (L_e: 5-dim 4x5 level space, defect
     e(L_e) in {1,2,3} since w is orthogonal to C(L_e) + C1) and L lies in T_1(M6). Census: (5,2) spaces + one generic w in (C+C1)^perp:
     dim T_1(M6) = 8 for 19 split, = 9 for 5 split and for all 3 non-split;  (5,3) lifts (random 5-dim subspaces of the (6,3) spaces):
     dim T_1 = 8 in 7/9, = 9 in 2/9 (both from the LM-limited file clm_p4_d6_defect3_s3, gap 7e-8: unreliable). So for z_e = 1 the
     first-order bound alone does NOT suffice in general; FO2 (or the (CA2)-type identities) must enter. The (5,3) case (e(L_e) = 3,
     M6 = L(L_e)) looks first-order closable. Remark: section 24 (F) already had the T_1 structure formula used in (B); (B) adds the general
     reduction (any 9-dim level L with a_e = 1, z_e >= 2) and the census of the three non-split (5,2) spaces.
 (D) (S3-a) REDUCED TO A PURE 4x5 STATEMENT [rigorous reduction + numerical census, r9/rowproj5.py, ns52.py].
     In (S3-a) (regime + z = (2,0,0,0,0)): lam_re = 3 for r in R ((c2) and lam >= 3), so X_re = ker(pi_r on L_e) is 3-dim and
     dim pi_r(L_e) = 2 for ALL r in R; L_e has no single-row element (z_r = 0). Hence
         (PR2)  "no 5-dim 4x5 level space without single-row elements has all four row projections of dim 2"   ==>   (S3-a) is impossible,
     whatever e(L_e) is (no appeal to (DI_5) needed). CENSUS of the 50 stored 5-dim 4x5 level spaces (rows/*.npy): row-projection dims
     (2,2,2,2) occur ONCE (clm_p4_d5_defect2_s9, single-row dims (1,1,0,0), so not a counterexample; its lift has dim T_1 = 8); the spaces
     without single-row elements have row-projection dims (2,2,4,4) [4 spaces, incl. c52_rand_242, c52_seedns_39] or (3,3,4,4) [2 spaces].
     So (PR2) holds on every known example. It is a 4x5 problem in the 8-dim space (+)_r e_r (x) P_r (L_e a 5-dim subspace), the setting
     of the plane lemmas (secs 12, 15) and of COMPUTE item 2; with (CA2) one also has P_a P_b P_c P_d = 0. The same reduction for
     (2,1,..): L_e then has all row projections 2-dim and single-row dims (1,0,0,0) -- also absent from the census (s9 has (1,1,0,0)).
STATUS 20:28: (S3-a) reduced to the 4x5 statement (PR2) (census 50/50 consistent); T_1 route also recorded; completeness check of the F4b classification running.
 (E) NUMERICAL COMPLETENESS CHECK of the moment classification (M3)-(M4) [r9/mom_search.py; holomorphic LM on level(N) + (Y4) + (YU) with
     Rabinowitsch variables for y_r != 0 and (w, p) independent -- exactly the lemma's hypotheses]: s = 1: 12 of 12 starts converge
     (residual <= 7e-14), 11 of type C1 (one all-ones column, four thin columns; 10 with one nonzero u_r, 1 with two) and 1 of type C3
     (columns with 1,1,2,2,4 nonzero y-coordinates, w on two columns); NOTHING else.  s = 0: no convergence (as Lemma (M3) predicts; run
     continuing, log r9/mom_s0.log). Without the Rabinowitsch variables the s = 0 search converges to DEGENERATE points (three y_r = 0, p = 0),
     which shows that the hypotheses y_r != 0, (w,p) independent are really used.
 (F) (PR2) PROBE [r9/pr2_search.py]: without hinges LM converges fast but to degenerate spaces (row projections of dim 0/1, single-row
     elements); with the rank-2 hinge 0/3 in the first test (floors 2.8e-4 .. 2e-2): NOT calibrated yet; calibration run (40 starts, hinge
     rank 2 only, must find s9-type spaces) in r9/pr2_cal.log.
STATUS 20:31: completeness check of the F4b classification: s=1 12/12 of types C1/C3 only; s=0 none. Writing final report.
STATUS 20:33: round 9 final. Still running in background (both end by ~20:55, logs in stage3/r9): mom_s0.log (s=0 completeness, expected empty), pr2_cal.log ((PR2) probe calibration, 0/4 so far). Handover: handover/HANDOVER-stage3.md.

# ROUND 10 (start 20:35 UTC; budget ~90 min). Targets: (1) prove (PR2) in (+)_r e_r (x) P_r (exact over Q where it helps);
#  (2) T_1 route for non-split (5,2) lifts; (3) mixed patterns (1,1,..) with moments + (c1)-(c5) (check reg2's SP8); (4) deflation for S3-1.

## 30. ROUND 10: (PR2), its split variant, and what the normal forms give
 (A) TWO SUFFICIENT 4x5 STATEMENTS FOR (S3-a) [rigorous reductions].
   (PR2)       no 5-dim 4x5 level space without single-row elements has all four row projections of dim 2   [L_e is such a space].
   (PR2-split') no 5-dim 4x5 level space containing a 2-dim single-row part e_e (x) Z and NO single-row element in the other three rows [<< REFUTED r17: (PR3)/(PR2-split') are FALSE as stated -- explicit counterexample, sec. 37 (E); only (PR3') (all three row projections EXACTLY 2-dim) survives >>]
               has all row projections of dim <= 2.   [CORRECTED 21:02: without the clause on the other rows the statement is FALSE
               numerically -- the round-9 calibration hit of r9/pr2_search.py (seed 3, start 8: residual 6.3e-13, fresh-point error
               1.6e-12) has single-row dims (2,1,0,0) and row projections (2,2,2,2). This is exactly the shape of L_r in the MIXED
               pattern z = (2,1,..), which therefore is NOT closed by this route.]
     Why (PR2-split') suffices: in (S3-a), Lemma S3-1 gives L_r = X_re (+) e_e Z for every r in R, with pi_e(L_r) = Z and [<< REFUTED r17: (PR3)/(PR2-split') are FALSE as stated -- explicit counterexample, sec. 37 (E); only (PR3') (all three row projections EXACTLY 2-dim) survives >>]
     pi_s(L_r) = pi_s(X_re) inside P_s = pi_s(L_e) (s in R - r): so L_r (rows != r) is such a space -- for EVERY defect of L_e.
     Census (r9/rowproj5.py): the stored 5-dim 4x5 spaces with single-row dims (2,0,0,0) have row projections (2,2,2,3) or (3,3,3,3): none
     violates (PR2-split').  Structure: N = X (+) e_4 (x) Z with X a 3-dim 3x5 level space with rows in 2-planes, and N level <=>
     X level and Z orthogonal to 1, to the column sums c(x) and to the deletion vectors D_2(x)_j = sigma_2(x minus column j),
     D_3(x)_j = sigma_3(x minus column j) for all x in X. Z 2-dim forces ALL of c(X), D_2(X), D_3(X) into the 2-dim U' = (Z + C1)^perp.
 (B) NORMAL FORMS FOR (PR2): the incidence argument of section 16 needs only "L' 5-dim inside (+)_r e_r (x) P_r, no single-row element":
     m_kl in {1,2} for all six pairs (>= 1: 5 + 4 - 8; <= 2: else a single-row element), pairs with m = 2 disjoint, normal forms (t0)
     [0 / 1 triangle / collapsed], (t1), (t2). For (t2): L' = {(v + de w, phi v, u + de s, psi u)}, and "no single-row element" <=>
     phi, psi injective and w, s != 0.
     Identities for (t2) [rigorous, from the 3-row kernels X_d = {(v + de w, phi v, de s)}, X_b and the delta^0 parts of sigma_2, sigma_3]:
       s(s) = -s(w),  <w,s> = -s(w)^2,  <c(v), s> + <w, phi v> + s(w) s(v) = 0  (c(v) := v + phi v),  <c(w), s> = 0,
       Q(v) := 2 v o phi v + s(v)(v - phi v)  [= deletion vector of the 2-row element (v, phi v)]  is orthogonal to s and to c'(P_c);
       symmetric ones with (u, psi, s) <-> (v, phi, w);  c(P_a) orthogonal to c'(P_c).
 (C) EXACT ATTEMPT on (t2) (r10/gen_t2.py; 36 unknowns after the S_5 / GL_2 normalisation): one chart without injectivity ran 600 s in
     msolve (840 MB) without finishing; one chart with the injectivity minors did not finish in 100 s. Too heavy as it stands: the system
     must first be cut down by hand (the identities of (B)) or split into 3-row pieces.
 (D) NUMERICS: (PR2) probe r9/pr2_search.py: calibration (rank-2 hinge only) 1 all-2 solution in 21 starts (with single-row dims
     (2,1,0,0)); target (no single-row element) 0 of 48 starts converge (floors 1e-4 .. 1e-2). Weak evidence for (PR2).
 (E) X0 = Y_ab (+) Y_cd, THE 4-DIM CORE OF (t2), IN CLOSED FORM [rigorous; generating function, checked against a direct expansion].
     With Pi_A := prod_j (1 + t_a v_j + t_b (phi v)_j) = 1 + s(v)(t_a - t_b) mod squares (Y_ab level), likewise Pi_C, and
     1 + A_j + C_j = (1 + A_j)(1 + C_j)(1 - R_j), R_j = (A_j - 2 t_a t_b v_j phi_j)(C_j - 2 t_c t_d u_j psi_j), one gets: X0 is level iff
     Y_ab, Y_cd are level and for all v in P_a, u in P_c  (c(v) = v + phi v, Q(v) = 2 v o phi v + s(v)(v - phi v) = deletion vector of (v, phi v)):
       (X2) <c(v), c'(u)> = 0;      (X3) <Q(v), c'(u)> = 0 and <Q'(u), c(v)> = 0  (bidegrees (2,1), (1,2));
       (X4) -<Q(v), Q'(u)> + <v,u><phi v, psi u> + <v, psi u><phi v, u> - 2 <v o phi v, u o psi u> = 0.
     COUNT: a 2-dim 2x5 level space is a 2-dim isotropic subspace of a 9-dim nondegenerate quadric (sigma_2 on {sigma_1 = 0}): an
     11-dim family; X0 imposes 4 + 6 + 6 + 9 = 25 conditions on 22 parameters: expected dimension -3. Consistent with numerics:
     r10/t2_lm.py (full (t2) normal form): 0/32 converged with s != 0 forced, 0/32 with s = 0 allowed (floors >= 1e-4);
     r10/x0_lm.py (X0 alone): 0/3. (Uncalibrated: no level space of this shape is known.)
     Consequence of the closed form in the case dim c(P_a) = dim c'(P_c) = 2: c'(P_c) = c(P_a)^perp cap 1^perp and Q(P_a) inside c(P_a),
     Q'(P_c) inside c'(P_c) -- each a strong condition on a single 2-row space (6 conditions on the 11-dim family).
 (F) SP8 (reg2, verified) needs a 3-dim single-row part; in the (S3) regime z_i <= 5 - lam_{ri} <= 2, so SP8 does not shortcut any mixed
     pattern. Its lemma (Z3), C(L_i) inside Z_i^perp cap 1^perp, with Lemma S3-2 and verifyfl's SPLIT gives for the mixed patterns:
     e_r = 1 and z_i >= 1 for some i != r force C(L_r) = Z_i = C m with m ISOTROPIC. Not a contradiction by itself; the mixed patterns
     need the lam-pattern analysis of section 26 (A) (not started).
 (G) TWO NEW NECESSARY CONDITIONS / CHECKS [rigorous statement + numerical check, r10/s9_check.py].
     (G1) QUADRIC RANK. sigma_2 on V8 = (+)_r e_r (x) P_r is Q(x) = sum_{r<r'} x_r^T (J - I) x_r'; on H = ker sigma_1 (dim 7, or 8 if all
          P_r lie in 1^perp) Q = (1/2)(sum_r q(x_r) - <c,c>), q(y) = <y,y> - s(y)^2, c = sum_r x_r. A 5-dim level L' is totally Q-isotropic,
          so  rank(Q|H) <= 2 (dim H - 5)  (= 4 if dim H = 7): a condition on the four PLANES alone (generic planes: rank 7).
          Radical description: x in H is in rad(Q|H) iff x_r - c(x) - (s(x_r) + k) 1 is orthogonal to P_r for all r (one k).
     (G2) the known all-2 space clm_p4_d5_defect2_s9 (data accurate to ~1e-7) has rank(Q|H) = 2 (singular values 0.71, 0.71, then <= 1e-7)
          and VIOLATES (Q4) (a 4x4 subpermanent of size 0.40 on unit basis vectors): it is not an (S3-a) core candidate on two counts.
 (H) EXACT X0 CHART TIMING: r10/gen_x0.py chart 0_0_0 (34 variables): > 3 CPU-min, 0.9 GB and growing (final in r10/x0_one.log).
 (I) THE ROW-KERNEL FIRST-ORDER BOUND [rigorous; = the mechanism of reg2's R2-2(a)]. For ANY level L and row r, with L_r = L cap {row r = 0}
     and y_r := e_r 1^T - J/5:  perm(J + m + s y_r) = 120 (1 + 4s/5)(1 - s/5)^4 for m in L_r (row r of J + m + s y_r is (1 + 4s/5) 1, the other
     rows are (1 - s/5)(1 + m_i/(1 - s/5)), and L_r is a linear level space), so y_r lies in T_1(L_r); and sigma_2(y_r) = 6 (4/5) + 4 (-16/5) = -8,
     so y_r lies in no level space. As L lies in T_1(L_r):     dim L <= dim T_1(L_r) - 1.
     So a 9-dim level space with a_r = 1 needs a 5-dim 4x5 level space L_r with dim T_1(L_r) >= 10 (T_1 of L_r embedded with zero row r).
 (J) CENSUS of dim T_1 over the 51 stored 5-dim 4x5 level spaces [numerical, r10/t1_census5.py]: values 9 .. 13 (so no general obstruction);
     the two all-2 spaces of shape single-row (2,1,0,0) / row projections (2,2,2,2) found by the probes (r9/pr2_sol_3_8.npy, gap 2e-4/2e-14;
     r10/pr2split_sol_1_0.npy, gap 5e-6/2e-9) have dim T_1 = 9 EXACTLY ONE TOO FEW; T_1 of each is not level (errors 5 .. 50) and contains y_4.
     [SUPERSEDED 21:09 by (L): with more examples dim T_1 is 9 OR 10 for this shape; the sharper FO2_0 bound excludes all of them.]
     The non-split (5,2) spaces (row projections (2,2,4,4), (3,3,4,4)) have dim T_1 = 10, 11.
 (K) (PR2-split') PROBE [numerical, r10/pr2split_search.py: L' = X (+) e_d (x) Z forced]: calibration (no hinge on the other rows) 1 of 2
     starts converges to a (2,1,0,0)/(2,2,2,2) space; target (no single-row element in rows a,b,c) running (r10/pr2split_target.log).
STATUS 21:04: (PR2-split) corrected to (PR2-split'); row-kernel bound dim L <= dim T_1(L_r) - 1 recorded; (2,1,0,0) examples have T_1 = 9 (excluded as L_r); X0 exact chart still running.
 (L) FO2_0 CENSUS [numerical, r10/t1_census5.py, ext9_test.py]. Every level L containing N lies in T_1(N) and is totally isotropic for
     sigma_2 (= q_0/12 of FO2 at m = 0), so dim L <= FO2_0(N) := largest sigma_2-isotropic dimension in T_1(N) = (n - rk) + floor(rk/2)
     (n = dim T_1(N), rk = rank of sigma_2 on T_1(N)).  Over the 60 stored 5-dim 4x5 level spaces (rows' files + the 11 probe solutions
     of shape single-row (2,1,0,0) / row projections (2,2,2,2)): FO2_0 <= 8 for 58; = 9 only for clm_p4_d5_defect2_s9 (all-2, single-row
     (1,1,0,0)) and ncdef_d5_e2_k1_s1 (row projections (1,1,2,2)). The (2,1,0,0)/(2,2,2,2) spaces: dim T_1 = 9 (6 of them) or 10 (5), and
     FO2_0 = 7 (10 of them) or 8 (1) [sigma_2 on T_1 has rank 5 when dim T_1 = 10]. So NONE of the known spaces of the (2,1,..)-L_r shape
     lies in a 9-dim level space, and none of the non-split (5,2) spaces (FO2_0 = 7, 8) can be the L_e of one. [Corrects (J).]
     Next step for the two FO2_0 = 9 spaces: the full FO2 (all q_m, m in N), r9-style, as in verify2/fo2lib.py.
STATUS 21:08: (J) corrected by (L): FO2_0 census, 58/60 known 5-dim 4x5 spaces <= 8 (s9 and ncdef_d5_e2_k1_s1 give 9); all (2,1,0,0)-shape examples excluded as L_r.
 (M) FULL FO2 on the two FO2_0 = 9 spaces [numerical, verify2/fo2lib.fo2 with a random combination of 6 forms q_m, two seeds; r10/fo2_two.py]:
     clm_p4_d5_defect2_s9: dim T_1 11, rank 6, FO2 bound 8 -> excluded as L_r of a 9-dim level space.  pr2split_sol_7_13: bound 8.
     ncdef_d5_e2_k1_s1 (row projections (1,1,2,2), single-row (1,1,0,0)): dim T_1 13, rank 8, FO2 bound 9 -- the ONLY stored 5-dim 4x5 level
     space that first/second order do not exclude as L_r of a 9-dim level space. Next: the common isotropic subspaces of ALL q_m (not one
     combination), or seeded extension N (+) (4-dim) inside T_1(N) (an 8-parameter Grassmannian search -- small).
STATUS 21:10: round 10 final. Background (end by ~21:30, logs in stage3/r10): pr2split_target.log, pr2split_cal.log. Handover addendum written.

# ROUND 11 (start 21:12 UTC; budget ~90 min). Targets: (1) ncdef_d5_e2_k1_s1 (the only stored 5-dim 4x5 space with FO2 bound 9):
#  polish, common isotropic subspaces of all q_m on T_1/N, structured search for a 4-dim complement; exclude rigorously or report a 9-dim
#  space at once; (2) (PR2-split') via the 3-row reduction; (3) (2,1,..) FO2_0 <= 8 by classification; (4) (t2) exactly (dim c(P_a) split).

## 31. ROUND 11: the exceptional space ncdef_d5_e2_k1_s1 -- an explicit family, its T_1 jump locus, and its (non-)extension
 (A) STRUCTURE [rigorous]. ncdef_d5_e2_k1_s1 (rows' file; level error 3e-12, row projections (1,1,2,2)) is a member of
       N(w2,w3) = F_4 (+) C e_2 w2^T (+) C e_3 w3^T,  F_4 = {c (x) e_0 : c on rows 0..3, sum c = 0} (column 0, four rows),
       w2, w3 in V0 = {w : w_0 = 0, sum w = 0}.
     MOMENT PROOF: for x = c (x) e_0 + al e_2 w2^T + be e_3 w3^T, prod_j (1 + <t, x_.j>) = (1 + sum_r c_r t_r)(1 - al be <w2,w3> t_2 t_3) mod
     squares, so N(w2,w3) is level iff <w2,w3> = 0. A 3-dim (projective) family; the stored member has w2 close to (not equal to) e_4 - e_1.
 (B) T_1 JUMP LOCUS [numerical, r11/ncdef_locus.py, ncdef_hyper.py, ncdef_inv.py]. Generic member: dim T_1 = 10, forms q_m span 2 dims on
     T_1/N (dim 5), a single q_m has rank 5: FO2 bound 7. dim T_1 = 13 exactly on
       H = { w2 o w3 in span(w2, w3) }  [columnwise: the points (w2_j, w3_j) lie on one hyperbola (x - mu)(y - la) = la mu through 0; then
            <w2,w3> = 0 is automatic], containing all w2 = e_a - e_b (two-column, w3 ⊥ w2), and on D = { w2 = w3 isotropic };
     the stored member lies on H (rank [w2, w3, w2 o w3] = 2, third singular value 0). So the FO2 bound 9 of round 10 is a property of H.
 (C) EXTENSION TEST ON H [numerical, calibrated; r11/ncdef_cone.py]. On V = T_1/N (dim 8) the forms q_m (m in N) span 11 dims. A 9-dim
     level L containing N needs a 4-dim subspace of V isotropic for ALL q_m, i.e. a P^3 inside the common null cone K (P^7); an 8-dim
     one needs a P^2. CALIBRATION: the image of the 7-dim lift L(N) in V is a 2-dim common isotropic subspace (|form| <= 7e-13).
     Results (LM on K, Jacobian rank at each point = 7 - tangent dim):  stored member: 12/12 points with tangent dim 1 or 2;
     three random members of H: 8/8 points each with tangent dim 1.  So K has dimension <= 2 near every point found (<= 1 for generic H):
     NO 9-dim extension (and for generic H not even 8-dim), numerically.  (Two bugs found and fixed on the way: conjugated basis of the
     form span -- rows of vh, not vh.conj(); QR on a rank-deficient coordinate matrix -- use SVD.)
 (D) EXACT CERTIFICATES ON H [exact over Q; r11/ncdef_exact.py, ncdef_exact2.py, plane_check.py; Singular std / minAssGTZ].
     Members (all on H, rational):  H0: w2 = e4 - e1, w3 = (0,1,1,-3,1) (two-column);  H1: w2 = (0,10,15,-30,5), w3 = (0,-3,-2,-1,6);
     H2: w2 = (0,35,-35,-5,5), w3 = (0,-3,-2,-1,6)  [H1, H2: four distinct nonzero entries; found by r11/find_ratH.py].
     For each: N(w2,w3) exactly level (perm(J+m) = 120 at 30 integer points, and by (A)); T' := null space of the cofactor conditions at 160
     integer points of N (contains T_1(N)): dim 13; V = T'/N (dim 8); the forms q_m (Hessians at 45 integer points m of N) span 8 (H0) resp.
     11 (H1, H2) dims; the common null cone K (homogeneous ideal of these forms; fewer forms only ENLARGE K, so the bound is safe):
       Krull dim 3, i.e. K is a projective SURFACE;  minAssGTZ over Q: exactly 5 components, each = {4 linear forms, one quadric} = a quadric
       surface in a P^3 whose quadric has RANK 3 on that P^3 -> absolutely irreducible of degree 2 -> contains NO plane.
     Since a level L containing N lies in T_1(N) inside T', and L/N maps injectively onto a common isotropic subspace (N is in the radical of
     every q_m on T_1(N); for t = n + v with v in the complement, v lies in T_1 and q_m(t) = q_m(v)), a 3-dim L/N would be a plane in K:
       THEOREM (exact, three members): every level space containing N(w2,w3) for H0, H1, H2 has dim <= 7.
     (A 4-dim L/N -- a 9-dim L -- would need a P^3 in K, already excluded by Krull dim 3.)
 (E) STATUS OF THE EXCEPTIONAL SPACE. The stored ncdef_d5_e2_k1_s1 is an irrational member of H (numerically): no 9-dim extension
     (calibrated null-cone LM, all tangent dims <= 2); exact for three rational members of the same locus (dim <= 7); generic members of
     the family: dim T_1 = 10, FO2 <= 7 (numerical); D (w2 = w3 isotropic): null cone a curve (numerical). Missing for a full proof: the
     whole family (parametric T_1 and K over H, D and the generic stratum). NO 9-dim (or 8-dim) level space found anywhere.
STATUS 21:28: target 1: ncdef = explicit family N(w2,w3); T_1 jump locus H found; EXACT: three rational H members lie in no level space of dim >= 8; stored member numerically excluded.
 (F) LEMMA PFC (partial free column) [rigorous reduction; same mechanism as the proof of Theorem FL]. Let L be a level space containing a
     free column on four rows, F = {c (x) e_j : c_i = 0, sum c = 0} (column j, all rows but i). Then L^T has the single-row part
     Z_j(L^T) >= U = {w : w_i = 0, sum w = 0} (3-dim). If Z_j = 1^perp, Theorem FL gives dim L <= 7. Otherwise, by (Z3) (reg2 5.1(a), verified)
     the 4x5 level space (L^T)_j has defect inside U^perp cap 1^perp = C m_0, m_0 = 1 - 5 e_i ~ (1,1,1,1,-4); defect 0 is impossible for
     dim >= 4 (Lemma SL), and dim (L^T)_j = dim L - dim pi^j(L) >= dim L - 4 (FK). Hence
         dim L >= 9  ==>  there is a (5,1) space (4x5, dim 5) with defect line C (1,1,1,1,-4).
     So "no (5,1) space with defect line C(1,1,1,1,-4)" (one specific, S_4-symmetric, NON-isotropic line with |supp| = 5 -- verifyfl's open
     stratum (o1)/(o2), DI5-R4) implies: every level space containing a partial free column on four rows has dim <= 8. This would exclude the
     WHOLE ncdef family N(w2,w3) (it contains F_4 in column 0 on rows 0..3) and also the domino branch of configuration (II) (sec. 11, 13).
     Proposed: verifyfl's [DC3]/[T22]/[T31] systems + principal stratum for m = (1,1,1,1,-4) (gen_dc handles |supp m| = 4, 5).
STATUS 21:30: Lemma PFC: partial free column => dim <= 8 unless a (5,1) space with defect line (1,1,1,1,-4) exists (reduces the ncdef family to one verifyfl-type (5,1)_m case).
STATUS 21:32: RESULT ROUND 11 written; COMPUTE items 10, 11 added.
 (G) (PR2-split') AS A 3-ROW STATEMENT [rigorous equivalence + numerics, r11/pr3_search.py]. With N = X (+) e_4 (x) Z: N is level iff X is
     level and Z is orthogonal to 1 and to the 3-row deletion vectors c(x), D_2(x), D_3(x) (all in 1^perp, 4-dim). So (PR2-split') <=>
       (PR3) every 3-dim 3x5 level space X with all rows in 2-planes and no single-row element has 3-row defect >= 3 [<< REFUTED r17: (PR3)/(PR2-split') are FALSE as stated -- explicit counterexample, sec. 37 (E); only (PR3') (all three row projections EXACTLY 2-dim) survives >>]
     (a 2-dim Z needs defect <= 2). [Corrects the round-11 wording "defect 3": the maximum is 4.] Numerics: 4/4 converged solutions of the
     unconstrained (rows-in-planes, no single-row) problem have defect 4 (generic stratum); the forced-Z probes (r10/pr2split_search.py,
     queued S3-PR2probe) found no defect <= 2 in 135 starts. (PR3) has ~31 unknowns with equations of degree <= 3: a candidate for an exact run.
 (H) (5,1)_{m0} PROBE [numerical, r11/m0_search.py: rows' defect-mode LM with the defect line FIXED]: calibration with the defect line of a
     known (4,1) space: 2/2 hits (residual 5e-14). m0 = (1,1,1,1,-4): D = 5: 0/1; D = 4: 0/4 (floors ~3). A (5,1)_{m0} space would contain a
     (4,1)_{m0} space (SL), so D = 4 is the sharper test; random lines at D = 4 running (r11/rand_d4.log) to see whether m0 is special.
     If no (4,1) space has defect line C m0, Lemma PFC improves to dim L <= 7 (as Theorem FL).
     UPDATE (H), 21:40: m0 at D = 4: 0/14 (best residual 2.6). Random line: 0/1 (5.9). But the calibration is LINE-DEPENDENT and weak:
     defect lines of six different known (4,1) spaces gave 2/2, 0/2, 1/2, 0/2, 0/2, 0/2 (floors up to 6). So the m0 negative is INCONCLUSIVE.
     Reformulation for an exact attack: L' has defect line C m0 iff for every Y in L' the four 4x4 permanents of J + Y with column 0, 1, 2 or 3
     deleted are EQUAL (expand the lift perm(J + (Y; u)) along the partial free row u in {u_4 = 0, sum u = 0}); with level, 4 f_0 + f_4 = 120.
     Known 7-dim spaces (16 lifts): none contains a partial free row or column (their 3-dim single-row parts are (Cm + C1)^perp with m not of
     type (1,1,1,1,-4); r11/pfc_known.py).
 (I) QUEUED PROBES (coordinator, 21:40): (PR2) 0/133, (PR2-split') 0/155 target starts.
STATUS 21:39: round 11 final. Running (mine, end by ~21:55): r11/m0_d4.log. Handover addendum written.

# ROUND 12 (start 21:42 UTC). Target 1: [T31] split A for m0 = (1,1,1,1,-4) (verifyfl R8.8 did split B): normal form for Z.
STATUS 21:42: read verifyfl R4, R7, R8 (R8.8 = [T31-B] for m0 by hand; [DC3] p5b running; [T22] via gen_n3g); BRIEF U12 memory rule.

## 32. ROUND 12: [T31] split A for m0 = (1,1,1,1,-4) -- normal form for verifyfl (their R8.8 did split B)
 Setting (verifyfl R7.1, R8): K 4-dim column-centred, defect in C m0, type (3,1): s(K) = V, K cap ker s = C Z, Z doubly centred, and split A:
 vartheta(Z) = 0, i.e. all five columns z_j of Z isotropic (in V, 3-dim nondegenerate), sum_j z_j = 0. b_j := 2 y_j - s. Tool (C2'pol):
 <b_j(Y), b_j(Y')> = <s,s'> + 4 m_j Theta(Y,Y'); with Y' = Z (s(Z) = 0, b_j(Z) = 2 z_j):  <b_j(Y), z_j> = 2 m_j l(Y), l := Theta(., Z), l(Z) = 0.
 (A) LEMMA SA1 [rigorous]. If l == 0 on K, then for every j with z_j != 0, b_j(K) lies in E_j := z_j^perp cap V, a DEGENERATE plane (radical
     C z_j), so b_j^* g = s^* g + 4 m_j vartheta has rank <= 1; two nonzero columns j, k with m_j != m_k would make (m_k - m_j) s^*g =
     m_k b_j^*g - m_j b_k^*g of rank <= 2, but s^*g has rank 3 (s(K) = V). Hence l == 0 forces z_4 = 0 (the only column with m = -4; z_4 alone
     cannot be nonzero since sum z_j = 0). Conversely ANY zero column c of Z gives l == 0 (<b_c, z_c> = 0 = 2 m_c l, and m0 has full support).
     So split A for m0 splits into exactly two cases:
       (alpha) z_4 = 0 (Z = [W | 0], W 4x4 doubly centred with isotropic columns) and l == 0 on K;
       (beta)  all five columns nonzero and l != 0.
     [This contains verifyfl's R8.2(ii) argument for Z = v(e_a - e_b)^T with 4 in {a,b}; for {a,b} in {0..3} that Z is in (alpha).]
 (B) THE SPLIT-A Z-FAMILY [numerical, r12/zfam.py; LM on P^11 with the line conditions of C Z]: 55 starts, every solution has a ZERO column:
     rank 3 with exactly one zero column (any position; local dim 2) or rank 1 on two columns (chi_1-type v (e_a - e_b)^T). Combined with SA1
     only (alpha) survives if (beta) is empty; Lemma SA1 also kills the rank-3 Z with zero column c in {0..3}.  (beta) = "no Z in the family
     with all columns nonzero": exact Z-only system r12/zbeta.py (12 coordinates, 243 charts) -- first chart > 90 s in msolve, running longer.
 (C) NORMAL FORMS FOR THE SYSTEMS [rigorous derivations].
     (alpha): l == 0 gives the LINEAR relations <b_j(Y), z_j> = 0 for all j, Y; with K' a complement of C Z, b_j = A_j s on K':
       A_j^* z_j = 0 (j = 0..3), A_j^*A_j = P_1 := 1 + 4 Psi (j = 0..3), A_4^*A_4 = 5 - 4 P_1, sum A_j = -3, and P_1 has RANK <= 1
       (from (A): the pulled-back form of b_j, j with z_j != 0, has rank <= 1). If P_1 = 0, A_j(V) lies in C z_j for j in supp W.
     (beta): H := ker l (3-dim, contains Z): b_j(H) inside E_j for all j; rho := b_j^*g|H (j = 0..3) and rho_4 := b_4^*g|H have rank <= 1,
       s^*g|H = (4 rho + rho_4)/5; writing E_j = C z_j (+) C w_j with <w_j,w_j> = 1: b_j(Y) = mu_j(Y) z_j + alpha(Y) w_j (j <= 3),
       b_4(Y) = mu_4(Y) z_4 + beta(Y) w_4 on H, alpha(Z) = beta(Z) = 0, mu_j(Z) = 2, and sum_j b_j = -3 s.
 (D) CASE (beta), FIRST HALF [rigorous + exact]. Parametrise the isotropic cone of V by z = u^2 chi_1 + 2uv chi_2 - 2v^2 chi_3 (chi_k = (1,i^k,
     i^2k,i^3k); <x,x> = 4b^2 + 8ac in the chi-coordinates (a,b,c)); with z_j <-> (u_j,v_j), sum_j z_j = 0 <=> sum u_j^2 = sum u_jv_j = sum v_j^2 = 0,
     i.e. U = (u_j), V = (v_j) span a TOTALLY ISOTROPIC subspace of C^5. Either (beta-2) U, V independent (a maximal isotropic plane), or
     (beta-1) V = k U: Z = w l^T of rank one (w isotropic, l_j = u_j^2 all != 0, sum l = 0).
     (beta-1) IS IMPOSSIBLE. Rank-one expansion perm(J_4 + t w l'^T) = sum_k (4-k)! k! t^k e_k(w) e_k(l'), e_1(w) = e_2(w) = 0:
       e_3(w) = 0: then e_4(w) != 0 and (prod_{k != j} l_k)_j ~ m0 forces l_0 = .. = l_3 = a, l_4 = -a/4, sum l != 0.
       e_3(w) != 0: the degree-4 condition forces e_4(w) = 0 (else the same contradiction), so w is of iso type (0, z, z w, z w^2); the degree-3
       condition reads e_3(l^(j)) = e_3 - l_j e_2 - l_j^3 = k m0_j; summing, 2 e_3(l) = 0; k = 0 gives l_j = +-sigma (five terms, sum 0:
       impossible); k != 0: l_0..l_3 roots of x^3 + e_2 x + k, l_4 root of x^3 + e_2 x - 4k, with sum l = 0, e_3(l) = 0: UNIT IDEAL over Q
       (Singular std, r12/beta1.sing, with Rabinowitsch k prod l_j != 0).
     So (beta) = (beta-2) only: five nonzero isotropic columns whose (u,v)-coordinates span a maximal isotropic plane of C^5 (OG(2,5) = P^3).
     Exact attempts on the full (beta) charts (r12/zbeta.py in Z-coordinates; r12/zbeta_uv.py in (u,v)): msolve > 90 s / segfault (930 MB),
     Singular > 3 min (630 MB): too heavy unreduced. Calibrated numerical test (r12/zfam2.py, hinges on the nonzero columns) running.
 (E) CASE (alpha) NORMAL FORM [rigorous]. Z = [W | 0], l == 0, A_j^* z_j = 0, A_j^*A_j = P_1 (j = 0..3) of rank <= 1, A_4^*A_4 = 5 - 4 P_1,
     sum A_j = -3. Sub-case P_1 = 0: A_j = n_j (x) phi_j (rank <= 1, isotropic image; n_j ~ z_j for j in supp W), so on K'
       y_j = (s + <phi_j,s> n_j)/2 (j <= 3),  y_4 = -s - (1/2) sum_j <phi_j,s> n_j;
     the phi_j must SPAN V: otherwise some s != 0 has <phi_j,s> = 0 for all j and Y_s = (s/2)(1,1,1,1,-2)^T is a rank-one element with defect in
     C m0, which verifyfl's exact identity (R8.8: t^k-coefficients -6 e_2, -12 e_3, -(21/2) e_4 of C_4 + 4 C_0) forbids. The gauge
     Y_s -> Y_s + <lam,s> Z shifts all phi_j (j in supp W) by 2 lam. Sub-case rank P_1 = 1: A_j (j <= 3) of rank <= 2 with degenerate image.
     These two sub-cases are SMALL explicit systems (W: 9 parameters with 4 isotropy quadrics; phi_j: 12; n_j for zero columns) -- the
     equal-entries normal form for verifyfl's [T31] split A.
 (F) NUMERICAL TEST OF (beta) [r12/zfam2.py: Z-family LM with Rabinowitsch hinges forcing chosen columns nonzero]. CALIBRATION (columns 0..3
     forced nonzero, column 4 free): 3/20 starts converge, all rank 3 with column 4 = 0 (exactly the (alpha) shape, residual <= 2e-14).
     Second calibration (columns 0,1,2,4 forced, column 3 free): 8/40, all rank 3 with column 3 = 0.
     TARGET (all five columns forced nonzero): 0/190 (seeds 6, 8: 40 + 150 starts). Strong numerical evidence that (beta) is EMPTY.
STATUS 22:00: sec. 32 written (Lemma SA1, beta-1 excluded exactly, alpha/beta-2 normal forms, COMPUTE item 12); larger beta numerics running.
STATUS 22:04: round 12 final. (beta) numerics 0/190 vs calibrations 3/20, 8/40. No jobs of mine running.

# ROUND 13 (start 22:07 UTC). Targets: (1) (beta-2) empty by hand via z_j = c_j w(t_j); (2) (alpha0) by hand; (3) (PR3) exactly.
STATUS 22:07: started; checking the closed forms of <,>, tau, q4 in the conic coordinates (t, lambda).

## 33. ROUND 13: conic coordinates; (beta-2) needs both blocks; (alpha0) reduced to finitely many tiny systems (Lemma S-SPEC)
 (A) CONIC COORDINATES [rigorous; numerically checked, r13/conic_check.py]. Isotropic columns z = l w(t), w(t) = chi_1 + 2t chi_2 - 2t^2 chi_3:
       <z_a,z_b> = -8 l_a l_b (t_a - t_b)^2;  tau(z_a z_b z_c) = 8 l_a l_b l_c [e_1 + 4 e_2 e_3](t_a,t_b,t_c);
       q4 = 4 prod l [1 + 16 e_4 + 16 e_4^2 + 4 e_2(t^2) - 8 sum_l t_l^2 e_2(t without l)];  perm(W) = sum of the 3 pairings - 6 q4 (columns in V).
     All rational: the line conditions of the split-A Z-family are a system over Q in (t, l). WLOG all t_j finite: the S_4-orbit of the
     point t = infinity (the line C chi_3) has 6 points (stabiliser = the 4 cyclic row shifts), more than the 5 columns.
 (B) (beta-2) [numerical]: moments + degree-3 conditions alone: 12/12 solutions (all l != 0, distinct t); moments + degree-4 alone: 10/12.
     So no single-block identity exists; the contradiction (expected dim 6 - 8 = -2) needs both blocks. Exact unreduced run over Q
     (r13/beta_t.sing, 10 variables, degree 12): > 10 min, 770 MB, stopped. Left to verifyfl (COMPUTE item 12).
 (C) (alpha) STRUCTURE [rigorous + exact]. z_4 = 0 makes T_4 = sum_j T_j = 4T = -4T: ALL FOUR triple moments of W vanish and perm(W) = 0;
     in conic coordinates g(t_a,t_b,t_c) = 0 (g = e_1 + 4 e_2 e_3) for the four triples: minAssGTZ (r13/walpha.sing) = one 2-dim component
     + isolated points; with perm(W) = 0 the (alpha) W-family is at most a curve.  |supp W| = 3: W = v l^T with e_3(v) = 0, i.e. v SPECIAL
     (rank-one expansion: the e_3-vector (0,0,0,l_0l_1l_2,l_0l_1l_2) is not ~ m0); |supp W| = 2: W = v (e_a - e_b)^T, v isotropic.
 (D) (alpha0) REDUCTION TO SHAPE S [rigorous]. With n_j = z_j on supp W and the gauge element mu Z, for EVERY support there is s != 0 with
       Y_s + mu Z = (s/2) (x) (1,1,1,1,-2)^T + b (x) (e_k - e_4)^T,   b isotropic  ("shape S"):
     |supp| = 4: <phi_0,s> = <phi_1,s> = <phi_2,s>, mu = -<phi_0,s>/2, b = delta z_3 (uses sum_{j<=3} z_j = 0); |supp| = 3: same on the support,
     b = (c_k/2) n_k for the column k outside; |supp| = 2 = {a,b}: <phi_a,s> = <phi_b,s> and <phi_j,s> = 0 for one more column, b = (c_k/2) n_k.
     b = 0 would leave a rank-one element (R8.8's identity) -> b != 0.
 (E) LEMMA S-SPEC [exact over Q, r13/shapeS*.sing]: if a shape-S element (a = s/2 in V nonzero, b in V isotropic) has its line's defect in C m0,
     then p_3(b) = 0, i.e. b lies on one of the 6 SPECIAL isotropic lines (row permutations of chi_1). [Charts a_i = 1, i = 0,1,2: the line
     conditions alone are 0-dimensional (36 solutions, all with b special); with 1 - u p_3(b) added: UNIT on all three charts.]
 (F) CONSEQUENCES for (alpha0): |supp W| = 4: b = delta z_3 with delta != 0, and by the choice of the triple every column of W is SPECIAL;
     enumeration (r13/special_W.py): the only W with four special columns, sum 0, tau = 0, perm = 0 use 4 special lines omitting an opposite
     pair (lambda = (+-1, +-i)); the octahedral action of the row S_4 on the 6 lines is transitive on the 3 opposite pairs and S_4 on columns
     0..3 preserves m0 -> ONE W up to symmetry and scale. |supp W| = 3: v special and n_k special; |supp| = 2: n_j, n_k special. So every
     (alpha0) case is a small exact system with finitely many discrete choices (W or v from the 6 lines, n_k from the 6 lines) plus phi's.
     The |supp| = 4 system (9 unknowns phi_1..phi_3 over Q(i)) is running: r13/alpha0_W4.sing.
 (G) THEOREM (alpha0), |supp W| = 4 [hand reduction (D)-(F) + exact over Q(i)]: impossible. Completeness of the W list: four DISTINCT special
     lines span V (a plane meets the conic in <= 2 points), so the kernel of sum l_j v_j = 0 is a line and the enumeration is exhaustive;
     repetition patterns (p,p,q,r) force two l_j = 0; (p,p,p,q) forces l = 0; (p,p,p,p) = rank-one W with 4-support is excluded by the
     e_3 / e_4 vectors (not ~ m0); (p,p,q,q): W = [a v, -a v, b w, -b w] needs tau(v,v,w) = tau(v,w,w) = 0 and <v,w>^2 = 3 sum v_r^2 w_r^2 --
     no pair of special lines satisfies this (exact). For the three surviving W (lines omitting an opposite pair; all three run, no symmetry
     argument needed), the system "K = {Y_s + mu Z}, y_j = (s + <phi_j,s> z_j)/2, y_4 = -s - (1/2) sum <phi_j,s> z_j, phi_0 = 0, all defect
     coefficients in (s, mu)" (9 unknowns phi_1..phi_3, 218 equations) is the UNIT IDEAL over Q(i) (Singular std; r13/alpha0_W4n_*.sing).
STATUS 22:25: (alpha0) |supp W| = 4 EXCLUDED (hand reduction to one W + exact over Q(i)); Lemma S-SPEC exact; doing |supp| = 3, 2.
 (H) (alpha0), |supp W| = 3 [hand reduction + exact over Q(i), r13/alpha0_small.py s3]: W = v (1, l_1, -1-l_1, 0, 0) (WLOG supp {0,1,2}) with v
     special ((C)), A_3 = n_3 (x) phi_3 with n_3 special (shape S with c_3 != 0, else rank-one) -- all 6 x 6 choices of (v, n_3) run without
     symmetry reduction; unknowns l_1 (Rabinowitsch l_1 (1 + l_1) != 0), phi_1, phi_2, phi_3 (phi_0 = 0): ALL 36 systems UNIT.
     CALIBRATION of the generator: the |supp| = 4 system truncated to the t^{<=2} coefficients is NON-unit (dim 3), so the unit verdicts use
     the degree-3/4 conditions (r13/alpha0_W4_cal2.sing).
 (I) (alpha1) (rank P_1 = 1, P_1 = k f (x) f): on f^perp the elements Y_s have the (alpha0) form (A_j = z_j (x) psi_j + u_j (x) f, <u_j,z_j> = 0),
     but the shape-S construction needs two linear conditions on s inside the 2-dim f^perp: one dimension short. Left to verifyfl's system.
STATUS 22:29: (alpha0) |supp| = 4 and 3 EXCLUDED (exact over Q(i), calibrated); |supp| = 2 batch running.
 (J) (alpha0), |supp W| = 2 [hand reduction + exact over Q(i), r13/alpha0_P2.py]: W = v (e_0 - e_1)^T (WLOG {0,1}); for s in
     S_2 = {<phi_0 - phi_1, s> = 0} (dim >= 2) the element Y(s) = Y_s + mu(s) Z, mu(s) = -<phi_0,s>/2, has columns 0, 1 equal to s/2 and column 4
     free of v, so K contains the PLANE P2 = {(s/2)(1,1,1,1,-2) + (c_2(s)/2) n_2 (e_2 - e_4) + (c_3(s)/2) n_3 (e_3 - e_4) : s in S_2} (v drops out).
     n_2, n_3 special by S-SPEC applied inside P2 (c_2 == c_3 == 0 gives rank-one elements; c_2 == 0 makes n_2 irrelevant), n_2 = SPEC[0]
     WLOG (row S_4 transitive on the special lines). System: S_2 in the 3 Gr(2,V) charts, c_2, c_3 linear on S_2 (6 unknowns), all six n_3:
     ALL 18 systems UNIT.
 THEOREM (alpha0) [hand reductions (D)-(J) + exact computations over Q(i), calibrated; NOT yet verified]: case (alpha0) of [T31] split A
     for m0 = (1,1,1,1,-4) is impossible. Remaining for split A: (alpha1) (rank P_1 = 1) and (beta-2) -- with verifyfl.
STATUS 22:33: THEOREM (alpha0) for m0 (all supports excluded, exact over Q(i)). Left in split A: (alpha1), (beta-2).
STATUS 22:34: round 13 final. No jobs of mine running.

# ROUND 14 (start 22:34 UTC). Targets: (1) check verifyfl's (beta) chart cover vs (beta-2); (2) (alpha1); (3) (PR3).
STATUS 22:34: started; reading NOTES-verifyfl R9 and its m0 scripts.

## 34. ROUND 14: verifyfl's (beta) covers (beta-2); (alpha1)
 (A) CHECK OF verifyfl R9.4(b) against my (beta-2) [audit of verifyfl/exact/gen_m0a.py build_beta]: columns z_j = c_j w(t_j) or c_j chi_3 (t = inf;
     every nonzero isotropic vector of V is uniquely of one of these forms), all 32 subsets INF of columns at infinity, sum z_j = 0 as the three
     linear chi-coordinate equations, c_0 = 1 (c_0 != 0 in (beta)), u prod_{j>=1} c_j = 1 (all columns nonzero), and the line conditions as
     R_i(xZ) = sum_j W_ij (C_j(xZ) - 24) with W a basis of m0^perp (so the constant term is handled correctly, unlike my first draft in sec. 32).
     This is EXACTLY case (beta) (all five columns nonzero), containing (beta-1) and (beta-2). verifyfl: UNIT in all 32 charts at p = 2147483629.
     STATUS: [modular]; it is a char-0 proof via verifyfl's Lemma RED-p as soon as ALL pieces of the (SL_m0) case split are decided at the same
     prime (types via [DC3]/[T22], [T31-B] by hand (valid for p not in {2,3,5,7}), split A via my Lemma SA1 (valid for p > 5: uses m-values 1 and
     -4 distinct, char != 2), (beta) and verifyfl's (alpha) charts, which cover (alpha0) and (alpha1) together). My (alpha0) proof (sec. 33) is
     char 0 (exact over Q(i)) -- an independent confirmation of that part, not a piece of the mod-p cover.
STATUS 22:36: (beta-2) covered by verifyfl's (beta) run [modular, RED-p]; working on (alpha1).
 (B) (alpha0) AT P1 = 2147483629 (for verifyfl's Lemma RED-p cover; r14/to_modp.py converts every stage3 script to char P1, i -> 1518275076;
     r14/run_modp.sh, results r14/modp_results.log): Lemma S-SPEC UNIT 3/3 charts (calibration: line conditions alone 0-dim non-unit 3/3);
     |supp W| = 4: the three W systems UNIT 3/3 (calibration: degree-<=2 truncation non-unit, dim 3); |supp W| = 3: 36/36 UNIT;
     |supp W| = 2: plane systems P2 18/18 UNIT (NEW calibration: degree-<=2 truncation of a P2 system non-unit, dim 3, in char 0 and at P1).
     Special-W enumeration EXACTLY over F_P1 (r14/special_W_modp.py): 72 ordered 4-tuples = 3 sets of four special lines omitting one pair,
     (p,p,q,q) survivors 0 -- identical to char 0, so the converted W4 systems cover all cases at P1.
     => (alpha0) is UNIT AT P1 as well as in char 0.
 (C) |supp W| = 3 BY HAND AT THE QUADRATIC LEVEL [rigorous; explains why its degree-<=2 truncation is already unit, r14/s3_cal2.sing]:
     A_j = l_j v (x) phi_j (j <= 2), A_3 = n_3 (x) phi_3, so A_4 = -3 - v (x) Phi - n_3 (x) phi_3 (Phi = sum l_j phi_j), v, n_3 isotropic, and P_1 = 0
     requires A_4^*A_4 = 5. If v || n_3 a rank-<=2 operator would equal -4 Id. Otherwise c = <v,n_3> != 0, w spans span(v,n_3)^perp (non-isotropic);
     with al = <Phi,v>, be = <Phi,n_3>, ga = <phi_3,v>, de = <phi_3,n_3>, p = <Phi,w>, q = <phi_3,w>, the identity evaluated on (v,v), (n,n), (v,n),
     (w,w), (w,v), (w,n) gives ga(3+al) = 0, be(3+de) = 0, 4 + 3al + 3de + be ga + al de = 0, pq = -2<w,w>/c != 0, q(3+al) + ga p = 0, p(3+de) + be q = 0;
     all four branches of the first two equations contradict the rest. (Needs only v, n_3 isotropic -- not that they are special.)
 COMBINATION RULE (as asked by verify2/coordinator): verifyfl's (beta) verdict (32/32 unit at P1, with the open condition u prod c_j = 1) proves
     (beta) -- hence (beta-2) -- in characteristic 0 ONLY through Lemma RED-p for the closed split-A variety, i.e. once ALL of (alpha) is unit
     at the same P1. (alpha0) is now unit at P1 (this section); what remains is (alpha1) at P1 (verifyfl's (alpha) charts cover it).
STATUS 22:44: (alpha0) unit at P1 (all pieces), combination rule stated; supp-3 quadratic hand proof; back to (alpha1).
 (D) (alpha1) STRUCTURE [rigorous]. P_1 = A_j^*A_j = k f (x) f (k != 0) for j <= 3, A_4^*A_4 = 5 - 4k f (x) f, sum A_j = -3, A_j^* z_j = 0. For each j <= 3:
     A_j = n_j (x) psi_j + u_j (x) f with n_j isotropic, <u_j,n_j> = 0, <u_j,u_j> = k; n_j || z_j for j in supp W (two orthogonal isotropic vectors are
     parallel). [A_j(V) carries a form of rank 1, so it is a non-isotropic line (psi_j = 0) or a degenerate plane with radical C n_j, and
     A_j(f^perp) lies in that radical.] Polarised (C2') on K': Theta(s,s') = (k <f,s><f,s'> - <s,s'>)/4.
     On f^perp the elements have the (alpha0) form y_j = (s + <psi_j,s> n_j)/2; for s in f^perp with <psi_0,s> = <psi_1,s> one gets
       Y(s) + mu Z = (s/2)(1,1,1,1,-2) + delta_2 z_2 (e_2 - e_4) + delta_3 z_3 (e_3 - e_4)   ("shape S2", b's along columns of W)  [|supp| = 4],
     and analogous S2 elements for smaller supports. The S2 line-condition variety is much larger than shape S (exact dimension runs > 2.5 min,
     r14/shapeS2*.sing running) -- no S-SPEC analogue yet.
 (E) CUTS FOR verifyfl's FAILING (alpha) CHARTS (valid in all of (alpha), any char p > 5): rank-one W = v l^T with |supp l| = 3 forces v SPECIAL
     (Z-family: the e_3-vector (0,0,0,l_0l_1l_2,l_0l_1l_2) is not ~ m0, so e_3(v) = 0) -> the chart "v = w(t)" can be replaced by v = SPEC[0]
     (row symmetry) when l has three nonzero entries; |supp W| = 4: W satisfies g(t_a,t_b,t_c) = 0 for all four triples (conic coordinates) and
     h(t) = 0 (perm W = 0), a curve -- adding these Z-only equations explicitly before the plane stage may help.
STATUS 22:48: (alpha1) structure + cuts for verifyfl's charts written; S2 dimension run in background.
STATUS 22:56: (alpha1) |supp W| = 3: 96/96 systems UNIT over Q(i) (calibration running); S2-dimension run stopped (memory rule).
 (F) (alpha1), |supp W| = 3 [hand normal form + exact; r14/alpha1_s3.py, run_a1s3.sh, run_a1s3_modp.sh]: W = v l^T with v SPECIAL ((E)), WLOG
     v = chi_1 (row symmetry), e = chi_2/2 the unit vector of v^perp; A_j = v (x) psi_j + eps_j rho e (x) f (j <= 2; u_j in v^perp with <u_j,u_j> = k = rho^2,
     the v-part absorbed into psi_j; psi_0 = 0 by the Z-gauge); A_3 = n (x) phi + eps_3 rho e_3 (x) f with n = w(tau), e_3 = chi_2/2 - tau chi_3 or
     n = chi_3, e_3 = chi_2/2 (every non-isotropic u_3 lies in n^perp for an isotropic line n of u_3^perp, so the line case A_3 = u_3 (x) f is covered);
     f in 3 charts; all 16 sign patterns; Rabinowitsch q l_1 (1 + l_1) rho = 1. Result: ALL 96 systems UNIT over Q(i) (< 1 s each) AND ALL 96 UNIT
     at P1. Calibration (degree-<=2 truncation) running.
     CALIBRATION (r14/a1s3_cal_num.py): the degree-<=2 truncation of these systems is equivalent to the operator identity
     A_4^*A_4 = 5 - 4 rho^2 f (x) f in the normal form; a numerical solution exists (residual 1.7e-12, rho != 0), so the truncation is non-unit and the
     unit verdicts use the degree-3/4 conditions.
 (G) (alpha1), |supp W| = 2 and 4: same normal form (r14/alpha1_gen.py; all isotropic directions at finite tau by the 6-point orbit argument;
     sign patterns up to the global sign rho -> -rho and the column symmetries): 18 + 9 systems running (r14/a1big.log, 2 GB cap).
STATUS 22:58: (alpha1) |supp| = 3 UNIT in char 0 and at P1 (96/96 each, calibrated); |supp| = 2, 4 runs started.
     UPDATE (G), 23:05: the full |supp| = 2 system (15 unknowns, parameters s, mu, t) exceeded 1.5 GB in 2 min -> stopped. Reduced formulation
     (r14/alpha1_s2plane.py): for s in Pi = {<psi_1,s> = 0} (mu = 0) the elements Y_s form a 2-dim subspace of K whose columns involve v only
     through e_v; only phi_k|Pi and f|Pi matter; rho = 1 by the rho <-> f scaling: 11 unknowns, parameters (x, y, t); 8 sign patterns x 3 charts.
     First system > 110 s (running, r14/a1s2p_pppp_0.out). If f|Pi = 0 this is the (alpha0) plane P2 (already unit). |supp| = 4: alpha1_gen.py
     (19 unknowns) not run (memory). Both are covered at P1 by verifyfl's (alpha) charts; my normal form (sec. 34 (D)) can cut those charts.
STATUS 23:07: round 14 final. (alpha0) unit in char 0 and at P1; (alpha1) |supp| = 3 unit in char 0 and at P1; (alpha1) |supp| = 2, 4 open (heavy; plane system a1s2p running until 23:14). Combination rule stated.

# ROUND 15 (start 23:11 UTC). Targets: (1) hand lever for (alpha1) |supp W| = 2, 4; (2) (PR3). First: COMPUTE item 13 for verifyfl.
STATUS 23:11: writing COMPUTE item 13 (cuts for gen_m0a.py).
STATUS 23:12: COMPUTE item 13 written (cuts C1-C3 for gen_m0a).
STATUS 23:24: S2 numerics: both-nonzero solutions all have b2 = b3; LEMMA S2 mod P1: parallel case unit (3/3 a-charts), non-parallel unit in chart a1 (105 s); charts 2,3 running.
STATUS 23:35: LEMMA S2 UNIT at P1 (neq 3/3, par 3/3 a-charts); (alpha1) |supp 4| excluded by hand given S2; |supp 2| reduced by hand to (c1), (c3): 12/12 UNIT char 0 and P1 (calibrated). S2 over Q running (r15/run_s2q.sh, 2 GB cap).

## 35. ROUND 15: LEMMA S2 and the hand reduction of (alpha1) |supp W| = 2 and 4
 (A) LEMMA S2 [modular at P1 = 2147483629 (all pieces); char 0 running]. Let Y = a (x) (1,1,1,1,-2) + b2 (x) (e_2 - e_4) + b3 (x) (e_3 - e_4) with
     a in V nonzero and b2, b3 in V isotropic ("shape S2"). If the line C Y has defect in C m0, then b2 = 0 or b3 = 0 or b2 = b3.
     (By Lemma S-SPEC, exactly one of b2, b3 being zero forces the other onto a special line; both zero is the rank-one element a (x) m',
     excluded by R8.8.) By column symmetry (m0 is S_4-symmetric on columns 0..3) the same holds for any two columns {c,d} in {0..3}.
     Proof scheme (r15/s2lemma.py, chilib.py): chi-coordinates over Q (<,>, tau, q4 all rational, chilib.py checked against brute-force
     permanents), the formula perm(J + tX) = 24 - 2t^2 sum_pairs <,> + 2t^3 sum_triples tau + t^4 (sum_pairings <,><,> - 6 q4) for column-centred X;
     b2 = w(t2) (scale), b3 = be w(t3), both t finite WLOG (the 6 special lines are the row-S_4 orbit of the chi_3-line; pick one avoiding both
     b-lines); a-charts: v a_k = 1 (k = 1,2,3).  'neq': u be (t2 - t3) = 1 -> UNIT at P1 in all 3 a-charts (105 s, 97 s, 75 s; <= 164 MB);
     'par': t3 = t2, u be (be - 1) = 1 -> UNIT at P1 in all 3 a-charts. Without a != 0 the 'par' ideal is NOT unit (4 components, all a = 0;
     mod 32003) -- the a-charts are needed. CALIBRATION: numerics r15/s2_explore*.py (LM, hinges forcing b3 resp. b2, b3 nonzero): 3/98 starts
     converge, ALL with b2 = b3 (tau2 = tau3, be2 = be3, p_3(b) != 0, local dim 1) -- the S2= family Y = a (x) m' + b (x) (0,0,1,1,-2) is non-empty,
     so the lemma is sharp and its systems are not trivially inconsistent.
 (B) THEOREM (alpha1), |supp W| = 4 [hand, given Lemma S2; valid in char 0 and char p > 7]: impossible.
     For s in f^perp (2-dim) A_j s = c_j(s) z_j (j <= 3, sec. 34 (D), n_j = z_j) and, with mu = -c_p(s)/2,
       Y(s) + mu Z = (s/2) (x) m' + sum_{j<=3} delta_j z_j (x) (e_j - e_4),  delta_j = (c_j - c_p)(s)/2      (uses z_4 = 0, sum z_j = 0).
     View P_j := c_j|f^perp as four points of the affine plane (f^perp)^* (the Z-gauge translates all four). For a pair {p,q} with P_p != P_q
     take s != 0 in ker(P_q - P_p): the element has delta_p = delta_q = 0 and delta_c = 0 iff P_c lies on the line P_p P_q.
       * If two further points are on that line (all four collinear) the element is a (x) m' (rank one, a = s/2 != 0): excluded (R8.8).
       * If P_p = P_q = P_c, s in ker(P_d - P_p) gives a rank-one element: excluded. If P_p = P_q, P_c = P_d: all collinear, excluded.
       So the configuration is (A) general position, (B) four distinct with exactly three collinear, or (C) exactly one coincidence.
     (A): every pair {p,q} gives delta_c, delta_d != 0, Lemma S2 => delta_c z_c = delta_d z_d => z_c || z_d for ALL pairs => W = v l^T of rank one with
          four nonzero entries -- impossible (sec. 33 (G): e_3-vector (prod_{k != j} l_k)_j, e_4-vector (0,0,0,0,prod l) not ~ m0).
     (B): P_0, P_1, P_2 on L, P_3 off L: the pairs {0,3}, {1,3}, {2,3} give z_1 || z_2, z_0 || z_2, z_0 || z_1, and z_3 = -(z_0+z_1+z_2): rank one again.
     (C): P_0 = P_1, P_0, P_2, P_3 not collinear: the pair {2,3} gives delta_0 = delta_1 != 0, so z_0 = z_1 =: z; then z_2 + z_3 = -2z with z_2, z_3, z
          isotropic gives 2 <z_2,z_3> = 0, so z_2 || z_3 (orthogonal isotropic vectors are parallel) and W has rank one: impossible.
 (C) THEOREM (alpha1), |supp W| = 2 [hand, given Lemma S2 + Lemma S-SPEC, + 12 exact systems]: impossible. W = v (e_0 - e_1)^T, n_0 = n_1 = v,
     n_2, n_3 isotropic (A_j(f^perp) in C n_j). On f^perp put sig = (c_0 + c_1)/2, gam_k = c_k/2 (k = 2,3). The elements of
     K_f = {Y(s) + mu Z : s in f^perp} have y_0 = s/2 + al_0 v, y_1 = s/2 + (sig(s) - al_0) v, y_k = s/2 + gam_k(s) n_k, y_4 = -s - sig(s) v - sum gam_k(s) n_k
     (al_0 free via mu), giving S2 elements on columns {2,3} (s in ker sig), {0,2} (s in ker gam_3), {0,3} (s in ker gam_2).
     sig, gam_2, gam_3 do not all vanish at a common s != 0 (rank-one element), i.e. they are not all proportional.
       generic (pairwise non-proportional): S2 on {2,3}, {0,2}, {0,3} gives n_2 || n_3 || v, then (normalising n_k = v) gam_2 - gam_3 in C sig,
         sig - gam_2 in C gam_3, sig - gam_3 in C gam_2  =>  sig = gam_2 + gam_3 and then 2 gam_2 in C(gam_2 + gam_3): contradiction (char != 2).
       sig == 0 (resp. gam_2 == 0, gam_3 == 0): S2 on {2,3} (resp. {0,3}, {0,2}) for ALL s forces the two remaining forms equal: contradiction.
       (c1) sig || gam_2, gam_3 not: n_2 = v, gam_2 = sig, and n_3 SPECIAL (shape S on column 3 for s in ker sig, Lemma S-SPEC);
       (c2) sig || gam_3: (c1) with columns 2 <-> 3;
       (c3) gam_2 || gam_3, sig not: n_2 = n_3 =: n, gam_2 = gam_3 =: gam, and v SPECIAL (shape S on column 0 for s in ker gam_2).
     (c1), (c3) are small systems on K_f alone (r15/s2red.py; special vector = chi_1 WLOG by row symmetry; the free isotropic vector w(tau) or
     chi_3; f^perp in the 3 Gr(2,3) charts; sig, gam linear on f^perp with u det(sig, gam) = 1; 7 unknowns; all coefficients in (s1, s2, al_0)):
     ALL 12 systems UNIT over Q AND at P1 (r15/red.log, < 1 s each). CALIBRATION: degree-2 truncation NON-unit (dim 4), the restriction to
     the S2 / S2= line (s in ker sig, al_0 = 0) NON-unit (dim 3) for (c1) and (c3); the degree-<=3 system is already unit (the contradiction
     sits in the cubic conditions on the 3-dim K_f). [A size()-vs-ncols() loop bug in the first draft skipped zero generators -- found by
     the d2 calibration, fixed; older generators (r13, r14) loop over k = 1..4 and are not affected.]
 (D) CONSEQUENCE. With sec. 33 ((alpha0), char 0 and P1), sec. 34 (B), (F) ((alpha0) at P1; (alpha1) |supp 3| char 0 and P1) and (B), (C) here:
     CASE (alpha) OF [T31] SPLIT A FOR m0 IS IMPOSSIBLE AT P1 (all pieces at the same prime; hand steps valid for p > 7) -- so, by verifyfl's
     Lemma RED-p, (alpha) + verifyfl's (beta) (32/32 at P1) close split A of [T31] for m0 in characteristic 0 as soon as the remaining type pieces
     ([DC3], [T22]) are in at P1. Independent char-0 proof of (alpha): everything except Lemma S2 is exact over Q / Q(i); Lemma S2 over Q is running.
STATUS 23:37: sec. 35 written: Lemma S2 (P1), (alpha1) |supp 4| and |supp 2| excluded => (alpha) unit at P1.
 (A') CORRECTION to the count in (A): the S2 numerics finished with 2/40 (b3 hinged) + 5/60 (b2, b3 hinged) = 7/100 converged starts, ALL with
     b2 = b3 (tau2 = tau3 to 1e-4, be2 = be3).
     CALIBRATION of 'neq' (A): the same system with u be = 1 only (t2 = t3 allowed), a-chart 1, at P1: NON-unit, dim 1 (= the S2= family);
     so the unit verdict uses exactly the open condition t2 != t3.
STATUS 23:40: COMPUTE item 13 updated ((alpha) closed at P1; verifyfl's alpha charts now a cross-check). Interim message sent to main. Next: (PR3).
 (E) (PR3) -- SET-UP ONLY this round [rigorous stratification; no exact run]. X in (+)_{i<3} e_i (x) P_i (dim P_i = 2), dim X = 3, level
     (esig_1 = esig_2 = esig_3 = 0), no single-row element. K_i := X cap ker pi_i has dim >= 1 and K_i cap K_j = 0 (i != j: an element in both is
     single-row), so at most one K_i is 2-dim. Strata:
       (I)  three independent lines: X = span{(0, v_0, w_0), (u_1, 0, w_1), (u_2, v_2, 0)} (30 coordinates, 3 scalings);
       (II) three coplanar lines: H = K_0 + K_1 + K_2 = {(a h_0, b h_1, c h_2) : a + b + c = 0} after rescaling the h_s, and level on H forces
            sigma(h_0) = sigma(h_1) = sigma(h_2) =: s, <h_s, h_s'> = s^2 (s != s'), tau(h_0, h_1, h_2) = s^3  (esig_1, esig_2, esig_3 on the plane a+b+c = 0);
       (III) K_i 2-dim: row i lies on a line C p, X = K_i (+) C x', K_j, K_k lines outside K_i with K_j cap K_k = 0.
     With Z (Gr(2,4)) the stratum (I) system has ~31 unknowns and degrees up to 3 in products of row coordinates -- not feasible without a
     further hand lever; (II) is the most constrained and the natural first exact target (next round).
STATUS 23:45: Lemma S2 parallel case UNIT OVER Q in all 3 a-charts (slimgb: 75 s, 8 s, 127 s; <= 196 MB); non-parallel over Q running (slimgb, r15/run_s2q.sh).
STATUS 23:58: S2 non-parallel over Q still running (chart a1, slimgb, 1.4 GB at 13 min, 20-min cap); adapted-basis reformulation (a = x b2 + y b3 + z e: degree-2 condition becomes z^2 = be(4xy+3x+3y+1), so a != 0 is automatic) is NOT faster at P1. verify2 is re-deriving Lemma S2 (verify2/r13/s2c_*).
STATUS 00:06: round 15 final. S2 non-parallel over Q: chart a1 timed out (slimgb 20 min, peak ~1.4 GB) -> chain stopped; adapted-basis variant ran out of memory at P1 (450 MB cap, 341 s). No jobs of mine running.

# ROUND 16 (start 00:13 UTC). Coordinator: [T31] for m0 COMPLETE at P1 (verify2 confirmed). Targets: (1) (PR3) = leaf 7: stratum (II)
#  exactly, then (I), (III), structural reason; (2) leaf 8: case list for multi-row z-vectors / mixed (2,1,..); (3) z = (2,0,0,0,0) uniform argument.
STATUS 00:13: started; reading PROOF-MAP.md leaves 7, 8.
STATUS 00:22: (PR3) stratum (II): hand formulas (D_3 on H = a0 a1 a2 G; F_ij = 2 k_i o k_j - (s^2/2) 1 in Delta); exact systems (15 resp. 13 unknowns) > 110 s at P1 -> looking for structure in the 14 stored (2,1,0,0) examples.

## 36. ROUND 16: (PR3) -- stratum (II) analysis, the (2,1,0,0) examples, and the leaf-8 case list
 (A) FORMULAS [rigorous]. For a level 3x5 x (rows r_i, s_i = s(r_i)): c(x) = -(r_0 + r_1 + r_2); D_2(x) = sum_i s_i r_i + 2 sum_{i<k} r_i o r_k;
     D_3(x) = -sum_i [s_k s_l - <r_k, r_l>] r_i + 2 sum_{i<l} s_k r_i o r_l - 6 r_0 o r_1 o r_2  ({i,k,l} = {0,1,2}).  A 2-row element (0, v, w)
     has c = -(v + w), D_2 = s(v)(v - w) + 2 v o w (= Q of round 10), D_3 = 0.  [r16/pr3lib.py: sigma_m by brute force, self-checked.]
 (B) STRATUM (II) ON H [rigorous]. H = {(a h_0, b h_1, c h_2): a+b+c = 0} is level iff s(h_i) = s, <h_i, h_k> = s^2 (i != k), tau(h_0,h_1,h_2) = s^3;
     then on H:  D_2 = sum_{i<k} a_i a_k F_ik,  F_ik = 2 h_i o h_k - s(h_i + h_k);   D_3 = a_0 a_1 a_2 G,  G = 2s sum_{i<k} h_i o h_k - 6 h_0 o h_1 o h_2.
     If dim Delta = 2 (Delta := c(H) = span(h_0 - h_2, h_1 - h_2)) and defect(X) <= 2, then U' = Delta, so F_01, F_02, F_12, G lie in Delta.
     [In the shifted vectors k_i = h_i - (s/2) 1: F_ik = 2 k_i o k_k - (s^2/2) 1, and G in Delta <=> k_2 o F_01 in span(1, Delta).]
     NUMERICAL [r16/st2_num.py]: this H-PART system ALONE is SOLVABLE (2/2 starts converge to generic-looking h's, residual <= 4e-13; one more
     with h_0 = e_3): the H-part does not cut stratum (II); the extra element x* must enter. Exact H-part systems (r16/strat2.py, strat2b.py,
     13-15 unknowns) did not finish in 110 s at P1 -- consistent with a positive-dimensional H-part variety.
 (C) THE STORED DEFECT-<=2 EXAMPLES [numerical, r16/ex21.py, 14 files]: for every stored 5-dim 4x5 space of shape single-row (2,1,0,0), the
     3-row part X has kernel dims (1,1,1) with K_1 = K_2 (that is the single-row element, in row 0), dim c(X) = 2 and defect exactly 2.
     So all known defect-<=2 spaces are "stratum (II) with two kernels merged" -- the configuration the hypothesis of (PR3) excludes.
STATUS 00:25: sec. 36 (A)-(C) written; full stratum (II) numerics running (r16/st2_full.py: target + nodef calibration).
 (D) LEAF 8 -- CASE LIST for z-vectors with single-row parts in >= 2 rows (at most one entry 2) [regime: 9-dim level L, all a_r = 1, all
     lam >= 3; tools: (c1)-(c5) of sec. 26, Lemma S3-2 of sec. 24 (A), Theorem Z22, F4b-X, PFC].
     GENERAL CUT (rigorous, from Lemma S3-2 (a), (b)): for every row r,   z_r + dim( sum_{i != r} Z_i ) <= 4,   and the Z_i are pairwise
     orthogonal subspaces of 1^perp.  [e_r >= dim sum_{i != r} Z_i (S3-2 (b)) and z_r <= 4 - e_r (S3-2 (a)).]
     RANK-ONE FAMILY LEMMA (rigorous, one line): if L contains c (x) m for all c supported on a row set S (|S| = k), then e_j(m) = 0 for
     j <= k [sigma_j(c (x) m) = j! e_j(c) e_j(m)]; k = 5 is impossible (e_1 = .. = e_5 = 0 forces m = 0); k = 4 forces m = la (1, zeta, .., zeta^4)
     up to a column permutation (zeta^5 = 1, the "Fourier vector"); k = 3 forces e_3(m) = 0 as well as isotropy.
     ORTHOGONALITY BOOKKEEPING (rigorous linear algebra in the 4-dim nondegenerate 1^perp): pairwise orthogonal single-row vectors: the
     non-isotropic ones are linearly independent of all the others; the isotropic ones span a totally isotropic space (dim <= 2, and
     <= 1 inside the orthogonal complement of a non-isotropic vector or of a nondegenerate plane).
     CASES (sorted z; first the counting, then what is known):
       (1,1,0,0,0)  no counting cut. Known: w_1 orthogonal to w_2; SPLIT (S3-2 (c)) if one is non-isotropic; W W' . P_k P_l = 0 (sec. 26 (D)).  OPEN.
       (1,1,1,0,0)  no counting cut; tau(w_1, w_2, w_3) = 0 (sigma_3 on e_1 w_1 + e_2 w_2 + e_3 w_3).  OPEN.
       (1,1,1,1,0)  no counting cut; all triple products tau = 0 and q4(w_1..w_4) = 0 (sigma_4).  OPEN.
       (1,1,1,1,1)  CUT: any four of w_1..w_5 span <= 3 dims, so at most two are non-isotropic, and the isotropic ones lie in a totally
                    isotropic space: either all five isotropic (in a plane T, so >= 2 parallel pairs among five vectors in dim 2), or
                    one/two non-isotropic and the other 4/3 PARALLEL to one isotropic m -> rank-one family with k = 4 (m = Fourier vector)
                    or k = 3 (e_3(m) = 0). All five parallel: impossible (k = 5). Remaining: OPEN but very rigid.
       (2,1,0,0,0)  no counting cut. Known: the L_r of this pattern have shape single-row (2,1,0,0) / row projections (2,2,2,2) (sec. 30 (A));
                    all 14 stored such L_r have FO2_0 <= 8 [numerical]. OPEN as a theorem.
       (2,1,1,0,0)  counting: dim(Z_1 + C w_3) <= 3 (automatic). OPEN.
       (2,1,1,1,0)  CUT: span(w_2, w_3, w_4) <= 2-dim (row 1) and inside Z_1^perp cap 1^perp (2-dim); if Z_1 is nondegenerate, three pairwise
                    orthogonal vectors in a nondegenerate plane are all PARALLEL to one isotropic m -> rank-one family k = 3 (e_3(m) = 0).
                    Z_1 degenerate: Z_1^perp cap 1^perp is a degenerate plane containing rad Z_1. OPEN, rigid.
       (2,1,1,1,1)  CUT: span(w_2..w_5) <= 2-dim inside Z_1^perp cap 1^perp; Z_1 nondegenerate => w_2..w_5 all parallel to one isotropic m,
                    rank-one family k = 4: m = Fourier vector (1, zeta, .., zeta^4) up to order and scale, and Z_1 = (C m + C m' + C1)^perp-type
                    constraints from orthogonality. Then lam_{rr'} = 4 for all pairs in {2..5} and lam_{1r} = 3 ((c1), (c2)). OPEN, very rigid
                    (finite data up to Z_1) -- the best candidate for a short exact run.
     None of these is closed by Z22 (one entry 2 only), F4b-X (z = (1,0,0,0,0) only) or PFC (needs a free COLUMN c (x) e_j, while the
     rank-one families here are c (x) m with m isotropic, m != e_j); PFC would apply only after transposition, where c (x) m becomes m (x) c.
STATUS 00:28: sec. 36 (D) leaf-8 case list written (general cut z_r + dim sum_{i!=r} Z_i <= 4; rank-one family lemma; (1,1,1,1,1), (2,1,1,1,0), (2,1,1,1,1) forced into parallel isotropic families).
 (E) NEW THEOREMS FOR LEAF 8 [rigorous hand proofs + tiny exact checks over Q; they use ONLY the level conditions of the span of the
     single-row elements, so they hold for every level space, in any regime; char p > 5 as well].
     Tools: (i) single-row vectors of different rows are orthogonal, all in 1^perp; tau(w_a,w_b,w_c) = 0 for three distinct rows;
     (ii) RANK-ONE FAMILY on rows S (|S| = k) with vector m (L contains c (x) m, supp c in S): e_1(m) = .. = e_k(m) = 0, and every single-row
     vector z of a row OUTSIDE S satisfies <z, m^t> = 0 for t = 0..k (entrywise powers) [sigma_{t+1} of al e_o z + sum c_i e_i m: its
     al c_T-coefficient is t! <z, (e_t(m minus entry j))_j> = (-1)^t t! <z, m^t> since e_1..e_k(m) = 0]; a vector z of a row INSIDE S
     (a second vector of that row) satisfies the same for t <= k - 1;
     (iii) e_1 = e_2 = e_3 = 0 forces >= 4 distinct entries (p_1 = p_2 = p_3 = 0 with <= 3 distinct nonzero values: Vandermonde), so then
     1, m, m^2, m^3 are independent and their orthogonal complement is a LINE; e_1 = .. = e_4 = 0 forces m = la (zeta^{pi(j)}) (zeta^5 = 1),
     whose powers m^0..m^4 are a basis (k = 4 + any outside vector => contradiction; k = 5 => m = 0);
     (iv) a totally isotropic plane T in 1^perp has dim(T o T) = 3 (Theorem Z22, STEP 2), so tau cannot vanish identically on T
     (tau|_T = 0 would put T o T inside (T + C1)^perp, of dim 2).
   THEOREM SR5: NO level space has nonzero single-row elements in ALL FIVE rows.  [Covers z = (1,1,1,1,1) and (2,1,1,1,1).]
     Proof: pick w_i != 0 in each row. Non-isotropic w's are independent of the others; the isotropic ones span a totally isotropic
     subspace of (span of the non-isotropic)^perp. #non-isotropic >= 3: impossible (five vectors, dim 4). = 2: the three isotropic ones
     are parallel (k = 3 family m), the two others lie in the LINE orthogonal to 1, m, m^2, m^3 (iii), hence are parallel, but they are
     orthogonal and non-isotropic: contradiction. = 1: four parallel isotropic (k = 4) and a fifth vector: contradiction (iii).
     = 0: all in a totally isotropic plane T (a line: k = 5, impossible). A line of T with >= 4: (iii). With exactly 3 (vector m): the other
     two are parallel (iii) -> configuration (3,2) -> exact: E_{a,b}(m, m') = 0 (a <= 3, b <= 2) is the UNIT ideal over Q (r16/srow32.py,
     charts m_0 = 1, m'_0 = 1 or m'_1 = 1; calibration: the (2,2), (3,1), (2,1) configurations are NON-unit, dims 1, 1, 3). At most 2 per line
     (distributions (2,2,1), (2,1,1,1), (1^5), >= 3 distinct lines): the tau-conditions of the distinct-row triples force tau|_T = 0, against (iv).
   THEOREM SR2111: z = (2,1,1,1,0) is IMPOSSIBLE (again for any level space with these single-row parts). Z := Z_1 (2-dim), w_2, w_3, w_4 lie
     in Y := Z^perp cap 1^perp (2-dim), pairwise orthogonal.  Z nondegenerate: Y is a nondegenerate plane, so w_2, w_3, w_4 are parallel and
     isotropic (k = 3, vector m) and Z lies in the LINE orthogonal to 1, m, m^2, m^3: contradiction.  Z of rank 1 (radical C n): Y = span(n, y'),
     at most one w has a y'-part; all three parallel to n gives the k = 4 family on rows 1..4 (n in Z) and the second vector of Z orthogonal to
     n^0..n^3, i.e. parallel to n: contradiction; two parallel to n and one w not: CONFIGURATION C*.  Z totally isotropic (Y = Z): three distinct
     lines give tau|_Z = 0 against (iv); all parallel: k = 4 as before; distribution (2,1): again CONFIGURATION C* (rows 2, 3 carry n,
     row 4 carries w not parallel to n, row 1 carries span(n, z')).  C* exact (r16/srow2111.py): all sigma_t-coefficients of
     (al z' + c1 n; c2 n; c3 n; c4 w); charts n_0 = 1, z'_0 = 0 (gauge), z'_1 = 1 (S_4), w_k = 1 (k = 0..4), u (n_0 w_j - n_j w_0) = 1 (j = 1..4):
     20/20 UNIT over Q. Calibration: dropping row 3 gives a NON-unit ideal (dim 2).
   UPDATED LEAF-8 TABLE: (1,1,1,1,1), (2,1,1,1,1), (2,1,1,1,0): IMPOSSIBLE (SR5, SR2111).  OPEN: (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0),
     (2,1,0,0,0), (2,1,1,0,0) -- the single-row level conditions alone cannot kill (1,1,1,1,0) (the Fourier family m = (zeta^j) on four rows
     satisfies all of them), so these need the regime (lam, 2-row elements, (CA2)).
STATUS 00:33: THEOREM SR5 (no single-row elements in all five rows) and SR2111 (z = (2,1,1,1,0) impossible): hand + exact over Q (srow32 2/2, srow2111 20/20 unit, calibrated).
 (F) STRATUM (II), FURTHER [rigorous + numerical]. (1) If dim Delta = 2 then c(x*) lies in U' = Delta = c(H), so after subtracting an element
     of H:  x* = (r_0, r_1, r_2) with r_0 + r_1 + r_2 = 0  (WLOG). Then sigma_1(x*) = 0, sigma_2(x*) = (1/2) sum_i q(r_i) (q(y) = <y,y> - s(y)^2,
     nondegenerate), and the H-x* part of sigma_2 gives  <h_i, r_i> - s(h_i) s(r_i) = xi  for i = 0,1,2 (one common xi).
     (2) The H-part solution set has local dimension 4 at all 7 numerical solutions (Jacobian kernel of the normalised sampled system,
     r16/st2_dim.py): the H-part is a 4-dim family, so stratum (II) needs the x*-conditions; the full numerical probe (r16/st2_full.py, 34
     unknowns) is too slow here (2 starts in 15 min, residuals 7e-3, 2.7 -- inconclusive; calibration without the defect conditions: 19/20).
     (3) Exact plan: unknowns h (15) and r_0, r_1 (10) with the WLOG above, Delta-chart as in r16/strat2b.py -- big-slot size (COMPUTE item 14).
 (G) SIDE REMARK: by transposition (perm(J + tX) = perm(J + tX^T)) Theorem SR5 also says that no level space has nonzero single-COLUMN
     elements in all five columns.
STATUS 00:35: sec. 36 (F), (G) and COMPUTE item 14 written. No jobs of mine running.
STATUS 00:39: COORDINATOR CHECK (COMPUTE-ERRATA [N], modStd): NONE of my recorded exact verdicts used alg = modstd. stage3/r9/exact9c.py has the option but it was never used for a recorded verdict: the three record files r9/exact_{C12ac,C1G,C3c}_FULL_*.txt list only 'std(batch)' (578 charts) and 'std' (126 charts, + 1 TIMEOUT), and none of the 126 generated r9/gb/exc_*.sing files contains modStd; no other stage3 script calls modStd (grep over stage3/). Rounds 10-16 used std / slimgb only.
 (H) FOURIER LEMMA [rigorous hand proof; any level space]. If L contains e_i (x) m for the four rows i of S (so m = la (zeta^{pi(j)}) by the
     rank-one family lemma), then EVERY 2-row element of L is a sum of single-row elements of L (no proper 2-row elements).
     Proof. Pair (o, j), o outside S, y = e_o v + e_j w: in sigma_t(al y + sum_S c_i e_i m) the al c_T-coefficients (T in S - j) give
     <v + w, m^t> = 0 (t = 0..3) and the al c_j c_T-coefficients give <v, m^s> = 0 (s = 1..4); with the dual-basis relation
     <m^a, m^b> = 5 la^{a+b} delta_{a+b = 0 mod 5}: v = la' 1, w = -la' 1 + mu m; then y - mu e_j m = la' (e_o - e_j) (x) 1 has sigma_2 = -20 la'^2, so
     la' = 0. Pair (j, k) inside S: v, w orthogonal to m^1, m^2, m^3 and v + w to m^0, m^1, m^2, so v, w in span(1, m), and the same sigma_2
     argument leaves only multiples of m.  CONSEQUENCE for z = (1,1,1,1,0), Fourier sub-case (k_N = 0, all four vectors parallel): m_jk = z_j + z_k
     for all pairs; with (c5) all lam among the rows of S equal 3. Not yet a contradiction; the sub-case is now extremely rigid.
   CLASSIFICATION of the single-row configurations of (1,1,1,1,0) [rigorous, same tools]: k_N = #non-isotropic in {4, 2, 1, 0}
     (k_N = 3 impossible: an isotropic vector in a nondegenerate line); k_N = 2: the two isotropic ones parallel (k = 2 family m), the two
     others orthogonal to 1, m, m^2; k_N = 1: three parallel (e_3(m) = 0), the fourth on the line orthogonal to 1, m, m^2, m^3; k_N = 0: in a
     totally isotropic plane T with distribution (4) [Fourier, lemma above], (3,1), (2,2) or (2,1,1); (1,1,1,1) is impossible (tau|_T = 0).
STATUS 00:41: sec. 36 (H): Fourier lemma (four parallel single-row vectors => no proper 2-row elements) + classification of (1,1,1,1,0) single-row configurations. Full stratum-(II) exact system ran out of 1.5 GB at P1 in 194 s (big-slot size, COMPUTE item 14).
STATUS 00:42: round 16 final. No jobs of mine running.

# ROUND 17 (start 00:45 UTC). Targets: (1) item 14(a) runnable (generator + driver + calibration + QUEUE line) and a hand cut via the
#  zero-column-sum x*; (2) mechanism 'defect <= 2 => two kernels coincide'; (3) (PR3) strata (I), (III); (4) leaf 8 (1,1,1,1,0).
STATUS 00:45: started; deriving the x*-linear conditions of stratum (II).

## 37. ROUND 17: stratum (II) -- the x*-linear conditions, the special locus, the big-slot generator; the kernel mechanism; leaf 8
 (A) HAND CUT: EXPLICIT x*-CONDITIONS [rigorous]. Stratum (II), dim Delta = 2, x* = (r_0, r_1, r_2) with r_0 + r_1 + r_2 = 0 (WLOG, sec. 36 (F)),
     k_i := h_i - (s/2) 1, F_pq = 2 k_p o k_q - (s^2/2) 1 (in Delta), rho_i := s(r_i):
     (S2m) [d^1 of sigma_2]   <k_i, r_i> - (s/2) rho_i = xi   for i = 0,1,2 (one xi);
     (S3m) [d^1 of sigma_3]   <F_pq, r_t> = 0  for {p,q,t} = {0,1,2}   [the s_0 s_1 s_2 term cancels against the <,> s terms];
     (D2m) [d^1 of D_2]       M_i - M_k in Delta,  M_i := rho_i h_i - 2 k_i o r_i  (and s(M_i) = -2 xi, consistent with (S2m));
     (Q*)  [d^2 of sigma_2, D_2]  sum_i q(r_i) = 0 (q(y) = <y,y> - s(y)^2),  sum_i rho_i r_i - sum_i r_i o r_i in Delta.
     All d^0/d^1 conditions (level + Delta-membership of c, D_2, D_3) are LINEAR in x*.
 (B) THE x*-LINEAR SYSTEM HAS FULL RANK AT GENERIC H-POINTS [numerical, r17/lin_rank.py]: at the 7 numerical H-part solutions, the d^1-
     coefficients of all conditions form a 180 x 10 matrix A(h) in (r_0, r_1): rank 10 at the 5 generic points (smallest singular value
     0.005 .. 0.06 relative), rank 8 at the 2 special points (where h_0 = s e_j has four zero entries). So for generic H-points x* = 0 is
     forced: stratum (II) lives over the RANK-DROP LOCUS of A(h) on the 4-dim H-family -- the structural reason the H-part cannot cut and
     the x*-conditions do. Expected: the rank-drop locus is the special locus h_i = s e_j (plus lower strata).
     SPECIAL LOCUS (rigorous algebra): if h_0 = s e_j (s != 0), then <h_0, h_k> = s^2 gives h_1(j) = h_2(j) = s, tau(h_0,h_1,h_2) = s^3 holds
     automatically, F_01 = h_0 - h_1 and F_02 = h_0 - h_2 lie in Delta automatically, and G in Delta reduces to F_12 in Delta. So H has the
     FREE 3-ROW COLUMN s (a, b, c) (a + b + c = 0) in column j, row 0 vanishes off column j, and rows 1, 2 carry b h_1', c h_2' (h_1', h_2' in C^4,
     sum 0, <h_1', h_2'> = 0) off column j.
 (C) THE KERNEL MECHANISM (coordinator's target 2) IS EQUIVALENT TO (PR3) [rigorous remark]: in a 3-dim X with rows in planes, two kernel
     lines K_j = K_k (j != k) means an element with rows j and k zero, i.e. a single-row element in the third row; in stratum (III) a 2-dim
     K_i containing K_j does the same. So "defect <= 2 => two kernels coincide (or a kernel contains another)" is exactly the contrapositive
     of (PR3) -- no collapse to a smaller statement. What the mechanism DOES suggest is the strategy of (B): prove that the x*-linear
     conditions force x* = 0 off a small special locus, and treat the special locus (free 3-row column) separately.
STATUS 00:51: sec. 37 (A)-(C): explicit x*-conditions; x*-linear system full rank at generic H-points (numerical), drop only on the special locus h_i = s e_j; kernel mechanism == (PR3). P1 timing run of the 'lin' chart in background (r16/st2Q_lin_s1_00_p.log).
 (D) LEAF 8, z = (1,1,1,1,0): THE FOURIER SUB-CASE IS IMPOSSIBLE IN THE REGIME [rigorous hand proof]. Rows S = {1,2,3,4} carry the same
     single-row vector m (k_N = 0, distribution (4); m = la (zeta^{pi(j)})), row 5 carries none. Take r, k in S, {l, n} = S - {r, k}. The 3-row
     part X_{rk} = {x in L : rows r, k = 0} has dim lam_{rk} >= 3 (regime; lam_{rk} = 5 - dim pi_k(L_r)) and contains e_l m, e_n m. Let
     xi = e_5 v + e_l w_l + e_n w_n in X_{rk}. In sigma_t(al xi + sum_{i in S} c_i e_i m) the al c_T-coefficients (T in S, |T| = t) are
     t! < v + [l not in T] w_l + [n not in T] w_n , (-1)^t m^t >, so: v orthogonal to m^2, m^3, m^4 (T contains l, n); v + w_n and v + w_l orthogonal to
     m, m^2, m^3; v + w_l + w_n orthogonal to 1, m, m^2. Hence v, w_l, w_n are orthogonal to m (and v to m^1..m^4): v = la' 1, w_l, w_n in
     span(1, m). Subtracting multiples of e_l m, e_n m leaves (la' e_5 + mu_l e_l + mu_n e_n) (x) 1 with la' + mu_l + mu_n = 0, whose sigma_2, sigma_3
     are 20 e_2, 60 e_3 of (la', mu_l, mu_n): all three vanish. So X_{rk} = span(e_l m, e_n m) has dim 2 < 3: contradiction.
     [The same "outside-row" mechanism -- a 3-row element xi of X_{rk} must be orthogonal to many products of the single-row vectors -- is
     the natural tool for the remaining (1,1,1,1,0) configurations ((3,1), (2,2), (2,1,1), k_N = 1, 2, 4); not done.]
STATUS 00:53: sec. 37 (D): Fourier sub-case of z = (1,1,1,1,0) impossible in the regime (X_{rk} would be 2-dim).
 (E) *** (PR3) AND (PR2-split') ARE FALSE AS STATED *** [EXACT, r17/pr3_counter.py (sympy, rational)]. Found from the special-locus system
     (r17/spec_exact.py at P1: non-unit, one 5-dim component with x* supported in column 0). EXPLICIT X (rho = 1; any rho not in {0,-1}):
         x_b = [[-1,0,0,0,0],[1,1,-1,0,0],[0,0,0,0,0]],  x_c = [[-1,0,0,0,0],[0,0,0,0,0],[1,0,0,1,-1]],  x_d = [[1,0,0,0,0],[rho,0,0,0,0],[-1-rho,0,0,0,0]].
     X = span(x_b, x_c, x_d) is a 3-dim 3x5 LEVEL space (sigma_1..3 = 0 identically), row projections of dims (1, 2, 2) (all inside 2-planes),
     NO single-row element, and DEFECT 2 (deletion vectors span Delta = span(e_1 - e_2, e_3 - e_4)). Correspondingly N = X (+) e_3 (x) Z,
     Z = {z : sum z = 0, z_1 = z_2, z_3 = z_4}, is a 5-dim 4x5 level space (sigma_1..4 = 0 checked exactly) with single-row part e_3 (x) Z (2-dim),
     no single-row element in rows 0..2, all row projections <= 2: a counterexample to (PR2-split').
     GENERAL FAMILY (rigorous hand computation): X = {(-b-c+d, b+d rho, c-d(1+rho)) (x) e_0 + b e_1 (x) (0,y) + c e_2 (x) (0,z)} with y, z in C^4,
     s(y) = s(z) = 0, <y,z> = 0, y o z in span(y,z), y ^ z != 0: level <=> s(y) = s(z) = <y,z> = 0 (sigma_3 = 0 automatically); c(x) = -(0, b y + c z),
     D_2(x) = (0, p_1 b y + p_2 c z + 2bc y o z), D_3(x) = 2 p_0 bc (0, y o z) (p = column 0 of x): defect <= 2 <=> y o z in span(y, z).
     It lies in STRATUM (III) (row 0 on a line, K_0 2-dim). So: (PR3) can only hold for all row projections EXACTLY 2-dim (strata (I), (II));
     and the (S3-a) reduction via (PR2-split') breaks exactly when some pi_s(X_re) is 1-dim, i.e. when a 2-row part of L_e has m_kl = 2.
STATUS 01:04: *** (PR3)/(PR2-split') FALSE as stated: explicit exact counterexample (stratum III), sec. 37 (E). Interim message to main.
 (F) THE COUNTEREXAMPLE FAMILY IS HARMLESS FOR (S3-a) [numerical, r17/counter_t1.py, T_1/FO2_0 code of round 10]. Family parametrisation:
     y in C^4 (sum 0), z_j = y_j/(y_j - be) with sum_j y_j/(y_j - be) = 0 (a cubic in be; then <y,z> = 0 and y o z = be z + y automatically), rho free.
     N = X (+) e_3 Z: generic members (4 random): dim T_1(N) = 9 (gaps 2e-4 .. 5e-3 vs 1e-16) => dim L <= 8 by the row-kernel bound; the two
     disjoint-support members: dim T_1 = 10, FO2_0 = 8 => dim L <= 8. So no member is the L_r of a 9-dim level space (numerically).
     CORRECTED ROUTE for (S3-a): (S3-a) <= "every 5-dim 4x5 level space of (PR2-split') shape has dim T_1 <= 9 or FO2_0 <= 8" -- true on all
     known examples INCLUDING the new family; (PR3) itself survives only for strata (I), (II) (all row projections exactly 2-dim).
 (G) INDEXING (explicit, as asked by the coordinator): everything in (E), (F) is 0-INDEXED: rows 0, 1, 2 of X (row 3 of N carries Z),
     columns 0..4; the free column is column 0; Z = {(-2s-2r, s, s, r, r)} (z_1 = z_2, z_3 = z_4, sum 0). With 1-indexed columns the same
     formulas would put Z on the wrong pairs and sigma_2, sigma_3 of N would NOT vanish. [Coordinator re-checked sigma_1..4(N) = 0 for symbolic rho.]
     NAME CLASH WARNING: stage3's "(PR3)" (3-row defect statement, sec. 31 (G)) is NOT verifyfl's "THEOREM PR3" (R4.5, verified by verify2).
     Only stage3's (PR3) is refuted.
 (H) CORRECTED STATEMENT AND WHAT (S3-a) NOW NEEDS [rigorous bookkeeping].
     (PR3')  every 3-dim 3x5 level space X with all three row projections of dimension EXACTLY 2 and no single-row element has defect >= 3
             (= strata (I) and (II) of sec. 35 (E)).  OPEN.  Stratum (III) (one row projection 1-dim) has the counterexample family (E).
     In (S3-a), L_e (5-dim 4x5, rows R, all pi_r(L_e) = P_r 2-dim, no single-row element) has two-row parts Y_kl of dim m_kl in {1,2}, the
     pairs with m = 2 disjoint (normal forms (t0) none, (t1) one, (t2) two disjoint pairs; sec. 30 (B)). For r in R and s in R - r,
     dim pi_s(X_re) = 3 - m_kl with {k,l} = R - {r,s}. ONE excluded L_r already kills (S3-a), hence:
       (t0): every X_re is in strata (I)/(II)              -> (PR3') would close it;
       (t1) (m_kl = 2 for one pair): take r in {k,l}; X_re has all kernels Y over pairs != {k,l}, all m = 1 -> strata (I)/(II) -> (PR3');
       (t2) (m_kl = m_rs = 2, R = {k,l} u {r,s}): EVERY X_re contains a 2-dim two-row part -> stratum (III) for every r -> the (PR2-split')
            route is DEAD here (the counterexample family lives exactly in this configuration: K_0 = Y_12 is 2-dim).
     Tools for (t2): (i) the T_1/FO2 bound -- every member of the counterexample family has dim T_1(N) <= 10 and FO2_0(N) <= 8 (19 members incl.
     degenerate ones, r17/counter_scan.log), so "(t2)-type L_r have FO2_0 <= 8" is the natural replacement statement; (ii) the (t2) core of
     sec. 30 (E): X0 = Y_ab (+) Y_cd is level iff (X2)-(X4) hold, 25 conditions on 22 parameters (expected dim -3, numerics 0/67), plus the (t2)
     identities of sec. 30 (B); (iii) (Q4) P_a P_b P_c P_d = 0 (sec. 29 (C1)) and the weakened (Q4) for 4-sets containing e (sec. 24 (C2));
     (iv) Lemma S3-2 bookkeeping (e_r >= dim of the other single-row parts) -- not decisive alone. In the counterexample family the 2-dim
     two-row part K_0 together with x* = w (x) e_0 gives a COLUMN element; a PFC-type (free-column) argument on L is a further candidate.
STATUS 01:08: sec. 37 (F)-(H): family harmless (max FO2_0 = 8 over 19 members); (PR3') stated; (S3-a) route now misses exactly type (t2); old RESULT/sec. 30/31 mentions of (PR3)/(PR2-split') flagged REFUTED in place; indexing and PR3 name clash stated.
 (I) STRATUM (II) ON ITS SPECIAL LOCUS IS EMPTY [EXACT over Q, r17/spec_exact.py, run_spec.sh]. Special locus: some h_i has four zero
     entries, i.e. (row/column symmetry) h_0 = s e_0, s = 1. Unknowns h_1 = (1, y), h_2 = (1, z) (sums 0), x* = (r_0, r_1, -r_0-r_1), chart
     u (y1 z2 - y2 z1) = 1 (S_4 on columns 1..4), x*-charts r_{I,J} = 1 (I = 0,1; J = 0..4): the 8 charts with J >= 1 are UNIT over Q; the two
     charts with J = 0 are NON-unit (dim 5; mod 32003: one component, r_{0,j} = r_{1,j} = 0 for j >= 1). Hence on the special locus EVERY
     solution has x* = w (x) e_0 (supported in column 0), so r_0 || h_0: these are exactly the stratum-(III) counterexamples of (E); stratum (II)
     proper (all r_i not parallel to h_i) has NO point on the special locus.
     With (B) (the x*-linear conditions have full rank 10 at generic H-points, rank drop seen only at special points) this is the picture:
     stratum (II) (dim Delta = 2) is empty iff the rank-drop locus of A(h) on the H-variety is contained in the special locus. OPEN (numerical
     evidence 7/7 sampled H-points).
 (J) WHY ITEM 14(a) MUST NOT BE QUEUED AS WRITTEN [rigorous]: the hinge-free stratum-(II) system contains the counterexample family of (E)
     (with H = its d = 0 part: h_0 = e_j, h_1 = (1, y), h_2 = (1, z) in the free column j, x* = w (x) e_j), so it is NON-unit by construction.
     A proof run needs the three stratum hinges h_i ^ r_i != 0, i.e. a chart cover of the decomposable-bivector cone per row (>= 7 forms per row),
     about 10 x 49 x 2 ~ 10^3 jobs with the row-0 wedge used as the x*-normalisation -- not reasonable before the rank-drop reduction of (I).
     Generator r16/st2_bigQ.py and driver r16/run_st2Q.sh are written and smoke-tested (they run; P1 timing of one 'lin' chart: > 20 min,
     > 1 GB); they are kept for a hinged version, NOT queued.
STATUS 01:09: sec. 37 (I) special locus of stratum (II) EMPTY for stratum (II) proper (exact over Q, 10 charts); (J) item 14(a) not queued (non-unit by construction without row hinges).
 (K) LEAF 8, z = (1,1,1,1,0), CONFIGURATION "three rows m (e_1 = e_2 = e_3 = 0) + one row w on the line orthogonal to 1, m, m^2, m^3"
     (= k_N = 1 and the (3,1) distribution of k_N = 0) [hand + exact + numerical]. Regime: X_{03} (rows 0 = m-row, 3 = w-row zero) must be 3-dim.
     Hand: for xi = (v; a; b) on rows (4; 1; 2) the al c_T-coefficients give v orthogonal to m, m^2, m^3, w m^2, w m^3 and a, b orthogonal to m, m^2,
     w m, w m^2; if R1: rank(m, m^2, m^3, w m^2, w m^3) = 4 and R2: rank(m, m^2, w m, w m^2) = 3, then v in C1, a, b in span(1, m), and sigma_2, sigma_3 of
     the remaining (la, mu, nu) (x) 1 (la + mu + nu = 0) force xi into the gauge: X_{03} = span(e_1 m, e_2 m), contradiction.
     Exact (r17/leaf8_rank.py, over Q): R2 FAILS only if m has a zero entry (unit with u m_1..m_4 = 1, all 5 w-charts); R1 the same for w-charts 1-3
     (charts w0, w4 rerunning with a longer timeout, r17/lrank_R1_04.log). Numerical: kernel = gauge + (c (x) 1) exactly, at 3 random members.
     The zero-entry member m = (1, i, -1, -i, 0), w = (1,1,1,1,-4) [exact over Q(i), r17/leaf8_beta0.py]: X_{03} DOES admit a third element,
     supported in column 4 (a column element c (x) e_4 on rows 1, 2, 4; charts v4, a4, b4 non-unit, all others unit). So this configuration is
     excluded in the regime EXCEPT this single rigid member, which carries free-column structure (a PFC-type argument is the natural next step).
     Not yet done: k_N = 2, k_N = 4, distributions (2,2), (2,1,1). The exact 65-chart version of the general system (r17/leaf8_31x.py) is too slow
     over Q (> 120 s per chart) -- the hand reduction + rank loci above replaces it.
STATUS 01:26: sec. 37 (K): (1,1,1,1,0) 'three m + w' configuration excluded in the regime except one rigid member (m with a zero entry, column element); R1 charts w0/w4 rerunning.
     RIGID MEMBER -> PFC (lead) [exact, r17/rigid_check.py]: for m = (1, i, -1, -i, 0) (rows 0,1,2), w = (1,1,1,1,-4) (row 3), the pairs (r,3),
     r in {0,1,2}, force column elements c^(r) (x) e_4 in L with supp c^(r) in ({0,1,2} - r) u {4}, sum 0. The 7-dim space span(e_0 m, e_1 m, e_2 m,
     e_3 w) (+) {C (x) e_4 : supp C in {0,1,2,4}, sum C = 0} is LEVEL (sigma_1..5 = 0 identically). If the three c^(r) span the 3-dim space of such C,
     L contains a free column on four rows and Lemma PFC gives dim L <= 8 (given (SL_m0)); the case "c^(r) span only 2 dims" is left.
STATUS 01:27: rigid member: free column on rows {0,1,2,4} compatible (exact 7-dim level space); PFC route recorded.
STATUS 01:28: RESULT ROUND 17 updated; handover addendum. Running (mine, small): r17/lrank_R1_04.log (<= 20 min), r17/strat3_num.log (<= 30 min).
 (L) LEAD FOR (S3-a) TYPE (t2): the counterexample family contains the COLUMN element x_d = w (x) e_0 (w = (1, rho, -1-rho) on the three rows
     of X). If such an X occurs as X_re in (S3-a), then L itself contains a single-COLUMN element (column 0, three nonzero entries, sum 0), i.e.
     L^T (also a 9-dim level space) has a nonzero single-ROW element: z(L^T) != 0, and the whole single-row machinery (Theorem SR5, SR2111, the
     rank-one family and Fourier lemmas, F4b-X for z = (1,0,0,0,0), Z22) applies to L^T -- provided L^T is in the regime (all a_r = 1, lam >= 3)
     or the non-regime cases are covered elsewhere. The stratum-(III) probe (r17/strat3_num.py) so far found only solutions of this shape
     (p = e_4, a column element): numerical support for "stratum-(III) defect-<=2 spaces all carry a column element".
STATUS 01:28: sec. 37 (L): transposition lead for type (t2).
     UPDATE (K): R1 chart w0 UNIT over Q (rerun); chart w4 is equivalent to chart w1 under the column transposition (1 4) (which fixes the
     normalisation m_0 = 1 and the symmetric Rabinowitsch u m_1 m_2 m_3 m_4) -> R1 and R2 hold for every m without zero entry. So the 'three m + w'
     configuration of (1,1,1,1,0) is IMPOSSIBLE in the regime except for the rigid member (m with a zero entry) [hand + exact over Q].
STATUS 01:34: round 17 final. Stratum-(III) probe stopped (6 starts, 1 solution, of family shape). No jobs of mine running.

# ROUND 18 (start 01:37 UTC). Targets: (1) (t2) via transposition: stratum-(III) defect-<=2 spaces carry a column element; (2) (PR3')
#  stratum (II): rank-drop locus = special locus; (3) leaf 8 rigid member via PFC, then k_N = 2, 4, (2,2), (2,1,1); (4) stratum (I).
STATUS 01:37: started; setting up the stratum-(III) classification (Delta-chart, x* zero column sums, rows in planes).

## 38. ROUND 18: the rigid leaf-8 member via PFC; stratum (III) = the r_0 || h_0 part of stratum (II); ...
 (A) THE RIGID MEMBER IS EXCLUDED (given (SL_m0), i.e. under Lemma PFC) [exact over Q(i), r18/rigid_pairs.py]. Configuration: rows 0,1,2 carry
     m = (1, i, -1, -i, 0), row 3 carries w = (1,1,1,1,-4), row 4 none (0-indexed). For the pair (0,1) the third element of X_{01} (rows 0, 1 zero;
     gauge: the row-2 and row-3 entries at column 0 set to 0; 13 charts) exists only in the charts xl4, v4 (0-dim), all other charts UNIT, and
     the solution is xi = (e_4 - e_2) (x) e_4 (a column element on rows {2,4}). By the symmetry of the three m-rows the pairs (0,2), (1,2) give
     (e_4 - e_1) (x) e_4 and (e_4 - e_0) (x) e_4. These span {C (x) e_4 : supp C in {0,1,2,4}, sum C = 0}: L contains a FREE COLUMN ON FOUR ROWS, and
     Lemma PFC gives dim L <= 8. [The 7-dim span with m, w is level, r17/rigid_check.py -- consistent.]
     => z = (1,1,1,1,0), configuration "three m + w" (k_N = 1 and (3,1)) is IMPOSSIBLE in the regime (with sec. 37 (K); rigid member under PFC).
STATUS 01:44: sec. 38 (A): rigid member forces a free column on four rows -> PFC. 'three m + w' configuration closed (rigid member under (SL_m0)).
 (B) STRATUM (III) = THE r_0 || h_0 PART OF THE HINGE-FREE STRATUM-(II) SYSTEM [rigorous]. In stratum (III) (row 0 of X = C w, K_0 = Y 2-dim,
     K_1 = C x'', K_2 = C x'), the kernel elements x' = (w, s, 0), x'' = (w, 0, g) (normalised) span an H-plane
     {((a+b) w, a s, b g)} = {(A h_0, B h_1, C h_2) : A + B + C = 0} with h_0 = w, h_1 = -s, h_2 = -g, whose three coordinate lines are
     K_0 cap H, K_1, K_2; so X = H (+) C y (y in Y), and if dim c(H) = 2, X = H (+) C x* with x* of zero column sums and r_0 || h_0.
     Conversely every solution of the hinge-free stratum-(II) system with r_0 || h_0 is a stratum-(III) space. HENCE targets 1 and 2 are the
     SAME computation: classify the solutions of the hinge-free system ("H-plane + zero-column-sum x*"); stratum (II) proper = no r_i || h_i,
     stratum (III) = some r_i || h_i. The special locus (some h_i = s e_j) gives exactly family (E) (sec. 37 (I), exact). Both (M1) and the
     stratum-(II) exclusion therefore follow from ONE statement: "the x*-linear system A(h) is injective on the H-variety off the special locus".
     Exact attempts (r18/st3.py, r18/st3h.py with r_0 = lam h_0 imposed): > 110 s at P1 -- big-slot size.
 (C) LEAF 8 (1,1,1,1,0), THE REMAINING CONFIGURATIONS [numerical, r18/cfg_kernels.py]. Random members of (2,2), k_N = 2, (2,1,1) and k_N = 4
     all have outside-row kernel dimension EXACTLY 4 (= gauge 2 + the (c (x) 1) part) for EVERY pair (r,k); then sigma_2 = 20 e_2(c),
     sigma_3 = 60 e_3(c) of the remaining (c (x) 1)-part (cross terms with the gauge vanish: s(w) = <1,w> = <w_l,w_n> = 0, tau(1,1,w) = s(w) = 0,
     tau(1,w_l,w_n) = <w_l,w_n> = 0) force c = 0, so X_{rk} is 2-dim: CONTRADICTION in the regime for GENERIC members of every configuration.
     Remaining: the special members where every pair's kernel jumps (e.g. the disjoint-support orthogonal basis of k_N = 4 has kernels 5..10;
     the rigid member of 'three m + w', closed in (A)). Configuration families are <= 1-dim, so these special members form finite lists.
STATUS 01:53: sec. 38 (B) unification (stratum III = r_0||h_0 part of stratum II system), (C) leaf-8 generic members of all configurations excluded (numerical kernels). X0-core numerics running (hinge-free and hinged).
STATUS 01:57: COMPUTE item 15 ((M3) X0 core facts + reduction). Running: r18/x0num_hinge.log, r18/off_cal.log.
STATUS 01:59: QUEUE line ST3-X0MAIN appended (3 charts over Q, 6 GB, <= 1 h each); X0 main-case reduction: c'(P_c) = c(P_a)^perp, both Q-closed, only (X4) left.
 (D) *** verify2's (M3) "the (t2) core X0 is empty" IS FALSE (numerically) *** [r18/x0_num2.py seed 2 start 1, saved r18/x0sol_hinge_2_1.npy;
     r18/x0_verify.py]. A 4-dim 4x5 level space X0 = Y_ab (+) Y_cd with BOTH 2-row parts 2-dim and NO single-row element (P_a, P_b, P_c, P_d all
     2-dim): sigma_1..sigma_4 vanish at 30 FRESH random points to 2.1e-13. Structure: Y_ab contains (e_0, -e_0) exactly (v1 = e_0, w1 = -e_0), so
     dim c(P_a) = 1 (NOT the main case of COMPUTE 15), dim c'(P_c) = 2, c-planes orthogonal; X0 has exactly ONE column element
     (e_a - e_b) (x) e_0 (column 0, rows a, b) and defect 4. Hinge-free numerics give only degenerate solutions (single-row elements); the hinged
     run converged in 1 of 2 starts. => (t2) cannot be closed by X0 alone; the queued ST3-X0MAIN run (main case dim c = 2) is still meaningful
     but no longer decisive. Note the recurring COLUMN ELEMENT (also in family (E)): support for the transposition route.
STATUS 02:06: (M3) X0 core EXISTS numerically (no single-row elements, fresh-point 2e-13), with a column element; sec. 38 (D).
     UPDATE (D): a SECOND non-degenerate X0 (r18/x0sol_hinge_3_0.npy, seed 3 start 0; fresh-point max|sigma| = 2.2e-13; P_a..P_d all 2-dim) is in
     the MAIN case (dim c(P_a) = dim c'(P_c) = 2) and has NO column element. Its shape is a COLUMN-BLOCK structure: Y_ab is supported on the
     columns {0,1,4} (entries in columns 2,3 vanish), Y_cd is CONSTANT on {0,1,4} (u_1, u_2, t_1, t_2 have equal entries in columns 0, 1, 4) and
     free on {2,3} -- the "free column (+) D" pattern of the F4b analysis. So (i) the queued main-case run ST3-X0MAIN will come out NON-unit;
     (ii) "every (t2)-type structure carries a column element" is FALSE at the level of X0. The column-element statement can only hold for
     the stratum-(III) spaces X_re themselves (target 1 proper), where all solutions found so far (family (E), probe solutions) do carry one.
STATUS 02:09: second X0 (main case, no column element, column-block shape {0,1,4} | {2,3}); ST3-X0MAIN will be non-unit.
STATUS 02:10: RESULT ROUND 18 written; handover addendum.
 (E) (t2) NORMAL FORM WITHOUT delta [rigorous]: in type (t2), L_e = Y_ab (+) Y_cd (+) C x5 and, subtracting elements of Y_ab and Y_cd (whose row
     projections already fill P_a and P_c), x5 = (0, g, 0, h) with g in P_b, h in P_d, both nonzero (else a single-row element): L_e is the sum of
     THREE 2-row spaces Y_ab, Y_cd, Y_bd (dims 2, 2, >= 1). Since X0 exists, the decisive (t2) question is whether X0 extends by such a 2-row
     element (0, g, 0, h) to a level L_e with defect <= 2. Numerical probe r18/t2Le.py (calibration 'lev': level only; target 'def': + defect <= 2).
 (F) NUMERICS ON THE UNIFIED SYSTEM [r18/offspecial.py]: calibration (no hinges) 4/7 starts converge, ALL on the special locus (one h_i with a
     single nonzero entry, r_i || h_i, x* supported in one column = family (E)); target (hinges keeping every h_i off the coordinate axes):
     0/5 starts converge (floors 8.5e-4 .. 5e-2). Evidence for "rank-drop locus = special locus" (target 2) and for the column-element statement
     on stratum (III) (target 1). (t2) L_e probe r18/t2Le.py (calibration "lev", level only): 0/2 (floors 2.6e-2, 2.2e-2), slow -- inconclusive.
 (G) COST OF THE EXACT COLUMN-ELEMENT STATEMENT (as asked): on the unified system "H-plane + zero-column-sum x*" (dim Delta = 2) the claim
     "x* is supported in one column" = emptiness with two nonzero columns: charts r_{i,a} = 1, u r_{i',b} = 1 (a != b): 80 charts, ~20 orbits under the
     residual S_2 x S_3, times 2 sigma-charts ~ 40 charts; one chart of the hinge-free system already needs > 1.5 GB at P1 (r16, 194 s) -> each chart
     a big-slot job of several GB and hours over Q. Equivalent for stratum (III) only ("h_0 is a coordinate vector"): 36 charts (r18/st3h.py 'pp').
     NOT queued: first a hand reduction of the x*-linear system (sec. 37 (A)) is needed to make it pool-sized.
STATUS 02:26: sec. 38 (F), (G) written.
STATUS 02:26: round 18 final. Still running (mine, small, self-terminating by 02:43): r18/off_off.log (0/5 so far), r18/t2Le_lev.log (0/2 so far).

# ROUND 19 (start 02:27 UTC). Targets: (1) hand-reduce the x*-linear system (injective off the special locus) to a pool-sized check,
#  else a big-slot spec + QUEUE line; (2) (t2): extension of X0 shapes (a)/(b) by C(0,g,0,h); (3) leaf-8 special members; (4) circularity caveat.
STATUS 02:27: started; reading the leftover probe logs.

## 39. ROUND 19: the column-element route on the unified system; the D_3-linear conditions; the circularity caveat
 (A) BIG-SLOT FORMULATION (queued by the coordinator as ST3-TWOCOL, P1 triage first). Unified system "H-plane + zero-column-sum x*", dim Delta = 2,
     plus "x* has a second nonzero column" (chart r_{I,J} = 1, Rabinowitsch u3 r_{I2,J2} = 1, J2 != J): the 80 charts fall into 8 orbits under
     S_2 (rows 0 <-> 1) x S_2 (columns 0 <-> 1 with f_0 <-> f_1) x S_3 (columns 2,3,4) (r16/twocol_reps.txt), times 2 sigma-charts = 16 jobs
     (r16/st2_bigQ.py mode 'twocol', driver r16/run_twocol.sh P TO VMEM). One chart at P1 exceeds 0.93 GB in 90 s. UNIT on all 16 <=> x* is a
     column element on every solution.
     FOLLOW-UP, POOL-SIZED (mode 'colel'): x* = w (x) e_J, w = (1, rho, -1-rho) or (0,1,-1): 20 charts {s1,s0} x {I = 0,1} x {J = 0..4}, run at P1
     and over Q (r16/st2Q_colel_*; results below). The family (E) needs the special column J outside the Delta-chart columns {0,1}.
 (B) THE D_3-LINEAR CONDITIONS IN CLOSED FORM [rigorous]. With x = (a_i h_i + d r_i), sum r_i = 0, b(x,y) = <x,y> - s(x) s(y):
       d^1-part of D_3 = sum_{p<q} a_p a_q Phi_pq,  Phi_pq = b(h_q, r_t) h_p + b(h_p, r_t) h_q + 2 rho_t h_p o h_q + r_t o gamma_pq,
       gamma_pq := -6 k_p o k_q - s (k_p + k_q) + (s^2/2) 1 = -3 F_pq - s (k_p + k_q) - s^2 1   ({p,q,t} = {0,1,2}),
     and Phi_pq in Delta. LOCAL-GLOBAL STRUCTURE: at each column j the three (D3m) and two (D2m) conditions are linear in the column (r_0j, r_1j, r_2j)
     with coefficients in the point p_j = (k_0j, k_1j, k_2j) and in ~22 GLOBAL numbers (rho_t, xi, the b(h_q, r_t), the Delta-coordinates of the
     five vectors); where gamma_pq(j) != 0, (D3m) solves r_tj in terms of the globals. Counting: 15 local + 18 global consistency conditions on
     ~22 globals -> x* = 0 generically; x* != 0 needs the globals to satisfy extra relations or gamma_pq(j) = 0 at special columns. This is the
     mechanism behind "x* is a column element"; turning it into a proof needs the classification of the degenerate columns (small: one point
     p in C^3) plus the global consistency (not done).
STATUS 02:35: sec. 39 (A), (B) written; colel charts running.
 (C) COLUMN-ELEMENT FOLLOW-UP 'colel' [exact over Q, sigma = 1 charts]: x* = w (x) e_J: UNIT for J in {0,1} (the Delta-chart columns), NON-unit
     for J in {2,3,4} (dim 5 for w = (1, rho, -1-rho), dim 4 for w = (0,1,-1)) -- these contain family (E); decomposition (to check that every
     component lies on the special locus, i.e. some h_i || e_J with r_i || h_i) running (mod 32003). sigma = 0 charts slower (> 120 s at P1, running).
     DECISIVE RUN, as verify2 asks: route (a) -- the 16 'twocol' charts OVER Q (run_twocol.sh 0), since "a second nonzero column" is an open
     condition; the P1 pass (queued LOW) is triage only.
 (D) Off-special numerics final: 0/7 (r18/off_off.log) vs calibration 4/7 on the special locus.
 (E) LEAF 8, the special k_N = 4 member W = (e_0-e_1, e_2-e_3, (1,1,-1,-1,0), (1,1,1,1,-4)) [exact over Q, r19/kn4_special.py]: third elements of
     X_{rk} EXIST for every pair (e.g. pair (2,3): non-unit in all charts; pair (0,1): only in the column-4 charts xl4, v4) -- this member is not
     excluded by the outside-row test; like the rigid member it carries column elements (column 4); a PFC-type continuation is the next step.
STATUS 02:38: sec. 39 (C)-(E) written.
 (F) STRATUM (II) PROPER IS EMPTY ON THE COLUMN-ELEMENT LOCUS (sigma = 1) [EXACT over Q, r16/st2_bigQ.py 'colel s1 0 2 ... c0 c1 c2']: with
     x* = (1, rho, -1-rho) (x) e_2 and the stratum-(II) hinges u3 rho (1 + rho) h_0[c0] h_1[c1] h_2[c2] = 1 (c_i in {0,1,3,4}: every r_i not parallel to h_i
     means w_i != 0 and h_i not a multiple of e_2), ALL 64 charts are UNIT over Q (slimgb). J = 3, 4 are equivalent to J = 2 (S_3 on columns 2,3,4),
     J = 0, 1 are unit already, w = (0,1,-1) or rho in {0,-1} gives some r_i = 0 (stratum III). sigma = 0 charts running (r16/colel_s0.log).
     => DECISIVE CHAIN for dim Delta = 2: [ST3-TWOCOL over Q: x* is a column element] + [this: column-element locus has no stratum-(II)-proper point]
        => stratum (II) of (PR3') empty; and every stratum-(III) defect-<=2 space (dim c(H) = 2) carries the column element x* (target 1).
        Left: the sub-case dim Delta <= 1 (both strata) and sigma = 0.
 (G) THE CIRCULARITY CAVEAT (target 4) [rigorous bookkeeping]. In (S3-a) of type (t2) every r in R gives a stratum-(III) X_re; if each carries a
     column element, L contains c^(r) (x) e_{j(r)} with c^(r) supported on the three rows R - {r} (zero in rows r and e, sum 0), i.e. L^T contains the
     single-row elements e_{j(r)} (x) c^(r). Extra structure of L^T that L lacks: (i) if the j(r) are not all equal, z(L^T) has >= 2 nonzero
     entries -- a multi-row pattern, NOT (2,0,0,0,0): the circle is broken (and SR5, SR2111, Fourier, the (1,1,1,1,0) configuration results apply);
     (ii) if all j(r) = j, the single-row part Z'_j of L^T contains four vectors c^(r) with c^(r)_r = c^(r)_e = 0, so Z'_j lies in the coordinate
     hyperplane {c_e = 0} and contains, for every r in R, a vector with TWO zero coordinates; if dim Z'_j = 2 (z(L^T) = (2,0,0,0,0)) this is a
     2-dim single-row part with a COMMON ZERO coordinate (position e). L's own Z_e has no such property a priori. A lemma "an (S3-a) single-row
     part has no common zero coordinate" would break the circle; it is the natural target (column e of L^T restricted to Z'_j vanishes, which
     plays against the plane lemmas / (Q4) for the 4-set of rows of L^T other than j).
STATUS 02:41: sec. 39 (F) exact: column-element locus has no stratum-(II)-proper point (sigma = 1, 64/64 unit over Q); (G) circularity bookkeeping.
 (H) sigma = 0 part of (F): 24 of the 64 stratum-(II)-proper charts UNIT over Q, 40 TIMED OUT at 60 s / 900 MB (no verdict; e.g. c = 030, 031,
     033, 034, 040, 041, 043, 044, 130, 140, ...) -- rerun with a longer timeout (pool, < 1 GB per chart, or the big slot).
 (I) (t2) EXTENSION TESTS [numerical, seeded probe r18/t2Le_seed.py at the two X0 shapes + random (0,g,0,h)]: shape (a): 0/4 (floors 1.1e-3 ..
     1.4e-2); shape (b): 0/3, LM drives (g,h) to 0 (residual exactly the normalisation, 1.0). Evidence that neither X0 shape extends to a level
     L_e (level conditions only, before the defect condition).
STATUS 03:36: round 19 final. No jobs of mine running.

# ROUND 20 (start 03:37 UTC). Targets: (1) the 40 sigma=0 colel charts with staged refinement; (2) TWOCOL over Q sized in the pool with
#  refinement; (3) dim Delta <= 1; (4) leaf 8 k_N = 4 special member via PFC; (5) common-zero-coordinate lemma, (t2) extension.
STATUS 03:37: started; reading ncol/r32/refine.py (staged chart refinement).

## 40. ROUND 20: staged refinement closes the colel sigma = 0 charts; dim Delta <= 1; TWOCOL sizing
 (A) STRATUM (II) PROPER HAS NO POINT ON THE COLUMN-ELEMENT LOCUS [EXACT over Q, all charts]. sigma = 1: 64/64 charts unit (sec. 39 (F)).
     sigma = 0: STAGED CHART REFINEMENT (BRIEF UPDATE 16) with the symmetry group generated by rows 0 <-> 1 and columns 0 <-> 1, 3 <-> 4 (J = 2
     fixed): if chart (a',b,c) is unit then every solution has rho(1+rho) h_0[a'] h_1[b] h_2[c] = 0, so chart (a,b,c) (where h_1[b] h_2[c] rho(1+rho) != 0)
     may add h_0[a'] = 0 (closed conditions; similarly for the other slots; sound by induction). r20/staged_colel.py: 14 orbit representatives
     computed, ALL UNIT within seconds (0..8 refinement zeros each), the remaining 50 charts by the symmetry orbits -> 64/64 (r20/staged_colel_s0.log).
     Symmetry check: the row swap maps x* = (1, rho, -1-rho) (x) e_2 to (1, 1/rho, -1-1/rho) (x) e_2 after rescaling (rho(1+rho) != 0 keeps the hinge), the
     sigma = 0 normalisation det = 1 goes to det = -1, equivalent over C by the scaling h -> i h.
     => CONDITIONAL THEOREM: if every solution of the unified system (dim Delta = 2) has x* supported in one column (ST3-TWOCOL), then stratum (II)
        of (PR3') is EMPTY (dim Delta = 2), and every stratum-(III) space with dim c(H) = 2 carries the column element x*.
 (B) dim Delta <= 1 (h_i = h + t_i d): CAUTION -- a first H-part test came out UNIT instantly but used a non-WLOG normalisation (d_A = 0); with the
     correct charts (d = h_0 - h_2 has no free scale except the global one: d_0 = 1 after S_5; U' = span(d, uq), uq = (0,1,*,*,*)) the H-part does not
     finish in 100 s at P1 (r20/dlt1.py). Rigorous partial structure (distinct t's): s(d) = <d,d> = <h,d> = 0, <h,h> = s(h)^2, and
     d o d, h o d, h o h - s(h) h all lie in the 2-dim U' (from the differences of the F_ik).
 (C) TWOCOL chart over Q (s1, 02, 00), unrefined: > 300 s and > 0.9 GB (r16). Staged refinement needs a first verified chart; none is pool-sized.
STATUS 03:44: sec. 40 (A): colel sigma=0 64/64 by staged refinement (exact over Q) -> stratum (II) proper empty on the column-element locus; (B) dim Delta<=1 caution; (C) TWOCOL still big.
STATUS 03:45: QUEUE line ST3-TWOCOL-Q-STAGED appended (r20/staged_twocol.py).
 (D) dim Delta = 1, DISTINCT t's: HAND CLASSIFICATION OF THE H-PART [rigorous]. With h_i = h + t_i d (d != 0): s(d) = <d,d> = <h,d> = 0, <h,h> = s^2,
     and d o d, h o d, h o h - s h lie in the 2-dim U'. (i) d o d is not in C d (else d = k 1_S with s(d) = k|S| = 0, d = 0), so U' = span(d, d o d).
     (ii) h o d = al d + be d o d gives h_j = al + be d_j on supp(d); h o h - s h in U' gives h_j in {0, s} off supp(d), and on supp(d) (>= 3 entries; if d
     takes >= 3 distinct values there) al^2 = s al. (iii) s(h) = s, <h,h> = s^2 then give: s != 0 (normalise s = 1): al = 0 and EXACTLY ONE off-support
     column j0 with h_{j0} = 1, i.e. h_i = e_{j0} + g_i d (g_i = be + t_i distinct), so column j0 of H is a FREE 3-ROW COLUMN; s = 0: h = be d, so
     h_i = g_i d and H consists of rank-one matrices lam (x) d (then e_3(d) = 0 from sigma_3). [The case "d takes only two distinct values on its
     support" (al^2 = s al not forced) is listed separately.] These are tiny explicit families -- exact checks next (r20/dlt1b.py).
 (E) THEOREM (dim Delta = 1, distinct t's) [rigorous hand proof, completing (D)]: some h_i is a coordinate vector (special locus).
     Proof. A zero-sum isotropic d != 0 takes >= 3 distinct nonzero values on its support (one value: d = k 1_S, s(d) = 0 forces k = 0; two values
     v_1 (n_1 times), v_2 (n_2 times): n_1 v_1 + n_2 v_2 = 0 and n_1 v_1^2 + n_2 v_2^2 = 0 give n_1 v_1^2 (1 + n_1/n_2) = 0), so (D)(ii)-(iii) apply.
     s = 1: h_i = e_{j0} + g_i d. Then <h_i,h_k> = 1, s(h_i) = 1, F_ik = 2 g_i g_k d o d - (g_i + g_k) d lies in U' automatically, tau(h_0,h_1,h_2) = 1 + g_0 g_1 g_2 p_3(d),
     so g_0 g_1 g_2 p_3(d) = 0, and G = 2 e_2(g) d o d - 6 g_0 g_1 g_2 d o d o d lies in U' = span(d, d o d) iff g_0 g_1 g_2 = 0 or d^3 in span(d, d^2); the latter
     makes d take <= 2 distinct nonzero values on its support -- impossible as above. So some g_i = 0, i.e. h_i = e_{j0}.
     s = 0: h_i = g_i d with all g_i != 0 (h_i != 0 since the coordinate lines of H are distinct kernels), and G = -6 g_0 g_1 g_2 d^3 in U' again forces
     d^3 in span(d, d^2): impossible. QED  [So dim Delta = 1 with distinct t's lands on the special locus with dim Delta = 1; its exact x*-analysis
     is the next small system (r20/dlt1sp.py). Not yet covered: t_i = t_k for one pair, and dim Delta = 0.]
STATUS 03:50: sec. 40 (E): dim Delta = 1 with distinct t's forces the special locus (hand proof).
 (F) dim Delta = 1 SPECIAL LOCUS, x*-analysis (h_0 = e_4, h_1 = e_4 + g_1 d, h_2 = e_4 + g_2 d; U' = span(d, d o d); x* with c(x*) = ka (d o d))
     [r20/dlt1sp.py]. ka = 0: at P1 the charts r_{0,J} = 1 (J = 0..3) are UNIT (over Q: J = 3 unit, J = 0,1,2 rerunning with 600 s), the charts
     r_{0,4} and r_{1,J} are non-unit (a dim-6 component). Numerically (r20/dlt1sp_num.py, 6/6 random points of that component): NO single-row
     element, row projections (1,2,2) (stratum III), r_1 off column 4 parallel to d, and a COLUMN ELEMENT in column 4 -- i.e. these are stratum-(III)
     spaces of the "parallel" degenerate family-(E) type (y || z), again carrying a column element. ka = 1 (c(x*) = d o d != 0): running (P1 900 s, Q).
 (G) dim Delta = 0 (h_0 = h_1 = h_2 = h): H = {lam (x) h : sum lam = 0}, level <=> e_2(h) = e_3(h) = 0, D_2(H) = C(h o h - s h), D_3(H) = C(s h^2 - h^3)
     [rigorous]. Exact chart (r20/dlt0.py) > 60 s at P1 -- open. Also open: dim Delta = 1 with t_i = t_k for one pair.
STATUS 04:13: sec. 40 (F), (G): dim Delta = 1 special locus -> stratum (III) with column element (numerical 6/6, P1 charts); Q reruns and ka = 1 running.
STATUS 05:15: resumed after the usage-limit cut (04:25). dlt1sp over Q charts 00, 01, 02 timed out at 600 s, ka = 1 at P1 timed out at 900 s. Applying staged refinement (chart 03 unit over Q => r_{0,3} = 0, and r_{0,2} = 0 by the column swap 2 <-> 3).
 (H) dim Delta = 1 SPECIAL LOCUS, ka = 0, EXACT over Q with staged refinement [r20/dlt1sp.py]: chart r_{0,3} = 1 unit (direct); r_{0,2} by the column
     swap 2 <-> 3 (a symmetry of the chart u2 * minor_{01}(d, d o d) = 1); chart r_{0,0} = 1 refined by r_{0,2} = r_{0,3} = 0: UNIT in 0.4 s; chart r_{0,1} by the
     swap 0 <-> 1 (and also directly with r_{0,0} = r_{0,2} = r_{0,3} = 0: unit). So r_0 vanishes off column 4: r_0 || h_0 = e_4, pi_0(X) is 1-dim -> STRATUM (III)
     (no stratum-(II)-proper point here), and numerically (6/6) these spaces carry a column element in column 4.
     ka = 1 (c(x*) = d o d != 0; the case r_0 = r_1 = 0 is a single-row element and outside (PR3')): charts u3 r_{I,J} = 1 time out (> 120 s over Q,
     > 60 s at P1) -- OPEN.
STATUS 05:21: RESULT ROUND 20 + handover written.
STATUS 05:23: round 20 final. ka = 1 P1 scan: 5/5 charts time out at 60 s. No jobs of mine running.

# ROUND 21 (start 05:25 UTC). Targets: (1) dim Delta = 1, ka = 1 by hand; (2) equal-t case and dim Delta = 0; (3) staged refinement from
#  closed pool charts (<= 0.5 GB); (4) leaf-8 k_N = 4 member, common-zero-coordinate lemma.
STATUS 05:25: started; idea: on the dim-Delta-1 special locus U' vanishes at column j0, so X minus column j0 is a 3x4 LEVEL space.

## 41. ROUND 21: dim Delta = 1, ka = 1 via the 3x4 restriction; equal t's; dim Delta = 0
 (A) HAND CUTS FOR ka = 1 [rigorous]. On the dim-Delta-1 special locus (h_0 = e_4, h_i = e_4 + g_i d, U' = span(d, d o d)) every vector of U' vanishes at
     column 4, so all deletion vectors do: sigma_t(x minus column 4) = 0, i.e. X^(4) = {x restricted to columns 0..3} is a LEVEL 3x4 space. It contains
     e_1 (x) d', e_2 (x) d' (from H) and y = (r_0', r_1', r_2') with r_0' + r_1' + r_2' = -(d' o d'). The rank-one family computation on 4 columns
     (eps_1 = -d', eps_2 = d' o d' since e_1(d') = e_2(d') = 0) gives <r_0' + r_2', d'> = <r_0' + r_1', d'> = 0 and <r_0', d' o d'> = 0, hence
     <r_0', d'> = p_3(d), <r_1', d'> = <r_2', d'> = -p_3(d). The sigma_2 cross term gives <h_i, r_i> - s(r_i) + g_i p_3(d) = xi (all i), i.e. -s(r_i') = xi,
     and summing, xi = 0: s(r_0') = s(r_1') = s(r_2') = 0.  [The 3x4 conditions ALONE are satisfiable: 6/6 numerical starts, r21/x4num.py.]
 (B) WITH THESE CUTS the ka = 1 system becomes UNIT AT P1 in 4.5 s (r20/dlt1sp.py, ka = 1, 0.05 GB); over Q std > 110 s; slimgb run in progress
     (r20/ka1_q_slim.log, 0.5 GB cap).
STATUS 05:39: sec. 41 (A), (B): ka = 1 hand cuts; unit at P1 with them; Q run in progress.
     RESULT (B): ka = 1 is UNIT OVER Q (slimgb, 0.78 s, 31 MB) with the cuts of (A) (rigorous consequences) -> EMPTY.
 (C) THEOREM (dim Delta = 1, distinct t's) [hand (sec. 40 (D)-(E), 41 (A)) + exact over Q]: such a space lies on the special locus h_0 = e_{j0},
     h_i = e_{j0} + g_i d; with c(x*) = 0 it is a stratum-(III) space (r_0 || e_{j0}; staged refinement, sec. 40 (H)), with c(x*) = d o d it does not exist.
     In particular stratum (II) of (PR3') has NO point with dim Delta = 1 and distinct t's.
STATUS 05:39: sec. 41 (B), (C): ka = 1 EMPTY over Q -> dim Delta = 1 (distinct t) closed for stratum (II). Next: equal t's.
 (D) LEAF 8: THE SPECIAL k_N = 4 MEMBER IS EXCLUDED (given (SL_m0), i.e. under Lemma PFC) [exact over Q, r19/kn4_special.py with printed GBs].
     W = (w_0, w_1, w_2, w_3) = (e_0-e_1, e_2-e_3, (1,1,-1,-1,0), (1,1,1,1,-4)) on rows 0..3, row 4 none (z = (1,1,1,1,0)). Third elements (regime: X_{rk} 3-dim):
       pair (0,1): the ONLY solution (charts xl4, v4; all other charts unit) is (e_2 - e_4) (x) e_4;
       pair (0,2): (e_1 - e_4) (x) e_j with j in {0,1,4} (charts v0, v1, v4; v2, v3 unit);
       pair (1,2): (e_0 - e_4) (x) e_j with j in {2,3,4} (charts v2, v4, and v3 by the column swap 2 <-> 3).
     Two column elements c (x) e_a, c' (x) e_b of L with a != b (sum c = sum c' = 0) need sigma_2(c (x) e_a + c' (x) e_b) = -<c, c'> = 0. Since
     <e_1 - e_4, e_2 - e_4> = <e_0 - e_4, e_2 - e_4> = 1, both other column elements must sit in column 4: L contains the FREE COLUMN
     {C (x) e_4 : supp C in {0,1,2,4}, sum C = 0} on four rows, and Lemma PFC gives dim L <= 8.
STATUS 05:47: sec. 41 (D): leaf-8 special k_N = 4 member -> free column on four rows -> PFC (exact).
 (E) EQUAL t's (h_0 = h_1 = w, h_2 = h, d := w - h) [rigorous structure, not finished]: level of H <=> s(w) = s(h) = s, <w,w> = <w,h> = s^2,
     tau(w,w,h) = s^3; D_2(H) = ab F_ww + (a+b)c F_wh with F_ww = 2 w o w - 2 s w, F_wh = 2 w o h - s(w+h) both in U'; D_3(H) = abc G,
     G = 6 s w^2 - 4 s w d - 6 w^3 + 6 w^2 d in U'; F_ww - F_wh = 2 w o d - s d, so U' contains d, w o d, F_ww, G. Case A (w o d not in C d):
     U' = span(d, w o d), off S = supp(d) w_j in {0, s} (so the columns of H off S are zero or FREE 3-row columns s(a,b,c)), and on S
     d_j (al + 2 w_j) = 2 w_j (w_j - s) when w takes >= 3 values on S (from G in U'). Case B: w constant on S. To be finished (next round).
     Numerics (r21/eqt_num.py): without stratum hinges, LM converges to DEGENERATE spaces (single-row elements, row projections (1,1,1) or
     (1,1,2), column elements); with the stratum-(II) hinges 0/1 so far (floor 1.8e-3).
 (F) dim Delta = 0 (h_0 = h_1 = h_2 = h, H = {lam (x) h : sum lam = 0}) [rigorous structure]: e_2(h) = e_3(h) = 0; U' contains h^2 - s h and s h^2 - h^3;
     the x*-linear conditions from the constrained family lam (x) h: <r_i, s 1 - h> equal for i = 0,1,2 and <r_i, h^2 - s h> = 0 (i = 0,1,2).
     s = 0: h has e_1 = e_2 = e_3 = 0, U' = span(h^2, h^3) vanishes where h_j = 0; s = 1: U' contains h(h - 1), h^2(1 - h), vanishing where h_j in {0,1}.
     To be finished.
STATUS 05:47: sec. 41 (E), (F): equal-t and dim Delta = 0 structure recorded (not finished).
STATUS 05:51: round 21 final. No jobs of mine running.

# ROUND 22 (start 05:52 UTC). Targets: (1) equal t's case A (free/zero columns off supp d, X^(j) trick); (2) case B, dim Delta = 0;
#  (3) classify the special members of (1,1,1,1,0); (4) common-zero-coordinate lemma.
STATUS 05:52: started; equal-t case A as explicit partition systems (S = supp d, F = free columns, Z0 = zero columns).

## 42. ROUND 22: equal t's -- case B closed by hand (to the coordinate-vector locus); case A partitions; dim Delta = 0
 (A) THEOREM (equal t's, case B) [rigorous hand proof]. Case B: w o d = la d (w = la on S = supp d). Level of H gives s(w) = s, <w,w> = s^2, and
     tau(w,w,h) = sum w_j^2 (w_j - d_j) = p_3(w) - la^2 s(d) = p_3(w) = s^3, so p_1 = s, p_2 = s^2, p_3 = s^3, i.e. e_2(w) = e_3(w) = 0. Since F_wh = F_ww -
     (2 la - s) d, the conditions are F_ww = 2 w(w - s) in U' and G = 6 w^2 (s - w) + (6 la^2 - 4 s la) d in U', so W := span(w(w - s), w^2(w - s)) lies in U'.
     (i) If dim W = 2 then U' = W (dim U' = 2), so d = w(w - s)(al + be w); on S (w = la) all d_j are equal, and s(d) = 0 forces d = 0: impossible.
     (ii) If dim W <= 1, w(w - s)(al + be w) = 0, so w takes values in {0, s, nu}; with p_1 = s, p_2 = s^2, p_3 = s^3: s = 0 gives w = 0 (impossible), s = 1
     gives n_nu nu (1 - nu) = n_nu nu^2 (1 - nu) = 0, so w = e_j (a coordinate vector). Then w is constant on S only with j not in S (j in S would force
     S = {j}, d_j = s(d) = 0), so w = 0 on S, h = e_j - d, and H contains the column element (e_0 - e_1) (x) e_j (rows 0,1, column j).  QED
     [The same dichotomy applies to dim Delta = 0 (h_0 = h_1 = h_2 = h, e_2(h) = e_3(h) = 0, W_h = span(h(h - s), h^2(h - s)) in U'): dim W_h <= 1 gives
     h = e_j (coordinate vector: H = {lam (x) e_j} is a free 3-row column); dim W_h = 2 gives U' = W_h EXPLICIT (no U'-unknowns) -- the remaining dim
     Delta = 0 case.]
STATUS 05:56: sec. 42 (A): equal-t case B -> w = e_j (coordinate vector, column element) by hand; dim Delta = 0 reduced to dim W_h = 2 (U' explicit) or h = e_j.
 (B) EQUAL t's, CASE A, |supp d| = 2 [EXACT over Q, staged refinement, r22/eqtA.py, staged_eqtA2.py]: for all partitions (|S| = 2, |F| = 0..3,
     |Z0| = 3 - |F|; WLOG by S_5) the 10 x*-charts (c(x*) = 0) and the c(x*) = w o d system are UNIT over Q: no such space at all.
     |S| >= 3: single charts time out (> 30 s at P1, no seed for the refinement) -- next: hand cuts.
STATUS 05:57: sec. 42 (B): equal-t case A with |S| = 2 EMPTY over Q; |S| >= 3 open.
 (C) EQUAL t's, CASE A, |S| = 3 [exact over Q, r22/staged_eqtA2.py]: c(x*) = w o d (ka = 1) UNIT for |F| = 0, 1; c(x*) = 0 (ka = 0): the x*-charts are
     NON-unit (|F| = 0: 0/10 unit; |F| = 1: 2/10 unit) -- solutions exist, nature unknown (they may be stratum (III), degenerate, or stratum (II));
     tests with a stratum hinge on row 0 (r22/eqtA.py ... H0ab) time out at 60 s. Numerics (r22/eqtA_num.py) too slow here. OPEN; |S| = 4, 5 not run.
 (D) LEAF 8: THE SPECIAL MEMBERS ARE NOT JUST THE TWO KNOWN ONES [numerical + exact check of the jump]. r22/special_find.py found, for k_N = 2,
     a member with EVERY pair's outside-row kernel jumping: m = (1, w^2, w, 0, 0) (w^3 = 1) on rows 0,1 and n_2, n_3 an orthogonal basis of the plane
     P = {1, m, m^2}^perp = {(al,al,al,be,ga) : 3 al + be + ga = 0} (rows 2,3) -- a 1-PARAMETER FAMILY (every orthogonal basis of P works: all single-row
     level conditions hold identically since 1 + w + w^2 = 0). Exact pair tests (r22/kn2_special.py, member n_2 = (0,0,0,1,-1), n_3 = (2,2,2,-3,-3), over
     Q(w)): third elements exist for every pair tested, supported in the column BLOCKS {0,1,2} (where m lives) or {3,4}; pair (2,3) even has a
     2-dim family. No single free column appears, so the PFC route does not apply directly; a block version (free 2-column block?) would be needed.
     So target 3 ("exactly the two known special members") is FALSE as stated; the special locus contains at least this k_N = 2 family.
     [<< CORRECTED r23 (sec. 43 (D), exact over Q(w)): only t in {0, -1/4, -1/3, 1} have a pair-(0,1) third element; the special k_N = 2
      locus is TWO members mod symmetry (M0 = this member, M1 = {(1,1,1,1,-4), (1,1,1,-3,0)}), not a 1-parameter family. >>]
STATUS 06:12: sec. 42 (C), (D): case A |S| = 3 non-unit (open); leaf-8 special members include a new 1-parameter k_N = 2 family (block structure).
     UPDATE (C): first non-unit components found have h = 0 (d = w, degenerate). With the hinge h != 0 (u h_j = 1, j = 0 or 2), the x*-charts with
     J in {3,4} (off S) are UNIT over Q, J in {0,1,2} remain non-unit; a generic 2-plane slice of the hinged chart (00, h_0 != 0) gives 6 points, ALL
     DEGENERATE (single-row elements in every row, all row projections 1-dim). So for |S| = 3, |F| = 0 the 2-dim components contain only degenerate
     spaces (numerical evidence from an exact slice); lower-dimensional components and |F| = 1, 2, |S| = 4, 5 are not settled.
STATUS 06:19: round 22 final. No jobs of mine running (staged |S| = 3 run finished/killed).

# ROUND 23 (start 06:20 UTC). Targets: (1) k_N = 2 special family: symmetry, block-PFC, scan (2,2)/(2,1,1) special loci; (2) case A |S| = 3-5
#  with row hinges + refinement; (3) dim Delta = 0; (4) common-zero-coordinate lemma.
STATUS 06:20: started; scanning the (2,2) and (2,1,1) special loci (r22/special_find.py).

## 43. ROUND 23: the special locus of (1,1,1,1,0) is a BLOCK locus; case A |S| = 3 row hinges
 (A) THE k_N = 2 PARAMETER IS NOT REMOVABLE BY SYMMETRY [rigorous]: the family m = (1, w^2, w, 0, 0) (rows 0,1), {n_2, n_3} an orthogonal basis of
     P = {(al,al,al,be,ga) : 3al + be + ga = 0} (form 12 al al' + 3(al be' + al' be) + 2 be be'). The symmetries preserving the configuration act on P only through
     the column swap 3 <-> 4 (a reflection: be -> -3al - be); permutations of {0,1,2} fix P pointwise (and map m to a multiple of m or of m-bar, which
     the swap w <-> w^2 returns); no continuous symmetry exists. So the orthogonal bases of P modulo symmetry form a genuine 1-parameter family.
 (B) SPECIAL MEMBERS FOR (2,2) AND (2,1,1) EXIST TOO [numerical, r22/special_find.py; all six pair kernels jump]: (2,2): m = (1,0,w,w^2,0) on rows
     0,1 (cube roots on the block {0,2,3}) and m' constant on {0,2,3}; (2,1,1): two members, one with m a cube-root vector on {0,2,3}, one with m
     constant on {1,2,3} and m', m'' zero-sum vectors supported on {1,2,3}.
     BLOCK STRUCTURE (conjecture, supported by all special members found): there is a split of the columns into a 3-block B3 and a 2-block B2 such
     that every single-row vector lies in V_Z = {supported on B3, sum 0} or in V_C = {constant on B3}. [V_Z is orthogonal to V_C, V_Z o V_C lies in V_Z,
     V_C is a subalgebra, and for the cube-root vector m: m o m = m-bar in V_Z, m o m-bar in V_C -- so most single-row level conditions hold
     identically.] V_Z is exactly the census defect type C = V_S, |S| = 3, of the (5,2) spaces without single-row elements (sec. 29 (B)), whose
     two complementary columns are neutral = deletable: a NCOL/neutral-column argument is the natural candidate for the block analogue of PFC.
     (r22/special_find2.py + r22/blockcheck.py: saved members and an automatic block test, running.)
STATUS 06:23: sec. 43 (A), (B): k_N=2 parameter not removable; special members for (2,2), (2,1,1) too, all of block type (3+2 column split).
 (C) CASE A, |S| = 3, ROW-PROJECTION HINGES [exact over Q, r22/rowhinge_sweep.py, sweep2 for |F| >= 1]: for each x*-chart r_{I,J} = 1, each h-chart
     (h_j != 0, j in S; for |F| >= 1 h != 0 is automatic) and each row i, the 10 systems "u (minor_{ab}(h_i, r_i)) = 1" are tested; all UNIT means row i's
     projection is 1-dim on every solution of that chart. |F| = 0: chart 00 with h_0, h_1, h_2: ALL 3 x 10 row hinges UNIT (so every solution there has
     all three row projections 1-dim: single-row elements, outside (PR3')); remaining charts running (r22/rowhinge_30.log); |F| = 1 running
     (rowhinge_31.log). |S| = 4: one hinged chart > 100 s over Q.
STATUS 06:34: sec. 43 (C): case A |S| = 3 row-hinge sweeps running (chart 00 all unit).
     RESULT (C), |F| = 0 COMPLETE: all 30 combinations (10 x*-charts x 3 h-charts) give UNIT for all 3 x 10 row hinges [exact over Q]. THEOREM:
     equal t's, case A, |S| = 3, |F| = 0 has NO space with any 2-dim row projection (and h != 0); every solution is degenerate (all row projections
     1-dim, single-row elements) -- excluded from (PR3') and from stratum (III) as well. |F| = 1 (running): in charts 00, 01 row 2 is always 1-dim
     (all 10 hinges unit), rows 0,1 have non-unit/timeout hinges (stratum-(III) candidates with row 2 a line; no stratum (II) proper there).
     |F| = 2 sweep started (rowhinge_32.log).
STATUS 06:54: case A |S|=3 |F|=0 EXCLUDED (row-hinge sweep 30/30 unit); |F|=1: row 2 always a line so far (stratum III at most); |F|=2 running.
 (D) *** THE k_N = 2 "1-PARAMETER SPECIAL FAMILY" IS NOT SPECIAL: ONLY TWO MEMBERS SURVIVE (mod symmetry) *** [EXACT over Q(w), t a ring variable,
     std + eliminate; r22/kn2_fam.py, r22/kn2_elim.py, r22/kn2fam_sweep.sh -> kn2fam_sweep.log]. Parametrise the family by n_2 = (t,t,t,1,-3t-1),
     n_3 = (3t+2,3t+2,3t+2,-12t-3,3t-3) (<n_2,n_3> = 0 identically; with the row swap 2 <-> 3 this covers every orthogonal basis of P, the isotropic
     degenerate case included; t = -2/3 is the t = 0 member with rows 2,3 swapped). Pair test (third element xi of X_{rk}, gauges, chart xi_XC = 1,
     hinges u0 (3t+2) = 1 and u1 t = 1), ALL 13 charts of each pair:
       pair (0,1): charts in columns {0,1,2} UNIT; the charts xn3, v3 give t = -1/4, xl4 gives t = -1/3, xn4 gives t = 1, v4 gives (3t+1)(t-1) = 0.
       pairs (0,2), (0,3): third elements for EVERY t (dim 1, t-projection 0); pair (2,3): for every t (2-dim family over each t).
     Round 18 (C) [rigorous given the kernel]: ONE pair with no third element gives dim X_{rk} = 2, a contradiction in the regime. Hence every member
     with t not in {0, -1/4, -1/3, 1} is EXCLUDED. Up to symmetry the survivors are TWO members:
       M0 (t = 0):  n_2 = (0,0,0,1,-1),  n_3 = (2,2,2,-3,-3)     [the round-22 member]
       M1 (t = 1):  n_2 = (1,1,1,1,-4),  n_3 = (1,1,1,-3,0)     [t = -1/3: rows 2,3 swapped; t = -1/4: columns 3,4 swapped and rows swapped]
     So target 1(a)'s "one exact member suffices" holds in the form "two exact members suffice". M1 carries the PFC line m0 = (1,1,1,1,-4) as a
     single-row element (row 2). At M1 the pair-(0,1) third elements are finitely many per chart (xn4 chart: linear equations + one quadric).
     [The round-22 statement "every orthogonal basis of P works" was correct only for the existence of the members, not for their specialness:
     flagged in place in RESULT ROUND 22 (3) and sec. 42 (D).]
STATUS 07:06: sec. 43 (D) EXACT: k_N=2 'family' reduced to two members M0 (t=0), M1 (t=1) mod symmetry; round-22 claim corrected in place.
 (E) THE TWO k_N = 2 SURVIVORS: M0 IS IMPOSSIBLE, M1 GIVES A FREE COLUMN (-> PFC) [EXACT over Q (w a variable, w^2+w+1), std, dim/vdim + solve
     of the 0-dim pair varieties, all 13 charts per pair; r22/kn2_pts.sh, r22/kn2_span_check.py]. Notation: (c) (x) v = rows c, row vector v; r_i = e_i.
     M0 (t = 0): pair (0,1): X_{01} third element in {(r_2 - r_4) (x) mbar, (r_2 - r_4) (x) e_k (k = 0,1,2)} (mbar = (1,w,w^2,0,0); vdim 8 = 2 elements x
       2 conjugates per chart, all other charts empty). Pair (0,2): {(r_1 - r_4) (x) e_3, (r_1 - r_4) (x) e_4} only; by the row swap 0 <-> 1, pair (1,2):
       (r_0 - r_4) (x) e_j, j in {3,4}. In the regime every X_{rk} has a third element, so L contains (r_0 - r_4) (x) e_j and one of:
         (r_2 - r_4) (x) e_k: column elements in different columns need <r_2 - r_4, r_0 - r_4> = 0, but it is 1 -> impossible;
         (r_2 - r_4) (x) mbar: sigma_3 of span{m (x) r_0, (r_2 - r_4) (x) mbar, (r_0 - r_4) (x) e_j} has the c0 c4 c5 coefficient <m, mbar> = 3 != 0
         (hand computation, confirmed exactly: r22/span_M0.sing gives 3 c0 c4 c5 + ...) -> impossible.
       => M0 IS EXCLUDED [exact/rigorous, unconditional].
     M1 (t = 1, n_2 = (1,1,1,1,-4), n_3 = (1,1,1,-3,0)): pair (0,1): the ONLY third element is (r_3 - r_4) (x) e_4 (charts xn4, v4; others empty, incl.
       the t-sweep). Pair (0,3): (r_1 - r_4) (x) e_3 or (r_1 - r_4) (x) e_4; the first is not orthogonal to r_3 - r_4 (column elements in columns 3, 4)
       -> (r_1 - r_4) (x) e_4; by the row swap 0 <-> 1, (r_0 - r_4) (x) e_4. So L contains the FREE COLUMN {C (x) e_4 : C_2 = 0, sum C = 0} on rows
       {0,1,3,4}; Lemma PFC gives dim L <= 8 (given (SL_m0)). [Span of the 4 single-row elements + the free column: level, exact, r22/span_M1.sing.]
     => THE WHOLE k_N = 2 CONFIGURATION OF (1,1,1,1,0) IS CLOSED (M1 under Lemma PFC, everything else unconditional).
STATUS 07:10: sec. 43 (E): k_N=2 closed -- M0 excluded (orthogonality / sigma_3), M1 forces free column 4 -> PFC.
 (F) BLOCK FAMILY B = the (2,1,1) member B and the (2,2) member [exact over Q(a), 6a^2+3a+1 = 0 (a = (-3 +- sqrt(-15))/12), t a ring variable;
     r22/famB.py, r22/famB_sweep.sh -> famB_01.log ...]. In block coordinates (B3 = {0,1,2}, B2 = {3,4}): rows 0,1 m' = (a,a,a,1,b), b = -1-3a
     (the unique isotropic zero-sum vectors constant on B3, up to scale); rows 2,3 an orthogonal basis of V_Z: n_2 = (1,t,-1-t,0,0),
     n_3 = (1+2t,-(2+t),1-t,0,0). At t^2+t+1 = 0 (n_2 = n_3 = cube-root vector, isotropic) this is the (2,2) member; the numerical (2,1,1) member A is
     a member of the k_N = 2 family of (D) up to a column permutation (block {0,2,3}), at a generic t -> already EXCLUDED by (D).
     Pair (0,1): the charts in the block columns give third elements only for t in {0, -1, 1, -2} (one S_3-orbit: {e_0 - e_2, e_0 - 2e_1 + e_2});
     BUT the charts xl3, xn3 (column 3, off-block) give a 2-dim family of third elements for EVERY t (dim 3, t-projection 0). By hand these are
     the "free 2-column block" elements xi = p (x) e_3 + q (x) e_4 with p, q supported on rows {2,3,4}, s(p) = s(q) = 0 (the sigma_1 and the
     m'-cross sigma_2 give s(p) + s(q) = 0 = s(p) + b s(q), b != 1) and <p,q> = 0 (sigma_2 of xi); all other cross terms vanish by s(n_i) = 0,
     <n_2,n_3> = 0, <m',n_i> = 0, e_2(m') = 0. So family B is the genuine "free 2-column block" case: no pair forces a single element. OPEN.
     (Pairs (2,3), (0,2), (0,3) sweeps running/queued in the same pool job; see famB_*.log.)
 (G) UPSTREAM LEMMAS (coordinator, r23) [read from the working tree lean/PEqualNP/Outside/, no git used]:
     L_gct_110 (complementary blocks): L1 on A x B, L2 on A^c x B^c, both level => L1 + L2 level. A SUFFICIENCY lemma: it explains the block members
       (M0 = span(m (x) r_0, m (x) r_1) on {0,1} x {0,1,2} plus (e_3 - e_4) (x) r_2 on {2,3,4} x {3,4}: complementary blocks), but gives no upper
       bound, so it is not by itself a block-PFC. In family B the rows 0,1 (m' has entries in B2) are not block-supported, so it does not even apply.
     L_gct_111 (row-wise product spaces): if t is level whenever row i of t lies in V_i, then sum dim V_i <= 4. COROLLARY [rigorous]: for any level
       L, the single-row parts Z_i = {v : v (x) r_i in L} satisfy sum_i dim Z_i <= 4 (their sum is a product subspace of L). This reproves at
       once SR5 (z = (1,1,1,1,1)), SR2111 ((2,1,1,1,0)) and (2,1,1,1,1). Transposed (perm(J + t^T) = perm(J + t)): the column parts
       C_j = {c : c (x) e_j in L} satisfy sum_j dim C_j <= 4. For the PFC situation (C_j >= 3-dim) the other columns carry at most a 1-dim column part.
       Block analogue (candidate lemma, not proved): for the "2-column block" part K = {xi in L supported on (rows) x B2}, every xi = p (x) e_3 + q (x) e_4
       has <p,q> = 0, s(p) = s(q) = 0 after the m'-cross terms; I do not see an L_gct_111-type bound for such coupled (non-product) spaces yet.
STATUS 07:19: sec. 43 (F) family B: pair (0,1) has 2-column-block third elements for all t (open); (G) L_gct_110/111 assessed (111 gives sum dim Z_i <= 4: reproves SR5/SR2111).
 (H) CASE A, |S| = 3, |F| = 1 (partial; sweep stopped at the 30-min job limit) [exact over Q]: x*-charts 00, 01, 02, 03, 04, 10 (6 of 10), h != 0
     automatic: row 2's projection is 1-dim on every solution (all 10 row-2 hinges UNIT); chart 04 is entirely unit. So these charts contain no (PR3')
     space (at most stratum (III)/degenerate). Charts 11-14 not run; |F| = 2 not run (sweep started and stopped for the k_N = 2 work).
     |S| = 4: one hinged chart > 100 s over Q (needs hand cuts first).
STATUS 07:24 UTC: case A |F|=1 sweep stopped at 6/10 charts (row 2 always a line); famB sweep (pool, 1 core, <= 0.5 GB, <= 25 min) still running.
STATUS 07:22 UTC: round 23 final. Pool job famB sweep (1 core, <= 0.5 GB, self-terminates by ~07:38) still running; nothing else of mine.

# ROUND 24 (start 07:23 UTC). Targets: (1) block-PFC for family B; (2) case A |F| = 1 charts 11-14, then |F| = 2; (3) |S| = 4, 5 hand cuts;
#  (4) dim Delta = 0, common-zero lemma.
STATUS 07:23: started.

## 44. ROUND 24: family B excluded outright (no block-PFC needed); leaf-8 block special members all closed
 (A) *** FAMILY B IS EXCLUDED *** [EXACT over Q(a), 6a^2+3a+1 = 0, t a ring variable, std; r22/famB.py, famB_sweep.sh -> famB_23.log, plus the
     same 13 charts with the hinge u0(1+2t) = 1 removed (t unrestricted) and at t = -1/2]. For pair (2,3) (third element xi of X_{23} on rows {0,1,4},
     gauges xi_0[3] = xi_1[3] = 0 since m'_3 = 1) ALL 13 charts are UNIT, for every t. So X_{23} is the 2-dim gauge for every member of family B, and
     Round 18 (C) gives the contradiction in the regime. Family B = rows 0,1 m' = (a,a,a,1,-1-3a), rows 2,3 any orthogonal basis of V_Z: n_2 = (1,t,-1-t),
     n_3 = (1+2t,-(2+t),1-t) on the block (n_2 with n_2[0] = 0 is (0,1,-1) ~ t = 0 under the block S_3, which fixes m'); it contains the (2,2) member
     (t^2 + t + 1 = 0, n_2 = n_3 = cube-root vector) and the (2,1,1) member B.
     [The pair-(0,1) 2-column-block third elements of sec. 43 (F) are irrelevant: one empty pair suffices. Pairs (0,2), (0,3): third elements
     for every t (charts xn1..v4: points, and 1-dim in columns 3,4).]
 (B) STATUS OF THE (1,1,1,1,0) SPECIAL MEMBERS FOUND SO FAR: Fourier (excluded), rigid "three m + w" member (PFC), k_N = 4 special member (PFC),
     k_N = 2: M0 excluded, M1 (PFC); (2,1,1) member A (inside the k_N = 2 family: excluded unless M0/M1); family B incl. the (2,2) member: excluded.
     CAVEAT: the generic-member exclusion (sec. 38 (C)) and the completeness of the special list (special_find scans) are NUMERICAL. The exact
     t-parametric pair test (as in sec. 43 (D), 44 (A)) over each whole configuration variety would make leaf 8 rigorous (mod PFC) -- next item.
STATUS 07:25: sec. 44 (A): family B EXCLUDED (pair (2,3) empty for all t, exact). Case A |F|=1 charts 11-14 running (split jobs).
 (C) EQUAL t's, CASE A, |S| = 3, |F| = 1: COMPLETE [exact over Q, r22/rowhinge_sweep3.py charts 11-14 -> rowhinge_31.log, now 10/10 charts]: in every
     x*-chart row 2's projection is 1-dim on all solutions (all 10 row-2 hinges UNIT; charts 04 and 14 entirely unit). So |S| = 3, |F| = 1 contains
     no (PR3') space (rows 0,1 non-unit hinges: stratum (III)/degenerate only).
 (D) EQUAL t's, CASE A, |S| >= 4 VIA A CLASS REDUCTION [rigorous cut + exact over Q, r24/eqtA_cls.py, r24/cls_sweep.sh]. The hand cut "G in U'"
     (sec. 41 (E)/42) says (6 - 3be) w_j^2 - (3al + 4s + ep) w_j - ga = 0 for every j in S, a FIXED quadric. Non-degenerate case: w takes at most two values
     on S, and exactly two since dim U' = 2 needs w non-constant on supp d (minor_{01}(d, w o d) = d_0 d_1 (w_1 - w_0)); WLOG w_0 != w_1 (S_{|S|}), so
     w = (wA on class A, wB on class B) with 0 in A, 1 in B; d is kept GENERAL (the F_ww cut fixes d_j only where al + be w_j != 0). Degenerate case
     ('deg'): be = 2, ga = 0, 3al + 4s + ep = 0, w general.
     |S| = 4, |F| = 0, classes (3,1) = 0100 and (2,2) = 0110, hinges h_0, h_1: ALL 10 x*-charts + ka = 1 UNIT (fast). [Hinges h_2, h_3 running,
     r24/cls_40x.log; d general means h != 0 must be split over all S columns.] 'deg': memory-out at 0.5 GB in 8/11 charts (h_0) -- needs a hand cut.
STATUS 07:52: case A |S|=3 |F|=1 COMPLETE (no (PR3')); |S|=4 class-reduced charts unit (h0,h1); deg case memory-bound.
 (E) dim Delta = 0: x* IS A FUNCTION OF h COLUMNWISE [rigorous hand derivation; new]. X = {lam (x) h : sum lam = 0} (+) C x*, x* = (r_0, r_1, r_2), s(h) = 1,
     e_2(h) = e_3(h) = 0, U' = W_h = span(h^2 - h, h^2 - h^3) (2-dim). The e^1-coefficient of D_2(lam (x) h + e x*) is -sum_i lam_i V_i with
     V_i = s(r_i)(1 - h) + (2h - 1) o r_i - <h, r_i> 1; by the level cut <r_i, 1 - h> = kappa (all i), V_i = (2h - 1) o r_i - s(r_i) h + kappa 1. So for
     delta = r_i - r_k:  (2h - 1) o delta - s(delta) h  lies in W_h, i.e.  (2h_j - 1) delta_j = s(delta) h_j + h_j (h_j - 1)(al + be h_j)  for every j.
     The gauge r_i -> r_i + nu_i h (sum nu = 0) shifts al by 2(nu_i - nu_k), so WLOG al = 0 for delta_1 = r_1 - r_0, delta_2 = r_2 - r_0. With c(x*) =
     r_0 + r_1 + r_2 in W_h (c_j = h_j (h_j - 1)(al_c + be_c h_j)): r_0 = (c - delta_1 - delta_2)/3. Hence every row of x* is r_ij = G_i(h_j) with
     (2x - 1) G_i(x) a polynomial (deg <= 4) depending on SIX parameters (S_1, B_1, S_2, B_2, al_c, be_c) -- x* has 6 projective parameters instead of
     13 unknowns, and columns j, k with h_j = h_k carry identical columns of X. (s(h) = 0 variant: 2 h_j delta_j = s(delta) h_j + h_j^2 (al + be h_j),
     c_j = h_j^2 (al_c + be_c h_j): polynomial in h_j on supp h.)
     Exact system r24/dlt0d.py (h, the 6 parameters, level of X, D_2/D_3 in U' by minors): out of memory at 0.5 GB even with the level conditions
     only -> QUEUE line ST3-DLT0D (12 charts, 4 GB each, <= 25 min per chart; P1 triage, then Q).
STATUS 07:54: sec. 44 (E): dim Delta = 0 x* = function of h (6 parameters); QUEUE ST3-DLT0D appended (4 GB/chart).
 (F) STATE AT ABORT (08:03 UTC). Equal t's, case A: |S| = 2 empty; |S| = 3, |F| = 0 excluded, |F| = 1 no (PR3') (10/10 charts), |F| = 2 not run;
     |S| = 4, |F| = 0 non-degenerate class cases (0100, 0110; hinges h_0..h_3; 10 x*-charts + ka = 1) ALL UNIT; |S| = 5, |F| = 0 classes 01000, 01100
     unit for hinges h_2..h_4 (h_0, h_1 not run); |S| = 4, |F| = 1 not completed (r24/cls_41.log partial). DEGENERATE quadric case (be = 2):
     h = mu(w), mu(x) = x(2s + al)/(2x + al) (Moebius, fixes 0 and s), level of H leaves an irreducible 2-dim family of (w, al) (r24/degH.sing); the
     x*-system memory-outs at 0.5 GB -- open. dim Delta = 0: function-of-h reduction (E); ST3-DLT0D queued but NOT run; pool splits (r24/dlt0e.py,
     G-mode, level-only) still memory-out at 0.5 GB. Leaf 8 (1,1,1,1,0): all special members found are closed modulo Lemma PFC (k_N = 2: M0
     excluded, M1 -> PFC; family B incl. (2,2) and (2,1,1) members excluded; k_N = 4 special and rigid members -> PFC); the generic-member exclusion
     and the completeness of the special list remain NUMERICAL (exact configuration varieties memory-out at 0.5 GB, r24/cfgvar.py).
STOPPED 08:03 UTC (coordinator: L-gct-210 aborted). No jobs of mine running.
     [correction to (F): r24/cls_41.log shows |S| = 4, |F| = 1 non-degenerate classes 0100, 0110 ALL UNIT (10 x*-charts + ka = 1); only its deg case was not run.]
