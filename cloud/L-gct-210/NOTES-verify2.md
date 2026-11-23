# NOTES-verify2 (role: verify2; round 1: 16:09-16:49; round 2: 16:49-17:31; round 3: 18:06-18:49; round 4: 18:57-19:27; round 5: 19:33-20:04)

## RESULT ROUND 5 (verify2, 20:04) -- spec audit (COMPUTE-ERRATA.md) + rows R4.10/R4.14/R4.15, verifyfl R4/R5, stage2 R6, stage3 sec. 26, reg2
 PART 1: AUDIT of handoff/HANDOFF.md sec. 2, handoff/oracle.py, COMPUTE-{rows,verifyfl,stage3,reg2,stage2}.md -> /home/claude/work/L-gct-210/COMPUTE-ERRATA.md
  Six [A] items (would give a wrong conclusion or a meaningless run):
   A1 COMPUTE-stage3 sec. 0 says "Level spaces of dim 8 exist": false (largest known 7); two "calibrations at dim 8" cannot succeed.
   A2 COMPUTE-stage3 (5c): the pure-plane CLAIM is false. Counterexample: P_c = P_d = P_e = span(e_1, e_2 + e_3), P_a = P_b = span(e_2 - e_3, e_4),
      rho_a = rho_b = e_2 - e_3: all hypotheses hold, four columns used. N2-X is unaffected (it excludes P_c = P_d = P_e by (Q5J)/(P2));
      correct three-way conclusion given.
   A3 COMPUTE-verifyfl C/D (HANDOFF C3): the scripts under-sample (28/44/40/60/45 points vs 34/69/69/125 monomials) and the acceptance
      list has no fresh-point test: a spurious hit would be reported as a counterexample to (SL_m) or as a (5,1) space. Test added.
      (Empirically 19 of 19 hits for k = 3 were genuine: a risk, not an observed failure.)
   A4 "unit ideal modulo p" is evidence, not proof (HANDOFF C4, verifyfl A/B/E, stage3 2/5, rows X1-X4).
   A5 rows/clm.py samples N = 140 points: too few for d = 7 (210 quartic coefficients) and for 5x5 with d = 7, 8 (462, 792);
      run_clm.py does not pass N. reg2/ext7.py: 300 points vs 329.
   A6 "(S6') dim Omega <= 2 without a full free row" (HANDOFF branch 4, C2) is FALSE: reg2's exact family M* (confirmed by me: level
      exactly for 3 rational members; (dim T_1, dim Omega, rank, FO2) = (11, 4, 5, 8); no full free row). Target is (S6-FO2).
  [B]: A_m has dim 16, not 17 (verifyfl A: 13 unknowns; D: Gr(5,16)); "(NCOL_3) + (DI_4x4) => no (7,3)" needs (DI_5;2); C1 acceptance should
   be d - e >= 4; "7-dim 4x5" decides the gap only if e <= 3; FO2 on unpolished LM output under-estimates T_1.
  No errors: oracle.py (the conjugation is handled correctly; three spot runs), all definitions of COMPUTE-rows (re-derived incl. Walsh
   coordinates P_2 = 8 sum x^2, P_3 = 64 perm_3(x), padding, (X2)-(X4)), COMPUTE-reg2 (19:52 version), COMPUTE-stage2 (S3 formulas re-derived).
 PART 2: VERIFICATION (own re-derivation; no error found)
  rows R4.10 (a)-(d) transposed defect construction + padding lemma                     VERIFIED
  rows R4.14 Theorem NCOL-S (a), (b)                                                   VERIFIED (D^(1)(Y) m = -2S m + 4 c o m - 2(c.m) 1 recomputed)
  rows R4.15 (F1), (F2), (FS-DEC) with the lists for e = 1, 2, 3, (F1^T)               VERIFIED
  verifyfl R4.1 Lemma QB, R4.3 Theorem PS, R4.4 PR-RED, R4.5 THEOREM PR3               VERIFIED (all tau-values; det Q_m = -<m,m>/2; remark (i))
  verifyfl R5.1 Lemma C', R5.2 Lemma 3C, R5.3 Lemma NP                                 VERIFIED; the blueprint fact "7 pairs" confirmed numerically
  verifyfl R5.4 Lemma T, R5.5 Prop I', Prop V, R5.6 Theorem SL3-RED (extra)            VERIFIED (my ID8 reads -2<chi_3,u><chi_3,u'> + 2<chi_2,uu'>;
                                                                                        it agrees with the notes' form where it is used)
  stage2 R6-2 cross-family theorem                                                     VERIFIED (T_1 by hand for all b != 0, a not in C1; rank 5 by the
                                                                                        block argument + numerics; the polar formula of P_2 not recomputed)
  stage2 R6-5 (z_i = 3 => four minimal pairs), (T2), lam = 5 lemma, Lemma (z_i = 3)    VERIFIED
  stage3 sec. 26 (round 7): (c1)-(c5), (A1), (A2), (A3) F1, (A4) F3 and F4a, (B)       VERIFIED ((A4): every input of N2-X re-derived for the pair
                                                                                        with lam = 4; the isotropy count replaces (beta-0))
  stage3 sec. 26 (A5) F4b structure, (C5)-(C8)                                         (C5) checked; the rest NOT verified (open families)
  reg2 section 1 (L1-L5), 4.3 (M* level by hand + EC), RESULT C (S6-FO2 => no a_r = 2) VERIFIED; (S6') is false (see A6); the taxonomy F/NC/DR/M*
                                                                                        is numerical (not rerun beyond the 20 files of round 4 and M*)

## RESULT ROUND 4 (verify2, 19:27) -- stage2 RESULT-R5, stage3 sec. 24 (round 6), rows R4 + FL2* consequences, reg2
 Method as before. No error found. One statement is unproved as written ((Q-r)(iii) for columns; partial proof supplied), two wordings are
 imprecise, three numerical readings are tolerance-sensitive (conclusions unaffected).
 1. STAGE 2 RESULT-R5
    Lemma FO2                                                                   VERIFIED
      Exact statement: M a linear subspace of a level space L. T_1(M) = {t in C^{5x5} : <C(J+m), t> = 0 for all m in M} (C = matrix of 4x4
      subpermanents). q_m = Hessian of perm at J + m, a symmetric BILINEAR form on C^25 with entries perm_3((J+m) without rows i,k and
      columns j,l) (0 if i = k or j = l). Then L is inside T_1(M) and q_m(t,t') = 0 for t,t' in L; so for every q in span{q_m}:
      dim L <= dim T_1(M) - ceil(rank(G)/2), G = Gram matrix N^T Q N (plain transpose, NOT conjugate) of q on a basis N of T_1(M); the
      rank is the rank of the restricted form itself (= dim T_1(M) - dim of its radical), not modulo M or L. Proof: eps- and eps^2-
      coefficients of perm(J + m + eps t) = 120, polarisation on L, and "isotropic subspace <= dim - rank + floor(rank/2)".
      Addition: M lies in the radical of q_m on T_1(M), so rank <= dim T_1(M) - dim M and the bound is always >= dim M.
      Sanity with my own implementation (verify2/fo2lib.py, fo2_known.py): (dim T_1, rank, bound) = (8,1,7) for all nine 7-dim spaces of
      my collection, (6,1,5) for K5, with M = L; with random M of codimension 2 the bound is >= dim L in all cases. My first version
      had exactly the bug the author reports (conjugated null basis = hermitian restriction; bounds 5 < 7); fixed.
    Theorem FO-M* (dim T_1(M*) = 8 for ALL parameters) and R5-7 (a) (dim <= 7)   VERIFIED -- closes the GAP of my round 3
      (a)-(d) re-derived; the four exact facts confirmed with my own rational code (verify2/fo_mstar_exact.py): (s1) all perm_4 = 24;
      (s2); (s3) rank 17, T_1(W_7) = W_7 (+) C tau, also directly from 40 cofactor vectors; (s4) dim T' = 10 and the a_c-, a_e-
      coefficients of Q_a, Q_b vanish identically on T'. W_7 is parameter-free, so one exact computation covers all parameters.
      P_2(tau) = -8 checked. FO2 on M* at 5 parameter sets (2 complex): (8,1,7).
    Cases A and B of family (alpha) (R5-2)                                       VERIFIED
      "no zero column"; support analysis of Case A (wording: in (3,3,2) the 2-set either meets S_c cap S_d or meets S_c in ONE point --
      the text says "meets the triple intersection"); Xi* gives rho' = 0; Case B for 0, 1, 2, 3 nonzero h. L_a + L_b = M* follows.
    R5-3 kernel condition, R5-4 formulas (a)-(c)                                 VERIFIED
    Reduction of REG1 to (B1)/(B2)                                               VERIFIED (uses Lemma C, Theorem N and its transpose, S3-1, (Z3))
    Formulation (Q-r): (i), (ii), (iii) rows, (iv)                               VERIFIED
    (Q-r)(iii) columns "every column projection of L_r has dim <= 3"             GAP (no proof in the notes; Lemma C is about two rows)
      REPAIR (own proof): dim pi^c(L_r) <= 3 for every column c EXCEPT possibly one column c with kappa^r = e_c and kappa'^c = e_r
      (the entry (r,c) vanishes identically on L). Reason: pi_{row r + column c}(L) lies in the 9-dim cross space and is killed by the
      functionals <kappa^r, t_r> and <nu, t^c> (nu any annihilator of column c); they are independent unless both are multiples of
      t_rc, so dim(L_r cap L^c) >= 2. In the exceptional case only dim pi^c(L_r) <= 4 holds, and then L = L_r + L^c. Impact: none on
      the surveys (r5_Lr3/r5_Lr4 filter by row projections only); (iii) should be restated with the exception.
    Numerical applications recomputed with my code: N2 block examples (11,7,7) and (13,8,9); L_r candidates (9,3,7) and (10,5,7);
      r5_Lr3_1_0 is not level (the author's "spurious" output). r5_Lr_2_1 (inadmissible) contains 1e-6 singular values: (7,2,6) at
      tolerance 1e-9, (12,7,8) at 1e-5 (author: (11,6,8)). Cross family (R6-2/R6-3): (10,5,7) for b != 0, (13,8,9) for b = 0.
    STILL NUMERICAL (author's own flag): every diagonal block with a two-row column lies in family (alpha). Superseded by N2-X.
 2. STAGE 3 sec. 24 (round 6)
    Lemma S3-2 (b),(c); Lemma S3-3 (b); Lemma S3-4; "planes well defined"        VERIFIED
    Lemma S3-5                                                                   VERIFIED (all coefficient equations redone; the printed P_2 omits
      the term a c s(gam_y) s(p), which vanishes because y is level)
    Lemma 5V                                                                     VERIFIED with an OWN PROOF (the notes give a sketch only):
      three parallel vectors u: U^3 = 0, so u is a unit vector or 2-sparse and then U^2 V = 0 puts all five into C^{mn}; span of
      dim 2 without three parallel: the trilinear map vanishes on U (3, 4 or 5 distinct lines), so U is a coordinate plane; span of
      dim >= 3 without three parallel: impossible (pair with nonzero product, (G2), the two sub-cases "three distinct lines" and
      "two parallel" with |supp x| = 1, 2, 3, 4). Exact pattern filter (verify2/lemma5v_patterns.py): 736 support patterns, 615
      killed by a one-monomial coefficient, 44 inside the conclusion, 77 left to the hand proof.
    THEOREM PL4 (four planes and a line)                                          VERIFIED
      Part 1 ((PL4-1), shapes (I), (D), (B)); Part 2: concurrent-or-coplanar; (2B) v_0 = e_j and |supp v_0| >= 2; (2A)(i) incl. the
      sub-cases "P_k = C^T" and "P_k = P_l = C^T" that the text does not spell out (same computation); (2A)(ii) |R_w| = 4, 0, 1, 2, 3
      with the annihilator table of sec. 21 (the three spaces P_m P_r, w P_m, w P_r span Sym^2 V_3: checked).
      Own numerical probe (verify2/pl4_probe.py; s(w) = 0, |w| = 1, triple products of norm >= 0.5): 35 unconstrained starts gave 9
      exact solutions = 8 (3col) + 1 type I, none of another type; 8 starts with four prescribed non-vanishing columns: none converged.
      Slow solver (10-35 s per start): weak corroboration only.
    THEOREM S3-G and extension S3-G'                                              VERIFIED, given Lemma Q4-gen on L_e
      type I by S3-5; (3col) by the checked L157 (statement read: 3-row level space with zero row sums has dim <= q - 1); only
      gam(L_e) (not all of C(L_e)) is needed inside C^{N_3}. Q4-gen is applied to L_e with the incidence data of case N1 (3-dim row
      kernels, m in {1,2}, disjoint m = 2 pairs, no single-row element in L_e); I checked that these data hold, not the normal forms again.
      S3-G' (1) (one and two rank-one maps), (2), (3) re-derived.
    (C2), (G)(i)-(v)                                                             VERIFIED except the pigeonhole remark in (G)(iii) (not checked)
 3. ROWS R4 and FL2* consequences                                                VERIFIED
    R4.1 Hyperplane Lemma; R4.2 (a)-(d); R4.3 RS-HYP (e = 1, 2, 3; upstream L067 read: k dim W <= M for vanishing power sums 2..k);
    R4.7 Lifting Lemma, D-UP, C-UP; R4.11 ((D)_8 + (DI_5) <=> no 8-dim level space); FL2* (a) (dim(m o U') = 3 iff m has <= 1 zero;
    2 for two zeros), (b) both statements.  Not checked: R4.10, R4.14, R4.15 (not on my list), all numerics of R4.4-R4.13.
 4. REG2
    Phi(L_r) inside R_r^perp of dim a_r - 1                                      VERIFIED
    Omega criterion (dim L - dim L_r <= dim Omega(L_r) - 1)                       VERIFIED (tau_r in T_1(M): derivative of (1-4e)(1+e)^4 at 0)
    Numbers for the six-dim 4x5 spaces                                           CONFIRMED with my own code for all 20 (verify2/reg2_fo2.py):
      19 x (dim T_1, rank, FO2 bound, dim Omega) = (9, 3, 7, 2); rc45 = (10, 4, 8, 3). Caveat: three files (clm_p4_d6_defect3_s3,
      seed_d6_e3_t1, seed_d6_e3_t6) have a smallest kept singular value of 2e-7 .. 1e-9 relative in the cofactor system (their
      reduced bases contain entries of size 1e-7 that cannot be dropped: level error 4e-5 after dropping); read at tolerance 1e-6
      they give (10, 4, 8, 2). Either way the bound is < 9 and Omega = 2: none of the 20 known spaces is the L_r of a 9-dim level space.
      This does NOT close a_r = 2: it is a statement about the known spaces only; T_1 and the rank are semicontinuous, so a proof
      needs a classification of 6-dim 4x5 level spaces or a structural bound (reg2's target dim Omega <= 3).

## RESULT ROUND 3 (verify2, 18:49) -- stage3 sec. 21 (THEOREM N2-X), verifyfl DI5-R3, stage2 RESULT-R4, stage3 secs 18-20/22, rows DI + round 3
 Method as before (own re-derivation line by line; exact machine checks where a claim is computational). No error found; one textual
 slip, and one claim that is proved only at sampled parameters (so stated by its author).
 0. STAGE 3 sec. 21: THEOREM N2-X (family N2 does not occur)                 VERIFIED
    Inputs re-derived: (Q4) for the three 4-sets {a,b,k,l} (the fifth row i in S has L_i = Y_kl (+) X_li; forms (t1)/(t2) apply, incl. the
    triangle form when w || w'; ranks 16 from round 2); (Qb)/(Qa) (the form is antisymmetric under two transpositions, hence 0 on a
    2-dim space); (Q5) and (Q5J); (P2) (all three beta_ik alternating, g_cd = g_ce - g_de); (NT), (NT'); (M7) = (N2-d); pairwise
    meeting of P_c, P_d, P_e; lam_ab = 5 impossible; Lemma I3.
    Proof re-derived: STEP 0; (alpha)(1),(2); (A1) D and B; (A2); (beta-0) (the forced plane span(e_1-e_2, e_3-e_4) and the skew
    argument); polarity (S2 = V_3V_3 resp. PV_3); (beta-2) and (beta-1) for all six types.
    EXACT support (verify2/n2x_annihilators.py, n2x_annihilators2.py, n2x_scan.py; rational arithmetic): dim K(V_3V_3) = 3, 2, 1, 0, 1, 0
    for types (1,1), (1,2), (1,3), (1,4), (2,2), (2,3) (column scalings are automorphisms of A, so alpha = 1_A, beta = 1_B is general);
    K(PV_3) for EVERY plane P spanned by integer combinations with coefficients in -2..2 (349 planes per type): the dimension equals
    the value claimed for its sub-case, no deviation, and no one-dimensional K is spanned by a monomial; K = C H^* L_0 with
    Lam(u_0) = C l_0 and K = C Q_beta + y_x Lam(u_0) confirmed by exact membership.
    SECOND PASS (18:47, whole of sec. 21 re-derived once more from scratch): all annihilators now also by HAND for EVERY plane P, not
    only on the scanned ones: (2,3) Q = q12 y1y2 + y1 l1 + y2 l2 + Q_B: P = V_B gives C Q_beta; P = C u0 + C h gives H^* Lam(u0) with
    dim Lam(u0) = 1 (M_u invertible for zero-free u; for u = (beta_v,-beta_u,0) beta is not in im M_u and ker M_u = C u^*) and l0 never a
    unit vector; P = C u0 + C(h+u1) gives l in Lam(u0) cap Lam(u1) = {l : l.(A_B)_2 = 0} = 0, then Q = c Q_beta and c = 0. (2,2): e5 not in P
    gives P V_3 = V_3 V_3 (the kernel of Sym^2 V_3 -> A_2 is C e5^2), K = C H^*H'^*; P = C e5 + C(xh + x'h'): the six coefficient equations
    give L = 0 if x x' != 0 and L in C H^* if x' = 0. (1,3), (1,4), (1,2), (1,1) inside (A_N)_2 as in the text. Polarity statement
    (annihilator of P_k P_l in Sym^2 V_3^* is span(l_k^2, l_l^2); three squares of pairwise non-proportional forms are independent) and
    T0 (3x2 block: the quadric s(x)s(y) - <x,y> has rank 5 on the hyperplane, so isotropic spaces have dim <= 2) re-proved.
    Numerical probe of the core (verify2/n2x_planes.py: five planes with (Q4) for the three 4-sets, charts forcing the pivots; slow, 46
    starts): 11 solutions = 8 with P_c = P_d = P_e, 2 violating (NT), 1 inside three columns; 0 outside the classes of the theorem.
    CONSEQUENCE (THEOREM N): a 9-dim level space with all a_r = 1 and lam_rr' >= 3 for all row pairs contains a single-row element.
    Dependencies: (P), (G1), (G2); Theorem N1 (round 2 list); Theorem N2-X; upstream L156, L101.
 1. VERIFYFL DI5-R3: THEOREM SPLIT, FS, TS, Lemma HYP                         VERIFIED
    SPLIT is stated correctly: hypotheses "defect line C m, e_i m^T in L', <m,m> != 0". The third-kind space L'_3 (two-column m, ker kappa
    not strongly level) is NOT split (zeta = span(uh, z_1) contains no unit vector), so there is no conflict. For isotropic m the
    conclusion fails: verifyfl's saved spaces re-evaluated with my code (verify2/iso_check.py): split, defect line 1-dim, ker kappa not
    strongly level (0.73; 4.9; 5.6), L(L') level (<= 8e-11). Fresh test (verify2/split_test.py): 12 new 2-/3-dim split spaces with four
    non-isotropic m: ker kappa strongly level in all. (E4)(a) and the search statistics were not rerun.
 2. STAGE 2 RESULT-R4                                                          VERIFIED, except (FO) for all parameters = GAP (as its author says)
    (Z3) z_r <= 4 - e(L_r); Lemma N2-Z (A-D, incl. the new (n,k) = (4,4) computation and the reductions to N2-GEN, which do not use "no
    unit vector"); Theorem N2-Z' ((E0)-(E2), both inclusion-exclusion formulas, Cases A and B). Slip in (alpha2): the text says
    "rho'_4 = r/3"; correct is rho'_4 = 0 and then h_c = x r = 0, so r = 0 and rho' = 0 -- same conclusion.
    M*: level EXACTLY (polynomial identity) and dim T_1(M*) = 8 EXACTLY at 9 parameter sets incl. m_a = m_b, m_a = 0, m_a = m_b = 0, a sign
    change and a rational set (verify2/mstar_check.py). (FO) logic is correct (every level space containing M lies in T_1(M)). GAP: rank 17
    is not proved for all parameters; the chain "N2 with a diagonal block => M*" has two numerical links. All of this is now superseded by
    N2-X (N2 does not occur at all), so nothing downstream depends on the gap.
 3. STAGE 3 secs 18-20, 22                                                     VERIFIED, except (N2-g) (numerical, not rerun) and (N2-h) (steps (1)-(3) checked, (4)-(5) not; moot)
    (N2-a), (N2-b), (N2-c)/(Q5) with its consequences, (N2-d), (N2-e)/I3 with the Lefschetz and 3-support remarks, (N2-f)/(E1), sec. 19
    remarks, Lemma S3-1 (z_i <= 5 - lam_ri <= 2). (N2-h): steps (1)-(3) checked, (4)-(5) NOT checked; its premise is vacuous after N2-X.
 4. ROWS section DI and round 3                                                VERIFIED
    (I1); (I2); (I3) for k = 2, 3, 4 (k = 4 redone by hand: p_4 = -6 beta_R + 24 e_4^col - 2 sum_i beta_{R-i} y_i, counts 6+8+3+6+1 = 24, and beta_R = 0 by P_4 = 0); Lemma D; DDI; DI_3; Proposition O; Corollary H;
    Lemma B'; Lemma TC; SL_3 (a)-(d); FL2 normal form; FL2* (1)-(6) with Delta_1 recomputed; R3.1 (upstream L_gct_215 read: 4x5 level
    <= 7), Lemma EC, Tower Lemma, saturation principle. Not rerun: R3.4, R3.7 numerics and the census.


## RESULT ROUND 2 (verify2, 17:31) -- stage3 secs 13-16, verifyfl DI5, stage2 RESULT-R3: everything VERIFIED; R3-1 is now EXACT
 Same method as round 1 (own line-by-line re-derivation; scripts rerun and re-implemented where they carry weight). No error found.
 1. STAGE 3, secs 14-16                                              VERIFIED
    Lemma Q4-coll (normal form of L_e, the five mu-degrees, h = 0); MIN-D; MIN-E: (a) with the upstream statement of Gct/L156 read in the
    checkout (3 x q, P_1 = P_2 = P_3 = 0 => dim <= q+1; M^T is such a space with q = 5, dim 7); (b-alpha) all three support sizes, plus an
    exact pattern check of the case v_0 = e_j on three columns (verify2/minE_b_alpha.py: 103 patterns; the 6 loop/edge survivors of the
    monomial filter are exactly the ones the text kills); (b-beta) all four multiplicity patterns. (G1), (G2).
    Lemma Q4-gen / THEOREM N1: normal forms re-derived independently (A: one m = 2 pair, no triangle; B: one m = 2 pair, triangle -- here
    "w independent of p" is FORCED, the alternative w = 0 would put zeta in Y_cd; C: two m = 2 pairs, zeta = x^{ac}); the three rank-16
    claims confirmed with my own exact code (verify2/n1_rank.py, coefficient vectors over Q; stage3/q4_m2.py rerun: 16 in all forms).
    Dependency trace of N1: (P), (G1); P_i well defined; CA2 [my repaired proof, round 1]; T1; TR; MIN-A [rank 16]; Q4-coll; Q4-gen
    [rank 16 x 3]; TV; NT [3x2 level <= 2]; MIN-B; plane lemma |Z| = 0 [sec. 12 + my repair 2]; |Z| = 1 [sec. 15 (b)]; |Z| >= 2 [L156].
 2. VERIFYFL DI5: Lemma EQ, THEOREM TC5                               VERIFIED
    Normal form DI5.2 ((i), (ii), C2', C3', C4'), Lemmas Z, LAG, NB, (P1)-(P4) and all seven branches (N-a, N-b, c1, c3, c2-i, c2-ii, c2-iii)
    re-derived, including my own classification of the pairs with tau(v^2v') = tau(vv'^2) = 0 (3 antipodal + 4 zero-row pairs, each
    line in exactly one) and of the blueprint facts actually used (P-a/b, Lemma N, A1, G23, Q1-Q4). TC5 does NOT need Lemma SL itself.
    Simplification: in (c3) the appeal to "type IV is excluded (S6)" is unnecessary -- the u-column of N'' would sweep a 2-dim space,
    against Lemma N. Resultant (F1): confirmed exactly at 60 rational points (both sides have degree <= 24), closed forms E_t, P_t
    confirmed exactly from the definitions; the points at infinity (v or v' = chi_3), not covered by the parametrisation, checked by
    hand (no solution there). (verify2/tc5_checks.py)
 3. STAGE 2 RESULT-R3 and the earlier layers                           VERIFIED
    a. LEMMA N2-GEN (R3-5): Steps 0-3 re-derived line by line. In particular the two strata flagged by the author: |S| = 4, (1,1,1,1):
       all seven moment equations and be be_a be_b = 4c^2 recomputed, the two factorisations A tau (tau-B)(tau-h) = 0,
       B tau (tau-A)(tau-h) = 0 expanded by hand, all four ends (h = 0, tau = 0, tau = h, tau = A = B) contradictory; (2,1,1,1): AB = N,
       VN - F' = A N_b - F' = B N_a - F' = -3F_1, om pqr = -2, the three quadratic class sums give XY = XZ = YZ = -2 and the cubic one
       gives 1 + XY + XZ + YZ = 1: contradiction. Also (1,1,1,1,1) (B | l_b impossible), (3,2), |S| = 1, 2, 3.
       Machine support: the two elimination identities of |S| = 4 hold on the unisolvent 6^4 grid, the Lagrange moment facts and the
       class-sum product identities hold exactly (verify2/n2gen_identities.py); my own LM search on (i)-(iii) with a, b = exp(.)
       (verify2/n2gen_search.py): 96 starts, 58 zeros, 56 with a weight -> 0 or infinity, 2 with a unit vector in P, 0 genuine.
    b. R3-1 (exception triples) IS NOW EXACT. (E1)-(E3) re-derived. (E4) redone over Q(i) (verify2/r3_exact.py, six runs <= 137 s):
       1800 canonical configurations: 1668 excluded by (E1), 120 killed, 12 survive -- identical to stage2's floating-point survey.
       Every one of the 1320 cubics c_S carries an exact certificate: 151 have ell = 0 on Pi~_S (no condition); 673 have three distinct
       linear factors over Q(i), each verified exactly; 152 have one exact linear factor and a cofactor quadric of rank >= 3 on its
       kernel (irreducible); 344 have no linear factor, certified by a rational plane section that is a SMOOTH cubic (Jacobian ideal
       contains all 15 quartics, exact rank); uncertified: 0. DFS and admissibility tests with exact ranks.
       For the 12 survivors (verify2/r3_exact_leaves.py): exactly ONE maximal leaf, containing all others, and it EQUALS the family
       stated in (E4) (exact rank test): 6 x family (a), 3 x A, 2 x B, 1 x C. (E5) recomputed by hand: (a) E_1 = -(1+i) delta_h c_1 ell,
       and for delta_h = 0 perm_3 = c_1 ell^2; A, C (and B by exchanging rows 2,3; computation written out) coefficient of t_1 =
       ell [ i(b-a) + 2d(ell-a-b) ], be = 0 inadmissible. Independent float confirmation of the factor lists by a multiplicity-robust
       finder (r3_survey_robust.py: 2171 = 2171 factors, same verdicts).
    c. Lemma 4x3, Lemma H (incl. 3x3 subpermanents of the Hadamard matrix = +-2), GEN-1, GEN-3, (Y3), (Y5) (incl. the determinant identity
       and AB+AC+BC = e_1e_3 - 4e_4), GEN-7, GEN-8, one-zero layer R2-1 (Type I_0, nu_j0 = 0, no Type II; script r2_triple_onezero.py
       audited and rerun: 364 + 672 killed, 0 survivors): re-derived, correct.
 THEOREM GEN (now unconditional as far as this verification goes): no 9-dim level space of 5x5 matrices has all a_r = b_c = 1 and all row
 and column FK annihilators zero-free.   Proof chain and dependencies:
   (1) R0, ZBF+UFD, ThB, Lemma C (lam >= 2), Theorem A, C4                                  [chief; verified round 1]
   (2) C7/C7'' (minimal pairs are of Type I or II), tau-coordinates, T0                     [chief/stage2; verified round 1]
   (3) T1 (exact scripts t5, t10 + rank check + my re-implementation; T1' by hand), T2, T2'' => (S2)   [verified round 1]
   (4) R3-1: exception triples impossible => (S2*): X_ijk != 0 for all row triples          [exact: verify2/r3_exact*.py; (E5) by hand]
   (5) SR/SC (no single-line elements in GEN), S2-d/GEN-tri, GEN-0, GEN-lin, GEN-2 => no minimal pair: lam >= 3 for all row pairs
   (6) (P), (G1), (G2): all lam = 3 [N1] or exactly one lam_ab = 4 with m_cd = m_ce = m_de = 2 [N2]; lam_ab = 5 impossible
   (7) THEOREM N1 (dependencies in item 1 above; uses upstream Gct/L156) => a single-row element, contradiction with (5)
   (8) LEMMA N2-GEN excludes N2.
 Only the row side of (5) and zero-free column annihilators are used after (5).
 Residual risk, stated honestly: every link is a hand proof re-derived by one verifier (me) plus exact/numerical checks; the parts with
 the least machine support are the plane lemma for supports of size 3, 4 (sec. 12, hand algebra + weak numerics) and sec. 15 (b-beta).
 NOT verified in round 2: stage3 sec. 13 details beyond (II)'s exclusion, sec. 17-18 (family N2 outside GEN), verifyfl DI5.4-DI5.6
 (examples, assessments), stage2 R3 scripts other than those named.


## RESULT (verify2, 16:49) -- independent verification of N3', the ZBF foundations, the stage-2 triple layer / GEN-2, and MIN-A..MIN-C
Method: every proof below was RE-DERIVED by me line by line (not read for plausibility); every machine claim was rerun and, where it
carries weight, re-implemented independently; statements valid for all level spaces were tested on 11 level spaces (L080, ex1, ex2,
ex3, fam(2), fam(0.6+1.4i), K5, K4, rows' Lm(c=0), Lm(c=1), rows' second-kind space). NO ERROR FOUND that invalidates a downstream
statement. Two justifications needed repair (both repaired, items 4b, 4c), one script lacked a needed check (added, item 3c).

 1. THEOREM N3' (stage3 sec. 10)                                   VERIFIED (own proof = the four steps, each re-derived)
    Step 1 (cell factorisation; UFD on the linear space V'; rank <= 1 on the image => dim <= 2), Step 2 ((A) nondegenerate case,
    (D) rank M_u = 2 in BOTH degenerate shapes of u_r, equality iff Rad Q_u in V'', (E) all three sub-cases), Step 3 (kernel of
    multiplication by W^2 is a line), Step 4 ((a)-(e), incl. the explicit expansion in (c) and the transposed use of (b),(c) in (d)):
    all correct. No hidden use of b = J; the only uses of perm(b) != 0 are "no base point has a zero row/column" and k' != 0.
    Counterexample searches (all negative):
      - EXACT structured search (verify2/n3p_struct*.py): all 4-dim spans of 4 elements among the 45 matrices E_c, E_c +- E_c' (c, c' in
        a common line): 148995 subsets, 8934 distinct 4-dim spans inside {perm = 0}; for EVERY one of them perm vanishes identically
        on a complement of V_0 in B_V := {b : D_v D_v' perm(b) = 0 on V_0} (rational arithmetic), so no base point with perm(b) != 0
        exists at all. Controls: the pipeline accepts the 3-dim spaces (strictly upper triangular, b = I) and (3x3 level space,
        b = J); and on 1468 structured 3-dim spans the same criterion finds perm != 0 on the complement 842 times, with an explicit
        valid base point 209 times (verify2/n3p_struct_ctrl2.py) -- so "0 of 8934" in dimension 4 is not an artefact.
      - numerical (verify2/n3p_search.py, own formulation: Grassmannian chart + 60 sample points): 9 structured base points with
        perm(b) != 0: 4-dim 0/360 starts (residual floors >= 2), 3-dim found for every b. Unplanned calibration: for 3 base points
        with perm(b) = 0 the same search FINDS 4-dim spaces in 86/112 starts -- so the hypothesis perm(b) != 0 is essential and the
        search is able to find 4-dim spaces when they exist. With b free (perm(b) = 1): 0/77, only blow-ups (|b| ~ 100, a row -> 0).
    COROLLARY N3'-L                                                 VERIFIED (2 lines from GZ-a + N3'); 71 B1 blocks on 11 spaces, 0 violations.

 2. FOUNDATIONS (chief secs. 2-4)                                   VERIFIED
    R0; ZBF incl. the UFD step (ell != 0 on U: f_i = k_i ell^deg with k_1 k_2 = 120, both k_i != 0; ell = 0 on U: U in L and one
    factor vanishes -- every family to which the team applies it is a LINEAR subspace of L^, I checked each use in items 1-4);
    ThB; Lemma C; Theorem A; N3 (3x3 level <= 3 in 8 lines); C4 (B_x = 0 on the plane of a minimal (1,1) pair; no zero-freeness needed).
    Remark (strengthening, same proof): Lemma C's argument never uses dim L = 9. It proves for EVERY level space of n x n matrices and
    every pair of rows:  dim pi_{rr'}(L) <= 2n - 3,  i.e. dim(L cap {rows r, r' = 0}) >= dim L - (2n-3).  (n = 5: >= dim L - 7.)
    Tests (verify2/test_spaces.py, 11 spaces, both transposes): R0 33; general ZBF over ALL 250 blocks S x Z with |S|+|Z| = 5:
    326 cases with ell != 0 (f_1 = k ell^s, f_2 = k' ell^(5-s), kk' = 120) and 4926 with ell = 0 (f_1 = 0 or f_2 = 0); ThA 1038 + 346;
    ThB 71; CA2 214 + 32: 0 violations.

 3. STAGE 2: C7/C7'/C7'', T0, T1, T1', T2, T2'', S2, GEN-2           VERIFIED
    a. Pair rules re-derived in tau-coordinates (q_T ~ om_j a_j b_l + om_l a_l b_j on {a_j+a_l = b_j+b_l, rho.a + rho'.b = 0}); the
       classification "Type I or Type II" and the normal forms (c = 1/(K_1-K_2), sigma_0 = -K_2(1+c); y = (-1+eps i)/2, corner
       sigma = eps i s) are correct. Small addition: B1 needs k != 0, which gives sigma_j = sigma_l != 0 ALSO for pairs separated by
       both rho and rho' (chief's RP5 omits "!= 0"); harmless, both types already have it.
    b. T2 and T2'' (hand proofs): both cubics recomputed (2t(t a_1 + a_1a_2 + a_1a_3 - a_2a_3), Gram det 1/16; the T2'' cubic and its
       irreducibility), the n** argument and the final "functional of row 1 alone" step are correct. T1' (cyclic Type II triple):
       elimination redone by hand, correct (c = (1-i)/4 leaves -i/8). S2 follows.
    c. T1 scripts: t3, t5, t10, t13 reviewed and rerun (outputs as in the notes). t10 computes Pi_S as the kernel of five explicit
       annihilators but never checks that they are independent on C^15 (needed: otherwise I_3^perp would have an unknown fifth element
       and the certificate would be void). I checked it: rank 5 in all 2080 configurations (verify2/t10_rank.py). So t10 is valid.
       INDEPENDENT re-implementation (verify2/t1_indep.py, own enumeration: the (2,3) structure is found by testing all 315 structures
       against the ratio, not by stage2's shortcut): identical counts -- (I,I) 28 killed / 2 inadmissible; (I,II) 760 / 220;
       (II,I) 120 / 30; (II,II) 2168 killed, 32 survive the kernel test, 640 inadmissible; cube test on the 32: 26 killed, 6 survive =
       exactly the six cyclic triples.
    d. GEN-2 (R2-3) with its inputs SR, S2-d/GEN-tri (incl. |Sigma| != 2, != 5), GEN-0, GEN-lin: Steps 1-4 re-derived, correct
       (dim U = 6 for both types; Step 4 incl. the non-onto case Q_2 = {d} / Q_3 = {d}). r2_gen2_check.py rerun: 50 + 1500, dim 0.
    NOT verified by me (outside the assignment): GEN-1, Lemma 4x3, Lemma H, GEN-3, the one-zero layer R2-1, C8 / Type I', RESULT-R3.

 4. STAGE 3: MIN-A, TV, MIN-B, MIN-C (secs. 11-12)                  VERIFIED, with two repairs
    a. MIN-A: the rank claim re-computed exactly with my own code (verify2/minA_rank.py): 16 for 0 triangles (all 6^4 labellings and
       200 random line triples), 16 for 1 triangle (normal form + 200 random), 11 collapsed. TR, T1 (stage3), MIN-B, TV re-derived;
       dim K(P) <= 1 proved for each support size and checked on 780 planes (verify2/kp_check.py); "3x2 level <= 2" re-derived from
       P_1, P_2 (the hyperplane is nondegenerate: Q(n) = 24).
    b. REPAIR 1 (CA2, used by T1 and hence MIN-A). The stated reason "the 1x4 blocks {e} x (all but m) are not ell-supporting" is
       FALSE when kappa^e_m = 0 (then kappa^e itself is a sum-1 relation on that block) -- and zeros in kappa^e do occur in the
       minimal case (S3-D). The conclusion is still true: for xi in L_e and u in L^, the s^4-coefficient of perm(u + s xi) is
       <u_e, G(xi)>, and pi_e(L^) = C^5 when a_e = 1, so G(xi) = 0. (General form: G(xi) in pi_e(L^)^perp for any a_e; tested.)
    c. REPAIR 2 (MIN-C, (beta), type (2,3,0)). The text jumps from "no 4-set without pinned row" to "every 4-set has >= 2 pinned
       rows"; the case of a 4-set with 3 free rows and 1 pinned row d is not treated. It closes in one line: the coefficient of the
       free variable lam_d is tau(om_a,om_b,om_c) on V_beta^3, which is not identically 0. With that, every 4-set is all-pinned,
       as claimed. Everything else in MIN-C is correct as written: (alpha) supp v_0 = 3, 2, 1 with k = 4 (patterns (4), (3,1), (2,2),
       (2,1,1), (1,1,1,1)), k = 3, k <= 2; (beta) (2,2,1) (two free rows impossible; one free row; no free row).
    d. Extra check of (alpha), v_0 = e_j (verify2/alpha_ej_k2.py, alpha_ej_all.py, alpha_ej_lm.py): of the 736 support patterns of five
       vectors in C^4 (up to column permutations), 103 violate (NZ), 20 violate (NT), 560 are killed EXACTLY by a coefficient that is
       a single monomial; all 125 loop/edge patterns (k <= 2) are settled exactly (the 2 survivors of the monomial filter need three
       parallel edges with pairwise opposite ratios). The remaining 51 patterns (k = 3, 4) are covered by the hand argument; LM in
       logarithmic coordinates finds no bounded solution for the 49 I could run (corroboration only).
    Not verified: sec. 13 (configuration (II)), S3-A/B/C/D.

 Consequence for the team: N3', N3'-L, R0/ZBF/ThA/ThB/LC, C4, C7'', T1, T2, T2'', S2, GEN-2, MIN-A, TV, MIN-B, MIN-C can be used as
 stated. Lean-relevant: Lemma C in the general form above is a clean 2n-3 statement; CA2 should be formalised by the direct Laplace
 argument of 4b, not via ell-supporting blocks.

## Log
STATUS 16:09: started; reading BRIEF, chief secs 2-4, stage3 sec 10.
STATUS 16:13: N3' (all four steps), N3'-L, R0, ZBF, ThB, LC, ThA, N3 re-derived by hand: no error.
STATUS 16:18: stage2 layer re-derived by hand (C4, C7, C7', C7'', T0, T2, T2'', T1', S2, SR, S2-d, GEN-0, GEN-lin, GEN-2); t3, t5, t10, t13
 rerun; t10's missing independence check done (rank 5 in 2080/2080).
STATUS 16:24: stage3 secs 11-12 re-derived (TR, CA2, T1, TV, MIN-B, MIN-C); omitted sub-case in (beta)(2,3,0) found and closed; CA2's
 justification repaired.
STATUS 16:28: MIN-A ranks confirmed exactly; foundation tests on 11 level spaces: 0 violations; N3' numerical search negative with a
 positive calibration at perm(b) = 0.
STATUS 16:40: exact pattern check of MIN-C (alpha) k <= 2; dim K(P) check; free-b N3' search (only blow-ups).
STATUS 16:47: exact structured N3' search (8934 spans, none admits a base point); independent re-implementation of T1 reproduces all counts.
STATUS 16:49: RESULT written. Files: verify2/{test_spaces,vlib,minA_rank,t10_rank,t1_indep,n3p_search,n3p_free2,n3p_struct,n3p_struct2,
 n3p_struct3,n3p_struct_ctrl,alpha_ej_k2,alpha_ej_all,alpha_ej_lm,kp_check}.py, logs in verify2/logs/.

# ROUND 2 (start 16:49, budget 90 min -> ends ~18:19). Targets: (1) stage3 secs 13-16 (Q4-coll, (II), MIN-D, MIN-E, N1 + q4_m2.py);
#  (2) verifyfl DI5 (Lemma EQ, TC5); (3) stage2 RESULT-R3, R2-1, GEN-1, GEN-3, Lemma H.
STATUS 16:49: round 2 started; reading stage3 secs 13-16.
STATUS 16:53: stage3 secs 14-16 re-derived: Q4-coll, MIN-D, MIN-E ((a) with the checked L156 statement read in the checkout; (b-alpha), (b-beta)
 all four multiplicity patterns), (G1), (G2), Q4-gen (normal forms re-derived; ranks 16/16/16 by my own exact script n1_rank.py), N1: no
 error. Exact pattern check of (b-alpha) v_0 = e_j on 3 columns (minE_b_alpha.py). Next: verifyfl DI5.
STATUS 17:01: verifyfl DI5 re-derived by hand: DI5.2 normal form ((i),(ii), C2', C3', C4'), Lemma EQ, Lemma Z, LAG (a),(b), NB, TC5 (P1)-(P4) and all
 seven branches (N-a, N-b, c1, c3, c2-i, c2-ii, c2-iii), incl. my own derivation of the pair classification tau(v^2v') = tau(vv'^2) = 0 and of
 the blueprint facts actually used (P-a/b, A1, G23, Q1-Q4, Lemma N). Resultant (F1) confirmed exactly at 60 rational points (degree <= 24),
 closed forms E_t, P_t confirmed exactly (tc5_checks.py). No error. Next: stage2 RESULT-R3, R2-1, GEN-1, GEN-3, Lemma H.
STATUS 17:03: stage2 extras re-derived by hand: Lemma 4x3, Lemma H (V_4-Fourier argument), GEN-1, GEN-3 (a),(b),(c), R2-1 pair classification
 (Type I_0; nu_j0 = 0; no Type II): no error. Next: R3-1 (exception triples), R3-5 (N2-GEN), scripts.
STATUS 17:20: Lemma N2-GEN re-derived line by line (Steps 0-3; all seven moment equations of |S| = 4 (1,1,1,1) and all class-sum identities of
 (2,1,1,1) recomputed): no error. R3-1: (E1)-(E3) re-derived; (E5) both hand computations recomputed (family (a): E_1 = -(1+i) delta_h c_1 ell,
 then perm_3 = c_1 ell^2; families A/C: coefficient ell[i(b-a) + 2d(ell-a-b)]); (E4) redone EXACTLY over Q(i) (verify2/r3_exact.py):
 parts 0-4 of 6 done, 0 uncertified cubics; part 5 and the leaf identification running.
STATUS 17:26: exact R3-1 complete (6 parts, 0 uncertified cubics; 12 survivors = the 12 claimed families, unique maximal leaves).
STATUS 17:31: RESULT ROUND 2 written (moved to the top). New files: verify2/{n1_rank,minE_b_alpha,tc5_checks,r3_survey_robust,r3_stats,r3_exact,r3_exact_leaves,r3_e5}.py,
 logs in verify2/logs/ (r3_exact_p5.log, r3_leaves_b1.log, r3_leaves_b2.log).

# ROUND 3 (start 18:06, budget 90 min -> ends ~19:36). Targets: (1) verifyfl DI5-R3 (THEOREM SPLIT, TS, isotropic m); (2) stage2 RESULT-R4
#  (N2-Z, N2-Z', M*, FO, Z3); (3) stage3 secs 18-20; (4) rows section DI (DI_3, Lemma D, DDI, Prop O, Cor H, Lemma B', Lemma TC).
STATUS 18:06: round 3 started; reading verifyfl DI5-R3.
STATUS 18:11: verifyfl R3: SPLIT, FS, TS, HYP re-derived (correct; hypotheses of SPLIT are right: the third-kind space L'_3 is NOT split,
 zeta = span(uh, z_1) contains no unit vector); fresh 2-/3-dim split spaces with non-isotropic m: ker kappa strongly level in 11/11.
 stage2 R4: (Z3) and the logic of (FO) re-derived; M* level exactly and dim T_1(M*) = 8 exactly at 9 parameter sets (mstar_check.py).
STATUS (after restart): verifyfl's isotropic examples re-evaluated with my own code (verify2/iso_check.py): the 2-dim and both 4-dim spaces are
 split (e_3 m^T inside), m = (1,w,w^2,0,0) up to order, defect line 1-dim, ker kappa NOT strongly level (0.73, 4.9, 5.6), L(L') level (<= 8e-11).
 So <m,m> != 0 in THEOREM SPLIT is necessary and the theorem is stated correctly. stage2 R4: Lemma N2-Z and Theorem N2-Z' re-derived
 (one slip in the text of (alpha2): it should read rho'_4 = 0 and r = 0, conclusion unchanged). New top priority: stage3 sec. 21 (N2-X).
STATUS 18:27: stage3 sec. 21 THEOREM N2-X re-derived line by line: inputs ((Q4) for the 4-sets containing a,b via the (t1)/(t2) normal forms incl.
 the triangle case w || w'; (Qb) by total antisymmetry; (Q5)/(Q5J); (P2); (NT), (NT'); (M7); pairwise meeting; lam_ab = 5 impossible; Lemma I3);
 case (alpha) (A1: D, B; A2); case (beta) (beta-0; types (1,1), (1,2), (1,3), (1,4), (2,2), (2,3) for three distinct planes and for
 P_k = P_l). All annihilator claims K(V_3V_3), K(PV_3) confirmed EXACTLY (verify2/n2x_annihilators.py, n2x_annihilators2.py, rational
 arithmetic, incl. K = C H* L_0 and K = C Q_beta + y_x Lam(u_0)). No error. Next: rows section DI and round 3.
STATUS 18:30: rows section DI and round 3 re-derived: (I1)-(I3) for k = 2, 3, Lemma D (Rado induction), DDI, DI_3, Proposition O, Corollary H,
 Lemma B', Lemma TC, SL_3 (all of (a)-(d) recomputed), FL2 normal form, FL2* (steps 1-6, Delta_1 recomputed), R3.1 (upstream L_gct_215
 statement read: 4x5 level <= 7), EC, Tower Lemma, saturation principle: no error. Next: stage3 sec. 18 remainder, 19, 20, 22.
STATUS 18:38: RESULT ROUND 3 written at the top. New files: verify2/{split_test,split_test2,iso_check,mstar_check,n2x_annihilators,n2x_annihilators2,
 n2x_dbg,n2x_scan,n2x_planes}.py, logs/{split_iso,n2x_planes_s2}.log.
STATUS 18:49: second pass over sec. 21 finished (annihilators by hand for all planes; (I3) k = 4 redone). (N2-h): steps (1)-(3) checked,
 (4)-(5) not, and it is moot after N2-X. Handing back.

# ROUND 4 (start 18:57, budget 90 min -> ends ~20:27). Targets: (1) stage2 RESULT-R5 (FO2, FO-M*, Cases A/B of (alpha), REG1 -> (B1)/(B2), (Q-r));
#  (2) stage3 secs 22-24 (S3-5, PL4, S3-G); (3) rows R4 (R4.1, R4.2, R4.3, R4.7, C-UP, R4.11) + FL2* consequences; (4) reg2 (Phi(Y) remark, FO2 numbers).
STATUS 18:57: round 4 started; reading stage2 RESULT-R5.
STATUS 19:04: stage2 R5 checked: Lemma FO2 (statement + proof; bilinear restriction; own implementation verify2/fo2lib.py reproduces (8,1,7) on all
 nine known 7-dim spaces and (6,1,5) on K5 -- my first version had the conjugation bug the author describes, bounds 5 < 7, fixed); Theorem FO-M*
 for all parameters ((a)-(d) re-derived; (s1)-(s4) confirmed exactly, verify2/fo_mstar_exact.py: rank 17, dim T' = 10, linear parts in the a_d-
 direction only); R5-7 (a) (dim <= 7, P_2(tau) = -8); Cases A and B of family (alpha) by hand (one imprecise sentence in (3,3,2)); R5-4 formulas.
 OPEN POINT: (Q-r)(iii) "every column projection of L_r has dim <= 3" has no proof in the notes (rows: Lemma C; columns: ?).
STATUS 19:11: stage3 sec. 24 re-derived: Lemma S3-2 (b),(c); S3-3 (b); Lemma S3-4 (V-twisted, (QL)); planes well defined; Lemma S3-5 (all coefficient
 equations; the formula for P_2 omits the term a c s(gam_y) s(p), which is 0 because y is level); LEMMA 5V: OWN PROOF (three parallel => unit or
 2-plane; span 2-dim => T = 0 on U => coordinate plane; span >= 3 and no three parallel => contradiction via (G2), kernel types, the isotropy
 argument in three columns) + exact pattern filter (verify2/lemma5v_patterns.py: 736 patterns, 77 survive the monomial filter -- these are covered
 by the hand proof); THEOREM PL4 Part 1 ((I),(D),(B)), Part 2 (2B), (2A)(i),(ii) all sub-cases incl. the three sub-cases of "a plane equals C^T"
 that the text treats as one; THEOREM S3-G ((3col) step with the checked L157, statement read); S3-G' (1)-(3). No error.
STATUS 19:14: rows R4.1 (Hyperplane Lemma), R4.2 (a)-(d), R4.3 (RS-HYP; L067 statement read: k dim W <= M), R4.7 (Lifting Lemma, D-UP, C-UP),
 R4.11 (equivalence), FL2* consequences (a), (b) (dim(m o U') = 3 for <= 1 zero; = 2 for two zeros): all re-derived, no error. Next: reg2.
STATUS 19:18: reg2: (a) Phi(L_r) in R_r^perp (dim a_r - 1) re-derived; (b) the Omega criterion (tau_r = J - 5 e_r 1^T in T_1(M); 1 not in pi_r(L);
 dim L - dim M <= dim Omega(M) - 1) re-derived; (c) numbers recomputed with my own code (verify2/reg2_fo2.py) for ALL 20 six-dim 4x5 spaces:
 19 x (dim T_1, rank, bound, dim Omega) = (9, 3, 7, 2), rc45 = (10, 4, 8, 3): agree with reg2. Caveat: for clm_p4_d6_defect3_s3, seed_d6_e3_t1,
 seed_d6_e3_t6 the smallest kept singular value of the cofactor system is 2e-7 .. 1e-9 relative (entries of size 1e-7 in the reduced bases):
 at tolerance 1e-6 they read (10, 4, 8, 2). Bound < 9 and Omega = 2 either way.
 stage2 extras recomputed: L_r candidates /tmp/r5_Lr3_1_1 (9,3,7), r5_Lr3_1_2 (10,5,7) agree; r5_Lr3_1_0 is not level (the "spurious" one);
 r5_Lr_2_1 (inadmissible) has singular values 1e-6 in two row projections: (7,2,6) at tol 1e-9, (12,7,8) at tol 1e-5 (author: (11,6,8));
 N2 block examples: (11,7,7) and (13,8,9) agree; cross family X(a,b): (10,5,7) for b != 0, (13,8,9) for b = 0 agree (R6-2/R6-3).
 (Q-r)(iii) columns: OWN PROOF of "dim pi^c(L_r) <= 3 unless kappa^r = e_c and kappa'^c = e_r" (the functionals <kappa^r, t_r> and
 <kappa'^c, t^c> on the 9 cross coordinates are independent unless both are multiples of t_rc); the exceptional column is NOT excluded.
 Remark on FO2: M lies in the radical of q_m restricted to T_1(M) (q_m(m',t) = d/de D_t perm(J + m + e m') = 0), so rank <= dim T_1 - dim M.
 PL4 probe running (verify2/pl4_probe.py).
STATUS 19:27: PL4 probe finished (35 starts: 8 (3col), 1 type I, 26 not converged; variant with four non-vanishing columns: 0 of 8 converged).
 RESULT ROUND 4 written at the top. New files: verify2/{fo2lib,fo2_known,fo2_mstar,fo_mstar_exact,fo2_stage2_cands,reg2_fo2,reg2_limits,
 lemma5v_patterns,pl4_probe}.py, logs/pl4_probe_*.log. Handing back.

# ROUND 5 (start 19:33, budget 90 min -> ends ~21:03). (1) audit COMPUTE-{rows,verifyfl,stage3,reg2}.md + handoff/HANDOFF.md sec. 2 + oracle.py
#  -> COMPUTE-ERRATA.md; (2) rows R4.10, R4.14, R4.15; verifyfl round 4 (QB, PS, PR-RED, PR3) + round 5 (3C, NP); stage2 round 6 (R6-2, (T2),
#  lam = 5 lemma, "z_i = 3 forces four minimal pairs"); stage3 round 7; reg2 (S6'), Type F / Type NC.
STATUS 19:45: spec audit done -> /home/claude/work/L-gct-210/COMPUTE-ERRATA.md. [A] items: stage3 "level spaces of dim 8 exist" (false; breaks two
 calibrations); stage3 (5c) claim false as a plane statement (explicit counterexample P_c=P_d=P_e=span(e1,e2+e3), P_a=P_b=span(e2-e3,e4));
 verifyfl C/D acceptance lacks a fresh-point test while the scripts under-sample (28/44/40/60/45 points vs 34/69/69/125 monomials);
 mod-p unit ideals are not proofs; clm N = 140 too small for d = 7, 8. [B]: A_m has dim 16 not 17; (NCOL_3)+(DI_4x4) => no (7,3) needs
 (DI_5;2); C1 acceptance should be d - e >= 4. oracle.py: no errors. Now part (2): rows R4.10, R4.14, R4.15.
STATUS 19:47: rows R4.10 (a)-(d) (transposed defect construction, padding lemma), R4.14 (Theorem NCOL-S: formula D^(1)(Y) m = -2S m + 4 c o m
 - 2(c.m) 1 recomputed; (a), (b)), R4.15 ((F1), (F2), (FS-DEC) incl. the lists for e = 1, 2, 3, (F1^T)): re-derived, no error. Next: verifyfl R4/R5.
STATUS 19:50: verifyfl R4: Lemma QB, Theorem PS (a)-(c), PR-RED, THEOREM PR3 (steps (1)-(4), all tau-values, det Q_m = -<m,m>/2, remark (i))
 re-derived, no error. R5: Lemma C', Lemma 3C (identity ID10, cases r = 0, 1, >= 2, sign contradiction), Lemma NP (a), (b) re-derived; the
 blueprint fact "7 pairs" confirmed numerically (verify2/seven_pairs.py: 14 ordered solutions, 7 disjoint pairs: 4 zeta, 3 chi). Next: stage2 R6.
STATUS 19:52: stage2 R6: cross-family theorem R6-2 (permanent formula, all cofactors, <C(U),t>, degree 2/1/0 analysis -> T_1 of dim 10 for
 b != 0, a not in C1; block rank argument 2*2 + 1 = 5; numerics (10,5,7) from round 4; the polar formula for P_2 not recomputed), R6-5 (a),(b),
 (T2) (order-2 coefficient of <v, G(T(v)+xi)>), lam = 5 lemma (C Phi + Phi^T C = 0; diagonal argument), Lemma (z_i = 3): re-derived, no error.
STATUS 19:55: stage3 sec. 26 (round 7): counting tools (c1)-(c5); (A1); (A2) lam-patterns F1/F3/F4a/F4b; (A3) F1 (graph connectivity, (QL) with
 one/two/three rank-one maps); (A4) F3 and F4a: every input of N2-X re-derived for the pair with lam = 4 ((Q4) x 3 via (CA2) on L_m and the
 injectivity lemma, planes independent of m, (Qb), (Q5) by the hyperplane argument, (NT), (NT'), (M7)), and the isotropy count replacing
 (beta-0) (Q = (J_3 - I) (x) I_2 nondegenerate on P^3); (B) Lemma dim(U o U') >= 2 and its corollary: re-derived, no error. (A5), (C5)-(C8):
 structure statements read, (C5) checked, the rest not (open families).
STATUS 20:01: stage2 COMPUTE spec read; reg2's M* confirmed (verify2/reg2_mstar.py, reg2_mstar_exact.py); verifyfl R5.4-R5.6 verified; errata
 updated (A6, stage2, section F); RESULT ROUND 5 written. Lemma Z probe running (verify2/lemmaz_probe.py).
STATUS 20:04: Lemma Z probe: 0 constrained solutions in 9 starts, control 20/20 (17 with an exact zero row or column). Conjugation handling
 checked in all scripts that compute T_1 / Omega. Errata final (180+ lines). New files: verify2/{audit_verifyfl,audit_sampling,seven_pairs,
 reg2_mstar,reg2_mstar_exact,lemmaz_probe}.py, verify2/spot/ (one (4,1) hit of run_clm.py), logs/lemmaz_s*.log. Handing back.

# ROUND 6 (start 20:09, budget ~2 h -> ends ~22:09). (1) audit local session's exact runs /home/claude/coord/local/results/VF-A, VF-B;
#  (2) COMPUTE-verifyfl NEXT (N1-N6, (F1)-(F4)), COMPUTE-stage2 S4, COMPUTE-rows X4/X5; (3) rows R5 (NCOL-P3, P51, SC1, DC/NC'-DC, R5.13),
#  stage2 R7 ((FO-r), 25 cofactors, cross family), verifyfl R5.9, R5.10; (4) stage3 sec. 26 (A5), (C6)-(C8).
STATUS 20:25: VF-A audited line by line (gen.py = spec A; W basis, A_m parametrisation, coefficient extraction, cases, normalisation). The verdict is
 now established three ways: (i) local gen.py (generic chart, 4 primes); (ii) my OWN generator (verify2/vf/own_gen_A.py: 20 variables + linear
 constraints, squarefree-algebra expansion, N removed by two zero cells) on ALL 18 coordinate charts: unit in 18/18 for A1-A4 at two primes, CAL
 non-unit in 19/19; homogeneous Groebner basis = 18 linear forms + all three quadratic monomials of the two remaining variables; (iii) exact
 linear algebra mod p (verify2/vf/exact_A.py): first-order rank 12 (kernel = N + 2 directions), the x^2-coefficients on these two directions
 span all binary quadrics. Since the solution set is PROJECTIVE, emptiness mod one prime proves emptiness in characteristic 0 (a point over
 Q-bar reduces to a point mod P): request A is a THEOREM, not only evidence. VF-B: gen.py = spec B (parametrisation, (2), (3), saturation);
 calibration reproduced here with Singular (unit; dim 0 vdim 24) and with my OWN generator in an exact chart gauge (verify2/vf/own_gen_B.py).
