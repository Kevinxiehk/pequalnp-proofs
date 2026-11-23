# NOTES-stage2 (role: stage2; start 14:38, budget 90 min -> ends ~16:08)
## RESULT-R7 (stage2 round 7, 19:50) -- details in sections R7-1 .. R7-4 at the end; heavy-computation specs in COMPUTE-stage2.md.
 REG1 is NOT proved; (2,4) is settled only numerically; z = 3 is reduced, not closed.
 (FO-r) LEMMA [rigorous; sanity on the 10 full-projection lines of the known spaces]: for a line r with 4-dim projection, the projection
        of T_1(L_r) to line r is ALL of C^5; equivalently every column-deletion permanent G_j(J' + xi) is, on L_r, a first-order variation
        D_{t'} N(J' + xi) of the level function. Strictly sharper than "dim T_1 >= 9".
 CROSS  [rigorous]: for every cross space with a not in C1 the projection is 3-dim -- excluded at first order, INCLUDING the locus b = 0
        (3-dim single-column part) which FO2 could not exclude.
 (2,4)  [formulas rigorous, conclusion numerical]: explicit cofactors; (FO-r) <=> s * gam_j in D(X) for j = 1..4. Case A (s = 0): (FO-r)
        holds, FO2 bound 8 numerically. Case B (generic; all solutions with dim T_1 = 9): projection = C e_0 + C 1, dimension 2: dead at
        first order in all 20+ solutions; no proof (needs the parametrisation of Case B).
 TABLE  (stage2/r7_table.py): of all saved candidates the only ones passing (FO-r), FO2 and (T2) are of the form X_{ri} + e_i Z_i with
        z_i = 3 (four (3,3) solutions, cross with a in C1); none of the five tested extends to an 8-dim level space.
 z = 3  [rigorous reductions]: for non-isotropic m no other row carries a single-row element (P_2 + verifyfl's SPLIT), so L_i is a NON-SPLIT
        (5,1) space, not two-column (TC5), whose defect function is a first-order variation of N ((FO-r) for row i) -- as for all its
        hyperplanes, which are non-split (4,1) spaces (HYP); no such space is known. Not closed; isotropic m untouched.
 (iii)  corrected as verify2 found; none of my results used the column part; the exceptional case (an identically vanishing entry)
        is listed as (B0), no contradiction found.

## RESULT-R6 (stage2 round 6, 19:13) -- details in sections R6-1 .. R6-7 at the end. (Q-r) is NOT classified; REG1 is NOT proved.
 RIGOROUS: (1) THEOREM (cross family, R6-2): for the 5-dim level subspaces X(a,b) of a cross (one row + one column) with sparse parts of
     dim <= 2 (b != 0, a not in C1), T_1 is explicit (dim 10) and every level space containing X(a,b) has dim <= 7. On the two exceptional
     loci (b = 0; a in C1) X has a 3-dim single-column resp. single-row part and the FO2 bound is 9.
     (2) LEMMA (lam_{rr'} = 5): needs Phi in GL_5 with C(xi) Phi + Phi^T C(xi) = 0 on L_r; impossible if the ten 3x3 subpermanent cubics are
     independent. (3) (T2): the order-2 part of chief's (**) at v -> 0 is a LINEAR condition on T -- a cheap exact test for a candidate L_r.
     (4) z_i = 3 forces four minimal pairs through line i (so the split free line is a sub-case of (B1)) and dim T_1(M_i) >= 10 for the
     8-dim M_i = L_i + e_i Z_i. (5) every single-row element e_i w^T gives the relation 1_{rows != i} (x) w.
 NUMERICAL (all solutions verified on fresh points): census of (Q-r) solutions -- general search 6, inside FK(2,4) 9, FK(3,3) 7, FK(1,5) 1.
     Every solution found vanishes on a block s x t with s + t >= 6. After FO2 and (T2) the ONLY survivors have a 3-dim sparse part
     (split free line): cross with b = 0 or a in C1, and two FK(3,3) solutions. All solutions with a 3-dim row projection and sparse
     parts <= 2 (the L_r of a minimal pair) have FO2 bound 7 or 8.
 HYPOTHESIS for target (3): "no 3-dim single-row or single-column part in L_r" (forced by (H1) for the crossing family of lines, stage3
     S3-1, or by the exclusion of (5,1) spaces). Under it every candidate found has FO2 <= 8; I have a proof only for the cross family.
 NOT DONE: classification (non-FK solutions of (ii) exist; none found by LM); FO2 on L_r + L_r' for Types I, II, I_0 (no explicit
     candidates for the three other rows); FK(4,2); a proof for FK(2,4) (there dim T_1 = 9 in all 9 solutions).

## RESULT-R5 (stage2 round 5, 18:38) -- details in sections R5-1 .. R5-7 at the end. The theorem for REG1 is still NOT proved.
 (FO-M*) THEOREM [structural proof + exact parameter-free certificate]: T_1(M*) = W_7 (+) C(1 e_0^T - J/5) has dimension 8 for ALL parameters;
         W_7 = full free column + 3-dim strongly level part, M* a hyperplane of it. Corollary: every level space containing M* has dim <= 7.
 (R5-2)  Cases A and B of family (alpha) are now HAND proofs: inside family (alpha), N2 forces L_a + L_b = M*. With (FO-M*): family (alpha)
         is excluded at dimension 9 rigorously. Still numerical: that every diagonal block with a two-row column lies in family (alpha)
         (and I found a parameter count showing that isolated solutions could have been missed by the survey).
 (FO2)   LEMMA [rigorous] + applications [numerical]: L is totally isotropic for q_m = D^2 perm(J+m) on T_1(M), so
         dim L <= dim T_1(M) - ceil(rank/2). Reproduces "maximal" for all 7 known spaces. Excludes at dimension 8 and 9: all 26 generic
         non-diagonal level N2 blocks found (bound 7, from the 4-dim block alone), M* (7), and both admissible candidates for L_r (7).
 (Q-r)   UNIFORM FORMULATION: for every line with full projection, L_r is a 5-dim level space of 4x5 matrices with all 4x4 subpermanents
         identically zero, row/column projections of dim <= 3, and FO2 bound >= 9. Only 2 such candidates found (both cross-like, both
         fail FO2); the survey is thin.
 NEW INPUT: stage3's Theorem N2-X / Theorem N (not yet verified) removes N2 altogether; my N2 results are an independent confirmation on
         the sub-families. REMAINING in REG1: (B1) a minimal pair (then L contains the 8-dim level space L_r + L_r'); (B2) single-row and
         single-column elements with z <= 2. FO/FO2 on (B1) not done: no explicit candidates (the pair classification lives on the
         relation side). What carries over to a_r >= 2: section R5-6 C.

## RESULT-R4 (stage2 round 4, 18:00) -- regime REG1 := all a_r = b_c = 1 without zero-freeness. Details: sections R4-1 .. R4-6 at the end.
 The theorem for REG1 is NOT proved. Delivered: three rigorous reductions, one explicit obstruction, and the list of survivors.
 (N2-Z)  LEMMA [hand proof]: moment problem with zero weights. If every column of the N2 block has 3, 1 or 0 nonzero weights (every
         kappa'^j has at most one zero among the rows c,d,e), the block is (alpha1) or (alpha2): one column with entries sigma(p_i) and
         its two dominoes, the other columns proportional to one form mu.
 (N2-Z') THEOREM [hand proof; direct numerical confirmation]: N2 with a block (alpha1) or (alpha2) is impossible (vanishing of all 4x4
         subpermanents on L_a). So N2 is impossible whenever every column annihilator has at most one zero among c,d,e -- in particular
         for zero-free column annihilators with ARBITRARY row annihilators (Lemma N2-GEN no longer needs "no single-column element").
         Corollary: all a_r = 1, lam >= 3, column annihilators with at most one zero each => single-row element (uses stage3's N1).
 (M*)    EXPLICIT 6-dim LEVEL SPACE [exact integer check] of the N2 shape for L_a + L_b (block (alpha3)): the level condition and
         the vanishing subpermanents on L_a, L_b do not exclude N2. M* contains a split free column (3-dim space of single-column elements).
 (FO)    [added 18:04; section R4-6] FIRST-ORDER EXTENSION TEST: every level space containing M* lies in T_1(M*) := {t : D_t perm(J + m) = 0
         for all m in M*}, and dim T_1(M*) = 8 (exact rank 17 at one parameter set; rank 17 at 409 further parameter sets incl. the
         special loci). So M* lies in NO 9-dim level space: N2 with a diagonal block is impossible at dim 9 [num-assisted: the
         classification of two-row-column blocks and "Case B" for Xi with zeros are numerical; the parameter scan is not a proof for
         all parameters]. This does not use the (5,1) conjecture.
 (Z3)    single-row elements are a defect phenomenon: z_r <= 4 - e(L_r); in REG1 z_r <= 3, and z_r = 3 => L_r is a (5,1) space and L contains an 8-dim
         level space with a deletable line (rows' open (DI_5) at e = 1; TC5 covers two-column defect lines).
 SURVIVORS in REG1: (S-I) minimal pairs with a zero in the annihilators involved; (S-II) single-row/column elements with z = 1, 2 (and
         z = 3 = the (5,1) problem); (S-III) N2 with a non-diagonal block (some kappa'^j with >= 2 zeros among c,d,e, the column carrying
         two independent forms; extreme case: two identically vanishing cells). No uniform kill found for these three; the first-order
         extension test (FO) is the candidate uniform tool: build the forced sub-configuration, compute dim T_1, compare with 9.
 Correction to my round-3 handback text: the survey count sentence was garbled; the correct numbers are 346 solutions = 335 with a zero
         or infinite weight + 11 with a unit vector in P + 0 genuine.

## RESULT-R3 (stage2 round 3, 16:37; HEADLINE UPDATED 16:59) -- details in sections R3-1 .. R3-5 at the end
 HEADLINE (16:59): THEOREM GEN -- "a 9-dim level space cannot be fully generic" (GEN: all a_r = b_c = 1, all row and column FK
 annihilators zero-free) -- now has a COMPLETE PROOF CHAIN, but it is CONDITIONAL on two inputs that are not fully rigorous/verified:
   (a) my R3-1 (exception triples; num-assisted) -> GEN-6 (lam >= 3 for all row pairs);
   (b) stage3's round-3 section 16 (all a_r = 1, lam >= 3, no single-row element => all lam = 3 [Theorem N1: impossible] or the
       rigid family N2; hand proof + exact rank checks, "not yet independently verified" by stage3's own label).
   New here (section R3-5): LEMMA N2-GEN [hand proof, every step re-checked; numerically corroborated]: stage3's family N2 is
   impossible when the column annihilators are zero-free. Mechanism: X_ab = {(pi_c; a o pi_d; b o pi_e): pi_i in P, sum pi_i = 0} for ONE
   2-plane P and the weights a = K'_c/K'_d, b = K'_c/K'_e; the level condition on this 4-dim block alone is a moment problem
   (sum c_j lam_j^r = sigma^r for seven weight/degree pairs) which has no solution with zero-free weights and no unit vector in P.
 The text below (16:37) is the state BEFORE stage3's round-3 result and Lemma N2-GEN; it remains correct, and (E), (GEN-6) are inputs:
 GEN (all a_r = b_c = 1, all annihilators zero-free) was reduced to stage3's non-minimal regime (R3) on both the row and column side:
 (E)    The exception triples of (S2) are impossible [num-assisted: floating-point enumeration of the admissible fifth annihilators
        (132 configurations: 120 have none, 12 have one family each) + hand computation that every member of these 12 families
        violates the cube condition perm_3 = k ell^3; confirmed numerically]. Hence (S2*): ANY three rows with a = 1 and zero-free
        annihilators have X_ijk != 0 (no Type II proviso).
 (GEN-6) GEN => no minimal pair: lam >= 3 for all ten row pairs and all ten column pairs  [(E) + GEN-2].
 (Y3),(Y5) two general factorisation lemmas for 2-row elements (rigorous, tested on the examples); (GEN-7): in GEN a 2-row
        element spanning Y_ab (m_ab = 1) never has full column support.
 (GEN-8) stage3's configuration (II) (twisted partial free column) is impossible in GEN when some pair of its four rows has
        m = 1 [rigorous]; with stage3's MIN-C: GEN is not in the minimal case.
 REMAINING IN GEN at 16:37: all lam >= 3, and (some row lam >= 4 or some row m >= 2) and (some column lam >= 4 or some column m >= 2).
 [16:59: closed by stage3's N1/N2 reduction + Lemma N2-GEN, conditional on (a), (b) above.]
 One correction this round: the round-1 survey of exception configurations (21 survivors) used too weak an admissibility
        test and only part of the column triples; the corrected survey is stage2/r3_survey.py.

## RESULT-R2 (stage2 round 2, 16:02) -- headline of round 2 (details: sections R2-1 .. R2-5 at the end)
 (GEN-2) THEOREM [rigorous]. Let L be a 9-dim level space in the FULLY GENERIC regime GEN (all a_r = b_c = 1, all row and column
      FK annihilators zero-free). Then L has NO minimal Type I row pair and NO minimal Type I column pair; more generally no
      minimal pair (r,r') whose plane X_{rr'} meets all three {row i = 0} ("triangular"). Every minimal pair of L is a Type II
      pair with X_{rr'i} = 0 for some third row i, i.e. it lives in a (II,II,lam=3) exception triple of (S2).
      Mechanism: X_{rr'} is rank one in column-weighted coordinates (S2-d); the quadratic part of perm(u + x) = perm(u)
      factorises on suitable linear subspaces of L^ as (linear form) x (quadratic form in rows r,r'); zero-free column
      annihilators kill the linear factor; the quadratic factor vanishing contradicts dim(L cap {column d = 0}) = 5
      (|Sigma| = 3) or the explicit annihilators of I^_{rr'} (|Sigma| = 4: sigma_0 != 0 resp. y != -1).
 (GEN-3) LEMMA: in GEN a 2-row element opposite to a minimal pair has column support of size 2, 3 or 5, never 4.
 (ONE ZERO) First non-generic layer [rigorous + exact]: if kappa^r has exactly one zero entry (kappa^r' zero-free) a minimal pair
      is of "Type I_0" (Type I with the zero column inside one block; the zero column is FREE in row r; no Type II), and (T1)
      extends: three rows, one zero entry in one annihilator, all pairs minimal => X_123 != 0 (1036 configurations, exact).
 NOT achieved in round 2: "a 9-dim level space cannot be fully generic" (missing: non-triangular Type II pairs and the regime
      all lam >= 3); item O2 (the 21 Type II / Type II configurations) in general; two minimal pairs + lam = 3 in the one-zero layer.
 Two intermediate claims of mine were WRONG and are withdrawn (both caught by sanity scripts): "(Z-0): E empty" (round 1) and
      "for |Sigma| = 3 two rows of G coincide" (round 2).

## RESULT (stage2, 15:21; last update 15:26) -- Stage 2 is NOT closed (minimal row pairs are not excluded), but its PURPOSE is reached in the
## main case by a new route: "triples instead of pairs".  All statements rigorous unless marked [num].
 Setting: L level, dim L = 9, L^ = CJ + L, a_r = 5 - dim pi_r(L), X_{rr'} = L cap {rows r,r' = 0}, minimal pair := dim X_{rr'} = 2.
 (V)  Chief's C4, C7, C7'' re-derived by hand: CORRECT, no error. C4 does not need zero-free annihilators, and it extends
      to the mixed minimal pair (a_r,a_r') = (2,1): in EVERY minimal pair all 3x3 subpermanents vanish on the plane X_{rr'}.
 (G)  Unified pair criterion with zero entries allowed (2x2 matrices Gamma_T; section 2), machine-checked.
 (TAU) In coordinates tau_i = kappa^i o u_i the minimal types are kappa-free (section 3): on L every row has weighted sum 0 and
      Type I  <=> the weighted partial sums over a column block C of the two rows agree;
      Type II <=> (partial sum of row i over Q_3) + (partial sum of row i' over Q_2) = 0  (three cells Q_1,Q_2,Q_3).
 (T1) Three rows with a = 1 and zero-free annihilators whose three pairs are ALL minimal have a common kernel element:
      X_123 != 0.  [EXACT: 3x2 zero-block factorisation on I_3 = pi_123(L^) + exact Q / Q(i) linear algebra over all 3108
      type configurations (t5_triple_all.py; the 2080 all-Type-II ones with the full cube test, t10_typeII_exact.py) + a hand elimination for the one surviving "cyclic
      Type II" family, which contradicts J in L^.]
 (T2) Two minimal Type I pairs (1,2), (1,3) and dim X_23 = 3: again X_123 != 0.  [hand proof, section 4]
 (T2'') A minimal Type I pair (1,2), a minimal Type II pair (1,3) and dim X_23 = 3: again X_123 != 0.  [hand proof, section 5b]
 (S2) COROLLARY (fully rigorous). Let rows i,j,k have a = 1 and zero-free FK annihilators. If X_ijk = 0 then the triple has
      EXACTLY two minimal pairs, BOTH of Type II, sharing a row, and the third pair has dim X = 3.  In particular:
      (a) a minimal Type I pair (r,r') and ANY third row r'' with a = 1 (zero-free) have X_{rr'r''} != 0: the plane X_{rr'}
          contains a nonzero element whose row r'' vanishes;
      (b) if all five rows have 4-dim projections with zero-free annihilators and no minimal pair is of Type II, then EVERY
          triple of rows kills a nonzero element of L, i.e. every pair of rows carries a nonzero 2-row element of L.
      This is exactly what "lam_{rr'} >= 3 for all pairs" was meant to deliver to Stage 3 -- obtained without excluding Type I.
 (S2-c) Hence the plane X_{12} of a Type I pair (rows 3,4,5 with a = 1) has a common zero row, or contains a single-row
      element, or is {(mu' p'; mu p; (mu-mu') q)} with all 3x3 subpermanents of (p';p;q) zero.
 (S2-d) GENERIC REGIME "GEN" (all a_r = b_c = 1, all row AND column FK annihilators zero-free; then stage3's (SR) excludes
      single-row elements).  For a minimal Type I pair (1,2) the plane X_12 is a TRIANGLE of 2-row elements
      x_3 + x_4 = x_5 (x_i with rows 1,2,i zero), and in column-weighted coordinates (t_ij -> kappa'^j_i t_ij, kappa'^j = FK
      annihilator of column j) it is RANK ONE:   X_12 = { c zeta^T : c supported on rows 3,4,5, sum c = 0 }  for one vector
      zeta in C^5 with |supp zeta| >= 3, sum_j (kappa^i_j / kappa'^j_i) zeta_j = 0 (i = 3,4,5), and perm[(1/kappa'^j_i)] = 0 on
      rows 345 x any three columns of supp zeta.  (section 7)
 (M)  A minimal Type I pair (1,2) and a row 3 with a_3 = 2: (1,3) and (2,3) cannot both be minimal (Type I' would force
      K_1 = K_2 = 1/2, but Type I needs K_1 != K_2).
 [num] Two minimal Type II pairs sharing a row, third pair with lam = 3, X_123 = 0 (t8_two_minimal.py, floating point,
      necessary conditions only): 1668 excluded by a dimension count, 111 killed, 21 canonical configurations survive.
      (The same survey reproduces (T2), (T2'') numerically: all (I,I), (I,II), (II,I) configurations are killed.)
 [num] For all-Type-I minimal triples dim X_123 = 1 is NOT excluded by the same necessary conditions (75 of 105 pairs of
      partitions admit a sixth annihilator; t11_lam3.py), so "X_123 = X_12" could not be forced.
 Sanity: the 3x2-block factorisation (T0) holds on L080, ex1, ex2, ex3, two s-family members, K + E_0 (676 cases, 0 violations);
      Type I / II tau-forms pass the ThB pair test (15 + 300 structures); T1 reproduced numerically on synthetic Type I
      annihilator data at random kappa (105 pairs of partitions, each with >= 3 violating column triples).
 STILL OPEN (exact list):
  O1 the minimal pairs themselves: Type I, Type II (zero-free (1,1) pairs) and Type I' ((2,1) pairs) are not excluded; what is
     excluded is X_123 = 0 for the triples listed in (T1), (T2), (T2''), and the combination (M);
  O2 two minimal Type II pairs sharing a row, third pair lam = 3, X_123 = 0: OPEN (21 canonical configurations survive the
     necessary conditions of t8_two_minimal.py); this is the only way a zero-free a = 1 triple can have X_123 = 0;
  O3 annihilators WITH zero entries: no classification (the criterion (G) is ready; first consequences (Z-0), (Z-1) in section 6); the
     tau-coordinates need zero-free kappa, so (T1), (T2) do not cover such rows;
  O4 rows with a_r >= 2: only C8 (chief), the extension of C4, and (M); triples containing such a row are open;
  O5 pairs with dim X_{rr'} >= 3 are not constrained at pair level (dim Pi_T can be 1); they enter only through the count
     lam_ij + lam_ik <= 5 when X_ijk = 0.
 Files: stage2/pairlib.py, exactla.py, t1_verify.py (criterion), t2_triple.py (numeric T1), t3_triple_exact.py (Type I exact),
  t4_typeII_pair.py, t5_triple_all.py (exact, all types), t6_typeII_full.py, t10_typeII_exact.py (Q(i) exact), t7_sanity.py,
  t8_two_minimal.py, t9_cyclic.py, t11_lam3.py, t12_zeros.py, t13_T2pp.py (exact cubic identities of T2, T2'').  Every run < 30 s.
  Round 2: r2_onezero.py, r2_triple_onezero.py (exact), r2_gen_lemmas.py, r2_lemmaH.py, r2_gen2_check.py, r2_block_rank.py.
  Round 3: r3_survey.py (corrected exception survey), r3_cube2.py, r3_hand_check.py, r3_generic_fail.py, r3_Y3.py, r3_Y5.py
   (r3_leaves*.py, r3_two_minimal.py, r3_cube.py: exploratory; r3_cube.py and one r3_cube2.py run took 2m43s / 1m12s).
STATUS 14:50: BRIEF + NOTES-chief (all, incl. C7'', C8, section 7) read. Re-derived C4, C7 by hand (correct; details below).
 Working on: unified pair-level criterion (zeros allowed), cubic-level consequences (G = 0 on L_r), Types I / II / I'.
STATUS 15:03: (a) C4, C7, C7'' re-derived by hand: CORRECT (no error found); unified pair criterion with zeros (Gamma_T) proved and
 machine-checked (stage2/t1_verify.py: Type I passes for all 15 partitions; closed form agrees with the direct ThB test on
 3951 random degenerate data). (b) NEW: "tau-coordinates" make Type I kappa-free; TRIPLE THEOREM (T1 exact rational computer
 check of 210 sign configurations, T2 hand proof): three rows with 4-dim projections whose minimal pairs are of Type I always
 have a common kernel element: X_{rr'r''} != 0. Writing proofs; next: Type II in triples, Type I', zeros.

## 1. Verification of chief's C4 / C7 / C7'' (all re-derived by hand; no error)
 C4 (B_x = 0 on the plane X_{rr'} of a minimal (1,1) pair): a quadratic form z_1^T C z_2 vanishing on the codim-2 space I^ has
   rank <= 4, so rank C = 2, C = a b^T + b a^T with disjoint supports; I^ is the preimage of a maximal isotropic plane of
   alpha_1 beta_2 + beta_1 alpha_2 (alpha_i = z_i.a, beta_i = z_i.b); the family {alpha_1 = mu beta_1, alpha_2 = -mu beta_2} and
   the members mu = 0, infinity of the other family contain an annihilator supported on ONE row, impossible as both row
   projections of I^ are onto; the rest is as in chief's text. The proof does NOT use that kappa, kappa' have no zeros.
   ADDITION: the same holds for the mixed minimal pair (a_r, a_r') = (2,1), dim X = 2 (chief's C8 setting): there
   I^perp = span{(n,0),(kappa*,-kappa')} contains no element (0,n') and only the line C(n,0) of elements (n'',0); both members
   mu = 0, infinity of family 1 need a 2-dim space of one-row annihilators, the general member of family 1 needs none (but
   (n,0) is one), family 2 needs one of each kind. Hence B_x = 0 for all x in X_{rr'} in EVERY minimal pair (dim X = 2).
 C7'' (only Types I, II): re-derived: sigma-classes have <= 2 distinct points (rho_j,rho'_j); two points on an anti-diagonal
   admit as third point only one of the two corners (both corners would force y = y'); no anti-diagonal pair => all points on
   an axis-parallel line => rho or rho' constant. Correct.

## 2. Unified pair criterion (zeros allowed) [rigorous; machine-checked]
 Minimal (1,1) pair: I^perp = span{(kappa,-kappa'),(nu,nu')}. For T = {j,l} put p_i = (kappa_i,nu_i), p~_i = (-kappa'_i,nu'_i) in C^2
 (then sum_i (p_i + p~_i) = 0 encodes (1,1) in I^), R_T = [p_j p_l p~_j p~_l] (2x4), Gamma_T = p_j p~_l^T + p_l p~_j^T (2x2),
 G_T = sym(Gamma_T), a_T = (Gamma_12 - Gamma_21)/2. Then ThB for T is equivalent to:
   (i)  rank R_T <= 1  =>  (kappa_j,kappa_l,0,0) in rowspace(R_T)   [dim Pi_T >= 3 forces ell = 0 on Pi_T];
   (ii) rank R_T = 2 and (kappa_j,kappa_l,0,0) not in rowspace (type B1)  =>  G_T != 0, det G_T = 0, and (a_T = 0 or
        G_11 = G_12 = 0).   [G_T is the Gram matrix of q_T^{-1} on Pi_T^perp; rank q_T|Pi_T = rank G_T; the radical vector
        is the q-dual of c_1 R_1 + c_2 R_2 with G c = 0 and ell of it equals a_T c_2.]
 With no zeros this reproduces C7' (G_11 = -kappa_j kappa_l (omega_j+omega_l), ...). Not carried out: the full list of
 solutions with zero entries (see open list).

## 3. tau-COORDINATES: the minimal pair types become kappa-free  [rigorous]
 For a row i with a_i = 1 and kappa^i without zeros put tau_i := kappa^i o u_i (entrywise), f_i := sum_j tau_i(j). Then
 f_i = ell on L^ (FK annihilator), and for a minimal pair (i,i') (dim X_{ii'} = 2) the second relation of I^_{ii'} reads
   TYPE I  (columns = C + C^c):           sum_{j in C} (tau_i(j) - tau_i'(j)) = sigma_0 ell,   kappa^i' = c w kappa^i, w = +1 on C, -1 on C^c;
   TYPE II (cells Q_1,Q_2,Q_3, eps = +-1): sum_{Q_3} tau_i + sum_{Q_2} tau_i' = -y ell, y = (-1 + eps i)/2,
                                          kappa^i' = c w kappa^i, w = eps*i on Q_1, 1 on Q_2, -1 on Q_3.
 So ON L:  every row has weighted sum 0;  Type I: the weighted partial sums over the block C of the two rows AGREE;
 Type II: (partial sum of row i over Q_3) + (partial sum of row i' over Q_2) = 0.  (This is the "two-block structure" in its
 cleanest form: Ann(L) contains K o (e_i 1_C^T - e_i' 1_C^T), K = matrix of the FK annihilators.)  The set of Type II
 structures is symmetric under exchanging the two rows (Q_2 <-> Q_3). Both forms machine-checked against the ThB pair test
 (stage2/t1_verify.py: 15 partitions; t4_typeII_pair.py: all 300 Type II structures pass, wrong sign of y fails).
 Permanents: z_ij = tau_ij / kappa^i_j, so for rows i with kappa^i = c_i w_i kappa^1 (w_i with entries in {+-1,+-i}) and a column
 set S:  perm(u[rows; S]) = const * perm( (tau_ij / w_i(j)) ),  const != 0.   Everything below is linear algebra over Q(i).

## 4. TRIPLE THEOREM  [T1: exact computer check, rational/Gaussian arithmetic; T2: hand proof]
 Setting: dim L = 9, rows 1,2,3 with a = 1 and zero-free kappa^1 (then all minimal pairs among them are of Type I or II and all
 three kappa's are zero-free), X_123 := L cap {rows 1,2,3 = 0} (2-row elements), lam_ii' = dim X_ii'.
 (T0) I_3 := pi_123(L^) has dim 10 - dim X_123, and for a column triple S: U_S := {u in L^: rows 1,2,3 supported in S},
      Pi_S = I_3 cap C^{3xS} = U_S / X_123, and ZBF (3x2 zero block): perm(u) = perm(u[123;S]) perm(u[45;S^c]) on U_S. Hence
        ell != 0 on Pi_S  =>  perm_3 = k ell^3 on Pi_S (k != 0), in particular perm_3 = 0 on Pi_S cap ker(ell);
        ell  = 0 on Pi_S  =>  U_S in L and (perm_3 = 0 on Pi_S  or  perm(u[45;S^c]) = 0 on U_S).
 (T1) ALL THREE PAIRS MINIMAL and X_123 = 0 is impossible if at least one pair is of Type I; if all three are of Type II it
      is impossible except for ONE configuration (up to column permutations / complex conjugation): the CYCLIC TYPE II
      triple: columns = A + B + C,  w_2 = (i,1,-1), w_3 = (-1,1,i) on (A,B,C), and on L
            sum_C tau_1 + sum_B tau_2 = 0,   sum_A tau_1 + sum_B tau_3 = 0,   sum_A tau_2 + sum_C tau_3 = 0.
      Proof. If X_123 = 0 then dim I_3^perp = 5 and I_3^perp contains the 5 functionals f_1-f_2, f_1-f_3, g_12 - s_12 ell,
      g_13 - s_13 ell, g_23 - s_23 ell (g = the pair relations of section 3). Whenever the six functionals f_1,f_2,f_3,g_12,
      g_13,g_23 restricted to C^{3xS} are independent, these five are independent (so they span I_3^perp), ell != 0 on Pi_S
      for EVERY value of the constants s_ii', and Pi_S cap ker(ell) is the common kernel of the six (3-dim, defined over Q).
      By (T0) perm((tau_ij/w_i(j))) must vanish identically on that kernel.  stage2/t3_triple_exact.py (Type I only: all
      210 pairs of partitions) and t5_triple_all.py (canonical (1,2)-structure x all 315 (1,3)-structures x all admissible
      (2,3)-structures: 3108 configurations with admissible ratio kappa^3/kappa^2, exact Fractions / Gaussian units) find
      in every configuration with a Type I pair a triple S with independent functionals and a point of the kernel where
      the permanent is != 0  [(I,I) 28/28, (I,II) 760/760, (II,I) 120/120 killed].  For all-Type-II triples the constants
      s = -y are universal, so I_3 is completely explicit; the full cube test (t6_typeII_full.py, floating point, 2080
      configurations) leaves exactly the cyclic family (6 canonical members = the 6 compositions of 5 into block sizes);
      there perm_3 = k ell^3 does hold (|k| = 0.707) for S meeting A, B, C once each and ell = 0, perm_3 != 0 on Pi_S for the
      other S (so perm(u[45;S^c]) = 0 on U_S is forced there).   [all-II part: numerical survey, not exact]
 (T2) EXACTLY TWO MINIMAL PAIRS (1,2), (1,3), BOTH OF TYPE I, and X_123 = 0 is impossible.  [hand proof]
      X_12 + X_23 direct in L_2 (dim 5) gives lam_23 <= 3; lam_23 = 2 is (T1); so lam_23 = 3, dim I_23^perp = 3, and
      I_3^perp (dim 5) contains N_12 + N_13 (dim 4: look at the row-2 and row-3 components) and I_23^perp (dim 3), whose
      intersection therefore has dim >= 2: some a g^_12 + b g^_13 + x(f_1-f_2) + y(f_1-f_3), (a,b) != 0, has row-1 component
      a 1_{C12} + b 1_{C13} + (...) 1 = 0, so C13 = C12 or its complement; w.l.o.g. C12 = C13 = C (then kappa^2 = kappa^3), and
      I_3^perp = span{f_1-f_2, f_1-f_3, g^_12, g^_13, n**} with n** = (0,m_2,m_3) supported on rows 2,3.
      Take S = {p,q,s} with p in C, q,s not in C (or p not in C, q,s in C). The five known functionals are independent on
      C^{3xS}; K_S := their common kernel with ell = 0 is {tau_i = (t, a_i, -t-a_i), i = 1,2,3} (4-dim), and on K_S
            perm((tau_ij/w_i(j))) = perm[[t,a_1,-t-a_1],[t,-a_2,t+a_2],[t,-a_3,t+a_3]] = 2 t (t a_1 + a_1 a_2 + a_1 a_3 - a_2 a_3),
      t times an IRREDUCIBLE quadric (Gram determinant 1/16 != 0).  If n**|K_S != 0 then ell != 0 on Pi_S and
      Pi_S cap ker ell = K_S cap ker n**, so by (T0) the linear form n**|K_S divides this cubic: n**|K_S is a multiple of t.
      In both cases the coefficients of a_2, a_3 in n**|K_S vanish: m_2(q) = m_2(s), m_3(q) = m_3(s). Hence m_2, m_3 are constant
      on C and on C^c:  n** = (al_2 - be_2) sum_C tau_2 + (al_3 - be_3) sum_C tau_3 + (be_2 + be_3) ell on I_3; with
      sum_C tau_i = sum_C tau_1 - s_1i ell this is (al_2 - be_2 + al_3 - be_3) sum_C tau_1 + const * f_1, a functional of ROW 1
      alone vanishing on I_3; as pi_1(L^) = C^5 it is identically 0, i.e. n** lies in the span of the other four. Contradiction.
 COROLLARY (T). Let rows 1,2,3 have a = 1 and zero-free annihilators, and suppose none of their minimal pairs is of Type II.
      Then X_123 != 0: L contains a nonzero element supported on the other two rows, lying in X_12, X_13 and X_23.
      (If X_123 = 0 then lam_ij + lam_ik <= 5 for all i, so at most one pair has lam >= 3: case (T1) or (T2).)
      This is exactly the conclusion "L_{rr'r''} != 0" that chief's Stage 2 (lam >= 3) was meant to deliver to Stage 3,
      obtained WITHOUT excluding Type I.
STATUS 15:06: sections 3, 4 written (T1, T2, corollary T). Next: mixed cases with Type II when only two pairs are minimal;
 sanity run of (T0) on the exact examples; Type I'.

## 5. Completion of (T1), the case of two minimal pairs with Type II, and consequences
 (T1') THE CYCLIC TYPE II TRIPLE IS IMPOSSIBLE  [hand proof; numerics agree: stage2/t9_cyclic.py, residual floor 0.25-0.45].
      It contradicts J in L^ (tau_i = kappa^i must satisfy the three pair relations). With a, b, c' the sums of kappa^1 over
      A, B, C, kappa^2 = c_2 (i,1,-1) kappa^1, kappa^3 = c_3 (-1,1,i) kappa^1, y = (-1+i)/2:
         a + b + c' = 1,  c_2 (i a + b - c') = 1,  c_3 (-a + b + i c') = 1,  c' + c_2 b = -y,  a + c_3 b = -y,  i (c_2 a + c_3 c') = -y.
      Eliminating a, c':  b(1 - c_2 - c_3) = i;  c_2 (i + b(1 + c_2 - i c_3)) = 1;  c_3 (i + b(1 + c_3 - i c_2)) = 1;
      -y(c_2 + c_3) - 2 c_2 c_3 b = i y.  The difference of the middle two is (c_2 - c_3)(i + b(1 + c_2 + c_3)) = 0; the second
      factor together with the first equation gives b = 0, absurd; so c_2 = c_3 = c, b = i/(1-2c), and the remaining two
      equations become c^2 + i c - (1+i)/4 = 0 and c^2 + 2 i c - (1+i)/2 = 0, whose only possible common root c = (1-i)/4
      gives -i/8 != 0.  Hence:
 (T1) FINAL FORM. Three rows with a = 1 and zero-free annihilators, all three pairs minimal, X_123 = 0: IMPOSSIBLE.
      Status of the proof: 3108 - 32 configurations exact (t5_triple_all.py); 26 all-Type-II configurations only in floating
      point (t6_typeII_full.py: perm_3 is not k ell^3 on some Pi_S with ell != 0; margins O(1)); 6 cyclic ones by (T1').
 (T2') TWO MINIMAL PAIRS (1,2), (1,3), lam_23 = 3, X_123 = 0, with Type II involved [numerical survey, t8_two_minimal.py].
      As in (T2): the row-1 parts of the two pair relations (1_C for Type I, 1_{Q_3} for Type II) must agree up to complement
      (otherwise dim count); then I_3^perp = N_12 + N_13 + C n**, n** on rows 2,3, and for every S on which f_1,f_2,f_3,g_12,g_13
      are independent, n**|K_S is 0 or a linear factor of the cubic perm|K_S; moreover n**|K must not be the restriction of a
      one-row functional of row 1. Result: (I,I): 28 dim count + 2 killed (= the hand proof (T2)); (I,II): 556 + 44 killed;
      (II,I): 84 + 6 killed; (II,II): 1668 dim count, 111 killed, 21 canonical configurations SURVIVE these necessary conditions.
 CONSEQUENCES (rows with a = 1 and zero-free annihilators throughout):
 (S2-a) [superseded by (S2) in the RESULT block: now fully rigorous by section 5b] If a minimal pair (r,r') is of Type I and r'' is a third row with a = 1, then X_{rr'r''} != 0, i.e. the plane X_{rr'}
        contains a nonzero element whose row r'' vanishes.  [rigorous if the other minimal pairs of the triple are of Type I
        or if all three pairs are minimal; numerical ((T2') (I,II)) otherwise.]
 (S2-b) If all five rows have a = 1 with zero-free annihilators and no minimal pair is of Type II, then EVERY triple of rows
        kills a nonzero element of L: every pair of rows carries a nonzero 2-row element of L. [fully rigorous: only (T1) with
        Type I pairs (exact) and (T2) (hand) are used.]  This is the input Stage 3 needs; it replaces "lam >= 3".
 (S2-c) Shape of the plane X = X_{12} of a Type I minimal pair when rows 3,4,5 have a = 1 (from S2-a): X meets each of
        {row 3 = 0}, {row 4 = 0}, {row 5 = 0} nontrivially, so either (alpha) X has a common zero row (a plane of 2-row elements),
        or (beta) X contains a single-row element e_i w^T, or (gamma) X = {(mu' p' ; mu p ; (mu - mu') q)} (rows 3,4,5), three
        fixed vectors p', p, q with all 3x3 subpermanents of the matrix (p';p;q) equal to 0 (by C4).
 (M)  MIXED TRIPLE [rigorous, from C8]: if (1,2) is a minimal Type I pair (partition C) and a_3 = 2 (zero-free N_3-data), then
      (1,3) and (2,3) are NOT both minimal: Type I' for (3,1) and (3,2) gives N_3 = span(kappa^1|_D, kappa^1|_{D^c}) =
      span(kappa^2|_{D'}, kappa^2|_{D'^c}) with block sums 1/2; as kappa^2 = c(kappa^1|_C - kappa^1|_{C^c}) this forces D = D' = C
      (up to complement), hence K_1 = K_2 = 1/2, contradicting c = 1/(K_1 - K_2).
STATUS 15:13: (T1) complete (cyclic Type II family killed by hand), (T2') surveyed, consequences S2-a/b/c and (M) written.
 Next: make the 26 floating-point cases exact if cheap; then final RESULT block and open list.
STATUS 15:17: all-Type-II (2,2,2) triples now EXACT (t10_typeII_exact.py: 2074 of 2080 killed by exact non-cube certificates
 over Q(i); the 6 survivors are the cyclic family, killed by hand in (T1')). lam_3 = 1 survey done (not excluded). RESULT
 block written at the top.

## 5b. (T2'') Type I + Type II sharing a row  [hand proof; cubic identities checked exactly, stage2/t13_T2pp.py]
 Setting: (1,2) minimal of Type I (block C), (1,3) minimal of Type II, dim X_23 = 3, X_123 = 0. As in (T2), I_3^perp (dim 5)
 contains N_12 + N_13 (dim 4) and I_23^perp (dim 3), so some combination of the two pair relations has no row-1 part:
 1_{Q_3} = 1_C or 1 - 1_C; Type I is symmetric under C <-> C^c, so C = Q_3, D := C^c = Q_1 + Q_2, and
 I_3^perp = N_12 + N_13 + C n**, n** = (0,m_2,m_3). On K := {ell = 0} cap (N_12 + N_13)^perp:
      sum tau_i = 0 (i = 1,2,3),   sum_C tau_1 = sum_C tau_2 = - sum_{Q_2} tau_3.
 Take S = {p,q,s}, p in C, q in Q_1, s in Q_2 (exists always). The five functionals are independent on C^{3xS},
 K_S = { tau_1 = (t,a_1,-t-a_1), tau_2 = (t,a_2,-t-a_2), tau_3 = (a_3, t-a_3, -t) } and, with the weights 1/w
 (row 2: (+,-,-), row 3: (-1, -eps i, 1)),
      perm|K_S = (a_2 - a_1) t [ t - eps i (t - a_3) ] - a_3 [ t(a_1 + a_2) + 2 a_1 a_2 ]  =: c.
 c is IRREDUCIBLE: a linear factor lam restricts on {a_3 = 0} to a factor of (1 - eps i)(a_2 - a_1) t^2 and on {t = 0} to a
 factor of -2 a_1 a_2 a_3 (neither restriction of c vanishes); lam|{a_3=0} ~ t gives lam = al t + ga a_3 with al ga != 0, and
 on a_3 = theta t the monomial -2 theta t a_1 a_2 of c survives; lam|{a_3=0} ~ a_2 - a_1 gives lam|{t=0} with both a_1 and a_2:
 impossible. Hence (argument of (T2)) n**|K_S = 0 for all such S:
      m_2(q) = m_2(s),   m_3(p) = m_3(q),   m_2(p) - m_2(s) + m_3(q) - m_3(s) = 0     (p in C, q in Q_1, s in Q_2).
 So m_2 = al on C, al' on D; m_3 = be on C + Q_1, be' on Q_2, with al - al' + be - be' = 0, and on K
      n** = (al - al') sum_C tau_2 + (be' - be) sum_{Q_2} tau_3 = (al - al' + be - be') sum_C tau_1 = 0,
 i.e. n** lies in N_12 + N_13 + C ell, hence in N_12 + N_13: contradiction with dim I_3^perp = 5.  QED
 (Also checked exactly: the cubics for S = {p in C; q,s in Q_2} and {p,p' in C; q in Q_2} are -2t x (irreducible quadric), for
 S = {p in C; q,s in Q_1} it is -2 b a_1 a_2; not needed.)
 PROOF OF (S2): X_123 = 0 gives lam_ij + lam_ik <= 5 inside the 5-dim L_i, so at least two pairs are minimal and a third
 pair, if not minimal, has lam = 3. Three minimal pairs: (T1). Two minimal pairs (they share a row): (I,I) is (T2), (I,II)
 is (T2''); only (II,II) is left.

## 5c. Hand-checkable instance of (T1)
 C12 = {1}, C13 = {2} (so C23 = {3,4,5}), S = {1,2,3}: the six functionals are the three row sums, tau_1(1) - tau_2(1),
 tau_1(2) - tau_3(2), tau_2(3) - tau_3(3); common kernel: tau_1 = (x,y,-x-y), tau_2 = (x,b,-x-b), tau_3 = (x+b-y, y, -x-b);
 signs (+,+,+), (+,-,-), (-,+,-); at (x,y,b) = (1,0,1): perm[[1,0,-1],[1,-1,2],[-2,0,2]] = -4 != 0, while ell != 0 on Pi_S.

## 6. Zero entries: what the criterion (G) gives at once  [rigorous; sanity stage2/t12_zeros.py]
 Minimal (1,1) pair, E := {j : kappa_j kappa'_j != 0}, Z_0 := {j : kappa_j = kappa'_j = 0}, omega = kappa'/kappa, rho = nu/kappa,
 rho' = nu'/kappa', sigma = rho + rho' on E.
 (Z-0) If j in Z_0 and nu_j = nu'_j = 0 (column j free in both rows) then sigma_l != 0 for every l in E (otherwise
       Pi_{j,l} is 3-dim with ell != 0).   [an earlier stronger claim "E is empty" was WRONG and is withdrawn]
 (Z-1) If j in Z_0 and (nu_j,nu'_j) != 0 then for every l in E the pair {j,l} is of type B1 with G_11 = 0, hence
       nu'_j / nu_j = omega_l  and  sigma_l != 0:  omega is CONSTANT on E (no pair of E is separated by both rho and rho').
 (Z-2) Inside E the four pair rules of C7' hold verbatim, but rho, rho' need not be non-constant on E any more, so besides
       Types I, II restricted to E also "all points on an axis-parallel line" and "one point" occur. Full list: not done.
STATUS 15:21: (T2'') proved by hand (one irreducible cubic), so (S2) is fully rigorous; RESULT block updated; zero-entry
 consequences (Z-0), (Z-1) recorded (one wrong intermediate claim caught by the sanity script and withdrawn).

## 7. (S2-d): the plane of a Type I pair in the generic regime GEN  [rigorous, given stage3's (SR): a single-row element
##    e_a w^T with w_j != 0 forces a sum-1 annihilator of column j vanishing at a]
 GEN: all a_r = b_c = 1, all kappa^r and all column annihilators kappa'^c zero-free. Then L has no single-row element (SR).
 Let (1,2) be a minimal Type I pair, X = X_12 (plane, rows 3,4,5). By (S2)(a), V_i := X cap {row i = 0} != 0 for i = 3,4,5.
 V_i cap V_i' consists of single-row elements, so it is 0; three nonzero subspaces of a plane with pairwise zero
 intersections are three distinct lines C x_3, C x_4, C x_5, and after scaling x_5 = x_3 + x_4:
      x_3 = (0;p;q), x_4 = (p';0;-q), x_5 = (p';p;0)   (rows 3,4,5),   X = {(mu' p'; mu p; (mu - mu') q)}.
 Every column j of every x in X is orthogonal to kappa'^j, i.e. kappa'^j_3 mu' p'_j + kappa'^j_4 mu p_j + kappa'^j_5 (mu - mu') q_j = 0
 for all mu, mu'. With zeta_j := kappa'^j_4 p_j this gives p_j = zeta_j / kappa'^j_4, q_j = - zeta_j / kappa'^j_5, p'_j = - zeta_j / kappa'^j_3:
      x(c)_ij = c_i zeta_j / kappa'^j_i   (i = 3,4,5; c = (-mu', mu, mu' - mu), sum c = 0).
 Row annihilators: sum_j kappa^i_j zeta_j / kappa'^j_i = 0 (i = 3,4,5). C4 (all 3x3 subpermanents vanish on X):
 c_3 c_4 c_5 zeta_j zeta_l zeta_m perm[(1/kappa'^{j'}_i)]_{i in 345, j' in {j,l,m}} = 0. A 2-row element in GEN has >= 2 nonzero
 columns (a one-column element (xi kappa'^j_b e_a - xi kappa'^j_a e_b) e_j^T violates <kappa^a, x_a> = 0), so |supp zeta| >= 2.
 P_2 = 0 on X is equivalent to s_i s_i' = sum_j zeta_j^2 / (kappa'^j_i kappa'^j_i') for the three pairs i < i' in {3,4,5},
 s_i := sum_j zeta_j / kappa'^j_i.   No contradiction derived from these alone.
STATUS 15:24: (S2-d) added (uses stage3's (SR)); stage3 and rows notes read (stage3 already uses (S2) as its hypothesis (H2)).
 Final report follows.
 ADDENDUM to section 7: |supp zeta| >= 3. If supp zeta = {j,l}, X is a plane of 3x2-block matrices x(c)_ij = c_i zeta_j g_ij
 (g_ij := 1/kappa'^j_i) and P_2(x(c)) = zeta_j zeta_l sum_{i<i'} c_i c_i' (g_ij g_i'l + g_il g_i'j) = 0 on {sum c = 0}; a form
 sum_{i<i'} M_ii' c_i c_i' vanishing on that plane has all M_ii' = 0, so r_i + r_i' = 0 for the three pairs (r_i := g_il/g_ij != 0),
 which forces r = 0. Hence each of x_3, x_4, x_5 has >= 3 nonzero columns, so (stage3, GEN) Q_x != 0 for them: every such
 Type I pair produces "bad" 3x2 blocks for the row triples (1,2,i), i = 3,4,5 -- the place to look for the final contradiction
 in GEN (not done).
STATUS 15:26: addendum |supp zeta| >= 3 written. Handing back.

# ROUND 2 (start 15:29, budget 75 min -> ends ~16:44)
STATUS 15:35: round-2 brief + stage3 sections 2-9 read. Working on: (3) one zero entry (pair classification done by hand,
 being machine-checked), then extension of (T1) to that layer, then (1)/(2).

## R2-1. First non-generic layer: ONE zero entry  [rigorous hand proof + machine check, stage2/r2_onezero.py]
 Minimal (1,1) pair (r,r'), kappa := kappa^r has exactly one zero entry kappa_{j0} = 0, kappa' := kappa^{r'} zero-free; E := the other
 four columns. Criterion (G) for T = {j0,l}, l in E (R_T has rank 2, G_11 = -kappa_l kappa'_{j0} != 0, so B1 needs a_T = 0 and
 det G_T = 0):  either  (al) rho'_l = rho'_{j0} and [nu_{j0} = -kappa'_{j0} sigma_l / omega_l (B1)  or  nu_{j0} = 0, sigma_l != 0 (not B1)],
                or      (be) rho'_l != rho'_{j0}, rho_l = -rho'_{j0}, nu_{j0} = 0.
 If nu_{j0} != 0 every l is of kind (al), so rho' is constant and (kappa',nu') dependent: impossible. Hence nu_{j0} = 0: COLUMN j0
 IS FREE IN ROW r ((e_{j0},0) lies in pi_{rr'}(L): some t in L has t_r = e_{j0}, t_{r'} = 0). Gauge rho'_{j0} = 0: every point
 (rho_l,rho'_l), l in E, lies on the axes; rho must be non-constant on E and rho' not identically 0 on E; the C7' rules inside E
 leave only two points (x,0), (0,x) on an anti-diagonal (the L-shape would need the corner (0,0) with sigma = 0, impossible;
 an axis-parallel line makes rho or rho' constant). Result:
   TYPE I_0:  E = E_1 + E_2 (both nonempty), kappa' = c kappa on E_1, -c kappa on E_2 (kappa'_{j0} != 0 arbitrary), and on L
              sum_{E_1} tau_r + sum_{E_2} tau_{r'} = 0   (tau = kappa o t, tau' = kappa' o t)   <=>  Type I with block C = E_1 + {j0}.
   Type II does NOT occur in this layer. Checks: all 14 structures pass the ThB pair test; nu_{j0} != 0 or omega != +-c fail;
   a grid search over 19200 candidate data (rho, rho' in {0,1,2}, omega in +-c, nu_{j0}, rho'_{j0} in {0,1}) finds exactly the
   7 Type I_0 structures compatible with the gauge.
 (T1_0) [EXACT, stage2/r2_triple_onezero.py] Rows 1,2,3 with a = 1, kappa^1 with exactly one zero, kappa^2, kappa^3 zero-free, all
   three pairs minimal ((1,2), (1,3) of Type I_0; (2,3) of Type I or II with the forced ratio pattern): X_123 != 0.
   All 1036 configurations (364 with (2,3) of Type I, 672 of Type II) are killed by an exact non-vanishing certificate.
   (Coordinates: tau_1(j0) is a free coordinate, the weights are still units.)  Not done in this layer: two minimal pairs + lam = 3,
   two zero entries, zero in a row with a >= 2.

## R2-2. The fully generic regime GEN (all a_r = b_c = 1, all row and column FK annihilators zero-free)
 K_ij := kappa^i_j, K'_ij := kappa'^j_i (column annihilators). Tools: (SR) no single-row/column elements (stage3); every column j of
 every t in L is orthogonal to kappa'^j.  Call a minimal row pair (r,r') TRIANGULAR if X_{rr'} meets {row i = 0} nontrivially
 for each of the three other rows i. By (S2): Type I pairs are triangular; a Type II pair is triangular unless some triple
 containing it is the (II,II,lam=3) exception.
 (GEN-0) [rigorous] In GEN the block C of a Type I pair has |C| in {2,3}: for C = {j} the relation K_1j t_1j - K_2j t_2j = 0 would
      be an annihilator of column j with zero entries. For |C| = 2 the Type I relation is a relation of L supported on the 2x2
      block {1,2} x C; if the COLUMN pair C is minimal it is of column-Type I with row block {1,2} (column-Type II is
      impossible) and K/K' = gamma [[1,-1],[-1,1]] on the block ("2x2 block duality").
 (GEN-lin) [rigorous] In GEN, if b is supported off column d and (u_i.b) u_{i'd} + u_{id} (u_{i'}.b) = 0 for all u in L^, then b = 0.
      Proof: on the hyperplane {u_{id} = 0} of L^ one factor of (u_i.b) u_{i'd} vanishes identically; u_{i'd} = lam u_{id} on L^
      would be an annihilator of column d with zero entries; so u_i.b = mu u_{id} on L^, and pi_i(L^) = C^5 gives b = mu e_d, b = 0.
 (GEN-tri) [rigorous; = (S2-d) for any triangular pair] X_12 = { x(c) : x(c)_ij = c_i G_ij, i = 3,4,5, sum c = 0 }, G_ij = zeta_j / K'_ij
      on Sigma := supp zeta, with: equal row sums s (P_1), G_i.G_i' = s^2 (P_2), G_3 G_4 G_5 = 0 in the squarefree algebra (C4).
      |Sigma| = 5 is impossible (multiplication by a full-support G_5 is injective A_2 -> A_3, so G_3 G_4 = 0, impossible for
      zero-free rows on >= 3 columns); |Sigma| = 2 is impossible (addendum of section 7). So |Sigma| in {3,4}; and for
      |Sigma| = 3: s != 0 (s = 0 would make the three rows pairwise orthogonal in the 2-dim space 1^perp, hence all isotropic and
      parallel, and then perm = 6 t t' t'' n_1 n_2 n_3 != 0).
      [CORRECTION: an intermediate claim "for |Sigma| = 3 two rows of G coincide" was wrong (3 vectors in a plane only need a
      singular Gram matrix); caught by stage2/r2_gen_lemmas.py and not used.]
 (Lemma 4x3) [rigorous] No 4x3 matrix with all entries nonzero has equal row sums s, pairwise row products s^2 and all four 3x3
      permanents zero. Proof: s != 0, s = 1: rows 1/3 + v_i, v_i in 1^perp (2-dim), v_i.v_i' = 2/3; the Gram matrix (2/3)J + D of
      four vectors in a plane has rank <= 2, which forces at least three d_i = 0 (rank(D + 11^T) = rank D + 1 when D has a zero
      diagonal entry); for those three rows the differences are isotropic and pairwise non-orthogonal unless parallel, and
      v_i = v_2 + t n with v_2.v_i = 2/3 gives t = 0 (v_2.n = 0 would make v_2 isotropic): three EQUAL rows g, perm = 6 g_1 g_2 g_3 != 0.
      s = 0: four pairwise orthogonal vectors in the plane 1^perp are all isotropic and parallel: perm != 0 again.
 (Lemma H) [rigorous] No 4x4 matrix with all entries nonzero has all sixteen 3x3 subpermanents zero.
      Proof (squarefree algebra on 4 variables, V_4-Fourier): no two rows are parallel (g^2 G = 0 gives t_j + t_l + t_m = 0 for
      all triples, t = G/g, so t = 0). Scale columns so that row G_2 = e. Q := G_4 G_5 != 0 is killed by e, so Q_12 = Q_34 = al,
      Q_13 = Q_24 = be, Q_14 = Q_23 = ga, al + be + ga = 0, i.e. Q is a function phi on V_4 = {1,a,b,ab} with phi(1) = 0; G_3 Q = 0
      reads rho * phi = 0 (convolution, rho = G_3/G_2), i.e. rho^(chi) phi^(chi) = 0 for all characters, phi^ = (0, 2al, 2be, 2ga).
      As rho is not constant exactly one of al, be, ga vanishes, say ga, and rho is constant on {1,4} and on {2,3}; ga = 0 means
      (G_5/G_4)_1 = -(G_5/G_4)_4 and (G_5/G_4)_2 = -(G_5/G_4)_3. Applying this to every splitting of the four rows into two
      pairs: every ratio G_q/G_p is a constant times a balanced sign vector, so G = D_1 H D_2 with H the 4x4 Hadamard matrix,
      whose 3x3 subpermanents are all +-2. Contradiction.  (LM search: all 25 converged solutions of the 16 equations have a
      numerically zero entry, stage2/r2_lemmaH.py.)
 THEOREM GEN-1 [rigorous]. In GEN no row lies in two triangular minimal pairs; in particular NO ROW LIES IN TWO MINIMAL
      TYPE I PAIRS (the minimal Type I pairs of a fully generic 9-dim level space form a matching), and the same for columns.
      Proof. Let (1,2), (1,3) be triangular. X_123 = X_12 cap X_13 is the line of both triangles on rows 4,5, so the two zeta's
      are proportional: W := X_12 + X_13 = { c_i zeta_j / K'_ij : c on rows 2,3,4,5, sum c = 0 } (3-dim, inside L_1). With
      G = (zeta_j/K'_ij), rows 2..5, columns Sigma: P_1, P_2 on W give equal row sums s and G_i.G_i' = s^2 for all six pairs
      (the monomials c_i c_i' are independent on {sum c = 0}); the cubic part of perm(u + x(c)) = perm(u) gives
      perm(u with rows I replaced by G_I) = 0 for all four triples I and all u in L^ (the four cubic monomials are independent
      on {sum c = 0}); for I = 345, 245 this is C4; for I = 235: |Sigma| = 3: perm(G[235;Sigma]) q_{Sigma^c}(u_1,u_4) = 0 and u = J
      gives perm(G[235;Sigma]) = 0; |Sigma| = 4, Sigma^c = {d}: the identity is (u_1.b) u_4d + u_1d (u_4.b) = 0 with
      b_l = perm(G[235;Sigma - l]), so b = 0 by (GEN-lin); same for I = 234. So all 3x3 subpermanents of G vanish:
      |Sigma| = 3 contradicts Lemma 4x3, |Sigma| = 4 contradicts Lemma H.  QED
 CONSEQUENCE. If (1,2) is a minimal Type I pair in GEN, every pair (1,i), (2,i) (i = 3,4,5) has lam >= 3 or is a NON-triangular
      minimal Type II pair (then some triple through it is the (II,II,lam=3) exception).
 NOT achieved: "a 9-dim level space cannot be fully generic". Missing: a single triangular pair; Type II pairs; all lam >= 3
      (stage3's S3-D regime).
STATUS 15:50: R2-1 (one zero entry: Type I_0, T1_0) and R2-2 (GEN-0, GEN-lin, Lemma 4x3, Lemma H, Theorem GEN-1) written.

## R2-3. THEOREM GEN-2: a fully generic 9-dim level space has NO triangular minimal pair, hence NO minimal Type I pair
 [rigorous hand proof; the two linear-algebra steps machine-checked: stage2/r2_gen_lemmas.py (independence of the monomials),
  stage2/r2_gen2_check.py (no isotropy matrix B: 50 Type I and 1500 Type II cases, dim = 0 in all)]
 Setting GEN, (1,2) a triangular minimal pair, X_12 = {x(c)_ij = c_i G_ij}, G_ij = zeta_j/K'_ij (i = 3,4,5; j in Sigma), as in (GEN-tri).
 Step 1. perm(u + x(c)) = perm(u) on L^ for all c with c_3 + c_4 + c_5 = 0; its part of degree 2 in c gives (c_3c_4, c_3c_5, c_4c_5
   are independent on the plane)   P_ii'(u) := perm(u with rows i,i' replaced by G_i, G_i') = 0  for all u in L^, {i,i'} in {3,4,5}.
   Laplace along rows i,i':  P_45(u) = sum_{T in Sigma} Q_45[T] perm(u[123; T^c]),  Q_45 := G_4 G_5 != 0 (zero-free rows).
 Step 2. |Sigma| <= 2 and |Sigma| = 5 are impossible (GEN-tri).
 Step 3. |Sigma| = 3, Sigma^c = {d,e}. On V_i := {u in L^ : u_id = u_ie = 0} (dim 8; i = 3): perm(u[123;{p,d,e}]) = u_3p q_de(u_1,u_2), so
   P_45 = q_de(u_1,u_2) <Q*,u_3>, Q*_p := Q_45[Sigma - p] != 0. A product vanishing on a vector space has a vanishing factor;
   <Q*,u_3> = 0 on V_3 would give <Q*,u_3> = al u_3d + be u_3e on L^, impossible since pi_3(L^) = C^5. So q_de(u_1,u_2) = 0 on V_3:
   the image of V_3 in the 2x2 block [12;de] is totally isotropic for the nondegenerate form q_0, so it has dim <= 2 and
   {u in L^ : u[12i;de] = 0} has dim >= 6; the same for i = 4, 5 (use P_35, P_34).
   But U := {u in L^ : u[12;de] = 0} has dim exactly 6: no nonzero combination of the two annihilators of I^_12 (Type I or II)
   is supported on two columns [Type I: row 2 forces al = 0 or al = -be, row 1 then be sigma_0 = 0; Type II: row 2 forces
   al = 0 or (Sigma inside Q_2, al = be), row 1 then be y = 0 or be(1+y) = 0]. Hence all of U has u_id = u_ie = 0 for i = 3,4,5:
   columns d, e of every u in U vanish, U lies in L cap {column d = 0}, which has dim 9 - 4 = 5 < 6. Contradiction.
 Step 4. |Sigma| = 4, Sigma^c = {d}. On U_d := {u in L^ : u_1d = u_2d = 0}: perm(u[123;{p,q,d}]) = u_3d q_pq(u_1,u_2), so
   P_45 = u_3d Phi(u_1,u_2), Phi(z) = z_1^T B z_2, B[j,l] := Q_45[Sigma - {j,l}] (4x4 symmetric, zero diagonal, B != 0).
   u_3d = 0 on U_d would be a column-d annihilator (al,be,-1,0,0) with zeros. So Phi = 0 on I^d := {z in I^_12 : z_1d = z_2d = 0},
   a subspace of codimension exactly 2 of C^{2 x Sigma} (no annihilator of I^_12 is supported on one column: GEN-0 for Type I,
   direct for Type II). Then rank B = 2, B = a b^T + b a^T with disjoint supports A, B' and I^d is the preimage of a maximal
   isotropic plane; if both row projections of I^d are onto, I^d^perp = {(xa + yb, mu(-xa + yb))}, so kappa^2 = mu kappa^1 on A,
   -mu kappa^1 on B', and in tau-coordinates EVERY annihilator of I^d has the form (v,-v), v constant on A and on B'.
   Type I: the second annihilator is (1_{C cap Sigma} - sigma_0 1_Sigma, -1_{C cap Sigma}): needs sigma_0 = 0, false.
   Type II: the ratio kappa^2/kappa^1 takes two opposite values on Sigma, so Q_1 = {d}, {A,B'} = {Q_2,Q_3}, and the second
   annihilator (1_{Q_3} + y 1_Sigma, 1_{Q_2}) needs y = -1, false. If a row projection of I^d is not onto (only Type II with
   Q_2 = {d} or Q_3 = {d}): I^d = {<n,z_1> = 0, <kappa^2,z_2> = <kappa^1,z_1>} with n zero-free on Sigma and not parallel to
   kappa^1; then B z_1 = 0 for a dense set of z_1 in n^perp, so rank B <= 1, B = 0. Contradiction in all cases.   QED
 COROLLARIES (GEN):
   (i)   no minimal Type I row pair and (transpose) no minimal Type I column pair  [Type I pairs are triangular by (S2)];
   (ii)  every minimal pair is of Type II and NON-triangular: for a minimal pair (r,r') some third row i has X_{rr'i} = 0, and
         the triple (r,r',i) is the exception of (S2): a second minimal Type II pair through r or r' and a third pair with lam = 3;
   (iii) Theorem GEN-1 (R2-2) is a special case; Lemma 4x3 and Lemma H remain true but are no longer needed.
 So in GEN:  minimal pairs exist  <=>  one of the (II,II,lam=3) exception triples exists (the 21 canonical configurations of
 item O2, further restricted in GEN: no relation of L may be supported in one column, e.g. Q_2 = Q_2' = {j} is excluded).
 If these are excluded, GEN reduces to "all lam >= 3 for rows and columns" = stage3's hypothesis (H1) with all a_r = b_c = 1.
STATUS 15:55: Theorem GEN-2 proved and written (no minimal Type I pairs in the fully generic regime).

## R2-4. Lemma GEN-3 (2-row elements against a minimal pair) and the remaining minimal pairs in GEN  [rigorous]
 Steps 3 and 4 of GEN-2 use only ONE 2-row element. In GEN let (r,r') be a minimal pair, i a third row and y != 0 a 2-row
 element of L on the two remaining rows (so y lies in X_{rr'i}); Sigma_y := its column support, Q_y := the vector of its 2x2
 subpermanents. Since perm(u with the two rows replaced by those of y) = 0 on L^ (s^2-coefficient of perm(u + s y)):
   (a) |Sigma_y| = 4 is impossible (Step 4 verbatim; block-rank facts checked for all pair types, stage2/r2_block_rank.py);
   (b) if |Sigma_y| = 3, Sigma_y^c = {d,e}: every t in L with t[rr';de] = 0 also has t[i;de] = 0 (Step 3); in particular every
       x in X_{rr'} vanishes at the cells (i,d), (i,e);
   (c) |Sigma_y| >= 2 always (GEN), and Q_y != 0 iff |Sigma_y| >= 3.
 Use for a NON-triangular minimal pair (1,2) (Type II by GEN-2), V_i := X_12 cap {row i = 0}:
   two lines V_4 = C x_4, V_5 = C x_5 (V_3 = 0), supports Sigma' and Sigma: C4 gives Q_{x_5} G'_5 = 0 = Q_{x_4} G_4 (rows as elements of
   the squarefree algebra), so not both supports have size >= 3 with one of size 5; by (a) sizes lie in {2,3,5}; by (b) a
   support of size 3 contains the other support; (3,3) with equal supports puts {t in L : t[12;de] = 0} (dim 6) inside
   {column d = 0} (dim 5): impossible. Left: (|Sigma|,|Sigma'|) in {(2,2),(2,3),(3,2),(2,5),(5,2)}, one line only, a common zero
   row, or no line at all (three exception triples).  NOT finished.
 WHAT REMAINS IN GEN (exact): minimal pairs can only be non-triangular Type II pairs in the sub-cases just listed, each
 forcing at least one (II,II,lam=3) exception triple; if those are excluded, GEN is the regime "all lam >= 3 for rows and
 columns, all a_r = b_c = 1" (stage3's (H1): S3-A, S3-D apply; not closed).
STATUS 15:59: Lemma GEN-3 written. Items (2) (the 21 Type-II/Type-II configurations) NOT attacked computationally in round 2
 (only restricted in GEN). Updating the RESULT block and handing back.

## R2-5. Two more rigorous remarks for GEN
 (GEN-4) A minimal pair (1,2) whose plane X_12 has a common zero row (X_12 = plane of 2-row elements y(xi), xi in a 2-plane Xi,
      on rows 4,5): by (GEN-3)(a),(c) every nonzero element has support of size 2, 3 or 5; counting the zeros of the five
      coordinate forms on Xi leaves generic support 3 with three simple zeros, or generic support 5 with proportionality
      classes of sizes (2,3). Generic support 3 is impossible: P_2 = sum_T xi_j xi_l perm(K'[45;T]) vanishes on the plane
      Xi = {n.xi = 0} of C^3 (n zero-free), a squarefree quadric divisible by n.xi is 0, so perm(K'[45;T]) = 0 for all three
      pairs, impossible. So X_12 = span(y_A, y_B) with y_A of B-type on a 2x2 block [45;A] and y_B supported on the
      complementary three columns; and every t in L with t[12;A] = 0 has t[3;A] = 0.  (Not excluded.)
 (GEN-5) In an exception triple with Q_3 = Q_3' the difference of the two Type II relations is sum_{Q_2} tau_2 - sum_{Q_2'} tau_3 = 0
      on L; if Q_2 = Q_2' = {j} this is an annihilator of column j with zero entries: excluded in GEN. This removes 3 of the
      21 canonical survivors of t8_two_minimal.py ((0,1,2,2,2), (0,0,0,1,2), (0,0,1,2,2) paired with their conjugates); 18 remain.
STATUS 16:00: R2-5 added.
STATUS 16:05: round-2 final report sent. Best next steps: (i) in GEN finish the non-triangular Type II minimal pairs with
 (GEN-3) + C4 + P_2 (sub-cases listed in R2-4, R2-5), which would give "GEN => lam >= 3 for all row and column pairs";
 (ii) the 18 remaining (II,II,lam=3) configurations (full cube condition + J-relations; not attempted); (iii) transfer the
 product-factorisation argument of GEN-2 to rows/columns with one zero entry (Type I_0), where single-row elements can exist.

# ROUND 3 (start 16:09, budget 75 min -> ends ~17:24)
STATUS 16:12: stage3 round-2 RESULT read (N3', N3'-L, MIN-A/B/C, configuration (II)). Working on the exception triples.

## R3-1. THE EXCEPTION TRIPLES ARE IMPOSSIBLE  [num-assisted: the list of admissible fifth annihilators comes from a floating-point
##        search over exact combinatorial data; the final contradictions are hand computations, confirmed numerically]
 Setting (any 9-dim level L, not only GEN): rows 1,2,3 with a = 1 and zero-free annihilators, (1,2), (1,3) minimal Type II,
 dim X_23 = 3, X_123 = 0. Then I_3^perp = span(A0) + C n**, A0 = {f_1-f_2, f_1-f_3, g_12 + y_12 f_1, g_13 + y_13 f_1}, n** = (0,m_2,m_3).
 (E1) [rigorous] Dimension count: the row-1 parts 1_{Q_3}, 1_{Q_3'} agree up to complement (1668 of 1800 canonical pairs excluded).
 (E2) [rigorous lemma, as in (T2)] For EVERY column triple S with ell != 0 on Pi~_S := span(A0)^perp cap C^{3xS} (also when the
      pair functionals are dependent on S), with K_S := Pi~_S cap ker ell and c_S := perm|K_S:  n**|K_S = 0 or n**|K_S divides c_S.
 (E3) [rigorous] Admissibility: m_3 not in span(1, 1_{Q_2'}) and m_2 not in span(1, 1_{Q_2}) (otherwise n** would be equivalent to a
      functional of rows (1,2) or (1,3), giving I_12 or I_13 a third annihilator).  [Round 1's t8 survey used only "not a
      row-1 functional" and only the S with independent functionals; that is why it reported 21 survivors.]
 (E4) [floating point] stage2/r3_survey.py: of the 132 remaining canonical configurations 120 have no admissible n** at all;
      12 survive, each with exactly ONE maximal family ("leaf") of admissible n**:
        (a) the six CONJUGATE configurations (same cells Q_1,Q_2,Q_3, eps_2 = +1, eps_3 = -1):
              n** = sum_{Q_1}(tau_2 - i tau_3) + (1-i) sum_{Q_2} tau_2 - delta ell      (delta in C the only parameter);
        (b) six NON-CONJUGATE ones, in two column/row-swap classes:
              A: Q_1={0,1,2}, Q_2={3}, Q_3={4}; Q_1'={0,3}, Q_2'={1,2}:  n** = al tau_2(0) + be (tau_3(1) - tau_3(2)) + ga tau_2(3) - delta ell
              (B = A with rows 2,3 exchanged);
              C: Q_1=Q_2'={0,1}, Q_2=Q_1'={2,3}, Q_3={4}:               n** = al (tau_2(3) - tau_2(2)) + be (tau_3(0) - tau_3(1)) + ga (tau_2(2) + tau_2(3)) - delta ell.
 (E5) [hand; confirmed by stage2/r3_hand_check.py and r3_generic_fail.py: cube defect 1.0 in all 12 configurations]
      FULL CUBE CONDITION (perm_3 = k ell^3 on Pi_S whenever ell != 0 there) fails for every member of these families:
        (a) S = {p in Q_1, q in Q_2, s in Q_3}: Pi_S is parametrised by ell, a_1 = tau_1(p), c_1 = tau_1(s), a_3 = tau_3(p);
            the coefficient of a_1 in perm_3 is E_1 with quadratic part 0, A-coefficient 0 and c_1-coefficient -(1+i) delta_h
            (delta_h = delta + i), so delta_h = 0, and then perm_3 = (1+i)(1+ybar) c_1 ell^2 = c_1 ell^2, not a multiple of ell^3.
        (b) A and C: S = {the two columns of the 2-element cell carrying tau_3(.) - tau_3(.)} + {column 4}: on Pi_S
            tau_3 = (d ell, -d ell, ell) (d = delta/(2 be)), tau_1 = (t_1, (1+y) ell - t_1, -y ell), tau_2 = (a, b, ell - a - b), and the
            coefficient of t_1 in perm_3 is ell [ i(b - a) + 2d(ell - a - b) ], which vanishes identically only if i = 2d = -i;
            be = 0 is inadmissible by (E3).
 CONSEQUENCES.
 (S2*) [num-assisted] For ANY three rows with a = 1 and zero-free annihilators of a 9-dim level space: X_ijk != 0. So if all five
      rows have a = 1 and zero-free annihilators, every pair of rows carries a nonzero 2-row element (no hypothesis on Type II).
 (GEN-6) [num-assisted for the exception part, otherwise rigorous] A fully generic 9-dim level space has NO minimal pair:
      lam >= 3 for all ten row pairs and all ten column pairs. (A minimal pair would be triangular by (S2*), impossible by GEN-2.)

## R3-2. Two general factorisation lemmas for 2-row elements  [rigorous; sanity on the examples: stage2/r3_Y3.py (144 cases),
##        r3_Y5.py (90 cases), 0 violations]
 y != 0 a 2-row element of a 9-dim level L on rows a,b; {c,d,e} the other rows; Q_y[T] := 2x2 subpermanent of y on the column
 pair T. Always: perm(u with rows a,b replaced by y_a, y_b) = sum_T Q_y[T] perm(u[cde;T^c]) = 0 for all u in L^.
 (Y3) |Sigma_y| = 3, Sigma_y^c = {d',e'}, Q_y != 0, and a_i = 1 for i in {c,d,e}: on {u in L^ : u_id' = u_ie' = 0} the identity is
      q_{d'e'}(u_i',u_i'') <Q*,u_i>, the linear factor cannot vanish (pi_i(L^) = C^5), so the image of that 8-dim space in the 2x2
      block [i'i'';d'e'] is totally isotropic and  dim {u in L^ : u[cde;d'e'] = 0} >= 6  (generic value 4): the 3x2 block
      {c,d,e} x Sigma_y^c carries >= 2 independent relations of L^.  [No minimality needed; this is Step 3 of GEN-2.]
 (Y5) c a row with a_c = 1, j a column with kappa^c_j != 0, F := [5] - j, B^{y,j}[p,q] := Q_y[F - {p,q}] (4x4, symmetric, zero
      diagonal). On V_cj = {u in L^ : u_c in C e_j} (dim 6) the identity is u_cj * (u_d^T B^{y,j} u_e) (columns F), and u_cj != 0
      there, so the image W of V_cj in rows d,e, columns F is isotropic:  rank B^{y,j} <= 8 - dim W.  In GEN the kernel of
      V_cj -> W is Y_ab, so      rank B^{y,j} <= 2 + m_ab.
      For m_ab = 1: det B^{y,j} = 0, i.e. with pi_1, pi_2, pi_3 the products of Q_y over the three perfect matchings of F:
      pi_1^2 + pi_2^2 + pi_3^2 = 2(pi_1 pi_2 + pi_1 pi_3 + pi_2 pi_3).  In GEN Q_y[pq] = - xi_p xi_q K'_ap K'_aq (r_p + r_q), r := K'_b/K'_a, and the
      condition becomes (A,B,C the three matching sums of products of r)  AB + AC + BC = e_1 e_3 - 4 e_4 = 0, i.e.
            (sum_{x in F} r_x)(sum_{x in F} 1/r_x) = 4      for every 4-set F inside Sigma_y.
 (GEN-7) In GEN a 2-row element y with m_ab = 1 has |Sigma_y| <= 4.  Proof: for |Sigma_y| = 5 all five 4-sets satisfy the
      equation, so every r_j is a root of h x^2 - (sh - 3) x + s = 0 (s = sum r, h = sum 1/r; h = 0 gives r = 0): at most two
      values, with multiplicities (n_1,n_2), n_1 + n_2 = 5; a 4-set with k and 4-k of them needs k^2 + (4-k)^2 + k(4-k)(t + 1/t) = 4:
      k = 2: t + 1/t = -1; k = 1,3: t = -1; k = 0,4: impossible; (4,1) contains a (4,0) set, (3,2) contains both (2,2) and (3,1)
      sets. Contradiction. (LM search for five such numbers: residual floor 2.8, stage2/r3_Y5.py.)

## R3-3. Configuration (II) (stage3) is impossible in GEN  [rigorous given the lemmas above]
 (II): F = { sum_{i in N_4} c_i e_i rho_i^T : sum c = 0 } in L, N_4 four rows. In GEN the column annihilators give
 K'_ij rho_i(j) = zeta_j independent of i, so F is rank one in column-weighted coordinates, G := (rho_i(j)) = (zeta_j/K'_ij),
 zero-free on Sigma := supp zeta. P_1, P_2 on F: equal row sums s, rho_i.rho_k = s^2; lineality of F: perm(u with the rows of a
 triple I in N_4 replaced by rho_I) = 0 on L^.
   |Sigma| = 1: rho_i = c e_j is not orthogonal to kappa^i.   |Sigma| = 2: P_2 forces r_i + r_k = 0 for all pairs of four rows.
   |Sigma| = 3: the triple identity is perm(G[I;Sigma]) q_{Sigma^c}(u_d,u_e), and u = J gives perm(G[I;Sigma]) = 0 for all four
               triples: contradicts Lemma 4x3.
   |Sigma| = 4: the triple identity has the form of (GEN-lin), so all sixteen 3x3 subpermanents of G vanish: contradicts Lemma H.
   |Sigma| = 5: x^{ik} = e_i rho_i^T - e_k rho_k^T is a 2-row element with full support; if m_ik = 1 this contradicts (GEN-7).
 So (II) cannot occur in GEN when some pair inside N_4 has a 1-dimensional space of 2-row elements; in particular not in
 stage3's minimal case (all lam = 3, all m = 1). With stage3's MIN-C (minimal case + (NZ) => (II); (NZ) holds in GEN):
 (GEN-8) A fully generic 9-dim level space is NOT in the minimal case: some row pair has lam >= 4 or some row pair carries
      a >= 2-dim space of 2-row elements; and (transpose) the same for columns.

## R3-4. State of GEN after round 3 and the precise remaining list
 PROVED for a fully generic 9-dim level space L (all a_r = b_c = 1, all annihilators zero-free):
   (1) no single-row / single-column elements, no dominoes (stage3 SR/SC);   (2) no minimal Type I pair (GEN-2, rigorous);
   (3) no minimal pair at all, i.e. lam >= 3 for all row and column pairs (GEN-6; the exclusion of the exception triples is
       num-assisted, R3-1);   (4) every row pair and every column pair carries a nonzero 2-line element, each with >= 2 nonzero
       columns (rows);   (5) not the minimal case (GEN-8; uses stage3's MIN-C);   (6) constraints (Y3), (Y5), (GEN-3), (GEN-7) on
       every 2-row element.
 NOT PROVED: "a 9-dim level space cannot be fully generic". What survives in GEN is exactly stage3's (R3) on BOTH sides:
   rows:    some lam_{rr'} >= 4  or  some m_ab >= 2;        columns:  some lam^{cc'} >= 4  or  some m^{T} >= 2,
 with all lam >= 3, no sparse (one-line) elements, and the identities (Y3)/(Y5) for all 2-row and 2-column elements.
 Other open items (unchanged): making R3-1 exact (leaf enumeration over Q(i)); zero entries beyond one zero with all pairs
 minimal; rows with a_r >= 2 (Type I'); stage3's (R2), (R4), (R5).
STATUS 16:35: R3-1 .. R3-4 written.
STATUS 16:37: RESULT-R3 written at the top. Remaining time used for (R3) in GEN.
STATUS 16:41: stage3's round-3 RESULT read (N1: all lam = 3 => single-row element; otherwise the rigid family N2). Attacking N2 in GEN.

## R3-5. LEMMA N2-GEN (family N2 is impossible with zero-free column annihilators) and THEOREM GEN
##       [hand proof; numerics: stage2/r3_N2.py, r3_N2b.py, r3_N2c.py, r3_N2d.py]
 LEMMA N2-GEN. Let L be a level space (any dimension) and c,d,e three rows such that every column j has an FK annihilator kappa'^j
 with K'_ij := kappa'^j_i != 0 for i in {c,d,e}; L has no single-row element in rows c,d,e and no single-column element in rows c,d
 [both automatic in GEN]. Then it is IMPOSSIBLE that m_cd = m_ce = m_de = 2 and Y_de lies in Y_cd + Y_ce.
 [In stage3's case N2: lam_ab = 4, X_ab = Y_cd (+) Y_ce contains Y_de, all three m = 2.]
 Step 0 (normal form). 2-row elements obey the column annihilators: on (c,d) t_dj = -a_j t_cj, on (c,e) t_ej = -b_j t_cj, with
   a_j := K'_cj/K'_dj, b_j := K'_cj/K'_ej (all nonzero). Y_cd = {(v; -a o v): v in P_cd}, Y_ce = {(v'; -b o v'): v' in P_ce}, the sum
   is direct (no single-row element). An element of the sum with row c = 0 has v' = -v in P_cd cap P_ce; dim Y_de = 2 forces
   P_cd = P_ce =: P (a 2-plane), and     X := Y_cd + Y_ce = {(pi_c; a o pi_d; b o pi_e) : pi_i in P, pi_c + pi_d + pi_e = 0}.
   P contains no unit vector (e_j in P gives the single-column element (e_j; -a_j e_j) in Y_cd).
 Step 1 (level conditions). For t supported on three rows, perm(J + t) = 120 + 24 P_1 + 6 P_2 + 2 P_3 with (s_i = row sums)
   P_1 = sum t_ij, P_2 = sum_{i<k} (s_i s_k - <t_i,t_k>), P_3 = s_c s_d s_e - sum s_i <t_k,t_l> + 2 sum_j t_cj t_dj t_ej.
   Let lam_j be the coordinate functions on P and sigma := sum_j lam_j. P_1, P_2 on Y_cd, Y_ce, Y_de and P_3 on X give
     (i)   sum a_j lam_j = sum b_j lam_j = sigma;      (ii)  sum c_j lam_j^2 = sigma^2  for c in {a, b, ab};
     (iii) sum a_j b_j lam_j^3 = sigma^3
   [(iii): with (i),(ii) polarised, P_3 = 2 Phi(pi_c,pi_d,pi_e), Phi(x,y,z) := sum a_j b_j x_j y_j z_j - sigma(x)sigma(y)sigma(z);
   Phi(x,x,-2x) = 0 kills the cubic form]. Conversely (i)-(iii) are equivalent to "X level" (r3_N2c.py: 39 numerical solutions
   of (i)-(iii) give |perm(J+t) - 120| < 4e-9 on X; random data give 1e3).
 Step 2 (moment form). Take nu != 0 in ker(sigma|P), S := supp nu, eta in P - C nu, tau := sigma(eta), zeta_j := eta_j/nu_j (j in S),
   lam = s nu + t eta. Coefficients of s^i t^k (weights c: (M1) c in {1,a,b}; (M2) c in {a,b,ab}; W_j := a_j b_j nu_j^3 != 0):
     (M1) sum_S c nu = 0,                         sum_S c nu zeta   + sum_{S^c} c eta   = tau;
     (M2) sum_S c nu^2 zeta^r = 0 (r = 0,1),      sum_S c nu^2 zeta^2 + sum_{S^c} c eta^2 = tau^2;
     (M3) sum_S W zeta^r = 0 (r = 0,1,2),         sum_S W zeta^3    + sum_{S^c} ab eta^3 = tau^3.
   (V) If zeta takes k <= 3 distinct values on S, all class sums of W vanish (Vandermonde): no zeta-class is a singleton.
   (L) For k distinct points z_m, F := prod (z - z_m), om_m := 1/F'(z_m): sum om_m z_m^r = 0 (r <= k-2), = 1 (r = k-1); every vector on
       the points is om_m G(z_m) with deg G <= k-1, and the moments read off the top coefficients of G.
 Step 3 (cases: |S| and the partition of S into zeta-classes).
   |S| = 1: unit vector.   |S| = 2: (M1) gives nu_1 + nu_2 = 0 and a_1 = a_2, so sum a nu^2 = 2 a_1 nu_1^2 != 0, against (M2).
   |S| = 3: by (V) one class, so eta' := eta - zeta nu lives on S^c and has support exactly 2 (no unit vector). sigma(eta') = 0 is the
     case |S| = 2. Otherwise sigma(eta') = 1 and A_j := a_j eta'_j, B_j := b_j eta'_j (j = 4,5) satisfy sum eta' = sum A = sum B = 1,
     sum A eta' = sum B eta' = sum A B = 1, i.e. (2A_4-1)(2eta'_4-1) = (2B_4-1)(2eta'_4-1) = (2A_4-1)(2B_4-1) = 1, so (2A_4-1)^2 = 1
     and A_4 A_5 = 0. Contradiction.
   |S| = 4, S^c = {5}: by (V) the classes are (4) [eta - zeta nu in C e_5: unit vector], (2,2) or (1,1,1,1).
     (2,2), class {1,2}: the class sums of W and (two points, r = 0,1) of ab nu^2, a nu^2, b nu^2 vanish; W_1 + W_2 = 0 = V_1 + V_2
       gives nu_1 = nu_2, then a_1 = -a_2, b_1 = -b_2 and (ab nu^2)_1 + (ab nu^2)_2 = 2 a_1 b_1 nu_1^2 != 0. Contradiction.
     (1,1,1,1): by (L) W_j = c om_j (c != 0), ab nu^2 = om_j(al + be zeta_j), a nu^2 = om_j(al_a + be_a zeta_j), b nu^2 = om_j(al_b + be_b zeta_j);
       so nu_j = c/(al + be zeta_j), and (al_a + be_a z)(al_b + be_b z)(al + be z) - c^2 F'(z) is a cubic with four roots: be be_a be_b = 4c^2.
       With h := eta_5, A := a_5 h, B := b_5 h the remaining equations of (M1)-(M3) read
          4c/be = tau - h,  be_a be/c = tau - A,  be_b be/c = tau - B,  be_a = tau^2 - A h,  be_b = tau^2 - B h,  be = tau^2 - AB,  c = tau^3 - AB h.
       h = 0: 4 tau = tau and c = tau^3 = 0. h != 0: be_a be = c(tau - A) expands to A tau (tau - B)(tau - h) = 0, likewise
       B tau (tau - A)(tau - h) = 0; tau = 0 gives 5h = 0, tau = h gives c = 0; so tau = A = B, be_a be = 0, against be be_a be_b = 4c^2.
   |S| = 5: sigma is not 0 on P (else every nonzero vector of P would be zero-free by the cases above), ker = C nu, tau != 0, normalise
     tau = 1. By (V): (5) [eta in C nu]; (3,2) [P = C phi + C psi with disjoint supports, polarised (ii) gives sigma(phi) sigma(psi) =
     sum a phi psi = 0: a vector of ker sigma that is not zero-free]; (2,1,1,1); (1,1,1,1,1).
     (1,1,1,1,1): by (L) nu = om N, a nu = om N_a, b nu = om N_b (cubics, leading coefficient 1), a nu^2 = om A, b nu^2 = om B (monic
       quadratics), W = om (z + w_0); shift eta by a multiple of nu: w_0 = 0. (a nu^2)(b nu^2) = W nu gives AB = z N (degree <= 4, five
       roots). So z | A or z | B; by the symmetry a <-> b let A = z(z - al), N = (z - al) B. (b nu)(nu) = b nu^2 gives
       N_b N - F' B = F l_b, l_b linear with leading coefficient 1 - 5 = -4. Hence B [(z - al) N_b - F'] = F l_b; B(zeta_j) != 0 for all j,
       so B is prime to F and divides l_b: impossible (deg B = 2).
       [r3_N2d.py: this step needs BOTH a nu and b nu: the 16 moment equations for nu, a nu, b nu, a nu^2, b nu^2, ab nu^3 in 20
       unknowns have 0/120 LM solutions; without the two a nu equations 110/120 non-degenerate solutions (the branch z | B).]
     (2,1,1,1), double class {1,2} at z_1, F = (z - z_1) F_1: class sums W = om (constant 1); a nu^2, b nu^2, ab nu^2 <-> monic linear
       A, B, V; nu, a nu, b nu <-> monic quadratics N, N_a, N_b. At the three singleton points: AB = N; VN - F' = A N_b - F' =
       B N_a - F' = -3 F_1 (cubics, three roots, leading coefficient 1 - 4). So N_b = VB, N_a = VA, VAB = (z - z_1) F_1' - 2 F_1.
       With p,q,r := A,B,V at z_1 and om := 1/F_1(z_1): om p q r = -2, and the class sums over {1,2} are
          sum nu = om pq, sum a nu = om rp, sum b nu = om rq, sum a nu^2 = om p, sum b nu^2 = om q, sum ab nu^2 = om r, sum ab nu^3 = om.
       Put nu_i = om pq (1 +- Z)/2, a_i nu_i = om rp (1 +- X)/2, b_i nu_i = om rq (1 +- Y)/2: the quadratic sums give
       (1 + XZ)/2 = (1 + YZ)/2 = (1 + XY)/2 = 1/(om pqr) = -1/2 and the cubic sum gives (1 + XY + XZ + YZ)/4 = 1/(om pqr)^2 = 1/4,
       i.e. -5/4 = 1/4. Contradiction.                                                                                   QED
 Numerical corroboration of the whole lemma (r3_N2b.py, LM on (i)-(iii), 200 starts): 198 solutions, 191 with a zero or infinite
 weight a_j or b_j, 7 with a unit vector in P, 0 genuine. (The strata with a singleton class, (2,1,1,1) and |S| = 4 are
 overdetermined, so they are only covered by this survey, not by a separate underdetermined test.)

 THEOREM GEN [CONDITIONAL on (a), (b)]. A 9-dim level space is never fully generic.
 Proof. In GEN: lam >= 3 for all row pairs (GEN-6 = GEN-2 [rigorous] + R3-1 [num-assisted] = input (a)); no single-row element
 (zero-free column annihilators); all a_r = 1. stage3 sec. 16 = input (b): either all lam = 3, and then Theorem N1 produces a
 single-row element, or case N2: lam_ab = 4, m_cd = m_ce = m_de = 2, X_ab = Y_cd (+) Y_ce. Lemma N2-GEN excludes N2.   QED
 Only the ROW side of GEN-6 and the zero-freeness of the column annihilators at three rows are used after GEN-6.
 What I did NOT do: verify stage3's sections 12, 14, 15, 16 myself (I read section 16 and re-derived only (G1)/(G2)-type facts
 I use: X_ab = Y_cd (+) Y_ce and P_cd = P_ce); make R3-1 exact.
 REMAINING LIST (16:59): (1) verification of the two conditional inputs: R3-1 exact (leaf enumeration over Q(i)) and stage3's
 sections 12-16; an independent check of Lemma N2-GEN (short; a CAS elimination of the seven moment families would settle it);
 (2) family N2 OUTSIDE GEN (column annihilators with zero entries at the rows c,d,e, or b_c >= 2): the normal form of Step 0 changes;
 (3) zero entries in the annihilators beyond one zero with all pairs minimal; rows/columns with a_r >= 2 (Type I'); stage3's (S2), (S3).
 Runs to report: r3_N2.py first run (400 starts) hit its 170 s timeout with no output; r3_N2b.py hit its 150 s timeout in the
 second (exp-parametrised) half, the first half is the survey quoted above; r3_N2d.py symmetric run 1m49s. All others < 20 s.
STATUS 16:59: R3-5 written; headline updated. Final report follows.
STATUS 17:02: second survey seed for Lemma N2-GEN (r3_N2b.py 23 0 150 plain, 59 s): 148 solutions of (i)-(iii): 144 with a zero or
 infinite weight, 4 with a unit vector in P, 0 genuine (total over both seeds: 346 solutions, 0 genuine). Re-derived the elementary
 parts of stage3's reduction that Theorem GEN uses ((P), (G1), (G2), lam_ab = 5 impossible): correct; so input (b) is exactly
 stage3's Theorem N1 (all a_r = 1, all lam = 3 => single-row element). Round-3 final report sent.

# ROUND 4 (start 17:08, budget 90 min -> ends ~18:38). Target: regime REG1 := "all a_r = 1 and all b_c = 1", annihilators may have zeros.
STATUS 17:27: read rows' defect normal form / Corollary H, verifyfl's TC5, chief's RP6/RP7/RP9 (Lemma DS), stage3 sec. 16-17.
 Census of the known examples (stage2/r4_census.py): none is in REG1 (all have several lines with a >= 2), so REG1 has no examples to guide.
 Numerical exploration of the GENERAL N2 block X_ab = {(psi_c(p_c); psi_d(p_d); psi_e(p_e)): sum p_i = 0} (stage2/r4_block.py, 14 starts):
 level blocks exist with all five columns of generic type (three independent-ish forms, rank 2) and with all five columns diagonal
 (rank 1) -- the latter all have class structure (4,1), i.e. a unit vector in P (consistent with Lemma N2-GEN). So without zero-free
 column annihilators the block alone does not give a contradiction; N2 must be attacked with more of its structure (L_a, L_b).
 Session was interrupted once at ~17:26 (server restart); resumed.
STATUS 17:49: three results so far this round (sections R4-1..R4-3 below): the dictionary "zeros / single-row elements / defects" for
 REG1, the general normal form of the N2 block, and LEMMA N2-Z (moment problem with zero weights). Pattern survey for two-row columns running.

## R4-1. REG1 dictionary: what a zero of an annihilator and what a single-row element mean  [rigorous; mostly re-readings of chief RP6/RP9,
##       stage3 GZ/SR/SC and rows' defect construction, collected because they are the replacement for the tau-coordinates]
 REG1: dim L = 9, all a_r = b_c = 1; kappa^r, kappa'^c the unique FK annihilators (sum = 1). L_r := L cap {row r = 0} (dim 5).
 (Z1) kappa^r_j = 0  <=>  e_j in pi_r(L)  <=>  the 1x4 block {r} x ([5]-j) is ell-supporting. Then V_rj := {t in L : t_r in C e_j} has
      dim 6, and perm_4(t^(rj)) = 0 on V_rj (GZ-b; chief RP6 with v = e_j). If kappa^r_j != 0, V_rj is replaced by the 6-dim space
      {u in L^ : u_r in C e_j}, on which perm_4(u^(rj)) = 120 (kappa^r_j)^5 u_rj^4. Same for columns with kappa'.
      So the tau-coordinates tau_r(j) = kappa^r_j u_rj survive on supp(kappa^r); the columns j outside supp(kappa^r) are "free" coordinates of
      row r (ell does not see them), each carrying a 6-dim linear subspace of L with a vanishing 4x4 subpermanent.
 (Z2) (chief RP9) all five 4x4 subpermanents vanish identically on L_r (as 4x5 matrices), for every r; dually on every L^c.
 (Z3) SINGLE-ROW ELEMENTS = DEFECT (valid in every level space, every row): Z_r := {w : e_r w^T in L} lies in (C(L_r) + C 1)^perp, where
      C(L_r) is rows' defect space of the 4x5 level space L_r. [Lineality of e_r w^T on CJ + L_r: <w, G(cJ' + xi)> = 0, and
      G(cJ' + xi) = sum_k c^(4-k) (4-k)! p_k(xi).]  Hence z_r <= 4 - e(L_r), and L_r (+) e_r (x) Z_r is a level space with deletable row r.
      In REG1: dim L_r = 5, so e(L_r) >= 1 (zeros' Lemma SL: e = 0 forces dim <= 3) and z_r <= 3. z_r = 3 forces L_r to be a (5,1) space
      (an 8-dim level space with a deletable row would exist inside L): excluded by verifyfl's TC5 when the defect line is C(e_j - e_l),
      i.e. when Z_r = {w : sum w = 0, w_j = w_l}; excluded in general only by rows' open conjecture (DI_5).
      rows' Corollary H applied to L' = L_r: z_i <= e(L_r) and m_ij <= e(L_r) + 1 for all rows i, j != r. So
            max_{i != r} z_i  <=  e(L_r)  <=  4 - z_r      and      m_ij <= 5 - z_r   ({i,j} not containing r).
 (Z4) (stage3 SR/SC) e_a w^T in L, w_j != 0 => kappa'^j_a = 0; y e_j^T in L, y_a != 0 => kappa^a_j = 0.
 Census (stage2/r4_census.py): none of the known example spaces is in REG1 (every 7-dim example has several lines with a >= 2).

## R4-2. The N2 block without zero-freeness  [normal form rigorous; existence statements numerical]
 In stage3's family N2 (lam_ab = 4, m_cd = m_ce = m_de = 2, no single-row element) there are a 2-dim space P and injective maps
 psi_c, psi_d, psi_e : P -> C^5 with      X_ab = {(psi_c(p_c); psi_d(p_d); psi_e(p_e)) : p_i in P, p_c + p_d + p_e = 0}
 (Y_cd = graph on p_e = 0, etc.; the three rows play symmetric roles). Column j of X_ab is given by three linear forms
 (al_j, be_j, ga_j) on P. The column annihilator gives K'_cj al_j = K'_dj be_j = K'_ej ga_j, so every column is of one of the types
   D : three nonzero PROPORTIONAL forms (then (K'_cj,K'_dj,K'_ej) is zero-free or 0),
   0 : the column vanishes on X_ab,
   S : the column is supported on rows where kappa'^j vanishes (one row: S1; two rows: S2; three rows: S3),
 and a column whose three entries are independent functionals on X_ab forces kappa'^j in span(e_a, e_b).
 Level conditions in general: the three row-sum forms coincide (= sigma); <psi_i(p),psi_k(p)> = sigma(p)^2 for the three pairs, the
 alternating parts w_ik of <psi_i(p),psi_k(p')> - sigma(p)sigma(p') satisfy w_cd = w_ce - w_de; and P_3.
 Numerics (stage2/r4_block.py, r4_inspect.py, r4_inspect3.py; 14 starts): level blocks exist
   - with all five columns generic (three pairwise independent forms; 7 hits): no sparse element, every column projection 3-dim.
     In REG1 this forces all five kappa'^j into span(e_a,e_b); since dim A_ab = 1 + lam_ab = 5 these five relations span all relations on
     rows a,b, and then kappa^a = e_{j_a}, kappa^b = e_{j_b}: TWO IDENTICALLY VANISHING CELLS (a,j_a), (b,j_b) [rigorous deduction];
   - with all five columns of type D (5 hits): always the unit-vector configuration (alpha1) below.
 So, unlike in GEN, the block alone does not give a contradiction. Necessary conditions on M = L_a + L_b (level + (Z2) on L_a, L_b;
 stage2/r4_N2full.py, r4_N2inj.py, r4_N2fast.py): LM mostly runs into non-injective psi (not N2); one genuine solution found, with a
 3-dim space of single-column elements in one column (a "split free column"). Too few runs to conclude anything.

## R4-3. LEMMA N2-Z: the moment problem with zero weights  [hand proof; both families checked by direct permanent evaluation,
##       stage2/r4_alpha2.py: defects 2e-13 and 9e-14, control 99]
 DIAGONAL MODEL: no column of X_ab carries two independent forms, i.e. t_ij = g_ij lam_j(p_i) with a weight matrix g in C^{3x5}
 (zeros allowed; in the normalisation g_c = 1 of Lemma N2-GEN a zero weight is a weight 0 or infinity). Level conditions:
   (i) sum_{j: g_ij != 0} g_ij lam_j = sigma (i = c,d,e);   (ii) sum_j g_ij g_kj lam_j^2 = sigma^2 (three pairs);   (iii) sum_j g_cj g_dj g_ej lam_j^3 = sigma^3.
 A column with one nonzero weight (S1) enters only one equation of (i); a column with two nonzero weights enters two equations of (i)
 and one of (ii); only the FULL columns (three nonzero weights; set D, n = |D|) enter (iii).
 LEMMA N2-Z. Suppose every column has 3, 1 or 0 nonzero weights (in REG1: every kappa'^j has at most one zero among the rows c,d,e, or
 the column vanishes on X_ab) and psi_c, psi_d, psi_e are injective. Then, up to permuting rows and columns, X_ab is one of
   (alpha1) five full columns: one column j_1 with entries (sigma(p_c), sigma(p_d), sigma(p_e)), and four columns t with entries
            X_i(t) mu(p_i), where sigma, mu are independent forms and X_c, X_d, X_e in (C^*)^4 are orthogonal to 1, pairwise orthogonal
            (bilinear dot product) and sum_t X_c X_d X_e = 0;                         [= the unit-vector case of Lemma N2-GEN]
   (alpha2) four full columns and one single-row column: column j_1 as above, three columns (x mu(p_c), u_t mu(p_d), v_t mu(p_e)) with
            u, v in 1^perp (in C^3) zero-free and orthogonal, and a fifth column (-3x mu(p_c), 0, 0).
 In both cases X_ab CONTAINS THE TWO DOMINOES (e_c - e_d) e_{j_1}^T, (e_c - e_e) e_{j_1}^T (take p_i in ker mu); hence (SC)
 kappa^c_{j_1} = kappa^d_{j_1} = kappa^e_{j_1} = 0, and K'_{c j_1} = K'_{d j_1} = K'_{e j_1}.
 Proof. Classes of proportional forms among the full columns: mu_1, .., mu_k, lam_j = n_j mu_m; class sums A_m of g_c g_d g_e n^3 and
 B_m^{ik} of g_i g_k n^2. (iii): sum A_m mu_m^3 = sigma^3; (ii): sum B_m^{ik} mu_m^2 = sigma^2. Cubes (squares) of <= 4 (<= 3) pairwise
 non-proportional binary forms are independent.
  A. k >= 2. [k = 0: sigma = 0 and each row needs >= 3 single-row columns with forms summing to 0. k = 1: sigma in C mu_1 and each row
     needs >= 2 single-row columns whose forms sum into C mu_1. Both need more than 5 columns.]
  B. sigma != 0. [sigma = 0, k <= 4: all A_m = 0, so no singleton class: k = 2, then all B_m = 0, and a class {1,2} of size 2 has
     x_i x_k = -y_i y_k for the three pairs and x_c x_d x_e = -y_c y_d y_e (x_i = g_i1 n_1, y_i = g_i2 n_2): the product of the first three
     gives (x_c x_d x_e)^2 = -(y_c y_d y_e)^2, the last gives +: contradiction. sigma = 0, k = 5: five distinct points, case of N2-GEN.]
  C. sigma not proportional to any mu_m: then k >= 4. (n,k) = (5,4), (5,5): Lemma N2-GEN, cases (2,1,1,1) and (1,1,1,1,1).
     (n,k) = (4,4) [fifth column single-row or zero]: with nu in ker sigma, zeta_j = eta_j/nu_j on the four full columns (distinct),
     tau = sigma(eta) != 0: W_j = tau^3 om_j, c_j nu_j^2 = om_j(al_c + tau^2 zeta_j) for c = a, b, ab (the fifth column does not enter
     (ii), (iii)); (a nu^2)(b nu^2) = W nu and nu = W/(ab nu^2) give (al_a + tau^2 z)(al_b + tau^2 z)(al + tau^2 z) = tau^6 F'(z) at the
     four points: the difference is a cubic with leading coefficient tau^6 - 4 tau^6 != 0 and four roots. Contradiction.
  D. sigma = mu_1 (normalised). k <= 4, so A_1 = 1, A_m = 0 (m >= 2): the other classes have size >= 2, so k <= 3 and squares are
     independent: B_1 = 1, B_m = 0; a class of size 2 with A = B = 0 is impossible (as in B), so k = 2 with sizes (1,3), (1,4), (2,3).
     [k = 5 with sigma = mu_1 is the case |S| = 4, (1,1,1,1) of N2-GEN.]
     Class 1 = {j_1}: x_c x_d = x_c x_e = x_d x_e = x_c x_d x_e = 1 gives x = (1,1,1). Class 1 of size 2 (n = 5): the computation of
     N2-GEN, case |S| = 3, gives A_4 A_5 = 0. So class 1 is one column with entries sigma(p_i), and class 2 consists of 3 or 4 columns
     X_i(t) mu(p_i) with X_i pairwise orthogonal and sum X_c X_d X_e = 0; (i) says X_i is orthogonal to 1 for every row without
     single-row column. Size 4: (alpha1). Size 3: if the fifth column is zero, X_c, X_d, X_e are three pairwise orthogonal vectors of
     the nondegenerate plane 1^perp in C^3, hence all proportional to one isotropic vector n = (1,w,w^2), and sum X_c X_d X_e =
     3 x_c x_d x_e != 0; if the fifth column lives in row c: X_d, X_e in 1^perp, X_c orthogonal to both, and the triple sum forces
     X_c = x 1 (also when X_d, X_e are proportional and isotropic); (i) for row c gives the form -3x mu: (alpha2).              QED
 Calibration of the numerical pattern search (stage2/r4_patterns.py, 20 starts per pattern): pattern "four full + one single-row column":
 4 hits, all with a 2-dim domino space in one column; "five full": 6 hits, all (alpha1); "four full + zero column": 0 hits;
 "four full + one two-row column": 0 hits.
 COROLLARY (N2 in REG1, sub-regime "at most one zero of each kappa'^j among the rows c,d,e" [covers GEN_c := column annihilators
 zero-free, row annihilators arbitrary]): the block X_ab is (alpha1) or (alpha2); L contains two dominoes of one column j, and the row
 annihilators of c, d, e all vanish at j. In particular with zero-free ROW annihilators at (c,j), (d,j) or (e,j) N2 is impossible.
STATUS 17:58: pattern survey for two-row columns finished (4 batches); N2 inside the family (alpha) analysed by hand; explicit M* found.

## R4-4. N2 with a block of type (alpha): killed for (alpha1), (alpha2) by hand; ONE survivor (alpha3) = explicit 6-dim level space M*
 FAMILY (alpha) (contains (alpha1), (alpha2)): one column j_1 with entries sigma(p_i), four columns t with entries X_i(t) mu(p_i);
 Xi := [X_c; X_d; X_e] (3x4, rows nonzero, zeros allowed) with X_i orthogonal to 1, pairwise orthogonal, sum_t X_c X_d X_e = 0.
 Every such block is level and contains the two dominoes of column j_1.
 In N2: L_a = {(s rho_b; psi_c(p_c); psi_d(p_d); psi_e(p_e)) : sum p_i = s om} (dim 5), rho_b = rho_1 e_{j_1} + rho' != 0, and all
 4x4 subpermanents of these 4x5 matrices vanish ((Z2), a_a = 1). With p_i = y_i q_sigma + s_i q_mu (row i = y_i e_{j_1} + s_i X_i):
   deleting column j_1:  s s_c s_d s_e perm_4[rho'; X_c; X_d; X_e] = 0                                              => (E0)
   deleting a mu-column t, Laplace along column j_1, coefficients of y_c, y_d and the rest:
        perm_3[rho'; X_i; X_k] restricted to [4]-t vanishes for the three pairs and all t                           => (E1)
        rho_1 perm_3[X_c; X_d; X_e] restricted to [4]-t vanishes for all t                                          => (E2)
 Inclusion-exclusion with zero row sums and orthogonal rows:
        perm_3(Xi without column t) = -6 X_c(t) X_d(t) X_e(t),
        perm_3([rho';X_i;X_k] without column t) = (2r - 6 rho'_t) X_i(t) X_k(t) + h_k X_i(t) + h_i X_k(t) + 2 tau_ik,
   r = sum rho', h_i = <rho',X_i>, tau_ik = sum_t rho'_t X_i(t) X_k(t); summing (E1) over t gives tau_ik = 0.
 CASE A (rho_1 != 0): every column of Xi contains a zero. Impossible for (alpha1) (Xi zero-free) and for (alpha2) (three zero-free columns).
 CASE B (rho_1 = 0, rho' != 0):
   (alpha1): dividing (E1) by X_i(t) X_k(t): h_i/X_i(t) = 3 rho'_t - r for all i, t. Some h_i = 0 gives rho' = (r/3) 1, r = 4r/3, rho' = 0.
     All h_i != 0: X_i = h_i xi with xi = 1/(3 rho' - r 1), so the power sums p_1 = p_2 = p_3 of xi vanish, xi_t are the four roots of
     z^4 = const, sum 1/xi = 0, and <rho',xi> = (4 + r sum xi)/3 = 4/3, but h_i = h_i <rho',xi> needs 1. Contradiction.
   (alpha2) (X_c = x(1,1,1,-3), X_d = (u,0), X_e = (v,0)): (E1) at t = 4 gives h_d = h_e = 0; then at t <= 3 for the pair (d,e):
     rho'_t = r/3, and for (c,d): h_c = 0, i.e. rho'_4 = r/3; so rho' = (r/3) 1 = 0. Contradiction.
 THEOREM N2-Z' [rigorous by hand, given Lemma N2-GEN and Lemma N2-Z]. In stage3's family N2 the block X_ab is neither (alpha1) nor
 (alpha2). Hence N2 IS IMPOSSIBLE WHENEVER EVERY COLUMN HAS AN FK ANNIHILATOR WITH AT MOST ONE ZERO AMONG THE ROWS c, d, e -- in
 particular whenever all column annihilators are zero-free, with NO hypothesis on the row annihilators (this removes the hypothesis
 "no single-column element" of Lemma N2-GEN).
 COROLLARY. all a_r = 1, lam >= 3 for all row pairs, and every column has an FK annihilator with at most one zero entry  =>  L contains
 a single-row element e_a w^T (stage3 sec. 16 + N2-Z'; conditional on stage3's Theorem N1), and then (SR) row a is the zero of >= 2
 column annihilators.
 TWO-ROW COLUMNS (weights with two nonzero entries; kappa'^j with two zeros among c,d,e) [numerical]:
   - pattern survey stage2/r4_patterns.py: all 75 support patterns with a two-row column, 12 starts each (hit rate about 20-30% per start
     on patterns with known solutions): level blocks with injective psi found only for the patterns 011 011 111 111 111 and
     011 011 101 101 111 (rows c,d,e top to bottom, up to permutation), both in family (alpha) (2-dim domino space in the full column).
   - inside family (alpha) with zeros (stage2/r4_alphaN2.py, 60 starts each): CASE A has solutions, all of one shape
        (alpha3)  X_i = al (1,0,0,-1),  X_k = be (1,-1,-1,1),  X_l = ga (0,1,-1,0)      (one zero in every column of Xi);
     CASE B has none (0/60). For (alpha3), (E1) forces rho' = 0 (hand computation), so rho_a, rho_b are multiples of e_{j_1}.
 THE SURVIVOR M* [EXACT integer check, stage2/r4_Mstar.py: perm(J + m) = 120 at 400 random integer points of the 6-dim space, (Z2) on
 L_a and L_b at 200 points each, 0 violations]: with j_1 = 0, rows a..e = 0..4,
     M* = span{ -E_a0 + (e_0 + m_a al(e_1 - e_4)) in row c,   -E_b0 + (e_0 + m_b al(e_1 - e_4)) in row c,   (e_c - e_d)e_0^T,   (e_c - e_e)e_0^T,
                (al(e_1-e_4) ; -be(e_1-e_2-e_3+e_4)) on rows (c;d),    (al(e_1-e_4) ; -ga(e_2-e_3)) on rows (c;e) }
 is a 6-dim LEVEL space of exactly the N2 shape for L_a + L_b (lam_ab = 4, no single-row element, rows a, b supported in column 0).
 So N2 cannot be excluded from L_a + L_b alone. M* contains a 3-dim space of single-column elements of column 0
 ({y e_0^T : sum y = 0, m_a y_a + m_b y_b = 0}): a SPLIT FREE COLUMN. In a 9-dim L with b_0 = 1 this gives z'^0 = 3 and, by (Z3)
 transposed, L^0 is a (5,1) space with defect line (Z'^0 + C1)^perp: an 8-dim level space with a deletable column would exist.
 (The numerical solution found earlier by r4_N2inj.py is of this type.)
 Direct confirmation of the derivation (Z2) => (E0),(E1),(E2) (stage2/r4_alphaLa.py: the original condition "all 4x4 subpermanents
 vanish on L_a" evaluated at random points, family (alpha) with Xi, rho_b, om free; 40 starts): 10 solutions, ALL with one zero in every
 column of Xi, rho' = 0, rho_1 != 0 (= (alpha3)); 30 starts do not converge. So inside family (alpha), N2 means M*.

## R4-5. State of REG1 (all a_r = b_c = 1, dim 9) after round 4, and the precise list of surviving configurations
 The theorem "no 9-dim level space in REG1" is NOT proved. What is proved / reduced (zero-freeness no longer needed where stated):
  (1) [conditional as before: R3-1 num-assisted, stage3's N1] all annihilators zero-free: impossible (Theorem GEN).
  (2) [rigorous given N2-GEN, N2-Z; + stage3 sec. 16] all a_r = 1, lam >= 3 for all row pairs, every column annihilator with at most one
      zero: L contains a single-row element. (Transposed statement for columns.) So zero-free COLUMN annihilators + lam >= 3 on the row
      side is contradictory without any hypothesis on the row annihilators (no single-row element by SR).
  (3) [rigorous] a single-row element is a defect phenomenon: z_r <= 4 - e(L_r), z_r <= 3, and z_r = 3 => an 8-dim level space with a
      deletable row and a (5,1) space L_r exist (rows' open (DI_5) at e = 1; TC5 excludes the two-column defect lines).
  (4) [rigorous + numerical for two-row columns] N2 with a "diagonal" block (no column of X_ab carries two independent forms) forces
      L_a + L_b = M* (explicit), hence a split free column, hence again a (5,1) space.
 SURVIVING CONFIGURATIONS in REG1 (each also in transposed form):
  (S-I)   a MINIMAL PAIR (lam = 2) in which at least one annihilator of the pair, or one of the column annihilators used by GEN-2,
          has a zero. Known: one zero in one annihilator of the pair => Type I_0 (round 2). Not classified beyond that; the tool is
          criterion (G) (Gamma_T), which allows zeros.
  (S-II)  all row lam >= 3 and a SINGLE-ROW ELEMENT e_a w^T (this is what stage3's N1 produces): then z_a <= 3, every column in supp(w)
          has kappa'^j_a = 0, e(L_i) >= z_a for the other rows i, e(L_a) <= 4 - z_a. Sub-case z_a = 3: the (5,1) problem.
          Sub-cases z_a = 1, 2: L_a is a (5,e) space with e <= 3, 2 -- such 4x5 spaces exist ((5,2) occurs in the 7-dim examples), so
          defect theory alone does not exclude them; what is missing is a use of the other four rows having 4-dim projections.
  (S-III) all row lam >= 3, no single-row element: family N2 with
          (a) block (alpha3) / M*: contains a split free column (so it is (S-II) transposed with z' = 3: the (5,1) problem);
          (b) a NON-DIAGONAL block: some column of X_ab carries two independent forms, so that kappa'^j has >= 2 zeros among c,d,e; in
              the extreme case of five generic columns: all kappa'^j in span(e_a,e_b) and two identically vanishing cells (a,j_a), (b,j_b).
              Level blocks of this kind exist (numerically); not analysed further.
 THE COMMON CORE: every surviving configuration I can make explicit contains a partially free line (split free column in M*; the
 dominoes of (alpha1)/(alpha2)), i.e. lives in rows'/verifyfl's defect regime "(5,e) spaces with e <= 3"; the sharpest single open
 statement is: NO (5,1) SPACE (rows' (DI_5) at e = 1), which kills z = 3 and N2 with a diagonal block.
 NOT DONE: classification of minimal pairs with zeros (S-I); N2 with non-diagonal blocks (S-III b); (S-II) with z = 1, 2; a hand proof
 that Case B has no solution for Xi with zeros (numerical 0/60 and 0/40 only); exhaustive pattern survey with more starts.
 Runs to report (round 4): r4_block.py first run (60 starts) hit its 150 s timeout without output (1m28 CPU), rerun with 14 starts 22 s;
 r4_N2inj.py: one run interrupted by the session restart, one hit its 100 s timeout after 2 starts; r4_N2fast.py hit a 110 s timeout
 (1m40 CPU) with one start; r4_alphaN2.py (60 s) was started while batch 2 of r4_patterns.py was still running (two processes at once
 for about a minute -- against the one-run-at-a-time habit); the four r4_patterns.py batches took 100-125 s each.
STATUS 18:00: RESULT-R4 at the top; R4-5 written. Final report follows.

## R4-6. First-order extension test; M* lies in no 9-dim level space  [exact at one parameter set + numerical scan]
 For a linear subspace M of a level space L and t in L, m in M: perm(J + m + eps t) = 120, so sum_ij t_ij perm_4((J+m)^(ij)) = 0.
 Hence L lies in T_1(M) := annihilator of the span of the cofactor matrices C(J + m), m in M; and dim L <= dim T_1(M).
 (rows used the same space for the 7-dim examples.)
 M* (parameters m_a, m_b, al, be, ga; stage2/r4_Mstar_ext.py, r4_Mstar_scan.py): the cofactor matrices span a 17-dim space
   - exactly (rational arithmetic, 40 integer points) for (m_a,m_b,al,be,ga) = (1,2,1,1,1);
   - in floating point (relative 17th singular value >= 1e-3, 18th = 0) for 300 random integer parameter sets, 100 random complex ones
     and the special loci m_a = m_b, m_a = -m_b, m_a = 0, m_a = m_b = 0, sign changes of al, be, ga.
 So dim T_1(M*) = 8 and M* lies in no 9-dim level space. Consequence for REG1 (and for any 9-dim level space with all a_r = 1):
 family N2 with a DIAGONAL block is impossible  [chain: Lemma N2-Z (hand) / pattern survey for two-row columns (numerical) =>
 family (alpha); (Z2) on L_a => (alpha3) and rho' = 0 (hand for (alpha1), (alpha2); numerical for Xi with zeros) => M* => T_1].
 Remark: the test gives nothing on the 4-dim blocks alone (stage2/r4_T1.py: dim T_1(X_ab) = 11 for 8 generic blocks, 13 for 5 blocks of
 family (alpha)); it needs the 6-dim L_a + L_b.
 Updated survivor (S-III): only (b), N2 with a non-diagonal block, remains.
STATUS 18:04: R4-6 added; RESULT-R4 updated. Final report follows.
 Sanity of the test (stage2/r4_T1_sanity.py): for the 7 known example spaces and for random subspaces M of them, L lies in T_1(M)
 (pairings <= 6e-12) and dim T_1(L) = 8 for every 7-dim example (rows' "first-order extension space").
STATUS 18:04: sanity check of (FO) added. [R4-5's item (S-III)(a) is superseded by R4-6: M* is excluded at dim 9.] Round-4 final report sent.

# ROUND 5 (start 18:06, budget 90 min -> ends ~19:36). Targets: (1) (FO) for M* as a theorem for all parameters + hand proofs for the
# numerical parts of round 4; (2) FO on the survivors (S-III b), (S-I); (3) what remains in REG1, and what survives when some a_r >= 2.
STATUS 18:08: round-4 handback was not sent (the round-5 message arrived first); the round-4 results are in RESULT-R4 and R4-1..R4-6.
 Key observation for (1): M* is a hyperplane of the 7-dim level space W_7 = {full free column 0} (+) {(a_c X_c; a_d X_d; a_e X_e)}
 (X_c = e_1 - e_4, X_d = e_1 - e_2 - e_3 + e_4, X_e = e_2 - e_3 on rows c, d, e), a "free column + strongly level 3-dim" space;
 M* = W_7 cap {a_c/al + a_d/be + a_e/ga + m_a y_a + m_b y_b = 0}.
STATUS 18:12: (1) done for M* (theorem, exact certificate) and for Cases A/B of family (alpha) (hand proofs). Lemma N2-Z corroborated
 (stage2/r4_patterns.py, the 16 patterns with 3/1/0-weight columns, 22 starts each: solutions only for "five full" (5 hits) and "four full
 + one single-row column" (8 hits), all with the 2-dim domino space).

## R5-1. THEOREM FO-M*: dim T_1(M*) = 8 for ALL parameters  [structural proof + exact parameter-free certificate, stage2/r5_FO_Mstar.py]
 W := {t : column 0 = y in C^5; row c = y_c e_0 + a_c X_c, row d = y_d e_0 + a_d X_d, row e = y_e e_0 + a_e X_e; rows a,b in C e_0}
 (X_c = e_1 - e_4, X_d = e_1 - e_2 - e_3 + e_4, X_e = e_2 - e_3; coordinates (y,a) in C^5 x C^3), W_7 := W cap {sum y = 0}.
 (a) perm(J + w) = 120 + 24 sum y on W, so W_7 is a 7-dim level space (full free column 0 + a 3-dim strongly level part), and
     M* = W_7 cap ker(phi), phi = a_c/al + a_d/be + a_e/ga + m_a y_a + m_b y_b  (checked on the basis of M*).
 (b) For t in C^{5x5} and w = (y,a):  <C(J+w), t> = 24 tau_0 + sum_k (1 + y_k) Q_k^t(a),  tau_0 = sum_i t_i0,
     Q_k^t(a) = sum_{i != k} sum_{j=1..4} t_ij perm_3(N without rows i,k and column j), N = the 5x4 matrix of the columns 1..4 of J + w.
     Exact facts (rational polynomial arithmetic): (s1) all perm_4(N without row i) = 24; (s2) every Q_k is multilinear in (a_c,a_d,a_e)
     and Q_c, Q_d, Q_e do not involve a_c, a_d, a_e respectively (obvious from the definition); (s3) T_1(W_7) = {t : Q_k^t = -(24/5) tau_0 for
     all k} has dimension 8 (rank 17), = W_7 (+) C(1 e_0^T - J/5).
 (c) m := (m_a,m_b) != 0. On M*, for fixed a the vector y runs over an affine space with direction 1^perp cap m^perp; so t in T_1(M*) iff
     Q_k(a) = q(a) + m_k p(a) (k = a,b; m_k = 0 for k = c,d,e) and 24 tau_0 + 5q + (m_a + m_b - <mu^,a>) p = 0, mu^ = (1/al,1/be,1/ga).
     q = Q_c = Q_d = Q_e does not depend on a_c, a_d, a_e: q is constant. Then (m_a + m_b - <mu^,a>) p(a) is constant, so p = 0
     (mu^ != 0), and t lies in T_1(W_7).
 (d) m = 0. M* = 1^perp x {<mu^,a> = 0}: t in T_1(M*) iff all Q_k are equal to -(24/5) tau_0 on the plane <mu^,a> = 0. Q_c, Q_d, Q_e are
     functions of two variables and the plane projects onto each coordinate plane (mu^ zero-free): they are constant. Q_a, Q_b are
     multilinear and constant on the plane: Q - const = R <mu^,a> with R constant (degree 1 in each variable, mu^ zero-free).
     Exact (s4): on T' := {t : all conditions of (s3) except the linear coefficients of Q_a, Q_b} (dim 10) the linear parts of Q_a and
     Q_b are multiples of (0,1,0) (the a_d-direction) only; R mu^ = x(0,1,0) with mu^ zero-free forces R = 0. So t lies in T_1(W_7).
 THEOREM FO-M*. For all m_a, m_b in C and al, be, ga in C^*: T_1(M*) = T_1(W_7) = W_7 (+) C(1 e_0^T - J/5), of dimension 8.
 Hence every level space containing M* has dimension <= 8.                                                                    QED

## R5-2. Hand proofs for the numerical parts of R4-4 inside family (alpha)  [rigorous]
 Family (alpha): Xi = [X_c;X_d;X_e] 3x4, rows nonzero, orthogonal to 1, pairwise orthogonal, sum_t X_c X_d X_e = 0. Xi has no zero column
 (three nonzero pairwise orthogonal vectors of the nondegenerate plane 1^perp in C^3 are multiples of one isotropic n = (1,w,w^2), and
 then the triple sum is 3 x_c x_d x_e != 0).
 CASE A (every column of Xi has a zero) => Xi = Xi* := (al(e_p - e_q); be(1_{pq} - 1_{rs}); ga(e_r - e_s)) up to permutations.
   Supports S_i: |S_i| >= 2 (zero sum); |S_i cap S_k| != 1 (orthogonality); S_c cap S_d cap S_e empty. A row with full support forces the
   other two supports to be disjoint, hence complementary pairs, and the shape Xi*. Without a full row: (3,3,3) and (3,3,2): the
   2-set (or third 3-set) meets the triple intersection; (3,2,2): the two 2-sets lie in the 3-set, meet in 1 point or coincide;
   (2,2,2): two supports coincide and then X_i.X_k = 2 kappa kappa' != 0. All impossible.
   For Xi*: (E1) gives h_c = h_e = 0 (zeros of X_c, X_e against X_d), rho'_p = rho'_q, rho'_r = rho'_s, and the two remaining equations
   give rho' = 0 (R4-4).
 CASE B (rho_1 = 0, rho' != 0) IS IMPOSSIBLE for every Xi of the family. (E1) at a column t reads
       (2r - 6 rho'_t) X_i(t) X_k(t) + h_k X_i(t) + h_i X_k(t) = 0   (three pairs),  and tau_ik = 0.
   Consequences per column: three nonzero entries: h_i = (3 rho'_t - r) X_i(t) for all i; exactly X_l(t) = 0: h_l = 0 and
   h_i/X_i(t) + h_k/X_k(t) = 6 rho'_t - 2r; only X_i(t) != 0: h_k = h_l = 0.
   - all h = 0: rho'_t = r/3 on every column with >= 2 nonzero entries; for a column whose only nonzero entry is X_i(t): h_i = 0 reads
     sum over such columns of (rho'_t - r/3) X_i(t) = 0. A row cannot own two such columns (the other two rows would live on the two
     remaining columns and be proportional, not orthogonal), so rho' = (r/3) 1, r = 4r/3, rho' = 0.
   - h_c != 0: X_c is zero-free (a zero of X_c under a nonzero entry of another row gives h_c = 0; zero columns do not exist).
     All three h != 0: Xi zero-free, contradiction 4/3 = 1 (R4-4). h_c, h_d != 0 = h_e: a column with X_e(t) != 0 has three nonzero
     entries and h_e = 0 gives 3 rho'_t = r, hence h_c = 0; so X_e = 0. Contradiction. h_c != 0 = h_d = h_e: no column has three
     nonzero entries, so supp X_d, supp X_e are complementary pairs and Xi = Xi* with full row c; rho'_t = r/3 + h_c/(6 X_c(t)) for all t;
     summing: r = 0; then h_c = <rho',X_c> = (4/6) h_c, so h_c = 0. Contradiction.
 RESULT: inside family (alpha), N2 forces Xi = Xi* and rho_a, rho_b in C e_{j_1}, i.e. L_a + L_b = M*  -- now a HAND proof; with
 Theorem FO-M*: family (alpha) is excluded at dimension 9 for all parameters, rigorously (given Lemma N2-GEN / N2-Z for the reduction
 to family (alpha) when all columns have 3, 1 or 0 nonzero weights).
 STILL NUMERICAL: that every diagonal block with a TWO-ROW column lies in family (alpha) (pattern survey of R4-4). Caveat found now:
 for the pattern "four full columns + one two-row column" a parameter count gives 7 equations in 7 unknowns, so ISOLATED solutions
 are not excluded by a search with 12-20 starts. This part is therefore weaker than I stated in R4-4.
STATUS 18:28: session was cut off at ~18:15 (usage limit) and resumed 18:20 with 75 more minutes. New inputs read: stage3's Theorem N2-X
 (N2 does not occur; hence Theorem N: all a_r = 1, lam >= 3 => single-row element; not yet verified), Lemma S3-1 (z_i <= 2 under (H1)),
 verifyfl's SPLIT / FS / HYP. Consequence for my list: (S-III) is settled by stage3 if N2-X is verified; my results on N2 (N2-GEN, N2-Z,
 N2-Z', FO-M*) are an independent confirmation on the diagonal sub-families and no longer needed for the chain.

## R5-3. Consistency of M* with stage3's N2-X, and the kernel condition  [rigorous derivation; small numerics]
 M* is a 6-dim level space of N2 shape for L_a + L_b; N2-X says N2 does not occur in a 9-dim L with all a_r = 1. No conflict: in M* the
 planes P_c, P_d, P_e meet in the unit vector e_0 (stage3's case (alpha), sub-case v_0 = e_j), which stage3 excludes with conditions
 coming from L_c, L_d, L_e; and by Theorem FO-M* no 9-dim level space contains M*. The two exclusions are independent.
 KERNEL CONDITION (valid for every N2 block, diagonal or not): for x in X_ab let C(x) be the symmetric zero-diagonal 5x5 matrix
 C(x)_{jl} = perm_3(x[cde; [5]-{j,l}]). (Z2) on L_a at first order in the row-b parameter gives C(x) rho_b = 0 for all x in X_ab, and
 likewise C(x) rho_a = 0: the matrices C(x) have a common kernel vector. [(E1),(E2) of R4-4 are this condition in family (alpha).]
 Numerics (stage2/r5_kernel.py part 1): for 7 level blocks found by plain LM (4 generic non-diagonal, 3 of type (alpha1)) the common
 kernel is 0, so none of them is an N2 block. Part 2 (search for level blocks WITH a kernel vector) hit its 115 s timeout without
 output and was not repeated after N2-X arrived.

## R5-4. The first-order extension test for a row: general formulas  [rigorous; valid for every row of every level space]
 With perm(u) = <u_r, G(u')> (G = vector of the five 4x4 subpermanents of the other four rows) and t = (t_r; t'):
       D_t perm(u) = <t_r, G(u')> + <u_r, D_{t'} G(u')>.
 (a) X = L_r (row r = 0):  T_1(L_r) = {t : <t_r, G(J'+xi)> + D_{t'} N(J'+xi) = 0 for all xi in L_r},  N = sum_j G_j the 4x5 level function.
     It contains L_r (+) e_r (x) (C(L_r) + C1)^perp, of dimension dim L_r + 4 - e(L_r).
 (b) M_r := L_r (+) e_r (x) Z_r (always inside L; a level space with deletable row r):
       T_1(M_r) = {t : D_{t'} G(Y) in Z_r^perp and <t_r, G(Y)> + <1, D_{t'} G(Y)> = 0 for all Y in J' + L_r};
     it always contains M_r (+) C(e_r 1^T - J/5)  [D_{J'} G(Y) = 4 G(Y) - D_xi G(Y), D_xi G(Y) in C(L_r), <1,G> = 120], so
     dim T_1(M_r) >= dim L_r + z_r + 1, and L inside T_1(M_r) needs  dim L <= dim T_1(M_r).
     If z_r = 4 - e(L_r) (the free part is as large as L_r allows; e.g. z_r = 2 with L_r a (5,2) space) then dim M_r = dim L_r + 4 - e, and a
     9-dim L needs at least 9 - dim M_r - 1 first-order deformations t' of L_r, modulo L_r + C J', with D_{t'} G(J' + xi) in C(L_r) + C1
     for all xi ("first-order deformations preserving the defect space"). rows found dim T_1 = 8 for all 27 known 7-dim level spaces
     with a deletable line (types (3,0), (4,1), (5,2), (6,3)): these L' are rigid, so none of them is the L_r of a 9-dim level space with
     the full free part; in particular stage3's case z_i = 2 with L_i a (5,2) space of a known type is excluded.
 (c) Nothing here uses a_r = 1: the test applies verbatim to rows with a_r >= 2 (then dim L_r = 4 + a_r <= 7 by the checked L_gct_215,
     so a_r <= 3 in every 9-dim level space).
STATUS 18:37: second-order test (FO2) found, sanity-tested and applied; candidates for L_r surveyed. Writing up.

## R5-5. The second-order extension test (FO2)  [lemma rigorous (two lines); applications numerical; stage2/r5_FO2.py, r5_FO2_apply.py]
 LEMMA FO2. Let M be a linear subspace of a level space L. For m in M put q_m(t,t') := D_t D_t' perm(J + m) (the symmetric bilinear form
 with entries perm_3((J+m) without rows i,k and columns j,l)). Then L lies in T_1(M) and L is totally isotropic for every q_m, m in M
 (and for all their linear combinations). Hence
        dim L  <=  dim T_1(M) - ceil( rank(q restricted to T_1(M)) / 2 )        for every q in span{q_m : m in M}.
 Proof: perm(J + m + eps t) = 120 for t in L, m in M; the eps- and eps^2-coefficients vanish; polarise on the linear space L.   QED
 SANITY (bug caught here: my first version used the hermitian instead of the bilinear restriction and gave bounds 5 < 7 on ex1; fixed):
 on the 7 known example spaces, with M = L and with random subspaces M of codimension 2, the bound is >= dim L in all 14 cases, and it
 is EQUAL to dim L for M = L in all of them (dim T_1 = 8, rank 1, bound 7 for the six 7-dim spaces; 6, 1, 5 for K5): FO2 proves
 numerically that each known space is a maximal level space.
 APPLICATIONS (numerical; random m, random combinations of five q_m):
   - M* (three parameter sets): dim T_1 = 8, rank 1: every level space containing M* has dim <= 7 (so it is W_7 or M* itself).
   - generic NON-DIAGONAL level N2 blocks X_ab (4-dim; stage2/r4_block.py solutions; 26 blocks in two runs): dim T_1 = 11, rank 7,
     bound 7 in all 26: such a block lies in no level space of dimension 8 or 9. So the block alone already excludes them -- no use of L_a, L_b.
   - level N2 blocks of family (alpha) (10 blocks, one of them with two-row columns): dim T_1 = 13, rank 8, bound 9: not excluded at second order (they are excluded by
     hand, R4-4).
   - candidates for L_r, i.e. 5-dim level spaces of 4x5 matrices with all 4x4 subpermanents identically zero ((Z2); necessary for
     every row with a_r = 1 of a 9-dim level space), found by LM (stage2/r5_Lr.py, r5_Lr3.py; verified on fresh points):
       two with all row projections of dim <= 3 (as Lemma C requires): (dim T_1, rank) = (9,3) and (10,5): bound 7 and 7;
       one with two rows of 4-dim projection (not admissible): (11,6): bound 8.
     All three contain single-row and single-column elements ("cross" shape). A third LM output was spurious (not level on fresh
     points) -- the sample of 45 points was too small for a quartic in five variables; with 85 points 0 of 4 starts converged in 250
     iterations, so this survey is thin: 2 admissible candidates only.

## R5-6. What remains in REG1 after round 5, the uniform formulation, and what carries over to a_r >= 2
 A. UNIFORM FORMULATION (every row r with a_r = 1 of a 9-dim level space L; dually for columns with b_c = 1):
    (Q-r)  L_r is a 5-dim linear space of 4x5 matrices with  (i) sum_j perm_4((J' + xi)^(j)) = 120,  (ii) perm_4(xi^(j)) = 0 for all j
           and all xi in L_r,  (iii) every row projection of dim <= 3 (Lemma C) and every column projection of dim <= 3,
           (iv) FO2-bound(L_r) >= 9, and the same for M_r = L_r (+) e_r (x) Z_r.
    REG1 means: all five L_r and all five L^c are such spaces. The two admissible candidates found so far fail (iv).
    A classification of the solutions of (i)-(iii), or a proof that (iv) fails for all of them, would exclude every 9-dim level space
    having one line with full projection -- a statement about 4x5 matrices only.
 B. REMAINING CASES IN REG1 (using stage3's Theorem N, not yet verified, for B2):
    (B1) a MINIMAL PAIR (lam_{rr'} = 2, rows or columns). Then L contains the 8-dim level space L_r + L_r' (every element is a sum of
         an element with zero row r and one with zero row r'), both summands satisfying (Q-r); no 8-dim level space is known at all.
         Known: impossible if all annihilators are zero-free (Theorem GEN); one zero in one annihilator of the pair: Type I_0.
         FO/FO2 need explicit candidates for L_r, L_r'; I have none (the pair classification lives on the side of the relations).
    (B2) no minimal row pair: a single-row element exists (Theorem N), z_r <= 2 (stage3 S3-1), L_r is a (5,e) space with e <= 4 - z_r,
         and L lies in T_1(M_r) (R5-4): for z_r = 2 and L_r of type (5,2), L_r must have first-order deformations preserving its
         defect space; all 27 known deletable-line spaces are rigid (rows). Same for columns; if neither a minimal row pair nor a
         minimal column pair exists, L contains e_a w^T and y e_j^T with w_j y_a = 0 (P_2), kappa'^l_a = 0 on supp(w), kappa^i_j = 0 on supp(y).
    (B3) N2: excluded by stage3's N2-X (unverified). Independently excluded here on the sub-families: zero-free column weights
         (N2-GEN + N2-Z', hand), family (alpha) incl. M* (hand + Theorem FO-M*), generic non-diagonal blocks (FO2, numerical).
 C. WHAT CARRIES OVER WHEN SOME a_r >= 2:
    - valid for every level space, no hypothesis on a_r: FO and FO2 (Lemma FO2, Theorem FO-M*: no level space of dim >= 8... precisely:
      every level space containing M* lies in the 8-dim T_1(M*)); (Z3) z_r <= 4 - e(L_r) and R5-4; (Z1) in the form "a sub-block of row r
      is ell-supporting iff it contains the support of an annihilator of row r with sum 1"; the kernel condition is specific to N2.
    - a_r <= 3 for every row of a 9-dim level space (dim L_r = 4 + a_r <= 7 by the checked L_gct_215), and a_r = 3 makes L_r an
      EXTREMAL 7-dim 4x5 level space.
    - (Z2) weakens: for a row with a_r >= 2 one only gets G(xi) in pi_r(L^)^perp (dimension a_r - 1) for xi in L_r: the five 4x4
      subpermanents of L_r span at most an (a_r - 1)-dim space of functions' values. So (Q-r) has an analogue with (ii) replaced by
      "G(xi) lies in a fixed (a_r - 1)-dim subspace of 1^perp", dim L_r = 4 + a_r.
    - need all a_r = 1 (or at least a_r = 1 for the rows involved): Types I/II and GEN-2 (pairs of rows with a = 1; Type I' for (2,1)),
      R3-1, stage3's N1/N/N2-X, hence Theorem GEN and everything built on N2 (N2-GEN, N2-Z, N2-Z'); SR/SC keep the form "some annihilator
      of the line vanishes there" but lose the uniqueness that makes them zero-entry statements.

## R5-7. Two additions
 (a) COROLLARY of Theorem FO-M* [rigorous]: every level space containing M* has dimension <= 7. Proof: L lies in W_7 (+) C tau,
     tau = 1 e_0^T - J/5, and P_2 = 0 on L; an 8-dim L would be all of W_7 (+) C tau and contain tau, but P_2(tau) = (0 - 0 - 20 + 4)/2 = -8
     (P_2(t) = ((sum t)^2 - sum_i s_i^2 - sum_j c_j^2 + sum t_ij^2)/2 with row sums 0 and column sums (4,-1,-1,-1,-1)).
 (b) Shape of the two admissible candidates for L_r (R5-5): the first is a CROSS SPACE -- every element is supported on one row i and one
     column j of the 4x5 block (2-dim single-row part vanishing at column j, 2-dim single-column part vanishing at row i, one more
     element); the second has two rows that are multiples of e_j, a 2-dim single-column part in column j and one single-row element.
     Both are of type (B2) (sparse elements), and both fail FO2.
STATUS 18:38: R5-5 .. R5-7 written. Final report (rounds 4 and 5) follows.
STATUS 18:40: one more (Q-r) run (r5_Lr4.py, seed 21) reached its 118 s timeout with 0 of 3 starts converged; the survey stays at 2 admissible
 candidates. Runs to report (round 5): r5_kernel.py part 2 hit its 115 s timeout without output; r5_Lr3.py and r5_Lr4.py were each
 launched once with a clobbered trial/iteration count (ran nothing; I waited 100 s on the second before noticing); r5_Lr4.py with 85
 sample points: 0 of 4 starts in 110 s. All other round-5 runs < 60 s. Final report (rounds 4 and 5) sent.

# ROUND 6 (start 18:41, budget 90 min -> ends ~20:11). Target: classify the solutions of (Q-r), prove FO2 <= 8 on each component (or find
# the weakest hypothesis under which that is provable); (B1): FO2 for minimal pairs.
STATUS 18:46: plan. (Q-r) in the squarefree algebra A = C[y]/(y_j^2): rows Xi_i in A_1; (ii) <=> Xi_1 Xi_2 Xi_3 Xi_4 = 0 in A_4 on X; level <=>
 the coefficient sums of the elementary symmetric E_1, E_2, E_3 of the Xi_i vanish. Observed: all three solutions found so far vanish on an
 s x t block with s + t >= 6 (Frobenius-Koenig type); but non-FK solutions of (ii) exist (two rows on two columns of the form
 (x,y), (-x,y) plus two rows on the other three columns), so the classification is not just FK. First experiment: (B1) through the plane
 X_{rr'} of a minimal pair alone (2-dim, all 3x3 subpermanents identically 0, P_1 = P_2 = 0): sample such planes and compute FO2.
STATUS 18:58: cross family treated by hand (T_1 explicit, bound 7 for b != 0); the locus b = 0 is the split-free-line locus (bound 9 at
 second order, no 8-dim extension found); planes of minimal pairs alone give FO2 bounds 10-12 (not enough). Census batches running.

## R6-1. (Q-r) in the squarefree algebra; Frobenius-Koenig families  [rigorous remarks]
 A = C[y_1..y_5]/(y_j^2); a 4x5 matrix xi <-> its row forms Xi_1..Xi_4 in A_1. Then
   (ii)  all 4x4 column-deletion subpermanents vanish  <=>  Xi_1 Xi_2 Xi_3 Xi_4 = 0 in A_4;
   (i)   level  <=>  the coefficient sums of the elementary symmetric E_1, E_2, E_3 of the Xi_i vanish (E_4 = 0 by (ii)).
 (ii) holds identically on each of the following linear spaces of 4x5 matrices (zero block s x t with s + t >= 6):
   FK(1,5) a zero row;  FK(2,4) two rows supported in one common column j_0;  FK(3,3) three rows supported in two common columns;
   FK(4,2) two zero columns;  and on CROSS(i_0,j_0) = matrices supported on one row and one column (inside FK(2,4), zero block 3x4).
 But (ii) also has non-FK linear solutions (e.g. rows 1,2 = (x,y,0,0,0), (-x,y,0,0,0) and rows 3,4 supported on the last three columns),
 so a classification cannot be a pure zero-pattern statement. On FK(2,4) (rows i_1,i_2 = s_1 e_{j0}, s_2 e_{j0}; rows i_3,i_4 = p, q):
   P_1 = s + sum p + sum q,  P_2 = s(sum' p + sum' q) + sum p sum q - <p,q>,  P_3 = s (sum' p sum' q - <p,q>'),   s = s_1 + s_2, ' = without j_0,
 so a level subspace has s = 0 identically (a domino (e_{i1} - e_{i2}) e_{j0}^T direction plus a 2-row level space on rows i_3,i_4) or
 sum' p sum' q = <p,q>' identically. In a 9-dim L, an L_r of type FK(2,4) forces lam_{r i_1}, lam_{r i_2} >= 4 and m_{i_3 i_4} >= 3.

## R6-2. THEOREM (cross family): every level space containing X(a,b), b != 0, a not in C1, has dimension <= 7  [hand proof; formula for
##       T_1 and all ranks confirmed numerically for 6 random complex and 7 special parameter sets, stage2/r6_cross.py]
 Rows 0..4 with r = 0 (zero row), i_0 = 1, j_0 = 0. W' := {t(y,w): column 0 = y in C^5, row 1 = y_1 e_0 + w, w on columns 1..4};
 perm(J + t(y,w)) = 24(1 + y_1) + (24 + 6 sum w) sum_{i != 1}(1 + y_i); W_7' := {sum y = 0, sum w = 0} is a 7-dim level space (full free
 column 0 + three single-row elements of row 1).  CROSS FAMILY (the 5-dim level subspaces of CROSS(1,0) with zero row 0 whose row-1
 projection is 3-dim):     X(a,b) := {t(y,w) : y_0 = 0, sum y = 0, sum w = 0, b y_1 + <a,w> = 0},   (a mod C1, b) in P^3.
 [The other maximal level subspace of the cross, {sum_{i != 1} y_i = 0, y_1 + sum w = 0}, only gives X = (3-dim single-row space) (+)
 (2-dim single-column space), i.e. z = 3.]
 Cofactors of U = J + t(y,w) (direct Laplace expansions): C_i0 = 24 + 6 sum w (i != 1), C_10 = 24, C_1j = 24 + 6(sum y - y_1),
 C_ij = 6(1 + y_1) + 2(3 + sum w - w_j)(3 + sum y - y_i - y_1) (i != 1, j >= 1). On X(a,b), with S(t) = sum of all entries,
 rho_i = sum_{j>=1} t_ij, gamma_j = sum_{i != 1} t_ij, t_i' = (t_ij)_{j>=1}:
     <C(U),t> = 24 S - 6 <y,rho> - 6 <w,gamma> + 2 sum_{i=2,3,4} y_i <w,t_i'> + 2 y_1 <w,gamma>.
 Degree 2 on X (b != 0, a not in C1): t_i' = u + c_i 1 (i = 2,3,4) and gamma = u mod 1; degree 1: gamma in C1 + C a, rho_2 = rho_3 = rho_4
 = lam, rho_1 = lam + nu b; degree 0: S = 0. Result (dim 10):
     T_1(X(a,b)) = { column 0 arbitrary; row 1 arbitrary; row 0 on columns 1..4 = -2 nu a + c_0 1; rows 2,3,4 on columns 1..4 = nu a + c 1 }
                   with  sum_{j>=1} t_1j = nu (sigma_a + b) + 4c  and  S(t) = 0     = W_7' (+) (the three directions nu, c, c_0).
 Second order: P_2 vanishes on W_7', and for t in W_7', t' in T_1:  P_2(t,t') = -(1/2)[ y_0 (4c_0' - 4c' - 3 nu' sigma_a) + nu' (b y_1 + <a,v>) ].
 The functionals y_0 and b y_1 + <a,v> are independent on W_7' (their common kernel is X(a,b)), so the pairing has rank 2; the direction
 c = c_0 (which is 1 e_0^T - J/5 up to scale) pairs to 0 with W_7' and has P_2 = -8 != 0. Hence rank(P_2 on T_1) = 5 and
 dim L <= 10 - 3 = 7 for every level space L containing X(a,b).                                                                QED

## R6-3. The locus b = 0 (and a in C1): the split free line  [T_1 by hand; extension search numerical]
 X(a,0) = (3-dim space of single-column elements of column 0 on rows 1..4) (+) (2-dim space of single-row elements of row 1), so as an
 L_r it has z' = 3. Here T_1 is 13-dim (same computation: block rows 0,2,3,4 x columns 1..4 with all four rows in span(1,a)), a generic
 q_m has rank 8, FO2 bound 9: NOT excluded at second order. This is exactly the (5,1) / split-free-line situation (rows' (DI_5) at
 e = 1; excluded under (H1) for the other family of lines by stage3's S3-1). Direct search (stage2/r6_cross_b0.py, a = (1,2,3,5)): level
 spaces of dimension 7 containing X(a,0) are found at once (4/4 starts, residual 1e-10 .. 1e-7: W_7'), dimension 8: 6/6 starts end at
 the same residual 0.775. So no 8-dim level space through X(a,0) is visible; not a proof.
STATUS 19:05: censuses done for the general search and for FK(2,4), FK(3,3); FK(1,5), FK(4,2) running. Writing R6-4 .. R6-6.

## R6-4. Numerical census of (Q-r) solutions and their FO2 bounds  [numerical; every solution verified on fresh points]
 (a) GENERAL search (stage2/r5_Lr3.py, r6_census.py: 5-dim X, level + (ii), rows of rank <= 3; about 20 starts in four batches, LM often
     stuck at residual 0.75): 6 verified solutions. ALL vanish on a 2x4 block (type FK(2,4); one is a cross space):
        row proj [2,3,1,1] (three times): dim T_1 = 9, rank 3, bound 7;   [1,3,1,1] cross: (10,5), bound 7;
        [1,2,1,2]: (12,7), bound 8;   [3,1,1,3]: (12,7), bound 8.
     (One more solution of the unconstrained search has two rows of 4-dim projection, not admissible: (11,6), bound 8.)
 (b) inside FK(2,4) (stage2/r6_fk.py 24; only the level condition remains; 14 starts): 9 verified solutions, row projections
     (1,1,2,3), (1,1,3,3), (1,1,2,2), with 1-2 single-row and 1-2 single-column dimensions: ALL have dim T_1 = 9, rank 3, bound 7.
 (c) inside FK(3,3) (10 starts): 7 verified solutions, ALL with a 3-dim single-row space in the fourth row (z = 3):
     (dim T_1, rank, bound) = (12,7,8) twice, (11,6,8) twice, (13,8,9) three times.
 (d) cross family: R6-2 (bound 7 for z, z' <= 2) and R6-3 (z' = 3: bound 9).
 Solutions with a row of 3-dim projection (the L_r of a MINIMAL pair (r,i)) occur in (a), (b): all of them have bound 7.
 PICTURE: every solution found with all sparse parts of dimension <= 2 has FO2 bound <= 8 (mostly 7); the bound 9 occurs only with a
 3-dim single-row or single-column part. No non-FK solution was found, although non-FK solutions of (ii) exist (R6-1); LM from random
 starts finds the large components only, so this is NOT a classification.

## R6-5. The split free line (z = 3) is a sub-case of (B1); a relation given by every single-row element  [rigorous, short]
 (a) e_i (x) Z_i lies in L_r for every r != i, so z_i <= dim pi_i(L_r) = 5 - lam_{ri} when a_r = 1 (stage3's S3-1). Hence in REG1:
     z_i = 3  =>  lam_{ri} = 2 for ALL four rows r != i, and L_r = X_{ri} (+) e_i (x) Z_i:  a split free row is in four minimal pairs.
     So the only configurations on which FO2 gave bound 9 are minimal-pair configurations (B1) of a very rigid kind, and L_i is a (5,1) space.
 (b) For every single-row element e_i w^T of a level space L and every t in L:  <w, sum_{k != i} t_k> = 0  (polar form of P_2; sum w = 0).
     So each single-row element gives the relation 1_{rows != i} (x) w in the annihilator of L: the column sums over the other four rows
     are orthogonal to Z_i. For z_i = 3 they lie in the 2-dim space span(1, m), m the defect line.

## R6-6. (B1) with FO2
 - the plane X_{rr'} of a minimal pair alone (2-dim, all 3x3 subpermanents identically 0, level; stage2/r6_planes.py, 40 planes): FO2
   bounds 10-12 (dim T_1 = 19-22, rank 17-20). Not enough; and LM finds mostly degenerate planes (a zero row).
 - through (Q-r): L_r of a minimal pair (r,i) is a (Q-r) solution with a row of 3-dim projection. Those found (R6-4) have bound 7,
   except the z = 3 family (bounds 8-9).
 - FO2 on L_r + L_r' with the tau-coordinate descriptions of Types I, II, I_0: NOT done. The tau-descriptions give the relations on the
   two rows r, r', not the elements of L_r and L_r' in the other three rows; an explicit 8-dim candidate L_r + L_r' needs a solution
   of (Q-r) for both rows with a common 2-dim plane, which I did not construct.
STATUS 19:09: FK(1,5) census: 1 solution (lam = 5 type), bound 9; FK(4,2): no result (timeout). New linear test (T2) and the
 antisymmetry condition for lam = 5 found and applied.

## R6-7. Beyond (Q-r): the next order of chief's identity (**), and what survives  [conditions rigorous; applications numerical]
 For a_r = 1, L^ = {(v; T(v) + xi)}, <v, G(T(v) + xi)> = 120 <kappa^r, v>^5 for all v in C^5, xi in L_r (chief RP6). Expanding at v -> 0:
   order 1:  G(xi) = 0 on L_r                                                                      [= (ii) of (Q-r)];
   order 2:  (T2)  D_{T_k} G_j(xi) + D_{T_j} G_k(xi) = 0 for all j <= k, xi in L_r,  T_k = T(e_k),  sum_k T_k = J' mod L_r.
 (T2) is LINEAR in T, so it is a cheap exact test for a candidate L_r: solve the linear system and ask whether J' lies in
 {sum_k T_k} + L_r (stage2/r6_T2.py). Expanding at v -> 1 instead gives FO and FO2. So (Q-r), FO2 and (T2) are three independent
 consequences of the single statement "there is a linear T with (**)", which is EQUIVALENT to the existence of the 9-dim L.
 LEMMA (lam_{rr'} = 5, a_r = a_r' = 1) [rigorous]. Then L_r = L_r' =: X (a 5-dim level space on the other three rows, (ii) is void), row r'
 of u in L^ is Phi(u_r) with Phi in GL_5, Phi(1) = 1, and (T2) becomes   C(xi) Phi + Phi^T C(xi) = 0 for all xi in X,
 C(xi)_{jl} = perm_3(xi without columns j,l). In particular all C(xi) are singular, and if the ten cubics C(xi)_{jl} are linearly
 independent on X there is no such Phi (Phi would be diagonal with Phi_jj + Phi_mm = 0 for all j != m).
 RESULTS on the saved candidates (distance of J' from {sum_k T_k} + L_r; 0 = (T2) solvable):
   FK(2,4) [2,3,1,1] (two of them): 2.8 and 1.7 -> (T2) fails (they also fail FO2);   FK(2,4) [1,2,1,2]: solvable (fails FO2, bound 8);
   FK(1,5) (lam = 5, FO2 bound 9): 2.2 -> (T2) fails; the antisymmetry system has only Phi = 0 (stage2/r6_lam5.py);
   FK(3,3) with z = 3, FO2 bound 9 (three of them): 3.0 -> fails; 2e-14, 9e-15 -> solvable;
   cross spaces: solvable for all (a,b) (there D G = 0).   [Two older LM solutions give 4e-3, 3e-2: not accurate enough to decide.]
 SURVIVORS of (Q-r) + FO2 + (T2) among everything found:  the cross spaces with b = 0 or a in C1, and two FK(3,3) solutions -- all with
 a 3-DIM SPARSE PART (z = 3 or z' = 3), i.e. a split free line, which in REG1 means four minimal pairs through that line (R6-5).
 LEMMA (z_i = 3) [rigorous]. If z_i = 3 in a 9-dim level space, then M_i = L_i (+) e_i (x) Z_i is an 8-dim level space with deletable row i,
 L = M_i (+) C t_0, and t_0 is a first-order extension direction of M_i outside M_i (+) C(e_i 1^T - J/5):  dim T_1(M_i) >= 10.
 [T_1(M_i) contains M_i (+) C tau', tau' = e_i 1^T - J/5 (R5-4); P_2(tau' + m) = -8 - 4 s_i(m) = -8 for m in M_i since the row-i sum of m
 is 0; so a 9-dim level L cannot be M_i (+) C(tau' + m).]
STATUS 19:13: RESULT-R6 at the top. Runs to report (round 6): r6_census.py was launched once with clobbered parameters (crashed at once);
 census batch 32 overlapped for about 100 s with the FK(2,4) run (two processes at once); r6_fk.py for FK(1,5)+FK(4,2) hit its timeouts
 twice (first time without output; FK(4,2) gave no result); batches 32, 33 reached the 170-175 s timeout after 5 starts. Final report sent.

## R6-8. Additions after the first write-up (19:13 - 19:18)  [numerical]
 - second seeds (stage2/r6_fk.py): FK(2,4): 11 more solutions (total 20): (dim T_1, rank, bound) = (9,3,7) seventeen times, (12,7,8) twice,
   (8,3,6) once -- all <= 8, all with sparse parts <= 2.  FK(3,3): 8 more (total 15): the two with z = 2 have (10,5,7); the thirteen
   with z = 3 have bound 8 (seven) or 9 (six).  FK(4,2): 0 solutions in 6 starts.  General search, batch 33: one more FK(2,4) solution,
   row projections [3,1,1,3], (12,7,8) (already counted in R6-4).
 - direct extension search (stage2/r6_extend.py) for the two FK(3,3) solutions that survive FO2 and (T2): level spaces of dimension 8
   containing them: 8 starts, residual floors 0.77 - 1.2. With R6-3 (cross, b = 0: 6 starts, floor 0.775): none of the survivors is seen to
   extend even to dimension 8.
 - SANITY of (T2) (stage2/r6_T2_sanity.py): on the 7 known spaces, for all 10 lines with full projection (rows and columns), G = 0 on L_r
   and (T2) is solvable with sum_k T_k = J' (distance <= 5e-15); for random spaces of the same dimension 3 the distance is about 4.
STATUS 19:18: R6-8 added. Final report sent.

# ROUND 7 (start 19:33, budget 90 min -> ends ~21:03). Targets: (0) COMPUTE-stage2.md; (1) dim T_1 and "not level beyond" for the (2,4)
# family; (2) z = 3 in REG1; (3) what remains of REG1. Correction to (Q-r)(iii) from verify2: the column projections of L_r have dim <= 3
# except possibly for ONE column c with kappa^r = e_c, kappa'^c = e_r (entry (r,c) = 0 on L), where only <= 4 holds and L = L_r + L^c.
STATUS 19:36: /home/claude/work/L-gct-210/COMPUTE-stage2.md written (tasks S1-S6: census at scale, non-block solutions, exact FO2 for (2,4),
 minimal pairs with zeros as an exact problem, two-row-column blocks, z = 3). Starting (1).
STATUS 19:43: new first-order test (FO-r) found: it kills the generic (2,4) solutions and the whole cross family including the locus b = 0.

## R7-1. LEMMA (FO-r): the row-r projection of T_1(L_r) must be all of C^5  [rigorous; sharper than "dim T_1 >= 9"]
 Let r be a row with 4-dim projection of a level space L, X = L_r. Then T_1(X) contains L and tau = e_r 1^T - J/5 (R5-4), whose row r is
 (4/5) 1, not in pi_r(L) = (kappa^r)^perp. Hence  pi_r(T_1(X)) = C^5.  Explicitly (perm(u) = <u_r, G(u')>):
     t_0 in pi_r(T_1(X))   <=>   the function xi -> <t_0, G(J' + xi)> on X lies in D(X) := { xi -> D_{t'} N(J' + xi) : t' in C^{4x5} },
 so (FO-r) says: EVERY column-deletion permanent G_j(J' + xi) is, on L_r, a first-order variation of the level function N.
 [It is the order-1 part at v = 1 of chief's identity: G_j(J' + xi) + D_{T(e_j)} N(J' + xi) = 600 kappa^r_j.]
 Always: pi_r(T_1(X)) contains (C(X) + C1)^perp and 1, so its dimension is >= 5 - e(X); (FO-r) can only fail if e(X) >= 2.
 APPLIED to every saved candidate (stage2/r7_FOrow.py; dim T_1, dim of the row projection):
   cross X(a,b), b != 0: (10, 3) DEAD;   cross, b = 0 (3-dim single-column part): (13, 3) DEAD;   cross, a in C1 (3-dim single-row part): (13, 5) passes;
   (2,4) solutions with dim T_1 = 9 (all of "Case B" below; 6 saved): (9, 2) DEAD;   (2,4) "Case A" (3 saved): (12, 5) pass (FO2 bound 8);
   (3,3) solutions with z = 3 (6 saved): (13, 5) pass;   (1,5) candidate: (13, 5) passes (dead by (T2)).
 For the cross family this is a one-line proof from R6-2/R6-3: the row-0 part of T_1(X(a,b)) is (y_0 ; -2 nu a + c_0 1) for b != 0, and
 (y_0 ; span(1,a)) for b = 0: dimension 3 < 5 in both cases. So EVERY cross space with a not in C1 is excluded at first order [rigorous],
 including the split-free-column locus b = 0 that FO2 could not exclude.

## R7-2. The (2,4) family  [formulas rigorous and machine-checked (stage2/r7_fk24_formula.py); the last step of Case B numerical]
 Rows 0 (= r, zero on X), 1, 2 (= s_1 e_0, s_2 e_0), 3, 4 (= p, q). U = J + xi, P = 1 + p, Q = 1 + q, ' = columns 1..4, al = sum P', be = sum Q',
 gam = al be - <P',Q'>, al_j = al - P'_j, be_j = be - Q'_j, gam_j = al_j be_j - <P',Q'> + P'_j Q'_j, s = s_1 + s_2, h_j := 2 P_0 be_j + 2 Q_0 al_j.
 Cofactors:  C_00 = C_10 = C_20 = 2 gam,  C_30 = 6 be,  C_40 = 6 al,  and for j = 1..4:
     C_0j = (2 + s) gam_j + h_j,   C_1j = (2 + s_2) gam_j + h_j,   C_2j = (2 + s_1) gam_j + h_j,   C_3j = 2(3 + s) be_j + 6 Q_0,   C_4j = 2(3 + s) al_j + 6 P_0.
 Hence C_00 = C_10 and C_0j - C_1j = s_1 gam_j, C_1j - C_2j = (s_2 - s_1) gam_j, so
     pi_r(T_1(X)) = C e_0 (+) { t in C^4 : s * sum_j t_j gam_j restricted to X lies in D(X) }.
 Level conditions (R6-1): s = -(p_0 + a + q_0 + b),  p_0 a + q_0 b + a^2 + ab + b^2 + <p',q'> = 0,  s (ab - <p',q'>) = 0  (a = sum p', b = sum q').
 CASE A (s = 0 on X): rows 1,2 form a domino direction, (p,q) runs through a 2-row level space; pi_r(T_1(X)) = C^5: (FO-r) holds, no
   first-order obstruction. The three solutions found have dim T_1 = 12, rank 7, FO2 bound 8 (and one earlier (8,3,6)): dead by FO2
   numerically; not proved.
 CASE B (ab = <p',q'> on X, s not 0): then p_0 a + q_0 b + (a+b)^2 = 0, i.e. a u + b w = 0 with u = a + b + p_0, w = a + b + q_0; if a, b are
   independent on X this forces p_0 = -a - (1+mu) b, q_0 = (mu-1) a - b, s = (1-mu) a + (1+mu) b for a constant mu.
   (FO-r) requires s * gam_j in D(X) for every j. In all 6 saved Case-B solutions (and all 20 census solutions with dim T_1 = 9) the
   projection is only C e_0 (+) C 1: DEAD at first order. A proof needs the parametrisation of the 5-dim solutions of Case B
   (COMPUTE-stage2.md, S3); I did not obtain it.
 So "dim T_1 = 9" is explained: T_1(X) = (7-dim part with zero row r) (+) (2-dim row-r part e_0, 1); and "not level beyond" holds in the
 stronger form "no level space with a 4-dim row-r projection contains X as its L_r".

## R7-3. z_i = 3 in REG1 (split free line)  [reductions rigorous; NOT closed]
 Setting: 9-dim level L, a_i = 1, z_i = 3, Z := Z_i = (C1 + Cm)^perp, m orthogonal to 1 (the defect line of the (5,1) space L_i).
 (a) [P_2] single-row parts of different rows are orthogonal, so Z_k lies in Z^perp cap 1^perp = C m for every other row k: z_k <= 1, and a
     single-row element of another row is e_k m^T, which lies in L_i. If <m,m> != 0, verifyfl's Theorem SPLIT (a 4x5 space with defect line
     C m, <m,m> != 0, containing e_k m^T has dim <= 4) gives a contradiction. So for non-isotropic m:  z_k = 0 for all k != i, and L_i is a
     NON-SPLIT (5,1) space.  (rows' FL2*(a) and NCOL-S apply to split spaces only, so they give nothing more here.)
 (b) [TC5] m is not a two-column vector e_a - e_b.  [HYP] every hyperplane of L_i is a non-split (4,1) space with the same defect line; all
     known non-split (4,1) spaces have a two-column defect line (rows U5), so no such hyperplane is known.
 (c) [(FO-r) for row i] pi_i(T_1(L_i)) contains Z (+) C1 automatically; the fifth dimension requires the defect function g of L_i
     (G(J' + xi) = 24*1 + g(xi) m) to be a first-order variation of N on L_i: g = D_{t'} N(J' + .) + const for some t'. The same then holds on
     every hyperplane. All 27 known 7-dim level spaces with a deletable line are rigid (T_1 = M + C tau; rows), i.e. their defect
     functions are NOT such variations. So z_i = 3 needs a first-order FLEXIBLE non-split (5,1) space.
 (d) [R6-5, R6-7] four minimal pairs through row i, L_r = X_{ri} (+) e_i Z for r != i; column sums of all x in X_{ri} lie in C m; L = M_i (+) C t_0
     with dim T_1(M_i) >= 10; and on the 6-dim space Lam_0 = L_i (+) C Theta (Theta = rows != i of t_0): G(J' + eta) lies in span(1,m), with
     m-component 120 kappa_m - (1 - kappa_m s)(N(J'+eta) - 120)/s  (s = coordinate of Theta, kappa^i = 1/5 + kappa_m m).
 (e) Candidates: every (Q-r) solution found that passes (FO-r), FO2 and (T2) is of the form X_{ri} (+) e_i Z with z_i = 3 (four (3,3)
     solutions and the cross spaces with a in C1; table: stage2/r7_table.py). z_i = 3 would need an 8-dim level space M_i containing it;
     the direct search (stage2/r6_extend.py, D = 8) finds none for the five candidates tested (4 starts each, residual floors 0.8 - 1.6).
 NOT DONE: a proof. The statement that would finish z = 3 for non-isotropic m is verifyfl's (SL_m) / "every (4,1) space with a
 non-two-column defect line is split"; isotropic m is not touched.

## R7-4. Correction of (Q-r)(iii), the exceptional case, and what remains of REG1
 (iii) corrected (verify2): row projections of L_r have dim <= 3 (Lemma C); column projections have dim <= 3 except possibly for ONE
 column c, when kappa^r = e_c and kappa'^c = e_r (the entry (r,c) vanishes identically on L); then only <= 4 holds and L = L_r + L^c.
 None of my statements used the column part: the censuses impose row ranks only, and (FO-r), FO2, (T2), the cross theorem and the
 (2,4) formulas do not use (iii). In the exceptional case one has in addition: ell(u) = u_rc; for the four columns j != c the 6-dim
 spaces {t in L : t_r in C e_j} have vanishing (r,j)-deletion permanent (and dually for the four rows i != r in column c); and by (**)
 at v = e_c the image of L_r in the (r,c)-minor is a linear space of 4x4 matrices on which perm_4(B + .) = 120 is constant for a
 suitable B. I found no contradiction for this case and no candidate (no census solution has a 4-dim column projection).
 WHAT REMAINS OF REG1 (with stage3's Theorem N for (B2)):
   (B1) a minimal row or column pair. Sub-case z = 3: R7-3. General case: L_r is a (Q-r) solution with a 3-dim row projection passing
        (FO-r), FO2, (T2); the ones found are dead unless z = 3.
   (B2) no minimal pair on either side: single-row and single-column elements with z, z' <= 2; every L_r is a (Q-r) solution passing the
        three tests; all 40-odd solutions found with z, z' <= 2 fail at least one test (most already fail (FO-r) or FO2).
   (B0) the exceptional case of (iii): an identically vanishing entry.
 A proof of REG1 now needs: the classification of (Q-r) solutions (COMPUTE-stage2.md S1-S3) or a structural proof that a (Q-r) solution
 passing (FO-r) and FO2 contains a 3-dim single-row part; and the non-split (5,1) problem for z = 3.
STATUS 19:48: R7-1 .. R7-4 written. Table of all saved candidates: stage2/r7_table.py (ALIVE: four (3,3) solutions with z = 3 and the cross
 spaces with a in C1; all others dead).
 Sanity of (FO-r) (stage2/r7_FOrow_sanity.py): on the 7 known spaces all 10 lines with 4-dim projection have projection dimension 5.
 The four ALIVE (3,3) candidates are spanned by sparse elements only: X = C y e_0^T + C y' e_1^T + e_i Z (two single-column elements with
 <y,y'> = 0 and a 3-dim single-row space); their m is neither two-column nor isotropic.
STATUS 19:50: RESULT-R7 at the top. Runs: r6_extend.py on three files reached its 115 s timeout after two; r7 struct scripts < 40 s.
 Final report sent.
