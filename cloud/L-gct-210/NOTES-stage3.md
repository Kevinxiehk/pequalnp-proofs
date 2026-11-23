# NOTES-stage3 (role: stage3; start 14:37, budget 90 min -> ends ~16:07)
## RESULT, ROUND 7 (stage3, 20:12; final) -- details in section 26; requests for the heavy machine in COMPUTE-stage3.md
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
 (5) COMPUTE-stage3.md (asked for by the coordinator): six self-contained computation requests (direct structured searches for
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
        Sanity checks (z22_check.py, 200 random instances): dim(Z o Z) = 3 for totally isotropic Z; no B != 0 in Lemma DEG; generic
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
STATUS 20:12: THEOREM Z22 proved (two rows with 2-dim single-row parts are impossible, degenerate planes included). Final report of round 7.
