# NOTES-rows (role rows; start 14:17, budget 90 min -> ends ~15:47)
## RESULT, ROUND 5 (rows; final 20:00) -- (NC') NOT proved; (NCOL_1) PROVED in the principal case (Theorem NCOL-P3), exact 4x4 statement found
 Details and proofs: section R5 (R5.1 - R5.13).  Heavy-computation requests: COMPUTE-rows.md (H1-H6, exact systems X1-X4).
 V1 [RIGOROUS, R5.9] THEOREM NCOL-P3: let L' be a 4 x 5 level space with defect line C m (ANY m, isotropic allowed), K in L' a 3-dim strongly
    level subspace with row sums s(K) = 1^perp living on three columns a, b, c, and Z in L' with zero row sums and c(Z) != 0. Then
    m_a m_b m_c = 0 (two columns: m_a m_b = 0). So every (4,1) space whose column-centred part ker c is such a K has a neutral column,
    and it is an active column of K.  Proof: isometries B_j with B_a+B_b+B_c = 1, normal form z_j = m_j((kappa/4)1 + B_j f), <f,f> =
    (3/4)kappa^2 != 0, and a 3 x 3 Gram computation that ends in (alpha+beta-gamma)(alpha-beta+gamma)(-alpha+beta+gamma) = 8 m_a m_b m_c = 0.
    Covers 28 of the 30 known (4,1) spaces (the 2 others are column-centred with a two-column defect line); every ingredient checked
    numerically to 1e-9 or better.  Hypothesis left: "K lives on <= 3 columns" (true for 90/90 principal kernels and 49/49 fresh strongly
    level 3-spaces; types by column ranks (1,1,1), (2,1), (3), (3,2), (2,2,1)); exact problem X4.
 V1' [RIGOROUS, R5.11] THEOREM P51: if the five entries of m are pairwise distinct, there is NO (5,1) space with defect line C m containing a
    3-dim strongly level K with s(K) = 1^perp that is spanned by single-column elements or lives on two columns (kernel types (1,1,1),
    (2,1), (3), (3,2) = 41 of 49 fresh strongly level 3-spaces); a (4,1) space of the first kind is split.  Mechanism: the row-centred
    elements are RANK ONE, Z = a m^T, and the derivative of the deletion vector along each single-column element forces a = kappa e_i.
    Left for principal (5,1): kernel type (2,2,1), repeated entries of m (incl. isotropic (1,w,w^2,0,0)); see also R5.10.
 V1'' [NUMERICAL + partly rigorous, R5.12] (R-LAW): in all 90 principal extremal spaces every row-centred element has ALL ITS ROWS IN THE
    DEFECT SPACE C (N = L' cap ker s lies in C^4 (x) C; Z w = 0 for w in W); proved for kernels spanned by single-column elements (any e).
 V2 [RIGOROUS, R5.6] (SC1) first-order law for a single-column element x e_n^T in ANY column: <x, s(Y) - y_n> = 0 and (<x,y_j>)_{j != n} in
    C cap e_n^perp for all Y in L'.  For e = 1 and m_n != 0: all other columns of all of L' are orthogonal to x.
 V3 [RIGOROUS, R5.2] THEOREM DC / NC'-DC: dim L' = rank c + rank s + dim L'_dc, so (DI_5) can fail only through DOUBLY CENTRED elements.
    With a neutral column:  dim L' = e + 3 + delta - s1 - s2 - s3,  delta = dim Q_dc,  s1 = e^col(Q) - rank rho,  s2 = 3 - e^col(Q) - dim X_n,
    s3 = e - rank kappa (all >= 0).  So the exact 4 x 4 statement behind (NC'_e) is (DC-COST): delta <= s1 + s2 + s3; (NC') holds whenever Q
    has no doubly centred element; with the checked L_gct_216: dim L' <= e + 6.  Bilinear form of the problem (R5.1):
    Xh^T (Adj(q) - 6J) Wh = 0 on Q and the claim dim Q + dim Xh + dim Wh <= 8, which interpolates between a triviality (Q = 0) and the
    checked L_gct_214 (Xh = Wh = C1). The checked 4 x 4 theorems 214/216/217 alone do NOT give (DC-COST).
 V4 [RIGOROUS, R5.3] (NCOL_3) + (DI_4x4) => no (7,3), where (DI_4x4): "a 4 x 4 level space has dim Q <= e^col(Q) + 3" = (DI_5) for 4 x 5
    spaces with a zero column; it needs only: no (dim, e^col) = (5,1), (6,2); (5,1) with a two-column line is excluded by TC5.
 V5 [NUMERICAL, calibrated] 4 x 4: (4,1) 9/17, (5,1) 0/14; (5,2) 2/10, (6,2) 0/15; any 6-dim 4 x 4 level space 0/15; row-centred (4,1): 1/34
    and that hit has a two-column defect line.  Block pattern (3,2) for (6,3): 0/30 (control 4/19).  Towers continue: in all 120 cases
    the 4 x 4 base Q has again a deletable row or column.  Principal census: 90 of 95 extremal spaces have ker c = strongly level
    3-space with s = 1^perp, always on <= 3 columns, always containing a single-column element in a neutral column.
    Slack census: delta = 0 in 126 of 135 tower positions; delta > 0 in 7, always paid exactly (s3 or s1); s2 = 0 always.
 V6 [RIGOROUS, partial, R5.13] (NCOL_2) for kernels spanned by single-column elements when C o C is independent of C modulo C
    (hypothesis (G)); (G) fails for the known defect planes, so this is a constraint, not a proof of (NCOL_2).
 NOT PROVED: (NC'_e) (= (DC-COST)); (DI_4x4); (NCOL_1) for non-principal spaces and "K on <= 3 columns"; (NCOL_2), (NCOL_3)
    (for e >= 2 the Gram argument of V1 needs rank-one column data; only numerics and (FS-DEC)).
## RESULT, ROUND 4 (rows; final 19:13) -- (6,2), (7,3) and (D) NOT proved. Induction on e set up exactly; one new structural law
## (NCOL, numerical, 0 exceptions in 120 spaces) reduces (DI_5) to 4 x 5 spaces with a neutral column = "double towers" over 4 x 4.
 Details and proofs: section R4 (R4.1 - R4.15).  (d,e) space = 4 x 5 level space of dim d with defect space C of dim e; extremal: d = e + 3.
 U1 [RIGOROUS, R4.1] HYPERPLANE LEMMA: if no (e'+4, e') space exists for e' < e, then in an (e+4, e) space every subspace K has
    e(K) >= min(e, dim K - 3); every hyperplane is an EXTREMAL (e+3, e) space with the SAME defect space C.
 U2 [RIGOROUS, R4.2/R4.3] single-row parts U_i: U_i in C, U_i perp U_k, cubic condition, u_i + u_k <= e + 1; LEMMA RS-HYP: the generic
    hyperplane of a minimal (e+4, e) space is NOT fully row-split (sum_i U_i != C), e = 1, 2, 3 (e = 3 uses the checked L067).
 U3 [RIGOROUS, R4.7] LIFTING LEMMA: a finite union of "polynomial identities hold on the subspace" properties that fails for L fails
    for all subspaces through a suitable t in L.  D-UP: (D)_d => (D)_d+1; so (D) <=> (D)_7 and "(D) for dim >= 8" FOLLOWS from the
    7-dim statement.  C-UP: under the induction hypothesis, any property of C common to all extremal (e+3,e) spaces holds for every
    (e+4,e) space.   [(D)_8 itself: not proved; with (DI_5) it is equivalent to "no 8-dim level space" (R4.11).]
 U4 [RIGOROUS, R4.10] transposed defect construction: if column n of L' is neutral (C in e_n^perp), then L' = {(q | x)} over the level
    4 x 4 space Q = L' minus column n, C_j(Y) = (1+x).M^(j)(q), and dim L' <= dim Q + 3 - e^col(Q); PADDING LEMMA: a 4 x 4 level space
    with e^col = 0 or e^row = 0 has dim <= 3; so "a 4 x 5 level space with a neutral column has dim <= 6" (which contains (7,3) in
    the neutral case) follows from: no 4 x 4 level space with (dim, e^col) = (5,1), (6,2).
 U5 [NUMERICAL, R4.4] answer to the question "are extremal spaces all split over rows?": NO. Of 68 extremal spaces, 53 are fully
    row-split, 15 are not ((4,1): 2 with C = C(e_a - e_b); (5,2): 3 with C = V_S, |S| = 3; (6,3): 10 with C = V_S, |S| = 4).
    What holds in all 68: (LAW) C = sum_i U_i + span{two-column vectors of C}.
 U6 [NUMERICAL, R4.8 -- the main finding] (NCOL): EVERY extremal space has a NEUTRAL COLUMN (C lies in a coordinate hyperplane e_n^perp;
    L' minus column n is a level 4 x 4 space).  87/87 of my extremal spaces; 33/33 seven-dim 5 x 5 level spaces of other agents
    (after deleting their deletable line the rest has a neutral line of the other kind).  Direct calibrated test at e = 3 (R4.13):
    defect space fixed = e_0^perp cap 1^perp: (6,3) found 4/19; defect space fixed generic: 0/46.  In 5 x 5 terms: every known
    7-dim level space with deletable row r contains e_r(1 - 5e_n)^T, and is a DOUBLE TOWER
          L = Q (+) [column n: 3 - e^col(Q) dims] (+) [row r: 4 - e^row(Q) dims],   dim Q = e^row(Q) + e^col(Q)   (R4.10, numerical),
    so 7 comes out identically; no extremal space has a deletable ROW.
 U7 [RIGOROUS reduction, R4.8/R4.12] by C-UP:   (DI_5)  <=  (NCOL_e) and (NC'_e), e = 1, 2, 3,
    (NC'_e) := "a 4 x 5 level space with a neutral column and defect dimension e has dim <= e + 3".  This replaces (LAW) + the list of
    mixed/degenerate patterns of R4.6 by one statement about C and moves the rest to the 4 x 4 world.
 U8 [NUMERICAL, calibrated, R4.9] neutral columns: k = 2: dim 5 12/25, dim 6 0/22;  k = 1: dim 6 7/29, dim 7 0/25;  k = 1, e <= 1:
    dim 4 5/11, dim 5 0/8;  k = 1, e <= 2: dim 5 3/5, dim 6 0/15.  (6,2) seeded at the three column-type (5,2) spaces: 0/17.
 U9 [RIGOROUS, R4.14] THEOREM NCOL-S = (NCOL_1) in the split non-isotropic case: a 4 x 5 level space with defect line C m, <m,m> != 0,
    containing e_i m^T, has dim <= 3 if m has no zero entry. So every split (4,1) space with non-isotropic m has a neutral column
    (proof: first-order eigenvector condition D_i(Y)m = mu m forces equal column sums, then a zero row, then Lemma SL_3).
    Every step confirmed on the 27 split (4,1) examples.  Same computation, any e (R4.15): (F1) c^(i)(Y).u = 0 and c^(i)(Y) o u in C
    for u in U_i, Y in L'; (F2) U_i o U_k inside C (i != k); (FS-DEC) an extremal space in which one row carries a nondegenerate C
    has DECOMPOSABLE C (e = 3: C = V_A + V_B with block sizes (4,1) = neutral column, or (3,2)).
    (F1^T) for a neutral column n: x^T q in C and x.rho(q) = 0 for single-column elements x in X_n and all (q|x') in L'.
 NEGATIVES: (i) "column-centred 4 x 5 level spaces have dim <= 3" is false (dim 4 exists), although the column-sum map is linear with
    image in C; (ii) "dim L <= e_row(L) + e_col(L)" (true with equality for the 7-dim spaces) is false for the level line
    C circ(1,i,-i,-1) padded (all ten deletions level); (iii) EQ-induction step (round 3).
 OPEN (exact): (NCOL_e) and (NC'_e) for e = 1, 2, 3 [known: (NCOL_1) for split non-isotropic m = U9; (NC'_1) for two-column m = TC5;
    one row carrying a nondegenerate C = FS];
    equivalently for the gap: (D)_7 (or (D)_8) + these.  (6,2), (7,3), (5,1) remain unproved.
## RESULT, ROUND 3 (rows; final 18:20) -- upper floors NOT closed; two new rigorous theorems that cut down the split cases
 Details and proofs: section R3 (R3.0 - R3.9).  (DI_5) remains open; the gap (with (D)) needs only "no (5,1) and no (6,2)".
 T1 [RIGOROUS, hand proof, R3.8] LEMMA SL_3: a 3 x 5 space all of whose 3 x 4 column deletions are level has dim <= 2
    (= (DI_4) at e = 0; sharp). Corollary: a 4 x 5 level space containing a full free row has dim <= 6.
 T2 [RIGOROUS, R3.9] THEOREM FL2*: let U be a subspace of 1^perp with U cap U' = 0, U' = (U + C1)^perp. Every 5 x 5 level space
    containing the split pair T_U = e_i (x) U (+) e_r (x) U' has  dim <= 10 - dim(U o U')  (U o U' = span of entrywise products).
    So dim <= 7 as soon as dim(U o U') >= 3. Consequences for the defect table:
      (a) NO (5,1) or (6,1) space contains e_i m^T with m non-isotropic and at most one zero entry   [split case of e = 1];
      (b) no (6,2) / (7,2) space has a row carrying its whole defect plane C when C is nondegenerate and dim(C o W) >= 3;
          no (7,3) space has a row carrying its whole defect space when w (W = Cw) is non-isotropic with <= 1 zero entry.
    Open split cases at e = 1: m isotropic; m supported on exactly three columns (bound 8 only). (Two-column m: verifyfl's TC5.)
    Sanity (numerical): fixed m = (1,2,-4,1,0): dim 7 found, dim 8 not; fixed full-support m: dim 6 found, dim 7 not; fixed
    generic 2-dim U: dim 6 reached (slowly), dim 7 not; unknown U of dim 2: dim 7 found (U in a coordinate hyperplane), dim 8 not.
 T3 [RIGOROUS, short] from the checked "4 x 5 level <= 7" (L_gct_215) via the defect construction (R3.1): every 3 x 5 level space has
    dim <= e + 3; every 5 x 5 level space meets {row r = 0} in dim <= 7, so a 9-dim level space has all row/column projections
    of rank >= 2 and (8,3), (8,4), (9,4) are excluded.  Lemma EC (R3.2): an equal-column level space M extends by e_i(e_a-e_b)^T
    with defect C(M) + C(e_a-e_b).  Tower Lemma (R3.3): after an untwisted deletable row, the next free part lies in the radical
    of the previous defect space.  Saturation principle for any row (R3.5).  Split-pair normal form FL2 (R3.6).
 T4 [what L_gct_215 contains, R3.0] a contradiction proof for dim 8 by the single-row parts u_i and pair ranks; no classification
    of 7-dim spaces; internal lemma: a 4 x 5 level space with two equal columns has dim <= 6.
 NUMERICAL ONLY: no 7-dim 4 x 5 level space found (calibrated; so (7,3), (7,2) are probably vacuous, but "<= 6" is unproved);
    (6,2): 0/37; EQ-induction census: the step "dim(L'/{y_a = y_b}) <= 1 for a suitable pair" FAILS on all four (6,3) examples
    (min 2, once 3) and on one (5,2) example, so target (2) as posed does not work; only the trade-off = (DI_5) itself holds.
 NOT DONE: (7,3), (6,2) in general; conjecture (D) for dim >= 8 (no progress beyond the saturation principle).
## RESULT, ROUND 2 (rows; task "prove (DI)"; written 15:30, final 15:36) -- (DI) PROVED for p = 3; for p = 4, 5 only on the orthogonal part
 (DI_p): for a (p-1) x q level space L', dim L' <= dim C(L') + p - 2.  (p = 5, q = 5 is what the gap needs, with (D).)
 R6 [RIGOROUS; section DI] THEOREM DI_3: every 2 x q level space L' has dim L' <= dim C(L') + 1; hence a 3 x q level space with a
    deletable row has dim <= q (sharp; the checked L156 gives q + 1). Proof: on the hyperplane of zero row sums the level
    conditions and the defect are DIAGONAL (columnwise elementary symmetric functions), then Rado (checked L171 / L157).
 R7 [RIGOROUS; new tools, any number of rows]
    LEMMA D: a linear space V of p x q matrices with sum_j prod_i (1 + x_ij) = q on V has dim <= q - 1 (Rado induction of the
       checked ThreeRowRado file, verbatim for p rows).  COROLLARY: in ANY 5 x 5 level space, a linear subspace all of whose
       elements have zero row sums and pairwise orthogonal rows has dim <= 4 (same for columns).
    THEOREM DDI: if sum_j e_i(col_j(Y)) = 0 on a linear space M of k x q matrices (i = 1..k) then
       dim M <= dim span{ (e_i(col_j Y))_j : Y in M, i <= k }.
    DELETION FORMULA (I1): C(Y)_j = sum_{S} (-1)^{|S|}|S|! N^{(R-S)}(J+Y) prod_{i in S}(1 + Y_ij); exact p_k formulas (I3).
    PROPOSITION O: for a 3- or 4-row level space L' and a linear M in L' with zero row sums and pairwise orthogonal rows (4 rows:
       also zero triple sums), dim M <= dim C(L'); so dim L' <= dim C(L') + codim M.
    All identities checked exactly in rational arithmetic (rows/di_ident.py).
 R8 [numerical census of the 29 example spaces, rows/orth_chk.py] 26 of 29 have row-sum rank q_s = 3 and L'_s := L' cap {row
    sums 0} of dimension exactly e with pairwise orthogonal rows and zero triple sums: for these Proposition O PROVES
    dim L' <= e + 3 (tight). The 3 others have non-orthogonal L'_s: (d,e,q_s,dim L'_s) = (4,1,2,2), (5,2,2,3), (6,3,3,3).
    Uniform form of the conjecture:  (DI_5')  dim L'_s <= e + 3 - q_s.
 R9 [RIGOROUS corollaries, section DI] (H) in a 3- or 4-row level space L' with e = dim C(L'): every single-row part has dim <= e and
    every TWO-ROW part has dim <= e + 1 (checked on 69 example spaces, 0 violations); so dim L' <= e + 1 + rank(projection of L' to
    the other rows), and in a (5,1) or (6,1) space every two-row part of L' has dim <= 2.
    (B') Gram identity |b_j(Y)|^2 = |s|^2 + 3 c_j^2 - 4 p_2(Y)_j on level 4 x 5 spaces (zeros' isometries B_j for every e).
    (TC) if C(L') is inside C(e_a - e_b): L'' := {Y in L' : y_a = y_b} is strongly level (dim <= 3 by SL) and
    dim L' <= 3 + (4 - dim zeta), zeta = {z : z(e_a - e_b)^T in L'} (e_2-isotropic).  [Does not yet exclude (5,1) for this m.]
 NOT PROVED: (DI_4), (DI_5) in general; (DI_5) for e = 1 (no (5,1)). Reason, precisely: for p = 5, e = 0 the statement IS
    Lemma SL, whose non-orthogonal DC parts (types I, II) need the cubic/quartic case analysis; the Rado/diagonal method
    cannot see the pairing terms (y_a.y_b)(y_c.y_d) of P_4. Exact set-up of the e = 1 case and of the split-free-row sub-case:
    section DI, "WHAT IS NOT PROVED".
## RESULT, ROUND 1 (rows; final 15:07) -- gap NOT settled (no proof of <= 8, no 8- or 9-dim level space). What is new:
 R1 [RIGOROUS, 3-line proof, section D] DEFECT CONSTRUCTION = the exact normal form of "deletable row" (repr's conjecture (D)).
    For a 4x5 matrix Y put p_k(Y)_j := P_k(Y minus column j) (k = 1..4, j = 1..5); for a 4x5 level space L' let
    C(L') := span{p_k(Y) : Y in L', k}  (inside 1^perp of C^5; e := dim C(L')).  Then
        L(L') := L' (+) e_r (x) (C(L') + C1)^perp       (L' placed in the rows != r)
    is a 5x5 LEVEL space of dimension dim L' + 4 - e with row r deletable; conversely a level L with deletable row r has a level
    4x5 projection L', dim L <= dim L' + 4 - e(L'), and L + e_r(x)(C(L')+C1)^perp is still level. e = 0 is zeros' free-row case.
    Hence:  (D) + (DI4): "dim L' - e(L') <= 4 for all 4x5 (and 5x4) level spaces"  ==>  the gap;  and an 8-dim level space with a
    deletable row exists  <=>  a 4x5 level space with (dim L', e) in {(5,1),(6,2),(7,3),(8,4)} exists (+ transposes).
 R2 [EXACT] explicit 7-dim level spaces WITHOUT a full free row or column, explained by R1 (free part of the deletable row 3-dim):
    (a) L_m = span{ e_2 m^T ; e_4 w^T (w.1 = w.m = 0) ; x e_2^T (x_0+x_1+x_3 = 0, x_2 = x_4 = 0) ; (1,1,-3,1,0)^T e_4^T },
        m = (m_0,m_1,m_2,m_3,0), sum m = 0: hand proof for all m (section D); integer polynomial identity perm(J+t) == 120
        checked for m = (1,2,-4,1,0), also with a shear c = 1 (rows/exact7.py). [L_m with c = 0 is of repr's product type,
        pattern (2,1 | 3,1) up to transpose: repr's files prod_*_{31000,22000,21100,11110} already contain free-line-free
        7-dim spaces numerically, so UPDATE 4's "every known 7-dim space contains a full free line" was not accurate.]
    (b) NOT of product type, DC part = ex1's plane, (r,d,r_A,r_B) = (5,2,2,3):  span{ u(e_0-e_3)^T, ubar e_1^T, ubar e_4^T
        (u = (1,w,w^2) on rows 0,1,3), (1,1,-3,1,0)^T e_2^T, e_4 w^T (w_0 = w_3, sum w = 0) }: exact identity in Z[w] (exact7b.py).
    Numerically (1e-13, two independent checkers, 27 spaces) 7-dim level spaces exist for (dim L', e) = (3,0), (4,1), (5,2), (6,3):
    free part of the deletable row of dim 4, 3, 2, 1. All 27 have exactly one deletable line and first-order extension space
    L + C(e_r 1^T - J/5) (dim 8), hence lie in no 8-dim level space. 14 of 15 (4,1) spaces contain the "split free row"
    e_i m^T (+) e_r(x){1,m}^perp with m = the defect line.
 R3 [numerical; seeded searches calibrated on the analogous existing transitions (5/12, 5/12, 1/9)] no 4x5 level space with
    (dim L', e) = (5,1), (6,2), (7,3) found (0/38, 0/29, 0/24; residual floors 4.1, 3.7, 2.4), none with (7,4) (0/12): no 8-dim
    level space with a deletable row found. Equal-row block classes mu = (4,1), (3,2), (3,1,1), (2,2,1): dim 8 not found
    (dim 7 is reached in (4,1), (3,1,1), (2,2,1)).
    UNIFORM LAW seen on three floors (q = 5): for (p-1) x 5 level L', dim L' - e(L') <= p - 2 with equality for every e
    (p = 3: (1,0),(2,1),(3,2),(4,3) exist, (2,0),(3,1),(4,2) do not; p = 4: (2,0),...,(5,3) exist, (3,0),...,(6,3) do not;
    p = 5: (3,0),...,(6,3) exist; (4,0) impossible by zeros' SL).  CONJECTURE (DI): dim L' - dim C(L') <= p - 2.
 R4 [RIGOROUS] Target (A) of my task is FALSE as stated: 5-dim degenerate level 4x5 spaces exist: (i) F_3 (+) C(e_1-e_2)e_j^T
    (three rows, contains a full free row), (ii) a 5-dim 4x4 level space (2n-3 type: free column + 2) padded with a zero column.
    Correct statement of the a_r = 1 branch: normal form (*) in section S; a_r = 1 does not imply deletable (L080, row 4).
    Side remark: the team's sol_n4_d5 is (to its 1e-4 subspace accuracy) free column 0 (+) 2-dim, column 0 deletable (error
    7e-6 against 0.8..1 for the other lines) -- it is NOT free-line-free (zeros' remark was a tolerance artefact).
 R5 [RIGOROUS] GENERALISED FK: perm restricted to L + CJ is 120 lambda^5, so every LINEAR subspace Y of {perm = 0} of codimension c
    meets a d-dim level space in dimension >= d + 1 - c; new instances Y = {row i in C(a e_j + b e_k), row i' in C(a e_j - b e_k)}.
 OPEN (precise): (DI) [already (DI4) suffices with (D)]; (D); in the branch a_r = 1 of a 9-dim L the three types of section S.
 BEST NEXT STEP: prove (DI) for p = 3 (2 x q; formulas in section D': C = span{a+b, A(a-b) + 2 a o b}) and then by induction along
    the tower (C(L') contains the free parts of all rows of L'; C'(Y2,v) = D(Y2)(1+v) for Y2 = the rows above); or classify the
    (4,1) spaces: with a split free row e_i m^T the condition is "m is an eigenvector of D(Y3) for all Y3 in the 3-row projection".
STATUS 14:25: read BRIEF + zeros/kbuild/lemmaz/hessmix/lowd. First observation (to be verified exactly): target (A) as
 literally stated ("degenerate level 4x5 space has dim <= 4") is FALSE: (i) F_3 (+) C(e_1-e_2)e_j^T (3x5, free row) and
 (ii) a 5-dim 4x4 level space (sol_n4_d5) padded with a zero column are 5-dim degenerate level 4x5 spaces. So (A) must be a
 classification into types, each killed separately inside a 9-dim L.
STATUS 14:41: (1) EXACT general construction ("defect construction", proof 3 lines, see section D below): for ANY 4x5 level space
 L' (rows != r), with p_k(Y)_j := P_k(Y minus column j) and defect space C(L') := span{p_k(Y): Y in L', k=1..4} (inside 1^perp),
     L(L') := L' (+) e_r (x) (C(L') + C1)^perp   is a 5x5 level space of dim  dim L' + 4 - dim C(L'),   row r deletable;
 and every level L with deletable row r is contained in L(L') for L' = its 4x5 projection (rho-part must be orthogonal to
 the p_k). Strongly level = defect 0 = zeros' free-row case. (2) NUMERICAL, verified with two independent checkers (level
 error 1e-13): 4-dim L' with 1-dim defect EXIST (10/25 random LM starts) and 5-dim L' with 2-dim defect exist (3/21): they give
 NEW 7-dim level spaces WITHOUT any full free row or column (free parts: row r 3-dim resp. 2-dim, all other lines <= 2).
 So "every 7-dim level space contains a full free line" is false, and Theorem FL does not cover all deletable-line spaces.
 Files rows/clm_p4_d4_defect1_s*.npy, clm_p4_d5_defect2_s*.npy (4x5 bases), rows/build7.py (builds + checks the 5x5 space).
 (3) (d,e) = (5,1) [would be an 8-dim level space]: 0/17 random starts -- NOT evidence (same LM misses the known 6-dim 4x5
 level spaces, (6,4): 0/4). Next: seeded searches with calibration, exact form of a (4,1) example.
STATUS 14:52: RESULT block written (R1-R5). Now: sections D (proofs), S (a_r = 1 normal form), then (DI) attempts.

## Section D. Deletable row: defect construction (rigorous)
 Notation: rows of a 5x5 matrix z as linear forms l_i = sum_j z_ij y_j in A = C[y_1..y_5]/(y_j^2), sigma = sum y_j, 'int' = top
 coefficient; perm(J+z) = int prod_i (sigma + l_i). For z = (z'; v) (z' = rows != r as a 4x5 matrix, v = row r):
        perm(J + z) = (1 + v) . C(z'),     C_j(z') := perm((J' + z') minus column j)  = 24 + sum_{k=1..4} (4-k)! p_k(z')_j .   (D1)
 sum_j p_k(z')_j = (5-k) P_k(z') (each k x k subpermanent avoids 5-k columns). Hence z' is 4x5-level <=> 1.C(z') = 120 <=> all
 p_k(z') lie in 1^perp;  and 'row r deletable in L' <=> the 4x5 projection L' of L is level <=> v.C(z') = 0 on L.
 PROPOSITION D. (a) L' a 4x5 level space, W := (C(L') + C1)^perp. Then L(L') = L' (+) e_r(x)W is level: for w in W,
   (1+w).C(z') = 1.C(z') + w.(C(z') - 24*1) + 24 w.1 = 120 + 0 + 0.   dim = dim L' + 4 - e.
 (b) L level, row r deletable, L' its projection, W_L := {w : e_r w^T in L}. For z in L and w in W_L: w.C(z') = 0 (compare z
   and z + e_r w^T in (D1)), so W_L is inside W = (C(L') + C1)^perp [w.1 = 0 from the linear part of v.C = 0] and
   dim L = dim L' + dim W_L <= dim L' + 4 - e.  Moreover L + e_r(x)W is again level (same computation), so maximal level
   spaces with deletable row r are exactly the graphs {(z', rho(z') + w)}: rho : L' -> 1^perp/W linear with rho(z').p_k(z') = 0.
   If e = 1 and L' is not strongly level then rho = 0 (rho(z').m * theta_k(z') = 0 with p_k = theta_k m, a product of two
   polynomials), i.e. L = L(L').
 (c) Equivalent 'two-form' statement: row r deletable <=> perm restricted to L + CJ + C e_r 1^T equals 120 mu lambda^4
   (lambda, mu the coordinates along [J'; 0] and e_r 1^T). Then {mu = 0} = (L' + CJ') (+) e_r(x)W_L is a linear space inside
   the permanent hypersurface of dimension dim L + 1.
 CONSEQUENCE. Under (D), max level dim = max over 4x5 (and 5x4) level L' of dim L' + 4 - e(L').  Dimension 8 needs
   (dim L', e) in {(5,1), (6,2), (7,3), (8,4)}, dimension 9 needs (6,1), (7,2), (8,3), (9,4); (d,0) with d >= 4 is excluded by
   zeros' Lemma SL. Degree-1 part: p_1(Y) = -(column sums of Y), so e >= rank of the column-sum map on L'.
   Degree 2: p_2(Y)_j = c_j^2 + s.y_j - |y_j|^2 (c = column sums, s = row sums, y_j = column j).
 PROOF THAT L_m IS LEVEL (R2). Y = a e_2 m^T + x e_2^T + t u e_4^T (u = (1,1,-3,1), rows 0..3): rows 0,1,3 are
   sigma + t y_4 + x_i y_2, row 2 is sigma + a mu - 3t y_4 (mu = sum m_j y_j). Since y_2^2 = 0 and sum x_i = 0,
   prod_{i=0,1,3}(sigma + t y_4 + x_i y_2) = (sigma + t y_4)^3 = sigma^3 + 3t sigma^2 y_4, and
   G = (sigma^3 + 3t sigma^2 y_4)(sigma + a mu - 3t y_4) = sigma^4 + a mu sigma^3 + 3 a t sigma^2 mu y_4.
   Coefficient of y_{[5]-j}: 24 - 6a m_j - 6at(m_j + m_4) [j != 4], 24 - 6a m_4 [j = 4]. With m_4 = 0: C(Y) - 24*1 = -6a(1+t) m.
   So L' is level with defect line Cm, and Prop. D(a) gives L_m (W = {1,m}^perp).   (x drops out: a block of rows that are
   equal except for a sum-zero vector in ONE column behaves like equal rows.)
 EQUAL-ROW PRINCIPLE (rigorous, same computation): if the rows of a block R (|R| = mu) of J + t are kappa + x_i y_c with sum_R x_i
   = 0 then prod_R = (sigma + kappa)^mu. So any level space L_mu inside {matrices with equal rows in the blocks of a partition
   mu of the rows} extends by (5 - #blocks) dimensions (one column c per block, all sum-zero vectors on the block).
   L080 / ex-types are mu = (4,1) and (3,1,1); L_m is mu = (3,1,1) with (kappa, a, b) = (t y_4, a mu - 3t y_4, w).
 Numerics for this section: rows/clm.py (holomorphic LM on a Grassmannian chart, analytic Jacobian, 1 s per start),
   run_clm.py, seeded.py, mult.py, build7.py, deletable.py, look.py, fam8.py; logs clm_*.log; solutions *.npy.
   CALIBRATION WARNING: unseeded LM does not find the known 6-dim 4x5 level spaces ((6,4): 0/4) nor converges fast on singular
   solutions; only the seeded negatives in R3 are calibrated (by the analogous successful transitions).
STATUS 14:56: more data. (a) 14 of the 15 (4,1) spaces found contain the split free row  e_i m^T (+) e_r(x){1,m}^perp  (the single-row
 element of L' is EXACTLY e_i m^T, m = the defect line; m always has a zero entry). (b) The 15th is of a second kind, exact form
 read off:  u(e_0-e_3)^T, ubar e_1^T, ubar e_4^T (u = (1,w,w^2) on rows 0,1,3), (1,1,-3,1,0)^T e_2^T, e_4 w^T (w_0 = w_3, sum w = 0);
 m = e_0 - e_3, (r,d,r_A,r_B) = (5,2,2,3), DC part = ex1's plane; no single-row element outside row 4. (c) L_m has first-order
 space of dim 8 (singular values 1.2 | 3e-14) for m = (1,2,-4,1,0), (1,i,-1,-i,0), (1,-1,0,0,0): no 8-dim level space contains
 L_m. (d) seeded 8-dim searches, second batch: (5,1) 0/23, (6,2) 0/15 (floors 4.1, 3.7). Totals: (5,1) 0/38, (6,2) 0/29.

## Section S. The branch a_r = 1 (row projection of dimension 4): normal form, what is true, what is open
 Setting: L level of dim l, row r, Ann_r = C n (sum n = 1), H = n^perp = pi_r(L), M = L_r (dim l - 4), M' its 4x5 part.
 Choose a linear section; then L + CJ = {(x' + Lam(v), v) : x' in M', v in C^5}, Lam : C^5 -> C^{4x5} linear, Lam(1) = J', and
        (*)   v . Phi(x' + Lam(v)) = 120 (n.v)^5      for all x' in M', v in C^5        (Phi = the five maximal-minor permanents),
 and conversely (*) defines a level space. [perm(lambda J + z) = 120 lambda^5 on L + CJ, lambda = n.v.]  By degree in v:
   deg 1: Phi(x') = 0 (zeros' CA2);  deg 2: S_x := DPhi(x') o Lam is a SKEW 5x5 matrix (cubic in x'), i.e. for every z in L + CJ:
          sum_{k != r} B_k(x') z_k = S_x z_r,  B_k = symmetric zero-diagonal matrix of 3x3 subpermanents of x' without row k
          (with z = J: (P_3(x' minus column j))_j = S_x 1);   deg 3, 4: v . D^2Phi(x')[Lam v, Lam v] = 0, v . D^3Phi(x')[(Lam v)^3] = 0;
   deg 5: the 5-dim space {(Lam v, v)} has perm = 120 (n.v)^5.
   Columnwise (v = t e_j): perm((x' + t Lam e_j) minus column j) = 120 n_j^5 t^4: each column-deleted image of M' is a 4x4
   space on which perm is constant on a translate (base point (Lam e_j)^(j)); useful only with extra information, because
   general base points allow big spaces (I + strictly upper triangular: 6-dim, perm == 1).
 a_r = 1 does NOT imply 'row r deletable': L080 has a_4 = 1 with n = (1,1,1,1,0)/4 and M = {u e_4^T : u_4 = 0, sum u = 0}.
 TYPES of M for a hypothetical 9-dim L (dim M = 5; a linear space inside the variety Z of 4x5 matrices with vanishing
 maximal minors lies in one irreducible component of Z; component list as quoted in NOTES-lemmaz from arXiv 2402.17839 --
 NOT re-proved here):
   (i) common zero row r': M is a 5-dim 3x5 level space and row r' is a linear function of row r on all of L. Example of such
       M: F_3 (+) C(e_1-e_2)e_j^T (then FL gives dim L <= 7). OPEN: other 5-dim 3x5 level spaces. My LM converges slowly
       (singular solutions, residual 1e-8) to spaces that do NOT contain a full free row (free parts of dims 2,1 / 1,1 and one
       single-column element) -- unresolved whether these limits are genuine (rows/long35.log, long35_s*.npy).
   (ii) common zero column c: M is a 5-dim 4x4 level space in the corner. The team's sol_n4_d5 (accurate only to 1e-4 as a
       subspace: singular solution) has row-projection ranks (1,2,2,1) and column ranks (3,2,2,2).  OPEN.
   (iii) no common zero line (inside the 3-row cone or the Kirkup component). lemmaz's K_new is a 2-dim example. OPEN.
   So the chain (A) => (B) of my task does not go through as stated; each of (i)-(iii) needs its own argument inside (*).
 GENERALISED FK (R5), proof: on L^ = L + CJ, perm = 120 lambda^5; a linear Y inside {perm = 0} of codimension c meets L^ in
   dimension >= l + 1 - c, and there lambda = 0. New instance: for rows i != i', columns j != k and (a:b) in P^1,
   Y = {row i in C(a e_j + b e_k), row i' in C(a e_j - b e_k)} (the two rows multiply to 0 in A; codim 8) meets a 9-dim level L in
   dim >= 2. With T := image of {z in L : rows i,i' supported on columns j,k} in C^{2x2} and L_{ii'} := L cap {rows i,i' = 0}:
   if dim L_{ii'} <= 1 then P(T) meets every line of one ruling of the quadric {perm_2 = 0} in P^3, so dim T >= 3 or T is a
   plane of the other ruling {(l, c D l)}; if L_{ii'} = 0 then T = C^{2x2}.  (Not exploited further.)
 (B)/(C) of the task, in the light of section D: if a 9- or 8-dim level space has a deletable row r then a_r = 1 + e >= 2
   (e = 0 is Theorem FL), L_r = L' and the minor-permanent map Phi : L' -> C(L') = Ann_r cap 1^perp is exactly p_4; the whole
   deletion vector C(z') - 24*1, not only its top part, stays in the fixed e-dim space. An 8-dim level space with a deletable
   row is EXACTLY one of: (5,1): L = L' (+) e_r(x){1,m}^perp, L' a 5-dim 4x5 level space with all p_k(Y) in Cm;  (6,2): L' 6-dim,
   defect plane, rho-twist allowed;  (7,3), (8,4).  Targeted searches for (5,1), (6,2): negative (R3).
STATUS 15:02: (a) (7,3) seeded from the four (6,3) spaces: 0/24 (floor 2.4). (b) MAXIMALITY CHECK (rows/maxchk.py): all 27 new spaces
 ((4,1): 15, (5,2): 8, (6,3): 4) are 7-dim, level (1e-13), with first-order extension space of dim exactly 8 and the extra
 direction = e_r 1^T - J/5 (cos = 1 to 1e-6; P_2 != 0): NO 8-dim level space contains any of them. Since L(L'_d) is inside
 L(L'_{d+1}) whenever both have the same defect space, none of the found (4,1) spaces lies in a (5,1) space, etc.
 (c) THE SAME DEFECT LAW ONE AND TWO FLOORS DOWN (rows/small_di.py, unseeded LM, small problems, 1 s per start):
     L' 2x5 -> 3x5:  (d,e) = (1,0),(2,1),(3,2),(4,3) all exist (16/16, 12/16, 13/16, 4/4)  [3x5 level of dim 5];
                     (2,0),(3,1),(4,2) [dim 6]: 0/15, 0/11, 0/6 (floors 10, 6.4, 4.9).
     L' 3x5 -> 4x5:  (2,0),(3,1),(4,2),(5,3) exist (12/16, 6/14, 4/10, 3/12)  [4x5 level of dim 6];
                     (3,0),(4,1),(5,2),(6,3) [dim 7]: 0/11, 0/7, 0/5, 0/8 (floors 7.8, 5.8, 4.6, 3.5).
     L' 4x5 -> 5x5:  (3,0),(4,1),(5,2),(6,3) exist [dim 7];  (4,0) impossible (zeros' SL, rigorous); (5,1),(6,2),(7,3): not found.
   CONJECTURE (DI_p), uniform: for a (p-1) x q level space L' (p <= q), with defect space C(L') in 1^perp of C^q spanned by the
   deletion vectors (P_k(Y minus column j))_j, k = 1..p-1:      dim L' - dim C(L') <= p - 2,
   with equality for every value of dim C(L') from 0 to q-2 (numerically, q = 5). Together with 'deletable line' at each
   floor this is exactly the p + q - 3 law; p = 2 is trivial (L' = U in 1^perp, C(U) = U), p = 5, e = 0 is zeros' Lemma SL.
   Easy exact facts: C(L') contains the free part W_i of every row i of L' (take Y = e_i w^T: p_1 = -w), and
   C'(Y'', v) = D(Y'')(1 + v), D(Y'')_{jk} = perm((J'' + Y'') minus columns j,k) (symmetric, zero diagonal), D(0) = 6(J - I) for
   3 rows; so perm(J + z) = (1 + z_r)^T D(z'') (1 + z_i) for any two rows i, r. If L' contains e_i m^T and C(L') = Cm then m is
   an EIGENVECTOR of D(Y''') for every Y''' in the projection of L' to the other three rows (L_m: D = 6(J-I) + 6t(J-I)_{0123}).
STATUS 15:06: RESULT block rewritten (R1-R5 final wording; relation to repr's product type; sol_n4_d5 remark; exact check of the
 second-kind example in Z[w]).
## Section D'. Formulas for the bottom floor (2 x q -> 3 x q), for whoever proves (DI) at p = 3
 L' in C^q x C^q, elements (a,b), A = sum a = -sum b, level <=> a.b = -A^2. Deletion vectors: p_1 = -(a+b),
 p_2 = A(a-b) + 2 a o b (o = entrywise product). In c = a+b, delta = a-b, D = sum delta: level <=> c.c - delta.delta + D^2 = 0,
 2 p_2 = D delta - delta o delta + c o c, polar form ((D delta' + D' delta)/2 - delta o delta' + c o c')/2.
 On L'_0 = {c = 0} = Delta_0: psi(delta_0, delta) = T_0 delta, T_0 = diag(D_0/2 - delta_0) + (1/2) delta_0 1^T, whose kernel is
 at most 1-dim when no entry of delta_0 equals D_0/2; so dim psi(delta_0, Delta_0) >= dim Delta_0 - 1 there. Missing for a
 proof of d <= e + 1: independence of this image from c(L') (and the degenerate entries). Strongly level (e = 0): d <= 1 (a_j
 in {0, A} for all j forces a = A e_j), i.e. L' = C (e_1 - e_2) e_j^T, giving F_3 (+) E_j.
 Hand check of (3,1) with b = 1, dim Delta_0 = 2: impossible (delta_1 o delta_1, delta_1 o (1/2 - delta_2), delta_2 o (1 - delta_2)
 all parallel to m force delta_1 = +-s on its support with sum 0 and delta_1.delta_1 = 0, so s = 0).
STATUS 15:09: final additions.
 (1) Relation between my assigned program (row projections, CA2) and deletability, exact: for ANY row r of a level L,
     dim L = dim L_r + 5 - a_r, so the gap is equivalent to "dim L_r <= a_r + 3 for one (hence every) row r". CA controls only the
     TOP degree part p_4 = Phi of the deletion vector on L_r (Phi(L_r) inside Ann_r cap 1^perp, dim a_r - 1); the pure 4x5
     statement "dim M <= dim span Phi(M) + 4 for 4x5 level M" is FALSE (F_3 (+) E_j: Phi == 0, dim 5). Deletability of row r is
     exactly the extra information that ALL p_k (k = 1..4) of L_r lie in Ann_r cap 1^perp; then the conjectural (DI) applies.
 (2) Closed-form (5,2) example: L' = the 5-dim 4x4 level space of 2n-3 type {e_3(e_a - e_2)^T (a=0,1), (e_b - e_3)e_3^T (b=0,1,2)}
     padded with a zero column 4 is a 5-dim degenerate level 4x5 space with 2-dim defect space (checked 1e-16), so
     L(L') is a 7-dim level 5x5 space whose deletable row has a 2-dim free part.
 (3) (5,2) solution clm_p4_d5_defect2_s2: C(L') = sum-zero vectors on columns {0,2,4}; rows 1 and 2 carry single-row elements
     m_1, m_2 in C(L') (mutually orthogonal), row r carries {w : w_0 = w_2 = w_4, sum w = 0}, and a 3-dim part lives in columns 1,3:
     a free row split over three rows.
 Files (all in rows/): lib.py, rect.py (scipy LM; slow, superseded), clm.py (solver), run_clm.py, seeded.py, mult.py, small_di.py,
   build7.py, deletable.py, maxchk.py, chk41.py, look.py, fam8.py, exact7.py, exact7b.py, ex_rows.py, calib1.py, long35.py; logs
   clm_*.log, long35.log; solutions clm_p4_d*_defect*_s*.npy, seed_d*_e*_t*.npy, di_p*_d*_e*_s*.npy, mult_*.npy.
STATUS 15:26 (round 2, new task "prove (DI)", budget to ~16:40): (DI) for p = 3 PROVED (via the checked L157 / Rado L171);
 new rigorous tools: deletion formula (I1), diagonal lemma D for ANY number of rows, diagonal defect inequality DDI; (DI) for
 p = 4, 5 proved only for the "orthogonally centred" part of L'; the remaining part is exactly where zeros' case analysis of
 Lemma SL lives (e = 0), so no short proof of (DI4) can avoid it. Details in section DI below.

## Section DI. The defect inequality: what is proved (round 2)
 Notation (any q >= 2): a k x q matrix Y has rows y_1..y_k in C^q and columns col_j(Y) in C^k; X = J + Y.
   N^{(R)}(X) := sum over injections f : R -> [q] of prod_{i in R} X_{i f(i)}  (R a set of rows; N^{(empty)} = 1);
   Y (or a linear space of such Y) is LEVEL if N^{(all rows)}(J + cY) is constant in c, i.e. P_1(Y) = ... = P_k(Y) = 0;
   deletion vector C(Y)_j := N^{(all rows)}((J+Y) minus column j) = (q-1)_k + sum_{i=1..k} (q-1-i)_{k-i} p_i(Y)_j,
   p_i(Y)_j = P_i(Y minus column j);  C(L') := span{p_i(Y) : Y in L', 1 <= i <= k}  (inside 1^perp when L' is level);
   beta_B(Y) := sum_j prod_{i in B} Y_ij (block sums; beta_{i} = row sum, beta_{ii'} = y_i.y_i');
   e_i^col(Y) := (e_i(col_j(Y)))_j in C^q (columnwise elementary symmetric functions), sum_j e_i^col(Y)_j = sum_{|B|=i} beta_B(Y).
   (DI_p): for a (p-1) x q level space L',  dim L' <= dim C(L') + p - 2.      [p x q level space L(L') has dim <= p + q - 3]
 All identities below were checked EXACTLY in rational arithmetic at random points (rows/di_ident.py: (I1) for k = 2,3,4;
 (I2); (I3) including the four deletion vectors).

 (I1) DELETION FORMULA [rigorous]. For every k x q matrix X and column j:
        N^{(R)}(X minus column j) = sum_{S subset R} (-1)^{|S|} |S|! N^{(R-S)}(X) prod_{i in S} X_ij.
   Proof. N^{(R)} is linear in column j: N^{(R)}(X) = N_j^{(R)} + sum_{i in R} X_ij N_j^{(R-i)} (N_j = injections avoiding j; at
   most one row uses column j). Solve recursively: N_j^{(R)} = sum over sequences (i_1..i_r) of distinct rows of
   (-1)^r X_{i_1 j}...X_{i_r j} N^{(R - {i_1..i_r})}.  QED
   So C(Y) = sum_S (-1)^{|S|}|S|! N^{(R-S)}(J+Y) X_S (X_S = entrywise product of the rows 1 + y_i, i in S): the deletion vector
   lies in the Hadamard algebra generated by the rows, with coefficients the level polynomials of the row subsets.
 (I2) Moebius form [rigorous, standard]: P_i(Y) = sum_{|R|=i} sum over set partitions pi of R of prod_{B in pi} (-1)^{|B|-1}(|B|-1)! beta_B(Y).
   Hence if all row sums of Y vanish: P_2 = -sum_j e_2(col_j), P_3 = 2 sum_j e_3(col_j) (any k), and
   if moreover the rows are pairwise orthogonal (beta_{ii'} = 0) and k <= 5:  P_i(Y) = (-1)^{i-1}(i-1)! sum_j e_i(col_j(Y)), i >= 3
   (a set of <= 5 rows has no partition into blocks of size >= 3 except the trivial one).
 (I3) Deletion vectors [rigorous; beta_B(Y minus column j) = beta_B(Y) - prod_{i in B} Y_ij]:
   k = 2, row sums 0, level:           p_1 = -e_1^col,  p_2 = 2 e_2^col.
   k = 3, row sums 0, level:           p_1 = -e_1^col,  p_2 = 2 e_2^col,  p_3 = -6 e_3^col + kappa(Y),
                                        kappa(Y) := (y_2.y_3) y_1 + (y_1.y_3) y_2 + (y_1.y_2) y_3.
   k = 4, row sums 0, rows pairwise orthogonal, level:  p_i = (-1)^i i! e_i^col (i <= 3),
                                        p_4 = 24 e_4^col - 2 sum_i beta_{R-i}(Y) y_i     (beta_{R-i} = triple sums).

 LEMMA D (diagonal lemma, any number of rows) [rigorous; uses Rado's theorem = checked L171; the 3-row case is the core of
   the checked L157, file Gct/Helpers/ThreeRowRado.lean, whose induction I repeat verbatim for p rows].
   Let V be a linear space of p x q matrices (q >= 1) with  F(x) := sum_{j=1..q} prod_{i=1..p} (1 + x_ij) = q  for all x in V
   (equivalently sum_j e_i(col_j(x)) = 0 on V for i = 1..p). Then dim V <= q - 1.
   Proof. Strong induction on q. Suppose dim V >= q. For a column set U let S(U) be the span in V^* of the entry functionals
   g_ij (i in [p], j in U). (a) If dim S(U) >= |U| for all U: Rado gives i(j) with (g_{i(j),j})_j linearly independent, so some
   x in V has x_{i(j),j} = -1 for all j; every column product vanishes, F(x) = 0 != q. (b) Otherwise take U nonempty with
   dim S(U) < |U| and V_U := {x in V : columns in U vanish}; dim V_U = dim V - dim S(U) >= q - |U| + 1 and V_U, as matrices on
   the remaining q' = q - |U| columns, has F = q'. If q' = 0 then V_U = 0, contradiction; else induction gives dim V_U <= q' - 1,
   contradiction.  QED
 THEOREM DDI (diagonal defect inequality) [rigorous]. Let M be a linear space of k x q matrices with sum_j e_i(col_j(Y)) = 0
   for all Y in M, i = 1..k, and T(M) := span{e_i^col(Y) : Y in M, 1 <= i <= k}. Then  dim M <= dim T(M).
   Proof. T(M) is in 1^perp. Put W0 := (T(M) + C1)^perp (dim q - 1 - dim T(M)) and V := {(Y; w) : Y in M, w in W0} ((k+1) x q).
   e_i(col_j(Y;w)) = e_i(col_j Y) + w_j e_{i-1}(col_j Y), so sum_j e_i(col_j(Y;w)) = 0 + w.e_{i-1}^col(Y) = 0 for i = 1..k+1
   (e_0^col = 1, e_{k+1}(col_j Y) = 0). Lemma D: dim M + q - 1 - dim T(M) <= q - 1.  QED
   [Numerical sanity for k = 2 (rows/g1test.py): (dim M, dim T) = (1,1),(2,2),(3,3),(4,4) found 14/14 each; (2,1),(3,2),(4,3): 0/38.]

 THEOREM DI_3 [RIGOROUS]. Every 2 x q level space L' satisfies dim L' <= dim C(L') + 1. Consequently a 3 x q level space
   with a deletable row has dim <= q (sharp: F_3 (+) C(e_1-e_2)e_j^T; the checked L156 gives q + 1 without deletability).
   Proof. M := {Y in L' : row sum of row 1 = 0} has codimension <= 1 and both row sums vanish on it (P_1). On M,
   sum_j e_2(col_j) = y_1.y_2 = beta_1 beta_2 - P_2 = 0, so M satisfies the hypothesis of DDI (k = 2), and by (I3)
   T(M) = span{p_1(Y), p_2(Y) : Y in M} = C(M), a subspace of C(L'). DDI: dim M <= dim C(L').  QED
   Second proof (uses the checked L157 directly): M (+) e_3 (x) (C(L') + C1)^perp is a ROW-CENTRED 3 x q level space
   (P_2 = -(a.b + (a+b).w) = 0, P_3 = w.p_2(Y) = 0), so dim M + q - 1 - e <= q - 1.
   Checked on 101 numerically found 2 x 5 level spaces (rows/di_p2_*.npy, g1_*.npy): |row sums|, |P_2|, |P_3| of (a,b,w) <= 2.2e-10,
   dim M + dim W <= 4 and d <= e + 1 in all; formulas p_1, p_2 exact.

 PROPOSITION O ("orthogonally centred part") [rigorous]. Let L' be a k x q level space, k = 3 or 4, and M a LINEAR subspace of L'
   all of whose elements have zero row sums and pairwise orthogonal rows (for k = 4 also: all triple sums beta_T(Y) = 0, or
   merely sum_i beta_{R-i}(Y) y_i in C(L') + C1). Then dim M <= dim C(L'), hence  dim L' <= dim C(L') + codim(M in L').
   Proof. By (I2) M satisfies the hypothesis of DDI; by (I3) T(M) is inside C(L') (+ the stated correction).  QED
   So (DI_4) [resp. (DI_5)] holds for every L' that has such an M of codimension <= 2 [resp. <= 3]. The row-sum-zero part
   L'_s := L' cap {all row sums 0} always has codimension q_s <= p - 2, so (DI_p) is EQUIVALENT to
        (DI_p')   dim L'_s <= dim C(L') + (p - 2 - q_s),
   and Proposition O proves it when the pair products y_i.y_i' vanish on a subspace of L'_s of codimension <= p - 2 - q_s.
   For k = 3 the exact defect is  C(L'_s) = span{e_1^col, e_2^col, 6 e_3^col - kappa}  against  T(L'_s) = span{e_1^col, e_2^col, e_3^col}:
   DDI gives  dim L'_s <= dim(C(L') + span kappa(L'_s)),  kappa = A y_1 + B y_2 + C y_3 with A + B + C = 0 the pair products.

 WHAT IS NOT PROVED, AND WHY IT IS HARD (precise).
  (a) (DI_4) (3 x q -> 4 x q) and (DI_5) = (DI4)/(DI) for the gap are NOT proved in general. The missing statement is (DI_p')
      for the NON-orthogonal part of L'_s. For p = 5, e = 0 this is exactly zeros'/verifyfl's Lemma SL (there L'_s = N, the DC
      part, q_s = q, and (DI_5') reads q + dim N <= 3): the spaces N of types I, II (chi_1 (x) C^3, ex1's plane) have
      non-orthogonal rows, T^diag = 0 fails for them, and they are excluded/bounded only by the long cubic+quartic case
      analysis S4-S8 of NOTES-verifyfl. So any proof of (DI_5) contains a proof of SL; a short uniform argument of the
      Rado type cannot exist unless it also handles the pairing terms  sum over pairings (y_a.y_b)(y_c.y_d)  of P_4.
  (b) e = 1, p = 5 (no (5,1), i.e. no 8-dim level space with a deletable row whose free part is 3-dim): NOT proved. Exact
      set-up for whoever continues (all rigorous, derived as in verifyfl S2/S5 with one extra quadratic form):
      C(L') = Cm. tau(y_j) = kappa(Y) m_j (kappa a linear form); L'_0 := ker kappa (codim <= 1, columns in V_4). On L'_0:
        (C2') q_j(Y) := <y_j,y_j> - <s,y_j> = theta(Y) m_j,   (C3') T_j(Y) = theta_3(Y) m_j,   (C4') [Y^(j)] = theta_4(Y) m_j,
      theta, theta_3, theta_4 forms of degree 2, 3, 4 on L'_0 (p_2 = -q_j, p_3 = 2 T_j, p_4 = bracket). For a section
      sigma -> Y(sigma), B_j := 2A_j - iota:  <B_j s, B_j s'> = <s,s'> + 4 m_j theta_S(s,s'),  sum_j B_j = -3 iota,
      <z_j, B_j s> = 2 m_j theta(Y(s),Z) for Z in N := L'_0 cap DC, and <z_j,z'_j> = m_j theta(Z,Z') on N.
      Neutral columns (m_j = 0; present in all 15 examples): the deletion of column j of L' is a 4 x 4 LEVEL space and
      column j of N is an isotropic line. On a theta-isotropic subspace all of SL's quadratic steps hold verbatim; what is
      missing is the classification of N (analogue of S3-S4: columns of N are no longer isotropic, the five column forms are
      proportional to ONE form theta) and the cubic/quartic exclusions with the unknowns theta_3, theta_4.
      Sub-case "split free row" (14 of 15 examples): if e_i m^T is in L' then dim L' = 1 + dim L''' (L''' the 3-row projection)
      and the conditions are (E1) D(Y''') m in Cm, (E2) D(Y''')(1 + l(Y''')) in 24*1 + Cm, with D(Y''') v = deletion vector of
      the 4-row matrix (J + Y'''; v) given by (I1); claim to prove: dim L''' <= 3.
  (c) e = 2, 3 (p = 5): nothing beyond Proposition O and the numerics of R3.
STATUS 15:34: census + two more exact facts added below; RESULT ROUND 2 block is at the top.
 CENSUS (numerical, rows/orth_chk.py, kappa_chk.py): (i) 4 x 5 examples (29): 26 have q_s = 3 and L'_s of dimension exactly e with
   pairwise orthogonal rows and zero triple sums (Proposition O proves dim L' <= e + 3 for them, with equality); the other 3
   are (d,e,q_s,dim L'_s) = (4,1,2,2), (5,2,2,3), (6,3,3,3) with non-orthogonal L'_s (all satisfy dim L'_s = e + 3 - q_s).
   (ii) 3 x 5 examples (25): 23 have q_s = 2, L'_s orthogonal of dimension e; 2 are strongly level DC planes (d,e,q_s) = (2,0,0),
   non-orthogonal, with dim(C + span kappa) = 2 = dim L'_s (DDI tight). So on both floors the conjecture reads
        (DI_p')   dim L'_s <= e + (p - 2 - q_s),     and is PROVED whenever L'_s is orthogonally centred (then dim L'_s <= e).
 LEMMA B' (generalises verifyfl's Lemma B to every e; rigorous; identity checked to 5e-14 at random points, rows/gram_chk.py).
   For a 4 x 5 matrix Y with zero total sum: c_j = sum of column j, s = row sums, b_j(Y) := 2(y_j - (c_j/4) 1) - s in V_4. Then
        |b_j(Y)|^2 = |s(Y)|^2 + 3 c_j(Y)^2 - 4 (p_2(Y)_j - P_2(Y)),     sum_j b_j(Y) = -3 s(Y).
   So on a level space L' the linear maps b_j : L' -> V_4 have Gram forms  G_j = s^*(dot) + 3 c_j (x) c_j - 4 p_2(.,.)_j ,
   where (c_j)_j and (p_2(.,.)_j)_j are C(L')-valued; for every w in C(L')^perp:  sum_j w_j (|b_j|^2 - |s|^2 - 3 c_j^2) = 0.
   e = 0: B_j isometries (zeros). Consequences for e = 1 (C = Cm): G_j = s^*(dot) + 3 m_j^2 kappa^2 - 4 m_j Pi has rank <= 3 for
   each j; for a NEUTRAL column (m_j = 0) b_j is an isometry of s(L'), and if q_s = 3 then column j of every Z in L'_s is 0.
   Example of use: if m = e_a - e_b and q_s = 3 then L'_s is inside {z (e_a - e_b)^T : e_2(z) = 0} (level forces e_2(z) = 0;
   the column sums (sum z)(e_a - e_b) are allowed), so dim L'_s <= 2 and dim L' <= 5 only -- NOT enough to exclude (5,1).
   [CORRECTION 15:36 of a first version of this remark that claimed dim L'_s <= 1.] Indeed
       M_2 := { z (e_0 - e_1)^T : z in span((1,w,w^2,0), (1,1,1,-1)) }
   is an exact (2,1) space (level error 1e-15, defect line C(e_0 - e_1)) with non-orthogonal rows. Searches STARTED at M_2 plus
   random vectors converge to (3,1) 6/8 and (4,1) 11/24 spaces, (5,1) 0/12 (floor 4.2) [numerical]; the solver moves all basis
   vectors and the limits do NOT contain M_2 (their zeta is 0, rows/twocol_chk.py), so whether M_2 itself extends is untested.
STATUS 15:37: rigorous corollaries of Theorem DI_3 for the upper floors (the "k-row part" hierarchy).
 COROLLARY H (rigorous). Let L' be a k x q level space (k = 3 or 4), e = dim C(L'), W = (C(L') + C1)^perp (dim q - 1 - e).
   (H1) the single-row part U_i := {u : e_i u^T in L'} lies in C(L'):  dim U_i <= e.            [p_1(e_i u^T) = -u]
   (H2) every TWO-ROW part L'_{ii'} := {Y in L' : only rows i, i' nonzero} has  dim <= e + 1.
        Proof: L'_{ii'} is a 2 x q level space and L'_{ii'} (+) e_r (x) W is a 3 x q level space (a subspace of L(L')) in which
        the row carrying W is deletable; by the corollary of Theorem DI_3 its dimension is <= q.  QED
   (H3) consequently  dim L' <= e + 1 + min over pairs {i,i'} of rank(projection of L' to the rows other than i, i'),
        and in a 5 x 5 level space L with a deletable row r every 3-row part containing row r has dim <= 5 (L156 alone: 6).
   The same statement one floor up, "every three-row part of a 4 x 5 level L' has dim <= e + 2", is equivalent to (DI_4) for the
   3-row parts; (DI_5) is the statement for the 4-row part: conjecturally "the k-row parts have dim <= e + k - 1".
   For the hypothetical 8- and 9-dim spaces: in a (5,1) space every two-row part of L' has dim <= 2, in a (6,1) space too, so
   the projection of L' to any two rows has rank >= 3 (resp. >= 4).
STATUS 15:39: LEMMA TC (two-column defect line; rigorous, uses the verified Lemma SL; sanity-checked on the 7 example spaces with
 m = e_a - e_b, rows/twocol_chk.py: the kernel L'' below has defect 0 to 1e-11, one LM-limited case 4e-8).
   Let L' be a 4 x 5 level space with C(L') inside C(e_a - e_b). Put zeta := {z in C^4 : z (e_a - e_b)^T in L'} and
   eps(x,z) := tau(x) tau(z) - x.z (the polar form of 2 e_2 on C^4, nondegenerate). Then
   (i)  e_2 vanishes on zeta (level), so dim zeta <= 2;
   (ii) y_a - y_b is eps-orthogonal to zeta for every Y in L'   [add the a- and b-coordinates of the polarised deletion form
        p_2(Y,Z)_j = c_j(Y)c_j(Z) + (s(Y).z_j + s(Z).y_j)/2 - y_j.z_j, which are opposite because p_2(Y,Z) is a multiple of e_a - e_b];
   (iii) L'' := {Y in L' : y_a = y_b} is STRONGLY level (C_j = 24 for j != a,b because those coordinates of C(L') vanish;
        C_a = C_b by the symmetry of Y and C_a + C_b = 48), hence dim L'' <= 3 by Lemma SL;
   (iv) dim L' <= 3 + dim{y_a - y_b : Y in L'} <= 3 + (4 - dim zeta).
   So a (5,1) space with defect line C(e_a - e_b) is L'' (+) (2 more dimensions) with L'' a 3-dim strongly level space having
   two equal columns, or has dim L'' <= 2 and at least 3 independent differences y_a - y_b; if zeta is 2-dim (Lagrangian) then
   L' = zeta (x) (e_a - e_b)^T (+) L''. Finishing this sub-case needs only zeros' list of 3-dim strongly level spaces
   (types (3,0), (2,1), (1,2)) with two equal columns and the cubic cross conditions -- not done.
STATUS 15:41 (round 2 final): proved = Theorem DI_3, Lemma D, Theorem DDI, Proposition O, Corollary H, Lemma B', Lemma TC, identities
 (I1)-(I3) (all rigorous; identities exact in rational arithmetic). Numerical only = the census (orth_chk, kappa_chk), existence
 of the (d,e) types, all "not found" statements. (DI_4), (DI_5), and (DI_5) at e = 1 remain open; the obstruction is identified
 (pairing terms / non-orthogonal row-centred part, i.e. the generalisation of the type I-IV analysis of Lemma SL).
 Round-2 files (rows/): di_ident.py (exact identities), g1test.py, small_di.py, orth_chk.py, kappa_chk.py, gram_chk.py,
 twocol_chk.py, cand_M2.npy, di_p*_d*_e*_s*.npy, g1_p2_*.npy.

STATUS 17:52 (ROUND 3 started 17:38, budget to ~19:08; targets: upper floors (6,2), (7,3); EQ-induction; (D)).
## Section R3 (round 3)
 R3.0 WHAT THE CHECKED PROOF Outside/L_gct_215.lean ("4 x 5 level <= 7") CONTAINS (read: definitions lines 128-170, final assembly).
   It is a proof by contradiction for an 8-dim L (no classification of 7-dim spaces). Invariants: u_i := dim of the single-row
   part of L in row i (my U_i), p_ij := rank of the projection to rows i, j. Case tree (abbrevs vJ, MidCase, mI, eI, HighPair, vK):
     some u_i >= 4 (full free row)           -> impossible                       [vJ]
     some u_i in {2,3}                        -> impossible                       [MidCase, the longest part]
     some u_i = 1                             -> there is a 7-dim level M with two EQUAL COLUMNS  [mI], and
                                                 no 7-dim level space has two equal columns        [eI]
     all u_i = 0: some p_ij = 7 -> impossible [HighPair];  all p_ij <= 6 -> impossible [vK].
   Useful checked by-products: (eI) a 4 x 5 level space with two equal columns has dim <= 6; the u_i = 1 case is treated through
   the 3-row projection (their W L, K3, S3), i.e. exactly the "split free row" normal form.
 R3.1 CONSEQUENCES OF "4 x 5 level <= 7" THROUGH THE DEFECT CONSTRUCTION (rigorous).
   (a) every 3 x 5 level space L'' has dim L'' <= e(L'') + 3   [L(L'') = L'' (+) e_4 (x) W'' is 4 x 5 level of dim d'' + 4 - e''];
       this is (DI_4) with 3 in place of 2. Every three-row part of a 4-row level L' has dim <= e(L') + 3.
   (b) a level space L of 5 x 5 matrices has dim(L cap {row r = 0}) <= 7 for every row (column): in a 9-dim level space every row
       and column projection has rank >= 2 (a_r <= 3), an 8-dim one has no zero row or column. In the defect table this
       removes (8,4), (8,3), (9,4): with (D), the gap follows from "no (6,1) and no (7,2)", hence from "no (5,1) and no (6,2)".
 R3.2 LEMMA EC (equal columns; rigorous; checked on 74 cases, level error 2e-14, defect as predicted).
   Let M be a 4 x 5 level space with y_a = y_b for all Y in M, and E_i := e_i (e_a - e_b)^T for ONE row i. Then M (+) C E_i is level
   and C(M (+) C E_i) = C(M) (+) C(e_a - e_b).
   Proof. N is linear in row i: N(J + Y + tE_i) = N(J+Y) + t (N_{i,a} - N_{i,b}), N_{i,c} = injection sum of the other rows into
   the columns != c; the other rows have equal columns a, b, so N_{i,a} = N_{i,b}. Same computation for the deletions:
   C_j unchanged for j != a,b, and C(Y + tE_i) - C(Y) = t nu_i(Y)(e_b - e_a), nu_i = perm of (rows != i, columns != a,b), nu_i(0) = 6. QED
   Consequences: (i) dim M <= 6 (also eI); (ii) with verifyfl's Lemma EQ: for a (d,e) space L' and a pair (a,b) with C(L') not inside
   {c_a = c_b}, M := L'_ab = {y_a = y_b} is a (d - delta, <= e-1) space (delta := dim{y_a - y_b}) and M (+) C E_i is a
   (d - delta + 1, <= e) space containing the two-column split row E_i; delta >= 1 whenever d = 7.
   (iii) a (7,3) space with a moving pair of delta = 1 contains a (6, <= 2) space; a (6,2) space with delta = 1 contains a (5, <= 1)
   space; so in a MINIMAL counterexample to (DI_5) every moving pair has delta >= 2.
 R3.3 TOWER LEMMA (rigorous; checked on 9 spaces L(L''), L'' 3 x 5 with nondegenerate defect: all have defect 4).
   Let L'' be a (p-1) x q level space, W'' = (C(L'') + C1)^perp, L' := L(L'') = L'' (+) e_p (x) W''. Then C(L') contains C(L'') + W''
   [deletion vector of (Y'', w) is Delta(Y'')(1 + w), Delta(0) = (q-2)_{p-2}... (J - I) up to a constant, so w itself is a defect vector],
   hence the next free part W' := (C(L') + C1)^perp lies in C(L'') cap W'' = rad(C(L'')) (the radical of the dot form on C(L'')):
   W' is totally isotropic, dim W' <= 2, and W' = 0 when C(L'') is nondegenerate.
   So a 5 x 5 level space with two successively deletable ROWS (both untwisted) has free parts W'' (row 4) and W' (row 5) with
   W' inside rad C(L''): the 6-dim 4 x 5 spaces L(L'') built from my 3 x 5 examples all have defect 4 and give nothing in 5 x 5;
   the (6,3) spaces (defect 3) are not of this kind (their deletable line, if any, is a column, or the defect below is isotropic).
 R3.4 NUMERICS (not proofs). (a) 7-dim 4 x 5 level spaces: none found (unseeded 0/10, floor 0.5; seeded at the five known 6-dim
   spaces 0/15, floor 0.5, with the calibration "5-dim subspace of a 6-dim space -> 6-dim" 3/15 + slow singular convergences;
   equal-row classes (3,1), (2,2), (2,1,1): 6 reached, 7 not). So numerically max = 6 = 4+5-3, the checked 7 is not sharp, and
   (7,3), (7,2) would be vacuous; but there is no known 7-dim space to compute a defect on, and I cannot prove "<= 6".
   (b) (6,2): 0/8 more starts seeded at ALL known 6-dim spaces (floor 3.8; same code moves rc45 (e = 4) to a (6,3) space).
   (c) EQ-induction census (rows/eq_chk.py; delta_ab = dim{y_a - y_b}, only pairs moving C(L')):
        (4,1): a pair with delta = 1 and L'_ab strongly level of dim 3 exists in 23 of 24 spaces;
        (5,2): a "tight" pair (delta = e - e(L'_ab)) exists in 7 of 8; one space (clm_p4_d5_defect2_s9) has min delta = 2;
        (6,3): NO tight pair in 4 of 4: min delta = 2 (three spaces, L'_ab of type (4,2)) and 3 (one space).
      So the proposed induction step "dim(L'/{y_a = y_b}) <= 1 for a well-chosen pair" FAILS on existing extremal spaces
      (already "<= 2" fails once), and "<= 2" would not close the induction anyway (it gives d <= 2e + 3). What holds in all
      examples is only the trade-off (d' - e') + (delta - (e - e')) <= 3 for L'_ab of type (d', e'), which is (DI_5) itself.
 R3.5 SATURATION PRINCIPLE FOR ANY ROW (rigorous, 1 line; generalises the defect construction to non-deletable rows).
   For a p x q level space L and a row i let Pi_i := projection of L to the other rows (NOT level in general) and
   C^(i)(L) := span{C(Y) - C(0) : Y in Pi_i} mod C1 (deletion vectors of the (p-1)-row projections). Because N is linear in row i,
        N(J + z + e_i v^T) = N(J + z) + v . C(pi_i z),
   so L + e_i (x) (C^(i)(L) + C1)^perp is level, the single-row part U_i of L lies in (C^(i)(L) + C1)^perp, with equality when L is
   maximal (or saturated). Row i is deletable iff Pi_i is level, and then C^(i)(L) = C(Pi_i) is the defect space.
   In L_gct_215 the case u_i = 1 is exactly this: e_i v^T in L iff v is orthogonal to the deletion vectors of the 3-row projection;
   their sub-lemmas show that in an 8-dim 4 x 5 level space v must be a two-column vector e_a - e_b and then the other three rows of
   every element have equal columns a, b (abbrev oT), which produces the 7-dim equal-column space excluded by eI.
STATUS 17:59: split-pair normal form (FL2) and searches.
 R3.6 SPLIT FREE ROW PAIRS: NORMAL FORM "FL2" (rigorous; all conditions checked on 5 numerical examples to 1e-13, resp. to the
   1e-7 accuracy of the singular LM solutions).  For U inside 1^perp put U' := (U + C1)^perp and T_U := e_i (x) U (+) e_r (x) U'
   (a 4-dim 2-row level space; U = 0 is the full free row). Let L be level and contain T_U. Then L cap {only rows i, r} = T_U,
   dim L = 4 + dim Pi (Pi = projection of L to the other three rows), and with Delta(Y'')_{jk} := perm((J + Y'')[all 3 rows; columns
   != j,k]) (symmetric, zero diagonal, Delta(0) = 6(J - I)), perm(J + z) = (1 + z_r)^T Delta(z'') (1 + z_i). So L is level iff
   for all Y'' in Pi with lifts a = row i mod U, b = row r mod U':
     (i)   Delta(Y'') U inside U + C1   (equivalently Delta(Y'') U' inside U' + C1);
     (ii)  Delta(Y'')(1 + a) in U + C1,   Delta(Y'')(1 + b) in U' + C1;
     (iii) (1 + b)^T Delta(Y'') (1 + a) = 120.
   Degree 1: a = -c mod (U + C1), b = -c mod (U' + C1) (c = column sums of Y''), and c o U inside U + C1, c o U' inside U' + C1
   (o = entrywise product): the column sums of the 3-row part act on U and U' modulo constants.
   U = 0 is Theorem FL (dim Pi <= 3 by Lemma SL). CONJECTURE FL2: dim Pi <= 3 for every U (then every level space containing a
   split pair has dim <= 7). In the defect table: a (5,1) space containing e_i m^T is the case dim U = 1 (verifyfl's split case);
   a (6,2) space in which some row of L' carries the whole defect plane (U_i = C(L')), in particular every (6,2) space that
   is an untwisted double row tower, is the case dim U = 2; by the Tower Lemma a double row tower needs U' = W inside rad, i.e.
   U = U' Lagrangian.
 R3.7 NUMERICS for FL2 (rows/splitpair.py: unknown U, U' in Grassmannian charts, dpp extra vectors with independent 3-row parts;
   positives are verified level spaces, negatives are calibrated only by the dim-7 hits of the same code):
     dim U = 1: dim 7 found 4/7, dim 8: 0/14 (floor 0.2);     dim U = 2: dim 7 found 2/8 (NEW: free parts (2,2) on two rows, U
     nondegenerate, U (+) U' = 1^perp, exactly one deletable row, (r,d,r_A,r_B) = (7,0,3,4)), dim 8: 0/14 (floor 0.2).
     [dim U = 0, dim 7: 0/6 converged within 250 iterations (one at 4e-2, slow): this instance is NOT calibrated.]
   A first reading of these (2,2) spaces with too strict a rank tolerance gave "first-order space of dim 7, no deletable line";
   that was wrong: the singular value at the cut is 1e-6 (LM accuracy of singular solutions), the deletion test gives one
   deletable row at 4e-7 against 0.7..2 for the other nine lines. Conjecture (D) is NOT contradicted.
STATUS 18:08: TWO NEW RIGOROUS RESULTS: Lemma SL_3 (strongly level 3 x 5 spaces have dim <= 2) and Theorem FL2* (split pairs).
 R3.8 LEMMA SL_3 (rigorous hand proof; formulas checked to 4e-13 in rows/sl3_chk.py): a linear space Pi of 3 x 5 matrices all of
   whose 3 x 4 column deletions are level has dim <= 2.  [= (DI_4) at e = 0; sharp: ex1's plane; the LM search found none of
   dim 3.]  COROLLARY: a 4 x 5 level space containing a full free row has dim <= 6 (it is F (+) Pi by zeros' reduction).
   Proof. u := (1,w,w^2), ub its conjugate; V_3 = span(u,ub) = sum-zero vectors of C^3; <u,u> = <ub,ub> = 0, <u,ub> = 3;
   u o u = ub, ub o ub = u. (a) P_1 of the deletions: all column sums vanish, so Y = u p^T + ub r^T with p, r in C^5, row sums
   s = (sum p) u + (sum r) ub. Toolbox (kbuild): P_2(u p^T + ub r^T) = 3(p.r - sum p sum r), P_3 = 6(e_3(p) + e_3(r)), any number of
   columns. Hence strongly level <=> for all j:
        (S2_j)  r_j(sum p - 2p_j) + p_j(sum r - 2r_j)... in the normalised form  q_j := |eta_j|^2 - <s,eta_j> = 0  (eta_j = column j),
        (S3_j)  e_3(p without p_j) + e_3(r without r_j) = 0;   summing (S3_j): E := e_3(p) + e_3(r) = 0.
   (b) S := s(Pi) inside V_3 (dim q <= 2), N := Pi cap {s = 0}, dim Pi = q + dim N. Polarising q_j as in verifyfl S5: with a section
   Y(sigma), eta_j = A_j sigma, B_j := 2A_j - id: <B_j sigma, B_j sigma'> = <sigma,sigma'> and <zeta_j, B_j sigma> = 0 for Z in N.
   q = 2: B_j is an isometry of V_3, so zeta_j = 0: N = 0, dim Pi = 2.
   (c) On N every column lies in C u or C ub (the two isotropic lines of V_3): Z = u lam^T + ub mu^T with disjoint supports,
   sum lam = sum mu = 0. (S3_j) with E = 0 reads lam_j (lam.lam - 2 lam_j^2) = 0 on the support of lam (e_2(lam) = -lam.lam/2), so on
   the linear space N each coordinate lam_j is 0 or satisfies lam_j^2 = lam.lam/2; summing, exactly two coordinates are active
   and lam = l (e_a - e_b); likewise mu = l' (e_c - e_d). So dim N <= 2, and dim N = 2 iff N = span{u(e_a-e_b)^T, ub(e_c-e_d)^T}.
   (d) (q, dim N) = (1,2) is impossible: let Y_0 = u p^T + ub r^T have s != 0. Cross conditions with u(e_a-e_b)^T and ub(e_c-e_d)^T:
   r_a = r_b = (sum r)/2, p_c = p_d = (sum p)/2; then q_a = 0 gives (sum p)(sum r) = 0; by the symmetry u <-> ub take sum r = 0,
   t := sum p != 0: r_a = r_b = 0, p_c = p_d = t/2, p_a + p_b + p_e = 0. On Y_0 + N (p_a -> p_a + lam, p_b -> p_b - lam, r_c -> r_c + mu,
   r_d -> r_d - mu, identities in lam, mu): (S3_a) - (S3_b) gives e_2(p) = t(p_a+p_b) - p_a^2 - p_a p_b - p_b^2, i.e. p_e = -t/4;
   q_e = 3 r_e (2p_e - t) = 0 gives r_e = 0, so r = (0,0,nu,-nu,0); then E = (3t/4) p_a p_b - t^3/16 and
   (S3_c) = E - (t/2) e_2(p) + t^3/8 with e_2(p) = p_a p_b + 3t^2/16: E = 0 forces p_a p_b = t^2/12, (S3_c) forces p_a p_b = t^2/16.
   Contradiction. So dim Pi = q + dim N <= 2.  QED
 R3.9 THEOREM FL2* (rigorous; identities exact in rows/fl2_ident.py; conditions verified on 5 numerical examples; consistent with
   all examples). Let U be a subspace of 1^perp in C^5 with U cap U' = 0, U' := (U + C1)^perp (i.e. the dot form is nondegenerate on U),
   and let L be a 5 x 5 level space containing the split pair T_U = e_i (x) U (+) e_r (x) U'. Then
        dim L <= 10 - dim(U o U'),         U o U' := span{u o u' : u in U, u' in U'}  (entrywise products; a subspace of 1^perp).
   In particular dim L <= 7 whenever dim(U o U') >= 3, and <= 6 when U o U' = 1^perp.
   Proof. Notation of R3.6. (1) L cap {rows i,r only} is a 2 x 5 level space containing the 4-dim T_U, hence equals it
   (2 x q level <= q-1): dim L = 4 + dim Pi. (2) Degree-1 part of (i): u'^T Delta_1(Y'') u = 4 c.(u o u') with c = column sums of
   Y'' [Delta_1 u = -2S u + 4 c o u - 2(c.u)1, S = sum c]. So c(Y'') lies in (U o U')^perp, which contains 1. Let Pi_0 := {Y'' in Pi :
   c(Y'') in C1}; codim of Pi_0 in Pi is <= dim (U o U')^perp - 1 = 4 - dim(U o U'). (3) Degree-1 part of (ii): u'.(a + c) = 0 and
   u.(b + c) = 0, so on Pi_0: a in U + C1, b in U' + C1; subtracting elements of T_U, every Y'' in Pi_0 has a unique lift
   z = (Y''; alpha 1; beta 1) in L, alpha, beta linear forms. (4) perm(J + z) = (1+alpha)(1+beta) 1^T Delta(Y'') 1 = 120 identically on
   the linear space Pi_0; a product of polynomials equal to a nonzero constant has constant factors: alpha = beta = 0, and then
   P_1 gives c = 0 on Pi_0. (5) Now (ii) says Delta(Y'')1 lies in (U + C1) cap (U' + C1) = C1 (+) (U cap U') = C1, and
   1^T Delta 1 = 120, so Delta(Y'')1 = 24*1: all 3 x 4 deletions of Y'' are level, Pi_0 is strongly level, dim Pi_0 <= 2 (SL_3).
   (6) dim L = 4 + dim Pi <= 4 + 2 + 4 - dim(U o U').  QED
   Values of dim(U o U'): dim U = 1, U = C m with m.m != 0: 3 - max(|Z(m)| - 1, 0), Z(m) = zero set of m (so 3 iff m has at most
   one zero entry); dim U = 3: the same with U' = C m'; dim U = 2: 4 for generic U, 3 in the two (2,2) examples found (U or U'
   inside a coordinate hyperplane), in which the bound 7 is attained; for L_m (one zero entry) the bound 7 is attained too.
   COROLLARIES for the defect table (L(L') contains T_U as soon as L' contains e_i (x) C(L')):
   (a) NO (5,1) OR (6,1) SPACE CONTAINS e_i m^T WITH m NON-ISOTROPIC AND AT MOST ONE ZERO ENTRY  (split case of (DI_5) at e = 1).
       Remaining split cases at e = 1: m isotropic (U inside U'); m supported on exactly 3 columns (bound 8 only);
       two-column m is verifyfl's TC5.
   (b) no (6,2) or (7,2) space L' has a row carrying the whole defect plane (U_i = C(L')) when C(L') is nondegenerate with
       dim(C(L') o W) >= 3; no (7,3) space has a row carrying C(L') when C(L') is nondegenerate with dim(C(L') o W) = 3 (max possible).
   (c) with SL_3: every level space containing a full free row lies one floor down too: 4 x 5 level with a full free row <= 6.
STATUS 18:14: sanity runs for FL2* done (rows/fl2star_chk.py, fl2gen_chk.py): fixed m = (1,2,-4,1,0): dim 7 found 2/5, dim 8 0/3
 (floor 0.8); fixed m = (3,1,-2,5,-7) (full support): dim 6 found 2/5, dim 7 0/5 (floor 0.3) -- suggests that for full-support m the
 true bound is 6 (i.e. kappa = 0: the column sums of the 3-row part are constant), which would explain why the defect line m of
 every known (4,1) space has a zero entry; not proved. RESULT ROUND 3 block written at the top.
 Round-3 files (rows/): lev45.py, eq_chk.py, r3_chk.py, splitpair.py, fl2gen_chk.py, fl2star_chk.py, fl2_ident.py (exact), sl3_chk.py,
 split_k*_d3_s*.npy (7-dim spaces with split pairs), rc45.npy.
 R3.10 WHAT IS LEFT OF THE SPLIT CASE AT e = 1 AFTER FL2* (set-up for whoever continues; rigorous as far as stated).
   m supported on exactly three columns, zeros z, z' (m.m != 0): (U o U')^perp = span(1, e_z, e_z'), so c(Y'') = gamma 1 + kappa e_z +
   kappa' e_z'; the proof of FL2* gives b = 0 (row r), a = alpha 1 - kappa e_z - kappa' e_z' (row i, mod C m), alpha = -gamma, and
   Pi_0 = {kappa = kappa' = 0} strongly level (dim <= 2); L' = C e_i m^T (+) Lambda, Lambda = {(Y''; alpha 1 - kappa e_z - kappa' e_z')} a
   level 4 x 5 space with (E1) Delta(Y'') m in span(1,m), (E2) m . Delta(Y'')1 = 0, (E3) Delta(Y'')(1 + a) in span(1,m).
   To exclude (5,1) one must show that kappa and kappa' cannot both be nonzero independent forms when dim Pi_0 = 2
   (for the naive candidate with two column vectors (1,1,1,.)e_z^T, (1,1,1,.)e_z'^T the cross term -6 sigma^2 kappa^2 kills levelness).
   m isotropic (U inside U'): step (5) of the proof only gives Delta(Y'')1 in span(1,m), i.e. Pi_0 is a 3-row level space with defect
   line C m; one needs "dim Pi_0 <= 2" there (true for L_m with isotropic m), which is a 3-row statement at e = 1 with the extra
   condition (i).  Full-support m: numerics suggest the sharper bound 6 (kappa = 0).
STATUS 18:20 (round 3 final): see RESULT ROUND 3 at the top. Rigorous this round: SL_3, FL2*, R3.1-R3.3, R3.5, R3.6 (normal form).
 Numerical only: R3.4, R3.7 and the sanity runs. Not achieved: (6,2), (7,3) in general; (D).

STATUS 18:36 (ROUND 4 started 18:20, budget to ~19:50; targets: induction on e via hyperplanes, structure of extremal spaces, (D)).
## Section R4 (round 4)
 Conventions: an (d,e) space is a 4 x 5 level space L' with dim L' = d and defect space C = C(L') of dim e; W_1 := C^perp (contains 1),
 W = W_1 cap 1^perp; U_i := {u : e_i u^T in L'} (single-row parts, u_i := dim U_i); a column n is NEUTRAL if every vector of C
 vanishes at n (e_n in W_1, i.e. C_n(Y) == 24 on L'); C_2 := span{e_a - e_b : e_a - e_b in C} (the "two-column part" of C).
 (DI_5;e): every (d,e') space with e' <= e has d <= e' + 3.  Known: (DI_5;0) = Lemma SL (verified).
 R4.1 HYPERPLANE LEMMA (rigorous, 2 lines; generalises verifyfl's Lemma HYP). Assume (DI_5; e-1) and let L' be an (e+4, e) space.
   Then every subspace K of L' has e(K) >= min(e, dim K - 3); in particular EVERY hyperplane H of L' is an extremal (e+3, e)
   space with the SAME defect space C(H) = C(L'), and every subspace of codimension 2 has defect space C or a hyperplane of C.
   Proof. e(K) <= e. If e(K) <= e-1 then (DI_5; e-1) gives dim K <= e(K) + 3.  QED
 R4.2 CONSTRAINTS ON SINGLE-ROW PARTS (rigorous).  For every (d,e) space: (a) U_i inside C (H1); (b) U_i perp U_k for i != k
   [P_2(e_i u^T + e_k u'^T) = -<u,u'>]; (c) sum_j u_j u'_j u''_j = 0 for u, u', u'' in U_i, U_k, U_l with i,k,l distinct [P_3];
   (d) u_i + u_k <= e + 1 for i != k [Corollary H2: the two-row part has dim <= e + 1].
 R4.3 LEMMA RS-HYP (rigorous; uses (d), and for e = 3 the checked iterated Fermat lemma L067 on power sums).
   Assume (DI_5; e-1), e in {1,2,3}, and let L' be an (e+4, e) space. Then a generic hyperplane H of L' is NOT fully row-split,
   i.e. sum_i U_i(H) != C.   [So: if every extremal (e+3,e) space with defect space C were fully row-split, no (e+4,e) space
   with defect space C would exist.]
   Proof. For generic H, U_i(H) is a hyperplane of U_i(L') (or 0), so dim sum_i U_i(H) <= sum_i (u_i - 1)_+ with u_i = u_i(L').
   e = 1: u_i <= 1, the sum is 0. e = 2: the sum is >= 2 only if u_i = u_k = 2 for two rows, contradicting (d). e = 3: by (d) the sum
   is >= 3 only if three rows have u = 2; by (b) and nondegeneracy of the dot form on the 4-dim space 1^perp the three planes
   coincide with one totally isotropic plane Lam; by (b), (c) the power sums p_1, p_2, p_3 vanish on Lam, so 3 dim Lam <= 5 (L067):
   contradiction.  QED
 R4.4 CENSUS OF EXTREMAL SPACES (numerical; rows/r4_census.py, r4_c52.py; 44 old + 24 new (5,2) spaces, 15 of the new ones seeded at the
   two NON-split (4,1) spaces).  "Extremal spaces are always fully row-split" is FALSE:
     (4,1): 22 row-split (C = C m carried by e_i m^T), 2 with no single-row element and C = C(e_a - e_b);
     (5,2): 29 fully row-split (u = (1,1,0,0): 18, u = (2,0,0,0): 11), and 3 with NO single-row element and C = V_S, |S| = 3;
     (6,3): 2 fully row-split (u = (3,0,0,0), FS type); 10 with sum U_i of dim 1 only and C = V_S, |S| = 4.
   (V_S := sum-zero vectors supported on the column set S.)  What holds in ALL 68 spaces:
        (LAW)   C = sum_i U_i + C_2      (the defect space is spanned by single-row parts and two-column vectors),
   and in every space that is not fully row-split, C = V_S with |S| = e + 1, i.e. the 4 - e columns outside S are NEUTRAL
   (the maximal possible number of neutral columns for defect dimension e). [One LM-limited file gives rank 3 > e for sum U_i + C_2;
   tolerance artefact.]  Neutral columns are exactly the deletable columns of L' (deleting column n leaves a level 4 x 4 space),
   so these (6,3) spaces are the "alternating towers" predicted by the Tower Lemma: row r of L deletable, then a COLUMN of L'.
   Also: the defect line m of every row-split (4,1) space has a zero entry = a neutral column (and fixed full-support m only reach
   dim 3, round 3): in all examples an extremal L' has a deletable line of its own (a neutral column or a deletable row).
 R4.5 THE CHAIN (NC_k) (statement; two ends are theorems).  (NC_k): a 4 x 5 level space with k neutral columns has dim <= 7 - k.
   k = 4 (then all five deletions are level): Lemma SL.   k = 3: verifyfl's TC5 (defect line e_a - e_b).   k = 0: the checked
   L_gct_215.   k = 2 (would exclude the column-type (6,2)) and k = 1 (would exclude the column-type (7,3)): OPEN.
   Reduction of (NC_1) to 4 x 4 statements (rigorous): if column n is neutral, Q := L' minus column n is a 4 x 4 level space and
   N(J + (q | x)) = 24 + (1 + x).M(q), M(q)_i := level polynomial of q minus row i (3 x 4), sum_i M_i = 96; so with
   C^col(Q) := span{M(q) - 24*1} (inside 1^perp of C^4, e^col := its dimension) the single-column part X_n of L' lies in
   (C^col(Q) + C1)^perp and dim L' <= dim Q + 3 - e^col(Q)  (the transposed defect construction). Hence
        (NC_1)  <=  "every 4 x 4 level space Q has dim Q <= e^col(Q) + 3";
   e^col = 3 is the checked L_gct_214 (dim Q <= 6); e^col = 0 reads "a 4 x 4 level space all of whose rows are deletable has
   dim <= 3" (attained by a free row); e^col = 1, 2 need dim Q <= 4, 5.
 R4.6 WHAT WOULD CLOSE (DI_5) BY INDUCTION ON e (precise, given R4.1 - R4.5).  Let L' be an (e+4, e) space of minimal e; every
   hyperplane is extremal with the same C. Suppose (LAW) holds for all extremal spaces. With e_2 := dim C_2 (a property of C, the
   same for all hyperplanes) a generic hyperplane H needs dim sum_i U_i(H) >= e - e_2, hence sum_i (u_i(L') - 1)_+ >= e - e_2.
     e = 1: e_2 = 0 impossible (R4.3); e_2 = 1 is TC5.  So (5,1) <= (LAW) for (4,1) spaces [= verifyfl's dichotomy].
     e = 2: e_2 = 0 impossible (R4.3); e_2 = 1 forces a row with U_i = C: excluded by verifyfl's FS when C is nondegenerate
            [degenerate C with exactly one two-column vector: open]; e_2 = 2: C = V_{abc} (two neutral columns: (NC_2)) or
            C = span{e_a - e_b, e_c - e_d} (one neutral column and a two-column structure: open).
     e = 3: e_2 <= 2 forces, by R4.2(d), rows with (u_i) = (3) [FS, C nondegenerate] or two/three rows with u = 2 etc. (finite list,
            not worked out); e_2 = 3: C = V_{abcd} ((NC_1)) or C = V_{abc} + C(e_d - e_e) (no neutral column: open).
   So the extra statements are: (LAW) for extremal spaces, (NC_1), (NC_2), and the finitely many mixed/degenerate patterns of C.
STATUS 18:56: second half of round 4: lifting lemma, (NCOL), calibrated (NC) searches, 4x4 data, (D) reduced to dim 7. Sections R4.7 - R4.12.
 R4.7 LIFTING LEMMA (rigorous, elementary).  Let F_1, .., F_m be sets of polynomial functions on a vector space; a linear subspace K
   "has property i" if every f in F_i vanishes identically on K. If a linear space L has none of the m properties, there is t in L
   such that NO linear subspace of L through t has any of them (so the generic subspace of every dimension k >= 1 has none).
   Proof. Choose f_i in F_i with f_i not identically 0 on L; the product f_1...f_m is not identically 0 on L; take t with
   f_1(t)...f_m(t) != 0.  QED.   "Row r deletable" (pi_r(L) level: P'_k(pi_r t) = 0, k = 1..4) and "column n neutral" are of this form.
   COROLLARY D-UP: if every level space of dimension d has a deletable line, so has every level space of dimension >= d.
     Hence (D) <=> (D)_7 := "every 7-dim level space has a deletable row or column", and (D) for dim >= 8 FOLLOWS from (D)_7;
     an 8-dim level space without deletable line would contain an open dense family of 7-dim level subspaces without one.
   COROLLARY C-UP (with R4.1): assume (DI_5; e-1). Every property of the defect space that holds for all extremal (e+3, e) spaces
     holds for every (e+4, e) space (all its hyperplanes are extremal with the SAME defect space).
 R4.8 (NCOL): THE DEFECT SPACE OF AN EXTREMAL SPACE LIES IN A COORDINATE HYPERPLANE   [NUMERICAL, 0 exceptions].
   Statement (NCOL_e): every extremal (e+3, e) space, e = 1, 2, 3, has a NEUTRAL COLUMN n (C inside e_n^perp; equivalently L' minus
   column n is a level 4 x 4 space Q; equivalently W contains 1 - 5 e_n, i.e. the 5 x 5 space L(L') contains e_r (1 - 5 e_n)^T, i.e.
   L(L') + CJ contains the matrix "J with row r replaced by 5 e_n^T").
   Evidence: (i) all 87 extremal spaces of rows/ (rows/ext_chk.py): (d,e,#neutral columns) = (4,1,1): 13, (4,1,2): 8, (4,1,3): 3,
   (5,2,1): 25, (5,2,2): 19, (6,3,1): 19 [so every known (6,3) space has C = V_S, |S| = 4, W = C(1 - 5e_n)]; NONE has a deletable ROW
   (3 x 5 rest level).  (ii) independent sample (rows/ncol_ext.py): the 33 seven-dim 5 x 5 level spaces found by repr, numerics,
   lowd, split, methods, dc5: each has a deletable line, and the rest L' always has a neutral line of the other kind
   ((3,0): 17, (4,1): 3, (5,2): 6, (6,3): 5; two files needed the rank cut 1e-3 because they are LM-limited).  (iii) with the defect
   line fixed WITHOUT zero entry no (4,1) space was ever found (verifyfl 0/39; rows round 3: fixed full-support m reaches only dim 6
   for L). Non-extremal spaces need not have one ((3,1) spaces with full-support m exist), so (NCOL) is an extremality statement.
   So: EVERY KNOWN 7-DIM LEVEL SPACE IS A DOUBLE TOWER over a 4 x 4 level space Q: delete a row, then a column (or transposed).
   REDUCTION (rigorous, by C-UP): (DI_5)  <=  (NCOL_e) and (NC'_e) for e = 1, 2, 3, where
        (NC'_e): a 4 x 5 level space with a neutral column and defect dimension e has dim <= e + 3.
   [Induction on e: (DI_5;0) is SL; given (DI_5;e-1) and (NCOL_e), every (e+4,e) space has a neutral column, excluded by (NC'_e).]
 R4.9 CALIBRATED SEARCHES for spaces with neutral columns (rows/nc_search.py, ncdef_search.py; residual < 1e-9 = found) [NUMERICAL]:
     k = 2 neutral columns:  dim 5: 12/25 found (all e = 2);   dim 6: 0/22 (best residual 2.2)          -> supports (NC_2)
     k = 1 neutral column:   dim 6:  7/29 found (all e = 3);   dim 7: 0/25 (best residual 1.5)          -> supports (NC_1)
     k = 1 and e <= 1:       dim 4:  5/11;  dim 5: 0/8 (best 4.2)        k = 1 and e <= 2:  dim 5: 3/5;  dim 6: 0/15 (best 3.2)
   so (NC'_1), (NC'_2), (NC'_3) are supported at the usual (uncertified) level. The 19 new spaces are in rows/nc_d*_k*_s*.npy.
   NEGATIVE: "a column-centred 4 x 5 level space has dim <= 3" (which would give (DI_5) at once, because the column-sum map
   Y -> c(Y) = -p_1(Y)/6 is LINEAR with image inside C, so dim L' <= e + dim ker c) is FALSE: column-centred level spaces of dim 4
   exist (rows/cc_search.py: 5/60, e = 2 or 3; dim 3: 30/30 with e = 4).  The exact statement is dim ker c <= 3 + e - rank c.
 R4.10 THE TRANSPOSED DEFECT CONSTRUCTION AND THE 4 x 4 DATA.
   Rigorous. Let column n of L' be neutral, Y = (q | x), Q := {q} (level 4 x 4), X_n := {x : (0|x) in L'}, M_i(q) := level polynomial of
   the 3 x 4 matrix (J+q minus row i) (sum_i M_i = 96 on Q), M^(j)_i(q) := perm_3((J+q) minus row i, column j), C^col(Q) :=
   span{M(q) - 24*1} (inside 1^perp of C^4, dim e^col <= 3), e^row(Q) := the usual defect of Q (column deletions). Then
     (a) C_j(Y) = (1+x).M^(j)(q) (j != n);  L' level <=> sum x = 0 and x.(M(q) - 24*1) = 0;  the row-sum map of Q has image in C^col(Q);
     (b) X_n inside (C^col(Q) + C1)^perp, so dim L' = dim Q + dim X_n <= dim Q + 3 - e^col(Q)  [dim Q <= 6 by the checked L_gct_214];
     (c) PADDING LEMMA: a 4 x 4 level space with e^col = 0 (or e^row = 0) has dim <= 3   [(Q^T | 0) is a strongly level 4 x 5 space: SL];
     (d) hence (NC'_3) [= (NC_1)]  <=  no 4 x 4 level space with (dim Q, e^col) = (5,1) or (6,2)  (the 4 x 4 copy of the defect problem).
   Numerical (rows/q44_chk.py, all 87 extremal spaces, every neutral column; 9 LM-limited cases read off in the limit):
        e^row(Q) = e(L'),     dim X_n = 3 - e^col(Q),     dim Q = e^row(Q) + e^col(Q),
   with (dim Q, e^col, e^row) = (2,1,1), (3,2,1), (4,3,1), (3,1,2), (4,2,2), (5,3,2), (4,1,3), (5,2,3), (3,0,3), (2,0,2).  So every known
   7-dim level space is  L = Q (+) [column n: 3 - e^col(Q)] (+) [row r: 4 - e^row(Q)]  with  dim Q = e^row(Q) + e^col(Q):
   the total is 7 IDENTICALLY, and 8 would need a 4 x 4 level space with dim Q > e^row + e^col in this position.
   Test of the symmetric inequality on 5 x 5 spaces (rows/sym_chk.py; e_row, e_col <= 4 := dimensions of the spans of the column- resp.
   row-deletion vectors of L): among 90 level spaces of other agents, dim L <= e_row + e_col holds in 89, with EQUALITY (3+4 or 4+3)
   for 36 of the 39 seven-dim ones (the 3 others are LM-limited); it FAILS for methods/sp_circ4.npy: C * circ(1, i, -i, -1) padded by a zero
   row and column is a level line with ALL TEN line deletions level (e_row = e_col = 0). So "dim L <= e_row(L) + e_col(L)" (which
   would give 8 for 5 x 5, 6 for 4 x 4, 4 for 3 x 3) is false as it stands; the correct form must account for doubly strongly level
   parts (not found). [C circ4 (+) full free column is a (4,3) space, exact check: not extremal, no contradiction.]
 R4.11 TARGET (2), conjecture (D) for dim >= 8: NOT proved. What is rigorous: D-UP (R4.7): (D)_7 => (D)_8 => (D)_9, and (D) <=> (D)_7.
   (D)_8 and (DI_5) together are EQUIVALENT to the gap statement at 8 ("no 8-dim level space"): a deletable row r of an 8-dim L gives
   pi_r(L) of type (8-z, <= 4-z), i.e. (7,<=3), (6,<=2), (5,<=1) ((8,.) and (4,0) are excluded); conversely vacuous. So (D)_8 is
   not a lemma on the way but half of the problem. What Lemma C + (Z3) + R3.1 give for an 8-dim L without assuming (D): for every row
   r, L_r := L cap {row r = 0} is a 4 x 5 level space of dim 3 + a_r in {4,..,7} (a_r <= 4), e(L_r) >= 1, z_r <= 4 - e(L_r) <= 3, and for
   r != r' dim(L_r cap L_r') >= 1; under (DI_5): e(L_r) >= a_r, z_r <= 4 - a_r. None of this forces row sums == 0 on L. I found no
   argument; the realistic route is (D)_7 (a statement about 7-dim spaces, testable: 39 + 33 known spaces, 0 exceptions).
 R4.12 WHAT WOULD CLOSE (DI_5) NOW (sharpest form found).  By R4.8:  (NCOL_1,2,3) + (NC'_1,2,3).   Compared with R4.6 this replaces
   (LAW) and the list of mixed/degenerate patterns of C by ONE statement about C ("C lies in a coordinate hyperplane"), and puts all
   remaining cases into the 4 x 4 world: L' = (Q | x), x in the affine fibre over q cut out by x.(M(q) - 24*1) = 0, sum x = 0.
   Known cases of (NC'): (NC'_1) with two-column m (TC5); (NC'_e) when one row carries a nondegenerate C (FS).  Open: everything else.
 R4.13 DIRECT TEST OF (NCOL_3) WITH THE DEFECT SPACE FIXED (rows/fixC_search.py) [NUMERICAL, calibrated only for e = 3]:
   defect space required inside a fixed 3-dim C0 of 1^perp:  C0 = e_0^perp cap 1^perp: dim 6 found 4/19;  C0 generic (no neutral column):
   dim 4: 2/5, dim 5: 1/37, dim 6: 0/46 (best residual 2.4).  For e = 2 the same test is NOT calibrated (a generic plane inside
   e_0^perp cap 1^perp gave 0/12 at dim 5: the known (5,2) planes are special, in line with (LAW)), so no claim is made there.
STATUS 19:05: RESULT ROUND 4 written at the top. Rigorous this round: R4.1 - R4.3, R4.7, R4.10(a)-(d), reduction R4.8.
   Numerical only: R4.4, (NCOL), R4.9, the 4 x 4 data of R4.10, R4.13.  Not proved: (6,2), (7,3), (D)_8.
 R4.14 THEOREM NCOL-S (RIGOROUS; (NCOL_1) in the split non-isotropic case).  Let L' be a 4 x 5 level space with 1-dim defect space C m,
   <m,m> != 0, containing a single-row element e_i m^T.
     (a) If m has no zero entry, then dim L' <= 3.   [So a split (4,1) space with non-isotropic m HAS A NEUTRAL COLUMN.]
     (b) In general: for every Y in L' the column sums c_j(Y'') of the three rows != i are equal for all j with m_j != 0; and on
         N := L' cap {<y^i, m> = 0} (strongly level, verifyfl's THEOREM SPLIT) row i is supported on the zero set of m when m has
         exactly one zero n; then N cap {row i = 0} is a strongly level 3 x 5 space of dim exactly 2 if dim L' = 4.
   Proof. Notation of verifyfl R3.1: <w, C(Y)> = Per(1+y^1,..,1+y^4, w) (symmetric 5-linear), D_i(Y) the symmetric zero-diagonal matrix
   with (D_i)_jk = perm_3((J+Y) minus row i, columns j,k); it depends only on Y'' (rows != i). Since Y + lambda e_i m^T is in L' and
   C(.) - 24*1 is in C m:  D_i(Y) m = mu(Y) m on L';  <m, C(Y)> = mu(Y) <y^i, m>, so N is strongly level, dim N >= dim L' - 1.
   Degree-1 part (Y -> tY): D^(1)(Y) m is in C m, and (exact formula, rows/fl2_ident.py)  D^(1)(Y) m = -2S m + 4 c o m - 2(c.m) 1,
   S, c = total sum and column sums of Y''.  Hence  4 c_j m_j - 2(c.m) = (mu_1 + 2S) m_j  for all j.            (*)
   (a) m_j != 0 for all j: (*) reads c_j = alpha + (c.m)/(2 m_j), alpha := (mu_1+2S)/4; multiplying by m_j and summing,
   c.m = alpha sum m_j + 5 (c.m)/2 = 5(c.m)/2, so c.m = 0 and c(Y'') = alpha(Y) 1 on L' (alpha a linear form).  On N all column
   sums of Y vanish (the linear part of C(tY) = 24*1), so y^i = -c(Y'') = -alpha(Y) 1.  If alpha != 0 on N, take Y_1 in N with
   alpha(Y_1) = 1: row i of J + Y_1 is zero, all 4 x 4 column-deletion permanents vanish, contradicting C(Y_1) = 24*1.  So row i
   vanishes on N, and then C_j(Y) = N_{3x4}((J+Y'') minus column j) = 24: N is a strongly level 3 x 5 space, dim N <= 2 by Lemma SL_3
   (R3.8).  dim L' <= 3.
   (b) If m_n = 0, (*) at j = n gives c.m = 0 and (*) at j != n (m_j != 0) gives c_j = alpha. If n is the only zero: y^i = -alpha 1 - delta e_n
   on N; alpha(Y_1) = 1 would make row i of J + Y_1 a multiple of e_n and C_n(Y_1) = 0: so alpha = 0 on N, row i of N lies in C e_n,
   and N cap {row i = 0} has dim >= dim N - 1 and <= 2 (SL_3).  QED
   Numerical confirmation of every step (rows/ncol1_chk.py): on all 27 split non-isotropic (4,1) spaces (1, 2 or 3 zeros of m) the column
   sums of Y'' lie in span(1, e_n : m_n = 0) and row i of N is supported on the zeros of m, to 1e-10 or better (mostly 1e-15).
   Sharpness: split (3,1) spaces with full-support m exist (round 3: fixed m of full support reaches dim 6 = 3 + 3 for L, not 7).
   REMARK (FS type, any e; same proof): if e_i (x) C lies in L', C nondegenerate, then c(Y'') o C is inside C + C1 for all Y in L',
   and on N = ker gamma: y^i = -c(Y'') in C^perp, the set G = {c(Y'') : Y in N} satisfies 1 not in G + C e_n for every n, and
   dim G >= dim N - 2.  So an EXTREMAL FS-type space needs c in C^perp, not in C1, with c o C inside C + C1.  e = 1: m has a zero (above).
   e = 3 (C = w^perp cap 1^perp): w takes exactly two values, i.e. w ~ 1 - 5e_n [neutral column; then row i of N lies in C e_n] or
   w ~ (3,3,-2,-2,-2) [not excluded here; never seen].
   WHAT IS LEFT OF (NCOL_1): (4,1) spaces without single-row element (both known ones have a two-column defect line, 3 neutral
   columns) and isotropic m.  With verifyfl's (NS4') ["every (4,1) space with non-two-column m is split"], (NCOL_1) follows for
   all non-isotropic m.
 R4.15 FIRST-ORDER CONSTRAINTS FROM SINGLE-ROW ELEMENTS (RIGOROUS; same computation as R4.14, any e).  Let L' be a 4 x 5 level space,
   u in U_i (e_i u^T in L'), Y in L', c := c^(i)(Y) the column-sum vector of the three rows != i of Y.  Then D_i(Y) u is in C, and
   its degree-1 part -2S u + 4 c o u - 2 (c.u) 1 is in C inside 1^perp; pairing with 1 gives -6 (c.u) = 0. Hence
     (F1)  c^(i)(Y) . u = 0   and   c^(i)(Y) o u  in C        for all Y in L', u in U_i;
     (F2)  U_i o U_k inside C  for i != k   [take Y = e_k u'^T];  (with U_i perp U_k this is new information when e >= 2:
           for C = Cu + Cu' split over two rows, the five points (u_j, u'_j) lie on a conic (x - b)(y - a) = ab through 0);
     (FS-DEC) if one row carries C (U_i = C), the diagonal operators c^(i)(Y) o . preserve C for every Y in L'; if moreover C is
           nondegenerate and L' is extremal (d = e + 3), some c^(i)(Y) is not a multiple of 1 [N = ker gamma is 3-dim strongly level,
           N cap {row i = 0} has dim <= 2 by SL_3, row i of N is -c^(i)(Y), and it is never -1], so C is DECOMPOSABLE:
           C = sum over the blocks A of a partition of the columns into >= 2 blocks of (C cap V_A).
           e = 1: m has a zero (R4.14).  e = 3: C = V_A + V_B with (|A|,|B|) = (4,1) [neutral column] or (3,2) [not excluded, never seen].
           e = 2: C inside V_A with |A| = 4 [neutral column], or C = V_A (|A| = 3), or C = Cu + C(e_a - e_b), u in V_A, {a,b} = A^c.
   Numerical check (rows/uiuk_chk.py, 87 extremal spaces, 70 pairs (u,u') from different rows): (F2) to 1.3e-7, (F1) to 5e-6
   (LM-limited files; two files exceed only on vectors of norm 1e-6).
     (F1^T) transposed version for a NEUTRAL column n (notation R4.10): for x in X_n ((0|x) in L') and every Y = (q|x') in L':
           x . rho(q) = 0 (rho = row sums of q) and the row combination x^T q (a vector on the columns != n) lies in C.
           [C_j is linear in column n: (x . M^(j)(q))_{j != n} is in C; its degree-1 part is 2(x^T q)_j - 2 x.rho(q), and x.rho(q) = 0
           is the degree-1 part of x.(M(q) - 24*1) = 0.]   Checked: 96 (space, neutral column) pairs with X_n != 0, 711 tests, max rel.
           distance 3.3e-5 (attained on an LM-limited file).
STATUS 19:13 (round 4 final): Theorem NCOL-S (R4.14) and first-order constraints (R4.15, incl. (F1^T)) added; RESULT ROUND 4 at the top (U1-U9).
STATUS 19:16 (ROUND 5 started 19:14, budget 100 min -> ~20:54; targets: (NC_e) via 4x4, (NCOL_1) beyond split, (NCOL_2,3)).
STATUS 19:33: COMPUTE-rows.md written (heavy-computation requests H1-H6, exact systems X1-X3). Round 5 so far: Theorem NC-DC (slack identity), 4x4 searches, tower checks; write-up pending (section R5).
## Section R5 (round 5; started 19:14)
 Notation as in R4. For a 4 x 5 matrix Y: c(Y) in C^5 column sums, s(Y) in C^4 row sums. For L' with neutral column n: Y = (q | x), Q = {q}
 (level 4 x 4), rho(q), kappa(q) = row / column sums of q, X_n = {x : (0|x) in L'}, e^col(Q) = dim span{M(q) - 24*1} (row deletions of Q),
 e^row(Q) = dim span{R(q) - 24*1} (column deletions).  Q_dc := doubly centred part of Q (rho = kappa = 0); L'_dc likewise for L'.
 R5.1 THE EXACT 4 x 4 STATEMENT BEHIND (NC') (rigorous reformulation).  Put Adj(q)_ij := perm_3((J+q) minus row i, column j) (4 x 4;
   Adj(0) = 6J; M(q) = Adj(q) 1; R(q) = Adj(q)^T 1; 1^T Adj(q) 1 = 96 on a level Q).  With W_0 := {w in C^4 (columns != n) : w perp 1,
   w perp C(L')} (so W = W_0 + C(1 - 5e_n), dim W_0 = 3 - e) the lift is  L = {(q | x ; w_0)} + C e_r(1 - 5e_n)^T  and
        perm(J - E + [[q, x],[w_0, 0]]) = 120 + (1+x)^T Adj(q) w_0,      E := e_r(1 - 5e_n)^T.
   Hence: (L' level with neutral column n and W_0 perp C(L'))  <=>  Q level and  (1+x)^T Adj(q) wh = 24 (1.wh)  for all (q|x) in L' and
   all wh in C1 + W_0; in the UNTWISTED case (L' = (Q|0) + (0|X), X = X_n inside 1^perp) this reads: for Xh := C1 + X, Wh := C1 + W_0,
        (TRI)   Xh^T (Adj(q) - 6J) Wh = 0 for all q in Q     and the claim (NC') is     dim Q + dim Xh + dim Wh <= 8.
   Extreme cases: Q = 0 (trivial, 0 + 4 + 4) and Xh = Wh = C1 (then (TRI) is empty and the claim is the checked L_gct_214, 6 + 1 + 1).
   So (NC') is an interpolation between a triviality and L_gct_214; first order of (TRI): Xh^T q Wh = 0 (R4.15 (F1^T)).
 R5.2 THEOREM DC (rigorous, elementary).  (a) For every 4 x 5 level space:  dim L' = rank c + rank s + dim L'_dc,  rank c <= e (c(L') lies
   in C because p_1 = -6c), rank s <= 3.  So  dim L' <= e + 3 + dim L'_dc - (e - rank c) - (3 - rank s):  (DI_5) can only fail through
   DOUBLY CENTRED elements, and (DI_5) <=> "dim L'_dc <= (e - rank c) + (3 - rank s) for every 4 x 5 level space".
   (b) THEOREM NC'-DC. If column n is neutral:  dim L' = dim Q + dim X_n,  dim Q = rank rho + rank kappa + dim Q_dc,  rank rho <= e^col(Q)
   (M^(1) = -6 rho),  dim X_n <= 3 - e^col(Q) (R4.10),  rank kappa <= e (kappa(q) = c(Y) on the columns != n).  Hence the IDENTITY
        dim L' = e + 3 + delta - s1 - s2 - s3,   delta := dim Q_dc,  s1 := e^col(Q) - rank rho,  s2 := 3 - e^col(Q) - dim X_n,  s3 := e - rank kappa
   (all s_i >= 0), and (NC'_e) <=> (DC-COST): delta <= s1 + s2 + s3.  Consequences: (i) (NC') holds whenever Q has no nonzero doubly
   centred element; (ii) with the checked L_gct_216 (delta <= 3): every 4 x 5 level space with a neutral column has dim <= e + 6
   [and <= 7 by L_gct_215]; (iii) an (e+4,e) space with a neutral column contains Y = (q|x) with q != 0 doubly centred.
   Census (rows/slack_chk.py, 135 (space, neutral column) pairs of extremal spaces): the identity holds in every case; delta = 0 and
   s1 = s2 = s3 = 0 in 126; delta > 0 in 7 (delta = 1: 3, delta = 2: 4), paid by s3 alone (rank kappa < e: 5), s1 alone (1), s1 + s3 (1);
   s2 = 0 always (saturation dim X_n = 3 - e^col(Q)); 2 LM-limited files give an impossible e^col = 4 (rank artefact).
   So doubly centred elements DO occur in extremal towers, always paid exactly.
   What the three checked 4 x 4 theorems give: dim Q <= min(6, 5 + rank rho, 5 + rank kappa, 3 + rank rho + rank kappa) (214, 217, 217^T, 216);
   this proves (NC'_3) only for dim X_n = 0 and does not reach (DC-COST): (DC-COST) with X_n = 0 = W_0 IS L_gct_214.
 R5.3 (7,3) FROM (NCOL_3) AND A 4 x 4 STATEMENT (rigorous).  (DI_4x4): a 4 x 4 level space has dim Q <= e^col(Q) + 3.
   (a) (DI_4x4) is (DI_5) for 4 x 5 spaces with a ZERO column: (Q^T | 0) is level with defect dimension e^col(Q) (R4.10(c) computation).
   (b) (NCOL_3) + (DI_4x4) => no (7,3) space.  Proof: by C-UP a (7,3) space has a neutral column n; dim Q + dim X_n = 7 with
       dim X_n <= 3 - e^col(Q) gives dim Q >= e^col(Q) + 4.  QED.   [Equivalently: (7,3) follows from (NCOL_3) and the exclusion of (5,1),
       (6,2) for spaces with a zero column; for (6,2) and (5,1) themselves the same count gives only equality cases, see (DC-COST).]
   (c) (DI_4x4) needs: no (dim, e^col) = (5,1), (6,2).  (5,1) with a TWO-COLUMN defect line is excluded by TC5 (padding).  Since
       rank rho <= e^col, a (5,1) space has a row-centred part of dim >= 4 with row-deletion vectors in 24*1 + C mu.
   Numerical (rows/q44_search.py, calibrated; 4 x 4 via padding): (4,1) 9/17, (5,1) 0/14; (5,2) 2/10, (6,2) 0/15; ANY 6-dim 4 x 4 level
   space: 0/15 (the checked bound 6 may not be sharp; all Q of the census have dim <= 5).  Row-centred: (3,1) 14/16; (4,1) 1/34, and
   the one hit has the two-column defect line e_0 - e_1 (as in the 4 x 5 case, where verifyfl's (SL_m) fails exactly for two-column m).
 R5.4 TOWERS GO ON (numerical, rows/tower_chk.py): in all 120 (extremal space, neutral column) pairs the 4 x 4 space Q has again a
   deletable row or column (3 x 4 or 4 x 3 rest level): every known 7-dim level space is a tower 5x5 -> 4x5 -> 4x4 -> 3x4/4x3.
   PRINCIPAL CENSUS (rows/kc_chk.py): in 90 of 95 extremal spaces rank c = e and K = ker c is a 3-dim STRONGLY LEVEL space with
   s(K) = 1^perp (verifyfl's "principal" kind, for every e); exceptions: one column-centred (4,1) with two-column line, one (5,2)
   with e(K) = 1, three (6,3) with rank c < 3 (K of dim 4, 5).  In the principal case L'_dc = 0.
 R5.5 (NCOL_3), block pattern (3,2) (numerical, rows/fixC_search.py ... b32): defect space fixed = V_{012} + V_{34}: dim 5 found 2/9,
   dim 6: 0/30 (control with a neutral column: 4/19).  With R4.13 (generic C0: 0/46) and (FS-DEC): no sign of a (6,3) space
   without neutral column.
STATUS 19:39: section R5 (R5.1-R5.5) written: Theorem DC / NC-DC, (7,3) from (NCOL_3) + (DI_4x4), 4x4 searches, towers, principal census.
 R5.6 FIRST-ORDER LAW FOR SINGLE-COLUMN ELEMENTS IN ANY COLUMN (rigorous; generalises (F1^T), no neutrality assumed).
   (SC1) Let x e_n^T be in a 4 x 5 level space L' (x in C^4, sum x = 0). Then for every Y in L' (columns y_j, row sums s(Y)):
          <x, s(Y) - y_n> = 0      and      the vector (<x, y_j>)_{j != n}, with 0 at n, lies in C cap e_n^perp.
   Proof. C_j is linear in column n: C(Y + lam x e_n^T) - C(Y) = lam v(Y), v_n = 0, v_j = x.M^(j;n)(Y), M^(j;n)_i = perm_3((J+Y) minus row i,
   columns j, n); v(Y) lies in C. Degree 1: v^(1)_j = 2[<x,y_j> + <x,y_n> - <x,s>]; sum over j != n is 6[<x,y_n> - <x,s>] = 0 as C is in 1^perp. QED
   Consequence for e = 1: if m_n != 0 and x e_n^T is in L', then EVERY column j != n of EVERY Y in L' is orthogonal to x.
   Checked (rows/sc1_chk.py): 184 (space, column) pairs with single-column elements, 68 of them non-neutral columns, 1167 tests, max 6e-6.
 R5.7 THEOREM NCOL-P (rigorous; (NCOL_1) when the single-column elements span the row sums; NO hypothesis on m, isotropic allowed).
   Let L' be a 4 x 5 level space with defect space C m, dim L' >= 4, X_n := {x : x e_n^T in L'}. If sum_n X_n = 1^perp (in C^4), then
   m_n = 0 for some n with X_n != 0: L' has a neutral column carrying a single-column element.
   Proof. (1) K := sum_n X_n e_n^T is strongly level: P_k of a sum of single-column elements in distinct columns is multi-homogeneous in
   the pieces, each piece may be scaled inside L', so every multi-homogeneous part of P_k vanishes, and these parts are exactly the terms of
   the deletion polynomials. P_2 gives X_n perp X_n' (n != n'), so 1^perp = (+) X_n orthogonally, dim K = 3, s : K -> V := 1^perp bijective.
   (2) Isometries (zeros / verifyfl): for h in K write h_j = A_j s(h); polarising p_2 = 0 on K, B_j := 1 - 2A_j are isometries of V,
   sum_j A_j = 1.  Here A_j is the orthogonal projector onto X_j:  B_j x = x for x in X_n, j != n, and B_n x = -x.
   (3) Normal form (verifyfl PS, any m): N := L' cap ker s has dim >= 1 (L' = K + N); for Z in N, p_2(Z, h)_j = <s(h), B_j^T z_j^V> (z_j^V =
   component of column j in V; the 1-component is (c_j(Z)/4) 1, c(Z) = kappa m) must be a multiple of m_j for every s(h) in V, so
   z_j^V = m_j B_j f with one f = f(Z) in V.  f(Z) != 0 for Z != 0: otherwise Z = (kappa/4) 1 m^T with kappa != 0; the line C Z is level only
   if e_1(m) = .. = e_4(m) = 0, and then p_2(tZ)_j = 24 (t kappa/4)^2 m_j^2 must be proportional to m_j, i.e. m_j in {0, alpha} for all j,
   impossible with sum m = 0, m != 0.
   (4) Row sums of Z vanish: sum_j m_j B_j f = 0. Pair with x in X_n: sum_j m_j <f, B_j^{-1} x> = (sum_{j != n} m_j - m_n) <f,x> = -2 m_n <f,x>.
   So m_n <f, x> = 0 for all n and x in X_n. As f != 0 and the X_n span V, some <f,x> != 0, hence m_n = 0.  QED
   Coverage: of the 28 principal (4,1) examples, 15 have K spanned by single-column elements (types (1,1,1) and (2,1) below).
   The same pairing for any e: for Z in ker s and x in X_n: <z_n, x> = 0  (column n of every row-centred element is orthogonal to X_n).
 R5.8 STRUCTURE OF THE STRONGLY LEVEL KERNEL K = ker c IN THE 90 PRINCIPAL EXTREMAL SPACES (numerical):
   K is always supported on at most THREE columns; column ranks of K: (1,1,1): 21, (2,1): 30, (3): 9 [K spanned by single-column
   elements: 60], (3,2): 25, (2,2,1): 5 [exactly one single-column direction]; K has no single-row element; K ALWAYS contains a
   single-column element, and in every case some column carrying a single-column element of K is NEUTRAL (90/90).
   So the mechanism of (NCOL) in the principal case is: "a single-column element of the strongly level kernel sits in a neutral column".
   Proved: e = 1 with K spanned by single-column elements (R5.7); e = 1 split non-isotropic (R4.14).  Not proved: types (3,2), (2,2,1); e >= 2.
 R5.9 THEOREM NCOL-P3 (RIGOROUS; (NCOL_1) for principal spaces whose strongly level kernel lives on <= 3 columns; ANY m, isotropic allowed).
   Let L' be a 4 x 5 level space with defect space C m. Let K in L' be a 3-dim strongly level subspace with s(K) = V := 1^perp (in C^4)
   all of whose elements vanish outside three columns a, b, c, and let Z in L' have s(Z) = 0 and c(Z) = kappa m with kappa != 0.
   Then  m_a m_b m_c = 0.   If K vanishes outside two columns a, b:  m_a m_b = 0;  outside one column a:  m_a = 0.
   So every (4,1) space with K := ker c strongly level, s(K) = V and K on <= 3 columns has a NEUTRAL column, and it is an active column of K.
   Proof. (1) Isometries: h_j = A_j s(h) on K, B_j := 1 - 2A_j in O(V), sum_j B_j = 3 (polarised p_2 = 0 on K; zeros/verifyfl). Columns
   d, e outside {a,b,c}: A_d = A_e = 0, B_d = B_e = 1, hence  B_a + B_b + B_c = 1.
   (2) Normal form (R5.7 (3)): z_j = (kappa m_j/4) 1 + m_j B_j f, f in V; p_2(Z)_j = 2c_j^2 + 2<s - z_j, z_j> = m_j^2 [(3/2)kappa^2 - 2<f,f>]
   must be proportional to m_j, and (m_j^2)_j is not (sum m = 0), so  nu := <f,f> = (3/4) kappa^2 != 0.
   (3) Put g_j := B_j f (j = a,b,c):  <g_j,g_j> = nu,  g_a + g_b + g_c = f.  Row sums of Z: 0 = sum_j m_j B_j f = m_a g_a + m_b g_b + m_c g_c
   + (m_d + m_e) f, and m_d + m_e = -(m_a+m_b+m_c), so with (alpha,beta,gamma) := (m_b+m_c, m_a+m_c, m_a+m_b):
          alpha g_a + beta g_b + gamma g_c = 0.
   (4) Gram matrix: tau_j := <g_j, f>; from g_a+g_b+g_c = f: tau_a+tau_b+tau_c = nu and <g_a,g_b> = -tau_c, <g_a,g_c> = -tau_b, <g_b,g_c> = -tau_a.
   Pairing the relation with g_a, g_b, g_c:   beta tau_c + gamma tau_b = alpha nu,   alpha tau_c + gamma tau_a = beta nu,   alpha tau_b + beta tau_a = gamma nu.
   If alpha beta gamma != 0: tau_a = nu (beta^2+gamma^2-alpha^2)/(2 beta gamma) etc., and tau_a+tau_b+tau_c = nu becomes
   (alpha+beta-gamma)(alpha-beta+gamma)(-alpha+beta+gamma) = 0, i.e. 8 m_c m_b m_a = 0.  If alpha = 0 (say): gamma tau_a = beta nu, beta tau_a =
   gamma nu give beta gamma = 0 (then alpha = beta = gamma = 0 and m_a = m_b = m_c = 0) or tau_a = nu (beta = gamma: m_b = m_c, with alpha = 0:
   m_b = m_c = 0) or tau_a = -nu (beta = -gamma: m_a = 0).  In every case m_a m_b m_c = 0.
   Two columns: B_b = -B_a =: -B, the relation is (m_a - m_b) B f = (m_a + m_b) f; f is non-isotropic, so the eigenvalue is +-1 (m_b = 0 or
   m_a = 0), or m_a = m_b = 0.  One column: B_a = -1, -2 m_a f = 0.  QED
   Checked numerically on all 28 principal (4,1) spaces (rows/ncolp_chk.py, ncolp3_chk.py): normal form (3e-6), <f,f> = (3/4)kappa^2 (2e-11),
   sum B_j = 3 (1e-14), g_a+g_b+g_c = f (2e-9), the relation (6e-10), product of m over the active columns of K = 0 (1e-12).
   This contains R5.7 (K spanned by single-column elements has <= 3 active columns) and needs no classification of K.
   STATUS OF (NCOL_1): proved for (a) split non-isotropic m (R4.14); (b) principal K on <= 3 columns (this theorem) = 28 of the 30 known
   (4,1) spaces; the 2 others are column-centred with a two-column defect line (three neutral columns).  Still unproved: that a principal K
   always lives on <= 3 columns (true in 90/90 examples; exact problem X4 in COMPUTE-rows.md), and non-principal (4,1) spaces.
   For e >= 2 the same computation gives only: sum_{j in {a,b,c}} A_j F_j(Z) = 0 for the column data F(Z) in V (x) C of row-centred Z
   (the Gram argument needs F = f (x) u of rank one); open.
STATUS 19:47: Theorem NCOL-P3 (R5.9), (SC1) (R5.6), K-structure census (R5.8) written.
 R5.10 REMARKS ON PRINCIPAL (5,1) SPACES (rigorous, partial; for verifyfl's N-problem).  Setting of R5.9 with N := L' cap ker s of dim 2
   (L' = K + N a (5,1) space), K on columns a, b, c.  Row sums of Z in N:  sum_j m_j A_j f(Z) = 0, i.e. with P := f(N) (2-dim, the form
   <,> has rank 1 on P by <f(Z),f(Z')> = (3/4) kappa(Z) kappa(Z')):   (m_a A_a + m_b A_b + m_c A_c) p = 0 for all p in P.
   By R5.9 one of m_a, m_b, m_c vanishes, say m_c = 0. If also m_a m_b (m_a + m_b) != 0, then A_b = -(m_a/m_b) A_a on P, and the isometry
   identities <p,A_j p'> + <A_j p,p'> = 2<A_j p,A_j p'> for j = a, b give <A_a p, A_a p'> = 0 on P: A_a(P) is totally isotropic, so A_a has rank
   <= 1 on P and there is p_0 != 0 in P with A_a p_0 = A_b p_0 = 0, A_c p_0 = p_0:  K CONTAINS THE SINGLE-COLUMN ELEMENT p_0 e_c^T IN THE
   NEUTRAL COLUMN c, with p_0 in f(N).  Every Z in N has zero column c, and the element Z_* of N with kappa = 0 is (q_*|0) with q_* a
   DOUBLY CENTRED 4 x 4 matrix whose columns m_j B_j f_* are all isotropic (this is the doubly centred element forced by R5.2(b)(iii)).
   Remaining sub-cases: m_a = 0 as well (then A_b = 0 on P), m_b = -m_a (then A_b = A_a on P).  Not finished: the cubic and quartic conditions.
 R5.11 THEOREM P51 (RIGOROUS): NO (5,1) SPACE OF THE TWO MAIN PRINCIPAL TYPES WHEN m HAS FIVE DISTINCT ENTRIES.
   Let L' be a 4 x 5 level space with defect line C m, all five entries of m pairwise distinct (so at most one zero), and K in L' a 3-dim
   strongly level subspace with s(K) = V = 1^perp.  Put N := L' cap ker s (L' = K + N).
   (i)  If K is spanned by single-column elements (K = (+)_n X_n e_n^T), then dim L' <= 4, and if dim L' = 4 then L' is split:
        N = C e_i m^T for some row i.
   (ii) If K lives on two columns a, b and dim N >= 2, then K is the full free column F_a or F_b; so by (i) dim N >= 2 is impossible.
   Hence there is no (5,1) space with such a K of column-rank type (1,1,1), (2,1), (3) or (3,2).  [Left: type (2,2,1), where the same
   computation gives N inside {a m^T + t n(e_a - e_b)^T}, n isotropic; not finished.  Isotropic m is allowed here; e.g. (1,w,w^2,0,0) has
   a repeated entry and is NOT covered.]
   Proof of (i). Notation of R5.7/R5.9: A_j = orthogonal projector onto X_j, V = (+) X_j. For Z in N, sum_j m_j A_j f = 0 splits into
   m_j A_j f = 0 for each j, so B_j f = f whenever m_j != 0 and  Z = a m^T  with a = (kappa/4) 1 + f (RANK ONE);  f != 0 for Z != 0.
   Let x be in X_n and j != n. C_j is linear in column n, and the cofactors are 3 x 3 permanents of J + a m^T:
        d/d eps C_j(a m^T + eps x e_n^T) = sum_{k=0}^{3} (3-k)! k! <x, E_k(a)> e_k(m^(j,n)),     E_k(a)_i := e_k(a without a_i),
   m^(j,n) := m without the entries j, n   [checked numerically to 3e-13].  As a vector over j (0 at n) it lies in C m cap e_n^perp.
   Here e_1(m^(j,n)) = -(m_j + m_n), e_2(m^(j,n)) = e_2(m^(n)) + m_j(m_j + m_n) =: q_2(m_j), e_3(m^(j,n)) = e_3(m^(n)) - m_j q_2(m_j) =: q_3(m_j)
   are polynomials in m_j of exact degrees 1, 2, 3, and <x,E_1(a)> = -<x,f>.
   If m_n != 0: <x,f> = 0 and the vector must vanish: 2<x,E_2> q_2(m_j) + 6<x,E_3> q_3(m_j) = 0 at the four distinct points m_j (j != n).
   If m_n = 0: it equals lam m_j at the four distinct points: a polynomial of degree <= 3 in m_j with four roots.
   In both cases <x,E_2(a)> = <x,E_3(a)> = 0. The X_n span V, so E_2(a) and E_3(a) are multiples of 1:
        a_i (kappa - a_i) = t for all i,   and   a_i (e_2(a) - t) is independent of i      (kappa = sum a_i).
   So the a_i take at most two values alpha, beta with alpha + beta = kappa; a constant vector gives f = 0; multiplicities (3,1) give
   alpha = 0, a = kappa e_i; multiplicities (2,2) give kappa = 0 and e_2(a) = -2 alpha^2 = t = -alpha^2, a = 0.  Hence a(Z) is a multiple
   of a unit vector for every Z in N; a is linear and injective on N, so dim N <= 1 and N = C e_i m^T.  QED (i)
   Proof of (ii). B_b = -B_a =: -B; the row-sum relation on P := f(N) is (m_a + m_b) p = (m_a - m_b) B p; m_a != m_b, so B = lam on P.
   P is 2-dim with a form of rank 1 (<f(Z),f(Z')> = (3/4) kappa kappa', kappa not identically 0), so P = n^perp for an isotropic n; P contains
   non-isotropic vectors, so lam = +-1; an isometry of V that is +-1 on n^perp is +-1 on V. So B = 1 (A_a = 0, K = F_b) or B = -1 (K = F_a).  QED
   Consequences: (a) every (4,1) space whose single-column elements have row sums spanning 1^perp and whose m has distinct entries
   is SPLIT (consistent with the census); (b) for the principal (5,1) problem with distinct entries only the kernel type (2,2,1)
   (and kernels on 4 or 5 columns, never seen) remain.  This is consistent with verifyfl's numerics (R4.7: no solution of the
   N-problem for distinct entries, solutions only for repeated entries).
STATUS 19:55: R5.10, R5.11 (Theorem P51) written.
 R5.12 (R-LAW): ROW-CENTRED ELEMENTS HAVE THEIR ROWS IN THE DEFECT SPACE.
   Numerical (all 90 principal extremal spaces, every kernel type, e = 1, 2, 3; max relative distance 1e-12): every Z in N = L' cap ker s
   has ALL ITS ROWS in C, i.e. N lies in C^4 (x) C, equivalently Z w = 0 for all w in W = (C + C1)^perp (so column n of Z vanishes for every
   neutral n).  For e = 1 all 28 principal (4,1) spaces have N = C e_i m^T (rank one, split).  N is spanned by single-row elements in 74 of
   the 90 (this is the "row-split" phenomenon of R4.4), not always.  It FAILS in the non-principal extremal spaces.
   Rigorous part (any e): if K is spanned by single-column elements (A_j orthogonal projectors onto X_j), then for Z in N with c(Z) = u:
   z_j = (u_j/4) 1 + B_j F_j with (F_j) in V (x) C (normal form R5.7(3) for general e: (<sigma, B_j^T z_j^V>)_j lies in C for all sigma),
   the row sums give sum_j A_j F_j = 0, hence A_j F_j = 0 and B_j F_j = F_j for every j:  Z = (1/4) 1 u^T + F  with F in V (x) C.  QED
   For the other kernel types the law is equivalent to: sum_j w_j <z_j, h_j> = 0 for all h in K, w in C^perp (not proved).
   Use: with (R-LAW) an extremal principal space is L' = K (+) N, K strongly level on <= 3 columns, N an e-dim subspace of C^4 (x) C mapped
   isomorphically onto C by the column sums; an (e+4,e) space of this kind would have N of dim e+1 inside C^4 (x) C with a doubly centred
   element of rank <= e whose rows lie in C.
STATUS 19:59: R5.12 (R-LAW) written.
 R5.13 PROPOSITION NCOL2-P (rigorous, partial (NCOL_2); kernel spanned by single-column elements, C "square-generic").
   Let L' be a 4 x 5 level space with dim C = 2 whose single-column elements have row sums spanning V (K = (+) X_n e_n^T as in R5.7) and
   such that the column sums map N = L' cap ker s ONTO C (e.g. a principal (5,2) space).  Assume
        (G)  the classes of u1 o u1, u1 o u2, u2 o u2 (entrywise products, u1, u2 a basis of C) are linearly independent modulo C.
   Then some column n with X_n != 0 is neutral.
   Proof. Suppose not. By R5.12, Z_u = (1/4) 1 u^T + F(u), F(u) in V (x) C, F_n(u) perp X_n. By (SC1) (R5.6), for x in X_n the row vector
   x^T F(u) = (<x, z_j>)_j lies in C cap e_n^perp, a LINE C u^(n) (n is not neutral). As V = (+) X_n orthogonally,
        F(u) = sum_n xi_n(u) (x) u^(n),     xi_n : C -> X_n linear.
   Degree 2 of the defect: p_2(Z_u)_j = (3/2) u_j^2 - 2 <F_j,F_j> = (3/2) u_j^2 - 2 sum_n <xi_n(u),xi_n(u)> (u^(n)_j)^2 is a vector of C. By (G):
        (3/4) u (x) u = sum_n nu_n(u) u^(n) (x) u^(n)   in Sym^2 C,    nu_n(u) := <xi_n(u), xi_n(u)>,   for all u in C.
   The squares u (x) u span the 3-dim space Sym^2 C, so at least three columns are active with pairwise independent u^(n): the kernel
   has type (1,1,1), each X_n is a line and nu_n(u) = l_n(u)^2 <x_n,x_n> is the SQUARE of a linear form.  But in the basis
   u^(a) (x) u^(a), u^(b) (x) u^(b), u^(c) (x) u^(c) of Sym^2 C the coefficients of u (x) u are products of two INDEPENDENT linear forms
   (for u = alpha u^(a) + beta u^(b), u^(c) = g_a u^(a) + g_b u^(b): the coefficient of u^(c) (x) u^(c) is alpha beta/(g_a g_b)).  Contradiction.  QED
   Scope: (G) FAILS for the defect planes of the known (5,2) spaces (e.g. u o u' in C by (F2), or C = V_S), so this does not prove (NCOL_2);
   it shows that a (5,2) space of this kernel type without neutral column needs a relation between C o C and C.  The same argument for
   e = 1 is R5.7 (C cap e_n^perp = 0 forces F = 0).
STATUS 20:00: R5.13 written.  Round 5 final: see RESULT ROUND 5 at the top.
STATUS 20:04 (ROUND 6 started 20:04, about 2 h -> ~22:04; targets: (1) principal K on <= 3 columns by hand, (2) non-principal (4,1) and (5,1) strata, (3) (DC-COST), (4) (R-LAW)).
