# NOTES-reg2 (role reg2; start 18:47, budget 100 min -> ends ~20:27). Regime: some row/column with a_r >= 2.
## RESULT (reg2, final 19:55) -- regime a_r >= 2 NOT closed by a proof. New: a rigorous first-order criterion, the taxonomy of 6-dim 4x5
## level spaces (four families, one of them NEW and exact), and the exact statement that would close the regime.
 Notation: L level 5x5, row r, M := L_r (4x5 level, dim 4 + a_r if dim L = 9), W_r := row-r projection of L, J' = 4x5 all-ones,
 N_j(X) = perm_4(X without column j), F = sum_j N_j, C(M) = defect space (rows), e = dim C(M), Phi(Y) = N(Y),
 T_1(M) = stage2's first-order space (M placed in the rows != r), Omega(M) := row-r projection of T_1(M)  (a subspace of C^5).
 A [RIGOROUS, section 1] FIRST-ORDER + FK CRITERION (new):  tau_r := J - 5 e_r 1^T lies in T_1(M) for EVERY level M, so 1 is in Omega(M);
    W_r lies in Omega(M) and never contains 1 (FK). Hence for every level space L and every row r
          dim L  =  dim L_r + dim W_r  <=  dim L_r + dim Omega(L_r) - 1,      dim Omega(M) = (4 - e(M)) + g(M),  1 <= g(M) <= e(M) + 1
    (g = number of independent defect functions <v, N(J'+Y)> of M that are first-order level variations D_X F(J'+Y); g = 1:
    dim L <= dim L_r + 4 - e(L_r), rows' defect bound WITHOUT assuming row r deletable). Also rigorous: Phi(L_r) lies in
    (row-r projection of L^)^perp (dim a_r - 1); Omega(M) is orthogonal to Phi(M);
          Omega(M) = { s in C^5 : the function Y -> D_{Y D_s} F(J'+Y) on M is of the form Y -> D_X F(J'+Y) }      (D_s = diag(s)),
    i.e. Omega = infinitesimal COLUMN scalings keeping M level to first order up to a translation. Checked on 70 lines of the 7
    known spaces: no violation, equality in 39 (reg2/chk_lemma.py). For a 9-dim L: a_r = 2 needs dim Omega(L_r) >= 4.
 B [NUMERICAL + EXACT examples; sections 2, 4] THE KEY QUESTION "does every 6-dim 4x5 level space contain a full free line?": NO.
    Every 6-dim 4x5 level space found (about 200, from five differently biased searches) has a DELETABLE row or column and
    falls into one of four families, with invariants (dim Omega, dim T_1, FO2 bound):
      F    full free row e_i (x) 1^perp (+) 2-dim, e = 4:                         (3,10,8) [rc45] or (5,12,9) [kernels of L080, ex2, ex3, ...]
      NC   one neutral column c, e = 3, Omega = span(1,e_c) (19 files of rows):   (2, 9,7)
      DR2/DR3  deletable row with free part of dim 2 or 3, e = 4, no neutral column, no full free row (NEW here):
               (2,9,7), or (3,10,8) with Omega = indicators of a column partition {a},{b},{rest} (rc45-like), or
      M*   (4,11,8):  the EXACT family  M*(x,y) = e_3 (x) {w : sum w = 0, w_1 = w_2} (+) C x e_0^T (+) C y e_3^T (+) C e_2 (e_1-e_2)^T,
               x, y in C^3 (rows 0,1,2), sum x = sum y = 0, <x,y> = 0 (e.g. x = (1,-1,0), y = (1,1,-2)): 6-dim, level (hand proof,
               section 4), NO full free row, Phi = 0, Omega(M*) = (e_1 - e_2)^perp of dimension 4, dim T_1 = 11.
    So "(S6') dim Omega <= 2 (or <= 3) without a full free row" is FALSE: M* passes EVERY first-order necessary condition for being
    L_r of a 9-dim level space with a_r = 2 (R_r = k^perp, k = e_1 - e_2, Phi = 0). It is excluded only at SECOND order:
    EXACT (rational arithmetic, reg2/mstar2_fo2.py): dim ker = 11, rank of q_Y on it = 5, so every level space containing M* has
    dim <= 8. Numerically M* lies in 7-dim level spaces (9 of 12 starts) but in no 8-dim one (0 of 70 starts, 6 unknowns).
    The Type F spaces with Omega = C^5 have FO2 bound 9: for them only Theorem FL (dim <= 7) works.
    All 41 spaces of rows / of the 7-dim examples are maximal 4x5 level spaces (E_0 = M + C d, P_2(d) != 0); 7-dim search through
    45 known smaller level spaces: 0 of 132 starts. No 7-dim 4x5 level space is known.
 C [CONSEQUENCE, rigorous given FL and stage2's Lemma FO2] a_r = 2 is impossible at dim 9 as soon as
      (S6-FO2)  every 6-dim 4x5 level space M without a full free row has FO2 bound <= 8
    (true for every space found: bounds 7, 7, 8, 8). a_r = 3 is impossible as soon as no 7-dim 4x5 level space exists, or every
    7-dim one has FO2 bound <= 8 (it contains no full free row by rows' SL_3 corollary). Both are statements about 4x5 matrices.
 D [NOT DONE] no proof of (S6-FO2); no classification of the 6-dim spaces ("deletable line" is the 4x5 analogue of conjecture (D));
    no proof of "4x5 level <= 6". The first-order criterion alone cannot close the regime (M*).
 Best next steps: (1) census of 6-dim 4x5 level spaces with dim Omega >= 4 and no full free row, with the FO2 bound of each
    (COMPUTE-reg2.md, sections 1-3; the equal-column extensions of 5-dim equal-column spaces are the place to look: M* is one);
    (2) prove "6-dim 4x5 level => deletable row or column" along upstream L_gct_215's case tree; (3) for REGIME 1 the criterion
    gives the cheap filter Omega(L_r) = C^5; hyperplanes of the F spaces with Omega = C^5 and of M*-like spaces are candidates there.
STATUS 18:53: BRIEF + rows/stage2/chief notes read. First facts (numerical, reg2/t.py, a1.py, a2.py):
 - the "key question" has answer NO: rc45 contains a full free row, but the 19 (6,3) spaces of rows (clm_p4_d6_defect3_*, nc_d6_k1_*,
   seed_d6_e3_*) contain NO full free row (single-row parts of dim <= 2) and no full free column. All 19 have dim T_1 = 9, rank q = 3,
   FO2 bound 7; rc45: T_1 = 10, rank 4, FO2 bound 8 (and <= 7 by FL).
 - rigorous remark (Z2 weak form, 2 lines): for u in L^ and Y in L_r, s^4-coefficient of perm(u + sY): <u_r, Phi(Y)> = 0, Phi(Y)_j =
   perm_4(Y without column j). So Phi(L_r) lies in R_r^perp (dim a_r - 1): for a_r = 2, Phi(Y) = phi(Y) k for ONE vector k (sum k = 0).
   Among the 19 spaces only some have rank Phi <= 1 (rc45, seed t4/t9: Phi = 0; nc s2, s23: rank 1).
STATUS 19:10: (1) the LM (6,3) files are 1e-7-close to SPARSE limit spaces (rounded rref, level error 1e-12): all 15 clean limits are
 spanned largely by single-row and single-column elements (e.g. nc_d6_k1_s23 = full free column of the 4 rows (+) three single-row
 elements; seed_d6_e3_t4 = e_1 (x) 3-dim (+) three single-column elements); none has a full free row except rc45. Row-projection
 ranks of the limits: (3,3,3,3), (2,2,1,2), (3,2,3,2), ... so "some row projection >= 4" is NOT a general property.
 (2) NEW first-order criterion (rigorous; see section 2): Omega(M) := row-r projection of T_1(M) contains 1 (tau_r = J - 5 e_r 1^T is
 always in T_1(M)), while the row projection W_r of a level L never contains 1 (FK). Hence for L_r = M: dim L - dim M = dim W_r <=
 dim Omega(M) - 1. Data: all 19 (6,3) spaces have dim Omega = 2 (so L_r = M forces dim L <= 7), rc45 has Omega = span(e_4, e_0+e_1,
 e_2+e_3) (dim 3; dim L <= 8, and <= 7 by FL). So none of the 20 known 6-dim 4x5 level spaces can be L_r of a 9-dim level space,
 already at first order. Target now: prove dim Omega(M) <= 3 for every 6-dim level M (would close a_r = 2), or find a counterexample.
STATUS 19:18: (a) COUNTEREXAMPLES to "dim Omega <= 3 for all 6-dim M": the 6-dim line-kernels of L080 (columns 0-3), ex2, ex3, fam2,
 s-family (row 4) have Omega = C^5, dim T_1 = 12, FO2 bound 9 -- but all of these contain a FULL FREE ROW (Type F: free row (+) 2-dim),
 so FL applies. All other known 6-dim spaces (Type NC: exactly one neutral column c, e = 3, C(M) = e_c^perp cap 1^perp) have
 Omega = span(1, e_c), dim T_1 = 9, FO2 = 7. (b) every known 6-dim M has E_0(M) = M (+) C d with P_2(d) != 0: maximal 4x5 level
 spaces. (c) reg2/ext6.py: ALL 6-dim level extensions of 16 known 4- and 5-dim level spaces (search inside E_0(M_b)/M_b, 2-10
 unknowns): 60 new 6-dim spaces, every one of Type NC. Writing up: regime a_r >= 2 is closed by FL + (S6'): "a 6-dim 4x5 level
 space without a full free row has dim Omega <= 2" (first-order statement about 4x5 spaces).
STATUS 19:30: COMPUTE-reg2.md written (heavy computations for the 24-core machine: censuses A-D, exact items). Exact Type NC family
 found and hand-proved (section 2.5, reg2/fam_nc.py). Writing sections 1-3.

## 1. Rigorous statements (hand proofs; all checked numerically by reg2/chk_lemma.py: 70 lines of the 7 known spaces)
 Setting: M a 4x5 level space, embedded in 5x5 matrices with zero row r (write t = (X ; rho), X = the rows != r, rho = row r).
 perm(J + (X;rho)) = sum_j (1 + rho_j) N_j(J' + X)  (Laplace along row r), N(J') = 24*1, F = <1, N>.
 gamma(v) := the function Y -> <v, N(J'+Y)> on M (v in C^5);  delta(X) := the function Y -> D_X F(J'+Y) on M (X in C^{4x5}).
 L1 (structure of T_1). (a) T_1(M) = {(X;rho) : gamma(rho) + delta(X) = 0}.  (b) ker gamma = Z(M) := (C(M) + C1)^perp (dim 4 - e),
    im gamma has dim e + 1 and contains the constants (gamma(1) = 120).  (c) ker delta = E_0(M), and delta(J') = 480
    [F(c(J'+Y')) = 120 c^4 and D_Y F(J'+Y') = 0 for Y, Y' in M give D_{J'} F(J'+Y') = 480].  (d) Hence tau_r := (J' ; -4*1) =
    J - 5 e_r 1^T lies in T_1(M), Omega(M) := {rho : exists X, (X;rho) in T_1(M)} contains 1 and Z(M), and
         dim T_1(M) = dim E_0(M) + dim Omega(M),   dim Omega(M) = (4 - e) + g,  g := dim(im gamma cap im delta), 1 <= g <= e + 1.
    Proof: (a) is the derivative of the Laplace expansion; (b): span{N(J'+Y)} = C1 (+) C(M); the rest is linear algebra.  QED
 L2 (degree splitting). (X;rho) in T_1(M) iff for all Y in M:  <X, grad P_{k+1}(Y)> + <rho, p_k(Y)> = 0 (k = 0..3) and
    <rho, Phi(Y)> = 0, where P_k are the 4x5 subpermanent sums, p_k(Y)_j = P_k(Y without column j), Phi = p_4, and
    p_k(Y) = colsum(grad P_{k+1}(Y)) / (4 - k) for k <= 3.  [D_t P^{5x5}_{k+1}((Y;0)) = 0 for each k by homogeneity; the (i,j)
    entry of the gradient is P_k of the minor.]  So Omega(M) is orthogonal to Phi(M), and with G_k := span{grad P_{k+1}(Y)}:
    Omega(M)^perp = span Phi(M) + { sum_k colsum(V_k)/(4-k) : V_k in G_k, sum_k V_k = 0 }  (relations among G_0..G_3).
 L3 (column scalings). For every 4x5 X and s in C^5:  <s, N(X)> = (sum s) F(X) - D_{X D_s} F(X), D_s = diag(s) acting on columns
    [perm((X;rho) D) = det(D) perm(X;rho), differentiate at D = 1, rho = 1]. Hence
         Omega(M) = { s : the function Y -> D_{Y D_s} F(J'+Y) on M lies in im delta },
    in particular Omega(M) contains every s with M D_s inside M. Euler form: s in Omega iff there is X with, for all Y in M,
      (D1) 4 <s, colsum Y> = D_X P_2(Y);  (D2) 3 E_s P_2(Y) = D_X P_3(Y);  (D3) 2 E_s P_3(Y) = D_X P_4(Y);  (D4) E_s P_4(Y) = 0,
    E_s P_k(Y) := sum over k-subsets S of columns of (sum_{c in S} s_c) * (sum of the k x k subpermanents of Y in columns S).
    (Row scalings give nothing: D_{D_x Y} F(J'+Y) = 120 sum x - D_{x 1^T} F(J'+Y) is always in im delta.)
 L4 (CRITERION). Let L be a level space of 5x5 matrices, r a row, M := L_r, W_r := row-r projection of L. Then
      (i) L lies in T_1(M) (stage2's FO), so W_r lies in Omega(M);  (ii) dim L = dim M + dim W_r;  (iii) 1 is not in W_r
      (if t_r = c 1, c != 0, then J - t/c has a zero row: perm = 0 != 120);  (iv) 1 is in Omega(M) (L1).
    Therefore  dim L <= dim L_r + dim Omega(L_r) - 1 = dim L_r + 3 - e(L_r) + g(L_r).   QED
    Remarks. g = 1 ("untwisted"): dim L <= dim L_r + 4 - e(L_r), the bound of rows' defect construction, now for EVERY row
    (deletable or not). The criterion uses no second-order information; it is sharp on 39 of the 70 lines of the known spaces.
 L5 (Phi). For u in L^ = CJ + L and Y in L_r the s^4-coefficient of perm(u + sY) is <u_r, Phi(Y)>, so Phi(L_r) is orthogonal to
    R_r := row-r projection of L^ (dim 6 - a_r): for a_r = 2, Phi(Y) = phi(Y) k with one vector k, R_r = k^perp, sum k = 0.
    More generally for u = (X;rho) in L^, Y in L_r: sum_j rho_j N_j(X + Y) = 120 ell(u)^5 does not depend on Y; its parts of
    Y-degree 4, 3, 2, 1 are the exact (not only first-order) conditions; for rho zero-free it says that the column-rescaled
    space M D_rho^{-1} is "level at the base point X D_rho^{-1}" (F(X D^{-1} + Y D^{-1}) constant) -- a 4-parameter family of
    such rescalings when a_r = 2.
 L6 (pairs, consistent with chief's C8; rigorous). a_r = 2 (R_r = k^perp), a_i = 1 (ell = <n_i, u_i>), T = {j,l} with
    (k_j,k_l) != 0: on U_T = {u in L^ : u_r, u_i supported in T} row r is c (k_l e_j - k_j e_l), so perm_2 = c (k_l b - k_j a)
    ((a,b) = u_i on T) and ell = c lam_T. If ell != 0 on U_T (case B1) then k_l b - k_j a is proportional to ell, hence either
    n_ij k_l + n_il k_j = 0 or the image of U_T in the 2x2 block is ONE-dimensional and dim L_{ri} >= dim U_T - 1 >= 3.
    (No contradiction comes out: 6-dim spaces with all row projections of dim <= 3 exist, section 2.2.)

## 2. Data (numerical unless said otherwise; scripts in reg2/)
 2.1 The files of rows (rc45, clm_p4_d6_defect3_*, nc_d6_k1_*, seed_d6_e3_*; a2.py, a5.py, a6.py, a8.py). The LM files are within
     1e-7 of SPARSE limit spaces (rounded rref still level to 1e-12); invariants of the limits:
       rc45: single-row parts (0,0,0,4): full free row; e = 4; Phi = 0; dim E_0 = 7; dim T_1 = 10; Omega = span(e_4, e_0+e_1, e_2+e_3);
             FO2 bound 8 (FL: 7). The extra first-order directions are block means x (x) 1_C, C in {01}, {23}, {4}.
       the 19 others: no full free row (single-row parts <= 3), e = 3, exactly one neutral column c, Omega = span(1, e_c),
             dim E_0 = 7, dim T_1 = 9, rank 3, FO2 bound 7. Examples of limits: nc_d6_k1_s23 = {x e_0^T} (+) three single-row
             elements (section 2.5); seed_d6_e3_t4 = e_1 (x) (3-dim) (+) three single-column elements; nc_d6_k1_s4: row-projection
             ranks (3,3,3,3). Phi-rank 0, 1 or 2.
 2.2 Line-kernels of the 7 known 7-dim spaces (a10.py, a12.py): the 21 six-dim kernels are Type F (rows/columns: L080 columns 0-3,
     ex1/ex2/ex3/fam2/s-family row 4; Omega = C^5, dim T_1 = 12, rank 6, FO2 bound 9, except ex1 = rc45) or Type NC (L080 rows
     0-3, ex2 columns 2,3, ex3 columns 0,1, ...; Omega = span(1,e_c), T_1 = 9, FO2 = 7). So FO2 alone does NOT exclude dim 9 for the
     Type F kernels with Omega = C^5; FL does.
 2.3 Extension censuses (ext6.py, ext6c.py; every 6-dim level space containing M_b lies in E_0(M_b)): from 16 bases of dim 4, 5
     (60 solutions, all NC), from random 2-,3-dim subspaces of 8 six-dim spaces (61 solutions: the space itself, F or NC), from
     the 3-,4-dim line-kernels (25 solutions: 17 F, 8 NC). No space of another type. (Early "OTHER" labels were tolerance
     artefacts of singular convergence: defect singular values 1e-5; with relative tolerance 1e-4 they are NC or the F seed.)
 2.4 Maximality (a13.py): for all 41 spaces of 2.1-2.2, E_0(M) = M (+) C d with d a row-mean direction x (x) 1 (Type F) or a
     column-mean direction 1 (x) (5 e_c - 1) (Type NC), and P_2(d) != 0: none lies in a 7-dim 4x5 level space.
     5-dim census (ext5.py, 53 spaces): dim Omega in {2,3,4,5}; Omega = C^5 with Phi = 0 occurs with a full free row (9 times) and
     once without (a space with a full free column of its 4 rows) -- relevant for REGIME 1 only.
 2.5 EXACT Type NC family [hand proof]. w0, w1, w3 in C^4 (placed in columns 1..4) with sum w_i = 0, <w_i,w_j> = 0 (i != j),
     sum_c w0_c w1_c w3_c = 0;  M := {x e_0^T : sum x = 0} (+) C e_0 w0^T (+) C e_1 w1^T (+) C e_3 w3^T (dim 6 if all w_i != 0).
     Proof of level: expand F(J'+Y) along column 0: F = N_0 + sum_i (1 + x_i) n_i, n_i := sum over injections of the rows != i
     into columns 1..4. Rows are 1 + a_i w_i (i = 0,1,3) and 1 (i = 2). For rows with zero sums a 3x4 injection sum is
     24 - 2 sum_{pairs}<.,.> + (triple term), the triple term being 2 sum_c of the triple product when the pairwise dot products
     vanish; so n_0 = n_1 = n_3 = 24 (one of the three rows is 1), n_2 = 24 + 2 a_0 a_1 a_3 sum_c w0_c w1_c w3_c = 24, and
     N_0 = perm_4 with a row of ones = n_2 = 24. Hence F = 24 + 96 + 24 sum x_i = 120, and N_0 = 24: column 0 is neutral. QED
     Member w0 = (1,-1,0,0), w1 = (0,0,1,-1), w3 = (1,1,-1,-1): exact rational check of level; e = 3, dim T_1 = 9,
     Omega = span(1, e_0), FO2 bound (9,3) -> 7 (fam_nc.py).

## 3. What the regime a_r >= 2 now needs   [WRITTEN 19:30 -- SUPERSEDED by section 4 and by the RESULT block: (S6') is FALSE (family M*);
##    the statement to prove is (S6-FO2). Sections 2.1-2.5 remain correct as data; the F / NC dichotomy of 2.3 is incomplete.]
 (S6') every 6-dim 4x5 level space without a full free row has dim Omega <= 2.   Then (RESULT C) no 9-dim level space has a row or
 column with a_r >= 2, and more: dim L_r >= 6 implies dim L <= dim L_r + 1.
 Suggested split: (i) [structure] a 6-dim 4x5 level space has a full free row or a neutral column c with C(M) = e_c^perp cap 1^perp
 (then M = transposed defect extension of the 4x4 level space M^(c) of type (d',e') in {(3,0),(4,1),(5,2)}: the extremal cases of
 the 4x4 defect inequality); (ii) [no twist] for such M, im gamma cap im delta = constants. In the language of L2: the defect
 vectors p_k(Y) (k = 1,2,3) must all be weighted column sums of relations among G_0..G_3; in the language of L3: no column scaling
 other than span(1, e_c) preserves levelness of M to first order.
 Weak form sufficient for a_r = 2 alone: "dim Omega <= 3 without a full free row". For a_r = 3 alternatively: "no 7-dim 4x5 level
 space" (all 41 known 6-dim spaces are maximal).
 Files: reg2/{t,a1,a2,a5,a6,a7,a8,a9,a10,a11,a12,a13,show}.py (invariants), ext6.py, ext6b.py, ext6c.py, ext5.py (censuses),
 fam_nc.py (exact family), chk_lemma.py (sanity of section 1), M_L080_col0.npy, M_ex2_row4.npy (Type F with Omega = C^5),
 ext_*.npy (new NC spaces). Heavy-computation plan: COMPUTE-reg2.md.
STATUS 19:40: exact certificates (exact_T1.py) and the 7-dim extension search (ext7.py) added; RESULT block final. Remaining budget
 used for one more attempt on (ii) "neutral column => no twisted extension" (lead below).
STATUS 19:50: CORRECTION of the 19:18-19:40 picture. Two new censuses not seeded from known spaces (reg2/linespan.py: spaces spanned by
 single-row and single-column elements, 45 support patterns; reg2/drsearch.py: deletable row with free part of dim u) found
 6-dim level spaces OUTSIDE Types F / NC, among them the exact family M* with dim Omega = 4. (S6') is false. RESULT rewritten.

## 4. Deletable-row families and M* (found 19:40-19:50)
 4.1 linespan.py (M = sum of single-row parts e_i (x) U_i and single-column parts V_c (x) e_c, dims (u_i), (v_c), total 6; 45 patterns,
     2 starts each, two seeds): solutions for 12 patterns; NC for (3,0,0,0|3), (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1), (2,1|1,1,1),
     (1,1,1|3), (1,1,1|2,1); and a type with e = 4, NO neutral column, Omega = span(1, e_c), (2,9,7), for (2,2|2), (2,1,1|2),
     (3,1|2), (3,1|1,1): there one row i meets M only in its single-row part (M = e_i (x) U (+) M_i, a deletable row with free
     part U of dim 2 or 3; rows' L(L'') spaces built from 3x5 spaces are of this kind).
 4.2 drsearch.py u (M = e_3 (x) U (+) N, dim U = u, N in rows 0-2 arbitrary): u = 3: 4 solutions in 25 starts: three with
     (dim Omega, T_1, FO2) = (3,10,8), Omega = span(e_a, e_b, 1 - e_a - e_b), single-row part of row 3 exactly 3-dim; one whose sparse
     limit is M* (4,11,8). u = 2: 1 solution in 4 starts (not analysed).  Each (3,10,8) space lies in 7-dim level spaces but in no
     8-dim one (reg2/ext55.py: 0 of 12 starts each, Gr(2,4)), like rc45.
 4.3 THE FAMILY M*(x,y) [exact; hand proof of level]. U := {w : sum w = 0, w_1 = w_2}; x, y in C^3 with sum x = sum y = 0, <x,y> = 0.
     M_0 := e_3 (x) U (+) C x e_0^T (+) C y e_3^T has equal columns 1 and 2 and is level: P_1 clear; P_2: the pairings are
     -<x,y> = 0, w_0 x_3 = 0 (x has no row 3), P_2(x e_0^T) = 0; P_3: only the triple (w, x, y) contributes,
     (sum_{i != i'} x_i y_i')(sum_{j != 0,3} w_j) = -<x,y>(...) = 0; P_4 = 0 because three of the rows 0,1,2 would have to use the two
     columns 0, 3. By rows' Lemma EC (equal columns 1, 2) M* := M_0 (+) C e_2 (e_1 - e_2)^T is level. dim M* = 6; row 3 carries only U.
     Exact rational member x = (1,-1,0), y = (1,1,-2) (reg2/mstar2.py, Mstar2.npy): level at 320 integer points, rank_Q of the gradient
     span = 14, dim T_1 = 11, Omega^perp = C(e_1 - e_2), e = 4, Phi = 0; FO2: exact rank 5 on the 11-dim kernel => dim <= 8.
     Other members ((2,-1,-1),(0,1,-1)); x = y = (1,w,w^2); ((1,2,-3),(5,-4,-1)): same invariants (11, 4, 8) numerically.
     Why Omega is large: U o s lies in U + C1 for every s constant on {1,2} (a 4-dim algebra), and the three other generators are
     single-line or equal-column elements. Extensions (ext55.py, ext55b.py): 7-dim level spaces M* (+) C t exist (9 of 12 starts,
     row-r rank 1); 8-dim: 0 of 82 starts (2-planes in the 5-dim T_1/M*).
     Meaning: M* is the first 6-dim space without a full free row that is first-order admissible as L_r for a_r = 2; any proof of
     the regime must use second-order (P_2-type isotropy) information or FL-type arguments, not only T_1.
 4.4 EC MOVES (reg2/ecmove.py; level by rows' Lemma EC; numerical invariants). For a Type F space e_3 (x) 1^perp (+) N whose N has two
     equal columns a, b, replace the free-row direction e_3 (e_a - e_b)^T by e_i (e_a - e_b)^T, i in {0,1,2}. All 30 spaces built
     this way (N = {x e_4^T : sum x = 0}: six pairs (a,b); N = C x e_0^T + C y e_3^T: three pairs; i = 0, 2) are 6-dim, level, without
     full free row, e = 4, and have (dim Omega, dim T_1, FO2) = (4, 11, 8) -- the Type F parents have (5, 12, 9). So moving one
     free-row direction costs one dimension of Omega and one unit of the FO2 bound. (rc45's plane has no equal columns.)
     OPEN and decisive: is there a 6-dim 4x5 level space without a full free row and with FO2 bound >= 9 ? None among ~200.
 4.5 DOUBLE MOVES (reg2/ecmove2.py). Row 3 keeps a 2-dim part U = {w_a = w_b = w_c} or {w_a = w_b, w_c = w_d} of 1^perp and the two
     complementary directions are placed in rows of {0,1,2} (same row, or two rows with orthogonal directions e_a - e_b and
     e_a + e_b - 2 e_c, resp. e_a - e_b and e_c - e_d): 15 of the 20 variants tried are level (6-dim, single-row parts (2,0,0,2),
     (1,1,0,2), ...), all with (dim Omega, dim T_1, FO2) = (3, 10, 8). Empirical law along the chain Type F -> one move -> two
     moves: Omega 5 -> 4 -> 3, T_1 12 -> 11 -> 10, FO2 bound 9 -> 8 -> 8. So in everything found:
          FO2 bound = 9  <=>  full free row (and Omega = C^5);   no full free row  =>  FO2 bound <= 8.
STATUS 19:55: COMPUTE-reg2.md revised (families DR, M*; target (S6-FO2); census E). Final report follows.
