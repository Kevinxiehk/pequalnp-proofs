# NOTES-reg2 (role reg2; start 18:47, budget 100 min -> ends ~20:27). Regime: some row/column with a_r >= 2.
## RESULT ROUND 2 (reg2, 19:59 - 21:xx; details in sections 5 - 8) -- the regime is NOT closed; four new rigorous pieces
 R2-1 [RIGOROUS, hand; section 5] THEOREM SP8: a level space of 5x5 matrices containing e_i (x) {w : sum w = 0, <m,w> = 0} has dim <= 8 if
      m = e_a - e_b, or if <m,m> != 0 and it contains e_i' m^T for another row i'. (stage2's (Z3): L_i is a 4x5 level space with defect in C m;
      then verifyfl's TC5 / SPLIT / SL.) This excludes, for ALL parameters and without computation, the families that defeated the
      first-order criterion: M*_1(x,y), M*_2, every single EC move of a Type F space, and the DR3 spaces with their split element.
 R2-2 [RIGOROUS; 8.1] (a) FO2 bound(M) <= dim T_1(M) - 1 for every M (q_0 = 12 P_2 is nonzero on tau_r in T_1(M)); so dim T_1(M) <= 9 implies
      (S6-FO2) for M. (b) (S6-FO2) + FL exclude a_r = 3 as well as a_r = 2 (6-dim subspace of L_r) -- as verify2 noted.
 R2-3 [EXACT, char 0, all charts, calibrations non-unit; 8.2, 8.3] with Singular / msolve in this container:
      NC family M(w0,w1,w3) (pattern (1,1,1|3)): Omega = span(1,e_0), E_0 = M + C d, dim T_1 = 9 for EVERY member;
      the WHOLE support pattern (2,2|2) (a new explicit 2-parameter family M(mu), level for every mu): dim T_1 = 9 except at the 0/1
      vectors mu, where (dim T_1, dim Omega, rank q) = (10, 3, 4). So (S6-FO2) holds on both (every level space containing a member has
      dim <= 8; dim <= 7 if it is L_r and mu is not 0/1), and all these spaces are maximal 4x5 level spaces.
 R2-4 [RIGOROUS; 7.1-7.3] Lemma DL / Proposition MAX: row i deletable <=> (e_i - 1/4) (x) 1 in E_0(M); neutral column c => 1 (x) (e_c - 1/5)
      in E_0(M); P_2 = -15/2, -24/5 on these directions; so a space with a deletable row or neutral column and dim E_0 = dim M + 1 is
      maximal. Hence "every 6-dim 4x5 level space has a deletable row or neutral column and dim E_0 = 7" would give "4x5 level <= 6".
 R2-5 [section 6] FILTER for regime 1: a row with a_r = 1 needs Phi = 0 and Omega(L_r) = C^5 (one SVD). Generic hyperplanes of the Type F
      spaces with Omega = C^5 pass it (and FO2 = 9): by (Z3) they are regime-1 candidates exactly if a (5,1) space with a generic line
      exists. Hyperplanes of M* fail it or are excluded by SP8.
 STATUS OF "L_r = M (dim 6) inside a 9-dim level space", by family:   F: FL [rigorous];   M*, EC moves, DR3-split: SP8 [rigorous];
      pattern (2,2|2), NC family (1,1,1|3): [exact];   other NC / DR2 spaces: criterion A with Omega computed per space [numerical];
      DR3 with isotropic or non-split m: none found; reduces to "(5,1) with that line".
 NOT DONE: target (1) "6-dim => deletable row or column" (no proof; upstream L_gct_215 has no dim-6/7 structure statements beyond the
      case tree, see 7.4); target (3) reduced to (1) + dim E_0 = 7 (7.3) or to (S6-FO2) (8.1(b)); no 7-dim space found.
 EMPIRICAL LAW (EL) [numerical, 7.5]: Omega(M) lies in {s : U_i o s inside U_i + C1} for every single-row part of a 6-dim M (55 rows, 0
      violations); if true for L_r in regime a_r = 2 it forces every single-row element outside row r to be a multiple of e_i (e_a - e_b)^T.
 Best next steps: TASK X1 of COMPUTE-reg2.md section 7 (exact treatment of the remaining line-spanned patterns; each run is seconds with
      reg2/gb/famtool.py), a proof of (EL), and the classification (1).

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
    (COMPUTE-reg2.md, sections 1-3b; the equal-column extensions of 5-dim equal-column spaces are the place to look: M* is one);
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
 4.6 EXACT certificates (reg2/exact_fo2.py, Fractions; gradient rows at 300 integer points, exact kernel, exact rank of q_Y on it):
       M*_1 with (x,y) = ((1,-1,0),(1,1,-2)), ((2,-1,-1),(0,1,-1)), ((1,2,-3),(5,-4,-1)) and
       M*_2 := e_3 (x) {sum w = 0, w_1 = w_2} (+) {x e_4^T : x in C^3, sum x = 0} (+) C e_2 (e_1 - e_2)^T  (unique up to symmetry):
            dim ker = 11, Omega inside (e_1 - e_2)^perp, rank q = 5  =>  every level space containing the space has dim <= 8  [THEOREM for
            these four spaces, given that they are level (section 4.3 / Lemma EC)];
       Type F parent e_3 (x) 1^perp (+) {x e_4^T}: dim ker = 12, Omega = C^5, rank q = 6: second order allows 9; only FL excludes it.
     Up to row/column permutations the single EC moves of the two known kinds of Type F spaces with Omega = C^5 are exactly M*_2 and the
     one-parameter family M*_1(x). Remark: M* contains rows' split pair e_3 (x) U (+) e_2 (x) U' with U' = C(e_1 - e_2) (two-column m);
     Theorem FL2* gives only dim <= 10 - dim(U o U') = 9 there -- this is the case the team already found delicate (verifyfl's TC5).
STATUS 19:56: final. Scripts added since 19:40: linespan.py, drsearch.py, look3.py, look4.py, mstar2.py, mstar2_fo2.py, exact_fo2.py, ecmove.py,
 ecmove2.py, ext55.py, ext55b.py, ext7.py; data: Mstar2.npy, dr_u3_*.npy, ec_*.npy, ec2_*.npy, linespan_other_*.npy.
 4.7 (reg2/ecmove3.py) EC moves of the Type F row-4 kernels of ex2, ex3, fam2 and the s-family (their N lives on two columns, three
     zero columns): 24 more spaces, all level, all (dim Omega, dim T_1, FO2) = (4, 11, 8). Total: 54 single-move spaces, all (4,11,8).

# ROUND 2 (start 19:59, budget ~2 h). Targets: (1) deletable line at dim 6, (2) (S6-FO2) family by family, (3) a_r = 3, (4) FILTER.
STATUS 20:08: (2) the families with a 3-dim single-row part (M*, EC moves, DR3) are now excluded from 9-dim level spaces by a HAND proof
 (Theorem SP8 below: stage2's (Z3) + verifyfl's TC5 / SPLIT), no computation. (4) FILTER tested. NC family: 10 random members (2,9,7).

## 5. Theorem SP8 and the family-by-family status of "L_r = M, dim L = 9" (round 2)
 5.1 (Z3) in the form used [rigorous; = stage2 (Z3) / rows' saturation; 3 lines]. L level 5x5, i a row, Z_i := {w : e_i w^T in L} (single-row
     part, inside 1^perp), L_i := L cap {row i = 0} (a 4x5 level space), W_i := row-i projection of L. Then
        (a) C(L_i) lies in Z_i^perp cap 1^perp (dim 4 - z_i),      (b) dim L = dim L_i + dim W_i <= dim L_i + 4.
     Proof: for t in L_i, w in Z_i: perm(J + t + e_i w^T) = perm(J + t) + <w, N(J' + pi_i t)>, both permanents are 120.  QED
     So in a 9-dim level space, for EVERY row i (and column), L_i is a 4x5 level space of type (4 + a_i, <= 4 - z_i).
 5.2 THEOREM SP8 [rigorous given verifyfl's TC5, SPLIT and Lemma SL, all verified]. Let L be a level space of 5x5 matrices containing
     e_i (x) U, U = {w : <1,w> = 0, <m,w> = 0} (dim 3), m in 1^perp. If  (a) m = e_a - e_b,  or  (b) <m,m> != 0 and e_i' m^T is in L for
     some row i' != i,  then dim L_i <= 4 and dim L <= 8.
     Proof: by 5.1(a) L_i is level with defect inside C m. (a): TC5 ("a 4x5 space with defect line inside C(e_a - e_b) has dim <= 4").
     (b): e_i' m^T lies in L_i; defect 0: Lemma SL (dim <= 3); defect line C m, non-isotropic, split: Theorem SPLIT (dim <= 4).
     Then 5.1(b).  QED      [Compare rows' FL2*: 10 - dim(U o m) = 7, 8, 9 for |supp m| = 4-5, 3, 2; SP8 gives 8 also for two columns.]
     COROLLARY (regime a_r = 2, hand proof, all parameters): L_r cannot be a member of the families M*_1(x,y), M*_2, any single EC
     move of a Type F space (they contain e_3 (x) {w_a = w_b} and e_i (e_a - e_b)^T), nor a DR3 space containing its split element
     e_i' m^T with <m,m> != 0 (the four DR3 spaces found by drsearch do: m two-column up to 1e-3 in three of them, three-column in one).
     Sanity (pfr_chk.py): in the 7-dim spaces M* (+) C t, row 3 has rank 4, L_3 is a (3,1) space with defect direction e_1 - e_2.
     In general: a 3-dim single-row part e_i (x) {1,m}^perp in a 9-dim level space  <=>  L_i is a (5,1) [or (6,1)] space with line C m:
     the team's open (DI_5) case e = 1, now only for the lines m NOT covered by TC5 / SPLIT / PR3.
 5.3 STATUS TABLE for M = L_r of dimension 6 in a 9-dim level space (census families of section 4):
       F  (full free row)                                    excluded: Theorem FL                          [rigorous]
       M*, EC moves, DR3-split (3-dim single-row part)       excluded: Theorem SP8                         [rigorous]
       DR3 non-split or isotropic m                          none found; would need "no (5,1) with line C m"
       DR2, NC (dim Omega = 2)                               excluded by criterion A: dim L <= 7           [rigorous GIVEN Omega(M) = span(1,e_c);
                                                             Omega computed per space: exact for 2 spaces, numerical for the others]
     So what is missing for a proof of the regime is (i) the classification "6-dim => one of these families" and (ii) a structural
     proof of dim Omega = 2 for DR2 / NC (symbolic tasks G1, G2 in COMPUTE-reg2.md section 7).
 5.4 NC family of section 2.5: 10 random members (fam_nc2.py): (e, dim T_1, dim Omega, FO2, dim E_0) = (3, 9, 2, 7, 7) for all.

## 6. FILTER for regime 1 (rows with 4-dim projection), from criterion A  [statement rigorous; tests numerical, reg2/filter1.py]
 Let L be a 9-dim level space and r a row with a_r = 1 (W_r 4-dim, M := L_r 5-dim). NECESSARY:
   (F1) M is a 4x5 level space with Phi = 0 on M (all five 4x4 subpermanents vanish identically)           [stage2 (Q-r)(ii)]
   (F2) Omega(M) = C^5, i.e. dim T_1(M) = dim E_0(M) + 5: EVERY e_j (j = 0..4) is the row-r part of a first-order extension, equivalently
        each deletion permanent N_j(J'+Y) restricted to M is of the form -D_X F(J'+Y) (g(M) = e(M) + 1: all defect functions twisted-
        realisable). Proof: W_r (dim 4) lies in Omega(M) and misses 1, which is in Omega(M).   [new, cheap: one SVD]
   (F3) for every OTHER row i: L_i is a (4 + a_i, <= 4 - z_i) space (5.1); in particular a 3-dim single-row part of M in row i forces a
        (5,1) space with that line, impossible in the cases of SP8.
   (F4) FO2 bound(M) >= 9.
 Tests (5-dim spaces; invariants (Phi-rank, dim Omega, dim T_1, FO2)):
   generic hyperplane of a Type F space with Omega = C^5 (F1 = free row (+) {x e_4^T}, F2 = free row (+) C x e_0^T (+) C y e_3^T):
        (0, 5, 12, 9), single-row part of dim 3 with a GENERIC line m: passes F1, F2, F4. By (F3) it is a regime-1 candidate exactly if a
        (5,1) space with a generic line exists: these hyperplanes are the "(5,1) problem" seen from the other side.
   hyperplane of F1/F2 obtained by dropping a free-row direction: (0, 5, 13, 9): same remark (m two-column: excluded by SP8(a)).
   generic hyperplane of M*_1, M*_2: (0, 4, 11, 8): FAILS (F2) and (F4).
   special hyperplanes of M*: drop x e_0^T or y e_3^T: (0, 4 or 5, 15, 10): pass first/second order, but contain the split pair: excluded
        by SP8(b) -- an example where SP8 is strictly stronger than FO2; drop the EC element: (0, 5, 15, 10), m two-column: SP8(a).
   5-dim census of round 1 (ext5.py, 53 spaces): Omega = C^5 with Phi = 0 in 10 of them: 9 with a full free row, 1 without.
 So (F2) removes most 5-dim level spaces, and what survives so far all contains a 3-dim piece of a free row, i.e. reduces by (F3) to (5,1).

## 7. Deletable lines, maximality and the 7-dim question (targets 1 and 3)   [rigorous unless marked]
 7.1 LEMMA DL. For a 4x5 level space M:  (a) row i is deletable (pi_i(M) is a 3x5 level space)  <=>  d_i := (e_i - (1/4) 1) (x) 1 lies in E_0(M);
     (b) column c neutral (N_c(J'+Y) = 24 on M)  =>  d^c := 1 (x) (e_c - (1/5) 1) lies in E_0(M);
     (c) P_2(d_i + Y) = -15/2 and P_2(d^c + Y) = -24/5 for every Y in M.
     Proof. (a) D_{e_i 1^T} F(J'+Y) = 2 F_3(rows != i of J'+Y) (each injection of three rows into five columns misses two columns) and
     D_{J'} F(J'+Y) = 480 (L1(c)); so D_{d_i} F = 2 F_3 - 120 vanishes iff F_3 = 60. (b) Let p = perm_4, A = J_4 + Y^(c), v = 1 + y_c.
     Level and neutral: F = p(A) + D_{v 1^T} p(A) = 120, p(A) = 24, so D_{v 1^T} p(A) = 96; M^(c) is a linear level space, so
     D_{Y^(c)} p(A) = 0 and D_{J_4} p(A) = 4 p(A) = 96; hence D_{1 e_c^T} F(J'+Y) = D_{J_4} p(A) = 96 = D_{J'}F / 5.
     (c) b'(d, Y) = D_d P_2(Y) = 0 for d in E_0(M), and P_2(x (x) 1) = -10 sum x_i^2, P_2(1 (x) y) = -6 sum y_j^2 for sum-zero x, y.  QED
 7.2 PROPOSITION MAX. If M has a deletable row or a neutral column and dim E_0(M) = dim M + 1, then M is a maximal 4x5 level space.
     (Any level space containing M lies in E_0(M) = M + C d, and P_2(d + Y) != 0.)  All 41 spaces of sections 2.1-2.2 and the
     exact members of sections 2.5, 4.3 satisfy the hypotheses numerically (dim E_0 = 7).
 7.3 COROLLARY (what a 7-dim 4x5 level space M_7 must look like). (i) no full free row (rows' SL_3 corollary); (ii) no two equal
     columns (upstream L_gct_215, abbrev eI, Lean-checked); (iii) every 6-dim subspace M_6 has E_0(M_6) containing M_7; if M_6 has a
     deletable row or neutral column then dim E_0(M_6) >= 8 (the direction d is in E_0(M_6) but not in M_7). In particular a 7-dim space
     with a neutral column c (or deletable row) has ALL its 6-dim subspaces of this kind -- never seen: every 6-dim level space found
     (about 250 by now) has a deletable line and dim E_0 = 7 [numerical].
     So: "every 6-dim 4x5 level space has a deletable row or neutral column and dim E_0 = 7"  ==>  no 7-dim 4x5 level space  ==>  a_r <= 2.
     (iv) [numerical] extension search for dimension 7 through 45 known 3-,4-,5-dim spaces: 0 of 132 starts (ext7.py; N = 330 sample
     points = number of monomials, see COMPUTE-ERRATA A5: to be redone with N >= 400 on the 24-core machine).
     For a 9-dim L with a_r = 3: M_7 = L_r must in addition have dim Omega(M_7) >= 3 (criterion A) and e(M_7) <= 4 - z_r (5.1).
 7.4 What upstream L_gct_215 contains (read: statements only; proofs are 7.5k obfuscated lines). Case tree for an 8-dim L by u_i = dim of the
     single-row part of row i and p_ij = rank of the projection to rows i, j:  u_i >= 4 (aG7: then dim <= 7);  2 <= u_i <= 3 (MidCase);
     u_i = 1 (mI: produces a 7-dim level space with two equal columns; eI: none exists; the 7-dim lemmas vR, uQ, aAp, aGk, xQ, aEu, vU,
     aEv, aDh are all UNDER the equal-columns hypothesis);  all u_i = 0 (HighPair: some p_ij = 7; vK: all p_ij <= 6).
     General tool (aBu, pure linear algebra, any dimension d):  d + r_i <= p_ij + p_ik + u_l  for distinct rows i, j, k, l.
     Nothing in the file classifies 6- or 7-dim spaces; at dim 6 the tree gives only the case distinction itself. With 5.1 the cases read,
     for M = L_r (dim 6) inside a 9-dim L and a row i != r:  u_i = 4: FL;  u_i = 3: L_i is a (5 or 6, 1) space with line C m (SP8 closes
     m two-column and the split non-isotropic case);  u_i = 2: L_i is a (5,2) space [or (6,2)], a_i = 1;  u_i <= 1 for all i: the
     neutral-column / single-column side (transposed 5.1 for the column c).  Target (1) is NOT proved.
 7.5 EMPIRICAL LAW (EL) [numerical, reg2/autest.py: 55 rows of 29 six-dim spaces, 0 violations, equality in 47]:
        for a 6-dim 4x5 level space M and every row i with single-row part e_i (x) U_i:   Omega(M) lies in A(U_i) := {s : U_i o s in U_i + C1}.
     It is NOT a formal consequence of "e_i w^T in M": for (X;rho) in T_1(M), w in U_i, Y in M one has the exact identity
        perm[pi_i(J+Y) ; w o rho] = sum_k perm[pi_i(J+Y) with row k replaced by X_k - rho - Y_k o rho ; w]      (rows k != i, r)
     (column scaling of perm[Z ; w], which vanishes on pi_i(CJ + M) by 5.1), and the right side need not be a multiple of F: (EL) fails
     for one 3-dim subspace of a line-spanned space (lemA_test.py; deviation 5e-2), while it holds to 1e-14 on all 6-dim spaces.
     CONSEQUENCE IF (EL) HOLDS for L_r in regime a_r = 2 (Omega contains k^perp, dim 4): every single-row part U_i (i != r) of L is
     0, C k, k^perp cap 1^perp or 1^perp, and k = e_a - e_b is a two-column vector as soon as some U_i != 0, 1^perp [A(Cw) has dim
     6 - |supp w| or <= 2]. The last two cases are excluded (SP8(a), FL), so all single-row elements of L outside row r would be
     multiples of e_i (e_a - e_b)^T with u_ra = u_rb on L^.  (Stated as a target; not proved.)
STATUS 20:25: msolve / Singular runs (reg2/gb/): the NC family of 2.5 and the whole support pattern (2,2|2) are now settled EXACTLY
 (char 0, all charts, calibrations non-unit). verify2's remark checked: (S6-FO2) + FL exclude a_r = 3 as well (section 8.1).

## 8. Exact results with msolve / Singular (round 2; scripts reg2/gb/polylib.py, famtool.py, gen_nc.py, gen_dr22.py; reg2/dr22_exact.py)
 8.1 Two remarks [rigorous].
   (a) q_0 := D^2 perm(J) = 12 P_2 and tau_r = J - 5 e_r 1^T lies in T_1(M) for every M, with P_2(tau_r) = -200. So the rank of q_0 on T_1(M) is
       >= 1 and  FO2 bound(M) <= dim T_1(M) - 1  ALWAYS: every level space containing M has dim <= dim T_1(M) - 1. In particular
       dim T_1(M) <= 9  ==>  (S6-FO2) for M; and (S6-FO2) for M with dim T_1 = 10, 11 means rank q >= 3, 5.
   (b) (S6-FO2) + FL  ==>  no 9-dim level space has a row or column with a_r >= 2 -- INCLUDING a_r = 3: if dim L_r >= 6 take any 6-dim
       subspace M_6 of L_r; either M_6 contains a full free row (then L does: dim L <= 7 by FL) or FO2 bound(M_6) <= 8 and L contains M_6.
       (My round-1 statement "a_r = 3 needs the non-existence of 7-dim 4x5 spaces" was unnecessarily weak: the FO2 bound holds for every
       level space CONTAINING M_6, not only for those with L_r = M_6.)
 8.2 THEOREM NC-FAM [EXACT, char 0]. For every member M(w0,w1,w3) of the family of section 2.5 (w_i != 0):
        Omega(M) = span(1, e_0),   E_0(M) = M (+) C d^0 (d^0 = 1 (x) (5 e_0 - 1)),   dim T_1(M) = 9.
     Hence: L_r = M => dim L <= 7 (criterion A); every level space containing M has dim <= 8 (8.1(a)); M is a maximal 4x5 level space (7.2).
     Method (gen_nc.py): variables w0, w1, w3 (12), X (20), rho (5); equations: the 7 family relations, the 32 coefficient equations of
     D_t perm(J + (Y;0)) = 0 in y (the polynomial has only 32 monomials in y), a parameter chart a_1 = 1, b_j = 1, c_l = 1 (five charts
     (1,1,1), (1,1,2), (1,2,1), (1,2,2), (1,2,3) cover all members up to the S_4 symmetry of the columns 1..4), and
       Omega-test: rho_0 = 0, rho_1+..+rho_4 = 0 (allowed: subtract tau and e_r (5e_0 - 1)^T), chart rho_j = 1 (j = 1..4): 20 systems;
       E_0-test:   rho = 0, column 0 of X zero, x_{0,ja} = x_{1,jb} = x_{3,jc} = 0 (X modulo M + C d^0), chart x_ib = 1: 65 systems.
     Results: UNIT IDEAL in all 85 systems over Q (Singular std, 14 s + 3 s) and modulo 65521, 2147483629, 1073741789 (msolve, 4 s each).
     Calibrations (must be non-unit, and are, over Q and mod p): rho = e_0 (basis sizes 151-187); column 0 of X free with x_00 = 1 (110-123).
 8.3 THEOREM DR22 [EXACT, char 0]: the complete support pattern (2,2|2) (two rows with 2-dim single-row parts, one column with a 2-dim
     single-column part, direct sum of dimension 6).
     (i) [hand] P_1, P_2 force, up to the symmetries: U_0 = {w : w_0 = 0, sum w = 0, <mu,w> = 0} (mu in C^4 on columns 1..4, not
         constant), U_1 = (U_0 + C1)^perp cap 1^perp = span(5 e_0 - 1, mu~ - mean), V = {x : x_1 = 0, sum x = 0};
         M(mu) := e_0 (x) U_0 (+) e_1 (x) U_1 (+) V (x) e_0.   [cases: both row parts vanishing at column 0, or V vanishing at both rows,
         are impossible by dimension.]
     (ii) [exact] in the chart mu = (0,1,m3,m4) ALL coefficients of F(J'+Y) - 120 vanish identically: M(mu) is level for EVERY mu.
          Row 1 is deletable, e = 4, no neutral column, no full free row.
     (iii) [exact] E_0(M(mu)) = M (+) C d_1 for every (m3,m4) (13 X-charts, elimination ideal (1)).
     (iv) [exact] in each of the four rho-charts the elimination ideal of {(m3,m4) : Omega not inside span(1,e_0)} is (m3^2 - m3, m4^2 - m4)
          (over Q and mod two 31-bit primes). So for mu NOT a 0/1 vector: Omega = span(1, e_0), dim T_1 = 9: dim L <= 7 if L_r = M, and <= 8
          for every level space containing M.
     (v) [exact, Fractions] the four special members mu = (0,1,0,0), (0,1,0,1), (0,1,1,0), (0,1,1,1) (mu = indicator of a column set T;
          two orbits): dim T_1 = 10, Omega = span(e_0, 1_T, 1_{T^c}) (dim 3), rank q = 4: every level space containing them has dim <= 8.
     So (S6-FO2) holds on the whole pattern (2,2|2). Calibration: rho = e_0 is non-unit (basis size 21). Numerics agree (dr22_num.py).
 8.4 Pattern remarks [hand]. In a line-spanned space the P_2 conditions are: <u,u'> = 0 for single-row elements in different rows, and
     u_c x_i = 0 for e_i u^T and x e_c^T. Hence for a row with a 3-dim part U = {1,m}^perp every single-row element in another row is a
     multiple of e_i' m^T: the patterns (3,1|2), (3,1|1,1) always contain the split pair, and SP8(b) applies when <m,m> != 0.
     Not yet treated exactly: (2,1,1|2) and the NC patterns (3|3), (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1), (2,1|1,1,1), (1,1,1|2,1)
     (all (2,9,7) numerically); precise task in COMPUTE-reg2.md section 7.
STATUS 20:35 (END OF ROUND 2, stopped on the coordinator's instruction): handover written: handover/HANDOVER-reg2.md.
 Added after section 8 was written: pattern (2,1,1|2) case (iii) EXACT (level for every mu; Omega = span(1,e_0), E_0 = M + C d_1 for every
 mu; reg2/gb/gen_dr211.py); case (ii) (reg2/gb/gen_dr211b.py): level conditions = P_2 relations + triple product, calibration non-unit,
 but the Omega-test over Q is NON-UNIT in chart (1,2,3), rho_2, rho_3, rho_4: UNDECIDED whether these members have a larger Omega
 generically; their (dim T_1, dim Omega, FO2) were NOT computed (reg2/dr211b_num.py is written but not run). First pending task.
 Small lemma not recorded above (P8 of the handover): a level 4x5 space with an identically zero column has that column neutral.
