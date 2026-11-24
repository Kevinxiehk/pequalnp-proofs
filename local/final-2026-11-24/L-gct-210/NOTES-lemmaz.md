# NOTES-lemmaz (role lemmaz: LEMMA Z = "doubly centred singular points of perm_5 have a zero line")

## RESULT
LEMMA Z is NOT proved in general and NOT refuted. Status by rank of g (g 5x5, DC, all 25 minor permanents 0):
  [round 2] the one-sided variant (only column sums zero) is FALSE (explicit matrix, section 3b (Z')): both centrings are
  needed. Rank 4 is equivalent to the adjugate statement (A) in section 3c; open sub-cases stated in section 5.
  rank 1: PROVED (2 lines).   rank 2: PROVED (hand proof, section 2; no computer).
  rank 3, 4: OPEN. No counterexample: (numerical) 30/30 fresh LM solutions have a zero line (lemmaz/gen.py; with
  methods' 31 that is 61/61); (numerical) the five Z5-symmetric families (twisted circulants g_ij = w^{ki} a_{j-i},
  the only shapes with a transitive symmetry, where a zero line would force g = 0) have NO nonzero solution
  (lemmaz/circ.py, 30 starts per k, residuals stall at 1e-3 with |a| = 0.3).
New exact tools for the open ranks (section 3, all hand-proved, one checked numerically to 1e-16):
  (R) row form: g special <=> for every i the product of the four rows l_k (k != i), as linear forms in y_1..y_5,
      is 0 in A = C[y]/(y_1^2,...,y_5^2).
  (T) torus form: Lemma Z <=> every g in Sing(perm_5) without zero line has e_j in rowspace(g) or e_i in
      colspace(g) for some i/j (no kernel vector with all coordinates nonzero on one of the two sides).
  (B) Kirkup relations: for three rows tau and the other two rows d, e: B_tau l_d = B_tau l_e = 0, B_tau the symmetric
      zero-diagonal 5x5 matrix of 3x3 subpermanents, B_tau[m,n] = perm g[tau; all columns but m,n].
  (K) generic closed form: if all 2x2 minors Delta_mn of rows d,e are nonzero, the solutions B of (B) form the line
      spanned by B[m,n] = 1 / prod_{k not in {m,n}} Delta_mk Delta_nk.  So in the generic stratum
      perm g[tau; T] * prod_{k in T} Delta_mk Delta_nk  (T = complement of {m,n}) does not depend on T.
  (N) Newton form (NEW, exact, checked 1e-14, lemmaz/newton.py): for column-centred g, in A:
        prod_{k != e} l_k = l_e^4 - (p_2/2) l_e^2 - (p_3/3) l_e + e_4,   p_m = sum_k l_k^m,  e_4 = sum_e prod_{k != e} l_k.
      So special <=> every row is a root of X^4 - (p_2/2) X^2 - (p_3/3) X over A (five roots with sum 0), and the rows are
      critical points of one squarefree quintic Psi on C^5 built from the 2nd and 3rd column moments of g.
  (G) g special <=> gamma^4 = 0 in C[x,y]/(x_k^2, y_j^2), gamma = sum g_kj x_k y_j; DC <=> gamma is killed by both
      lowering operators F_x, F_y (F = sum_j (d_j - y_j d_j^2)).
  (Z_n) the n x n analogue: n = 3 PROVED (g = 0); n = 4 numerically true, 25/25 LM solutions have a zero line.
Part (3) (level space L whose DC part K is all special): only conditional/structural statements, NO new unconditional
  dimension bound (section 4; round 2: trichotomy 4.6 gives d <= 4 unless the generic element of K has a single zero
  line, and a new exact DC special level plane K_new of that last type): common zero line (needs Lemma Z, or only rank <= 2 elements); d <= 6 always, d <= 4 if
  K has two common zero rows (L157); exact row-5 identities (4.3) that couple the row-5 part of L to the 4x5 part.
  The rectangular lemmas in the project (L101, L156, L157: <= 3 rows; L_gct_180/198/208: constructions only) do not
  bound a 4x5 level space, and a bound for L' = L cap {row 5 = 0} alone cannot work (LS(4,5) >= 6, so 6 + 5 > 8).
Best next step: section 5.

## 1. Setting, rank 1
g in C^{5x5}, rows l_1..l_5, columns sum to 0 (sum_k l_k = 0), rows sum to 0. M_ij = permanent of g minus row i, col j.
"Special" = all M_ij = 0 (then perm g = sum_j g_1j M_1j = 0).
Rank 1: g = u v^T, sum u = sum v = 0, M_ij = 24 prod_{k != i} u_k prod_{l != j} v_l. All vanish iff u has two zero
entries or v has two zero entries. So g has at least two zero rows or two zero columns.  QED

## 2. Rank 2 (PROVED): a DC special g of rank 2 has a zero row or a zero column
Write g = u v^T + u' v'^T, (u,u') independent, (v,v') independent. g 1 = 0 gives sum v = sum v' = 0; likewise
sum u = sum u' = 0. Put lambda_i = u_i x + u'_i y, mu_j = v_j x + v'_j y (binary linear forms), U_i = prod_{k != i} lambda_k,
V_j = prod_{l != j} mu_l (binary quartics), and <f,h> = sum_k k!(4-k)! f_k h_k (f_k = coefficient of x^k y^{4-k}).
 (a) perm(p q^T + p' q'^T) = sum_k k!(n-k)! E_k(p,p') E_k(q,q') for n x n, E_k(p,p') = coefficient of x^k in prod(p_i x + p'_i)
     (expand prod_i (p_i q_s(i) + p'_i q'_s(i)) over the set S of rows taking the first term). Hence M_ij = <U_i, V_j>.
 (b) Assume no zero row and no zero column: all lambda_i, mu_j != 0. The U_i span a space of dimension r_U = number of
     classes of proportional lambda_i (divide by the gcd and evaluate at the roots); same for V. <,> is nondegenerate on
     the 5-dim space of quartics, so r_U + r_V <= 5. r_U, r_V >= 2 (else rank 1). After transposing, r_U = 2.
 (c) The row vectors w_i = (u_i,u'_i) lie on two lines C a, C b and sum to 0, so each class sums to 0, so has >= 2
     members: classes {1,2}, {3,4,5} after permuting rows. Changing basis in C^2 (which does not change g):
     a = (1,0), b = (0,1), i.e. u = (c,-c,0,0,0), u' = (0,0,c_1,c_2,c_3), all nonzero, sum c_i = 0. Then
     U_5 = -c^2 c_1 c_2 x^2 y^2 and U_1 = -c c_1 c_2 c_3 x y^3, so M = 0 says: every V_j has no x^2y^2 and no x y^3 term,
     V_j in Wq := span(x^4, x^3 y, y^4).
 (d) Take j, l with mu_j, mu_l not proportional and C := prod_{k != j,l} mu_k (cubic, nonzero). V_j = C mu_l, V_l = C mu_j,
     so C x and C y lie in Wq. For C = a x^3 + b x^2y + c' xy^2 + d y^3: Cx in Wq gives c' = d = 0, Cy in Wq gives b = 0.
     So C = a x^3: mu_k is a multiple of x, i.e. v'_k = 0, for the three k outside {j,l}.
 (e) Z := {k : v'_k = 0}. By (d), Z contains the complement of every non-proportional pair, and such a pair exists.
     Z is not everything (v' != 0). Pick j outside Z, l in Z (not proportional: mu_j has a y-term, mu_l = v_l x != 0):
     the other three indices lie in Z, so Z = all but j, v' = v'_j e_j, and sum v' = 0 gives v' = 0. Contradiction. QED
 Remark: (a) for r summands is perm(sum_a p^a (q^a)^T) = <prod_i lambda_i, prod_j mu_j> with <x^m, x^m> = m! on forms
 in r variables (the L099/L089 type formula), so M_ij = <U_i, V_j> for every rank; only steps (b)-(e) used r = 2.

## 3. Tools for rank 3 and 4 (exact)
A := C[y_1..y_5]/(y_j^2); A_d has basis y_T, |T| = d; rows are elements l_k = sum_j g_kj y_j of A_1.
 (R) The coefficient of y_{all but j} in prod_{k != i} l_k is M_ij. So special <=> all 4-fold products of the rows are 0 in A.
     With sum_k l_k = 0: l_a l_b l_c l_d = 0 and l_a l_b l_c (l_a + l_b + l_c) = 0 for the four triples of a fixed 4-set.
 (T) perm's singular locus is stable under row/column scalings; D_1 g D_2 is DC iff D_2^{-1} 1 in ker g and D_1 1 in ker g^T.
     A subspace inside a union of coordinate hyperplanes lies in one of them; ker g inside {y_j = 0} <=> e_j in rowspace.
     So Lemma Z is a statement about Sing(perm_5) only (whose components are not known in the literature:
     Boralevi-Carlini-Michalek-Ventura arXiv 2402.17839 give only codim bounds for 5x5, and for 4x5 matrices with
     vanishing maximal subpermanents the component types: zero row / zero column + complementary permanent 0 /
     three rows with all 3x3 subpermanents 0 ("cone over P_{3,5}") / one "Kirkup" component, all of codim 5).
 (B) Expand the permanent of g[tau + d; all columns but n] along row d: sum_j g_dj B_tau[n,j] = 0. Rows d and e (and
     l_a + l_b + l_c = -(l_d + l_e)) lie in ker B_tau. If l_d, l_e are independent, rank B_tau <= 3 for each of the 10 triples.
     A DC g without zero column has no 4-row submatrix with a zero column, so for each i the 4x5 matrix g minus row i is of
     "Kirkup" type or has three rows tau with B_tau = 0.
 (K) Let a, b in C^5 with all Delta_mn = a_m b_n - a_n b_m != 0. Symmetric zero-diagonal B with Ba = Bb = 0:
     B[m,n] = 1/prod_{k != m,n} Delta_mk Delta_nk is a solution [scale columns so that a = 1; then B[m,n] = c_m c_n (b_m - b_n)^2,
     c_n = 1/prod_{k != n}(b_n - b_k), and sum_n c_n p(b_n) = 0 for deg p <= 3 (Lagrange)]; numerically |Ba|,|Bb| = 3e-16
     (lemmaz/gen.py). Uniqueness up to scalar for generic (a,b): 10 unknowns, 10 equations with the single Koszul relation
     b.(Ba) = a.(Bb); Hilbert series of A/(l_d,l_e) is 1,3,1 for a Lefschetz pair. [uniqueness: generic statement, not
     proved for every pair with nonzero minors]
     Consequence in the generic stratum (rank 4, all 2x2 minors of all row pairs nonzero): for each tau,
     l_a l_b l_c = c_tau * sum_{m<n} y_T / prod_{k in T} Delta^{de}_mk Delta^{de}_nk, and the transposed statement for columns.
     Each tau then gives 9 equations on the 8 free parameters of (l_a,l_b,l_c) given l_d,l_e: overdetermined by 1 per
     triple, which matches "no solutions without zero line" but is not a proof.
 Lefschetz facts used above (A is the cohomology ring of (P^1)^5; a form with all coefficients nonzero is equivalent to
 sigma = sum y_j under y_j -> y_j/a_j): l: A_1 -> A_2 is injective iff |supp l| >= 3; l l' = 0 iff l = 0 or l' = 0 or
 both are supported on the same two variables with l' proportional to (a_j, -a_k) or on the same single variable.

## 3b. Newton form and the small analogues (exact)
 (N) Proof. The rows are commuting elements of A; prod_k (X - l_k) = X^5 - e_1 X^4 + e_2 X^3 - e_3 X^2 + e_4 X - e_5 and
     e_4(l without l_e) = e_4 - l_e e_3 + l_e^2 e_2 - l_e^3 e_1 + l_e^4. Column sums 0 give e_1 = 0, so e_2 = -p_2/2,
     e_3 = p_3/3. Summing over e and Newton (p_4 = -e_2 p_2 - 4 e_4) shows that "all rows are roots" forces e_4 = 0. QED
     In coordinates (a = a row, G_jj' = sum_k g_kj g_kj', T_jj'j'' = sum_k g_kj g_kj' g_kj'', n = 1..5):
        12 prod_{j != n} a_j = sum_{pairings {j,j'},{m,m'} of the columns != n} (G_jj' a_m a_m' + G_mm' a_j a_j')
                               + sum_{m != n} a_m T_{columns != n,m}.
     These five equations are dPsi/da_n = 0 for Psi(a) = top coefficient of l^5/5 - (p_2/2) l^3/3 - (p_3/3) l^2/2
     (top = coefficient of y_1...y_5). The same holds for columns with the row moments. Lemma Z is thus: five points of
     1^perp with sum 0 that are critical points of the quintic defined by their own 2nd and 3rd moments contain 0 or lie
     in a coordinate hyperplane.
 (G) gamma^m = m! sum_{|S|=|T|=m} perm g[S,T] x_S y_T. F_y(gamma^4) = -12 gamma^2 sum_j y_j m_j^2 when F_y gamma = 0
     (m_j = column j as a form in x), so special DC g also satisfy gamma^2 * sum_j y_j m_j^2 = 0 = gamma^2 * sum_k x_k l_k^2.
 (Z_3) n = 3: the Newton form reads l_e^2 = p_2/2 for all e; summing, p_2 = 0, so l_e^2 = 0: every row has at most one
     nonzero entry, and row sums 0 give g = 0. QED
 (Z_4) n = 4: l_e^3 = (p_2/2) l_e and p_3 = 0. For a row a with all a_j != 0 this gives a_1 a_2 G_34 = a_3 a_4 G_12,
     a_1 a_3 G_24 = a_2 a_4 G_13, a_1 a_4 G_23 = a_2 a_3 G_14 and their sum = 6 a_1a_2a_3a_4 (subtract the four coordinate
     equations after multiplying the n-th by a_n). Not finished by hand; it is the natural testbed (9 DC coordinates).
     The rank-2 argument of section 2 works verbatim for n = 4 (classes (2,2), V_j in span(x^3, y^3)).

 (Z') ONE-SIDED VARIANT IS FALSE (exact; corrects an earlier guess in this file). Column sums zero alone do not force a
     zero line: g with rows v, -v, e_1, e_1, -2e_1 (v with all entries nonzero) has column sums 0, no zero row, no zero
     column, and every 4x4 minor contains two rows supported in column 1, so all 25 minor permanents vanish
     (checked: lemmaz/sing.py). Its right kernel lies in {y_1 = 0}. So the Newton form (N) ALONE cannot prove Lemma Z;
     both centrings must be used (equivalently the torus form (T) with BOTH kernels of full support).

## 3c. Further exact reformulations found in round 2 (all hand-derived; g column-centred unless said otherwise)
 (L) LOCAL / MERGING FORM. special <=> for every three rows a,b,c:  a b c (a+b+c) = 0 in A_4, i.e. for every 4 columns U
     perm[a;a;b;c] + perm[a;b;b;c] + perm[a;b;c;c] = 0 on U (a condition on 3x4 submatrices only, 50 equations).
     Proof: with sig_e := product of the rows != e, column sums 0 give sig_d + sig_e = -a b c (a+b+c) for {d,e} the
     complement of {a,b,c}; if all ten sums sig_d + sig_e vanish then all sig_e vanish. Equivalently: merging any two
     rows (replace l_d, l_e by l_d + l_e) gives four forms with sum 0 and product 0, i.e. a special matrix with a
     zero row. Four forms with sum 0 have product 0 iff 6 m_U = haf(G_U) for all U (m_U = sum_k prod_{i in U} g_ki,
     G = Gram matrix of the columns, haf = sum over the 3 pairings), from Newton p_4 = p_2^2/2 - 4 e_4.
 (C) CUBE FORM (needs both centrings). Put v(s) = g^T s for s in {+1,-1}^5 and pi_j(v) = prod_{n != j} v_n. Then
     g special <=> for every j the function s -> pi_j(v(s)) on the cube has Walsh degree <= 2
     <=> for all e, j:  sum_{k != e} pi_j(r_e + r_k) = pi_j(r_e) + sum_k pi_j(r_k)      (r_k = rows of g).
     Proof: a translation-invariant quartic F (here prod_{n != j} of the column forms) has no squarefree monomial iff its
     restriction to the 0/1 cube has degree <= 3; F(1_T) = F(1_{T^c}) kills the odd Walsh part; v(1_T) = -(1/2) g^T s.
     The 16 points of the cube mod sign are 0, the rows, and the 10 pair sums. For n = 4 the same argument gives
     "linear on the cube", i.e. pi_j(r_e + r_k) = pi_j(r_e) + pi_j(r_k): a condition on PAIRS of rows; for n = 5 the
     condition couples all rows through the quadratic form, which is why n = 5 is harder.
 (I) HADAMARD FORM (rows centred). For every four rows S and every column n:
        12 prod_{k in S} g_kn = sum_{pairs kk' in S} R_kk' g_mn g_m'n + sum_{m in S} t_{S-m} g_mn - (sum_j M_ej - M_en)/2,
     R = Gram matrix of the rows, t_abc = sum_j g_aj g_bj g_cj, e = the row not in S. With M = 0: the Hadamard product of
     four rows is a fixed combination of pairwise Hadamard products and rows. Pairing with a row gives, for every 4 rows,
        6 sum_j g_aj g_bj g_cj g_dj = R_ab R_cd + R_ac R_bd + R_ad R_bc.
 (Q) CONIC FORM of (K). B_tau induces a quadratic form on C^5 / span(l_d,l_e) (3-dim) for which the five images of the
     coordinate vectors are isotropic: five points on a conic, the Gale dual of the five points (g_dj : g_ej) of P^1.
     In coordinates B_tau[m,n] = c_tau c_m c_n (beta_m - beta_n)^2, beta_j = g_ej/g_dj (a squared-distance matrix of five
     collinear points, rank 3). With the transposed statement, in the open stratum of rank 4 the 10 x 10 array
        Omega[tau,T] = prod_{kk' in tau} Delta(kk'|mn) / prod_{jj' in T} Delta(de|jj')     ({d,e}, {m,n} the complements)
     of 2x2 minors must have rank one. (Derived; not checked numerically since no rank-4 solution exists to test on.)
 (A) ADJUGATE FORM OF THE RANK-4 CASE. For rank 4, adj(g) = y x^T with x, y the kernel vectors, so
     Lemma Z for rank 4  <=>  there is NO 5x5 matrix with det = 0, all 25 minor PERMANENTS zero and all 25 minor
     DETERMINANTS nonzero.   (A DC matrix of rank 4 has no zero row or column, so rank 4 means "no solution at all".)
 (P) RANK-3 PENCIL. If g is DC special of rank 3 with kernels span(1,y), span(1,x), then D(1+sx) g D(1+ty) is DC special for
     all s,t. All zero-line solutions have rank <= 3 (a 4x5 DC matrix has rank <= 3), so rank 3 is where the solutions
     live; the generic 4x5 DC solution has no zero entry, no proportional rows or columns and no vanishing 3x3
     subpermanent (lemmaz/look.py, 9 of 12 sliced solutions), so there is no support-type shortcut for rank 3.
 (Z_4, partial, exact) n = 4, two rows a, b with all entries nonzero, t = b/a entrywise: the pair condition is
     e_1(t_U) + e_2(t_U) = 0 for every 3 columns U, and its solutions are exactly t = (-1,-1,-1,-1) or t a permutation of
     (w,w,w^2,w^2) (w a primitive cube root of 1) [two triples give t_3 = t_4 unless {t_1,t_2} = {w,w^2}; then
     t_3^2 + t_3 + 1 = 0]. Consequently a DC special 4x4 matrix cannot have all entries nonzero, and three rows
     without zero entry force r_2 = t r_1, r_3 = conj-pattern, r_4 = -(1 + w + w^2) r_1 = 0. Rows with zero entries: not done.
 Numerics round 2 (torus form, lemmaz/sing.py, sing2.py): 30 LM solutions of {25 minor permanents = 0, det = 0}, no
     centring: 13 clean rank-4 solutions, all with a zero row or column (cofactor matrix supported on that line); 6
     apparent "rank 4, no zero line, full kernels" are NOT solutions of that kind: on inspection they are slowly
     converging degenerate points (rows/columns of size 1e-4..1e-6, singular values 1e-4, 1e-5, 1e-8). No counterexample.
     Second batch with an automatic test (sing3.py, 60 starts, strict cleanliness: residual < 1e-14 and a 1e-8 gap in the
     singular values): 10 clean solutions, all rank 4, none with both kernels of full support (one has no zero line
     but both kernels inside coordinate hyperplanes: a support-type point, allowed by (T)); 50 starts not clean.
 (P4r) ROW-REFINED P_4 (exact, from (I) by summing; DC special g; r_a, c_j = row/column sums of squares, T_j = sum_k g_kj^3):
     for every row a:  36 sum_j a_j^4 - 18 sum_j a_j^2 c_j - 12 sum_j a_j T_j + 3 r_a p_2 + 6 (R^2)_aa - 18 r_a^2 + 6 sum_b R_ab r_b = 0;
     summing over a gives exactly 24 P_4 = 0 in the brief's formula (consistency check of (I)). Same for columns.

## 4. Part (3): L level, every element of K = L cap DC special
 4.1 (exact given Lemma Z for the elements of K; unconditional if all elements of K have rank <= 2): K lies in the union
     of the ten subspaces {row i = 0}, {col j = 0}, hence in one of them. Say row 5: K is a space of 4x5 DC matrices.
 4.2 d = dim K <= 6 (sum of squares is nondegenerate on the 12-dim space of 4x5 DC matrices, and is 2P_2). If K has two
     common zero rows, K is a 3x5 row-centred level space and d <= 4 by L157 (attained: kbuild's K). The DC special
     matrices with zero row 5 contain three kinds of pieces (numerics, gen.py types): a second zero row (any 3x5 DC,
     dim 8), a zero column with perm of the 4x4 block = 0 (dim 8, circ4 type), and rank 3 with exactly one zero row and
     no zero column (expected dim 7, seen in 5 of 30 runs).
 4.3 Row-5 identities (exact; coefficient of s^3 in perm(J + t + s g) = 120, t = (T; tau) in L with rows T_1..T_4 and
     row 5 = tau, g in K, B_i := B_{[4] minus i}(g)):
        (a) sum_i ( tau^T B_i 1 + 1^T B_i T_i ) = 0,        (b) sum_i tau^T B_i T_i = 0,       and B_i g_i = 0 (Kirkup).
     [The s^4 coefficient is trivial because g is special, so (a),(b) are the first conditions that see row 5.]
     Polarising (b) against t' in L' := L cap {row 5 = 0}: the row-5 image rho(L) in C^5 is orthogonal to
     S := span{ sum_i B_i(g) T'_i : g in K, t' in L' }, and S is orthogonal to 1 by (a). Hence
        dim L = dim L' + dim rho(L) <= dim L' + 5 - dim S.
     This is the only coupling found; it is empty when all 3x3 subpermanents of K vanish (ex1's K, on a 3x4 block).
 4.4 What a bound needs: dim L' - dim S <= 3 for 4x5 level spaces L' containing a nonzero DC special K, or the analogous
     statement with the s^2 coefficient when B = 0. In ex1 (dim 7): L' = rc45 (dim 6), rho(L) = C (one column direction).
     No project lemma gives this; it is a new rectangular statement ("4x5 level space with nonzero DC part: how many
     row-5 directions can be added").
 4.5 General (non-special-specific) exact fact, for reference: phi(L) is orthogonal to K + K o K (o = entrywise product,
     phi(t) = t - (R_i + C_j)/2, injective on L); follows from P_2 and the polarised P_3 with two slots in K. For K in a
     4x5 block this gives nothing new.

 4.6 TYPES OF K IN THE SPECIAL BRANCH (round 2). Assume Lemma Z for the elements of K and let row 5 be the common zero row.
     K is the union of the subspaces K cap {row i = 0} (i <= 4), K cap {col j = 0} and the set of elements with exactly
     one zero line, so exactly one of the following holds (exact):
       (I)  K has a second common zero row: K is a 3x5 row-centred level space, d <= 4 (L157; attained by kbuild's K);
       (II) K has a common zero column: K is a 4x4 DC level space, d <= 3 (L_gct_216);
       (III) the generic element of K has exactly one zero line.  Here only d <= 6 is proved.
     Hence in the special branch d <= 4 unless K is of type (III).
     NEW EXACT EXAMPLE of type (III) with d = 2 (found by LM, lemmaz/plane.py run 6, then verified by hand):
       K_new = { x * u (e_0 - e_3)^T + y * u' (e_1 + w^2 e_2 + w e_4)^T },  u = (1,-1,i,-i,0)^T, u' = (1,1,-1,-1,0)^T, w^3 = 1.
     Every element has rank 2, zero row 4, no other zero line; columns {0,3} and {1,2,4} form two rank-one blocks.
     Level: P_k(p q^T) = k! e_k(p) e_k(q); e_2(u) = 0 and e_k(e_0 - e_3) = 0 for k != 2; e_2(1,w^2,w) = 0, e_3(u') = 0; a mixed
     term would need 2 + 3 = 5 nonzero rows. Special: the 4x4 subpermanents are multiples of sum_i u_i/u'_i = 0 and of
     e_2(u/u') = e_2(1,-1,-i,i) = 0. So type (III) is not empty; whether K_new lies in a large level space is not examined.
     NUMERICS (lemmaz/plane.py, 40 LM starts for planes of 4x5 DC special level matrices, 31 converged): 15 of type (I),
     15 of type (II) (one slowly converging), 1 = K_new; NO plane whose generic element has rank 3 and a single zero
     line. Not calibrated for that last type (no planted example exists), so this is weak evidence that type (III)
     planes are all of rank 2; rank-2 DC special matrices can be classified completely with section 2.
 4.7 Checks: all formulas (C), (I), the 4-row moment identity, (P4r), (L) verified numerically on a random DC matrix or on
     an LM solution to 1e-14 (lemmaz/forms.py); in (C) the Walsh coefficient equals M_ej exactly.

## 5. Smallest open sub-cases, and what would settle them
 Everything below is about DC matrices g with core h = g[1..4,1..4] (16 coordinates) and the ideal I generated by the 25
 minor permanents (quartics in h).
 (Z-4) RANK 4 (det h != 0): claim V(I) has NO such point. Equivalent: (A) no 5x5 matrix with det = 0, all minor permanents 0,
       all minor determinants != 0. Nothing is proved here, not even for matrices with all 25 entries nonzero.
 (Z-3) RANK 3 (det h = 0, 15-dim ambient): claim every point of V(I) has a zero row or column. The zero-line solutions
       form families of dimension 7 (one zero line, rank 3, generic entries) and 8 (two zero rows; zero row + zero
       column), so the claim is "no further component", and by (P) a further component would have dimension >= 3.
 (Z-2), (Z-1): proved (sections 1, 2).
 What settles (Z-3) and (Z-4) together (needs a computer algebra system; outside this brief's limits, not attempted):
   saturate I successively by the ten line ideals (row i: the entries of row i; column j likewise) over Q, or over F_p and
   lift; Lemma Z <=> the result is the unit ideal. Cheaper variant by strata: for a set E of cells meeting every row and
   column (it suffices to take minimal ones, i.e. star forests of K_{5,5}, up to S5 x S5 x transpose), show
   1 in I + (1 - z prod_{E} g_ij); a point of V(I) outside all ten lines lies in one of these strata. A numerical
   irreducible decomposition (homotopy continuation) of V(I) in P^15 would give strong evidence in minutes but no proof.
 Human-proof route (the n = 4 model shows the pattern): for n = 4 the cube form gives a condition on PAIRS of rows whose
   full-support solutions are rigid (ratios -1 or cube roots of unity), and the lemma follows by combinatorics of the
   pairs. For n = 5 the same role is played by TRIPLES of rows via (L): (a,b,c) must lie in
       Y := { (a,b,c) sum-zero rows : a b c (a+b+c) = 0 in A_4 }  (= 4x5 DC special matrices, 7-dim, d = -(a+b+c) spans ker B_abc),
   and Lemma Z says: five sum-zero rows with sum 0, all ten triples in Y, include 0 or miss a column. The missing
   ingredient is a usable parametrisation of Y (its generic point has no zero entries and no proportional lines); (Q)
   gives one handle: B_abc is the conic through the Gale dual of the points (d_j : e_j) for every pair d,e of rows.
 For the gap itself: Lemma Z is used only on K = L cap DC, where p_2 = p_3 = 0 and P_4 = 0 also hold; and by (Z') any
   argument must use both centrings.

STATUS (start): rank 1, 2 proved by hand; circulant test.
STATUS (mid): Kirkup relations (B), closed form (K) verified numerically; 30 LM runs typed.
STATUS (round 2 end): Z' refuted, forms (L),(C),(I),(Q),(A),(P),(P4r) added, section 5 rewritten.
STATUS (end): notes written; Lemma Z open for rank 3, 4. Added Newton form (N), gamma^4 form (G), Z_3 proof, Z_4 and one-sided numerics.
Files: lemmaz/core.py (vectorised minor permanents, complex LM), circ.py (twisted circulants), gen.py (LM + typing + (K) check),
 newton.py ((N) check), onesided.py, look.py (4x5 DC solutions), sing.py / sing2.py / sing3.py (torus-form sampling, (Z') example).
