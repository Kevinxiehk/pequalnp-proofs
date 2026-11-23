# NOTES-kbuild (role kbuild: which level spaces contain the 3-row DC space K)

## RESULT 13:27 (EXACT): the level spaces containing K are exactly K and the five 5-dim spaces
##   K (+) C*E_j,  E_j = (e_3 - e_4) e_j^T  (j = 0..4).   So max dim = 5 (not 9, not 8, not 7).
K = {u p^T + ubar q^T : p in P = span(chi1,chi4), q in Q = span(chi2,chi3)}, u = (1,z^2,z,0,0) (rows 0..2).
Proof (all steps exact; computer only for step 1, rigorous by reduction mod a prime):
 1. First-order space E(K) = {y : <grad P_k(x), y> = 0 for all x in K, k = 1..5} equals
        E(K) = K (+) D (+) C*rho,   D = (e_3 - e_4) (x) C^5 (5-dim),  rho = r 1^T, r = (2,2,2,-3,-3).
    '>=': D: for x on rows 0..2 the gradient rows 3 and 4 coincide (dP_k/dt_ij = P_{k-1}(X minus col j), i = 3,4).
         rho: d/de P_k(x + e rho) = (6-k)(2-2k) P_{k-1}(X) = 0 (count of subpermanents; holds for ANY level K' on 3 rows).
    '<=': rank of the first-order system at 8 integer points of K is 15 mod p = 1000000021 (zeta15 -> element of order 15),
          hence >= 15 over C (kbuild/exactK.py). Any level L containing K lies in E(K) (differentiate P_k(x + e y)).
 2. So L = K (+) M with M = L cap (D + C rho) (K is inside L). Write m = (e_3-e_4) v^T + c rho. Each m in M is level and
        P_2(m) = -300 c^2 - 2 e_2(v),   P_3(m) = -600 c^3 - 36 c e_2(v)   =>  P_3 = 4800 c^3 on {P_2 = 0}  =>  c = 0.
    So M = (e_3 - e_4) (x) W, W a subspace of C^5.
 3. For t = x + (e_3-e_4)v^T (x in K, X its 3x5 block): P_k(t) = P_k(X) - sum_{j != l} v_j v_l P_{k-2}(X^{(jl)})
    (Laplace along rows 3,4; X^{(jl)} = X minus columns j,l). Conditions on W (all v in W, all X in K):
      k=2: e_2(v) = 0;  k=3: automatic (X doubly centred);  k=5: perm(X^{(jl)}) = 6(prod_{c not in{j,l}} p_c + same for q)
      (perm of a 3x3 block of u p^T + ubar q^T: the mixed terms carry sum u^2 = sum ubar^2 = 0, and u_0u_1u_2 = 1), so
      f_p(v) := sum_{j != l} v_j v_l prod_{c not in {j,l}} p_c = 0 for all p in P and all p in Q.  (k=4 not needed.)
 4. In Fourier coordinates v = sum_a nu_a chi_a the 8 coefficient forms of f_p (p = alpha chi1 + beta chi4, gamma chi2 + delta chi3)
    are, per Z5-weight s = a+b (exact check in Z[zeta15], exactK.py):
      s=2: -nu0nu2 + 2nu1^2 - nu3nu4,  2nu0nu2 + nu1^2 - 3nu3nu4;   s=4: 2nu0nu4 - 3nu1nu3 + nu2^2,  -nu0nu4 - nu1nu3 + 2nu2^2;
      s=1: 2nu0nu1 - 3nu2nu4 + nu3^2, -nu0nu1 - nu2nu4 + 2nu3^2;    s=3: -nu0nu3 - nu1nu2 + 2nu4^2,  2nu0nu3 - 3nu1nu2 + nu4^2;
    and e_2: 2nu0^2 = nu1nu4 + nu2nu3. So on W: nu_a nu_b depends only on a+b (for a+b != 0 mod 5). Elementary elimination:
    nu0 = 0 forces nu = 0; nu0 = 1 forces nu1 = nu3^2, nu2 = nu1^2, nu3 = nu4^2, nu4 = nu2^2, nu1^15 = 1, then theta := nu1 has
    theta^5 = 1 and nu = (1,theta,...,theta^4), i.e. v is a multiple of a unit vector e_j. A subspace inside the union of
    the 5 lines C e_j is one of them: dim W <= 1, and W = C e_j works (one nonzero entry kills the sum over j != l).
 Consequences: (a) every level space containing K (or any S5xS5xconj image of it, incl. the transposed 5x3 version) has dim <= 5;
 (b) such L has r_B = 0, r_A <= 1, d = 4: consistent with (S); (c) the earlier '10-dim first-order extension' is
 K + D + C rho, and the extra 6 directions are killed already by P_2, P_3 (c = 0), e_2-isotropy and the P_5 forms.
 Files: kbuild/exactK.py (exact), kbuild/sanity.py (numerical check of the row-3/4 Laplace formula, 1e-12), kbuild/forms*.py.

## RESULT 2 (14:05): what the K-mechanism gives for OTHER DC parts (first-order space E(D) + second-order isotropy)
Mechanism (exact, general): for a level L and any D inside L (e.g. D = L cap DC):
  (M1) L is inside E(D) = {y : <grad P_k(x), y> = 0, x in D, k=1..5};
  (M2) L is totally isotropic for B_2 = Hess P_2 and all H_k(x) = Hess P_k(x), x in D, k = 3,4,5
       (coefficient of e e' in P_k(x + e y + e' y'));   H_5(x) has entries = 3x3 subpermanents of x;
  (M3) dim L = d + rank pi|_L <= d + dim pi(E(D)), pi = (row sums, column sums), d = dim(L cap DC).
  S2(D) := dim D + max dim of a common isotropic subspace of E(D)/D  >=  dim L.   (kbuild/second.py, second2.py)
TABLE (dim E exact-looking ranks from SVD with clear gaps; isotropic dims by LM, 2 seeds: 'exists' is reliable (res 1e-14),
'not found' is a numerical negative):
  D                                             dim E(D)  ranks of B2,H3,H4,H5 on E/D   S2 (2nd-order bound on dim L)
  K (4-dim, 3-row)                                 10      (exact analysis)               5 EXACT (all orders: RESULT above)
  generic DC level g (rank 4)                      20      19,19,19,19                    <= 6 (m=6 not found; count predicts m<=5)
  generic element of K (rank 2, 3-row)             21      20,11,11,8                     7  (m=6 exists, m=7 not found)
  a chi1^T, sum a = 0, a_4 = 0 (Wxv type)          20      18,16,18,6                     7  (m=6 exists, m=7 not found)
  u chi1^T (rank one, 3-row, in K)                 21      18,11,6,8                      >= 9 (m=8 EXISTS, res 8e-15, t3q.py)
  u(e0-e1)^T  (DC elements of ex1/ex2; 3x2 block)  22      20,2,4,0                       >= 9 (m=8 EXISTS)
  (e0-e1)x^T, x sum-zero isotropic (2 rows)        22      21,6,13,0                      >= 9 (m=8 EXISTS)
  DC part of ex1 = <u(e0-e1)^T, ubar(e2-e3)^T>     20      18,4,10,0                      >= 9 (m=7 EXISTS, res 2e-14, ex1q.py)
  coordinate 3-dim subspace K3 of K                13      (10 forms on N)                6  (m=3 exists, not level; m=4 not found)
  generic 3-dim subspace of K                      11                                     5
CONCLUSIONS for the proof side:
 (C1) "D contains g  =>  dim L <= 8 by first+second order AT g" holds numerically (LM negatives at m = 7 and 8, 2-3 seeds each;
      positives up to the stated m) for: generic DC level g (<= 6), generic element of K (7), a chi1^T with generic a (7).
      CAUTION: LM negatives here are weak (for u chi1^T an ascending search stalled at m = 6 although m = 8 exists).
 (C2) It is FALSE as a method for RANK-ONE 3-row elements u v^T (u = cube roots on 3 rows; v = chi1 or e0-e1) and for the
      degenerate class Z = {DC level g with ALL 3x3 subpermanents zero} (H_5(g) = 0):
      2-row / 2-column elements (e_a - e_b)x^T, x(e_a - e_b)^T (x sum-zero, sum x^2 = 0) and combinations like the DC part of
      ex1. There E(g) has codimension only 3 (grad P_4 = grad P_5 = 0; explicitly for g = u(e0-e1)^T:
      E(g) = {sum y = 0, <g,y> = 0, sum_{i<3,j>=2} ubar_i y_ij = 0}), H_3, H_4 have rank <= 13, and 9-dim subspaces of E(g)
      isotropic for all four forms exist. So for D inside Z the bound must come from GLOBAL conditions on L (P_3 on all of L:
      lowd's 'P_2 = P_3 = 0 caps at 7', or the block/Laplace structure), not from the Taylor data at D.
 (C3) Proposed case split for the gap:  (A) L cap DC contains a 'non-degenerate' g (S2(g) <= 8: a statement about 4 explicit
      quadratic forms on E(g); generic g, generic K-elements, generic a chi1^T) -> done by (M1)+(M2);  (B) every element of
      L cap DC is degenerate (rank-one 3-row/3-column u v^T, or in Z) -> use several elements of D at once (K: exact bound 5
      although its rank-one elements u chi_k^T individually allow 9), or classify linear subspaces of Z (2-line types and ex1-like sums of rank-one
      u v^T on a 3-row or 3-column block with prod_C p + prod_C q = 0) and use the exact row-Laplace formula
      P_k([X; a; b]) = P_k(X) + sum_j (a_j+b_j) P_{k-1}(X^(j)) + sum_{j != l} a_j b_l P_{k-2}(X^(jl))  (X = 3x5 block).
 (C3') Lead for case (B), exact: if g = x(e_0 - e_1)^T is in L (x sum-zero, sum x^2 = 0; ex1/ex2 type), then P_k(y + s g) has
      degree <= 2 in s (g has two nonzero columns), and the s^2-coefficient involves only the 5x3 block Y' = y[:, 2..4]:
          sum_{i<i'} x_i x_i' P_{k-2}(Y' minus rows i,i') = 0  for all y in L   (k=3: sum_{r,c} x_r^2 Y'_rc = 0; k=4: a quadric;
      k=5: a cubic in Y'),  and the s-coefficient gives  sum_i x_i [P_{k-1}(y minus (row i, col 0)) - P_{k-1}(y minus (row i, col 1))] = 0.
      These are (M2)-type conditions taken at x = y in L (not at x in D) - the part of the level conditions that the
      'Taylor data at D' misses; any treatment of ex1-type DC parts has to use them (or P_3 on all of L).
 (C4) (S) is consistent and TIGHT on the new examples: K + E_j has (d, r_A, r_B) = (4,1,0); K3 + 1_012(x)chi_1 + E_j has (3,1,1).
      For d = 4 the target (S) follows from the K-lemma (r_B = 0 exactly) as soon as every 4-dim DC level space is
      shown to be K-type (dc5: 3-row case exact except the split step; non-3-row 4-dim DC level spaces: none known).
3-ROW TOOLBOX (exact, verified numerically 1e-13): every matrix on rows 0..2 is 1 o^T + u p^T + ubar q^T (o,p,q in C^5) and
   P_1 = 3 sum o;  with sum o = 0:  P_2 = 3(p.q - sum p sum q - sum o^2),
   P_3 = 6(e_3(o) + e_3(p) + e_3(q)) + 3(o.p) sum q + 3(o.q) sum p - 6 sum_j o_j p_j q_j,   P_4 = P_5 = 0.
   (perm of a 3x3 column block = 6(prod o + prod p + prod q) - 3 perm[o|p|q]; uses sum u = sum u^2 = 0, u_0u_1u_2 = 1.)
   P_2 is a nondegenerate quadric on the 14-dim space {sum o = 0}: 3-row level spaces have dim <= 7 (so <= 8 with one E_j).
   Exhaustive Z3 x Z5-graded search (span of 1(x)chi_a, u(x)chi_b, ubar(x)chi_c; kbuild/graded3.py): max 3-row level dim = 4,
   exactly 18 spaces: K, its row-swap, and 16 of type (3-dim coordinate subspace of K or swap) + 1_012(x)chi_a (G2 type).
   Second-order bounds for the three G2-type classes: 6, 5, 5 (kbuild/kg.py); the 2-dim isotropic extensions of the first
   (E_j + u(x)chi_0) fail P_3, so 5 is the likely truth. Unstructured LM for 5-dim 3-row level spaces stalls at residual
   1e-7 (kbuild/rows3lm.py, pol3.py; dc5's rect_012_d5.npy likewise 1e-6..1e-8) - NOT a solution, undecided.

STATUS 13:15: started (75 min budget). Plan: exact E(K), symmetry decomposition, higher-order conditions on E(K)/K.
STATUS 13:22: K classified exactly (max 5). Next: 3-dim subspaces of K and other 3-row DC spaces, generalized lemma.
STATUS 13:29: RESULT on K written (exact). Now numerics: max level extension of 3-dim subspaces K3 of K inside E(K3) (coordinate K3: E=13, N = u(x)chi1, u(x)chi0, 1_012(x)chi1, 1_012(x)chi2, D, rho; generic K3: E=11).

## FINDINGS 13:33 (beyond K)
 G1 (EXACT, general): for ANY level space K' supported on rows {0,1,2} and any column j, K' (+) C*E_j is level
    (E_j = (e_3 - e_4) e_j^T). Laplace along rows 3,4: P_k(x + sE_j) = P_k(X) since a + b = 0 and a_j b_l = 0 (j != l).
    Also D = (e_3-e_4)(x)C^5 and rho = (2,2,2,-3,-3) 1^T always lie in the first-order space E(K'), and any element
    m = (e_3-e_4)v^T + c rho of a level space has c = 0 (P_2 = -300c^2 - 2e_2(v), P_3 = -600c^3 - 36c e_2(v)).
 G2 (EXACT): new 5-dim level spaces with d = 3, r_A = r_B = 1 (so (S) is TIGHT on them: min + d = 4):
    K3 (+) C*(1_012 (x) chi_1) (+) C*E_j,  K3 = span(u(x)chi4, ubar(x)chi2, ubar(x)chi3) (K minus u(x)chi1),
    1_012 = (1,1,1,0,0). Proof: 3-row part: P_1 = P_2 = 0 by direct computation (row sums 0, col sums 3 o, sum o^2 = 0,
    chi4.chi2 = chi4.chi3 = 0), P_3 = 0 by Z3 x Z5 torus weights (no weight-0 cubic monomial in s,beta,gamma,delta with
    weights (0,1),(1,4),(2,2),(2,3)); then G1. Same with 1_012(x)chi_2. Found by LM in E(K3) (polished 1e-11), checked
    numerically to 1e-9 for all j. (K3 + 1(x)chi1 + 1(x)chi2 fails P_3; K3 + u(x)chi0 fails P_3.)
 G3 (numerical, 2nd order): E(K3) has dim 13 for coordinate K3 (= K3 + u(x)chi1 + u(x)chi0 + 1(x)chi1 + 1(x)chi2 + D + rho),
    dim 11 for a generic 3-dim subspace K3 of K. Common isotropic subspaces of all Hessian forms Hess P_k(x)|_N
    (x in K3, k = 2..5) on the complement N: max dim 3 (coordinate K3; dim 4 not found, 6 LM seeds) and 2 (generic K3);
    for K itself max 1 (matches the exact result). The 3-dim isotropic ones are NOT level (P_3..P_5 ~ 10).
    => level spaces containing a 3-dim subspace of K have dim <= 6 (coordinate) / <= 5 (generic) [second-order numerics];
    actual LM: dim 5 found (G2 and K + E_j), dim 6 (m = 3) not found (coordinate K3, one LM seed only: weak).
 Other 3-row 3-dim DC spaces: in the n = 5 character family every 3-dim one is a coordinate subspace of K or of its
    row-swap image (S1, S2 must be among {1,4},{2,3} or singletons), so G3 covers them; non-character 3-dim 3-row DC
    level spaces (isotropic for p.q with c(p) + c(q) = 0) were not treated.
 Caveat for the K lemma's scope: it covers every 4-dim 3-row DC level space that is S5 x S5 x conj-equivalent to K;
    dc5's classification of 4-dim 3-row DC level spaces is exact except the 'split step' (Lagrangian K' in V0+V0 for p.q
    with c(p)+c(q) = 0 must be A0 + A0^perp; graph case done by dc5, mixed cases (dim A0, dim B0) in {(1,*),(2,1),...} open).
STATUS 13:33: findings G1-G3 written; waiting for last m=3 LM seeds.
STATUS 13:49: restarted after session interruption; now: second-order bound S2(g) for single DC level elements g of each type (kbuild/second.py). T1 = u(e0-e1)^T (ex1/ex2 DC type): dim E(g) = 22, common isotropic m = 8 EXISTS -> single-element 2nd-order argument does NOT give <= 8 for this type.
STATUS 13:55: S2 results so far (numerical LM, 2 seeds): generic DC level g: dim E 20, S2 <= 6; generic element of K: S2 = 7; T1 u(e0-e1)^T and T8 (e0-e1)x^T (2-row): isotropic m = 8 exists (no bound <= 8 from a single element at 2nd order). Running a chi1^T and the 2-dim DC part of ex1.
STATUS 14:12: RESULT 2 written (table of E(D), second-order bounds, case split, 3-row toolbox). Negatives: single-element / DC-part second-order mechanism does NOT exclude dim 9 for u chi1^T, u(e0-e1)^T, 2-row elements, and the 2-dim DC part of ex1 (isotropic subspaces of total dim 9 exist). Finished; final report sent.
