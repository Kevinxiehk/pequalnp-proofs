# NOTES-repr (role repr: invariant-theoretic structure of (P_2,P_3) on W, 24-dim)
## RESULT (final summary, 14:10; details in the numbered sections below)
 R1 [EXACT, refutes the P_2/P_3-only target] L9 = { x v^T + z e_4^T : x in C^5, sum z = 0 }, v = (1,i,-1,-i,0): 9-dim, P_1=P_2=P_3=0
    exactly, P_4, P_5 != 0; maximal by inclusion for (P_2,P_3). Any proof of the gap must use P_4 / P_5 (and (S) at d = 4 too:
    L9 has (r_A, r_B, d) = (4,1,4)). Every LEVEL subspace of an L9-type space has dim <= 7 (hand proof, section 4).
 R2 [numerical, clear rank gap] Stab(P_2,P_3) in GL(24) has identity component = scalars (even for P_3 alone): no torus/Borel reduction.
 R3 [EXACT, new structure] perm(J + X V^T) = sum_a (5-|a|)! a! E_a(X) E_a(V) for any 5 x M matrices X, V (section 8), and the
    resulting factorised criterion for 'rank-one-family' (RF) spaces -- the class containing ALL known examples (L080, ex1, ex2,
    rc45, K, product type, L9): for each multidegree, a row-side polynomial identity OR a column-side one must hold.
 R4 [complete negative table, but uncalibrated] expected-dimension scan of the full system over 34 cyclic classes, 48 abelian
    products R x C, 14 transposed/diagonal abelian groups: no configuration with expected dim >= 0 at K = 8, 9 (best -11, -15);
    also none at K = 6, 7 where solutions exist => no evidence either way (repr/TABLE-expdim.txt).
 R5 [calibrated numerics, all negative at K = 8] equivariant LM (found planted 7-dim spaces and L9): Z3-rows (all 9 admissible
    eigen-dimension vectors), Z4-cols (7), Z5-cols (9), transpose (5), diagonal Z3 (10), diagonal Z5 (>= 3): every start stalls at
    residual 0.7 - 20.  PRODUCT TYPE (L_gct_114 setting, bound 2n-2 = 8): LM finds the 7-dim patterns (3|4), (4|1,1,1) in 3/3
    starts within 7 iterations, and finds NOTHING for (4|4) in any row/column dimension pattern (table in section 9)
    => product type max is 7 at n = 5 (numerically), i.e. L_gct_114's 2n-2 is not attained.
 R6 [family ideas] lam-family: finite exceptional set, but lam = -16/9 is exceptional (L9) => useless. For the full system only
    DEGENERATION transfers rigorously (section 5); natural weights give limits with >= 12-dim isotropic spaces. Base-point family:
    {X : a K-dim level space at X exists} is Zariski closed; the torus orbit of J is closed in {perm != 0}; X = I has a 10-dim level
    space (strictly upper triangular), so the bound is specific to rank-one base points.
 R7 [NEW numerical family, well conditioned, level error 1e-16] 7-dim PRODUCT-TYPE level spaces exist in ALL 15 dimension patterns
    (rows 3 / 21 / 111) x (cols 4 / 31 / 22 / 211 / 1111) (repr/prod_*_9.npy; by transpose also (4|3)); every one has
    (r_A, r_B, r, d) = (4,3,7,0), first-order extension space = L + C*(1 e_c^T - J/5) for exactly ONE column c, and
    P_2 of that direction = -2 != 0, so each is maximal by inclusion.  EXACT reformulation of that extra direction (section 11):
    it is in the first-order space  <=>  L stays level after zeroing column c. The same holds (one deletable row OR column) for all 19 other 7-dim spaces in the team's files: 34/34.
 NO 8-dim level space found; no proof of <= 8. Best next step: section 10.
## !!! RESULT (13:27): the P_2/P_3-only target is FALSE: an explicit 9-dim subspace of the 24-dim sum-zero space
## on which P_1 = P_2 = P_3 = 0 EXACTLY (not level: P_4, P_5 != 0). So any proof of the gap MUST use P_4 or P_5.
   L9 = { x v^T + z e_4^T :  x in C^5 arbitrary,  z in C^5 with sum z = 0 },   v = (1, i, -1, -i, 0).
 Proof (hand): columns 0..3 of t are v_j x, column 4 is z. A k x k subpermanent using a column set C:
   C inside {0..3}: perm = k! prod_R x * prod_C v  -> summed: k! e_k(x) e_k(v);
   C = C' + {4}, C' in {0..3}, |C'| = k-1: summed over C' it carries the factor e_{k-1}(v).
   e_1(v) = e_2(v) = e_3(v) = 0 (v = 4th roots of unity on 4 columns), so P_1 = P_2 = P_3 = 0; P_4 = 24 e_4(x) e_4(v) - ...
 Exact check (Gaussian-integer arithmetic, all polarised components on a basis): repr/nine.py -> max |P2 polar| = max |P3 polar| = 0;
 brute-force subpermanent sums at a random Gaussian-integer point: P1=P2=P3=0, P4 = -3120-4680i, P5 = 57960-43080i.
 Found via the equivariant expected-dimension scan (repr/equiv.py): for h = 4-cycle on columns, L = (3- or 4-dim part of
 the fixed space W_0) + (the whole -i eigenspace W_3 = C^5 (x) v); eigenvalue bookkeeping kills every cross term.
 => the 'KEY NEW LEAD' (P_2 = P_3 = 0 alone caps at 7) was an LM artifact (special, excess solution missed by random charts).
STATUS 13:16: started; computing symmetry Lie algebra of (P_2,P_3).
## (1) Symmetry Lie algebra [numerical, exact-rank clear: next sv 3.0 vs 1e-15] (repr/lie.py)
 The linear vector fields X on the 24-dim sum-zero space W with P_3(Xt,t,t) = c P_3 (resp. and P_2(Xt,t) = c' P_2)
 form a 1-dim space: scalars only. So the identity component of Stab_{GL(24)}(P_3) (even P_3 alone, up to scale)
 is C^* (scalars); the symmetry group of (P_2,P_3) is finite mod scalars. => NO Borel-fixed-point / torus
 degeneration reduction is available from symmetries (idea (3) of the task is dead).
## (2) Clean one-parameter reformulation [exact; follows from split's u-identities]
 In u-coordinates (u = g + a in W subset C^25 with Hadamard product, tau = sum of entries, a in AB = V(x)1 + 1(x)V,
 g in DC = V(x)V):   2P_2 = lam tau(a^2) + tau(g^2),
                (3/2)P_3 = lam tau(a^3) + 3 tau(a^2 g) + 3 tau(a g^2) + tau(g^3),   lam = 1 - 25/9 = -16/9.
 I.e. (P_2,P_3) are the power sums p_2, p_3 of C^25 restricted to W, with ONLY the pure-AB parts reweighted by lam.
 At lam = 1 these are honest power sums on W in C^25, so L061 gives 3 dim <= 25, dim <= 8.
 Consequence (properness of Gr(9,24)): Lambda_9 := {lam in P^1 : some 9-dim L is isotropic for (Q_lam, C_lam)} is
 Zariski-closed in P^1 and misses lam = 1, hence FINITE. (lam = infinity is in it: DC is 16-dim isotropic.)
 So the P_2/P_3 target is 'generically true in lam'; it fails only if -16/9 is one of finitely many special values.
 (Equivalently: a weighted power-sum model on C^35 = cells + row means + col means, weights 1 and -125/9, gives only 11.)
STATUS 13:29: 9-dim P2/P3 space verified exactly; next: equivariant expected-dim scan for the FULL level system (P_2..P_5).
STATUS 13:50: L9 is maximal by inclusion for P2/P3 (first-order extension space = L9 + the column-mean direction
 1 (x) (-1,-1,-1,-1,4), which has Q(y,y) != 0) (repr/ext9.py).
## (3) Equivariant expected-dimension scan for the FULL level system (repr/eqlevel.py; cyclic subgroups of S5xS5 and
## (s,1)T): for every cyclic subgroup and every eigen-dimension vector, expected dim (= chart unknowns - number of
## components of the NONZERO restricted polarised P_2..P_5 forms) is NEGATIVE for K = 8, 9 (best -11, -15: h = (3-cycle,
## 5-cycle)), but ALSO negative for K = 6, 7 (best -5, -8), although 7-dim level spaces exist. So the scan is
## UNCALIBRATED for the level system (all known level spaces of dim >= 6 are excess objects); its negatives mean nothing.
## (For P2/P3 alone it is calibrated: K=8 had expected dims +2,+1,+1,0,... and led to L9.)
 Correction to (2): L9 shows lam = -16/9 IS in the finite exceptional set Lambda_9, so the lam-family gives nothing for P2/P3.
## (4) Deforming L9 toward level spaces [exact, hand proofs]  (coordinator item 2)
 Column-block calculus: if columns are split into blocks B and in block B column j equals v^B_j x^B (v^B fixed,
 x^B in C^5), then perm(J+t) = sum_{(a_B)} (5-sum a)! prod_B e_{a_B}(v^B) a_B! S_a(x),  S_a = sum over DISJOINT row
 sets R_B (|R_B| = a_B) of prod_B prod_{i in R_B} x^B_i.  (Singleton block: e = (1,1).)
 (a) L9-type T(v) = {x v^T + z e_4^T} (v any vector on cols 0..3 with e1=e2=e3=0, i.e. 4th roots, e4(v) = -v0^4):
     P_1 = sum z, P_2 = P_3 = 0, P_4 = 24 e4(v) e4(x), P_5 = 24 e4(v) sum_i z_i prod_{j != i} x_j.
     LEMMA: every level subspace L' of T(v) has dim <= 7. Proof: P_4 depends on x only, so e4 vanishes on the
     x-projection X; e4 is irreducible (setting x_4 = 0 gives x0x1x2x3, a linear factor would have to be a single
     variable, but e4 contains x1x2x3x4), so X is not a hyperplane, dim X <= 3; fibre over x = 0 is inside {z e_4^T}
     (dim 4). Equality: X = {x_a = x_b = 0}, all z  -> L080-type 7-dim level space (P_5 = 0 since every
     prod_{j != i} x_j contains x_a or x_b).
 (b) 5-column block with e1..e3(v) = 0: {x v^T}: P_4 = 24 e4(v)e4(x), P_5 = 120 e5(v)e5(x). v = 5th roots (e4 = 0):
     X inside a coordinate hyperplane, dim 4 (e5 = prod x_i). Otherwise X inside {e4 = 0}: dim <= 3.
 (c) blocks (3,2) with v = cube roots, w = (1,-1): conditions e2(y) = 0 on Y, e3(x) = 0 on X, S_{3,2}(x,y) = 0:
     dim <= 2 + 3 = 5.  So column-graded (rank-one-per-block) deformations of L9 stay <= 7; the 4+1 block is the
     only one that makes P_2, P_3 vanish for free, and P_4 then costs 2 dimensions.
## (5) One-parameter families for the full system (coordinator item 3) -- what is and is not available
 * The lam-family is useless for the truth question: lam = -16/9 is itself exceptional (L9).
 * Rigorous principle that DOES transfer: DEGENERATION. If g_s in GL(25) (s -> 0) and F_0 = initial forms of
   (P_1..P_5) w.r.t. the weight of g_s, then any K-dim level L gives a K-dim common isotropic subspace lim g_s L of
   F_0 (Grassmannian is proper). So 'F_0 has no 9-dim common isotropic subspace' => gap. Also the set of parameter
   values (in any algebraic family of systems) admitting a 9-dim isotropic subspace is Zariski closed.
   Natural weights fail: row/column torus weights give in(P_k) = subpermanents on the k lowest-weight rows (or the
   leading k x k block) -> 20-dim isotropic spaces (zero row 0); the AB-vs-DC weight gives the bidegree parts used by
   split/lowd (limits have >= 12-dim isotropic spaces: AB (+) a DC-isotropic for the pure-g parts, or DC itself).
   So no single natural degeneration keeps the bound; a useful one would have to be found by search (not attempted).
STATUS 13:49: (after restart) cyclic + abelian product expected-dim scans complete (all negative, also at K=6,7 -> uncalibrated); running calibrated equivariant LM (repr/eqlm.py) batches for K=8.
STATUS 13:58: tables written (repr/TABLE-expdim.txt); calibrated equivariant LM + product-type LM running.
## (6) COMPLETE expected-dimension table, full system P_2..P_5 (coordinator item 1)  -> repr/TABLE-expdim.txt
 Scanned: all 34 conjugacy classes of cyclic subgroups of (S5 x S5).2 (incl. transpose type), all 48 products R x C of
 abelian subgroups R, C of S5 (1, Z2, Z2', Z3, Z4, Z5, Z6, two Klein groups, Z3xZ2), and 14 non-cyclic abelian groups that are
 diagonal or contain the transpose. For each: joint eigenspaces W_a (dims d_a), all multisets of characters with trivial
 product whose restricted polarised P_k is nonzero (random evaluation), then max over (k_a), sum k_a = K, of
 sum k_a(d_a-k_a) - #equations.
 RESULT: NO configuration has expected dimension >= 0 for K = 8 or K = 9 (best: -11 at K=8, -15 at K=9, for Z3 x Z5 / the
 order-15 element; typical values -20..-300). So there is nothing to 'test exactly'.
 CAVEAT (important): the same scan is negative for K = 6 and K = 7 too (best -5, -8), although 7-dim level spaces with Z3-
 and Z4-symmetry exist. Every level space of dim >= 6 is an excess-intersection object even inside symmetric charts, so this
 table carries no evidence about existence; it only says 'no cheap automatic 8'.
## (7) CALIBRATED equivariant LM (repr/eqlm.py: analytic Jacobian via Pk_grad, charts on the eigenspaces; KS env selects P_k)
 Calibration (planted structures found): Z3-rows {fixed:5, w:2} K=7 -> res 7e-9 (1/3 starts); Z4-cols {fixed:4, i:3} K=7 ->
 5e-9 (L080 type); Z4-cols {fixed:4, -i:5} K=9 with P_2,P_3 only -> 2.5e-9 (= L9).
 K = 8, full system, best residual over 3-4 random starts (all stall at O(1); 'residual' = norm of P_2..P_5 at ~1000 unit points):
   Z3 rows (dims 14,5,5), all vectors (k0,k1,k2) with k1,k2 <= 3 up to w<->w^2:  (6,2,0) 1.2 | (5,3,0) 1.4 | (5,2,1) 1.4 |
     (4,2,2) 1.6 | (6,1,1) 1.1 | (7,1,0) 3.4 | (4,3,1) 1.7 | (3,3,2) 2.2 | (8,0,0) 6.8      [k1 >= 4 impossible: P_3 = 6 e3(p)
     on the w-eigenspace u (x) p forces e3 = 0 on the p-space]
   Z4 cols (dims 9,5,5,5): (5,3,0,0) 4.7 | (4,4,0,0) 0.77 | (4,3,1,0) 1.3 | (4,3,0,1) 1.6 | (6,2,0,0) 10.7 | (3,3,0,2) 2.2 | (5,2,0,1) 4.9
   Z5 cols (dims 4,5,5,5,5): (3,5,0,0,0) 16 | (4,4,0,0,0) 22 | (2,4,2,0,0) 5.7 | (3,4,1,0,0) 16
   transpose T (sym 14, antisym 10): (8,0) 6.3 | (7,1) 4.0 | (6,2) 2.6 | (5,3) 2.1 | (4,4) 1.8   [rest not run: load]
 K = 9, which of P_4 / P_5 is needed in the L9 symmetry class (Z4 cols):
   P_2,P_3,P_4: (4,0,0,5) 0.75 | (5,0,0,4) 3.8 | (4,1,0,4) 1.9;  Z5 cols (0,5,4,0,0) 2.9 | (2,5,2,0,0) 4.6
   P_2,P_3,P_5: (4,0,0,5) 0.69    -> numerically EACH of P_4, P_5 alone already destroys the 9-dim solutions of this class.
## (8) STRUCTURE: a Cauchy-type identity and an exact factorised criterion for 'rank-one-family' (RF) spaces  [exact]
 IDENTITY (hand proof via perm(J+t) = [y_1..y_5] prod_j (u + l_j) in C[y]/(y_i^2), u = sum y_i; numerically verified
 to 1e-15 for M = 1,2,3,5,7 in repr/cauchy.py): for ANY 5 x M matrices X, V
      perm(J + X V^T) = sum_{a in N^M, |a| <= 5} (5-|a|)! a! E_a(X) E_a(V),
      E_a(X) := coefficient of z^a in prod_{i=1..5} (1 + sum_m X_im z_m)
               = sum over pairwise disjoint row sets R_1..R_M, |R_m| = a_m, of prod_m prod_{i in R_m} X_im.
 (M = 1: sum_k (5-k)! k! e_k(x) e_k(v). V = I: the column expansion. Symmetric under X <-> V.)
 RF CLASS: L = (+)_m { x v_m^T : x in X_m } (+) (+)_m' { u_m' y^T : y in Y_m' }  (fixed patterns v_m, u_m'; subspaces X_m, Y_m').
 EVERY known example is RF: L080, ex1, ex2, rc45, the 4-dim DC space K = u p^T + conj(u) q^T, product type (patterns e_j),
 and L9. Writing t = [X | U][V | Y]^T, multidegrees separate, and each term is (polynomial in x) * (polynomial in y), so
   RF CRITERION: L is level  <=>  for every multidegree (a; a') != 0 with |a| + |a'| <= 5:
        G_{a,a'}(x) := [z^a w^a'] prod_i (1 + sum_m x_m(i) z_m + sum_m' u_m'(i) w_m')  vanishes identically on prod X_m,   OR
        F_{a,a'}(y) := [z^a w^a'] prod_j (1 + sum_m v_m(j) z_m + sum_m' y_m'(j) w_m')  vanishes identically on prod Y_m'.
   (For column-only RF: for each a, E_a(V) = 0 or E_a == 0 on prod X_m.  L9: E_(a,b)(chi, e_4) = [z1^a z2^b](1 - z1^4)(1 + z2).)
   PRODUCT TYPE (L_gct_114 setting; patterns e_i, e_j): for all column sets C and row sets R, not both empty, |C|+|R| <= 5:
        M_{R^c}(s_C) == 0 on prod_{j in C} S_j   OR   M_{C^c}(w_R) == 0 on prod_{i in R} V_i,
        M_A(s_C) := sum over injections f: C -> A of prod_j s_j(f(j))  (restricted injective sums).
   Consequences by hand: (i) a c-family of dim 4 needs e2 = e3 = e4(v) = 0, so v = e_j (X = sum-zero) or v = 5th roots
   (X = a coordinate hyperplane); no c-family has dim 5.  (ii) full row i0 (dim 4) forces S_j(i0) = 0 and a level column
   system on the other 4 rows, so column part <= 3: product type with a full row/column has dim <= 7.
 This turns the search for structured counterexamples into combinatorics on pattern sets + small polynomial identities.
## (9) PRODUCT-TYPE LM (repr/prodlm.py; unknowns = charts of V_i, S_j in Gr(.,5); analytic Jacobian; residual = P_1..P_5 at ~1000 pts)
 Calibration: rows (3) | cols (4) [L080]: 3/3 starts, 7 iterations, 1e-13;  rows (4) | cols (1,1,1) [ex2 type]: 3/3, 1e-13.
 K = 8 needs (sum dim V_i, sum dim S_j) = (4,4) (L_gct_114). All 15 unordered pairs of dimension patterns, 4 starts each, best residual:
   (4|4) 4.9  (4|31) 3.5  (4|22) 3.6  (4|211) 3.2  (4|1111) 3.1      [(4|*) also impossible by hand, section 8 (ii)]
   (31|31) 2.5  (31|22) 2.0  (31|211) 2.3  (31|1111) 2.1
   (22|22) 1.5  (22|211) 1.8  (22|1111) 2.1
   (211|211) 1.9  (211|1111) 1.7   (1111|1111) 3.4
 => no product-type level space of dim 8 at n = 5 (strong numerical evidence: the same code hits every planted 7 immediately).
 Further equivariant LM results (K = 8, full system, 3 starts): diagonal Z3 ((012),(012)), dims (10,7,7): (4,2,2) 2.0 | (5,2,1) 2.4 |
   (6,1,1) 6.1 | (4,3,1) 2.1 | (3,3,2) 2.1 | (2,3,3) 2.5 | (6,2,0) 6.0 | (5,3,0) 2.1 | (4,4,0) 1.9 | (7,1,0) 8.1;
   diagonal Z5, dims (4,5,5,5,5): (2;2,2,1,1) 1.9 | (2;3,3,0,0) 2.3 | (2;3,0,0,3) 5.1 | (2;2,2,2,0) 2.0 | (0;2,2,2,2) 2.2 | (1;3,2,1,1) 1.4;
   Z5 cols, two 5th-root column families: (0;4,4,0,0) 3.5 | (0;4,0,4,0) 3.0 | (0;4,0,0,4) 7.2 | (2;3,3,0,0) 5.1 | (1;4,3,0,0) 2.1;
   Z2 x Z2 ((01) on rows, (01) on cols), dims (15,4,4,1): (6,1,1,0) 1.9 | (5,2,1,0) 1.5 | (4,2,2,0) 1.6 | (6,2,0,0) 3.2 | (7,1,0,0) 3.2 |
     (5,1,1,1) 3.0 | (4,4,0,0) 12;   Z3 x Z3, dims (8,3,3,3,1,1,3,1,1): five vectors, 1.6 .. 8.4;
   Z4 cols (4,4,0,0) re-run with 3 more starts: 0.75, 0.74, 0.74 (a genuine local minimum, not a solution).
 RF with FREE patterns (repr/rflm.py) FAILS calibration (families collapse onto each other; (c4,r3) not found) -> not used.
## (10) Best next steps
 0. (most promising, see section 11) CONJECTURE (D): every level space of dim >= 7 has a deletable row or column (34/34 examples,
    exactly one each). Exact dictionary: with delta_c(t) := sum_i t_ic padj(J+t)_ic = 120 - (column-c sum of padj(J+t)) one has
    perm(J + t^(c)) = 120 - delta_c(t), sum_c delta_c = 0 on L, and the linear part of delta_c is 120 beta_c; so 'column c
    deletable' <=> delta_c == 0 on L => beta_c == 0 on L => r_B <= 3. (D) therefore implies split's 'alpha, beta not both onto'
    and gives a normal form (L = (L cap column c) (+) lift of a 5 x 4 level space) on which <= 8 can be attacked; an LM search
    for 8-dim spaces can be restricted to this normal form (not done here).
 a. Prove 'product type <= 2n-3' at n = 5 from the factorised criterion (section 8): finite case analysis over zero patterns
    S_j(i) = 0 / V_i(j) = 0; it would sharpen L_gct_114 and is a template for the RF class.
 b. RF class with a FINITE pattern menu (unit vectors, k-th roots of unity on k coordinates, e_a - e_b, (1,1,1,0,-3)): with fixed
    patterns the LM is as well conditioned as prodlm.py, and the criterion is 'F_a == 0 or G_a == 0' per multidegree -- a
    combinatorial search that either yields an 8-dim RF level space or a proof that RF spaces have dim <= 7.
 c. For a proof of the gap: P_4 is the decisive form (it alone kills L9 and its symmetric relatives); in u-coordinates use the
    identity of section 8 with V = Fourier matrix (only multidegrees with sum m a_m = 0 mod 5 survive) to get sparse formulas.
## (11) New 7-dim product-type level spaces in every pattern; the 'deletable column' phenomenon   [14:16]
 repr/prodlm.py, K = 7, patterns rows in {(3),(2,1),(1,1,1)} x cols in {(4),(3,1),(2,2),(2,1,1),(1,1,1,1)}: ALL 15 converge
 (res 1e-13, 3 starts each); saved as repr/prod_<rows>_<cols>_9.npy (7 x 25 complex bases). Independent checks (repr/ext.py):
 normalised-basis smin 0.45..1.0; P_1..P_5 at 400 random points: 1e-16; first-order extension space has dim 8 for all 15.
 For all 15: (r_A, r_B, r, d) = (4, 3, 7, 0) (the L080 split), and the extra first-order direction is y = 1 e_c^T - J/5 for one
 column c (pure AB, P_2(y) = -2 for unit y) -> no 8-dim level space contains any of them (second-order obstruction in P_2).
 EXACT identity behind it: perm is linear in column c, so D_{1 e_c^T} P_k (t) = (6-k) P_{k-1}(t with column c zeroed), and
 D_J P_k(t) = (6-k) P_{k-1}(t). Hence  y_c := 1 e_c^T - J/5 is in the first-order extension space of a level L
   <=>  P_k(t^(c)) = 0 for k = 1..4 and all t in L   <=>   L remains level after zeroing column c.
 Numerically each of the 15 product-type spaces has EXACTLY ONE such column (and no such row).
 CHECKED on the other known 7-dim spaces (CORRECTION 14:20: my first test used a 1e-7 threshold on LM bases that are only
 ~1e-7 accurate as subspaces (singular solutions: level error ~ basis error^2) and wrongly reported 'none'; with the actual
 errors the picture is uniform): split/rc45p1 (= ex1): row 3 deletable (err 3e-7, next best 0.3); numerics/nb_c1_e1_1_0..3,
 nb_c2_e2_2_0,1: column 4 (2e-8..7e-8 vs 0.5); numerics/r2/F_e2_blk_0,3,5,6,7: row 3 (3e-15 vs 0.6); r2/row3_e3_1_0,5: row 3
 (1e-7 vs 0.5); r2/sol7_ex1_d0_0..2, d2_0, d6_0: row 3 (3e-8..2e-5 vs 0.2..0.6, in line with their level errors 1e-15..1e-10).
 For rc45p1, nb_c1_e1_1_0, row3_e3_1_0 the extra first-order direction was computed directly: it is exactly the coordinate
 direction (e_3 - 1/5)(x)1, resp. 1(x)(e_4 - 1/5), with P_2 = -2.
 ==> OBSERVED LAW (34 of 34 spaces: 19 from the team + the 15 new product-type ones): every known 7-dim level space has
     EXACTLY ONE deletable row or column, and its first-order extension space is L + C*(that constant row/column direction).
 CONJECTURE (D): every level space of dim >= 7 (n = 5) has a deletable row or column. If (D) holds, the gap reduces to:
   L level with column c deletable  =>  dim L <= 8, where pi_c(L) is a level space of 5 x 4 matrices (perm[1 | J + t'] = 120)
   and ker(pi_c|L) = L cap {x e_c^T} has dim <= 4 (FK). A deletable column gives a concrete normal form to attack.
STATUS 14:21: final. Remaining background LM (batch5: Z2xZ2 configs) may still be running; results so far all negative.
STATUS 14:18: background jobs stopped; final report sent. Files: repr/{core,lie,equiv,eqlevel,abscan,abscan2,eqlm,prodlm,rflm,ext,cauchy,nine,ext9}.py, repr/TABLE-expdim.txt, repr/prod_*_9.npy (15 new 7-dim product-type level spaces), repr/*.log.
