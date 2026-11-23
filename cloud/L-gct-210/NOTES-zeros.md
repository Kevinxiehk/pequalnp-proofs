# NOTES-zeros (role: zeros; start 13:19, budget 75 min -> ends ~14:34)

## RESULT (zeros, final 14:15) -- gap NOT proved in general; the FREE-LINE BRANCH is settled completely and sharply
 R1 [RIGOROUS hand proof, sections "RESULT 1" + "RESULT 4"; uses P_4/P_5 exactly where needed; kills L9; 7-dim examples survive]
    THEOREM FL: a 5x5 level space containing a full free row F_r = {e_r w^T : sum w = 0} (or a full free column) has
    dim <= 7 (sharp: L080, ex1, ex2, ex3, the s-family, the 4x2 family and the new R3 space all are F_r (+) 3-dim).
    Core, LEMMA SL: a linear space L' of 4x5 matrices all of whose 4x4 column deletions are 4x4-level ("strongly level")
    has dim <= 3; and L level with F_r inside  <=>  L = F_r (+) L', L' strongly level (rows != r).
    Proof skeleton: q = dim(row-sum image) <= 3, N = L' cap DC, dim L' = q + dim N;
      (i) each column of N lies in one isotropic line of V_4 (deletion-P_2)  => N = {sum l_m v_m e_m^T, sum l_m v_m = 0};
      (ii) dim N <= 2 (deletion-P_3, deletion-P_4 = P_5 of the 5x5 space; this is the step that kills L9^T, where N = chi_1 (x) V_5);
      (iii) q = 3 => N = 0, q = 2 and N != 0 => S = u^perp degenerate (B_m := 2A_m - I is an isometry; N-columns perp B_m(S));
      (iv) (q,d) = (2,2) impossible: 2-dim N are of types I (chi_1 (x) sum-zero on 3 columns), II (ex1 plane: two isotropic
           vectors with a common zero row, on column pairs), III, IV; III and IV do not exist (cubic/quartic), I and II are
           incompatible with the isotropic row-sum direction u (cubic + quartic).
    COROLLARIES: (a) no level space of dim >= 8 contains a full free row or column; in particular no level space properly
    containing a 7-dim space of the known types exists, and any 8/9-dim level space is "free-line-free" (the n = 4 dim-5
    space sol_n4_d5 is of that kind, so such spaces are not absurd).  (b) if L_r = L cap {row r = 0} is strongly level for
    some r then dim L <= 3 + 4 = 7; so in a level space of dim >= 8, for EVERY row r (and column) some element of L_r has
    non-constant deletion polynomials perm(J_4 + s Y^(j)).  (c) closes the exceptions (r,d) left open in NOTES-hessmix.
 R2 [RIGOROUS, general] COFACTOR-ANNIHILATOR principle (CA), section "RESULT 2": for every FK block K and x in L vanishing on K,
    grad P_5(x) is supported on K, is rank one for 3x3 and 2x4 blocks, and lies in Ann_K cap J^perp (dim a_K - 1).
    For a 9-dim level L: (CA1) every 3x3 block has either a >= 2-dim vanishing subspace or a vanishing element with a zero
    line or a (2 rows + 1 column)/(1 row + 2 columns) support; (CA2) if a row projection pi_r(L) is 4-dim then L_r is a 5-dim
    4x5 level space on which all five maximal-minor permanents vanish identically (inside Sing(perm_5));
    (CA3) for a 2x4 block with a_K = 1, the 2-dim M_K either has rows a,b == 0 or all 3x3 minors of its 3x4 part vanish.
 R3 [EXACT, new example] F_r (+) chi_1 (x) C^3 is a 7-dim level space: rows 0..3 = (1,i,-1,-i)^T x^T with x supported on 3
    columns, row 4 any sum-zero row.  (P_k(chi_1 x_S^T) = k! e_k(chi_1) e_k(x_S) = 0.)  Split (r,d,r_A,r_B) = (5,2,1,4), generic
    rank 2 (ex1 has rank 4): a new type; it is the maximal level part of L9^T containing the free row; (q,d) = (1,2) with
    ISOTROPIC row-sum line (ex1 has (1,2) with non-isotropic line).
 Ruled out / dead: FK admissibility alone (allows dim 20); "every 4x5 level space of dim >= 5 contains a free line" (false:
    embed sol_n4_d5); LM as evidence for strongly level spaces (it misses the existing (1,2) types).
 Best next step: the gap now needs only FREE-LINE-FREE level spaces. Use CA2: classify 5-dim 4x5 level spaces on which all
    maximal-minor permanents vanish (show they are strongly level -> contradiction with SL, or contain a free row -> FL);
    that would force every row and column projection of a 9-dim level space to have dim <= 3 (a_r >= 2).
    Formalisation note: Lemma SL is a finite statement about <= 3 + columns in a 3-dim quadratic space; steps (i)-(iii) are
    short; step (iv) needs the explicit character computations of section RESULT 4.
STATUS 13:19: started; read BRIEF (+UPDATE), NOTES-lowd/adversary/methods/split/numerics/dc5/hessmix.
 Observation (exact, trivial): FK admissibility ALONE is useless: {t : t_{i,sigma(i)} = 0} (20-dim) meets no FK block
 condition (every p x q block with p+q = 6 contains a cell of every permutation). Zero-pattern arguments must use P_k content.

## RESULT 1 (13:27, RIGOROUS, hand proof; numerically sanity-checked): FREE ROW => dim L <= 8.
Lemma FR. Let L be a 5x5 level space containing a full free row F_r = {e_r w^T : sum w = 0} (all 7-dim examples
L080, ex1, ex2, ex3, the s-family, the 4x2 family contain one, up to transpose). Then dim L <= 8. (Same for columns.)
Proof. (a) REDUCTION (zero pattern = row r). WLOG r = 5. For y in L, s, w in V_5: perm(J+sy+e_5 w^T) is linear in row 5:
  perm(J+sy) + sum_j w_j C_j(s) = 120, C_j(s) = perm of J+sy minus row 5, column j. So C_j(s) = C(s) for all j, and
  120 = perm(J+sy) = (5 + s rho) C(s), rho = row-5 sum of y; polynomial identity => rho = 0, C(s) == 24.
  Hence L = F_5 (+) L'_0 with L'_0 = L cap {row 5 = 0} =: L' (4x5 matrices Y = rows 1..4), dim L = 4 + dim L', and
  L' is "STRONGLY LEVEL": every 4x4 column deletion Y^(j) is a 4x4 level matrix (perm(J_4 + s Y^(j)) == 24). Conversely
  any strongly level L' gives a level F_5 (+) L'. So the claim is: strongly level L' has dim <= 4.
(b) CONDITIONS. P_1(Y^(j)) = 0 for all j => all column sums of Y are 0 (columns Y^j in V_4 = sum-zero C^4, form = dot).
  With s = s(Y) = row-sum vector (in V_4), the 2P_2 identity (2P_2 = p_2 - |rowsums|^2 - |colsums|^2) gives
    P_2(Y^(j)) = 0 for all j  <=>  q_j(Y) := <Y^j,Y^j> - <s,Y^j> = 0 for every column j   (Sum_j q_j = |Y|^2 - |s|^2).
  CC formula: P_3(Z) = 2 sum_i e_3(Z_i) for column-centred Z; P_4(Y^(j)) = perm(Y^(j)).
  On N := L' cap {s = 0} (= L cap DC): with e_3(v minus entry d) = p_3(v)/3 - d^3 + d p_2(v)/2 (p_1(v) = 0):
    (C3_j) sum_i Y_ij^3 = (1/2) sum_i Y_ij p_2(Y_i)   for every column j  (and p_3(Y) = 0),   (C4_j) perm(Y^(j)) = 0.
(c) N COLUMNWISE ISOTROPIC. Polarising q_j on N: 2<Y^j,Z^j> = 0, so the column-j projection of N is a totally isotropic
  subspace of the 3-dim nondegenerate V_4: a line C v_j with v_j.v_j = 0, or 0.  So N = {sum_j l_j v_j e_j^T : sum_j l_j v_j = 0}
  restricted further by C3, C4. Group the active columns by line: g distinct lines => dim N <= k - rank <= 2 if g >= 3
  (3 points on a smooth conic span V_4); g = 1: N = {v l^T : l in Lambda}; if dim Lambda >= 2, C3_j reads
  l_j^3 p_3(v) = (1/2) l_j p_2(l) p_3(v) identically, which forces p_3(v) = 0 (else all active l_j = +-one form), so
  v = 4th roots of unity (all v_i != 0), and C4_j: 24 e_4(v) prod_{m != j} l_m == 0 forces two coordinates of Lambda
  to vanish: dim N <= 2. g = 2 with column classes M1 (line v), M2 (line v'): dim N <= |M1|+|M2|-2 <= 3, with 3 only for
  sizes {2,3}, N = {mu v (e_a - e_b)^T + v' nu^T : nu on M2, sum nu = 0}. Then C3 on M2 (mu = 0, 2-dim nu space) forces
  p_3(v') = 0, WLOG (row permutation) v' = chi_1 = (1,i,-1,-i); C3 on M1 gives v . (v' * v') = v . chi_2 = 0; C4 for the
  deletion of a in M1 gives 6 e_4(v') sum_i v_i / v'_i = 0, i.e. v . chi_3 = 0; with v . chi_0 = 0 this forces v = c chi_3
  (<chi_a, chi_b> = 4[a+b = 0 mod 4]); but then C4 for a deletion in M2 gives -mu^2 nu nu' perm[v,v,v',v'] = -8 c^2 mu^2 nu nu'
  != 0 (perm[chi3,chi3,chi1,chi1] = 8 checked numerically). So dim N <= 2 ALWAYS.
(d) q := dim s(L') = 3 FORCES N = 0 (orthogonal-matrix trick). Choose L'' in L' with s: L'' -> V_4 iso; Y(sig)^j = A_j sig,
  sum_j A_j = I. q_j = 0 <=> A_j^T A_j = (A_j + A_j^T)/2 <=> B_j := 2A_j - I is ORTHOGONAL (B_j^T B_j = I).  Polarising q_j
  between Y(sig) and Z in N: <Z^j, (2A_j - I) sig> = 0 for all sig, i.e. B_j^T Z^j = 0, so Z^j = 0: N = 0.
  [More generally the cross condition is  Z^j  perp  B_j(S),  S = s(L'), B_j an isometric embedding of S (form restricted).]
(e) dim L' = q + dim N with q <= 3, dim N <= 2, and q = 3 => N = 0: dim L' <= 4, dim L <= 8.  QED
 Remarks: uses only P_1..P_4 of the deletions (i.e. levelness). The same trick with q = 2: if S = s(L') is a NONDEGENERATE
 plane then B_j(S)^perp is a non-isotropic line, so N = 0; so (q,d) = (2,2) needs S = u^perp, u isotropic (as in ex2).
 The sharp "free row => dim <= 7" needs (q,d) = (2,2) with S degenerate excluded: DONE in section RESULT 4 (types I-IV).
STATUS 13:38: read UPDATE 3. CHECK vs L9 (exact P2P3-only 9-space {x v^T + z e_4^T}, v = (1,i,-1,-i,0)): L9 CONTAINS A FULL
 FREE COLUMN (z e_4^T). Transposed it is F_4 (+) L' with L' = chi_1 (x) C^5 (4x5), q = 1, N = chi_1 (x) {sum x = 0} (dim 4,
 type g = 1 with v = chi_1, p_3(v) = 0). It satisfies every quadratic/cubic step (b)-(d) of Lemma FR and is killed ONLY by
 the quartic step C4: perm(Y^(m)) = 24 e_4(chi_1) prod_{j != m} x_j != 0 (deletion-P_4 = coefficient of s^4 in C_j(s),
 i.e. it comes from P_5 of the 5x5 space). So Lemma FR uses P_4/P_5 exactly where the brief says it must, kills L9,
 and is tight-compatible with all 7-dim examples (q + d = 3 there).
 Numerics (zeros/sl.py, Gr(k,15) LM on strongly level 4x5 spaces): k = 3 found 3/3 (all of type (q,d) = (3,0), columns
 supported on 2 columns); k = 4: 0/4 (cost ~1e3). Structured (zeros/sqd.py): (q,d) = (2,1) with S degenerate found 3/3
 (ex2 type); (1,2) [ex1 type] NOT found 0/4 -> structured negatives for (2,2) would be uncalibrated; not relied on.

## RESULT 2 (13:45, RIGOROUS, general): COFACTOR-ANNIHILATOR principle (CA) for FK blocks -- a P_5 zero-pattern tool
Setting: L level, dim l, K an FK block (p x q, p+q = 6: 3x3, 2x4, 4x2, rows, cols), Ann_K := {n in C^K : <n, x|_K> = 0 for all
x in L} (a_K := dim Ann_K >= 1 by FK, and Ann_K contains n_K with sum n_K != 0), M_K := L cap {x|_K = 0},
dim M_K = l - |K| + a_K.   For x in M_K, grad P_5(x) (= 4x4 minor permanents) VANISHES OFF K (every other minor still
contains a FK zero block), and since L perp grad P_5(x) (s^4 coefficient of the gradient condition) and
<grad P_5(x), J> = P_4(x) = 0:
      Phi_K(x) := grad P_5(x)|_K  lies in  Ann_K cap J^perp   (dimension a_K - 1)   for every x in M_K.
Explicit Phi_K (checked numerically on L080, ex1, ex2 for all 210 blocks, zeros/cofann.py, violation <= 1e-14):
  3x3 block R x C, x = [[Z, X],[Y, 0]] (X = x[R^c, C] 2x3, Y = x[R, C^c] 3x2):  Phi_K(x) = u v^T,
      u_i = perm(Y[R\i, :]) (2x2 permanents of row pairs of Y),  v_j = perm(X[:, C\j]);  sum u * sum v = P_4(x).
  2x4 block (rows a,b; columns != c): rows a,b of x live in column c only; Phi_K(x) = (x_bc e_a + x_ac e_b) w^T,
      w_j = perm(x[other 3 rows, [5]\{j,c}]).
  row r: Phi_r(x) = (perm of x minus row r, column j)_j  (the 5 maximal-minor permanents of the 4x5 matrix).
CONSEQUENCES for a 9-dim level L (dim M_K = a_K for 3x3, a_K + 1 for 2x4, a_r + 4 for rows):
 (CA1) 3x3 blocks: either a_K >= 2 (a >= 2-dim subspace of L vanishes on K, and Phi_K maps it into an (a_K - 1)-space of
   rank-one matrices), or a_K = 1 and the unique x_K has u = 0 or v = 0. u = 0 <=> the rows of Y are pairwise orthogonal
   for beta(a,b) = a1 b2 + a2 b1, which forces (U1) a zero column of Y, i.e. x_K vanishes on a 3x4 block (support = 2 rows
   + 1 column), or (U2) a zero row of x_K (and the other two rows of Y beta-orthogonal). Same with v: (V1) 4x3 zero block
   (support 1 row + 2 columns) or (V2) a zero column of x_K.  So in a 9-dim level space EVERY 3x3 block carries either a
   2-dim vanishing subspace or an element with a zero line / a (2 rows + 1 col) support.
 (CA2) rows: a_r = 5 - dim pi_r(L). If a_r = 1 (row projection 4-dim, the generic case) then L_r = L cap {row r = 0} is a
   5-dim 4x5 level space on which ALL FIVE maximal-minor permanents vanish identically (L_r inside Sing(perm_5)); if
   a_r >= 2 then dim L_r >= 6 and the minor-permanent vector of L_r stays in a fixed (a_r - 1)-space.
 For the free-row case (Lemma FR) a_r = 1 and CA2 is exactly the quartic step C4 that kills L9.
 These are necessary conditions only; no contradiction for 9-dim extracted yet (time). They are the natural P_5 input for
 a zero-pattern chain: e.g. "a 5-dim 4x5 level space with all maximal-minor permanents == 0 does not exist" would force
 a_r >= 2 for every row and column (all row/column projections <= 3-dim).

## RESULT 4 (14:05-14:12): PROOF of the sharp bound "strongly level L' has dim <= 3" -- column (Hadamard) form of the conditions
 Notation: Y in L' (4x5, column sums 0), columns y_m in V_4, s = sum_m y_m (row sums), products = Hadamard products in
 C^4, tau = sum of the 4 coordinates, a.b = tau(ab). Put w_m := y_m - s/2, W2 := sum_m w_m^2. Then strongly level <=>
   (C2_m) tau(w_m^2) = tau(s^2)/4,     (C3_m) tau( (w_m + s/2)(2 w_m^2 + (3/4) s^2 - W2) ) = 0,     (C4_m) perm(Y^(m)) = 0,
 for every column m, where perm[y_1..y_4] = -6 tau(y_1y_2y_3y_4) + sum over the 3 pairings (y_a.y_b)(y_c.y_d).
 (Derivation: P_k(Y^(m)) = sum over partitions without singletons; Newton in the Hadamard algebra; E := tau(s^3) -
  3 tau(s P2) + 2 P3 = 0 follows by summing over m.  C2 is "B_m := 2A_m - I isometric".)
 Characters chi_a = (i^{a k})_k: chi_a chi_b = chi_{a+b}, tau(chi_a) = 4[a = 0 mod 4]; V_4 = span(chi_1,chi_2,chi_3);
 isotropic vectors: v(t) = chi_1 + t chi_2 - (t^2/2) chi_3 and chi_3; the six "4th-root" lines form one S_4-orbit, so in any
 finite configuration one may assume all lines are v(t), t finite.  Exact formulas (checked numerically, zeros/t4n.py):
   perm[v(t1),v(t2),v(t3),v(t4)] = 2 e_2^2 - (3/2)(e_4 - 4)^2,   tau(v(t) v(u)^2) = 4(2u + t + t u^4/4 + t^2 u^3/2),
   v(t) has a zero entry in row k iff t^2 - a t + b = 0 with (a,b) = (2,-2), (-2i,2), (-2,-2), (2i,2) (k = 0,1,2,3).
 (2,2) set-up: S = span(u,p), u.u = u.p = 0; Y(u), Y(p) with w_m = B_m sigma/2, b_m := B_m u isotropic, sum_m b_m = -3u;
   cross condition z_m perp B_m(S) forces b_m in C v_m on every active column (two orthogonal isotropic vectors of V_4 are
   proportional). So on Y = t Y(u) + Z (Z in N): w_m = omega_m v_m (active), w_m = t b_m/2 (inactive), s = t u.
 TYPE II (N = span(v(e_a-e_b)^T, v'(e_c-e_d)^T)): N alone needs tau(v v'^2) = tau(v' v^2) = 0 (C3) and perm[v,v,v',v'] = 0 (C4,
   deletion of the inactive column). With v = v(t), v' = v(u), a = t+u, b = tu: difference and sum of the two cubic equations
   give 4 + a^2 b + b^2 = 0 and a(12 + a^2 b - b^2) = 0; a = 0 contradicts the permanent equation (-32 vs 96); so b^2 = 4,
   a^2 b = -8: exactly the 4 pairs above = "common zero row k" (and the permanent equation then holds).  So N is the ex1
   plane: v = zeta = (1,w,w^2,0), v' = conj(zeta) up to S_4.  Now the t mu'^2 coefficient of C3_a and the t mu^2 coefficient of
   C3_c give tau(u v'^2) = tau(u v^2) = 0; v^2 = v', v'^2 = v, so u perp zeta, conj(zeta), u in C(1,1,1,-3): not isotropic. EXCLUDED.
 TYPE III (classes {a,b} (line v) and M2 of size 3 (line v'), N a plane in {mu v(e_a-e_b)^T + v' nu^T}): either mu = alpha(nu)
   or nu = kappa n; in both cases C3 on M2 forces tau(v'^3) = 0 (so v' = chi_1) and tau(v' v^2) = 0, C3 on {a,b} gives
   tau(v v'^2) = 0, C4 (delete a) gives perm[v,v',v',v'] = 6 e_4(v') tau(v/v') = 0, hence v = c chi_3, and C4 (delete a column of
   M2) gives perm[v,v,v',v'] = 8c^2 != 0. IMPOSSIBLE.
 TYPE I (N = chi_1 (x) Lambda_M, |M| = 3): C3 on Y(u) (+) N gives u, b_4, b_5 perp chi_2, so all of them lie in C chi_1 u C chi_3;
   u = c chi_3 is impossible (C4 with the closed permanent formula on span(chi_1,chi_3):
   perm = -24(p1p2p3p4 + r1r2r3r4) + 8 sum_{|P|=2} p_P r_{P^c} forces b_4 = b_5 = -c chi_3, contradicting b_4 + b_5 = -3c chi_3);
   u = c chi_1 forces Y(u) in chi_1 (x) C^M, so L' contains chi_1 (x) C^M (the R3 example). The 4th vector Y(p), p = chi_2 mod
   chi_1: polarised C2 against chi_1 x^T gives all columns in span(chi_1,chi_2), then C2 gives exactly one column with chi_2-
   coefficient 1: Y(p) = chi_2 e_a^T (a in M) or (chi_2 + pi chi_1) e_4^T - pi chi_1 e_5^T; C3 on an M-column then reads
   8 t x_m x_{a'} = 0, resp. 8 t x_m (sum x - x_m - pi t) = 0: false. EXCLUDED (also numerically, zeros/t22.py).
 TYPE IV: see "TYPE IV DONE" below (rigorous).  Sanity (zeros/sldc.py): LM inside DC finds 2-dim strongly level planes (3/4 starts), each
   with 4 active columns and column ranks 1 (type II), and no 3-dim one (0/4), as Lemma FR(c) predicts.
 TYPE IV DONE (14:12, rigorous; replaces "open" above). Five active columns force multiplicity pattern (2,1,1,1) or all
   distinct (patterns (3,1,1), (2,2,1) force an inactive column). Lines v_m = C v(theta_m), all theta finite WLOG;
   Psi(l) := sum_a l_a^2 v_a^2 = A chi_2 + 2B chi_3 - C chi_1,  A = sum l_a^2 (1 + theta_a^4/4), B = sum l_a^2 theta_a,
   C = sum l_a^2 theta_a^3;  tau(v(t)^3) = 3t(4 + t^4);  C3_m on N (s = 0) reads
        G(theta_m) := 4B + 2 theta_m A + theta_m^2 C = 3 theta_m (4 + theta_m^4) l_m^2      (quadratic forms on N).
   [Checked numerically: P_3(Z^(m)) = (2/3) sum_a l_a^3 tau(v_a^3) + l_m (8B + 4 theta_m A + 2 theta_m^2 C) - 6 l_m^3 theta_m(4+theta_m^4),
    error 1e-16, zeros/chk4.py.]
   (2,1,1,1): N = span(e_a - e_b, n); the mu^2 coefficient of C3_c, C3_d, C3_e gives f(theta_c) = f(theta_d) = f(theta_e) = 0 for
     f(x) = 2 theta_1^3 x^2 + (4 + theta_1^4) x + 8 theta_1, a quadratic with 3 distinct roots: f == 0, impossible.
   all distinct: l_m = g(theta_m)/omega'(theta_m), g = alpha + beta x, omega = prod (x - theta_a).  G(x) has degree <= 2 in x and
     G(theta_m) = c_m g(theta_m)^2 at 5 points; comparing the alpha^2, alpha beta, beta^2 coefficients G_1, G_2, G_3: G_2 - 2x G_1
     (degree <= 3) and G_3 - x^2 G_1 vanish at 5 points, so G = c_0 (alpha + beta x)^2 with c_0 constant, i.e.
     4B = c_0 alpha^2, A = c_0 alpha beta, C = c_0 beta^2, and 3 theta_m(4 + theta_m^4) = c_0 omega'(theta_m)^2 for all m.
     c_0 = 0: the theta_m are the 5 roots of x^5 + 4x, omega' = 5x^4 + 4 (= 4 at 0, -16 else), and the alpha beta coefficient of C
       is 2 sum theta^4/omega'^2 = -1/8 != 0.  c_0 != 0: A = (c_0/12) sum_a g(theta_a)^2/theta_a has alpha beta coefficient
       (c_0/12)*10 = (5/6) c_0 != c_0.  IMPOSSIBLE in both cases.
   Numerics agree: zeros/t4n.py 0/81 LM starts (cost floor 1.3); zeros/sldc.py: every 2-dim DC strongly level plane found has a
   zero row and 4 active columns (type II), none of dim 3.
 Remark on types II/III and Lemma FR(c): the step "v perp chi_2" is not needed: v isotropic and v perp chi_3 already give
   v in C chi_3 (v = p chi_1 + q chi_2 + r chi_3, v.chi_3 = 4p, v.v = 8pr + 4q^2).  In type I the fourth vector may be taken
   as chi_2 e_a^T + chi_1 (pi_4 e_4 + pi_5 e_5)^T (then C4 forces pi_4 pi_5 = 0 and C3 gives 8 t x_m (x_{a'} + t pi) != 0) or
   (chi_2 + pi_4 chi_1) e_4^T + pi_5 chi_1 e_5^T (C3 gives 8 t x_m (sum_{M\m} x + t pi_5) != 0).
STATUS 14:15: final. See RESULT at top.
 Completeness of the type list for a 2-dim N (all columns of N in isotropic lines, k active columns, g distinct lines):
   g = 1: Lemma FR(c) gives p_3(v) = 0 and two vanishing coordinates, so N = chi_1 (x) {sum-zero on 3 columns} (type I);
   g = 2: a class of size 1 would be inactive, so sizes (2,2) (k = 4, N = the whole 2-dim space: type II) or (2,3) (k = 5, N a
          plane in a 3-dim space: type III, sub-cases mu = alpha(nu) and N containing v(e_a - e_b)^T);
   g >= 3: dim N <= k - 3 forces k = 5 and N = ker[v_1..v_5]; activity of all 5 columns forces pattern (2,1,1,1) or (1^5): type IV.
 Why (2,2) is the only way to dim 4: dim L' = q + d, q <= 3, d <= 2, q = 3 => d = 0; and for q = 2, d >= 1 the plane S must be
   degenerate, S = u^perp with u isotropic in S; then C Y(u) (+) N is a (1,2) configuration with isotropic row-sum line, which
   exists only for type I (it is chi_1 (x) C^3, R3), and that one admits no fourth vector.
 Caveat on numerics: zeros/extsl.py (fixed-F extension LM) FAILS its calibration (does not recover ex1's h e_4^T over the type
   II plane), so no numerical extension test is quoted; the formulas used in the hand proofs were each checked numerically
   (zeros/chk1.py, chk4.py, t22.py, t4n.py header lines, cofann.py) and the examples exactly.
STATUS 14:12: done; final report sent (Theorem FL: free line => dim <= 7, hand proof; CA principle; new 7-dim example; general gap still open).
