# NOTES-chief (role: chief; start 13:47, budget 90 min -> ends ~15:17)

## RESULT (chief, 14:10; all statements below are RIGOROUS hand proofs unless marked; numerics only as sanity checks)
NO complete proof of the gap and no 9-dim space. NEW TOOL that nobody used: "zero-block factorisation + unique factorisation
on L^ = CJ (+) L" (ZBF). It gives, in a few lines each:
 (R0) REFORMULATION. L level  <=>  perm restricted to the (dim L + 1)-dim space L^ := CJ (+) L is 120 * ell^5, ell(cJ + t) = c.
      (perm(cJ + t) = c^5 perm(J + t/c).) So the gap is: no 10-dim linear space of 5x5 matrices containing J on which perm_5 is
      120 x (fifth power of a linear form). Consequences: u in L^ with perm(u) = 0 (zero row, zero p x q block with p+q >= 6) lies
      in L (FK); for x in L, u in L^: perm(u + s x) does not depend on s.
 (ZBF) If u has a zero block S x Z with |S| + |Z| = 5 then perm(u) = perm(u[S,Z^c]) * perm(u[S^c,Z]). On the LINEAR space
      U_{S,Z} := {u in L^ : u[S,Z] = 0} this is an identity f_1 f_2 = 120 ell^5 between polynomial functions, so (UFD):
      either ell != 0 on U and f_1 = k ell^|S|, f_2 = k' ell^(5-|S|) (k k' = 120), or U inside L and f_1 = 0 or f_2 = 0 on U.
      The same holds for block-triangular zero patterns with several diagonal blocks (each block permanent is k_i ell^(size)).
 (ThB) 2 x 3 zero block. Rows r != r', columns T = {j,l}, U = {u in L^: u_r, u_r' supported in T} (dim >= dim L - 5),
      Pi = image of U in the 2x2 block [rr';T] = U / L_{rr'} (L_{rr'} := L cap {rows r, r' = 0}). Then one of
        (B1) the 2x2 permanent has rank <= 1 on Pi, hence dim Pi <= 2 and dim L_{rr'} >= dim U - 2 >= dim L - 7;
        (B2) U inside L and perm(u[other 3 rows; other 3 columns]) = 0 for all u in U.
      (B1) holds whenever some t in L has rows r, r' of J + t supported in T.
 (LC) LEMMA C. If dim L = 9 then for EVERY pair of rows dim L_{rr'} >= 2 (a >= 2-dim subspace of L vanishes on both rows), i.e.
      dim pi_{rr'}(L) <= 7; same for every pair of columns. (Pigeonhole alone gives only >= 1; the improvement uses P_4, P_5,
      and the column version is VIOLATED by repr's P2P3-only space L9 (columns {0,4}: only 0 vanishes), as it must be --
      though L9 already violates plain FK there: its projection to columns {0,4} is 9-dim.)
 (ThA) AFFINE ISOTROPY. x in L with rows r, r' zero, B_x := symmetric zero-diagonal 5x5 matrix B_x[j,l] = perm(x[other rows; all
      columns but j,l]). Then (1 + t_r)^T B_x (1 + t_r') = 0 for all t in L; so C(1,1) + pi_{rr'}(L) (dim p+1) is totally
      isotropic for the form (v,v') -> v^T B_x v' of rank 2 rank(B_x):   dim pi_{rr'}(L) <= 9 - rank B_x.
      For dim L = 9: every x in L_{rr'} has rank B_x <= dim L_{rr'}; span{B_x} is a linear space of such matrices.
 (ThG) GROWTH/DUALITY FORM (bidegree (k,5-k) part of perm(u+v) = 120(ell(u)+ell(v))^5 on L^):
      sum_{|S|=|T|=k} perm(u[S,T]) perm(v[S^c,T^c]) = 120 C(5,k) ell(u)^k ell(v)^(5-k)   for u, v in L^.
      With rho_k := dim span{k x k subpermanents restricted to L^} (as degree-k forms on L^):  rho_k + rho_(5-k) <= C(5,k)^2 + 1.
      Because J is in L^, D_J maps 3x3 subpermanents ONTO 2x2 ones (the inclusion matrix of 2- and 3-subsets of [5] is invertible):
      rho_2 <= rho_3. Hence  rho_2 <= 50,  rho_1 + rho_4 <= 26.   For dim L = 9 the space of quadrics on L^ is 55-dim, so
        K_2(L^) := {sigma in S^2(L^) : all polarised 2x2 subpermanents of sigma vanish}  has dim >= 5
      (a random 10-dim L^ has K_2 = 0, rho_2 = 55; for dim L <= 8 the inequality is empty: again a 9-versus-8 threshold).
      Data (chief/rho.py, k2.py): (rho_2, rho_3, dim K_2) = L080 (20,20,16), ex1 (25,43,11), ex2 (22,31,14), ex3 (23,37,13),
      s-family (24,38,12), K+E_0 (20,38,1); K_2 is spanned by products of single-row / single-column elements of L plus 0-2 more.
 (N3) PROOF OF CONCEPT: ZBF proves "3x3 level => dim <= 3" (Gct/L094, 1650 Lean lines with certificates) in 8 lines (section 3).
 Sanity: ThA, ThB checked on L080, ex1, ex2, ex3, two s-family members, K + E_0 (700 (pair,T) cases, chief/testAB.py): no violation.
 (C4/C7/C8) MINIMAL ROW PAIRS ARE CLASSIFIED at dim 9 (annihilators without zero entries): if rows r, r' both have 4-dim
      projections and dim L_{rr'} = 2, the relations satisfied by (t_r, t_r') on L are of TYPE I (two column blocks C_1 + C_2:
      <k_1,t_r> = c<k_1,t_r'> = -<k_2,t_r> = c<k_2,t_r'>) or TYPE II (an L-shaped 3-cell pattern with a 4th root of unity);
      the generic position is impossible; and L_{rr'} is a plane of 3-row level matrices ALL of whose 3x3 subpermanents
      vanish. If the projections have dims 3 and 4 and dim L_{rr'} = 2: TYPE I' (two column blocks). (Section 4: C4, C7'', C8.)
 (DS)  Bridge to repr's conjecture (D) and zeros' Lemma SL: a deletable row with 4-dim projection forces L_r strongly level,
      hence dim L <= 7 (section 6, RP7; checked on all examples).
WHAT REMAINS (honest): (LC)+(ThA)+(C7) reduce a hypothetical 9-dim L to a rigid, non-generic configuration (section 4), and
 section 5 proposes a "sparsity cascade" ending in zeros' free-row lemma, but I did NOT derive a contradiction: the degenerate
 row pairs (zeros in n_r, the sign relation, lam >= 3, a_r >= 2) are open, and stage 3 of the cascade is not started. The method is the
 only one so far in which dim 9 differs from dim 8 by a pigeonhole and in which P_4/P_5 enter through elementary factorisations;
 it is formalizable (Laplace expansion along a row set + UFD in a polynomial ring, or the rank-<=1 quadratic-form lemma).

STATUS 13:47: started; reading BRIEF + all NOTES.
STATUS 14:00: all notes read; synthesis below; new tool found (zero-block factorisation on L^ = CJ + L).

## 1. SYNTHESIS (one page) of the team's state at 13:55
Setting: L level <=> P_1..P_5 = 0 on L. dim L = r + d, d = dim D, D = L cap DC, r = dim of (rowsum, colsum)-image <= 8,
r <= r_A + r_B. Gap <=> "D != 0 => r + d <= 8". Lean (Frame210.lean): d = 0 case; gap <= (S): r_A + d <= 4 if r_A <= r_B.
EXACT FACTS
 F1 2P_2 nondegenerate on the 24-dim sum-zero space (dim L <= 12); u-coordinates u = g - (3/2)(al_i + be_j):
    2P_2 = p2(u) - (5/9)(|R|^2+|C|^2), P_3 = (2/3)[p3(u) - (1/9)(sum R^3 + sum C^3)] (hessmix/split/growth), full P_4 formula (hessmix).
 F2 P_2, P_3 alone do NOT suffice: L9 = {x v^T + z e_4^T}, v = (1,i,-1,-i,0), is 9-dim with P_1=P_2=P_3=0 (repr). (r_A,r_B,d) = (4,1,4).
 F3 FK: for t in L, J + ct has no zero p x q block with p+q = 6; every row/column projection of L misses 1, has dim <= 4 (lowd R4).
 F4 Free row lemma (zeros, FR): L contains {e_r w^T : sum w = 0} => dim L <= 8 (4 + strongly level 4x5 <= 4). All known 7-dim
    examples contain a free row or column.  CA principle (zeros): for x in L vanishing on an FK-complement block, grad P_5(x) is
    supported on the block and lies in Ann cap J^perp.
 F5 Full rank-one row/column block {x v^T: sum x = 0} in L => r <= 7, and r = 7 => d = 0 (hessmix; P_2, P_3 only).
 F6 K (3-row DC, dim 4, exact): level spaces containing K are K and K + C E_j (dim 5) (kbuild; method L in E(D) + 2nd order).
    DC level max >= 4 (dc5), 4x4 DC max = 3 tight; DC bound <= 4 at n = 5 is NOT proved (only isotropy 8).
 F7 Special DC elements (grad P_5 = 0) = DC points of Sing(perm_5); Lemma Z (zero line) proved for rank <= 2, open rank 3, 4 (lemmaz).
 F8 supports with vertex cover 2: <= 7 exact; 2 rows + 2 cols: exact reduction P4 = q qY (adversary).
 F9 4x4: DC <= 3, row-centred <= 5 checked; n = 4 full (<= 5) unchecked.
KNOWN 7-DIM FAMILIES (all maximal by inclusion, E(L) = L + one rank-one mean direction, all with r + d = 7, min(r_A,r_B) + d = 3):
 L080 (7,0); ex1 (5,2) = rc45 + column; ex2, ex3 (6,1); 1-parameter s-family (7,0)/(6,1) at s = i sqrt 3; 4x2-block family (7,0).
DEAD ENDS
 Fermat/Kneser on 24/25/35/45 coordinates; P_2/P_3-only target (L9); growth dim(L + L o L) >= 2l-2 (no proof; nonassociative);
 Hessian-image counting (= first-order extension E(L), needs block exceptions); fixed-g relaxation (fails at block-supported g,
 undecidable numerically at generic g); symmetry (stabiliser of (P_2,P_3) is finite); natural torus degenerations (lose the bound);
 "4x5 level with all maximal minor permanents 0 has dim <= 4" is FALSE (rc45, dim 6, checked by hand here: all 3x3 subperms of
 its 3-row part vanish). LM negatives at n = 5 are unreliable (missed V(x)v, K, L9).
OPEN REDUCTIONS
 O1 (S): r_A + d <= 4 (needs DC <= 4, itself open).  O2 d = 1: r != 8 (numerically already from P_2,P_3; no proof).
 O3 Lemma Z rank 3, 4.  O4 block case of hessmix: (r,d) in {(6,>=3),(5,>=4),(4,>=5)}.  O5 4x5 rectangular coupling (lemmaz 4.4).
 Common obstacle: every method needs a separate treatment of block-supported (sparse) elements, and none of the methods
 distinguishes dim 9 from dim 8 by a pigeonhole.

STATUS 14:10: Theorems A, B, Lemma C proved and sanity-checked (chief/testAB.py); writing proofs; next: push the 9-dim configuration.

## 2. Proofs
(R0) perm(cJ + t) = c^5 perm(J + t/c) = 120 c^5 (c != 0); c = 0: perm(t) = P_5(t) = 0. Conversely clear. J not in L.
(ZBF) a permutation sigma with prod u_{i,sigma i} != 0 must send S into Z^c, |Z^c| = |S|, so sigma(S) = Z^c, sigma(S^c) = Z.
     Polynomial functions on a complex vector space U form a UFD and a nonzero linear form is irreducible.
(ThB) S = {r,r'}, Z = T^c. q(u) = u_rj u_r'l + u_rl u_r'j factors through pi: U -> C^4 = [rr';T]-block, ker pi = {u in L^: rows
     r,r' zero} = L_{rr'} (zero row => perm = 0 => ell = 0). ell|_U also factors through Pi. q_0(z) = z11 z22 + z12 z21 is a
     NONDEGENERATE quadratic form on C^4. If ell != 0 on U: q_0|_Pi = k ellbar^2, rank 1. If ell = 0 on U: q f = 0, so q_0|_Pi = 0
     or f = 0 on U (B2). A subspace Pi of a nondegenerate 4-dim quadratic space on which the form has rank <= 1 has
     dim Pi - 1 <= dim rad <= dim Pi^perp = 4 - dim Pi, so dim Pi <= 2.  dim U >= dim L^ - 6.
(LC) Let dim L = 9 and suppose dim L_{rr'} <= 1. Then dim pi_{rr'}(L) >= 8; as pi_r(L), pi_r'(L) miss 1 (FK) they are hyperplanes
     H_r = n_r^perp, H_r' = n_r'^perp (sum n_r = sum n_r' = 1) and pi_{rr'}(L) = H_r (+) H_r', dim L_{rr'} = 1. Pick j with
     (n_r)_j != 0, l with (n_r')_l != 0 and T containing j, l. v = e_j/(n_r)_j - 1 in H_r, v' = e_l/(n_r')_l - 1 in H_r', so some
     t in L has (t_r, t_r') = (v, v'): u = J + t in U_T with ell(u) = 1. By (ThB)(B1) dim U_T <= 1 + 2 = 3, but dim U_T >= 10 - 6 = 4.
     Contradiction. Columns: transpose (the transpose of a level space is level).
(ThA) Laplace along rows r, r': perm(J + t + s x) = sum_{j != l} (1+t_rj)(1+t_r'l) perm((J+t+sx)[abc; {j,l}^c]); the s^3-coefficient
     is (1+t_r)^T B_x (1+t_r') and must vanish. A bilinear pairing vanishing on the affine space (1,1) + pi_{rr'}(L) (which does not
     contain 0: rows r, r' of t both equal to -1 would give perm(J + t) = 0) vanishes as a quadratic form on its linear span.
     Remark: with psi(z) = (2x2 subpermanents q_T(z))_T in C^10 and phi(y) = (3x3 subpermanents f_T(y))_T, perm(u) = <psi(u_rr'), phi(u_abc)>,
     and ThA says span psi(pi_rr'(L^)) is orthogonal to span phi(L_{rr'}).

## 3. (N3) 3x3 level spaces have dim <= 3 by ZBF (shows the strength of the tool)
 Suppose dim L = 4, L^ 5-dim in C^9, perm_3 = 6 ell^3 on L^. Fix a cell (r,j). V = {u in L^: u_r in C e_j} has dim >= 3 and
 perm(u) = u_rj * q(u^(rj)) (q = 2x2 permanent of the minor). The map V -> C^4, u -> u^(rj), has kernel F^j := elements of L^
 supported in column j (they lie in L). Three cases: (i) ell != 0 on V: q = k ell^2 on the image, so the image has dim <= 2 and
 F^j != 0. (ii) ell = 0 and u_rj = 0 on V: V = L cap {row r = 0} is a 2x3 level space of dim >= 3, impossible (P_2 = x_1^T (J-I) x_2
 is nondegenerate of rank 5 on the hyperplane P_1 = 0 of C^6: dim <= 2). (iii) ell = 0 and q = 0 on the image: image dim <= 2, F^j != 0.
 So every column j carries a nonzero y^j e_j^T in L (sum y^j = 0), and by transposition every row r carries e_r (w^r)^T in L.
 Polarised P_2 between them: 2P_2(x,y) = <x,y> - R.R' - C.C' = y^j_r w^r_j = 0. Each y^j and each w^r has >= 2 nonzero entries
 (sum zero), so the cells {y^j_r != 0} (>= 6) and {w^r_j != 0} (>= 6) are disjoint subsets of 9 cells. Contradiction. QED
 (For general n the same count gives: dim L >= 2n-2 forces dim L_{rr'} >= 1 for every row pair with a (B1)-column pair -- the
 pigeonhole threshold of ZBF is exactly the conjectured maximum 2n-3 plus one.)

STATUS 14:16: Theorem G (duality/growth form, rho_2 <= 50, dim K_2 >= 5 at dim 9) proved + checked (chief/rho.py, k2.py, pairing.py).
(ThG) proof details: perm(u+v) = sum_k sum_{S,T} perm(u[S,T]) perm(v[S^c,T^c]) (expand each row of u+v); restrict to L^ and
 compare bidegrees. A_k(u) := (perm(u[S,T]))_{S,T} in C^(C(5,k)^2); the dot pairing between span A_k(L^) (dim rho_k) and
 span A_(5-k)(L^) has rank <= 1 (its values on spanning vectors are f(u) g(v)), so rho_k - 1 <= C(5,k)^2 - rho_(5-k).
 D_J perm(u[S,T]) = sum_{i in S, j in T} perm(u[S-i,T-j]); the map e_{S,T} -> sum e_{S-i,T-j} is W (x) W, W the 10x10 inclusion
 matrix of 2-subsets in 3-subsets of [5], invertible (Gottlieb). So Q_2 = D_J Q_3 as spaces of forms on L^ and rho_2 <= rho_3.
 K_2 in coordinates: sigma in S^2(L^), sigma^{ii'} := 5x5 block (rows i, i'); condition: for i != i' the off-diagonal part of
 sigma^{ii'} is antisymmetric. Squares v^2 lie in K_2 iff all 2x2 subpermanents of v vanish iff v is supported in one row, one
 column, or a 2x2 block with zero permanent.

STATUS 14:20: refined ThB (ThB') and the generic (1,1) row-pair analysis written below; no contradiction for dim 9 yet.

## 4. The forced configuration of a hypothetical 9-dim level space (all rigorous)
Notation: a_r := 5 - dim pi_r(L) >= 1 (rows), b_c likewise (columns); L_r := L cap {row r = 0} (dim 4 + a_r), X_{rr'} := L_{rr'}
(3-row level matrices, dim lam_{rr'}), I^ := pi_{rr'}(L^) (dim 10 - lam), Pi_T := I^ cap C^{2 x T}, U_T as in ThB.
 (C1) lam_{rr'} >= max(2, a_r + a_r' - 1) (LC + dim(L_r + L_r') <= 9); same for columns. dim L_{r,o} >= a_r + b_o - 1 + eps (cross).
 (C2) ThB': each column pair T is of exactly one type for the pair rr':
        B1: ell != 0 on U_T; then q_T = k ell^2 on Pi_T (dim Pi_T <= 2) and perm(u[abc;T^c]) = k' ell(u)^3 on U_T (k k' = 120);
        B2: U_T in L, perm(u[abc;T^c]) = 0 on U_T;      q0: U_T in L, q_T = 0 on Pi_T (dim Pi_T <= 2).
      Hence for x in X_{rr'}:  B_x[T] = perm(x[abc;T^c]) = 0 unless T is of type q0  (B_x lives on the q0-pairs only), and
      dim Pi_T >= 3 forces type B2.
 (C3) ThA: C(1,1)-extended projection I^ is isotropic for z_1^T B_x z_2; rank B_x <= lam_{rr'}.
 (C4) GENERIC ROW PAIR. If a_r = a_r' = 1 and lam_{rr'} = 2 then B_x = 0 for ALL x in X_{rr'}: X_{rr'} is a PLANE of 3-row level
      matrices all of whose 3x3 subpermanents vanish (rows l_a l_b l_c = 0 in C[y]/(y_j^2); the type of ex1's DC plane).
      Proof: if some C != 0 (symmetric, zero diagonal) has z_1^T C z_2 = 0 on I^ (codim 2), then rank C = 2, C = a b^T + b a^T with
      disjoint supports, and I^ is a maximal isotropic subspace of (z_1.a)(z_2.b) + (z_1.b)(z_2.a). Both row projections of I^ are
      onto, so I^ = {z_1.a = mu z_2.a, z_1.b = -mu z_2.b}, mu != 0; J_2 in I^ and n_r in span(a,b), sum n_r = 1 give (up to a <-> b)
      mu = 1, sum b = 0, n_r = a/sum(a) + beta b, n_r' = a/sum(a) - beta b. T inside supp(a): dim Pi_T = 3 and ell != 0 on Pi_T,
      contradicting B1; so a = a_0 e_j0. T inside supp(b) (exists as sum b = 0): dim Pi_T = 3, so ell = 0 on Pi_T, i.e. beta = 0.
      T = {j0, l}, l in supp(b): Pi_T = {z_1j0 = z_2j0, z_1l = -z_2l}, ell = z_1j0 != 0 but q_T = 0 on Pi_T: contradicts B1. QED
 (C5) ThG: dim K_2(L^) >= 5.
 (C6) FR (zeros): no free row/column, so every single-row / single-column space in L has dim <= 3.
 What a proof still needs: classify the planes of (C4) (3 linear forms in A_1 depending linearly on 2 parameters with product 0,
 plus P_1 = P_2 = 0) -- types: common zero row (plane of 2-row elements), support in 2 columns, ex1-type -- and play the ten
 row pairs and ten column pairs against each other with (C1)-(C6); and treat the non-generic pairs (a_r >= 2) the same way.
 I did not get further. The n = 4 analogue (L-gct-091: 4x4 level <= 5, unchecked in the project) is the right testbed:
 there ZBF gives at once, for dim L = 6: for all row pairs rr' and column pairs Z, L_{rr'} != 0 or L^{Z} != 0; hence (up to
 transpose) EVERY pair of rows carries a nonzero 2-row element of L; and every staircase order carries a nonzero triangular
 element u of L^ (6 conditions on a 7-dim space) with u_11 u_22 u_33 u_44 = 24 ell(u)^4.

STATUS 14:25: (C7) below: the generic row pair (a_r = a_r' = 1, lam = 2, annihilators without zeros) is IMPOSSIBLE (clean
 combinatorial contradiction); degenerate sub-cases remain. (C2) checked on all examples (chief/testC2.py: 980 values, 0 violations).
 (C7) GENERIC (1,1) PAIR WITH lam = 2 IS IMPOSSIBLE. Setting of (C4): kappa := n_r, kappa' := n_r' (FK annihilators of rows
      r, r'; sums 1), I^ = {z : <kappa,z_1> = <kappa',z_2>, <nu,z_1> + <nu',z_2> = 0}, ell(z) = <kappa,z_1>, and (kappa,nu),
      (kappa',nu') are pairs of independent vectors (both row projections of I^ are onto). For T = {j,l} put
      h_T = kappa_l e_j - kappa_j e_l, h'_T likewise, D_T = kappa_l kappa'_j + kappa_j kappa'_l, and p_j = (kappa_j,nu_j),
      p'_j = (kappa'_j,nu'_j) in C^2. Assume kappa|_T != 0 != kappa'|_T. Then Pi_T cap ker(ell) = {(mu h_T, mu' h'_T) :
      mu <nu,h_T> + mu' <nu',h'_T> = 0} and q_T(mu h_T, mu' h'_T) = -mu mu' D_T. If T is of type B1 then dim Pi_T = 2 (>= 4 - lam,
      <= 2), so the kernel is a line and must be q_T-isotropic:  D_T = 0  or  det(p_j,p_l) = 0  or  det(p'_j,p'_l) = 0.
      If T is not B1 then (n_r|_T,0) lies in the span of the two annihilators on T, which forces det(p_j,p_l) = det(p'_j,p'_l) = 0.
      So: EVERY pair {j,l} with D_T != 0 (and kappa|_T, kappa'|_T != 0) has p_j || p_l or p'_j || p'_l.
      If all kappa_j, kappa'_j != 0: rho := nu/kappa, rho' := nu'/kappa' are NON-constant functions on the 5 columns and every pair
      with omega_j + omega_l != 0 (omega := kappa'/kappa) is monochromatic for rho or for rho'. Two non-constant functions cannot
      make all pairs monochromatic (the pairs separated by rho form a connected complete multipartite graph, on which rho' would be
      constant). Hence: contradiction unless some pairs have omega_j + omega_l = 0 (kappa'_j/kappa_j = -kappa'_l/kappa_l) -- these
      exceptional pairs must cover every pair separated by both rho and rho'.   [rigorous; hand proof]
      So a 9-dim level space has NO row pair in "general position"; the surviving (1,1) pairs have lam >= 3, or zeros in n_r, n_r',
      or the sign relation above. Same for column pairs.

 (C7') SHARPER FORM (all kappa_j, kappa'_j != 0; sigma_j := rho_j + rho'_j, which is independent of the choice of (nu,nu')).
      Using the full rank-one statement of B1 (the kernel line z* must lie in the RADICAL of q_T on Pi_T, i.e. b(z*,z_0) = 0):
        pair monochromatic for rho only:     omega_j + omega_l != 0  and  omega_j sigma_j + omega_l sigma_l = 0;
        pair monochromatic for rho' only:    omega_j + omega_l != 0  and  omega_l sigma_j + omega_j sigma_l = 0;
        pair monochromatic for both:         sigma_j = sigma_l != 0, T is not B1 (so B2 if D_T != 0: the complementary 3x3
                                             permanent vanishes on the 4-dim space U_T inside L);
        pair separated by both:              omega_j + omega_l = 0 (and one more radical equation).
      plus sum kappa = 1, sum omega kappa = 1, sum kappa rho + sum kappa omega rho' = 0. Example of a surviving pattern:
      rho = (0,0,0,0,1), rho' = (a',a',a',b',a'): then omega_1 = omega_2 = omega_3, omega_5 = -omega_4, b' = -a'^2/(1+a') -- a
      positive-dimensional family, so the pair (r,r') alone is not contradictory; the cubic conditions (B1: perm_3 = k' ell^3 on
      U_T; B2) and the other pairs are needed.  [hand computation, not machine-checked]

## 5. Proposed END-TO-END architecture (what I would do with more time)  -- "sparsity cascade"
 Stage 1 [DONE, rigorous]: dim 9 => every two rows (columns) are killed by a plane of L (LC).
 Stage 2 [generic case DONE (C7), degenerate cases OPEN]: lam_{rr'} = 2 is impossible => lam_{rr'} >= 3 for all pairs. If all
          a_r = 1 this forces L_{rr'r''} != 0 for all triples (three 3-dim subspaces X_{rr'} of the 5-dim L_r meet pairwise):
          every pair of rows carries a 2-row element of L.
 Stage 3 [OPEN]: same analysis one level down (2-row elements x, coefficient forms: 2x2 subpermanents of x paired with 3x3
          subpermanents of the other three rows; ZBF families (3,2), (1,2,2), (2,1,2)) to force single-row elements.
 Stage 4 [DONE by zeros]: a full free row/column gives dim <= 8 (Lemma FR). Needs: the single-row space is 4-dim.
 Parallel constraint for every stage: ThG (dim K_2 >= 5) and ThA (rank B_x <= lam).
 Formalizability: R0, ZBF (Laplace expansion along a row set: needs a Lean lemma "perm of a matrix with a zero |S| x (n-|S|)
 block factors"; the UFD step can be replaced by the elementary lemma "if q f = c ell^5 on a vector space with q quadratic,
 ell linear nonzero, then q = k ell^2" or avoided by evaluating on lines), ThA, LC, N3: formalizable now (each < 300 lines
 given a permanent-Laplace lemma). ThG: formalizable (bilinear algebra + invertibility of a 10x10 inclusion matrix).
 C4/C7: formalizable but fiddly. Stages 2 (degenerate) and 3: mathematics missing.
 Risk: the cascade may stall at configurations that mimic the 7-dim examples (free row + block); those are exactly the cases
 covered by zeros' FR lemma and hessmix's block lemma, which is encouraging but not a proof.
Files: chief/core.py (exact example bases), testAB.py + testAB_lib.py (ThA, ThB), testC2.py (C2), rho.py, k2.py, pairing.py (ThG).
STATUS 14:28: C7' machine-checked on synthetic annihilator data (chief/c7check.py: rank q_T|Pi_T = 2 generically, = 1
 exactly under (R1)/(R1'), ell = 0 on Pi_T when both ratios agree).

STATUS 14:33: coordinator message (UPDATE 4) read. Section 6 = clean row-pair statements for agent "rows"; then continuing
 (extra 30 min allowed): trying to push the a_r = 1 case with ZBF.

## 6. FOR AGENT "rows": row-projection / row-pair statements for a 9-dim level space (all RIGOROUS, hand proofs in sections 2, 4)
Notation. L level, dim L = 9, L^ = CJ (+) L (dim 10), ell(cJ + t) = c, perm = 120 ell^5 on L^ (R0).
 pi_r(L) = row-r projection, a_r := 5 - dim pi_r(L) >= 1 (FK: 1 not in pi_r(L)); N_r := pi_r(L)^perp (dim a_r), it contains n with
 sum n = 1, and pi_r(L^)^perp = N_r cap 1^perp (dim a_r - 1). If a_r = 1: N_r = C kappa^r, sum kappa^r = 1, pi_r(L^) = C^5 and
 ell(u) = <kappa^r, u_r> for every u in L^.   L_r := L cap {row r = 0} (dim 4 + a_r),  X_{rr'} := L cap {rows r, r' = 0}.
 (RP1) dim X_{rr'} >= max(2, a_r + a_r' - 1) for every pair of rows; equivalently dim pi_{rr'}(L) <= 7 (Lemma C).
       So for a_r = 1: EVERY other row projection of the 5-dim space L_r has dim <= 3 (pi_r'(L_r) = L_r / X_{rr'}), and if also
       a_r' = 1 the two 4-dim row projections are NOT independent: L satisfies at least one relation <nu,t_r> + <nu',t_r'> = 0
       with nu not in C kappa^r, nu' not in C kappa^r'.
 (RP2) Trichotomy for a row pair (r,r') and a column pair T = {j,l} (ThB/C2). U_T := {u in L^ : u_r, u_r' supported in T},
       Pi_T := its image in the 2x2 block = U_T / X_{rr'}, q_T(z) = z_1j z_2l + z_1l z_2j, f_T(u) := perm(u[other 3 rows; T^c]).
         B1: some u in U_T has ell(u) != 0 (<=> some t in L has rows r, r' of J + t supported in T). Then q_T = k ell^2 on Pi_T,
             f_T = (120/k) ell^3 on U_T, dim Pi_T <= 2, and Pi_T cap ker(ell) (dim <= 1) is q_T-isotropic and q_T-orthogonal to Pi_T.
         B2: U_T inside L and f_T = 0 on U_T.         q0: U_T inside L and q_T = 0 on Pi_T (then dim Pi_T <= 2).
       dim Pi_T >= 3 forces B2. For x in X_{rr'}: perm(x[other 3 rows; T^c]) = 0 unless T is of type q0.
 (RP3) Affine isotropy (ThA): for x in X_{rr'}, (1 + t_r)^T B_x (1 + t_r') = 0 for all t in L, B_x[j,l] = perm(x[other rows; {j,l}^c]);
       dim pi_{rr'}(L) <= 9 - rank B_x.
 (RP4) (C4) a_r = a_r' = 1, dim X_{rr'} = 2  =>  ALL 3x3 subpermanents vanish on the plane X_{rr'}.
 (RP5) (C7/C7') a_r = a_r' = 1, dim X_{rr'} = 2, kappa := kappa^r, kappa' := kappa^r' without zero entries, (nu,nu') the extra
       relation of (RP1), rho := nu/kappa, rho' := nu'/kappa', omega := kappa'/kappa, sigma := rho + rho' (entrywise).
       Then rho, rho' are non-constant and for every column pair {j,l}:
         rho_j = rho_l, rho'_j != rho'_l  =>  omega_j + omega_l != 0 and omega_j sigma_j + omega_l sigma_l = 0;
         rho'_j = rho'_l, rho_j != rho_l  =>  omega_j + omega_l != 0 and omega_l sigma_j + omega_j sigma_l = 0;
         both equal                       =>  sigma_j = sigma_l != 0 and T is B2 or q0;
         both different                   =>  omega_j + omega_l = 0 and sigma_j = sigma_l.
       In particular "general position" is impossible, and the complete solution is TYPE I or TYPE II of (C7'') in section 4
       (two column blocks with <k_1,t_r> = c<k_1,t_r'> = -<k_2,t_r> = c<k_2,t_r'>, or an L-shaped 3-cell pattern).
       Mixed pair a_r = 2, a_r' = 1 with dim X_{rr'} = 2: TYPE I' of (C8): pi_r(L)^perp = span(k'_1,k'_2), kappa^r' = k'_1 + k'_2.
 (RP6) SINGLE ROW WITH a_r = 1 (generalises zeros' reduction for a free row; trivial from R0 + Laplace along row r).
       Write u in L^ as (u_r ; u') with u' the other four rows, G(y) := (perm_4(y minus column j))_j for a 4x5 matrix y, so
       perm(u) = <u_r, G(u')>. Because pi_r(L^) = C^5 there is a linear map T : C^5 -> C^{4x5} / L_r (L_r viewed as 4x5 matrices)
       with L^ = {(v ; T(v) + xi) : v in C^5, xi in L_r}, T(1) = J_{4x5}, and
            <v, G(T(v) + xi)> = 120 <kappa^r, v>^5      for all v in C^5, xi in L_r.                         (**)
       v = e_j:  perm_4((T(e_j) + xi) minus column j) = 120 (kappa^r_j)^5 for all xi in L_r: every column deletion of the 5-dim
       space L_r is "level relative to the base point T(e_j)^(j)" (or has perm_4 = 0 on a 6-dim space when kappa^r_j = 0).
       Free row r is the special case T(v) = <kappa,v> J_{4x5}, kappa = 1/5 (then (**) says L_r is strongly level, Lemma SL).
       v = alpha e_j + beta e_l in (**) gives the coupling between the deletions j and l (coefficients of alpha^a beta^b).
 (RP7) Dictionary to repr's "deletable row r": with u = (u_r ; u'), perm(u) = <u_r, G(u')>:
         row r deletable  <=>  <1, G(u')> = 120 ell(u)^4 for all u in L^   (replace row r of u by ell(u) 1).
       LEMMA DS (deletable + zeros' Lemma SL; rigorous given SL). If row r of a level space L is deletable then
         (i) for every xi in L_r the vector g(xi) := (perm_4(J_4 + xi^(j)))_j of deletion permanents lies in pi_r(L)^perp = N_r
             (proof: perm(J + t) = <1 + t_r, G(J' + t')> = 120 and deletability <1, G(J' + t')> = 120 give <t_r, G(J' + t')> = 0
             on L; apply it to s t + xi and let s -> 0), and g(0) = 24*1, so 1 is in N_r: all row-r sums vanish on L;
         (ii) if moreover dim pi_r(L) = 4 (a_r = 1) then N_r = C 1, g = 24*1 on L_r, i.e. L_r is STRONGLY LEVEL, hence
              dim L_r <= 3 (Lemma SL) and dim L <= 4 + 3 = 7.
       So repr's conjecture (D) settles every space whose deletable line has a full (4-dim) projection; (D) + "deletable line with
       a_r >= 2 => dim L_r <= 3 + a_r" would give the gap. (A free row is the case pi_r(L) = 1^perp.)
       Caution: a_r = 1 does NOT imply deletable (L080, row 4: kappa = (1,1,1,1,0)/4).
 (RP9) Inside X := L_r when a_r = 1 (all five 4x4 deletion permanents vanish on X, and dim pi_i(X) <= 3 for the other rows i):
       for a row i != r and a column j, Y := {xi in X : xi_i in C e_j} (dim >= 2) has either xi_ij = 0 on Y (Y = X_{ri}) or ALL
       3x3 subpermanents of the 3x4 matrix xi[rows != r,i ; columns != j] vanish on Y; for a column pair {j,k},
       Y' := {xi in X : xi_i supported in {j,k}} has xi_i = 0 on Y' or perm(xi[rows != r,i ; columns != j,k]) = 0 on Y'.
       (Factorisation of the vanishing deletion permanents + irreducibility of a linear space.)
 (RP8) ThG: at dim 9 the 100 quadrics "2x2 subpermanents" restricted to L^ span at most 50 of the 55 dimensions.
 What I could NOT do: exclude a_r = 1. The cheapest missing statement: a 5-dim space L_r of 4x5 matrices with (**) for some T.
STATUS 14:34: Lemma DS (deletable row with 4-dim projection => L_r strongly level => dim <= 7) and RP9 added to section 6.
STATUS 14:37: (C7'') complete classification of the annihilator data of a (1,1) row pair with lam = 2 and no zero entries:
 only two rigid types survive ThB (verified on synthetic data, chief/c7types.py). Lemma DS checked on all examples (chief/ds.py:
 each 7-dim example has exactly one deletable line, its projection is 4-dim, dim L_r = 3, g = 24).
 (C7'') [rigorous, hand proof; correction of the last line of C7': a pair separated by both rho and rho' needs omega_j + omega_l = 0
      AND sigma_j = sigma_l]. Setting of (RP5). "sigma_j = sigma_l" holds exactly for the pairs that are equal in both or separated
      in both, so it is an equivalence relation; inside a sigma-class distinct points (rho_j,rho'_j) are pairwise separated in both
      coordinates and need omega_j = -omega_l, so a class has at most 2 distinct points; points of different classes must share
      a coordinate. Plane combinatorics (points on anti-diagonals x + y = const, at most 2 per anti-diagonal, points on different
      anti-diagonals on a common horizontal or vertical line, both coordinates non-constant) leaves exactly:
        TYPE I  : two points on one anti-diagonal: sigma = sigma_0 != 0 constant, columns = C_1 + C_2, omega = c on C_1, -c on
                  C_2, c = 1/(K_1 - K_2) (K_i = sum of kappa over C_i), sigma_0 = -K_2 (1 + c) (rho = 0 on C_1, 1 on C_2).
                  Equivalently, with kappa = kappa_1 + kappa_2 split along C_1, C_2: on L
                     <kappa_1, t_r> = c <kappa_1, t_r'> = -<kappa_2, t_r> = c <kappa_2, t_r'>.
                  Pairs inside C_1 or inside C_2 are of type B2 (the complementary 3x3 permanent vanishes on a 4-dim U_T in L and
                  L contains elements with (row r, row r') = (h_T, 0) and (0, h_T), h_T = kappa_l e_j - kappa_j e_l);
                  pairs across are B1.
        TYPE II : an L-shape (x,y), (x,y'), (x',y) with x + y' = x' + y: omega = c on the cell (x,y'), -c on (x',y),
                  -+ i c on the corner cell, sigma(x,y') = +- i sigma(x,y), plus one global linear relation on kappa.
      So a (1,1) row pair with dim X_{rr'} = 2 and kappa, kappa' without zeros is of Type I or II. Not yet excluded: these types
      (need the B2 cubic conditions and (C4)), zero entries in kappa or kappa', and dim X_{rr'} >= 3.
STATUS 14:39: (C8) the mixed pair a_r = 2, a_r' = 1 with dim X_{rr'} = 2 is classified too (Type I', chief/c7typeIp.py).
 (C8) ROW PAIR WITH a_r = 2, a_r' = 1, dim X_{rr'} = 2 (the minimum allowed by (RP1)) [rigorous, hand proof].
      pi_r(L^)^perp = C n (sum n = 0), kappa* in N_r with sum 1 (mod n), kappa' = kappa^r'; I^perp = span{(n,0),(kappa*,-kappa')},
      pi_{rr'}(L) = pi_r(L) (+) pi_r'(L), ell = <kappa',z_2> = <kappa*,z_1>. For T = {j,l} with n|_T != 0 != kappa'|_T:
      Pi_T = {(mu h^, z_2): <kappa',z_2> = mu theta_T}, h^ = n_l e_j - n_j e_l, theta_T = kappa*_j n_l - kappa*_l n_j; T is B1 iff
      theta_T != 0, and then (radical condition) n_l kappa'_j + n_j kappa'_l = 0. If n and kappa' have no zero entries: with
      y = kappa*/n (non-constant) and x = n/kappa', every pair has y_j = y_l or x_j + x_l = 0; three y-classes are impossible, so
        TYPE I': columns = C_1 + C_2, kappa' = kappa'_1 + kappa'_2 with sum kappa'_1 = sum kappa'_2 = 1/2, and
                 pi_r(L)^perp = span(kappa'_1, kappa'_2):  <kappa'_1,t_r> = <kappa'_2,t_r> = 0 and <kappa'_1 + kappa'_2, t_r'> = 0 on L
                 (on L^: ell(u) = <kappa',u_r'> = 2<kappa'_1,u_r> = 2<kappa'_2,u_r>). Pairs inside C_1 or C_2 are B2.
      For pairs with a_r, a_r' >= 2 and dim X_{rr'} = 3 (the minimum), ThB gives only open conditions (dim Pi_T can be 1).
 PATTERN: every surviving minimal row pair (Types I, I', and the 7-dim examples: ex1 rows 0-2 have N_i = span(e_0+e_1, e_2+e_3))
 shows a TWO-BLOCK column structure with weighted block-sum relations on the rows -- the block structure that hessmix's and
 zeros' lemmas need. Conjectural structure theorem suggested by this: in a level space of dim >= 8 the FK annihilators of the
 rows are sums of a common family of disjointly supported column-block vectors.

## 7. Adjustment after rows' 14:41 result (7-dim level spaces WITHOUT a full free line exist; "defect construction")
 rows' L(L') = L' (+) e_r (x) W is exactly the DECOUPLED case of (RP6): the single-row space W_r equals the whole row projection
 pi_r(L) (then T(v) = <kappa*,v> J' and (**) reads G(cJ' + Y) in W^perp, <1,G> = 120 c^4, i.e. Lemma DS (i)). Consequences for
 my section 5: the cascade cannot be expected to end in a FULL free line (conjecture "F" is false); the right endpoint is
 "deletable line + defect bound": gap <= (D) + [4x5 level L' => dim L' <= 4 + dim C(L')]  (Lemma SL is the case defect 0).
 What my tools say inside the decoupled class at dim 9 (L = L' (+) e_r (x) W, f_r = dim W <= 3 by FL, so dim L' >= 6):
  - (RP1) for the pairs (r,r'): {Y in L' : row r' of Y = 0} has dim >= max(2, a_r + a_r' - 1) >= a_r' + 1 for every other row r';
  - ThA with x = e_r w^T: G(u') is orthogonal to W for all u in L^ (first-order condition, = rows' "rho-part orthogonal to p_k");
  - ZBF with row r: e_j lies in C1 + W iff 5 e_j - 1 lies in W iff C(L') is orthogonal to e_j; then the j-th deletion of L' is
    level (perm_4(J_4 + Y^(j)) = 24). ThB for the pairs (r,r'): not worked out.
  - trivial count in this class: r_A(L) = q := dim(row-sum image of L') <= 3, p_1(Y) = -(column sums of Y) lies in C(L'), so
    dim L' <= q + defect + dim(L' cap DC): the defect inequality can only fail if dim(L' cap DC) >= 2.
  - (C8) applies verbatim when a_r = 2 (f_r = 3, defect 1) and a_r' = 1, dim X_{rr'} = 2: then W^perp = span(k'_1, k'_2) with
    kappa^r' = k'_1 + k'_2 split along two column blocks -- a testable prediction on rows' (dim L', defect) = (6,1) candidates.
STATUS 14:44: final report sent. Scripts: chief/{core,testAB,testAB_lib,testC2,rho,k2,pairing,c7check,c7types,c7typeIp,ds}.py.
