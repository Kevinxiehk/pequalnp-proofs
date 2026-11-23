# NOTES-proof (role: proof, started 11:19)

STATUS (11:33): NO proof found; no RESULT section. Useful by-products: exact reformulations (1)-(4),
a doubly centred level space of dim n-2 for every n (tight at n=3 by L_gct_109), and five routes
ruled out with reasons (A-E). Scripts: proof/chk.py, proof/initial.py.

No complete proof found (see log). Facts below are checked numerically (proof/chk.py, n=5).

## Reformulations (all exact; verified numerically)
1. Doubly centred (DC) t: inclusion-exclusion kills every index used once, so P_k(t) is a
   UNIVERSAL (n-independent) combination of "tensor-network" contractions of t over bipartite
   multigraphs with all vertex degrees >= 2, vertex weight (-1)^(d-1)(d-1)!, over k!.
   P_2 = (1/2) sum t_ij^2,  P_3 = (2/3) sum t_ij^3,
   P_4 = (3/2)p_4 - (3/4)(sum_i r_i^2 + sum_j c_j^2) + p_2^2/8 + (1/4) tr((t t^T)^2),
   where p_k = sum t_ij^k, r_i = sum_j t_ij^2, c_j = sum_i t_ij^2.  (checked)
2. G_t(y) := sum_k P_k(t) y^k. Level <=> G_t == 1 (perm(J+xt) is the Laplace/Borel transform
   of G_t: (n-k)! = int u^(n-k) e^-u). By the exponential formula log G_t = sum_k c_k(t) y^k with
   c_k = sum over CONNECTED multigraphs; c_k = ((k-1)!/k) p_k + (graphs with >= 3 vertices).
   Level <=> c_k(t) = 0 for ALL k >= 1 (equivalently k <= n). G is multiplicative under
   block-diagonal sums (=> L1 (+) L2 level; same as infra's L_gct_110 gluing).
3. Gaussian/Fischer form (by Wick's theorem; valid for ALL t, z standard complex Gaussian on C^n):
   P_k(t) = E[ e_k(t z) * conj(e_k(z)) ],  so  Level <=> E[ prod_i (1+(tz)_i) * prod_j (1+conj z_j) ] = 1
   for all t in L.  For DC t one may take w Gaussian on V = 1^perp = C^(n-1) (DC matrices = End(V)):
   i.e. P_k(t) = <E_k, Sym^k(t) E_k> where E_k = e_k|_V are the fundamental invariants of
   S_n acting on its reflection rep. (derivation: perm(A)=E[prod_i (Az)_i prod_j conj z_j],
   split z = (s/n)1 + w.)  So: L subset End(V) with <E_k, (t_1 . ... . t_k) E_k> = 0 (k=2..n).
   The k=2 case is the isotropy bound; any proof must use E_k for k ~ n.

## New explicit DC level space (checked): dim n-2
   u = (1, w, w^2, ..., w^(n-1)), w = primitive n-th root of 1;  L = { u v^T : sum v = 0, v_n = 0 }.
   P_k(u v^T) = k! e_k(u) e_k(v); e_k(u)=0 for k<n, e_n(v)=0 since v_n=0. Row/col sums 0.
   (u(x)W + W(x)u and u(x)W + W(x)conj(u) are NOT level: checked.)
   Power sums p_k(t) = p_k(u)p_k(v) vanish for k<n but NOT k=n.

## Log of directions

4. "Avoid the zero set": L is level <=> perm(J+t) != 0 for every t in L (a polynomial with no zero
   on C^d is constant). <=> perm restricted to the projective span P(CJ + L) equals s^n.
   Consequence (transversality test): for every affine Y inside {perm = 0}, J+L misses Y, so
   L + Y_lin != C^(n^2) whenever J - y0 in L + Y_lin would follow; in particular if L + Y_lin is
   everything we get a contradiction. Determinant analogue = affine spaces of nonsingular matrices
   (max n(n-1)/2, attained at I); for perm the base point matters (perm at I also allows
   I + strictly upper triangular, dim n(n-1)/2), so a proof must use that the base point is J.
   DEAD (as a full route): using only Frobenius-Koenig zero blocks Z_{A,B} (|A|+|B| = n+1) as the
   Y's: J + (strictly upper triangular) meets none of them (a zero block would need max A < min B,
   so |A|+|B| <= n), yet that space has dim n(n-1)/2.  So zero-pattern obstructions alone cannot
   give anything subquadratic; need non-combinatorial linear spaces in {perm=0}.
   Small free consequence: 2x2 blocks [[a,b],[c,d]] with alpha a = beta b, beta d = -alpha c are
   planes in {ad+bc=0}; putting rows i,i' inside columns j,j' with such a block gives a linear Y in
   {perm=0}; for DC L this forces dim(projection of L to any two rows) <= 2n-3. Weak.

## Log of directions (what failed and why)
A. Power sums. Leading term of c_k is ((k-1)!/k) p_k, p_k = sum t_ij^k. If c_k were just p_k, the
   lemma "N linear forms on C^d spanning, with p_1..p_m = 0  =>  N >= m d + 1" (tight: points
   (z^j, z^{2j}, ..., z^{dj}), z primitive (md+1)-th root; I did NOT prove the lemma; true for
   d=1 (Vandermonde) and m<=2 (isotropy)) with N = n^2, m = n would give d < n. FAILS as stated:
   p_k is NOT forced to vanish on DC level spaces (u(x)W above has p_n != 0; block sums of 3x3
   copies have p_3 != 0), the >=3-vertex graph terms of c_k (e.g. sum_i r_i^2, tr((tt^T)^2)) are
   genuinely present. Heuristic still useful: eigenspace construction (L_gct_119) with z of order
   m+1 gives P_1..P_m = 0 with dim ~ n^2/(m+1), matching "order m => n^2/m". A proof would need a
   quantitative "order m => dim <= n^2/m + O(n)" statement; I found no handle on the graph terms.
B. Induction on n by deleting a row and column: L cap {row i = 0, col j = 0} IS exactly level
   for n-1 (P_k unchanged), but the loss is the rank of (row i, col j) on L, which is >= d/n on
   average, so only D(n) <= D(n-1) + 2n - 1 (quadratic). Minors t^(ij) of level t are NOT level
   (u(x)W: e_k(u minus one root) != 0), and d/dt_ij perm(J+t) = perm(J'+t^(ij)) only reproduces
   polarizations of the P_k (= the gradient-span bound L083, already checked). No O(1)-loss
   reduction found; it would need a row/column of bounded rank on L, which large spread-out
   spaces need not have.
C. Positivity (van der Waerden/Bregman/real points): any real DC level space is 0 (P_2 = sum
   t^2/2 > 0), so the extremal objects are genuinely complex (L cap conj L cap DC = 0), and
   positivity bounds only reproduce the isotropy bound (n-1)^2/2. The Gaussian form (3) is a
   Hermitian pairing but the level conditions are holomorphic in t, so Cauchy-Schwarz gives
   nothing linear. Dead as far as I can see.
D. Rank-one / Binet-Cauchy (L099): t = U W^T with U fixed needs prod_i (1 + l_i(z)) = 1 + prod l_i
   (k < n parts vanish), which forces all rows l_i of U proportional (Newton: l_i(z) are the n-th
   roots of one function) -> only the rank-one family u(x)W. Bounded, nothing superlinear there.
E. Groebner/torus degeneration (initial forms). P_k is in the linear ideal I(L), so for any weight
   w, in_w(P_k) lies in in_w(I(L)) = I(L_w), L_w a flat limit of dimension d. Generic w:
   in_w(P_k) = monomial of the max-weight k-matching, in_w(I(L)) = variables outside the
   min-weight basis F(w) of the coordinate matroid of L; criterion "max k-matching not inside
   F(w)". DEAD: proof/initial.py (n=3,4,5, 300 random w, all k): the FULL DC space (cographic
   matroid of K_{n,n}, F = complement of a max spanning tree, dim (n-1)^2, not level) never
   violates it. Rank-one weights w_ij = a_i + b_j (= limits under diagonal scaling D1 L D2) give
   only "leading principal k x k permanents vanish on the limit", satisfied by strictly upper
   triangular (quadratic). So single-P_k initial terms cannot see the bound.
F. Dimension count heuristic: d-planes in V = {P_1=...=P_n=0} (codim n) have expected
   dimension d(n^2-d) - sum_k C(d+k-1,k) < 0 already for d = 3 and n > ~18, so every level space
   of dim >= 3 is "special"; known ones come from cyclic/root-of-unity symmetry (L_gct_119
   eigenspaces, u(x)W, row+column 2n-3). No proof route from this.

G. Power-sum lemma (model case only): with g of degree <= m, sum_i g(l_i) = N g(0). Taking
   g = q * prod_c (1 - phi/c) over the distinct values c of phi off a hyperplane H = ker phi shows:
   every hyperplane through 0 misses points with >= m+1 distinct phi-values. Gives N >= m+1+...,
   not yet md+1 (d=2,m=2 needs isotropy). Unfinished; only relevant if graph terms can be handled.

## Most promising next step (my view)
Prove the quantitative bounded-order statement  D_m(n) := max dim of DC spaces with
P_2 = ... = P_m = 0  satisfies  D_m(n) <= n^2/m + O(n)  (eigenspaces of z of order m+1 give
~n^2/(m+1), so this would be tight up to O(n)); with m = n it gives the gap. First milestone:
the pure power-sum lemma (N forms with p_1..p_m = 0 span <= (N-1)/m dims), then show the
>=3-vertex graph terms of c_k can be absorbed (e.g. by an induction on m using c_m = 0 together
with the already-established structure from c_2..c_{m-1}).
