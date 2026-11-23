# NOTES-construct (role: construct)  — no RESULT (no superlinear family found)

## SUMMARY [11:39]
No refutation. Every structured family I could build (block sums, root-of-unity column groups,
row+column covers, shared-row gluing, Kronecker with [[1,-1],[-1,1]]) gives at most ~2 dims per
line. All known lower bounds fit ONE formula: LS(a,q) = a+q-3 for a,q >= 2 (LS(1,q) = q-1):
LS(2,q)=q-1 (checked), LS(3,3)=3 (checked), LS(3,q) in [q, q+1] (UB checked L156), LS(4,4)>=5 (row-centred <=5 checked), LS(4,5)>=6, LS(4,6)>=7, LS(5,5)>=7, and
the rectangular row+column construction gives a+q-3 in general. Numerics (below) found no space
one dimension above it. Suggested sharp target: LS(a,q) <= a+q-3, i.e. LS(n) = 2n-3; the
rectangular version is the natural induction hypothesis (delete a row / a column; L_gct_110
gluing shows rectangular blocks are unavoidable anyway).

## 1. Exact algebraic reformulation for rectangular blocks (useful for both sides)
For an a x c matrix t with columns u_j in C^a put l_j = sum_i u_j(i) x_i in
A = C[x_1..x_a]/(x_1^2,..,x_a^2) and eps(f) = sum of all coefficients of f.  Then
   sum_k M_k(t) z^k = eps( prod_j (1 + z l_j) )      (columns used once = product over j,
                                                      rows used once = x_i^2 = 0).
log prod_j(1+l_j) = sum_B c_B m_B(t) x^B, c_B = (-1)^{|B|-1}(|B|-1)!, m_B = sum_j prod_{i in B} t_ij
(squarefree row moments), so M_k is a fixed polynomial in the 2^a - 1 moments, and the moment
vector is ADDITIVE over column-disjoint pieces that share rows.
GLUING-WITH-SHARED-ROWS LEMMA (easy, exact): let W ⊂ A_+ be a graded subalgebra with eps(W)=0.
If L_1,..,L_g are spaces of a x c_b matrices (disjoint column sets, SAME rows) with
prod_{j in block b}(1+l_j) ∈ 1+W for all t in L_b, then L_1 ⊕..⊕ L_g is a level space.
(1+W is a multiplicative group.)  W=0 is "all squarefree row moments vanish", which by
L098/L090-type chain bounds gives <= c_b - 1 per block, i.e. ratio < 1.  Nonzero W exist, e.g.
W = (x1-x2)U ⊕ x1x2·U·U with U ⊂ C[x3..xa]/(x^2) isotropic for beta(f,g)=eps(fg)
(beta = ⊗ [[1,1],[1,0]], nondegenerate, so isotropic U up to dim 2^{a-3}); but the GRADED
requirement (forced, since t -> s t acts by x -> s x) kills most of it: for a=3 the only graded
choice is W = span((x1-x2)x3), i.e. m_1=m_2=m_3=m_12=m_123=0, m_13 = -m_23: barely weaker than W=0.
So this route does not give ratio > 1 per column; I did not find a graded eps-null W that lets a
block of s columns carry more than ~s dimensions.

## 2. Families tried (all exact/elementary), dimension vs lines (rows+cols)
- Block diagonal / disconnected support: matching polynomial factorises over components, so
  LS is superadditive: LS(n) >= sum LS(a_i,b_i) (= L_gct_110). Hence LS(n)/n -> sup; a
  refutation needs LS(a,c)/(a+c) unbounded for some rectangular family. Square blocks of
  2k-3 give < 2n.
- Any support with matching number nu has <= nu*n edges (König), so a superlinear family needs
  vertex covers (a rows + b cols) with a+b -> infinity; all M_1..M_{a+b} are then active.
- Roots-of-unity groups (exact): columns in groups of s >= w+1, column (g,l) = zeta_s^l y_g with
  y_g in C^{W_g}, |W_g| = w: all m_B vanish (|B| <= w < s), so level. dim = n*w/(w+1) < n.
- 3 x c: columns (a_j, w a_j, w^2 a_j)·(sign pattern) with w^2+w+1=0 kills M_2's form
  a^2+ab+b^2; then M_3 needs p_3(a)=0 on the space: a = (x1,-x1,x2,-x2,..) works, dim c/2.
  (Checked bound LS(3,q) <= q+1 says nothing much better exists.)
- a rows + b columns cover, t = [[0,Y],[X,Z]]: if X (a x (n-b)) and Y have all moments zero they
  contribute <= (n-b-1)+(n-a-1) (L098), Z adds LS(a,b): linear. Nonzero moments in X,Y must be
  compensated through Z, which only has ab entries -> I see no way to get more than O(n).
- One free sum-zero row + rest: the free row forces, for every grade k, the (a-1) x (c-1)
  "column j deleted" matching sums of the other rows to be independent of j. Two free rows are
  impossible (cross term -<t1,t2> in M_2). Gives c-1 + (small), consistent with 4x6 dim 7.
- Determinant-style triangular patterns: strictly upper triangular t is NOT level (M_1 = sum of
  entries, and M_k = weighted rook numbers of the staircase board, all nonzero generically);
  after centring, M_2 = (1/2) sum t^2 is a nondegenerate form, so at most half survives; the
  higher M_k (rook sums on the staircase) have no cancellation analogous to det's block-triangular
  multiplicativity. Dead.

## 3. Numerics (construct/numsearch.py: LM on a Grassmannian chart, residuals = M_k at
## 1.1*#monomials random points; cost ~1e-30 = exists)
- 2x4: d=3 found (cost 4e-30), d=4 not (cost >= 3.6): matches LS(2,4)=3.
- 3x5: d=6 not found (cost 5.1, 3 starts), d=7 not found; d=5 not found in 2 starts (cost 1e-4,
  probably slow convergence / degenerate; inconclusive).
- 4x6 d=8: first start cost 98.5 (not found; 2nd start cut by 150 s timeout). Consistent with LS(4,6)=7 (L_gct_198 LB), weak evidence only.

## 3b. Root-of-unity column groups, exact identity (spot-checked, construct/rootgroups.py)
a x (N*G) matrix, column group g = (zeta^l u_g)_{l<N}, zeta primitive N-th root, N > a/2:
   sum_k M_k z^k = 1 - (-1)^N N! z^N sum_g e_N(u_g)
(proof: prod_l (1+zeta^l l_g) = 1-(-l_g)^N, and (l_g^N)(l_h^N) has degree 2N > a, so 0 in A).
So level <=> sum_g e_N(u_g) = 0 on L. Best I get: pair groups u_h = xi u_g (xi^N = -1) ->
a dims per 2N > a columns (ratio < 1 per column); or u_g in a linear space inside {e_N=0}
(e.g. e_3 on C^4 = Cayley cubic, max 2-dim). For 2N <= a cross terms appear (checked
numerically: a=4,N=2 gives M_4 != 0); iterating groups-of-groups just gives order NM groups.
Kronecker t = [[U,-U],[-U,U]]: odd M_k vanish, M_2 = 2 sum U_ij^2, but M_4 is NOT a multiple
of sum perm(U[R,C])^2 (checked, construct/kron.py); no clean reduction, dropped.

## 3c. Numeric calibration (numsearch.py, LM, 2-3 random starts each)
found (cost ~1e-23..1e-30): 2x4 d=3, 4x5 d=6.   slow/inconclusive: 3x5 d=5 (1e-4), 3x6 d=6 (2e-3)
(both exist by the a+q-3 construction, so the optimizer is not reliable near degenerate spaces).
not found: 2x4 d=4, 3x5 d=6, 3x5 d=7, 3x6 d=7 (cost 5.7), 4x5 d=7 (cost 56), 4x6 d=8 (cost 98..150).
Weak evidence only, but no space above a+q-3 was found anywhere.

## 4. Large eps-null graded subalgebra (exact) and what it would need  [11:46]
W_half = ⊕_{k > a/2} ker(eps_k) ⊂ A is a graded subalgebra with eps(W)=0 (products of two
elements have degree > a, hence 0). So by §1: column blocks sharing all a rows glue freely as soon
as each block has (i) all squarefree row moments m_B with |B| <= a/2 equal to 0 and (ii) its own
M_k = 0 for k > a/2. A refutation along these lines needs a block of s columns of dimension
>> s satisfying (i)+(ii). (i) already contains: rows pairwise bilinear-orthogonal and sum-zero
for every t, i.e. L is a common isotropic space of the pencil Λ⊗I_s (Λ symmetric, zero diagonal),
which only gives dim <= a s/2 a priori; tensor-type L = U⊗C^s forces dim U = 1, and Clifford-type
(t_i = A_i y, A_i antisymmetric anticommuting) gives exactly s. I found no block beating s.
OPEN SUB-QUESTION worth one more look: max dim of an a x s space with m_B = 0 for all
1 <= |B| <= a/2 (no condition on higher moments). If it is >> s for large a, combine with §1
(plus fixing (ii) on a large block) to get a superlinear family; if it is <= s + O(a), the
shared-row gluing route is dead.
