# NOTES-smallcases (role: smallcases)

## Checked statements in the project (read from Lean, read-only)
- L-gct-080 (Gct/L080.lean, helper Gct/Helpers/LevelLow.lean): for every n >= 2 a level space of
  dim 2n-3 exists. Explicit: t supported on last row and last column; last row off the corner =
  (x_1..x_{n-2}, -sum x) (sums to 0), last column off corner = y_1..y_{n-1} free, corner = -sum y.
  (Proof: bordered expansion; any partial permutation inside the support has size <= 2.)
- L-gct-094 (Gct/L094.lean, Helpers/LevelThree.lean): n=3, every level space has dim <= 3 = 2n-3
  (tight). Route: Fourier coords for cyclic shifts, entry-sum-zero 3x3 matrices = 8 coords,
  perm(J+t) = 6 + 3 c6, quadratic part = 4 hyperbolic pairs, isotropic => graph over a chart,
  cubic gives unit ideal in each of 16 charts.
- L-gct-090 (Gct/L090.lean): subspaces S_1..S_n of C^n all of whose nonempty column product sums
  vanish (sum_i prod_{j in A} s_j(i) = 0) have total dim <= n-1.
- L-gct-092 (Gct/L092.lean): if doubly centred level spaces have dim <= G then all level spaces
  have dim <= G + 2n (rank-nullity on row/col sums).
- Related Outside/: L_gct_109: n=3 doubly centred level => dim <= 1. L_gct_216: n=4 doubly
  centred with P_2=P_3=P_4=0 => dim <= 3. L_gct_123: column-structured level spaces
  (t_{.,j} in S_j for each column independently) have sum dim S_j <= n-1. L_gct_114: row part +
  column part spaces bounded. L_gct_119: if t(sigma i, tau j) = z t(i,j) with z^k != 1 for
  k<=n then t is level (weight-vector construction). L_gct_120/121: rank-one facts.

## Tools (in smallcases/)
- level.py: Pk(T), Pk_grad(T) (Ryser in s: (n-k)! P_k = (-1)^n sum_S (-1)^|S| |S|^(n-k) e_k(u(S)),
  u(S)_i = sum_{j in S} T_ij), exact Pk_exact and check_exact(basis,n) (certifies P_k == 0 on the
  span by evaluating on all a in N^d, |a| = k: unisolvent for degree-k forms), check_numeric.
- search.py n d full|dc starts maxit seed: complex Levenberg-Marquardt on Grassmannian chart.
- tangent.py: ext_space_dim(L) = dim{t : DP_k(l)[t]=0 all l in L, all k} (contains every
  level L' >= L); weight_space(n,sigma,tau,N,E).  extend.py: LM extension of a fixed space.

## Findings (all light runs, < 2 min each)
1. 2n-3 construction certified EXACTLY (integer basis, all P_k, k=1..n) for n=3,4,5,6.
2. It is maximal by inclusion: first-order extension space has dim 2n-2 for n=3..6; the one extra
   direction is (mod L) the rank-one matrix 1 * w^T, w = (-1,...,-1, n-1)/(n-1) (all rows equal,
   row sum 0); adding it breaks P_2 (and P_3..). So no level space contains the 2n-3 one.
3. Weight (torus) construction, generalising L_gct_119: g=(sigma,tau) of order N, E subset of
   Z/N with no zero sum of k<=n terms (e.g. E inside (0,N/n)); sum of z^e eigenspaces is level.
   Gives DOUBLY CENTRED level spaces (checked numerically to 1e-13, also follows from invariance):
     n=4: sigma=4-cycle, tau=3-cycle+fixed pt, N=12, E={1,2}: dim 2
     n=5: sigma=5-cycle, tau=(3)(2), N=30, E={2,3,4}: dim 3
     n=6: sigma=6-cycle, tau=5-cycle+fixed, N=30, E={1,2,3,4}: dim 4
   Counting bound for this family: an orbit of length l contributes only characters of order
   dividing l that are zero-sum-free up to length n, ~ (l-1)/n of them; sum of l over orbits is
   n^2, so ANY abelian weight construction has dim < n. Symmetry constructions are linear.
4. LM random search: n=4 full ambient: dim 5 found (res 2e-10), dim 6 NOT found (30 starts, best
   res 0.40). n=4 dc: dim 2 found (quadratic convergence), dim 3 not found (20 starts) -- the
   project's L_gct_216 bound is 3; evidence that the dc max at n=4 is 2 = weight construction.
   n=5 dc: dim 2 found by random LM, dim 3 not (but the weight construction gives 3: random LM is
   weak at n=5). n=5 full: random LM failed even for dim 7 (known to exist) -> unstructured
   search is useless beyond n=4.
5. Seeded extension: the n=4 dc weight space (dim 2) extends to full level spaces of dim 3,4,5
   (res 1e-11..1e-12) but not 6 (25 starts, best 0.87); the n=5 dc weight space (dim 3) extends
   to dim 7 (res 6e-8, fresh-point check 9e-9). So 2n-3 also reached via dc-dim-(n-2) + (n-1)
   non-centred directions; neither route exceeds 2n-3.
Evidence: 2n-3 looks optimal at n=4 (all searches stall at 5); dc maxima small (1,2,>=3,>=4 for
n=3..6, consistent with n-2).  No superlinear pattern seen.
