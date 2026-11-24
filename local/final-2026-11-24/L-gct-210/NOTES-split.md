# NOTES-split (role: split, 12:07-13:07)
## RESULT (summary; details below)
1. Exact identities with u := g - (3/2)a (a = alpha_i + beta_j, g DC):
     2P_2 = p_2(u) - (125/4)(p_2 alpha + p_2 beta),   P_3 = (2/3) p_3(u) + (125/4)(p_3 alpha + p_3 beta).
2. Rigorous (r,d) consequences of P_2, P_3: r + e <= 8, r + 2d - e <= 16 (e = dim L cap AB);
   D orthogonal to U + U*U (U = {u_l}), so with Kneser 2r + 3d <= 25 + dim Stab(U*U).  Plus first-order:
   L orthogonal to grad P_k(D).  These do NOT give r + d <= 8: for a DC line, or for the D of rc45, they
   leave r <= 8 (AB-rank of W_D^perp = 8). Only for the weight space W5 (d=3) do they force r <= 4.
3. Trivial but sharper than L092: dim L <= 8 + DC bound (P_1 kills the constant; AB is 8-dim).
   Better reformulation: dim L = r + d <= 4 + min(r_A, r_B) + d. TARGET (S): min(r_A,r_B) + d <= 4 gives dim <= 8.
   Every known level space satisfies min(r_A,r_B) + d <= 3 (= n-2), with equality at every dim-7 example.
4. NEW EXACT 7-dim level spaces (Z[w] exact check, both first-order rigid = maximal by inclusion):
     ex.1 split (5,2): rows 0-2: cols(0,1) = p(w^i,-w^i), cols(2,3) = q(w^2i,-w^2i); row 3 free sum-zero; col 4 = c(1,1,1,0,-3).
     ex.2 split (6,1): cols 0 and 1 each a free multiple of (1,w,w^2,0,0); row 3 free sum-zero; col 4 = c(1,1,1,0,-3).
   With L080 (7,0): dim-7 splits (7,0),(6,1),(5,2); r + d = 7 throughout; each DC dimension costs one AB dimension
   via the P_3 coupling -3 sum alpha_i r_i(g) - 3 sum beta_j c_j(g). Neither extends to dim 8 (LM in Gr(2,4)).
5. Case d=1 of (S) is a statement about 5-dim spaces (delta + graph of invertible M: A -> B); 34 structured LM starts
   find none (solutions drift to singular M). d >= 2 searches are uncalibrated (DC planes too rare for LM).

STATUS 12:09: started; setting up (r,d) decomposition computations.

## Exact identities (verified numerically to 1e-14, split/core.py)
Notation: t = a + g, a = alpha_i + beta_j (alpha, beta sum-zero), g DC, <x,y> = sum_ij x_ij y_ij,
x*y = Hadamard product, p_k(x) = sum x_ij^k.  Put  u := g - (3/2) a  (= Phi_{5/2}(t), Phi_c t := t - c a).
  2 P_2(t) = p_2(u) - (125/4)(p_2(alpha) + p_2(beta))          [= <t, t - 5a> = p_2(g) - 4 p_2(a)]
    P_3(t) = (2/3) p_3(u) + (125/4)(p_3(alpha) + p_3(beta))
  Bidegree form: P_3 = 20(p3 al + p3 be) + 9 al^T g be - 3 sum_i al_i r_i(g) - 3 sum_j be_j c_j(g) + (2/3) p3(g)
  Pure AB part (general k, n=5, e_1 = 0): P_k(a) = sum_s e_s(al) e_{k-s}(be) (5-s)!(5-k+s)!/((5-k)!)^2, i.e.
    P_2(a) = -10(|al|^2+|be|^2), P_3(a)=60(e3 al+e3 be), P_4(a)=120(e4+e4)+36 e2(al)e2(be),
    P_5(a)=120(e5+e5)+12(e2(al)e3(be)+e3(al)e2(be)).
## Exact consequences for (r,d,e)  (D = L cap DC, R = AB-projection, E = L cap AB, U = Phi_{5/2}(L))
 (i) P_2 isotropy (orthogonal sum AB (+) DC):  r + e <= 8,  r + 2d - e <= 16.  Allows r = 8 with d <= 4.
 (ii) P_2,P_3 polarised with one/two slots in D: since u_delta = delta and alpha_delta = beta_delta = 0,
      D  is orthogonal to  U + U*U  (U has dim r+d, contains D).  Kneser (L065) => 2r + 3d <= 25 + s,
      s = dim Stab(U*U) (s = 1 generic).  Weak: allows (8,3).
 (iii) First order at D: L orthogonal to W_D := span{grad P_k(delta): delta in D, k=1..5}; D lies in the
      radical of every Hessian form restricted to Y_D := W_D^perp.  So r <= AB-rank(Y_D).
STATUS 12:18: rc45 (4x5 row-centred padded, (r,d)=(4,2), dim 6) + 1 direction found inside its first-order ext space: GENUINE 7-dim level (fresh orthonormal check 6e-13), (r,d,e)=(5,2,0) -> split/rc45p1.npy. Trying +2.

## NEW EXACT EXAMPLE: 7-dim level space with split (r,d,e) = (5,2,0)  [STATUS 12:4x]
Basis (w = primitive cube root of 1, rows/cols 0..4):
  B1: rows i=0,1,2: t[i,0] = w^i, t[i,1] = -w^i      (DC)
  B2: rows i=0,1,2: t[i,2] = w^{2i}, t[i,3] = -w^{2i} (DC)
  B3..B6: row 3 = any sum-zero row (t[3,j] - t[3,4], j<4)
  B7: column 4 = (1,1,1,0,-3)^T
EXACT check over Z[w] (split/exact7.py, unisolvent evaluation, P_1..P_5): all zero.
= L_gct_180's 4x5 row-centred space padded with a zero row (dim 6, split (4,2)) + the column B7.
Found by LM inside the first-order extension space E(rc45) (dim 10); E(this space) = itself
(first-order rigid, maximal by inclusion). rc45 + 2 directions (dim 8, 4-param Grassmannian Gr(2,4)):
20 starts all stall at res >= 1.7 -> no 8-dim level space contains rc45.
So dim-7 level spaces realise at least the splits (7,0) [L080] and (5,2) [this].
NB numerics agent: the old "W5 (d=3) extends to 7" was a degenerate artifact; genuine W5 extensions
seen so far: (1,3) dim 4, (2,3) dim 5.

## NEW EXACT EXAMPLE 2: 7-dim level space with split (r,d,e) = (6,1,0)  [STATUS 12:30]
  columns 0 and 1: each an independent multiple of v = (1, w, w^2, 0, 0)^T     (2 params; D = {col0 = -col1})
  row 3: any sum-zero row (4 params);  column 4: multiple of (1,1,1,0,-3)^T (1 param).
EXACT check over Z[w] (split/exact7b.py): P_1..P_5 vanish on the span.  First-order rigid (E = itself).
Found as (rc45p1 minus B2) + 1 LM direction inside E (complement dim 4).  +2 (dim 8): 10 starts, res >= 2.
So genuine 7-dim splits known: (7,0) L080, (6,1) ex.2, (5,2) ex.1 -- all r + d = 7, all maximal by inclusion.
Mechanism visible in ex.1/ex.2: P_3's (1,2)-coupling  -3 sum_i alpha_i r_i(g) - 3 sum_j beta_j c_j(g)  forces the
column vector c (col 4) to be orthogonal to the row-square-sum vectors (sum_j delta_ij delta'_ij)_i of D, so each
DC dimension kills one direction of the column part. (Here the DC part of every l in L is orthogonal to D*D, so
the general relation  <(d d')_DC, g_l> = (3/2)(alpha_l . rho(d,d') + beta_l . kappa(d,d'))  reduces to alpha_l . rho = 0.)

## PROPOSED SHARPER SPLIT TARGET (S)  [STATUS 12:33]
r_A := rank of l -> alpha_l (row means) on L, r_B := rank of l -> beta_l, d = dim(L cap DC). Always r <= r_A + r_B,
r_A, r_B <= 4, so  dim L = r + d <= 4 + min(r_A, r_B) + d.   Hence
  (S)  min(r_A, r_B) + d <= 4     ==>   dim L <= 8.
(S) is monotone under passing to subspaces. Data (r_A, r_B, d): L080 (4,3,0); ex.2 (2,4,1); ex.1 (1,4,2);
rc45 (1,4,2); rc44 (1,3,2); W5 (0,0,3); W5+1 [numerics] (1,1,3).  All satisfy min+d <= 3 except W5+1 (= 4).
All three dim-7 examples have R = (R cap A) (+) (R cap B) and max(r_A,r_B) = 4, min + d = 3.
Cases of (S): d=1: alpha- and beta-projections not both onto; d=2: min <= 2; d=3: min <= 1; d=4: L row- or
column-centred; d>=5 excluded by a DC bound <= 4.
CORRECTION 12:40 (rank bug for zero alpha): (r_A,r_B,d): L080 (4,3,0), ex.2 (2,4,1), ex.1 (1,4,2), rc45 (0,4,2),
rc44 (0,3,2), W5 (0,0,3), W5+1 (1,0,3).  ALL known examples satisfy  min(r_A,r_B) + d <= 3 = n-2,
with equality for every dim-7 example.  So conjecture (S3): min(r_A,r_B) + d <= n-2, which with
r <= (n-1) + min(r_A,r_B) gives exactly dim L <= 2n-3.  (S) [<= 4] suffices for the gap.

## (S) at d = 1 reduces to a 5-dim configuration; numerics say it does not exist  [STATUS 12:5x]
Case d=1 of (S) <=> "if alpha(L) = A and beta(L) = B then L cap DC = 0". If violated, L contains a 5-dim level
subspace span(delta, l_1..l_4) with delta DC and (alpha_k, beta_k) = (f_k, M f_k), M INVERTIBLE (choose the
section of R -> A suitably; possible because beta(R) = B). Structured LM (split/sviol.py, sviol2.py; unknowns
delta (normalised), DC parts g_k, M; 96 params):
 - calibration R = B (r_A=0, r_B=4, d=1): solution found (res 2e-12, 1 of 4 starts).
 - M free: 22 starts; best "solutions" (res 5e-10) have M -> 0 (sv(beta) 2e-3,7e-5,1e-5): drift to the
   column-centred boundary, not a violation.
 - det M = 1 imposed: 12 starts, all stall at residual ~1 (LM gives up det, M near-singular).
Weak but consistent evidence that the d=1 case of (S) holds. The d=1 case is a statement about 5-dim spaces only.

## Structured tests of (S3)/(S) at small dims (split/sgen.py: D of dim d (chart) + k elements whose alpha- and
## beta-parts both have rank k (det of top minors = 1); dim d+k)  [STATUS 12:43]
 calibration (d,k)=(1,2) [exists, e.g. inside ex.2]: found, res 9e-13, fresh 9e-14 (5 starts).
 calibration (d,k)=(2,1) [exists inside ex.1]: NOT found in 36 starts -> searches with d >= 2 are not trustworthy
   (DC level planes are rare/special); no conclusions for d >= 2.
 (d,k)=(1,3) [would violate (S3) but not (S)]: 25 starts, best res 6.7e-5, NONDEGENERATE (sv alpha .23 .18 .12,
   sv beta .27 .22 .09, basis well conditioned). Structured polish: 6.7e-5 -> 9e-7 -> 1.6e-7 with the structure
   frozen (slow, singular-type convergence). delta is rank 2, supported on rows {0,1,3}.  UNRESOLVED: possibly a
   genuine 4-dim level space with d=1, r_A=r_B=3 (then (S3) is FALSE, (S) still fine). File split/sgen_1_3_pol_pol.npy.
UPDATE 12:42: (1,3) candidate is a NEAR-MISS, not a solution: structured polish stalls at res 1.6e-7 (LM damping
blows up); polishing in the support ambient {rows 0,1,3} + {(2,2),(4,2)} converges quadratically (2.9e-14, fresh 7e-13)
to a d = 0 space (r_A,r_B,d) = (3,4,0) at distance ~6e-5. So no evidence against (S3).
Check: on ex.1/ex.2, max|<D,U>| ~ 1e-15, max|<D,U*U>| ~ 1e-15 (claim (ii)), dim U*U = 16 / 19.
Observation 12:45: ex.2 and L080 are both of L_gct_114 product type ("row part + column part", every
combination level): L080 = row V (3) + column S (4); ex.2 = row 3 V_3 (4) + columns S_0 = S_1 = C(1,w,w^2,0,0),
S_4 = C(1,1,1,0,-3) (1+1+1).  Both have sum dim = 7 vs the checked bound 2n-2 = 8 of L_gct_114.  ex.1 is NOT
product type (columns 0 and 1 are tied: col1 = -col0).
STATUS 12:40: second (1,3) batch (seed 11, 160 s): best res 5.4e-4, no solution. (1,3) total ~45 starts, only the near-miss. Evidence for (S3) at d=1: a level space containing a nonzero DC matrix has min(r_A,r_B) <= 2. Done; final report sent.
STATUS 12:48: NEW TASK (exact algebra for d=1 of (S)) started.

## TASK 2 (12:47-): exact algebra for d = 1 of (S)
### (a) Why there are no "conditions on M alone"
With L = span(delta, l_1..l_4), l_k = a_k + g_k, a_k = f_k 1^T + 1 (M f_k)^T, the DC parts g_k (psi: A -> DC/C delta, 60
unknowns) enter every level condition. The pure-AB components P_k(a) are only the top a-degree pieces; no degeneration
isolates them (lambda -> 0 / infinity limits of (a,g) -> (a, lambda g) lose all information, see NOTES above).
The first-order conditions grad P_k(delta).(a + g) = 0 are linear in g and are always absorbed by g. So any obstruction
must come from eliminating psi from the full system: not a "small subsystem".
### (b) Rigorous lemma for psi = 0 (pure AB part), via the Clebsch cubic
P_k(a) on pure AB matrices: P_2 = -10(p2 al + p2 be), P_3 = 20(p3 al + p3 be). A 4-dim level space of pure AB matrices
would be a graph beta = phi(alpha) with phi invertible on V4 = sum-zero C^5 and p2.phi = -p2, p3.phi = -p3.
theta = i phi is p2-orthogonal with p3.theta = i p3. The linear stabiliser of the Clebsch diagonal cubic {p3 = 0} in P(V4)
is S5 (classical), so theta = mu sigma with sigma a permutation: mu^2 = 1 and mu^3 = i: impossible. Hence e = dim(L cap AB)
<= 3 (numerically: pure-AB level planes not found (4 starts), lines exist: e <= 1 expected). Not enough for (S).
### (c) Where the obstruction sits (numerics)
- (1,1) and (1,2) configurations (delta + k elements with alpha, beta both of rank k) exist; the (1,2) ones found have
  a GENERIC rank-4 delta, so no constraint on delta or on M restricted to planes comes from 3-dim subsystems.
- Expected dimension: 3-dim level spaces form a family of expected dim 63 - 52 = 11 > 0; 4-dim: 80 - 121 = -41.
  Every 4-dim level space is an excess-intersection object, so the (1,3) obstruction is invisible to counting.
- Seeds S = delta + 2 generic elements of ex.2 (a (1,2) config): E(S) has dim 12 with alpha-projection rank 3 and
  beta-projection rank 4, so FIRST ORDER allows (3,3,1). One-step LM extensions inside E(S): 19 'solutions' with
  (r_A,r_B,d) = (3,3,1) at res 1e-11, but all lie within ~1e-4 of the ex.2 span (third alpha s.v. ~1e-4); the ones
  far from ex.2 have r_A = 2.
- HOMOTOPY TEST (split/push2.py): structured parametrisation (delta DC + 3 graph elements), force the alpha 3x3 minor
  up while holding the beta minor: residual grows like smin(alpha)^2:  smin 9e-5 -> res 3e-13, 9e-4 -> 2e-12,
  2.7e-3 -> 1e-10, 9e-3 -> 5e-9, 6e-2 -> 7e-7, 0.17 -> 4e-6 (beta then starts to collapse). Forcing alpha alone
  (push.py): beta collapses to rank 1 (sv .28, 1e-3, 5e-4). So near ex.2 the (3,3,1) direction is a
  first-order-but-not-second-order deformation: a SECOND-ORDER obstruction. Consistent with (S3) at d = 1.
- Generic (1,2) configuration (sgen_1_2.npy, rank-4 delta) is first-order RIGID: E(S) = S (dim 3). So (1,3)
  configurations can only grow out of special (1,2) configurations (like subspaces of ex.2, where dim E(S) = 12).
- Exact identities for a two-column rank-one delta = v (e_0 - e_1)^T (the ex.2 type; DC level iff sum v = sum v^2 = 0):
  for every t in L, A = J + t:  perm(A) = 120,  perm(A with col 0 := v) = perm(A with col 1 := v),
  perm(v, v, A_2, A_3, A_4) = 0  (multilinearity in columns 0,1).  For v = (1,w,w^2,0,0) the last one reads
  sum_{c=2,3,4} tau_c(t) perm((J+t)[{3,4},{2,3,4}\c]) = 0,  tau_c(t) = sum_{k<3} w^{-k} t_kc.  (No lemma extracted.)
STATUS 13:05: task 2 wrap-up. Conclusion: no small exact subsystem exists (psi absorbs everything below the 4-dim level);
the d=1 obstruction is a second-order (excess-intersection) phenomenon, numerically robust near ex.2.
Tools: split/push.py, push2.py (homotopy: force alpha (and hold beta) 3x3 minors, watch residual), split/seed13*.py.
CORRECTION/ADDENDUM 13:12:
- Growth law: with longer LM (55 s per step) the homotopy residual is at noise (1e-13..1e-12) up to smin(alpha) ~1e-3,
  then 3e-9 at smin 9e-3 (fresh 6e-7): growth ~ smin^3..4, not ^2. A tangent-to-high-order (non-reduced) direction,
  like the L080 pitfall found by numerics.
- PITFALL: a fixed-S extension test that only fixes the linear functional ell(y) = 1 (alpha component outside alpha(S))
  finds 'solutions' (fresh 1e-10) with third alpha s.v. ~1e-4: y becomes dominated by ex.2 directions. Any such test
  must control the alpha-out FRACTION (normalised basis); push2.py does (fixed 3x3 minors in structured coordinates).
- 13:16: long polish (160 s) at fixed alpha/beta minors, smin(alpha) = 8.7e-3, smin(beta) = 7.3e-2: residual 3e-9 -> 8.6e-10
  (fresh 5.7e-7 -> 1.1e-7), still decreasing slowly, no damping stall. So near ex.2 the numerics are INCONCLUSIVE:
  either a valley/near-miss, or a genuine non-reduced (3,3,1) family that LM converges to very slowly. In contrast,
  the random-start (1,3) near-miss stalled hard (damping blew up at 1.6e-7), and the k=4 test with det M = 1 stalled
  at O(1). Net: (S) at d=1 (k=4) has decent support; (S3) at d=1 (k=3) is NOT settled. Do not rely on (S3).
STATUS 13:17: task 2 done (no exact lemma for d=1; see TASK 2 section).
