# COMPUTE-verifyfl.md — heavy computations requested by verifyfl (written 19:29, round 5)

Self-contained. Scripts referred to are in /home/claude/work/L-gct-210/verifyfl/ (numpy only; every script starts with
`import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")`, run with `python3 -I`).  Helpers: core.py (perm, Pk, sl_check),
di_core.py (Cvec, defect, onb, kernel_of), di_ext.py (mperp, res_m, ambient_m, ext, chk_m), r3_z.py (search), r4_n2.py, r4_pr3.py.

## 0. Definitions (everything below uses only these)

* perm = permanent.  For a 4x5 complex matrix Y and j = 1..5:  C_j(Y) := perm(J_4 + Y^(j)), where J_4 is the all-ones 4x4 matrix and
  Y^(j) is Y with column j removed.  C(Y) := (C_1(Y),...,C_5(Y)).  (C(0) = (24,...,24).)   [di_core.Cvec]
* m in C^5 is fixed, m != 0, sum_j m_j = 0.  P := {j : m_j != 0}.  "m two-column" = |P| = 2.  "m isotropic" = sum_j m_j^2 = 0.
* A LINEAR space L of 4x5 matrices "has defect in C m" if for every Y in L the vector C(Y) - (24,..,24) is a multiple of m.
  Equivalently: for a basis w^(1..4) of {w in C^5 : sum_j w_j m_j = 0},  R_i(Y) := sum_j w^(i)_j (C_j(Y) - 24) = 0 for all Y in L.
  With a basis B_1..B_k of L and Y = sum x_r B_r this means: every coefficient of the polynomials R_i(x_1..x_k) (degree <= 4) vanishes.
  (The degree-1 coefficients say: the column-sum vector of every Y in L is a multiple of m.)   [di_ext.res_m evaluates (R_1..R_4)]
* L is "strongly level" if C(Y) = (24,..,24) on L (known theorem, Lean-checked: then dim L <= 3).  A "(k,1) space" is a k-dim space with
  defect in C m that is not strongly level.  L is "column-centred" if every column sum of every Y in L is 0.
* TARGETS.  (SL_m): a column-centred space with defect in C m has dim <= 3 (for m not two-column).   (5,1): there is no 5-dim space with
  defect in C m.  (SL_m) for all non-two-column m implies (5,1) for all m (two-column m is already proved).
* Vectors in C^4: one = (1,1,1,1), chi_1 = (1,i,-1,-i), chi_2 = (1,-1,1,-1), chi_3 = (1,-i,-1,i); w = exp(2 pi i/3).
  <x,y> := sum_k x_k y_k (bilinear, NO conjugation).  V := {x in C^4 : sum x = 0}.

## A. (small, exact, decisive) The four explicit isotropic planes N have no extension   [decides: principal (5,1) for m = (1,w,w^2,0,0)]

m = (1, w, w^2, 0, 0).  For beta in {+sqrt(3)/4, -sqrt(3)/4} and xi one of the two roots of xi^2 = -3/(32 beta):
    h_0 := (1/4) one + beta chi_2;   Z := h_0 (1, w, w^2, 0, 0) + chi_1 (0, xi, -xi, 0, 0);   Zs := chi_1 (1, w^2, w, 0, 0)   (outer products, 4x5)
    N := span(Z, Zs).   (r4_pr3.py, function Nplane(beta, sgn), builds exactly these; they have defect in C m, checked to 1e-13.)
Unknown: one matrix E in the 17-dim linear space A_m := {4x5 matrices whose column-sum vector is a multiple of m}, taken modulo N.
Equations: all coefficients in (k, t, x) of R_i(k Z + t Zs + x E), i = 1..4, that contain x (they are polynomials of degree <= 4 in the
entries of E).  Normalise: 2 generic linear equations l_1(E) = l_2(E) = 0 (to remove the N-directions) and one generic affine equation
l_3(E) = 1 (to remove E = 0), leaving 14 unknowns over Q(i, sqrt 3, xi) (or work modulo a prime p = 1 mod 12 in which these exist, for
several primes).
Method: exact Groebner basis (msolve / Singular / Macaulay2), any order; only "is the ideal the unit ideal?" matters.
Output decides: UNIT IDEAL for all four (beta, xi)  ==>  no 3-dim space with defect in C m contains N  ==>  (by my Theorem PS and the
proof of Theorem PR3, NOTES-verifyfl.md R4.3-R4.5: every (5,1) space for this m whose kernel-of-column-sums contains a 3-dim subspace H
with zero quadratic defect and row sums spanning V contains a row-permuted copy of one of the four N)  ==>  no such "principal" (5,1).
Not unit: print the solution set (dimension, and one point): that is a new 3-dim space; then repeat with it in place of N.
Numerical status here: 0 extensions in 60 Levenberg-Marquardt starts (r4_pr3.py part (3)); 18 greedy climbs stop at dim <= 3 (r4_climb2.py).
Calibration (must be NON-unit): replace N by span(Zs) alone (2-dim extensions exist: N itself).

## B. (exact, medium) The "N-problem" for |P| = 4 and |P| = 5   [decides: principal (5,1) for these m]

Given m with support P, |P| = p in {4,5}.  Unknowns: two 4x5 matrices Z, Zs with all columns outside P equal to 0, such that
 (1) all row sums of Z and of Zs are 0;  column sums of Z are m_j (j in P);  column sums of Zs are 0;
 (2) span(Z, Zs) has defect in C m: all coefficients in (k,t) of R_i(k Z + t Zs), i = 1..4, vanish;
 (3) (normal form) for j in P, with z_j the j-th column of Z, z0_j := z_j - (m_j/4) one, zs_j the j-th column of Zs:
        <z0_j, z0_j> = (3/4) m_j^2,     <zs_j, zs_j> = 0,     <z0_j, zs_j> = 0;
 (4) (non-degeneracy, to be imposed by SATURATION) zs_j != 0 for every j in P.
Free unknowns after (1): 6p - 6 (18 or 24).  Gauge: Z -> Z + c Zs and Zs -> c' Zs (fix by one generic linear equation on Z and one
generic affine equation on Zs); the 24 row permutations act.
Method: exact Groebner (msolve over Q or modulo large primes), ideal I of (1)-(3), then saturate successively by the ideals
(entries of zs_j), j in P; equivalently run over the charts "entry (r,j) of zs_j equals 1" for one fixed j and saturate for the others.
Output decides: UNIT IDEAL  ==>  no "principal" (5,1) space with this defect line (Theorem PS, R4.3).  Otherwise: the solution set
(dimension, degree, sample points) - these N must then be tested for extensions as in A.
Values of m, in this order: (1,2,3,-6,0); (1,2,-4,1,0) [expected NON-empty: LM finds solutions, files verifyfl/r4_n2_inj_2_*.npy, each
a 2x4x5 array (Z-like basis, not gauge-fixed)]; (1,1,1,-3,0); (1,1,-1,-1,0); (1,i,-1,-i,0); (1,2,3,-1,-5); (1,1,1,1,-4); (2,2,2,-3,-3);
(1,z,z^2,z^3,z^4) with z = exp(2 pi i/5).  If feasible: m_1..m_4 as PARAMETERS for |P| = 4 (m_4 = -m_1-m_2-m_3, projective, so set m_1 = 1)
and eliminate all matrix unknowns: the result is the locus of m admitting a solution (I expect it to be contained in "two entries equal"
union "isotropic").
Calibration (|P| = 3, same system with p = 3, 12 unknowns): m = (1,2,-3,0,0) MUST give the unit ideal (Theorem PR3, proved by hand);
m = (1,w,w^2,0,0) MUST give exactly the planes of A (plus row permutations).  Numerical version of this system: r4_n2.py (LM on a
Grassmannian; option 'nf' adds (3); the flag "ALL COLUMN MAPS INJECTIVE" is (4)).

## C. (numerical, large) Calibrated searches for (SL_m): column-centred 4-dim spaces with defect in C m

Ambient space: 4x5 matrices with all column sums 0 (dim 15).  Search Gr(4,15) for 4-dim subspaces with defect in C m.
Start from r3_z.py: `search(k=4, m, starts, seed, tmax)` (chart of the Grassmannian, 44 complex unknowns, residual = (R_1..R_4) at 44 random
points of the space, complex Levenberg-Marquardt with finite-difference Jacobian, acceptance |residual| < 1e-9).  It is slow and weak:
improve it (analytic Jacobian, or use the exact coefficient equations instead of sampled points, many random restarts, several charts).
CALIBRATION THAT MUST SUCCEED FIRST: m = (1,-1,0,0,0) (two-column) HAS solutions; my solver finds them at only 3 of 82 starts.  Do not
trust negatives before the control rate is >= 20 hits per 1000 starts; report the control rate with every result.
Then, >= 5000 starts each: (1,2,-3,0,0); (1,1,-2,0,0); (1,w,w^2,0,0); (1,2,3,-6,0); (1,2,-4,1,0); (1,1,1,-3,0); (1,1,-1,-1,0);
(1,i,-1,-i,0); (1,2,3,-1,-5); (1,1,1,1,-4); (2,2,2,-3,-3); fifth roots of unity; 5 random complex m for each support size 3, 4, 5.
Every hit: polish by Newton to 1e-13, confirm dim 4 (SVD), confirm not strongly level (core.sl_check > 1e-5), save the basis (.npy).
Output decides: a verified hit for a non-two-column m  ==>  (SL_m) is FALSE in that stratum (then run D seeded with the hit: is there a
5-dim space with defect in C m containing it? di_ext.ext does one-vector extensions).  No hit with a healthy control rate = evidence only.
Also useful, same code with k = 3: the census of 3-dim column-centred spaces by type (q,d) (q = rank of the row-sum map, d = dim of its
kernel) - r5_types.py prints it; I need to know whether any 3-dim column-centred (3,1) space with d >= 1 and q = 2 exists for
m = (1,2,-3,0,0) (they would be the 3-dim slices of a hypothetical 4-dim space of type (3,1)).

## D. (numerical, large) Direct search for (5,1) spaces

Ambient A_m (dim 17, di_ext.ambient_m(m)); search Gr(5,17) for 5-dim subspaces with defect in C m (di_gr.py: gr_search(k, m, starts,
seed, tmax)), same list of m as in C plus two-column controls.  CALIBRATION: Gr(4,17) with the same code must find the known (4,1) spaces
(for m = (1,2,-3,0,0) they exist: e.g. rows/clm_p4_d4_defect1_s*.npy and verifyfl/r3_gr_*.npy; they all contain a matrix e_i m^T with a
single nonzero row).  Output decides: a verified 5-dim hit is a COUNTEREXAMPLE to the defect inequality (DI_5) at e = 1: report it at once and save the basis.
(It yields the level 5x5 space L' + e_5 (x) {w : sum w = 0, sum w_j m_j = 0} of dimension 5 + 3 = 8; what that means for the
overall strategy is for the coordinator to judge.)  No hit with a healthy control rate = evidence only.

## E. (exact, medium) One-vector extensions of explicit 2-dim spaces for a good 3-support m   [feeds the hand proof of (SL_m), |P| = 3]

m = (1,2,-3,0,0).  r := sqrt 7, c+ := (1, -3 + r, 2 - r), c- := (1, -3 - r, 2 + r) (the two zero-sum vectors c on the first three columns
with m_1 c_2 c_3 + m_2 c_1 c_3 + m_3 c_1 c_2 = 0).  Explicit doubly centred planes with defect in C m (checked 1e-12, r5_checks.py):
   N_V := span( chi_1 (c+,0,0), chi_3 (c-,0,0) )  (defect exactly C m),     N_I := span( chi_1 (1,-1,0,0,0), chi_1 (0,1,-1,0,0) )  (strongly level).
For F in {N_V, N_I, span(chi_1 (c+,0,0)), span(chi_1 (1, w, w^2, 0, 0))}: compute ALL matrices E with zero column sums (15 unknowns, modulo F,
one affine normalisation) such that F + C E has defect in C m (equations: coefficients containing x of R_i(y + x E), y in F).
Method: exact Groebner / primary decomposition; output: for each F the irreducible components of the extension variety (dimension, and
for each component whether the row-sum vector of E is 0 on it, and the ranks of columns 4 and 5 of E).  This decides which branches of the
type analysis of (SL_m) for |supp m| = 3 are empty (R5 of NOTES-verifyfl.md); in particular "no component with row sums spanning a 3-dim
space together" for F = span(chi_1 l^T) kills type (3,1) with that Z_*.
