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
Unknown: one matrix E in the 16-dim linear space A_m := {4x5 matrices whose column-sum vector is a multiple of m}, taken modulo N.
Equations: all coefficients in (k, t, x) of R_i(k Z + t Zs + x E), i = 1..4, that contain x (they are polynomials of degree <= 4 in the
entries of E).  Normalise: 2 generic linear equations l_1(E) = l_2(E) = 0 (to remove the N-directions) and one generic affine equation
l_3(E) = 1 (to remove E = 0), leaving 13 unknowns over Q(i, sqrt 3, xi) (or work modulo a prime p = 1 mod 12 in which these exist, for
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

Ambient A_m (dim 16, di_ext.ambient_m(m)); search Gr(5,16) for 5-dim subspaces with defect in C m (di_gr.py: gr_search(k, m, starts,
seed, tmax)), same list of m as in C plus two-column controls.  CALIBRATION: Gr(4,16) with the same code must find the known (4,1) spaces
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

## F. (numerical first, then exact) The four residual kinds (R1)-(R4) of (SL_m) for |supp m| = 3, m non-isotropic   [added 19:45]

Proved by hand (NOTES-verifyfl.md, section DI5-R5, Theorem SL3-RED): let m = (m_1,m_2,m_3,0,0) with m_1 m_2 m_3 != 0, sum m_j^2 != 0, and let
K be a 4-dim column-centred space with defect in C m.  Put s(Y) := vector of the four row sums, q := rank of s on K, N := {Y in K : s(Y) = 0},
N_P := {Y in N : columns 4 and 5 are 0}.  Then K is of one of four kinds; each is a much smaller search than Gr(4,15):
 (R1) q = 3, N = C Zs, Zs has columns 4, 5 zero, all row and column sums zero, and <z_1,z_1> != 0 (z_j = columns of Zs).
      Unknowns: Zs (6-dim linear space of such matrices: (z_1, z_2) in V x V, z_3 = -z_1 - z_2) and three more matrices Y_1, Y_2, Y_3 with zero
      column sums and s(Y_i) = i-th vector of a fixed basis of V (12 unknowns each).  Equations: all coefficients of R_i(t Zs + x_1 Y_1 + x_2 Y_2
      + x_3 Y_3).  Necessary conditions already known for Zs alone: <z_j,z_j> = th m_j (j = 1,2,3) for one number th != 0, sum_k (z_1 z_2 z_3)_k = 0.
 (R2) m = (1,1,-2,0,0), q = 3, N = C v (1,-1,0,0,0) with v in V, <v,v> = 0 (one-parameter family of v up to scale: v = chi_1 + x chi_2
      - (x^2/2) chi_3, or v = chi_3).  Unknowns: x and Y_1, Y_2, Y_3 as in (R1).
 (R3) q = 2, dim N = 2, the image of s is u^perp cap V for some u in V with <u,u> = 0, and some matrix in N has a nonzero column 4 or 5.
 (R4) q = 1, dim N = 3: i.e. a 3-dim space N of matrices with ALL row and column sums zero (ambient dim 12) with defect in C m.
Requests.  (F1) Gr(3,12) search for (R4): 3-dim doubly centred spaces with defect in C m, m = (1,2,-3,0,0), (1,1,-2,0,0), (2,-1,-1,0,0),
 two random complex m.  CALIBRATION: Gr(2,12) with the same code must find the explicit planes N_V of request E (they have defect exactly
 C m) at a healthy rate.  Output: no 3-dim hit  =>  evidence that (R4) is empty (the hand proof needs "doubly centred => dim <= 2").
 An exact version is feasible: N = N_V + C E or N = (a known 1-dim piece) + ..., as in E.
 (F2) typed LM searches for (R1), (R2), (R3) with >= 5000 starts each; calibration for (R3): the same code with the two-column
 m = (1,-1,0,0,0) MUST find 4-dim spaces (they exist with q = 2, dim N = 2, e.g. verifyfl/r5_r2_control_zeta_1.npy, a 4x4x5 array).
 (F3) exact, for (R2): for v = zeta := (1,w,w^2,0) and v = chi_1, all column-centred E (modulo v (1,-1,0,0,0), one affine normalisation)
 such that span(v (1,-1,0,0,0), E) has defect in C (1,1,-2,0,0); then the same one dimension up.  Output: the components and the rank of
 s on each; (R2) needs a 3-dim family of E with s(E) spanning V.
Any verified 4-dim hit for a non-two-column m is a counterexample to (SL_m): save it and try to extend it to a 5-dim space with defect
in C m (di_ext.ext).

## NEXT (written 20:05 after the result of A: unit ideal at four primes, < 0.2 s per run)

Correction (thanks): dim A_m = 16, not 17 (fixed above).  Remark on the numerical requests C, F2: in this container Levenberg-Marquardt on
Grassmannians of 4-dim spaces FAILS EVEN ON THE CONTROL (typed Gr(4,14) search: 0 of 34 starts; untyped: 3 of 82), whereas greedy
one-vector extension from explicit seeds (di_ext.ext, script r5_climb_r3.py) finds the two-column control space in 3 of 3 runs.  So prefer
exact ideals and extension climbs to Grassmannian LM.

### The plan: (SL_m) for a fixed m is equivalent to the emptiness of three small typed systems
For a 4-dim column-centred K put s(Y) := row-sum vector (it lies in V), q := rank of s on K (q <= 3), N := {Y in K : s(Y) = 0} (the
"doubly centred" part), d := dim N = 4 - q.  So K has type (q,d) in {(3,1), (2,2), (1,3), (0,4)}, and (SL_m) holds for m iff
   [DC3] there is no 3-dim space of doubly centred matrices with defect in C m            (kills (1,3) and (0,4));
   [T22] there is no 4-dim K with q = 2;        [T31] there is no 4-dim K with q = 3.
Proved facts that shrink the unknowns (any m; n is "neutral" if m_n = 0; <x,y> bilinear):
   (F1) every column of every Y in K has sum 0.
   (F2) if Z in K is doubly centred then <z_n,z_n> = 0 for neutral n, and <z_j,z_j> = th(Z) m_j for all j with one number th(Z);
        on a doubly centred SPACE the n-th columns (n neutral) all lie on one line C v_n, <v_n,v_n> = 0 (or are all 0).
   (F3) if q = 3 then every doubly centred Z in K has z_n = 0 for all neutral n.
   (F4) if q = 2 and some doubly centred Z in K has z_n != 0 for a neutral n, then s(K) = {x in V : <x,u> = 0} for some u in V, <u,u> = 0.
Every "unit ideal" claim should be run on ALL reduced-echelon cells of the relevant Grassmannian (or all charts of the parametrisation),
at >= 3 primes, with the stated calibrations; then, if unit, once exactly (Singular/msolve over Q or the needed number field).

### N1. [DC-k] doubly centred spaces, k = 2, 3, 4   (decides types (1,3), (0,4); classifies the N of type (2,2))
Ambient D := {4x5 matrices with all row sums and all column sums 0} (dim 12).  For |supp m| = 3 (neutral columns 4, 5) use (F2): unknown
isotropic v_4, v_5 in V (cases: both nonzero / exactly one zero / both zero; an isotropic vector: 3 coordinates in a basis of V, one equation
<v,v> = 0, one affine normalisation), and the space N inside D(v_4,v_5) := {Z in D : column 4 in C v_4, column 5 in C v_5}, which has
coordinates (z_1, z_2 in V; lam_4, lam_5) (z_3 := -z_1 - z_2 - lam_4 v_4 - lam_5 v_5), dim 8 (7, 6 when a v is 0).  Unknown N in Gr(k, 8):
k x 8 matrix in reduced echelon form, all C(8,k) cells.  Equations: all coefficients of R_i(x_1 Z_1 + ... + x_k Z_k), i = 1..4.
Unknown counts (big cell): k = 2: 12 + 4;  k = 3: 15 + 4;  k = 4: 16 + 4.   For |supp m| = 4: one neutral column, ambient D(v_5) of dim 10;
for |supp m| = 5: ambient D itself (dim 12): Gr(2,12), Gr(3,12), Gr(4,12): 20, 27, 32 unknowns.
Output: k = 3 (hence k = 4): UNIT in every cell and every case  ==>  [DC3] for this m.   k = 2: the irreducible components (dimension,
generic point, which columns vanish, value of th) = the complete list of 2-dim doubly centred spaces with defect in C m.
CALIBRATIONS that must come out right for m = (1,2,-3,0,0) (all proved by hand, section DI5-R5 of NOTES-verifyfl.md):
   - k = 2 must contain: chi_1 (x) {zero-sum vectors on any 3 columns} (type I), mu zeta (e_i - e_j)^T + mu' conj(zeta) (e_k - e_l)^T
     (type II, zeta = (1,w,w^2,0)), and N_V = span(chi_1 (c+,0,0), chi_3 (c-,0,0)) of request E, all up to the 24 row permutations;
   - k = 2 with v_4 = v_5 = 0 (spaces supported on columns 1-3) must give EXACTLY type I on columns 1-3 and N_V (Lemma NP);
   - no cell with v_4 = v_5 = 0 and k = 3 (Lemma NP: dim <= 2).
m to run: (1,2,-3,0,0), (1,1,-2,0,0), (1,w,w^2,0,0) [isotropic: here I expect k = 2 families U (x) (1,w^2,w,0,0) and possibly k = 3],
(1,-1,0,0,0) [two-column: what is the largest k?], then |supp m| = 4, 5 from the list of request B, then SYMBOLIC m = (1, mu, -1-mu, 0, 0)
with mu as an additional variable: eliminate everything else; the result is the set of mu for which a 3-dim doubly centred space exists.

### N2. [T31] type (3,1)
Unknowns: Zs doubly centred with zero neutral columns (F3) (|supp m| = 3: (z_1,z_2) in V x V, 6 unknowns, one affine normalisation;
|supp m| = 4: 9; |supp m| = 5: 12), and Y_1, Y_2, Y_3 column-centred with PRESCRIBED row sums s(Y_r) = b_r, b_1 = (1,-1,0,0), b_2 = (0,1,-1,0),
b_3 = (0,0,1,-1) (each Y_r: four columns free in V, the fifth determined: 12 unknowns; remove the gauge Y_r -> Y_r + c Zs by one generic
linear equation per r).  Equations: all coefficients of R_i(t Zs + x_1 Y_1 + x_2 Y_2 + x_3 Y_3).
Stage (a): only Y_1, Y_2 (about 30 unknowns for |supp m| = 3): UNIT  ==>  no K of type (3,1) (K would contain Zs, Y_1, Y_2).
Stage (b), only if (a) is not unit: the full system, and report the components of (a).
For |supp m| = 3, m non-isotropic, I proved that Zs must satisfy <z_1,z_1> != 0 (saturate by it), except when two entries of m are equal
(m = (1,1,-2,0,0): then also Zs = v (1,-1,0,0,0), <v,v> = 0).  Calibration: m = (1,2,-3,0,0) with Zs FIXED to chi_1 (1,1,-2,0,0) (outer product; it has <z_1,z_1> = 0): stage (b) MUST be unit
(hand proof: Theorem SL3-RED, case (i)); stage (a) need not be.
m to run: as in N1.

### N3. [T22] type (2,2)
For each component of the k = 2 list of N1 (its parameters as unknowns) with basis Z_1, Z_2: unknowns Y_1, Y_2 column-centred with
s(Y_1) = b_1 + al b_3, s(Y_2) = b_2 + be b_3 (and the two other charts of planes in V), al, be unknown (if a neutral column is nonzero on N
use (F4): the plane is u^perp with <u,u> = 0, one parameter); gauge Y_r -> Y_r + N removed by two generic linear equations per r.
Equations: coefficients of R_i(x_1 Z_1 + x_2 Z_2 + x_3 Y_1 + x_4 Y_2).  UNIT for every component  ==>  [T22].
CALIBRATION (must be NON-unit): m = (1,-1,0,0,0), N = span(zeta (e_1 - e_2)^T, conj(zeta) (e_4 - e_5)^T): 4-dim spaces exist (numerically:
verifyfl/r5_r2_control_zeta_1.npy, there s(K) = u^perp with u = (1,w^2,w,0)).  For m = (1,2,-3,0,0) and (1,1,-2,0,0) the same N MUST give
the unit ideal, and so must N = chi_1 (x) {zero-sum on any 3 columns} (hand proofs: Props I-ALL, II-ALL of R5.9).

### N4. Cheap cross-checks of my hand lemmas (seconds each; they calibrate the pipeline in both directions)
   - Lemma 3C: spaces supported on columns 1-3 with zero column sums (ambient V^3, dim 9), defect in C m: Gr(4,9) must be UNIT in all cells
     for every m with m_1 m_2 m_3 != 0 (try (1,2,-3,0,0), (1,w,w^2,0,0), symbolic mu); Gr(3,9) must be NON-unit.
   - Theorem PR3: request B with |P| = 3, m = (1,2,-3,0,0): UNIT.
   - Props I-ALL / I': for m = (1,2,-3,0,0) and F = chi_1 (x) {zero-sum vectors on M}, M = {1,2,3}, {1,2,4}, {1,4,5}: the one-vector
     extension variety (E column-centred, modulo F, one affine normalisation) must be EXACTLY ONE point, E = chi_1 e_j^T (j in M) modulo F
     (possibly non-reduced).  NOTE: my numerical extension search (di_ext.ext) does NOT find this existing extension (0 of 36 starts,
     r5_climb_I.py), presumably because it is a degenerate solution - so its negative results elsewhere are weak; please redo exactly
     the one numerical claim that is still used: the 8 planes verifyfl/r4_n2_inj_2_*.npy for m = (1,2,-4,1,0) (request B will
     produce them exactly) have no one-vector extension.
   - Lemma SL (m irrelevant, th == 0, i.e. C(Y) = 24 identically): Gr(4,15) typed as above [DC3], [T22], [T31] must all be UNIT (this is
     the Lean-checked theorem): the best end-to-end test of the typed pipeline.

### N5. If N1-N3 succeed for |supp m| = 3: the same three systems for |supp m| = 4 and 5 (list of request B), then symbolic m per support
size (2 resp. 3 parameters).  A complete unit result for [DC3], [T22], [T31] over symbolic non-two-column m would be a computer proof of (SL_m),
hence of the defect inequality at e = 1.  Please record for every run: the cells, the primes, the timings, and the Groebner bases of all
non-unit cells.

### RIGOUR NOTES for the certification runs (a "unit ideal" is used as a proof of emptiness, so no case may be lost)
   (i)  Isotropic lines of V: every v in V with <v,v> = 0, v != 0, is a multiple of v(th) := chi_1 + th chi_2 - (th^2/2) chi_3 for exactly one
        th in C, or of chi_3.  So "unknown isotropic line" = unknown th, plus the separate case v = chi_3.
   (ii) "Unknown nonzero vector/matrix X up to scale": do NOT use one generic affine equation; run the coordinate charts X_c = 1 for every
        coordinate c (a nonzero X has a nonzero coordinate).  The run of request A used a generic affine normalisation; for the exact
        certification please repeat it with the 13 coordinate charts (or argue that the solution set is a cone not contained in l_3 = 0).
   (iii) Gauge freedoms (Y_r -> Y_r + c Zs etc.): either leave them unfixed (emptiness is unaffected), or fix them with a linear form that
        is nonzero on the gauge direction IN THAT CHART (e.g. in the chart "coordinate c of Zs = 1" use the equation "coordinate c of Y_r = 0").
   (iv) All reduced-echelon cells of each Grassmannian, all cases (each v zero / nonzero), all charts of planes S in V.
   (v)  Characteristic 0: exact over Q or the number field, or unit modulo a prime p together with the remark that the ideal is generated by
        polynomials with p-integral coefficients and the certificate 1 = sum a_i f_i lifts - whichever is easier to certify.

### N6. (think big) The same pipeline decides (6,2) and (7,3): replace the line C m by a subspace C
Let C be a linear subspace of {w in C^5 : sum w = 0} of dimension e (e = 1: C = C m).  "Defect in C": C(Y) - (24,...,24) in C for all Y in
the space; equations R_i for a basis w^(i) of C^perp (5 - e of them).  FACT (one line): if L' is a 4x5 space with defect in C then all
column-sum vectors lie in C, so K := {Y in L' : all column sums 0} has dim >= dim L' - e and is column-centred with defect in C.
Hence the single statement
     (SL_C)  a column-centred space with defect in C has dim <= 3
implies dim L' <= e + 3 for every space with defect in C, i.e. it excludes (5,1), (6,2), (7,3) at once for that C.  (SL_C) is FALSE when C
contains a two-column vector e_a - e_b (then the two-column examples apply); those C need a separate argument.
The typed systems [DC3], [T22], [T31] and the facts (F1)-(F4) hold verbatim with "neutral column" := a column on which every vector of C
vanishes, and (F2) reading <z_j,z_j> = th(Z)_j with th(Z) in C.  Request: run N1-N3 for
   e = 2:  C = span((1,2,-3,0,0), (0,1,1,-2,0)),  span((1,2,-3,0,0), (0,0,1,2,-3)),  span((1,-1,0,0,0), (0,0,1,-1,0)) [control: must be
           NON-empty, it contains two-column vectors],  span((1,1,-2,0,0), (0,0,1,1,-2)),  two random rational planes;
   e = 3:  C = span((1,2,-3,0,0), (0,1,1,-2,0), (0,0,1,2,-3)),  C = {w : w_5 = 0, sum w = 0} [contains two-column vectors: control],
           two random rational 3-spaces;
and, if cheap, C in a chart of the Grassmannian of planes in the 4-dim space {sum w = 0} with its 4 parameters as variables (elimination:
for which C does a 4-dim column-centred space exist?).  A unit answer for a C without two-column vectors is new information about
(6,2)/(7,3); the answers for all C would reduce the defect inequality to the C containing two-column vectors.
