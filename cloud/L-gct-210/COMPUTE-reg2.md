# COMPUTE-reg2: heavy computations that would help close the regime a_r >= 2 of L-gct-210

Written by agent reg2 (19:30). Self-contained. Background and proofs: /home/claude/work/L-gct-210/NOTES-reg2.md.
All scripts named below live in /home/claude/work/L-gct-210/reg2/ and must be run FROM THAT DIRECTORY with `python3 -I`
(they read `../rows/*.npy`, and insert the absolute paths /home/claude/work/L-gct-210/{reg2,stage2,chief} into sys.path:
mirror that layout or edit the first line of each script). They need numpy only. Copy also rows/, stage2/, chief/.

## 0. Definitions (everything over C; indices from 0)

- perm(A) = permanent. J = 5x5 all-ones, J' = 4x5 all-ones.
- For a 4x5 matrix X: N_j(X) := perm of the 4x4 matrix "X without column j" (j = 0..4); N(X) := (N_0..N_4) in C^5;
  F(X) := sum_j N_j(X) = sum over injective f:{0..3}->{0..4} of prod_i X[i,f(i)].  (F(J') = 120, N(J') = 24*(1,1,1,1,1).)
- 4x5 LEVEL SPACE: a linear subspace M of C^{4x5} with F(J' + Y) = 120 for all Y in M. Equivalent: P_1 = P_2 = P_3 = P_4 = 0
  on M, P_k(Y) = sum of the permanents of all k x k submatrices of Y. (dim M <= 7 is proved upstream; largest known: 6.)
- A 4x5 matrix Y is EMBEDDED as the 5x5 matrix (Y ; 0) (rows 0..3 = Y, row 4 = 0). Then perm(J + (Y;0)) = F(J' + Y).
- 5x5 level space: linear L in C^{5x5} with perm(J + t) = 120 on L. The GAP: dim L <= 8. Regime a_r >= 2: L of dim 9 such
  that L_r := {t in L : row r of t = 0} has dim >= 6 (it is then an embedded 4x5 level space of dim 6 or 7).
- cof(A)[i,j] := perm of A without row i and column j (5x5 -> 25 numbers; it is the gradient of perm).
- T_1(M) := { t in C^{5x5} : sum_{i,j} t[i,j] * cof(J + (Y;0))[i,j] = 0 for all Y in M }.  (Every 5x5 level space containing
  the embedded M lies in T_1(M).)  In coordinates t = (X ; rho), X = rows 0..3, rho = row 4:
      t in T_1(M)  <=>  <rho, N(J'+Y)> + D_X F(J'+Y) = 0 for all Y in M      (D_X = derivative in direction X).
- Omega(M) := { rho : (X ; rho) in T_1(M) for some X } (row-4 projection of T_1(M)); always contains (1,1,1,1,1).
- E_0(M) := { X in C^{4x5} : (X ; 0) in T_1(M) } = { X : D_X F(J'+Y) = 0 on M }  (contains M; every 4x5 level space containing M
  lies in E_0(M)).   dim T_1(M) = dim E_0(M) + dim Omega(M).
- Defect space C(M) := span{ N(J'+Y) - 24*(1,..,1) : Y in M } (inside the sum-zero vectors of C^5); e(M) := dim C(M).
  Column c is NEUTRAL for M if N_c(J'+Y) = 24 for all Y in M (i.e. every vector of C(M) has c-th coordinate 0).
- FULL FREE ROW: M contains { e_i w^T : w in C^5, sum w = 0 } (4-dim) for some row i.
- TYPE F: M contains a full free row.   TYPE NC: no full free row, exactly one neutral column c, e(M) = 3, and
  Omega(M) = span((1,1,1,1,1), e_c) (so dim Omega = 2, and then dim T_1 = 9 in all examples).   Anything else: OTHER.
- FO2 bound of M: n - ceil(rank/2), n = dim T_1(M), rank = rank of a random linear combination of the Hessian forms
  D^2 perm(J + (Y;0)) restricted to T_1(M) (bilinear, not hermitian). Code: stage2/r5_FO2.py, function FO2(Mb, rg) with
  Mb = embedded basis (d,5,5); returns (n, rank, bound). Every level space containing M has dim <= bound.
- PROVED (NOTES-reg2 section 1): for a level L and row r:  dim L <= dim L_r + dim Omega(L_r) - 1.  And (Theorem FL, verified by
  the team): a 5x5 level space containing a full free row has dim <= 7.
- THE TARGET STATEMENT (S6'): every 6-dim 4x5 level space M WITHOUT a full free row has dim Omega(M) <= 2.
  (S6') implies: no 9-dim level space has a row or column with a_r >= 2.  ("dim Omega <= 3" suffices for a_r = 2;
  a_r = 3 would also follow from "no 7-dim 4x5 level space exists".)  About 180 six-dim spaces checked so far (41 independent ones + 146 census solutions): all Type F or NC.

Helper functions already written (import from reg2/):
  t.py: perm, level_err(B) (max |F(J'+Y)-120| at random points of span(B)), rank, rowpart/colpart (single-row/column parts);
  a1.py: embed(B) ((d,4,5) -> (d,5,5)), defect(B) (singular values spanning C(M)), phirank, Phi, pk;
  a6.py: T1(Mb, rg) (basis of T_1 as (n,5,5)), E0(B, rg) (basis of E_0 as (n,4,5));
  a9.py: Omega(B, rg) -> (basis of Omega, dim T_1);
  ext6.py: F45, perm5 (vectorised), complement, solve_ext(M, D, m, rg, iters, N), classify(B, rg) -> ('F'|'NC'|'OTHER', text).
NUMERICAL PITFALL (important): many solutions are reached by "singular convergence": residual 1e-12 but the SPACE is only
  accurate to about 1e-6. Decide all ranks with a RELATIVE tolerance 1e-4 .. 1e-5 (classify() does), or polish first (Newton in
  extended precision, mpmath / Arb), before calling anything OTHER. Never report an OTHER space without re-checking level error
  < 1e-10 at 100 fresh random points and re-computing its invariants after polishing.

## 1. Census A (most useful, already working): 6-dim level spaces containing a known smaller level space

System. Given a level space M_b (basis, dim b in {2,3,4,5}), compute E_0(M_b) (linear algebra), D := a complement of M_b in
E_0(M_b) (dim q). Unknown: an m-plane G in D, m = 6 - b (Grassmannian chart, m(q-m) complex unknowns, 2..40). Equations:
F(J' + Y + g) = 120 for all Y in M_b, g in G (sampled at 300 random points; polynomial of degree 4). Every 6-dim level space
containing M_b arises this way (rigorous), so with enough starts this ENUMERATES the 6-dim level spaces through M_b.
Start from: `python3 -I ext6.py SEED TMAX` (bases: rows' (4,1), (5,2) spaces and the 5-dim line-kernels of the 7-dim spaces);
            `python3 -I ext6c.py SEED TMAX sub` (random 2-,3-dim subspaces of known 6-dim spaces);
            `python3 -I ext6c.py SEED TMAX ker` (3-,4-dim line-kernels of the 7-dim spaces, rows' strongly level 3-dim spaces);
            `python3 -I ext5.py SEED TMAX` (same with target dimension 5; prints dim Omega of each 5-dim space).
Scale-up wanted: (i) base spaces = EVERY 4x5 level space on disk: ../rows/clm_p4_d*_*.npy, nc_d6_*.npy, seed_d6_*.npy,
c52_*.npy, cc_d*_*.npy (check shape (d,4,5) and level_err < 1e-9 first), all line-kernels of dims 2..5 of the seven 7-dim
spaces in chief/core.py (dict core.SP; see ext6c.py for how kernels are taken; use rows AND columns = transposes), and for
every 6-dim space found, 20 random subspaces of each dimension 1, 2, 3 (ITERATE until no new type appears); (ii) 200 starts per
base (solve_ext uses a finite-difference Jacobian and LM; raise iters to 600; for m(q-m) > 20 use N = 500 sample points);
(iii) also target dimension 7 (m = 7 - b): `python3 -I ext7.py SEED TMAX` (here: 0 of 132 starts, residual floor 118).
Calibration that must succeed first: from a random 3-dim subspace of ../rows/rc45.npy and of ../rows/nc_d6_k1_s4.npy the
search must return the 6-dim space itself (it does here: 4-5 of 5 starts, about 1 s per start).
Output and decision: table base -> number of solutions of type F / NC / OTHER, plus for each solution dim T_1, dim Omega, e,
FO2 bound, dim E_0. * Any polished OTHER space with no full free row and dim Omega >= 3: counterexample to (S6'); save its
basis; if moreover its FO2 bound is >= 9 it is a genuine candidate for L_r (then run section 5 seeded with it). * A polished
OTHER space with dim Omega <= 2: (S6') survives, the F/NC dichotomy does not; save it. * Any 7-dim 4x5 level space: save it
(none is known; it would decide whether a_r = 3 is vacuous), and report dim Omega (need <= 2).

## 2. Census B: unseeded / lightly seeded census on Gr(6,20) and Gr(7,20)

System. Unknown: 6-dim (7-dim) subspace of C^20, chart W in C^{6x14} (C^{7x13}). Equations: P_1 = .. = P_4 = 0 on it
(6 + 21 + 56 + 126 = 209 coefficient equations for dim 6; sampled). Code: rows/clm.py, class Problem(4, d, 'level', 0, seed=s),
`z, c = solve(P, iters=...)`, `Z = P.basis(z)` (see rows/lev45.py, which also shows seeded starts `start_level`). In this
container unseeded starts NEVER reach a 6-dim space (0 of 10 at 300 iterations), so: 2*10^4 starts, >= 2000 iterations,
plus starts seeded at (random k-dim subspace of a known 6-dim space) + random, k = 0..5.
Calibration that must succeed first: the same code must find (a) 5-dim level spaces from unseeded starts at a measurable rate
and (b) 6-dim spaces from "5-dim subspace of a known 6-dim space + random direction" (rate here: 3 of 15). Report the rates.
Output and decision: classify every solution exactly as in section 1 (ext6.classify after polishing). This is the only test of
(S6') that is not biased towards the neighbourhoods of the known spaces. Dimension 7: any solution is a new object.
Optional strata (smaller systems, same code with a restricted ambient space, see class Mult4 in rows/lev45.py): spaces with a
prescribed single-row part of dimension u in {0,1,2,3} in a prescribed row (upstream's case tree for "4x5 level <= 7" is
organised by these u_i), and spaces with all four row projections of dimension <= 3.

## 3. Census C: direct attack on (S6') -- 6-dim level spaces with dim Omega >= 3 (and the 9-dim first-order system)

System. Unknowns: M (6-dim subspace of C^{4x5}, chart 84 unknowns) and k matrices t_a = (X_a ; rho_a) in C^{5x5}, a = 1..k,
with X_a taken modulo M (14 unknowns each) and rho_a in the sum-zero vectors of C^5, (rho_1..rho_k) in a chart of Gr(k,4)
(this normalisation removes the trivial direction tau = (J' ; -4,-4,-4,-4,-4), which is in T_1(M) for every M).
Equations: (level) F(c J' + Y) = 120 c^4 for all c in C, Y in M; (first order) sum_{ij} t_a[i,j] cof(c J + (Y;0))[i,j] = 0 for
all c, Y in M, a = 1..k. Both are quartic forms in (c, Y): 210 coefficients each; sample >= 400 points of C x M.
k = 2  <=>  dim Omega(M) >= 3;   k = 3  <=>  dim Omega(M) >= 4 (necessary for M = L_r with a_r = 2).
No script yet; building blocks: ext6.F45 / perm5 (level residual), stage2/r5_FO2.cof55 and hess (first-order residual and its
Y-derivative), an LM loop as in ext6.solve_ext (replace the finite-difference Jacobian by the analytic one).
Calibration that must succeed first: k = 2 seeded at ../rows/rc45.npy perturbed by 1e-2 .. 1e-1 must return to a Type F space
(rc45 has dim Omega = 3); k = 3 seeded at reg2/M_L080_col0.npy or reg2/M_ex2_row4.npy (Type F, Omega = C^5) likewise; then
unseeded and broadly seeded starts (all 6-dim spaces found in sections 1-2, perturbed).
Output and decision: every solution is tested for a full free row (ext6.classify). A solution WITHOUT a full free row is a
counterexample to (S6') (k = 2) / to "dim Omega <= 3" (k = 3): save it and compute its FO2 bound. Only Type F solutions in a
large calibrated run = strong evidence that the regime is closed.

## 4. Exact computations

(a) Exact Omega on exact spaces (proves the Type NC / Type F invariants on them). T_1(M) for a basis B_1..B_d with entries in
Q or Q(w), w = primitive cube root of 1: expand sum_{ij} t[i,j] cof(J + sum_k c_k (B_k;0))[i,j] as a polynomial in c_1..c_d
with coefficients linear in t; T_1 = common kernel of the <= 210 coefficient forms (a 210 x 25 matrix over the field; exact
rank). Omega = projection to t[4,*]. Spaces: the line-kernels of L080 (integer entries; chief/core.py, core.SP['L080']; rows
0-3 give Type NC with neutral column 4, columns 0-3 give Type F with Omega = C^5), of ex1 (Z[w]; split/exact7.py), rc45
(rows/lev45.py, function rc45()), and the exact family of (b).
(b) An exact Type NC FAMILY (hand-proved level, NOTES-reg2 section 2.5; reg2/fam_nc.py builds it): w0, w1, w3 in C^4 with
sum w_i = 0, <w_i, w_j> = 0 for i != j (bilinear dot product), sum_c w0_c w1_c w3_c = 0, and
   M(w0,w1,w3) := { x e_0^T : x in C^4, sum x = 0 }  (+)  C e_0 (0,w0)^T (+) C e_1 (0,w1)^T (+) C e_3 (0,w3)^T
(vectors (0,w) live in columns 1..4). Column 0 is neutral. Rational member: w0 = (1,-1,0,0), w1 = (0,0,1,-1), w3 = (1,1,-1,-1)
(checked: dim T_1 = 9, Omega = span(1, e_0), FO2 bound 7). Wanted: over R = Q[w0,w1,w3]/(the five relations above; decompose
into prime components first), the exact rank of the coefficient matrix of (a) on each component (generic rank and the locus
where it drops): proves "(S6') on the whole family" or exhibits the special members with larger Omega.
(c) Exact local classification: for an exact 5-dim level space M_5 (e.g. hyperplanes of the spaces in (a), the 5-dim kernels
of ex1 over Q(w)), solve EXACTLY (Groebner / msolve; <= 5 unknowns, equations of degree <= 4) the system of section 1 with
m = 1: this lists rigorously all 6-dim level spaces through M_5, and E_0 computed exactly gives q.
    A working exact prototype for (a): `python3 -I exact_T1.py` (pure Fractions; evaluates cof at 260 integer points, exact rank
    and exact kernel; already certifies Omega inside span(1,e_c) for the L080 row-0 kernel and the rational member of (b)).
(d) The same for dimension 7 over each exact 6-dim space: E_0(M) = M (+) C d always so far; exact check that P_2(d) != 0
proves that M lies in no 7-dim 4x5 level space.

## 5. Census D: the regime itself (5x5), dimension 8

System. An 8-dim level space L of 5x5 matrices (perm(J + t) = 120, i.e. P_1..P_5 = 0 on L) whose row 4 takes values in a
2-dim subspace W of C^5 -- equivalently dim L_4 = 6. (A 9-dim level space with a_r = 2 contains such an 8-dim space; no
8-dim level space of any kind is known.) Unknowns: W in Gr(2,5), L in Gr(8, 22) inside {t : row 4 in W}.
Code: /home/claude/work/L-gct-086/smallcases/search.py, extend.py, level.py (LM searches and an exact checker for 5x5
level spaces; read NOTES-infra.md there), restricted to the ambient space above; or section 3 with k = 2 followed by an
exact level search inside M (+) span(t_1, t_2).
Calibration that must succeed first: the analogous problem one step down (7-dim L with row 4 in a 1-dim W, dim L_4 = 6) must
be found from "L_4 of a known 7-dim space + random direction" (targets: L080, ex2, ex3 in chief/core.py).
Output and decision: any 8-dim solution is a major find (send basis + level error at fresh points). None in a calibrated
run: consistent with "dim L_r = 6 => dim L <= 7", which is what (S6') + FL give.

## 6. What decides what (summary)

- polished OTHER 6-dim space, no full free row, dim Omega >= 3, FO2 >= 9  -> candidate L_r; the regime is NOT closed by
  first/second order; run section 5 seeded with it.
- same but FO2 <= 8  -> (S6') false but the regime still dies for this space; (S6') must be replaced by the FO2 statement.
- OTHER with dim Omega <= 2 -> only the F/NC structure conjecture changes.
- a 7-dim 4x5 level space -> new object; needs dim Omega <= 2.
- nothing but F and NC in calibrated censuses A, B, C -> (S6') is the right theorem to prove; exact items 4(a)-(d) then give
  the rigorous base cases, and the proof to look for is: (i) 6-dim => full free row or neutral column, (ii) neutral column and
  dim 6 => Omega = span(1, e_c).
