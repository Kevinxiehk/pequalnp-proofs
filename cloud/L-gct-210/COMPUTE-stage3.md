# COMPUTE-stage3 -- heavy computations that would help (S3) of L-gct-210   (stage3, written 19:31, round 7)
Self-contained. Everything is over C. All scripts named below are in /home/claude/work/L-gct-210/stage3/ and run with
`python3 -I <script> <args>` (numpy/scipy only; they are small and can be copied). Hand proofs they relate to: NOTES-stage3.md, sections
named below. Order = priority. For every numerical item a CALIBRATION is listed that must succeed before a negative result means anything.

## 0. Conventions (used in all items)
 * 5x5 matrices; rows are indexed a,b,c,d,e = 0..4, columns 1..5. J = all-ones matrix. e_r w^T = the matrix with row r equal to w, 0 elsewhere.
 * LEVEL SPACE: a linear subspace L of Mat_5(C) with perm(J + t) = 120 for all t in L. Equivalent (L is linear): sigma_k(t) = 0 for all t
   in L and k = 1..5, where sigma_k(t) = sum of the permanents of ALL k x k submatrices of t  [perm(J + t) = sum_k (5-k)! sigma_k(t)].
   The gap L-gct-210 claims: every level space has dim <= 8. Level spaces of dim 8 exist.
 * SQUAREFREE ALGEBRA A = C[y_1..y_5]/(y_1^2, ..., y_5^2), graded; to v in C^5 attach V = sum_j v_j y_j in A_1. For k vectors v^1..v^k
   (the rows of a k x 5 matrix N):  V^1 ... V^k = sum over k-subsets S of columns of perm(N restricted to the columns S) * y_S.
   So "V^1 V^2 V^3 V^4 = 0 in A_4" means: the five 4x4 subpermanents of the 4x5 matrix N vanish; "= 0 in A_3" : the ten 3x3 subpermanents.
   For subspaces P_1..P_k of C^5: "P_1 ... P_k = 0" means the product vanishes for all choices v^i in P_i (enough: basis vectors, the
   product is multilinear). "u . P_1 ... P_k = 0" (u a vector) likewise. eps: A_k -> C = sum of all coefficients.
   s(v) = sum_j v_j;  <u,v> = sum_j u_j v_j (bilinear, NO conjugation);  1 = (1,1,1,1,1);  1^perp = {s = 0}.
 * For a subspace L: pi_r(L) = set of r-th rows; a_r = 5 - dim pi_r(L); L_r = {t in L : row r = 0}; X_{rr'} = {rows r, r' = 0},
   lam_{rr'} = dim X_{rr'}; Z_r = {w : e_r w^T in L}, z_r = dim Z_r (single-row elements; always s(w) = 0); a "2-row element on (k,l)" is a
   t in L with all rows except k, l equal to 0.
 * THE REGIME OF (S3): L level, dim 9, all a_r = 1 (every pi_r(L) is 4-dim; then dim L_r = 5), all lam_{rr'} >= 3, and z != 0.
   Proved by hand so far: z = 0 is impossible; z = (1,0,0,0,0) is impossible unless lam = 4 for two disjoint row pairs (family F4b, item 3);
   two entries z_i = 2 are impossible unless both planes Z_i are degenerate for <,>. OPEN: z_e = 2 (item 1, 2), F4b (item 3), several
   rows with single-row elements (item 4).
 * FIRST-ORDER SPACE AND FO2 (stage2, NOTES-stage2.md R5; library verify2/fo2lib.py). For a level space M:
     T_1(M) = { t in Mat_5 : sum_{ij} t_ij C_ij(J + m) = 0 for all m in M },  C_ij(B) = permanent of B with row i and column j deleted
   (so d/ds perm(J+m+st) at s=0 is that sum). q_m(t) = second derivative d^2/ds^2 perm(J + m + s t) at s = 0 (a quadratic form in t).
   Every level L containing M satisfies: L inside T_1(M), q_m = 0 on L for all m in M, and M lies in the radical of q_m restricted to
   T_1(M). Hence dim L <= dim M + (largest dim of a subspace of T_1(M)/M that is isotropic for ALL q_m, m in M)
                        <= dim T_1(M) - ceil( rank(q_m on T_1(M)/M) / 2 ) for every single m.
 * Generic numerical recipe used in all my scripts: unknown vectors as complex numbers split into real and imaginary parts, residual =
   all equations + gauge fixing (orthonormal bases) + one-sided hinge penalties wt*max(0, delta - quantity) for the open conditions;
   scipy.optimize.least_squares(method='lm'); a start counts as a solution if sqrt(2*cost) < 1e-8, then it is polished and classified
   by ranks (tolerance 1e-6). On the big machine: analytic Jacobians (or jax/autodiff), >= 2000 starts per configuration, and every
   claimed solution re-evaluated at fresh random points in 50-digit arithmetic (mpmath) before it is believed.

## 1. (top priority) DIRECT SEARCH: a 9-dim level space containing a 2-dim single-row part  [decides (S3-a) numerically; could refute the gap]
 SYSTEM. Unknowns: z_1, z_2 in 1^perp (independent), t_1, ..., t_7 in Mat_5.  L := span(e_e z_1^T, e_e z_2^T, t_1, ..., t_7), required of dim 9.
   Equations: perm(J + x) = 120 identically on L, i.e. all coefficients of the polynomials sigma_k(sum_i c_i b_i), k = 2..5, in the 9
   coordinates c vanish (45 + 165 + 495 + 1287 = 1992 equations), plus sigma_1: every basis matrix has entry sum 0.
   Cheap equivalent residual: (perm(J + x_n) - 120) for N = 4000 fixed random points x_n = sum_i c_{n,i} b_i (c complex Gaussian, |c| ~ 1).
   Gauge: row e of t_i orthogonal (Hermitian) to z_1, z_2; (t_i) orthonormal for the Hermitian Frobenius product; z_1, z_2 orthonormal.
   Runs: (i) no further condition; (ii) with hinges "all a_r = 1": the 4th singular value of the 9x5 matrix of r-th rows >= 0.2, for r = a..d
   and for r = e.
 CALIBRATION (must succeed first): the same code with t_1..t_5 only (dim 7) must find solutions in a positive fraction of starts:
   the 7-dim spaces M = L' (+) e_e (x) (C(L') + C1)^perp built from a 4x5 level space L' with 2-dim defect are known solutions
   (/home/claude/work/L-gct-210/rows/build7.py, data rows/c52_*.npy; my check stage3/t1_defect.py lists them). Then run dim 8
   (t_1..t_6) and REPORT whether 8-dim level spaces with z_e = 2 exist and their invariants (a_r, lam, z, column analogues).
 DECISION. A dim-9 solution verified in high precision (then rationalised or certified by alpha-theory) REFUTES L-gct-210 -- report
   immediately with the matrices. No solution in >= 2000 starts for (i) and (ii) while dim 7/8 calibrate: strong evidence for (S3-a);
   then item 2 is the route to a proof.
 Start from: stage3/s3_planes_z2.py for the least-squares skeleton (unpack / residual / hinges / classification), numerics/core.py.
 SAME SEARCH for the whole of (S3): replace e_e (x) span(z_1,z_2) by ONE single-row element e_e w^T (w in 1^perp, not a multiple of
   e_j - e_l is NOT assumed) and 8 free matrices; calibration at dim 8. This covers every z-pattern at once.

## 2. THE 7-DIM CORES OF (S3-a): sample the variety, test the missing identity, run FO2   [route to a PROOF of (S3-a)]
 Facts proved by hand (NOTES-stage3.md 24 (C), 26 (C)): if L is in the regime with z_e = 2, Z := Z_e, R = {a,b,c,d}, then
   M := L_e (+) e_e (x) Z is a 7-dim level space, L_e (rows a..d, dim 5) has dim pi_r(L_e) = 2 for r in R (planes P_r), and
   (CA2)  Xi_a Xi_b Xi_c Xi_d = 0 in A_4 for every xi in L_e (xi_r = its rows);    (Q4R) P_a P_b P_c P_d = 0 in A_4;
   (CZ)   z . Xi_k Xi_l Xi_m = 0 in A_4 for z in Z and xi in L_e with xi_r = 0 ({k,l,m} = R - r);
   (PR)   P_r . Xi_k Xi_l Xi_m = 0 in A_4 for the same xi;
   (ORT)  <xi_a + xi_b + xi_c + xi_d, z> = 0 for xi in L_e, z in Z;  Z inside 1^perp;
   every L_e cap {row r = 0} is 3-dim; L_e contains no single-row element; for every pair k,l in R the space of 2-row elements of L_e
   on (k,l) has dim 1 or 2, and the pairs with dim 2 are disjoint.
 SYSTEM. Unknowns: bases (u_r, v_r) of P_r (r in R; 8 vectors in C^5), a 5x8 matrix Gamma (L_e = row space of Gamma inside
   (+)_r e_r (x) P_r = C^8), z_1, z_2 in 1^perp. Equations: M level (sigma_2..sigma_5 on the 7 coordinates: 28 + 84 + 210 + 462
   coefficients) and (CA2) (70 quartic coefficients x 5). The other items of the list are consequences on a solution or cheap to add.
   Hinges: rank conditions above (singular values >= 0.2). Gauge: orthonormal bases, Gamma with orthonormal rows.
 WHAT TO COMPUTE for every solution found (>= 2000 starts; cluster the solutions by the discrete invariants m_kl, column supports,
   dim T_1): (a) the 2-row elements x^{kl} = e_k p_kl^T + e_l p_lk^T of L_e and, for each triple {k,l,m}, the two CYCLIC PRODUCTS
   z . p_kl p_lm p_mk and z . p_km p_lk p_ml in A_4 (z in Z)   [hand result: their SUM vanishes; the hand proof of (S3-a) needs each
   of them to vanish -- then the plane lemma of sections 12/15 applies to (P_a,P_b,P_c,P_d,Z)];
   (b) whether the full (Q4) Z P_k P_l P_m = 0 holds for the four triples;   (c) dim T_1(M) and the FO2 bound of section 0: the largest
   common isotropic subspace of T_1(M)/M for the forms q_m (take 10 random m in M; a 2-dim common isotropic subspace exists iff a
   small polynomial system in Gr(2, T_1/M) is solvable -- trivial when dim T_1(M) <= 8).
 DECISION. If every core has dim T_1(M) <= 8, or no 2-dim common isotropic subspace: (S3-a) holds numerically, and the stratification
   (which m_kl-pattern, which column supports) tells which exact statement to prove; please then try the exact version on each stratum
   (Groebner over Q or F_32003: ideal of the core equations, saturated by the hinge minors, + "T_1(M) has dim >= 9" as rank
   condition -> expect the unit ideal). If some core has cyclic products != 0 but T_1 small: the cyclic identity is NOT a property of
   M and the proof must use L/M (FO2). If a core passes FO2 with a 2-dim isotropic subspace: feed it as a start into item 1.
 CALIBRATION: with (CA2) switched off the search must reproduce the three (5,2)-based spaces of rows (stage3/core_check.py shows that
   they violate (CA2) on two row kernels) and dim T_1 = 8 for them (stage3/t1_defect.py; command: python3 -I t1_defect.py).
 WEAKENED PLANE PROBLEM (the abstract form I could not run here: 148 real unknowns, 6.6 ms per evaluation, finite-difference Jacobian):
   stage3/s3_planes_z2.py, command `python3 -I s3_planes_z2.py SEED DELTA NVAN TIMELIMIT MAXNFEV` (e.g. 1 0.2 0 3000 3000).
   Unknowns: planes P_a..P_d, Z (2x5 each) and marked vectors p_kl in P_k (12 of them; p_kl, p_km independent). Equations:
   (Q4R); for each triple {k,l,m} of R: z . p_kl p_lk P_m = 0 and its two analogues, z . (p_kl p_lm p_mk + p_km p_lk p_ml) = 0.
   ADD (not in the script; all proved): sum_{l != k} p_kl = 0 for every k (the one linear relation among the six x^{kl}, after
   rescaling them, pattern "all m_kl = 1"); (PR) with p's in place of xi; (ORT): <p_kl + p_lk, z> = 0, s(p_kl) + s(p_lk) = 0,
   s(p_kl) s(p_lk) = <p_kl, p_lk>; Z inside 1^perp. Hinges: all ten triple products of the five planes nonzero (norm >= DELTA),
   at most NVAN columns vanish on all five planes. Output wanted: for each solution the line the script prints ("full Q4 for the 4 sets
   with Z: n of 4", number of planes equal to one coordinate plane, columns used). DECISION: if all solutions have full (Q4) (n = 4)
   the missing identity is a consequence of this system -> ask for the exact ideal membership "z . p_kl p_lm p_mk in the radical of
   (system) saturated by the hinges"; if solutions with n < 4 exist, the extra input must come from item 2 (c).

## 3. FAMILY F4b (z = (1,0,0,0,0), lam_ab = lam_cd = 4)   [the only open family with exactly one single-row direction]
 Proved structure (NOTES-stage3.md 26 (A5)): there are vectors y_a, y_b, y_c, y_d, p, w, g_a, g_b, g_c, g_d in C^5 with
   M = { sum_{r in R} c_r e_r y_r^T + (sum_r c_r) e_e p^T + mu e_e w^T + ga (e_a g_a^T + e_b g_b^T) + de (e_c g_c^T + e_d g_d^T) }
   a 7-dim level subspace of L (coordinates c_a, c_b, c_c, c_d, mu, ga, de); (y_r, g_r) independent for each r; (w, p) independent;
   s(w) = 0; w orthogonal to y_r and to g_a + g_b, g_c + g_d; L/M is 2-dim and for every r the map L/M -> C^5 / pi_r(M) is injective.
 NECESSARY IDENTITIES in A_4 (from the 9-dim L, NOT from M alone; P_r := span(y_r, g_r) for r in R, P_e := span(w, p)):
   (i)   P_a P_b P_c P_d = 0;      (ii)  y_a . P_c P_d P_e = 0  and  y_b . P_c P_d P_e = 0;      (iii) y_c . P_a P_b P_e = 0  and  y_d . P_a P_b P_e = 0.
 SYSTEM A (core): the ten vectors (50 unknowns); equations: M level (784 coefficient equations as in item 2) AND (i), (ii), (iii)
   (16 + 16 + 16 products, 5 coefficients each). Hinges: the independences above (second singular value of the normalised pairs >= 0.3,
   all ten vectors of norm >= 0.3 after the normalisation |p|^2 + sum |y_r|^2 = 5, |w| = 1, |g_a|^2 + |g_b|^2 = |g_c|^2 + |g_d|^2 = 2).
 SYSTEM B (full): add t_1, t_2 in Mat_5; equations: L = M + C t_1 + C t_2 level (1992 equations); hinges: all a_r = 1 for L, t_i away from M.
 WHY (i)-(iii) MUST BE IMPOSED: M alone can be level. EXPLICIT EXAMPLE M_0 (exact; stage3/f4b_example.py checks perm(J+m) = 120 at 900
   random points with coefficients in Z[omega], omega = exp(2 pi i/3)):  y_r = e_1 (all r), p = -e_1, w = (0,-1,-1,3,-1),
   g_a = -g_b = n := (0,1,omega^2,0,omega),  g_c = -g_d = n' := (0,1,omega,0,omega^2).  M_0 = (free column 1) (+) C e_e w^T (+)
   C (e_a - e_b) n^T (+) C (e_c - e_d) n'^T is a 7-dim level space with z = (0,0,0,0,1), lam_ab = lam_cd = 4, all other lam = 3
   -- exactly the invariants of the F4b core. It violates (iii) (y_c . g_a g_b w != 0) and has dim T_1(M_0) = 8.
 Method: numerical, >= 2000 starts each. CALIBRATION for A: with (i)-(iii) switched off the search must find M_0-like solutions
   (here: script stage3/f4b_core.py / f4b_run.py, `python3 -I f4b_run.py SEED TIMELIMIT`; my 7 hinged starts without (i)-(iii) found
   none, residual floor 0.03-0.14, so the plain LM has a low success rate on this system -- use many starts / better globalisation;
   the free-column sub-family below is found in 1 of 14 starts).
 DECISION: no solution of A -> F4b is impossible at the level of (core + identities); then an exact elimination would be a proof.
   Solutions of A but none of B -> compute T_1(M) and the FO2 bound on the solutions of A as in item 2 (c). A solution of B refutes the gap.
 EXACT SUB-PROBLEM (small enough for Groebner/primary decomposition): the FREE-COLUMN SUB-FAMILY y_a = y_b = y_c = y_d = e_1.
   Proved by hand: then p = -e_1 + p', and w, p', q_r := g_r (r in R) are vectors of C^N, N = {2,3,4,5}, with coordinate sum 0, q_r != 0,
   w != 0 (18 unknowns up to scaling). Equations: M level; (i') the four triple products q_k q_l q_m = 0 in (A_N)_3 and
   q_a q_b q_c q_d = 0 in (A_N)_4; (ii'),(iii') q_a q_b w = q_c q_d w = q_a q_b p' = q_c q_d p' = 0 in (A_N)_3.
   Script: stage3/f4b_fc.py, `python3 -I f4b_fc.py SEED TIMELIMIT 1 ID` (ID = 1 imposes (i')-(iii'); here ID = 0: 1 solution (M_0)
   in 14 starts; ID = 1: 0 in 8 starts, residual floor 0.58). Wanted: exact decision "the system with ID = 1 has no solution with
   all q_r != 0 and w != 0".

## 4. SEVERAL ROWS WITH SINGLE-ROW ELEMENTS (z = (1,1,*,*,*), (2,1,*,*,*), (2,2,..) with degenerate planes) -- not analysed by hand
 Direct search as in item 1 with prescribed single-row elements e_e w^T and e_d w'^T (two different rows; proved: s(w) = s(w') = 0 and
   <w,w'> = 0), 7 free matrices, dim 9; hinges all a_r = 1. Calibration at dim 8 (report which z-vectors occur among 8-dim spaces).
   Variant "degenerate planes": e_e (x) Z and e_d (x) Z' with <,> degenerate on both 2-planes (Z = span(n, h), Z' = span(n, h'),
   <n,n> = <n,h> = <n,h'> = <h,h'> = 0, s = 0 on all), 5 free matrices. Proved for this variant (NOTES-stage3.md 26 (B'), Lemma DEG):
   every element of L with rows d, e equal to 0 has all ten 3x3 subpermanents equal to 0; in the main sub-case L contains 2-row elements
   t = e_b u^T + e_c (mu n - u)^T, t' = e_c v^T + e_a (mu' n - v)^T, t'' = e_a x^T + e_b (mu'' n - x)^T. SMALL EXACT PROBLEM: unknowns
   n, h, h', u, v, x in C^5 and mu, mu', mu''; equations: the 7-dim space span(t, t', t'') (+) e_d (x) Z' (+) e_e (x) Z is level, and the product
   X_a X_b X_c vanishes identically on span(t, t', t''); hinges: t, t', t'' independent with all six rows nonzero. Expected: no solution.

## 5. EXACT CONFIRMATION OF THE PLANE LEMMAS (hand proofs exist; an exact decision would remove the verification burden)
 All are statements "a quasi-projective set is empty". Suggested exact method: every plane in a Schubert chart (reduced row echelon
   form with pivot columns (i,j); 6 free parameters), use the symmetry S_5 (columns) x permutations of the planes to cut the pivot
   patterns, Groebner basis over F_32003 (and one prime more) of the equations + one Rabinowitsch variable per hinge; expected
   output: the unit ideal in every chart. Numerical alternative: numerical irreducible decomposition (Bertini/PHCpack) of the closed
   system, then test the conclusions on a witness point of every component.
 (5a) PLANE LEMMA (sections 12, 15): five 2-planes P_1..P_5 of C^5 with P_a P_b P_c P_d = 0 in A_4 for all five 4-subsets (5 x 16 x 5
      quartic equations in the basis vectors). CLAIM: either some column vanishes on all five planes, or three of the planes are
      equal to one coordinate plane span(e_j, e_l). (Emptiness of: equations + "no common zero column" + "no three planes equal to
      one coordinate plane".) Numerics here: stage3/test_Q4planes.py (185 of 191 starts converge, all with four planes equal to one
      coordinate plane), test_Q4planes_sep.py (planes forced distinct: 0 of 35).
 (5b) THEOREM PL4 (section 24 (J)): four 2-planes P_a..P_d and a vector w != 0, not a multiple of a unit vector, with
      (Q4) P_a P_b P_c P_d = 0 in A_4;  (QL) w . P_k P_l P_m = 0 in A_4 for the four triples;  (NZ) P_k P_l P_m != 0 in A_3 for the
      four triples. CLAIM: EITHER two of the planes are equal to one coordinate plane C^T (|T| = 2) and w lies in C^T, OR the four
      planes and w lie in one coordinate 3-space. Numerics here: stage3/s3_planes_line.py and s3_planes_lineW.py
      (`python3 -I s3_planes_lineW.py SEED 0.2 NVAN 150 1500`, NVAN = number of columns allowed to vanish; 52 solutions, all of the
      two claimed types).
 (5c) The plane problem of Theorem N2-X (section 21): five 2-planes P_a..P_e, vectors rho_a in P_a, rho_b in P_b, with
      P_a P_b P_k P_l = 0 for {k,l} inside {c,d,e}; rho_a . P_c P_d P_e = 0; rho_b . P_c P_d P_e = 0; all ten triple products of the
      planes nonzero. CLAIM: all five planes lie in one coordinate 3-space. Numerics: stage3/n2_planes.py
      (`python3 -I n2_planes.py SEED 0.25 110 NVAN 1500`; 75 of 76 solutions in 3 columns, none with >= 4 columns).
 (5d) LEMMA 5V: five nonzero vectors of C^4 with all ten triple products zero in (A on 4 variables)_3: three of them are multiples of
      one unit vector, or all five lie in a coordinate 2-plane. (Tiny: 20 unknowns, 40 cubics -- exact primary decomposition is feasible.)
 (5e) Annihilator table of section 21 (exact linear algebra over Q(parameters)); stage3/kcheck.py does it at random rational points.

## 6. What output to send back
 For items 1-4: number of starts, residual quantiles, every solution as .npy (basis matrices), its invariants (dim, a_r, b_c for columns,
 lam for all row pairs, z-vector, m_kl), dim T_1 and the FO2 rank. For item 5: per chart "unit ideal / not", and for "not" a point.
