# COMPUTE-stage3 -- heavy computations that would help (S3) of L-gct-210   (stage3, written 19:31, round 7; errata A1, A2 of
# COMPUTE-ERRATA.md applied 20:20, round 8)
Self-contained. Everything is over C. All scripts named below are in /home/claude/work/L-gct-210/stage3/ and run with
`python3 -I <script> <args>` (numpy/scipy only; they are small and can be copied). Hand proofs they relate to: NOTES-stage3.md, sections
named below. Order = priority. For every numerical item a CALIBRATION is listed that must succeed before a negative result means anything.

## 0. Conventions (used in all items)
 * 5x5 matrices; rows are indexed a,b,c,d,e = 0..4, columns 1..5. J = all-ones matrix. e_r w^T = the matrix with row r equal to w, 0 elsewhere.
 * LEVEL SPACE: a linear subspace L of Mat_5(C) with perm(J + t) = 120 for all t in L. Equivalent (L is linear): sigma_k(t) = 0 for all t
   in L and k = 1..5, where sigma_k(t) = sum of the permanents of ALL k x k submatrices of t  [perm(J + t) = sum_k (5-k)! sigma_k(t)].
   The gap L-gct-210 claims: every level space has dim <= 8. [CORRECTED, errata A1: NO 8-dim level space is known; the largest known
   dimension is 7. So every calibration below is at dim 7; dim 8 is a TARGET: a verified 8-dim level space would be new (it would not
   refute the gap) and must be reported at once.]
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
   two entries z_i = 2 are impossible (Theorem Z22, section 26 (B'), proved at 20:10). OPEN: z_e = 2 (item 1, 2), F4b (item 3), several
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
   (t_1..t_6) as a TARGET (not a calibration): report at once any 8-dim level space with z_e = 2 and its invariants (a_r, lam, z, columns).
 DECISION. A dim-9 solution verified in high precision (then rationalised or certified by alpha-theory) REFUTES L-gct-210 -- report
   immediately with the matrices. No solution in >= 2000 starts for (i) and (ii) while dim 7/8 calibrate: strong evidence for (S3-a);
   then item 2 is the route to a proof.
 Start from: stage3/s3_planes_z2.py for the least-squares skeleton (unpack / residual / hinges / classification), numerics/core.py.
 SAME SEARCH for the whole of (S3): replace e_e (x) span(z_1,z_2) by ONE single-row element e_e w^T (w in 1^perp, not a multiple of
   e_j - e_l is NOT assumed) and 8 free matrices; calibration at dim 7 (6 free matrices; the lifts of rows' (5,2) and (4,1) spaces are known solutions), dim 8 as
   a target. This covers every z-pattern at once.

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
   <w,w'> = 0), 7 free matrices, dim 9; hinges all a_r = 1. Calibration at dim 7 (5 free matrices); dim 8 is a target (report any solution at once).
   Variant "degenerate planes" (e_e (x) Z and e_d (x) Z' with <,> degenerate on both 2-planes): NOW PROVED IMPOSSIBLE by hand
   (Theorem Z22, NOTES-stage3.md 26 (B')); together with rows' FL2* no two rows carry 2-dim single-row parts. A numerical confirmation
   is welcome but has low priority: 9-dim level L containing e_d (x) span(n,h) (+) e_e (x) span(n,h') with <n,n> = <n,h> = <n,h'> =
   <h,h'> = 0 and all sums 0 (5 free matrices) -- expected: no solution; calibration at dim 7 and 8.

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
 (5c) The plane problem of Theorem N2-X (section 21) [CORRECTED, errata A2: the claim "all five planes lie in one coordinate 3-space"
      is FALSE for the plane equations alone; counterexample of verify2: g = e_2 + e_3, g* = e_2 - e_3, P_c = P_d = P_e = span(e_1, g),
      P_a = P_b = span(g*, e_4)]. Five 2-planes P_a..P_e with P_a P_b P_k P_l = 0 in A_4 for the three pairs {k,l} inside {c,d,e} and
      (NT) no three of the five planes equal to one coordinate plane. CORRECT CLAIM (what section 21 proves from these plane equations):
          all five planes lie in one coordinate 3-space,  OR  P_c = P_d = P_e,  OR  two of P_c, P_d, P_e are equal to one coordinate plane.
      Test this three-way conclusion (rho_a, rho_b are not needed for it). The second alternative is excluded in section 21 by (Qb),
      (Q5J) and (P2), which are level conditions of X_ab and not plane equations. Numerics: stage3/n2_planes.py
      (`python3 -I n2_planes.py SEED 0.25 110 NVAN 1500`; its hinge "all ten triple products nonzero" with (Qa), (Qb) imposed:
      75 of 76 solutions in 3 columns).
 (5d) LEMMA 5V: five nonzero vectors of C^4 with all ten triple products zero in (A on 4 variables)_3: three of them are multiples of
      one unit vector, or all five lie in a coordinate 2-plane. (Tiny: 20 unknowns, 40 cubics -- exact primary decomposition is feasible.)
 (5e) Annihilator table of section 21 (exact linear algebra over Q(parameters)); stage3/kcheck.py does it at random rational points.

## 6. What output to send back
 For items 1-4: number of starts, residual quantiles, every solution as .npy (basis matrices), its invariants (dim, a_r, b_c for columns,
 lam for all row pairs, z-vector, m_kl), dim T_1 and the FO2 rank. For item 5: per chart "unit ideal / not", and for "not" a point.

## ROUND 9 UPDATE (stage3, 20:30 UTC) -- items 3 and 4 partly superseded; new items 6, 7
 * ITEM 3 (F4b) IS DONE: Theorem F4b-X (NOTES-stage3.md section 28): moment lemma + exact Singular-over-Q eliminations on all charts
   (stage3/r9/gen9.py, exact9.py, exact9c.py; msolve cross-checks at 3 primes). No further F4b computation is needed.
 * z = (1,0,0,0,0) is therefore impossible; item 1's "same search for the whole of (S3)" only matters for the patterns with a 2-dim single-row
   part (now reduced, item 7) and for single-row elements in >= 2 rows (item 4).
## 6. S3-1 DIRECT SEARCH -- CALIBRATION FINDING AND WHAT TO RUN INSTEAD
 FINDING (NOTES-stage3.md 29 (A)): the known 7-dim lifts are singular points of the sampled level system (Jacobian kernel 11 > tangent
 dimension); LM/Newton converge only linearly there (with or without slices) and stall at 1e-5 .. 1e-8. Random-start LM 0/40 (coordinator),
 seeded 0/3, planted at distance 0.03: floors 3.7e-7, 5.2e-7.  So no plain-LM negative at dim 8/9 is meaningful.
 RUN (if cores are free): (a) planted-distance calibration with long runs, to measure the basin:
     cd /home/kevxhk/work/L-gct-210/stage3/r9 && ITERS=2000 python3 -I s3seed.py near0.1 0 16 0.0 0   (also near0.3, near1.0)
     decision: a start is a HIT if its residual < 1e-7 AND oracle fresh-point error < 1e-6 (the script prints both); report hits / starts.
 (b) only if (a) gives a positive rate at distance >= 0.3: ITERS=2000 python3 -I s3seed.py ext8 0 64 0.0 1 and ext9 (dim-8/9 TARGETS;
     any verified hit = report at once). 1 core per process, ~10 min per start at ITERS=2000.
 (c) better solver (not written): deflation -- augment with J(z) v = 0, <r, v> = 1 (v in the Jacobian kernel) to make singular solutions
     regular; calibrate on the 16 lifts first.
## 7. (S3-a) AND ALL PATTERNS WITH z_e >= 2 (a_e = 1): FIRST-ORDER BOUND FOR (5,2) LIFTS   [route to a proof]
 Reduction (rigorous, NOTES-stage3.md 29 (B)): such an L contains M = L(L_e) for a (5,2) space L_e (or L_e is a (5,1) space, rows' DI_5),
 and L lies in T_1(M). So it suffices that dim T_1(L(L')) <= 8 for every (5,2) space L' (for (S3-a): those without single-row elements).
 Census: 27/27 stored (5,2) spaces have dim T_1 = 8 (stage3/r9/t1_c52.py).  WANTED: (a) the same census on every (5,2) space the C1/R6
 runs produce (cheap: python3 -I t1_c52.py after adding the files); (b) an exact version: parametrise the non-split (5,2) spaces
 (C = V_S, |S| = 3, two neutral columns, per rows' LAW) and decide "rank of the T_1 system >= 17" exactly.

## ROUND 10 UPDATE (stage3, ~21:00 UTC): item 8 = exact (PR2) / normal form (t2)
## 8. (PR2) FOR NORMAL FORM (t2): exclude X0 = Y_ab (+) Y_cd (two 2-dim 2-row level blocks, phi, psi injective) -- kills (t2)
 Reduction (rigorous, NOTES-stage3.md 30 (B), (E)): every (t2) space contains X0; X0's level conditions are (X2)-(X4) of 30 (E);
 expected dimension -3.  Generator: stage3/r10/gen_x0.py (34 variables incl. 2 Rabinowitsch; 1000 charts = 10 Schubert pivot pairs of P_c
 x 10 Pluecker charts of (b1,b2) x 10 of (d1,d2); P_a pivots (0,1) by S_5).
   cd /home/kevxhk/work/L-gct-210/stage3/r10 && python3 -I gen_x0.py 65521 KC_MB_MD      (one chart; or no 2nd argument for all)
 Measured here: one chart (0_0_0) ran > 1 min at ~0.5 GB and growing (see x0_one.log for the final time / memory if it finished).
 RAM: budget >= 3 GB per msolve process (msolve -t 1); do not run more than 3 in parallel on the 12 GB machine.
 Decision: unit on all 1000 charts at 3 primes = strong evidence; then the same over Q (Singular, per-chart, stratified cover for slow
 charts as in round 9). A non-unit chart: print the basis; a genuine X0 would be new (and would have to be checked for extension to (t2)).
 Cheaper alternative (not written): split by dim c(P_a): (ii) some phi v0 = -v0 (basis vector with b1 = -v1: 5 fewer unknowns);
 (i) dim c(P_a) = dim c'(P_c) = 2: add Q(P_a) inside c(P_a), c'(P_c) = c(P_a)^perp cap 1^perp (more equations, usually faster).
## 9. CALIBRATED PROBES FOR (PR2) AND (PR2-split') (round 10; cheap, ~150 MB RAM per process)
   cd /home/kevxhk/work/L-gct-210/stage3/r10 && python3 -I pr2split_search.py SEED 200 1     (target: L' = X (+) e_d (x) Z, no single-row element in rows a,b,c)
   cd /home/kevxhk/work/L-gct-210/stage3/r9  && python3 -I pr2_search.py SEED 200 1          (target: all row projections 2, no single-row element)
 CALIBRATION (same scripts with last argument 0): pr2split 2 hits in the first 3 starts (shape (2,1,0,0)/(2,2,2,2)); pr2_search 1 in 21.
 Rate here: ~40 s per start per core. Suggested: 4 cores x 2 h (SEEDS 100..103 for each script), plus one calibration seed each.
 DECISION: a target hit with fresh-point error < 1e-7 refutes (PR2) resp. (PR2-split') -- report it, then run r10/t1_census5.py on it:
 only dim T_1 >= 10 matters for the gap (row-kernel bound, NOTES-stage3.md 30 (I)). No hit in 800 starts per script = evidence for both.
 Saved solutions: r9/pr2_sol_*.npy, r10/pr2split_sol_*.npy (also the calibration (2,1,0,0) spaces -- run t1_census5.py on all of them:
 so far dim T_1 = 9 for every one, which excludes them as L_r of a 9-dim level space in the mixed pattern (2,1,..)).

## ROUND 11 UPDATE (stage3, 21:35 UTC)
## 10. THE (5,1) PROBLEM FOR ONE DEFECT LINE: m0 = (1,1,1,1,-4)  [decides Lemma PFC => all partial-free-column spaces, incl. the ncdef family]
 Statement wanted: there is no 5-dim 4x5 level space whose deletion vectors all lie in C(1,1,1,1,-4) (+ C1). By NOTES-stage3.md 31 (F) this
 implies: every level space containing a free column on four rows has dim <= 8 (exactly as SL gives Theorem FL for a full free column).
 m0 is non-isotropic (<m0,m0> = 20), |supp| = 5, invariant under S_4 on columns 0..3: verifyfl's open stratum (DI5-R4 (o1)/(o2)).
 Suggested method: verifyfl's typed systems [DC3], [T22], [T31] for this m (gen_dc covers |supp m| = 4, 5) plus the principal stratum
 (Theorem PS / N-problem); the S_4 symmetry should cut the charts. Owner: verifyfl (their generators), or stage3 next round.
## 11. ncdef FAMILY, remaining strata (only if item 10 is not done): the exact pipeline stage3/r11/ncdef_exact2.py W2 W3 TAG +
 plane_check.py TAG proves "no level space of dim >= 8 contains N(W2,W3)" for one rational member in < 1 min (RAM < 100 MB). Done for three
 members of the jump locus H. A full proof needs the generic stratum (dim T_1 = 10: one form of rank 5 on T_1/N) and the special
 sub-loci of H and D parametrically -- item 10 is the cleaner route.

## ROUND 12 UPDATE (stage3, ~22:05 UTC)
## 12. [T31] SPLIT A FOR m0 = (1,1,1,1,-4): CASE LIST AND NORMAL FORMS (for verifyfl's generators; derivations NOTES-stage3.md sec. 32)
 Split A = vartheta(Z) = 0 (all five columns of Z isotropic, sum 0); split B is verifyfl's Theorem [T31-B] (R8.8).
 Lemma SA1 (rigorous): l := Theta(., Z) == 0 on K  <=>  Z has a zero column, and then z_4 = 0. So exactly two cases:
  (alpha) Z = [W | 0] (W 4x4 doubly centred, isotropic columns: supports {a,b} (W = v (e_a - e_b)^T), {a,b,c} (W = v l^T, l zero-sum) or all
          four), l == 0, i.e. the LINEAR equations <b_j(Y), z_j> = 0 for all j and all Y in K. With b_j = A_j s on a complement K':
          A_j^* z_j = 0, A_j^*A_j = P_1 (j <= 3) with rank P_1 <= 1, A_4^*A_4 = 5 - 4 P_1, sum A_j = -3.
          (alpha0) P_1 = 0: y_j = (s + <phi_j,s> n_j)/2 (j <= 3), y_4 = -s - (1/2) sum <phi_j,s> n_j, n_j = z_j on supp W, n_j isotropic otherwise;
                   gauge: phi_j -> phi_j + 2 lam on supp W (set phi_a = 0 for one a in supp W); phi's span V. Unknowns ~17 (supp = all four).
          (alpha1) rank P_1 = 1: P_1 = f (x) f (f in V, possibly isotropic), each A_j (j <= 3) of rank <= 2 with A_j(V) inside z_j^perp.
  (beta)  all columns nonzero, l != 0. (beta-1) rank-one Z: EXCLUDED (hand + exact, r12/beta1.sing). (beta-2) (u,v)-coordinates of the columns
          span a maximal isotropic plane of C^5: Z-ONLY system r12/zbeta_uv.py (charts of (u_j,v_j) != 0); too heavy unreduced here (Singular
          > 3 min, 630 MB; msolve segfault) -> needs the OG(2,5) = P^3 parametrisation or verifyfl's staging. Numerically: see sec. 32 (F).
 Decision: (alpha0), (alpha1), (beta-2) all UNIT at one prime p > 5 (Lemma RED-p applies: char-p case split) => [T31-A] for m0
 => with [T31-B] (done), [DC3] (running, p5b) and [T22] (gen_n3g): (SL_m0) => no (5,1) with line m0 => Lemma PFC => the ncdef family and
 every partial-free-column space have dim <= 8.
 (beta-2) RECOMMENDED FORMULATION: z_j = c_j w(t_j), w(t) = chi_1 + 2t chi_2 - 2t^2 chi_3 (charts u_j != 0; the point t = infinity, z = chi_3,
 in separate charts); sum z_j = 0 <=> sum c_j = sum c_j t_j = sum c_j t_j^2 = 0 (LINEAR in c), so c = al c1(t) + be c2(t) on the 2-dim kernel;
 unknowns t_0..t_4, (al:be): 6 projective parameters against the 8 line conditions (expected dimension -2); nonzero columns = c_j != 0.
 The S_4 row symmetry acts on the conic by a finite group (cuts the t-charts). Coefficients in Q(i).
## ROUND 13 UPDATE (stage3, 22:40 UTC): item 12 (alpha0) is DONE by hand + exact (NOTES-stage3.md sec. 33 (D)-(J): Lemma S-SPEC, the unique
 special W for |supp| = 4, 36 systems for |supp| = 3, the v-free plane P2 for |supp| = 2; all unit over Q(i), calibrated). verifyfl: skip
 (alpha0); still needed: (alpha1) (rank P_1 = 1) and (beta-2).

## 13. CUTS FOR verifyfl's m0 (alpha) CHARTS (gen_m0a.build_alpha_kt / build_alpha_r1)  [stage3 round 15; all rigorous, valid in char p > 5]
 Notation as in gen_m0a: columns of W are z_j = k_j n_j, n_j = w(t_j) = chi_1 + 2 t_j chi_2 - 2 t_j^2 chi_3 or n_j = chi_3 (t_j = inf), z_4 = 0.
 (C1) RANK-ONE W = v l^T WITH THREE NONZERO ENTRIES (|supp l| = 3): v is SPECIAL, i.e. p_3(v) = sum_r v_r^3 = 0 (v is a row permutation of chi_1).
      Proof: rank-one expansion perm(J + t v l'^T) = sum_k (4-k)! k! t^k e_k(v) e_k(l'); the t^3 vector (e_3(l^(j)))_j = (0,0,0,l_0l_1l_2,l_0l_1l_2)
      is not ~ m0, so e_3(v) = 0 (e_1 = e_2 = 0 by isotropy). In build_alpha_r1: replace the chart v = w(t) by v = chi_1 (WLOG by the row S_4,
      transitive on the 6 special lines) whenever l has three nonzero entries; the two-entry case l = (1,-1,0,0) keeps v = w(t) (and then K contains
      the v-free plane P2 of NOTES-stage3 sec. 33 (J) when P_1 = 0).
 (C2) |supp W| = 4: ALL FOUR triple moments of W vanish (z_4 = 0 makes T_4 = sum_j T_j = 4T = -4T) and perm(W) = 0. Explicit (factor 8 k_a k_b k_c dropped):
        tau(z_a,z_b,z_c) ~ g(t_a,t_b,t_c) = (t_a+t_b+t_c) + 4 (t_a t_b + t_b t_c + t_a t_c) t_a t_b t_c      (all finite),
                          ~ -2 t_a t_b (t_a + t_b)                                                       (t_c = inf),
                          ~ t_a                                                                          (t_b = t_c = inf),
                          = 0                                                                            (all three inf);
      perm(W) = sum over the 3 pairings <z_a,z_b><z_c,z_d> - 6 sum_r prod_j (z_j)_r, with <w(s),w(t)> = -8 (s-t)^2, <w(t),chi_3> = 4, <chi_3,chi_3> = 0.
      These are consequences of the Zs line conditions (already in the system) -- adding them explicitly before the plane stage Z+Y_1 typically
      shrinks the Zs-GB (the four g's cut the t-space to one 2-dim component + points, NOTES-stage3 sec. 33 (C)).
 (C3) (alpha0) (P_1 = 0) is DONE (char 0 and P1); only (alpha1) (P_1 = k f (x) f, k != 0) remains. In (alpha1) the K'-data have the normal form
      A_j = n_j (x) psi_j + eps_j rho e_j (x) f (e_j = chi_2/2 - t_j chi_3, resp. chi_2/2 for n_j = chi_3; rho^2 = k), stage3/r14/alpha1_gen.py, and
      |supp W| = 3 is DONE (96/96 unit, char 0 and P1). Open: |supp W| = 2 and 4.
 UPDATE 13 (round 15, 23:45): (alpha1) |supp W| = 2 and 4 are CLOSED at P1 by hand + small systems (NOTES-stage3 sec. 35): LEMMA S2 (shape S2
      with b2, b3 != 0 forces b2 = b3; unit at P1, r15/s2l_{neq,par}{1,2,3}_p.sing) gives |supp 4| by a point-configuration argument
      and reduces |supp 2| to two 7-unknown systems (r15/s2red.py; 12/12 unit over Q and at P1). So ALL of (alpha) is unit at P1:
      verifyfl's (alpha) KT charts for m0 are now a CROSS-CHECK, not a needed piece; RED-p needs only [DC3] and [T22] at P1 in addition.
      Still open for an independent char-0 proof of (alpha): Lemma S2 over Q (running, r15/run_s2q.sh; heavy over Q, instant at P1).
 REPRODUCE sec. 35 (cwd stage3/r15): python3 -I chilib.py (self-check vs brute-force permanents);
      Lemma S2: python3 -I s2lemma.py {neq|par} K P (K = a-chart 1..3, P = 0 or 2147483629) -> s2l_{neq|par}K_{q|p}.sing; Singular -q (at P1 std,
      over Q use slimgb: s2l_*_qs.sing); calibration: python3 -I s2lemma.py cal 1 2147483629 (non-unit, dim 1).
      |supp 2| reduced systems: ./run_red.sh -> red.log (12 + 12 systems + calibrations d2/d3/line/line0).

## 14. (PR3) STRATUM (II) and LEAF 8 -- specs for the big slot  [stage3 round 16]
 (a) (PR3) stratum (II), sub-case dim Delta = 2 (NOTES-stage3 sec. 36 (B), (F)): unknowns h_0, h_1, h_2 (Delta-chart of r16/strat2b.py:
     h_2 = k, h_0 = k + l0 f_0 + m0 f_1, h_1 = k + l1 f_0 + m1 f_1, f_0 = (1,0,p2,p3,*), f_1 = (0,1,q2,q3,*)) and x* = (r_0, r_1, -r_0 - r_1)
     (WLOG zero column sums); equations: all (a,b,d)-coefficients of sigma_1..3 on x = (a h_0, b h_1, (-a-b) h_2) + d x*, and the Delta-membership
     of every coefficient vector of c, D_2, D_3 (entries 2,3,4 of v - v_0 f_0 - v_1 f_1); hinges u (l0 m1 - l1 m0) = 1 and r_i not parallel to h_i
     (stratum condition; charts on 2x2 minors). Normalisation s(k) = 1 or (s(k) = 0, det = 1). Expected UNIT; must be EXACT over Q
     ((PR3) has an open hypothesis -- no single-row element -- and its closed variety is non-empty (the (2,1,0,0) examples), so RED-p does
     not apply). The H-part alone is NOT unit (4-dim family): calibrate with it.
 (b) Leaf 8: closed by hand + small exact checks: (1,1,1,1,1), (2,1,1,1,1) (Theorem SR5), (2,1,1,1,0) (Theorem SR2111). Open:
     (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0) -- they need the regime (single-row level conditions alone are satisfiable,
     e.g. the Fourier family on four rows, or an orthogonal basis like e_0 - e_1, e_2 - e_3, (1,1,-1,-1,0), (1,1,1,1,-4)).
 Reproduce: cwd stage3/r16: python3 -I srow32.py 0 {0|1} (+ calibrations '0 1 2 2', '0 1 3 1', '0 1 2 1'); python3 -I srow2111.py 0 k j
     (k = 0..4, j = 1..4); Singular -q <file>.
 UPDATE 14 (round 17): (a) MUST NOT be run as written -- its variety contains the stratum-(III) counterexample family of NOTES-stage3
      sec. 37 (E) (no row hinges), so it is non-unit by construction; (PR3) itself is FALSE (only (PR3') = strata (I), (II) can hold).
      Runnable generator/driver exist (r16/st2_bigQ.py MODE SCHART I J [ALG] [P]; r16/run_st2Q.sh MODE CHARTLIST [TO] [VMEM]; modes full | lin |
      cal; slimgb or std over Q, never modStd) and are kept for a HINGED version (stratum hinges h_i ^ r_i != 0, ~10^3 jobs) -- not queued.
      NEW, cheap and decisive first: the special locus of stratum (II) is already empty for stratum (II) proper (exact over Q, 10 charts,
      r17/spec_exact.py); the open piece is "rank-drop locus of the x*-linear system A(h) on the H-variety = special locus".

## 15. (t2) of (S3-a): the X0 core (verify2's (M3)) and the unified stratum system  [stage3 round 18]
 (a) X0 = Y_ab (+) Y_cd (two 2-dim 2-row level spaces on disjoint row pairs, no single-row elements): (t2) => X0 exists, so EMPTINESS of X0
     closes (t2) without any classification. Generator r18/x0core.py UC P [HW HT] (charts: P_a identity on columns 0,1 (S_5 + GL_2);
     (u1,u2) identity on UC in {01,02,23}; hinges HW, HT = 2x2 minors (i,j) of (w1,w2), (t1,t2) with Rabinowitsch).
     FACTS (round 18): the HINGE-FREE system is NON-unit (numerics r18/x0_num.py: 5/5 converged solutions all degenerate, rank(w) or rank(t) <= 1
     = single-row elements), so hinges are needed; one hinged chart at P1 exhausts 900 MB in 56 s. Full hinged cover: 3 x 10 x 10 = 300 charts
     (fewer with the residual S_2 x S_3) -- big slot, each chart > 1 GB. NOT queued yet: first a reduced formulation (below).
     REDUCTION (rigorous, from sec. 30 (E)): if dim c(P_a) = dim c'(P_c) = 2 then c'(P_c) = c(P_a)^perp cap 1^perp, Q(P_a) inside c(P_a),
     Q'(P_c) inside c'(P_c) ("Q-closed" 2-row spaces), (X3) holds automatically, and only (X4) (9 conditions) remains on a 6-parameter family
     (Delta_a: 4, one parameter for each Q-closed space with given c-plane): expected dim -3. Q-closed spaces are generic (25/25 random members
     with P_a cap P_b = 0, r18/qclosed.py). Degenerate cases dim c <= 1 separately (then Y contains (v, -v) with q(v) = 0).
 (b) The UNIFIED stratum system (NOTES sec. 38 (B)): "H-plane + zero-column-sum x*" (= r16/st2_bigQ.py hinge-free); stratum (III) = some
     r_i || h_i, stratum (II) = none. Needed statement: x*-linear system injective off the special locus. Exact: big slot as well.

## 16. ST3-TWOCOL -- the column-element statement on the unified stratum-(II)/(III) system  [stage3 round 19]
 Statement: on "H-plane + zero-column-sum x*" (dim Delta = 2; r16/st2_bigQ.py hinge-free), every solution has x* supported in ONE column.
 Jobs: 8 symmetry orbits (r16/twocol_reps.txt) x 2 sigma-charts = 16 charts; r16/run_twocol.sh P TO VMEM (mode 'twocol': chart r_{I,J} = 1 and
 Rabinowitsch u3 r_{I2,J2} = 1). DECISIVE RUN = route (a): over Q (P = 0, slimgb), because "a second nonzero column" is an open condition (a P1
 verdict is triage only, as verify2 noted). Follow-up already done/pool-sized: on the column-element locus x* = w (x) e_J the stratum-(II)-proper
 hinges give the unit ideal over Q (sigma = 1: 64/64 charts; sigma = 0 running), so TWOCOL-unit over Q => stratum (II) of (PR3') empty and every
 stratum-(III) space (dim c(H) = 2) carries a column element. Not covered: dim Delta <= 1.
