# HANDOVER-stage3  (written 20:35, 2026-11-23, at the stop of round 8; workspace = cloud/L-gct-210/ on branch coord-L-gct-210)
All paths below are relative to the workspace root. Full proofs: NOTES-stage3.md (1436 lines; RESULT blocks of rounds 8..1 at the top,
sections 1-27). Scripts: stage3/ and stage3/gb/. Run Python as `python3 -I`; the scripts insert their own directory into sys.path and some
contain the ABSOLUTE path /home/claude/work/L-gct-210/stage3 -- replace it on another machine.

## 1. Role and question
Gap L-gct-210: every linear space L of 5x5 complex matrices with perm(J + t) = 120 for all t in L ("level space", J = all ones) has
dim <= 8. (Largest known dimension: 7.) Assume a 9-dim level L. I am "stage3" of chief's sparsity cascade: stage 2 hands over
lam_{rr'} := dim{t in L : rows r, r' = 0} >= 3 for all row pairs (and the same for columns); my regime is ALL a_r = 1
(a_r := 5 - dim pi_r(L), pi_r = r-th row; then L_r := {row r = 0} has dim 5) and all lam >= 3 ("no minimal row pair"). Task: show that
this regime is empty. Organising invariant: z = (z_r), z_r := dim Z_r, Z_r := {w : e_r w^T in L} (single-row elements; z_r <= 2 here).
Conventions: A = C[y_1..y_5]/(y_j^2); a row v is V = sum v_j y_j; a product of k rows has as coefficients the k x k subpermanents;
"P_a P_b P_c P_d = 0 in A_4" for subspaces = all products of one vector from each; eps = sum of coefficients; s(v) = sum of entries;
<u,v> bilinear without conjugation; level <=> sigma_k = 0 on L for k = 1..5 (sigma_k = sum of all k x k subpermanents).
KEY TOOL (CA2): if a_e = 1 then for every xi in L_e all five 4x4 subpermanents of the rows != e vanish (Xi_a Xi_b Xi_c Xi_d = 0 in A_4).
[Top coefficient of perm(J + s xi + eta); uses 1 not in pi_e(L), which always holds.]

## 2. Results
### 2a. PROVED by hand (section of NOTES-stage3.md; verification status as told to me by the coordinator)
 * Theorem N1 (all lam = 3 and z = 0 impossible): sections 11-16 (MIN-A..E, plane lemma of sec. 12/14/15).  VERIFIED by verify2.
 * Theorem N2-X (z = 0 with one pair lam_ab = 4 impossible): section 21.  VERIFIED by verify2.
   => THEOREM N: z = 0 is impossible (every 9-dim level L of the regime has a single-row element).
 * Theorem N3' (lineality bound for perm_3 at any base point): section 10. Lemma S3-1 (z_i <= 5 - lam_{ri} <= 2): section 22.
 * Lemmas S3-2..S3-5, Theorem PL4 (four 2-planes + a line), Theorem S3-G / S3-G': section 24 (C)-(L). verify2 re-proved PL4 and
   Lemma 5V independently; the rest of sec. 22-24 was on its list (status unknown to me).
 * Section 26 (round 7): counting tools (c1)-(c5); z = (1,0,0,0,0) impossible in the families F1 (all lam = 3), F3 (lam_ae = 4),
   F4a (lam_ab = 4, lam_cd = 3): (A1)-(A4); Lemma dim(U o U') >= 2 and FL2*-corollary (B).  VERIFIED by verify2: (c1)-(c5), (A1)-(A4), (B).
 * THEOREM Z22 (26 (B')): two rows with 2-dim single-row parts are impossible, degenerate planes included.  Listed as proved in
   BRIEF UPDATE 9; I have no explicit confirmation that (B') was re-derived. Sanity script stage3/z22_check.py (exact identities).
 * 26 (A5), (A5'): structure of F4b and "(CA2) gives exactly (i)-(iii)"; (C5)-(C9): structure of z_e = 2.  PENDING at verify2.
 * 27 (B): in F4b, parallel y_a..y_d force the free-column type.  27 (C): z = (2,1,..) is the z = 2 structure plus one single-row
   element.  NOT verified (written in the last 30 minutes; short arguments).
### 2b. EXACT / MODULAR (round 8, section 27 (A))
 * THEOREM FC [exact + modular]: the free-column sub-family of F4b is impossible. System "core level + (ii'),(iii')" (and the larger
   system with (i')) is the UNIT ideal on all 81 charts: Singular std over Q; msolve at p = 65521, 2147483629, 2147483497.
   Calibration (level only) is NON-unit on all 81 charts at the 3 primes; M_0 (below) is an exact solution.
 * EXACT EXAMPLE M_0 (stage3/f4b_example.py, arithmetic in Z[omega], 900 random points): free column 1 (+) C e_e w^T (+) C (e_a - e_b) n^T
   (+) C (e_c - e_d) n'^T, w = (0,-1,-1,3,-1), n = (0,1,omega^2,0,omega), n' = (0,1,omega,0,omega^2): a 7-dim level space with exactly the
   invariants of the F4b core (z = (0,0,0,0,1), lam_ab = lam_cd = 4, other lam = 3). It violates identity (iii); dim T_1(M_0) = 8 [numerical].
 * Exact rational rank checks behind sections 16, 21 (stage3/kcheck.py, span16_exact.py, n2_exact_family.py, s35_check.py).
### 2c. NUMERICAL (corroboration only; LM with gauge fixing and hinge penalties)
 * Plane lemma (5 planes): 185/191 starts converge, all with four planes equal to one coordinate plane; planes forced distinct: 0/35.
 * N2 plane problem: 75/76 solutions in three columns. PL4: 52 solutions, all of the two claimed types. (4,1)/(5,2) defect-form
   7-dim spaces of rows: dim T_1 = 8 for all (stage3/t1_defect.py); none is a valid core for z_e = 2 (stage3/core_check.py).
 * F4b cores: level-only searches have a very low success rate (general core with hinges 0/7 and 0/8; free-column family 1/19 = M_0).
   These negatives are NOT evidence.
### 2d. REFUTED / DEAD (do not retry)
 * "(N2-unit)" conjecture and the claim (N2-c) "B_w 1 = 0, dim W = 1" of round 4: superseded/withdrawn (N2 is impossible altogether).
 * "The level conditions of the 7-dim F4b core alone exclude F4b": FALSE (M_0).
 * "The cyclic identity for z_e = 2 follows from lineality along e_e Z": cannot (26 (C7)); restriction to X_{re} only sees the cyclic SUM.
 * COMPUTE item 5c as first written ("five planes in one coordinate 3-space" from the plane equations alone): FALSE (errata A2; corrected).
 * "8-dim level spaces exist" (my COMPUTE sec. 0): unfounded (errata A1; corrected). Calibrate at dim 7.
 * s3_planes_z2.py (weakened plane problem by LM with finite differences): too slow here, no result. n2_La.py: too slow.
 * Full split pair e_e (x) Z (+) e_d (x) U' inside L for z_e = 2: impossible (Z22). Pattern "m_ie = 3": impossible by counting.

## 3. OPEN -- exact statements, ranked by promise
Regime: 9-dim level L, all a_r = 1, all lam >= 3. Closed: z = 0; z = (1,0,0,0,0) except F4b; two entries 2. Open:
### O1. F4b  (most promising; I would do this first; 1-3 hours)
 z = (1,0,0,0,0), Z_e = C w, lam_ab = lam_cd = 4, other lam = 3, R = {a,b,c,d}. PROVED STRUCTURE (26 (A5), (A5')): vectors
 y_a..y_d, p, w, g_a..g_d in C^5 with
   M = { sum_R c_r (e_r y_r^T + e_e p^T) + mu e_e w^T + ga (e_a g_a^T + e_b g_b^T) + de (e_c g_c^T + e_d g_d^T) }  (7-dim, level, inside L),
 (y_r,g_r) independent, (w,p) independent, L/M 2-dim. With P_r = span(y_r,g_r), P_e = span(w,p), (CA2) is EXACTLY:
   (i) P_a P_b P_c P_d = 0;   (ii) y_a, y_b kill P_c P_d P_e;   (iii) y_c, y_d kill P_a P_b P_e     (all in A_4).
 Level conditions of N := span(x^{re}, e_e w^T): eps(Y_r) = s = -eps(P); eps(Y_T) = 0 (|T| >= 2); eps(Y_T P) = 0 (|T| >= 1); eps(Y_T W) = 0;
 equivalently sum_j prod_r (1 + t_r y_rj) = 4 + prod_r (1 + s t_r) on multilinear monomials (for s = 1: column 1 of Y "looks like" (1,1,1,1)).
 Consequence of (i)-(iii): FULL (Q4) for the five row spaces of N:  Y_a Y_b Y_c Y_d = 0 and Y_k Y_l Y_m . P_e = 0 (four triples).
 DONE: y_r all parallel => free-column type (27 (B)) => impossible (Theorem FC).
 OPEN STATEMENT: no such configuration with y_a..y_d not all parallel.
 NEXT STEP (my best idea): a "four lines and a plane" lemma in the style of Lemma 5V / PL4. For each triple, w3 := Y_k Y_l Y_m in A_3 is
 killed by P_e and by y_r (r the fourth row), i.e. the symmetric zero-diagonal matrix B_{w3} kills span(w, p, y_r); if that span is
 3-dim, B has rank <= 2 and is alpha beta^T + beta alpha^T with disjoint supports (Lemma I3) or 0. Combine with the moment conditions
 <y_r,y_r'> = s^2, tau(y_r,y_r',y_r'') = s^3, sum_j prod_r y_rj = s^4, <y_r,w> = 0, <y_r,p> = -s^2. CONJECTURE: these force all y_r
 proportional to one e_j. Test FIRST by machine: unknowns y_a..y_d, p, w (30; fix s = 1 or s = 0, w-scale, gauge p -> p + al w), equations
 = N level + the five 4-fold products, Rabinowitsch "y_a, y_b independent" (one 2x2 minor per chart): expect the unit ideal. Generator
 template: stage3/gb/fc_gen.py (replace system()). If non-unit, the surviving components give the families to feed into the full core
 (then add g's, (i)-(iii), and (FO-r): Omega(L_r) = C^5 for every row r, stage2 R7 / reg2). Fallback: COMPUTE-stage3.md item 3 (A/B).
### O2. z = (2,0,0,0,0) = (S3-a), and with it z = (2,1,..)   (hard; the core problem; half a day on the 24-core machine)
 Z := Z_e 2-dim, U' := (Z + C1)^perp. PROVED (24 (C), 26 (C5)-(C9), 27 (C)): M = L_e (+) e_e Z is 7-dim, L_r = X_{re} (+) e_e Z, all 2-row spaces
 through e are trivial, lam_{rr'} = 2 + m_kl, (Q4) P_a P_b P_c P_d = 0 for R (needs z_r = 0 on R), column sums of L_e in U',
 (CZ) Z . Xi_k Xi_l Xi_m = 0 and (PR) P_r . Xi_k Xi_l Xi_m = 0 on X_{re}. If the full (Q4) held for the 4-sets containing e (with P_e := Z),
 the plane lemma of sec. 12/15 would finish. MISSING: Z . p_kl p_lm p_mk = 0 (cyclic product; only the cyclic SUM is known).
 NEXT: (a) COMPUTE item 2: sample/solve the variety of cores (core level + (CA2)), evaluate the cyclic products, dim T_1(M), FO2 and
 (FO-r) on each; (b) exact: pattern "all m_kl = 1": L_e = span of six 2-row elements x^{kl} = e_k p_kl^T + e_l p_lk^T with
 sum_{l != k} p_kl = 0 for every k (8 free vectors) plus Z; (c) idea not yet tried: the lifting trick of Z22 STEP 1 (elements whose
 special rows are multiples of 1 give perm = product of polynomials = constant) applied to pairs of ROWS OF L_e after a column
 operation, or to the transposed space (stage 2 also gives lam >= 3 for column pairs).
 z = (2,1,..): the same structure with e_e w'^T inside L_d (27 (C)); identities there. Not analysed further.
### O3. z = (1,1,..) (several rows with one single-row direction each)   (unexplored; 2-4 hours for a first classification)
 Known: single-row vectors of different rows are orthogonal with sum 0; for rows d, e with w, w': for all x in L (c = column sums of the
 other three rows) <c, w o w'> = 0, <w, x_e + c> = 0, <w', x_d + c> = 0; and W W' . P_k P_l = 0 in A_4 for the pairs of the other rows.
 NEXT: redo the lam-pattern count of 26 (A2) for two rows (tools (c1)-(c5)), then the generic sub-case as in Theorem S3-G (planes for
 the three other rows, two lines), where PL4-type arguments should apply.
### O4. Verification debt
 26 (A5), (A5'), (B'), (C5)-(C9), 27 (B), (C); sections 22-24 if not yet done. Theorem FC: re-run at more primes / other charts.
### Outside my regime (others): rows with a_r >= 2 (reg2: dim L <= dim L_r + dim Omega(L_r) - 1), and the transposed statements.

## 4. Pitfalls
 * (CA2) needs a_e = 1. With a_e >= 2 every (Q4)-type identity holds only modulo an (a_e - 1)-dim space (24 (G)).
 * Lemma Q4-gen / (Q4) for R needs NO single-row elements in the rows of R (errata [B]).
 * Polarising an identity from a row kernel to planes requires the restriction to be INJECTIVE on monomials; for the triangle normal
   form the monomial al be ga carries TWO products (cyclic sum). This is exactly what blocks z_e = 2. Check monomial independence each time.
 * K(P) type lemmas: (K1) dim{Q in A_2 : Q P = 0} <= 1; (G2) dim{y : Q y = 0} <= 2; zero products (Q0) are of type D (same e_j) or B
   (p e_j + q e_l with c(p e_j - q e_l)) -- do not forget type B.
 * The Z22 count uses only steps (1)-(4) of rows' FL2* proof; step (5) (U cap U' = 0) is NOT available in the degenerate cases.
 * Numerics: LM from random starts is dominated by degenerate solutions; hinge penalties give residual floors, not proofs. scipy
   least_squares(method='lm') with finite differences is slow (max_nfev counts iterations here); np.einsum for the Glynn permanent
   is 10x slower than the reshaped matmul in f4b_core.perm5.
 * Modular Groebner: unit ideal mod p is evidence; do >= 3 primes, ALL coordinate charts (or a justified WLOG by symmetry), and a
   calibration that must be non-unit. For exact runs I recover integer coefficients with modulus 2^127 - 1 and assert |coeff| < 10^9.
 * No 8-dim level space is known. M_0 and all free-column cores found contain a full free column (excluded also by Theorem FL).
 * My timestamps in the STATUS lines are wall-clock checked; estimates of elapsed time made "in the head" ran about 2x fast.

## 5. Files
NOTES-stage3.md sections: 1 hypotheses; 2-9 round 1 (GZ, P_2 table, S3-A, S3-B, squarefree calculus); 10 N3'; 11-15 minimal case
(MIN-A..E, plane lemma); 16 Theorem N1 and reduction of lam >= 4; 18-20 family N2; 21 THEOREM N2-X; 22-23 landing of a single-row
element; 24 round 6 (S3-2..5, PL4 (J), S3-G (K)); 25 state; 26 round 7 ((A) z = (1,0,0,0,0), (B),(B') Z22, (C) z_e = 2, (D) table);
27 round 8 (Theorem FC, parallel y, z = (2,1,..)).   COMPUTE-stage3.md: five computation requests (errata A1, A2 applied).
Scripts (all `python3 -I <script> ...`, each < 3 min on 2 shared cores):
 stage3/gb/gbl.py            modular polynomial library (dict polynomials, permanent by subset DP, msolve writer/runner).
 stage3/gb/fc_gen.py P MODE  free-column F4b system on 81 charts, msolve; MODE = LEVEL | IDENT23 | FULL; about 20 s. Tools expected at
                             /home/claude/tools/gb/msolve (path inside gbl.msolve).
 stage3/gb/fc_exact.py MODE  same over Q with Singular (/home/claude/tools/gb/Singular); FULL 12 s, IDENT23 16 s; LEVEL > 100 s (unfinished).
 stage3/f4b_example.py       exact check of M_0 in Z[omega], dim T_1, invariants; 20 s.
 stage3/z22_check.py         exact degree-1 identities of Z22 STEP 1 (Fractions) and two small lemmas; 10 s.
 stage3/f4b_core.py, f4b_run.py SEED TL   LM search for the general F4b core (level only, hinges); slow, low success.
 stage3/f4b_fc.py SEED TL PP ID          LM search in the free-column family (ID = 1 adds (i')-(iii')).
 stage3/f4b_newton.py SEED TL            holomorphic LM with analytic Jacobian + Rabinowitsch non-degeneracy; inconclusive.
 stage3/deg_small.py SEED TL ID          LM for the degenerate two-plane shape (now settled by Z22).
 stage3/s3_planes_line.py, s3_planes_lineW.py SEED DELTA NVAN TL MAXNFEV   plane problem of PL4 (numerical corroboration).
 stage3/s3_planes_z2.py SEED DELTA NVAN TL MAXNFEV   weakened plane problem for z_e = 2 (too slow here; 148 real unknowns).
 stage3/n2_planes.py, n2_planesB1.py, n2_planesB1c4.py   N2 plane problems.  stage3/kcheck.py, k1check.py   annihilator tables, (K1), (G2).
 stage3/t1_defect.py, core_check.py   T_1 and (CA2) on rows' defect-form spaces (needs rows/build7.py and rows/*.npy).
 stage3/test_Q4planes.py, test_Q4planes_sep.py   five-plane lemma numerics.  stage3/s35_check.py, span16_exact.py, n2_exact_family.py   exact checks.
Data: stage3/f4b_fc_sol_2_1_3.npy (numerical M_0), stage3/gb/fc_*.ms and *.out (msolve inputs/outputs), stage3/gb/fc_exact_*.sing/.out.

## 6. Pending compute tasks and decision rules (details in COMPUTE-stage3.md unless marked NEW)
 T1 (NEW, small, first): N-system of O1 (30 unknowns): N level + Y_a Y_b Y_c Y_d = 0 + Y_k Y_l Y_m . P_e = 0, hinge "y_a, y_b independent"
    (and each other pair), cases s = 1 and s = 0, all charts, >= 3 primes, calibration = same system without the hinge (must contain
    the free column).  UNIT => F4b is impossible (with Theorem FC and 27 (B)); write the exact run over Q.  NON-unit => decompose,
    add g's and (i)-(iii), then (FO-r).
 T2 (item 3): F4b systems A (core + (i)-(iii)) and B (core + two free matrices). No solution of A => F4b impossible numerically;
    a solution of B would be a 9-dim level space (refutes the gap) -- verify in high precision and report at once.
 T3 (item 2): cores of z_e = 2: cyclic products, dim T_1, FO2, (FO-r). All cores with FO2 bound <= 8 => (S3-a) holds numerically and the
    strata tell which exact statement to prove; a core with a 2-dim common isotropic subspace => feed into item 1.
 T4 (item 1): direct search for a 9-dim level space containing e_e (x) Z (dim Z = 2), and with one single-row element; calibrate at
    dim 7; dim 8 or 9 solutions are new and must be reported at once.
 T5 (NEW): exact LEVEL classification of the free-column family (fc_exact.py LEVEL with primary decomposition): expected "finitely
    many solutions up to symmetry, all with p' in C w"; would make Theorem FC a corollary of Theorem FL as an independent check.
 T6 (item 5): exact confirmation of the plane lemmas (5a five planes; 5b PL4; 5c corrected three-way claim; 5d Lemma 5V).
 T7 (item 4, low priority): two single-row rows (z = (1,1,..), (2,1,..)) by direct search; the degenerate two-plane variant is proved.
