# COMPUTE-ERRATA — audit of the computation specs (verify2, round 5; written 19:45, last update 20:04)

Audited: handoff/HANDOFF.md section 2 (C1–C5), handoff/oracle.py, COMPUTE-rows.md, COMPUTE-verifyfl.md, COMPUTE-stage3.md,
COMPUTE-reg2.md. Method: every definition and every "X decides Y" re-derived by hand; named scripts read and spot-run
(rows/run_clm.py, handoff/oracle.py, verifyfl/r3_z.py + di_ext.py + r4_pr3.py, reg2/exact_T1.py, stage3/t1_defect.py,
stage2/r5_FO2.py). Severity: [A] = would produce a wrong conclusion or make a run meaningless; [B] = wrong number / imprecise
statement, harmless if the oracle is applied; [C] = clarification.

Versions audited: HANDOFF.md (19:28), oracle.py (19:27), COMPUTE-stage3.md (19:31), COMPUTE-rows.md (19:32 version in full; the 19:47
version checked for new sections: (X4) added, no error), COMPUTE-verifyfl.md (19:29 version in full; section F added 19:45: read, see below),
COMPUTE-reg2.md (19:31 version in full; the 19:52 update read: sections 0, 3b, 6), COMPUTE-stage2.md (19:44; not on my list, read once).

Summary of the [A] items
 A1 (COMPUTE-stage3 sec. 0, 1, 4): "Level spaces of dim 8 exist" is FALSE as far as anyone knows (largest known: 7). So "calibration at
    dim 8" can never succeed; calibrate at dim 7, treat dim 8 as a target.
 A2 (COMPUTE-stage3 item 5c): the CLAIM is false as a statement about planes (explicit counterexample below). An exact run would
    return "not the unit ideal" and could be misread as refuting Theorem N2-X. Corrected claim given.
 A3 (COMPUTE-verifyfl C, D and HANDOFF C3): hits of r3_z.search / di_gr.gr_search / di_ext.ext are solutions of an UNDER-SAMPLED system;
    the spec's acceptance list (dim, not strongly level) contains no fresh-point test. Add it (below), otherwise a spurious hit
    would be reported as a counterexample to (SL_m) or as a (5,1) space.
 A4 (all specs with Groebner tasks: HANDOFF C4, verifyfl A/B/E, stage3 2/5, rows X1–X3): "unit ideal modulo a prime (or several
    primes)" is evidence, not a proof of the characteristic-0 statement; "not unit modulo p" is not a counterexample either.
 A5 (COMPUTE-rows sec. 1, H1/H2/H5; COMPUTE-reg2 sec. 2 and ext7): clm.Problem samples N = 140 points; that is fewer than the number of
    monomials for d = 7 (4x5) and d = 7, 8 (5x5). run_clm.py does not pass N. Raise it (table below).
 A6 (HANDOFF sec. 1 "Blocked 4" and C2; COMPUTE-reg2 sections 1-3 in their 19:31 wording): the statement "(S6') a 6-dim 4x5 level space
    without a full free row has dim Omega <= 2" is FALSE. reg2's exact family M*(x,y) has no full free row, dim Omega = 4, dim T_1 = 11,
    FO2 bound 8 — confirmed by me (exact level identity for three rational members; (11, 4, 5, 8) with my own code). So the first-order
    criterion does not close a_r = 2; the target is (S6-FO2): "no full free row => FO2 bound <= 8". COMPUTE-reg2 (19:52) says this in its
    READ FIRST; HANDOFF does not. C2's decision rule must read: report (dim Omega, dim T_1, FO2 bound); the decisive event is a 6-dim
    space without a full free row and FO2 bound >= 9.

--------------------------------------------------------------------------------------------------------------------------
## handoff/oracle.py — no errors found
 * c(Y)_j = perm(J4 + Y^(j)) − 24, level <=> sum_j c_j = 0, e = rank of the span of c(Y): correct.
 * lift_to_5x5: the free vectors are `Vh[rank:].conj()`, i.e. w with sum_j c_j w_j = 0 (BILINEAR pairing) for all c in C + C1: correct
   (this is the conjugation pitfall; it is handled correctly here). Lift dimension d + 4 − e: correct.
 * Spot runs: rows/clm_p4_d6_defect3_s12.npy -> (6,3), lift dim 7, lift level error 3e-12; rows/rc45.npy -> (6,4), lift dim 6;
   a fresh (4,1) hit of run_clm.py -> (4,1), lift dim 7, error 6e-13.
 [C] Tolerance: e is decided at 1e-7 relative. For LM-limited spaces (accurate to ~1e-6, see reg2's pitfall) polish first, or the
   reported e can be too large. e too large is the SAFE direction for (DI_5) hits, but check it before discarding a hit.

## handoff/HANDOFF.md section 2
 C1  [B] "an 8-dim 5x5 level space with a deletable row exists <=> one of these exists" is correct for (5,1), (6,2), (7,3)
        (any (d,e) with d >= e + 4 contains one of them by restriction to subspaces; (4,0), (8,.) are excluded by SL / L_gct_215).
        It is NOT correct for "7-dim 4x5 level spaces" in general: a (7,4) space lifts only to dimension 7. A 7-dim hit decides the
        gap question only if e <= 3.
     [B] Acceptance "oracle reports the right (d,e)" should read "oracle reports d − e >= 4" (the solver only enforces e' <= e;
        e.g. a (6,1) space found in the (6,2) run is an even stronger counterexample and must not be discarded).
     [C] "<w, c(Y)>" is the BILINEAR pairing sum_j w_j c_j (no complex conjugation); (C + C1)^perp = {w : sum w = 0, sum_j w_j u_j = 0
        for u in C}. A solver that orthogonalises with Hermitian products changes the meaning of the equations.
     [C] Hit thresholds differ between HANDOFF (residual < 1e-12, sigma_min/sigma_max > 1e-3) and rows/run_clm.py (residual < 1e-9,
        cond < 1e6). Harmless: the oracle decides.
 C2  [B] "Any other type is a candidate for a 9-dim space": more precisely, by dim L <= dim L_r + dim Omega(L_r) − 1 a 6-dim space
        can be the L_r of a 9-dim level space only if it has no full free row AND dim Omega >= 4; dim Omega = 3 still allows dim 8.
     [C] T_1 and Omega: take the null space as conj(right singular vectors) and the Gram matrix N^T Q N without conjugation
        (verify2/fo2lib.py and stage2/r5_FO2.py do; my first version did not and gave bounds 5 < 7 on known spaces).
 C3  [A3] see COMPUTE-verifyfl below (fresh-point verification is missing).   The statement (SL_m) and "(SL_m) for all non-two-column
        m => no (5,1)" are correct (the column-sum map of a (5,1) space with defect line C m has rank <= 1).
 C4  [A4] the equivalence "Lemma Z <=> the successive saturation is the unit ideal" is correct over an algebraically closed field of
        characteristic 0, i.e. for the computation over Q. Over F_p it is evidence only (bad primes exist in principle in both
        directions). For a proof: compute over Q, or reconstruct the certificate over Q and verify it.
     [C] Quick numerical probe of Lemma Z itself (verify2/lemmaz_probe.py): with all row and column norms^2 forced >= 0.1 resp. 0.02,
        0 solutions in 9 LM starts (smallest residuals 1.6e-3, 2.6e-5); without the constraint 20 of 20 starts converge, 17 to a matrix
        with a zero row or column at machine precision and 3 LM-limited ones (smallest row/column norm 1e-4 .. 1e-6). Consistent with
        Lemma Z; tiny sample.
 C5  no errors found (the scripts' own sample sizes: see A5-type remark under COMPUTE-rows; verify every reported solution at fresh points).

## COMPUTE-rows.md
 Definitions (N, P_k, c(Y), p_k, C(L'), lift, neutral column, M(q), R(q), padding, (DI_4x4), Walsh coordinates): re-derived, correct.
   In particular: N(J + Y) = 120 + 24 P_1 + 6 P_2 + 2 P_3 + P_4; p_1 = −6 x column sums; sum_i M(q)_i = 96 on a level space;
   c((q^T | 0))_j = M(q)_j − 24, c_4 = 0; for t = H x H^T: P_2(t) = 8 sum x_ab^2, P_3(t) = 64 perm_3(x); M^(2)(t)_i = −2 <row_i,row_i>.
   (X2): c(Y + e_0 u^T) = c(Y) + D(Y) u, so (ii) + (iii) give a (6,3) space without neutral column: correct; (i) is consistent
   (row 0 in C^perp follows from P_2). (X3): correct.
 [A5] sec. 1: `clm.Problem(..., N=None)` uses N = 140 sample points. A homogeneous form of degree k in d coordinates has
   C(d+k−1, k) coefficients:      4x5, k = 4:  d = 5: 70,  d = 6: 126,  d = 7: 210;      5x5, k = 5:  d = 7: 462,  d = 8: 792.
   So N = 140 is enough only for d <= 6 (4x5). For H1 target (7,3), H2 `4 7 level`, H5 `5 7 level` and `5 8 level` the sampled
   system is strictly weaker than "level on the space". run_clm.py / ncdef_search.py / seeded.py do not pass N.
   FIX: construct Problem(p, d, mode, e, seed=s, N=...) with N >= 2 x the count above (420 for d = 7 at p = 4; 924 / 1584 for
   d = 7 / 8 at p = 5), and keep the rule "every hit goes through oracle.py" (the scripts' own HIT test is on the sampled points only).
 [B] sec. 0, last line: "(NCOL_3) + (DI_4x4) => no (7,3)" needs in addition "no (5,1) and no (6,2)" (the hyperplane lemma R4.1 is
   what gives a (7,3) space the neutral column of its hyperplanes). Correct form: (DI_5; 2) + (NCOL_3) + (DI_4x4) => no (7,3).
 [C] The code's p_k has no factor (4−k)! (same span, no effect).
 [C] (X4) (added 19:47): K = {(A_0 sigma | ... | A_4 sigma)}, sum A_j = id; "the quadratic part says exactly that B_j = id − 2A_j are
   isometries" is correct (b_j = −B_j sigma; the five conditions <y_j,y_j> = <s,y_j> are equivalent to <b_j,b_j> = <s,s>); 36 unknowns.
 [C] H5: for a 7-dim hit with deletable line and rest of type (d,e): d − e >= 3 always; d − e >= 4 is itself a counterexample to (DI_5)
   — report it as such, not only as an (NCOL) test.
 Spot run: `run_clm.py 4 4 defect 1 0 4 80` -> 1 hit in 4 starts (5 s), confirmed (4,1) by the oracle.

## COMPUTE-verifyfl.md
 Definitions (C_j, defect in C m with the BILINEAR pairing, strongly level, column-centred, (SL_m), the vectors chi_k, c+-): correct.
 Checked numerically with my own evaluation (verify2/audit_verifyfl.py): the four planes N of A have defect exactly C m
   (error 7e-14) and coincide with r4_pr3.Nplane; in E: N_V has defect exactly C m, N_I, span(chi_1 c+), span(chi_1 (1,w,w^2,0,0))
   are strongly level; c+- solve the stated cubic.
 [B] A and D: A_m = {4x5 matrices whose column-sum vector is a multiple of m} has dimension 16, not 17 (di_ext.ambient_m returns 16
   for m = (1,w,w^2,0,0) and (1,2,−3,0,0)). Hence A: 16 − 2 − 1 = 13 unknowns (not 14); D: Gr(5,16), calibration Gr(4,16).
 [A3] C, D (and E numerically): sample sizes in the scripts are below the number of monomials of degree <= 4:
        k = 3: 34 monomials, r3_z.search uses 28 points;   k = 4: 69, r3_z uses 44, di_gr uses 40, di_ext.ext uses 45;
        k = 5: 125, di_gr uses 60, di_ext.ext uses 45.
   So a "hit" satisfies a weaker system. In a test (k = 3, 19 hits) all hits were genuine at 300 fresh points, so this is a risk,
   not an observed failure. REQUIRED ADDITION to the acceptance list of C and D, before "not strongly level":
        di_ext.chk_m(B, m, trials=300) < 1e-9 at FRESH points, and handoff/oracle.py must report (k,1) with defect line C m.
   Recommended: >= 2 x (monomial count) sample points (70, 140, 250 for k = 3, 4, 5), or the exact coefficient equations.
 [A4] A, B, E: "work modulo a prime p ... for several primes" gives evidence only. The decisions "UNIT IDEAL ==> no extension /
   no principal (5,1)" are valid for a computation over Q(i, sqrt 3, xi) resp. Q, or for a lifted and verified certificate.
 [C] The chain "UNIT IDEAL for all four N ==> no principal (5,1) for m = (1,w,w^2,0,0)" rests on verifyfl's Theorem PS and the proof
   of PR3 (both verified by me in round 5: the four planes are exactly the solutions of step (4) for isotropic m), and B's system
   (1)-(4) is a set of NECESSARY conditions for a principal (5,1) (Theorem PS (a)-(c)); so "unit ideal over Q" does decide what is claimed.

## COMPUTE-stage3.md
 Conventions (sigma_k, squarefree algebra, bilinear <,>, a_r, L_r, lam, Z_r), T_1 / FO2 block, coefficient counts (45 + 165 + 495 +
   1287 = 1992; 28 + 84 + 210 + 462 = 784; 70 x 5), N = 4000 sample points for item 1: correct.
 [A1] sec. 0: "The gap L-gct-210 claims: every level space has dim <= 8. Level spaces of dim 8 exist." The second sentence is
   wrong: no 8-dim 5x5 level space is known (largest known: 7; HANDOFF sec. 1; COMPUTE-rows sec. 0; COMPUTE-reg2 sec. 5).
   Consequences: item 1, last paragraph ("8 free matrices; calibration at dim 8") and item 4 ("Calibration at dim 8 (report which
   z-vectors occur among 8-dim spaces)") name a calibration that cannot succeed. FIX: calibrate at dim 7 (known spaces with the
   required single-row elements, e.g. the lifts of rows' (5,2) and (4,1) spaces); dim 8 is a TARGET (any verified 8-dim level space
   is new and must be reported at once; it would not refute the gap but would refute "maximum = 7").
 [A2] item (5c): the CLAIM "all five planes lie in one coordinate 3-space" is FALSE for the system as written. Counterexample
   (checked exactly, all entries 0, +-1):  g = e_2 + e_3, g* = e_2 − e_3,
        P_c = P_d = P_e = span(e_1, g),    P_a = P_b = span(g*, e_4),    rho_a = rho_b = g*.
   Then P_a P_b P_k P_l = 0 for the three pairs, rho_a . P_c P_d P_e = rho_b . P_c P_d P_e = 0, all ten triple products are
   nonzero, and the planes use the four columns 1, 2, 3, 4. Theorem N2-X is not affected: its proof excludes P_c = P_d = P_e by
   (Q5J) (the sum of all 3x3 subpermanents vanishes on P_c x P_d x P_e; here it is 2) and (P2), and uses (NT') for one more case.
   CORRECT pure-plane statement (this is what section 21 proves from (Q4) for the three 4-sets and (NT)):
        all five planes lie in one coordinate 3-space,  OR  P_c = P_d = P_e,  OR  two of P_c, P_d, P_e are equal to one coordinate plane.
   For an exact confirmation test this three-way conclusion (the vectors rho_a, rho_b are then not needed). The second alternative is
   excluded in section 21 by (Qb), (Q5J) and (P2), which are not plane equations of this system; I have not checked whether the plane
   equations with (Q5J) added still admit solutions with P_c = P_d = P_e (the hand proof needs (P2) for P = span(e_1 − e_2, e_3 − e_4)).
 [B] item 2, "Facts proved by hand": (Q4R) and "L_e contains no single-row element" hold when z_r = 0 for the four rows r != e
   (this is the sub-case z = (0,0,0,0,2)); with single-row elements in other rows they are not proved (that is item 4).
 [A4] items 2 and 5: Groebner "over F_32003 (and one prime more)": evidence only.
 [C] items (5a), (5b), (5d): statements agree with the hand-proved ones (plane lemma of sec. 14, Theorem PL4, Lemma 5V; I proved 5V
   and PL4 independently in round 4).
 Spot run: `t1_defect.py` runs (1 s) and prints dim T_1 = 8 for the (5,2)-based spaces.

## COMPUTE-reg2.md
 Definitions (N, F, embedding, T_1, Omega, E_0, C(M), neutral column, Type F / NC), dim T_1 = dim E_0 + dim Omega, tau = (J'; −4 1) in
   T_1(M), the inequality dim L <= dim L_r + dim Omega(L_r) − 1, the count 6 + 21 + 56 + 126 = 209, the normalisation of sec. 3
   (Omega = C1 (+) (Omega cap 1^perp); k = 2 <=> dim Omega >= 3, k = 3 <=> dim Omega >= 4), sec. 5 (ambient dimension 22): correct.
 (S6') => no 9-dim level space with some a_r >= 2: correct, including a_r = 3 (for a 7-dim L_r take any 6-dim subspace M: T_1(L_r)
   lies in T_1(M), so dim Omega(L_r) <= 2 and dim L <= 8; a full free row is excluded by FL). The exact family (b) is level and has
   neutral column 0 (re-derived by hand).
 [A5] sec. 1 (iii): ext7.py (target dimension 7) samples 300 points; a quartic in 7 coordinates has 329 non-constant monomials.
   Use N >= 660. Sec. 2: clm.Problem for d = 7 needs N >= 420 (see COMPUTE-rows A5). For d = 6: 209 monomials vs 300 points: fine.
 [B] FO2 on unpolished solutions: stage2/r5_FO2.FO2 cuts the rank of the cofactor system at 1e-8 relative. On an LM-limited space
   (accurate to ~1e-6) this UNDER-estimates dim T_1 and gives a bound that is too small — the unsafe direction for the decisions
   in sec. 6 ("FO2 <= 8 -> the regime dies for this space"). Example: stage2's candidate /tmp/r5_Lr_2_1.npy reads (7,2,6) at
   1e-9 and (12,7,8) at 1e-5. FIX: polish first (as sec. 0 already demands for the type), and print the singular-value gap.
 [A6] the 19:31 text of sections 1-3 and 4(b) speaks of "(S6')" and of the F / NC dichotomy; both are superseded (see A6 above and the
   file's own READ FIRST of 19:55). The updated sections 0, 3b, 6 are consistent: (S6-FO2) + FL => no a_r = 2 at dim 9 (and also no
   a_r = 3: apply (S6-FO2) to a 6-dim subspace of the 7-dim L_r, which has no full free row by rows' SL_3 corollary). Lemma EC and the
   level proof of M* (sec. 4(e) / NOTES-reg2 4.3) re-derived by hand; M* level exactly (verify2/reg2_mstar_exact.py).
 Otherwise no errors found. Spot run: `exact_T1.py` (1.5 s) certifies Omega inside span(1, e_c) for the two exact spaces.
 Recomputed with my own code (verify2/reg2_fo2.py): (dim T_1, rank, bound, dim Omega) = (9,3,7,2) for 19 six-dim spaces of rows and
   (10,4,8,3) for rc45; three files are near-degenerate (see NOTES-verify2.md, RESULT ROUND 4).

## COMPUTE-stage2.md (not on my list; read once)
 Definitions ((Q-r) with the corrected (iii), block types, T_1, q_m as a symmetric BILINEAR form, FO2, (T2), (FO-r)), the DEAD/ALIVE
   logic, and the level conditions of the block family (2,4) in S3 (re-derived: P_1, P_2, P_3 as stated): no errors found.
 [A5-type] r6_census.py samples (i) at 50 points and (ii) at 28 (the spec itself says to raise them to 140, 80 and re-checks every
   solution at 80 fresh points). (i) is an inhomogeneous quartic in 5 coordinates: 125 monomials, so use >= 250 for (i) and >= 140 for (ii).
 [C] S5 (diagonal N2 blocks) is not needed: Theorem N2-X is verified (NOTES-verify2.md, RESULT ROUND 3).
 [C] S4 (closed-form pair conditions, pairlib.py): not audited.

## COMPUTE-verifyfl.md, section F (added 19:45)
 Rests on verifyfl's Theorem SL3-RED (NOTES-verifyfl R5.6): verified by me after the first version of this file (Lemma C', 3C, NP,
 Lemma T, Propositions I' and V, and the four-way case analysis re-derived; the kinds (R1)-(R4) are stated correctly).
 A hit is a counterexample to (SL_m) only after the fresh-point test of A3.
 (R2): v = chi_1 + x chi_2 - (x^2/2) chi_3 is isotropic (checked).

## Conjugation check of the scripts that compute T_1, Omega, (T2), extensions
 All take the null space as conj(right singular vectors) and pair bilinearly: stage2/r5_FO2.py, r7_FOrow.py, r6_T2.py, r6_extend.py;
 reg2/a6.py (T1, E0); verifyfl/di_ext.py (mperp, ambient_m); handoff/oracle.py; verify2/fo2lib.py. stage3/t1_defect.py and reg2/a9.py use
 ranks only. No error found. (reg2's numbers for 20 spaces and for M* were reproduced with my own code.)

## Sample-size table (number of coefficients of a form of degree k in d coordinates = C(d+k−1, k))
   d      k=4 (4x5 level / defect, top degree)     k=5 (5x5 level, top degree)     all degrees 1..4 together (inhomogeneous quartic)
   3              15                                      21                                34
   4              35                                      56                                69
   5              70                                     126                               125
   6             126                                     252                               209
   7             210                                     462                               329
   8             330                                     792                               494
   9             495                                    1287                               714
 Rule already stated in HANDOFF C1 ("sample >= 2 x the number of monomials") — apply it to every script before a long run.

==========================================================================================================================
# ROUND 6 ADDENDUM (verify2, 2026-11-23 20:35) — audit of the local session's exact runs VF-A, VF-B and of the new spec sections
Files audited: /home/claude/coord/local/results/VF-A/{gen.py, RESULT.md, A1_2147483629.ms, CAL_2147483629.gb}, VF-B/{gen.py, calpts.py,
RESULT.md}; COMPUTE-verifyfl.md section NEXT (20:05); COMPUTE-stage2.md S4; COMPUTE-rows.md X4, X5.
Own scripts (all in /home/claude/work/L-gct-210/verify2/vf/): own_gen_A.py, drive_A.sh, exact_A.py, firstorder_A.py, secondorder_A.py,
own_gen_B.py; outputs in vf/run and vf/runB.

## VF-A (one-vector extensions of the four isotropic planes) — generator CORRECT; verdict CONFIRMED and now a PROOF
 gen.py, line by line: constants (i, sqrt 3, w, beta, xi), Z, Zs, the four cases, the parametrisation of A_m (rows 0..2 free + lambda,
   16 unknowns), C_j, the basis W of m^perp, the coefficient extraction (every (k,t,x)-coefficient containing x), the two generic
   linear equations (N-directions) and the generic affine equation: all as in spec A. The verdict proves what verifyfl claims:
   by PS / the proof of PR3 (verified in round 5) a principal (5,1) for m = (1,w,w^2,0,0) contains, after a row permutation, one of the
   four planes N, hence a 3-dim extension of it. The four cases are closed under the conjugations i -> -i, sqrt 3 -> -sqrt 3 (they
   permute the cases up to a row and a column permutation), so one choice of square roots mod p covers all conjugates.
 The caveat "single generic affine normalisation" IS a gap for a proof (a solution cone inside the hyperplane l_3 = 0 would be missed;
   likewise the two generic linear equations must be independent on N). It is now CLOSED, three ways:
   (1) OWN generator (different parametrisation: E a general 4x5 matrix with the four linear equations "column sums in C m";
       C_j - 24 by the squarefree-algebra expansion; N removed by setting two entries of E to 0 where (Z,Zs) has an invertible minor),
       ALL 18 coordinate charts E[r][c] = 1:  UNIT in 18 of 18 charts for each of A1..A4, at p = 2147483629 and p = 2147483497;
       calibration CAL non-unit in 19 of 19 charts.  (msolve 0.10.1 in this container, about 6 s in total.)
   (2) homogeneous system (no affine equation): reduced DRL basis = 18 linear forms + E34^2, E32*E34, E32^2: the only solution is 0.
   (3) no Groebner basis at all (exact_A.py, exact arithmetic mod p): the first-order system has rank 12 on the 16-dim A_m, so the
       first-order extension space is N + 2 directions; on these two directions the x^2-coefficients span ALL binary quadrics (rank 3).
       (Numerically over C: same ranks, singular values 10..20 against 1e-13.)
 CHARACTERISTIC 0: the set of extensions is a PROJECTIVE variety (homogeneous equations in E modulo N). A point over Q-bar can be
   scaled to be integral with a unit coordinate at a prime above p and then reduces to a point mod p. So "empty mod p" (all charts
   unit, or (2), or (3)) at ONE prime PROVES "empty in characteristic 0". Request A is settled rigorously: none of the four planes N
   lies in a 3-dim space with defect in C m; hence no principal (5,1) space for |supp m| = 3 (with PR3 for non-isotropic m).
   No further run is needed for A.

## VF-B (N-problem) — generator CORRECT; calibration REPRODUCED; two caveats for the main cases
 gen.py: parametrisation by (1) (rows 0..2 x columns P[:-1] free, the rest from row sums 0 / column sums m_j resp. 0), (2) all (k,t)-
   coefficients of R_i(k Z + t Zs) with W = {e_j (j not in P), m_b e_a - m_a e_b}, (3) the three normal-form equations per column,
   successive saturation by the ideals (entries of zs_j): as in spec B. The system is a set of NECESSARY conditions for a principal
   (5,1) (Theorem PS (a)-(c), verified), so "unit after saturation" does give "no principal (5,1) with this defect line".
 Reproduced here (Singular in this container, gen.py unchanged, P = 2147482921): m = (1,2,-3,0,0): unit after saturation (4 s);
   m = (1,w,w^2,0,0): dim 0, vdim 24 (9 s). With my OWN generator (own_gen_B.py: full 4 x |P| blocks of variables, linear conditions
   as equations, squarefree-algebra expansion, exact CHART gauge): (1,2,-3,0,0) unit, (1,1,-2,0,0) unit, (1,w,w^2,0,0) dim 0 vdim 24.
 [B] Gauge. gen.py fixes the gauge (Z -> Z + c Zs, Zs -> c' Zs) by one generic linear equation on Z and one generic affine equation
   on Zs. A solution orbit with ls(Zs) = 0 or lz(Zs) = 0 has no representative: for a PROOF use the exact chart
        Zs[0][j0] = 1,  Z[0][j0] = 0    for ONE fixed j0 in P,   then saturate by the ideals (entries of zs_j), j in P, j != j0.
   This loses nothing: zs_{j0} != 0 has a nonzero entry, a row permutation (a symmetry of the system) moves it to row 0, the two gauge
   freedoms normalise it. own_gen_B.py does exactly this (argument 4 = j0). For |P| = 4 it did not finish in 100 s here.
 [A4, still valid here] After saturation the solution set is only QUASI-projective (the conditions zs_j != 0 are open), so the
   projectivity argument of VF-A does NOT apply: "unit after saturation mod p" for the main cases is evidence, not a proof. For a
   proof: Singular over Q (or Q(i), Q(w), Q(z)); or show in addition that the boundary is empty mod p, i.e. that the UNSATURATED
   system has no solution with some zs_j = 0 that is a limit of solutions (not available: before saturation the system is non-unit).

## COMPUTE-verifyfl.md, section NEXT
 (F1)-(F4): correct (they are (C1), (C2') at s = 0 with (Nn), (B-i'), (B-ii') of NOTES-verifyfl R5.1; verified in round 5).
 [B] "(SL_m) holds for m iff [DC3], [T22], [T31]": only "if" is true. (SL_m) does not imply [DC3] (a 3-dim doubly centred space is
   allowed by (SL_m)). So: UNIT for all three  ==>  (SL_m).  But a NON-unit [DC3] does not refute (SL_m); in that case type (1,3)
   needs its own system [T13]: N = a 3-dim doubly centred space of the k = 3 list of N1 plus one column-centred Y with s(Y) != 0
   (and [DC4] for type (0,4)). The spec expects k = 3 solutions for isotropic m, so this case will occur.
 [C] RIGOUR NOTE (v) can be sharpened, and this saves the expensive characteristic-0 runs wherever it applies:
      if a system describes ALL points of a projective variety — every cell of a Grassmannian, every coordinate chart of a projective
      space, every case of an isotropic line (v(th) and chi_3), no saturation, no open condition — and all its coefficients are
      integral at p, then UNIT in every cell at ONE prime p proves emptiness in characteristic 0.
   Applies to: request A (done above); N4 "Gr(4,9) all cells" (Lemma 3C) and "Lemma SL on Gr(4,15)"; N1 [DC-k] (all cells of
   Gr(k,8), all cases of v_4, v_5 — the parameter space is projective); the statement "no 4-dim column-centred K" as a whole
   (closed subvariety of Gr(4,15)). It does NOT apply to a single TYPED system with an open condition (q = 3 exactly, <z_1,z_1> != 0,
   zs_j != 0): a characteristic-0 solution of type (3,1) may reduce mod p to a K of another type. So either all types are shown
   empty at the same prime with reductions that are valid in characteristic p (the hand lemmas (F2)-(F4), Lemma N, "7 pairs" use only
   nondegenerate forms and Newton's identities: fine for p > 5, but each use should be named), or the typed systems are run over Q.
 N1 calibrations (type I, type II, N_V; Lemma NP for v_4 = v_5 = 0), N2 calibration (Zs = chi_1 (1,1,-2,0,0): SL3-RED case (i)),
   N3 calibrations (Props I-ALL, II-ALL), N4: consistent with the hand results, all of which I have verified (round 5 and round 6:
   Lemma 3C, NP, T, Props I', V, I-ALL, II-ALL, SL3-RED). In N4, "extension variety of chi_1 (x) Lam_M = exactly one point": correct
   (the second alternative of Prop I', chi_3 (e_n - e_n')^T, is not an extension: its quartic term is 8 c^2 l_p l_p' != 0).
 N6: (SL_C) => dim L' <= e + 3 correct; (F2) for general C reads <z_j,z_j> = th(Z)_j with th(Z) in C (Lemma QB for general e, verified).
   The listed planes / 3-spaces C contain no two-column vector except the two marked controls (checked).

## COMPUTE-stage2.md S4 (minimal pairs with zeros)
 The closed form is correct: I re-derived (i), (ii) (G_T = Gram matrix of the inverse form on the row space of R_T; the radical vector
   of q_T on Pi_T is the dual of c_1 R_1 + c_2 R_2 with G c = 0, and ell of it equals a_T c_2), and gamma_check agrees with the
   independent pair_check on 29750 random sparse column pairs.
 [B] The data are stated incompletely. (nu, nu') must annihilate the rows of J as well: add the equation
        sum_i nu_i + sum_i nu'_i = 0,
   and (nu, nu') is then defined modulo (kappa, -kappa') and scaling — not modulo (kappa,0) and (0,kappa') separately (NOTES-stage2
   section 2: "sum_i (p_i + p~_i) = 0 encodes (1,1) in I^"). The row space of R_T, hence the condition for T, is not invariant under
   (nu,nu') -> (nu + a kappa, nu') in general (it is in the alternative G_11 = G_12 = 0, not in the alternative a_T = 0). Without the
   equation the solution set is larger than the set of pair data.

## COMPUTE-rows.md X4, X5 — no errors found
 X5: re-derived from Theorem NCOL-P3 / P51 for kernel type (2,2,1): B_a = R, B_b = -R on v^perp, B_a v = B_b v = v, B_c = reflection in v;
   the row-sum relation forces m_c = 0 (m_a = 0 or m_b = 0 give f = 0 when the entries of m are distinct) and R p = lam p with
   lam = (m_a+m_b)/(m_a-m_b); then Z = a m^T + t n (e_a - e_b)^T with a = (kappa/4)1 + phi v + eta n, t = 2 m_a m_b eta/(m_a-m_b),
   kappa^2 = (4/3) phi^2 <v,v>: as stated.
 [B] (rows' notes, not the spec) Theorem DC (a) and NC'-DC (b) of NOTES-rows R5.2 state identities that are only inequalities:
   dim L' = rank c + rank(s restricted to ker c) + dim L'_dc <= rank c + rank s + dim L'_dc (example with strict inequality: the level
   line spanned by e_0 u^T + (e_1 - e_2) e_0^T). All uses in COMPUTE-rows are of the "<=" form and stand.
