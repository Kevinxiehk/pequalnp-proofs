# COMPUTE-ERRATA — audit of the computation specs (verify2, round 5; written 19:45, updated 19:58)

Audited: handoff/HANDOFF.md section 2 (C1–C5), handoff/oracle.py, COMPUTE-rows.md, COMPUTE-verifyfl.md, COMPUTE-stage3.md,
COMPUTE-reg2.md. Method: every definition and every "X decides Y" re-derived by hand; named scripts read and spot-run
(rows/run_clm.py, handoff/oracle.py, verifyfl/r3_z.py + di_ext.py + r4_pr3.py, reg2/exact_T1.py, stage3/t1_defect.py,
stage2/r5_FO2.py). Severity: [A] = would produce a wrong conclusion or make a run meaningless; [B] = wrong number / imprecise
statement, harmless if the oracle is applied; [C] = clarification.

Versions audited: HANDOFF.md (19:28), oracle.py (19:27), COMPUTE-stage3.md (19:31), COMPUTE-rows.md (19:32 version in full; the 19:47
version only checked for new sections: none), COMPUTE-verifyfl.md (19:29 version in full; section F added 19:45: read, see below),
COMPUTE-reg2.md (19:31 version in full; the 19:52 update read: sections 0, 3b, 6), COMPUTE-stage2.md (19:44; not on my list, read once).

Summary of the [A] items
 A6 (HANDOFF sec. 1 "Blocked 4" and C2; COMPUTE-reg2 sections 1-3 in their 19:31 wording): the statement "(S6') a 6-dim 4x5 level space
    without a full free row has dim Omega <= 2" is FALSE. reg2's exact family M*(x,y) has no full free row, dim Omega = 4, dim T_1 = 11,
    FO2 bound 8 — confirmed by me (exact level identity for three rational members; (11, 4, 5, 8) with my own code). So the first-order
    criterion does not close a_r = 2; the target is (S6-FO2): "no full free row => FO2 bound <= 8". COMPUTE-reg2 (19:52) says this in its
    READ FIRST; HANDOFF does not. C2's decision rule must read: report (dim Omega, dim T_1, FO2 bound); the decisive event is a 6-dim
    space without a full free row and FO2 bound >= 9.
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
 [C] The chain "UNIT IDEAL for all four N ==> no principal (5,1) for m = (1,w,w^2,0,0)" rests on verifyfl's Theorem PS / PR3
   (hand proofs, being verified now; see NOTES-verify2.md round 5).

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
 Rests on verifyfl's Theorem SL3-RED (NOTES-verifyfl R5.6), which I have not verified (Lemma C', Lemma 3C, Lemma NP are verified).
 The kinds (R1)-(R4) are search targets; a hit is a counterexample to (SL_m) only after the fresh-point test of A3.
 (R2): v = chi_1 + x chi_2 - (x^2/2) chi_3 is isotropic (checked).

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
