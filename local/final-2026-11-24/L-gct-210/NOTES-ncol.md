# NOTES-ncol (role ncol; leaf 6 of PROOF-MAP: (6,2), (7,3) = Branch 1.2; start 23:37 UTC)
## RESULT, ROUND 12 (ncol; 07:47 - 08:05 UTC, STOPPED: L-gct-210 aborted) -- b23 (1,1) restricted classification done for every U_0
##   (generic: one family A23; special U_0: families span(nu_1 a^T, nu_2 (e2-e3)^T)), all excluded by K_0-fixed family systems (R12.3-R12.6);
##   (c)/(d) of (6,2): Walsh-coordinate identities and Q_00 != 0 structure only (R12.1-R12.2), no kill.
## STATE AT STOP: K0 FALSE (R11.7).  Restricted a3/b22 classification: (1,1) COMPLETE, every member excluded (R11.13, R11.16; verify2
##   re-ran 154/154 at a second prime); r_a = 2 charts OPEN (NCOLK0Q, 42 jobs, not run).  H-a3-SL, H-b22-SL (verified), H-b23-SL (R11.5).
##   b23: (1,1) done (R12.3-R12.6), r_a = 2 open.  (6,2) (c)/(d): open; lead = kill a nonzero doubly-centred level part Q_00 (L_gct_216/217).

## RESULT, ROUND 11 (ncol; 06:55 - 07:46 UTC) -- CONJECTURE K0 IS FALSE (exact counterexample family); the restricted (zero-free,
##   a3/b22-shaped) problem: three member types found, ALL excluded by K_0-fixed systems, and the (1,1) sub-case classified COMPLETELY
##   (hand split + exact over Q); only the r_a = 2 Pluecker charts remain (big slot NCOLK0Q, driver rewritten).  Also THEOREM H-b23-SL.
 N1 [R11.7, exact] K0 FALSE: span(nu_1 a^T, nu_2 (e_0 - e_1)^T), a = (-3,-3,7,14,-21): level, d2 == 0, e = 1, m = (49,49,-81,-36,19)
    zero-free.  Family: b = e_i - e_j, a_i = a_j, other entries sum 0, e_3(a) = 0 (m_i = m_j; missed by the round-9 census).
    => the round-10 consequence "K0 + H-a3-SL => H-a3" is WITHDRAWN as stated (also for b22).
 N2 [R11.8, R11.11, R11.12] zero-free members with the a3 shape (m0=m1=m2) / b22 shape (m0=m1, m2=m3): F (family; b22 rational
    a = (1,1,-3,-3,6) + Q(sqrt -39) pair; a3 Q(sqrt -15), Q(i) pairs), S4 (b = (zeta,zeta,zetabar,zetabar,1), a = conj b, zeta = -1+i,
    m = (1,1,1,1,-4), both shapes), N (a3: a = (s,s,s,1,-1-s), b = (0,0,0,1,beta), 2s^2+3s+3 = 0, 4beta^2+7beta+4 = 0).  All verified exactly.
 N3 [R11.13, modular 65521 + properness => char 0] K_0-FIXED SYSTEMS: every member (15 incl. conjugates/swaps) with its forced C
    (KCAL) has NO admissible Y: 330/330 UNIT; calibration (01|23) reproduces R9.6.  So none of them occurs in the last piece.
 N4 [R11.14, R11.16; rigorous + exact over Q] (1,1) COMPLETE: Lemma Z (F == 0 => |supp a| <= 2); Case A impossible; Case B0 = the family
    exactly; B1 (Q): only N; Case C (Q, factorised split, seconds): only S4.  So the restricted list is complete on (1,1).
 N5 [R11.3, R11.5] THEOREM H-b23-SL (strongly level K_0 excluded for b23; 1078 systems, all finite or UNIT).
 N6 [process] NCOLK0Q rewritten (42 r_a = 2 jobs, exact over Q, resumable); NCOLHB22T2 queued; local b22-T2 pass stopped (over 0.5 GB).
 OPEN: r_a = 2 charts of the restricted classification (NCOLK0Q; split idea R11.15 if it stalls); b22-T2 / H-system runs (big slot);
    b23 with e(K_0) = 1; (6,2) configurations (c)/(d) via L_gct_216/217 (nonzero Q_00) -- next; (SR3); (CCN).

## RESULT, ROUND 10 (ncol; 06:07 - 06:55 UTC) -- verify2's rigidity gap in H-a3-SL / H-b22-SL found real and CLOSED: strongly level
##   2-dim zero-row spaces are the rigid pairs plus two explicit 1-parameter families F1, F2 (complete, char 0), and the family-parametrised
##   K_0 systems are finite for every parameter; THEOREM H-b22-SL added.  CONJECTURE K0 itself still open.  Details R10.1 - R10.9.
 M1 [R10.5] q(K_0) = 0 is NOT forced; strongly level 2-dim zero-row spaces form 1-dim families (mod-p decomposition): verify2 was right.
 M2 [rigorous + exact over Q, R10.8-R10.9] complete char-0 classification: rigid pairs (q = 0), F1(a,b)[h] = span(nu_1(h0 e_a - h1 e_b)^T,
    nu_2(h0 e_a + h1 e_b)^T), F2(a,b)[h] = span((h0 nu_1 + h1 nu_2) e_a^T, (h0 nu_1 - h1 nu_2) e_b^T)  (rows' SL_3 (b),(c) normal forms,
    hand + three tiny exact GBs).
 M3 [modular 65521 + semicontinuity, R10.6, R10.9] K_0-family systems: a3 308 (248 UNIT, 60 with fibres finite over the parameters),
    b22 572 (520 UNIT, 52 finite).  => THEOREM H-a3-SL and THEOREM H-b22-SL hold for every strongly level K_0.
 M4 [R10.1] THEOREM H-b22-SL (rigid pairs): 132 systems, 128 UNIT, 4 finite.  (A precedence bug in the first b22 generator was caught.)
 M5 [R10.2-R10.4] K0: structure (pencil / involution, "K0 <=> >= 2 neutral columns"), sub-case (2,0) generic part by hand; the exact
    sub-case classifications ran out of memory at 0.5 GB.  Given K0, the H-conjecture is done for a3 and reduced for b22 to ONE fixed-C
    system (family T2 of b22 = first job of NCOL-HCONJ-B); b23 untouched.
 OPEN: CONJECTURE K0; b22-T2 (big slot); b23; (SR3); (CCN).
## RESULT, ROUND 9 (ncol; 05:28 - 06:05 UTC) -- hand route to the H-conjecture: exact second-order identities, a closed case cover for
##   type a3 (two cases done), and THEOREM H-a3-SL (the zero-row part of ker c cannot be strongly level), by 66 tiny systems; the
##   remaining gap is CONJECTURE K0 (e = 1 two-dimensional zero-row spaces need >= 2 zeros in the defect line).  Details R9.1 - R9.6.
 L1 [rigorous, R9.1] (D2), (C2): the degree-2 parts of D_0(Y)u and of the defect of Y in H, in the coordinates (s, a, b); checked against
    the direct permanent expansion (2.7e-13) on the verified 3-dim solution.
 L2 [rigorous, R9.1-R9.3] TYPE a3: (I1) 6X + (8/3)(Ss - s o s) + gamma 1 in C t', (I2) (b.u)(a.w) + (a.u)(b.w) = 0; hence every K lies
    in one of the CLOSED loci CA_jj', CB_jj' (two of the columns 0,1,2 coincide on K), E1, E2, E3.  E1, E2: UNIT 148/148 on all T0 orbit
    charts (instant).  E3 / CA / CB need more than the 0.5 GB pool cap -> optional big-slot route NCOL-HCASE-A3T0.
 L3 THEOREM H-a3-SL [modular 65521, closed projective, char 0 by semicontinuity of fibre dimension; R9.6] -- [CORRECTED R10.5: valid only
    when K_0 has zero row sums (q(K_0) = 0); strongly level K_0 with q in {1,2} form 1-dim families and are NOT covered]: in the last piece with U_0 of
    type a3, K_0 is not a strongly level rigid pair.  [SL_3 rigidity: K_0 = span(nu_1(e_a-e_b)^T, nu_2(e_c-e_d)^T); with K_0 fixed the admissible Y form a
    FINITE set for every C (64/66 charts UNIT, 2 single points at C = V_0123 (neutral) and C = V_012 + V_34); so dim ker c <= 3 < 4.]
 L4 [numerical, calibrated; R9.5] CONJECTURE K0: a 2-dim zero-row space with e = 1 has >= 2 zeros in its defect line (e = 1 solutions found
    for m = e_2 - e_3 but not for generic m, m = (x,x,x,y,z) or m = (x,x,y,y,z)).  With K0, the H-conjecture for a3 follows from L3
    (t' is zero-free for every non-neutral a3 C except V_012 + V_34, done in R8.6).  Exact check of K0 at a fixed m: over 0.5 GB (k2f.log).
 L5 [process] host memory: msolve needs >= 1.2 GB VIRTUAL even for tiny systems; ncol/gb/runlog_rss.sh enforces a RESIDENT cap instead.
 OPEN: CONJECTURE K0 (or the big-slot runs NCOL-HCONJ-A3T0 / NCOL-HCASE-A3T0); types b22 / b23 (same K_0 route: b22's t' is zero-free,
    b23's t' has two zeros); (SR3); (CCN).
## RESULT, ROUND 8 (ncol; 04:03 - 04:25 and 05:15 - 05:40 UTC, cut off in between by the usage limit) -- THEOREM L6G: with K' fixed, the general "Z" system has exactly 3 solutions in char 0, all
##   single-column elements of ker c; hence (COROLLARY K'-KILL) every case-(C) configuration whose zero-row part of ker c is 3-dimensional
##   is impossible (given the K' classification).  Case (C) is now down to ONE piece.  Details R8.1 - R8.3.
 K1 THEOREM L6G [modular 65521 (and 2147483629) + exact char-0 lengths + SN length argument; R8.1, R8.3]: for K' = span(n1 (e_1-e_2)^T,
    n2 e_3^T, n2 e_4^T), U_0 = C cap t^perp and Z with c(Z) in C t (c^(0)(Z) ARBITRARY), K' (+) e_0 U_0 (+) C Z is level with defect in C
    only for the 3 points Z = x e_j^T (x = (-1, 1/3, 1/3, 1/3), j = zero column or a single-column column of K', U_0 = {u_1 = u_2, u_j = 0}):
    34/39 charts UNIT, 5 charts with one reduced point each; char-0 Jacobian rank 14 = full at the 3 rational points.
 K2 COROLLARY K'-KILL [char 0, given K' classification]: no (7,3) space (non-isotropic w, u_i = 2) has the K' type inside the zero-row part
    of ker c: P(ker c / K') lies in 3 points, so rank c = 3 and a Z with c(Z) = t contradicts K1.  Covers sub-case dim(U_i + U_i o w) = 3
    (re-proves R211-3 without the Y_gamma normalisation) and sub-case dim = 2 with rank c = 2 or rho = 1.
 K3 [rigorous, R8.2] the remaining piece (dim(U_i + U_i o w) = 2, rank c = 3, rho = 2, dim K'' = 2): U_i is a sum over level sets of w;
    type a4 (U_i inside V_A, |A| = 4) has a neutral column; types a3, b22, b23 remain; 2-dim K'' are not rigid (numerical census).
 K4 [R8.5-R8.7] the last piece reduces to the H-CONJECTURE: no 4-dim column-centred ker c with row 0 in U_0^perp (1 not in s(ker c))
    such that ker c (+) e_0 U_0 is level with defect in C, for U_0 of type a3 / b22 / b23.  PROVED for type a3 with C = V_012 + V_34
    (family T2: 74/74 orbit charts UNIT by staged refinement, modular 65521, closed projective, RED-p).  Evidence for the rest: properly
    sampled LM (a3 4/4, b22 2/2, b23 2/2 stall at dim 4; dim-3 calibration solved and verified).  Generic C for a3 (family T0) running
    locally (hiter.sh) and queued (NCOL-HCONJ-A3T0); b22 / b23 generators written (hgen2.py) and queued (NCOL-HCONJ-B).
 K5 ERRATUM R8.4: LM probes lm2z / lm211 / early lmH were under-sampled (fake solutions); R6.10 withdrawn; no exact result affected.
 OPEN: H-conjecture (a3 generic C, b22, b23: big slot); K' classification (NCOL-K3CLASS); (SR3); (CCN).
## RESULT, ROUND 7 (ncol; 03:36 - 04:02 UTC) -- R2.11 (case (C), sub-case dim(U_i + U_i o w) = 3) is CLOSED CONDITIONALLY on an
##   explicit classification of the 3-dim zero-row K' (all K' found are ONE rigid type of three rank-one matrices); LEMMA SC (single-column
##   elements); the (7,3) chain written as one list.  Details R7.1 - R7.6.
 J1 [numerical 6/6 + exact point checks; R7.2] every 3-dim column-centred 3x5 level space with defect <= 1 found is
    K'(p,q;s1,s2) = (C(e_p - e_q), 0) (+) (0, span(e_s1, e_s2)) in isotropic coordinates (or the mirror): span(nu_1 (e_p-e_q)^T, nu_2 e_s1^T,
    nu_2 e_s2^T), zero column z, defect line m = e_p - e_q; the points are isolated and reduced (Jacobian rank 24, exact mod p).
    e = 1 exactly [rigorous, Lemma SL_3].  Exact classification: blocked by 2 GB segfaults (015_J0 UNIT; others fail).
 J2 THEOREM R211-3 [char 0, conditional on J1; projective 27/27 UNIT at 65521 AND 2147483629, Singular check; RED-p; R7.4 - R7.7]: given K', U_i = C cap t^perp and L'
    contains a 6-dim "case (B)" space L6 = K' (+) e_0 U_0 (+) C Z (c(Z) = t, c^(0)(Z) in C1), and no such L6 exists.  Calibration: the 5-dim
    part is automatic, the variant with c^(0)(Z) in span(1, d) is NONUNIT 15/15.  Affine 7-dim version also UNIT 15/15.
 J3 LEMMA SC [rigorous, R7.3]: x e_s^T in L' => for all Y: sum_{l != s} x.Y_{:,l} = 0 and (x.Y_{:,l})_{l != s} lies in C.
 J4 [R7.1] the (7,3) chain as one list: ROUTE SR3 = (DI_5;3) + (SR3) + R2.11 + CC3-e2; plus routes CC (CCN), ZR (CC3-e2 + SN + (PROD)), NCOL.
 OPEN: exact K' classification; case (C) sub-case dim(U_i + U_i o w) = 2; (SR3); (CCN); CC3-e2 (PROD-NCOL big slot).
## RESULT, ROUND 6 (ncol; 02:53 - 03:40 UTC) -- THEOREM SN PROVED (char 0, all 3 charts by two independent methods); NO SPLIT ISOTROPIC
##   (5,1) SPACE: the R3.2 shape (one zero, every dim P) and the two-zero case are both impossible (projective mod-p systems at p = 65521,
##   all charts, calibrated at the extremal size d = 4).  Details R5.12, R6.1 - R6.6.
 I1 THEOREM SN [proved; R5.4, R5.12, R6.2, R6.6]: length(Y_p + det M) = 24 / 12 / 0 in charts 01_01 / 01_02 / 01_23, each by std/vdim AND by
    multiplication matrices (commutativity asserted).  verify2's clarifications (completion Z_p; distinct reductions) are in R5.12.
 I2 THEOREM R32 [modular 65521, projective, RED-p -> char 0; given R5.1 (CC34 NOT needed, R6.9); R6.1, R6.3, R6.9]: no split isotropic (5,1) space with exactly
    one zero.  ONE closed system covers every dim P: (y', L'') on the incidence variety {(0|y') in L''} in P(V4) x Gr(4,11), times the
    m'-conic; 8 orbit charts x 4 m'-charts, 26 unknowns: UNIT 32/32.  Calibration: point check at the CC34 space (R_4 part 34/34, negative
    controls fail) and the same generator with 2-dim / 1-dim span (L' of dim 4 / 3) NONUNIT 8/8.
 I3 THEOREM Z2 [modular 65521, projective, RED-p -> char 0; R6.4, R6.5]: no split isotropic (5,1) space with exactly two zeros.
    m = (1,w,w^2,0,0); row 0 of ker c in Gamma(Cm) = span(1, e_3, e_4) by (F1); L'' in Gr(4,13), 82 orbit charts (715 charts), 36 unknowns.
    47 UNIT plain; the 35 charts that segfault at 2 GB are closed by STAGED REFINEMENT (add p_T = 0 for charts T already verified empty --
    closed conditions, sound by induction): 6 + 22 + 7 UNIT.  Calibration: 3-dim L'' NONUNIT (z_1_3_8), 1-dim alpha-pivot NONUNIT (z_0).
 I4 COROLLARY [char 0]: with R2.14 (zero-free, via CC3): NO (5,1) space has a row carrying an isotropic defect line.  (Branch 1.1 split
    isotropic case closed, modulo the inputs (F1), CC3 (zero-free case) and the RED-p computations; CC34 is not needed.)
 I5 [process] the 2 GB segfaults are beaten twice this round: GB-as-standard-basis + reduced Laplace det (SN), and staged chart refinement.
 I6 [R6.9] I2 re-proved WITHOUT CC34: L'' in Gr(4,11) directly, 52/52 UNIT (24 plain + 28 staged-refined).  Engine check: Singular reproduces
    msolve UNIT on 4 charts incl. a refined one (R6.7).
 OPEN: (CCN); (SR3); R2.11 (both are (6,3)/(7,3) problems: need structure
    before a chart system is feasible).
## RESULT, ROUND 5 (ncol; 02:00 - 02:52 UTC) -- THEOREM SN ("e <= 3 => same node", char 0) is reduced to ONE pending mod-p count:
##   charts 01_02 and 01_23 are DONE at p = 65521 (12 = 6 x 2, and 0); chart 01_01 (target 24) is running by two independent methods.
##   R3.2 shape: dim P = 1 excluded; dim P = 3 survives the P-internal conditions.  Details R5.1 - R5.11.
 H1 THEOREM SN (pending chart 01_01) [modular at the single prime 65521 + exact char-0 local length + rigorous lift; R5.4, R5.6-R5.11]:
    a product-type column-centred 3x5 level 4-space has e <= 3 iff it is a same-node pair W (+) W, W = span(e_k, chi_sigma); defect e_k^perp cap V5.
    (i)  [modular] pair GB degrees at 65521: 864 / 828 / 792, so Y_p is finite and Y is finite over Z_(p);
    (ii) [exact, Singular ds] local length of Y at the same-node points: 6 over Q(i), 6 mod 65521 (18/18 points);
    (iii)[modular, exact] one random 4x4 combination M (seed 7) of the 12 defect generators: local length of Y_p + det M = 2 at each
         same-node point (18/18); length(Y_p + det M) = 12 in chart 01_02 (target 12) and 0 in chart 01_23 (target 0); chart 01_01: PENDING (target 24);
    (iv) [rigorous] lift: a char-0 point with e <= 3 specialises to an F_p-point with e <= 3, which is a same-node point s-bar by (iii);
         if it were not s, the local algebra at s-bar would have generic length >= 6 + 1 > 6 = special length, impossible for a finite Z_p-module.
 H2 [rigorous + exact, R5.1, R5.5] R3.2 shape: alpha == 0, Q = P (+) C e_i m'^T, x_n = 4 - dim P; dim P = 1 impossible.
 H3 [exact + numerical, R5.10] dim P = 3 passes the P-internal conditions (CC34 calibration space, m' = (-1 +- i sqrt 2, 1, 1)), so
    excluding it needs column n.  The concrete system is written down in R5.10.
 H4 [identities, R5.3] Witt coordinates for column-centred 4x5 (towards (CCN)).  No proof of (CCN) yet.
 OPEN: chart 01_01 count; R3.2 dim P in {2, 3}; two-zero case; (CCN); (SR3); R2.11; PROD-NCOL (big slot).
## RESULT, ROUND 4 (ncol; 01:42 - 02:05 UTC) -- product spaces are RIGID and classified numerically (e = 3 exactly for the 30 same-node
##   pairs, e = 4 for general lines); THEOREM CC34 (no column-centred 3x4 level 4-space) -> R3.2 gets a single-column element; a tempting
##   column-centred shortcut to the whole of (DI_5) is refuted by a polished column-centred (4,2) space.  Details: R4.1 - R4.13.
 G1 [rigorous, R4.1-R4.2] Sing{e_3 = 0} = the 5 coordinate points; lines through a node e_k are span(e_k, v), v' in {e_2 = e_3 = 0}.  Product pairs
    through a node: both through the same node forces W_a = W_b = span(e_k, chi_sigma) (30 spaces, one S5-orbit, e = 3, defect = e_k^perp cap V5);
    two different nodes are impossible (B(e_i, e_j) = -1); node + non-node: finitely many (lines of a nodal cubic surface).
 G2 [modular -> char 0 by semicontinuity, R4.3] the set of product pairs is FINITE (3 orbit charts, 0-dimensional, degrees 864, 828, 792).
 G3 [numerical, R4.4, R4.8] chart (01,01): 745 general-line pairs found, all with e = 4; same-node pairs e = 3.  Conditional on (PROD) in char 0 (NOT given by PROD-NCOL, see R3.9) and the
    exact version of this ("e <= 3 => same node"), any 4-dim zero-row column-centred subspace of a (7,3) space forces a neutral column (R4.5).
    The exact E = 3 test segfaults at 2 GB (R4.13).
 G4 THEOREM CC34 [modular, projective, RED-p, 3 primes, point-calibrated; R4.9]: no column-centred 3x4 level space of dimension 4.
    => in the R3.2 shape (split isotropic (5,1), one zero) ker c contains a single-column element in the neutral column.
 G5 [rigorous reduction + numerical refutation, R4.12] (CC45) "column-centred 4x5 level 4-spaces have e >= 3" would give no (5,1), no (6,2) and,
    with (CCN), no (7,3) -- but it is FALSE (polished column-centred (4,2) space, e = 2 to 1e-12).  (CCN) "column-centred (4,3) spaces have a
    neutral column" survives (4/4) and closes the (7,3) sub-case rank c = 3, e(ker c) = 3 (R4.6).
 G6 (PROD) chart 0123 with isotropy eliminated (14 unknowns, R4.11) still segfaults at 2 GB: no local proof; big slot as scheduled.
 OPEN: (PROD) [big slot]; exact "e <= 3 => same node"; (SR3) / R2.11; (7,3) sub-cases e(ker c) <= 2 or rank c <= 2; R3.2 shape.

## RESULT, ROUND 3 (ncol; 00:57 - 01:40 UTC) -- column-centred 3x5 level 4-spaces EXIST (so CC3' is not free) but they look like products
##   W_a (+) W_b of lines on the cubic threefold {e_3 = 0}; for products, defect <= 2 is IMPOSSIBLE (exact, projective).  Details: R3.0 - R3.6.
 F0 [check, R3.0] E-STALE-OUTPUT: runners patched (output deleted first, FAILED on missing/old output or rc != 0); N2 (56/56 x 3 primes),
    its calibration, e3planes and the CC3 survivor checks all re-run and reproduced.
 F1 [numerical, fresh-point checked; R3.1, R3.3'] column-centred 3x5 level spaces of dim 4 exist: 8 LM hits (e = 4: four, e = 3: four), ALL of
    product type S = (W_a, 0) (+) (0, W_b) in isotropic coordinates.  (4,<=2): 0 hits.
 F2 [exact over Q(i,w3), R3.5] explicit example W_a = W_b = span(e_0, (0,1,i,-1,-i)), defect span(chi', chi'^2, chi'^3), e = 3.
 F3 [exact over Q via S5-symmetry + 3 primes; R3.1, R3.1'] e_3 vanishes on no 3-dim subspace of C^5 (all 10 charts of Gr(3,5)), so dim S_a, dim S_b <= 2.
 F4 [modular, projective -> char 0 by RED-p; R3.6] NO product-type column-centred 3x5 level 4-space has defect <= 2: 11/11 S5 x Z2 orbit
    charts of Gr(2,5) x Gr(2,5) x Gr(2,V5) UNIT at THREE primes (33/33, R3.7); calibration by exact point evaluation of the d2 and d3
    equations at the exact example (R3.6').  Over-Q spot check (Singular): chart 01_01_01 did not finish in 300 s (R3.10).
 F5 [reduction, R3.3] (PROD) "every column-centred 3x5 level 4-space is a product" <=> the Gr(4,10) charts of orbit types 0123, 0125, 0128 are
    empty; queued in the big slot (PROD-NCOL, 03:00-06:00 UTC).  [CORRECTED after verify2 R18: "non-product" is OPEN, so a UNIT PROD-NCOL at
    P1 does NOT give (PROD) in char 0; it DOES give CC3-e2 in char 0 together with PT2 at the same prime, by whole-cover RED-p on the closed
    variety {(S,G)} -- see R3.9.]  PROD-NCOL unit + F4 at P1 => CC3-e2 (no column-centred 3x5 level 4-space with e <= 2)
    => CC3' => residual R2.15 (isotropic w, u_i = 2, w in U_i) is dead, and CC3 gets a second proof.
 F6 [rigorous, R3.2] split isotropic (5,1) with one zero has the rigid shape L' = K'' (+) C e_i m^T (+) C Y_0 (K'' 3-dim zero-row column-centred,
    row i of Y_0 = -e_n); not yet excluded.
 OPEN: (SR3); R2.11; the R3.2 shape and the two-zero case; configurations (c), (d) (no progress this round).

## RESULT, ROUND 2 (ncol; 00:15 - 01:00 UTC) -- THEOREM CC3; a second route to "no (7,3)" via single-row elements (SR3); isotropic-w and
##   u_i = 2 rows reduced to CC3 and killed; generic hyperplanes of (e+4,e) spaces are non-principal.  Details: section R2 (R2.1 - R2.12).
 D1 [rigorous, R2.1] the generic hyperplane of an (e+4,e) space is NON-principal (principal ones exist only if ker c contains a strongly level
    3-space with s = V); so principal NCOL results reach (N_e+) only through such a kernel.
 D2 [rigorous, R2.2-R2.4] diagonal stabilizer Gamma(C) = span of block indicators; isotropic w => Gamma(C) = C1.  "Zero row on ker c" lemma: if
    c^(i)(Y) is always a multiple of 1, row i vanishes on ker c and C(ker c) is orthogonal to U_i.  In a (7,3) space: a row carrying C with isotropic
    w, or a row with u_i = 2 and dim(U_i + U_i o w) = 4, forces ker c to be a column-centred (4,1) space with a zero row.
 D3 THEOREM CC3 [rigorous case analysis + three small Groebner bases over Q, R2.10]: no column-centred 3x5 level space of dimension 4 has
    defect <= 1 (column-centred (DI_4) at e = 1; new).  Tool: isotropic coordinates (a, beta) (R2.5), in which P_2 = 3(sum a beta - AB),
    P_3 = 6(e_3(a) + e_3(beta)), and degree 2 becomes a^ o beta^ in span(1, m) (a pencil of rank-<=2 quadrics).
    => the D2 cases are IMPOSSIBLE; also (6,2) rows carrying a degenerate C with 1-dim radical.
 D4 [rigorous reduction, R2.8] NO (7,3)  <=  (DI_5;3) + (SR3) + [u_i = 2, dim(U_i + U_i o w) = 3, rank c = 3, gamma != 0 on ker c (R2.11)]
    + [isotropic w, u_i = 2, w in U_i], where (SR3) = "every (6,3) space has a single-row element" (NUM 23/23; false for e = 1, 2).
    This route needs no neutral column.  (N_3+) remains an alternative.
 D5 [numerical] isotropic w (6,3): 0/105 (w = (1,i,-1,-i,0)), 0/116 (w = (1,w3,w3^2,0,0)); control (1,1,1,1,-4): 3/52.  CC3 LM: see R2.13.
 OPEN after round 2: (SR3) [or (N_3+)]; the two residual u_i = 2 cases; (T2)/(N_2+); configurations (c), (d) (R2.12: twisted (c) with h(0) = 0
    is a 5-dim row-centred 4x4 space, extremal for L_gct_217); totally isotropic C in (6,2).

## RESULT, ROUND 1 (ncol; 23:37 - 00:20 UTC) -- exact chain for (6,2), (7,3); (DI_4x4) is NOT needed; (7,3) <= ONE statement (N_3+);
##   (6,2) <= (N_2+) + configurations (c), (d) only: configurations (a) and (b) EXCLUDED (Theorem N2, duality N3)
 Notation (rows R4): (d,e) space = 4x5 level space L' of dim d, defect space C = C(L') of dim e (C inside V5 := 1^perp of C^5); extremal: d = e+3.
 Column n NEUTRAL: C inside e_n^perp (equivalently Q := L' minus column n is a level 4x4 space).  For neutral n: L' = {(q|x)}, X_n = {x : (0|x)
 in L'}, e^col(Q) = dim span{M(q) - 24*1} (row deletions of Q).  (DI_5;k) := no (e+4,e) space with e < k.  (N_e+) := every (e+4,e) space has a
 neutral column.  Labels: "here" = proved in this file, not yet re-derived by verify2.

 STATUS TABLE (per PROOF-MAP; inputs I use):
  Lemma SL [V, Lean]; L_gct_214 (4x4 level <= 6), L_gct_215 (4x5 level <= 7) [checked upstream]; R4.10(a)-(d) transposed defect construction
  + padding [V]; Hyperplane Lemma R4.1 [V]; RS-HYP R4.3 [V]; FS-DEC R4.15 [V]; FL2* R3.9 [V]; chain R7.2(c) [V-r7]; R5.1 (TRI equivalence)
  [rows; definitions re-derived by verify2]; NCOL-S, NCOL-P3, P51, DC [V-r5/r6]; NCOL2-P under (G) [V, (G) fails on known planes];
  NCOL_1 generic two-column (2,1) [CL].  (NCOL_e), (N_e+), (DC-COST') in general: OPEN (NUM 120/120 for NCOL).

 C1 [rigorous, N1.1] SOME vs EVERY hyperplane: under (DI_5;e) all hyperplanes of an (e+4,e) space have the same C, so NCOL for one hyperplane
    <=> NCOL for every hyperplane <=> (N_e+).  "SOME" is a freedom of proof strategy only.
 C2 [rigorous, N1.2] NO (7,3)  <=  (DI_5;3) + (N_3+).   (DC-COST') at e = 3 is automatic: dim Q >= 4 + e^col(Q), and the padded (Q^T|0)
    violates SL / (DI_5;3) / L_gct_214.  So (DI_4x4) is never an extra hypothesis (it is the zero-column case of the floors + L_gct_214).
 C3 [rigorous, N1.3] (NC'_2): a (6,2) space with a neutral column (under no (5,1)) is one of (a) dim Q = 3, X_n = 1^perp; (b) dim Q = 4,
    dim X_n = 2; (c) dim Q = 5, dim X_n = 1; (d) dim Q = 6, X_n = 0.
 C4 [rigorous, N1.4] in a (7,3) space with non-isotropic w (C = w^perp cap V5) no row carries C: FS-DEC + FL2*.
 C5 [rigorous, N1.5] (6,2), C nondegenerate, no neutral column => u_i <= 1 for all rows, so the generic hyperplane is a (5,2) space with NO
    single-row element; (7,3), w non-isotropic => generic hyperplane has u_i <= 1 and sum U_i != C.  So (N_2+) <= (T2) "single-row-free extremal
    (5,2) spaces with nondegenerate C have a neutral column"; (N_3+) <= (T3) (analogue for (6,3)); degenerate C separately.
 C6 THEOREM N2 [rigorous reduction + projective mod-p computation, RED-p] configuration (a) is impossible (a 6-dim 4x5 level space with a full
    free column has e >= 3).  Hand part: forms/pencil argument (N2.1-N2.3) reduces to a 3-dim Q with two equal columns; that system (Gr(3,8),
    56 Pluecker charts, no saturation) is UNIT at 3 primes, calibration non-unit 32/56 at 3 primes (N2.4).
 C7 [rigorous, N3] TRANSPOSITION DUALITY for untwisted neutral-column spaces: (Q, Xh, Wh) -> (Q^T, Wh, Xh) preserves TRI (R5.1), giving a dual
    level space with d'' - e'' >= d - e.  Consequences: second 3-line proof of (a) (dual is strongly level of dim 4: SL); (b) is ALWAYS untwisted
    (e^col = 1 cancels the twist) and its dual is a (5,<=1) space: (b) EXCLUDED given no (5,1).
 X2 TEST [numerical] (6,3) with row 0 carrying C = V_012 + V_34: see N4 (0 hits; control C = V_0123: 83/100).  Not needed for the chain (C4).

 ANSWERS: (i) the reduction needs NCOL only for SOME hyperplane, which is the same as for every hyperplane (C1); (ii) (DI_4x4) is needed at
    NO e: e^col = 3 is L_gct_214, e^col = 1, 2 are zero-column cases of no (5,1), no (6,2) (C2).
 SINGLE STATEMENT THAT REMOVES THE MOST: (N_3+) (or its sharpened form (T3)): it closes (7,3) outright given the floors.  For (6,2): (N_2+)
    [(T2)] plus the two 4x4 configurations (c), (d) (both need a 4x4 level Q with dim Q > e^row(Q) + e^col(Q), never seen numerically).
STATUS 23:43: RESULT block (chain) written; proofs in N1 next; then X2 numerics and (N_3+).

## Section N1 (round 1): proofs of C1 - C4  [all rigorous hand arguments from VERIFIED ingredients; not yet re-derived by verify2]
 N1.0 Descent.  If (DI_5;k) holds and L' is a (d,e) space with e < k and d >= e+4, let K_0 be an (e+4)-dim subspace; e(K_0) =: e_1 <= e.
   If e_1 = e, K_0 is an (e+4,e) space, contradiction.  Otherwise take an (e_1+4)-dim subspace of K_0 and repeat; the defects strictly decrease
   until an (e'+4,e') space with e' < k appears ((4,0) included: Lemma SL).  QED.  [Used: defect of a subspace <= defect of the space.]
 N1.1 (C1).  Under (DI_5;e) the Hyperplane Lemma R4.1 [V] gives C(H) = C(L') for every hyperplane H of an (e+4,e) space L'.  "Column n is
   neutral for H" means C(H) in e_n^perp, i.e. C(L') in e_n^perp.  Hence neutral columns of H = neutral columns of L' for every H.  QED.
 N1.2 (C2): (DI_5;3) + (N_3+) => no (7,3).
   Let L' be a (7,3) space and n a neutral column (N_3+).  R4.10(b) [V]: dim L' = dim Q + dim X_n and dim X_n <= 3 - e^col(Q), so
   dim Q >= 4 + e^col(Q), with 0 <= e^col(Q) <= 3 (C^col(Q) lies in the 3-dim 1^perp of C^4).  R4.10(c)/R5.3(a) [V]: Q' := (Q^T | 0) is a
   4x5 level space of dim Q and defect dimension e^col(Q).  e^col = 0: Q' strongly level of dim >= 4, against Lemma SL.  e^col = 1, 2:
   Q' is a (d', e') space with e' <= 2 and d' >= e'+4, against (DI_5;3) by N1.0.  e^col = 3: dim Q >= 7 > 6, against L_gct_214.  QED.
   Remark: the same count is R5.3(b); the point is that the "4x4 defect problem" (DI_4x4) is nothing but the zero-column case of the floors.
 N1.3 (C3): (6,2) with a neutral column n, under (DI_5;2).  As in N1.2, dim Q >= 3 + e^col(Q).
   e^col = 0: dim Q <= 3 (padding lemma), so dim Q = 3 and dim X_n = 3: X_n = (C1)^perp = 1^perp (FULL FREE COLUMN n).
   e^col = 1: dim Q <= 4 by (DI_5;2) applied to Q', so dim Q = 4, dim X_n = 2 = 3 - e^col.
   e^col = 2: 5 <= dim Q <= 6 (L_gct_214): dim Q = 5, dim X_n = 1 = 3 - e^col; or dim Q = 6, X_n = 0.
   e^col = 3: dim Q = 6, X_n = 0.
   So: (a) dim Q = 3, X_n = 1^perp;  (b) dim Q = 4, dim X_n = 2;  (c) dim Q = 5, dim X_n = 1;  (d) dim Q = 6 (= the L_gct_214 maximum), X_n = 0.
   In (a)-(c) X_n = (C^col(Q) + C1)^perp exactly (saturation, as in all 135 census tower positions, where also s2 = 0).  QED.
   Partial result on (a) [rigorous]: X_n = 1^perp forces x.(M(q) - 24*1) = 0 for all x in 1^perp (R4.10(a)), so M(q) = 24*1 on Q; the degree-1
   part gives rho(q) = 0 (Q row-centred); L' = (Q|0) (+) (0|1^perp) is untwisted, and
        C(L') = span{ y^T (Adj(q) - 6J) : y in C^4, q in Q }   (on the columns != n; Adj as in R5.1),
   whose degree-1 part 2(q_i - kappa(q)) gives  C(L') contains every row of every q in Q.  So in case (a) with e = 2 all rows of all q lie in
   one 2-dim U inside 1^perp, and (Q^T|0) is a strongly level 3-space with all columns in U (row-sum rank <= 2: non-principal).
   Example (not a (6,2)): Q = {a chi^T : a in C^{012}}, chi = (1,i,-1,-i): L' = (Q|0) + (0|1^perp) is a (6,3) space (oracle: level 4e-14,
   e = 3; ncol/caseA_chi.py).  Open: exclude e = 2 in (a) (classify 3-dim row-strongly-level Q with rows in a plane), and (b)-(d).
 N1.4 (C4).  Let L' be a (7,3) space under (DI_5;3), C = w^perp cap V5 with <w,w> != 0, and suppose U_i = C for some row i.  Take a hyperplane
   H containing e_i (x) C; H is a (6,3) space with C(H) = C (R4.1 [V]), row i carries C, and C is nondegenerate (orthogonal complement of the
   non-isotropic w in the nondegenerate V5).  FS-DEC (R4.15 [V]): C = V_A + V_B with (|A|,|B|) = (4,1) or (3,2); hence w ~ |B| 1_A - |A| 1_B
   (no zero entry).  The lift L = L' (+) e_r (x) C w has dim 7 + 4 - 3 = 8 and contains T_U = e_i (x) U (+) e_r (x) U' with U = C,
   U' = (U + C1)^perp = C w, U cap U' = 0.  C o w = C (w is constant on the blocks A, B), so FL2* (R3.9 [V]) gives dim L <= 10 - 3 = 7.
   Contradiction.  QED.  [Isotropic w (C degenerate, w in C) is NOT covered.]
STATUS 23:50: N1 proofs written (C1-C4). Running: X2 test b32 (row 0 carries V_012+V_34) + control b41 (all hits so far); case (a) (6,2)-with-full-free-column search (calibration (5,2) 3/3).
 N1.5 (C5) REDUCTION OF (N_e+) TO GENERIC HYPERPLANES WITH FEW SINGLE-ROW ELEMENTS [rigorous; ingredients R4.1, R4.3 (RS-HYP), R4.15
   (FS-DEC), R3.9 (FL2*), all V].  Lifting (R4.7 [V]): a generic hyperplane H of L' has U_i(H) = U_i(L') cap H, so u_i(H) = max(u_i(L') - 1, 0).
   (a) (6,2) under no (5,1), C NONDEGENERATE, no neutral column  =>  u_i(L') <= 1 for every row, so a generic hyperplane H is a (5,2) space
       with C(H) = C and NO single-row element at all.
       Proof. Let U_i(L') = C.  A hyperplane H through e_i (x) C is an extremal (5,2) space with C(H) = C whose row i carries C.  FS-DEC, e = 2
       list: C inside V_A (|A| = 4) or C = V_A (|A| = 3) [neutral columns, excluded], or C = C u + C(e_a - e_b), u in V_A, |A| = 3,
       {a,b} = A^c, u_A zero-free (a zero of u in A is a neutral column).  Nondegenerate: <u,u> != 0.  W := (C + C1)^perp = {x : sum x = 0,
       x_a = x_b, <u,x> = 0} (2-dim).  C o W contains e_a - e_b (take x in W with x_a = 1) and u o W, which is 2-dim and supported on A
       (x -> u_A o x_A is injective on W).  So dim(C o W) = 3, and FL2* gives dim L <= 7 for the lift L = L' (+) e_r (x) W, whose dimension is
       6 + 4 - 2 = 8.  Contradiction.  QED
   (b) (7,3) under (DI_5;3), <w,w> != 0: u_i(L') <= 2 (C4), so a generic hyperplane H has u_i(H) <= 1 for all i, and sum_i U_i(H) != C (RS-HYP).
   CONSEQUENCE (sharpened targets; each implies the corresponding (N_e+) for nondegenerate C):
     (T2) every extremal (5,2) space with NO single-row element and nondegenerate C has a neutral column;
     (T3) every extremal (6,3) space with u_i <= 1 for all rows, sum_i U_i != C and non-isotropic w has a neutral column.
   (Numerically: the 3 known single-row-free (5,2) spaces have C = V_S, |S| = 3; the 10 known (6,3) spaces with dim sum U_i = 1 have
   C = V_S, |S| = 4 (rows R4.4).  (T2) follows from rows' (LAW) C = sum U_i + C_2 applied to H; (LAW) is unproved.)
   Left outside: DEGENERATE C ((6,2): C contains an isotropic radical vector or is totally isotropic; (7,3): w isotropic).

## Section N2 (round 1): configuration (a) of C3 (a (6,2) space with a FULL FREE neutral column)  [rigorous unless labelled]
 Setting: L' = (Q|0) (+) (0|1^perp) (N1.3: X_n = 1^perp forces M(q) = 24*1, rho(q) = 0, untwisted), Q 3-dim, row-centred, all four 3x4
 row deletions of Q level; C(L') = span{ y^T (Adj(q) - 6J) : y, q } (on the columns != n) contains R := span of all rows of all q.
 Write r_0..r_3 for the rows of q (linear forms on Q with values in R), sigma = sum r_i = kappa(q), g = dot form, tau(a,b,c) = sum_j a_j b_j c_j.
 N2.1 Row-deletion P_2, P_3 of three sum-zero rows: P_2 = -(sum of the three dots), P_3 = 2 tau(r_k,r_l,r_m).  Hence (L2) g(r_i, sigma - r_i) == 0
   for every i [sum over the deletions: T := sum_{k<l} g(r_k,r_l); deletion i gives T - g(r_i, sigma - r_i) = 0; summing, 4T = 2T, so T = 0];
   (L3) tau(r_k,r_l,r_m) == 0 for every triple of distinct rows.
 N2.2 dim R = 3 (R = 1^perp of C^4): e(L') >= 3.   dim R = 1: R = C rho_0, q = a rho_0^T; level of the 3x4 deletions forces
   e_2(rho_0) = e_3(rho_0) = 0 (some projection of the 3-dim coefficient space A in C^4 to three coordinates is onto, since A = C^4 otherwise),
   so rho_0 = permutation of chi = (1,i,-1,-i); level of Q forces e_4(a) == 0 on A, so A = C^S, |S| = 3: Q = C^S (x) chi (up to symmetry),
   L' is the (6,3) space of ncol/caseA_chi.py [oracle: level 3.8e-14, e = 3; numerical label for e = 3].
 N2.3 dim R = 2, e(L') = 2: then C(L') = R =: U = {1, v}^perp (v in 1^perp of C^4), i.e. Adj(q) v = 0 on Q.  Expanding perm(J + q with row i
   replaced by v) along the rows 1 + r_k: degree 2 gives (D2) sum_{k<l; k,l != i} beta(r_k,r_l) = 0, beta(a,b) := sum_j v_j a_j b_j, hence (as in
   N2.1) beta(r_i, sigma - r_i) == 0; degree 3 gives (D3) sum_j v_j r_kj r_lj r_mj == 0.  [|T| = 0, 1 terms vanish since sum v = 0, v perp U.]
   PENCIL ARGUMENT: every Phi in span(g|U, beta|U) satisfies Phi(r_i, sigma - r_i) == 0.
   (i) span 2-dim with two rank-1 members l1^2, l2^2: l(r_i) l(sigma - r_i) == 0 on Q forces, for each l = l1, l2, l(r_i) == 0 or l(r_i) == l(sigma);
       summing over i, l(r) is supported on at most ONE row; so q has at most two nonzero rows, each on a fixed line: dim Q <= 2. Contradiction.
   (ii) span = {l m' : m'} (double root of det): Phi = l^2 gives l(r) supported on one row i0 (or l(r) == 0, then dim R = 1); Phi = l m' then kills
       every row i != i0: dim Q <= 2.  Contradiction.   (iii) a 2-dim span of rank <= 1 forms does not exist.
   (iv) beta = lambda g on U: d := v - lambda 1 satisfies d o U inside U^perp = span(1, d).  Zero pattern of d: none / one zero -> contradiction
       (injectivity of a -> d o a); four zeros -> v = 0; THREE zeros -> U = V_S, |S| = 3: Q has a zero column t, so (Q^T|0) has a zero row and
       its strongly-level property is that of a 3x5 space with all 3x4 deletions level: dim <= 2 by Lemma SL_3 (R3.8 [V]). Contradiction.
       TWO zeros -> lambda = 0 and v ~ e_a - e_b: U = {x : sum x = 0, x_a = x_b}, i.e. COLUMNS a, b OF Q ARE EQUAL; then Adj(q) has equal
       columns a, b and C(L') lies in {c : sum c = 0, c_a = c_b, c_n = 0} automatically.
   RESULT N2: configuration (a) with e = 2 exists  <=>  there is a 3-dim 4x4 level space Q, row-centred, with all 3x4 row deletions level and
   TWO EQUAL COLUMNS (sub-case (iv-2)); then L' = (Q|0) + (0|1^perp) is a (6,<=2) space with two equal columns.  Numerical test: ncol/iv2_search.py.
 N2.4 SUB-CASE (iv-2) IS EMPTY [modular, projective => char 0 by RED-p; ncol/gb/iv2gen.py, runall.sh].  System: Q in Gr(3,8) (rows
   r_i = s_i u1 + p_i u2, U = {x : sum x = 0, x_0 = x_1} = span((1,1,-2,0),(0,0,1,-1))), equations = coefficients of (L2) g(r_i, sigma - r_i),
   (L3) tau(r_k,r_l,r_m) (4 triples), (L4) perm(q) = sum of the three pairings - 6 sum_j prod_i q_ij [identity for sum-zero rows; checked
   numerically], i.e. exactly "Q level + all row deletions level + rows in U" (N2.1).  All 56 Pluecker charts (pivot minor = I, 15 unknowns),
   integer coefficients, no saturation, no open condition: UNIT in 56/56 charts at p = 2147483629, 2147483497, 2147483077 (msolve 0.6.5,
   coefficients reduced mod p by construction; < 0.1 s per chart).  CALIBRATION (same generator, U = span(chi, e_0 - e_3), contains the known
   solutions C^S (x) chi): NON-unit in 32/56 charts at all three primes; chart 012 has the point m = 0 = C^{012} (x) chi (genuine).
   Numerical cross-check: ncol/caseA_search.py (L' = (Q|0) + (0|1^perp), defect inside an unknown plane of e_4^perp cap 1^perp): target
   (6,<=2) 0/264 (residual floor 3.4); same-shape calibrations (5,<=2) 3/3, (6,<=3) 13/20 (all e = 3).  chi-type e = 3 EXACT over Q(i)
   (ncol/caseA_chi_exact.py: rank 3).
   THEOREM N2 [rigorous reduction N2.1-N2.3 + the computation N2.4]: configuration (a) of C3 is impossible: a 4x5 level space with a
   full free column has defect dimension >= 3 if it has dimension 6.  (Equivalently: no (6,<=2) space contains 1^perp (x) e_n.)
STATUS 00:06: THEOREM N2: configuration (a) of the (6,2) residual (full free column) EXCLUDED (hand reduction to equal-column Q + projective mod-p system unit in 56/56 charts at 3 primes, calibration non-unit). X2 b32 running (0/345 so far; control 83/100).

## Section N3 (round 1): TRANSPOSITION DUALITY for untwisted towers -- a 3-line proof of THEOREM N2 and of configuration (b) untwisted
 N3.1 [rigorous; R5.1 [rows, used by verify2] + Adj(q^T) = Adj(q)^T].  Let L' = (Q|0) (+) (0|X) be an UNTWISTED 4x5 level space with neutral
   column n (X = X_n), W_0 := {w in C^4 : w perp 1, w perp C(L')} (dim 3 - e), Xh := C1 + X, Wh := C1 + W_0.  R5.1: this holds iff Q is level and
        (TRI)  Xh^T (Adj(q) - 6J) Wh = 0  for all q in Q.
   TRI is symmetric under (Q, Xh, Wh) -> (Q^T, Wh, Xh).  Hence the DUAL  L'' := (Q^T|0) (+) (0|W_0)  is again a level space with neutral
   column n and C(L'') perp X (C(L'') lies in {c : c_n = 0, c perp 1, c perp X}), so
        dim L'' = dim Q + 3 - e,   e'' := e(L'') <= 3 - dim X,   d'' - e'' >= d - e.
   [Check, ncol/dual_chk.py: the (5,2) and (6,3) full-free-column spaces of caseA_search give level (3,0) duals (level 5e-14, 6e-14).]
 N3.2 Consequences for the (6,2) residual C3 (untwisted members):
   (a) dim Q = 3, X = 1^perp (always untwisted): L'' is a strongly level space of dim 4 -> Lemma SL.  [= THEOREM N2, second proof; N2 stays as
       an independent check.]
   (b) untwisted, dim Q = 4, dim X = 2: L'' is a (5, <= 1) space -> excluded by (DI_5;2) (no (5,1)).
   (c) untwisted, dim Q = 5, dim X = 1: L'' is again of type (c) (self-dual);  (d) untwisted, dim Q = 6, X = 0: L'' is a (7, <= 3) space with a
       neutral column, i.e. (d) is dual to the (7,3) problem (circular with C2 at this level).
 STATUS OF (NC'_2) AFTER N2/N3: open only for TWISTED (b) [L' = {(q | tau(q) eta + X)}, twist = one linear form tau], (c) (untwisted: self-dual;
   twisted) and (d) (a 6-dim 4x4 level space Q = the L_gct_214 maximum, with a twisted column).  (d) would also follow from the unchecked
   n = 4 bound "4x4 level <= 5" (L-gct-091 in the BRIEF).
 N3.3 CONFIGURATION (b) IS ALWAYS UNTWISTED, HENCE EXCLUDED [rigorous].  In (b), e^col(Q) = 1: M(q) - 24*1 = m(q) mu with mu the row-defect line
   of Q and m a polynomial on Q, m not identically 0.  Write Y = (q | sigma(q) + xi), xi in X_n = (C mu + C1)^perp (saturated, N1.3).  Level
   (R4.10(a)): (sigma(q) + xi).(M(q) - 24*1) = 0, i.e. <sigma(q), mu> m(q) == 0 on Q; C[Q] is a domain, so <sigma(q), mu> == 0, hence
   sigma(q) lies in (C mu + C1)^perp = X_n and (q|0) is in L': L' is untwisted.  By N3.2(b) the dual is a (5,<=1) space: excluded by no (5,1).
   [The same argument untwists any neutral-column space with e^col(Q) = 1 and saturated X_n; it fails for e^col >= 2, where the level identity
   is sum_k <sigma(q), mu_k> m_k(q) == 0 and allows special twists.]
 STATUS OF (NC'_2): (a) and (b) EXCLUDED (given no (5,1)); left: (c) dim Q = 5, e^col = 2, dim X_n = 1 (untwisted: self-dual, Q would have
   e^row = e^col = 2, i.e. dim Q = e^row + e^col + 1, never seen); (d) dim Q = 6 (the L_gct_214 maximum), X_n = 0.
 N3.4 Twisted (c), structure [rigorous, partial]: with M(q) - 24*1 = m_1(q) mu_1 + m_2(q) mu_2 (m_1, m_2 independent) and lambda_k := <sigma(q), mu_k>,
   the level identity lambda_1 m_1 + lambda_2 m_2 == 0 forces either lambda == 0 (untwisted, self-dual case) or lambda_1, lambda_2 independent linear
   forms and M(q) - 24*1 = h(q) (lambda_2(q) mu_1 - lambda_1(q) mu_2) for a polynomial h (the row-defect vector factors through a LINEAR vector
   field orthogonal to the twist).  Not yet exploited.

## Section N4 (round 1): X2 test (rows COMPUTE X2) [numerical, calibrated]
 ncol/x2_search.py: L' = e_0 (x) C (+) N, C FIXED, N an unknown 3-dim complement (Gr chart, 42 unknowns), defect vectors p_k(Y) required
 perpendicular to 1 and w (i.e. inside C); 300 sample points (2.4x the 126 quartic monomials); hits checked with handoff/oracle.py.
   target  C = V_012 + V_34 (w = (2,2,2,-3,-3), no neutral column):  0 of 461 starts, residual floor 6.97 (t = 1500 s);
   control C = V_0123 (neutral column 4), same code:                  83 of 100 found, all oracle-confirmed (6,3) spaces (level <= 1e-13).
 So no FS-type (6,3) space with block pattern (3,2) was found: NCOL_3 for row-carried C is supported numerically (it is NOT needed for the
 (7,3) chain: C4 excludes row-carried C in (7,3) spaces rigorously for non-isotropic w).
STATUS 00:12: round 1 closing. X2: 0/461 (control 83/100). (a), (b) of the (6,2) residual excluded; (c), (d), (N_2+), (N_3+) open. Report next.
STATUS 00:16: ROUND 2 started (targets: (T3)/(N_3+), isotropic w / degenerate C, configs (c),(d), (T2)).

# ROUND 2 (start 00:15 UTC). Targets: (1) (T3)/(N_3+): u_i = 2 rows via diag(c^(i)(Y)), principal normal form at e = 3; (2) isotropic w,
#  degenerate C; (3) configuration (c) (self-dual TRI, twisted h.v), then (d); (4) (T2)/(N_2+).

## Section R2 (round 2)
 R2.1 GENERIC HYPERPLANES ARE NON-PRINCIPAL [rigorous].  Let L' be an (e+4,e) space under (DI_5;e).  If rank c(L') = e, ker c is 4-dim,
   not strongly level (SL); for a hyperplane H not containing ker c, ker(c|H) = ker c cap H runs over ALL 3-dim subspaces of ker c, so if the
   generic one were strongly level, ker c would be (identities vanishing on all 3-dim subspaces of a 4-space vanish on it): contradiction.  If
   rank c(L') < e, rank c|H < e for every H.  So principal hyperplanes (ker c|H strongly level with s = V) form a PROPER closed subset, nonempty
   iff rank c = e and ker c contains a strongly level 3-space K with s(K) = V ("principal (e+4,e) space").  NCOL results for principal extremal
   spaces therefore reach (N_e+) only through such a K (C1: one hyperplane suffices); the generic hyperplane is non-principal.
 R2.2 DIAGONAL STABILIZER [rigorous].  Gamma(C) := {d in C^5 : d o C inside C} is a unital subalgebra of C^5, hence = span{1_A : A in pi} for a
   partition pi, and C = sum_A (C cap C^A) with C cap C^A inside V_A.  For e = 3: pi nontrivial  <=>  C = V_A + V_B, |A|+|B| = 5 (dimension count
   sum (|A|-1) >= 3 forces two blocks), i.e. w ~ |B| 1_A - |A| 1_B (non-isotropic, (4,1) or (3,2) pattern).  ISOTROPIC w => Gamma(C) = C1.
 R2.3 THE "ZERO ROW ON ker c" LEMMA [rigorous, any e].  If c^(i)(Y) := column sums of the rows != i lies in C1 for every Y in L' (c^(i)(Y) =
   alpha(Y) 1), then row i vanishes on ker c.  Proof: on ker c, y^i = c(Y) - c^(i)(Y) = -alpha(Y) 1; if alpha(Y_1) = 1 for some Y_1 in ker c, row i
   of J + Y_1 is zero and every 4x4 deletion permanent vanishes, against sum_j C_j = 120.  QED.  Moreover, for u in U_i:
        <u, C(Y) - 24*1> = <y^i, D_i(Y) u>      [C(Y) = D_i(Y)(1 + y^i) by expansion along row i; D_i(Y) u in C is perp 1],
   so on ker c the defect vectors are orthogonal to U_i:  C(ker c) inside C cap U_i^perp.
 R2.4 ROWS CARRYING C OR A PLANE OF C IN A (7,3) SPACE [rigorous reductions].  (F1) gives d o u in C and d.u = 0 for d = c^(i)(Y), u in U_i, i.e.
   D_i := {c^(i)(Y)} inside (U_i + U_i o w)^perp (which contains 1).
   (A) u_i = 3, w ISOTROPIC: D_i inside Gamma(C) = C1 (R2.2), so by R2.3 ker c has zero row i and C(ker c) inside C cap C^perp = C w.  With
       dim ker c = 7 - rank c >= 4 and (DI_5;3): rank c = 3 and ker c is a column-centred (4,1) space with zero row i and defect line w.
   (B) u_i = 2, dim(U_i + U_i o w) = 4 ("case alpha"; generic): D_i inside C1, ker c has zero row i, C(ker c) inside C cap U_i^perp, which is
       1-dim for non-isotropic w ((span(1,w) + U_i) is 4-dim).  Again: rank c = 3 and ker c is a column-centred (4,1) space with a zero row.
   (C) u_i = 2, dim(U_i + U_i o w) <= 3 ("case beta"): there is a != 0 in U_i with a o w in U_i: either a is supported on a level set of w
       (w has a repeated value), or U_i = span(a, a o w) with a perp 1, w, w o w.  OPEN.
   In (A) and (B) everything is reduced to
     (CC3)  there is no column-centred 3x5 level space of dimension 4 with defect dimension <= 1
   (a 4x5 space with a zero row i is level iff its 3x5 part is; its deletion vectors are the 3x4 level polynomials).  (CC3) is the column-centred
   case of "(DI_4) at e = 1" (3-row defect inequality dim <= e + 2), which rows' numerics support but nobody has proved.
 R2.5 (CC3) IN ISOTROPIC COORDINATES [rigorous identities, checked numerically to 1e-14].  Columns of a column-centred 3x5 matrix lie in the
   2-dim space 1^perp of C^3; with nu_1 = (1,w,w^2), nu_2 = (1,w^2,w)/3 (w = e^{2 pi i/3}), y_j = a_j nu_1 + 3 beta_j nu_2, (a, beta) in C^5 x C^5:
        P_2 = 3(sum a_j beta_j - A B),  P_3 = 6(e_3(a) + e_3(beta))   (A = sum a, B = sum beta),
        P_2(Y^(j)) = 3(sum_{k != j} a_k beta_k - (A - a_j)(B - beta_j)),  P_3(Y^(j)) = 6(e_3(a^(j)) + e_3(beta^(j))).
   All coefficients rational: (CC3) is a system over Q.  Degree-2 part in hatted coordinates a^ = a - (A/2)1, beta^ = beta - (B/2)1:
   "P_2(Y^(j)) in C m for all j" <=> a^ o beta^ in span(1, m) on S, with sum_j a^_j beta^_j = (5/9)(sum a^)(sum beta^) from P_2 = 0.  For m = 0 this
   gives dim S <= 2 unless sum a^ sum beta^ == 0 (unique factorisation), i.e. Lemma SL_3 in the column-centred case.
 R2.6 (CC3), DEGREE-2 PART BY HAND [rigorous].  alpha_j := a^_j, b_j := beta^_j are linear forms on S (jointly injective, S 4-dim); degree 2 says
        alpha_j b_j = lambda + m_j mu   (all j),   lambda = sigma_a sigma_b / 9,  sigma_a = sum alpha_j, sigma_b = sum b_j,  mu a quadratic form.
   (i) lambda, mu independent and m has >= 4 distinct values: >= 4 distinct members of the pencil have rank <= 2; a 3x3 minor restricted to the
       pencil is a cubic, so EVERY member has rank <= 2: the pencil is binary in two forms l1, l2 (then all alpha_j, b_j lie in <l1,l2>: dim S <= 2)
       or has a common factor l (then {alpha_j, b_j} ~ {l, l' + m_j l''}: dim S <= 3).  [No member vanishes since lambda, mu are independent.]
       Contradiction.
   (ii) lambda = c mu, mu != 0: mu = l l' and {alpha_j, b_j} ~ {l, l'} unless m_j = -c; S^* = <l, l'> + (one free form per j with m_j = -c), so m
       has a value of multiplicity >= 2.   (iii) mu == 0: lambda != 0 gives dim S <= 2; lambda = 0 gives alpha_j b_j == 0 for all j (disjoint
       "supports" of a^ and beta^, as in the e = 0 case).
   So (CC3) survives the quadratic conditions only for m with a REPEATED value, or for disjoint supports; the cubic conditions F3, d3 must finish.
   The full system (all degrees) is the projective computation R2.7.
 R2.4' Refinement of (C) [rigorous]: if dim(U_i + U_i o w) = 3, then D_i inside span(1, d_0) (2-dim): c^(i)(Y) = alpha(Y) 1 + gamma(Y) d_0.  On
   K' := ker c cap ker gamma the R2.3 argument applies: row i = 0 on K' and C(K') inside C cap U_i^perp (1-dim for non-isotropic w).  If gamma
   vanishes on ker c, K' = ker c and we are back at (CC3); otherwise K' is a column-centred 3x5 space of dim >= 3 with defect <= 1 (allowed).
   Isotropic w with u_i = 2: if w is not in U_i the argument of (B) goes through verbatim (span(1,w) + U_i is still 4-dim) -> (CC3); if w in U_i,
   C cap U_i^perp is 2-dim and only e(ker c) <= 2 follows (open).
STATUS 00:30: R2.1-R2.6 written: generic hyperplanes non-principal; row-carried isotropic C and u_i = 2 (generic case) in (7,3) reduce to (CC3) (column-centred 3x5 (4,1)); CC3 degree-2 part by hand; CC3 exact charts generated (24 orbit reps / 840). Isotropic-w (6,3) LM running (iso1, iso2: 0 hits so far; control 3/52).
 R2.8 A SECOND ROUTE TO "NO (7,3)" THAT AVOIDS NCOL [rigorous reduction].  Under (DI_5;3) let L' be a (7,3) space.  If every row has u_i <= 1, a
   generic hyperplane H (a (6,3) space with C(H) = C) has NO single-row element (Lifting: u_i(H) = max(u_i - 1, 0)).  Hence
        (SR3)  "every (6,3) space [it suffices: every hyperplane of a (7,3) space] has a single-row element"
   forces a row with u_i >= 2, and then R2.4 applies: u_i = 3 is impossible for non-isotropic w (C4) and gives (CC3) for isotropic w; u_i = 2 gives
   (CC3) in case (B) and the partial case (C).  So
        NO (7,3)  <=  (DI_5;3) + (SR3) + (CC3) + [case (C) of R2.4] + [isotropic w, u_i = 2, w in U_i].
   No neutral column is needed on this route.  [numerical] (SR3) holds in 23/23 known (6,3) spaces (ncol/srow_chk.py on rows' clm/nc/seed files
   and my caseA/fixw hits): u = (0,0,1,0), (1,0,0,1), (1,2,0,0), (0,3,0,0), ...; also every one has a single-column element in its neutral column.
   The analogue for e = 2 is FALSE (3 single-row-free (5,2) spaces, all with C = V_S, |S| = 3), and for e = 1 too (non-split (4,1), two-column m).
 R2.7 (CC3) EXACT, FIRST ATTEMPT: generator ncol/gb/cc3gen.py (Gr(4,10) x P^3, 210 x 4 charts, 27 unknowns, 150 equations of degree <= 4; S5 x Z2
   symmetry reduces to 6 pivot orbits x 4 m-charts = 24 charts, ncol/gb/cc3d4_orb_P1/).  msolve SEGFAULTS under the 2 GB cap after 44 s on chart
   0123_m0 (memory); Singular test on the same chart running (cc3_0123_m0.sing.out).
 R2.6' (CC3), degree 2, SHARPENED [rigorous].  Note lambda = sigma_a sigma_b / 9 has rank <= 2 itself, so lambda is one more rank-<=2 member of the
   pencil (at t = 0).  e = 0 is Lemma SL_3 [V], so let m != 0 (sum m = 0, k := number of distinct values of m, k >= 2).
   - mu == 0: lambda != 0 gives dim S <= 2; lambda == 0 gives sigma_a == 0 or sigma_b == 0 (say sigma_b) and alpha_j b_j == 0 for all j, so
     S = {(a^, beta^) : supp a^ in J_a, supp beta^ in J_b, sum beta^ = 0} with J_a, J_b a partition (dimension count); then F3 == 0 splits into
     e_3(beta) == 0 on V_{J_b} (forces |J_b| <= 2) and e_3(a^ - (sigma_a/3)1) == 0 on C^{J_a} (fails: a^ = e_j gives 8/27).  DEAD.
   - lambda, mu independent: k >= 4 DEAD (R2.6 (i)); k = 2: the four factors of Pi_1, Pi_2 must be a basis z_1..z_4 of S^* (dim S = 4), and
     lambda = (t_2 z_1 z_2 - t_1 z_3 z_4)/(t_2 - t_1) has rank 4 unless t_1 t_2 = 0, impossible for a two-valued sum-zero m != 0: DEAD;
     k = 3 with 0 not a value: lambda, Pi_1, Pi_2, Pi_3 are four distinct rank-<=2 members: DEAD as in (i).
   SURVIVORS: (II-a) lambda = c mu, c != 0 (m has a value -c of multiplicity >= 2); (II-b) lambda = 0, mu != 0 (zero set T of m with |T| in {2,3});
   (I-3) lambda, mu independent and m has exactly three values, one of them 0.  In all survivors m has a repeated value or a zero entry;
   the cubic conditions F3, d3 have to finish them (not done by hand).
 R2.9 ISOTROPIC w, NUMERICS [numerical, calibrated weakly]: ncol/fixw_search.py, (6,3) spaces with C(L') inside w^perp cap 1^perp for a FIXED w
   (300 sample points, 2.4x the quartic monomials; hits checked with oracle):
     control w = (1,1,1,1,-4) (neutral column): 3 of 52 found (oracle-confirmed (6,3); lower rate than rows' 4/19, same code path);
     w = (1, i, -1, -i, 0)  (isotropic, one zero):  0 of 105 (residual floor 2.89);
     w = (1, w3, w3^2, 0, 0) (isotropic, two zeros, w3 = e^{2 pi i/3}): 0 of 116 (floor 2.53).
   So no extremal (6,3) space with isotropic w was found (NCOL_3 for isotropic w supported; with the low control rate this is weak evidence).
 R2.10 THEOREM CC3 [rigorous case analysis + exact Groebner bases over Q for three small survivor systems; ncol/cc3/survivors.py]:
   THERE IS NO COLUMN-CENTRED 3x5 LEVEL SPACE OF DIMENSION 4 WITH DEFECT DIMENSION <= 1.   (The column-centred case of "(DI_4) at e = 1".)
   Proof (notation R2.5/R2.6; S 4-dim, alpha_j = a^_j, b_j = beta^_j span S^*; G(x) := e_3(x - (sum x/3) 1) = (p_3(x) - p_1(x)^3/9)/3, so that
   F3 = G(a^) + G(beta^), and G = e_3 on sum-zero vectors).  Defect 0 is Lemma SL_3 [V]; so m != 0.  Degree 2: alpha_j b_j = lambda + m_j mu,
   lambda = sigma_a sigma_b / 9.
   (III) mu == 0: dead (R2.6').
   (I) lambda, mu independent: {0} u values(m) has >= 3 elements (values {0,t} contradict sum m = 0), giving three pairwise independent
       rank-<=2 members Pi_t = lambda + t mu; if their factors spanned 4 dims, a Pi_1 + b Pi_2 (ab != 0) would have rank 4; so all factors lie in a
       3-dim U, the whole pencil lies in Sym^2 U, every alpha_j, b_j (factors of Pi_{m_j} != 0) lies in U: dim S <= 3.  DEAD.
   (II) lambda = c mu, mu != 0 (rank <= 2), T := {j : m_j = -c}; for j not in T, {alpha_j, b_j} ~ factors of mu; for t in T, alpha_t b_t = 0, the
       nonzero one f_t lies in T_a (alpha) or T_b (b).  Restrict to S'' := common kernel of the factors of mu: there a^ lives on T_a, beta^ on T_b.
     (II-b) c = 0: WLOG sigma_b == 0, so sum_{T_b} f_t lies in <factors>; |T| <= 3.  mu = l^2: |T| = 3, T_b empty, a^|S'' free on C^3, G(e_t) = 8/27.
       mu = l l': |T| = 2: T_b empty, a^|S'' free on C^2: 8/27.  |T| = 3: T_b empty -> the image W (2-dim) of a^|S'' would lie on the cone
       9 p_3 = p_1^3 in C^3, an IRREDUCIBLE NODAL cubic (one ordinary node at (1:1:1), tangent cone 18(u^2 - u + 1); no line); |T_b| = 1: 8/27;
       |T_b| = 2: G = (8/27) h^3; |T_b| = 3: e_3 on all of V_3.  DEAD.
     (II-a) c != 0: sigma_a ~ l, sigma_b ~ l' (factors of mu = sigma_a sigma_b/(9c)), so on S'' both a^ and beta^ have sum 0 and F3|S'' =
       e_3(a^|S'') + e_3(beta^|S''); new dimensions <= (|T_a|-1)_+ + (|T_b|-1)_+, |T| <= 4.  All partitions die on S'' (e_3 does not vanish on V_3 or
       V_4, 8/27 terms) EXCEPT |T| = 4 (m ~ (1,1,1,1,-4)), mu of rank 2, partitions (4,0) [image of a^|S'' = a pairing plane {(x,-x,y,-y)}: the
       cubic p_3 = 0 on P(V_4) is the union of the three pairing lines] and (2,2).  These three systems (with both orientations of (alpha_p, b_p),
       all remaining coefficients free, c k != 0 enforced by inv*k*c = 1) have Groebner basis [1] over Q; calibrations: without the cubic
       conditions the systems are consistent (non-unit), with F3 alone or with d3 alone they are already unit.  QED.
   CONSEQUENCES: R2.4 (A) and (B) are IMPOSSIBLE; in (7,3): no row carries C when w is isotropic; no row with u_i = 2 and dim(U_i + U_i o w) = 4
   (w non-isotropic, or isotropic with w not in U_i); in (C) the sub-case gamma|ker c == 0.  In (6,2): a row carrying a DEGENERATE C with 1-dim
   radical and trivial stabilizer is impossible (R2.3: ker c has a zero row and defect in rad C; dim ker c >= 4; no (5,1); CC3).
STATUS 00:43: THEOREM CC3 proved (no column-centred 3x5 (4,1) space): hand case analysis + 3 survivor systems unit over Q. Kills R2.4 (A),(B) in (7,3) and row-carried degenerate C (1-dim radical) in (6,2).
 R2.11 What is left of case (C) of R2.4 after CC3 [rigorous]: K' = ker c cap ker gamma has a zero row and defect <= 1 (non-isotropic w), so by
   CC3 dim K' <= 3; hence rank c = 3, dim ker c = 4 and gamma does not vanish on ker c.  Open: this sub-case, and isotropic w with u_i = 2,
   w in U_i.
 R2.12 Configuration (c), twisted (N3.4): if h has no constant term, rho == 0 and Q is a 5-dim ROW-CENTRED 4x4 level space, i.e. an extremal
   space for the checked L_gct_217 (<= 5); if h(0) != 0, rank rho = 2 and rho(q) is orthogonal to the twist sigma(q).  Not pursued further.
 R2.14 COROLLARY FOR BRANCH 1.1 (split isotropic case of (5,1)) [rigorous, from R2.2-R2.3 + CC3]:
   GENERAL FORM: if a 4x5 level space L' of dim d and defect e has a row carrying its defect space (U_i = C), the stabilizer Gamma(C) is trivial
   (= C1) and dim rad C <= 1, then d <= e + 3.   [(F1): c^(i)(Y) in Gamma(C) = C1; R2.3: ker c has zero row i and defect in rad C; dim ker c
   >= d - e; if d - e >= 4, a 4-dim subspace of ker c contradicts CC3.]
   e = 1: Gamma(C m) = {d constant on supp m}, trivial iff m has NO zero entry; rad(Cm) = Cm or 0.  Hence:
     NO (5,1) SPACE CONTAINS e_i m^T WITH m ZERO-FREE -- in particular for ISOTROPIC zero-free m, the case left open by Theorem SPLIT /
     FL2* (rows R3.9(a), verifyfl R3.4: "the split case stays open there").  (Non-isotropic zero-free m was NCOL-S (a), dim <= 3.)
   Left of the split isotropic case: isotropic m with 1 or 2 zeros (|supp m| = 4 or 3).
STATUS 00:46: R2.14: CC3 also closes the split (5,1) case with zero-free (incl. isotropic) m. Waiting for CC3 LM cross-check; report next.
 R2.15 Residual "isotropic w, u_i = 2, w in U_i" [rigorous reduction]: U_i = span(w, u); generically dim(U_i + U_i o w) = 4, D_i inside C1, and
   R2.3 gives: ker c (dim >= 4) has a zero row and C(ker c) inside P := span(1, w, u)^perp, a DEGENERATE plane (w lies in P and is orthogonal to
   P).  So this residual reduces to (CC3'): "no column-centred 3x5 level space of dim 4 has its defect inside a degenerate plane" (an e = 2
   statement; CC3's pencil becomes a net).  Not attempted.
 R2.16 (6,2) rows with u_i = 1 [rigorous, partial]: C nondegenerate, no neutral column, U_i = C u.  (F1): D_i inside span(u, u o w1, u o w2)^perp
   (C = {1, w1, w2}^perp).  If that span is 3-dim, c^(i)(Y) = alpha 1 + gamma d_0 and K' = ker c cap ker gamma has a zero row with defect inside
   C cap u^perp (1-dim); dim K' >= dim ker c - 1, so CC3 forces rank c = 2 and gamma != 0 on ker c (the same residual shape as R2.11).
 R2.10' Independent engine for the CC3 survivors: ncol/cc3/survivors_ms.py writes the same three systems mod p (coefficients reduced mod p)
   and runs msolve: UNIT for (4,0), (2,2) orient 0, (2,2) orient 1 at p = 2147483629, 2147483497, 65521 (agrees with sympy over Q).
 R2.13 CC3 by LM [numerical; NOT a calibrated negative]: ncol/cc3_search.py (finite-difference LM on Gr(D,10) + defect chart, 70 sample
   points, fresh-point check of hits): target (4,<=1) 0 of 25 (floor 3.25); calibrations: (2,0) 3 of 4 (strongly level column-centred planes,
   fresh-point residual <= 2.5e-14), (3,<=1) 0 of 4, (4,<=2) 0 of 17 (floor 1.74).  The same-shape control finds nothing, so this run is only
   consistent with CC3 (which is proved exactly, R2.10); it also suggests that column-centred 3x5 level spaces of dim 4 may not exist at all
   (that would give (CC3') of R2.15 for free) -- unproved.
STATUS 00:54: round 2 closing; CC3 proved (sympy over Q + msolve 3 primes on survivors); report next.
STATUS 00:57: ROUND 3 started (targets: existence of column-centred 3x5 dim-4 level spaces -> CC3', R2.11; (SR3); R2.14 with zeros; config (c),(d)).

# ROUND 3 (start ~00:57 UTC). Targets: (1) do column-centred 3x5 level spaces of dim 4 exist at all (exact, reduced Gr(4,10))? -> CC3', R2.11;
#  (2) (SR3) on generic hyperplanes of (7,3); (3) R2.14 for isotropic m with 1 or 2 zeros; (4) configuration (c) twisted h(0) = 0, then (d).
 R3.1 COLUMN-CENTRED 3x5 LEVEL SPACES OF DIMENSION 4 EXIST [numerical, fresh-point checked]: ncol/cc3_search.py 4 -1 (no defect condition):
   hit at seed 19 (residual 2.2e-13, fresh-point level residual 2.4e-12 on 40 points, rank 4), file ncol/cc3_d4_e-1_s19.npy; its defect
   dimension is 4 (deletion-vector singular values 1, .57, .39, .27, 0).  Dim 3: 30/30.  So CC3' is NOT free; the defect bound matters.
   Also [modular, projective, all 10 charts of Gr(3,5), 1 prime]: e_3 vanishes on NO 3-dim subspace of C^5 (ncol/gb/e3planes/), so in any such S
   the pieces S_a = S cap (C^5 + 0), S_b = S cap (0 + C^5) have dim <= 2.  The full no-defect system (Gr(4,10), 24 unknowns, 30 equations)
   segfaults msolve at the 2 GB cap (86 s).
STATUS 01:03: R3.1: column-centred 3x5 dim-4 level spaces EXIST (defect 4); CC3' not free. Running LM (4,<=2), (4,<=3).
 R3.2 SPLIT ISOTROPIC (5,1) WITH ONE ZERO: STRUCTURE [rigorous, from R2.2-R2.3 + CC3].  Let L' be a (5,1) space with defect line C m, m isotropic,
   m_n = 0 the only zero, e_i m^T in L'.  Then Gamma(C m) = span(1, e_n), so c^(i)(Y) = alpha(Y) 1 + delta(Y) e_n and row i of every Y is
   y^i = kappa(Y) m - alpha(Y) 1 - delta(Y) e_n (c(Y) = kappa m).  On ker c: alpha = 0 (otherwise row i of J + Y_1 is a multiple of e_n and
   C_n(Y_1) = 0, against C_n == 24), so y^i = -delta e_n.  CC3 forces rank c = 1 and delta != 0 on ker c (else a 4-dim zero-row column-centred
   space with defect <= 1).  K'' := ker c cap ker delta is 3-dim with zero row i; H := ker delta (a hyperplane: delta == 0 on L' would make
   K'' = ker c 4-dim) satisfies alpha = zeta kappa on H, and e_i m^T in H gives zeta = 0.  HENCE
        L' = K'' (+) C e_i m^T (+) C Y_0,     K'' = column-centred 3-row level space (rows != i) of dim 3 with defect in C m,
        Y_0 in ker c with row i of Y_0 = -e_n (so the other rows of Y_0 have column sums e_n).
   Open: exclude this shape (K'' satisfies D(Z'') m in C m and D(Z'') 1 in 24*1 + C m; plus the cross conditions with Y_0).
 R3.3 [numerical] EVERY dim-4 hit so far is of PRODUCT TYPE: S = (W_a + 0) (+) (0 + W_b) in (a, beta) coordinates (r_a = r_b = 2), with W_a, W_b
   2-dim subspaces of C^5 on which e_3 vanishes (lines on the cubic threefold X = {e_3 = 0} in P^4) and W_a orthogonal to W_b for
   B(a, beta) = a.beta - (sum a)(sum beta).  Hits: s19 (e = 4), s103 of the (4,<=3) run (e = 3), s27 (see below).  Rigorous facts: product-type S
   has all Pluecker coordinates with 4 or 3 a-pivots (or b-pivots) equal to 0; conversely, if those vanish then rank pi_a, rank pi_b <= 2 and S is
   of product type (block-triangular minors).  So (PROD) "every column-centred 3x5 level space of dim 4 is of product type" <=> the Pluecker charts
   of orbit types 0123, 0125, 0128 (Gr(4,10), S5 x Z2) are empty.  Chart 0123 segfaults msolve at 2 GB.
   For product type the defect is explicit: d2(a, beta) = A beta + B a - 2 a o beta (bilinear W_a x W_b -> V5), d3 = d3^a(a) + d3^b(beta) with
   d3^a_j(a) = -a_j (e_2(a) - A a_j + a_j^2) (using e_3 == 0 on W_a).
 R3.0 E-STALE-OUTPUT CHECK (coordinator request, BRIEF UPDATE 14): my runners runall.sh / runlog.sh / runlog_big.sh did not delete the output
   before msolve.  All .out files of N2 (iv2_*, cal_*) and e3planes were newer than their .ms, but that does not exclude a crashed rerun, so I
   PATCHED the runners (rm -f output first; FAILED if rc != 0, output missing/empty or older than the input; verdict read after the '#---' line)
   and RE-RAN everything: iv2 56/56 UNIT at all 3 primes, cal 32/56 NONUNIT at all 3 primes, e3planes 10/10 UNIT, all identical to before; the
   CC3 survivor msolve check (survivors_ms.py, also patched) again UNIT x 3 systems x 3 primes.  (The CC3 survivors' primary certificate is
   sympy over Q, unaffected.)  Segfaulted charts were always reported NONUNIT/rc=139, never UNIT.
STATUS 01:11: stale-output check done (all verdicts reproduced with patched runners). Product-type defect charts generated.
 R3.3' LM census of column-centred 3x5 level 4-spaces [numerical, fresh-point checked]: free run 4/58 hits (s19, s27, s39, s48: e = 4), (4,<=3) run
   4 hits (s103, s115, s116, s117: e = 3), (4,<=2) run 0 hits so far; ALL 8 are of product type (r_a = r_b = 2).  So (PROD) is well supported;
   the exact test is queued (PROD-NCOL, big slot, ~03:00-06:00 UTC).
 R3.4 PRODUCT-TYPE DEFECT TEST (exact, running): ncol/gb/prod/prodgen.py P E: unknowns W_a, W_b in Gr(2,5) charts and the annihilator of an
   E-dim D in V5 (Gr(4-E,4) chart, representatives in C^5/C1 with g_4 = 0); equations e_3|W_a = e_3|W_b = 0, B(W_a, W_b) = 0, g.d2 = g.d3a =
   g.d3b = 0 (16 unknowns, ~36 equations, no saturation; projective over Gr x Gr x Gr).  E = 2: 600 charts (target: UNIT everywhere means every
   product-type space has e >= 3, hence -- with PROD-NCOL unit at the same prime, via CC3-e2 (R3.9) -- CC3' and R2.15 die); E = 3: 400 charts (calibration: must be NON-unit somewhere, the
   e = 3 hits exist).
 R3.5 AN EXACT EXAMPLE [exact over Q(i, w3), ncol/exact_prod.py]: chi' := (0, 1, i, -1, -i); W := span(e_0, chi') is a line on X = {e_3 = 0}
   (e_3(x e_0 + y chi') = x y^2 e_2(1,i,-1,-i) + y^3 e_3(1,i,-1,-i) = 0) and W is B-isotropic (B(e_0,e_0) = 1 - 1, B(e_0,chi') = 0, chi'.chi' = 0).
   So S = W (+) W (a, beta both in W) is a column-centred 3x5 level space of dim 4; its defect space is span(chi', chi'^2, chi'^3) (entrywise
   powers), dimension 3 (exact rank).  It calibrates the product-type generator: with only the d2 condition imposed (d2 spans span(chi', chi'^2),
   2-dim) it is a point of the E = 2 'only d2' system in chart 01_01_01.
 R3.6 PRODUCT-TYPE: DEFECT <= 2 IS IMPOSSIBLE [modular, projective -> char 0 by RED-p; ncol/gb/prod/prodgen2.py, reps_e2.txt].
   Unknowns: W_a, W_b in Gr(2,5) (S5-equivariant pivot charts), G = D^perp cap V5 in Gr(2, V5) with S5-equivariant pivot charts (g_r[p_r] = 1,
   g_r[p_{1-r}] = 0, sum g_r = 0); the system is invariant under S5 (simultaneous coordinate permutation) and Z2 (W_a <-> W_b), and the
   1000 chart triples fall into 11 orbits (01_01_01, 01_01_02, 01_01_23, 01_02_01, 01_02_03, 01_02_12, 01_02_13, 01_02_34, 01_23_01,
   01_23_02, 01_23_04).  Equations: e_3|W_a = e_3|W_b = 0, B(W_a, W_b) = 0, G.d2 = G.d3a = G.d3b = 0 (16 unknowns), integer coefficients,
   no saturation.  RESULT at p = 2147483629: UNIT in 11/11 orbit charts (1.5 - 120 s each, stale-safe runner).  [Primes 2147483497,
   2147483077 and the calibration (only-d2 system, chart 01_01_01 contains the exact point of R3.5) running.]
   => every product-type column-centred 3x5 level 4-space has defect dimension >= 3 (sharp: R3.5, LM hits with e = 3).
   With a UNIT PROD-NCOL at the same prime (queued in the big slot) this gives CC3-e2 "no column-centred 3x5 level 4-space with defect <= 2" in char 0 (R3.9), hence CC3' and R2.15 die,
   and CC3 gets an independent second proof.
STATUS 01:22: R3.6: product-type column-centred 3x5 4-spaces have defect >= 3 (11/11 orbit charts UNIT at P1); 2 more primes + calibration running; PROD queued (big slot).
 R3.6' CALIBRATION by POINT EVALUATION (independent of msolve; ncol/gb/prod/pointcheck.py): at the exact point of R3.5 in chart 01_01_01
   (W_a = W_b = span(e_0, chi'), G = D2^perp cap V5 with D2 = span(chi', chi'^2) = span of d2), all 20 equations of the only-d2 system vanish
   mod p (so that chart is NON-unit and the generator's e_3, B and d2 equations are right at a genuine solution); in the full E = 2 system
   exactly the 4 d3-equations do not vanish (the point has e = 3).  The msolve run of the positive-dimensional calibration was stopped
   (> 1 min, 0.9 GB).
 R3.1' E3P at three primes: the e_3-planes system (all coefficients are small positive integers, so the files for other primes are the same
   polynomials) is UNIT in 10/10 charts also at p = 2147483497 and 65521 (stale-safe runner).
   Also the only-d3a system vanishes identically (20/20 equations) at the same point with G = D3a^perp, D3a = span(chi'^2, chi'^3) = span of
   d3a values: the d3 equations are validated too (d3b is the same code with b).
STATUS 01:31: product-type defect<=2 test at primes 2,3 nearly done (18/22 UNIT); point calibrations pass; next: ra4 evidence, report.
   E3P over Q: all ten pivot triples of Gr(3,5) form ONE S5-orbit and e_3 is S5-invariant, so chart 012 suffices; its coefficient system has
   Groebner basis [1] over Q (sympy).  E3P is therefore [exact]: e_3 vanishes on no 3-dim subspace of C^5.
 R3.7 R3.6 at three primes: the 11 orbit charts are UNIT at p = 2147483629, 2147483497 and 2147483077 (33/33, stale-safe runner, 1.5 - 130 s
   per chart).  THEOREM PT2 [modular, projective, RED-p => char 0; calibrated by exact point evaluation]: no product-type column-centred 3x5
   level space of dimension 4 has defect dimension <= 2.
STATUS 01:34: THEOREM PT2 (product type => e >= 3) at 3 primes. Over-Q spot check (Singular, 2 charts) and r_a=4 evidence running.
 R3.9 CONSEQUENCES OF CC3-e2 [rigorous reductions].  [REWORDED after verify2 R18.]  CC3-e2 := "no column-centred 3x5 level 4-space has
   defect <= 2" is the emptiness of the CLOSED projective system {(S, G) : S in Gr(4,10) column-centred level, G in Gr(2, V5), defect of S
   orthogonal to G}.  Mod P1, every F_p-bar point would have S either non-product (excluded if PROD-NCOL is UNIT at P1) or product with e <= 2
   (excluded by PT2 at P1); so a UNIT PROD-NCOL at P1 plus PT2 at P1 gives CC3-e2 in characteristic 0 by whole-cover RED-p.  (PROD) itself in
   char 0 is NOT obtained this way (non-product is an open condition).  Consequences of CC3-e2:
   (i) CC3' holds, so residual R2.15 (isotropic w, u_i = 2, w in U_i) is impossible;
   (ii) CC3 gets a second proof;
   (iii) (6,2) with a row carrying a TOTALLY ISOTROPIC C: Gamma(C) = C1 for a 2-dim totally isotropic C? -- if yes, R2.3 gives ker c (dim >= 4)
        with a zero row and defect inside rad C = C (dim 2): CC3-e2 kills it.  [Gamma(C) for e = 2: nontrivial only for the FS-DEC list of R4.15
        (C inside V_A |A| = 4, C = V_A |A| = 3, C = C u + C(e_a - e_b)); a totally isotropic plane can only be C u_iso + C(e_a - e_b) if
        e_a - e_b were isotropic, which it is not, so Gamma(C) = C1 unless C has a neutral column.]  So: (6,2) with a row carrying a totally
        isotropic C has a neutral column (or is impossible).
   Not reached: R2.11 and the R3.2 shape (both have only 3-dim zero-row subspaces).
 R3.8 (PROD), stratum r_a = 4 in the affine OG chart (ncol/gb/ra4/ra4gen.py: 14 unknowns, 20 equations of degree <= 9; evidence only, an
   affine chart is not RED-p-safe): msolve segfaults at the 2 GB cap (46 s).  (PROD) stays with the big-slot job PROD-NCOL.
 R3.10 Over-Q spot check of PT2 (Singular std over Q, 300 s boxes, ncol/gb/prod/q0/): chart 01_01_01 timed out (halt); chart 01_01_23 see
   ncol/gb/prod/q0 run log (pending at 01:38).  The char-0 conclusion of PT2 rests on RED-p (projective system, no saturation, 3 primes).
STATUS 01:37: round 3 closing; report next.
STATUS 01:39: ROUND 4 started (targets: lines on X = {e_3=0} in product spaces -> hand route to PT2/(PROD); R2.11; (SR3); R3.2 shape).

# ROUND 4 (start ~01:42 UTC). Targets: (1) classify the lines on X = {e_3 = 0} occurring in product spaces, defect spans; hand route to PT2 and
#  (PROD) (graph strata); (2) R2.11; (3) (SR3); (4) R3.2 shape and the two-zero case.
 R3.10' Over-Q spot check: Singular timed out (300 s) on both charts 01_01_01 and 01_01_23; PT2's char-0 status rests on RED-p.

## Section R4 (round 4)
 R4.1 SINGULAR POINTS OF X = {e_3 = 0} in P^4 [rigorous]: grad e_3 = (e_2(x^(i)))_i and e_2(x^(i)) = e_2 - x_i e_1 + x_i^2, so at a singular point
   every x_i is a root of t^2 - e_1 t + e_2: x takes at most two values; checking the multiplicities, Sing(X) = the five coordinate points e_k.
 R4.2 LINES THROUGH NODES [rigorous]: W = span(e_0, v), v_0 = 0, lies on X iff e_2(v') = e_3(v') = 0 (v' = (v_1..v_4)); a curve C_0 of degree 6
   in P^3 for each node.  PRODUCT PAIRS WITH A NODE:
   (a) both lines through the same node e_0: B(e_0, v'') = -sum v'', so sum v = sum v'' = 0, whence e_1 = e_2 = e_3 = 0 on v', v'': v', v'' are
       orderings of (1, i, -1, -i) (6 classes); B(v, v'') = v'.v'' vanishes only for v'' ~ v'.  So W_a = W_b = span(e_k, chi_sigma): 30 spaces, one
       S5-orbit, defect 3 (R3.5).
   (b) lines through two DIFFERENT nodes: impossible, B(e_i, e_j) = -1.
   (c) W_a through e_0, W_b through no node: W_b lies in H_0 = {beta_1 + .. + beta_4 = 0}, a cubic surface X cap H_0 =
       {beta_0 (-p_2(beta')/2) + p_3(beta')/3 = 0} with a node at e_0 (6 lines through it = (a)), so W_b is one of the other lines of this nodal
       cubic surface, and v' is cut out on C_0 by two linear conditions: finitely many.
 R4.3 [modular] THE PRODUCT PAIRS FORM A FINITE SET: the pair system (Gr(2,5) x Gr(2,5): e_3|W_a = e_3|W_b = 0, B(W_a, W_b) = 0; 12 equations
   in 12 unknowns; 3 S5 x Z2 orbit charts 01_01, 01_02, 01_23) has a 0-dimensional Groebner basis in chart 01_01 (1109 elements, 864 standard
   monomials = number of solutions with multiplicity) at p = 2147483629 (ncol/gb/pairs/, gbdim.py, gbcount.py).  So product-type column-centred
   3x5 level 4-spaces are RIGID (finitely many), the 30 same-node ones (e = 3) and the general-line ones (LM: e = 4) among them.
 R4.3' All three orbit charts of the pair system are 0-dimensional at p = 2147483629: degrees (with multiplicity) 864 (01_01), 828 (01_02),
   792 (01_23).  By upper semicontinuity of fibre dimension (projective scheme over Z), the char-0 set of product pairs is finite too.
 R4.4 NUMERICAL ENUMERATION in chart (01,01) (ncol/pairs_num.py, Newton from random starts, then pairs_classify.py): 155 distinct pairs in 200
   starts: 141 pairs of GENERAL lines (no node), all with defect e = 4, W_a != W_b; 14 near-duplicates of the 12 same-node pairs W (+) W in this
   chart (non-reduced points, Newton converges slowly), all with e = 3 and defect = e_k^perp cap V5 (a neutral column at the node k).
   [larger runs pairs_num2/3 in progress]
   EMPIRICAL CLASSIFICATION: a product-type column-centred 3x5 level 4-space has e = 3 iff it is a same-node pair W (+) W, W = span(e_k, chi_sigma),
   and then its defect space is e_k^perp cap V5; otherwise e = 4.  (Exact test of "e <= 3 => same node" running: E = 3 orbit charts,
   ncol/gb/prod/prodgen3.py, reps_e3.txt.)
 R4.5 WHY THIS MATTERS FOR (7,3) [rigorous reduction, conditional on (PROD) IN CHARACTERISTIC 0 and R4.4's exact version; CAVEAT (verify2 R18):
   a unit PROD-NCOL at P1 does not give (PROD) in char 0, so this route needs a different argument for non-product spaces with e = 3]: if a (7,3) space contains a 4-dim
   column-centred zero-row subspace K (e.g. ker c with a vanishing row), then C(K) lies in the 3-dim C, so K is a same-node product with
   C(K) = e_k^perp cap V5 = C: column k is NEUTRAL and C2 excludes the space.  This would subsume R2.4 (A), (B) without CC3 and would apply to
   every row i with row i == 0 on ker c.
 R4.6 A COLUMN-CENTRED ROUTE FOR (7,3) [rigorous reduction]: let L' be a (7,3) space (under (DI_5;3)) and K := ker c.
   - rank c = 3, dim K = 4, e(K) = 3: C(K) = C, so a neutral column of K is a neutral column of L', and C2 excludes L'.  Hence
       (CCN) "every column-centred 4x5 level space of dimension 4 with defect 3 has a neutral column"
     kills this sub-case.  [numerical] rows' two column-centred (4,3) spaces cc_d4_s16, cc_d4_s38 both have w ~ 1 - 5 e_n (neutral columns 3 and
     0; s16 is LM-limited, the srow_chk tolerance missed it); a larger census is running (rows/cc_search.py from ncol/).
   - rank c = 3, e(K) in {1, 2}, and rank c <= 2 (dim K >= 5, e(K) <= 3): separate (column-centred (4,1)/(4,2) and (5,<=3) spaces).
   Note: (ZR) "column-centred (4,<=3) spaces have a zero row" is FALSE (s16, s38: all row projections have rank 3), so R4.5 alone does not suffice.
 R4.7 TOWARDS R3.2 (split isotropic (5,1), one zero) [rigorous reduction + exact check]: in the shape L' = K'' (+) C e_i m^T (+) C Y_0, every
   element of ker c = K'' (+) C Y_0 has row i in C e_n, and its other three rows have column sums in C e_n; since column n is neutral, C_n == 24
   means: the 3x4 matrices (rows != i, columns != n) of ker c form a COLUMN-CENTRED 3x4 LEVEL space P^(n), of dimension 4 - x_n(ker c).
   Column-centred 3x4 level spaces in isotropic coordinates (a, beta) in C^4 x C^4: P_2 = 3(sum a beta - AB), P_3 = 6(e_3(a) + e_3(beta)).
   [exact] Product-type ones (W_a (+) W_b) do not exist in dimension 4: the lines on the Cayley cubic {e_3 = 0} in P^3 are the 6 coordinate
   lines and the 3 pairing lines, and none of the 81 ordered pairs is B-orthogonal.  The full dim-4 test (Gr(4,8), 6 S4 x Z2 orbit charts,
   ncol/gb/cc34/) is running; if it is empty, x_n(ker c) >= 1 in R3.2 (a single-column element in the neutral column inside ker c).
 R4.8 [numerical] Enumeration of product pairs in chart (01,01) (runs of 200 + 3000 + 3000 Newton starts): 745 distinct pairs of general lines
   (no node), ALL with defect e = 4 (smallest 4th/1st singular-value ratio 3e-5); the 12 same-node pairs of this chart (non-reduced points of
   the 0-dim scheme; Newton returns many inaccurate copies) all with e = 3 and neutral column at the node.  Degree count: 864 = (general) +
   (multiplicities of the 12 same-node points), so at least ~10 general pairs are still unfound; consistent with PT2 (no e <= 2).
 R4.9 THEOREM CC34 [modular, projective -> char 0 by RED-p; ncol/gb/cc34/cc34gen.py]: THERE IS NO COLUMN-CENTRED 3x4 LEVEL SPACE OF
   DIMENSION 4.  Gr(4,8) Pluecker charts, 6 orbits under S4 x Z2 (system S4 x Z2-invariant), equations P_2 == 0, P_3 == 0 in isotropic
   coordinates; UNIT in 6/6 charts at p = 2147483629, 2147483497, 2147483077 (instant).  Calibration: the same generator at D = 3 vanishes
   identically (16/16 equations) at the explicit column-centred 3x4 level 3-space span((e_0,0), (e_1,0), (0, e_2 - e_3)) in chart 016.
   CONSEQUENCE for R3.2 [rigorous given CC34]: dim P^(n) <= 3, so ker c contains an element supported on the neutral column n: a single-column
   element y' e_n^T of L' (column-centred, sum y' = 0).  Either it has y'_i != 0 (then Y_0 may be taken to be y' e_n^T, y'_i = -1:
   L' = K'' (+) C e_i m^T (+) C y' e_n^T), or it lies in K''.
 R4.10 (CCN) census [numerical]: rows' cc_search.py (column-centred 4x5 level, dim 4) from ncol/ccn: 2 new hits (s111, s116, 300 starts
   box cut early), both e = 3 with w ~ 1 - 5 e_1 (column 1 neutral, max|C_1| = 0).  Together with rows' s16, s38: 4/4 column-centred (4,3)
   spaces have a neutral column.  (CCN) would close the sub-case rank c = 3, e(ker c) = 3 of (7,3) (R4.6).
 R4.11 (PROD), chart 0123 with isotropy ELIMINATED [exact reformulation; ncol/gb/prod0123/gen0123.py]: S = {(F t, G t)}, F = [I; f^T],
   (I - J) G = [K - f h^T; h^T], K skew -- a bijective polynomial reparametrisation of (Pluecker chart 0123) cap (isotropy locus), verified
   symbolically (F^T (I-J) G = K).  14 unknowns, 20 equations of degree <= 6 (instead of 24 unknowns, 30 equations).  msolve running.
 R4.11' chart 0123 reformulated: msolve still segfaults at the 2 GB cap (59 s).  (PROD) stays with the big-slot job.
 R4.12 A TEMPTING SHORTCUT, AND WHY IT FAILS [rigorous + numerical].  Since rank c <= e, every (d,e) space with d >= e + 4 has dim ker c >= 4,
   and a 4-dim subspace K4 of ker c is a COLUMN-CENTRED 4x5 level space with C(K4) inside C(L').  So
       (CC45) "every column-centred 4x5 level space of dim 4 has defect >= 3"  would exclude (5,1) and (6,2) outright, and
       (CC45) + (CCN) would exclude (7,3)   [e(K4) = 3 forces C(K4) = C, and a neutral column of K4 is one of L'].
   (CC45) is FALSE [numerical, polished]: rows' cc_d4_s52 polished with the defect constrained to a plane (ncol/ccpolish.py) gives a
   column-centred level 4-space with defect singular values 42, 31, 6e-11, ... (e = 2, level 4e-11; ncol/ccn/cc_d4_s52_pol_e2.npy); it has
   neutral column 0 and single-column elements x = (2,1,0,0,0).  So the 4-row analogue of CC3-e2 fails.  What survives: (CCN) for e = 3 (4/4
   examples) closes the (7,3) sub-case "rank c = 3, e(ker c) = 3"; the sub-cases e(ker c) <= 2 and rank c <= 2 remain.
   [Contrast: for 3 rows, products force e >= 3 (PT2); the 4-row column-centred spaces are richer.]
 R4.13 The exact version of R4.4 ("product with e <= 3 => same-node pair") via the E = 3 product system (ncol/gb/prod/prodgen3.py, 7 orbit
   charts) segfaults at 2 GB (chart 01_01_0, 220 s); stopped.  It stays numerical (R4.8: 745/745 general pairs have e = 4).
STATUS 01:59: round 4 closing; report next.
STATUS 02:00: ROUND 5 started (targets: exact 'e<=3 => same node' on the 0-dim pair scheme; (CCN); R3.2 shape; (SR3), R2.11).

# ROUND 5 (start ~02:07 UTC). Targets: (1) exact "e <= 3 => same node" over the 0-dim pair scheme (multiplicities!); (2) (CCN) via isotropic
#  coordinates for V4; (3) R3.2 shape with CC34's single-column element, two-zero case; (4) (SR3), R2.11.

## Section R5 (round 5)
 R5.1 R3.2 SHAPE, MORE STRUCTURE [rigorous]: in the split isotropic one-zero (5,1) shape, alpha == 0 on all of L' (alpha = zeta kappa on H with
   zeta = 0, and alpha = 0 on ker c), so c^(i)(Y) = delta(Y) e_n for EVERY Y: the three rows != i of every element have zero column sums off
   column n.  Hence Q := L' minus column n (level, n neutral) splits as Q = P (+) C e_i m'^T, where m' = m without entry n (zero-free, sum 0,
   isotropic: e_1(m') = e_2(m') = 0) and P = Q cap {row i = 0} is a column-centred 3x4 level space (rows != i).  CC34: dim P <= 3, so
   x_n(L') = 4 - dim P >= 1.  Level of Q in kappa gives m'.R'(p) = 0 for p in P, R'(p)_k = perm_3((J+p) minus column k): the 3x4 column-deletion
   defect vectors of P are orthogonal to m'.  Remaining: a 4x4 problem in (P, X_n, the twist), dim P in {1,2,3}.
 R5.2 PLAN FOR "e <= 3 => same node" (exact): RED-p alone does not settle a statement of the form "every point of Z is in SN" (a char-0 point
   outside SN could reduce onto an SN point), unless char-0 local lengths at SN are known.  Clean route: char-0 RATIONAL PARAMETRISATION of the
   0-dimensional pair scheme in each of the 3 orbit charts (msolve -P 1 over Q), then for the generic factor test a random 4x4 combination
   determinant of the 12 defect generators modulo the eliminating polynomial (non-vanishing mod p of gcd-type certificates implies non-vanishing
   over Q).  Note: chart (01,23) contains NO same-node pair (span(e_k, chi_sigma) never has both (0,1)- and (2,3)-minors nonzero), so there the
   claim is "e = 4 at every point".  Running: msolve -P 1 for chart 01_23 over Q and mod P1.
 R5.3 WITT COORDINATES FOR COLUMN-CENTRED 4x5 MATRICES (towards (CCN)) [identities, checked numerically to 1e-15]: with chi_k(i) = i^{k i}
   (i = 0..3), nu_1 = chi_1/2, nu_2 = chi_3/2, nu_0 = chi_2/2 (nu_1.nu_2 = 1, nu_0.nu_0 = 1, other products 0), write the columns of a column-
   centred 4x5 matrix as y_j = a_j nu_1 + b_j nu_2 + c_j nu_0, (a, b, c) in (C^5)^3.  Then
        P_2 = sum a_j b_j - A B + (sum c_j^2 - C^2)/2,       P_3 = sum_j c_j (e_2(a^(j)) + e_2(b^(j)))
   (the cubic form sum_i x_i^3 on V4 is (3/2) c (a^2 + b^2) by character orthogonality).  In particular P_3 == 0 on {c = 0}.  All column-centred
   level 4-spaces found (7) carry a single-column element exactly in their neutral column (s111 x_1 = 1, s116 x_1 = 2, s16 x_3 = 1, s38 x_0 = 1,
   s52 x_0 = 2, x_1 = 1).  Not pursued further this round.
 R5.4 LOCAL MULTIPLICITY OF THE SAME-NODE POINTS [exact over Q(i) and mod p, Singular local ordering ds; ncol/gb/pairs/loc/]: at the same-node
   point W_a = W_b = span(e_0, (0,1,i,-1,-i)) (chart 01_01) the pair scheme Y has local length 6 in characteristic 0 (over Q(i)) AND at
   p = 2147483629.  All 30 same-node points form one S5 x Z2-orbit, so all have length 6.  Degree bookkeeping: chart 01_01 contains 12
   same-node points (864 = 792 + 12*6), chart 01_02 contains 6 (828 = 792 + 6*6), chart 01_23 none (792): every orbit chart carries 792
   general points with multiplicity.
   LENGTH ARGUMENT [rigorous]: Y is projective over Z_(p) with 0-dimensional special fibre, hence finite; a characteristic-0 point P != s of Y
   specialising to the reduction of a same-node point s would force length_p >= length_0(s) + 1 = 7 at that point, but it is 6.  So if, MOD p,
   every F_p-bar point of Y with defect <= 3 is a same-node point, the same holds in characteristic 0.  (The mod-p statement may use
   saturation/Rabinowitsch, being a char-p statement.)  Running: pair system + random 4x4 combination determinant (+ Rabinowitsch excluding the
   same-node points) in the 3 orbit charts.
STATUS 02:13: verify2 R18 rigour flag addressed: R3.9 / F5 / R3.4 / R3.6 / R4.5 / G3 / handover reworded to go through CC3-e2 (closed system) instead of (PROD).
 R5.5 R3.2 SHAPE, CASE dim P = 1 IS IMPOSSIBLE [rigorous + exact check].  dim P = 1 gives x_n = 3, X_n = 1^perp (full free column), so as in
   configuration (a): M(q) = 24*1 on Q, rho(q) = 0, L' = (Q|0) + (0|1^perp) untwisted, and C(L') contains every row of every q.  With C(L') = C m
   all rows are multiples of m': Q = {alpha (x) m'}, alpha in span(e_i, a_0) (a_0 in C^3 on the rows != i, sum a_0 = 0).  Row deletions level:
   e_3(alpha') e_3(m') = 0 for every 3-row deletion alpha'.  If e_3(m') != 0: deleting row i gives a zero entry of a_0, so a_0 ~ (u,-u,0); deleting
   another row gives kappa s^2 (product of two entries of a_0) == 0, forcing u = 0.  If e_3(m') = 0: m' is an ordering of (1,i,-1,-i), level of Q
   forces e_4(alpha) = kappa s^3 prod(a_0) == 0, so again a_0 ~ (u,-u,0); this single configuration (up to symmetry) has defect dimension >= 3
   (exact rank 3 over Q(i) at 6 rational points), not 1.  Contradiction.  Left: dim P in {2, 3}.
 R5.6 EXACT ROUTE TO "e <= 3 => same node" (mod-p part) [in progress]: for a random 4x4 combination M of the 12 defect generators, points of the
   pair scheme with rank M <= 3 (which contains all points with e <= 3) are cut out by J_k := I + {M h = 0} with h in chart h_k = 1
   (ncol/gb/pairs/kergen.py; 15 unknowns, 16 equations).  At a same-node point the kernel vector is h = e_node (in V5 coordinates), so node-0
   points lie only in chart h_0, node-1 points only in chart h_1.  Local multiplicities of J_k at the same-node points [Singular ds, mod p,
   ncol/gb/pairs/locJ/]: 2 at each of the 12 points of chart 01_01 and the 6 points of chart 01_02.  So "the only points with rank M <= 3 are
   the same-node points" (mod p) <=> deg J_0 = deg J_1 = 12 and J_2, J_3 UNIT in chart 01_01; deg J_0 = 12 and J_1..J_3 UNIT in chart 01_02;
   all four UNIT in chart 01_23.  msolve runs in progress.
 R5.7 THE ARGUMENT (to be completed by the J_k verdicts): (a) [mod p, char-p statement] if deg J_k equals the sum of the local multiplicities of
   J_k at the same-node points of the chart (all = 2) for every orbit chart and h-chart, then every F_p-bar point of the pair scheme Y_p with
   rank M <= 3 -- in particular with defect <= 3 -- is a same-node point; (b) [exact, R5.4] the local length of Y at a same-node point is 6 in
   characteristic 0 and at p; (c) [rigorous] Y is finite over Z_(p), so a characteristic-0 product pair with e <= 3 that is not same-node would
   specialise to a point of Y_p with e <= 3, i.e. to a same-node point s-bar, and the length of Y_p at s-bar would be >= 6 + 1.  Hence:
   THEOREM (pending (a)): a product-type column-centred 3x5 level 4-space has defect <= 3 iff it is a same-node pair W (+) W,
   W = span(e_k, chi_sigma), and then its defect space is e_k^perp cap V5 (column k neutral).
 R5.8 The kernel-vector systems J_k segfault at 2 GB (chart 01_23 h0, 322 s); replaced by a QUOTIENT-ALGEBRA test at p = 65521 (p = 1 mod 4):
   msolve's reduced grevlex GB of the pair ideal is loaded into Singular as a standard basis (attrib isSB; VDIM 864 / 828 reproduced, same
   degrees as at P1), the 16 entries of a random combination M (seed 7) are reduced modulo it, det(M) is computed by Laplace expansion along
   2x2 minors with reduction at every step (procedure checked against Singular's det), and vdim(std(G + det)) is the length of the
   locus {rank M <= 3} in the chart (ncol/gb/pairs/mkq.py).  Local data at p = 65521 (ncol/gb/pairs/mkloc3.py, loc3.log): at all 18 same-node
   points of charts 01_01 / 01_02 the pair scheme has local length 6 (as in char 0 and at P1) and Y + det has local length 2.  So the target
   values are vdim = 24 (chart 01_01), 12 (01_02), 0 (01_23).
STATUS 02:36: target 1 mod-p part switched to quotient-algebra det test at p=65521 (pair degrees 864/828/792 reproduced; local lengths Y=6, Y+det=2 at all 18 same-node pts); multiplication-matrix export running for chart 01_01
 R5.9 CHART 01_02 VERDICT [mod p = 65521, exact Groebner/standard-basis computation]: vdim(std(G + det M)) = 12 = 6 same-node points x local length 2 (sing/q_01_02.out).
 R5.10 R3.2 SHAPE, dim P = 3: the P-INTERNAL conditions do not suffice [exact by hand + numerical check ncol/r32/pint.py].  In isotropic
   coordinates (columns y_j = a_j nu_1 + beta_j nu_2 of the 3 rows != i) the conditions on P alone are P_2 = P_3 == 0 (3x4 level: sum_k R'_k
   == 24) and m'.R'_2 == m'.R'_3 == 0 (R'_2,k = 3(sum_{j!=k} a_j beta_j - A^(k) B^(k)), R'_3,k = 6(prod_{j!=k} a_j + prod_{j!=k} beta_j)).  The
   CC34 calibration space P = span((e_0,0), (e_1,0), (0, e_2 - e_3)) satisfies all four for m' = (x, y, 1, 1), x, y = -1 +- i sqrt 2 (zero-free,
   e_1 = e_2 = 0): R'_3 == 0 and m'.R'_2 = 3A beta.m' = 3A c (m'_2 - m'_3) = 0 (numerically 1e-13 over 20 random points).  So excluding
   dim P = 3 must use column n (X_n, the twist phi: P (+) C -> V4/X_n, the neutral-column identity R_n == 0 and m_l R_k = m_k R_l for k, l != n).
   Concrete system for next round: L' = {(p + kappa e_i m'^T | phi(p, kappa) + x) : p in P, x in X_n}, dim X_n = 4 - dim P, unknowns
   P in Gr(dim P, 8) (orbit charts under S4 x Z2), m' on x^4 + s x + t (one projective parameter), X_n in Gr(4 - dim P, V4), phi.
 R5.11 CHART 01_23 VERDICT [mod p = 65521, exact]: vdim(std(G + det M)) = 0 (sing/q_01_23.out): det M is a unit, no point of the chart has rank M <= 3.
STATUS 02:48: det-test verdicts at p=65521: chart 01_02 = 12 (target 12), chart 01_23 = 0 (target 0); chart 01_01 running by two methods (std and multiplication matrices), target 24
STATUS 02:51: round-5 RESULT block written. Chart 01_01 det count still running: sing/q_01_01.out (std) and mm/c0101 (export, then lenmm.py mm/c0101 65521); target 24

## Round 6 (ncol; start 02:53 UTC)
STATUS 02:56: round 6 started; chart 01_01 det count still running (std: sing/q_01_01.out; mm export var 9/12); writing the R3.2 closure system
 R5.12 CHART 01_01 VERDICT and THEOREM SN [mod p = 65521 exact + R5.4 lift => char 0]: length(Y_p + det M) in chart 01_01 = 24 = 12 x 2
   by BOTH methods: Singular vdim(std(G + det M)) = 24 (sing/q_01_01.out) and the multiplication-matrix method lenmm.py on mm/c0101
   (n = 864, rank(mult by det) = 840, the commutativity checks [M_a, M_b] = 0 and [M_v, mult-by-det] = 0 passed): LENGTH 24.
   Together with R5.9 (01_02: 12) and R5.11 (01_23: 0): every F_p-bar point of Y_p with rank M <= 3 is a same-node point.
   THEOREM SN [proved, char 0]: a product-type column-centred 3x5 level 4-space has defect <= 3 iff it is a same-node pair W (+) W,
   W = span(e_k, chi_sigma); its defect space is then e_k^perp cap V5 (column k neutral).
   Clarifications to R5.4 requested by verify2 (audit: lift VALID, no flatness needed):
   (1) work over the COMPLETION Z_p (p = 65521 = 1 mod 4, so i in Z_p and Q(i) embeds in Q_p): the finite Z_p-algebra B of Y_{Z_p} splits
       as the product of its local factors B_y over the closed points y of Y_p; dim_{Q_p} B_y (x) Q_p <= dim_{F_p} B_y (x) F_p = length_p(y) for a
       finite Z_p-module.  The same-node point s is a Z_p-point reducing to s-bar, contributing length_0(s) = 6 to B_{s-bar} (x) Q_p (local
       length is invariant under the field extension Q(i) -> Q_p); any further char-0 point specialising to s-bar would add >= 1.
   (2) the 30 same-node points (coordinates in {0, +-1, +-i}) reduce to 30 DISTINCT points mod 65521 (i = 41224 != -i, 1, -1, 0); in the
       charts, the 12 points of 01_01 and 6 of 01_02 are pairwise distinct (loc3 uses distinct coordinate vectors), so s is the only same-node
       point specialising to s-bar.
   mm cross-check status: chart 01_01 DONE (above).  The earlier mm_01_02 "halt 1" was NOT a crash: I killed that export at 02:41 to free a
   core for the 01_23 std run (2-core cap); c0102.mm was therefore incomplete and lenmm stopped at its commutativity assertion, as designed.
   Re-running 01_02 (and then 01_23) with a faster export (link kept open).
STATUS 02:57: THEOREM SN PROVED: chart 01_01 = 24 by std AND by multiplication matrices; mm cross-checks for 01_02/01_23 re-running; R3.2 closure generator written
 R6.1 R3.2 CLOSURE SYSTEM (one projective system for ALL dim P, round-6 target 2) [setup, rigorous]: by R5.1 (alpha == 0) every Y in L'
   has row 0 = (kappa m', -delta) and L' = C e_0 m'^T (+) L'', L'' := ker c in Gr(4, U), U = (V3)^4 (+) V4 (11-dim; rows 1..3 column-centred
   on columns 0..3, column 4 in V4).  By CC34 (R4.9) L'' contains a single-column element (0|y'), y' in V4 (x_n >= 1 <=> dim P <= 3), so
   (y', L'') lies on the closed incidence variety {(0|y') in L''} subset P(V4) x Gr(4, U) -- a Gr(3, U/Cy')-bundle over P(V4), projective --
   times the conic {sum m' = sum m'^2 = 0} in P^3.  This single projective system covers dim P = 1, 2, 3 at once (no twist/stratum charts).
   Charts: y' = f_1 + y_2 f_2 + y_3 f_3 (f_r = e_r - e_0; S3 on rows 1..3 moves any y' there), L'' = C(0|y') (+) span(v_1, v_2, v_3) with v_s in
   (a_0..a_3, b_0..b_3, w_2, w_3) = (V3)^4 (+) span(f_2, f_3) (isotropic coordinates nu_1 = (1,w,w^2), nu_2 = (1,w^2,w) on rows 1..3),
   Pluecker chart S of Gr(3,10) up to S4 (columns 0..3, acting on m' too) x Z2 (rows 2<->3: a<->b, w_2<->w_3, y_2<->y_3): 8 orbits
   (012, 014, 016, 018, 019, 048, 058, 089; ncol/r32/orbits.py, reps3.txt); m' in all 4 charts M_J = 1.  Equations: coefficients in
   (u_0, u_s, kappa) of R_4(Y) and M_l R_k(Y) - M_k R_l(Y) (k < l <= 3), Y = u_0 (0|y') + sum u_s v_s + kappa e_0 m'^T,
   R_k(Y) = perm_4((J+Y) minus column k) - 24, plus sum M = 0, sum M^2 = 0.  26 unknowns, 472-514 equations, p = 65521 (= 1 mod 12, so w, i in F_p).
   Generator ncol/r32/r32gen.py (Singular builds the equations, writes msolve input).
   CALIBRATION: (a) point check: the R_4-only subsystem vanishes (34/34) at the CC34 calibration space with m' = (-1 +- i sqrt 2, 1, 1)
   and fails for m'_2 != m'_3 or a perturbed basis (negative controls; ncol/r32/evalpt.py); the full system fails there (88/510), as it must
   (zero twist).  (b) the same generator with only 2 (or 1) v's -- a 4-dim (resp. 3-dim) L' of the same shape -- is NONUNIT (calv.log:
   c01_J0 37, c01_J3 71, c04_J0 47, c04_J3 51, c08_J0 88 ...), so the cross conditions do not make the system inconsistent by construction.
   First full chart (016, J = 2): UNIT in 6.4 s.  All 32 running (full.log).
STATUS 03:05: R3.2 closure system (one-zero): 12/32 orbit charts UNIT so far, calibration NONUNIT 8/8; two-zero generator (Gr(4,13), 82 orbit charts) built, queued behind the 01_02 mm cross-check
 R6.2 mm CROSS-CHECK chart 01_02 [modular, exact]: export completed (link kept open), lenmm.py mm/c0102: n = 828, rank(mult by det) = 816, LENGTH 12 (commutativity asserts passed) = the std/vdim verdict of R5.9.  Charts 01_01 and 01_02 are now genuinely cross-checked; 01_23 export queued after the one-zero runs.
STATUS 03:12: one-zero R3.2 closure 27/32 UNIT (0 non-unit); 01_02 mm cross-check = 12; two-zero (82 charts) and Gr(4,11) variant (52) queued, serialized
 R6.3 ONE-ZERO R3.2 CLOSURE: UNIT 32/32 [modular at p = 65521, projective closure, all charts up to symmetry -> char 0 by RED-p]
   (ncol/r32/full.log: 8 orbit charts x 4 m'-charts, 0.4 - 83 s each).  With calibration R6.1 (point check + NONUNIT 8/8 for 2-dim / 1-dim spans).
   THEOREM R32 [char 0, given R5.1 (rigorous) and CC34 (R4.9, char 0)]: there is NO split isotropic (5,1) space with exactly one zero
   (the R3.2 shape is impossible for every dim P).  In fact more: no 5-dim L' = C e_0 m'^T (+) L'' with L'' a 4-dim subspace of
   (V3)^4 (+) V4 containing a single-column element, level with defect inside C (m', 0), exists for ANY m' on the isotropic conic
   (including m' with a zero, i.e. the alpha == 0 part of the two-zero case).  The CC34-free cross-check (L'' in Gr(4,11), 52 systems) is queued.
STATUS 03:16: one-zero R3.2 closure UNIT 32/32 (THEOREM R32); two-zero Gr(4,13): 28 UNIT, 3 segfaults at 2 GB (charts with both delta, delta' pivots) -> will refine those by the UNIT neighbour charts (p_T = 0, closed)
 R6.4 TWO-ZERO SPLIT ISOTROPIC (5,1) [setup rigorous; computation in progress]: isotropic m with |supp m| = 3 is, up to S5 and scaling,
   m = (1, w, w^2, 0, 0) (m_0^2 + m_0 m_1 + m_1^2 = 0; the other root is the column swap (1 2)).  Row 0 carries C m.  c(Y) in C m always
   (R^(1)(Y) = 6(s 1 - c(Y)) in C m forces s = 0), so L' = C e_0 m^T (+) ker c.  (F1): c^(0)(Y) in Gamma(C m) = span(1, e_3, e_4), so on
   ker c row 0 = -(alpha 1 + delta e_3 + delta' e_4) -- alpha is NOT forced to vanish here (the R3.2 argument needs a single zero), only
   alpha in span(delta, delta') on ker c (a zero row of J + Y would kill all deletion permanents).  System: L'' = ker c in Gr(4, U2), U2 the
   13-dim space with coordinates (alpha, delta, delta', a_0..a_4, b_0..b_4) (rows 1..3 of column j = -y0_j/3 (1,1,1) + a_j nu_1 + b_j nu_2);
   equations: coefficients of R_3, R_4 and m_l R_k - m_k R_l (k < l <= 2) in (u_1..u_4, kappa); 36 unknowns, ~460 equations.  Symmetry:
   rows 2<->3, columns 3<->4, cyclic columns (0 1 2) (m -> w^2 m): 82 orbit charts (ncol/r32/orbz.py, repsz.txt).  Generator r32z.py.
   Calibration: 3-dim L'' (zcal): z_1_3_8 NONUNIT(36) (4 others UNIT); more (1- and 2-dim, alpha/delta pivots) in zcal2.
   Charts with BOTH delta and delta' as pivots segfault at 2 GB (z_1_2_3_4, _6, _11 ...).  Remedy (closed, RED-p-valid): on a failed chart S
   add p_T = 0 for every chart T whose orbit is verified UNIT (single exchanges give g_{s,c} = 0, double exchanges 2x2 minors): a mod-p
   solution in chart S with p_T != 0 would lie in the empty chart T.  ncol/r32/refine.py, do_refine.sh.
STATUS 03:19: two-zero: all 27 alpha-pivot charts UNIT, 2 of 8 delta-delta' and 0 of 22 one-delta charts done (2 GB segfaults) -> staged refinement chain (neutral charts first, then one-delta, then delta-delta'); 01_23 mm export at var 6/12
STATUS 03:24: two-zero plain runs: all alpha charts UNIT; neutral charts mostly UNIT but 5 segfault; staged refinement next; numerical LM search for two-zero (5,1) spaces prepared (ncol/r32/num/lm2z.py) as a refutation probe
 R6.5 TWO-ZERO CASE: ALL 82 ORBIT CHARTS UNIT [modular at p = 65521, projective (Gr(4,13), m fixed over Z[w]), all 715 charts up to
   symmetry -> char 0 by RED-p].  Plain runs (zfull.log): 47 UNIT (all 27 alpha-pivot charts, 19 neutral, 1 delta-delta'), 12 segfaults at
   2 GB (the rest were set aside to be refined).  Staged refinement (R6.4; ncol/r32/stage.sh, refine.py), each stage using ONLY charts verified
   in earlier stages (no circularity): zrefN (6 neutral charts, +20-23 zeros, ~120 minors each): UNIT 6/6; zrefA (22 one-delta charts):
   UNIT 22/22; zrefB (7 delta-delta' charts, +20-22 zeros, ~190 minors): UNIT 7/7.  Soundness: a mod-p point in chart S with p_T != 0 for a
   chart T verified empty would be a point of chart T; by induction every verified chart (plain or refined) is completely empty, and
   Z is invariant under the symmetry group.  Calibration: same generator with 3-dim L'' (a 4-dim L', the extremal size) is NONUNIT in
   chart z_1_3_8 (36); more in zcal2.  The UNIT/NONUNIT boundary sits exactly at d = e + 3 = 4 -> 5, in both the one-zero and two-zero
   generators, as the defect inequality predicts.
   THEOREM Z2 [char 0, given (F1) and the setup of R6.4]: there is NO split isotropic (5,1) space with exactly two zeros.
   COROLLARY SPLIT-ISO [char 0]: with R2.14 (zero-free m, rigorous via CC3) and THEOREM R32 (one zero): NO (5,1) space has a row carrying an
   isotropic defect line (|supp m| = 5, 4, 3 are all the isotropic cases: |supp m| <= 2 forces m = 0).
STATUS 03:25: two-zero case 82/82 UNIT (47 plain + 35 refined) -> COROLLARY: no split isotropic (5,1) space; CC34-free Gr(4,11) cross-check and two-zero extra calibration next
 R6.6 mm CROSS-CHECK chart 01_23 [modular, exact]: lenmm.py mm/c0123: n = 792, rank(mult by det) = 792, LENGTH 0 = R5.11.  All three charts of THEOREM SN are now verified by two independent methods (std/vdim and multiplication matrices).
 R6.8 NEXT (plan for (SR3) / R2.11 with this round's machinery): both are (6,3)/(7,3) statements, too large for a raw Grassmannian.  The
   R2.11 structure (non-isotropic w, U_i = span(a, a o w) or a on a level set of w, rank c = 3, c^(i)(Y) = alpha 1 + gamma d_0,
   K' = ker c cap ker gamma a 3-dim zero-row column-centred space with defect <= 1) suggests a Grassmann-bundle chart system:
   (w, U_i) data x K' in Gr(3, (V3)^5) (CC3-type, 21 unknowns) x the gamma-direction and the 3-dim lift of C -- then staged refinement.
   The cleanest first step is probably to classify the 3-dim K' (zero-row column-centred 3x5 level spaces with defect line in C(L')), as
   PROD/E3P did for dimension 4.
STATUS 03:28: SN fully cross-checked (01_23 mm = 0); two-zero 82/82 UNIT; Singular independently confirms UNIT on z_0_1 and z_3_4_5_6 (c016_J2 running); CC34-free Gr(4,11) cross-check running (first 7 UNIT)
 R6.7 INDEPENDENT ENGINE CHECK [exact mod p, Singular std, ncol/r32/ms2sing.py, sx.log]: the msolve UNIT verdicts are reproduced by Singular
   on zcal2/z_0_1, zfull/z_3_4_5_6, zfull/z_6_7_11_12 (plain) and zrefB/z_1_2_3_4 (a REFINED delta-delta' chart): all UNIT (std = <1>).
   (The one-zero chart c016_J2 was stopped at 217 s / 0.8 GB to respect the one-big-job rule; not a disagreement.)
   CC34-free cross-check of THEOREM R32 (L'' in Gr(4,11), r32g411.py, 13 orbit reps x 4 m'-charts): the 24 charts without a column-4
   pivot are UNIT 24/24 (g411.log); the 28 with column-4 pivots segfault plain and are being closed by staged refinement (gz1, gz2, gz3).
STATUS 03:31: Gr(4,11) CC34-free check: 24/24 plain + 9/12 one-z refined UNIT so far; LM probe: dim-3 two-zero spaces found (residual 1e-26, calibration), dim-4 probe running
 R6.9 CC34-FREE CROSS-CHECK OF THEOREM R32: UNIT 52/52 [modular 65521, projective, RED-p -> char 0].  L'' in Gr(4,11) directly (no
   single-column element assumed; ncol/r32/r32g411.py; 13 orbit reps under S4 x S3 (orb411.py) x 4 m'-charts): 24 charts without a
   column-4 pivot UNIT plain (g411.log); the 28 with column-4 pivots closed by staged refinement (stage411.sh: an orbit rep counts as verified
   only when all four m'-charts are UNIT, since S4 acts on (chart, m'-chart) jointly): 1 z-pivot 12/12 (gz1), 2 z-pivots 12/12 (gz2),
   3 z-pivots 4/4 (gz3).  So THEOREM R32 no longer depends on CC34: it uses only R5.1 (alpha == 0, rigorous) and (F1).
STATUS 03:33: Gr(4,11) CC34-free check 52/52 UNIT -> THEOREM R32 independent of CC34; LM probe dim 3: 4/6 exact solutions (calibration), dim 4 running; writing the round report
 R6.10 [WITHDRAWN, under-sampled: see R8.4] NUMERICAL CORROBORATION OF THEOREM Z2 [numerical; ncol/r32/num/lm2z.py, Gram(L'') = I enforced]: with a 3-dim L'' (L' of dim 4, the
   extremal size) LM reaches exact solutions (residual 1e-26) in 4/6 starts -- calibration; with a 4-dim L'' (L' of dim 5) the residual
   stalls at >= 1.000 in 6/6 starts (min 1.0000000000000002) (exactly 1 = one Gram direction collapsing onto a 3-dim solution), as THEOREM Z2 predicts.
STATUS 03:35: round 6 closed: SN proved and fully cross-checked; no split isotropic (5,1) (one zero 32/32 + CC34-free 52/52, two zeros 82/82; Singular engine check; LM corroboration). Report sent.

## Round 7 (ncol; start 03:36 UTC)
STATUS 03:36: round 7 started; reading the (7,3) chain (R2.4, R2.8, R2.11, R2.15, R4.5, R4.6) to set up R2.11 / K' classification
STATUS 03:43: R2.11: sub-system K' (+) e_0 U_0 is numerically solvable (no contradiction there); K' census (3-dim column-centred, e <= 1) running on 2 cores: first hit is a product with a zero column, m = e_2 - e_4
 R7.1 THE (7,3) CHAIN AS ONE LIST (for verify2 / PROOF-MAP leaf 5), state at 03:45 UTC round 7.  Standing hypothesis (DI_5;3) (no (5,1),
   no (6,2)); L' a (7,3) space, C = C(L') = w^perp cap V5.
   [N] NEUTRAL COLUMN KILLS: if L' has a neutral column, contradiction (C2/N1.2, V-r14).  So every route below aims at a neutral column
       or at a forbidden subspace.
   [R1] Rows carrying C (u_i = 3): non-isotropic w impossible (C4, V-r14); isotropic w => ker c column-centred (4,1) with a zero row
        (R2.4 A) => impossible by CC3 (V-r16).
   [R2] u_i = 2, case (B) (dim(U_i + U_i o w) = 4): ker c column-centred (4,1) with zero row => CC3 (V-r15/16).
   [R3] u_i = 2, case (C) (dim(U_i + U_i o w) <= 3): R2.11.  [UPDATED round 8, R8.1/R8.2] given the K' classification (big slot
        NCOL-K3CLASS): every configuration whose zero-row part of ker c is 3-dim dies (THEOREM L6G + COROLLARY K'-KILL): all of sub-case
        dim = 3, and sub-case dim = 2 with rank c = 2 or rho = 1.  OPEN: sub-case dim = 2, rank c = 3, rho = 2 (dim K'' = 2), types a3, b22, b23
        (type a4 has a neutral column).
   [R4] isotropic w, u_i = 2, w in U_i: R2.15 => (CC3') "no column-centred 3x5 level 4-space with defect in a degenerate plane",
        implied by CC3-e2.  CC3-e2 [char 0] <= PROD-NCOL UNIT at P1 + PT2 (V-r18 RED-p on the closed {(S,G)} variety): BIG SLOT PENDING.
   [R5] all u_i <= 1: (SR3) "every (6,3) space has a single-row element" would force a row with u_i >= 2 on a generic hyperplane
        (R2.8, V-r15 as a reduction).  (SR3): OPEN (NUM 23/23).
   => ROUTE SR3:  no (7,3)  <=  (DI_5;3) + (SR3) + R2.11 + CC3-e2.   [R1, R2 done; R4 = CC3-e2 pending big slot; R3, R5 open]
   Alternative routes for the open pieces:
   [CC] rank c = 3, K := ker c column-centred 4x5 of dim 4 (R4.6): e(K) = 3 => C(K) = C, so (CCN) "column-centred (4,3) spaces have a
        neutral column" gives [N].  e(K) in {1, 2}: column-centred (4,1) -- excluded? (4,1) column-centred is NOT excluded by CC3 unless it
        has a zero row; column-centred (4,2) EXIST (R4.12).  rank c <= 2: dim K >= 5, column-centred (5, <= 3).  OPEN.
   [ZR] if ker c (or any 4-dim subspace) is column-centred WITH A ZERO ROW: it is a column-centred 3x5 level 4-space K with C(K) in C;
        CC3-e2 => e(K) = 3 = dim C, C(K) = C; if K is a PRODUCT, THEOREM SN (R5.12, proved) => same-node, C(K) = e_k^perp cap V5 => column k
        neutral => [N].  Non-product K with e = 3: (PROD) is OPEN in char 0 (PROD-NCOL decides it only at P1, V-r18).
   [NCOL] (N_3+) directly: OPEN (NUM 120/120; X2 test 0/461).
   Proven inputs used: C2, C4, R2.1-R2.4, R2.8, CC3, THEOREM SN, PT2, E3P, CC34 (only for R3.2, now not needed), R32/Z2 (these are (5,1)
   statements = (DI_5;2) pieces, feeding the standing hypothesis via Branch 1.1).
STATUS 03:49: K' (3-dim zero-row column-centred, e <= 1): census hits are ISOLATED reduced points (Jacobian full rank) of one exact type K' = (C(e_p-e_q), 0) (+) (0, span(e_s1, e_s2)) [+ mirror], m = e_p - e_q; exact classification by 0-dim scheme + length argument in progress (charts 015/017/012 x 5 m-charts)
 R7.2 K' CENSUS (3-dim zero-row column-centred 3x5 level spaces with defect <= 1) [numerical, 6 hits (seeds 7, 18, 20, 404, 405, 418; round 8: +4 more (1001, 1003-1005), all the same type, 10/10);
   ncol/r7/k3/, k3an.py, k3exact.py; exact rigour statements below].  e = 1 exactly in every case [rigorous: e = 0 is excluded by Lemma
   SL_3 (zero-row form, V/Lean: zero-row strongly level => dim <= 2)].  ALL hits are of ONE type, up to S5 x Z2:
        K'(p,q; s1,s2) = (C(e_p - e_q), 0) (+) (0, span(e_s1, e_s2))   (isotropic coordinates (a, b); or its a <-> b mirror),
   {p, q, s1, s2, z} = {0..4}: column z is ZERO on K', defect line m = e_p - e_q, single-column elements in columns s1, s2.  In matrix
   form (rows 1..3): K' = span(nu_1 (e_p - e_q)^T, nu_2 e_s1^T, nu_2 e_s2^T): three RANK-ONE matrices.  Exact check: these 60 points satisfy
   the exact chart systems (ncol/r7/k3known.py, all equations vanish) and are REDUCED there (Jacobian rank 24 = number of unknowns, mod
   65521); numerically each census point is isolated (Jacobian of the sampled residuals has full rank 24, smallest s.v. 7e-3 .. 3e-2).
   EXACT CLASSIFICATION (in progress): 0-dim scheme in Gr(3,10) x P(V5), 3 orbit charts (012, 015, 017) x 5 m-charts (k3gen.py); known
   points per chart: 017: 0,0,2,1,1 (J = 0..4), 015 and 012: none.  015_J0 UNIT (38.7 s); the other 015 and 012 charts segfault at 2 GB;
   017 running.  If 017 gives degrees 0,0,2,1,1, staged refinement ("all points known" charts as neighbours) + the SN length argument
   (known points reduced in char 0 and mod p) would give the classification in char 0.
 R7.3 LEMMA SC (single-column elements) [rigorous]: let L' be a 4x5 level space with defect space C and x e_s^T in L' (then sum x = 0).  For
   every Y in L' put y_l := x . Y_{:,l} (bilinear).  Then (a) sum_{l != s} y_l = 0 and (b) the vector (y_l)_{l != s} (0 in position s) lies in C.
   Proof: R(Y + r x e_s^T) = R(Y) + r v(Y), v_s = 0, v_k = sum_i x_i perm((J+Y) minus row i, columns k, s) (linearity in column s); every
   homogeneous part of v lies in C.  Degree 0: 6 sum x = 0.  Degree 1: v_k = 2 sum_i x_i (sum of Y over rows != i, columns not in {k,s})
   = -2(rho - y_k - y_s), rho = sum_l y_l; v in V5 forces rho = y_s, i.e. (a), and then v_k = 2 y_k (k != s), i.e. (b).  QED.
   For x = (0, nu_2) (rows 1..3 = nu_2, isotropic): y_l = 3 a_l(Y) (the nu_1-coordinate of column l on rows 1..3).
   CONSEQUENCE FOR R2.11 (conditional on the K' classification): K' contains nu_2 e_s1^T, nu_2 e_s2^T, so for every Y in L':
   a_s1(Y) = a_s2(Y), sum_{l != s1} a_l(Y) = 0, and (a_l(Y))_{l != s1} in C; with m = t = e_p - e_q in C cap U_0^perp.  These are linear
   conditions on the 7-dim L' (next round: plug into the R2.11 ansatz L' = K' (+) e_0 U_0 (+) C Y_gamma (+) C Z, which then has few unknowns).
 R7.4 R2.11 (sub-case dim(U_i + U_i o w) = 3) GIVEN THE K' CLASSIFICATION: NO SOLUTION [modular evidence at 65521, AFFINE chart system,
   conditional on R7.2; ncol/r7/r211gen.py, r211.log].  By S5 x Z2 take K' = span(n1 (e_1 - e_2)^T, n2 e_3^T, n2 e_4^T), t = e_1 - e_2.
   Then t in C cap U_0^perp forces U_0 = C cap t^perp EXACTLY (t.t = 2 != 0, dim C cap t^perp = 2), so C = U_0 (+) C t and U_0 is one
   point of Gr(2, {u in V5 : u_1 = u_2}) (3 charts).  L' = K' (+) e_0 U_0 (+) C Y_g (+) C Z with Y_g in ker c, c^(0)(Y_g) = al0 1 + d
   (d in V5, 5 charts), Z: c(Z) = t, gamma(Z) = 0 (normalised), both modulo K'.  21 unknowns.  Equations: coefficients of R(Y).1 and
   R(Y).w' (w' = generalised cross product of 1, t, u_1, u_2, checked orthogonal) in the 7 coefficients of Y.
   RESULT: full 7-dim system UNIT 15/15 (3 U_0-charts x 5 d-charts, instant; low-degree equations such as 4 alZ = 0, d_1 = d_2 appear).
   CALIBRATION: dropping Y_g and Z (L' = K' (+) e_0 U_0): ALL coefficients vanish identically (NEQ 0) -- the 5-dim part is automatically
   level with defect in C for every C containing t; dropping only Z (6-dim): NONUNIT 15/15 (13 GB elements) -- solutions exist; so the
   contradiction is produced exactly by the 7th dimension Z, as it must be for an "e + 4" statement.
   TO MAKE IT RIGOROUS (next round): (i) exact K' classification (R7.2; the plain charts segfault at 2 GB -- needs the pencil case split or
   the big slot); (ii) replace the affine normalisations of Y_g, Z by the projective formulation L'/(K' (+) e_0 U_0) in Gr(2, 10) inside
   {c(Y) in C, c^(0)(Y) in span(1, d)} (16 + 3 + 2 unknowns), all charts + staged refinement; (iii) the sub-case dim(U_i + U_i o w) = 2
   (U_i stable under o w: U_i spanned by vectors on level sets of w) is separate and not started.
STATUS 03:55: R2.11 dim-3 sub-case: conditional (K' classification) affine system UNIT 15/15 with calibration (6-dim version NONUNIT); exact K' classification blocked by 2 GB segfaults; writing round report
 R7.5 SHARPER FORM OF R7.4 [rigorous reduction + modular evidence]: in R2.11, Z' := Z - gamma(Z) Y_g has c(Z') = t and c^(0)(Z') in C1,
   so L' contains the 6-dim space L6 := K' (+) e_0 U_0 (+) C Z' on which c^(0) takes values in C1 (a "case (B)" (6, <= 3) space with
   rank c = 3, ker c = K').  The affine system for L6 alone (Y_g dropped, r211gen.py mode noY) is ALREADY UNIT (3/3 U_0-charts, instant),
   while K' (+) e_0 U_0 (+) C Y_g (mode noZ) is NONUNIT 15/15.  So, given the K' classification, R2.11 (dim-3 sub-case) reduces to:
     (L6) there is no 6-dim level space K' (+) e_0 U_0 (+) C Z with C(L6) inside C, c(Z) = t, c^(0)(Z) in C1, U_0 = C cap t^perp,
   a small statement (K' fixed, unknowns: U_0 (2), alpha_Z (1), Z mod K' (7)) whose projective version is the natural next exact target.
 R7.6 (L6) PROJECTIVE: UNIT 27/27 [modular at 65521, closed projective system over Z[w] (U_0 in Gr(2,3): 3 charts; Z in P(V_Z/K') = P^8:
   9 charts, including the closure lam = 0 where Z lies in ker c), RED-p -> char 0; ncol/r7/r211L6.py, l6.log].  Cross-check: the lam = 1
   chart reproduces the affine noY system of R7.5 equation for equation.  Calibration: K' (+) e_0 U_0 is level with defect in C for EVERY U_0
   (NEQ 0) and the same construction with c^(0)(Z) in span(1, d) (mode noZ) is NONUNIT 15/15, so the contradiction sits in Z.
   THEOREM R211-3 [char 0, CONDITIONAL on the K' classification R7.2; uses (F1), R2.3, CC3 (dim K' = 3), non-isotropic w (dim C cap U_0^perp
   = 1)]: case (C) of R2.4 with dim(U_i + U_i o w) = 3 is impossible.  Proof: R2.11 gives K' (3-dim, zero row, e(K') = 1, defect line
   t = C cap U_i^perp); the classification puts K' = K'(p,q;s1,s2) (or mirror) and t ~ e_p - e_q up to S5 x Z2; then U_i = C cap t^perp and
   L' contains L6 (R7.5), which (L6) excludes.
   OPEN to finish case (C): (i) the exact K' classification (0-dim scheme + SN-type length argument; plain charts segfault at 2 GB);
   (ii) the sub-case dim(U_i + U_i o w) = 2.
STATUS 03:58: (L6) projective 27/27 UNIT -> THEOREM R211-3 (conditional on the K' classification); RESULT block written; report next
 R7.7 (L6) ROBUSTNESS: UNIT 27/27 also at p = 2147483629 (ncol/r7/l6p2.log); Singular std reproduces UNIT on 3 charts at 65521
   (l6sx/).  Char-0 reducedness of the 60 known K' points: the K' chart systems have INTEGER coefficients (isotropic formulas) and the
   known points are RATIONAL ({0, +-1} coordinates); exact Jacobian rank over Q = 25 = number of unknowns (k3jac0.py, chart 017 J2), as mod p.
   So once the big-slot run NCOL-K3CLASS (QUEUE, spec ncol/r7/KBIG-SPEC.txt) shows chart degrees = known counts, the SN length argument
   gives the K' classification in char 0, and THEOREM R211-3 becomes unconditional.
STATUS 04:01: (L6) also UNIT 27/27 at p = 2147483629 + Singular check; K' char-0 reducedness exact; NCOL-K3CLASS queued; handover updated; reporting

## Round 8 (ncol; start 04:03 UTC)
STATUS 04:03: round 8 started; R2.11 dim-2 sub-case: plan = general-Z (L6'') system (c(Z) = lam t, c^(0)(Z) free), then rank c = 2 (Gr(2,12)) and dim K'' = 2
 R8.1 THEOREM L6G (general Z) [modular 65521 + exact char-0 lengths + SN length argument => char 0; ncol/r7/r211G.py, l6g.log, l6gjac0.py].
   Fix K' = span(n1 (e_1-e_2)^T, n2 e_3^T, n2 e_4^T) (zero column 0, t = e_1 - e_2).  Consider (U_0, Z) with U_0 = C cap t^perp in
   Gr(2, {u in V5 : u_1 = u_2}) (3 charts) and Z in P(V/K'), V = {Y : c(Y) in C t} with coordinates (lam, s_0..s_4, a, b): row 0 =
   lam t - s, rows 1..3 column l = (s_l/3) n0 + a_l n1 + b_l n2 (s = c^(0)(Z) ARBITRARY; 13 charts), such that L6 = K' (+) e_0 U_0 (+) C Z is
   level with defect inside C.  RESULT mod 65521: 34/39 charts UNIT; each of the other 5 has exactly ONE point, reduced (linear GB, vdim 1):
   lam = 0, a = b = 0, s = e_j and U_0 = {u in V5 : u_1 = u_2, u_j = 0}, for j in {0, 3, 4} = {zero column, s1, s2}: Z = x e_j^T,
   x = (-1, 1/3, 1/3, 1/3), a SINGLE-COLUMN element of ker c.  These 3 points are rational, satisfy the char-0 system and have char-0
   Jacobian rank 14 = number of unknowns (length 1).  The scheme is projective over Z_p[w] (p = 1 mod 3), with a finite special fibre;
   the length argument of R5.4/R5.12 then shows that in characteristic 0 these 3 points are the ONLY solutions.  In particular no solution
   has lam != 0.
   COROLLARY K'-KILL [char 0, given the K' type]: let L' be a (7,3) space (non-isotropic w) with u_0 = 2 and K' (classified type) inside
   ker c with zero row 0.  Then (R2.3) t perp U_0, so U_0 = C cap t^perp; every Y in ker c gives a solution with lam = 0, hence
   P(ker c / K') is contained in 3 points, so dim ker c <= 4 and rank c = 3, c(L') = C contains t; a Z in L' with c(Z) = t is a solution with
   lam != 0: contradiction.  No normalisation of c^(0)(Z) is needed, so this covers BOTH sub-cases of case (C) as soon as the zero-row part
   K'' of ker c has dimension 3 (and re-proves THEOREM R211-3 without Y_gamma).
   CASE (C) STATUS (given the K' classification): dim(U_i + U_i o w) = 3: done (K'' = K').  dim(U_i + U_i o w) = 2 (U_i stable under o w,
   D = U_i^perp 3-dim): K'' = ker c cap ker gamma_1 cap ker gamma_2 has dim = dim ker c - rho, rho = rank(gamma | ker c); CC3: dim K'' <= 3.
     dim ker c = 5 (rank c = 2): dim K'' = 3 -> K'-KILL (indeed rank c = 2 is impossible by the corollary).
     dim ker c = 4, rho = 1: dim K'' = 3 -> K'-KILL.
     dim ker c = 4, rho = 2: dim K'' = 2 -> OPEN (the last piece of case (C)).
STATUS 04:06: THEOREM L6G (general Z: only 3 single-column points, all lam = 0, char 0 by length argument) => case (C) reduced to dim(U+Uow) = 2, rank c = 3, rho = 2, dim K'' = 2 (given K' classification)
 R8.2 THE LAST PIECE OF CASE (C): dim(U_i + U_i o w) = 2, rank c = 3, rho = 2, dim K'' = 2 [rigorous reductions + numerical data].
   (a) U_i is stable under o w, so U_i = sum over level sets of w: up to S5, U_i = V_A (|A| = 3, type a3), U_i inside V_A with |A| = 4
       (type a4), U_i = V_ab (+) V_cd (type b22), or U_i = V_ab (+) C v, v in V_cde (type b23).
   (b) Type a4 is IMPOSSIBLE [rigorous]: w is constant on A (|A| = 4), so C = w^perp cap V5 = V_A and the fifth column is NEUTRAL (C2).
   (c) Type b23: w is constant on {a,b} and on {c,d,e} with two values, so C = V_ab (+) V_cde (the (2,3) FS-DEC pattern of rows R4.15) and
       the defect line of K'' is t' in V_cde cap v^perp (two zeros).  Types a3 / b22: t' = (x,x,x,y,z) / (x,x,y,y,z).
   (d) 2-dim zero-row column-centred spaces with defect <= 1 are NOT rigid [numerical, ncol/r8/k2, 5 hits]: products and non-products, defect
       lines with 2 or 3 nonzero entries.  So the K'-KILL mechanism (finitely many admissible Y) has no direct analogue; this piece needs a
       new idea (e.g. a second row, the degree-2/3 parts of D_0(Y)u in C for u in U_i, or FL2*-type lifts with U = U_i).
   (e) FL2* does not apply directly: the 5x5 lift contains e_0 (x) U_i but only e_r (x) (C + C1)^perp, not e_r (x) (U_i + C1)^perp.
 R8.3 ROBUSTNESS: THEOREM L6G's chart pattern is reproduced at p = 2147483629 (34 UNIT, the same 5 charts each with one point;
   ncol/r7/l6gp2.log).  The K' classification charts also segfault with the reduced generator set d_k = M_k d_J (81 equations instead of
   177; ncol/r7/kred.log), so the big-slot run NCOL-K3CLASS stays the route.  Note for the last piece (R8.2): 2-dim zero-row K'' can be
   strongly level (SL_3 allows dim 2), so closed "defect-pattern" systems for K'' are NONUNIT for trivial reasons; e = 1 exactly is open.
STATUS 04:13: round 8 write-up done (L6G + K'-KILL; last piece of case (C) isolated); reporting
 R8.4 ERRATUM (numerical probes) [found this round]: my LM probes lm2z.py (R6.10), lm211.py (R7, "K' (+) e_0 U_0 numerically
   solvable") and lmH.py evaluated the identities at too FEW random points (16-24 points for degree-4 identities in 5-6 variables: fewer
   equations than coefficient conditions), so their "exact solutions" can be FAKE: two lmH "solutions" fail on 60 fresh points (residual
   2.5e4, 3.7e4; ncol/r8/num/chkH.py).  R6.10 is WITHDRAWN as corroboration (its dim-4 failure is still consistent but proves nothing);
   R7's lm211 remark is superseded by the EXACT statement (r211gen mode noYZ: all coefficients vanish identically).  No exact result used
   these probes.  The rows/clm-based censuses (cc3_search.py: 70 points for degree-3 identities in 3 variables) are well sampled, so the
   K' census (R7.2) and the isolation check (k3tan.py) stand.
STATUS 04:19: erratum R8.4 (under-sampled LM probes withdrawn); properly sampled probe (NS=80) of H = ker c + e_0 U_0 for type a3 stalls at residual 1 (dim-4 ker c seemingly impossible); DK=3 calibration running
 R8.5 THE H-CONJECTURE (would close the last piece of case (C)) [setup rigorous; computation in progress].  In the last piece, ker c is
   4-dim and column-centred, its row 0 takes values s(Y) = c^(0)(Y) in U_i^perp, and 1 is NOT in s(ker c) (a Y with row 0 = -1 would give a
   zero row of J + Y: R2.3), so s(ker c) =: E is 2-dim (rho = 2).  H := ker c (+) e_0 U_0 is a 6-dim level space with defect in C.
   (H) CONJECTURE: for U_0 of type a3 / b22 / b23 there is no 4-dim K = ker c of this kind.  Evidence: the properly sampled probe
   (lmH.py, NS = 80) stalls at residual >= 1 (2/2 starts, type a3); BUT the dim-3 calibration has not yet produced a solution either
   (1.17 after one start; rigid K'-type solutions are hard to hit by LM), so this is weak evidence.
   EXACT SYSTEM (type a3; ncol/r8/hgen.py): U_0 = V_012, U_0^perp = span(1, e_3, e_4); K in Gr(4,13) (coordinates sg0, sg3, sg4, a, b),
   C = V_012 (+) C t'', t'' = p f1 + q f2 (families T0: p = 1, T2: p = 0, invariant under S3 x S2 x Z2); 37 unknowns, ~250 equations;
   74 orbit charts (orbh.py) x 2.  Plain charts segfault at 2 GB; STAGED by the number of s-pivots: 3 s-pivots (s-map contains 1, excluded
   by level): UNIT 4/4 instantly (hs3.log); 2 s-pivots refined by these: running (hs2.log); then 1 and 0 s-pivots.
STATUS 05:15: resumed after the usage-limit cut-off (04:25-05:15). Stage-2 H charts: family T2 (C = V_012 + V_34) 12/19 UNIT, family T0 1/19; properly sampled probes: a3 4/4, b22 2/2, b23 2/2 stall at dim 4 (dim-3 calibration solved, verified on fresh points)
 R8.6 H-CONJECTURE, TYPE a3, FAMILY T2 (C = V_012 (+) V_34, the (3,2) FS-DEC pattern): PROVED [modular 65521, closed projective system
   (K in Gr(4,13), C fixed), all 715 charts via 74 orbits, staged refinement; RED-p -> char 0].  Stage 1 (3 s-pivots) 2/2 UNIT; stage 2
   (2 s-pivots) 11 UNIT plain-refined + 8 UNIT after re-refinement with the stage-2 UNITs (hs2.log, hs2b.log); stage 3 (1 s-pivot) 31/31
   UNIT (hs1t2.log); stage 4 (0 s-pivots) 22/22 UNIT (hs0t2.log).  So: with U_0 = V_012 and C = V_012 (+) V_34 there is NO 4-dim
   column-centred K with row 0 in U_0^perp such that K (+) e_0 U_0 is level with defect in C.  Family T0 (C = V_012 (+) C(f1 + tp f2),
   all other C) is in progress: stage 2 only 1/19 UNIT so far (hs2.log).
 R8.7 H-CONJECTURE, further evidence [numerical, properly sampled NS = 80, ncol/r8/num/]: dim-4 K stalls at residual >= 1 in a3 4/4,
   b22 2/2, b23 2/2 starts; the dim-3 calibration (a3) reached 3.8e-25, CONFIRMED on 60 fresh points (2.3e-24), with s-map rank 2 and a
   1-dim zero-row part (not a K' type).  So the jump is again exactly at the extremal size.  Family T0 of type a3 (generic C): staged
   refinement by fixed-point iteration (hiter.sh: each pass uses only charts verified in earlier passes) is running; stage-4 plain/refined
   charts: some UNIT (6 s, 0.7 s, 18 s), some segfault.
 R8.8 CALIBRATION OF THE H GENERATOR [exact point check, ncol/r8/hcal/pt.ms]: with 3 basis vectors (3-dim K) in family T2, the exact
   point K = K'(3,4; 0,1) = span(n1 (e_3 - e_4)^T, n2 e_0^T, n2 e_1^T), U_0 = V_012, C = V_012 + V_34 (t = e_3 - e_4 perp U_0) satisfies all
   126 equations; perturbing one coordinate breaks 8-10 of them.  So in family T2 the 3-dim version HAS solutions (and the generator is
   right) while the 4-dim version is UNIT on all 74 orbit charts (R8.6): the jump sits exactly at dim K = 4.  (The 3-pivot msolve runs
   mostly segfault at 2 GB -- positive-dimensional solution sets; but chart 1_3_4 of family T2 completed: NONUNIT (29 GB elements),
   a direct msolve calibration of the same family; hcal.log.)
STATUS 05:26: round 8 closing: L6G + K'-KILL; H-conjecture proved for a3 / C = V_012 + V_34, calibrated; generic C and b22/b23 queued (NCOL-HCONJ-A3T0, NCOL-HCONJ-B); local T0 iteration still running until ~05:49 (ncol/r8/hiter_T0.log)

## Round 9 (ncol; start 05:28 UTC)
STATUS 05:28: round 9 started; stopped the local T0 iteration (2 GB cap vs the new 0.5 GB pool rule; host has ~1 GB free) -- A3T0 stays in the big slot; working on a hand proof of the H-conjecture
 R9.1 SECOND-ORDER IDENTITIES FOR H [rigorous derivation; formulas checked to 1e-13 on the verified 3-dim solution, ncol/r9/delta2chk.py,
   a3ident.py].  Notation: Y in K (column-centred, row 0 = -s, s in U_0^perp), rows 1..3 column j = (s_j/3) 1 + a_j nu_1 + b_j nu_2;
   S, A, B = sums of s, a, b; Q_{jj'} = (2/3) s_j s_j' - 3(a_j b_j' + a_j' b_j) (j != j', zero diagonal), R = Q 1, Qtot = sum_{j<j'} Q_{jj'}.
   (P) 3x3 block identities: P_2(block T) = sum_{j<j' in T} Q_{jj'};  perm(block T) = (2/9) s1 s2 s3 - sum_{distinct} s_i a_j b_k + 6 a1a2a3 + 6 b1b2b3.
   (D2) degree-2 part of D_0(Y)u (u in U_0):  -Qtot u + 2 u o R - (u.R) 1 + Q u  in C;  so u.R = 0 and 2 u o R + Q u in C.
   (C2) degree-2 part of the defect of Y:  -2(S^2 - |s|^2) 1 + 4 S s - 4 s o s + 2 Qtot 1 - 2 R  in C; level gives Qtot = S^2 - |s|^2.
   TYPE a3 (U_0 = V_012, w normalised to (0,0,0,mu,nu), t' = C cap U_0^perp ~ ((mu-nu)/3,(mu-nu)/3,(mu-nu)/3, nu, -mu)), with
   X := B a + A b - 2 a o b:
   (I1) 6X + (8/3)(S s - s o s) + gamma 1  lies in  C t'  for every Y in K   (gamma = 2Qtot - 2(S^2-|s|^2));
   (I2) (b.u)(a.w) + (a.u)(b.w) = 0 for every Y in K, u in V_012.
   [(C2) gives v := 6X + (8/3)(Ss - s o s) + gamma 1 in C; inserting it into (D2), whose only conditions mod C are the two functionals
   "sum" and ". w", the first kills the V_012-component of v (V_012 is nondegenerate) and the second is (I2).]
 R9.2 CONSEQUENCES FOR TYPE a3 [rigorous]: write a = abar 1_012 + a' (a' in V_012 on columns 0,1,2), same for b; s is constant on 0,1,2.
   (I2') p b' + q a' = 0 as vectors of quadratic forms on K (p := a.w, q := b.w).  (I1') the function j -> B a_j + A b_j - 2 a_j b_j is
   constant on {0,1,2}.  CASE A (p, q independent): a' = -c p, b' = c q for a fixed c in V_012, and (I1') forces c = 0 or, up to S3,
   c ~ (1,1,-2) together with -(B - 2 bbar) p + (A - 2 abar) q = 2x p q (c = x(1,1,-2)).  [Proof: (I1') becomes c_j L + (2c_j^2 -
   (2/3)|c|^2) pq = 0; if some c_j = 0 then |c|^2 = 0 and c = 0; otherwise f(c_j) = -2c_j + (2/3)|c|^2/c_j is the same for the three j,
   which forces two equal entries and the third = -2 x.]  So in case A two of the columns 0,1,2 COINCIDE on every Y in K (all three if
   c = 0).  The verified 3-dim solution has c = 0 (a, b constant on {0,1,2}: all three columns equal) and p, q independent.
   CASE B (p, q dependent) and the final contradiction in each case: OPEN (by hand).  Exact runs of the H system with these case-split
   equations added still exceed 0.5 GB resident in 10 s (ncol/r9/hc.log, RSS-capped runner ncol/gb/runlog_rss.sh).
STATUS 05:38: H-conjecture by hand: second-order identities (D2), (C2) derived and checked; type a3: (I1), (I2) => case A forces two (or three) of columns 0,1,2 to coincide on K; case B open; exact runs blocked by the 0.5 GB resident rule
 R9.3 CLOSED CASE COVER FOR TYPE a3 [rigorous]: every K satisfying (I1'), (I2') lies in one of the CLOSED (linear, given w) loci
     COLL_{jj'} (columns j, j' in {0,1,2} equal on K: a_j = a_j', b_j = b_j'),  j j' in {01, 02, 12};
     E1: b.w = 0, b' = 0, bbar + b_3 + b_4 = 0;   E2: the a <-> b mirror (a.w = 0, a' = 0, abar + a_3 + a_4 = 0);   E3: a.w = b.w = 0.
   Proof: case A (p, q independent) -> R9.2 -> COLL.  Case q = kappa p, p != 0, kappa != 0: (I2') b' = -kappa a'; (I1') gives
   a'_j (M + 2 kappa a'_j) = (2/3) kappa |a'|^2 for j = 0,1,2 (M = (B - 2bbar) - kappa(A - 2abar)); if a'_0, a'_1 were independent the
   pairwise differences give M = 2 kappa a'_2 = 2 kappa a'_1, contradiction; so a' = c l and, as in case A, c = 0 or c ~ (1,1,-2): COLL.
   kappa = 0 (q = 0): b' = 0 and (B - 2bbar) a'_j = 0, so a' = 0 (COLL) or B = 2 bbar (E1).  p = 0, q != 0: mirror (COLL or E2).
   p = q = 0: E3.  So (H) for type a3 <=  H cap COLL01, H cap COLL02, H cap COLL12, H cap E1, H cap E2, H cap E3 all empty (closed
   systems; the E's are S3-invariant, the COLL's are permuted by S3, so on orbit-representative charts all six are needed).
   Calibration: the exact 3-dim point K'(3,4;0,1) + e_0 V_012 (family T2) satisfies all 132 equations of the E3 system (ncol/r9/hcp/)
   and violates COLL01 (it lies in E3: p = q = 0).  The verified numerical 3-dim T0 solution lies in COLL (all three columns equal).
   Cost: these systems carry many extra linear equations; sample T0 charts run under the 0.5 GB RESIDENT cap (runlog_rss.sh).
STATUS 05:48: a3/T0 case cover: E1 and E2 UNIT 148/148 on all orbit charts (instant); refined COLL cover (CA/CB) sample running
 R9.4 REFINED COLL COVER AND FIRST RUNS [rigorous cover; modular runs, 65521, RSS <= 0.5 GB].  Case A with c = x(1,1,-2) (equal pair jj',
   odd index k) gives a_j - a_k = -3x p, b_j - b_k = 3x q; case B (q = kappa p, kappa != 0) gives b' = -kappa a'.  Closed loci:
     CA_{jj'}: a_j = a_j', b_j = b_j', x0 (a_j - a_k) + 3x (a.w) = 0, x0 (b_j - b_k) - 3x (b.w) = 0,  [x0 : x] in P^1  (x = 0: all three equal);
     CB_{jj'}: a_j = a_j', b_j = b_j', k0 (b.w) - k (a.w) = 0, k0 (b_j - b_k) + k (a_j - a_k) = 0,  [k0 : k] in P^1;
   with E1, E2, E3 they cover every K satisfying (I1'), (I2') (x0 = 0 in CA gives p = q = 0, i.e. E3).  Generator ncol/r8/hgenc.py
   (cases CAjj'_0/1, CBjj'_0/1, E1, E2, E3), driver ncol/r9/hcase_all.sh.
   RESULTS (family T0, generic C): E1 UNIT 74/74 and E2 UNIT 74/74 orbit charts (instant, <= 4 MB; ncol/r9/hE.log).  E3: 2/3 sample charts
   UNIT, one over the cap; plain COLL_{jj'}: over the cap or 2 GB VM (hcs.log); refined CA/CB: sample running (hcr.log).
STATUS 05:50: round 9 write-up: identities + closed case cover for a3; E1/E2 done; heavy cases queued (optional HCASE route); reporting
 R9.5 A SECOND ROUTE: THE ZERO-ROW PART K_0 [Lemma SL_3 rigorous + numerical evidence, properly sampled; ncol/r9/k0/lmk0.py].
   In the last piece, K_0 := ker s (2-dim, zero row, column-centred) has defect inside C t' (t' spanning C cap U_0^perp).
   (a) [rigorous, rows' Lemma SL_3 (c)] if e(K_0) = 0 then K_0 = span(nu_1 (e_a - e_b)^T, nu_2 (e_c - e_d)^T), {a,b} cap {c,d} = empty: RIGID.
   (b) [numerical, calibrated] 2-dim zero-row spaces with e = 1 seem to need >= 2 zero entries in the defect line (also: m with ONE zero, 3/3 converged starts e = 0, k0_more.log): with m = e_2 - e_3
       LM finds e = 1 solutions (2/4 starts; calibration), with generic m (4/4) or m = (x,x,x,y,z) (3/3) only e = 0 solutions; all 5 e = 1
       census hits of round 8 have >= 2 zeros in m.  CONJECTURE K0: e(K_0) = 1 forces >= 2 zero entries in its defect line.
   CONSEQUENCE (given K0): for type a3 with generic C, t' = ((mu-nu)/3 x3, nu, -mu) has no zero entry, so K_0 is the rigid SL_3 pair of
   (a), and the last piece becomes an L6G-type problem with K_0 FIXED (finitely many choices up to symmetry): admissible Y in ker c with
   K_0 (+) e_0 U_0 (+) C Y level -- a small system (like L6G, which ran in seconds), to be set up next round.
STATUS 05:56: second route: K_0 rigid (SL_3) whenever its defect line has < 2 zeros (numerical K0 conjecture, calibrated); planning the K_0-fixed system
 R9.6 THE K_0-FIXED SYSTEM, TYPE a3 [modular 65521, closed projective (Y in P^10, C in P^1 via T0 + T2), char 0 by upper semicontinuity
   of fibre dimension; ncol/r9/k0gen.py, k0s.log].  Fix K_0 = span(nu_1 (e_a - e_b)^T, nu_2 (e_c - e_d)^T) (Lemma SL_3 pair; orbit types
   under S3 x S2 x Z2: (ab|cd) = (01|23), (01|34), (03|14)), U_0 = V_012, C = V_012 + C t''.  "Admissible" Y in P(V_0'/K_0): K_0 (+) C Y
   (+) e_0 U_0 level with defect in C (11 unknowns, ~53 equations).  RESULT: 64/66 charts UNIT; the other two have ONE point each:
   (01|23), T0: Y = x e_4^T (single-column, x = (-1,1/3,1/3,1/3)) at tp = -3, i.e. C = V_0123 (column 4 NEUTRAL -- the a4 case, excluded by
   C2); (01|34), T2: Y = nu_1 e_0^T (one non-reduced point, length 4) at C = V_012 + V_34.  So the admissible set is FINITE for every C.
   Since every Y in ker c is admissible, P(ker c / K_0) is finite, i.e. dim ker c <= 3 -- but the last piece has dim ker c = 4.
   THEOREM H-a3-SL [char 0]: in the last piece of case (C) with U_0 of type a3, the zero-row part K_0 of ker c is NOT strongly level
   (i.e. e(K_0) = 1).  Together with CONJECTURE K0 (R9.5: e(K_0) = 1 needs >= 2 zeros in its defect line t', but t' is zero-free for
   every non-neutral a3 C except C = V_012 + V_34, which is done by R8.6) this would prove the H-conjecture for type a3 BY A SMALL
   COMPUTATION (66 systems, seconds, <= 5 MB) instead of the big-slot runs.
STATUS 06:03: round 9 closing: THEOREM H-a3-SL (66 tiny systems); conjecture K0 is the remaining gap for a3; reporting

## Round 10 (ncol; start 06:06 UTC)
STATUS 06:06: round 10 started; attacking CONJECTURE K0 via the degree-2 pencil: for dim S = 2 the products l_j lam_j lie on an affine line in the pencil <LM, Q_2>; base-point-free => an involution iota of P^1 with lam_j ~ iota(l_j)
 R10.1 THE b22 K_0-FIXED SYSTEM [modular 65521, closed projective; char 0 by semicontinuity; ncol/r10/k0gen2.py, k0b22.log].
   U_0 = V_01 + V_23, U_0^perp = span(1, e0+e1, e4), C = U_0 + C(f1 + tp f2) [T0] or + C f2 [T2], f1 = (1,1,0,0,-2), f2 = (0,0,1,1,-2).
   SL_3 pairs (ab|cd) up to (0 1), (2 3), nu_1 <-> nu_2: 6 types ((01|23), (01|24), (02|13), (02|14), (02|34), (04|23)); x {T0, T2} x 11
   charts = 132 systems (0.3 s, < 5 MB): 128 UNIT; the other 4 contain only Y = x e_4^T (single-column, x = (-1,1/3,1/3,1/3)): for every C
   one point (T0: the line {that point} x A^1_tp, non-reduced of length 2 in the chart; T2: one reduced point).  Hence the admissible
   set is FINITE for every C, P(ker c / K_0) is finite, dim ker c <= 3: THEOREM H-b22-SL: in the last piece with U_0 of type b22, K_0
   is not strongly level.  [A precedence bug in the first b22 generator (Y without its a/b coordinates) was caught by the unknown list
   and fixed before these runs; the a3 output of the generalised generator reproduces k0gen.py byte for byte.]
   With CONJECTURE K0 this leaves, for b22, only the C where t' = C cap U_0^perp has >= 2 zeros: C = U_0 + C f2 (T2) and C = U_0 + C f1
   (tp = 0) (the third, C inside e_4^perp, has a neutral column).
STATUS 06:15: THEOREM H-b22-SL (132 tiny systems; a generator precedence bug caught and fixed first); K0 itself: BPF normal-form GB exceeds 0.5 GB; pure-a sub-case reduces to a root count
 R10.2 K0: STRUCTURE [rigorous] AND SUB-CASES.  Let S be a 2-dim zero-row column-centred 3x5 level space (isotropic coordinates
   (a, b); x, y coordinates on S), defect line m, e = 1.  With l_j = a_j - A/2... (hat forms l_j := a_j + (1/3)... as in R2.6'):
   (i) d2 = -6 Q_2 m and l_j lam_j = LM/9 + m_j Q_2 (binary quadratics; L = sum l_j, M = sum lam_j); d3 = Q_3 m; e = 1 <=> (Q_2, Q_3) != 0.
   (ii) K0 <=> S has >= 2 NEUTRAL columns (m_n = 0 means the 4x5 zero-row space is neutral at n).
   (iii) if <LM, Q_2> is a base-point-free pencil, it is <x^2, y^2> after a change of coordinates on S; then lam_j = kappa_j iota(l_j),
        iota(x:y) = (x:-y), and m_j = 0 <=> the root of l_j lies in {root(L), iota root(L)} (with matching scale).
   (iv) sub-cases by (r_a, r_b) = ranks of the a- and b-projections: (2,0)/(0,2) pure, (1,1) product of two points, (2,1)/(1,2), (2,2).
   Exact classifications over Q of the small sub-cases (2,0) and (1,1) by minimal associated primes: running (ncol/r10/k0_20.sing,
   k0_11.sing).  The general (2,2) case in the base-point-free normal form (24 unknowns) exceeds 0.5 GB already for a GB mod p.
 R10.3 K0, SUB-CASE (2,0), GENERIC PART BY HAND [rigorous]: S = (W_a, 0), d2 = 0, d3_k = -6 a_k e_2(a without k) = m_k Q_3, Q_3 != 0.
   If m_k != 0 then a_k is not 0 on W_a (else Q_3 = 0) and a_k divides Q_3 (a binary cubic: at most 3 root classes).  So if the forms
   a_k (k with m_k != 0) are pairwise non-proportional, at most 3 of them exist: m has >= 2 zeros.  Proportional pairs (W_a in a
   hyperplane x_k = c x_k') need the extra identity E_k - E_k' = (a_k - a_k')(a_k + a_k' - A) (E_k := e_2(a without k)); the exact
   classification of (2,0) by minimal primes over Q is running (k0_20.sing).
 R10.4 WHERE THE H-CONJECTURE STANDS (given CONJECTURE K0):
   a3: done for every C (non-neutral C with zero-free t' by H-a3-SL + K0; C = V_012 + V_34 by R8.6).
   b22: non-neutral C with zero-free t' by H-b22-SL + K0.  t' has >= 2 zeros exactly for C = U_0 + C f2 (zeros 0,1) and C = U_0 + C f1
        (zeros 2,3), which the block swap {0,1} <-> {2,3} exchanges (it fixes U_0 = V_01 + V_23), so ONE fixed-C system remains:
        family T2 of type b22 = the first job of NCOL-HCONJ-B (hiter3.sh b22 2).
   b23: t' always has two zeros, so K0 does not apply; needs the b23 runs of NCOL-HCONJ-B or a classification of the e = 1
        two-dim spaces with defect line in V_234 (target 3).
   K0 itself: (2,0) generic part by hand (R10.3); exact (2,0) over Q ran out of memory at 0.5 GB; mod-32003 classification and the exact
   (1,1) classification are running.
STATUS 06:31: K0: BPF and (1,1)-with-m systems out of memory at 0.5 GB over Q; lighter (1,1) (rank<=1 minors) and (2,0) mod 32003 running; b22 K_0-fixed done (H-b22-SL)
 R10.5 CORRECTION (verify2's question on R9.5 (a)) [rigorous + modular data]: rows' Lemma SL_3 (c) classifies only N = Pi cap {row sums of
   the 3x5 part = 0}; a strongly level 2-dim Pi can a priori have (q, dim N) = (2,0), (1,1), (0,2) with q = dim of the image of the row-sum
   map Y -> A(Y) nu_1 + B(Y) nu_2 (rows 1..3).  K_0 = zero-row part of ker c has NO reason to have zero row sums (the K' types of R7.2 have
   B != 0), so R9.5 (a) holds only when q(K_0) = 0.  And the gap is real: the strongly level 2-dim zero-row column-centred spaces form
   1-DIMENSIONAL families (ncol/r10/slgen.py, sl.log: all 3 S5 x Z2 orbit charts of Gr(2,10) NONUNIT with Krull dimension 1), not just the
   30 rigid pairs.  THEREFORE: THEOREM H-a3-SL and THEOREM H-b22-SL are proved ONLY for q(K_0) = 0 (K_0 a rigid pair); the strongly level
   K_0 with q in {1, 2} still have to be excluded (their own family-parametrised K_0 systems, or an argument).  The rest of R9.6 / R10.1
   (closedness, finiteness, char-0 transfer) stands.
 R10.6 CLOSING THE q(K_0) >= 1 GAP FOR TYPE a3 [modular 65521 + semicontinuity; one completeness input left].
   (a) Strongly level 2-dim zero-row column-centred spaces, mod 65521 (minimal primes in the 3 S5 x Z2 orbit charts of Gr(2,10);
       ncol/r10/slgen.py, sl.log, /tmp decompositions recorded below): exactly
         - the 30 rigid pairs span(nu_1 (e_a-e_b)^T, nu_2 (e_c-e_d)^T)               (q = 0, isolated points);
         - F1(a,b)[h0:h1] = span(nu_1 (h0 e_a - h1 e_b)^T, nu_2 (h0 e_a + h1 e_b)^T)  (two columns, no single-column element);
         - F2(a,b)[h0:h1] = span((h0 nu_1 + h1 nu_2) e_a^T, (h0 nu_1 - h1 nu_2) e_b^T) (two single-column elements);
       (chart (0,5): four F1 curves; chart (0,1): one F2 curve; chart (0,6): 6 rigid pairs + two F2 curves).  Each family member is
       strongly level for every [h0:h1] (exact check: K_0 alone produces no equation, kfam.py).
   (b) K_0-FAMILY SYSTEMS, type a3 (ncol/r10/kfam.py, kfa3.log): F1 types (01),(03),(30),(34), F2 types {01},{03},{34} (up to S3 x S2 x Z2)
       x [h0:h1] charts x {T0, T2} x 11 Y-charts = 308 systems: 248 UNIT; in all 60 NONUNIT charts the admissible set is FINITE OVER THE
       PARAMETERS (block-order GB: every Y-variable has a pure-power leading monomial, ncol/r10/fib/: 60/60), e.g. F1(0,1): only
       Y = x e_3^T and x e_4^T for every (h, C) -- and their span is NOT admissible (spanchk_*.sing: UNIT).  With the rigid pairs (R9.6) this
       gives: for every strongly level K_0 and every C, P(ker c / K_0) is finite, so dim ker c <= 3.
   (c) Remaining input for char 0: COMPLETENESS of the list (a) in characteristic 0.  The mod-p scheme is reduced in charts (0,1)
       (checked) but NOT in chart (0,5) (I != rad I), so the "no extra char-0 component" argument needs either generic reducedness along the
       F1 curves (to be checked) or a hand classification of strongly level 2-dim spaces (rows' SL_3 (b)/(c) give q = 2 => N = 0 and the
       N-part; the q >= 1 parts are the families above).
STATUS 06:45: verify2 gap answered (R10.5); q>=1 strongly level K_0 = families F1, F2 (mod p); a3 family systems 308: 248 UNIT + 60 finite-over-parameters => H-a3-SL extends to all strongly level K_0, modulo char-0 completeness of the family list
 R10.7 ROUTE TO CHAR-0 COMPLETENESS OF THE STRONGLY LEVEL LIST [plan, from rows' SL_3 proof]: write Y = nu_1 p^T + nu_2 r^T, row sums
   sigma = (sum p) nu_1 + (sum r) nu_2, q = dim of the row-sum image.  rows' (b): for q = 2 the columns are eta_j = A_j sigma with
   B_j := 2A_j - id in O(V_3) (isometries of the 2-dim quadratic space V_3: diagonal diag(t, 1/t) or antidiagonal in the isotropic basis),
   sum_j B_j = -3 id (row sums), plus the cubic (S3_j); for q = 1, N is 1-dim of the SL_3 (c) form plus one section.  This is a finite,
   explicit classification (5-tuples of O(2) elements) that should reproduce exactly F1, F2 (and the rigid pairs for q = 0), in char 0,
   without RED-p.  Not done this round.
STATUS 06:49: b22 family systems running (kfb22); chart-(0,5) primary decomposition running
 R10.8 HAND CLASSIFICATION OF STRONGLY LEVEL 2-DIM SPACES WITH q = 2 (partial, rigorous so far) [rows' SL_3 (b) normal form]:
   columns eta_j = A_j sigma, B_j = 2A_j - id in O(V_3), sum B_j = -3 id, plus (S3_j).
   * all B_j rotations diag(t_j, 1/t_j): then Pi = span(nu_1 alpha^T, nu_2 beta^T), alpha = (t+1)/2, beta = (1/t+1)/2 (a product); (S3_j) for
     all j forces e_3 of every 4-subset of alpha (and of beta) to vanish, so alpha, beta have <= 2 nonzero entries, i.e. t_j = -1 for >= 3 j;
     with sum t = sum 1/t = -3: t = (-1,-1,-1, tau, -tau) up to order => Pi = F1(a,b)[1+tau : 1-tau] (incl. V_3 (x) e_a at tau = 1);
     four t_j = -1 forces the fifth = 1: Pi = V_3 (x) e_a = F1 at h1 = 0.  No other case.
   * reflections B_j (u -> c_j ubar): column j stays on the line C(nu_1 + c_j nu_2); two reflections with c_b = -c_a and three t = -1
     give F2(a,b)[1 : c_a].  Mixed / more-reflection cases still to be checked with (S3_j).
   q = 1 and the remaining mixed cases: next round.  Once finished this gives the char-0 completeness needed in R10.6 (c).
 R10.9 THE q(K_0) GAP IS CLOSED [rigorous classification in char 0 + modular K_0-family systems with semicontinuity].
   (a) CLASSIFICATION (char 0) of 2-dim strongly level zero-row column-centred 3x5 spaces Pi (q = dim of the row-sum image):
       q = 0: the rigid pairs (rows' SL_3 (c));
       q = 1: Pi = span(Z, Y0), Z = l u(e_a-e_b)^T + l' ubar(e_c-e_d)^T (SL_3 (c) form): EXACT over Q (ncol/r10/slq1.sing, minimal primes,
              both charts of the row-sum normalisation): l' = 0 is forced (or l = 0, mirror) and Pi = span(u e_a^T, u e_b^T) = F2(a,b)[1:0]
              or Pi = span(u(e_a-e_b)^T, ubar(e_a+e_b)^T) = F1(a,b)[1:1];
       q = 2: rows' SL_3 (b) normal form, B_j in O(V_3), sum B_j = -3 id.  All rotations: F1 (hand, R10.8; the 5-nonzero case of alpha is
              excluded since e_3(alpha without k) = 0 for all k forces e_3 = e_2 = 0 and alpha_k = A for all k).  Exactly two reflections:
              F2 (EXACT over Q, slq2.sing: t = (-1,-1,-1), c free).  Three reflections: UNIT over Q(w) (slq2.sing).  One, four or five
              reflections: impossible by sum B_j = -3 id.
       => strongly level 2-dim zero-row spaces = rigid pairs  U  F1  U  F2, in characteristic 0.
   (b) K_0-FAMILY SYSTEMS: type a3 308 systems (248 UNIT, 60 NONUNIT with fibres finite over the parameters (h, tp), fib/ 60/60);
       type b22 572 systems (520 UNIT, 52 NONUNIT, fibres finite 52/52, fibb22/).  Families up to symmetry: a3: F1 (01),(03),(30),(34),
       F2 {01},{03},{34}; b22: F1 8 ordered types, F2 5 types.  So for EVERY strongly level K_0 and every C the admissible Y are finitely
       many (char 0 by semicontinuity of fibre dimension over the projective parameter space), hence dim ker c <= 3.
   THEOREM H-a3-SL and THEOREM H-b22-SL hold for ALL strongly level K_0 (q = 0, 1, 2), not only for the rigid pairs.
STATUS 06:53: q-gap closed (classification + family systems); reporting

## Round 11 (ncol; start 06:55 UTC)
STATUS 06:55: round 11 started; K0 big-slot driver, b22-T2 feasibility test, hand reduction
 R11.0 verify2 VERIFIED the closure of the q(K_0) gap (slq1/slq2 re-run, reflection count, 112/112 fibre checks): H-a3-SL and H-b22-SL VERIFIED for all q (PROOF-MAP item 5). Case (C) now leaves CONJECTURE K0, type b23 and the K' classification.
 R11.1 K0 BIG-SLOT DRIVER [setup]: ncol/r11/runK0Q.sh (spec K0Q-SPEC.txt, QUEUE line NCOL-K0Q): every S has r_a = 2 or r_b = 2 (then, up to
   S5 x Z2, it lies in the Pluecker chart (0,1) of Gr(2,10)) or (r_a, r_b) = (1,1).  Jobs: chart (0,1) x 7 charts of (Q2, Q3) in P^6 (e = 1)
   x Rabinowitsch prod_{j != I} m_j != 0 (I in {0, 2}, the classes under the chart stabiliser); plus (1,1) x 3 x 2.  Singular std over Q
   (exact); resumable, per-job timeout, one verdict file per job.  K0 <=> all 20 verdicts are 1.  Local triage impossible (mod-p runs exceed
   0.5 GB / time out).
 R11.2 K0, HAT-COORDINATE FORM OF THE DEFECT [rigorous identity]: with l_k = a_k - A/2, lam_k = b_k - B/2, c_a = e_2(a) - A^2/4,
   c_b = e_2(b) - B^2/4:  e_2(a without k) = c_a + l_k^2, hence
        d2_k = -6 l_k lam_k + (3/2) A B,      d3_k = -6 [ (l_k + A/2)(c_a + l_k^2) + (lam_k + B/2)(c_b + lam_k^2) ].
   So the defect is ONE fixed pair of functions Psi_2(l, lam), Psi_3(l, lam) evaluated at the 5 points P_k = (l_k, lam_k) (forms on S),
   with sum_k l_k = -3A/2, sum_k lam_k = -3B/2; K0 says at least two P_k lie on {Psi_2 = Psi_3 = 0}.  (Hand route, not finished.)
 R11.1' job order of runK0Q.sh (coordinator's request): (1,1) sub-case first (6 small jobs), then chart (0,1) with the Q2-charts (generic e = 1) before the Q3-charts, I = 2 before I = 0.
 R11.3 TYPE b23, STRONGLY LEVEL K_0 [modular 65521, closed projective, char 0 by semicontinuity; ncol/r10/kfam.py and k0gen2.py with TYPE
   b23]: C = V_01 + V_234 fixed (w = (3,3,-2,-2,-2)), U_0 = span(e0 - e1, v), v = (0,0,1,tp,-1-tp) [T0] or e3 - e4 [T2], U_0^perp =
   span(1, e0+e1, (0,0,-tp,1,0)) resp. span(1, e0+e1, e2).  Symmetry used: (0 1) and nu_1 <-> nu_2 only.
   Families F1 (13 ordered types), F2 (7 types) x [h0:h1] x {T0,T2} x 11 Y-charts = 880 systems: 630 UNIT, 250 NONUNIT, and in ALL 250
   the admissible set is finite over the parameters (h, tp) (fibb23.log: 250/250 FIBRES_FINITE).  Several admissible loci sit at
   tp^2 + tp + 1 = 0, i.e. v = (0,0,1,w,w^2).  Rigid pairs (9 types x {T0,T2} x 11 = 198 systems): running (k0b23.log).
 R11.4 b22 family T2 needs the big slot (7 of the first 12 charts over the 0.5 GB cap in 4-10 s; local staged pass stopped at 07:08 with 8 UNIT / 30 RSSCAP / 1 TIMEOUT in h3_b22_T2_p1.log, which the big-slot hiter3.sh reuses): queued as NCOLHB22T2 (ULIM 8 GB, CT 600, 2 h) after NCOLK0Q, not before ~11:00 UTC.
 R11.5 THEOREM H-b23-SL [modular 65521 + semicontinuity; with the char-0 classification R10.9]: rigid pairs for b23 (9 types up to (0 1) and
   nu_1 <-> nu_2) x {T0,T2} x 11 Y-charts = 198 systems: 182 UNIT, 16 NONUNIT, all finite (14 by the block-order fibre check, 2 parameter-free
   T2 charts whose GB is a single reduced point).  With R11.3 (families 880: 630 UNIT + 250 finite): in the last piece with U_0 of type b23,
   K_0 is NOT strongly level.  So for all three w-stable types the strongly level K_0 are excluded; what remains of case (C) is exactly
   e(K_0) = 1: CONJECTURE K0 (types a3, b22) and, for b23 (whose t' always has two zeros), the e = 1 two-dim spaces with defect line in V_234.
STATUS 07:10: round 11 closing: H-b23-SL proved; K0Q and b22-T2 queued; reporting
 R11.6 K0, SUB-CASE (2,0) (and (0,2)) DONE [exact over Q; ncol/r11/k0_20b.sing]: S = (W_a, 0), W_a in the chart with pivots 0,1 (every
   2-dim W_a is there up to S5); conditions e_3 = 0 on W_a and rank <= 1 of the five binary cubics a_k e_2(a without k) (2x2 minors, no m
   variables).  Minimal primes over Q: ONE component, the point W_a = span(e_0, e_1), where all cubics vanish (e = 0; it is F2 at h1 = 0).
   So there is NO 2-dim pure space with e = 1 at all: K0 holds (vacuously) in sub-cases (2,0) and (0,2).  Remaining: (1,1), (2,1)/(1,2),
   (2,2) -- the first in the big slot's job order, the rest in chart (0,1).
STATUS 07:14: K0 (2,0) done exactly; (1,1) b-projective charts and the (2,1) rank-minor decomposition being tried locally
 R11.7 CONJECTURE K0 IS FALSE [exact; ncol/r11/cex/cex1.py (isotropic formulas, Fractions), famchk*.sing].  Counterexample (sub-case (1,1)):
        S = span( nu_1 a^T , nu_2 (e_0 - e_1)^T ),   a = (-3, -3, 7, 14, -21).
   Check: e_3(a) = 0, e_3(b) = 0, sum a b - A B = 0 (b = e_0 - e_1, B = 0, a_0 = a_1), so P_2 == P_3 == 0; d2_k == 0 for all k
   (A b_k + B a_k - 2 a_k b_k = 0 since a_0 = a_1 = A/2); d3_k = -6 x^3 F_k with F = (a_k e_2(a without k))_k = 21 (49, 49, -81, -36, 19):
   e = 1 and the defect line m = (49, 49, -81, -36, 19) has NO zero (no neutral column).
   FAMILY [rigorous, by the same computation]: b = e_i - e_j, a_i = a_j = s, the other three entries c, d, e with c + d + e = 0 and
   e_3(a) = 0 (<=> 2 s e_2(c,d,e) + c d e = 0); m = (f(a_k)), f(t) = t((t - s)^2 + e_2(c,d,e)), m_i = m_j, generically zero-free.  A
   1-parameter family up to S5 (it has m_i = m_j, which is why the round-9 census at generic m / (x,x,x,y,z) / (x,x,y,y,z) missed it).
 R11.8 THE SHAPES THAT MATTER ALSO OCCUR [exact, famchk2.sing]: inside this family,
   (a3 shape m_0 = m_1 = m_2, b on {0,1}): exactly 2 Galois orbits: c = s, 3d^2 + 3ds + 2s^2 = 0 (over Q(sqrt -15)) and c = 2s,
     d^2 + 2ds + 2s^2 = 0 (over Q(i)); both zero-free.  (b on {0,3} or {3,4}: none.)
   (b22 shape m_0 = m_1, m_2 = m_3, b on {0,1}): c = d = -3s, i.e. a = (1,1,-3,-3,6), m = (-27,-27,33,33,-12) (RATIONAL, zero-free), and
     2c + 2d = s, 6d^2 - 3ds + 2s^2 = 0 (over Q(sqrt -39)).  (b on {0,2} or {0,4}: none.)
   So the K0 route for a3 / b22 cannot work as stated: each such K_0 matches t' for one specific C, and there the K_0-fixed system
   (as R9.6) must be run.  The general (2,1)/(2,2) sub-cases may contain further members.
STATUS 07:19: CONJECTURE K0 FALSE (exact counterexample family); a3- and b22-shaped zero-free members exist; telling coordinator
 R11.9 RESTRICTED K0, (1,1) SUB-CASE [modular 32003, triage; ncol/r11/k0r.py, runK0R_local.sh, K0R11.log]: zero-free e = 1 members with the
   b22 shape in the (1,1) charts: 0-dim, VDIM 6-9 per chart (more than the 3 family points (1,1,-3,-3,6) and the Q(sqrt -39) pair), so
   the (1,1) sub-case has members OUTSIDE the R11.7 family.  Over Q run started (exact list needed).  Calibration: the chart containing
   the known members is non-unit (VDIM 9 for b22, 20 for a3).
 R11.10 K_0-FIXED SYSTEMS FOR THE KNOWN MEMBERS [ncol/r11/k0gen3.py; mod 65521 with sqrt(-1), sqrt(-15), sqrt(-39) mod p]: K_0 explicit,
   Y in P(V_0'/K_0) (11 charts), tp free.  Calibration KCAL (the K_0-only equations): b22 rational member gives tp = -11/9, exactly the
   C with t' ~ m = (-27,-27,33,33,-12).  First chart (z0, T0): UNIT.  Running all 7 members x 2 x 11 = 154 systems (kfix.log).
STATUS 07:26: K_0-fixed member systems generated (154); restricted (1,1) classification over Q running; big-slot driver rewritten
 R11.11 A SECOND KIND OF ZERO-FREE MEMBER: "S4-TYPE" [exact over Q(i); ncol/r11/cex/cexS4.sing]: with zeta = -1 + i,
        S = span( nu_1 a^T , nu_2 b^T ),  b = (zeta, zeta, zetabar, zetabar, 1),  a = conj(b) = (zetabar, zetabar, zeta, zeta, 1):
   P2 = P3 = 0, d2_k = 6xy m_k, d3_k = 12(x^3 + y^3) m_k with m = (1,1,1,1,-4): e = 1, zero-free, and m has BOTH the a3 shape and the
   b22 shape.  Mod-p census (R11.9): the b22-shaped (1,1) members are exactly the 3 family points (two equivalent placements) and the
   6 sign patterns b = (zeta^{eps_k})_{k<4} + (1) with two + and two - (a = conj b), VDIM 9 = 3 + 6 and 6 matching across all charts.
   Up to symmetry, the K_0-fixed systems needed are: b22: eps = ++--, +-+-; a3 (special entry at 4): eps = +--+, -++-  (k0gen3.py
   members b22_e1, b22_e2, a3_e1, a3_e2; expected tp = 1 since m = F1 + F2 for both types).
STATUS 07:28: K_0-fixed systems for 11 explicit members queued locally (242 tiny); (1,1) census mod p complete; Q run in progress
 R11.12 THE (1,1) CENSUS, MOD p [modular 32003, all 36 orbit charts x Q-charts; K0R11.log; points via gbpts.py]: every chart is 0-dim and
   the counts are explained exactly by three member types (with their symmetric images and a <-> b swaps):
     (F) the R11.7 family members (b22: rational + Q(sqrt -39) pair; a3: Q(sqrt -15) and Q(i) pairs);
     (S4) the S4-type members of R11.11 (m = (1,1,1,1,-4) up to position of the -4);
     (N, a3 only) NEW [exact over Q(sqrt -15), cex/cexN.sing]: a = (s,s,s,1,-1-s), b = (0,0,0,1,beta) with (s, beta) = ((-3 -+ r)/4,
         (-7 +- r)/8), r^2 = -15: P2 = P3 = 0, e = 1, m ~ (9-3r, 9-3r, 9-3r, -81-9r, 54+18r), zero-free, a3 shape.
   (b22: 9 = 3 F + 6 S4 in the charts seeing all; a3: 20 = 12 S4 + 8 F, 14 = 12 S4 + 2 N, 16 = 12 S4 + 4 N, all consistent.)
   NOT YET A PROOF of completeness: the Rabinowitsch (zero-free) condition is open, so this needs the over-Q run (in progress).
 R11.13 THEOREM (members excluded) [modular 65521 with sqrt(-1), sqrt(-15), sqrt(-39) mod p; the K_0-fixed system is closed projective
   (Y in P^10 by 11 charts, C in P^1 by T0/T2), so emptiness mod a prime above p implies emptiness in char 0 by properness]:
   for EVERY member above (F: 7 incl. conjugates; S4: 4 placements; N: 4 incl. conjugates and the a <-> b swap), with its own C
   (KCAL: the K_0-only equations force tp = tp0: b22 F rational -11/9, b22 F sqrt-39 6, S4 1, a3 F/N sqrt-15 the same two values), the
   admissible-Y system is UNIT in all 22 charts (330 systems, kfix.log): ker c = K_0, contradicting dim ker c = 4.
   Calibration: the rigid pair (01|23) for a3 reproduces R9.6 (one chart non-unit, a single point at tp = -3).
   So: H-a3 and H-b22 (last piece of case (C)) follow from H-a3-SL / H-b22-SL + this, PROVIDED the zero-free a3/b22-shaped e = 1
   list is complete: (1,1) over Q (local, running) and the r_a = 2 charts (NCOLK0Q, big slot).
STATUS 07:31: all known zero-free members (F, S4, N types) excluded by K_0-fixed systems (330 UNIT, calibrated); completeness pending
 R11.14 THE (1,1) SUB-CASE BY A HAND CASE SPLIT [rigorous + exact over Q; ncol/r11/k0_11case.py, case11/]: S = span((a,0),(0,b)),
   D_k = A b_k + B a_k - 2 a_k b_k, F_k = a_k e_2(a without k), G_k = b_k e_2(b without k); e = 1 means D, F, G are multiples of m.
   LEMMA Z [rigorous]: F == 0 implies |supp a| <= 2.  (F_k = a_k h(a_k), h(t) = t^2 - A t + e_2(a) = (t - r1)(t - r2).  r1 = r2 = r
     forces N r = 2r; a zero root forces one nonzero entry; two distinct nonzero roots with multiplicities n1, n2 >= 2 are impossible:
     (2,2): e_2 = -2 r1^2 != r1 r2 = -r1^2; (2,3)/(3,2): e_2 = -5 r^2 != -2 r^2; n_i <= 1 gives |supp| <= 2.)
   CASE A (F == G == 0): by Lemma Z some k lies outside supp a u supp b, and there D_k = 0, so m_k = 0: not zero-free. IMPOSSIBLE.
   CASE B (G == 0, F != 0; Case B' = the swap a <-> b): F zero-free, so all a_k != 0, and |supp b| <= 2.
     B0 (D == 0): for k outside supp b, B a_k = 0, so B = 0, b = beta(e_i - e_j), and D_i = b_i (A - 2 a_i) = 0 gives a_i = a_j = A/2:
        EXACTLY the R11.7 family [rigorous].
     B1 (D != 0, so D zero-free) [exact over Q, std + minAssGTZ, b = e_i + beta e_j over the orbit pairs, a_0 = 1]: a3: only supp b =
        {3,4}, one Q-irreducible point pair = the N-type; b22: NONE (all 4 systems UNIT).
   CASE C (F, G != 0, so all a_k, b_k != 0; chart a_0 = b_0 = 1): one system per shape, over Q, running (case11/C_*.out).
STATUS 07:34: (1,1) reduced by hand to Case C (one chart per shape, over Q, running); Case B done exactly (only N-type)
STATUS 07:37: waiting on Case C over Q (host load ~14, slow); 32 split sub-systems prepared as fallback
 R11.15 PLAN FOR THE r_a = 2 CHARTS IF THE BIG SLOT STALLS [idea, not run]: the shape equalities are products of linear forms.  With
   l_k = a_k - A/2, lam_k = b_k - B/2 (linear forms on S), d2_k = 3(AB/2 - 2 l_k lam_k), so m_i = m_j forces l_i lam_i = l_j lam_j as binary
   quadratics; by unique factorisation either both vanish or (l_j, lam_j) = (c l_i, lam_i / c) ["same"] or (c lam_i, l_i / c) ["crossed"].
   Then d3_i = d3_j becomes l P_a(l) = mu P_b(mu) (mu = lam/c, P_a(t) = c_a + (c+1)(A/2) t + (c^2+c+1) t^2, c_a = e_2(a) - A^2/4; c = 1 means
   columns i, j equal).  Splitting every shape pair this way gives linear substitutions (given c) and much smaller systems; the same split for
   Case C of (1,1) is k0_11C3.py (16 sub-systems per shape).
 R11.16 THE (1,1) SUB-CASE IS COMPLETE [rigorous hand split R11.14 + exact over Q; ncol/r11/k0_11C3.py, case11/C3/, C3.log]:
   CASE C split by the factorisation F_i - F_j = (a_i - a_j)(a_i^2 + a_i a_j + a_j^2 - A(a_i + a_j) + e_2(a)) (and the same for G) over the
   shape pairs: 16 sub-systems per shape, all over Q in seconds (the monolithic system did not finish in 7 min).  Results:
     b22: EEEE (1 Q-component, 2 points) + QQQQ (2 components, 4 points): exactly the 6 S4-type points (the -4 at position 4); rest UNIT.
     a3:  EEQQ, QQEE, QQQQ (2 components each, 12 points): exactly the 12 S4-type points (the -4 at position 3 or 4); rest UNIT.
   (components: z^2 - z + 1/2 = 0, entries in {1, 2z - 1, -z}, gam = 2z - 1, del = -2z: the S4 pattern.)
   THEOREM (1,1) [char 0]: the zero-free e = 1 two-dim spaces of the form span((a,0),(0,b)) with defect line of the a3 / b22 shape are
   exactly the F, S4 and N members (N only for a3) and their symmetric images; by R11.13 none of them extends to the last piece.
   So the K0-route for H-a3 / H-b22 now needs ONLY the r_a = 2 Pluecker charts (NCOLK0Q, 42 jobs; the (1,1) jobs were removed from it).
   Local test: the r_a = 2 charts exceed 0.5 GB mod p even with the R11.15 same/crossed split (k0rs.py, 2/2 halt 14).
STATUS 07:45: round 11 closing: (1,1) restricted classification COMPLETE (exact); all members excluded; r_a = 2 charts in big slot; reporting

# ROUND 12 (ncol; start 07:47 UTC). Targets: (1) (6,2) configurations (c)/(d) via L_gct_216/217 (kill a nonzero doubly-centred
#  level part Q_00); (2) b23 with e(K_0) = 1 (defect line in V_234); (3) same/crossed split for r_a = 2 if the big slot lags; (4) (SR3), (CCN).
STATUS 07:47: round 12 started; reading the (c)/(d) setting (N1.2/N1.3, R4.10)
 R12.1 WALSH COORDINATES FOR 4x4 [exact, ncol/r12/walsh.sing]: t = Ht X Ht^T, Ht = 4x4 Walsh-Hadamard (first column 1), X = [[0, u^T],
   [v, x]] (u, v in C^3, x in C^{3x3}; total sum 0 = the degree-1 level condition).  Row sums of t = 4 Ht(0,v), column sums = 4 Ht(0,u).
        perm(J + t) - 24 = P2 + P3 + P4,   P2 = 16 (|x|^2 - 3|u|^2 - 3|v|^2)   (Frobenius / standard forms),
        P3 = 64 [ 3u1u2u3 + 3v1v2v3 + sum_ij v_i u_j x_ij - sum_i sum_{k} u_k x_{ia} x_{ib} - sum_j sum_k v_k x_{aj} x_{bj} + perm_3(x) ]
   ({a,b,k} = {1,2,3}), P4 = 225 terms.  On u = v = 0 this is L_gct_216's form (16|x|^2, 64 perm_3 x, F).  So a 4x4 level Q is a totally
   isotropic subspace of (C^15, q2 = |x|^2 - 3|u|^2 - 3|v|^2) (max 7) with P3 == P4 == 0; Q_00 = Q cap {u = v = 0}.
 R12.2 STRUCTURE IN (c)/(d) [rigorous]: the degree-1 part of C(L') is the column-sum map, so rank u(Q) <= e(L') = 2; rank v(Q) <= e^col(Q).
   (c): dim Q = 5, rank u, rank v <= 2  => delta := dim Q_00 >= 1.   (d): dim Q = 6, rank u <= 2, rank v <= 3 => delta >= 1.
   Polarising P2 at q0 in Q_00: <x0, x(q)> = 0 for all q in Q, and W := x(Q_00) is isotropic; the map phi: u,v-image N -> W^perp/W,
   (u,v) -> x mod W, is a similitude (<phi w, phi w'> = 3<w, w'>) with kernel K = Q cap {x = 0}.  Isotropy alone does not kill
   (dimension count consistent for delta >= 1): P3, P4 are needed.  (c) and (d) are "slack 2" problems in the sense of NOTES-methods.
 R12.3 b23 WITH e(K_0) = 1, THE (1,1) SUB-CASE [rigorous split + exact over Q; ncol/r12/b23_11.py, b23/, b23s/]: target shape
   m = (0,0,m2,m3,m4), m2 m3 m4 != 0 (t' for generic U_0; t' = (0,0,-2tp-1, tp+2, tp-1) in chart T0).  Split as R11.14 (Lemma Z):
   CASE A (F == G == 0, |supp a|, |supp b| <= 2, m ~ D, D_0 = D_1 = 0, D_2 D_3 D_4 != 0), all 72 ordered support pairs over Q: the ONLY
     solutions are the 1-parameter family A23 (up to S2 x S3 and a <-> b): a = (0,0,a2,a3,0), b = (0,0,0,b3,b4), a2(b3+b4) + a3 b4 = 0
     (a curve in P^1 x P^1); e.g. a = e2 + h e3, b = e3 - e4/(1+h).
   CASE B (G == 0, F != 0): all 60 systems UNIT -- no members.
   CASE C (F, G != 0): monolithic systems time out (120 s); factorised split (F_0 = a_0 h_a(a_0) etc., 16 codes x 9 charts): running.
 R12.4 THE FAMILY A23 IS EXCLUDED [modular 65521; closed projective family (4 charts cover the curve), Y in P^10, U_0 in P^1 (T0/T2) =>
   char 0 by properness/semicontinuity; ncol/r12/k0gen4.py, kf4/res.log]: K_0-fixed (b23: C = V_01 + V_234, U_0 = V_01 + C v) admissible-Y
   systems with the family parameters free: 88 systems, 76 UNIT, 12 NON-UNIT with DIM 0 (finitely many (parameter, Y) points), all
   FIBRES_FINITE: for every member the admissible Y are finite, so dim ker c <= 3 < 4.  Calibration: the rigid pair (01|23) through the
   same generator gives NON-UNIT exactly in T0 z0-z3 with finite fibres, as k0b23.log (R11.5).
STATUS 08:00: b23 (1,1): Case A = one family (excluded, 88 systems), Case B empty, Case C split running; (c)/(d): Walsh identities + structure, numerics weak
 R12.5 b23 (1,1) CASE C: all 144 factorised sub-systems UNIT over Q (cross-check: the 9 unsplit systems UNIT mod 32003).  So the (1,1)
   members for generic U_0 are exactly the family A23, excluded by R12.4.
 R12.6 b23 SPECIAL U_0 (v = (0,0,1,1,-2), t' ~ e2 - e3; the three special tp are one case up to S3) [exact over Q, b23sp/]: (1,1)
   members only in Case A: K_0 = span(nu_1 a^T, nu_2 (e2 - e3)^T) with a in span(e_i, e_j), {i,j} in {0,1,4}, sum a != 0 (and a <-> b);
   Cases B, C empty.  K_0-fixed systems at tp = 1 (k0gen4.py MC 10-13, kf5/res.log): 44 systems, 36 UNIT, 8 NON-UNIT all FIBRES_FINITE
   [modular 65521, closed projective]: excluded.  So b23 (1,1) is done for every U_0; b23 r_a = 2 charts remain open (not queued).
 (c)/(d) status: R12.1-R12.2 only (Walsh identities, Q_00 != 0 forced, isotropy structure); no kill.  A numerical search tool
   (ncol/r12/qsearch2.py) did not converge reliably at d = 5 even on the unconstrained calibration, so it gives no evidence.
STATUS 08:05: STOPPED on the coordinator's instruction (L-gct-210 aborted by Kevin); all my jobs stopped.
STOPPED 08:05
