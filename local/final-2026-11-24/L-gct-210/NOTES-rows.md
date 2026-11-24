# NOTES-rows (role rows; start 14:17, budget 90 min -> ends ~15:47)
## RESULT, ROUNDS 21-22 (rows; 06:50-08:00 UTC) -- (SM4) REFUTED (rank-2 counterexample); case G proved BY HAND; (SM5) proved in rank <= 2;
##   G4-A reduced by hand; REAL trick (Q(i) -> Q) for all Walsh-coordinate generators
 Details: section R21 (R21.1 - R21.11).
 J1 [counterexample, verified exactly by verify2] (SM4) and (SM4'') are FALSE: rank-2 configurations on a Walsh coordinate plane (kappa = 0
    there).  W4P/W4Q stopped; SM4 big-slot jobs dropped; PL4 unaffected (own proof).  Corrected chain R21.6.
 J2 [hand, R21.8] support-4 case G: the ka^3, ka^2, ka^1 coefficients force C_T = 0, B_kk = 0, K(c(s_k),u,u) = 0 at 4 distinct points --
    impossible for the nonzero binary quadratic K(c(z),u,u).  Kills R15GQ and G4-z5.
 J3 [hand + exact Q, R21.5/R21.10] (SM5) holds in rank <= 2.  A counterexample to (SM5) must have rank 3 (big-slot SM5 jobs).
 J4 [hand + exact Q, R21.9-R21.9''''] G4-A CLOSED: the same chain gives l = 0; case (b) w = mu u impossible by hand (u a vertex, B^u
    has a triple root); case (a) (vertex pairs) = finitely many planes, exact certificate g4acert UNIT.  Kills R15G4P/Q.
 J7 [R21.12] the degree-2/3 relaxation of (SM5) has rank-2 5-column solutions: W5 and SP5 can never be unit; rank-3 W5 files made.
 J5 [R21.7] REAL trick: x_2 -> i x_2; every condition is (power of i) x (rational); realify.py converts the Q(i) files (parity check
    printed: 0 failures in every run).  Case-G plane mod P1 2x faster at 1/3 memory; P2-z3 REAL mod P1 UNIT 4 s; over Q running in the pool.
 J6 R4, R5 planes: no hand chain (general 5-column identity R21.11 does not separate); big slot (REAL versions available).
## RESULT, ROUND 20 (rows; 06:35-06:48 UTC) -- W4P running in the pool (3 h, 0.5 GB resident cap; ~0.18 GB); W5P exceeds the cap (big slot);
##   degree 2 of (SM4'') solved by hand in the main chart (R20.1); no hand proof yet
 Details: section R20 (R20.1 - R20.4).
 I1 [pool] W4P (rows/r18/w4_2147483629.sing) running since 06:35 under rsscap 500 MB / 10800 s; W4Q follows in the same worker (log kW.out).
    W5P: killed by the cap at 341 s -> R19W5P/Q stay in the big slot.
 I2 [rigorous, R20.1] in the chart "y_1, y_2, y_3 a basis with nondegenerate Gram", degree 2 <=> G_12 + G_13 + G_23 = 0 and y_4 = G_23 y^1 +
    G_13 y^2 + G_12 y^3 (dual basis); f = 0 <=> all G_ii = 0, y_4 = 0 <=> all G_ij = 0; the triples through y_4 are linear in
    (a,b,c) = Gamma^{-1}(G_23, G_13, G_12) and imply the cyclic identity P_12 P_23 P_31 + P_13 P_32 P_21 = 0 when abc != 0.
 I3 the adjugate (rational) form of this chart blows the 0.5 GB cap faster than the polynomial W4 system; W4P stays the decision.
 I4 (CCN): scoping only (R20.4).
## RESULT, ROUND 19 (rows; 06:13-06:4x UTC) -- (SM4'') reformulated three ways (Walsh, square-zero algebra, g-form/cube-linearity);
##   smallest exact tests (Walsh coordinates, rational) put FIRST in the big slot; no hand proof yet
 Details: section R19 (R19.1 - R19.4).
 H1 [rigorous reformulations] (SM4''): degree 2 <=> |g_j|^2 = |f|^2 (g_j = f - 2 y_j, sum g_j = 2f) <=> (A^2+B^2+C^2) e = 0 in
    R = C[z]/(z_k^2); degree 3 <=> ABC = 0 in R <=> kappa(z.y) linear on {+-1}^4 <=> sum kappa(g_j) = 2 kappa(f) and
    kappa(g_j + g_k - f) = kappa(g_j) + kappa(g_k) - kappa(f) for three pairings.
 H2 [numerical] the obstruction needs all four triples (one dropped: solutions exist, dropped value never 0); vanishing subpermanents
    alone allow generic rank-3 matrices with no zero entries.
 H3 [computation] Walsh-coordinate generator sm5w.py (12 / 15 variables, rational, chart f_1 = 1 complete by symmetry): n = 3 calibration
    dim 4 (0.06 s); n = 4 exceeds 15 min in the pool (0.18 GB, chart run) -- the generator run w4 (0.45 GB) was still going at the close.
    Big slot (coordinator): R19W4P, R19W5P FIRST among rows' jobs, then SP/SMC; R19W4Q/W5Q first among the Q versions.
 Not reached: (CCN).  Pool jobs <= 0.45 GB throughout.
## RESULT, ROUND 18 (rows; 05:24-06:15 UTC) -- isotropic slice written as an auditable lemma chain; (SM_n) reformulated over Q (cubic
##   relaxation, no i) and queued AHEAD of the conic jobs; a stronger 12-variable conjecture (SM4'') found numerically; no hand proof yet
 Details: section R18 (R18.1 - R18.4).
 G1 [rigorous, R18.1] lemma chain IS0-IS5 for verify2: single-matrix degree 2 <=> g_k = f - 2 y_k isotropic; fixed-point count IS1;
    principal kernels IS2 ((SM5) => (PL), (SM4) => PL4); (2,1) kernels IS3 (generic e1 + ka n has the plane support; the |S_0| >= 4 list);
    charts IS4 (one affine chart for n = 4 by S_4 transitivity on the vertices; n = 5 all-vertex case exact, 120/120 + calibration).
 G2 [rigorous reformulation, R18.3] the cubic part of (SM_n) has RATIONAL coefficients: moment equations sum la_k ta_k^m = 3 sg^m (m = 0,1,2)
    and t(c(a),c(b),c(c)) = 16 i Phi(a,b,c), Phi = abc(ab+bc+ca) - (a+b+c).  A unit verdict over Q is an exact char-0 certificate (relaxation).
    Numerics: the cubic part alone already excludes n = 4, 5 (0/8 each; n = 3 converges).  Big slot: R18SP5P, R18SP4P (queued first),
    then R17SMC5P/SMC4P; Q versions R18SP5Q/SP4Q before R17SMC5Q/SMC4Q.
 G3 [numerical, R18.4] (SM4''): four nonzero columns are impossible even for NON-isotropic nonzero f and without permanents (0/8;
    calibration n = 3 6/6).  12-variable exact test (Walsh coordinates, chart f_1 = 1) running in the pool (rows/r18/sm4wc_p.out).
    (SM5) genuinely needs isotropy (K_II elements have 5 nonzero columns and non-isotropic row sum).
 G4 binary model (R18.2): rows of m^2 are the values h_r(m) of the four tetrahedral quadrics; configurations of (SM_n) are isotropic
    2-planes of C^{n+1} (OG(2,5) = P^3 for n = 4) -- a rational parametrization without points at infinity; no hand proof found.
 Not reached: (CCN) analogue.  Host memory stayed at 0.6-1.5 GB free; all pool runs <= 0.49 GB.
## RESULT, ROUND 17 (rows; 03:54-05:25 UTC, interrupted 04:25-05:15) -- NEW REDUCTION: the ISOTROPIC SLICE.  (SM4) + (SM5) would give (PL),
##   re-prove PL4 and close every remaining leaf-3 case at once; exact SM runs are in the big slot (pool too small)
 Details: section R17 (R17.1 - R17.6).
 F1 [rigorous, R17.5] (SM_n): "no strongly level 4x5 matrix with nonzero ISOTROPIC row sum has exactly n nonzero columns".
    (a) (PL) <= (SM5), PL4 <= (SM4): Y_u = R^{-1} u (u isotropic, generic) has columns (u - B_k u)/2, all nonzero.
    (b) leaf 3: the generic element e1 + ka n of K_0 has row sum u and support = the plane support; so (SM4) + (SM5) exclude support-4 G,
        P2-A and support-5 G4, R4, R5, P5, S23, P2-A, P2-z3 -- i.e. ALL big-slot leaf-3 pieces (R15GQ, R15G4P/Q, R15R4P/Q, R15R5P/Q, R16P2*).
 F2 [numerical] forced-support LM: n = 4: 0/8, n = 5: 0/12; calibration n = 3: 8/8, n = 2: 6/6.  [exact] n = 3 mod P1: dim 3 (not vacuous).
 F3 [exact Q(i)] (SM5) all-vertex configurations (the only ones beyond one affine chart): 120/120 unit; calibration 120/120 non-unit.
 F4 computations: y-form and conic form (60x faster at n = 3) of (SM4), (SM5) exceed 0.43-0.88 GB locally -> big slot R17SM*/R17SMC*.
 F5 (PL) reflection split (R17.1, rigorous): a reflection column gives a principal plane on 4 columns; numerics (R17.3): none with all
    four columns nonzero (0/8 forced, unforced runs end on <= 3 columns).  Superseded in importance by F1.
 F6 target 3 ((CCN) analogue): not started; note R17.2.
 Memory: several idle background wait-loops were reaped by the host for low memory (not failures); no pool jobs running now.
## RESULT, ROUND 16 (rows; 03:13-03:55 UTC) -- leaf 3: support-5 P2 z34/z345 exact; all-vertex configurations exact; S23 condition audit
##   (verdict unchanged); closing statement drafted; remaining pieces all in the big slot.  (PL): Veronese SUMQ, 5-7x faster, in the big slot
 Details: section R16 (R16.1 - R16.8).
 LEAF 3 STATUS FOR verify2 (after round 16).  Char 0 done: two and three columns (all); support 4: P2, P3, PP (exact), P4 (hand); support 5:
   P3, P4, PP, P5, S23 (exact), P2 sub-cases z34, z345 (exact), all-vertex configurations for R5 and G4 (exact enumeration, R16.4).
   PENDING (big slot, mod P1 already unit where run): support-4 G (R15GQ, Q(i)); support-5 P2 z3, A (R16P2z3, R16P2A, Q(i)); G4-A (R15G4P/Q);
   R4 (R15R4P/Q); R5 (R15R5P/Q).  When these are unit, the closing statement R16.3 becomes final; manifest rows/leaf3/MANIFEST.txt.
 E1 [exact Q(i), R16.2] support-5 P2 z34, z345.   E2 [exact Q(i), R16.4] all-vertex configurations (R5, G4): 120/120 unit, calibrated.
 E3 [audit, R16.7] S23 plane test had an unjustified extra nonvanishing factor; rerun without it: still exact unit.  Other generators checked.
 E4 [rigorous, R16.5] support-5 P2 consequences (columns 3,4,5 orthogonal to sg(d,d), sg(d, m_1 - m_2)); z3, A still need > 0.42 GB.
 E5 [(PL), R16.1] Veronese SUMQ calibrated (3 columns) and 5-7x faster on 4 columns; 5-column patterns exceed 0.45-0.9 GB locally ->
    big slot R16V5* (equivalence with sumq.py argued in the message to the coordinator).  R16.6: reflection-column strata note.
## RESULT, ROUND 15 (rows; 02:10-03:15 UTC) -- leaf 3 (b): support 4 is char 0 except case G (mod P1); support 5 is char 0 for P3, P4, PP,
##   P5, S23, mod P1 for P2; G4-A, R4, R5 and the char-0 G runs are in the big slot
 Details: section R15 (R15.1 - R15.11).
 LEAF 3 STATUS FOR verify2 (after round 15).  (a) closed (round 13).  (b) (2,1) kernels on 4-5 columns, by the case trees R14.0/R14.3 and
   the PLANE TEST (R15.1: K_0 = span(e1,n) = rho^{-1}(C u), all columns nonzero when n has none; plane split for zero n-columns):
   SUPPORT 4: P2 [exact Q(i): z3, z34, A], P3 [exact], PP [exact], P4 [hand], G [plane test UNIT mod P1; char 0 pending big slot R15GQ].
   SUPPORT 5: P5, S23 [plane test, exact Q(i)]; P3, P4, PP [plane split, exact Q(i) in every sub-case]; P2 [plane split, UNIT mod P1 in all
   four sub-cases; exact runs in progress, kS5Q.out]; G4 [z5 reduces to support-4 G; A in the big slot R15G4P/R15G4Q]; R4, R5 [plane tests
   in the big slot R15R4P/R15R5P/R15R5M, then R15R4Q/R15R5Q].  Charts at infinity: one chart for <= 5 isotropic points (S_4 transitive on
   the octahedral vertices); R5 has an extra Moebius chart (R15R5M) for the all-vertex configuration.
 D1 [rigorous, R15.1] PLANE TEST and plane split (SUBZ / STAGED); calibrated on supports 2, 3 (dim 2, dim 1).
 D2 [exact Q(i), R15.7/R15.11] support-4 P2 in char 0 (big-slot job R14P2Q no longer needed).
 D3 [exact Q(i), R15.3/R15.10] support-5 P3, P4, PP, P5, S23.
 D4 [mod P1, R15.2/R15.9] support-4 G (30 s); support-5 P2 (4 sub-cases).
 D5 bugs caught and fixed: support-5 plane row sum 2u -> 3u (R15.3; R4 claim withdrawn, big-slot line restored, later replaced by the
    corrected plane test); a driver's argument order (no runs had happened).
## RESULT, ROUND 14 (rows; 01:33-02:10 UTC) -- leaf 3 (b), (2,1) kernels on 4-5 columns: support-4 case tree reduced to ONE open case (G)
##   mod P1, two cases exact over Q(i); support 5 set up but too heavy locally (queued)
 Details: section R14 (R14.0 - R14.7).
 C1 [rigorous, R14.0/R14.3] complete case trees on the doubly centred element n: support 4: P2, P3, PP, P4, G; support 5: P2, P3, P4, P5, PP,
    G4, S23, R4, R5.  CORRECTION: case PP (two parallel zero-sum pairs) was missing from my first support-4 list (added in place).
    One finite conic chart suffices for support 4 (S_4 acts transitively on the 6 octahedral vertices; <= 5 isotropic points involved).
 C2 support 4:  P4 impossible [hand, R13.8(d)];  P3 UNIT [exact over Q(i), 1.6 s];  PP UNIT [exact over Q(i), 1.7 s];
    P2 UNIT after the four "column nonzero" saturations [mod P1, 44 s with the hand consequences R14.4; exact over Q runs out of memory at
    0.88 GB -> queued R14-P2Q];  G OPEN [P1 run: timeout 20 min / 0.66 GB -> queued R14-K21BIG; point family made explicit, R14.7:
    e_2(s) = 0, e_4(s) = -1].
 C3 support 5: generator case5.py (all nine cases); P3 mod P1 died at the 0.48 GB cap (401 s) -> all nine queued (R14-K21BIG).
 What remains in leaf 3: support-4 case G (and P2 in char 0), and all of support 5.  Char 0 needs exact runs; RED-p does not apply
 (the "columns nonzero" conditions are open, R14.6).
## RESULT, ROUND 13 (rows; 00:17-01:30 UTC) -- leaf-3 item (a) CLOSED (RED-p cover of the 16 special points: 64/64 unit at P1); the
##   (2,1) stratum on <= 3 columns is char 0; item (b), (2,1) kernels on 4-5 columns, OPEN with a new structure lemma and partial cases
 LEAF 3 STATUS FOR verify2 (after round 13).  verify2 (round 15) verified in char 0: R10.7, R12.10, family B, the line d = u, the RED-p
   argument.  Now also: (a) the 16 special two-column points -- all 64 charts of the RED-p cover are UNIT at P1 = 2147483629 (R13.3;
   the one chart that had "halted" did not run out of memory -- its timeout ran during my SIGSTOP; rerun unit, 115 s, 0.25 GB).  So the
   two- and three-column (2,1) kernels are DONE.  WHAT REMAINS in leaf 3 is exactly (b): (2,1) kernels supported on FOUR or FIVE
   columns -- not classified.  New tools for (b): LEMMA RS (R13.6, rigorous: degree 2 <=> (R - 2A_k)^T (R - 2A_k) = R^T R; rho(K) = u^perp
   degenerate; normal form M_k = [al_k f_k, m_k, be_k f_k]); for support 4 LEMMA U and case (P) |supp n| = 4 (R13.8, rigorous); numerical
   evidence of non-existence (forced-support census does not converge; the same code finds 2- and 3-column kernels at once); exact normal-
   form generator k21sys.py (calibrated on supports 2 and 3) too heavy for support 4 so far.
 B1 [RED-p, R13.3] 16 special points (8 per i; R12.9 had tested only 4 per i -- flagged): 64/64 charts unit at P1; char 0 by RED-p.
 B2 [exact, R13.3] special locus = line d = u + 8 isolated points (Groebner over Q(i), points at infinity included).
 B3 [rigorous + exact over Q(i), R13.1/R13.1'/R13.2] family B and the line d = u: hand reductions to 4-7 unknowns, exact runs < 1 s.
 B4 [rigorous, R13.6] LEMMA RS (any support).  B5 [rigorous, R13.8] support 4: Lemma U, case (P) with |supp n| = 4; case (G) reduced to a
    2-dim family of 4-point configurations (t(c(a),c(b),c(c)) = 16 i (e_3 e_2 - e_1)).
 B6 [structure only, R13.5] five columns: Veronese-variable SUMQ (sumqv.py) written, not run (cores went to leaf 3).
 FYI ncol R2.14: no effect on leaf 3 / (PL) (R13.7).
## RESULT, ROUND 12 (rows; 23:31-00:17 UTC) -- the (q,d) = (2,1) KERNEL STRATUM IS CLOSED for (5,1): rigorous for the generic two-column
##   kernels and A1/A2 (exact over Q), modular for the special two-column kernels and the three-column family B
 Details: section R12 (R12.0 - R12.12).
 B1 [RIGOROUS, R12.5/R12.5'] (5,1) CRITERION: if every column-centred (4,1) extension K + CZ of a strongly level K (sum m = 0) has a two-column
    m (or there is none), then no (5,1) space contains K.  Reason: the column-centred part of a (5,1) space is >= 4-dim and contains K
    (Lemma SL); two-column m is TC5.  This replaces the pencil argument and the neutral-column case split.
 B2 [RIGOROUS, R12.10] generic two-column (2,1) kernels, m_a = m_b = 0: no column-centred extension (Lagrangian => Z = zeta m^T; zeta
    isotropic; the degree-3 and degree-4 parts kill zeta).  With R11.7: NO (5,1) space contains a generic two-column (2,1) kernel.
    The hand-off (H) to verifyfl is WITHDRAWN (R9.0 ADDENDUM-2).
 B3 [RIGOROUS, R12.8] LEMMA 3COL: a 3-dim strongly level space on exactly three columns has a column of rank 1.  Hence the three-column (2,1)
    kernels are A1, A2 (finite list up to symmetry; Groebner over Q) and the one-parameter family B = span{d e_a, d e_b, x e_c}
    (d isotropic, x = d x sg(d,d)).  Numerical census agrees (no other column-rank types).
 B4 [EXACT over Q, R12.6] A1, A2: no column-centred extension in any chart, so no (5,1) contains them.
 B5 [MODULAR, 3 primes, R12.9] the 8 isolated special two-column points (in Q(sqrt3, i), both e-signs): no column-centred extension.
    *** INCOMPLETE (round 13): only 4 of the 8 points per i were tested; see R13.3 (RED-p cover of all 16 geometric points at P1).
 B6 [MODULAR, R12.11] family B: no column-centred extension (prime 1 complete, all gamma incl. infinity, coprime gauge charts; prime 2 partial,
    unit so far).  Line d = u: column-centred extensions exist only with two-column m (minAssGTZ, 12 components), so TC5 applies.
    Primes 2-3 for B and the line are running in the background (rows/r12/kBU23.out).
 B7 [bug, R12.7] in the round-12 c21s.py point charts the gauge determinant vanished for 4 of the 16 point kernels.  Those runs were stopped
    and no verdict was recorded.  kgen.py now prints the gauge determinant in every run.
 OPEN: (i) exact (over Q) versions of B5/B6; (ii) five-column (PL): R12.12 gives a reformulation only, no proof; the big-slot SUMQ5 runs are the
    only decision procedure so far.
## RESULT, ROUND 11 (rows; 22:49-23:35 UTC) -- column-centred (5,1) over the rank-1 kernels excluded (exact); the GENERIC two-column (2,1)
##   kernel stratum settled BY HAND (NCOL_1 for (4,1); no (5,1) of rank c = 1; no column-centred extension)
 Details: section R11 (R11.1 - R11.7).
 A1 [EXACT over Q, R11.2] column-centred 4-dim extensions: over K_II they force m = e_0 - e_1 (two-column, finitely many lines); over chi (x) C^M
    none exist.  With Lemma SL (a hyperplane cannot be strongly level) + pencil principle / TC5: NO column-centred (5,1) space contains chi (x) C^M
    or K_II.  Together with R10.6: the (q,d) = (1,2) kernel stratum is settled for (4,1) and for ALL (5,1).
 A2 [RIGOROUS, hand, R11.1, R11.4 - R11.6] two-column (2,1) kernels K = span{u(e_a+e_b)^T, (p+e)e_a^T + (p-e)e_b^T, d(e_a-e_b)^T}:
    degree-2 K-Z relations (level forces kappa_U = kappa_W = delta = 0); the K-K-Z cubic forces <pi, z_t> = 0 for pi in
    Pi = span{u o u, d o d, p o p - e o e, u o p, e o d} (inside V) whenever m_a or m_b != 0.  GENERIC case Pi = V: columns c, d, e of Z are
    constant, all rows of every Y in L' agree outside a, b, the deletion vectors have explicit closed forms in (t, <y_a,y_b>), and a short
    case analysis (degree 2, one degree-3 check for m ~ (3,3,-2,-2,-2)) gives a ZERO ENTRY of m: NCOL_1.  The extension Z is UNIQUE for fixed
    (K, m) (five independent gauge-invariant linear conditions), so the pencil principle excludes (5,1) of rank c = 1 (m_a or m_b != 0).
 A3 [RIGOROUS, R11.7] no column-centred 4-dim extension with m_a or m_b != 0 over a generic two-column (2,1) kernel (z_t = 0 forces a 4-dim
    isotropic subspace of the 6-dim (V+V, beta)).
 A4 [structure, R11.3] five columns: the summed-cubic condition = 4 invariant conditions (eigenvalue 3 + octahedral eigenvector) on the 3-dim
    moduli -- expected empty; no proof.  SUMQ5 big-slot verdicts not yet in.
 A5 [modular + hand, R11.9] the SPECIAL two-column (2,1) kernels (Pi strictly inside V) are: a LINE d = u, where K = u^perp (x) e_a (+) C u (x) e_b
    (single-column elements; (SC1) gives z_j in span(u,1), j != a), and FINITELY many isolated (u, d) pairs (al = lam ga, lam^2 + 4 lam + 1 = 0,
    ga^4 = (5 lam + 19)/(lam - 1)).  Exact (4,1) test over the line (rows/r11/chi3gen.py, 0.2-0.4 GB) running with 30-min boxes
    (outputs rows/r11/chi3_{0,1}_long.out).
 A6 [structure, R11.8] three-column (2,1) kernels = two-column (2,1) plane (containing n = d(e_a - e_b)^T) + one direction with column c
    proportional to a two-row vector; the R11.1/R11.4 arguments should adapt.
 OPEN: the isolated special kernels and the line d = u (runs); m_a = m_b = 0 (|supp m| = 3: verifyfl's typed programme; |supp m| = 2: TC5);
    three-column (2,1) kernels; five-column (PL) (big slot: ----- since ~23:05, others in bigq3 pass 1).
## RESULT, ROUND 10 (rows; 22:14-22:50 UTC) -- summed cubic = P_3 of the 4x5 matrix; linear-algebra proof of PL4 cases; THEOREM CHI2;
##   the whole (q,d) = (1,2) kernel stratum settled (incl. no (5,1) via a pencil principle)
 Details: section R10 (R10.1 - R10.7).
 Z1 [RIGOROUS, R10.1] the summed cubic of R9.3 is exactly P_3(h(sigma)) = 0 (the 4x5 LEVEL condition in degree 3); binary-form version
    sum eps_j f o g_j = (n-2) f for the octahedral sextic.
 Z2 [EXACT, R10.2] second proof of PL4 for ++++, ----, ++-- from the summed cubic alone: rank(A^0 - 2I) = 7 on cubics over the respective
    number fields, i.e. 2 is not an eigenvalue of A^0 = sum rho_3(B^0_j) on H_3, so no rotation of the octahedral cubic can satisfy it.
 Z3 [EXACT over Q, R10.6] uniqueness: the only strongly level 3-spaces containing a type-I resp. type-II plane are chi (x) C^M resp.
    K_II = N_II + C (1,1,1,-3) e_e^T.  THEOREM CHI2: a (4,1) space with ker c = K_II has m in {(1,-1,-1,1,0), (1,1,-1,-1,0), (1,-1,1,-1,0)}
    (inactive column neutral; finitely many spaces).  PENCIL PRINCIPLE: if the (4,1) extensions of a kernel K with fixed m are finite, no
    (5,1) space of rank c = 1 has K in ker c.  => (1,2) stratum DONE for (4,1) (NCOL_1) and for (5,1) of rank c = 1.
 Z4 [numerical/structure, R10.3, R10.5, R10.7] five columns: eigenvalue formulation (3 must be an eigenvalue of sum rho_3(B_j) on H_3 with
    octahedral eigenvector; happens on a hypersurface of the moduli); moment-matrix (Choi rank <= n) route; (2,1) kernels exist on 2 and 3
    columns (two-column ones = Lagrangians of (V+V, beta), explicit family).
 COMPUTE: five-column summed systems die at 2 GB (----- 591 s, +---- 581/377 s); ----- in the big slot since 22:32; asked to move all
    six there (QUEUE R10-SUMQ5-note).  A-coordinate variant slower (not to be used).
 NOT DONE: five-column (PL) verdicts / hand proof; (2,1) kernel stratum; column-centred (5,1) (rank c = 0) over these kernels.
## RESULT, ROUND 9 (rows; 21:41-22:15 UTC) -- five columns: structure + the SUMMED-CUBIC cut (7 equations) that already kills 4 columns
 Details: section R9 (R9.0 - R9.3) at the end of this file.
 Y1 [RIGOROUS, R9.1] quaternion form of the degree-2 data on n active columns: sum eps_j v_j v_j^T = (c/2) I, sum eps_j s_j v_j = 0
    (no Choi needed); a column with eps = +1 vanishes iff v_j = 0, eps = -1 columns never vanish.  LEMMA TR5 (five columns): the traces
    s_j^2 = (6+c)(2 - c eps_j + c rho_j^2/Lambda)/12 depend on the kernel vector rho of the 4x5 frame: 3-dim moduli, no single orbit.
    [numerical] all six five-column sign patterns carry degree-2 solutions (6-dim; 7-dim for ++++-).
 Y2 [RIGOROUS identity, R9.3, checked on six genuine strongly level 3-spaces to 1e-14] THE SUMMED CUBIC: sum_j c(B_j sigma) = (n-2) c(sigma),
    c = p_3 = 24 x1x2x3 (Walsh); equivalently (sum_j rho_3(B_j)) c = (n-2) c in the spin-3 representation (7 equations).
 Y3 [numerical] degree 2 + full cubic: 0/9 on five columns; degree 2 + summed cubic ALONE: 0/6 on four and on five columns, 6/6 on three.
 Y4 [modular, p = 2147483629, calibrated] quaternion degree-2 data + summed cubic: three columns ++- non-unit dim 1 and --- non-unit dim 2
    (= the (2,2,1) and (1,1,1) families), +-- unit (Lemma O3); FOUR columns ---- and ++-- UNIT (140 s, 0.13 GB each) -- an independent
    modular re-certificate of these PL4 cases from 7 equations.  FIVE columns: running/queued (R9-SUMQ5; ----- needs > 1.4 GB).
 Y5 [division of labour] proposed to verifyfl in R9.0 (rows: principal stratum + hand cases with a strongly level kernel; verifyfl: typed
    (SL_m) systems).  (DC-COST') (target 3) is only needed for non-principal (5,1) with a neutral column, i.e. it merges into the typed systems.
 NOT DONE: the five-column verdicts themselves; a hand proof of the summed-cubic exclusion.
## RESULT, ROUND 8 (rows; 20:47-21:45 UTC) -- (T3) PROVED; THEOREM PL4: NO PRINCIPAL KERNEL ON EXACTLY FOUR COLUMNS; (PL) reduced to 5 columns
 Details: section R8 (R8.1 - R8.10) at the end of this file.
 X1 [RIGOROUS, hand, R8.1; VERIFIED by verify2] LEMMA O3 / THEOREM T3: three orthogonal maps of a 3-dim complex quadratic space summing
    to 1 include 1 or a reflection (det product -1); so every 3-column principal kernel has a column of rank <= 1.
 X2 [HAND + EXACT over Q, R8.6-R8.10] THEOREM PL4: no 3-dim strongly level K with s(K) = V has exactly four active columns.
    Method: with B_j = eps_j Ad(g_j) (SO(3,C) = PSL_2) the degree-2 data become a quadratic FRAME sum eps_j u_j u_j^T = 2 Omega Omega^T
    + c Q (u_j = vec g_j, Choi matrix), split by the sign pattern eps_j = det B_j:
      +++- (c = 0): all g_j commute; common axis u; the cubic forces the isotropic lines of u^perp onto the six octahedral lines, where
            t(u,n,n) != 0 (30 cases) -- contradiction; isotropic-axis and g_3 = +-1 sub-cases: exact sympy checks over Q(i) (R8.7);
      +--- : LEMMA TR (forced traces tr(g_j)^2 = (4+c)(1 - c eps_j/2)) makes three columns reflections and B_0 a trace-3 involution = 1 (R8.8);
      ++++, ----, ++-- : LEMMA ORB -- the degree-2 data form ONE O(3,C)-orbit of an explicit configuration (tetrahedral for ++++, ----;
            a weighted Parseval frame for ++--); the cubic test over R in O(3,C) (9 unknowns, degree <= 3 only) is the UNIT ideal over Q
            for all three (rows/r8/orb/orbgen.py, orb_ppmm.py; base configurations checked exactly in their number fields; calibration
            on the 3-column (1,1,1) orbit non-unit, dim 2).
    CONSEQUENCES: a principal kernel lives on <= 3 columns or on all five; every principal (5,1) kernel lives on all five columns;
    NCOL-P3 is unconditional except for kernels with five active columns.  Left of (PL): FIVE active columns (R8-Ksign ks5_* running).
 X3 [HAND + EXACT over Q, R8.2] THEOREM CHI1: a (4,1) space with ker c = chi (x) C^M has the two-column line on the complement of M.
 X4 [COMPUTATION, R8.5] msolve segfaults under the 2.5 GB cap on all plane charts; calibration fixed by random slices (R8-B3cal: 40 of
    41 NONUNIT, passed); fibre cut gives a smaller complete plane cover (c3charts.sh) -- deprioritised: the K version suffices.
 NOT DONE: (PL) for FIVE active columns; non-principal (5,1) beyond CHI1 (verifyfl's (SL_m) program: types (2,2), (1,3), (0,4),
    non-principal (3,1)); target 3 (DC-COST') for e = 1 with a neutral column (R8.4: no progress beyond R7.2).
## RESULT, ROUND 7 (rows; 19:45-20:45 UTC) -- THEOREMS X5 and PR5 [exact over Q]: principal (5,1) reduced to (PL) + (T3); DC / NC'-DC repaired; C redesigned
 Details: section R7 (R7.1 - R7.4) at the end of this file.
 W1 [EXACT, R7.3] THEOREM X5: no (5,1) space (any m) contains a 3-dim strongly level K with s(K) = V of column type (2,2,1).  Hand part:
    structure of 3-column kernels with a rank-one column (types (1,1,1) / (2,2,1) only) and the X5 normal form for any m (sub-case
    m_a = m_b = 0 via VF-A / TC5); computer part: Groebner bases OVER Q (Singular), 4 charts covering P^1 x P^1, saturation by the honest
    open condition <n,n'> != 0 (v non-isotropic): unit in all charts; also unit at 3 primes.  Checks: normal form numerically (degrees <= 2
    automatic), calibration (N a line) non-unit and its point confirmed by oracle.py as a (4,1) space (level error 1.5e-13).
    With P51 + VF-A: for m with 5 distinct entries, no principal (5,1) whose kernel lives on <= 3 columns and has a rank-one column or
    lives on two columns.  Left there: (PL) (kernels on >= 4 columns) and 3-column kernels with all column ranks >= 2 (never observed;
    exact check T3 queued).
 W2 [RIGOROUS, R7.2] THEOREM DC' / NC'-DC' (repair of R5.2 after verify2): dim L' = rank c + rank(s|ker c) + dim L'_dc and, for a neutral
    column, dim L' = e + 3 + delta - s1 - s2 - s3' with s3' = e - rank(kappa|ker rho): EXACT identities, so (DI_5) <=> dim L'_dc <=
    (e - rank c) + (3 - rank(s|ker c)) and (NC'_e) <=> (DC-COST') delta <= s1 + s2 + s3'.  The R5.2 forms (rank s, rank kappa) are only
    sufficient.  Corrected chain (R7.2(c)): (DI_5;e) + (NCOL_e for SOME hyperplane) + (DC-COST') => (DI_5;e+1); (DI_5;3) + (NCOL_3) +
    (DI_4x4) => no (7,3).  Generic hyperplanes of a (5,1) space with rank c = 1 are non-principal; principal (5,1) uses the hyperplane K + CY.
 W3 [ANALYSIS + NUMERICAL, R7.1] R6-1 now needs B (4 columns) AND C (5 columns) for (PL); (A) is not needed.  Calibrations: A4 must be
    non-unit (NEW: single strongly level matrices on exactly 4 columns form a 4-dim affine cone S_4, 15/16 LM hits, tangent dim 4), B3 is
    the same-shape control for B, A for C; no same-shape positive control exists for C.  B = lines on the 3-fold P(S_4) (20 unknowns,
    33 conditions).  Cost: msolve on one Rabinowitsch chart of B > 5 min (2 threads); coordinator's Singular A4/B/B3 silent after ~1 h.
    Queued instead: R7-B-charts (126 charts up to column symmetry, msolve) and R7-X4K (the 3-dim K version for 4 / 5 active columns,
    calibration 3 columns; plus T3).  [numerical] no line through the first sampled point of S_4 (best residual 0.15, 6 starts).
 W4 [HAND + EXACT over Q, R7.4] THEOREM PR5: in a principal (5,1) space (any m) the strongly level kernel K lives on >= 4 columns, or on
    exactly 3 columns with all column ranks >= 2.  Types (1,1,1), (3,2) and every 2-column K with m_a = m_b: by hand (+ VF-A, TC5);
    types (3) and (2,1) (where N is rank one, N = A_N (x) m, m_a = 0): unit over Q in all Pluecker charts (24 systems, no saturation for
    type (3)); (2,2,1): X5.  Calibrations (N a line) non-unit.  Hence NO PRINCIPAL (5,1) SPACE  <=  (PL) + (T3), both queued.
 W5 [DESIGN, for the coordinator's C failure] generic-h chart cover rows/r7/x4c2.py (h a generic element of the plane, z_j on one Walsh
    coordinate of each column of h; complete up to columns x Walsh-S_3): C = 21 charts, B = 15 charts, B3 = 10-chart calibration;
    generator verified against directly computed (s,t)-coefficients (B 40/40, C 60/60, both directions).  Queued R7-C2, R7-B3cal, R7-B2,
    R7-C1 (S_5 single-matrix charts; S_5 is a cone over a curve at the known point, tangent plane NOT strongly level).
 NOT DONE: (PL) and (T3) themselves (queued); non-principal (5,1); (6,2), (7,3) beyond the corrected chain.
## RESULT, ROUND 6 (rows; 20:04-20:35, stopped early) -- no new theorem; X4 reduced to strongly level PLANES and queued (R6-1); handover written
 Details: section R6.  [rigorous] reduction of "principal K lives on <= 3 columns" to (PL) "a strongly level plane with injective row
 sums has <= 3 nonzero columns" (R6.1); row-wise form of strongly level (R6.2); erratum to R5.3(b) and remarks (R6.3).
 [numerical] (PL) holds in 169/169 planes; single strongly level matrices with 4 and even 5 nonzero columns EXIST, so the statement is
 about planes, not matrices.  Not done: targets (2)-(4).  Everything a successor needs: handover/HANDOVER-rows.md.
## RESULT, ROUND 5 (rows; final 20:00) -- (NC') NOT proved; (NCOL_1) PROVED in the principal case (Theorem NCOL-P3), exact 4x4 statement found
 Details and proofs: section R5 (R5.1 - R5.13).  Heavy-computation requests: COMPUTE-rows.md (H1-H6, exact systems X1-X4).
 V1 [RIGOROUS, R5.9] THEOREM NCOL-P3: let L' be a 4 x 5 level space with defect line C m (ANY m, isotropic allowed), K in L' a 3-dim strongly
    level subspace with row sums s(K) = 1^perp living on three columns a, b, c, and Z in L' with zero row sums and c(Z) != 0. Then
    m_a m_b m_c = 0 (two columns: m_a m_b = 0). So every (4,1) space whose column-centred part ker c is such a K has a neutral column,
    and it is an active column of K.  Proof: isometries B_j with B_a+B_b+B_c = 1, normal form z_j = m_j((kappa/4)1 + B_j f), <f,f> =
    (3/4)kappa^2 != 0, and a 3 x 3 Gram computation that ends in (alpha+beta-gamma)(alpha-beta+gamma)(-alpha+beta+gamma) = 8 m_a m_b m_c = 0.
    Covers 28 of the 30 known (4,1) spaces (the 2 others are column-centred with a two-column defect line); every ingredient checked
    numerically to 1e-9 or better.  Hypothesis left: "K lives on <= 3 columns" (true for 90/90 principal kernels and 49/49 fresh strongly
    level 3-spaces; types by column ranks (1,1,1), (2,1), (3), (3,2), (2,2,1)); exact problem X4.
 V1' [RIGOROUS, R5.11] THEOREM P51: if the five entries of m are pairwise distinct, there is NO (5,1) space with defect line C m containing a
    3-dim strongly level K with s(K) = 1^perp that is spanned by single-column elements or lives on two columns (kernel types (1,1,1),
    (2,1), (3), (3,2) = 41 of 49 fresh strongly level 3-spaces); a (4,1) space of the first kind is split.  Mechanism: the row-centred
    elements are RANK ONE, Z = a m^T, and the derivative of the deletion vector along each single-column element forces a = kappa e_i.
    Left for principal (5,1): kernel type (2,2,1), repeated entries of m (incl. isotropic (1,w,w^2,0,0)); see also R5.10.
 V1'' [NUMERICAL + partly rigorous, R5.12] (R-LAW): in all 90 principal extremal spaces every row-centred element has ALL ITS ROWS IN THE
    DEFECT SPACE C (N = L' cap ker s lies in C^4 (x) C; Z w = 0 for w in W); proved for kernels spanned by single-column elements (any e).
 V2 [RIGOROUS, R5.6] (SC1) first-order law for a single-column element x e_n^T in ANY column: <x, s(Y) - y_n> = 0 and (<x,y_j>)_{j != n} in
    C cap e_n^perp for all Y in L'.  For e = 1 and m_n != 0: all other columns of all of L' are orthogonal to x.
 V3 [RIGOROUS, R5.2] THEOREM DC / NC'-DC: dim L' = rank c + rank s + dim L'_dc, so (DI_5) can fail only through DOUBLY CENTRED elements.
    With a neutral column:  dim L' = e + 3 + delta - s1 - s2 - s3,  delta = dim Q_dc,  s1 = e^col(Q) - rank rho,  s2 = 3 - e^col(Q) - dim X_n,
    s3 = e - rank kappa (all >= 0).  So the exact 4 x 4 statement behind (NC'_e) is (DC-COST): delta <= s1 + s2 + s3; (NC') holds whenever Q
    has no doubly centred element; with the checked L_gct_216: dim L' <= e + 6.  Bilinear form of the problem (R5.1):
    Xh^T (Adj(q) - 6J) Wh = 0 on Q and the claim dim Q + dim Xh + dim Wh <= 8, which interpolates between a triviality (Q = 0) and the
    checked L_gct_214 (Xh = Wh = C1). The checked 4 x 4 theorems 214/216/217 alone do NOT give (DC-COST).
 V4 [RIGOROUS, R5.3] (NCOL_3) + (DI_4x4) => no (7,3), where (DI_4x4): "a 4 x 4 level space has dim Q <= e^col(Q) + 3" = (DI_5) for 4 x 5
    spaces with a zero column; it needs only: no (dim, e^col) = (5,1), (6,2); (5,1) with a two-column line is excluded by TC5.
 V5 [NUMERICAL, calibrated] 4 x 4: (4,1) 9/17, (5,1) 0/14; (5,2) 2/10, (6,2) 0/15; any 6-dim 4 x 4 level space 0/15; row-centred (4,1): 1/34
    and that hit has a two-column defect line.  Block pattern (3,2) for (6,3): 0/30 (control 4/19).  Towers continue: in all 120 cases
    the 4 x 4 base Q has again a deletable row or column.  Principal census: 90 of 95 extremal spaces have ker c = strongly level
    3-space with s = 1^perp, always on <= 3 columns, always containing a single-column element in a neutral column.
    Slack census: delta = 0 in 126 of 135 tower positions; delta > 0 in 7, always paid exactly (s3 or s1); s2 = 0 always.
 V6 [RIGOROUS, partial, R5.13] (NCOL_2) for kernels spanned by single-column elements when C o C is independent of C modulo C
    (hypothesis (G)); (G) fails for the known defect planes, so this is a constraint, not a proof of (NCOL_2).
 NOT PROVED: (NC'_e) (= (DC-COST)); (DI_4x4); (NCOL_1) for non-principal spaces and "K on <= 3 columns"; (NCOL_2), (NCOL_3)
    (for e >= 2 the Gram argument of V1 needs rank-one column data; only numerics and (FS-DEC)).
## RESULT, ROUND 4 (rows; final 19:13) -- (6,2), (7,3) and (D) NOT proved. Induction on e set up exactly; one new structural law
## (NCOL, numerical, 0 exceptions in 120 spaces) reduces (DI_5) to 4 x 5 spaces with a neutral column = "double towers" over 4 x 4.
 Details and proofs: section R4 (R4.1 - R4.15).  (d,e) space = 4 x 5 level space of dim d with defect space C of dim e; extremal: d = e + 3.
 U1 [RIGOROUS, R4.1] HYPERPLANE LEMMA: if no (e'+4, e') space exists for e' < e, then in an (e+4, e) space every subspace K has
    e(K) >= min(e, dim K - 3); every hyperplane is an EXTREMAL (e+3, e) space with the SAME defect space C.
 U2 [RIGOROUS, R4.2/R4.3] single-row parts U_i: U_i in C, U_i perp U_k, cubic condition, u_i + u_k <= e + 1; LEMMA RS-HYP: the generic
    hyperplane of a minimal (e+4, e) space is NOT fully row-split (sum_i U_i != C), e = 1, 2, 3 (e = 3 uses the checked L067).
 U3 [RIGOROUS, R4.7] LIFTING LEMMA: a finite union of "polynomial identities hold on the subspace" properties that fails for L fails
    for all subspaces through a suitable t in L.  D-UP: (D)_d => (D)_d+1; so (D) <=> (D)_7 and "(D) for dim >= 8" FOLLOWS from the
    7-dim statement.  C-UP: under the induction hypothesis, any property of C common to all extremal (e+3,e) spaces holds for every
    (e+4,e) space.   [(D)_8 itself: not proved; with (DI_5) it is equivalent to "no 8-dim level space" (R4.11).]
 U4 [RIGOROUS, R4.10] transposed defect construction: if column n of L' is neutral (C in e_n^perp), then L' = {(q | x)} over the level
    4 x 4 space Q = L' minus column n, C_j(Y) = (1+x).M^(j)(q), and dim L' <= dim Q + 3 - e^col(Q); PADDING LEMMA: a 4 x 4 level space
    with e^col = 0 or e^row = 0 has dim <= 3; so "a 4 x 5 level space with a neutral column has dim <= 6" (which contains (7,3) in
    the neutral case) follows from: no 4 x 4 level space with (dim, e^col) = (5,1), (6,2).
 U5 [NUMERICAL, R4.4] answer to the question "are extremal spaces all split over rows?": NO. Of 68 extremal spaces, 53 are fully
    row-split, 15 are not ((4,1): 2 with C = C(e_a - e_b); (5,2): 3 with C = V_S, |S| = 3; (6,3): 10 with C = V_S, |S| = 4).
    What holds in all 68: (LAW) C = sum_i U_i + span{two-column vectors of C}.
 U6 [NUMERICAL, R4.8 -- the main finding] (NCOL): EVERY extremal space has a NEUTRAL COLUMN (C lies in a coordinate hyperplane e_n^perp;
    L' minus column n is a level 4 x 4 space).  87/87 of my extremal spaces; 33/33 seven-dim 5 x 5 level spaces of other agents
    (after deleting their deletable line the rest has a neutral line of the other kind).  Direct calibrated test at e = 3 (R4.13):
    defect space fixed = e_0^perp cap 1^perp: (6,3) found 4/19; defect space fixed generic: 0/46.  In 5 x 5 terms: every known
    7-dim level space with deletable row r contains e_r(1 - 5e_n)^T, and is a DOUBLE TOWER
          L = Q (+) [column n: 3 - e^col(Q) dims] (+) [row r: 4 - e^row(Q) dims],   dim Q = e^row(Q) + e^col(Q)   (R4.10, numerical),
    so 7 comes out identically; no extremal space has a deletable ROW.
 U7 [RIGOROUS reduction, R4.8/R4.12] by C-UP:   (DI_5)  <=  (NCOL_e) and (NC'_e), e = 1, 2, 3,
    (NC'_e) := "a 4 x 5 level space with a neutral column and defect dimension e has dim <= e + 3".  This replaces (LAW) + the list of
    mixed/degenerate patterns of R4.6 by one statement about C and moves the rest to the 4 x 4 world.
 U8 [NUMERICAL, calibrated, R4.9] neutral columns: k = 2: dim 5 12/25, dim 6 0/22;  k = 1: dim 6 7/29, dim 7 0/25;  k = 1, e <= 1:
    dim 4 5/11, dim 5 0/8;  k = 1, e <= 2: dim 5 3/5, dim 6 0/15.  (6,2) seeded at the three column-type (5,2) spaces: 0/17.
 U9 [RIGOROUS, R4.14] THEOREM NCOL-S = (NCOL_1) in the split non-isotropic case: a 4 x 5 level space with defect line C m, <m,m> != 0,
    containing e_i m^T, has dim <= 3 if m has no zero entry. So every split (4,1) space with non-isotropic m has a neutral column
    (proof: first-order eigenvector condition D_i(Y)m = mu m forces equal column sums, then a zero row, then Lemma SL_3).
    Every step confirmed on the 27 split (4,1) examples.  Same computation, any e (R4.15): (F1) c^(i)(Y).u = 0 and c^(i)(Y) o u in C
    for u in U_i, Y in L'; (F2) U_i o U_k inside C (i != k); (FS-DEC) an extremal space in which one row carries a nondegenerate C
    has DECOMPOSABLE C (e = 3: C = V_A + V_B with block sizes (4,1) = neutral column, or (3,2)).
    (F1^T) for a neutral column n: x^T q in C and x.rho(q) = 0 for single-column elements x in X_n and all (q|x') in L'.
 NEGATIVES: (i) "column-centred 4 x 5 level spaces have dim <= 3" is false (dim 4 exists), although the column-sum map is linear with
    image in C; (ii) "dim L <= e_row(L) + e_col(L)" (true with equality for the 7-dim spaces) is false for the level line
    C circ(1,i,-i,-1) padded (all ten deletions level); (iii) EQ-induction step (round 3).
 OPEN (exact): (NCOL_e) and (NC'_e) for e = 1, 2, 3 [known: (NCOL_1) for split non-isotropic m = U9; (NC'_1) for two-column m = TC5;
    one row carrying a nondegenerate C = FS];
    equivalently for the gap: (D)_7 (or (D)_8) + these.  (6,2), (7,3), (5,1) remain unproved.
## RESULT, ROUND 3 (rows; final 18:20) -- upper floors NOT closed; two new rigorous theorems that cut down the split cases
 Details and proofs: section R3 (R3.0 - R3.9).  (DI_5) remains open; the gap (with (D)) needs only "no (5,1) and no (6,2)".
 T1 [RIGOROUS, hand proof, R3.8] LEMMA SL_3: a 3 x 5 space all of whose 3 x 4 column deletions are level has dim <= 2
    (= (DI_4) at e = 0; sharp). Corollary: a 4 x 5 level space containing a full free row has dim <= 6.
 T2 [RIGOROUS, R3.9] THEOREM FL2*: let U be a subspace of 1^perp with U cap U' = 0, U' = (U + C1)^perp. Every 5 x 5 level space
    containing the split pair T_U = e_i (x) U (+) e_r (x) U' has  dim <= 10 - dim(U o U')  (U o U' = span of entrywise products).
    So dim <= 7 as soon as dim(U o U') >= 3. Consequences for the defect table:
      (a) NO (5,1) or (6,1) space contains e_i m^T with m non-isotropic and at most one zero entry   [split case of e = 1];
      (b) no (6,2) / (7,2) space has a row carrying its whole defect plane C when C is nondegenerate and dim(C o W) >= 3;
          no (7,3) space has a row carrying its whole defect space when w (W = Cw) is non-isotropic with <= 1 zero entry.
    Open split cases at e = 1: m isotropic; m supported on exactly three columns (bound 8 only). (Two-column m: verifyfl's TC5.)
    Sanity (numerical): fixed m = (1,2,-4,1,0): dim 7 found, dim 8 not; fixed full-support m: dim 6 found, dim 7 not; fixed
    generic 2-dim U: dim 6 reached (slowly), dim 7 not; unknown U of dim 2: dim 7 found (U in a coordinate hyperplane), dim 8 not.
 T3 [RIGOROUS, short] from the checked "4 x 5 level <= 7" (L_gct_215) via the defect construction (R3.1): every 3 x 5 level space has
    dim <= e + 3; every 5 x 5 level space meets {row r = 0} in dim <= 7, so a 9-dim level space has all row/column projections
    of rank >= 2 and (8,3), (8,4), (9,4) are excluded.  Lemma EC (R3.2): an equal-column level space M extends by e_i(e_a-e_b)^T
    with defect C(M) + C(e_a-e_b).  Tower Lemma (R3.3): after an untwisted deletable row, the next free part lies in the radical
    of the previous defect space.  Saturation principle for any row (R3.5).  Split-pair normal form FL2 (R3.6).
 T4 [what L_gct_215 contains, R3.0] a contradiction proof for dim 8 by the single-row parts u_i and pair ranks; no classification
    of 7-dim spaces; internal lemma: a 4 x 5 level space with two equal columns has dim <= 6.
 NUMERICAL ONLY: no 7-dim 4 x 5 level space found (calibrated; so (7,3), (7,2) are probably vacuous, but "<= 6" is unproved);
    (6,2): 0/37; EQ-induction census: the step "dim(L'/{y_a = y_b}) <= 1 for a suitable pair" FAILS on all four (6,3) examples
    (min 2, once 3) and on one (5,2) example, so target (2) as posed does not work; only the trade-off = (DI_5) itself holds.
 NOT DONE: (7,3), (6,2) in general; conjecture (D) for dim >= 8 (no progress beyond the saturation principle).
## RESULT, ROUND 2 (rows; task "prove (DI)"; written 15:30, final 15:36) -- (DI) PROVED for p = 3; for p = 4, 5 only on the orthogonal part
 (DI_p): for a (p-1) x q level space L', dim L' <= dim C(L') + p - 2.  (p = 5, q = 5 is what the gap needs, with (D).)
 R6 [RIGOROUS; section DI] THEOREM DI_3: every 2 x q level space L' has dim L' <= dim C(L') + 1; hence a 3 x q level space with a
    deletable row has dim <= q (sharp; the checked L156 gives q + 1). Proof: on the hyperplane of zero row sums the level
    conditions and the defect are DIAGONAL (columnwise elementary symmetric functions), then Rado (checked L171 / L157).
 R7 [RIGOROUS; new tools, any number of rows]
    LEMMA D: a linear space V of p x q matrices with sum_j prod_i (1 + x_ij) = q on V has dim <= q - 1 (Rado induction of the
       checked ThreeRowRado file, verbatim for p rows).  COROLLARY: in ANY 5 x 5 level space, a linear subspace all of whose
       elements have zero row sums and pairwise orthogonal rows has dim <= 4 (same for columns).
    THEOREM DDI: if sum_j e_i(col_j(Y)) = 0 on a linear space M of k x q matrices (i = 1..k) then
       dim M <= dim span{ (e_i(col_j Y))_j : Y in M, i <= k }.
    DELETION FORMULA (I1): C(Y)_j = sum_{S} (-1)^{|S|}|S|! N^{(R-S)}(J+Y) prod_{i in S}(1 + Y_ij); exact p_k formulas (I3).
    PROPOSITION O: for a 3- or 4-row level space L' and a linear M in L' with zero row sums and pairwise orthogonal rows (4 rows:
       also zero triple sums), dim M <= dim C(L'); so dim L' <= dim C(L') + codim M.
    All identities checked exactly in rational arithmetic (rows/di_ident.py).
 R8 [numerical census of the 29 example spaces, rows/orth_chk.py] 26 of 29 have row-sum rank q_s = 3 and L'_s := L' cap {row
    sums 0} of dimension exactly e with pairwise orthogonal rows and zero triple sums: for these Proposition O PROVES
    dim L' <= e + 3 (tight). The 3 others have non-orthogonal L'_s: (d,e,q_s,dim L'_s) = (4,1,2,2), (5,2,2,3), (6,3,3,3).
    Uniform form of the conjecture:  (DI_5')  dim L'_s <= e + 3 - q_s.
 R9 [RIGOROUS corollaries, section DI] (H) in a 3- or 4-row level space L' with e = dim C(L'): every single-row part has dim <= e and
    every TWO-ROW part has dim <= e + 1 (checked on 69 example spaces, 0 violations); so dim L' <= e + 1 + rank(projection of L' to
    the other rows), and in a (5,1) or (6,1) space every two-row part of L' has dim <= 2.
    (B') Gram identity |b_j(Y)|^2 = |s|^2 + 3 c_j^2 - 4 p_2(Y)_j on level 4 x 5 spaces (zeros' isometries B_j for every e).
    (TC) if C(L') is inside C(e_a - e_b): L'' := {Y in L' : y_a = y_b} is strongly level (dim <= 3 by SL) and
    dim L' <= 3 + (4 - dim zeta), zeta = {z : z(e_a - e_b)^T in L'} (e_2-isotropic).  [Does not yet exclude (5,1) for this m.]
 NOT PROVED: (DI_4), (DI_5) in general; (DI_5) for e = 1 (no (5,1)). Reason, precisely: for p = 5, e = 0 the statement IS
    Lemma SL, whose non-orthogonal DC parts (types I, II) need the cubic/quartic case analysis; the Rado/diagonal method
    cannot see the pairing terms (y_a.y_b)(y_c.y_d) of P_4. Exact set-up of the e = 1 case and of the split-free-row sub-case:
    section DI, "WHAT IS NOT PROVED".
## RESULT, ROUND 1 (rows; final 15:07) -- gap NOT settled (no proof of <= 8, no 8- or 9-dim level space). What is new:
 R1 [RIGOROUS, 3-line proof, section D] DEFECT CONSTRUCTION = the exact normal form of "deletable row" (repr's conjecture (D)).
    For a 4x5 matrix Y put p_k(Y)_j := P_k(Y minus column j) (k = 1..4, j = 1..5); for a 4x5 level space L' let
    C(L') := span{p_k(Y) : Y in L', k}  (inside 1^perp of C^5; e := dim C(L')).  Then
        L(L') := L' (+) e_r (x) (C(L') + C1)^perp       (L' placed in the rows != r)
    is a 5x5 LEVEL space of dimension dim L' + 4 - e with row r deletable; conversely a level L with deletable row r has a level
    4x5 projection L', dim L <= dim L' + 4 - e(L'), and L + e_r(x)(C(L')+C1)^perp is still level. e = 0 is zeros' free-row case.
    Hence:  (D) + (DI4): "dim L' - e(L') <= 4 for all 4x5 (and 5x4) level spaces"  ==>  the gap;  and an 8-dim level space with a
    deletable row exists  <=>  a 4x5 level space with (dim L', e) in {(5,1),(6,2),(7,3),(8,4)} exists (+ transposes).
 R2 [EXACT] explicit 7-dim level spaces WITHOUT a full free row or column, explained by R1 (free part of the deletable row 3-dim):
    (a) L_m = span{ e_2 m^T ; e_4 w^T (w.1 = w.m = 0) ; x e_2^T (x_0+x_1+x_3 = 0, x_2 = x_4 = 0) ; (1,1,-3,1,0)^T e_4^T },
        m = (m_0,m_1,m_2,m_3,0), sum m = 0: hand proof for all m (section D); integer polynomial identity perm(J+t) == 120
        checked for m = (1,2,-4,1,0), also with a shear c = 1 (rows/exact7.py). [L_m with c = 0 is of repr's product type,
        pattern (2,1 | 3,1) up to transpose: repr's files prod_*_{31000,22000,21100,11110} already contain free-line-free
        7-dim spaces numerically, so UPDATE 4's "every known 7-dim space contains a full free line" was not accurate.]
    (b) NOT of product type, DC part = ex1's plane, (r,d,r_A,r_B) = (5,2,2,3):  span{ u(e_0-e_3)^T, ubar e_1^T, ubar e_4^T
        (u = (1,w,w^2) on rows 0,1,3), (1,1,-3,1,0)^T e_2^T, e_4 w^T (w_0 = w_3, sum w = 0) }: exact identity in Z[w] (exact7b.py).
    Numerically (1e-13, two independent checkers, 27 spaces) 7-dim level spaces exist for (dim L', e) = (3,0), (4,1), (5,2), (6,3):
    free part of the deletable row of dim 4, 3, 2, 1. All 27 have exactly one deletable line and first-order extension space
    L + C(e_r 1^T - J/5) (dim 8), hence lie in no 8-dim level space. 14 of 15 (4,1) spaces contain the "split free row"
    e_i m^T (+) e_r(x){1,m}^perp with m = the defect line.
 R3 [numerical; seeded searches calibrated on the analogous existing transitions (5/12, 5/12, 1/9)] no 4x5 level space with
    (dim L', e) = (5,1), (6,2), (7,3) found (0/38, 0/29, 0/24; residual floors 4.1, 3.7, 2.4), none with (7,4) (0/12): no 8-dim
    level space with a deletable row found. Equal-row block classes mu = (4,1), (3,2), (3,1,1), (2,2,1): dim 8 not found
    (dim 7 is reached in (4,1), (3,1,1), (2,2,1)).
    UNIFORM LAW seen on three floors (q = 5): for (p-1) x 5 level L', dim L' - e(L') <= p - 2 with equality for every e
    (p = 3: (1,0),(2,1),(3,2),(4,3) exist, (2,0),(3,1),(4,2) do not; p = 4: (2,0),...,(5,3) exist, (3,0),...,(6,3) do not;
    p = 5: (3,0),...,(6,3) exist; (4,0) impossible by zeros' SL).  CONJECTURE (DI): dim L' - dim C(L') <= p - 2.
 R4 [RIGOROUS] Target (A) of my task is FALSE as stated: 5-dim degenerate level 4x5 spaces exist: (i) F_3 (+) C(e_1-e_2)e_j^T
    (three rows, contains a full free row), (ii) a 5-dim 4x4 level space (2n-3 type: free column + 2) padded with a zero column.
    Correct statement of the a_r = 1 branch: normal form (*) in section S; a_r = 1 does not imply deletable (L080, row 4).
    Side remark: the team's sol_n4_d5 is (to its 1e-4 subspace accuracy) free column 0 (+) 2-dim, column 0 deletable (error
    7e-6 against 0.8..1 for the other lines) -- it is NOT free-line-free (zeros' remark was a tolerance artefact).
 R5 [RIGOROUS] GENERALISED FK: perm restricted to L + CJ is 120 lambda^5, so every LINEAR subspace Y of {perm = 0} of codimension c
    meets a d-dim level space in dimension >= d + 1 - c; new instances Y = {row i in C(a e_j + b e_k), row i' in C(a e_j - b e_k)}.
 OPEN (precise): (DI) [already (DI4) suffices with (D)]; (D); in the branch a_r = 1 of a 9-dim L the three types of section S.
 BEST NEXT STEP: prove (DI) for p = 3 (2 x q; formulas in section D': C = span{a+b, A(a-b) + 2 a o b}) and then by induction along
    the tower (C(L') contains the free parts of all rows of L'; C'(Y2,v) = D(Y2)(1+v) for Y2 = the rows above); or classify the
    (4,1) spaces: with a split free row e_i m^T the condition is "m is an eigenvector of D(Y3) for all Y3 in the 3-row projection".
STATUS 14:25: read BRIEF + zeros/kbuild/lemmaz/hessmix/lowd. First observation (to be verified exactly): target (A) as
 literally stated ("degenerate level 4x5 space has dim <= 4") is FALSE: (i) F_3 (+) C(e_1-e_2)e_j^T (3x5, free row) and
 (ii) a 5-dim 4x4 level space (sol_n4_d5) padded with a zero column are 5-dim degenerate level 4x5 spaces. So (A) must be a
 classification into types, each killed separately inside a 9-dim L.
STATUS 14:41: (1) EXACT general construction ("defect construction", proof 3 lines, see section D below): for ANY 4x5 level space
 L' (rows != r), with p_k(Y)_j := P_k(Y minus column j) and defect space C(L') := span{p_k(Y): Y in L', k=1..4} (inside 1^perp),
     L(L') := L' (+) e_r (x) (C(L') + C1)^perp   is a 5x5 level space of dim  dim L' + 4 - dim C(L'),   row r deletable;
 and every level L with deletable row r is contained in L(L') for L' = its 4x5 projection (rho-part must be orthogonal to
 the p_k). Strongly level = defect 0 = zeros' free-row case. (2) NUMERICAL, verified with two independent checkers (level
 error 1e-13): 4-dim L' with 1-dim defect EXIST (10/25 random LM starts) and 5-dim L' with 2-dim defect exist (3/21): they give
 NEW 7-dim level spaces WITHOUT any full free row or column (free parts: row r 3-dim resp. 2-dim, all other lines <= 2).
 So "every 7-dim level space contains a full free line" is false, and Theorem FL does not cover all deletable-line spaces.
 Files rows/clm_p4_d4_defect1_s*.npy, clm_p4_d5_defect2_s*.npy (4x5 bases), rows/build7.py (builds + checks the 5x5 space).
 (3) (d,e) = (5,1) [would be an 8-dim level space]: 0/17 random starts -- NOT evidence (same LM misses the known 6-dim 4x5
 level spaces, (6,4): 0/4). Next: seeded searches with calibration, exact form of a (4,1) example.
STATUS 14:52: RESULT block written (R1-R5). Now: sections D (proofs), S (a_r = 1 normal form), then (DI) attempts.

## Section D. Deletable row: defect construction (rigorous)
 Notation: rows of a 5x5 matrix z as linear forms l_i = sum_j z_ij y_j in A = C[y_1..y_5]/(y_j^2), sigma = sum y_j, 'int' = top
 coefficient; perm(J+z) = int prod_i (sigma + l_i). For z = (z'; v) (z' = rows != r as a 4x5 matrix, v = row r):
        perm(J + z) = (1 + v) . C(z'),     C_j(z') := perm((J' + z') minus column j)  = 24 + sum_{k=1..4} (4-k)! p_k(z')_j .   (D1)
 sum_j p_k(z')_j = (5-k) P_k(z') (each k x k subpermanent avoids 5-k columns). Hence z' is 4x5-level <=> 1.C(z') = 120 <=> all
 p_k(z') lie in 1^perp;  and 'row r deletable in L' <=> the 4x5 projection L' of L is level <=> v.C(z') = 0 on L.
 PROPOSITION D. (a) L' a 4x5 level space, W := (C(L') + C1)^perp. Then L(L') = L' (+) e_r(x)W is level: for w in W,
   (1+w).C(z') = 1.C(z') + w.(C(z') - 24*1) + 24 w.1 = 120 + 0 + 0.   dim = dim L' + 4 - e.
 (b) L level, row r deletable, L' its projection, W_L := {w : e_r w^T in L}. For z in L and w in W_L: w.C(z') = 0 (compare z
   and z + e_r w^T in (D1)), so W_L is inside W = (C(L') + C1)^perp [w.1 = 0 from the linear part of v.C = 0] and
   dim L = dim L' + dim W_L <= dim L' + 4 - e.  Moreover L + e_r(x)W is again level (same computation), so maximal level
   spaces with deletable row r are exactly the graphs {(z', rho(z') + w)}: rho : L' -> 1^perp/W linear with rho(z').p_k(z') = 0.
   If e = 1 and L' is not strongly level then rho = 0 (rho(z').m * theta_k(z') = 0 with p_k = theta_k m, a product of two
   polynomials), i.e. L = L(L').
 (c) Equivalent 'two-form' statement: row r deletable <=> perm restricted to L + CJ + C e_r 1^T equals 120 mu lambda^4
   (lambda, mu the coordinates along [J'; 0] and e_r 1^T). Then {mu = 0} = (L' + CJ') (+) e_r(x)W_L is a linear space inside
   the permanent hypersurface of dimension dim L + 1.
 CONSEQUENCE. Under (D), max level dim = max over 4x5 (and 5x4) level L' of dim L' + 4 - e(L').  Dimension 8 needs
   (dim L', e) in {(5,1), (6,2), (7,3), (8,4)}, dimension 9 needs (6,1), (7,2), (8,3), (9,4); (d,0) with d >= 4 is excluded by
   zeros' Lemma SL. Degree-1 part: p_1(Y) = -(column sums of Y), so e >= rank of the column-sum map on L'.
   Degree 2: p_2(Y)_j = c_j^2 + s.y_j - |y_j|^2 (c = column sums, s = row sums, y_j = column j).
 PROOF THAT L_m IS LEVEL (R2). Y = a e_2 m^T + x e_2^T + t u e_4^T (u = (1,1,-3,1), rows 0..3): rows 0,1,3 are
   sigma + t y_4 + x_i y_2, row 2 is sigma + a mu - 3t y_4 (mu = sum m_j y_j). Since y_2^2 = 0 and sum x_i = 0,
   prod_{i=0,1,3}(sigma + t y_4 + x_i y_2) = (sigma + t y_4)^3 = sigma^3 + 3t sigma^2 y_4, and
   G = (sigma^3 + 3t sigma^2 y_4)(sigma + a mu - 3t y_4) = sigma^4 + a mu sigma^3 + 3 a t sigma^2 mu y_4.
   Coefficient of y_{[5]-j}: 24 - 6a m_j - 6at(m_j + m_4) [j != 4], 24 - 6a m_4 [j = 4]. With m_4 = 0: C(Y) - 24*1 = -6a(1+t) m.
   So L' is level with defect line Cm, and Prop. D(a) gives L_m (W = {1,m}^perp).   (x drops out: a block of rows that are
   equal except for a sum-zero vector in ONE column behaves like equal rows.)
 EQUAL-ROW PRINCIPLE (rigorous, same computation): if the rows of a block R (|R| = mu) of J + t are kappa + x_i y_c with sum_R x_i
   = 0 then prod_R = (sigma + kappa)^mu. So any level space L_mu inside {matrices with equal rows in the blocks of a partition
   mu of the rows} extends by (5 - #blocks) dimensions (one column c per block, all sum-zero vectors on the block).
   L080 / ex-types are mu = (4,1) and (3,1,1); L_m is mu = (3,1,1) with (kappa, a, b) = (t y_4, a mu - 3t y_4, w).
 Numerics for this section: rows/clm.py (holomorphic LM on a Grassmannian chart, analytic Jacobian, 1 s per start),
   run_clm.py, seeded.py, mult.py, build7.py, deletable.py, look.py, fam8.py; logs clm_*.log; solutions *.npy.
   CALIBRATION WARNING: unseeded LM does not find the known 6-dim 4x5 level spaces ((6,4): 0/4) nor converges fast on singular
   solutions; only the seeded negatives in R3 are calibrated (by the analogous successful transitions).
STATUS 14:56: more data. (a) 14 of the 15 (4,1) spaces found contain the split free row  e_i m^T (+) e_r(x){1,m}^perp  (the single-row
 element of L' is EXACTLY e_i m^T, m = the defect line; m always has a zero entry). (b) The 15th is of a second kind, exact form
 read off:  u(e_0-e_3)^T, ubar e_1^T, ubar e_4^T (u = (1,w,w^2) on rows 0,1,3), (1,1,-3,1,0)^T e_2^T, e_4 w^T (w_0 = w_3, sum w = 0);
 m = e_0 - e_3, (r,d,r_A,r_B) = (5,2,2,3), DC part = ex1's plane; no single-row element outside row 4. (c) L_m has first-order
 space of dim 8 (singular values 1.2 | 3e-14) for m = (1,2,-4,1,0), (1,i,-1,-i,0), (1,-1,0,0,0): no 8-dim level space contains
 L_m. (d) seeded 8-dim searches, second batch: (5,1) 0/23, (6,2) 0/15 (floors 4.1, 3.7). Totals: (5,1) 0/38, (6,2) 0/29.

## Section S. The branch a_r = 1 (row projection of dimension 4): normal form, what is true, what is open
 Setting: L level of dim l, row r, Ann_r = C n (sum n = 1), H = n^perp = pi_r(L), M = L_r (dim l - 4), M' its 4x5 part.
 Choose a linear section; then L + CJ = {(x' + Lam(v), v) : x' in M', v in C^5}, Lam : C^5 -> C^{4x5} linear, Lam(1) = J', and
        (*)   v . Phi(x' + Lam(v)) = 120 (n.v)^5      for all x' in M', v in C^5        (Phi = the five maximal-minor permanents),
 and conversely (*) defines a level space. [perm(lambda J + z) = 120 lambda^5 on L + CJ, lambda = n.v.]  By degree in v:
   deg 1: Phi(x') = 0 (zeros' CA2);  deg 2: S_x := DPhi(x') o Lam is a SKEW 5x5 matrix (cubic in x'), i.e. for every z in L + CJ:
          sum_{k != r} B_k(x') z_k = S_x z_r,  B_k = symmetric zero-diagonal matrix of 3x3 subpermanents of x' without row k
          (with z = J: (P_3(x' minus column j))_j = S_x 1);   deg 3, 4: v . D^2Phi(x')[Lam v, Lam v] = 0, v . D^3Phi(x')[(Lam v)^3] = 0;
   deg 5: the 5-dim space {(Lam v, v)} has perm = 120 (n.v)^5.
   Columnwise (v = t e_j): perm((x' + t Lam e_j) minus column j) = 120 n_j^5 t^4: each column-deleted image of M' is a 4x4
   space on which perm is constant on a translate (base point (Lam e_j)^(j)); useful only with extra information, because
   general base points allow big spaces (I + strictly upper triangular: 6-dim, perm == 1).
 a_r = 1 does NOT imply 'row r deletable': L080 has a_4 = 1 with n = (1,1,1,1,0)/4 and M = {u e_4^T : u_4 = 0, sum u = 0}.
 TYPES of M for a hypothetical 9-dim L (dim M = 5; a linear space inside the variety Z of 4x5 matrices with vanishing
 maximal minors lies in one irreducible component of Z; component list as quoted in NOTES-lemmaz from arXiv 2402.17839 --
 NOT re-proved here):
   (i) common zero row r': M is a 5-dim 3x5 level space and row r' is a linear function of row r on all of L. Example of such
       M: F_3 (+) C(e_1-e_2)e_j^T (then FL gives dim L <= 7). OPEN: other 5-dim 3x5 level spaces. My LM converges slowly
       (singular solutions, residual 1e-8) to spaces that do NOT contain a full free row (free parts of dims 2,1 / 1,1 and one
       single-column element) -- unresolved whether these limits are genuine (rows/long35.log, long35_s*.npy).
   (ii) common zero column c: M is a 5-dim 4x4 level space in the corner. The team's sol_n4_d5 (accurate only to 1e-4 as a
       subspace: singular solution) has row-projection ranks (1,2,2,1) and column ranks (3,2,2,2).  OPEN.
   (iii) no common zero line (inside the 3-row cone or the Kirkup component). lemmaz's K_new is a 2-dim example. OPEN.
   So the chain (A) => (B) of my task does not go through as stated; each of (i)-(iii) needs its own argument inside (*).
 GENERALISED FK (R5), proof: on L^ = L + CJ, perm = 120 lambda^5; a linear Y inside {perm = 0} of codimension c meets L^ in
   dimension >= l + 1 - c, and there lambda = 0. New instance: for rows i != i', columns j != k and (a:b) in P^1,
   Y = {row i in C(a e_j + b e_k), row i' in C(a e_j - b e_k)} (the two rows multiply to 0 in A; codim 8) meets a 9-dim level L in
   dim >= 2. With T := image of {z in L : rows i,i' supported on columns j,k} in C^{2x2} and L_{ii'} := L cap {rows i,i' = 0}:
   if dim L_{ii'} <= 1 then P(T) meets every line of one ruling of the quadric {perm_2 = 0} in P^3, so dim T >= 3 or T is a
   plane of the other ruling {(l, c D l)}; if L_{ii'} = 0 then T = C^{2x2}.  (Not exploited further.)
 (B)/(C) of the task, in the light of section D: if a 9- or 8-dim level space has a deletable row r then a_r = 1 + e >= 2
   (e = 0 is Theorem FL), L_r = L' and the minor-permanent map Phi : L' -> C(L') = Ann_r cap 1^perp is exactly p_4; the whole
   deletion vector C(z') - 24*1, not only its top part, stays in the fixed e-dim space. An 8-dim level space with a deletable
   row is EXACTLY one of: (5,1): L = L' (+) e_r(x){1,m}^perp, L' a 5-dim 4x5 level space with all p_k(Y) in Cm;  (6,2): L' 6-dim,
   defect plane, rho-twist allowed;  (7,3), (8,4).  Targeted searches for (5,1), (6,2): negative (R3).
STATUS 15:02: (a) (7,3) seeded from the four (6,3) spaces: 0/24 (floor 2.4). (b) MAXIMALITY CHECK (rows/maxchk.py): all 27 new spaces
 ((4,1): 15, (5,2): 8, (6,3): 4) are 7-dim, level (1e-13), with first-order extension space of dim exactly 8 and the extra
 direction = e_r 1^T - J/5 (cos = 1 to 1e-6; P_2 != 0): NO 8-dim level space contains any of them. Since L(L'_d) is inside
 L(L'_{d+1}) whenever both have the same defect space, none of the found (4,1) spaces lies in a (5,1) space, etc.
 (c) THE SAME DEFECT LAW ONE AND TWO FLOORS DOWN (rows/small_di.py, unseeded LM, small problems, 1 s per start):
     L' 2x5 -> 3x5:  (d,e) = (1,0),(2,1),(3,2),(4,3) all exist (16/16, 12/16, 13/16, 4/4)  [3x5 level of dim 5];
                     (2,0),(3,1),(4,2) [dim 6]: 0/15, 0/11, 0/6 (floors 10, 6.4, 4.9).
     L' 3x5 -> 4x5:  (2,0),(3,1),(4,2),(5,3) exist (12/16, 6/14, 4/10, 3/12)  [4x5 level of dim 6];
                     (3,0),(4,1),(5,2),(6,3) [dim 7]: 0/11, 0/7, 0/5, 0/8 (floors 7.8, 5.8, 4.6, 3.5).
     L' 4x5 -> 5x5:  (3,0),(4,1),(5,2),(6,3) exist [dim 7];  (4,0) impossible (zeros' SL, rigorous); (5,1),(6,2),(7,3): not found.
   CONJECTURE (DI_p), uniform: for a (p-1) x q level space L' (p <= q), with defect space C(L') in 1^perp of C^q spanned by the
   deletion vectors (P_k(Y minus column j))_j, k = 1..p-1:      dim L' - dim C(L') <= p - 2,
   with equality for every value of dim C(L') from 0 to q-2 (numerically, q = 5). Together with 'deletable line' at each
   floor this is exactly the p + q - 3 law; p = 2 is trivial (L' = U in 1^perp, C(U) = U), p = 5, e = 0 is zeros' Lemma SL.
   Easy exact facts: C(L') contains the free part W_i of every row i of L' (take Y = e_i w^T: p_1 = -w), and
   C'(Y'', v) = D(Y'')(1 + v), D(Y'')_{jk} = perm((J'' + Y'') minus columns j,k) (symmetric, zero diagonal), D(0) = 6(J - I) for
   3 rows; so perm(J + z) = (1 + z_r)^T D(z'') (1 + z_i) for any two rows i, r. If L' contains e_i m^T and C(L') = Cm then m is
   an EIGENVECTOR of D(Y''') for every Y''' in the projection of L' to the other three rows (L_m: D = 6(J-I) + 6t(J-I)_{0123}).
STATUS 15:06: RESULT block rewritten (R1-R5 final wording; relation to repr's product type; sol_n4_d5 remark; exact check of the
 second-kind example in Z[w]).
## Section D'. Formulas for the bottom floor (2 x q -> 3 x q), for whoever proves (DI) at p = 3
 L' in C^q x C^q, elements (a,b), A = sum a = -sum b, level <=> a.b = -A^2. Deletion vectors: p_1 = -(a+b),
 p_2 = A(a-b) + 2 a o b (o = entrywise product). In c = a+b, delta = a-b, D = sum delta: level <=> c.c - delta.delta + D^2 = 0,
 2 p_2 = D delta - delta o delta + c o c, polar form ((D delta' + D' delta)/2 - delta o delta' + c o c')/2.
 On L'_0 = {c = 0} = Delta_0: psi(delta_0, delta) = T_0 delta, T_0 = diag(D_0/2 - delta_0) + (1/2) delta_0 1^T, whose kernel is
 at most 1-dim when no entry of delta_0 equals D_0/2; so dim psi(delta_0, Delta_0) >= dim Delta_0 - 1 there. Missing for a
 proof of d <= e + 1: independence of this image from c(L') (and the degenerate entries). Strongly level (e = 0): d <= 1 (a_j
 in {0, A} for all j forces a = A e_j), i.e. L' = C (e_1 - e_2) e_j^T, giving F_3 (+) E_j.
 Hand check of (3,1) with b = 1, dim Delta_0 = 2: impossible (delta_1 o delta_1, delta_1 o (1/2 - delta_2), delta_2 o (1 - delta_2)
 all parallel to m force delta_1 = +-s on its support with sum 0 and delta_1.delta_1 = 0, so s = 0).
STATUS 15:09: final additions.
 (1) Relation between my assigned program (row projections, CA2) and deletability, exact: for ANY row r of a level L,
     dim L = dim L_r + 5 - a_r, so the gap is equivalent to "dim L_r <= a_r + 3 for one (hence every) row r". CA controls only the
     TOP degree part p_4 = Phi of the deletion vector on L_r (Phi(L_r) inside Ann_r cap 1^perp, dim a_r - 1); the pure 4x5
     statement "dim M <= dim span Phi(M) + 4 for 4x5 level M" is FALSE (F_3 (+) E_j: Phi == 0, dim 5). Deletability of row r is
     exactly the extra information that ALL p_k (k = 1..4) of L_r lie in Ann_r cap 1^perp; then the conjectural (DI) applies.
 (2) Closed-form (5,2) example: L' = the 5-dim 4x4 level space of 2n-3 type {e_3(e_a - e_2)^T (a=0,1), (e_b - e_3)e_3^T (b=0,1,2)}
     padded with a zero column 4 is a 5-dim degenerate level 4x5 space with 2-dim defect space (checked 1e-16), so
     L(L') is a 7-dim level 5x5 space whose deletable row has a 2-dim free part.
 (3) (5,2) solution clm_p4_d5_defect2_s2: C(L') = sum-zero vectors on columns {0,2,4}; rows 1 and 2 carry single-row elements
     m_1, m_2 in C(L') (mutually orthogonal), row r carries {w : w_0 = w_2 = w_4, sum w = 0}, and a 3-dim part lives in columns 1,3:
     a free row split over three rows.
 Files (all in rows/): lib.py, rect.py (scipy LM; slow, superseded), clm.py (solver), run_clm.py, seeded.py, mult.py, small_di.py,
   build7.py, deletable.py, maxchk.py, chk41.py, look.py, fam8.py, exact7.py, exact7b.py, ex_rows.py, calib1.py, long35.py; logs
   clm_*.log, long35.log; solutions clm_p4_d*_defect*_s*.npy, seed_d*_e*_t*.npy, di_p*_d*_e*_s*.npy, mult_*.npy.
STATUS 15:26 (round 2, new task "prove (DI)", budget to ~16:40): (DI) for p = 3 PROVED (via the checked L157 / Rado L171);
 new rigorous tools: deletion formula (I1), diagonal lemma D for ANY number of rows, diagonal defect inequality DDI; (DI) for
 p = 4, 5 proved only for the "orthogonally centred" part of L'; the remaining part is exactly where zeros' case analysis of
 Lemma SL lives (e = 0), so no short proof of (DI4) can avoid it. Details in section DI below.

## Section DI. The defect inequality: what is proved (round 2)
 Notation (any q >= 2): a k x q matrix Y has rows y_1..y_k in C^q and columns col_j(Y) in C^k; X = J + Y.
   N^{(R)}(X) := sum over injections f : R -> [q] of prod_{i in R} X_{i f(i)}  (R a set of rows; N^{(empty)} = 1);
   Y (or a linear space of such Y) is LEVEL if N^{(all rows)}(J + cY) is constant in c, i.e. P_1(Y) = ... = P_k(Y) = 0;
   deletion vector C(Y)_j := N^{(all rows)}((J+Y) minus column j) = (q-1)_k + sum_{i=1..k} (q-1-i)_{k-i} p_i(Y)_j,
   p_i(Y)_j = P_i(Y minus column j);  C(L') := span{p_i(Y) : Y in L', 1 <= i <= k}  (inside 1^perp when L' is level);
   beta_B(Y) := sum_j prod_{i in B} Y_ij (block sums; beta_{i} = row sum, beta_{ii'} = y_i.y_i');
   e_i^col(Y) := (e_i(col_j(Y)))_j in C^q (columnwise elementary symmetric functions), sum_j e_i^col(Y)_j = sum_{|B|=i} beta_B(Y).
   (DI_p): for a (p-1) x q level space L',  dim L' <= dim C(L') + p - 2.      [p x q level space L(L') has dim <= p + q - 3]
 All identities below were checked EXACTLY in rational arithmetic at random points (rows/di_ident.py: (I1) for k = 2,3,4;
 (I2); (I3) including the four deletion vectors).

 (I1) DELETION FORMULA [rigorous]. For every k x q matrix X and column j:
        N^{(R)}(X minus column j) = sum_{S subset R} (-1)^{|S|} |S|! N^{(R-S)}(X) prod_{i in S} X_ij.
   Proof. N^{(R)} is linear in column j: N^{(R)}(X) = N_j^{(R)} + sum_{i in R} X_ij N_j^{(R-i)} (N_j = injections avoiding j; at
   most one row uses column j). Solve recursively: N_j^{(R)} = sum over sequences (i_1..i_r) of distinct rows of
   (-1)^r X_{i_1 j}...X_{i_r j} N^{(R - {i_1..i_r})}.  QED
   So C(Y) = sum_S (-1)^{|S|}|S|! N^{(R-S)}(J+Y) X_S (X_S = entrywise product of the rows 1 + y_i, i in S): the deletion vector
   lies in the Hadamard algebra generated by the rows, with coefficients the level polynomials of the row subsets.
 (I2) Moebius form [rigorous, standard]: P_i(Y) = sum_{|R|=i} sum over set partitions pi of R of prod_{B in pi} (-1)^{|B|-1}(|B|-1)! beta_B(Y).
   Hence if all row sums of Y vanish: P_2 = -sum_j e_2(col_j), P_3 = 2 sum_j e_3(col_j) (any k), and
   if moreover the rows are pairwise orthogonal (beta_{ii'} = 0) and k <= 5:  P_i(Y) = (-1)^{i-1}(i-1)! sum_j e_i(col_j(Y)), i >= 3
   (a set of <= 5 rows has no partition into blocks of size >= 3 except the trivial one).
 (I3) Deletion vectors [rigorous; beta_B(Y minus column j) = beta_B(Y) - prod_{i in B} Y_ij]:
   k = 2, row sums 0, level:           p_1 = -e_1^col,  p_2 = 2 e_2^col.
   k = 3, row sums 0, level:           p_1 = -e_1^col,  p_2 = 2 e_2^col,  p_3 = -6 e_3^col + kappa(Y),
                                        kappa(Y) := (y_2.y_3) y_1 + (y_1.y_3) y_2 + (y_1.y_2) y_3.
   k = 4, row sums 0, rows pairwise orthogonal, level:  p_i = (-1)^i i! e_i^col (i <= 3),
                                        p_4 = 24 e_4^col - 2 sum_i beta_{R-i}(Y) y_i     (beta_{R-i} = triple sums).

 LEMMA D (diagonal lemma, any number of rows) [rigorous; uses Rado's theorem = checked L171; the 3-row case is the core of
   the checked L157, file Gct/Helpers/ThreeRowRado.lean, whose induction I repeat verbatim for p rows].
   Let V be a linear space of p x q matrices (q >= 1) with  F(x) := sum_{j=1..q} prod_{i=1..p} (1 + x_ij) = q  for all x in V
   (equivalently sum_j e_i(col_j(x)) = 0 on V for i = 1..p). Then dim V <= q - 1.
   Proof. Strong induction on q. Suppose dim V >= q. For a column set U let S(U) be the span in V^* of the entry functionals
   g_ij (i in [p], j in U). (a) If dim S(U) >= |U| for all U: Rado gives i(j) with (g_{i(j),j})_j linearly independent, so some
   x in V has x_{i(j),j} = -1 for all j; every column product vanishes, F(x) = 0 != q. (b) Otherwise take U nonempty with
   dim S(U) < |U| and V_U := {x in V : columns in U vanish}; dim V_U = dim V - dim S(U) >= q - |U| + 1 and V_U, as matrices on
   the remaining q' = q - |U| columns, has F = q'. If q' = 0 then V_U = 0, contradiction; else induction gives dim V_U <= q' - 1,
   contradiction.  QED
 THEOREM DDI (diagonal defect inequality) [rigorous]. Let M be a linear space of k x q matrices with sum_j e_i(col_j(Y)) = 0
   for all Y in M, i = 1..k, and T(M) := span{e_i^col(Y) : Y in M, 1 <= i <= k}. Then  dim M <= dim T(M).
   Proof. T(M) is in 1^perp. Put W0 := (T(M) + C1)^perp (dim q - 1 - dim T(M)) and V := {(Y; w) : Y in M, w in W0} ((k+1) x q).
   e_i(col_j(Y;w)) = e_i(col_j Y) + w_j e_{i-1}(col_j Y), so sum_j e_i(col_j(Y;w)) = 0 + w.e_{i-1}^col(Y) = 0 for i = 1..k+1
   (e_0^col = 1, e_{k+1}(col_j Y) = 0). Lemma D: dim M + q - 1 - dim T(M) <= q - 1.  QED
   [Numerical sanity for k = 2 (rows/g1test.py): (dim M, dim T) = (1,1),(2,2),(3,3),(4,4) found 14/14 each; (2,1),(3,2),(4,3): 0/38.]

 THEOREM DI_3 [RIGOROUS]. Every 2 x q level space L' satisfies dim L' <= dim C(L') + 1. Consequently a 3 x q level space
   with a deletable row has dim <= q (sharp: F_3 (+) C(e_1-e_2)e_j^T; the checked L156 gives q + 1 without deletability).
   Proof. M := {Y in L' : row sum of row 1 = 0} has codimension <= 1 and both row sums vanish on it (P_1). On M,
   sum_j e_2(col_j) = y_1.y_2 = beta_1 beta_2 - P_2 = 0, so M satisfies the hypothesis of DDI (k = 2), and by (I3)
   T(M) = span{p_1(Y), p_2(Y) : Y in M} = C(M), a subspace of C(L'). DDI: dim M <= dim C(L').  QED
   Second proof (uses the checked L157 directly): M (+) e_3 (x) (C(L') + C1)^perp is a ROW-CENTRED 3 x q level space
   (P_2 = -(a.b + (a+b).w) = 0, P_3 = w.p_2(Y) = 0), so dim M + q - 1 - e <= q - 1.
   Checked on 101 numerically found 2 x 5 level spaces (rows/di_p2_*.npy, g1_*.npy): |row sums|, |P_2|, |P_3| of (a,b,w) <= 2.2e-10,
   dim M + dim W <= 4 and d <= e + 1 in all; formulas p_1, p_2 exact.

 PROPOSITION O ("orthogonally centred part") [rigorous]. Let L' be a k x q level space, k = 3 or 4, and M a LINEAR subspace of L'
   all of whose elements have zero row sums and pairwise orthogonal rows (for k = 4 also: all triple sums beta_T(Y) = 0, or
   merely sum_i beta_{R-i}(Y) y_i in C(L') + C1). Then dim M <= dim C(L'), hence  dim L' <= dim C(L') + codim(M in L').
   Proof. By (I2) M satisfies the hypothesis of DDI; by (I3) T(M) is inside C(L') (+ the stated correction).  QED
   So (DI_4) [resp. (DI_5)] holds for every L' that has such an M of codimension <= 2 [resp. <= 3]. The row-sum-zero part
   L'_s := L' cap {all row sums 0} always has codimension q_s <= p - 2, so (DI_p) is EQUIVALENT to
        (DI_p')   dim L'_s <= dim C(L') + (p - 2 - q_s),
   and Proposition O proves it when the pair products y_i.y_i' vanish on a subspace of L'_s of codimension <= p - 2 - q_s.
   For k = 3 the exact defect is  C(L'_s) = span{e_1^col, e_2^col, 6 e_3^col - kappa}  against  T(L'_s) = span{e_1^col, e_2^col, e_3^col}:
   DDI gives  dim L'_s <= dim(C(L') + span kappa(L'_s)),  kappa = A y_1 + B y_2 + C y_3 with A + B + C = 0 the pair products.

 WHAT IS NOT PROVED, AND WHY IT IS HARD (precise).
  (a) (DI_4) (3 x q -> 4 x q) and (DI_5) = (DI4)/(DI) for the gap are NOT proved in general. The missing statement is (DI_p')
      for the NON-orthogonal part of L'_s. For p = 5, e = 0 this is exactly zeros'/verifyfl's Lemma SL (there L'_s = N, the DC
      part, q_s = q, and (DI_5') reads q + dim N <= 3): the spaces N of types I, II (chi_1 (x) C^3, ex1's plane) have
      non-orthogonal rows, T^diag = 0 fails for them, and they are excluded/bounded only by the long cubic+quartic case
      analysis S4-S8 of NOTES-verifyfl. So any proof of (DI_5) contains a proof of SL; a short uniform argument of the
      Rado type cannot exist unless it also handles the pairing terms  sum over pairings (y_a.y_b)(y_c.y_d)  of P_4.
  (b) e = 1, p = 5 (no (5,1), i.e. no 8-dim level space with a deletable row whose free part is 3-dim): NOT proved. Exact
      set-up for whoever continues (all rigorous, derived as in verifyfl S2/S5 with one extra quadratic form):
      C(L') = Cm. tau(y_j) = kappa(Y) m_j (kappa a linear form); L'_0 := ker kappa (codim <= 1, columns in V_4). On L'_0:
        (C2') q_j(Y) := <y_j,y_j> - <s,y_j> = theta(Y) m_j,   (C3') T_j(Y) = theta_3(Y) m_j,   (C4') [Y^(j)] = theta_4(Y) m_j,
      theta, theta_3, theta_4 forms of degree 2, 3, 4 on L'_0 (p_2 = -q_j, p_3 = 2 T_j, p_4 = bracket). For a section
      sigma -> Y(sigma), B_j := 2A_j - iota:  <B_j s, B_j s'> = <s,s'> + 4 m_j theta_S(s,s'),  sum_j B_j = -3 iota,
      <z_j, B_j s> = 2 m_j theta(Y(s),Z) for Z in N := L'_0 cap DC, and <z_j,z'_j> = m_j theta(Z,Z') on N.
      Neutral columns (m_j = 0; present in all 15 examples): the deletion of column j of L' is a 4 x 4 LEVEL space and
      column j of N is an isotropic line. On a theta-isotropic subspace all of SL's quadratic steps hold verbatim; what is
      missing is the classification of N (analogue of S3-S4: columns of N are no longer isotropic, the five column forms are
      proportional to ONE form theta) and the cubic/quartic exclusions with the unknowns theta_3, theta_4.
      Sub-case "split free row" (14 of 15 examples): if e_i m^T is in L' then dim L' = 1 + dim L''' (L''' the 3-row projection)
      and the conditions are (E1) D(Y''') m in Cm, (E2) D(Y''')(1 + l(Y''')) in 24*1 + Cm, with D(Y''') v = deletion vector of
      the 4-row matrix (J + Y'''; v) given by (I1); claim to prove: dim L''' <= 3.
  (c) e = 2, 3 (p = 5): nothing beyond Proposition O and the numerics of R3.
STATUS 15:34: census + two more exact facts added below; RESULT ROUND 2 block is at the top.
 CENSUS (numerical, rows/orth_chk.py, kappa_chk.py): (i) 4 x 5 examples (29): 26 have q_s = 3 and L'_s of dimension exactly e with
   pairwise orthogonal rows and zero triple sums (Proposition O proves dim L' <= e + 3 for them, with equality); the other 3
   are (d,e,q_s,dim L'_s) = (4,1,2,2), (5,2,2,3), (6,3,3,3) with non-orthogonal L'_s (all satisfy dim L'_s = e + 3 - q_s).
   (ii) 3 x 5 examples (25): 23 have q_s = 2, L'_s orthogonal of dimension e; 2 are strongly level DC planes (d,e,q_s) = (2,0,0),
   non-orthogonal, with dim(C + span kappa) = 2 = dim L'_s (DDI tight). So on both floors the conjecture reads
        (DI_p')   dim L'_s <= e + (p - 2 - q_s),     and is PROVED whenever L'_s is orthogonally centred (then dim L'_s <= e).
 LEMMA B' (generalises verifyfl's Lemma B to every e; rigorous; identity checked to 5e-14 at random points, rows/gram_chk.py).
   For a 4 x 5 matrix Y with zero total sum: c_j = sum of column j, s = row sums, b_j(Y) := 2(y_j - (c_j/4) 1) - s in V_4. Then
        |b_j(Y)|^2 = |s(Y)|^2 + 3 c_j(Y)^2 - 4 (p_2(Y)_j - P_2(Y)),     sum_j b_j(Y) = -3 s(Y).
   So on a level space L' the linear maps b_j : L' -> V_4 have Gram forms  G_j = s^*(dot) + 3 c_j (x) c_j - 4 p_2(.,.)_j ,
   where (c_j)_j and (p_2(.,.)_j)_j are C(L')-valued; for every w in C(L')^perp:  sum_j w_j (|b_j|^2 - |s|^2 - 3 c_j^2) = 0.
   e = 0: B_j isometries (zeros). Consequences for e = 1 (C = Cm): G_j = s^*(dot) + 3 m_j^2 kappa^2 - 4 m_j Pi has rank <= 3 for
   each j; for a NEUTRAL column (m_j = 0) b_j is an isometry of s(L'), and if q_s = 3 then column j of every Z in L'_s is 0.
   Example of use: if m = e_a - e_b and q_s = 3 then L'_s is inside {z (e_a - e_b)^T : e_2(z) = 0} (level forces e_2(z) = 0;
   the column sums (sum z)(e_a - e_b) are allowed), so dim L'_s <= 2 and dim L' <= 5 only -- NOT enough to exclude (5,1).
   [CORRECTION 15:36 of a first version of this remark that claimed dim L'_s <= 1.] Indeed
       M_2 := { z (e_0 - e_1)^T : z in span((1,w,w^2,0), (1,1,1,-1)) }
   is an exact (2,1) space (level error 1e-15, defect line C(e_0 - e_1)) with non-orthogonal rows. Searches STARTED at M_2 plus
   random vectors converge to (3,1) 6/8 and (4,1) 11/24 spaces, (5,1) 0/12 (floor 4.2) [numerical]; the solver moves all basis
   vectors and the limits do NOT contain M_2 (their zeta is 0, rows/twocol_chk.py), so whether M_2 itself extends is untested.
STATUS 15:37: rigorous corollaries of Theorem DI_3 for the upper floors (the "k-row part" hierarchy).
 COROLLARY H (rigorous). Let L' be a k x q level space (k = 3 or 4), e = dim C(L'), W = (C(L') + C1)^perp (dim q - 1 - e).
   (H1) the single-row part U_i := {u : e_i u^T in L'} lies in C(L'):  dim U_i <= e.            [p_1(e_i u^T) = -u]
   (H2) every TWO-ROW part L'_{ii'} := {Y in L' : only rows i, i' nonzero} has  dim <= e + 1.
        Proof: L'_{ii'} is a 2 x q level space and L'_{ii'} (+) e_r (x) W is a 3 x q level space (a subspace of L(L')) in which
        the row carrying W is deletable; by the corollary of Theorem DI_3 its dimension is <= q.  QED
   (H3) consequently  dim L' <= e + 1 + min over pairs {i,i'} of rank(projection of L' to the rows other than i, i'),
        and in a 5 x 5 level space L with a deletable row r every 3-row part containing row r has dim <= 5 (L156 alone: 6).
   The same statement one floor up, "every three-row part of a 4 x 5 level L' has dim <= e + 2", is equivalent to (DI_4) for the
   3-row parts; (DI_5) is the statement for the 4-row part: conjecturally "the k-row parts have dim <= e + k - 1".
   For the hypothetical 8- and 9-dim spaces: in a (5,1) space every two-row part of L' has dim <= 2, in a (6,1) space too, so
   the projection of L' to any two rows has rank >= 3 (resp. >= 4).
STATUS 15:39: LEMMA TC (two-column defect line; rigorous, uses the verified Lemma SL; sanity-checked on the 7 example spaces with
 m = e_a - e_b, rows/twocol_chk.py: the kernel L'' below has defect 0 to 1e-11, one LM-limited case 4e-8).
   Let L' be a 4 x 5 level space with C(L') inside C(e_a - e_b). Put zeta := {z in C^4 : z (e_a - e_b)^T in L'} and
   eps(x,z) := tau(x) tau(z) - x.z (the polar form of 2 e_2 on C^4, nondegenerate). Then
   (i)  e_2 vanishes on zeta (level), so dim zeta <= 2;
   (ii) y_a - y_b is eps-orthogonal to zeta for every Y in L'   [add the a- and b-coordinates of the polarised deletion form
        p_2(Y,Z)_j = c_j(Y)c_j(Z) + (s(Y).z_j + s(Z).y_j)/2 - y_j.z_j, which are opposite because p_2(Y,Z) is a multiple of e_a - e_b];
   (iii) L'' := {Y in L' : y_a = y_b} is STRONGLY level (C_j = 24 for j != a,b because those coordinates of C(L') vanish;
        C_a = C_b by the symmetry of Y and C_a + C_b = 48), hence dim L'' <= 3 by Lemma SL;
   (iv) dim L' <= 3 + dim{y_a - y_b : Y in L'} <= 3 + (4 - dim zeta).
   So a (5,1) space with defect line C(e_a - e_b) is L'' (+) (2 more dimensions) with L'' a 3-dim strongly level space having
   two equal columns, or has dim L'' <= 2 and at least 3 independent differences y_a - y_b; if zeta is 2-dim (Lagrangian) then
   L' = zeta (x) (e_a - e_b)^T (+) L''. Finishing this sub-case needs only zeros' list of 3-dim strongly level spaces
   (types (3,0), (2,1), (1,2)) with two equal columns and the cubic cross conditions -- not done.
STATUS 15:41 (round 2 final): proved = Theorem DI_3, Lemma D, Theorem DDI, Proposition O, Corollary H, Lemma B', Lemma TC, identities
 (I1)-(I3) (all rigorous; identities exact in rational arithmetic). Numerical only = the census (orth_chk, kappa_chk), existence
 of the (d,e) types, all "not found" statements. (DI_4), (DI_5), and (DI_5) at e = 1 remain open; the obstruction is identified
 (pairing terms / non-orthogonal row-centred part, i.e. the generalisation of the type I-IV analysis of Lemma SL).
 Round-2 files (rows/): di_ident.py (exact identities), g1test.py, small_di.py, orth_chk.py, kappa_chk.py, gram_chk.py,
 twocol_chk.py, cand_M2.npy, di_p*_d*_e*_s*.npy, g1_p2_*.npy.

STATUS 17:52 (ROUND 3 started 17:38, budget to ~19:08; targets: upper floors (6,2), (7,3); EQ-induction; (D)).
## Section R3 (round 3)
 R3.0 WHAT THE CHECKED PROOF Outside/L_gct_215.lean ("4 x 5 level <= 7") CONTAINS (read: definitions lines 128-170, final assembly).
   It is a proof by contradiction for an 8-dim L (no classification of 7-dim spaces). Invariants: u_i := dim of the single-row
   part of L in row i (my U_i), p_ij := rank of the projection to rows i, j. Case tree (abbrevs vJ, MidCase, mI, eI, HighPair, vK):
     some u_i >= 4 (full free row)           -> impossible                       [vJ]
     some u_i in {2,3}                        -> impossible                       [MidCase, the longest part]
     some u_i = 1                             -> there is a 7-dim level M with two EQUAL COLUMNS  [mI], and
                                                 no 7-dim level space has two equal columns        [eI]
     all u_i = 0: some p_ij = 7 -> impossible [HighPair];  all p_ij <= 6 -> impossible [vK].
   Useful checked by-products: (eI) a 4 x 5 level space with two equal columns has dim <= 6; the u_i = 1 case is treated through
   the 3-row projection (their W L, K3, S3), i.e. exactly the "split free row" normal form.
 R3.1 CONSEQUENCES OF "4 x 5 level <= 7" THROUGH THE DEFECT CONSTRUCTION (rigorous).
   (a) every 3 x 5 level space L'' has dim L'' <= e(L'') + 3   [L(L'') = L'' (+) e_4 (x) W'' is 4 x 5 level of dim d'' + 4 - e''];
       this is (DI_4) with 3 in place of 2. Every three-row part of a 4-row level L' has dim <= e(L') + 3.
   (b) a level space L of 5 x 5 matrices has dim(L cap {row r = 0}) <= 7 for every row (column): in a 9-dim level space every row
       and column projection has rank >= 2 (a_r <= 3), an 8-dim one has no zero row or column. In the defect table this
       removes (8,4), (8,3), (9,4): with (D), the gap follows from "no (6,1) and no (7,2)", hence from "no (5,1) and no (6,2)".
 R3.2 LEMMA EC (equal columns; rigorous; checked on 74 cases, level error 2e-14, defect as predicted).
   Let M be a 4 x 5 level space with y_a = y_b for all Y in M, and E_i := e_i (e_a - e_b)^T for ONE row i. Then M (+) C E_i is level
   and C(M (+) C E_i) = C(M) (+) C(e_a - e_b).
   Proof. N is linear in row i: N(J + Y + tE_i) = N(J+Y) + t (N_{i,a} - N_{i,b}), N_{i,c} = injection sum of the other rows into
   the columns != c; the other rows have equal columns a, b, so N_{i,a} = N_{i,b}. Same computation for the deletions:
   C_j unchanged for j != a,b, and C(Y + tE_i) - C(Y) = t nu_i(Y)(e_b - e_a), nu_i = perm of (rows != i, columns != a,b), nu_i(0) = 6. QED
   Consequences: (i) dim M <= 6 (also eI); (ii) with verifyfl's Lemma EQ: for a (d,e) space L' and a pair (a,b) with C(L') not inside
   {c_a = c_b}, M := L'_ab = {y_a = y_b} is a (d - delta, <= e-1) space (delta := dim{y_a - y_b}) and M (+) C E_i is a
   (d - delta + 1, <= e) space containing the two-column split row E_i; delta >= 1 whenever d = 7.
   (iii) a (7,3) space with a moving pair of delta = 1 contains a (6, <= 2) space; a (6,2) space with delta = 1 contains a (5, <= 1)
   space; so in a MINIMAL counterexample to (DI_5) every moving pair has delta >= 2.
 R3.3 TOWER LEMMA (rigorous; checked on 9 spaces L(L''), L'' 3 x 5 with nondegenerate defect: all have defect 4).
   Let L'' be a (p-1) x q level space, W'' = (C(L'') + C1)^perp, L' := L(L'') = L'' (+) e_p (x) W''. Then C(L') contains C(L'') + W''
   [deletion vector of (Y'', w) is Delta(Y'')(1 + w), Delta(0) = (q-2)_{p-2}... (J - I) up to a constant, so w itself is a defect vector],
   hence the next free part W' := (C(L') + C1)^perp lies in C(L'') cap W'' = rad(C(L'')) (the radical of the dot form on C(L'')):
   W' is totally isotropic, dim W' <= 2, and W' = 0 when C(L'') is nondegenerate.
   So a 5 x 5 level space with two successively deletable ROWS (both untwisted) has free parts W'' (row 4) and W' (row 5) with
   W' inside rad C(L''): the 6-dim 4 x 5 spaces L(L'') built from my 3 x 5 examples all have defect 4 and give nothing in 5 x 5;
   the (6,3) spaces (defect 3) are not of this kind (their deletable line, if any, is a column, or the defect below is isotropic).
 R3.4 NUMERICS (not proofs). (a) 7-dim 4 x 5 level spaces: none found (unseeded 0/10, floor 0.5; seeded at the five known 6-dim
   spaces 0/15, floor 0.5, with the calibration "5-dim subspace of a 6-dim space -> 6-dim" 3/15 + slow singular convergences;
   equal-row classes (3,1), (2,2), (2,1,1): 6 reached, 7 not). So numerically max = 6 = 4+5-3, the checked 7 is not sharp, and
   (7,3), (7,2) would be vacuous; but there is no known 7-dim space to compute a defect on, and I cannot prove "<= 6".
   (b) (6,2): 0/8 more starts seeded at ALL known 6-dim spaces (floor 3.8; same code moves rc45 (e = 4) to a (6,3) space).
   (c) EQ-induction census (rows/eq_chk.py; delta_ab = dim{y_a - y_b}, only pairs moving C(L')):
        (4,1): a pair with delta = 1 and L'_ab strongly level of dim 3 exists in 23 of 24 spaces;
        (5,2): a "tight" pair (delta = e - e(L'_ab)) exists in 7 of 8; one space (clm_p4_d5_defect2_s9) has min delta = 2;
        (6,3): NO tight pair in 4 of 4: min delta = 2 (three spaces, L'_ab of type (4,2)) and 3 (one space).
      So the proposed induction step "dim(L'/{y_a = y_b}) <= 1 for a well-chosen pair" FAILS on existing extremal spaces
      (already "<= 2" fails once), and "<= 2" would not close the induction anyway (it gives d <= 2e + 3). What holds in all
      examples is only the trade-off (d' - e') + (delta - (e - e')) <= 3 for L'_ab of type (d', e'), which is (DI_5) itself.
 R3.5 SATURATION PRINCIPLE FOR ANY ROW (rigorous, 1 line; generalises the defect construction to non-deletable rows).
   For a p x q level space L and a row i let Pi_i := projection of L to the other rows (NOT level in general) and
   C^(i)(L) := span{C(Y) - C(0) : Y in Pi_i} mod C1 (deletion vectors of the (p-1)-row projections). Because N is linear in row i,
        N(J + z + e_i v^T) = N(J + z) + v . C(pi_i z),
   so L + e_i (x) (C^(i)(L) + C1)^perp is level, the single-row part U_i of L lies in (C^(i)(L) + C1)^perp, with equality when L is
   maximal (or saturated). Row i is deletable iff Pi_i is level, and then C^(i)(L) = C(Pi_i) is the defect space.
   In L_gct_215 the case u_i = 1 is exactly this: e_i v^T in L iff v is orthogonal to the deletion vectors of the 3-row projection;
   their sub-lemmas show that in an 8-dim 4 x 5 level space v must be a two-column vector e_a - e_b and then the other three rows of
   every element have equal columns a, b (abbrev oT), which produces the 7-dim equal-column space excluded by eI.
STATUS 17:59: split-pair normal form (FL2) and searches.
 R3.6 SPLIT FREE ROW PAIRS: NORMAL FORM "FL2" (rigorous; all conditions checked on 5 numerical examples to 1e-13, resp. to the
   1e-7 accuracy of the singular LM solutions).  For U inside 1^perp put U' := (U + C1)^perp and T_U := e_i (x) U (+) e_r (x) U'
   (a 4-dim 2-row level space; U = 0 is the full free row). Let L be level and contain T_U. Then L cap {only rows i, r} = T_U,
   dim L = 4 + dim Pi (Pi = projection of L to the other three rows), and with Delta(Y'')_{jk} := perm((J + Y'')[all 3 rows; columns
   != j,k]) (symmetric, zero diagonal, Delta(0) = 6(J - I)), perm(J + z) = (1 + z_r)^T Delta(z'') (1 + z_i). So L is level iff
   for all Y'' in Pi with lifts a = row i mod U, b = row r mod U':
     (i)   Delta(Y'') U inside U + C1   (equivalently Delta(Y'') U' inside U' + C1);
     (ii)  Delta(Y'')(1 + a) in U + C1,   Delta(Y'')(1 + b) in U' + C1;
     (iii) (1 + b)^T Delta(Y'') (1 + a) = 120.
   Degree 1: a = -c mod (U + C1), b = -c mod (U' + C1) (c = column sums of Y''), and c o U inside U + C1, c o U' inside U' + C1
   (o = entrywise product): the column sums of the 3-row part act on U and U' modulo constants.
   U = 0 is Theorem FL (dim Pi <= 3 by Lemma SL). CONJECTURE FL2: dim Pi <= 3 for every U (then every level space containing a
   split pair has dim <= 7). In the defect table: a (5,1) space containing e_i m^T is the case dim U = 1 (verifyfl's split case);
   a (6,2) space in which some row of L' carries the whole defect plane (U_i = C(L')), in particular every (6,2) space that
   is an untwisted double row tower, is the case dim U = 2; by the Tower Lemma a double row tower needs U' = W inside rad, i.e.
   U = U' Lagrangian.
 R3.7 NUMERICS for FL2 (rows/splitpair.py: unknown U, U' in Grassmannian charts, dpp extra vectors with independent 3-row parts;
   positives are verified level spaces, negatives are calibrated only by the dim-7 hits of the same code):
     dim U = 1: dim 7 found 4/7, dim 8: 0/14 (floor 0.2);     dim U = 2: dim 7 found 2/8 (NEW: free parts (2,2) on two rows, U
     nondegenerate, U (+) U' = 1^perp, exactly one deletable row, (r,d,r_A,r_B) = (7,0,3,4)), dim 8: 0/14 (floor 0.2).
     [dim U = 0, dim 7: 0/6 converged within 250 iterations (one at 4e-2, slow): this instance is NOT calibrated.]
   A first reading of these (2,2) spaces with too strict a rank tolerance gave "first-order space of dim 7, no deletable line";
   that was wrong: the singular value at the cut is 1e-6 (LM accuracy of singular solutions), the deletion test gives one
   deletable row at 4e-7 against 0.7..2 for the other nine lines. Conjecture (D) is NOT contradicted.
STATUS 18:08: TWO NEW RIGOROUS RESULTS: Lemma SL_3 (strongly level 3 x 5 spaces have dim <= 2) and Theorem FL2* (split pairs).
 R3.8 LEMMA SL_3 (rigorous hand proof; formulas checked to 4e-13 in rows/sl3_chk.py): a linear space Pi of 3 x 5 matrices all of
   whose 3 x 4 column deletions are level has dim <= 2.  [= (DI_4) at e = 0; sharp: ex1's plane; the LM search found none of
   dim 3.]  COROLLARY: a 4 x 5 level space containing a full free row has dim <= 6 (it is F (+) Pi by zeros' reduction).
   Proof. u := (1,w,w^2), ub its conjugate; V_3 = span(u,ub) = sum-zero vectors of C^3; <u,u> = <ub,ub> = 0, <u,ub> = 3;
   u o u = ub, ub o ub = u. (a) P_1 of the deletions: all column sums vanish, so Y = u p^T + ub r^T with p, r in C^5, row sums
   s = (sum p) u + (sum r) ub. Toolbox (kbuild): P_2(u p^T + ub r^T) = 3(p.r - sum p sum r), P_3 = 6(e_3(p) + e_3(r)), any number of
   columns. Hence strongly level <=> for all j:
        (S2_j)  r_j(sum p - 2p_j) + p_j(sum r - 2r_j)... in the normalised form  q_j := |eta_j|^2 - <s,eta_j> = 0  (eta_j = column j),
        (S3_j)  e_3(p without p_j) + e_3(r without r_j) = 0;   summing (S3_j): E := e_3(p) + e_3(r) = 0.
   (b) S := s(Pi) inside V_3 (dim q <= 2), N := Pi cap {s = 0}, dim Pi = q + dim N. Polarising q_j as in verifyfl S5: with a section
   Y(sigma), eta_j = A_j sigma, B_j := 2A_j - id: <B_j sigma, B_j sigma'> = <sigma,sigma'> and <zeta_j, B_j sigma> = 0 for Z in N.
   q = 2: B_j is an isometry of V_3, so zeta_j = 0: N = 0, dim Pi = 2.
   (c) On N every column lies in C u or C ub (the two isotropic lines of V_3): Z = u lam^T + ub mu^T with disjoint supports,
   sum lam = sum mu = 0. (S3_j) with E = 0 reads lam_j (lam.lam - 2 lam_j^2) = 0 on the support of lam (e_2(lam) = -lam.lam/2), so on
   the linear space N each coordinate lam_j is 0 or satisfies lam_j^2 = lam.lam/2; summing, exactly two coordinates are active
   and lam = l (e_a - e_b); likewise mu = l' (e_c - e_d). So dim N <= 2, and dim N = 2 iff N = span{u(e_a-e_b)^T, ub(e_c-e_d)^T}.
   (d) (q, dim N) = (1,2) is impossible: let Y_0 = u p^T + ub r^T have s != 0. Cross conditions with u(e_a-e_b)^T and ub(e_c-e_d)^T:
   r_a = r_b = (sum r)/2, p_c = p_d = (sum p)/2; then q_a = 0 gives (sum p)(sum r) = 0; by the symmetry u <-> ub take sum r = 0,
   t := sum p != 0: r_a = r_b = 0, p_c = p_d = t/2, p_a + p_b + p_e = 0. On Y_0 + N (p_a -> p_a + lam, p_b -> p_b - lam, r_c -> r_c + mu,
   r_d -> r_d - mu, identities in lam, mu): (S3_a) - (S3_b) gives e_2(p) = t(p_a+p_b) - p_a^2 - p_a p_b - p_b^2, i.e. p_e = -t/4;
   q_e = 3 r_e (2p_e - t) = 0 gives r_e = 0, so r = (0,0,nu,-nu,0); then E = (3t/4) p_a p_b - t^3/16 and
   (S3_c) = E - (t/2) e_2(p) + t^3/8 with e_2(p) = p_a p_b + 3t^2/16: E = 0 forces p_a p_b = t^2/12, (S3_c) forces p_a p_b = t^2/16.
   Contradiction. So dim Pi = q + dim N <= 2.  QED
 R3.9 THEOREM FL2* (rigorous; identities exact in rows/fl2_ident.py; conditions verified on 5 numerical examples; consistent with
   all examples). Let U be a subspace of 1^perp in C^5 with U cap U' = 0, U' := (U + C1)^perp (i.e. the dot form is nondegenerate on U),
   and let L be a 5 x 5 level space containing the split pair T_U = e_i (x) U (+) e_r (x) U'. Then
        dim L <= 10 - dim(U o U'),         U o U' := span{u o u' : u in U, u' in U'}  (entrywise products; a subspace of 1^perp).
   In particular dim L <= 7 whenever dim(U o U') >= 3, and <= 6 when U o U' = 1^perp.
   Proof. Notation of R3.6. (1) L cap {rows i,r only} is a 2 x 5 level space containing the 4-dim T_U, hence equals it
   (2 x q level <= q-1): dim L = 4 + dim Pi. (2) Degree-1 part of (i): u'^T Delta_1(Y'') u = 4 c.(u o u') with c = column sums of
   Y'' [Delta_1 u = -2S u + 4 c o u - 2(c.u)1, S = sum c]. So c(Y'') lies in (U o U')^perp, which contains 1. Let Pi_0 := {Y'' in Pi :
   c(Y'') in C1}; codim of Pi_0 in Pi is <= dim (U o U')^perp - 1 = 4 - dim(U o U'). (3) Degree-1 part of (ii): u'.(a + c) = 0 and
   u.(b + c) = 0, so on Pi_0: a in U + C1, b in U' + C1; subtracting elements of T_U, every Y'' in Pi_0 has a unique lift
   z = (Y''; alpha 1; beta 1) in L, alpha, beta linear forms. (4) perm(J + z) = (1+alpha)(1+beta) 1^T Delta(Y'') 1 = 120 identically on
   the linear space Pi_0; a product of polynomials equal to a nonzero constant has constant factors: alpha = beta = 0, and then
   P_1 gives c = 0 on Pi_0. (5) Now (ii) says Delta(Y'')1 lies in (U + C1) cap (U' + C1) = C1 (+) (U cap U') = C1, and
   1^T Delta 1 = 120, so Delta(Y'')1 = 24*1: all 3 x 4 deletions of Y'' are level, Pi_0 is strongly level, dim Pi_0 <= 2 (SL_3).
   (6) dim L = 4 + dim Pi <= 4 + 2 + 4 - dim(U o U').  QED
   Values of dim(U o U'): dim U = 1, U = C m with m.m != 0: 3 - max(|Z(m)| - 1, 0), Z(m) = zero set of m (so 3 iff m has at most
   one zero entry); dim U = 3: the same with U' = C m'; dim U = 2: 4 for generic U, 3 in the two (2,2) examples found (U or U'
   inside a coordinate hyperplane), in which the bound 7 is attained; for L_m (one zero entry) the bound 7 is attained too.
   COROLLARIES for the defect table (L(L') contains T_U as soon as L' contains e_i (x) C(L')):
   (a) NO (5,1) OR (6,1) SPACE CONTAINS e_i m^T WITH m NON-ISOTROPIC AND AT MOST ONE ZERO ENTRY  (split case of (DI_5) at e = 1).
       Remaining split cases at e = 1: m isotropic (U inside U'); m supported on exactly 3 columns (bound 8 only);
       two-column m is verifyfl's TC5.
   (b) no (6,2) or (7,2) space L' has a row carrying the whole defect plane (U_i = C(L')) when C(L') is nondegenerate with
       dim(C(L') o W) >= 3; no (7,3) space has a row carrying C(L') when C(L') is nondegenerate with dim(C(L') o W) = 3 (max possible).
   (c) with SL_3: every level space containing a full free row lies one floor down too: 4 x 5 level with a full free row <= 6.
STATUS 18:14: sanity runs for FL2* done (rows/fl2star_chk.py, fl2gen_chk.py): fixed m = (1,2,-4,1,0): dim 7 found 2/5, dim 8 0/3
 (floor 0.8); fixed m = (3,1,-2,5,-7) (full support): dim 6 found 2/5, dim 7 0/5 (floor 0.3) -- suggests that for full-support m the
 true bound is 6 (i.e. kappa = 0: the column sums of the 3-row part are constant), which would explain why the defect line m of
 every known (4,1) space has a zero entry; not proved. RESULT ROUND 3 block written at the top.
 Round-3 files (rows/): lev45.py, eq_chk.py, r3_chk.py, splitpair.py, fl2gen_chk.py, fl2star_chk.py, fl2_ident.py (exact), sl3_chk.py,
 split_k*_d3_s*.npy (7-dim spaces with split pairs), rc45.npy.
 R3.10 WHAT IS LEFT OF THE SPLIT CASE AT e = 1 AFTER FL2* (set-up for whoever continues; rigorous as far as stated).
   m supported on exactly three columns, zeros z, z' (m.m != 0): (U o U')^perp = span(1, e_z, e_z'), so c(Y'') = gamma 1 + kappa e_z +
   kappa' e_z'; the proof of FL2* gives b = 0 (row r), a = alpha 1 - kappa e_z - kappa' e_z' (row i, mod C m), alpha = -gamma, and
   Pi_0 = {kappa = kappa' = 0} strongly level (dim <= 2); L' = C e_i m^T (+) Lambda, Lambda = {(Y''; alpha 1 - kappa e_z - kappa' e_z')} a
   level 4 x 5 space with (E1) Delta(Y'') m in span(1,m), (E2) m . Delta(Y'')1 = 0, (E3) Delta(Y'')(1 + a) in span(1,m).
   To exclude (5,1) one must show that kappa and kappa' cannot both be nonzero independent forms when dim Pi_0 = 2
   (for the naive candidate with two column vectors (1,1,1,.)e_z^T, (1,1,1,.)e_z'^T the cross term -6 sigma^2 kappa^2 kills levelness).
   m isotropic (U inside U'): step (5) of the proof only gives Delta(Y'')1 in span(1,m), i.e. Pi_0 is a 3-row level space with defect
   line C m; one needs "dim Pi_0 <= 2" there (true for L_m with isotropic m), which is a 3-row statement at e = 1 with the extra
   condition (i).  Full-support m: numerics suggest the sharper bound 6 (kappa = 0).
STATUS 18:20 (round 3 final): see RESULT ROUND 3 at the top. Rigorous this round: SL_3, FL2*, R3.1-R3.3, R3.5, R3.6 (normal form).
 Numerical only: R3.4, R3.7 and the sanity runs. Not achieved: (6,2), (7,3) in general; (D).

STATUS 18:36 (ROUND 4 started 18:20, budget to ~19:50; targets: induction on e via hyperplanes, structure of extremal spaces, (D)).
## Section R4 (round 4)
 Conventions: an (d,e) space is a 4 x 5 level space L' with dim L' = d and defect space C = C(L') of dim e; W_1 := C^perp (contains 1),
 W = W_1 cap 1^perp; U_i := {u : e_i u^T in L'} (single-row parts, u_i := dim U_i); a column n is NEUTRAL if every vector of C
 vanishes at n (e_n in W_1, i.e. C_n(Y) == 24 on L'); C_2 := span{e_a - e_b : e_a - e_b in C} (the "two-column part" of C).
 (DI_5;e): every (d,e') space with e' <= e has d <= e' + 3.  Known: (DI_5;0) = Lemma SL (verified).
 R4.1 HYPERPLANE LEMMA (rigorous, 2 lines; generalises verifyfl's Lemma HYP). Assume (DI_5; e-1) and let L' be an (e+4, e) space.
   Then every subspace K of L' has e(K) >= min(e, dim K - 3); in particular EVERY hyperplane H of L' is an extremal (e+3, e)
   space with the SAME defect space C(H) = C(L'), and every subspace of codimension 2 has defect space C or a hyperplane of C.
   Proof. e(K) <= e. If e(K) <= e-1 then (DI_5; e-1) gives dim K <= e(K) + 3.  QED
 R4.2 CONSTRAINTS ON SINGLE-ROW PARTS (rigorous).  For every (d,e) space: (a) U_i inside C (H1); (b) U_i perp U_k for i != k
   [P_2(e_i u^T + e_k u'^T) = -<u,u'>]; (c) sum_j u_j u'_j u''_j = 0 for u, u', u'' in U_i, U_k, U_l with i,k,l distinct [P_3];
   (d) u_i + u_k <= e + 1 for i != k [Corollary H2: the two-row part has dim <= e + 1].
 R4.3 LEMMA RS-HYP (rigorous; uses (d), and for e = 3 the checked iterated Fermat lemma L067 on power sums).
   Assume (DI_5; e-1), e in {1,2,3}, and let L' be an (e+4, e) space. Then a generic hyperplane H of L' is NOT fully row-split,
   i.e. sum_i U_i(H) != C.   [So: if every extremal (e+3,e) space with defect space C were fully row-split, no (e+4,e) space
   with defect space C would exist.]
   Proof. For generic H, U_i(H) is a hyperplane of U_i(L') (or 0), so dim sum_i U_i(H) <= sum_i (u_i - 1)_+ with u_i = u_i(L').
   e = 1: u_i <= 1, the sum is 0. e = 2: the sum is >= 2 only if u_i = u_k = 2 for two rows, contradicting (d). e = 3: by (d) the sum
   is >= 3 only if three rows have u = 2; by (b) and nondegeneracy of the dot form on the 4-dim space 1^perp the three planes
   coincide with one totally isotropic plane Lam; by (b), (c) the power sums p_1, p_2, p_3 vanish on Lam, so 3 dim Lam <= 5 (L067):
   contradiction.  QED
 R4.4 CENSUS OF EXTREMAL SPACES (numerical; rows/r4_census.py, r4_c52.py; 44 old + 24 new (5,2) spaces, 15 of the new ones seeded at the
   two NON-split (4,1) spaces).  "Extremal spaces are always fully row-split" is FALSE:
     (4,1): 22 row-split (C = C m carried by e_i m^T), 2 with no single-row element and C = C(e_a - e_b);
     (5,2): 29 fully row-split (u = (1,1,0,0): 18, u = (2,0,0,0): 11), and 3 with NO single-row element and C = V_S, |S| = 3;
     (6,3): 2 fully row-split (u = (3,0,0,0), FS type); 10 with sum U_i of dim 1 only and C = V_S, |S| = 4.
   (V_S := sum-zero vectors supported on the column set S.)  What holds in ALL 68 spaces:
        (LAW)   C = sum_i U_i + C_2      (the defect space is spanned by single-row parts and two-column vectors),
   and in every space that is not fully row-split, C = V_S with |S| = e + 1, i.e. the 4 - e columns outside S are NEUTRAL
   (the maximal possible number of neutral columns for defect dimension e). [One LM-limited file gives rank 3 > e for sum U_i + C_2;
   tolerance artefact.]  Neutral columns are exactly the deletable columns of L' (deleting column n leaves a level 4 x 4 space),
   so these (6,3) spaces are the "alternating towers" predicted by the Tower Lemma: row r of L deletable, then a COLUMN of L'.
   Also: the defect line m of every row-split (4,1) space has a zero entry = a neutral column (and fixed full-support m only reach
   dim 3, round 3): in all examples an extremal L' has a deletable line of its own (a neutral column or a deletable row).
 R4.5 THE CHAIN (NC_k) (statement; two ends are theorems).  (NC_k): a 4 x 5 level space with k neutral columns has dim <= 7 - k.
   k = 4 (then all five deletions are level): Lemma SL.   k = 3: verifyfl's TC5 (defect line e_a - e_b).   k = 0: the checked
   L_gct_215.   k = 2 (would exclude the column-type (6,2)) and k = 1 (would exclude the column-type (7,3)): OPEN.
   Reduction of (NC_1) to 4 x 4 statements (rigorous): if column n is neutral, Q := L' minus column n is a 4 x 4 level space and
   N(J + (q | x)) = 24 + (1 + x).M(q), M(q)_i := level polynomial of q minus row i (3 x 4), sum_i M_i = 96; so with
   C^col(Q) := span{M(q) - 24*1} (inside 1^perp of C^4, e^col := its dimension) the single-column part X_n of L' lies in
   (C^col(Q) + C1)^perp and dim L' <= dim Q + 3 - e^col(Q)  (the transposed defect construction). Hence
        (NC_1)  <=  "every 4 x 4 level space Q has dim Q <= e^col(Q) + 3";
   e^col = 3 is the checked L_gct_214 (dim Q <= 6); e^col = 0 reads "a 4 x 4 level space all of whose rows are deletable has
   dim <= 3" (attained by a free row); e^col = 1, 2 need dim Q <= 4, 5.
 R4.6 WHAT WOULD CLOSE (DI_5) BY INDUCTION ON e (precise, given R4.1 - R4.5).  Let L' be an (e+4, e) space of minimal e; every
   hyperplane is extremal with the same C. Suppose (LAW) holds for all extremal spaces. With e_2 := dim C_2 (a property of C, the
   same for all hyperplanes) a generic hyperplane H needs dim sum_i U_i(H) >= e - e_2, hence sum_i (u_i(L') - 1)_+ >= e - e_2.
     e = 1: e_2 = 0 impossible (R4.3); e_2 = 1 is TC5.  So (5,1) <= (LAW) for (4,1) spaces [= verifyfl's dichotomy].
     e = 2: e_2 = 0 impossible (R4.3); e_2 = 1 forces a row with U_i = C: excluded by verifyfl's FS when C is nondegenerate
            [degenerate C with exactly one two-column vector: open]; e_2 = 2: C = V_{abc} (two neutral columns: (NC_2)) or
            C = span{e_a - e_b, e_c - e_d} (one neutral column and a two-column structure: open).
     e = 3: e_2 <= 2 forces, by R4.2(d), rows with (u_i) = (3) [FS, C nondegenerate] or two/three rows with u = 2 etc. (finite list,
            not worked out); e_2 = 3: C = V_{abcd} ((NC_1)) or C = V_{abc} + C(e_d - e_e) (no neutral column: open).
   So the extra statements are: (LAW) for extremal spaces, (NC_1), (NC_2), and the finitely many mixed/degenerate patterns of C.
STATUS 18:56: second half of round 4: lifting lemma, (NCOL), calibrated (NC) searches, 4x4 data, (D) reduced to dim 7. Sections R4.7 - R4.12.
 R4.7 LIFTING LEMMA (rigorous, elementary).  Let F_1, .., F_m be sets of polynomial functions on a vector space; a linear subspace K
   "has property i" if every f in F_i vanishes identically on K. If a linear space L has none of the m properties, there is t in L
   such that NO linear subspace of L through t has any of them (so the generic subspace of every dimension k >= 1 has none).
   Proof. Choose f_i in F_i with f_i not identically 0 on L; the product f_1...f_m is not identically 0 on L; take t with
   f_1(t)...f_m(t) != 0.  QED.   "Row r deletable" (pi_r(L) level: P'_k(pi_r t) = 0, k = 1..4) and "column n neutral" are of this form.
   COROLLARY D-UP: if every level space of dimension d has a deletable line, so has every level space of dimension >= d.
     Hence (D) <=> (D)_7 := "every 7-dim level space has a deletable row or column", and (D) for dim >= 8 FOLLOWS from (D)_7;
     an 8-dim level space without deletable line would contain an open dense family of 7-dim level subspaces without one.
   COROLLARY C-UP (with R4.1): assume (DI_5; e-1). Every property of the defect space that holds for all extremal (e+3, e) spaces
     holds for every (e+4, e) space (all its hyperplanes are extremal with the SAME defect space).
 R4.8 (NCOL): THE DEFECT SPACE OF AN EXTREMAL SPACE LIES IN A COORDINATE HYPERPLANE   [NUMERICAL, 0 exceptions].
   Statement (NCOL_e): every extremal (e+3, e) space, e = 1, 2, 3, has a NEUTRAL COLUMN n (C inside e_n^perp; equivalently L' minus
   column n is a level 4 x 4 space Q; equivalently W contains 1 - 5 e_n, i.e. the 5 x 5 space L(L') contains e_r (1 - 5 e_n)^T, i.e.
   L(L') + CJ contains the matrix "J with row r replaced by 5 e_n^T").
   Evidence: (i) all 87 extremal spaces of rows/ (rows/ext_chk.py): (d,e,#neutral columns) = (4,1,1): 13, (4,1,2): 8, (4,1,3): 3,
   (5,2,1): 25, (5,2,2): 19, (6,3,1): 19 [so every known (6,3) space has C = V_S, |S| = 4, W = C(1 - 5e_n)]; NONE has a deletable ROW
   (3 x 5 rest level).  (ii) independent sample (rows/ncol_ext.py): the 33 seven-dim 5 x 5 level spaces found by repr, numerics,
   lowd, split, methods, dc5: each has a deletable line, and the rest L' always has a neutral line of the other kind
   ((3,0): 17, (4,1): 3, (5,2): 6, (6,3): 5; two files needed the rank cut 1e-3 because they are LM-limited).  (iii) with the defect
   line fixed WITHOUT zero entry no (4,1) space was ever found (verifyfl 0/39; rows round 3: fixed full-support m reaches only dim 6
   for L). Non-extremal spaces need not have one ((3,1) spaces with full-support m exist), so (NCOL) is an extremality statement.
   So: EVERY KNOWN 7-DIM LEVEL SPACE IS A DOUBLE TOWER over a 4 x 4 level space Q: delete a row, then a column (or transposed).
   REDUCTION (rigorous, by C-UP): (DI_5)  <=  (NCOL_e) and (NC'_e) for e = 1, 2, 3, where
        (NC'_e): a 4 x 5 level space with a neutral column and defect dimension e has dim <= e + 3.
   [Induction on e: (DI_5;0) is SL; given (DI_5;e-1) and (NCOL_e), every (e+4,e) space has a neutral column, excluded by (NC'_e).]
 R4.9 CALIBRATED SEARCHES for spaces with neutral columns (rows/nc_search.py, ncdef_search.py; residual < 1e-9 = found) [NUMERICAL]:
     k = 2 neutral columns:  dim 5: 12/25 found (all e = 2);   dim 6: 0/22 (best residual 2.2)          -> supports (NC_2)
     k = 1 neutral column:   dim 6:  7/29 found (all e = 3);   dim 7: 0/25 (best residual 1.5)          -> supports (NC_1)
     k = 1 and e <= 1:       dim 4:  5/11;  dim 5: 0/8 (best 4.2)        k = 1 and e <= 2:  dim 5: 3/5;  dim 6: 0/15 (best 3.2)
   so (NC'_1), (NC'_2), (NC'_3) are supported at the usual (uncertified) level. The 19 new spaces are in rows/nc_d*_k*_s*.npy.
   NEGATIVE: "a column-centred 4 x 5 level space has dim <= 3" (which would give (DI_5) at once, because the column-sum map
   Y -> c(Y) = -p_1(Y)/6 is LINEAR with image inside C, so dim L' <= e + dim ker c) is FALSE: column-centred level spaces of dim 4
   exist (rows/cc_search.py: 5/60, e = 2 or 3; dim 3: 30/30 with e = 4).  The exact statement is dim ker c <= 3 + e - rank c.
 R4.10 THE TRANSPOSED DEFECT CONSTRUCTION AND THE 4 x 4 DATA.
   Rigorous. Let column n of L' be neutral, Y = (q | x), Q := {q} (level 4 x 4), X_n := {x : (0|x) in L'}, M_i(q) := level polynomial of
   the 3 x 4 matrix (J+q minus row i) (sum_i M_i = 96 on Q), M^(j)_i(q) := perm_3((J+q) minus row i, column j), C^col(Q) :=
   span{M(q) - 24*1} (inside 1^perp of C^4, dim e^col <= 3), e^row(Q) := the usual defect of Q (column deletions). Then
     (a) C_j(Y) = (1+x).M^(j)(q) (j != n);  L' level <=> sum x = 0 and x.(M(q) - 24*1) = 0;  the row-sum map of Q has image in C^col(Q);
     (b) X_n inside (C^col(Q) + C1)^perp, so dim L' = dim Q + dim X_n <= dim Q + 3 - e^col(Q)  [dim Q <= 6 by the checked L_gct_214];
     (c) PADDING LEMMA: a 4 x 4 level space with e^col = 0 (or e^row = 0) has dim <= 3   [(Q^T | 0) is a strongly level 4 x 5 space: SL];
     (d) hence (NC'_3) [= (NC_1)]  <=  no 4 x 4 level space with (dim Q, e^col) = (5,1) or (6,2)  (the 4 x 4 copy of the defect problem).
   Numerical (rows/q44_chk.py, all 87 extremal spaces, every neutral column; 9 LM-limited cases read off in the limit):
        e^row(Q) = e(L'),     dim X_n = 3 - e^col(Q),     dim Q = e^row(Q) + e^col(Q),
   with (dim Q, e^col, e^row) = (2,1,1), (3,2,1), (4,3,1), (3,1,2), (4,2,2), (5,3,2), (4,1,3), (5,2,3), (3,0,3), (2,0,2).  So every known
   7-dim level space is  L = Q (+) [column n: 3 - e^col(Q)] (+) [row r: 4 - e^row(Q)]  with  dim Q = e^row(Q) + e^col(Q):
   the total is 7 IDENTICALLY, and 8 would need a 4 x 4 level space with dim Q > e^row + e^col in this position.
   Test of the symmetric inequality on 5 x 5 spaces (rows/sym_chk.py; e_row, e_col <= 4 := dimensions of the spans of the column- resp.
   row-deletion vectors of L): among 90 level spaces of other agents, dim L <= e_row + e_col holds in 89, with EQUALITY (3+4 or 4+3)
   for 36 of the 39 seven-dim ones (the 3 others are LM-limited); it FAILS for methods/sp_circ4.npy: C * circ(1, i, -i, -1) padded by a zero
   row and column is a level line with ALL TEN line deletions level (e_row = e_col = 0). So "dim L <= e_row(L) + e_col(L)" (which
   would give 8 for 5 x 5, 6 for 4 x 4, 4 for 3 x 3) is false as it stands; the correct form must account for doubly strongly level
   parts (not found). [C circ4 (+) full free column is a (4,3) space, exact check: not extremal, no contradiction.]
 R4.11 TARGET (2), conjecture (D) for dim >= 8: NOT proved. What is rigorous: D-UP (R4.7): (D)_7 => (D)_8 => (D)_9, and (D) <=> (D)_7.
   (D)_8 and (DI_5) together are EQUIVALENT to the gap statement at 8 ("no 8-dim level space"): a deletable row r of an 8-dim L gives
   pi_r(L) of type (8-z, <= 4-z), i.e. (7,<=3), (6,<=2), (5,<=1) ((8,.) and (4,0) are excluded); conversely vacuous. So (D)_8 is
   not a lemma on the way but half of the problem. What Lemma C + (Z3) + R3.1 give for an 8-dim L without assuming (D): for every row
   r, L_r := L cap {row r = 0} is a 4 x 5 level space of dim 3 + a_r in {4,..,7} (a_r <= 4), e(L_r) >= 1, z_r <= 4 - e(L_r) <= 3, and for
   r != r' dim(L_r cap L_r') >= 1; under (DI_5): e(L_r) >= a_r, z_r <= 4 - a_r. None of this forces row sums == 0 on L. I found no
   argument; the realistic route is (D)_7 (a statement about 7-dim spaces, testable: 39 + 33 known spaces, 0 exceptions).
 R4.12 WHAT WOULD CLOSE (DI_5) NOW (sharpest form found).  By R4.8:  (NCOL_1,2,3) + (NC'_1,2,3).   Compared with R4.6 this replaces
   (LAW) and the list of mixed/degenerate patterns of C by ONE statement about C ("C lies in a coordinate hyperplane"), and puts all
   remaining cases into the 4 x 4 world: L' = (Q | x), x in the affine fibre over q cut out by x.(M(q) - 24*1) = 0, sum x = 0.
   Known cases of (NC'): (NC'_1) with two-column m (TC5); (NC'_e) when one row carries a nondegenerate C (FS).  Open: everything else.
 R4.13 DIRECT TEST OF (NCOL_3) WITH THE DEFECT SPACE FIXED (rows/fixC_search.py) [NUMERICAL, calibrated only for e = 3]:
   defect space required inside a fixed 3-dim C0 of 1^perp:  C0 = e_0^perp cap 1^perp: dim 6 found 4/19;  C0 generic (no neutral column):
   dim 4: 2/5, dim 5: 1/37, dim 6: 0/46 (best residual 2.4).  For e = 2 the same test is NOT calibrated (a generic plane inside
   e_0^perp cap 1^perp gave 0/12 at dim 5: the known (5,2) planes are special, in line with (LAW)), so no claim is made there.
STATUS 19:05: RESULT ROUND 4 written at the top. Rigorous this round: R4.1 - R4.3, R4.7, R4.10(a)-(d), reduction R4.8.
   Numerical only: R4.4, (NCOL), R4.9, the 4 x 4 data of R4.10, R4.13.  Not proved: (6,2), (7,3), (D)_8.
 R4.14 THEOREM NCOL-S (RIGOROUS; (NCOL_1) in the split non-isotropic case).  Let L' be a 4 x 5 level space with 1-dim defect space C m,
   <m,m> != 0, containing a single-row element e_i m^T.
     (a) If m has no zero entry, then dim L' <= 3.   [So a split (4,1) space with non-isotropic m HAS A NEUTRAL COLUMN.]
     (b) In general: for every Y in L' the column sums c_j(Y'') of the three rows != i are equal for all j with m_j != 0; and on
         N := L' cap {<y^i, m> = 0} (strongly level, verifyfl's THEOREM SPLIT) row i is supported on the zero set of m when m has
         exactly one zero n; then N cap {row i = 0} is a strongly level 3 x 5 space of dim exactly 2 if dim L' = 4.
   Proof. Notation of verifyfl R3.1: <w, C(Y)> = Per(1+y^1,..,1+y^4, w) (symmetric 5-linear), D_i(Y) the symmetric zero-diagonal matrix
   with (D_i)_jk = perm_3((J+Y) minus row i, columns j,k); it depends only on Y'' (rows != i). Since Y + lambda e_i m^T is in L' and
   C(.) - 24*1 is in C m:  D_i(Y) m = mu(Y) m on L';  <m, C(Y)> = mu(Y) <y^i, m>, so N is strongly level, dim N >= dim L' - 1.
   Degree-1 part (Y -> tY): D^(1)(Y) m is in C m, and (exact formula, rows/fl2_ident.py)  D^(1)(Y) m = -2S m + 4 c o m - 2(c.m) 1,
   S, c = total sum and column sums of Y''.  Hence  4 c_j m_j - 2(c.m) = (mu_1 + 2S) m_j  for all j.            (*)
   (a) m_j != 0 for all j: (*) reads c_j = alpha + (c.m)/(2 m_j), alpha := (mu_1+2S)/4; multiplying by m_j and summing,
   c.m = alpha sum m_j + 5 (c.m)/2 = 5(c.m)/2, so c.m = 0 and c(Y'') = alpha(Y) 1 on L' (alpha a linear form).  On N all column
   sums of Y vanish (the linear part of C(tY) = 24*1), so y^i = -c(Y'') = -alpha(Y) 1.  If alpha != 0 on N, take Y_1 in N with
   alpha(Y_1) = 1: row i of J + Y_1 is zero, all 4 x 4 column-deletion permanents vanish, contradicting C(Y_1) = 24*1.  So row i
   vanishes on N, and then C_j(Y) = N_{3x4}((J+Y'') minus column j) = 24: N is a strongly level 3 x 5 space, dim N <= 2 by Lemma SL_3
   (R3.8).  dim L' <= 3.
   (b) If m_n = 0, (*) at j = n gives c.m = 0 and (*) at j != n (m_j != 0) gives c_j = alpha. If n is the only zero: y^i = -alpha 1 - delta e_n
   on N; alpha(Y_1) = 1 would make row i of J + Y_1 a multiple of e_n and C_n(Y_1) = 0: so alpha = 0 on N, row i of N lies in C e_n,
   and N cap {row i = 0} has dim >= dim N - 1 and <= 2 (SL_3).  QED
   Numerical confirmation of every step (rows/ncol1_chk.py): on all 27 split non-isotropic (4,1) spaces (1, 2 or 3 zeros of m) the column
   sums of Y'' lie in span(1, e_n : m_n = 0) and row i of N is supported on the zeros of m, to 1e-10 or better (mostly 1e-15).
   Sharpness: split (3,1) spaces with full-support m exist (round 3: fixed m of full support reaches dim 6 = 3 + 3 for L, not 7).
   REMARK (FS type, any e; same proof): if e_i (x) C lies in L', C nondegenerate, then c(Y'') o C is inside C + C1 for all Y in L',
   and on N = ker gamma: y^i = -c(Y'') in C^perp, the set G = {c(Y'') : Y in N} satisfies 1 not in G + C e_n for every n, and
   dim G >= dim N - 2.  So an EXTREMAL FS-type space needs c in C^perp, not in C1, with c o C inside C + C1.  e = 1: m has a zero (above).
   e = 3 (C = w^perp cap 1^perp): w takes exactly two values, i.e. w ~ 1 - 5e_n [neutral column; then row i of N lies in C e_n] or
   w ~ (3,3,-2,-2,-2) [not excluded here; never seen].
   WHAT IS LEFT OF (NCOL_1): (4,1) spaces without single-row element (both known ones have a two-column defect line, 3 neutral
   columns) and isotropic m.  With verifyfl's (NS4') ["every (4,1) space with non-two-column m is split"], (NCOL_1) follows for
   all non-isotropic m.
 R4.15 FIRST-ORDER CONSTRAINTS FROM SINGLE-ROW ELEMENTS (RIGOROUS; same computation as R4.14, any e).  Let L' be a 4 x 5 level space,
   u in U_i (e_i u^T in L'), Y in L', c := c^(i)(Y) the column-sum vector of the three rows != i of Y.  Then D_i(Y) u is in C, and
   its degree-1 part -2S u + 4 c o u - 2 (c.u) 1 is in C inside 1^perp; pairing with 1 gives -6 (c.u) = 0. Hence
     (F1)  c^(i)(Y) . u = 0   and   c^(i)(Y) o u  in C        for all Y in L', u in U_i;
     (F2)  U_i o U_k inside C  for i != k   [take Y = e_k u'^T];  (with U_i perp U_k this is new information when e >= 2:
           for C = Cu + Cu' split over two rows, the five points (u_j, u'_j) lie on a conic (x - b)(y - a) = ab through 0);
     (FS-DEC) if one row carries C (U_i = C), the diagonal operators c^(i)(Y) o . preserve C for every Y in L'; if moreover C is
           nondegenerate and L' is extremal (d = e + 3), some c^(i)(Y) is not a multiple of 1 [N = ker gamma is 3-dim strongly level,
           N cap {row i = 0} has dim <= 2 by SL_3, row i of N is -c^(i)(Y), and it is never -1], so C is DECOMPOSABLE:
           C = sum over the blocks A of a partition of the columns into >= 2 blocks of (C cap V_A).
           e = 1: m has a zero (R4.14).  e = 3: C = V_A + V_B with (|A|,|B|) = (4,1) [neutral column] or (3,2) [not excluded, never seen].
           e = 2: C inside V_A with |A| = 4 [neutral column], or C = V_A (|A| = 3), or C = Cu + C(e_a - e_b), u in V_A, {a,b} = A^c.
   Numerical check (rows/uiuk_chk.py, 87 extremal spaces, 70 pairs (u,u') from different rows): (F2) to 1.3e-7, (F1) to 5e-6
   (LM-limited files; two files exceed only on vectors of norm 1e-6).
     (F1^T) transposed version for a NEUTRAL column n (notation R4.10): for x in X_n ((0|x) in L') and every Y = (q|x') in L':
           x . rho(q) = 0 (rho = row sums of q) and the row combination x^T q (a vector on the columns != n) lies in C.
           [C_j is linear in column n: (x . M^(j)(q))_{j != n} is in C; its degree-1 part is 2(x^T q)_j - 2 x.rho(q), and x.rho(q) = 0
           is the degree-1 part of x.(M(q) - 24*1) = 0.]   Checked: 96 (space, neutral column) pairs with X_n != 0, 711 tests, max rel.
           distance 3.3e-5 (attained on an LM-limited file).
STATUS 19:13 (round 4 final): Theorem NCOL-S (R4.14) and first-order constraints (R4.15, incl. (F1^T)) added; RESULT ROUND 4 at the top (U1-U9).
STATUS 19:16 (ROUND 5 started 19:14, budget 100 min -> ~20:54; targets: (NC_e) via 4x4, (NCOL_1) beyond split, (NCOL_2,3)).
STATUS 19:33: COMPUTE-rows.md written (heavy-computation requests H1-H6, exact systems X1-X3). Round 5 so far: Theorem NC-DC (slack identity), 4x4 searches, tower checks; write-up pending (section R5).
## Section R5 (round 5; started 19:14)
 Notation as in R4. For a 4 x 5 matrix Y: c(Y) in C^5 column sums, s(Y) in C^4 row sums. For L' with neutral column n: Y = (q | x), Q = {q}
 (level 4 x 4), rho(q), kappa(q) = row / column sums of q, X_n = {x : (0|x) in L'}, e^col(Q) = dim span{M(q) - 24*1} (row deletions of Q),
 e^row(Q) = dim span{R(q) - 24*1} (column deletions).  Q_dc := doubly centred part of Q (rho = kappa = 0); L'_dc likewise for L'.
 R5.1 THE EXACT 4 x 4 STATEMENT BEHIND (NC') (rigorous reformulation).  Put Adj(q)_ij := perm_3((J+q) minus row i, column j) (4 x 4;
   Adj(0) = 6J; M(q) = Adj(q) 1; R(q) = Adj(q)^T 1; 1^T Adj(q) 1 = 96 on a level Q).  With W_0 := {w in C^4 (columns != n) : w perp 1,
   w perp C(L')} (so W = W_0 + C(1 - 5e_n), dim W_0 = 3 - e) the lift is  L = {(q | x ; w_0)} + C e_r(1 - 5e_n)^T  and
        perm(J - E + [[q, x],[w_0, 0]]) = 120 + (1+x)^T Adj(q) w_0,      E := e_r(1 - 5e_n)^T.
   Hence: (L' level with neutral column n and W_0 perp C(L'))  <=>  Q level and  (1+x)^T Adj(q) wh = 24 (1.wh)  for all (q|x) in L' and
   all wh in C1 + W_0; in the UNTWISTED case (L' = (Q|0) + (0|X), X = X_n inside 1^perp) this reads: for Xh := C1 + X, Wh := C1 + W_0,
        (TRI)   Xh^T (Adj(q) - 6J) Wh = 0 for all q in Q     and the claim (NC') is     dim Q + dim Xh + dim Wh <= 8.
   Extreme cases: Q = 0 (trivial, 0 + 4 + 4) and Xh = Wh = C1 (then (TRI) is empty and the claim is the checked L_gct_214, 6 + 1 + 1).
   So (NC') is an interpolation between a triviality and L_gct_214; first order of (TRI): Xh^T q Wh = 0 (R4.15 (F1^T)).
 R5.2 THEOREM DC (rigorous, elementary).  (a) For every 4 x 5 level space:  dim L' = rank c + rank s + dim L'_dc,  rank c <= e (c(L') lies
   in C because p_1 = -6c), rank s <= 3.  So  dim L' <= e + 3 + dim L'_dc - (e - rank c) - (3 - rank s):  (DI_5) can only fail through
   DOUBLY CENTRED elements, and (DI_5) <=> "dim L'_dc <= (e - rank c) + (3 - rank s) for every 4 x 5 level space".
   (b) THEOREM NC'-DC. If column n is neutral:  dim L' = dim Q + dim X_n,  dim Q = rank rho + rank kappa + dim Q_dc,  rank rho <= e^col(Q)
   (M^(1) = -6 rho),  dim X_n <= 3 - e^col(Q) (R4.10),  rank kappa <= e (kappa(q) = c(Y) on the columns != n).  Hence the IDENTITY
        dim L' = e + 3 + delta - s1 - s2 - s3,   delta := dim Q_dc,  s1 := e^col(Q) - rank rho,  s2 := 3 - e^col(Q) - dim X_n,  s3 := e - rank kappa
   (all s_i >= 0), and (NC'_e) <=> (DC-COST): delta <= s1 + s2 + s3.  Consequences: (i) (NC') holds whenever Q has no nonzero doubly
   centred element; (ii) with the checked L_gct_216 (delta <= 3): every 4 x 5 level space with a neutral column has dim <= e + 6
   [and <= 7 by L_gct_215]; (iii) an (e+4,e) space with a neutral column contains Y = (q|x) with q != 0 doubly centred.
   Census (rows/slack_chk.py, 135 (space, neutral column) pairs of extremal spaces): the identity holds in every case; delta = 0 and
   s1 = s2 = s3 = 0 in 126; delta > 0 in 7 (delta = 1: 3, delta = 2: 4), paid by s3 alone (rank kappa < e: 5), s1 alone (1), s1 + s3 (1);
   s2 = 0 always (saturation dim X_n = 3 - e^col(Q)); 2 LM-limited files give an impossible e^col = 4 (rank artefact).
   So doubly centred elements DO occur in extremal towers, always paid exactly.
   What the three checked 4 x 4 theorems give: dim Q <= min(6, 5 + rank rho, 5 + rank kappa, 3 + rank rho + rank kappa) (214, 217, 217^T, 216);
   this proves (NC'_3) only for dim X_n = 0 and does not reach (DC-COST): (DC-COST) with X_n = 0 = W_0 IS L_gct_214.
 R5.3 (7,3) FROM (NCOL_3) AND A 4 x 4 STATEMENT (rigorous).  (DI_4x4): a 4 x 4 level space has dim Q <= e^col(Q) + 3.
   (a) (DI_4x4) is (DI_5) for 4 x 5 spaces with a ZERO column: (Q^T | 0) is level with defect dimension e^col(Q) (R4.10(c) computation).
   (b) (NCOL_3) + (DI_4x4) => no (7,3) space.  Proof: by C-UP a (7,3) space has a neutral column n; dim Q + dim X_n = 7 with
       dim X_n <= 3 - e^col(Q) gives dim Q >= e^col(Q) + 4.  QED.   [Equivalently: (7,3) follows from (NCOL_3) and the exclusion of (5,1),
       (6,2) for spaces with a zero column; for (6,2) and (5,1) themselves the same count gives only equality cases, see (DC-COST).]
   (c) (DI_4x4) needs: no (dim, e^col) = (5,1), (6,2).  (5,1) with a TWO-COLUMN defect line is excluded by TC5 (padding).  Since
       rank rho <= e^col, a (5,1) space has a row-centred part of dim >= 4 with row-deletion vectors in 24*1 + C mu.
   Numerical (rows/q44_search.py, calibrated; 4 x 4 via padding): (4,1) 9/17, (5,1) 0/14; (5,2) 2/10, (6,2) 0/15; ANY 6-dim 4 x 4 level
   space: 0/15 (the checked bound 6 may not be sharp; all Q of the census have dim <= 5).  Row-centred: (3,1) 14/16; (4,1) 1/34, and
   the one hit has the two-column defect line e_0 - e_1 (as in the 4 x 5 case, where verifyfl's (SL_m) fails exactly for two-column m).
 R5.4 TOWERS GO ON (numerical, rows/tower_chk.py): in all 120 (extremal space, neutral column) pairs the 4 x 4 space Q has again a
   deletable row or column (3 x 4 or 4 x 3 rest level): every known 7-dim level space is a tower 5x5 -> 4x5 -> 4x4 -> 3x4/4x3.
   PRINCIPAL CENSUS (rows/kc_chk.py): in 90 of 95 extremal spaces rank c = e and K = ker c is a 3-dim STRONGLY LEVEL space with
   s(K) = 1^perp (verifyfl's "principal" kind, for every e); exceptions: one column-centred (4,1) with two-column line, one (5,2)
   with e(K) = 1, three (6,3) with rank c < 3 (K of dim 4, 5).  In the principal case L'_dc = 0.
 R5.5 (NCOL_3), block pattern (3,2) (numerical, rows/fixC_search.py ... b32): defect space fixed = V_{012} + V_{34}: dim 5 found 2/9,
   dim 6: 0/30 (control with a neutral column: 4/19).  With R4.13 (generic C0: 0/46) and (FS-DEC): no sign of a (6,3) space
   without neutral column.
STATUS 19:39: section R5 (R5.1-R5.5) written: Theorem DC / NC-DC, (7,3) from (NCOL_3) + (DI_4x4), 4x4 searches, towers, principal census.
 R5.6 FIRST-ORDER LAW FOR SINGLE-COLUMN ELEMENTS IN ANY COLUMN (rigorous; generalises (F1^T), no neutrality assumed).
   (SC1) Let x e_n^T be in a 4 x 5 level space L' (x in C^4, sum x = 0). Then for every Y in L' (columns y_j, row sums s(Y)):
          <x, s(Y) - y_n> = 0      and      the vector (<x, y_j>)_{j != n}, with 0 at n, lies in C cap e_n^perp.
   Proof. C_j is linear in column n: C(Y + lam x e_n^T) - C(Y) = lam v(Y), v_n = 0, v_j = x.M^(j;n)(Y), M^(j;n)_i = perm_3((J+Y) minus row i,
   columns j, n); v(Y) lies in C. Degree 1: v^(1)_j = 2[<x,y_j> + <x,y_n> - <x,s>]; sum over j != n is 6[<x,y_n> - <x,s>] = 0 as C is in 1^perp. QED
   Consequence for e = 1: if m_n != 0 and x e_n^T is in L', then EVERY column j != n of EVERY Y in L' is orthogonal to x.
   Checked (rows/sc1_chk.py): 184 (space, column) pairs with single-column elements, 68 of them non-neutral columns, 1167 tests, max 6e-6.
 R5.7 THEOREM NCOL-P (rigorous; (NCOL_1) when the single-column elements span the row sums; NO hypothesis on m, isotropic allowed).
   Let L' be a 4 x 5 level space with defect space C m, dim L' >= 4, X_n := {x : x e_n^T in L'}. If sum_n X_n = 1^perp (in C^4), then
   m_n = 0 for some n with X_n != 0: L' has a neutral column carrying a single-column element.
   Proof. (1) K := sum_n X_n e_n^T is strongly level: P_k of a sum of single-column elements in distinct columns is multi-homogeneous in
   the pieces, each piece may be scaled inside L', so every multi-homogeneous part of P_k vanishes, and these parts are exactly the terms of
   the deletion polynomials. P_2 gives X_n perp X_n' (n != n'), so 1^perp = (+) X_n orthogonally, dim K = 3, s : K -> V := 1^perp bijective.
   (2) Isometries (zeros / verifyfl): for h in K write h_j = A_j s(h); polarising p_2 = 0 on K, B_j := 1 - 2A_j are isometries of V,
   sum_j A_j = 1.  Here A_j is the orthogonal projector onto X_j:  B_j x = x for x in X_n, j != n, and B_n x = -x.
   (3) Normal form (verifyfl PS, any m): N := L' cap ker s has dim >= 1 (L' = K + N); for Z in N, p_2(Z, h)_j = <s(h), B_j^T z_j^V> (z_j^V =
   component of column j in V; the 1-component is (c_j(Z)/4) 1, c(Z) = kappa m) must be a multiple of m_j for every s(h) in V, so
   z_j^V = m_j B_j f with one f = f(Z) in V.  f(Z) != 0 for Z != 0: otherwise Z = (kappa/4) 1 m^T with kappa != 0; the line C Z is level only
   if e_1(m) = .. = e_4(m) = 0, and then p_2(tZ)_j = 24 (t kappa/4)^2 m_j^2 must be proportional to m_j, i.e. m_j in {0, alpha} for all j,
   impossible with sum m = 0, m != 0.
   (4) Row sums of Z vanish: sum_j m_j B_j f = 0. Pair with x in X_n: sum_j m_j <f, B_j^{-1} x> = (sum_{j != n} m_j - m_n) <f,x> = -2 m_n <f,x>.
   So m_n <f, x> = 0 for all n and x in X_n. As f != 0 and the X_n span V, some <f,x> != 0, hence m_n = 0.  QED
   Coverage: of the 28 principal (4,1) examples, 15 have K spanned by single-column elements (types (1,1,1) and (2,1) below).
   The same pairing for any e: for Z in ker s and x in X_n: <z_n, x> = 0  (column n of every row-centred element is orthogonal to X_n).
 R5.8 STRUCTURE OF THE STRONGLY LEVEL KERNEL K = ker c IN THE 90 PRINCIPAL EXTREMAL SPACES (numerical):
   K is always supported on at most THREE columns; column ranks of K: (1,1,1): 21, (2,1): 30, (3): 9 [K spanned by single-column
   elements: 60], (3,2): 25, (2,2,1): 5 [exactly one single-column direction]; K has no single-row element; K ALWAYS contains a
   single-column element, and in every case some column carrying a single-column element of K is NEUTRAL (90/90).
   So the mechanism of (NCOL) in the principal case is: "a single-column element of the strongly level kernel sits in a neutral column".
   Proved: e = 1 with K spanned by single-column elements (R5.7); e = 1 split non-isotropic (R4.14).  Not proved: types (3,2), (2,2,1); e >= 2.
 R5.9 THEOREM NCOL-P3 (RIGOROUS; (NCOL_1) for principal spaces whose strongly level kernel lives on <= 3 columns; ANY m, isotropic allowed).
   Let L' be a 4 x 5 level space with defect space C m. Let K in L' be a 3-dim strongly level subspace with s(K) = V := 1^perp (in C^4)
   all of whose elements vanish outside three columns a, b, c, and let Z in L' have s(Z) = 0 and c(Z) = kappa m with kappa != 0.
   Then  m_a m_b m_c = 0.   If K vanishes outside two columns a, b:  m_a m_b = 0;  outside one column a:  m_a = 0.
   So every (4,1) space with K := ker c strongly level, s(K) = V and K on <= 3 columns has a NEUTRAL column, and it is an active column of K.
   Proof. (1) Isometries: h_j = A_j s(h) on K, B_j := 1 - 2A_j in O(V), sum_j B_j = 3 (polarised p_2 = 0 on K; zeros/verifyfl). Columns
   d, e outside {a,b,c}: A_d = A_e = 0, B_d = B_e = 1, hence  B_a + B_b + B_c = 1.
   (2) Normal form (R5.7 (3)): z_j = (kappa m_j/4) 1 + m_j B_j f, f in V; p_2(Z)_j = 2c_j^2 + 2<s - z_j, z_j> = m_j^2 [(3/2)kappa^2 - 2<f,f>]
   must be proportional to m_j, and (m_j^2)_j is not (sum m = 0), so  nu := <f,f> = (3/4) kappa^2 != 0.
   (3) Put g_j := B_j f (j = a,b,c):  <g_j,g_j> = nu,  g_a + g_b + g_c = f.  Row sums of Z: 0 = sum_j m_j B_j f = m_a g_a + m_b g_b + m_c g_c
   + (m_d + m_e) f, and m_d + m_e = -(m_a+m_b+m_c), so with (alpha,beta,gamma) := (m_b+m_c, m_a+m_c, m_a+m_b):
          alpha g_a + beta g_b + gamma g_c = 0.
   (4) Gram matrix: tau_j := <g_j, f>; from g_a+g_b+g_c = f: tau_a+tau_b+tau_c = nu and <g_a,g_b> = -tau_c, <g_a,g_c> = -tau_b, <g_b,g_c> = -tau_a.
   Pairing the relation with g_a, g_b, g_c:   beta tau_c + gamma tau_b = alpha nu,   alpha tau_c + gamma tau_a = beta nu,   alpha tau_b + beta tau_a = gamma nu.
   If alpha beta gamma != 0: tau_a = nu (beta^2+gamma^2-alpha^2)/(2 beta gamma) etc., and tau_a+tau_b+tau_c = nu becomes
   (alpha+beta-gamma)(alpha-beta+gamma)(-alpha+beta+gamma) = 0, i.e. 8 m_c m_b m_a = 0.  If alpha = 0 (say): gamma tau_a = beta nu, beta tau_a =
   gamma nu give beta gamma = 0 (then alpha = beta = gamma = 0 and m_a = m_b = m_c = 0) or tau_a = nu (beta = gamma: m_b = m_c, with alpha = 0:
   m_b = m_c = 0) or tau_a = -nu (beta = -gamma: m_a = 0).  In every case m_a m_b m_c = 0.
   Two columns: B_b = -B_a =: -B, the relation is (m_a - m_b) B f = (m_a + m_b) f; f is non-isotropic, so the eigenvalue is +-1 (m_b = 0 or
   m_a = 0), or m_a = m_b = 0.  One column: B_a = -1, -2 m_a f = 0.  QED
   Checked numerically on all 28 principal (4,1) spaces (rows/ncolp_chk.py, ncolp3_chk.py): normal form (3e-6), <f,f> = (3/4)kappa^2 (2e-11),
   sum B_j = 3 (1e-14), g_a+g_b+g_c = f (2e-9), the relation (6e-10), product of m over the active columns of K = 0 (1e-12).
   This contains R5.7 (K spanned by single-column elements has <= 3 active columns) and needs no classification of K.
   STATUS OF (NCOL_1): proved for (a) split non-isotropic m (R4.14); (b) principal K on <= 3 columns (this theorem) = 28 of the 30 known
   (4,1) spaces; the 2 others are column-centred with a two-column defect line (three neutral columns).  Still unproved: that a principal K
   always lives on <= 3 columns (true in 90/90 examples; exact problem X4 in COMPUTE-rows.md), and non-principal (4,1) spaces.
   For e >= 2 the same computation gives only: sum_{j in {a,b,c}} A_j F_j(Z) = 0 for the column data F(Z) in V (x) C of row-centred Z
   (the Gram argument needs F = f (x) u of rank one); open.
STATUS 19:47: Theorem NCOL-P3 (R5.9), (SC1) (R5.6), K-structure census (R5.8) written.
 R5.10 REMARKS ON PRINCIPAL (5,1) SPACES (rigorous, partial; for verifyfl's N-problem).  Setting of R5.9 with N := L' cap ker s of dim 2
   (L' = K + N a (5,1) space), K on columns a, b, c.  Row sums of Z in N:  sum_j m_j A_j f(Z) = 0, i.e. with P := f(N) (2-dim, the form
   <,> has rank 1 on P by <f(Z),f(Z')> = (3/4) kappa(Z) kappa(Z')):   (m_a A_a + m_b A_b + m_c A_c) p = 0 for all p in P.
   By R5.9 one of m_a, m_b, m_c vanishes, say m_c = 0. If also m_a m_b (m_a + m_b) != 0, then A_b = -(m_a/m_b) A_a on P, and the isometry
   identities <p,A_j p'> + <A_j p,p'> = 2<A_j p,A_j p'> for j = a, b give <A_a p, A_a p'> = 0 on P: A_a(P) is totally isotropic, so A_a has rank
   <= 1 on P and there is p_0 != 0 in P with A_a p_0 = A_b p_0 = 0, A_c p_0 = p_0:  K CONTAINS THE SINGLE-COLUMN ELEMENT p_0 e_c^T IN THE
   NEUTRAL COLUMN c, with p_0 in f(N).  Every Z in N has zero column c, and the element Z_* of N with kappa = 0 is (q_*|0) with q_* a
   DOUBLY CENTRED 4 x 4 matrix whose columns m_j B_j f_* are all isotropic (this is the doubly centred element forced by R5.2(b)(iii)).
   Remaining sub-cases: m_a = 0 as well (then A_b = 0 on P), m_b = -m_a (then A_b = A_a on P).  Not finished: the cubic and quartic conditions.
 R5.11 THEOREM P51 (RIGOROUS): NO (5,1) SPACE OF THE TWO MAIN PRINCIPAL TYPES WHEN m HAS FIVE DISTINCT ENTRIES.
   Let L' be a 4 x 5 level space with defect line C m, all five entries of m pairwise distinct (so at most one zero), and K in L' a 3-dim
   strongly level subspace with s(K) = V = 1^perp.  Put N := L' cap ker s (L' = K + N).
   (i)  If K is spanned by single-column elements (K = (+)_n X_n e_n^T), then dim L' <= 4, and if dim L' = 4 then L' is split:
        N = C e_i m^T for some row i.
   (ii) If K lives on two columns a, b and dim N >= 2, then K is the full free column F_a or F_b; so by (i) dim N >= 2 is impossible.
   Hence there is no (5,1) space with such a K of column-rank type (1,1,1), (2,1), (3) or (3,2).  [Left: type (2,2,1), where the same
   computation gives N inside {a m^T + t n(e_a - e_b)^T}, n isotropic; not finished.  Isotropic m is allowed here; e.g. (1,w,w^2,0,0) has
   a repeated entry and is NOT covered.]
   Proof of (i). Notation of R5.7/R5.9: A_j = orthogonal projector onto X_j, V = (+) X_j. For Z in N, sum_j m_j A_j f = 0 splits into
   m_j A_j f = 0 for each j, so B_j f = f whenever m_j != 0 and  Z = a m^T  with a = (kappa/4) 1 + f (RANK ONE);  f != 0 for Z != 0.
   Let x be in X_n and j != n. C_j is linear in column n, and the cofactors are 3 x 3 permanents of J + a m^T:
        d/d eps C_j(a m^T + eps x e_n^T) = sum_{k=0}^{3} (3-k)! k! <x, E_k(a)> e_k(m^(j,n)),     E_k(a)_i := e_k(a without a_i),
   m^(j,n) := m without the entries j, n   [checked numerically to 3e-13].  As a vector over j (0 at n) it lies in C m cap e_n^perp.
   Here e_1(m^(j,n)) = -(m_j + m_n), e_2(m^(j,n)) = e_2(m^(n)) + m_j(m_j + m_n) =: q_2(m_j), e_3(m^(j,n)) = e_3(m^(n)) - m_j q_2(m_j) =: q_3(m_j)
   are polynomials in m_j of exact degrees 1, 2, 3, and <x,E_1(a)> = -<x,f>.
   If m_n != 0: <x,f> = 0 and the vector must vanish: 2<x,E_2> q_2(m_j) + 6<x,E_3> q_3(m_j) = 0 at the four distinct points m_j (j != n).
   If m_n = 0: it equals lam m_j at the four distinct points: a polynomial of degree <= 3 in m_j with four roots.
   In both cases <x,E_2(a)> = <x,E_3(a)> = 0. The X_n span V, so E_2(a) and E_3(a) are multiples of 1:
        a_i (kappa - a_i) = t for all i,   and   a_i (e_2(a) - t) is independent of i      (kappa = sum a_i).
   So the a_i take at most two values alpha, beta with alpha + beta = kappa; a constant vector gives f = 0; multiplicities (3,1) give
   alpha = 0, a = kappa e_i; multiplicities (2,2) give kappa = 0 and e_2(a) = -2 alpha^2 = t = -alpha^2, a = 0.  Hence a(Z) is a multiple
   of a unit vector for every Z in N; a is linear and injective on N, so dim N <= 1 and N = C e_i m^T.  QED (i)
   Proof of (ii). B_b = -B_a =: -B; the row-sum relation on P := f(N) is (m_a + m_b) p = (m_a - m_b) B p; m_a != m_b, so B = lam on P.
   P is 2-dim with a form of rank 1 (<f(Z),f(Z')> = (3/4) kappa kappa', kappa not identically 0), so P = n^perp for an isotropic n; P contains
   non-isotropic vectors, so lam = +-1; an isometry of V that is +-1 on n^perp is +-1 on V. So B = 1 (A_a = 0, K = F_b) or B = -1 (K = F_a).  QED
   Consequences: (a) every (4,1) space whose single-column elements have row sums spanning 1^perp and whose m has distinct entries
   is SPLIT (consistent with the census); (b) for the principal (5,1) problem with distinct entries only the kernel type (2,2,1)
   (and kernels on 4 or 5 columns, never seen) remain.  This is consistent with verifyfl's numerics (R4.7: no solution of the
   N-problem for distinct entries, solutions only for repeated entries).
STATUS 19:55: R5.10, R5.11 (Theorem P51) written.
 R5.12 (R-LAW): ROW-CENTRED ELEMENTS HAVE THEIR ROWS IN THE DEFECT SPACE.
   Numerical (all 90 principal extremal spaces, every kernel type, e = 1, 2, 3; max relative distance 1e-12): every Z in N = L' cap ker s
   has ALL ITS ROWS in C, i.e. N lies in C^4 (x) C, equivalently Z w = 0 for all w in W = (C + C1)^perp (so column n of Z vanishes for every
   neutral n).  For e = 1 all 28 principal (4,1) spaces have N = C e_i m^T (rank one, split).  N is spanned by single-row elements in 74 of
   the 90 (this is the "row-split" phenomenon of R4.4), not always.  It FAILS in the non-principal extremal spaces.
   Rigorous part (any e): if K is spanned by single-column elements (A_j orthogonal projectors onto X_j), then for Z in N with c(Z) = u:
   z_j = (u_j/4) 1 + B_j F_j with (F_j) in V (x) C (normal form R5.7(3) for general e: (<sigma, B_j^T z_j^V>)_j lies in C for all sigma),
   the row sums give sum_j A_j F_j = 0, hence A_j F_j = 0 and B_j F_j = F_j for every j:  Z = (1/4) 1 u^T + F  with F in V (x) C.  QED
   For the other kernel types the law is equivalent to: sum_j w_j <z_j, h_j> = 0 for all h in K, w in C^perp (not proved).
   Use: with (R-LAW) an extremal principal space is L' = K (+) N, K strongly level on <= 3 columns, N an e-dim subspace of C^4 (x) C mapped
   isomorphically onto C by the column sums; an (e+4,e) space of this kind would have N of dim e+1 inside C^4 (x) C with a doubly centred
   element of rank <= e whose rows lie in C.
STATUS 19:59: R5.12 (R-LAW) written.
 R5.13 PROPOSITION NCOL2-P (rigorous, partial (NCOL_2); kernel spanned by single-column elements, C "square-generic").
   Let L' be a 4 x 5 level space with dim C = 2 whose single-column elements have row sums spanning V (K = (+) X_n e_n^T as in R5.7) and
   such that the column sums map N = L' cap ker s ONTO C (e.g. a principal (5,2) space).  Assume
        (G)  the classes of u1 o u1, u1 o u2, u2 o u2 (entrywise products, u1, u2 a basis of C) are linearly independent modulo C.
   Then some column n with X_n != 0 is neutral.
   Proof. Suppose not. By R5.12, Z_u = (1/4) 1 u^T + F(u), F(u) in V (x) C, F_n(u) perp X_n. By (SC1) (R5.6), for x in X_n the row vector
   x^T F(u) = (<x, z_j>)_j lies in C cap e_n^perp, a LINE C u^(n) (n is not neutral). As V = (+) X_n orthogonally,
        F(u) = sum_n xi_n(u) (x) u^(n),     xi_n : C -> X_n linear.
   Degree 2 of the defect: p_2(Z_u)_j = (3/2) u_j^2 - 2 <F_j,F_j> = (3/2) u_j^2 - 2 sum_n <xi_n(u),xi_n(u)> (u^(n)_j)^2 is a vector of C. By (G):
        (3/4) u (x) u = sum_n nu_n(u) u^(n) (x) u^(n)   in Sym^2 C,    nu_n(u) := <xi_n(u), xi_n(u)>,   for all u in C.
   The squares u (x) u span the 3-dim space Sym^2 C, so at least three columns are active with pairwise independent u^(n): the kernel
   has type (1,1,1), each X_n is a line and nu_n(u) = l_n(u)^2 <x_n,x_n> is the SQUARE of a linear form.  But in the basis
   u^(a) (x) u^(a), u^(b) (x) u^(b), u^(c) (x) u^(c) of Sym^2 C the coefficients of u (x) u are products of two INDEPENDENT linear forms
   (for u = alpha u^(a) + beta u^(b), u^(c) = g_a u^(a) + g_b u^(b): the coefficient of u^(c) (x) u^(c) is alpha beta/(g_a g_b)).  Contradiction.  QED
   Scope: (G) FAILS for the defect planes of the known (5,2) spaces (e.g. u o u' in C by (F2), or C = V_S), so this does not prove (NCOL_2);
   it shows that a (5,2) space of this kernel type without neutral column needs a relation between C o C and C.  The same argument for
   e = 1 is R5.7 (C cap e_n^perp = 0 forces F = 0).
STATUS 20:00: R5.13 written.  Round 5 final: see RESULT ROUND 5 at the top.
STATUS 20:04 (ROUND 6 started 20:04, about 2 h -> ~22:04; targets: (1) principal K on <= 3 columns by hand, (2) non-principal (4,1) and (5,1) strata, (3) (DC-COST), (4) (R-LAW)).
STATUS 20:22: target (1) by hand not finished; reduction to strongly level PLANES (claims (A),(B)) + generator rows/gb/x4gen.py written, queued in COMPUTE-rows.md "NEW (round 6)"; local Groebner runs of A4 too slow (>100 s). Numerics: planes with injective row sums: <= 3 columns in 169/169; single strongly level matrices with 4 columns exist.
## Section R6 (round 6, 20:04 - 20:35; stopped early on the coordinator's instruction; nothing here is verified by verify2)
 R6.1 REDUCTION OF X4 TO PLANES [rigorous]. If a principal K (3-dim strongly level, s(K) = V) has >= 4 nonzero columns, a generic 2-dim
   subspace is a strongly level plane with the same nonzero columns and injective row sums. So "K lives on <= 3 columns" follows from
        (PL)  a strongly level plane {s h + t h'} with s(h), s(h') independent has at most three nonzero columns.
   The single-matrix analogue is FALSE [numerical]: strongly level matrices with 4 nonzero columns are common (rows/sle_d1_s*.npy) and
   one with 5 nonzero columns exists (rows/sle5_s1005.npy, error 2e-16).  Evidence for (PL) [numerical]: 45 + 124 strongly level planes
   with injective row sums, all on 2 or 3 columns (types (2,2), (1,1,1), (2,2,1)); 128 strongly level 3-spaces with one column forced
   to zero, all on <= 3 columns; the only plane on 4 columns found has row-sum rank 1.  Exact formulation and generator: COMPUTE-rows.md
   "NEW (round 6)", rows/gb/x4gen.py (cases B, C; calibrations A4, B3).  Local Groebner runs of the calibration A4 did not finish in 100 s.
 R6.2 ROW-WISE FORM OF "STRONGLY LEVEL" [rigorous, derived by hand; (S4) NOT yet checked numerically].  For a column-centred 4 x 5 matrix h
   with rows rho_i, columns h_a, Gram g_ab = <h_a,h_b>, rho_i^(j) := row i without entry j:   P_2 = -sum_i e_2(rho_i), P_3 = 2 sum_i e_3(rho_i).
   h strongly level  <=>  column sums 0 and for every j:
        sum_i e_2(rho_i^(j)) = 0,   sum_i e_3(rho_i^(j)) = 0,   6 sum_i prod_{a != j} h_ia = g_ab g_cd + g_ac g_bd + g_ad g_bc  ({a,b,c,d} = [5] - j);
   equivalently (S2_j) <s - h_j, h_j> = 0, (S3_j) sum_i h_ij e_2(rho_i^(j)) = 0, (S4_j) 6 sum_i h_ij e_3(rho_i^(j)) = sum_{a != j} g_aj^2.
   (perm_4 of four sum-zero vectors = sum of the three pairings - 6 sum_i x_i y_i z_w w_i.)  Consequences: a principal K on three columns
   a,b,c  <=>  B_a + B_b + B_c = 1 and sum_i (h_a h_b h_c)_i = 0 on K; its columns are pairwise orthogonal.  On four columns the Gram
   matrix has g_12 = g_34, g_13 = g_24, g_14 = g_23 with sum 0 (seen in all 4-column examples) and all four triple products vanish.
   In Walsh coordinates the triple product is 4 perm_3 of the coordinate vectors.
 R6.3 REMARKS [rigorous unless said]. (i) ERRATUM to R5.3(b): "(NCOL_3) + (DI_4x4) => no (7,3)" also needs no (5,1), no (6,2) (C-UP uses
   the induction hypothesis).  (ii) If ker c is 3-dimensional then dim L' = 3 + rank c <= e + 3: spaces with a 3-dim column-centred part
   satisfy (DI_5) trivially; the problem lives in ker c of dim >= 4.  (iii) (PRIN): "every extremal (e+3,e) space with rank c = e has a
   strongly level ker c" would exclude every (e+4,e) space with rank c = e (its 4-dim ker c would be strongly level, against SL); this is
   verifyfl's (K4) argument for all e.  [numerical] (PRIN) holds in 90 of the 95 extremal examples with rank c = e ... but FAILS for
   rows/clm_p4_d5_defect2_s9.npy (a (5,2) space with rank c = 2 and e(ker c) = 1).  (iv) Non-principal (4,1) with ker c = K strongly level
   of row-sum rank q < 3: Theorem DC forces rank s(L') = q and L'_dc = K_dc; for K = chi (x) C^S (zeros' R3, chi = (1,i,-1,-i), |S| = 3)
   and m not two-column the quadratic conditions give <chi, z_j> = 0 for every column of the row-centred generator Z [by hand, unchecked].
STATUS 20:33 (round 6 closed): handover written to handover/HANDOVER-rows.md.

# ROUND 7 (start 19:45 UTC on Kevin's 24-core machine; all STATUS times from here on are UTC). Targets: (1) R6-1: what B and C must
#  establish now that (A) is false, calibration logic, interpret Singular results, cheaper charts / reductions; (2) repair DC / NC'-DC
#  in inequality form and restate what (DI_5) still needs; (3) R-X5 (principal (5,1), kernel type (2,2,1)) and next handover items.
#  Housekeeping: handover/HANDOVER-rows.md was missing from the workspace; restored from coord-L-gct-210/cloud/L-gct-210 (my own file).
STATUS 19:47: round 7 started; read TEAM-RULES, BRIEF (UPDATE 11), handover, R5/R6, COMPUTE-rows, errata, RUNS (R6-1 A4/B/B3/C running ~20 min, no output yet).
## Section R7 (round 7)
 R7.2 REPAIR OF THEOREM DC / NC'-DC (rigorous; replaces R5.2 "=" statements; verify2's counterexample C(e_0 u^T + (e_1-e_2) e_0^T) checked:
   rank c = 1, ker c = 0, so rank(s|ker c) = 0 although rank s = 1).
   (a) THEOREM DC' (exact identity). For every 4 x 5 level space L', with c = column-sum map (image in C, so rank c <= e), s = row-sum map
       (image in V = 1^perp of C^4 because P_1 = 0), L'_dc := ker c cap ker s:
            dim L' = rank c + rank(s|ker c) + dim L'_dc        (rank-nullity twice: ker c -> V has kernel L'_dc).
       Hence the EXACT equivalence   (DI_5) for L'  <=>  dim L'_dc <= (e - rank c) + (3 - rank(s|ker c)).
       The old form with rank s is an inequality: dim L' <= rank c + rank s + dim L'_dc; the statement "(DI_5) <=> dim L'_dc <= (e - rank c)
       + (3 - rank s)" is only "<=" (the right-hand side is the stronger condition). Symmetric identity: dim L' = rank s + rank(c|ker s) + dim L'_dc.
       Unchanged consequences: dim L' <= e + 3 + dim L'_dc; an (e+4, e) space has dim L'_dc >= 1 + (e - rank c) + (3 - rank(s|ker c)) >= 1.
   (b) THEOREM NC'-DC' (exact identity). Column n neutral, Y = (q|x), Q = {q} (level 4x4), X_n = {x : (0|x) in L'}, rho / kappa = row / column
       sums of q, Q_dc = ker rho cap ker kappa, delta := dim Q_dc:
            dim L' = dim Q + dim X_n,     dim Q = rank rho + rank(kappa|ker rho) + delta,
       rank rho <= e^col(Q) (M^(1) = -6 rho), dim X_n <= 3 - e^col(Q) (R4.10, verified), rank(kappa|ker rho) <= rank kappa = rank c <= e
       (kappa(q) = c(Y) minus its n-th entry, and c(Y)_n = 0 since C is in e_n^perp). Hence the IDENTITY
            dim L' = e + 3 + delta - s1 - s2 - s3',   s1 = e^col(Q) - rank rho,  s2 = 3 - e^col(Q) - dim X_n,  s3' := e - rank(kappa|ker rho),
       all >= 0, and s3' >= s3 := e - rank kappa (the R5.2 slack).  EXACT:  (NC'_e) for L'  <=>  (DC-COST')  delta <= s1 + s2 + s3'.
       The R5.2 condition (DC-COST) delta <= s1 + s2 + s3 implies (DC-COST') (sufficient, NOT necessary).  The census line "identity holds in
       every case" (slack_chk.py, which used rank kappa) therefore also says rank(kappa|ker rho) = rank kappa in all 135 tower positions.
       Unchanged consequences: (NC'_e) whenever Q_dc = 0; dim L' <= e + 6 via L_gct_216; an (e+4,e) space with a neutral column has delta =
       1 + s1 + s2 + s3' >= 1, i.e. Q contains a nonzero doubly centred q.
   (c) CORRECTED CHAIN (what (DI_5) still needs, exactly).  Write (DI_5;k) := "no (e+4,e) space for e < k" ((DI_5;1) = Lemma SL, proved).
       For e = 1, 2, 3 in turn, assuming (DI_5;e):
         HYPERPLANE LEMMA (R4.1, verified): every hyperplane H of an (e+4,e) space L' is an (e+3,e) space with C(H) = C(L').
         C-UP step: if ONE hyperplane H has a neutral column n then C(L') = C(H) is in e_n^perp, so n is neutral for L'.
         Then (NC'_e) <=> (DC-COST') closes the case.
       So   (DI_5;e) + (NCOL_e for SOME hyperplane of each putative (e+4,e) space) + (DC-COST' for (e+4,e) spaces with a neutral column)
            ==> (DI_5;e+1).
       The freedom "SOME hyperplane" matters: a (5,1) space with rank c = 1 has 4-dim ker c, its GENERIC hyperplane is NON-principal
       (otherwise every 3-dim subspace of ker c is strongly level, so ker c is, against SL), but if ker c CONTAINS a strongly level 3-space
       K with s(K) = V (verifyfl's principal (5,1)), the hyperplane H = K + C Y_1 (c(Y_1) != 0) is principal with ker c|H = K, and
       NCOL-P3 applies to H as soon as K lives on <= 3 columns ((PL), R6-1).
       R5.3(b) corrected (verify2): (DI_5;3) + (NCOL_3) + (DI_4x4) ==> no (7,3).  For (5,1), (6,2) the count with (DI_4x4) gives only the
       equality case dim L' <= 6, so (DC-COST') is genuinely needed there.
STATUS 20:12: R7.2 (DC/NC'-DC repair, exact identities with rank(s|ker c), rank(kappa|ker rho)) written. X5 DONE: unit over Q in all 4 charts (after sat by <n,n'>), also mod 3 primes; calibration (N a line) non-unit; confirming a calibration point with oracle. R6-1 chart 0000 of B: msolve > 5 min (heavy).
 R7.1 R6-1 AFTER THE FALL OF CLAIM (A): WHAT B AND C MUST SHOW, CALIBRATION LOGIC, COST, CHEAPER ROUTES.
   (a) What is needed now [rigorous reduction R6.1, unchanged]:  (PL) "a strongly level PLANE with injective row sums has <= 3 nonzero
       columns" follows from  B (no such plane with exactly 4 nonzero columns)  AND  C (none with 5 nonzero columns).  (A) (single matrices)
       is no longer used: a principal K with 5 nonzero columns contains a C-plane (generic 2-dim subspace), one with exactly 4 contains a
       B-plane.  (PL) => every principal K (3-dim strongly level, s(K) = V) lives on <= 3 columns => NCOL-P3 unconditional for principal
       (4,1) spaces, and (via C-UP, R7.2(c)) a principal (5,1) space has a neutral column.
       Chart of B and C (row sums (1,0,u), (0,1,v) in Walsh coordinates) is complete: a 2-plane of V contains at most two Walsh axes and
       row permutations permute the Walsh axes (signed permutations, even number of signs). Column permutations: the active set can be
       taken to be {0,1,2,3} (B) resp. all five (C).
   (b) Calibration logic.  A4 (single matrix, 4 columns) MUST be non-unit: NEW [numerical, rows/r7/s4num.py, s4b.py] the variety S_4 of
       single strongly level matrices on exactly four columns is a 4-dimensional affine cone: 15 of 16 LM starts with one normalisation per
       column end on points with four nonzero columns (residual 1e-13), tangent dimension 4 at every point (clear singular-value gap
       4.0 | 1e-6), Gram pattern g01 = g23, g02 = g13, g03 = g12 confirmed.  (The 9 defining equations are not a complete intersection:
       codim 8.)  So B asks for LINES on a projective 3-fold P(S_4) in P^11 (Gr(2,12) has dim 20 = B's unknown count; B imposes 33
       conditions).  A4 tests the 4-column saturation machinery on single matrices; B3 (planes on 3 columns: (1,1,1) and (2,2,1) planes,
       4-dim families) is the same-shape calibration for B and must be non-unit; A (5 columns, single matrices: rows/sle5_s1005.npy) must be
       non-unit and calibrates C's saturation.  There is NO known same-shape positive control for C (a 5-column plane with injective row
       sums is exactly what C claims impossible).  Decision rule (unchanged): B unit and C unit at >= 3 primes with A4, B3 non-unit at the
       same primes => (PL) [modular EVIDENCE: affine chart + saturation, so not a proof even at one prime; a proof needs the computation
       over Q or a projective formulation without saturation].  If B or C is non-unit: extract a point (or a primary component), check it
       with handoff/oracle.py on the plane; a genuine plane on >= 4 columns would refute (PL) and leave NCOL-P3 conditional.
   (c) Cost.  Local test: msolve on B in the Rabinowitsch chart 0000 (one coordinate of each active column inverted; x4gen.py chart
       option) did NOT finish in 5 min with 2 threads (rows/r7/Bc0000.*).  The coordinator's Singular runs of A4, B, B3 (std(I) before any
       saturation) had printed nothing after ~50 min.  So the stated formulation is heavy; the bottleneck is the positive-dimensional
       degenerate part (planes on <= 3 columns: 4- and 5-dim families) that saturation / localisation must remove.
   (d) Cheaper routes (queued, see QUEUE.md lines "rows | R7-...").
       (d1) Full chart cover of B with symmetry reduction: a solution with four nonzero columns has some nonzero coordinate k_j in every
            column; the solution set is invariant under the S_4 of active columns, which permutes chart strings, so the 126 MULTISETS
            {k_0..k_3} in {0..5} suffice (sign changes of Walsh coordinates fix every chart).  msolve, 1 core per chart.  Unit in all 126 at
            3 primes => B [modular].  (The single random chart rrrr is a randomised certificate only.)
       (d2) The 3-dim K version directly (X4 restricted to NC = 4 or 5 active columns; generator rows/r7/t3/x4k.py P NC OUT): 27 resp. 36
            unknowns but far more equations (24 + 40 + 15 coefficient equations for NC = 4); calibration NC = 3 (non-unit).  This is
            all that NCOL-P3 needs (planes were only a device to shrink the system), and over-determination may make the Groebner basis
            collapse faster than for B.
       (d3) [numerical first] rows/r7/s4lines.py: lines through sampled points of S_4 (direction h' with all mixed coefficients zero).
 R7.3 THEOREM X5 [exact: Groebner bases over Q in Singular 4.3.2, four charts covering P^1 x P^1; also unit mod 2147483629, 2147483497,
   2147483077; normal form checked numerically; calibration confirmed by handoff/oracle.py].
   STATEMENT. There is NO (5,1) space L' (any defect line C m) containing a 3-dim strongly level K with s(K) = V whose column ranks are
   (2,2,1) (K on three columns a, b, c with rank A_a = rank A_b = 2, rank A_c = 1).  [Uses VF-A and TC5 for the sub-case
   m_a = m_b = 0 of step (2); without them: no such space with (m_a, m_b) != (0, 0).]
   PROOF.  (1) Structure of K [rigorous, by hand]: A_c has rank 1 and B_c = 1 - 2A_c is orthogonal, so A_c is the orthogonal projector onto
   a NON-isotropic line C v (for A = x y^T: y (x.x) y^T = (x y^T + y x^T)/2 forces x || y, x.x != 0).  From B_a + B_b + B_c = 1 (R5.9):
   B_a + B_b = 2P_v.  Put g = B_a v; |g|^2 = |2v - g|^2 = |v|^2 gives <v,g> = |v|^2, so w := g - v is isotropic and lies in v^perp.
   For y in v^perp: B_a y = -B_b y and, B_a, B_b being isometries, <B_a y, v + w> = 0 = <B_a y, v - w>, so B_a(v^perp) is inside
   v^perp cap w^perp; this is 2-dimensional only if w = 0.  Hence B_a v = B_b v = v, B_a = R and B_b = -R on v^perp with R in O(v^perp);
   rank A_a = rank A_b = 2 forces R to be a ROTATION with eigenvalues lam, 1/lam on the two isotropic lines n, n' of v^perp, lam != +-1.
   [Byproduct: a 3-column K with a rank-one column is of type (1,1,1) (R a reflection) or (2,2,1) (R a rotation != +-1), or lives on
   two columns (R = +-1).]  So K = span{ v e_c^T, n((1-lam)e_a + (1+lam)e_b)^T, n'((1-1/lam)e_a + (1+1/lam)e_b)^T }.
   (2) Row-centred part [rigorous; R5.7(3), R5.9(2), verified by verify2]: L' = K (+) N, N = L' cap ker s, dim N = 2; Z in N has
   z_j = (kappa m_j/4) 1 + m_j B_j f, <f,f> = (3/4) kappa^2, and the row sums give m_c phi = 0 and (m_a - m_b) R p = (m_a + m_b) p for
   f = phi v + p (p in v^perp).  If m_c != 0 then f(N) lies in v^perp and is 2-dim; if m_a != m_b this makes R scalar (= +-1): excluded;
   if m_a = m_b != 0 then p = 0, impossible; if m_a = m_b = 0 then supp m is inside {c,d,e}, |supp m| <= 3, and this sub-case is
   EXCLUDED BY VF-A (verified theorem: no principal (5,1) for |supp m| = 3) and TC5 (|supp m| = 2) -- not by this argument.  So m_c = 0.
   f is injective on N (f(Z) = 0 => kappa = 0 => Z = 0), so f(N) is 2-dim; it is inside C v + (lam'-eigenspace of R) with
   lam' = (m_a+m_b)/(m_a-m_b), so lam' must be an eigenvalue of R (name n its eigenvector: lam' = lam) and then m_a, m_b != 0, m_a != m_b
   (m_a = m_b = m_c = 0 is a two-column m, excluded by TC5; if m_a = m_b != 0 or lam' not an eigenvalue, dim f(N) <= 1).  This gives
   COMPUTE-rows X5 exactly: N = {A m^T + t n (e_a - e_b)^T}, A = (kappa/4)1 + phi v + eta n, kappa = kc*phi, kc^2 = (4/3)<v,v>,
   t = m_a (lam - 1) eta, lam (m_a - m_b) = m_a + m_b.  No hypothesis on the entries of m beyond the ones forced here.
   (3) Computation (rows/r7/x5/x5gen.py; scripts x5Q_*.sing, outputs x5Q_*.out over Q, x5_CH_P.out mod p): columns (a,b,c,d,e) =
   (0,1,2,3,4), m = (1, mb, 0, md, -1-mb-md) (m_a != 0 allows m_a = 1), n = Walsh(a1^2-a2^2, i(a1^2+a2^2), 2 a1 a2), n' likewise
   with (b1,b2) [this parametrises the isotropic conic bijectively; i is a variable with i^2 = -1, so both conjugates are covered],
   v = n x n' (Walsh cross product; <v,v> = -4 <n,n'>_W^2 up to the factor of the Walsh form, so v non-isotropic <=> <n,n'> != 0),
   lam*mu = 1.  Equations: every (s1,s2,s3,phi,eta)-coefficient of C_j(Y) - 24 - m_j (C_0(Y) - 24), j = 1..4, for
   Y = s1 K1 + s2 K2 + s3 K3 + Z(phi,eta), plus the relations above; charts (a2 = 1 | a1 = 1, a2 = 0) x (b2 = 1 | b1 = 1, b2 = 0).
   RESULT: over Q, charts 01 and 10 give the unit ideal outright; charts 11 and 00 give a 1-dim ideal containing a1 - b1 resp.
   n = n' (so <n,n'> = 0, v = 0), and the saturation by <n,n'> is the unit ideal.  Same at three primes.  Since (1) and (2) show that
   every (5,1) space of this kind is a point of this system with <n,n'> != 0, none exists.  QED
   CHECKS: (i) rows/r7/x5/nfcheck.py: for random parameters satisfying only the relations, the degree-1 and degree-2 parts of
   C(Y) - 24*1 lie in C m to 1e-10 (relative), degrees 3 and 4 do not: the system imposes exactly the cubic and quartic conditions.
   (ii) Calibration (same generator, N replaced by the LINE {Z(phi, r phi)}, i.e. a (4,1)-type system): NON-unit after the same
   saturation (dim 2 in chart 11, dim 1 in chart 10, at p = 2147483629; chart-10 solutions have m_b = 0, lam = 1); a numerical point
   (rows/r7/x5/x5cal10_point_4.npy, from calpt10.py) is confirmed by handoff/oracle.py as a (4,1) space, level error 1.5e-13, lift of
   dim 7 with level error 1.8e-12.  So the generator produces genuine level spaces where they exist.
   CONSEQUENCE (with P51, verified, and VF-A, verified): for m with five distinct entries there is no principal (5,1) space whose kernel
   K is of column type (1,1,1), (2,1), (3), (3,2) [P51] or (2,2,1) [X5].  Remaining for principal (5,1) with distinct entries:
   (PL) (K on >= 4 columns) and 3-column kernels with ALL column ranks >= 2 (never observed; exact check t3gen.py running/queued).
   For repeated entries: types (1,1,1), (2,1), (3), (3,2) with repeated nonzero entries of m remain (handover item 2 (ii)); (2,2,1) is
   done for every m.
STATUS 20:26: R7.1 (R6-1 analysis) and R7.3 (Theorem X5, exact over Q) written; running exact 3-column type check (t3) and S_4 line search.
 R7.4 THEOREM PR5 (principal (5,1) spaces, ANY m) [hand + exact over Q; rows/r7/rep/x51r.py; outputs: run log in this STATUS block].
   STATEMENT. Let L' be a (5,1) space containing a 3-dim strongly level K with s(K) = V (verifyfl's "principal").  Then K lives on at
   least four columns, or on exactly three columns with ALL three column ranks >= 2.  [Uses VF-A and TC5 (verified) for |supp m| <= 3.]
   So: no principal (5,1) space at all  <=  (PL) [R6-1: B and C, now queued as R7-B2, R7-C2]  +  (T3) "every 3-column K has a column of
   rank <= 1" [queued in R7-X4K; never violated numerically].
   PROOF.  Normal form (R5.7(3), R5.9(2), verified): L' = K (+) N, dim N = 2, z_j = (kappa m_j/4)1 + m_j B_j f, f injective on N,
   <f,f> = (3/4) kappa^2, kappa not identically 0 on N (else f(N) would be a 2-dim totally isotropic subspace of the 3-dim V), row sums
   sum_j m_j B_j f = 0.  Types of K on <= 3 columns:
   (i) ONE column, K = F_a (A_a = 1, B_a = -1): row sums give -2 m_a f = 0, so m_a = 0, and Z = a m^T with a = (kappa/4)1 + f (rank one).
   (ii) TWO columns a, b: B_b = -B_a =: -B (B in O(3), possibly non-diagonalisable).  Row sums: (m_a - m_b) B p = (m_a + m_b) p on
       P = f(N).  If m_a = m_b then m_a = m_b = 0 and supp m is in {c,d,e}: VF-A / TC5.  Otherwise B is a scalar lam' on the 2-dim P,
       which contains non-isotropic vectors, so lam' = +-1 and B = +-1 on P; then B = +-1 (P degenerate: the argument of P51(ii)) or B is
       +-(a reflection) (P nondegenerate: B preserves the line P^perp).  B = +-1 is case (i); B = +-reflection is type (2,1) (up to swapping a, b): A_a = P_{X_a} (rank 2), A_b = P_b (line x_b,
       X_a = x_b^perp); then m_a P_a f = 0 = m_b P_b f, so m_a = 0 (else dim f(N) <= 1), m_b != 0 (else VF-A / TC5), f in X_a and
       Z = a m^T (rank one).
   (iii) THREE columns with a rank-one column: by the lemma in R7.3(1) the type is (2,2,1) (Theorem X5) or (1,1,1) (A_j = orthogonal
       projectors onto mutually orthogonal lines x_a, x_b, x_c); in the latter case sum_j m_j P_j f = 0 splits into m_j P_j f = 0, so f(N)
       (2-dim) lies in the intersection of the x_j^perp with m_j != 0: at most one of m_a, m_b, m_c is nonzero, |supp m| <= 3: VF-A / TC5.
   Computation for (i) and (ii)-(2,1) (x51r.py, columns a,b,c,d,e = 0..4, m = (0, 1, mc, md, -1-mc-md) [m_a = 0 forced, m_b != 0 WLOG
   for (i) by the symmetry of columns b..e, forced for (2,1)], N = {a m^T : a in A_N}, A_N = row space of [a1; a2] in the 6 Pluecker
   charts (2x2 minor on coordinates (k,l) = identity); for (2,1): K = {(x_b cross w) e_a^T + s0 x_b e_b^T} in Walsh coordinates, chart
   x_b[q] = 1, q = 1..3; equations: all coefficients of C_j(Y) - 24 - m_j (C_b(Y) - 24)).  RESULT: type (3): unit in all 6 charts, type
   (2,1): unit in all 18 charts (already before saturating by <x_b,x_b>), OVER Q and mod 2147483629.  No saturation and no open
   condition is used for type (3); type (2,1) uses only the charts.  QED
   CALIBRATION: the same generator with N a LINE (a (4,1)-type system): non-unit, dim 2 (type (3), 4 charts) and dim 3 (type (2,1),
   12 charts) -- consistent with the existing split (4,1) spaces and with the oracle-confirmed (4,1) point of type (2,1) found in R7.3.
STATUS 20:39: R7.4 Theorem PR5 written (principal (5,1) kernels must be on >= 4 columns or T3-type; exact over Q). Coordinator's C redesign: x4c2.py generic-h charts (verified 40/40, 60/60 against direct coefficients), queued R7-C2, R7-B3cal, R7-B2.
STATUS 20:41: round 7 closing; local jobs stopped except msolve on S_5 chart 00000 (timeout 900 s, log rows/r7/s5/A_00000.mlog, .gb); all big pieces queued (R7-C2, R7-B3cal, R7-B2, R7-C1, R7-X4K, R7-B-charts superseded by R7-B2).

# ROUND 8 (start 20:44 UTC). Targets: (1) (T3) every 3-column K has a column of rank <= 1, by hand if possible; (2) non-principal
#  (5,1): column-centred spaces, ker c strongly level of row-sum rank < 3; (3) (DC-COST') for e = 1 with a neutral column; (4) interpret
#  R7-B3cal / R7-C2 / R7-B2.
STATUS 20:44: round 8 started.
## Section R8 (round 8)
 R8.1 THEOREM T3 (rigorous, hand proof; only the DEGREE-2 conditions are used).  Every 3-dim strongly level K with s(K) = V living on
   three columns has a column of rank <= 1.  It follows from
   LEMMA O3.  Let (V, <,>) be a nondegenerate 3-dim quadratic space over C and B_a, B_b, B_c in O(V) with B_a + B_b + B_c = 1.  Then some
   B_j is 1 or a reflection; equivalently some A_j = (1 - B_j)/2 has rank <= 1.  Moreover det B_a det B_b det B_c = -1, and if all three
   determinants are -1 then all three B_j are reflections (in mutually orthogonal non-isotropic lines).
   [For K on columns a, b, c: B_j = 1 - 2A_j are isometries and B_a + B_b + B_c + B_d + B_e = 3 with B_d = B_e = 1 (R5.9), so Lemma O3 applies.]
   PROOF.  Identify V with sl_2(C) with the form <x,y> = tr(xy)/2 (all nondegenerate ternary forms are equivalent); then
   SO(V) = {Ad(g) : g in SL_2}, O(V) = +-SO(V) (dimension 3 is odd).  Write B_j = eps_j Ad(g_j), eps_j = +-1, g_j in SL_2, s := sum eps_j.
   (a) Phi(x) := sum_j eps_j g_j x g_j^{-1} is a linear map of M_2(C) that is the identity on sl_2 and s on C1, so
       Phi(x) = x + c tr(x) 1 with c = (s-1)/2.  Under the isomorphism M_2 (x) M_2 -> End(M_2), u (x) w -> (x -> u x w), Phi is the tensor
       T := sum_j eps_j g_j (x) g_j^{-1}, of tensor rank <= 3.  Its Choi matrix sum_{ik} E_ik (x) Phi(E_ik) = Omega Omega^T + c I_4
       (Omega = e1(x)e1 + e2(x)e2, Omega^T Omega = 2) has rank <= 3, and det(Omega Omega^T + c I) = c^3 (c + 2).  So c in {0, -2},
       i.e. s in {1, -3}: an odd number of the eps_j equal -1, hence the determinant product -1.  (s = 3 or -1 is impossible.)
   (b) s = -3 (all B_j = -Ad(g_j)): the Choi matrix is Omega Omega^T - 2I, its image is the 3-dim space Omega^perp, and it equals
       -sum_j u_j v_j^T with u_j = (1 (x) g_j) Omega; so span(u_j) = Omega^perp and Omega^T u_j = tr(g_j) = 0 for all j.  tr g = 0 gives
       g^2 = -1, so Ad(g) is an involution != 1 in SO(V), a rotation by pi, and -Ad(g) is a reflection.  All three B_j are reflections.
   (c) s = 1 (WLOG eps_a = eps_b = 1, eps_c = -1): T = 1 (x) 1.  With g^{-1} = adj(g) = tr(g) 1 - g:  (sum_j eps_j t_j g_j - 1) (x) 1 =
       sum_j eps_j g_j (x) g_j (t_j = tr g_j).  The right side is symmetric, so the left side is lambda 1 (x) 1; applying the polarised
       determinant gives lambda = sum eps_j det g_j = 1.  So  g_a (x) g_a + g_b (x) g_b = 1 (x) 1 + g_c (x) g_c.
       If g_c is a multiple of 1 then g_c = +-1, the right side has rank 1, so g_a, g_b are dependent and g_a = +-1 (B_a = 1).
       Otherwise both sides have rank 2 with the same span P = <1, g_c>, and (g_a, g_b) = (1, g_c) N with N = [[al,be],[ga,de]] in
       O(2,C) (columns (al,ga), (be,de) orthonormal), i.e. N = [[C,-S],[S,C]] or [[C,S],[S,-C]], C^2 + S^2 = 1.  det(al 1 + be g_c) =
       al^2 + al be t_c + be^2 = 1 and the same for (ga, de) both reduce to  C S t_c = 0.  C = 0 or S = 0 makes g_b or g_a = +-1
       (B = 1, a zero column); t_c = 0 makes B_c = -Ad(g_c) a reflection.  QED
   Rank-one B_j = 1 - (rank one) orthogonal forces a reflection (R7.3(1)), so "rank A_j <= 1" <=> "B_j = 1 or a reflection".
   CHECKS [numerical, rows/r8/deg2.py, o3check.py]: 32 random solutions of B_a + B_b + B_c = 1 in O(3,C): s in {1,-3} always, the tensor
   identity T = 1 (x) 1 to 1e-15 when s = 1, tr g_j = 0 for all j when s = -3, and a column of rank <= 1 in every case; LM never converges to
   a solution with all ranks >= 2.
   CONSEQUENCES.  (i) Complete list of principal kernels on <= 3 columns: (1,1,1), (2,2,1) [3 columns], (2,1), (3,2), (3) [<= 2 columns].
   (ii) With PR5 (R7.4): EVERY PRINCIPAL (5,1) KERNEL LIVES ON >= 4 COLUMNS; "no principal (5,1)" <= (PL) alone (the K version on 4 / 5
   active columns, i.e. X4K NC = 4, 5, or the plane cases B, C).  (iii) The T3 computation in R7-X4K is now redundant (can be stopped).
STATUS 20:47: (T3) PROVED by hand (Lemma O3: three orthogonal 3x3 matrices summing to 1 -> one is 1 or a reflection; SL_2 + Choi rank). Principal (5,1) now needs only (PL).
 R8.2 THEOREM CHI1 (non-principal (4,1) with strongly level kernel of row-sum rank 1) [hand + exact over Q; rows/r8/chi/chigen.py].
   STATEMENT. Let L' be a (4,1) space (defect line C m) with ker c = K = chi (x) C^M, |M| = 3, chi in the S_4-orbit of (1, i, -1, -i)
   (the strongly level "R3 space", row-sum rank 1, doubly centred part chi (x) Lambda_M of blueprint type I).  Then m = e_d - e_e (up to
   scale) is the two-column vector on the complement {d, e} of M; in particular the three columns of M are neutral (NCOL_1 holds).
   PROOF.  (Hand, degree 2, any m not two-column; completes R6.3(iv).)  Polarise p_2(Y)_j = c_j^2 + s.y_j - |y_j|^2 between chi w^T
   (w supported on M, W = sum w) and Z (c(Z) = m): the vector v(w)_j = W alpha_j + w_j (beta - 2 alpha_j) [j in M], alpha_j := <chi, z_j>,
   beta := sum_j alpha_j, lies in C m for all w.  w = e_a gives alpha + (beta - 2 alpha_a) e_a in C m; differences give vectors supported
   on {a, b} in C m, which vanish as m is not two-column; so alpha_a = beta/2 on M and alpha = lam m; then beta = lam sum m = 0, so
   lam m_a = 0 on M, and lam = 0 unless m vanishes on M (two-column).  Hence <chi, z_j> = 0 for every column.
   [VERIFY2 (NOTES-verify2 STATUS 21:13): the hand step above has a SLIP -- p_2(Y)_j contains a j-independent term kappa(Y) whose
   polarisation is not zero, so v(w) lies only in C m + C 1; the "differences supported on {a,b}" step fails for m with three equal entries
   off {a,b}.  verify2's REPAIR (case analysis on the zeros of m on M) restores <chi, z_j> = 0.  The theorem rests on the exact part,
   which verify2 VERIFIED independently (own elimination: m = e_3 - e_4 is the only solution).]
   (Exact.)  Unknowns Z (gauge Z[0][a] = 0 for a in M, which uses Z -> Z + chi w^T), m, i (i^2 = -1); equations c(Z) = m and all
   (w, t)-coefficients of c_j(Y) - m_j c_k(Y) for Y = chi w^T + t Z.  By the symmetry of M and of {d, e} two charts cover m != 0:
   m_0 = 1 (0 in M): the ideal is UNIT over Q (no saturation); m_3 = 1 (3 not in M): dim 0 over Q and the elimination ideal in m is
   (m_0, m_1, m_2, m_4 + 1, i^2 + 1), i.e. m = e_3 - e_4.  Calibration: the known split space chi (x) C^M (+) C e_i (e_d - e_e)^T
   (verifyfl D3) lies in the m_3 = 1 chart (non-unit, as required).  QED
   CONSEQUENCE for (5,1): with TC5, no (5,1) space of rank c = 1 has chi (x) C^M inside ker c (the hyperplane chi (x) C^M + C Y_1 would
   be such a (4,1) space).  [Weaker than verifyfl's Prop I' (a column-centred space with defect in C m containing chi (x) W_P has dim <= 3),
   which already excludes ker c containing chi (x) Lambda_M; CHI1 is the exact (4,1)-level statement, i.e. NCOL_1 in this stratum.]
 R8.3 TARGET 2, STATE (non-principal (5,1)).  With DC' (R7.2): a (5,1) space has rank c in {0,1}; for rank c = 1, K4 := ker c is a
   4-dim column-centred space with defect in C m, of type (q,d) (q = rank s|K4, d = dim L'_dc, q + d = 4) -- exactly verifyfl's
   (SL_m) types: (3,1) [T31] (principal or not), (2,2) [T22], (1,3), (0,4) [DC3: char-0 theorem for three m].  Principal (3,1) is now
   reduced to (PL) (PR5 + T3); the non-principal types are verifyfl's typed systems (in progress there).  For rank c = 0 (column-centred
   (5,1)) every hyperplane is column-centred, so (SL_m) itself is the statement.  I did not duplicate verifyfl's computations.
STATUS 20:55: R8.2 Theorem CHI1 (exact over Q): (4,1) with ker c = chi (x) C^M forces two-column m (three neutral columns). R8.3 target-2 state written. Fixed calibration R7-B3cal-v2 queued (unsliced msolve segfaults on positive-dim).
 R8.4 TARGET 3 ((DC-COST') for e = 1 with a neutral column): NOT advanced beyond R7.2.  What stands: a (5,1) space with a neutral column n
   would have delta = dim Q_dc = 1 + s1 + s2 + s3' >= 1 (Q = L' minus column n, a 4x4 level space of dim 5 - dim X_n >= 2 + e^col(Q));
   by the Hyperplane Lemma all its hyperplanes are (4,1) spaces with the same line and the same neutral column; by PR5 + T3, if it is
   principal its kernel K lives on >= 4 columns.  The 4x4 counting with (DI_4x4) gives only dim L' <= 6, so a genuinely new input is needed
   (e.g. the twisted/untwisted split of R5.1 with the defect line forcing e^row(Q) <= 1 in the untwisted case).
 R8.5 R6-1 PIPELINE (practical) and a structural lead.
   (a) msolve 0.6.5 under `ulimit -v 2500000` SEGFAULTS when its hash table must grow ("Enlarging exponent vector for hash table failed
       for esz = 8388608, segmentation fault will follow"): all five unsliced B3 calibration charts (350-550 s, 1.2-1.4 GB RSS, coordinator),
       the unsliced generic-h chart B 0000 (~4 min), and the fibre-fixed chart B 0000 c=0 (~3 min, 1.28 GB).  Singular 4.3.2 on the
       fibre-fixed chart: no crash, 637 MB, not finished in 400 s.  So no chart of B fits the 2.5 GB pool with msolve.
   (b) CALIBRATION FIXED: random affine slices make the positive-dimensional calibration 0-dimensional: B3 chart 001 + 5 slices: NONUNIT
       (185-element basis) in 8 s, 80 MB; fibre-fixed B3 chart 001 (c = 0) + 4 slices: NONUNIT in 11 s, 80 MB.  Slices are used ONLY for
       calibrations (a unit verdict for B, C must be unsliced).
   (c) FIBRE CUT (rigorous cover): in the generic-h charts the only positive-dimensional freedom of a genuine plane is h -> h + t h', and
       sigma(h)_1 changes by t; each chosen coordinate of each column of h vanishes at most once on the fibre line, so the nact + 1
       values sigma(h)_1 = 0, 1, ..., nact give a complete cover (B: 15 charts x 5 values, 24 unknowns; C: 21 x 6).  x4c2.py P CASE CHART
       OUT [SLICE] [FIX]; driver rows/r7/c3charts.sh CASE P NPAR TIMEOUT [msolve|singular] [SLICE].
   (d) STRUCTURAL LEAD for principal (5,1) on >= 4 columns (not finished): with P = f(N) = n^perp (n isotropic; the form on P has rank 1)
       the row-sum relation says  M := sum_j m_j B_j  vanishes on n^perp, i.e. M = w n^T has rank <= 1, together with sum_j B_j = 3.
       In the SL_2 model (B_j = eps_j Ad g_j) this is a second operator identity: sum_j m_j eps_j g_j x g_j^{-1} = (1/2)(tr(n x) w + mu tr(x) 1)
       whose Choi matrix (1/2)(n^T (x) w + mu I) is (nilpotent part) + mu I.  Combined with the Choi identity of Lemma O3 for sum B_j = 3
       and the cubic conditions on K, this may exclude principal (5,1) on 4 or 5 columns WITHOUT (PL).  Next round's first hand target.
STATUS 21:05: R8.5 written: msolve segfaults under the cap on every B chart variant; calibration fixed by slicing (R8-B3cal); fibre cut gives a complete smaller cover; timing probe R8-Bprobe queued; R7-B2/R7-C2 withdrawn. Lead: principal (5,1) via M = sum m_j B_j of rank <= 1 + Choi.
 R8.6 (PL), K VERSION: TWO STRUCTURE CUTS [rigorous reformulations] + numerics.
   (a) DEGREE-2 DATA AS A QUADRATIC FRAME (generalises the Lemma O3 computation).  With B_j = eps_j Ad(g_j), u_j := vec(g_j) in C^4,
       Q := the symmetric matrix of the form vec(x)^T Q vec(y) = tr(adj(x) y) (so u^T Q u = 2 det), Omega = vec(1): the degree-2
       conditions of a strongly level K with s(K) = V on n active columns ("sum of the active B_j = (n-2) 1") are EQUIVALENT to
            sum_{j active} eps_j u_j u_j^T = (n - 2) Omega Omega^T + c Q,   u_j^T Q u_j = 2,   c = (s - (n-2))/2,  s = sum eps_j.
       (Choi matrix of x -> sum eps_j g_j x g_j^{-1}; v_j = Q u_j.)  n = 3: rank <= 3 forces c in {0,-2} (Lemma O3).  n = 4: no rank
       constraint; c = 0 (exactly one eps = -1) forces all g_j into C[g_3], i.e. COMMUTING B_j with a common axis; the other sign patterns
       give a rank-4 frame U diag(eps) U^T = 2 Omega Omega^T + c Q (U unique up to the orthogonal group of diag(eps)).
   (b) SIGN SPLIT: eps_j = det B_j is a discrete invariant; a column with eps_j = -1 can never vanish (A_j = 0 => B_j = 1).  Hence in the
       X4K system for NC active columns, after adding det(B_j) = eps_j, only the eps = +1 columns need saturation; the pattern with all
       eps = -1 needs NONE.  Generator rows/r8/x4ks.py P NC SIGNS DEG OUT (DEG = 3 drops the quartic: a relaxation, so unit stays a valid
       verdict).  Patterns up to column symmetry: NC = 4: ++++, +++-, ++--, +---, ----; NC = 5: six patterns.
   (c) [numerical, rows/r8/k4num.py] degree 2 + cubic ONLY (no quartic), Rabinowitsch-normalised columns: NC = 4: 0/10 starts converge
       (residuals 5e-4..7e-3, columns drifting to 0); control NC = 3: 6/10 converge, exactly to the T3 types (1,1,1), (2,2,1).  So the
       quartic is probably not needed for (PL) in the K version.
 R8.7 PROPOSITION PL4(+++-) [hand + two tiny exact Groebner checks over Q(i) (sympy), rows/r8/: inline scripts logged here].
   There is no 3-dim strongly level K with s(K) = V on EXACTLY four active columns whose sign pattern (eps_j = det B_j on the active
   columns) is (+,+,+,-).
   PROOF.  c = 0, so (R8.6(a)) sum_j eps_j g_j (x) g_j^{-1} = 2 (1 (x) 1); with g^{-1} = tr(g) 1 - g as in Lemma O3:
   g_0 (x) g_0 + g_1 (x) g_1 + g_2 (x) g_2 = 2 (1 (x) 1) + g_3 (x) g_3.
   (i)/(ii) g_3 not scalar: the right side has rank 2 with span <1, g_3>, so every g_j lies in C[g_3]: the B_j commute and fix the
   traceless part u of g_3 (B_j u = eps_j u, so A_j u = 0 for j = 0,1,2 and A_3 u = u).
     (i) u non-isotropic, W := u^perp, B_j|W = eps_j R_j with R_j a rotation, eigenvalues z_j, 1/z_j on the isotropic lines n, n' of W,
         z_j != 1 for j = 0,1,2 (columns active).  The triple (0,1,2): T(alpha u + w) = (1/8) t((1-R_0)w,(1-R_1)w,(1-R_2)w) == 0 gives
         t(n,n,n) = t(n',n',n') = 0, so n, n' lie on the six isotropic lines of the S_4-orbit {(0,1,+-i), (1,0,+-i), (1,+-i,0)}
         (Walsh coordinates: isotropic AND x1 x2 x3 = 0), and u is proportional to n x n'.  The triple (0,1,3) has the part
         (alpha/4) t(u,(1-R_0)w,(1-R_1)w), whose n^2-coefficient (1-z_0)(1-z_1) t(u,n,n) must vanish: t(u,n,n) = 0.  For all 30 ordered
         pairs (n,n') of the six lines with <n,n'> != 0, t(n x n', n, n) is in {+-2, +-2i, +-4}, never 0.  Contradiction.
     (ii) u isotropic (g_3 parabolic): g_j = +-(1 + b_j N), N isotropic, Ad(1 + bN) = 1 + b (N x .) + (b^2/2) N (N . ).  sum B = 2 gives
         b_3 = b_0 + b_1 + b_2 and b_0 b_1 + b_0 b_2 + b_1 b_2 = 0; for sigma in N^perp all three columns 0,1,2 are multiples of N x sigma
         in C N, so the triple (0,1,2) forces t(N,N,N) = 0: N is one of the six lines, WLOG N = (0,1,i) (S_4 is transitive on them).
         Exact: all coefficients of the four triple products, b_0 b_1 + b_0 b_2 + b_1 b_2 = 0 and w b_0 b_1 b_2 = 1 generate the unit ideal
         (sympy groebner over Q(i)); control: the same for a generic isotropic N = (1,1,i sqrt 2) is also unit.
   (iii) g_3 = +-1 (B_3 = -1, A_3 = 1, column 3 = sigma): B_0 + B_1 + B_2 = 3 with eps = +1; the Choi matrix 3 Omega Omega^T + c I has
       rank <= 3, so c = 0 and sum_j vec(g_j) vec(g_j)^T = 3 Omega Omega^T; restricted to Omega^perp this is W W^T = 0 for a 3x3 W, so W has
       rank <= 1: g_j = a_j 1 + lam_j h with one h -- again commuting.  h non-isotropic: same argument as (i) with u := h (triples (0,1,2),
       (0,1,3)).  h isotropic: b_0 + b_1 + b_2 = 0 = b_0^2 + b_1^2 + b_2^2; exact (sympy, N = (0,1,i), control generic N): unit.   QED
   So for four active columns only the sign patterns ++++, ++--, +---, ---- remain (rank-4 frames, R8.6(a)); exact runs of x4ks.py
   (deg <= 3) for ---- (no saturation needed) and +--- are running locally.
STATUS 21:14: R8.6 (Choi frame + sign split) and R8.7 (Prop PL4(+++-): sign pattern +++- impossible for 4-column kernels, hand + tiny exact checks) written.
 R8.8 LEMMA TR and PROPOSITION PL4(+---) [rigorous, degree 2 only; numerically confirmed].
   LEMMA TR.  For a K on exactly four active columns with sign pattern eps and c = (s - 2)/2 not in {0, -4} (patterns ++++, ++--, +---,
   ----): the frame U = [u_0..u_3] is invertible and  tr(g_j)^2 = (4 + c)(1 - c eps_j/2),  hence  tr A_j = (3 - eps_j (tr(g_j)^2 - 1))/2:
        ++++: tr A_j = 3/4;   ++--: -1/4 (eps = +1), 7/4 (eps = -1);   +---: 0 (+), 1 (-);   ----: 3/4.
   Proof.  U diag(eps) U^T = S := 2 Omega Omega^T + c Q (R8.6(a)), det S = c^3 (4 + c) != 0.  (1) U^T Q U = diag(eps) U^{-1} S Q U and
   S Q = 2 Omega Omega^T + c I, so with p := U^{-1} Omega, t_j := Omega^T u_j = tr g_j:  u_j^T Q u_j = 2 gives eps_j (c + 2 p_j t_j) = 2.
   (2) S Omega = (4 + c) Omega, and S Omega = U diag(eps) U^T Omega = U diag(eps) t, so p_j = eps_j t_j/(4 + c).  Combine.  tr Ad(g) =
   tr(g)^2 - 1 for g in SL_2 (eigenvalues mu^2, 1, mu^-2).  QED   [numerical, rows/r8/trchk.py: 3 + 3 + 3 random degree-2 solutions of
   ++++, ++--, ---- give exactly these traces.]
   PROPOSITION PL4(+---): no K on exactly four active columns has sign pattern (+,-,-,-).  Proof: c = -2, so tr(g_j)^2 = 0 for the three
   eps = -1 columns: g_j^2 = -1 and B_j = -Ad(g_j) are REFLECTIONS 1 - 2P_j (P_j symmetric rank-one projectors); then B_0 = 1 - 2A_0 =
   2(P_1 + P_2 + P_3) - 1 is symmetric and orthogonal, hence an involution, with trace 2*3 - 3 = 3, so B_0 = 1 and A_0 = 0: column 0 is
   inactive.  QED  [numerically: degree-2 solutions of this pattern have A_0 -> 0 (singular values ~1e-6).]
   STATE OF (PL), K VERSION, FOUR ACTIVE COLUMNS: +++- (R8.7) and +--- excluded by hand; ++++, ++--, ---- have genuine degree-2
   solutions (numerically: ranks (2,2,2,2), (2,2,3,3), (3,3,3,3)) and need the cubic; exact runs with the trace equations added
   (x4ks.py ... tr) for ---- (no saturation) and ++++ are running locally.  FIVE active columns: not yet analysed this way (5 vectors
   in C^4: the frame is not invertible; c = 0 for pattern ++++-).
STATUS 21:18: R8.8 Lemma TR (traces forced by the frame) + Prop PL4(+---) written; 4-column (PL) reduced to sign patterns ++++, ++--, ----; exact runs with trace equations running.
   [R8.8 addendum] Using Q = Omega Omega^T - K (K = commutation matrix, vec(x)^T K vec(y) = tr(xy)), the frame identity reads, for
   every 2x2 matrix a:   sum_j eps_j tr(a g_j)^2 = (2 + c) tr(a)^2 - c tr(a^2)   (four active columns; a = 1 gives Lemma TR's sum).
   For ++++ (c = 1) also sum_j g_j (x) g_j = 3 (1 (x) 1) - T_tr and sum_j tr(g_j) g_j = 5 * 1 (from the polarised determinant).
STATUS 21:32: patterns ++++ and ---- (4 active columns) EXCLUDED: degree-2 data = one O(3,C)-orbit of the tetrahedral configuration (Lemma ORB), cubic test over Q unit in seconds (rows/r8/orb/orbgen.py), calibration (3-column orbit) non-unit dim 2. Stopped my kt4_ runs (redundant). ++-- via quaternion system running.
 R8.9 THEOREM PL4(++++, ----) [hand reduction (Lemma ORB) + exact Groebner basis over Q(sqrt 5) resp. Q(sqrt -3) in Singular].
   No 3-dim strongly level K with s(K) = V lives on exactly four active columns with sign pattern ++++ or ----.
   LEMMA ORB.  For these two patterns every degree-2 datum (B_0..B_3 in O(V), sum = 2, the given determinants) is of the form
   B_j = R B^0_{pi(j)} R^{-1} with R in O(V), pi in S_4, and the TETRAHEDRAL configuration (Walsh coordinates, h_j = row j of H)
        ++++:  B^0_j = (1/4) I + (1/4) h_j h_j^T + (sqrt5/4) [h_j]_x          (rotation about h_j, cos = 1/4),
        ----:  B^0_j = (5/4) I - (3/4) h_j h_j^T - (i sqrt3/4) [h_j]_x        (minus a rotation about h_j, cos = -5/4).
   Proof.  Write g_j = t_j/2 + gamma_j (gamma_j traceless, <x,y> = tr(xy)/2).  The frame identity (R8.8 addendum) with a traceless,
   resp. a = lam 1 + x, gives  sum_j eps_j gamma_j gamma_j^T = -(c/2) Id,  sum_j eps_j t_j gamma_j = 0, and det g_j = 1 gives
   <gamma_j,gamma_j> = t_j^2/4 - 1 with t_j^2 from Lemma TR.  For ++++ (c = 1, t^2 = 5/2) and ---- (c = -3, t^2 = -1/2) the rescaled
   eta_j := gamma_j / sqrt(-c'/...) form an EQUAL-NORM PARSEVAL frame (sum eta eta^T = I, |eta_j|^2 = 3/4) of four vectors in C^3; the
   4 x 3 matrix E of rows eta_j is an isometric embedding onto n^perp with E E^T = I - n n^T/(n.n), n_j^2 = (n.n)/4, n_j = +-1, and
   sum t_j gamma_j = 0 forces t proportional to n.  Flipping (eta_j, t_j) -> -(eta_j, t_j) (g_j -> -g_j, same Ad) gives n = (1,1,1,1),
   and two isometric embeddings onto 1^perp differ by M in O(3): eta_j = M^T (h_j/2).  Ad(s + M gamma) = M Ad(s + gamma) M^{-1} for M
   proper and = M Ad(s + gamma)^{-1} M^{-1} for M improper; the inverse configuration is the image of B^0 under an improper symmetry of
   the tetrahedron combined with a relabelling pi.  QED   [The base configurations satisfy B^0_j orthogonal, sum = 2 I, det = +-1,
   tr A_j = 3/4 exactly (checked numerically to 1e-16).]
   COMPUTATION (rows/r8/orb/orbgen.py PAT OUT 0): unknown R in O(3,C) (9 entries, R^T R = I), r with r^2 = 5 resp. -3; all
   coefficients of the four triple products t(R A^0_a tau, R A^0_b tau, R A^0_c tau) (only degree <= 3 of strong levelness used).
   Over Q: UNIT for ++++ and for ---- (seconds).  The triple set is symmetric under pi, so the relabelling is covered.
   CALIBRATION (rows/r8/orb/cal3.sing): the same pipeline for the 3-column (1,1,1) orbit (A_j = projectors onto the Walsh axes, one
   triple) is NON-unit of dim 2 = the family of frames with t(x_a,x_b,x_c) = 0, as it must be.
   STATE: four active columns -- +++- (R8.7), +--- (R8.8), ++++ and ---- (R8.9) excluded; ++-- running (quaternion system, rows/r8/orb/
   quat4.py, an independent formulation that will also re-check ++++ and ----).
 R8.10 THEOREM PL4 [hand (R8.6-R8.9 + this section) + exact Groebner bases over Q; independent sympy checks for R8.7]:
   NO 3-dim strongly level K with s(K) = V lives on EXACTLY FOUR active columns.
   The last pattern ++-- (c = -1): the frame identities give sum eps_j v_j v_j^T = -(1/2) I, |v_j|^2 = -1/8 (eps = +), 5/8 (eps = -),
   sum eps_j s_j v_j = 0, s_j^2 = 9/8, 9/8, 3/8, 3/8 (quaternions q_j = (s_j, v_j), B_j = eps_j Rot(q_j)).  w_j := sqrt(-2 eps_j) v_j is a
   Parseval frame with norms (1/4, 1/4, 5/4, 5/4), complement n = (sqrt3, sqrt3, i, i)/2 (signs absorbed by q -> -q), and the signed sum
   forces s proportional to the coefficients of n.  Up to O(3) and the inverse configuration this is the unique datum
        s = (3/(2 sqrt2), 3/(2 sqrt2), -sqrt3/(2 sqrt2), -sqrt3/(2 sqrt2)),
        v_0,1 = (-+ i/2, 0, 1/(2 sqrt2)),  v_2,3 = (0, +-1/2, -sqrt3/(2 sqrt2))      (exact: sum B = 2I in Q(sqrt2, sqrt3, i): checked).
   Orbit test (rows/r8/orb/orb_ppmm.py OUT 0 INV, INV = 0 and 1 for both orientations): UNIT over Q.  ++++ and ---- (R8.9) re-run with an
   exact in-field check of sum B = 2I: UNIT over Q (orbgen.py; both orientations are in the ideal via r^2 = 5 resp. -3).
   [Caught and fixed on the way: Singular's "1/(2*r2)" is polynomial division (= 0); the first ++-- run was void; all runs now carry an
   exactness check of the base configuration.]
   CONSEQUENCES.  (i) With T3 (R8.1) and the 2-column list: a principal kernel lives on <= 3 columns OR ON ALL FIVE COLUMNS.
   (ii) With PR5: every principal (5,1) kernel lives on all five columns.  (iii) NCOL-P3 is unconditional except for principal (4,1) spaces
   whose kernel has five active columns.  (iv) What is left of (PL) (K version): FIVE active columns -- six sign patterns, in the queue
   (R8-Ksign ks5_*), and the frame method of R8.6 applies with five vectors in C^4 (not invertible; next round's hand target).
STATUS 21:38: THEOREM PL4 (no principal kernel on exactly 4 columns; hand + exact over Q, all 5 sign patterns) written. Left of (PL) K version: 5 active columns.
STATUS 21:39: round 8 closing; quaternion cross-check of PL4 queued (R8-PL4-quat; local run timed out at 600 s); no local jobs left running.

# ROUND 9 (start 21:42 UTC). Targets: (1) (PL) K version on FIVE active columns by the frame method (six sign patterns);
#  (2) non-principal (5,1) jointly with verifyfl (division of labour via NOTES); (3) (DC-COST').  Memory rule (BRIEF U12): one own job > 0.5 GB
#  at a time, cap 2 GB.
STATUS 21:42: round 9 started.
## Section R9 (round 9)
 R9.0 MESSAGE TO verifyfl -- proposed division of labour for (5,1) at e = 1 (please answer in NOTES-verifyfl):
   rows: (a) the PRINCIPAL stratum, now only (PL) on five active columns (K version; frame method, R9.1 ff.); (b) hand arguments for (4,1)/(5,1)
   strata in which ker c contains a strongly level 3-space of row-sum rank <= 2 (CHI1 did chi (x) C^M; next: type (2,1) with S = u^perp and
   the type-II (1,2) kernel), i.e. NCOL_1 / exclusion where a strongly level kernel is available.
   verifyfl: the typed (SL_m) systems [T31] (non-principal), [T22], [DC3] per m, and [T31-B]-style hand cases.  rows will NOT run typed systems.
   Interface: a (5,1) space with rank c = 1 has K4 = ker c of type (q,d), q + d = 4 (DC', R7.2); "principal" (q = 3 with a strongly level
   3-dim H inside K4) is rows'; everything else is the typed systems.  Shared fact for [T31]: with H strongly level the B_j are isometries and
   the frame identities of R8.6 / R9.1 hold for H; without strong levelness b_j^* g = s^* g - 2 m_j thetahat_2 (verifyfl QB) breaks them.
 R9.1 FIVE ACTIVE COLUMNS: DEGREE-2 DATA [rigorous] + census [numerical].
   (a) Quaternion form (no Choi needed): with B_j = eps_j Rot(s_j, v_j), Rot(s,v) = (s^2 - v.v) I + 2 v v^T + 2 s [v]_x, s^2 + v.v = 1,
       the condition sum_j B_j = (n-2) I on n active columns is EQUIVALENT to
            sum_j eps_j v_j v_j^T = (c/2) I,   sum_j eps_j s_j v_j = 0,   c = (sum eps_j - (n-2))/2
       (symmetric / antisymmetric parts; trace gives sum eps_j |v_j|^2 = 3c/2).  A column with eps = +1 is A_j = |v|^2 I - v v^T - s [v]_x
       (vanishes iff v_j = 0; kernel C v_j, so h(v_j) is a strongly level MATRIX on the other columns); eps = -1: A_j = s^2 I + v v^T + s [v]_x
       (never 0).  For n = 4 this is the frame of R8.6 in other coordinates.
   (b) LEMMA TR5 (n = 5, c not in {0, -6}): the 4 x 5 frame U~ = [s; v] has a one-dimensional kernel C rho (sum rho_j s_j = 0, sum rho_j v_j = 0),
       P := diag(eps) U~^T D^{-1} U~ (D = diag(3 + c/2, c/2, c/2, c/2)) is idempotent of rank 4, I - P = rho (diag(eps) rho)^T / Lambda,
       Lambda = sum eps_k rho_k^2, and comparing diagonals:   s_j^2 = (6 + c)(2 - c eps_j + c rho_j^2/Lambda)/12   (t_j = 2 s_j).
       So the traces are no longer forced; the 3-dim moduli (6-dim variety mod O(3)) are parametrised by rho on the hypersurface
       sum rho_j s_j = 0.  [n = 4: rho = 0 gives Lemma TR.]
   (c) [numerical, rows/r8/deg2_5.py, deg2_5s.py] degree-2 solutions on five columns exist for ALL SIX sign patterns: ++++- (tangent dim 7),
       +++--, ++---, +---- (dim 6) found unforced; +++++ and ----- 8/8 when forced.  So the cubic is essential for every pattern.
 R9.2 [numerical, rows/r8/k5num.py] degree 2 + cubic ONLY on five active columns (Rabinowitsch-normalised columns): 0 of 9 starts converge
   (residuals 7e-4..5e-3, columns drifting to 0); the same code converges for three columns (6/10, R8.6(c)).  So, as for four columns, the
   quartic is probably not needed.
STATUS 21:50: R9.1 (quaternion frame, Lemma TR5, all six 5-col patterns exist at degree 2), R9.2 (deg2+3 numerics: 0/9 on 5 columns) written; R9-Q5 queued; ks5 still running at the coordinator.
 R9.3 THE SUMMED CUBIC [rigorous identity; checked on genuine spaces] and a smaller exact target.
   IDENTITY: for a strongly level K with s(K) = V (B_j = 1 - 2A_j over all five columns, inactive B_j = 1):
            sum_{j=0}^{4} c(B_j sigma) = 3 c(sigma),   c(x) := t(x,x,x) = p_3(x) = 24 x1 x2 x3 (Walsh),
   i.e. sum over the n active columns of c o B_j = (n - 2) c.  Proof: the cubic conditions in g-form (g_k := B_k sigma, R := sum_k g_k o g_k)
   are b(sigma - g_j, 3 sigma o sigma + 2 g_j o g_j - R) = 0 for each j; summing over j with sum_j (sigma - g_j) = 2 sigma gives
   6 c(sigma) - 2 sum_j c(g_j) = 0.  [checked: rel. error 1e-14 on six saved strongly level 3-spaces rows/sl3_s1*.npy.]
   Representation form: Sym^3 V^* = H_3 (+) |x|^2 V^*, the |x|^2 V^* part holds automatically (sum B_j = 3), c is HARMONIC, so the
   identity is  (sum_j rho_3(B_j)) c = 3 c  in the 7-dim spin-3 representation -- 7 equations; with B_j = eps_j Ad(g_j):
   sum_j eps_j f(g_j^T z) = (n-2) f(z) for the octahedral binary sextic f = z1 z2 (z1^4 - z2^4) (rho_3(-1) = -1).
   NUMERICAL [rows/r8/sumcub.py]: degree 2 + summed cubic ALONE: n = 5: 0/6 starts converge, n = 4: 0/6; control n = 3: 6/6.
   EXACT [rows/r8/orb/sumq.py, quaternion unknowns + 7..10 summed-cubic coefficients, mod 2147483629]: calibrations n = 3: pattern ++-
   NON-unit, dim 1 (= the (2,2,1) family), pattern --- NON-unit, dim 2 (= the (1,1,1) family), pattern +-- unit (forbidden by Lemma O3).
STATUS 21:57: summed cubic suffices for 4 columns (SUMQ ---- unit, 145 s, 0.13 GB); running the six 5-column SUMQ patterns sequentially (sq5runs.sh, small memory). R9-Q5 (full quaternion) likely memory-bound (benchmark 1.57 GB at 7.5 min).
   EXACT, FOUR COLUMNS [mod 2147483629]: SUMQ ---- UNIT (145 s, 0.13 GB), SUMQ ++-- UNIT after saturation (140 s, 0.12 GB): the summed
   cubic alone already excludes these patterns (consistent with PL4; an independent second certificate for them, modulo p).
   FIVE COLUMNS: rows/r8/orb/sq5runs.sh (six patterns, sequential) running locally at p = 2147483629; queued for two more primes and Q
   (R9-SUMQ5).  If all are unit: (PL) K version on five columns => every principal kernel lives on <= 3 columns => NCOL-P3 unconditional
   for principal (4,1) spaces and NO principal (5,1) space (PR5 + T3 + PL4).
   FIVE COLUMNS, local runs at p = 2147483629: ----- DIED at the 2 GB cap (591 s, 1.97 GB, no verdict) -> R9-SUMQ5-big (big slot);
   msolve on the exported ----- system (sq5m5.ms, 24 polynomials) segfaults under ulimit (36 s) as usual.  +---- still running at the close
   of the round (1.4 GB at 6.5 min; result will appear in rows/r8/orb/sq5_+----_2147483629.out, line RESULT); driver stopped for Lean window 1
   (the remaining four patterns are left to R9-SUMQ5).
STATUS 22:13: round 9 closing (Lean window 1 open): driver sq5runs.sh stopped; only sq5_+---- (<= 2 GB, <= 30 min) still running.

# ROUND 10 (start 22:15 UTC). Targets: (1) hand proof of the summed-cubic exclusion on five columns; (2) react to the SUMQ5
#  verdicts; (3) non-principal (5,1) with verifyfl (R9.0 split).
STATUS 22:15: round 10 started.
## Section R10 (round 10)
 R10.1 THE SUMMED CUBIC IS THE 4x5 LEVEL CONDITION P_3 = 0 [rigorous, one line].  Put B_j = 1 - 2A_j, y_j = A_j sigma (columns of h(sigma) in
   Walsh coordinates), sum_j y_j = sigma, and m = polarised x1x2x3.  Expanding sum_j c(B_j sigma) = (n-2) c(sigma) leaves exactly
   -6 sum_{j<k<l} m(y_j, y_k, y_l) = 0, i.e.  sum of all triple products = 0  <=>  P_3(h(sigma)) = 2 sum_i e_3(row_i) = 0.
   So the relaxation of R9.3 is: "strongly level in degree 2 (B_j orthogonal)  +  4x5-LEVEL in degree 3".  Binary-form version (B_j =
   eps_j Ad g_j): sum_j eps_j q o g_j = (n-2) q for all binary quadratics q, and sum_j eps_j f o g_j = (n-2) f for the octahedral sextic
   f = z1 z2 (z1^4 - z2^4) (rho_3(-1) = -1).
 R10.2 SECOND PROOF OF PL4 FOR ++++, ----, ++-- BY LINEAR ALGEBRA [exact; rows/r10/rank2.py; uses only the summed cubic].
   By Lemma ORB every degree-2 datum of these patterns is B_j = R B^0_{pi(j)} R^{-1} (or the inverse orientation).  The summed cubic
   becomes A^0 (c o R) = 2 (c o R) with A^0 := sum_j rho_3(B^0_j) (pullback on cubic forms).  Each rho_3(B) preserves Sym^3 = H_3 (+) |x|^2 V^*,
   A^0 = sum B^0_j = 2 on |x|^2 V^*, and c o R is a NONZERO HARMONIC cubic.  EXACT: rank(A^0 - 2I) = 7 on the 10-dim space of cubics over
   Q(sqrt5) (++++), Q(i sqrt3) (----), Q(sqrt2, sqrt3, i) (++-- in both orientations) (sympy DomainMatrix over the algebraic field).
   Hence 2 is NOT an eigenvalue of A^0 on H_3 and no rotation R works.  QED  [spectra on H_3: ++++: 1 (on c itself), -5/4 +- i sqrt71/4
   (each x3); ----: 5 (on c), -4 (x3), 19/2 (x3); ++--: 13.578, -1.272 +- 3.322i, 1.461 +- 5.890i, 8.772 +- 6.876i.]
   This is independent of the orbit tests of R8.9/R8.10 (different equations, different engine), so PL4 now has two certificates for
   these patterns (+++- and +--- were by hand).
 R10.3 FIVE COLUMNS in this language: the summed cubic says 3 = n - 2 is an eigenvalue of A(B) := sum_j rho_3(B_j) on H_3 with an
   eigenvector in the octahedral orbit cone {lam c o R}.  [numerical, rows/r10/spec3b.py] on random five-column degree-2 data
   min |lambda - 3| over spec(A|H_3) ranges 0.4 .. 14, so the eigenvalue condition alone cuts a hypersurface of the 3-dim moduli; the
   octahedral-eigenvector condition (codim 3 in H_3) must then fail on it.  No hand proof yet.
   Local exact runs of the summed system at p = 2147483629: ----- and +---- both DIED at the 2 GB cap (591 s / 581 s); they need the big
   slot (scheduled by the coordinator, runs/bigq.sh and runs/postwin1.sh).
STATUS 22:28: R10.1 (summed cubic = P_3 of the 4x5 matrix), R10.2 (exact linear-algebra proof of PL4 ++++/----/++-- from the summed cubic: rank(A0-2I)=7) written.
 R10.4 COMPUTATION NOTES.  (a) The A-coordinate version of the summed system (rows/r10/aksum.py: orthogonality + det signs + the 10 coefficients
   of P_3(h(sigma))) is SLOWER than the quaternion version (four columns ----: > 4 min vs 145 s); the quaternion version (sumq.py) stays.
   (b) All five-column summed systems need more than 2 GB: ----- 591 s, +---- 581 s / 377 s at the cap.  ----- runs in the big slot since
   22:32 (runs/bigq.sh step 1b, output rows/r8/orb/sq5big_-----.out); asked the coordinator to move the other five patterns there (QUEUE R10-SUMQ5-note).
 R10.5 NEXT HAND ROUTE for five columns (not executed): the signed measure mu = sum_j eps_j delta_{g_j} has n atoms, so EVERY spin-j Choi
   (moment) matrix J_j = sum_k eps_k vec(rho_j(g_k)) vec(rho_j(g_k)^{-T})^T has rank <= n (Lemma O3 is the spin-1/2 case, rank <= 3).
   J_{3/2} (16 x 16, rank <= 5) is linear in the moments s, M_1 = sum rho_1(B_j) = (n-2) I, M_2^eps = sum eps_j rho_2(B_j) and M_3 = sum rho_3(B_j),
   and the summed cubic says M_3 c = (n-2) c.  A contradiction would come from showing that no M_2^eps, M_3 with these constraints give rank <= 5.
STATUS 22:33: R10.4 (computation notes: big slot needed for all 5-col patterns; A-variant slower) and R10.5 (moment-matrix route) written; ----- running in the big slot.
 R10.6 THEOREM CHI2 + THE (q,d) = (1,2) KERNEL STRATUM [exact over Q, Singular; rows/r10/chi2gen.py, extII.py, extI.py].
   (a) EXTENSIONS [exact].  The only 3-dim strongly level spaces containing a type-I plane chi (x) Lambda_M are chi (x) C^M; the only one
       containing a type-II plane N_II = {mu zeta (e_a - e_b)^T + mu' zetabar (e_c - e_d)^T} (zeta = (1, om, om^2, 0), Lemma SL S7 normal form)
       is K_II := N_II (+) C w e_e^T, w = (1,1,1,-3) (e = the inactive column).  [Unknown Y modulo the plane, all deletion coefficients:
       the radical of the ideal is the line through chi e_2^T resp. w e_4^T.]  With Lemma SL's classification (d = 2 => N of type I or II;
       III, IV impossible -- verified blueprint), every strongly level 3-space of row-sum rank 1 is chi (x) C^M or K_II (up to symmetries).
   (b) THEOREM CHI2 [exact].  A (4,1) space with ker c = K_II has, in the labelling (a,b,c,d,e) = (0,1,2,3,4) and m_0 = 1 (one chart suffices by
       the symmetries 0<->1, 2<->3 and (01)<->(23) with om <-> om^2),  m in {(1,-1,-1,1,0), (1,1,-1,-1,0), (1,-1,1,-1,0)}:  the inactive
       column e is NEUTRAL (NCOL_1), m is NOT two-column (four nonzero entries, repeated); the solution set is finite (dim 0).
   (c) PENCIL PRINCIPLE [rigorous] and COROLLARY.  If L' is a (5,1) space with rank c = 1 and K subset ker c, then for Z_1, Z_2 with c(Z_1) = m,
       c(Z_2) = 0 every hyperplane H_al = K + C(Z_1 + al Z_2) is a (4,1) space with ker c|H_al = K and the same m; the gauge representatives
       of Z_1 + al Z_2 form an affine line.  So if the (4,1) extensions of K with fixed m are FINITE, no such (5,1) space exists.
       => no (5,1) space with rank c = 1 has K_II inside ker c (CHI2 finite), and none has chi (x) C^M inside ker c (CHI1: chart m_3 = 1 has dim 0).
   (d) STATE of the strongly-level-kernel strata (rows' side of R9.0): (3,0) principal = PL4 + T3 + PR5 + (PL on five columns, running);
       (1,2) DONE (this section + CHI1); (0,3) impossible (Lemma SL); (2,1) (S = u^perp, u isotropic, 1-dim doubly centred part) OPEN.
STATUS 22:37: R10.6: Theorem CHI2 (exact over Q; neutral column), uniqueness of strongly level extensions of type-I/II planes (exact), pencil principle => no (5,1) of rank c = 1 over a row-sum-rank-1 kernel. Open on rows' side: (2,1) kernels; 5-column (PL) in the big slot.
 R10.7 THE (q,d) = (2,1) STRATUM -- first facts.  [numerical, rows/r10/k21num.py] strongly level 3-spaces with a doubly centred element and
   row-sum rank 2 EXIST (residual 1e-13), e.g. on two columns with column ranks (3,2).  [rigorous] Two-column strongly level spaces are exactly
   the Lagrangians of (V (+) V, beta), beta(Y,Y') = <y_a,y_b'> + <y_a',y_b> = (1/2)(<p,p'> - <d,d'>) with p = y_a + y_b (row sums), d = y_a - y_b
   (the only condition is <y_a, y_b> == 0; P_3, P_4 vanish with two nonzero columns).  Principal ones: graphs d = B p, B orthogonal.  The (2,1)
   ones: K cap (0 (+) V) = 0 (+) C d_0, d_0 isotropic; then p(K) = u^perp (u isotropic) and
        K = span{ u (e_a + e_b)^T,  (p_1 + e) e_a^T + (p_1 - e) e_b^T,  d_0 (e_a - e_b)^T },   <u,u> = <d_0,d_0> = 0, u . p_1 = 0, d_0 . e = 0,
        <p_1,p_1> = <e,e> = 1.
   NEXT: the CHI-style exact test of (4,1) spaces over this family (unknowns u, d_0 via the isotropic conic, p_1, e, Z, m) and the pencil
   principle for (5,1); then (2,1) kernels on three or more columns, if the census finds any.
   [census, k21num.py, 7 starts] (2,1) strongly level 3-spaces found on TWO columns (ranks (3,2): rows/r10/k21_s1_0.npy, _1, _4) and on THREE
   columns (ranks (2,2,1): rows/r10/k21_s1_5.npy); one start gave a 2-dim space.  The CHI-style exact test over the two-column family without
   a gauge for Z (rows/r10/chi21gen.py) hit the 2 GB cap in 185 s -- needs a gauge adapted to K (e.g. via the d_0 / u coordinates) or the
   pencil principle applied with an explicit (4,1) normal form.  OPEN.
STATUS 22:46: round 10 closing; RESULT ROUND 10 written; ----- in big slot; no own jobs running.

# ROUND 11 (start 22:49 UTC). Targets: (1) five-column hand proof (eigenvector condition on the TR5 moduli / spin-3/2 moment rank);
#  (2) the (2,1) kernel stratum (two-column family, gauge for Z, charts <= 2 GB; pencil principle; then three-column (2,1) kernels);
#  (3) column-centred (5,1) over these kernels.  SUMQ5: all six patterns in the big slot (verdicts expected 23:30-03:00).
STATUS 22:49: round 11 started.
## Section R11 (round 11)
 R11.1 (2,1) TWO-COLUMN FAMILY, HAND REDUCTION [rigorous].  For Y in K and the row-centred extension Z of a (4,1) space L' = K + C Z
   (c(Z) = m), polarising P_2(Y^(j)) = c_j^2 + s.y_j - |y_j|^2 + kappa(Y), kappa(Y) = (|Y|^2 - |s|^2 - |c|^2)/2 (j-independent; verify2's term),
   with Y = D = d_0 (e_a - e_b)^T gives the vector (beta, -beta, delta, delta, delta) in C m, beta = <d_0, s_Z - P_Z>, delta = <d_0, D_Z>
   (P_Z = z_a + z_b, D_Z = z_a - z_b).  As m is in 1^perp: delta = 0; and beta != 0 forces m = e_a - e_b (two-column).  So in the
   neutral-column question one may add delta = beta = 0 (rows/r11/c21gr.py).  With U = u(e_a + e_b)^T and W the analogous vectors are
   (gamma, gamma, 2<u,z_j> + kappa_U ...) and (..., 2<p,z_j> + kappa_W ...) in C m.
 R11.2 COLUMN-CENTRED SPACES OVER THE ROW-SUM-RANK-1 KERNELS [exact over Q; rows/r11/chi2cc.py, chi1cc.py].
   Unknown Z with c(Z) = 0 (gauge modulo the kernel), deletion vectors of K + C Z in 24*1 + C m, saturation by (Z) (Z = 0 gives a spurious
   component with arbitrary m):
   * K_II: the solutions with Z != 0 form finitely many lines and force m = e_0 - e_1 (two-column; by symmetry also e_2 - e_3).
   * chi (x) C^M: UNIT in both m-charts (no column-centred 4-dim extension with nonzero defect; consistent with verifyfl's Prop I').
   Since a hyperplane of a column-centred (5,1) space containing K is a column-centred 4-dim space with defect C m (zero defect would make it
   a 4-dim strongly level space, against Lemma SL), the pencil principle (or TC5 for the two-column m) gives:
   NO column-centred (5,1) space contains chi (x) C^M or K_II.  With R10.6: the (q,d) = (1,2) kernel stratum is settled for (4,1) and for
   ALL (5,1) (rank c = 0 and 1).
STATUS 22:52: R11.1 (hand reduction for the (2,1) two-column family), R11.2 (column-centred (5,1) over chi (x) C^M and K_II excluded, exact) written; c21g (gauge-fixed (2,1) test) running at 1 GB; n21 numerics running.
 R11.3 FIVE COLUMNS, structure of the summed-cubic condition (target 1; no proof).  "Exists R: A(B)(c o R) = 3 (c o R)" is O(3)-invariant,
   so it lives on the 3-dim moduli (R9.1(b)).  Writing H_3 = binary sextics (c <-> f = z1 z2 (z1^4 - z2^4)), it says: (i) det(A(B)|H_3 - 3) = 0
   and (ii) the 3-eigenvector is OCTAHEDRAL, i.e. its SL_2-invariants (degrees 2, 4, 6, 10) have the ratios of f (three equations).  Four
   conditions on a 3-dim family: expected empty, consistent with all numerics, but not proved.  The spin-3/2 moment-rank route (R10.5) is
   blocked by the non-scalar blocks N_2 = sum eps_j rho_2(B_j), M_3 (the Racah-coefficient formula for Choi(sum lam_l P_l) needs scalars).
   The decisive evidence remains the big-slot runs sq5big_<SG>.out.
   [R11.1 continued, rigorous] The level condition P_2(Y,Z) = 0 (sum of the polarised vector) gives kappa_U = kappa_W = 0 and delta = 0 for
   every (4,1) extension; the surviving degree-2 conditions are gauge-invariant (Z -> Z + K):
     (U) (<u,s_Z>, <u,s_Z>, 2<u,z_c>, 2<u,z_d>, 2<u,z_e>) = lam_U m;   (W) (<s_Z,p+e> - 2<e,z_a>, <s_Z,p-e> + 2<e,z_b>, 2<p,z_c>, 2<p,z_d>, 2<p,z_e>) = lam_W m;
     (D) <d, s_Z - P_Z> = 0 unless m is two-column.   Case split used in the exact runs: lam_U = 0 (rows/r11/c21grA.py) or m_a = m_b (c21grB.py).
   [the numerical search rows/r11/n21.py is DISCARDED: it imposed only the minors against m_0, so m_0 = 0 satisfied half of them trivially.]
   The three-column (2,1) sample rows/r10/k21_s1_5.npy also has a TWO-COLUMN doubly centred element d (e_0 - e_2)^T, d isotropic, so the D-part of
   the reduction applies to it as well.
 R11.4 (2,1) TWO-COLUMN FAMILY: THE K-K-Z CUBIC [rigorous].  For Y_1, Y_2 in K (supported on columns a, b) and Z, a 3x3 subpermanent with two
   rows from K and one from Z is nonzero only on column sets {a, b, t}; so the K-K-Z part of the cubic defect vector is
        (0, 0, T_d + T_e, T_c + T_e, T_c + T_d),   T_t := sum_{distinct r1,r2,r3} (y1a[r1] y2b[r2] + y1b[r1] y2a[r2]) z_t[r3]
                                                      = -( <y1a,y2b> + <y1b,y2a> ) m_t + 2 < y1a o y2b + y1b o y2a , z_t >
   and the first bracket is 0 (K Lagrangian).  If m_a != 0 (chart m_0 = 1) the vector must vanish:  <pi, z_t> = 0 for t = c, d, e and pi in
        Pi := span{ u o u,  d o d,  p o p - e o e,  u o p,  e o d }   (all in V, as <u,u> = <d,d> = <u,p> = <e,d> = 0, <p,p> = <e,e>).
   Generic case Pi = V: z_c, z_d, z_e are CONSTANT vectors (m_t/4) 1; then (U), (W) force lam_U = lam_W = 0 unless m is two-column,
   (D) holds automatically, and Z-Z in degree 2 gives (3/4) m_t^2 + kappa(Z) = theta m_t for t = c, d, e (at most two distinct values).
   These 15 linear equations are added to the exact system (rows/r11/c21gk.py; valid in the chart m_0 = 1, which covers every m except
   m_a = m_b = 0, where columns a, b are already neutral).
 R11.5 (2,1) TWO-COLUMN FAMILY, GENERIC CASE BY HAND [rigorous, partial].  Assume Pi = V (R11.4) and m_a != 0.  Then z_c, z_d, z_e are constant
   vectors, so EVERY Y in L' = K + C Z has rows that agree outside columns a, b (rows (1 + al_i, 1 + be_i, x_c, x_d, x_e) of J + Y).  For such
   matrices the deletion vectors depend only on c_a, c_b, the column values x_t = 1 + t m_t/4 and omega := <y_a, y_b>:
        C_a = 6 x_c x_d x_e (4 + c_b) - 24,  C_b = 6 x_c x_d x_e (4 + c_a) - 24,  C_c = 2 x_d x_e [12 + 3(c_a + c_b) + c_a c_b - omega] - 24  (etc.),
   and on L' (Y = Y_K + t Z): c = t m, omega = t l(Y_K) + t^2 <z_a, z_b> with l(Y_K) = <(Y_K)_a, z_b> + <z_a, (Y_K)_b>.
   (i) If l is not identically 0 on K, omega varies independently of t and its coefficient vector (0, 0, -2 x_d x_e, -2 x_c x_e, -2 x_c x_d) would
       be proportional to m; at t = 0 this is (0,0,-2,-2,-2), whose entries do not sum to 0: impossible.  So l == 0 and C(Y_K + t Z) = C(t Z).
   (ii) Degree 2 in t, components a, b: (3/2)(e_2 - m_b (m_a + m_b)) = mu m_a, (3/2)(e_2 - m_a (m_a + m_b)) = mu m_b (e_2 = e_2(m_c, m_d, m_e));
       if m_a != m_b: mu = (3/2)(m_a + m_b) and e_2 = (m_a + m_b)^2 = e_1^2; components c, d, e then give m_d m_e = m_c m_e = m_c m_d.  If all of
       m_c, m_d, m_e were nonzero they would be equal (= mu') with 3 mu'^2 = 9 mu'^2, i.e. mu' = 0; so at least two of them vanish: NEUTRAL columns.
   So NCOL_1 holds in the generic case with m_a != m_b.  Left: Pi strictly inside V (special kernels), m_a = m_b (needs degree 3/4), and the
   chart m_a = m_b = 0 is already neutral.  The exact runs (c21gk.py; reduced, case splits A/B) are heavy (~1 GB in 80 s).
 R11.6 (2,1) TWO-COLUMN FAMILY: GENERIC CASE COMPLETED BY HAND [rigorous; correction of a sign in R11.5(ii)].
   Correct degree-2 c-component: (3/2) m_d m_e + (3/2)(m_a + m_b)(m_d + m_e) + 2(m_a m_b - q) = mu m_c  (q := <z_a, z_b>), etc.
   (a) m_a != m_b: mu = (3/2)(m_a + m_b), e_2 = e_1^2 (e_k of m_c, m_d, m_e; e_1 = -(m_a + m_b)), and pairwise (m_d - m_c)(m_e - 2 e_1) = 0 etc.
       All equal => 3 mu'^2 = 9 mu'^2 => 0; exactly two equal (m_c = m_d) => m_e = -3 m_c/2 and e_2 = e_1^2 gives m_c = 0; pairwise distinct
       is impossible.  So m has zero entries.  [The conclusion of R11.5(ii) stands; its intermediate formula had a sign slip.]
   (b) m_a = m_b: pairwise (m_d - m_c)((3/2) m_e + 3 m_a + mu) = 0.  All equal => m proportional to (3,3,-2,-2,-2), q = -m_a^2, and then degree 3
       fails: 2 C_a + 3 C_c = -60 t^3 + (45/2) t^4 != 0 (explicit formulas of R11.5).  Exactly two equal => m_c (m_c + m_a) = 0 => a zero entry.
       Pairwise distinct impossible.
   => THEOREM (generic two-column (2,1) stratum): if K is a two-column (2,1) kernel with Pi = V, every (4,1) space L' = K + C Z has a zero entry
      of m (a NEUTRAL column).
   (c) (5,1), generic case [sketch, rigorous modulo a non-degeneracy]: for fixed (K, m) the conditions on Z modulo K are gauge-invariant:
      <u, P_Z> = 0, <p, P_Z> = <e, D_Z>, <d, D_Z> = 0, sum P_Z = m_a + m_b, sum D_Z = m_a - m_b (5 linear) and (|P_Z|^2 - |D_Z|^2)/4 = q
      (1 quadratic, q fixed by m) on the 5-dim quotient C^8 / gauge: finitely many Z unless the five functionals are dependent and the quadric
      is constant on the resulting line.  Then the pencil principle excludes (5,1) spaces of rank c = 1 over generic two-column (2,1) kernels.
   OPEN in this stratum: kernels with Pi strictly inside V (a closed condition on (u, d, p, e)); the non-degeneracy in (c); three-column (2,1)
   kernels; column-centred (5,1) over them.
STATUS 22:59: R11.4-R11.6: generic two-column (2,1) stratum settled by hand (NCOL_1; (5,1) via pencil modulo a non-degeneracy). Exact c21gk run heavy (~1 GB).
 R11.7 COLUMN-CENTRED SPACES OVER GENERIC TWO-COLUMN (2,1) KERNELS [rigorous].  Let K be a two-column (2,1) kernel with Pi = V and Z with c(Z) = 0
   such that K + C Z has defect C m with m_a != 0 or m_b != 0.  The K-K-Z cubic vector (0, 0, T_d + T_e, T_c + T_e, T_c + T_d) (R11.4, now with
   m_t replaced by c_t(Z) = 0) must vanish, so <pi, z_t> = 0 for pi in Pi = V: z_t is constant with column sum 0, i.e. z_t = 0 (t = c, d, e).
   Then K + C Z is a 4-dim column-centred space supported on columns a, b.  For such a space the deletion vector is (0, 0, -2w, -2w, -2w)
   (up to the factor of P_2), w = <y_a, y_b> (deleting a or b leaves one centred column), which is proportional to m only if w == 0; but then
   K + C Z would be a 4-dim isotropic subspace of (V (+) V, beta) (dim 6, maximal isotropic dim 3): impossible.
   => no column-centred 4-dim space with defect C m (m_a or m_b != 0) contains a generic two-column (2,1) kernel; in particular no column-centred
      (5,1) space does, except possibly with m_a = m_b = 0 (m supported on the other three columns -- left open).
   [R11.6(c) made rigorous] The five functionals (u,0), (p,-e), (0,d), (1,0), (0,1) on (P_Z, D_Z) in C^8 vanish on the gauge space
   G = span{(u,0), (p,e), (0,d)} (by <u,u> = <u,p> = <d,d> = <d,e> = 0, <p,p> = <e,e>, u,p,e,d in V) and are linearly independent on C^8
   (p in span(u, 1) would give p = c u, impossible as <p,p> = 1 != 0 = <u,u>); so they are a basis of G^perp = (C^8/G)^*, and for fixed
   (K, m) the generic-case extension Z (columns c, d, e = (m_t/4) 1, (z_a, z_b) modulo K fixed by the five linear conditions) is UNIQUE.
   => by the pencil principle: NO (5,1) space of rank c = 1 over a generic (Pi = V) two-column (2,1) kernel with m_a or m_b != 0.
   Gap: m_a = m_b = 0 (then the K-K-Z vector need not vanish); kernels with Pi strictly inside V.
   [numerical, R11 special locus] rank Pi < 3 occurs only at isolated-looking parameter pairs (al for u, ga for d): the octahedral line at
   infinity of the chart, and points such as (-0.103 + 1.911i, -0.238 + 0.556i), (-0.238 + 0.556i, 0.151 + 0.447i) (Nelder-Mead on the
   singular-value ratio; Pi depends only on (al, ga)).  So the special two-column (2,1) kernels form a small (finite-looking) set -- an exact
   finite check is the next step.
 R11.8 THREE-COLUMN (2,1) KERNEL, structure of the sample rows/r10/k21_s1_5.npy [numerical]: K = P (+) C Y_3 where P = K cap {column c = 0} is a
   strongly level PLANE on the two columns a, b containing the doubly centred element n = d(e_a - e_b)^T (d isotropic), and Y_3 has column c
   proportional to (1, -1, 0, 0)^T (non-isotropic); rows 0 and 1 of every element agree except in column c.  So three-column (2,1) kernels look
   like "two-column (2,1) plane + one two-row single-column direction": the K-K-Z and degree-2 arguments of R11.1/R11.4 should adapt (to do).
   [exact cross-check c21gk.py of the two-column case: DIED at the 2 GB cap (521 s); the hand proof R11.4-R11.6 covers the generic case.]
 R11.9 SPECIAL TWO-COLUMN (2,1) KERNELS (Pi strictly inside V) [modular p = 2147483629, rows/r11/special_p.sing, 0.2 s; over Q timed out].
   The locus rank Pi <= 2 is a CURVE in the (al, ga)-plane (u = u(al), d = u(ga) on the isotropic conic); its first equation factors as
   (al - ga)(al^2 + 4 al ga + ga^2) = 0 (decomposition running).  Component al = ga means d = u: then K = span{u e_a^T, u e_b^T, W} contains the
   two single-column elements u e_a^T, u e_b^T, and (SC1) (verified) gives, if m_a m_b != 0, <u, y_j> = 0 for every column of every Y in L'.
   These special kernels need their own (small) exact or hand treatment.
   [R11.9 continued] Hand decomposition of the special locus (mod p equations; generators g_1 = (al - ga)(al^2 + 4 al ga + ga^2), g_2, g_3):
   on al = ga both g_2 and g_3 vanish identically (a whole LINE: d = u); on al = lam ga, lam^2 + 4 lam + 1 = 0, g_3 gives
   ga^4 = (5 lam + 19)/(lam - 1): FINITELY many points.  On the line d = u: e = +-p + t u, so K = u^perp (x) e_a (+) C u (x) e_b (or a <-> b):
   a kernel spanned by single-column elements (X_a = u^perp degenerate, X_b = C u), depending only on u.  For it, (SC1) (m_a m_b != 0) gives
   z_j in span(u, 1) for j != a and z_a orthogonal to u; modulo K, Z = ((m_a/4)1, (m_b/4)1, al_j u + (m_j/4)1 ...); the row polynomial is
   Prod_i (sig + l_i) = sig'^4 + (p_3(u)/3) sig' M'^3 - (p_4(u)/4) M'^4 + nu (tau_1 sig' M'^2 - tau_2 M'^3) (e_1(u) = e_2(u) = 0), and the
   nu-part (zero a-entry) must vanish: either tau_1 = t(w,u,u) = 0 or al_c = al_d = al_e = 0.  Exact test rows/r11/chi3gen.py running.
STATUS 23:30: round 11 closing; RESULT ROUND 11 updated (A1-A6); chi3 runs (special line d = u) in background (<= 2 x 30 min, 0.4 GB).

# ROUND 12 (start 23:31 UTC). Targets: (1) isolated special two-column (2,1) kernels (CHI2-sized exact tests) + chi3 line verdicts;
#  (2) three-column (2,1) kernels (adapt R11.4-R11.6); (3) exact hand-off statement for m_a = m_b = 0, |supp m| = 3; (4) five-column invariant
#  formulation (resultant / elimination / orbit argument).
STATUS 23:31: round 12 started.
## R9.0 ADDENDUM (round 12) -- EXACT HAND-OFF to verifyfl for the case m_a = m_b = 0 (forwarded by the coordinator)
 Setting.  K = a 3-dim strongly level kernel of type (q,d) = (2,1) supported on two columns {a, b} (explicit family R10.7:
 K = span{u(e_a+e_b)^T, (p+e)e_a^T + (p-e)e_b^T, d(e_a-e_b)^T}, u, d isotropic, u.p = d.e = 0, p.p = e.e) -- and, when settled, the three-column
 (2,1) kernels R11.8.  rows has shown (R11.4-R11.7): if m_a != 0 or m_b != 0, every (4,1) space over K has a neutral column, no (5,1) space of
 rank c = 1 and no column-centred 4-dim space with defect C m contains K (generic K; special K in progress).
 WHAT IS NEEDED FROM THE TYPED PROGRAMME (the only remaining case for these kernels):
   (H)  Let m = (0, 0, m_c, m_d, m_e) (in the labelling a, b, c, d, e), |supp m| = 3, isotropic or not (a one-parameter family up to scale and
        S_3 on {c,d,e}).  There is NO column-centred 4-dim space K4 with deletion vectors in 24*1 + C m and NONZERO defect that contains a
        two-column (2,1) kernel K supported on the two NEUTRAL columns {a, b}.
   (H) implies: no (5,1) space with |supp m| = 3 contains such a K in ker c (rank c = 1: K4 = ker c; rank c = 0: take any 4-dim subspace through
   K, which has nonzero defect by Lemma SL).  In verifyfl's typing K4 has (q,d) in {(3,1), (2,2)} (it contains K of type (2,1)), so (H) is the
   restriction of [T31] + [T22] for |supp m| = 3 to spaces containing a doubly centred element d(e_a - e_b)^T on the two neutral columns.
   NOTE: for the three specific m already treated (m12m3, m11m2, iso) (H) follows from the completed typed results; it is needed for EVERY m
   with |supp m| = 3 (parametric in m_c : m_d : m_e), unless rows' reduction below closes it.
 rows' REDUCTION available to verifyfl [rigorous, R12.1]: in the generic case (Pi = V) the K-K-Z cubic gives <pi, z_t> = -(lam/2) m_t for all pi
 in Pi, hence the three non-kernel columns of the extension are PROPORTIONAL: z_t = m_t a (t = c, d, e) for one vector a with sum a = 1
 (for rank c = 1; for column-centred Z: z_t = m_t zeta with zeta in V).  So K4 = K + C Z with Z = (z_a, z_b, m_c a, m_d a, m_e a): a split-type
 extension on the support of m, small enough for a parametric exact run in (u, d, m_c : m_d).
## Section R12 (round 12)
 R12.0 ISOLATED SPECIAL TWO-COLUMN KERNELS, EXACT POINTS [rigorous hand computation + numerical check].  On the branch al = lam ga,
   lam^2 + 4 lam + 1 = 0, g_3 gives ga^4 = (5 lam + 19)/(lam - 1) = -(2 -+ sqrt3)^2 (for lam = -2 +- sqrt3), and then g_2 = -(ga/4)(lam^2 + 4 lam + 1)/(lam - 1)
   = 0 automatically.  Since 2 +- sqrt3 = (sqrt3 +- 1)^2/2:  ga = +-(sqrt3 +- 1)(1 +- i)/2, al = lam ga -- EIGHT points, all in Q(sqrt3, i);
   rank Pi = 2 exactly at all eight (numerical, singular values (52, 5.4, 0) etc.).  With variables sq3 (sq3^2 = 3) and ii (ii^2 = -1) the Galois
   sign choices are automatic, so two exact runs (ga -> -ga) cover all eight: rows/r12/c21s.py charts p, q (queued, 1 GB cap).
   The direct run over the whole special locus (chart f f with the rank minors, line removed by r4 (al - ga) = 1) exceeded the budget.
 R12.1 [rigorous] (used in the hand-off R9.0 ADDENDUM) m_a = m_b = 0, generic Pi = V: the K-K-Z vector (0, 0, T_d + T_e, T_c + T_e, T_c + T_d)
   = lam m with sum m = 0 gives T_t = -lam m_t, i.e. <pi, z_t> = -(lam/2) m_t for all pi in Pi = V: z_t = m_t a (t = c, d, e), one vector a.
 R12.2 THREE-COLUMN (2,1) KERNELS, first reduction [rigorous].  Write K = P (+) C Y_3 with P = K cap {column c = 0} a strongly level plane on the
   two columns a, b containing n = d(e_a - e_b)^T (as in the sample, R11.8), P = span{n, W'}, W' = w_1 e_a^T + w_2 e_b^T (<w_1,w_2> = 0,
   <d, w_2 - w_1> = 0).  For Y_1, Y_2 in P the K-K-Z vector is the two-column one, so if m_a or m_b != 0:  <pi, z_t> = 0 for pi in
   Pi_P = span{d o d, d o (w_2 - w_1), w_1 o w_2} (inside V) and t = c, d, e.  If Pi_P = V (generic), z_c, z_d, z_e are CONSTANT; columns d, e of every
   Y in L' are then constant (K vanishes there) while column c carries the single K-direction x of Y_3.  The closed-form analysis of R11.5 has to be
   redone with one extra varying column (c); not finished.
 R12.3 THREE-COLUMN (2,1) KERNELS: STRUCTURE [rigorous, assuming the sample's shape K = P (+) C Y_3, P = K cap {column c = 0} two-column on a, b,
   column c of K of rank 1 spanned by x].  Pairwise column orthogonality (degree 2) between column c and columns a, b gives x orthogonal to every
   a- and b-column vector of K; if <x,x> != 0 these lie in the plane x^perp.  The (a,b)-orthogonality makes the image of K in (x^perp)^2 an isotropic
   subspace of the 4-dim nondegenerate space (x^perp (+) x^perp, beta), hence of dim <= 2; so the a,b-part of Y_3 lies in that of P and
        K = P (+) C x e_c^T      (a SINGLE-COLUMN element in column c),
   P a two-column isotropic plane in (x^perp)^2 containing n = d(e_a - e_b)^T (d one of the two isotropic lines of x^perp), with the cubic conditions
   t(d,d,x) = t(w_1,w_2,x) = t(d, w_2 - w_1, x) = 0 (P = span{n, w_1 e_a^T + w_2 e_b^T}).  [matches the sample: column ranks (2,2,1).]
   Consequences for extensions L' = K + C Z: (SC1) for x e_c^T (m_c != 0) gives <x, y_j> = 0 for all j != c and all Y in L'; the two-column K-K-Z
   argument on P (m_a or m_b != 0) gives <pi, z_t> = 0, pi in Pi_P = span{d o d, d o (w_2 - w_1), w_1 o w_2}.  A small explicit family (x, then
   finitely many d, then W') -- next: CHI-style exact test or the closed-form analysis.
 R12.4 THREE-COLUMN (2,1) KERNELS: CLASSIFICATION (case <x,x> != 0) [rigorous].  Write x^perp = span(d, d') (the two isotropic lines, <d,d'> != 0),
   w_k = a_k d + b_k d'.  <d, w_2 - w_1> = 0 gives b_1 = b_2 =: b, and <w_1,w_2> = 0 gives b (a_1 + a_2) = 0.  Modulo n:
   (A) b != 0:  K = span{ d(e_a - e_b)^T, d'(e_a + e_b)^T, x e_c^T },  x proportional to d x d',  t(d,d,x) = t(d',d',x) = 0
       (exactly the X5 condition on the pair of isotropic lines of x^perp: finitely many configurations);
   (B) b = 0:   K = span{ d e_a^T, d e_b^T, x e_c^T },  x in d^perp, t(d,d,x) = 0 (a kernel SPANNED BY SINGLE-COLUMN ELEMENTS, isotropic d
       in two columns; a one-parameter family in the conic parameter of d).
   The case <x,x> = 0 (x isotropic) is separate (not treated).  Both families are explicit enough for CHI-style exact tests; in (B) (SC1) applies to
   all three generators (m_a, m_b, m_c != 0 give columns orthogonal to d resp. x).
STATUS 23:38: R12.0-R12.4 written (special points exact in Q(sqrt3,i), hand-off statement, three-column classification); 4 explicit special-point runs (1 GB cap) in progress.
 R12.5 A CLEAN (5,1) CRITERION [rigorous, 4 lines].  Let K be strongly level (3-dim) and L a (5,1) space containing K, with defect line Cm.
   Linear part: p_1(Y)_j = sigma(Y) - s_j(Y) lies in Cm for Y in L (s_j = column sums, sigma = sum s_j), so Y -> (sigma - s_j)_j has a kernel of
   dim >= 4 in L, and that kernel is exactly the set of column-centred elements of L (sigma - s_j = 0 for all j forces all s_j = 0); it contains
   K.  A 4-dim L'' with K < L'' < ker is a 4x5 level space with C(L'') = Cm (not 0, by Lemma SL), i.e. a COLUMN-CENTRED (4,1) extension of K,
   and m is in 1^perp (4x5 level <=> all p_k in 1^perp, R1/section D).
   HENCE: if K has NO column-centred (4,1) extension K + CZ (Z with zero column sums, C(K + CZ) = Cm, sum m = 0), then NO (5,1) space contains K.
   This bypasses the pencil argument and the neutral-column case analysis entirely, and the cc systems are much smaller than the cs ones.
   Implementation rows/r12/kgen.py (mode cc: column sums of Z = 0, sum m = 0, chart m_K0 = 1, all (s,t)-coefficients of c_j - m_j c_K0;
   gauge Z mod K by 3 entries with a Rabinowitsch variable on the coordinate determinant; self-check that K is strongly level).
   CALIBRATION: dropping "sum m = 0" the same systems have solutions (e.g. A1, chart m_c: a 2-dim family with m = (0,0,1,1,1)), so the
   systems are not vacuous; the sum-m condition is what kills them.
 R12.6 THREE-COLUMN (2,1) KERNELS OF TYPE (A) ARE EXCLUDED [exact: Groebner bases over Q, rows/r12/kA_Q.out; plus 3 primes kA_primes.out].
   (A) solutions x (rigorous, Groebner over Q, famA2.py, all charts): exactly the 10 lines e_i - e_j and 3e_i - 1 (up to S_4: x = e_1 - e_2 with
   d, d' = (1,1,-1 +- sqrt(-2), -1 -+ sqrt(-2)) [A1]; x = (1,1,1,-3) with d, d' = zeta, zetabar [A2]; the conjugate kernel (d <-> d') is the
   Galois conjugate, covered by the symbolic s2 / om).  kgen.py A1, A2, mode cc, charts m_a, m_c, m_d (m_b, m_e by the symmetries a <-> b,
   d <-> e of K): 1 in the ideal OVER Q in every chart.  So no column-centred (4,1) extension, hence (R12.5) NO (5,1) SPACE CONTAINS A1 OR A2.
   (cs mode, 3 primes: every (4,1) extension has a neutral column; solution sets 1- or 2-dim with m two- or three-column.)
 R12.7 GAUGE BUG FOUND in the round-12 explicit-point runs rows/r12/x_*.sing (c21s.py charts p/q): for eps = +1 and e-sign +1 the gauge
   determinant det M_K (positions (0,0),(1,0),(0,1)) VANISHES at the special points, so the Rabinowitsch chart r1 det M_K = 1 is empty and a
   "unit" verdict there would be vacuous.  Those runs were stopped before finishing (no verdict recorded); replaced by kgen.py spec S+/S-
   which PRINTS the gauge determinant and uses the alternative positions (2,0),(3,0),(2,1) where the first vanishes (checked numerically for
   all 16 point/sign combinations: one of the two determinants is 32, 55.4 or 111 in absolute value).
   AUDIT NOTE for the round-11 generic runs (c21g*.py): there det M_K is a Rabinowitsch chart over the whole family, so the vanishing locus is
   a proper closed subset; those runs only claimed the generic case (the hand proof R11.4-R11.6 is the actual argument), unaffected.
STATUS 23:56: A1/A2 three-column kernels excluded over Q (R12.6); clean (5,1) criterion R12.5; gauge bug in x_* runs found and replaced (R12.7); special points (cc, 3 primes) and family B parametric (1.5 GB cap) running.
 R12.8 LEMMA 3COL [rigorous, hand]: a 3-dim strongly level space K supported on exactly three columns a, b, c HAS A COLUMN OF RANK 1.
   Notation: A_j : K -> V the column maps; the strongly level conditions on 3 columns are exactly: B_jl(Y,Y') := <A_j Y, A_l Y'> is SKEW on K
   for each pair (pairwise Gram, polarized), and t(y_a,y_b,y_c) = 0 polarized (no degree-4 terms on 3 columns).  <,> on V is nondegenerate.
   (i) No column of rank 3: if A_a is invertible, identify K = V via A_a; then A_b, A_c are <,>-skew: A_b v = beta x v, A_c v = gamma x v
       (Walsh coordinates, dot form).  B_bc skew means 2(beta.gamma) I = beta gamma^T + gamma beta^T (as symmetric forms); the right side has
       rank <= 2, so beta.gamma = 0 and beta gamma^T + gamma beta^T = 0, forcing beta = 0 or gamma = 0: a zero column.
   (ii) Two columns of rank 2 have the same kernel line: let rk A_a = rk A_b = 2, k_j = ker A_j.  For Y in k_b, B_ab(Y',Y) = 0 for all Y', so
       by skewness Y is in the radical of B_ab; likewise k_a.  B_ab != 0, since B_ab = 0 means im A_a orthogonal to im A_b, two planes in the
       3-dim nondegenerate V - impossible.  A nonzero skew 3x3 form has a 1-dim radical, so k_a = k_b.
   (iii) If all three columns had rank 2, then k_a = k_b = k_c, and that element of K would have all three columns zero, i.e. would be 0.
   So some column, say c, has rank 1 (rank 0 means fewer columns): column c of K is C x.
   COMPLETION OF THE CLASSIFICATION (R12.3-R12.4 made unconditional): polarizing G_ac, G_bc gives columns a, b of K inside x^perp.
   * <x,x> != 0: K = P (+) C x e_c^T, P a beta-Lagrangian plane in (x^perp)^2 (R12.3); for type (2,1) the row-sum-zero element lies in P
     (its column-c coefficient must vanish because x is not in x^perp), so P contains d(e_a - e_b)^T, d isotropic, and R12.4 gives (A) or (B).
   * <x,x> = 0: x^perp = span(x, y0), <y0,y0> != 0, and the a,b-coefficients of y0 form a beta-isotropic image in C^2 with the hyperbolic form,
     so column b (say) is also inside C x; the cubic f(Y) = t(y_a,y_b,y_c) on the 4-dim space {(al1 x + be1 y0, al2 x, ga x)} equals
     al2 ga (al1 t(x,x,x) + be1 t(y0,x,x)) and must vanish on the hyperplane K; t(x,x,.) cannot vanish on x^perp (sg(x,x) is never
     proportional to an isotropic x, R12.4), so K = {be1/al1 fixed} = span{w e_a, x e_b, x e_c} with w in x^perp, t(w,x,x) = 0: family (B) with
     the roles d := x (isotropic, in two columns) and w in the third column.  (The hyperplanes al2 = 0, ga = 0 give two-column kernels.)
   RESULT: every three-column (2,1) kernel is, up to row/column symmetries, A1, A2 (or their Galois conjugates) or a member of the
   one-parameter family (B): span{d e_a, d e_b, x e_c}, d isotropic, x = d x sg(d,d) (Walsh).  [rigorous]
   NUMERICAL CROSS-CHECK (k3num2.py, 60 starts with row-sum rank <= 2): column-rank types found: (0,2,3) [two-column family, local dim 2],
   (1,2,2) [local dim 0 = (A)], (1,1,1) [local dim 1 = (B)]; nothing else.
STATUS 00:01: Lemma 3COL (R12.8) proved: three-column (2,1) kernels = A1, A2, family B. Special points cc: prime 1 all units so far; family B parametric chart m_a unit, chart m_c running (0.8 GB).
 R12.9 ISOLATED SPECIAL TWO-COLUMN KERNELS: NO COLUMN-CENTRED EXTENSION [modular; prime 1 complete, primes 2-3 running].
   *** INCOMPLETE (flagged round 13, R13.3): the runs used ga = eps (1+sq3)(1+ii)/2 with the SAME ii as in the conic, which covers only 4
   *** of the 8 points per choice of i; the other 4 have the factor (1 - ii).  The Galois argument below does not repair this.  Replaced by R13.3.
   kgen.py spec S+/S- (e-sign), argument eps (ga -> -ga), with sq3, ii replaced by square roots of 3 and -1 mod p (primes p = 1 mod 12:
   2147482621, 2147475601, 1001197); one root choice per prime suffices because the system is defined over Q and the statement for one
   embedding of Q(sqrt3, i) transfers to its Galois conjugates.  Gauge determinant printed and nonzero in every run (32, 540994950, ...).
   Charts m_a (covers m_b via a <-> b, which maps e -> -e, i.e. S+ <-> S-) and m_c (covers m_d, m_e).  p = 2147482621: all 8 runs UNIT
   (rows/r12/kS2.out).  With R12.5: NO (5,1) SPACE CONTAINS AN ISOLATED SPECIAL TWO-COLUMN KERNEL (modular, pending primes 2-3).
 R12.10 THEOREM (H) FOR TWO-COLUMN KERNELS, BY HAND [rigorous].  K a two-column (2,1) kernel on {a,b} OFF THE SPECIAL LOCUS (Pi = V and
   d not parallel to u).  Then K has NO column-centred (4,1) extension with m_a = m_b = 0.  Together with R11.7 (none with m_a or m_b != 0)
   and R12.5: NO (5,1) SPACE CONTAINS A GENERIC TWO-COLUMN (2,1) KERNEL.  (So the hand-off (H) of the R9.0 ADDENDUM is no longer needed for
   generic two-column kernels; it is replaced by the exact special-kernel runs R12.9 / U-line.)
   Proof.  Z column-centred, m = (0,0,m_c,m_d,m_e), m_c + m_d + m_e = 0, Y_K = (k_a, k_b) in K.  All columns have zero sums, so the degree-2,
   3, 4 parts of the deletion vector are  -2 sum_{pairs} <y_i,y_l>,  2 sum_{triples} t(y_i,y_j,y_l),  perm of the four columns.
   (1) K-K-Z (R12.1): z_t = m_t zeta (t = c,d,e), zeta in V (uses Pi = V and column-centredness: z_t - m_t zeta is in V cap C1 = 0).
   (2) (1,1) part: component a and b vanish (sum_t m_t = 0); component t equals -2 beta(Y_K, Z) + 2 m_t <k_a + k_b, zeta> with
       beta(Y_K,Z) = <k_a,z_b> + <k_b,z_a>.  Proportionality to m (whose c,d,e-part sums to 0) forces beta(Y_K, Z) = 0 for all Y_K.  K is a
       beta-LAGRANGIAN of (V+V, beta) (R10.7), so (z_a, z_b) lies in K's (a,b)-image: modulo K, z_a = z_b = 0 and Z = zeta m^T.
   (3) (2,0) part: component k is -2 <zeta,zeta> (e_2 + m_k^2), e_2 = e_2(m_c,m_d,m_e).  Component a: <zeta,zeta> e_2 = 0; if <zeta,zeta> != 0
       then e_2 = 0 and (m_t^2) would be proportional to (m_t) on c,d,e - impossible for m != 0 with zero sum.  So zeta is isotropic.
   (4) (1,2) part (one K factor, two Z factors): component a = 2 e_2 tau_b, component b = 2 e_2 tau_a (tau_i := t(k_i, zeta, zeta)).
       If e_2 != 0: tau_a = tau_b = 0 on K; the a- and b-columns together, {u, d, p+e, p-e}, span V (else p, e lie in span(u,d), which
       contradicts u.p = 0, p.p = 1 when u, d are independent), so sum_r x_r zeta_r^2 = 0 on V, i.e. zeta_r^2 = const; with sum_r zeta_r^2 = 0 this gives zeta = 0.
       If e_2 = 0: m is isotropic on {c,d,e}, m ~ (1, om, om^2), so m_c m_d m_e != 0.
   (5) (1,3) part (one K factor, three Z factors): component b = m_c m_d m_e perm(k_a, zeta, zeta, zeta) = 6 m_c m_d m_e phi(k_a),
       phi(x) = sum_r x_r prod_{s != r} zeta_s; components c,d,e vanish (a zero column of Z is involved); component a likewise gives phi(k_b).  So phi = 0 on the a- and b-columns,
       which span V: (prod_{s != r} zeta_s)_r is in C1.  If all zeta_s != 0 this forces zeta in C1 cap V = 0; if zeta_1 = 0 then zeta_2 zeta_3 zeta_4
       = 0 too, zeta = (0,0,x,-x), isotropic only for x = 0.  So Z = 0 modulo K: no extension.  QED
   (The (2,2) part forces perm(k_a,k_b,zeta,zeta) = 0 on K as well; not needed.)
## R9.0 ADDENDUM-2 (round 12, after R12.10): the hand-off (H) above is WITHDRAWN for two-column kernels -- generic ones are settled by hand
   (R12.10), the special ones by the exact all-m column-centred runs (R12.9 isolated points; the line d = u: kgen spec U/Ui).  For the
   three-column kernels the kgen cc runs cover every m (A1/A2 done over Q; family B in progress).  So, once B and U are confirmed, rows needs
   NOTHING from verifyfl's typed programme for the (2,1) kernel stratum.
 R12.12 FIVE COLUMNS (target 4) -- NO DECISION THIS ROUND.  Reformulation only [structure, not a proof]: with unit quaternions q_j (N(q) =
   q.q = 1) the data are 5 signed points on the quadric N = 1 of C^4 with  sum_j eps_j Q_rs(q_j) = 0  (9 quadrics Q_rs = Ad(q)_rs -
   (3/sum eps) delta_rs N)  and  sum_j eps_j G_k(q_j) = 0  (7 sextics G_k = (rho_3(Ad q) f)_k - (3/sum eps) f_k N^3, f a rotated octahedral
   cubic).  So it is a signed 5-point cubature problem (moments of degree 2 and 6 in prescribed isotypic components): a route via apolarity
   (the ideal of 5 points of P^3 contains the quadrics/sextics in a computable pattern), or via the generic rank of the 7 x 5 matrix
   (G_k(q_j)), could give a small determinantal elimination; not attempted.  The big-slot SUMQ5 runs remain the only decision procedure.
STATUS 00:08: R12.10 hand proof of (H) for generic two-column kernels; hand-off withdrawn (R9.0 ADDENDUM-2). Special points: prime 1 8/8 unit, prime 2 7/8 unit so far. Family B prime 1: charts m_a (both gauges, gcd of gauge dets = 1) and m_c (gauge 0) unit; gauge 1, infinity, line U, primes 2-3 queued (chain runB2 -> runU -> runBU23).
 R12.11 FAMILY B AND THE LINE d = u -- column-centred tests (kgen.py, mode cc) [modular].
   Family B (parametric gamma on the conic, i numeric mod p): charts m_a (all m with m_a != 0; m_b by a <-> b) and m_c with m_a = m_b = 0
   (mz=0,1; m_d, m_e by symmetry; m two-column on {d,e}: TC5), each in two linear gauges whose Rabinowitsch determinants (degree 8 in gamma)
   are COPRIME (gcdB.sing: gcd = 1), so together they cover every finite gamma; plus the point at infinity d = (1, i, 0) (spec Bi).
   p = 2147482621: ALL SIX RUNS UNIT (40-230 s, <= 0.27 GB; rows/r12/kBpar.out).  => NO (5,1) SPACE CONTAINS A FAMILY-B KERNEL (1 prime so
   far; primes 2147475601 and 1001197 queued in runBU23.sh -> kBU23.out).
   Line d = u (K_u = span{u e_a, p e_a, u e_b}, not a <-> b symmetric): charts m_a; m_b with m_a = 0; m_c with m_a = m_b = 0; two gauges + Bi-type
   point at infinity (runU.sh -> kU.out), then primes 2-3.
   Hand cross-check for the line, chart m_a != 0 [rigorous]: the (1,1) parts for y e_a (y in u^perp) force z_k = tau_k u (k != a) and then the
   (1,1) part for u e_b forces z_a in u^perp, so modulo K, Z = u (0,0,tau_c,tau_d,tau_e); the s_2 s_3 t- and s_1 s_3 t-coefficients of the cubic
   part are t(p,u,u) (0,0,tau_d+tau_e,tau_c+tau_e,tau_c+tau_d) and t(u,u,u) (same vector); t(.,u,u) does not vanish on u^perp = span(u,p)
   (R12.4), and proportionality to m (m_a != 0, component a of these vectors is 0) forces tau = 0: no extension.
 R12.9 UPDATE: special isolated points -- ALL 24 RUNS UNIT at the three primes 2147482621, 2147475601, 1001197 (8 per prime = eps x e-sign x
   chart), every gauge determinant nonzero, every strong-levelness self-check 0 (rows/r12/kS2.out).  [modular, 3 primes]
 R12.11 UPDATE (line d = u, p = 2147482621):
   * gauges: the two position gauges share a quadratic factor in al = the locus u.rA = 0, where p = u x rA degenerates to a multiple of u
     (K would be 2-dim); spec U2 (p = u x rB) covers it: gcd(g0, g1, h0) = 1 (gcdU.sing).
   * chart m_a (gauges 0, 1, U2, point at infinity): UNIT.  chart m_b with m_a = 0 (gauges 0, 1, U2, infinity): UNIT.
   * chart m_c with m_a = m_b = 0: NOT unit -- dim 1.  minAssGTZ (p = 1001197, gauges 0 and U2): 12 components, EVERY ONE with a TWO-COLUMN
     defect line m = (0,0,1,0,-1) or (0,0,1,-1,0) (6 each); at infinity: unit.
   So every column-centred (4,1) extension of K_u has a two-column m, and by R12.5 + TC5 NO (5,1) SPACE CONTAINS K_u.  [modular, 1 prime
   for the unit charts; primes 2-3 queued: runBU23.sh + runU2_23.sh -> kBU23.out]
   R12.5' (the criterion as used): if every column-centred (4,1) extension of K has a two-column m (or none exists), no (5,1) contains K.
 R12.11 family B, prime 2 (2147475601) so far: charts m_a (gauges 0, 1) and m_c (gauge 0) UNIT; rest running.
STATUS 00:16: special points 24/24 unit (3 primes); family B prime 1 complete (unit), prime 2 partial (unit); line d = u: only two-column m (TC5). Writing final report.

# ROUND 13 (start 00:17 UTC). Targets: (1) the (2,1) stratum in char 0 (exact over Q(zeta12)/Q(i), or a projective single-prime
#  cover for RED-p); (2) one-paragraph "what remains in PROOF-MAP leaf 3" for verify2 on top of the RESULT block; (3) five columns: smaller exact
#  formulation (7x5 determinantal route / fix the octahedral eigenvector first) under the 2 GB cap.
STATUS 00:17: round 13 started; runBU23 (primes 2-3 for B/U) still running in the background.
## Section R13 (round 13)
 R13.1 FAMILY B: REDUCED COLUMN-CENTRED SYSTEMS [rigorous reductions].  K = span{d e_a, d e_b, x e_c}, d on the conic (Walsh dW(ga), point at
   infinity (1,i,0)), x = d x sg(d,d).  DEGENERATE POINTS: if d1 d2 d3 = 0 (Walsh; ga in {0, +-1, +-i} and ga = infinity) then x is parallel
   to d and K = d (x) span(e_a,e_b,e_c) is a chi (x) C^M kernel of the (1,2) stratum, already excluded for all (5,1) (R10.6, R11.2).  So assume
   d1 d2 d3 != 0; then x, d are independent, x is not 0 (checked exactly, gcdBQ.sing), d^perp cap V = span(d,x), {d,x}^perp cap V = C d.
   Z column-centred, m in 1^perp, R := sum_k z_k.  The (1,1)-part for a single-column element y e_j of K is the vector with entries
   -2 <R - z_j - z_k, y> (k != j) and 0 at j; it lies in C m.
   CHART A (m_a = 1).  y e_j = d e_a: entry a of m is nonzero, so the vector is 0: <z_k, d> = <R - z_a, d> for all k != a, and summing, all are 0.
     d e_b: entries are 0 at a, b and -2<z_a,d> at c, d, e; proportional to m with m_a != 0 forces <z_a,d> = 0.  So all z_k lie in span(d,x),
     and modulo K:  Z = (aa x, ab x, ac d, ad x + bd d, ae x + be d)  (7 unknowns, canonical: no gauge chart needed).
   CHART C (m_a = m_b = 0, m_c = 1).  x e_c: <z_k, x> = 0 for k != c (same argument).  d e_a: entry b gives <R - z_a - z_b, d> = 0, then the
     entries at c, d, e are -2(<z_b,d> - <z_t,d>) = lam m_t; summing over t (sum m_t = 0) gives <z_b,d> = 0; likewise <z_a,d> = 0.  So
     z_a, z_b lie in {d,x}^perp = C d, i.e. vanish modulo K; z_d, z_e lie in x^perp; z_c is taken modulo x with the gauge r.z_c = 0
     (r = rA or rB, Rabinowitsch on r.x; the two gauges have NO common zero at a nondegenerate gamma: exact, gcdBQ.sing).
   m_b != 0 follows from chart A by the symmetry a <-> b of K; m_a = m_b = m_c = 0 means m two-column (TC5).
   Generator rows/r12/bred.py (adds the Rabinowitsch rd d1 d2 d3 = 1; saturates by the Z-unknowns).  Mod p the reduced systems take 0.3 s
   (chart A) and 27 s (chart C), against 40-230 s for the full kgen systems.
 R13.2 THE LINE d = u IN CHARACTERISTIC 0 [rigorous: hand reductions + exact Groebner over Q(i)].  K_u = u^perp (x) e_a + C u (x) e_b,
   u on the conic.  Basis of V valid for EVERY finite al: u, p = (al, i al, 1) (= u'/2: <p,u> = 0, never parallel to u), w = (1, i, 0)
   (<w,u> = -2, <w,p> = 0); at infinity u = (1,i,0), p = (0,0,1), w = (1,-i,0).  So no gauge charts are needed.
   CHART m_a != 0: no extension, by hand (R12.11 cross-check, now the proof).
   CHART m_a = 0, m_b = 1: u e_b gives <z_k,u> = 0 (k != b); z_a in u^perp vanishes mod K; the (1,1)-vector of u e_a is (0,0,-2b,-2b,-2b) with
     b = <z_b,u>, and proportionality to m (m_b != 0) gives b = 0.  So Z = (0, eta p, z_c, z_d, z_e) with z_t in span(u,p).
   CHART m_a = m_b = 0, m_c = 1: the (1,1)-vectors of y e_a (y in u^perp) give R' := z_c + z_d + z_e in C u, then <z_b, y> = 0, so z_b in C u
     (vanishes mod K) and z_t = m_t zeta + al_t u; the (1,1)-vector of u e_b gives <z_a,u> = 0, so z_a vanishes mod K.
   Exact runs (rows/r12/ured.py, P = 0, ii^2 + 1 = 0, < 0.2 s each): chart B finite and infinity: UNIT.  Chart C finite: solutions exist,
   but after saturation by m3 (1 + m3) (i.e. m_d m_e != 0) the ideal is UNIT, so every extension has m two-column; at infinity UNIT.
   => every column-centred (4,1) extension of K_u has a two-column m; with R12.5' (TC5): NO (5,1) SPACE CONTAINS K_u, IN CHARACTERISTIC 0.
 R13.3 THE SPECIAL LOCUS, EXACTLY [exact over Q(i), speclocQ.sing, speclocInf.sing].  With the canonical p = (al, i al, 1), e = (ga, i ga, 1)
   (Pi does not depend on p mod u, e mod d, or the signs), rank Pi <= 2 on the finite chart is exactly: the line al = ga, plus 4 prime
   components {ii^2 + 1, ga^2 -+ ga ii -+ ga -+ ii (four sign patterns), ga^5 + 4 al + 15 ga}, each of degree 4: 8 points for each choice of i,
   namely ga = +-(1 +- sqrt3)(1 +- i)/2 (BOTH signs of the factor (1 +- i), independently of the i in the conic) and al = (-2 + sqrt3') ga.
   At the points at infinity of the chart: u = (1,i,0) with d finite, or d = (1,i,0) with u finite, is never special (ideal = 1); u = d =
   (1,i,0) lies on the line.  So the special locus is: the line d = u (R13.2, settled in char 0) and 8 isolated points (16 geometric points
   counting both i).
   CORRECTION: R12.9 tested only the 4 points with factor (1 + ii) (see the flag there).  kgen.py now has the switch cj=1 for (1 - ii).
   RED-p COVER (running, runSP1.sh -> kSP1.out): all 16 geometric points (sq3 = +-r3, ii = +-ri, eps, cj) x 2 e-signs x charts m0, m2 (full),
   at P1 = 2147483629, with a gauge whose determinant is checked nonzero.  The point scheme is finite over Z[1/2] (monic equations in ga, ii;
   al = -(ga^5 + 15 ga)/4), the kernel K(pt) is a morphism to Gr(3), and the column-centred extension data live in Gr(4) x P^4: so the
   scheme X_S of (point, e-sign, L'', m) is proper over Z[1/2] and Lemma RED-p (NOTES-verifyfl R7.1 form) applies if every chart is unit at P1.
   (The exact run over Q(zeta12) of chart m0 exceeded 0.94 GB in 2.3 min and was stopped.)
 R13.1' FAMILY B IN CHARACTERISTIC 0 [rigorous: reductions + exact Groebner over Q(i)].  Extra observation: in Walsh coordinates
   x.x = -(d.s)^2 with s = sg(d,d) and d.s = 6 d1 d2 d3, so for NONDEGENERATE gamma (d1 d2 d3 != 0) x is non-isotropic and
   x^perp cap V = span(d, s) (s.x = (d x s).s = 0; s is never parallel to d).  CHART C refined: z_d, z_e in x^perp, z_c taken modulo x in
   span(d,s), and <z_t, d> = mu m_t (t = c,d,e; from the (1,1)-vectors of d e_a, d e_b) with <s,d> = 6 d1 d2 d3 != 0, so
        Z = d a^T + mu s m^T,  a = (0,0,a_c,a_d,a_e)   (4 unknowns + m_d; no gauge).
   Exact runs over Q (ii symbolic, rd d1 d2 d3 = 1), rows/r12/bred.py:  chart A (m_a = 1): dim 4 before, UNIT after Z != 0 saturation (0.3 s);
   chart D (= refined C; m_a = m_b = 0, m_c = 1): UNIT after Z != 0 saturation (0.09 s).  Also unit mod P1 (0.07 s).
   Degenerate gamma (incl. infinity): K = d (x) C^3 is in the (1,2) stratum (R10.6/R11.2, exact over Q).  m_b != 0 by a <-> b; m supported on
   {d,e} only: TC5.  => NO (5,1) SPACE CONTAINS A FAMILY-B KERNEL, IN CHARACTERISTIC 0.  (The unreduced exact runs, q_B0g0 and qbC0, exceeded
   0.4-0.85 GB / 6 min and were stopped as superseded.)
STATUS 00:31: line d = u and family B settled in char 0 (R13.1', R13.2); special locus classified exactly (R13.3); R12.9 found INCOMPLETE (4 of 8 points per i) and flagged; RED-p cover of all 16 special points at P1 running.
 R13.3 (cont.) RED-p bookkeeping: at P1 the 16 points (sq3 = +-59644493, ii = +-629208553, eps, cj) are DISTINCT, all lie on the exact
   locus components, and the denominators u.rA, d.rB (used for p, e in kgen spec S) are nonzero; the point scheme is free of rank 16 over
   Z[1/2], so these are ALL its geometric points mod P1.  Charts m0 (m_a != 0) and m2 (m_c != 0; m_d, m_e by the S_3 symmetry on {c,d,e},
   valid in every characteristic) cover every m != 0 with sum m = 0 (at least two nonzero entries, so one of a, c, d, e).  Gauge chosen per
   point by rows/r12/gsel.py (determinant nonzero mod P1; kgen prints it again).
STATUS 00:42: leaf-3 summary drafted at the top (RESULT ROUND 13); RED-p cover running (worker 0; worker 1 paused while the 5-column census runs).
 R13.4 (2,1) KERNELS ON FOUR OR FIVE COLUMNS -- NOT COVERED [numerical census only].  Lemma 3COL and R10.7 classify (2,1) kernels on <= 3
   columns; nothing so far excludes (2,1) kernels supported on 4 or 5 columns (R10.7's census had 7 starts; PL4 / (PL) concern q = 3 only).
   Census rows/r13/k21five.py (explicit P_2, P_3, P_4 of the column-centred deletion vector at 18 random points of K, a doubly centred
   element, LM): 7 starts in 15 min: (2,1) found 4 times, always on 2 or 3 columns ((2,3,0,0,0) x3, (2,2,1) x1); the others were (1,2) or
   degenerate.  Weak evidence only.  This is a gap in leaf 3 and is listed in the leaf-3 summary.  A hand route: the degree-2 identity
   <A_k Y, rho(Y)> = <A_k Y, A_k Y> (all k, Y) makes every column of the doubly centred element n isotropic, with sum 0; then a case split on
   the column-rank pattern as in Lemma 3COL.  Not attempted this round.
 R13.5 FIVE COLUMNS -- a smaller exact formulation (target 3 of round 13) [structure; calibration pending].
   (a) "Fix the octahedral eigenvector first" does not shrink the system by itself: SUMQ already fixes c = x1 x2 x3 (finite stabilizer);
       fixing instead a normal form of the frame (3 parameters of O(3)) and letting the eigenvector h run over the orbit of c (orbit
       equations (h,h)_4 = 0 for the binary sextic, 5 quadrics, + normalization) ADDS 7 variables.  It helps only together with an explicit
       rational parametrization of the 3-dim frame moduli (then 3 + 7 unknowns, linear (A - 3) h = 0 + 6 orbit equations), e.g. via the
       Waring form of the frame: Delta = sum_j eps_j (q_j . y)^2 with Delta = diag(sigma, cc, cc, cc), i.e. U = Delta^(1/2) W with W D W^T = I
       (4 rows of a D-orthogonal 5x5 matrix, Cayley-parametrizable) plus the 4 independent column-norm conditions.  Not implemented.
   (b) VERONESE VARIABLES (rows/r13/sumqv.py): Q_j = q_j q_j^T.  All SUMQ equations are even in each q_j, B_j = eps_j Ad(q_j) is LINEAR in Q_j,
       the frame equations and the norms are LINEAR, the summed cubic has degree 3 (instead of 6), and rank Q_j <= 1 is 20 quadrics per
       column; the 2^NC sign symmetry (q_j -> -q_j) is quotiented out.  50 variables of which 14 are eliminated linearly.  Calibration on
       3 columns (++- dim 1, --- dim 2 expected) and 4 columns (---- unit expected; sumq.py: 145 s, 0.13 GB) queued after the RED-p cover.
 R13.6 LEMMA RS (structure of ANY (2,1) kernel, any number of columns) [rigorous, hand].  K 3-dim strongly level, R := rho : K -> V
   (row sums) of rank 2, A_k : K -> V the column maps (all 5 slots; A_k = 0 off the support), matrices w.r.t. a basis of K and an orthonormal
   basis of V (Walsh, dot form).
   (i) The degree-2 conditions are exactly  A_k^T R + R^T A_k = 2 A_k^T A_k  for every k  (polarized <y_k, rho(Y) - y_k> = 0).
       Equivalently, with M_k := R - 2 A_k:   M_k^T M_k = R^T R   for every k,   and  sum_k M_k = 3R.
       (Principal case R invertible: M_k = B_k R, B_k = 1 - 2 A_k R^{-1} orthogonal, sum B_k = 3 -- the known frame.)
   (ii) P := rho(K) is DEGENERATE: P = u^perp for an isotropic u.  Proof: let n span ker R; M_k^T M_k n = R^T R n = 0 gives <M_k n, M_k Y> = 0
       for all Y.  If P were nondegenerate, Gamma = R^T R has rank 2, the images M_k e1, M_k e2 (Re1, Re2 a basis of P) have the same
       nondegenerate Gram matrix, so they span a nondegenerate plane Q_k, and M_k n is isotropic and orthogonal to Q_k, hence 0 (Q_k^perp is a
       nondegenerate line).  Then A_k n = -(M_k n)/2 = 0 for all k, i.e. n = 0.  Contradiction.
   (iii) Normal form: basis e1, e2, n of K with R e1 = u, R e2 = w (<w,w> = 1, <w,u> = 0), R n = 0, so R^T R = E_22.  M_k^T M_k = E_22 means:
       m_k := M_k e2 is a unit vector and M_k e1, M_k n are isotropic, orthogonal to each other and to m_k, hence on ONE isotropic line of
       m_k^perp:   M_k e1 = al_k f_k,  M_k e2 = m_k,  M_k n = be_k f_k  (f_k isotropic, <f_k, m_k> = 0),
       with  sum_k al_k f_k = 3u,  sum_k m_k = 3w,  sum_k be_k f_k = 0.   Columns: A_k e1 = (u - al_k f_k)/2, A_k e2 = (w - m_k)/2,
       A_k n = -be_k f_k/2.  Column k is zero iff al_k f_k = u, m_k = w, be_k = 0.
   (iv) Degree 3 in this form [rigorous algebra]: with r = RY, x_i = M_i Y, theta = t(r,r,r), the condition for the deleted column k is
        -(3/2) theta + (3/2) t(r,r,x_k) - t(r,x_k,x_k) + t(x_k,x_k,x_k) + (1/2) sum_i t(x_i,x_i, r - x_k) = 0,
       and the sum over k is the SUMMED CUBIC  sum_k t(x_k,x_k,x_k) = 3 t(r,r,r)  (same as the principal one).
   So the (2,1) problem on any support is a "degenerate frame" problem with 4 parameters per column (f_k on the conic, m_k in f_k^perp,
   al_k, be_k), much smaller than the raw Grassmannian.  Census in these coordinates: rows/r13/k21red.py (running).
 R13.3 RESULT so far: the RED-p cover at P1 has 63/64 charts UNIT (gauge determinants nonzero, strong-levelness self-check 0 in all 63).
   The 64th chart (sq3 = +r3, ii = +ri, eps = 1, cj = 0, e-sign +, chart m0, gauge 1) did not run out of memory.  Its timeout clock kept
   running while I paused worker 1 with SIGSTOP during the census, so it was killed on resume ("halt 1").  It is a FAILURE TO RUN, not a
   surviving chart.  Rerun now (runSP1fix.sh, 1 GB, 25 min).  (At prime 2147482621 the same kernel/chart was unit in 106 s, kS.out.)
 R13.7 FYI from the coordinator (ncol R2.14: no (5,1) contains e_i m^T with m free of zeros) -- no effect on leaf 3 or on (PL): the kernels
   here are column-centred 3-spaces, and single-row elements e_i m^T (column sums m != 0) lie in neither K nor the column-centred part L''
   used in R12.5; it may shorten Branch-2 cases, not this one.
 R13.3 COMPLETE: the 64th chart rerun is UNIT (115 s, 0.25 GB; gauge det -32, self-check 0).  So ALL 64 charts of the RED-p cover are unit at
   P1 = 2147483629 (rows/r12/kSP1.out).  By Lemma RED-p (properness of X_S over Z[1/2], case split valid in char P1) there is no
   column-centred (4,1) extension of any of the 16 special-point kernels in characteristic 0, so with R12.5 NO (5,1) SPACE CONTAINS ONE.
STATUS 01:07: leaf-3 item (a) closed: RED-p cover 64/64 unit at P1. Item (b): Lemma RS (R13.6) proved; exact normal-form system k21sys.py calibrated (support 2: dim 2, support 3: dim 1); support 4 running; reduced-coordinate census found no support-4/5 solutions (forced starts do not converge).
 R13.8 (2,1) KERNELS ON 4-5 COLUMNS -- partial results (round 13, after the coordinator made this the top target).
   (a) LEMMA RS (R13.6) holds on any support: rho(K) = u^perp degenerate, the doubly centred n has isotropic columns -be_k f_k/2, and the
       column maps are A_k = (R - M_k)/2 with M_k = [al_k f_k, m_k, be_k f_k].
   (b) SUPPORT EXACTLY 4 (columns a,b,c,d; e zero): the deletion conditions are equivalent to: every TRIPLE t(y_i,y_j,y_l) vanishes
       (polarized) for {i,j,l} in {a,b,c,d}, and perm(y_a,y_b,y_c,y_d) vanishes (polarized); degree 2: S_ab = S_cd, S_ac = S_bd, S_ad = S_bc,
       sum 0.
   (c) LEMMA U [rigorous]: a (2,1) kernel with support exactly 4 cannot have all its columns inside rho(K) = u^perp.  Proof: write
       y_k = a_k(Y) u + b_k(Y) w.  Degree 2 gives b_k (B - b_k) = 0 identically (B = sum b_l, not 0), so exactly one column (say a) has
       b_a = B and the other three lie in C u with a_k not identically 0.  The triple {b,c,d} gives a_b a_c a_d t(u,u,u) = 0, so t(u,u,u) = 0;
       the triple {a,b,c} gives t(y_a,u,u) = 0.  Since t(.,u,u) does not vanish on u^perp (sg(u,u) is never parallel to an isotropic u) and
       vanishes on u, its kernel in u^perp is C u, so y_a lies in C u, contradicting b_a = B.  QED
   (d) CASE (P), |supp n| = 4 [rigorous]: if n = d (x) lam with all four lam_k != 0 (n-columns parallel), then the triple condition at
       (n,n,n) gives t(d,d,d) = 0, at (n,n,Y) it gives lam_i lam_j L_l + lam_i lam_l L_j + lam_j lam_l L_i = 0 for every triple, L_k(Y) :=
       t(d,d,y_k); dividing, L_k/lam_k are equal with 3x their value = 0, so L_k = 0: every column lies in sg(d,d)^perp, hence
       rho(K) = sg(d,d)^perp = u^perp and all columns lie in u^perp -- impossible by (c).
   Remaining for support 4: n parallel with |supp n| = 2, 3, and n with non-parallel columns; for support 5: everything.  Evidence:
   reduced-coordinate census with all supported columns forced nonzero (k21redF.py, support 5: 4 starts, support 4: 1 start) never
   converges (residuals 1.3-2.1), while the same code finds the 2- and 3-column kernels at once.  Exact normal-form system k21sys.py
   (calibrated: support 2 -> dim 2 = the two-column family, support 3 -> dim 1 = family B) is too heavy for support 4 in the time available
   (> 5 min, > 0.6 GB at P1; Cramer-reduced variant k21cr.py > 9 min); a probe with numeric generic u at p = 32003 is running.
   (e) CASE (G) for support 4 (n-columns not all parallel) [rigorous reduction + exact]: then all four f_a..f_d are pairwise
       non-parallel (three distinct isotropic directions are independent), and the triple conditions at (n,n,n) say t(f_i,f_j,f_l) = 0 for
       all four triples.  On the conic, t(c(a),c(b),c(c)) = 16 i (e_3 e_2 - e_1)(a,b,c) (tfac.sing, exact).  These four conditions (plus
       perm(f_a..f_d) = 0) still leave a 2-DIMENSIONAL family of 4-point configurations (caseG4.sing, exact over Q(i), distinct points),
       so case (G) needs the mixed conditions (n,n,Y), (n,Y,Y) and the e1/e2 data; not finished.
   (f) The probe "support 4 with generic numeric u at p = 32003" (ks4g.sing) was still running at 10 min / 0.6 GB when the round ended (it
       stops itself at 15 min / 0.9 GB; output rows/r13/ks4g.out).
   PLAN for leaf 3 (b): finish support 4 by the case tree (P, |supp n| = 2, 3) and (G) using the mixed triple conditions (they are linear in
   the columns of Y, like (d)), each case as a SMALL exact system (a few conic parameters); then support 5 (deletion conditions are sums of
   four triples; Lemma RS + the summed cubic sum_k t(x_k,x_k,x_k) = 3 t(r,r,r) and its K_0-restriction sum_k al_k^3 t(f_k,f_k,f_k) =
   (|S| - 2) t(u,u,u) give the first equations).
STATUS 01:29: round 13 closing; RESULT ROUND 13 rewritten (leaf 3: (a) closed, (b) open with Lemma RS / Lemma U / case P4); ks4g probe self-terminates by 01:35.

# ROUND 14 (start 01:31 UTC). Targets: (1) support 4 by the case tree: (P) |supp n| = 2, 3; (G) with the mixed (n,n,Y), (n,Y,Y)
#  conditions; every exact system < 1 GB (bigger ones -> QUEUE.md, append only); (2) support 5, same tree; (3) five columns parked.
STATUS 01:31: round 14 started.
## Section R14 (round 14)
 R14.0 SUPPORT-4 CASE TREE (complete list, rigorous): supp n has 2, 3 or 4 columns (sum be_k f_k = 0 with f_k isotropic).  |supp n| = 2:
   parallel (case P2); |supp n| = 3: three distinct isotropic directions are independent, so parallel (case P3); |supp n| = 4: either
   parallel (case P4, impossible by R13.8(d)), or TWO parallel pairs each with be-sum 0 (case PP: two distinct isotropic directions are
   independent, so each group sums to 0, sizes (2,2); [added 01:37 -- missing in the first version of this list]), or four pairwise
   distinct directions (case G); three distinct directions would need three zero-sum groups of size >= 2, impossible with 4 columns.
   By the column symmetry, 1 in supp n; gauges be_1 = 1, al_1 = 0, mu_1 = 0; w = c'(s0)/2; m_k = ep_k c'(sig_k)/2 + mu_k c(sig_k) (all unit
   vectors orthogonal to c(sig_k); if al_k = be_k = 0 choose sig_k with c(sig_k) orthogonal to m_k).
   CHART AT INFINITY: the conic parameter misses only c(inf) = (1,i,0), an octahedral vertex (a zero Walsh coordinate); the row group S_4
   acts on the conic as the octahedral group, transitively on the 6 vertices; a support-4 configuration involves <= 5 isotropic points
   (u, f_1..f_4), so some vertex is free and a row permutation moves it to infinity.  ONE finite chart suffices for support 4.
   Generator rows/r13/case4.py (all y-coefficients of P_3, P_4 of all deletions; saturation "column k nonzero", k = 1..4).
 R14.1 CASE P2 [mod P1]: UNIT after the four column saturations (93 s, 0.15 GB); after three saturations dim 1 (= the 3-column kernels).
 R14.2 CASE P3: UNIT already before any saturation, mod P1 (0.9 s) and EXACTLY OVER Q(i) (1.6 s, ii symbolic): no strongly level 3-space of
   this shape at all (n parallel on three columns).
STATUS 01:36: support 4: P2 unit mod P1 (exact over Q running), P3 unit over Q, G running mod P1.
 R14.3 SUPPORT-5 CASE TREE (rigorous list): sum be_k f_k = 0 over the columns of supp n, grouped by distinct isotropic directions; a group's
   combined coefficient must vanish whenever <= 3 directions occur (they are independent).  |supp n| = 2: P2; 3: P3; 4: P4, PP (2+2), G4 (4
   distinct); 5: P5, S23 (zero-sum groups of sizes 2 and 3), R4 (one parallel pair with nonzero combined coefficient + 3 singletons, 4
   distinct directions), R5 (5 distinct).  (Three directions with 5 columns would need three zero-sum groups of size >= 2.)
   Generator rows/r13/case5.py (all 5 columns supported, sums 3u, 3w, 0; the same deletion coefficients; saturation by all 5 columns).
   CHART AT INFINITY for support 5: up to 6 isotropic points, so the S_4 argument covers every configuration except those whose points are
   exactly the 6 octahedral vertices; those need one extra Moebius chart (MOB= option).
 R14.4 CASE P2, hand consequences [rigorous]: n = d(e_1 - e_2) up to scale (be_1 = 1, be_2 = -1, f_1 = f_2 = d).  The triple conditions
   with n twice give t(d,d,y_k) = 0 (k = 3,4); with n once (derivative of t(y_1,y_2,y_k) in direction n) they give
   t(d, y_1 - y_2, y_k) = 0, and since y_1 - y_2 = -[((al_1 - al_2) y1 + 2 y3) d + y2 (m_1 - m_2)]/2 this is t(d, m_1 - m_2, y_k) = 0.
   So columns 3 and 4 are orthogonal to sg(d,d) and to sg(d, m_1 - m_2): 8 linear equations on (u - al_k f_k, w - m_k), k = 3, 4
   (option ADD of case4.py).  With them, P2 mod P1 is UNIT in 44 s (instead of 93 s).
 R14.5 CASE PP: UNIT already before any saturation, mod P1 (2.2 s) and EXACTLY OVER Q(i) (1.7 s).
STATUS 01:44: support 4: P2 unit mod P1 (exact over Q with ADD running), P3 and PP unit over Q, G (with point-family equations) running mod P1.
 R14.6 CHAR 0 for case P2: the exact run over Q(i) (even with the ADD consequences) runs out of memory at 0.88 GB (240 s); queued for the
   big-slot extras as R14-P2Q (QUEUE.md, appended).  Cases P3 and PP are exact over Q(i).  RED-p is NOT available here: "all four columns
   nonzero" and the case conditions are open, and the closed varieties containing these kernels also contain the (existing) 2-3-column
   kernels.  So char 0 for support 4 needs exact runs (or further hand reductions).
 R14.7 CASE G, the point family made explicit [rigorous, from the exact GB of g4fam.sing]: four distinct conic points (identity chart) with
   t(f_i,f_j,f_l) = 0 for all triples  <=>  e_2(s_1..s_4) = 0 and e_4(s_1..s_4) = -1, i.e. the s_k are the roots of z^4 - p z^3 - q z - 1
   (p = e_1, q = e_3 free).  [The third GB generator bcd(bc+bd+cd) - (b+c+d) follows: bcd = -1/a, e_2(b,c,d) = -a(b+c+d).]  The be_k are the
   Vandermonde weights be_k ~ 1/prod_{j != k}(s_k - s_j).  The case-G system at P1 (with these equations added) did NOT finish: timeout at
   20 min, 0.66 GB (c4_G2.sing; queued for the big-slot extras as R14-K21BIG).  Structure: for distinct i,j the quadric
   O(l_i,l_i,l_j,l_j,.,.) (O = octahedral sextic, f_k = l_k^2) vanishes at l_l and l_m, so sg(f_i,f_j) is proportional to l_l l_m, i.e. to
   f_l x f_m (the other two points).
STATUS 02:04: round 14 closing; support 4: P2 (P1), P3/PP (exact), P4 (hand) done; G open (queued); support 5 queued (R14-K21BIG, R14-P2Q in QUEUE.md).

# ROUND 15 (start 02:06 UTC). Targets: (1) case G by hand (sg(f_i,f_j) ~ f_l x f_m) -> small char-0 system; (2) P2 in char 0 if
#  R14P2Q fails; (3) support 5 hand reductions.  Big-slot extras queued by the coordinator (R14P2Q, K21_* ten jobs).
STATUS 02:06: round 15 started.
## Section R15 (round 15)
 R15.1 THE PLANE TEST [rigorous reduction].  K_0 := span(e1, n) = rho^{-1}(C u) is a strongly level PLANE inside K, with columns
   (u - a_k n_k)/2 (e1) and -n_k/2 (n), a_k = al_k/be_k, sum_k n_k = 0, sum_k a_k n_k = 2u (row sums of e1 = u), gauge a_1 = 0, be_1 = 1.
   When every column of n is nonzero (support-4 case G; support-5 cases P5, S23, R4, R5) every column of K_0 is nonzero, so "no such plane"
   excludes the case.  The plane system has only s0, s_1..s_4 (or the s-pattern), be_k, a_k: no m_k, mu_k, ep_k.  Generator rows/r15/plane.py.
 R15.2 CASE G (support 4) BY THE PLANE TEST: mod P1 UNIT in 30 s, 0.07 GB (rows/r15/pl4f.sing, with the point-family equations
   e_2 = 0, e_4 = -1 of R14.7, which are consequences of the plane's own (n,n,n) triple conditions in the identity chart).  [The same system
   without the family equations was still running after 6 min at 0.1 GB.]  EXACT run over Q(i): running (pl4fQ.sing).
STATUS 02:13: case G mod P1 UNIT by the plane test (30 s); exact over Q running; support-5 plane tests (P5, S23, R4, R5 shapes) started.
 R15.3 SUPPORT-5 PLANE TESTS (all n-columns nonzero).  BUG FOUND AND FIXED: the first support-5 runs used sum a_k n_k = 2u (the 4-column
   value); with 5 columns it is 3u.  Corrected (rows/r15/plane.py, clean output):  P5: UNIT mod P1 (0.2 s) and EXACT over Q(i) (0.6 s);
   S23: UNIT mod P1 (0.5 s) and EXACT over Q(i) (1.8 s).  *** S23 SUPERSEDED (round 16, R16.7): that run also required
   e_2(be3,be4,be5) != 0, an unjustified extra condition; rerun without it is still UNIT (mod P1 1.5 s, exact Q(i) 20 s).  R4: corrected run in progress (the earlier 72 s "unit" was the buggy version and
   is withdrawn).  R5: to run.  Chart at infinity for support 5: P5, S23, R4 involve <= 5 distinct isotropic points (S_4 argument applies);
   R5 involves 6 and needs one extra Moebius chart for the all-vertex configuration.
 R15.4 Plane tests for n-shapes WITH zero columns (support-4 P2, P4, PP; support-5 P4, PP, G4, P3, P2): generator extended (PAT=..._4/_5;
   a zero n-column k has e1-column (u - al_k c(t_k))/2, saturated to be nonzero).  NOTE: if the plane's column k vanishes (al_k f_k = u)
   the plane test does not apply to that sub-case; then column k of K is y2 (w - m_k)/2, of RANK 1 -- to be handled separately.
STATUS 02:20: G exact (Q) running; support-5 P5, S23 exact unit (plane test, corrected); R4 corrected running; generic plane tests for zero-column shapes prepared.
 R15.5 CALIBRATION of the plane test (not vacuous): support 2, n on two columns: dim 2 (the two-column planes); support 3 with one zero
   n-column: dim 1 after the column saturation (family-B planes).  Support-4 shapes PP and P4: plane UNIT mod P1 (consistent with R14.5 and
   R13.8(d)).  Support-4 P2 with both zero n-columns nonzero in the plane: dim 0, NOT unit -- finitely many P2 planes exist; so P2 needs the
   full K (case4.py: unit mod P1) or a "plane first, then extend" computation (planes are finitely many: extend each by e2).
 R15.6 CASE G EXACT over Q(i) by the plane test: out of memory at 0.87 GB (584 s).  Proposed for the big-slot extras (pl4fQ.sing).
 R15.7 CASE P2 (support 4) SPLIT BY THE PLANE COLUMNS (complete split): the plane K_0 = span(e1, n) has columns 1, 2 nonzero (n); its
   columns 3, 4 are y1 (u - al_k f_k)/2.
   (z3) plane column 3 zero (al_3 f_3 = u, i.e. sig_3 = s0, al_3 = 1; column 3 of K is then y2 (w - m_3)/2, rank 1):
        UNIT mod P1 (2.3 s) and EXACT over Q(i) (3.0 s).  (z4) is the same by the symmetry 3 <-> 4.  (z34) both zero: EXACT over Q(i) (3.0 s).
   (A)  both plane columns nonzero: STAGED computation (plane subsystem = e1/n sums + y2-free coefficients, saturated by "plane columns 3,4
        nonzero", then added to the full system): UNIT mod P1 (1.6 s); exact over Q(i) running (c4Q_P2A.sing).
   Generator option case4.py ADD SUBZ=.. STAGED.
STATUS 02:32: P2 sub-cases z3/z34 exact over Q; sub-case A unit mod P1 (staged), exact running; R4 support-5 plane died at 0.46 GB (big slot keeps K21_c5_R4).
 R15.8 Exact runs that did NOT fit locally: case-G plane over Q(i), staged version (y1-degree <= 1 first): out of memory at 0.85 GB before
   stage 1 finished; a rational reparametrization (Vandermonde weights and e_2 = 0, e_4 = -1 solved for s_4) is slower even mod P1.  The
   unstaged exact case-G plane run is in the big slot (R15GQ).  P2 sub-case A over Q(i): 15 min at 0.2 GB without a verdict; rerun with
   40 min / 0.9 GB.
 R15.9 SUPPORT 5, plane split per case (rows/r13/case5.py SUBZ= / STAGED; driver runS5sub.sh -> kS5sub.out), mod P1:
   P4: sub-case A (plane column 5 nonzero) UNIT already at the plane stage (7.5 s); z5 UNIT (5.9 s).  [others running]
STATUS 02:45: support 5: P4 settled mod P1 by the plane split; driver running PP, G4, P3, P2 sub-cases; P2-A (support 4) exact rerun.
   R15.9 cont.: PP: A UNIT at the plane stage (6.6 s), z5 UNIT (6.5 s).  P3: A UNIT at the plane stage (7.8 s), z4 UNIT at the plane stage
   (7.6 s; z5 the same by symmetry), z45 UNIT (5.6 s).  G4: A and z5 ran out of memory at 0.43 GB -> rerun with the point family
   e_2 = 0, e_4 = -1 (for G4 every triple of the four n-directions vanishes: deletions 1..4).  P2: running.  (All mod P1.)
STATUS 02:56: support 5 mod P1: P5, S23 (exact), P4, PP, P3 settled; P2 running; G4 rerun with family; R4/R5 in the big slot.
   R15.9 cont.: P2 (zero n-columns 3,4,5; sub-cases up to the S_3 symmetry): A UNIT at the plane stage (282 s, 0.22 GB); z3 UNIT (4.4 s);
   z34 UNIT after the column-3 saturation (4.3 s); z345 UNIT after the column-4 saturation (4.8 s).  => support-5 P2, P3, P4, PP settled
   mod P1 (P5, S23 exact over Q(i)); exact versions queued in my pool (runS5Q.sh -> kS5Q.out).  Open in support 5: G4 (family rerun),
   R4, R5 (big slot).
 R15.10 SUPPORT-5 EXACT over Q(i) (plane split, case5.py P = 0): P4 (A, z5), PP (A, z5), P3 (A, z4, z45): ALL UNIT, 8-18 s each, < 0.08 GB
   (rows/r13/kS5Q.out).  P2 sub-cases exact: running (runS5Q2.sh).
   G4: sub-case z5 (plane column 5 zero) means K_0 is a 4-column plane with case-G n -> excluded by R15.2 (mod P1; char 0 with R15GQ).
   Sub-case A (plane column 5 nonzero): the support-5 G4 plane test with the family equations runs out of memory at 0.43 GB
   (rows/r15/pl5_G4_5f.sing) -> big slot.
STATUS 03:03: support-5 P3, P4, PP exact over Q(i); P2 exact running; G4-A and R4/R5 need the big slot; support-4 P2-A exact still running.
 R15.11 SUPPORT-4 CASE P2 IN CHARACTERISTIC 0: sub-case A (both plane columns 3,4 nonzero), staged, EXACT over Q(i): UNIT (1383 s,
   0.54 GB; rows/r13/c4Q_P2A.out).  With z3 (= z4) and z34 exact (R15.7): case P2 is settled in char 0, so the big-slot job R14P2Q is no
   longer needed.  SUPPORT 4 IN CHAR 0: P2, P3, PP exact; P4 by hand; only case G remains (mod P1 by the plane test; char 0 = R15GQ).
STATUS 03:10: support-4 P2 exact over Q(i) (all sub-cases); support 4 char 0 except G (R15GQ).
STATUS 03:11: round 15 closing; RESULT ROUND 15 has the leaf-3 paragraph for verify2 on top; runS5Q2.sh (support-5 P2 exact sub-cases, 0.45 GB / 15 min each) still running, output rows/r13/kS5Q.out.

# ROUND 16 (start 03:12 UTC). Targets: (1) support-5 P2 exact sub-cases (big-slot lines at once if they time out); (2) read big-slot
#  verdicts rows/r15/*.big.out; (3) closing statement for leaf 3 when char 0 is complete; (4) five columns (PL).
STATUS 03:12: round 16 started.
## Section R16 (round 16)
 R16.1 VERONESE SUMQ (rows/r13/sumqv.py; Q_j = q_j q_j^T, B_j linear in Q_j, cubic of degree 3, sign symmetry quotiented) -- CALIBRATED and
   FASTER: 3 columns ++- dim 1, --- dim 2 (as sumq.py); 4 columns ---- UNIT in 20.5 s / 0.05 GB (sumq.py: 145 s / 0.13 GB), ++-- UNIT in
   29.7 s / 0.06 GB (sumq.py: 140 s / 0.12 GB).  Five columns: probe ----- (0.9 GB, 25 min) running.
STATUS 03:14: support-5 P2 big-slot lines sent; Veronese SUMQ calibrated (4-col 5-7x faster); five-column probe running.
 R16.2 SUPPORT-5 P2 EXACT over Q(i): z34 UNIT (11 s), z345 UNIT (12 s); z3 out of memory at 0.42 GB (730 s) -> big slot R16P2z3; A running in
   the pool (big-slot line R16P2A sent).  The full per-deletion cubic Veronese variant (sumqvF.py) is slower than the summed relaxation on
   4 columns (96 s vs 20 s), so the relaxation stays the decision procedure for (PL).
 R16.3 LEAF 3 CLOSING STATEMENT -- DRAFT (final once the big-slot jobs R15GQ, R15G4P/Q, R15R4P/Q, R15R5P/M/Q, R16P2z3, R16P2A are unit).
   CLAIM: no (5,1) space contains a strongly level 3-space K of type (q,d) = (2,1).
   ROUTE: R12.5/R12.5' (no column-centred (4,1) extension with non-two-column m => no (5,1); Lemma SL, TC5, C(L') in 1^perp).
   (i) TWO COLUMNS: normal form R10.7; generic K by hand (R11.4-R11.7, R12.10); special locus classified exactly (R13.3): the line d = u
       (R13.2, hand + exact Q(i)) and 16 geometric points (RED-p cover, 64/64 charts at P1, R13.3).  [verified by verify2, round 15]
   (ii) THREE COLUMNS: Lemma 3COL (R12.8, hand) => A1, A2 (exact over Q, R12.6) and family B (R13.1', hand reductions + exact Q(i)).
   (iii) FOUR COLUMNS (the kernel itself has no extension issue: we show NO such K exists): Lemma RS (R13.6) normal form; case tree on n
       (R14.0): P2 exact Q(i) (R15.7, R15.11: sub-cases z3 = z4, z34, A staged); P3, PP exact Q(i) (R14.2, R14.5); P4 by hand (R13.8(d));
       G: plane test (R15.1-R15.2) -- char 0 = R15GQ.  One conic chart (S_4 transitive on the octahedral vertices, <= 5 points).
   (iv) FIVE COLUMNS: case tree R14.3; P5, S23 plane test exact Q(i) (R15.3); P3, P4, PP plane split exact Q(i) (R15.10); P2 plane split:
       z34, z345 exact Q(i) (R16.2), z3 and A = R16P2z3, R16P2A; G4: z5 via support-4 G, A = R15G4P/Q; R4 = R15R4P/Q; R5 = R15R5P + R15R5M
       (extra Moebius chart for the all-vertex configuration) / R15R5Q.
   GENERATORS: rows/r13/case4.py, case5.py, rows/r15/plane.py (all print self-checks; plane test calibrated on supports 2, 3).
STATUS 03:21: leaf-3 closing statement drafted (R16.3); support-5 P2 z34/z345 exact; z3/A and the G/G4/R4/R5 char-0 runs wait for the big slot; Veronese SUMQ5 lines queued.
 R16.4 ALL-VERTEX CONFIGURATIONS (support 5, R5 and G4: six isotropic points = the six octahedral vertices) [EXACT over Q(i)]: rows/r15/vert.py
   enumerates them with explicit vectors (u = vertex 0 WLOG by transitivity; 5! assignments): R5 120/120 UNIT, G4 120/120 UNIT, mod P1 and over
   Q(i) (<= 4 s).  Calibration: without the plane conditions all 120 are non-unit (both cases).  => the identity chart suffices for R5 and
   G4 as well (R15R5M dropped).  [Note: G4's chart gap had not been noticed before; now closed.]
STATUS 03:25: all-vertex configurations (R5, G4) exact; waiting for the big-slot verdicts (first extras point ~03:45-04:45).
 R16.5 SUPPORT-5 P2 hand consequences [rigorous, as R14.4]: with n = d(e_1 - e_2), the deletion conditions with n twice give
   L_3 + L_4 + L_5 - L_k = 0 for k = 3,4,5 (L_l = t(d,d,y_l)), hence L_3 = L_4 = L_5 = 0; with n once, deletion k in {3,4,5} gives
   sum_{l in {3,4,5}\\k} t(d, y_1 - y_2, y_l) = 0, hence each t(d, y_1 - y_2, y_l) = 0 and so t(d, m_1 - m_2, y_l) = 0.  Option ADD of
   case5.py.  z3 with ADD: UNIT mod P1 in 7 s; exact over Q(i) running (q5a_P2_z3.sing).
 R16.6 (PL) note [structure, no decision]: for a principal kernel, K_k := ker A_k = R^{-1}(Fix B_k) is a strongly level space on the other
   four columns; for a REFLECTION column (B_k = -Ad(q_k) with s_k = 0) it is a PLANE with injective row-sum map onto the mirror plane, so the
   plane-test machinery (R15.1) applies to it; for rotation columns it is a line.  TR5 gives s_j^2 generically != 0, so this only
   covers the s_j = 0 strata of the SUMQ5 moduli.  Not pursued further this round.  Veronese SUMQ5 (R16.1) is in the big slot.
 R16.7 AUDIT of the nonvanishing (Rabinowitsch) conditions in all generators: plane.py S23 had an extra factor e_2(be3,be4,be5) (an
   unjustified restriction: zero-sum triples with e_2 = 0 exist).  Fixed; S23 rerun UNIT mod P1 (1.5 s) and EXACT over Q(i) (20 s,
   rows/r15/pl5e_S23_0.sing).  All other cases checked: plane.py (G, R4, P5, zero-column shapes), case4.py (P3, PP, G), case5.py (all nine)
   impose exactly "be's nonzero" + "distinct directions where required" + the case-defining combined-coefficient conditions.
STATUS 03:40: S23 plane condition audit: fixed and rerun (still exact unit); waiting for the big slot.
 R16.8 LEAF-3 MANIFEST for independent re-runs: rows/leaf3/MANIFEST.txt (every piece: char-0 basis, generator command, expected verdict,
   observed time/memory; big-slot pieces marked).
 R16.9 support-4 G plane test at two more primes: UNIT at p = 2147482621 (25 s) and p = 1000003 (27 s) -- with P1: [modular, 3 primes];
   char 0 pending R15GQ.
STATUS 03:51: G plane unit at 3 primes; big slot still in the Lean phase (no verdicts yet).
 R16.10 R4 plane test, STAGED, mod P1: out of memory at 0.43 GB (121 s) -- stays in the big slot (R15R4P).
STATUS 03:53: round 16 closing; no big-slot verdicts yet (big slot still in the Lean phase); all remaining leaf-3 pieces queued there.

# ROUND 17 (start 03:54 UTC). Targets: (1) read leaf-3 big-slot verdicts, finalize R16.3; (2) (PL): reflection-column split
#  (s_j = 0 => ker A_k a plane => plane test); (3) plane-test analogue for column-centred extensions / ncol (CCN).
STATUS 03:54: round 17 started.
## Section R17 (round 17)
 R17.1 (PL) REFLECTION SPLIT [rigorous reduction, computations too heavy so far].  For a principal 5-column kernel, column k has
   ker A_k = R^{-1}(Fix B_k): eps_k = +1 (rotation, B_k != I): a line (the axis); eps_k = -1: Fix(-Ad q_k) = 0 unless Ad q_k is a rotation by
   pi (s_k = 0), when it is the mirror plane P_k = v_k^perp, NONDEGENERATE (|v_k|^2 = 1 - s_k^2 = 1).  So a REFLECTION column yields a
   strongly level plane Pi = ker A_k on the other four columns with injective row-sum map onto a nondegenerate plane (its column j vanishes
   only if B_j is the same reflection).  Split of each sign pattern by the number r of reflection columns: r >= 1 reduces (by the symmetry
   among the minus columns) to "the first minus column is a reflection".
   Tests: (a) the principal plane test on 4 columns (rows/r17/pplane.py: p_i orthonormal, (b_j1, b_j2) orthonormal, sum_j b_ji = 2 p_i,
   all deletion coefficients, 30 unknowns): out of memory at 0.43 GB in 18 s.  (b) Veronese SUMQ5 with s_5 = 0 (pattern ++++-, stratum
   r >= 1; sumqvR.py REFL=4): out of memory at 0.88 GB in 299 s.  So even the reflection strata need the big slot or a better normal form;
   not queued (the full V5 jobs R16V5* cover them).  Stratum runs print "STRATUM SUMQV ..." (never "RESULT"), so they cannot be mistaken for
   pattern verdicts.
 R17.2 Target 3 (plane-test analogue for (CCN) / column-centred (4,1) extensions): not started this round (read NOTES-ncol R4.6, R4.10-R4.12:
   (CCN) = "every column-centred 4x5 level 4-space with defect 3 has a neutral column"; 4/4 numerical examples).  Idea for next round: the
   row-sum fibre structure (rho^{-1} of a line) of a column-centred level 4-space gives level planes with small defect.
STATUS 04:02: reflection strata for (PL) also too heavy locally (0.43 / 0.88 GB); waiting for leaf-3 big-slot verdicts (Lean window 3 ends ~04:28).
 R17.3 Principal planes on 4 columns (reflection strata of (PL)) [numerical]: rows/r17/pplane_num.py.  Unforced LM: 8/8 converge, to planes
   with 2 or 3 nonzero columns (one start ends with two columns of norm 2.3e-4, residual 1.4e-10: a 2-column limit, not a 4-column
   solution).  Forced (all four plane columns normalized nonzero): 0/8 converge (residuals 0.7-1.1).  Evidence that a reflection column is
   impossible in a principal 5-column kernel (then every minus column of a (PL) frame has s_k != 0).  No exact proof yet (pplane.py needs
   > 0.43 GB).
 R17.4 Attempts at an exact principal-plane test (reflection strata): isotropic-coordinate version (pplane2.py, homogeneous c(s:t), 20
   unknowns) and even the single-matrix sub-test (the row-sum-f element alone: columns (f - g_j)/2, sum g_j = 2f, triples + perm; single.py)
   run out of memory at 0.43-0.9 GB.  The homogeneous parametrization raises degrees (perm -> degree 8); a better normal form is needed
   (e.g. the Vandermonde-type reduction that made case G small: 5 isotropic vectors with one linear relation).  Next round.
 R17.5 THE ISOTROPIC SLICE -- a possible one-shot argument for (PL) AND for the rest of leaf 3 [rigorous reduction; computation running].
   (SM_n): "no strongly level 4x5 matrix with nonzero ISOTROPIC row sum has exactly n nonzero columns" (n = 4, 5).
   (a) (PL) <= (SM5), PL4 <= (SM4): for a principal kernel K (R invertible, B_k orthogonal, B_k != I), Y_u := R^{-1}u has columns
       (u - B_k u)/2; column k vanishes only if u is a fixed vector of B_k, and Fix(B_k) (dim <= 2) contains at most 2 isotropic directions.
       So for all but finitely many isotropic u, Y_u is strongly level with isotropic row sum u and all columns of K nonzero.
   (b) LEAF 3 cases <= (SM4) + (SM5): for a (2,1) kernel, every element e1 + ka n of K_0 has row sum u (isotropic); for all but finitely many
       ka its support is the plane support {k : be_k != 0} u {k : be_k = 0, al_k f_k != u}.  So every case whose plane has >= 4 nonzero
       columns is excluded: support-4 G and P2-A; support-5 G4 (A: 5 columns; z5: 4 columns), R4, R5, P5, S23, P2-A (5), P2-z3 (4), etc.
       Only plane supports <= 3 would remain -- exactly the sub-cases already settled exactly (P2-z34 in support 4, P2-z34/z345 in support 5,
       P3/P4/PP z-cases, ...).
   (c) Degree 2 for a single matrix is equivalent to "g_k := f - 2 y_k is isotropic" (|y_k|^2 = <f, y_k>), and sum g_k = (n-2) f.
   Numerics (rows/r17/sm5_num.py, forced nonzero columns): n = 5: 0/12 converge; n = 4: 0/8; calibration n = 3: 8/8, n = 2: 6/6.
   Exact (rows/r17/sm5.py: f = c(s0) fixed scale, columns y_k unknown, degree 2 + P_3, P_4 of every deletion, saturation by columns
   nonzero): n = 3 mod P1: dim 3 (solutions exist -- calibration, 152 s).  n = 4, 5 mod P1: running.
STATUS 04:24: NEW: isotropic-slice reduction (R17.5): (SM4)+(SM5) would give (PL), PL4 and close the remaining leaf-3 cases; exact SM4/SM5 runs going.
 R17.6 (SM_n) runs.  y-form (sm5.py) mod P1: n = 3 dim 3 (152 s); n = 4, 5 out of memory (0.43 / 0.88 GB, ~8 min).  CONIC form (smc.py:
   f = c(sg), g_k = la_k c(ta_k), sum g_k = (n-2) f, columns (f - g_k)/2; degree 2 automatic): n = 3 dim 3 in 2.7 s (60x faster);
   n = 4 out of memory at 0.43 GB (283 s).  All-vertex configurations for n = 5 (the only case beyond the S_4 one-chart argument):
   rows/r17/smv.py, 120/120 UNIT mod P1 and EXACT over Q(i); calibration (conditions dropped) 120/120 non-unit.
   Big slot (coordinator): R17SM5P, R17SM4P (y-form), R17SM5Q, R17SM4Q queued; conic-form R17SMC5P/SMC4P/SMC5Q/SMC4Q proposed as preferred.
   If (SM5) and (SM4) are unit: (PL) and PL4 hold (R17.5(a)), and every leaf-3 case whose plane K_0 has >= 4 nonzero columns is excluded
   (R17.5(b)) -- covering all big-slot leaf-3 pieces (R15GQ, R15G4P/Q, R15R4P/Q, R15R5P/Q, R16P2z3, R16P2A).
STATUS 05:22: (SM_n) conic form 60x faster at n = 3; n = 4, 5 need the big slot (lines sent); SM5 all-vertex configurations exact.
STATUS 05:23: round 17 closing.

# ROUND 18 (start 05:24 UTC). Targets: (1) hand proof / reduction of (SM5), (SM4); (2) R17.5 as a lemma chain for verify2;
#  (3) SMC5P/SMC4P verdicts -> finalise R16.3; (4) (CCN) analogue.  Pool <= 0.5 GB (host ~2 GB free).
STATUS 05:24: round 18 started.
## Section R18 (round 18)
 R18.1 THE ISOTROPIC SLICE AS A LEMMA CHAIN (for verify2's audit of R17.5).  V = 1^perp in C^4 with the dot form (nondegenerate, dim 3);
   t, perm as before; "strongly level" = all deletion P_2, P_3, P_4 vanish (column-centred columns).
   IS0 (single matrices).  Y with columns y_1..y_5 in V (column-centred) and row sum f = sum y_k.  Degree 2 for Y alone is equivalent to
       <y_k, f - y_k> = 0 for all k (R12.10 step (2) style: sum_{l != k} <y_k,y_l> = 0), i.e. |f - 2 y_k|^2 = |f|^2.  If f is isotropic this
       says g_k := f - 2 y_k is isotropic, and then sum_k g_k = 5f - 2f = 3f (resp. (n-2) f when only n columns are nonzero).
       (SM_n): no strongly level Y with f isotropic, f != 0, and exactly n nonzero columns (n = 4, 5).
   IS1 (fixed isotropic directions).  B in O(3,C), B != I: at most 2 isotropic directions are fixed by B.  [Fix(B) = ker(B - I) has dim <= 2;
       a line contains <= 1 isotropic direction; a plane W carries a nonzero form (V has no totally isotropic plane), so W contains 1 or 2
       isotropic lines.]
   IS2 (principal kernels).  K principal on the column set S (R = rho : K -> V bijective, A_k != 0 for k in S).  Lemma RS (R13.6(i)):
       B_k := I - 2 A_k R^{-1} is orthogonal; A_k != 0 means B_k != I.  For isotropic u != 0, Y_u := R^{-1} u is in K (strongly level), has row
       sum u and columns A_k R^{-1} u = (u - B_k u)/2, zero iff B_k u = u.  By IS1 only finitely many isotropic directions are bad; the
       isotropic cone has infinitely many directions; so some Y_u has exactly |S| nonzero columns.  Hence (SM_|S|) => no principal kernel on
       S.  |S| = 5: (PL);  |S| = 4: PL4 (second proof).
   IS3 ((2,1) kernels, any support).  Lemma RS normal form: K_0 := span(e1, n) = rho^{-1}(C u), u isotropic != 0; Y_ka := e1 + ka n has row
       sum u and columns (u - (al_k + ka be_k) f_k)/2.  If be_k != 0 the column vanishes for at most one ka; if be_k = 0 it vanishes iff
       al_k f_k = u (for every ka).  So for all but finitely many ka the support of Y_ka is the PLANE SUPPORT
       S_0 = {k : be_k != 0} u {k : be_k = 0, al_k f_k != u}, and (SM_|S_0|) excludes every kernel with |S_0| in {4, 5}.
       Cases with |S_0| >= 4: support 4: G (n-columns 1..4), P2-A (plane columns 3,4 nonzero), P3 and PP and P4 with all plane columns nonzero;
       support 5: P5, S23, R4, R5 (all n-columns nonzero), G4 (A: 5; z5: 4), P4/PP-A (5), P4/PP-z5 (4), P3-A (5), P3-z4 (4), P2-A (5),
       P2-z3 (4).  Only |S_0| <= 3 sub-cases are left to the direct computations (support 4: P2-z34; support 5: P3-z45, P2-z34, P2-z345;
       all exact over Q(i)).
   IS4 (charts for the conic form).  In the conic form f = c(sg), g_k = la_k c(ta_k) (la_k = 0 allowed) every isotropic vector except the
       direction c(inf) = (1,i,0) is represented.  The points involved are f and the directions of the g_k with la_k != 0: at most n+1.  The
       row group S_4 acts on V by T_d, on the conic by the octahedral rotation group, transitively on the 6 vertices (isotropic vectors
       with a zero Walsh coordinate; c(inf) is one of them), and preserves strong levelness.  If the configuration misses a vertex v, move v
       to c(inf): the configuration lies in the affine chart.  n = 4: <= 5 points, always.  n = 5: otherwise the six points are exactly the
       six vertices; f = vertex 0 WLOG, the five others go to g_1..g_5 in 5! ways: rows/r17/smv.py, 120/120 UNIT exactly over Q(i)
       (calibration: 120/120 non-unit without the conditions).
   IS5 (computation, pending): (SM4), (SM5) in the conic form, affine chart: big slot R17SMC4P/R17SMC5P (mod P1), R17SMC4Q/R17SMC5Q (Q(i)).
STATUS 05:25: R18.1 lemma chain written (IS0-IS5).
 R18.2 (SM_n) IN THE BINARY MODEL [reformulation; no hand proof yet].  W = C^2 (binary linear forms), V = S^2 W with the discriminant
   form; isotropic vectors are squares m^2.  The C^4 coordinates of a quadric q are its pairings with the four tetrahedral quadrics h_r
   (h_r = the Walsh rows (+-1,+-1,+-1), non-isotropic, sum_r h_r = 0; their 8 roots are the cube vertices): (m^2)_r = h_r(m).  Identities:
   sum_r h_r(m) = 0, sum_r h_r(m)^2 = 0, sum_r h_r(m)^3 = t(m^2,m^2,m^2) = O(m) (octahedral sextic), prod_r h_r(m) = perm(m^2,..,m^2)/24 (the
   octahedral octic, roots = cube vertices).
   (SM_n): f = m_0^2, g_k = m_k^2 (m_k in W, m_k = +-m_0 for zero columns), sum_k m_k m_k^T = (n-2) m_0 m_0^T (5-column layout: = 3 m_0 m_0^T
   including the zero columns), and the 4x5 matrix Y_rk = (h_r(m_0) - h_r(m_k))/2 must be strongly level: per deletion j,
   sum_{triples not j} sum_r Y_ra Y_rb Y_rc = 0 and perm(Y without column j) = 0.  The constraint says the 2x6 matrix
   [m_1 .. m_5 | i sqrt3 m_0] has isotropic, orthogonal rows: an isotropic 2-plane of C^6 (n = 5) / C^5 (n = 4); OG(2,5) = P^3 has the
   rational chart [I | -vv^T/2 + S | v] (split coordinates, S skew), so the configurations of (SM4) are rationally parametrized by 7
   numbers (chart parameters v, S and a 2x2 basis change), with no point-at-infinity issue for the g's.  Dimension counts: (SM4) expects
   1 (6 projective parameters, 5 conditions) but numerics find none; (SM5) expects -2.  A hand proof would need a structural reason for the
   (SM4) emptiness (numerics: 0/8; exact runs in the big slot).  Not found this round.
STATUS 05:26: R18.2 binary-model reformulation of (SM_n); host memory ~0.7 GB free, no pool jobs.
 R18.3 (SM_n) CUBIC RELAXATION IN CLOSED FORM OVER Q [rigorous reformulation; rows/r18/smphi.py].  c(s) = s^2 A + s B + C with A, B, C
   independent, so sum_k g_k = 3f (5-column layout, zero columns g = f, i.e. la = 1, ta = sg) is  sum_k la_k ta_k^m = 3 sg^m (m = 0,1,2);
   t(c(a),c(b),c(c)) = 16 i Phi(a,b,c), Phi = abc(ab+bc+ca) - (a+b+c); hence every per-deletion cubic has RATIONAL coefficients (no i), and a
   unit verdict with P = 0 is an exact char-0 certificate for (SM_n) (the cubic part is a relaxation).  Column k zero <=> la_k = 1, ta_k = sg.
   Numerics without the permanents (sm5_numB.py NOPERM): n = 4 0/8, n = 5 0/8, calibration n = 3 4/4 -- the cubic part alone seems to
   suffice.  Exact: n = 3 dim 3 (0.1 s, not vacuous); n = 4 out of memory at 0.28-0.47 GB (also with all la_k != 0).  Proposed big-slot
   lines R18SP4P/R18SP5P (mod P1) and R18SP4Q/R18SP5Q (over Q).
STATUS 05:46: cubic-only closed form over Q (R18.3) proposed for the big slot; no hand proof of (SM_n) yet.
 R18.4 A STRONGER CONJECTURE, (SM4''), and a much smaller test [numerical + exact running].  Numerically, 4 nonzero columns are impossible
   even WITHOUT isotropy of f and WITHOUT the permanents: sm5_numC.py GENF NOPERM: n = 4 0/8 (calibration n = 3 6/6; with permanents and
   general f: n = 4 0/8).  (SM4''): "four vectors y_1..y_4 in V with y_k.(f - y_k) = 0 (f = sum y_k) and all four triple values
   t(y_i,y_j,y_l) = 0 have f = 0 or some y_k = 0".  (Contrast: f = 0 IS possible -- N_II elements mu zeta(e_a - e_b) + mu' zetabar(e_c - e_d);
   and for 5 columns non-isotropic f is possible -- K_II elements; so (SM5) genuinely needs isotropy.)  Hadamard form: with
   u_1,u_2,u_3 the (Z/2)^2-transforms of the columns, degree 2 <=> u_i.u_j = u_k.f ({i,j,k} = {1,2,3}) and sum |u_i|^2 = 3|f|^2.
   Exact test rows/r18/sm4w*.sing: 12 unknowns (Walsh coordinates), 4 quadrics + 4 cubics, chart f_1 = 1 (coordinate permutations are
   symmetries, so one chart covers f != 0); the unrestricted homogeneous run was slow (positive-dimensional f = 0 components); chart run
   mod P1 in progress.  If unit (and over Q), (SM4'') gives PL4 and the support-4 leaf-3 cases by a 12-variable computation, no conic param.
STATUS 06:12: round 18 closing.

# ROUND 19 (start 06:13 UTC). Targets: (1) hand proof of (SM4''); (2) Q version of sm4wc if mod P1 unit; (3) SP5P/SP4P verdicts;
#  (4) (CCN).  Pool <= 0.5 GB.
STATUS 06:13: round 19 started.
## Section R19 (round 19)
 R19.1 (SM_n'') in WALSH COORDINATES (rows/r18/sm5w.py): unknowns the nonzero columns y_k in C^3, f = sum y_k, degree 2 y_k.(f - y_k) = 0,
   degree 3 per deletion sum of sg(y_a,y_b).y_c = 0, optional f.f = 0, chart f_1 = 1 (complete: coordinate permutations are symmetries),
   saturation by columns nonzero; rational coefficients (exact over Q possible).  Calibration n = 3 (general f): dim 4 (0.06 s).
   n = 4 (general f) mod P1: chart run sm4wc 15-min cap exceeded (0.18 GB); generator run w4 in progress (0.45 GB).  Big-slot lines
   R19W4P, R19W5P (mod P1), R19W4Q, R19W5Q (over Q) sent, proposed first among SP/SMC.
 R19.2 HAND-PROOF ATTEMPT for (SM4'') [reformulation]: in the square-zero algebra R = C[z_1..z_4]/(z_k^2) with A, B, C the row forms of the
   3x4 column matrix (A = sum_k a_k z_k etc.) and e = sum_k z_k:  degree 2 <=> (A^2 + B^2 + C^2) e = 0, i.e. the off-diagonal column Gram is
   of Klein type (G_12 = G_34, G_13 = G_24, G_14 = G_23, sum 0);  degree 3 <=> A B C = 0 in R (all 3x3 subpermanents vanish);  f_r = (row r) e^3/6.
   Claim (SM4''): then f = 0 or some z_k is absent from A, B, C.  Examples showing sharpness: f = 0 is possible (N_II rows); 3 nonzero columns
   are possible (dim 4).  Hadamard form of degree 2: u_a.u_b = u_c.f, sum |u_a|^2 = 3|f|^2.  No proof found yet.
STATUS 06:19: Walsh-coordinate (SM_n'') generator calibrated; W4/W5 big-slot lines sent; pool W4 run in progress; hand proof not found (R19.2 reformulation).
 R19.3 (SM4'') IN g-FORM [rigorous reformulation].  Put g_j := f - 2 y_j (j = 1..4), so sum_j g_j = 2f.  Then
   degree 2  <=>  |g_j|^2 = |f|^2 for all j  (four vectors on the "sphere" through f; [y_k.f = |y_k|^2]),
   degree 3  <=>  kappa(z.y) is a LINEAR function of z on the cube {+-1}^4 (kappa = x1 x2 x3 in Walsh coordinates; the squarefree
                  coefficients are the triple values), i.e.  (i) sum_j kappa(g_j) = 2 kappa(f)  and  (ii) kappa(g_j + g_k - f) =
                  kappa(g_j) + kappa(g_k) - kappa(f) for the three pairings {j,k} = {3,4}, {2,4}, {2,3}.
   Columns nonzero <=> g_j != f.  (SM4'') <=> f = 0 or some g_j = f.  Note the 3x4 column matrices with all 3x3 subpermanents zero form
   an 8-dimensional family with generic rank 3 and no zero entries (rows/r18/d3struct.py), so the obstruction is the interplay of the two
   degrees, not a zero pattern.  No proof yet.
 R19.4 Numerical structure: with ONE of the four triple conditions dropped, (SM4'') has solutions with f != 0 and four nonzero columns
   (rows/r18/drop1.py, 8/8 converge), on which the dropped triple value is never 0 (0.7-38).  So the emptiness needs all four triples;
   a hand proof must use them jointly (the cube-linearity form R19.3 is the natural candidate).
STATUS 06:29: round 19 closing (W4 pool run still going; big-slot W4P/W5P first in line).

# ROUND 20 (start 06:35 UTC). Targets: (1) pool runs W4P, W5P (3 h each, RSS cap 0.5 GB), then W4Q, W5Q; (2) hand proof via cube
#  linearity; (3) (CCN).
STATUS 06:35: round 20 started.
## Section R20 (round 20)
 R20.1 (SM4'') DEGREE 2 SOLVED [rigorous]: if y_1, y_2, y_3 are a basis with nondegenerate Gram Gamma, the four degree-2 conditions are
   equivalent to   G_12 + G_13 + G_23 = 0   and   y_4 = G_23 y^1 + G_13 y^2 + G_12 y^3   (y^i the dual basis: y_4.y_1 = G_23, y_4.y_2 = G_13,
   y_4.y_3 = G_12 -- the Klein pattern).  Writing y_4 = a y_1 + b y_2 + c y_3, (a,b,c) = Gamma^{-1}(G_23, G_13, G_12), and with
   P_ij := kappa(y_i,y_i,y_j), the four triple conditions are  kappa(y_1,y_2,y_3) = 0,  a P_12 + b P_21 = 0,  a P_13 + c P_31 = 0,
   b P_23 + c P_32 = 0  (each triple through y_4 is linear in (a,b,c)); if a b c != 0 they imply the cyclic identity
   P_12 P_23 P_31 + P_13 P_32 P_21 = 0.  So (SM4'') in its main chart is a 9-variable problem on (y_1,y_2,y_3) with G_12 + G_13 + G_23 = 0
   and kappa(y_1,y_2,y_3) = 0 (remaining charts: Gamma degenerate, or y_1,y_2,y_3 dependent).  Not yet a proof.
 R20.2 Pool runs (rows/r18/runW.sh, rsscap 500 MB, 3 h): W4P and W5P started 06:35; then W4Q, W5Q.  Log rows/r18/kW.out.
 R20.3 Pool verdicts so far: W5P killed by the 500 MB resident cap (341 s) -> big slot (R19W5P/Q kept); W5Q stopped (same cap expected);
   reduced main-chart W4 (w4r.sing, adjugate form of R20.1) killed by the cap (329 s; the rational y_4 inflates the system).  W4P running
   since 06:35 at ~0.18 GB (3 h timeout), W4Q queued after it in the same worker (runW.sh; log rows/r18/kW.out).
 R20.4 (CCN) scoping: with w the normal of the defect hyperplane C in 1^perp, (CCN) says w ~ 5 e_n - 1.  Degree 2 of "C(L) inside w^perp"
   reads sum_{a<b} (w_a + w_b) <y_a, y_b> = 0 on L; degree 3: sum_T (sum_{j in T} w_j) t(y_T) = 0; degree 4: sum_j w_j perm(Y without j) = 0.
   No reduction found this round.
STATUS 06:48: round 20 closing; W4P still running in the pool (W4Q next); verdicts will be in rows/r18/kW.out.

# ROUND 21 (start 06:50 UTC). Targets: (1) 9-variable chart of (SM4''); (2) degenerate charts; (3) W4P/W4Q verdicts; (4) (CCN).
STATUS 06:50: round 21 started.
## Section R21 (round 21)
 R21.1 Symmetry caution: O(3) is NOT a symmetry of (SM_n'') (kappa = x1 x2 x3 is only octahedral-invariant), so there is no triangular-Gram
   normal form; symmetries are octahedral x S_4 (columns) x scaling.  Zero-column-excluding coordinate charts (Rabinowitsch z_k y_{k,r} = 1;
   rows/r18/sm5w.py RAB=..) are slower (0.4 GB in 86 s for RAB=1111) than the plain W4 system.
 R21.2 Structure: the D2 + D3 variety for four columns (dim >= 4) lies inside {f = 0} u {some y_k = 0} (both parts exist: N_II rows with
   f = 0; 3-column solutions, a 4-dim family).  A hand proof must show this containment.  In the main chart (R20.1) the triples through y_4
   force (a,b,c) in the kernel of N = [[P_12, P_21, 0],[P_13, 0, P_31],[0, P_23, P_32]] (det N = -(P_12 P_23 P_31 + P_13 P_32 P_21)), i.e.
   (a,b,c) = mu (-P_21 P_31, P_12 P_31, P_21 P_13) when det N = 0, and = 0 (y_4 = 0) otherwise; together with Gamma (a,b,c) = (G_23, G_13, G_12),
   G_12 + G_13 + G_23 = 0 and kappa(y_1,y_2,y_3) = 0.
 R21.3 *** (SM4) IS FALSE *** [explicit counterexample; verified numerically here (rows/r21/cex4.py) and EXACTLY over Q(sqrt3, i) by verify2].
   Walsh coordinates, s = sqrt 3:  y1 = ((s+1)/2, -i(s-1)/2, 0), y2 = ((1-s)/2, i(s+1)/2, 0), y3 = (1/2, i/2, 0), y4 = -y3, column 5 zero.
   f = (1, i, 0) (isotropic, nonzero), 4 nonzero columns, perm(J + tY \ col j) = 24 identically in t for j = 1..5 (all P_2, P_3, P_4 vanish).
   MECHANISM (rank 2, coordinate plane U = {x3 = 0}): kappa = x1 x2 x3 vanishes on U, so every degree-3 condition is automatic.  Degree 2 =
   "g_k = f - 2 y_k isotropic"; in null coordinates p = x1 + i x2, q = x1 - i x2 (f: p = 0, q = 2) this is p_k = 0 or q_k = 1, with
   sum p_k = 0, sum q_k = 2.  Pattern S1 = {1,2} (q = 1, p = +-t), S0 = {3,4} (p = 0, q = +-w): P_4 = -w^2 (3 - t^2)/2, so t^2 = 3.
   (SM4'') (degrees 2, 3 only, f arbitrary) is false already with real points: f = (2,0,0), y = (0.7, +-0.954, 0), (0.3, +-0.714, 0).
   Why the numerics missed it: they used the main chart (y1, y2, y3 a basis).  The "degenerate Gram" chart is EMPTY (det Gamma = det(Y)^2),
   so the only degenerate chart is rank <= 2 -- and it contains the counterexamples.
   CONSEQUENCES: W4P/W4Q (and the big-slot SM4 jobs) cannot be unit -> stopped/dropped.  IS5 for n = 4 fails; PL4 is unaffected (own proof,
   V-r8/r10).  Leaf 3: support 4 needs only case G (verify2), and G4-z5 reduces to the support-4 G plane; P2-z3 = R16P2z3.
 R21.4 PENCILS IN THE COORDINATE-PLANE FAMILY.  The family contains IS3-shaped pencils Y_ka = e1 + ka n with plane support 4:
   t = sqrt 3 fixed, w = ka (g_1 = -t fbar, g_2 = t fbar constant, g_3 = (1 - ka) f, g_4 = (1 + ka) f, fbar = (1,-i,0)); P_4 = 0 for all ka.
   So "(SM4) for pencils" is ALSO false in general.  But here be_1 = be_2 = 0, i.e. NOT case G.  Within the coordinate-plane family there is
   NO case-G pencil (all be_k != 0): g_k in C f (k in S0) or C fbar (k in S1); sum be_k f_k = 0 and sum al_k f_k = 2f force
   sum_{S1} be = sum_{S0} be = 0, sum_{S0} al = 2; |S1| in {1, 3} gives a be = 0, |S1| = 0 gives rank 1 (P_4 != 0), |S1| = 4 is impossible,
   and |S1| = 2 has t = -(al_1 + ka be_1) non-constant, so P_4 = -w^2 (3 - t^2)/2 = 0 forces w = 0, i.e. be_3 = be_4 = 0.  [hand, rigorous]
STATUS 07:12: (SM4) refuted (R21.3); W4P/W4Q stopped; rank-2 (SM5) exact runs (graph charts) and rational case-G plane test running.
 R21.5 (SM5) IN RANK <= 2 [hand + exact].  f isotropic != 0, U = span of the columns (dim <= 2), f in U.
   RANK 1 (all y_k = c_k f, sum c_k = 1) [hand]: P_4 = 24 prod c_k prod_r (Hf)_r, so (Hf)_r = 0 for some row; with f.f = 0 this forces
     f ~ (1, z, z^2) up to signs/permutation (z^3 = 1), kappa(f) = 1 != 0, so degree 3 says e_3(c without j) = 0 for every j.  Then every
     c_j is a root of t^3 - E_1 t^2 + E_2 t - E_3 (E = elementary symmetric functions of all five c), so the c take <= 3 values; the
     multiplicity patterns (5), (4,1), (3,2), (3,1,1), (2,2,1) all force a zero c or a coincidence (e.g. (3,2): b^2(b+3a) = 0 and
     2ab(a+b) = 0).  Same argument for n = 4: c_a c_b c_c = 0 for every triple.
   U DEGENERATE (U = span(f, r), r in f^perp non-isotropic): g_k isotropic forces y_k || f -> rank 1.
   U NONDEGENERATE: U = span(f, f'), f' the second isotropic line, f.f' != 0.  Degree 2 <=> y_k = a_k f (S0) or y_k = f/2 + b_k f' (S1,
     b_k != 0); sum_{S1} b = 0, sum_{S0} a = 1 - |S1|/2.  |S1| = 0: rank 1; |S1| = 1: b = 0; |S1| = 5: 0 = -3/2.  |S1| = 2, 3, 4: rational
     chart f = c(sg), f' = c(sp) (IS4: a vertex outside {f, f'} goes to c(inf)), REAL coordinates (substitution x_2 -> i x_2: P_2, P_4 even,
     P_3 odd in x_2; checked per generator, 0 parity failures).  rows/r21/r2c.py: n = 5, |S1| = 2, 3, 4: UNIT mod P1 (2 s each) and over Q
     (see COMPUTE-rows).  Calibration: n = 4, |S1| = 2 mod P1: dim 1 (the R21.3 family) -- not vacuous.
   Coordinate planes by hand as a cross-check: with null coordinates the P_4 of a 4-set T is (prod_{T cap S0} q)(3 + e_2(p_{T cap S1}))
     (+ 3 prod p if T is inside S1); |S1| = 2: a deletion in S1 leaves e_2 of one number = 0 -> P_4 = 3 prod q != 0; |S1| = 3: p_a p_b = -3 for
     all pairs and sum p = 0 -> p = 0; |S1| = 4: p = (r,r,-r,-r), r^2 = 3, and the deletion of the S0 column gives 3 - 6 + 27 = 24 != 0.
 R21.6 CORRECTED ISOTROPIC-SLICE CHAIN (replaces R17.5 / R18.1 IS5; for verify2).  IS0-IS4 unchanged (audited).
   IS5' (n = 4): (SM4) is FALSE (R21.3).  Consequences: IS2 for |S| = 4 gives nothing (PL4 has its own proof, V-r8/r10); IS3 gives nothing
       for plane supports |S_0| = 4, and "(SM4) for IS3 pencils" is false as well (R21.4), so every |S_0| = 4 case needs its own argument:
       support 4: G (plane test: mod P1 unit R15.2 / R21.7; char 0 = R15GQ or pgRFQ), P2-A, P3, PP (exact Q(i)), P4 (hand);
       support 5: G4-z5 (= support-4 G plane), P4/PP-z5, P3-z4 (exact Q(i), R15.10), P2-z3 (R16P2z3).
   IS5' (n = 5): (SM5) still OPEN; rank <= 2 settled (R21.5); a counterexample would have rank 3.  (SM5) => all |S_0| = 5 cases: P5, S23
       (also exact directly), R4, R5, G4-A, P4/PP-A, P3-A, P2-A (5).  Without (SM5) these need R15R4P/Q, R15R5P/M/Q, R15G4P/Q, R16P2A.
   LEAF 3 then closes from:  [G plane, char 0] + [R16P2z3] + [(SM5) or {R15R4, R15R5, R15G4-A, R16P2A}].
 R21.7 THE REAL TRICK (all Walsh-coordinate generators).  Substituting x_2 -> i x_2 (D = diag(1,i,1)) makes the isotropic conic rational,
   c(s) = (s^2 - 1, s^2 + 1, 2s), and every strongly-level condition (power of i) x (rational polynomial): x_2 -> -x_2 sends H to
   -(row permutation of H), so P_2, P_4 are even and P_3 odd in the x_2-coordinates (the 4x4 permanent is invariant under row permutations
   and under negating all four rows).  Implemented with a per-generator check g = g0 + ii g1, g0 g1 = 0 (counted "parity failures": 0 in
   every run).  Case-G plane (rows/r21/planeG.py REAL FAM): UNIT mod P1 in 14 s / 45 MB (Q(i) version: 30 s / 0.07 GB); Lagrange-eliminated
   variant (LAG) UNIT mod P1 in 303 s (slower, as R15.8 found).  Exact char-0 run pgRFQ.sing started 07:16 (cap 480 MB).
STATUS 07:17: (SM5) rank <= 2 settled (mod P1 + Q partly); case-G plane exact over Q running in the pool (REAL trick).
 R21.8 *** CASE G (support 4) BY HAND, char 0 *** [rigorous; closed forms checked numerically, rows/r21/gidentity.py, deviation 1.7e-14].
   Plane K_0 = span(e1, n): columns y_k(ka) = (u - (al_k + ka be_k) c_k)/2, c_k = c(s_k) isotropic, u isotropic != 0,
   sum be_k c_k = 0, sum al_k c_k = 2u; case G: all be_k != 0 and s_1..s_4 pairwise distinct.  Four nonzero columns, so P_3 of
   deletion k is the single triple T_k = [4]\k: K(y_a, y_b, y_c) = 0 identically in ka.  Write A_k = K(c_k,u,u), B_ab = K(c_a,c_b,u),
   C_T = K(c_a,c_b,c_c).  Expanding 8K(y_T) and using the two linear relations (sum_b be_b B(z,s_b) = K(c(z), sum be_b c_b, u) = 0,
   sum_b al_b B(z,s_b) = 2 A(z), sum_b be_b A_b = 0):
     ka^3:  -be_a be_b be_c C_T
     ka^2:  -1/2 sum_a be_a^2 B_aa + be_k^2 B_kk - (sum_cyc al_a be_b be_c) C_T
     ka^1:  -be_k A_k + 2 al_k be_k B_kk - sum_a al_a be_a B_aa - (sum_cyc al_a al_b be_c) C_T.
   So: ka^3 => C_T = 0 for all T; ka^2 summed over k => sum_a be_a^2 B_aa = 0, then B_kk = 0 for all k; ka^1 => A_k = K(c(s_k),u,u) = 0
   for all k.  But z |-> K(c(z),u,u) is a binary quadratic, not identically zero: K(x,u,u) = 2 x . grad kappa(u), grad kappa(u) =
   (u2u3, u1u3, u1u2) = 0 would need two zero coordinates, hence u = 0 by isotropy; and the conic spans V.  So at most 2 of the s_k
   are roots -- contradiction with 4 (even 3) distinct points.  Hence NO case-G plane: support-4 G is excluded in char 0, and with it
   support-5 G4-z5 (= the support-4 G plane).  R15GQ is no longer needed.  (P_4 and ka^0 were not used.)
STATUS 07:27: case G proved by hand (R21.8); pgRFSQ stopped (not needed).
 R21.9 G4-A (support 5: n-columns 1..4 nonzero with distinct s_k, n-column 5 zero, plane column 5 nonzero) -- HAND REDUCTION [rigorous;
   closed forms checked numerically, rows/r21/g4identity.py, deviation 8e-15].  w := g_5 = al_5 c(t5) (constant), v := 2u - w,
   sum_{k<=4} be_k c_k = 0, sum_{k<=4} al_k c_k = 3u - w.  For j <= 4 (R = [4]\j) the deletion-j P_3 has ka-coefficients
     ka^3: -be_R C_R;   ka^2: -1/2 sum_a be_a^2 B^v_aa + be_j^2 B^v_jj - (cyc al be be)_R C_R;
     ka^1: -be_j l(c_j) - sum_a al_a be_a B^v_aa + 2 al_j be_j B^v_jj - (cyc al al be)_R C_R,   l(x) = 3K(x,u,u) - 3K(x,u,w) + K(x,w,w).
   Chain as in R21.8: C_R = 0 (all triples of [4]); B^v_jj = K(c_j,c_j,v) = 0 (j <= 4); l(c_j) = 0 at 4 distinct conic points, so the
   linear form l VANISHES: 3 Gr(u,u) - 3 Gr(u,w) + Gr(w,w) = 0 (Gr(a,b) = K(.,a,b)).  Coordinatewise: the columns (u_i, w_i) of the
   2x3 matrix [u; w] are pairwise orthogonal for M = [[6,-3],[-3,2]] (det 3), so either (b) w = mu u with mu^2 - 3mu + 3 = 0, or
   (a) one coordinate of u and w vanishes (u, w octahedral vertices on the same coordinate plane) with w = mu u or w = +-sqrt3 * (the
   other vertex of that plane, scaled).  Moreover B^v(z) = K(c(z),c(z),v) = 2[i v3 z^4 + 2(v2 + i v1) z^3 + 2(i v1 - v2) z - i v3] has
   automatically the point-family shape (no z^2 term, constant/leading = -1), and the s_k are its four roots.  So G4-A is reduced to
   finitely many (u, w) shapes with determined points; the remaining conditions (ka^0, deletion 5, P_4) are checked by the plane run
   with these derived equations added (pl5R_G4_5fD*.sing).
 R21.10 (SM5) RANK <= 2 COMPLETE IN CHAR 0.  |S1| = 4 (y_k = f/2 + b_k f', k <= 4, y_5 = -f): the P_3 of deletion j <= 4 is the SAME cubic
   D(b_j), D(z) = -6 k03 z^3 - k12 z^2 + (3/2 k21 - 6 e2 k03) z + (-15/4 k30 - e2 k12 + 6 e3 k03) (k = coefficients of kappa|U in the basis
   f, f'; e = elementary symmetric functions of b_1..b_4), and deletion 5 gives 3 k30 + 2 e2 k12 + 6 e3 k03 = 0 [hand].  Four distinct b's
   => D = 0 => kappa|U = 0 => coordinate plane => contradiction (R21.5 hand).  All equal => b = 0.  Patterns (3,1), (2,2): UNIT over Q (2 s).
   Pattern (2,1,1) (b, b, c, d distinct): k03 = 0 => D = 0 => coordinate plane; k03 != 0 => D = -6 k03 (z-b)(z-c)(z-d), which gives
   k12 = 6b k03, k21 = -4b^2 k03, 5 k30 = 8 b^3 k03 and (deletion 5) 5cd = 9b^2; with these added: UNIT over Q (2 s; the plain run had not
   finished in 573 s).  Together with |S1| = 2, 3 (UNIT over Q), rank 1 and the degenerate plane (hand): (SM5) holds in rank <= 2.
STATUS 07:37: (SM5) rank <= 2 complete (char 0); P2-z3 REAL over Q running (6 min, 0.21 GB); G4-A with derived equations running.
 R21.9' G4-A case split (consequences of l = 0): (b) t5 = s0, al5^2 - 3 al5 + 3 = 0; (a1) s0^2 = 1, al5 (t5^2 - 1) = 0; (a2) s0^2 = -1,
   al5 (t5^2 + 1) = 0; (a3) s0 = 0, al5 t5 = 0 (identity chart; the all-vertex configuration is vert.py's).  Plane system + derived equations
   (l = 0, B^v_kk = 0, C_T = 0) + case: ALL UNIT mod P1 (b 10 s, a1 74 s, a2 84 s, a3 2 s; realsplit ok, 79 generators).  Over Q: running
   (rows/r21/g4c_*.sing).
 R21.11 GENERAL 5-COLUMN CUBIC IDENTITY [rigorous algebra]: for any 4x5 Y with columns y_k and row sum u, 6 D_j = Gamma0 + Phi(y_j) with
   Gamma0 = K(u,u,u) - 3P(u) + 2 sum_a K(y_a,y_a,y_a), Phi(y) = -3K(u,u,y) + 6K(u,y,y) - 6K(y,y,y) + 3P(y), P(x) = sum_a K(y_a,y_a,x).
   With y = (u - g)/2 (degree 2: g isotropic, sum g = 3u): P_3 of all deletions <=> sum_a kappa(g_a) = 3 kappa(u) and
   psi(g_j) := 3K(g_j,u,u) - 2K(g_j,g_j,u) + 2K(g_j,g_j,g_j) - sum_a K(g_a,g_a,g_j) = 3K(u,u,u) - sum_a K(g_a,g_a,u) for every j.
   (For 4 columns plus a zero column, g_5 = u, this reproduces R21.8.)  For R4/R5 planes (five columns with be != 0) the ka-chain does
   not separate A_k (no zero column), so no hand proof yet; they stay with the big slot.
STATUS 07:46: G4-A hand-reduced + 4 cases unit mod P1 (Q running); P2-z3 REAL over Q running (15 min, 0.21 GB).
 R21.9'' G4-A CASE (b) BY HAND.  w = mu u, mu^2 - 3mu + 3 = 0, v = (2 - mu) u, so B^u_kk = 0.  Deletion 5 (columns 1..4), ka^0:
   8 D_5 = 4k0 - 3 sum al_a A_a + 2 sum_{pairs} al_a al_b B_ab - sum_T al_T C_T with sum_{a<=4} al_a c_a = (3 - mu) u, B_aa = 0, C_T = 0:
   = k0 (4 - 3(3 - mu) + (3 - mu)^2) = k0 (mu^2 - 3mu + 4) = k0.  So kappa(u) = 0: u is an octahedral VERTEX.  For a vertex u the quartic
   B^u(z) = K(c(z),c(z),u) has a TRIPLE root (u = c(1): B^u = 4i (z - 1)(z + 1)^3; all vertices are equivalent under the octahedral
   group), so it cannot have the four distinct roots s_1..s_4.  Case (b) is impossible.  [The Q run of case (b) was killed by the cap.]
   Case (a): u, w vertices of one coordinate plane, w = +-sqrt3 (other vertex); then B^v(z) = 2 (z^2 - 1)(i v3 z^2 + 2 v2 z + i v3) (plane
   x1 = 0): two of the s_k are the directions of u and w.  No hand contradiction yet; exact runs g4c_a1/a2/a3 (mod P1 UNIT).
 R21.9''' G4-A CASE (a): FINITELY MANY PLANES, NONE LEVEL.  Case (a) = one coordinate r with u_r = w_r = 0; then u = (0,1,e) (e = +-i,
   scale 1) and, M-orthogonality of the other two columns, w = mu u (-> case b) or w = sg sqrt3 (0,1,-e) (sg = +-1); w = 0 is impossible.
   The coordinate planes are equivalent under the octahedral group (coordinate permutations = row permutations), so plane x1 = 0 suffices
   (the x3 = 0 chart puts roots at s = inf).  For each (e, sg) the points are the 4 roots of B^v (distinct), and be, al are determined up
   to the gauge al -> al + mu be (= shift of ka): a SINGLE plane each.  rows/r21/g4a_cases.py: l = 0 to 1e-15 (consistency), and
   max |perm(J + tY_ka \ col j) - 24| = 107 (sg = +1) and 1.0e10 (sg = -1) at sample (t, ka): NOT strongly level.  [Numerical non-vanishing
   by a wide margin; exact confirmation = g4c_a1/a2/a3 over Q, running.]  With R21.9'' this closes G4-A modulo that exact confirmation.
 R21.9'''' G4-A case (a) EXACT: rows/r21/g4acert.py (plane x1 = 0, u = (0,1,e), w = sg q3 (0,1,-e), points {1, -1, rr, rr'} = roots of
   B^v, be/al by Cramer scaled by D = det[c2,c3,c4], Rabinowitsch rz D - 1, all (t, ka)-coefficients of perm(J + t Y_ka \ col j) - 24):
   UNIT over Q (g4acert_ii_1; ii^2 + 1 and q3^2 - 3 range over both roots, so e = +-i and sg = +-1 are all covered; cross-check
   g4acert_-ii_-1 UNIT, 6 s; "linear relations hold: 1").  => G4-A CLOSED in char 0 (hand chain R21.9 + case b R21.9'' + this).
 R21.12 THE DEGREE-2/3 RELAXATION OF (SM5) IS NOT UNIT (so W5 = sm5w.py ISO=1 and SP5 = cubic on the conic can never prove (SM5)):
   plane x3 = 0, f = (1,i,0), null columns (p,q) = (t,1), (-t,1), (0,1), (0,-2), (0,1): all t^1..t^3 coefficients vanish for every deletion
   (rows/r21/cex5relax.py, < 1e-12), P_4 does not (t^4 = -12, 4.9 - 0.96i, ...).  Only full-statement runs (with P_4) decide (SM5);
   since rank <= 2 is settled (R21.10), the rank-3 part suffices: rank-3 W5 files rows/r21/w5r3_{2147483629,0}.sing (det(y1,y2,y3) != 0,
   WLOG by S_5) as triage; full statement = R17SMC5P/Q (REAL: smcR5.sing).
STATUS 07:57: G4-A closed (exact certificate); W5/SP5 shown unable to be unit (R21.12); REAL big-slot lines sent.
STATUS 07:58: round 21-22 final report sent; pool: bq5R_P2_z3 (Q) + REAL mod-P1 validations running.

# ROUND 23 (start 08:01 UTC). Targets: (1) (SM5) rank 3; (2) P2-A / P2-z3 hand chains; (3) R4/R5 via R21.11; (4) watch logs.
STATUS 08:01: round 23 started.
 R23.0 (aborted round) Idea not pursued: (Z5) "no strongly level 4x5 matrix with ZERO row sum and 5 nonzero (isotropic) columns" would
   kill R4, R5, P5, S23 at once (the n-element of K_0 is such a matrix); necessary conditions: perm[H c(t_a)]_{a != j} = 0 for all j
   (5 equations on 5 conic points) plus the cubic 2K(y_j,y_j,y_j) = sum_a K(y_a,y_a,y_j); not computed (rows/r21/z5num.py draft).
 FINAL STATE (L-gct-210 aborted by Kevin):
   - (SM4)/(SM4'') FALSE (R21.3, cex4.py; exact check by verify2).  Corrected chain R21.6.
   - Case G (support 4) and G4-A (support 5) closed in char 0 by hand + exact certificate (R21.8, R21.9-R21.9''''); audits pending.
   - (SM5) proved in rank <= 2 (R21.5, R21.10); P4-free relaxations (W5, SP5) can never be unit (R21.12).
   - REAL trick + realify.py (R21.7); REAL files rows/r21/*R*.sing (big-slot names R16P2z3R, R16P2AR, R15R4QR, R15R5QR, R17SMC5QR,
     R21W5R3P/Q = w5r3_*.sing).
   - Leaf 3 still needs: P2-z3 (bq5R_P2_z3; pool run stopped without verdict) + [(SM5) in rank 3, or R4 + R5 + P2-A].
STOPPED 08:04
