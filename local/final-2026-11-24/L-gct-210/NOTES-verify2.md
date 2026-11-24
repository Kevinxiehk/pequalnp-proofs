# NOTES-verify2 (role: verify2; round 1: 16:09-16:49; round 2: 16:49-17:31; round 3: 18:06-18:49; round 4: 18:57-19:27; round 5: 19:33-20:04; round 6: 20:09-20:33, stopped early; round 7: 19:43-20:31 UTC; round 8: 20:35-21:04 UTC ; round 9: 21:05-21:25 UTC on Kevin's machine)

## RESULT ROUND 24 (verify2, 07:00-07:45 UTC) -- details in the STATUS lines 07:03-07:43 at the end
 1. UPSTREAM SURVEY (priority 1): no merged lemma closes an open leaf or contradicts a verified step (table in PROOF-MAP).
    - Leads: L_gct_216/217 force a nonzero doubly-centred part in ncol (c)/(d); L_gct_111 gives sum z <= 4; L_gct_152 is the Lean core of the kernel kills.
 2. (SM4) FALSE, verified exactly; (SM5) has no coordinate-plane counterexample.
    - rows R21.5: (SM5) rank <= 2 hand parts verified.
    - REAL trick verified (my own Q(i) generator agrees at |S1| = 2).
    - R21.4 hand claim verified (constant corrected: P4 = 2w^2(t^2-3)).
 3. rows R21.8: support-4 CASE G BY HAND (char 0) VERIFIED. R15GQ is not needed; leaf 3 now waits on R16P2z3 + ((SM5) or the 5-column runs).
 4. CONJECTURE K0 FALSE, verified exactly; the K0 route is withdrawn in PROOF-MAP item 5.
    - ncol's exclusion of all 15 known members is VERIFIED (properness; my re-run at a second prime, 154/154).
    - Open: completeness of the zero-free shaped e = 1 list.
 5. FLq2 LANDED: TC5 over C is LEAN-COMPLETE (0 errors, 0 sorry, standard axioms; the statement is exactly TC5).
    - TrK0p2 is clean; [DC3] A0-ne is UNIT, so SYM-M [DC3] is complete at P1.
 6. F2COL-TABLE (stage2, final): VERIFIED as structure and logic.
    - All symmetry cuts were re-implemented independently and agree exactly.
    - Both RD certificates were re-run exactly; the R2 (0,0,0) chain was re-checked with my own code.
    - CLOSED once 3 missing logs are supplied: Kt3 rows (my re-run is queued), nu = 0 / cross (0,0,1) RED-p, and the jump point (0,-8,7) RED-p.

## RESULT ROUND 23 (verify2, 06:29-07:00 UTC) -- details in the ROUND 23 log at the end
 1. GAP found and CLOSED the same round: ncol's H-a3-SL / H-b22-SL used "e(K_0) = 0 => rigid SL_3 pair", which needs zero 3x5 row sums.
    - ncol confirmed the gap: strongly level K_0 come in 1-parameter families.
    - ncol then closed it (R10.5-R10.9): the classification rigid pairs + F1 + F2 in char 0 checks out (slq1/slq2 re-run; the reflection count is right), and the family systems have finite fibres everywhere (112/112 re-run; the criterion is correct).
    - => Both theorems hold for every q. CONJECTURE K0 is still open.
 2. reg2 stage-1 kills: exact over Q and valid necessary conditions. Two independent spot checks (0000|11111 and 0000|21110) agree: EMPTY. Stage-2 rank-drop loci and the 74 timeouts are open.
 3. ncol's K_0-fixed systems re-run (66 + 132): consistent.
 4. verifyfl 'mu' junk removal: logic checked (induction on the number of '0' columns); 6 random unit items re-run [1]. 4 ab:ab:ab sub-items FAIL at the cap.
 5. stage2's g(nu) zeros lie in {0, -1, 1/3} (exceptional), so my Kt3 check item is closed.
 6. My own SM generator is calibrated (n = 3: dim 3, non-unit); its n = 4 run is too heavy for the pool. No big-slot landings: SYMDC3V2_A0 still holds the slot (msolve 1h45 in).

## RESULT ROUND 22 (verify2, 05:15-06:35 UTC) -- details in the ROUND 22 log at the end
 1. rows R17.5 / R18.1 (isotropic slice, IS0-IS5): VERIFIED as a reduction.
    - (SM4) + (SM5) exclude every remaining leaf-3 case (each has plane support >= 4) and give (PL) and PL4.
    - The single chart is honest (one isotropic point, S_4 row move). smv.py re-run: 120/120.
    - The exact over-Q(i) SM runs are the proof; P1 runs are triage. My own SM4 generator at P1 ran out of time (triage only).
 2. D003-PROP CASE A CLOSED (stage2 R19), audited.
    - The big-kernel lemma's degeneracy set = the setup-exceptional set; T1cert; the alpha_4 = 0 family; X0.
    - My d3a_slim over Q gave 64/70 unit + 6 failed; superseded.
 3. stage2 Kt3 over Q(sqrt46)/Q(sqrt76): VERIFIED (both conjugate lines via Galois). Check item: the zeros of g(nu).
    - R2 lines: msolve char 0 alone is evidence only.
 4. verifyfl R17.4 lambda-words: VERIFIED (cover complete with the decided '0'-pieces; open conditions inside the P1 whole cover; 24/24 words re-run).
    - t0c-01/02/12 are decided, so the rc4 jobs are not needed for them.
 5. stage3: leaf-8 special members include a 1-parameter k_N = 2 family (noted in PROOF-MAP item 7).
 6. Landings: none. The big slot has been held by SYMDC3V2_A0 since 05:11; the Lean extras wait on the lock.

## RESULT ROUND 21 (verify2, 04:00-04:25 and 05:15-05:30 UTC; cut off by the usage limit in between) -- details in the ROUND 21 log at the end
 1. Lean (big-slot extras):
    - FLq rebuild: 7 errors, all heartbeat timeouts, in P4_c2_canon, F1_vprod and noline. TC5_final depends on all three (my dependency closure), so TC5 over C is still NOT Lean-proved; heartbeats only.
    - FLK_FL (FL over Kf): 1 error (propR). TrK0p: 42 unsolved linear_combination goals with numeral denominators over Kf (port engineering).
    - R14s_shape: stopped after 100 Decidable-synthesis errors in f13_cases_00012 (mechanical; nothing after line 4859 checked).
    - R9f has not run yet.
 2. Chart B is redundant for SYM-M under R11.6: CONFIRMED (its only extra point (0,1,-1) is two-column). The four jobs were dropped; PROOF-MAP items 1b/1c updated.
 3. ncol:
    - R211-3: the (L6) system re-run 27/27; RED-p valid (the lam = 0 closure is included).
    - L6G: 39 charts re-run (34 unit, 5 single reduced points, lam = 0); the SN-type length argument is checked.
    - K'-KILL: logic checked.
    - All CONDITIONAL on the exact K' classification (big slot). Case (C) is down to types a3, b22, b23.
 4. Leaf 3: the big-slot runs are queued behind the Lean extras and SYMDC3V2_A0; none has landed. Leaf 3 is not yet closed.
 5. stage3 TWOCOL over Q and stage2 R2 symlines / R1 cofinterp2: not landed.
 6. FLq's TC5_final statement audited: it is exactly TC5 (defect inside C(e_0 - e_1), dim <= 4). Certificate: 0 errors + 0 sorry + no axiom declarations, since the axioms line covers only L_gct_210.

## RESULT ROUND 20 (verify2, 03:15-04:00 UTC) -- details in the ROUND 20 log at the end
 1. Lean window 3, leanzbf R9d (stub test): exit 0, 0 errors, 469 sorry (as designed).
    - Compiled in FULL: t1_proof : T1Hyp, t3f2_proof, lemB, the orientation bridges, the wrappers, and the repaired t1_IIi.
    - => T1 is Lean-checked across stub files, except the 95 never-compiled t3p_* core lemmas.
    - R12s_combo: see the log.
 2. ncol:
    - SPLIT ISOTROPIC (5,1) CLOSED in char 0: R2.14 (zero-free, via CC3) + THEOREM R32 (one zero) + THEOREM Z2 (two zeros).
    - Coverage, setup and RED-p checked (closed projective systems, no saturation, w and i in F_65521 compatibly; the staged refinement is sound). I re-ran sample charts.
    - With SPLIT, NO split (5,1) space exists.
    - THEOREM SN: the mm cross-check is re-run by me with the complete files (01_01 = 24, 01_02 = 12).
 3. stage2:
    - Deg = EMPTY, verified from the certificate polynomials a^5 (a-1)^4 (5a+6): no triple in {0,1,-6/5} sums to -1.
    - The jump locus and the special Z are closed (logic checked).
    - F2col ruling R2 = finitely many nu-lines (runs pending) + points. Ruling R1 still needs its exact rank-drop locus.
 4. rows:
    - Plane test verified; P5 and S23 re-run exact over Q(i); calibrations non-unit.
    - Leaf 3 is closed in char 0 except support-4 G and support-5 P2, G4-A, R4, R5 (mod P1 or big slot).
 5. R31Hyp size: every killed configuration dies with <= 3 column triples (24 need 2, 96 need 3), so at most 336 certified triples instead of about 453. No uniform lemma visible.
 6. Leaf-3 audit for closing:
    - SUBZ/STAGED split, the support-5 case tree and the charts at infinity: verified.
    - vert.py re-run exact over Q(i): R5 and G4 both 120/120 unit.
    - Leaf 3 closes when R15GQ, R16P2z3/A, R15G4, R15R4 and R15R5 land unit over Q(i).
 7. reg2 R15:
    - The 23.3 completeness argument is correct (type-by-type, given (BL) and R3). Leaf 10 is size L.
    - ntype1: ERROR in the q-rank, 4 not 5 (exact + numerical). FO2 <= 8 (not 7) still closes it. COMPUTE-ERRATA [R].

## RESULT ROUND 19 (verify2, 02:12-03:15 UTC) -- details in the ROUND 19 log at the end
 1. Lean window 3:
    - TrK0 (port smoke test): exit 1, 2 errors, 0 sorry. Both errors come from one syntax slip, (finrank_sumZero (Kf := Kf)) (n := k); the same slip sits at 7 places in FLK_field and 5 in TrK11. Reported; leanfl is fixing it.
    - FLK_field and TrK11 were stopped by the coordinator (they would exceed the 60-min per-file timeout); they wait for a dedicated window. So SL_p is NOT yet a Lean theorem.
    - FLq (over C): exit 1, 19 errors, 0 sorry; the final theorem SL+FL uses the standard axioms. The errors sit in 8 late TC5 declarations (TC5_P3, P4_k2_conf, chi_t12, cramer (renamed lemma div_add_div_same), P4_c2_canon, sig23, c2iii_zeta, F1_w0).
    - Tr11: exit 1, 20 errors in the same declarations plus C2iiiLag_proof, 0 sorry.
    - So TC5 is not Lean-checked even over C. R9d and R12s_combo are compiling (after 03:13).
 2. stage2 jump-locus lemma (R15-6): VERIFIED as logic. Deg is not computed yet (the script's superset certificates are correct).
 3. rows: R14-P2Q has not run yet.
 4. reg2 round 13:
    - All 29 line-spanned patterns are settled (reductions checked, exact parts re-run). (S6-FO2) holds for every line-spanned 6-dim space.
    - reg2 found a GAP in its own deformation table (spanning-set parts never deformed). I had missed it (COMPUTE-ERRATA [Q]). PROOF-MAP Branch 4 is relabelled GAP.
 5. stage3:
    - The second X0 (main case, no column element) is checked independently, so (M3') fails too.
    - The (t2) question is now EXTENSION of X0 by (0,g,0,h).
    - RIGOUR NOTE on ST3-TWOCOL: "a second column" is an open condition, so P1 units are evidence only, unless run over Q or used inside a whole cover.
 6. ncol THEOREM SN: audited.
    - The lift is VALID without flatness (finiteness + completion + generic length <= special length). A random M suffices, and the orbit reduction is fine.
    - Chart 01_01 = 24 landed, so THEOREM SN is VERIFIED in c0.
    - The multiplication-matrix cross-check is not available (incomplete data files).

## RESULT ROUND 18 (verify2, 01:57-02:15 UTC) -- details in the ROUND 18 log at the end
 1. leanfl K-field port, static audit PASSED (FLK_field.lean 8006 lines; TrK11.lean 7531 lines).
    - Hypotheses: Field; NeZero 2, 3, 5 only; sqrt(-1) in K; |K| > 20. The 29 derived numerals are products of 2, 3, 5. P1 divides none of them, and F_P1 / F_P1-bar satisfy everything.
    - TrK11 holds the TC5 BLOCKS. Missing even over C: (c1), (c2-iii), the transports and the dispatcher. Not compiled yet (window 3).
 2. ncol:
    - THEOREM PT2: VERIFIED c0 with my OWN generator (11/11 orbit charts unit at P1, RED-p; orbit count, formulas and calibration checked).
    - E3P: exact over Q (my GB [1]).
    - R3.3 (PROD) reduction: verified.
    - RIGOUR FLAG: PROD-NCOL at P1 gives CC3-e2 in c0 (with PT2, whole cover), but NOT (PROD) itself, because non-product is an open condition.
    - THEOREM CC34: VERIFIED with my OWN generator (6/6 orbit charts unit at P1, chart 0123 also over Q).
    - R4.2(a): checked. R4.3 semicontinuity argument: valid.
    - R4.12 (CC45 refuted): confirmed numerically by my fresh-point checks. The column-0 single-column part holds only to 5e-7.
 3. stage3:
    - Sec. 38 (A) rigid member: VERIFIED (re-run: unique column-element solution, radical vdim 1) => free column on 4 rows => PFC, conditional on (5,1)_{m0}. The "three m + w" closure is complete given 37 (K) and (5,1)_{m0}.
    - stage3's non-degenerate X0: checked independently. "X0 empty" is FALSE. PROOF-MAP item 6 now reads (M3') main case + (M3'') "c(v) = 0 forces a column element", then the transposition route.
 4. rows R14:
    - Support-4 case tree: verified (conic, octahedral chart argument).
    - P3 and PP re-run exact over Q(i): unit.
    - P2 needs an over-Q run; G is running.
 5. reg2 R12: (3,1,1,1|), (3,1,1|1)-101 and (2,2,2|) reductions verified, and the exact checks re-run (G = [1]).
    stage2: the R2 kernel kill is verified; the cofactor intersection {0,1}^3 is confirmed by my own minAssGTZ; the degenerate loci are listed.
 6. E-STALE-OUTPUT: CLOSED for the manifest covers (verifyfl re-solve, 0 mismatches).

## RESULT ROUND 17 (verify2, 01:28-01:55 UTC) -- details in the ROUND 17 log at the end
 1. PROOF-MAP: a consolidated "WHAT IS LEFT FOR A COMPLETE PROOF" list now sits at the top: 12 items, each with owner, size and kind.
 2. leanfl's K-field port has not landed. The audit tool is ready: verify2/r17/kfield_audit.py FILE [FINAL]. It lists C-remnants, sorry/axiom, the numeral hypotheses and their factorisations (P1 | N?), and the final theorem's binders.
 3. Stratum (III) / (t2): what is missing is now precise.
    - (M1) Classification. stage3's family is an ANSATZ with p = e_0; no proof yet that p must be a coordinate vector.
    - (M2) A uniform FO2_0 <= 8 certificate on the classified family.
    - (M3) Recommended main route: exact emptiness of the (t2) core X0 = Y_ab + Y_cd (expected dim -3). It needs no classification.
    - The (t0)/(t1)/(t2) bookkeeping is checked.
    - stage3's computation inside the ansatz is VERIFIED symbolically (level <=> s(y) = s(z) = <y,z> = 0; the D_1, D_2, D_3 formulas; defect <= 2 <=> y o z in span(y,z)).
 4. rows R13:
    - Leaf 3(a) VERIFIED: 64/64 distinct charts unit at P1, Galois-covered (sqrt3, i checked mod P1), gauges nonzero; RED-p => c0.
    - Lemma RS (i)-(iii) VERIFIED by hand. (iv) VERIFIED symbolically as a SYSTEM: sigma_3(Y_-k) = E_k/4 - S/12 modulo the degree-2 conditions, so the per-column wording is inaccurate but the systems are equivalent.
    - Leaf 3(b) (supports 4, 5) stays OPEN.
 5. reg2, all independent:
    - (1,1,1|1,1,1) is CLOSED. My own incidence split reproduces 476 EMPTY and 36 NONEMPTY (one orbit), and the single component is linear = M111.
    - R11-1 (conic double deformation trivial): VERIFIED (membership modulo (Q), plus exact conic points).
 6. Compute:
    - D3A drivers fixed. The round-16 wrapper did not count FAILED charts; d3a_slim.py now counts them, and d3a_slim6.py (6 GB) is written and smoke-tested.
    - A1-ne and B1-ne re-run by me: [1] at P1.
 7. Item 12 (top-level case split): I raised a mixed-case question and RESOLVED it. Every minimal pair, whatever its annihilators, goes to branch 3's (Q-r) program (REG1 reduction, V-r5). So the split is exhaustive; the PROOF-MAP wording is corrected.

## RESULT ROUND 16 (verify2, 00:53-~01:55 UTC) -- details in the ROUND 16 log at the end
 Bottom line: one ERROR found by stage3 and confirmed: (PR3) and (PR2-split') are false as stated. R11.6 is VERIFIED as logic, but it needs SL_p / TC5_p.
 1. verifyfl R11.6 (SYM-M targets (5,1) directly, whole cover at P1):
    - (a) properness / specialisation: VERIFIED; (c) R11.11: VERIFIED; (d) the R11.8 minors: VERIFIED (permutation minors in both charts).
    - (h) "u t (t+1) - 1" removes exactly the two-column points in charts A and B.
    - (b) TC5_p: both flagged steps re-checked by me mod P1. My extra check: the S7 pair equations give the same counts over Q(i) and mod P1 (17 + 1 + 1).
    - STILL NEEDED: SL_p and TC5_p as proofs. The Lean proof is over C (evidence: only i is used; literals have prime factors <= 7). Route: port FLk and TC5 to a field K with numeral hypotheses (leanfl).
    - Still open at P1: [DC3] A0-ne and B0-ne; [T22] A 21, 18, 11..0 and B 45, 21, 18, 11..0; [T31] split B (not built).
 2. E-STALE-OUTPUT:
    - My msolve test agrees with verifyfl's: timeouts and segfaults truncate the output to 0 bytes for -g 2, -t 1 and -e. Only an exec failure leaves an old file.
    - mtime audit: 5800 surviving input/output pairs, all genuine.
    - Exposure of recorded UNIT verdicts: nil in practice. Re-runs are optional.
 3. stage3 (PR3) counterexample: VERIFIED with my own code (level; dim 5; row projections (1,2,2,2); single-row part e_3 (x) Z only; defect(X) = 2).
    - It does not extend to dim 9: EXACT at rho = 1, 2, 7/3 (T_1 = 10, sigma_2 rank 4, dim L <= 8).
    - Leaf 7 rewritten. Corrected route: (PR3) for strata (I) and (II), plus a classification and uniform T_1/FO2 bound for stratum (III).
 4. ncol CC3: VERIFIED (case (II) re-derived; the three survivor GBs re-run, [1] x3). R2.14: VERIFIED given CC3.
    - R2.14 covers only SPLIT (5,1) spaces with zero-free m. The split case is left open only for isotropic m with |supp m| = 4.
 5. reg2 round 11, all EXACT by my own code:
    - M111: dim T_1 = 9 and dim L <= 7.
    - The (1,1,1,1|1,1) family: dim T_1 = 9 for every a in P^1, and sigma_2 is never 0 on T_1, so dim L <= 8.
    - The finite-mechanism theorem: VERIFIED as a conditional reduction.
    - Not re-run by me: the incpat uniqueness and emptiness splits, and R11-1.
 6. Lean audit (corrected; Lean writes `sorry` with backticks):
    - R7s_t3 is a stub test with 484 sorry. All 98 core lemmas t3p_* are stubbed (95 never compiled). What compiled is the t3_trans dispatch and T3Rest2 => T1Hyp.
    - Full files that have compiled: FLk (SL, FL) and R3e only.
    - FLn and Tr8full (0 sorry) failed with errors; R7c (0 sorry) is not compiled yet.
    - PROOF-MAP's Lean line now separates (a) blocks compiled in full from (b) full candidate files.
 7. D003-PROP Case A over Q (stage2 generator, Singular slimgb, 2 GB): 8 charts in 25 min (stopped at the 30-min cap). UNIT over Q: 0-1-2-3, 0-1-2-4, 0-1-2-5, 0-1-2-7 and 0-1-3-4, 0-1-3-5 in <= 3 s each;
    0-1-2-6 took 305 s / 0.6 GB and 0-1-2-7 178 s / 0.6 GB. 0-1-3-6 ran OUT OF MEMORY at 2 GB. 0-1-3-7 was at 584 s / 1.5 GB when stopped.
    All coefficients are integral (checked). VERDICT: the route works (exact slimgb over Q = proof per chart), but NOT within 2 GB for every chart.
    The coordinator should schedule the 70 charts with 6 GB / 30 min each (a hard chart is about 0.6-2+ GB); the easy charts take seconds.
    Script: verify2/r15/d3a_slim.py (CHARTS env; ulimit 2 GB inside; change the ulimit line for the big slot). d3a_std.py = the std variant (untested).

## RESULT ROUND 15 (verify2, 00:37-00:55 UTC) -- details in the ROUND 15 log at the end
 Bottom line: no ERROR. Leaf 3 is NOT closed. What remains:
  (a) the 16 special two-column points: RED-p cover at P1 running, 29/64 unit and 1 chart halted on memory;
  (b) (2,1) kernels supported on 4-5 columns, never classified.
 Everything else in leaf 3 is VERIFIED in char 0: R10.7 normal form; R11 (generic, m_a or m_b != 0); R12.10 (m_a = m_b = 0, by hand);
 line d = u (R13.2); A1/A2; family B (R13.1') -- the last three with rows' generators re-run over Q.
 stage3 SR5, SR2111 and the Fourier lemma VERIFIED (own generators: (3,2) 20/20, C* 20/20, calibrated). Leaf 8 open patterns:
 (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0), (2,0,0,0,0).
 stage2 D003-PROP Case A: the coverage is VERIFIED. The 70/70 at P1 uses affine parameters with exclusions, and the char-0 run is msolve
 multimodular, so the label is P1 + char-0 EVIDENCE (needs Singular over Q). F2col v3: slices only (evidence).
 ncol round 2: R2.1-R2.5, the (A)/(B) reductions to (CC3) and the (SR3) route are VERIFIED; Theorem CC3 itself is CL.
 Lean statements: T1Hyp = stage2 T1; TC5_P3 = DI5.3 (P3).
 S2 over Q, non-parallel case: chart 1 halted at 1.42 GB after 25 min (2 GB cap) -> big slot (QUEUE S2-Q-NEQ). No jobs of mine running.

## RESULT ROUND 14 (verify2, 00:12-00:30 UTC) -- details in the ROUND 14 log at the end
 Bottom line: no ERROR in any claim. VERIFIED:
  - ncol's chain for (6,2)/(7,3): "SOME hyperplane" is the same as "every hyperplane" and as (N_e+); (7,3) <= (DI_5;3) + (N_3+); C3, C4, C5.
  - THEOREM N2 (configuration (a)): my own Gr(3,8) generator is unit on 56/56 charts at 2 primes, calibration 32/56. RED-p valid.
  - N3.3 ((b) is untwisted) and the duality N3.1. So configurations (a) and (b) are excluded.
  - reg2 LEMMA SK3; the six double deformations (rank q >= 3 and dim T_1 <= 10).
  - rows R12.5 ((5,1) criterion), Lemma 3COL with its classification, R12.6 (A1/A2 over Q, valid gauge).
  - LEMMA S2 over Q, parallel case: all 3 charts unit by slimgb. The non-parallel charts exceed 2 GB; queued for the big slot as S2-Q-NEQ.
 reg2's (ii-g) curve cover: an open point (fibres over the roots of the lex leading coefficients) was raised and then closed by my own check.
 One PITFALL found: modStd(I,1) = 1 is not a char-0 certificate (errata [N]). PROOF-MAP.md updated: leaf 6, 3COL, SK3, double deformations.
 Errata [N], [O], [P].

## RESULT ROUND 13 (verify2, 23:31-00:10 UTC) -- details in the ROUND 13 log at the end
 Bottom line: [T31] for m0 is COMPLETE AT P1; I re-ran every piece with my own generators. LEMMA S2 is VERIFIED at P1 (independent
 chi-coordinate generator, calibrated); its char-0 run is in progress. stage3's (alpha1) supp-4/supp-2 hand reductions are VERIFIED, and the
 case split (alpha0) + (alpha1, supp 2/3/4) is exhaustive. One GAP: verifyfl's SYM-M per-case char-0 claim (R10.8/M6). The cases are strata,
 not closed sets, so only "all 254 cases unit in both charts" transfers to char 0 (errata [L]). Also VERIFIED: rows R11.1/R11.4-R11.7 (generic
 two-column (2,1) stratum; R11.6 conclusion by an exact Groebner check), reg2 SK2 and the SIGMA/(d) lift_gram certificates (coverage
 recomputed), stage2's patched re-runs (all fixed-data kills confirmed), the F2col audit (labels right: evidence), and the leanfl
 LAG/NB/TC5_P1 statements (they match the paper). PROOF-MAP.md written and current.
 T1 PROOF-MAP.md: base, case split, four branches, node statuses/bases/sources, 11 OPEN leaves with sizes, pending relabels.
 T2 S2 at P1: neq/par charts 1-3 UNIT (<= 122 s), calibration non-unit dim 1. (c1)/(c3) 12/12 (Q(i) and P1). (alpha1) supp 3 48/48 at P1. (alpha0)
    + S-SPEC 60/60 at P1. Hand: 35(B) configuration analysis and rank-one exclusion; 35(C) K_f columns, the S2 elements and the case analysis.
 T3 stage2: patched re-runs confirm crossC1, K33, crossA, D003ptA/B, D04-PROP sigma = 0, 2, (S2). F2col: chart cover and jump locus right; the 67/70
    are mod-p affine (evidence); 3 charts failed; m_0 = 0 open.
 T4 rows R11: hand steps re-derived; R11.6 by Groebner over Q (unit with all m-entries nonzero, calibration non-unit); R11.2 exact scripts re-run.
    Dependency: R10.7 kernel normal form (not re-derived). Open: special kernels, m_a = m_b = 0, three-column.
 T5 reg2 r9: SK2 VERIFIED; R9-1 VERIFIED (logs + my coverage computation + d_0 in T_1); R9-2 CL.
 T6 leanfl: LAG_a / LAG_b / NB / TC5_P1 statements match the paper (statements only; nothing compiled).
 Extra: verifyfl R10.8 audit (GAP, errata [L]); PROOF-MAP updated with SYM-M.

## RESULT ROUND 12 (verify2, 22:47-23:20 UTC) -- details in the ROUND 12 log at the end
 Bottom line: no ERROR in any claim. VERIFIED: stage3's R12 normal form for (alpha) (re-derived) and the whole THEOREM (alpha0) for m0 in
 char 0 (supp 4, 3, 2 each by an independent generator; supp 3 also by a NEW degree-2 hand lemma, found independently by stage3 R14(C));
 verifyfl's build_alpha_kt (complete per chart) and its same-prime ledger; rows R10.2 (independent det on H_3) and R10.6 (EXT-I/II, CHI2 on all
 four m-charts, pencil principle); reg2's (1,1,1,1|2)(A) (re-run), IV-iso/(a,b)/(a,a) points (own Q(sqrt -3) code), Lemma SK, R7-2 (complete),
 R8-1 (by re-run); leanfl's shorter X5_mc argument (paper level; scope: 3-column kernel). EVIDENCE GAP in reg2 R8-1: omega_e0's coverage
 print is broken and the saved log is a stale NPIV = 2 run with larger uncovered loci; my NPIV = 4 re-runs reproduce reg2's stated loci and
 my line runs close the NPIV = 2 extras, so the claims stand (errata [J]). SUMQ5: no verdict yet (big slot); over-Q plan needs the big slot.
 T1 (alpha) normal form: A_j^T z_j = 0, A_j^*A_j = P_1 = 1 + 4 Psi (rank <= 1), A_4^*A_4 = 5 - 4 P_1, sum A_j = -3; P_1 = 0 => A_j = n_j (x) phi_j,
    n_j ~ z_j on supp W. supp-3 lemma: 4 + 3(M + M^T) + M^T M = 0 has no solution with M = v (x) psi + n_3 (x) phi_3 (v, n_3 isotropic) -- char p > 5.
    build_alpha_kt: k_0 = 1 by S_4, 8 INF patterns, Y_r general column-centred with s = b_r, valid gauge, nY = 2 relaxation; KT charts x, 1, 0 open.
    stage3 R14(B) conversion to P1 (i^2 = -1 checked) makes (alpha0) a same-prime piece; R14(F) (alpha1) supp 3 VERIFIED in char 0 by my own
    generator (48/48 unit, sign-reduced; degree-2 truncation non-unit by a numerical root). (alpha1) supp 2, 4 still open (stage3/verifyfl).
    stage3 COMPUTE item 13 cuts (C1), (C2) verified (valid for p > 5).
 T2 R10.2: det(A0|H_3 - 2) = -3375, -273375, 820125 (nonzero; matches rows' spectra). R10.6: EXT lines confirmed with a different gauge and
    minpoly; CHI2 dim 0 in every chart m_k = 1, same three m (plus the trivial m = 1, excluded by sum m = 0).
 T3 SUMQ5: sq5big outputs empty at 23:05 (+---- running since 22:35, ----- paused during the Lean window). UNIT mod p = evidence.
 T4 reg2: details in the log; R8-2 special loci: methodology + one exact sample family ((1,1) row 0 -> 3: (10,4,8) at three t).
 Addition: leanfl X5_mc paper-verified; it removes X5's dependence on VF-A (TC5 still needed for m_a = m_b = m_c = 0).
 E-MSOLVE-BIGCOEFF: my 675 .ms files clean (no coefficient >= p; writers reduce mod p). stage2's mod-p kills relabelled PENDING except the
 five re-confirmed by its patched re-run (crossC1, K33, crossA, D003ptA/B).

## RESULT ROUND 11 (verify2, 22:17-22:47 UTC) -- details in the ROUND 11 log at the end
 Bottom line: no ERROR in any target. VERIFIED: rows R9.1/TR5/R9.3 (+ a relation-free proof of the summed cubic) and sumq.py (relaxation:
 only UNIT counts; UNIT over Q = proof per pattern, UNIT mod p = evidence); reg2 BB/BD, BLOCK (t != 0), DOUBLE-BLOCK (independent cover),
 (2,1,1|1,1) lift certificates (chart 1 + p21111x0); stage3 33(A) conic coordinates (symbolic), Lemma S-SPEC and (alpha0) |supp W| = 4, 3
 (independent generators over Q / Q(i)); stage2 R11 methods and labels. One TOOL TRAP (reg2 chart-0 option vacuous, unused) and one RIGOUR
 WARNING (m0 split A: verifyfl's mod-p (beta) is a proof only together with ALL of (alpha) at the SAME prime -- stage3's char-0 (alpha0)
 does not combine with it). Errata [F]-[I].
 T1 rows: summed cubic = SUM of the five cubic conditions: sum_j P_3(Y^(j))/2 = sum_j T_j = (3 c(sigma) - sum_k c(g_k))/12 exactly (sum-zero
    columns); rows' per-j g-form is valid only modulo degree-2 relations (true on genuine spaces), its sum = 24 sum_j T_j exactly. R10.1 agrees.
 T2 reg2: certificates re-run (CAL proper, lifts unique, rank<=2 locus (1)); 12 special points + 9 sample members re-certified with my code;
    DBLOCK: my seed-7 minors leave 3 points, each dim T' = 10 exactly -> dim T_1 <= 10 everywhere by my own cover. BD chart complete only by
    S_3 on columns 0,1,2 (wording). (1,1,1,1|2)(A): log audit only. (BL): numerical.
 T3 stage3: (A) sympy-exact; S-SPEC: p3(b) lies in the ideal (vdim 12 per chart); |supp 4|: exact Q(i) enumeration (3 W), independent system
    unit, calibrated (t-deg <= 2 non-unit); |supp 3|: 36/36 unit with my generator, but already unit at t-deg 2 even with free n_3 (weak
    calibration; rests on R12 normal form (3)); gauge only over supp W (checked). |supp 2| (stage3 batch) and (alpha1) not yet in.
 T4 stage2: R11-2 RED-p chart method sound; R11-4/5 loophole correctly labelled (second prime does not close it; Singular over Q would);
    Bw formula checked numerically; K33 level exact at 130 points.
 Not done: (1,1,1,1|2)(A) re-run; IV-iso/(a,b) points; R10.2/R10.6 (rows) exact parts; verifyfl build_alpha_kt audit; SUMQ5 verdicts (none yet).

## RESULT ROUND 10 (verify2, 22:03 UTC) -- details in the ROUND 10 log at the end
 Bottom line: rows' THEOREM PL4 (no principal kernel on exactly four active columns) is VERIFIED for all five sign patterns, the orbit
 computations confirmed by my own independent formulation over Q; so principal (5,1) reduces to the 5-column K case. verifyfl's [T31-B]
 for m0 = (1,1,1,1,-4) VERIFIED (hand). stage3's N(w2,w3) level proof and (PR2-split') <=> (PR3) VERIFIED; its exact "dim <= 7" for H0-H2
 independently confirmed by my Schubert-cell test. stage2's exact FO2-joint pipeline audited: sound. One LABEL GAP: verifyfl K1 ("[T31]
 split A empty in char 0 by RED-p") -- RED-p does not transfer a single non-closed stratum; repair by [T22] at the same prime or a run over Q(i)
 (my unstaged Q(i) run timed out; repair stays: conditional on [T22] at p, or verifyfl's staged cut over Q(i)). No error that changes a verdict.
  1. PL4: +++- / +--- (hand, r9); ++++ / ---- (Lemma ORB re-derived by hand + independent orbit test over Q: UNIT, calibration NON-unit dim 2);
     ++-- (datum exact in both orientations, uniqueness sketch, my orbit test over Q: UNIT for both orientations).
  2. R8-Ksign generator (x4ks.py) pre-audited: correct; affine + saturated, so its P1 verdicts will be EVIDENCE -- certify over Q.
  3. Parametric PROP exclusion: spec SPEC PROP-PARAM + QUEUE line "verify2 | PROP-PARAM" (cells 0, 2 of the symbolic-sg system, Singular over Q,
     8 GB, <= 3 h each); ext_qsym.py got a cells= option.
  4. Verdicts: none decisive (Ksign 5-column outputs empty; P5B cells ERROR (memory); [T22] m12m3 case 8 UNIT; stage2 queued runs pending).
  5. Also verified this round: stage2 R10-2 PROP classification (the "split" step holds because the Lagrangian's om-form is skew); stage3
     round 12 Lemma SA1 and (beta-1) (certificate re-run over Q: unit) for split A of [T31] at m0; stage3's H-locus description.
  6. Coordination: stage2 runs its own symbolic-sg D04-PROP chart job ("D04Pasym") -- overlaps my queued PROP-PARAM; keep only one.
 Files: verify2/r10/{orb_indep,orb_sing,t31A_Q,t31A_Q_ctrl2}.py, verify2/r10/orbS_*.sing, t31A_*.sing; verify2/r8/ext_q.py runs on H0-H2.

## RESULT ROUND 9 (verify2, 21:25 UTC) -- details in the ROUND 9 log at the end
 Bottom line: (A) NEW, decision-relevant: stage2's first candidates passing (FO-r) + FO2 + (T2) (R10-2: D003-PROP, D04-PROP) do NOT extend
 to ANY level space of dimension >= 8 -- shown exactly (one prime, Schubert-cell cover, no saturation => char-0 proof) for all 8 members
 tested, including stage2's two saved candidates, by "q_x isotropy at all base points x in X on Gr(3, T'/X)" (+ sampled full equations
 in one cell), calibrated in both directions on L080 (verify2/r8/ext_q.py, ext_full_cell.py). Member-wise; the parametric families
 (sg free, A free) still need a parametric run -- recommended to stage2. (B) No error that changes a verdict elsewhere; one GAP repaired.
  1. stage2 R9-8 LEMMA N1: VERIFIED (by hand). Direct tool audited; D00-3 cells re-run over Q (4 cells, as recorded); the D00-3 / D0-4 loci
     agree with my own numerical T_1/Omega code on rebuilt members. R10-3 decisive test ((**) <=> 9-dim level space, a_r = 1): VERIFIED;
     the two R10-2 candidates are exactly level and exactly (T2)-solvable (confirmed), so stage2 was right that only higher order decides.
  2. rows R8.2 THEOREM CHI1: exact part VERIFIED (re-run + my own elimination: m = e_3 - e_4 is the only solution in the m_3 chart).
     Hand part: GAP (the degree-2 defect has a j-independent term whose polarisation <w,alpha> - W beta was dropped) -- REPAIRED by a case
     split on the zeros of m on M; the conclusion <chi, z_j> = 0 stands.
  3. reg2 secs 8.2, 8.3, 9.4-D, 11.1-11.5: 18 rational members rebuilt with my own exact generator: level, dim T' = 9 / dim Omega' = 2 for
     generic members; dim T' = 10 / Omega' = 3 with exact rank q = 4 (FO2 bound 8) on the special loci -- all exactly as reg2 states.
     (Own bug found and fixed on the way: a null-space routine that silently used floats for integer input; recorded.)
  4. Verdicts: none decisive yet (X4K running; T22H on case 9; DC3-P45-CUT partial; R8-B3cal calibration NONUNIT as required).
  5. rows R5.1, R5.10: VERIFIED; R5.4/5/8 numerical.
  6. Coordinator additions: stage2 R10-4 FO2-JOINT lemma VERIFIED (it is the principle of my extension test; stage2's exact k = 4 chart covers
     agree with my independent k = 3 runs); stage3 LEMMA PFC and the row-kernel bound (sec 30) VERIFIED; rows R8.7 PL4(+++-) and R8.8 (Lemma
     TR, PL4(+---)) VERIFIED by hand (R8.7's finite check redone exactly; its two tiny GB checks not re-run); R8.9 base configurations
     confirmed exactly, Lemma ORB not yet re-derived. Over-Q confirmation: stage2's saved candidate cand_D003P_l1m1 lies in no level space
     of dim >= 8 (56/56 cells UNIT over Q); D04P sg = 3/10: 84/84 over Q. Symbolic-sg run for the whole D04-PROP family: 5 cells UNIT for all
     sg, the two largest cells time out (needs the big slot).
 Files: verify2/r8/{ext_T1,ext_q,ext_full_cell,t2_exact_cand,d003_num,d04_num,reg2_sample,reg2_fo2_special,v0_check,chi3_elim}.py/.sing,
  verify2/r8/extq/ (cell systems), verify2/logs/{extq_*,st2_d003_rerun,chi1_rerun}.log; ledger rows updated.

## RESULT ROUND 8 (verify2, final 21:04 UTC) -- coordinator targets 1-7 + (T2) + PR5 + (T3); details in the ROUND 8 log at the end
 Bottom line: NO ERROR found in any claimed theorem. VERIFIED this round, each with own re-derivation and, where computational, an
 independent or exact check:
  1. stage3 THEOREM F4b-X (z = (1,0,0,0,0) impossible in the regime): moment lemma (M1)-(M4) by hand, (M4) completeness by an exact
     enumeration of all fat-column configurations (C1, C3 only; C3 needs the Pi_w identity), gen9 audited + substitution-tested (M_0), ALL
     five exact eliminations REPRODUCED over Q (C3b 16, C12ab 16, C3c 256, C12ac 256, C1G 192 charts; all UNIT).
  2. rows R7.2 (DC'/NC'-DC' identities, corrected chain), R7.3 THEOREM X5, R7.4 THEOREM PR5: hand parts re-derived; X5 and PR5 each
     confirmed by an INDEPENDENT generator over Q (different charts/parametrisations, own permanent): X5 12/12 UNIT, PR5 24/24 UNIT,
     calibrations NON-unit.  rows R8.1 THEOREM T3 / LEMMA O3 verified.  => every principal (5,1) kernel lives on >= 4 columns;
     "no principal (5,1)" now needs only (PL) [rigorous reduction].
  3. stage2 (T2) re-derived (correct necessary condition). r6_T2.py: no conjugation error, but 30 sample points < 35 cubic monomials:
     its "(T2) not solvable" verdicts are robust, its "solvable" verdicts are not. Survivor (S3) is killed by (T2) for EVERY sg (exact
     polynomial certificate over Q(sg)); (S1): exact FO2 bound 8 (rigorous kill); (S2): exactly (T2)-solvable, z = 3 branch.
     stage2 R9: PROP, N0-W, B-IND (a)/(c)/(d), B(dep) geometry verified by hand; [CRIT] and the exact runs not reproduced (FM, D1M members
     numerically consistent with my own T_1 code).
  4. reg2 sec 9 (REG2-T1): hand parts 9.1-9.3 verified, 9.4 chart cover complete; exact test systems (9.4/9.6, 8.2/8.3) NOT reproduced.
  5. Verdicts landed: none decisive (DC3-P45: TIMEOUT/ERROR only so far; DC3X: 192+ UNIT, 2 memory errors; T22H running; no T31).
  6. SPEC SYM-M written (all |supp m| = 3 at once via the elimination ideal in t over Q; calibrations; why mod p is not enough).
 Files: verify2/r8/{f4b_classify,f4b_repro,x5_indep,pr5_indep,t2_exact,t2_exact_S12,t2_symbolic,fo2_exact_S1,bind_num,d1m_num}.py,
  verify2/r8/{sing,x5,pr5}/ (Singular scripts), verify2/logs/{f4b_chain*,x5_indep,pr5_indep}.log; ledger rows in handover/HANDOVER-verify2.md.

## RESULT ROUND 7 (verify2, final 20:31 UTC, Kevin's 24-core machine) -- targets 1-5 of the coordinator; details in the ROUND 7 log at the end
 Bottom line: NO ERROR that changes any verdict. Everything on my list for this round is VERIFIED (own re-derivation), with two wording
 slips and one stated-reason slip recorded. THEOREM DC3 (three specific m) is now VERIFIED, incl. an independent re-derivation of all its equations (item 6).
 1. verifyfl R5.9 PROP I-ALL, PROP II-ALL                       VERIFIED (all pressed points; ID8 by hand + numerics; ID11 for all 120 placements,
      err 3e-14; three placements complete; m_a = m_b sub-case recomputed). => the N3 calibrations rest on verified statements.
      Also verifyfl R6.2 (kind (R4) first reduction), R6.3 (conditional reduction)  VERIFIED.
 2. reg2 hand proof of 20:08 = THEOREM SP8 (+ 5.1 (Z3))          VERIFIED. Wording: 5.1(b) "dim W_i <= 4" is FK (a_i >= 1); the "<=>" remark
      after SP8 holds only "=>". M*_1, M*_2, single EC moves contain e_i (x) {1, e_a - e_b}^perp exactly: SP8(a) excludes them for all
      parameters. reg2 R2-2(a) (FO2 bound <= dim T_1 - 1) VERIFIED.
 3. stage3 round 7 final: THEOREM Z22 incl. LEMMA DEG            VERIFIED (all four steps, both (IND)/(DEP) branches; Lemma (B) re-proved for
      degenerate U). F4b core example M_0: CONFIRMED (exact level over Z[omega]; invariants; dim T_1 <= 8 rigorous via rank mod p).
      Also (A5) "one vector p" (own argument), (A5') level identities and (i)-(iii), (C6), (C8) VERIFIED; round 8 THEOREM FC [exact]
      REPRODUCED over Q (81/81 UNIT for IDENT23 and FULL) with a substitution control (M_0); (B) parallel y_r VERIFIED.
 4. Local results audited (C1, R6-1, VF-B, LEAN-1, DC3 cells)    no error. C1 samples >= 2x the per-degree quartic count C(d+3,4), acceptance as
      required, 0 target hits so far. R6-1 B/B3/C: affine + saturated => a unit verdict is EVIDENCE only. VF-B: generic-gauge runs m1-m6
      stopped without verdict; chart gauge (c1..c9) implemented correctly; saturated => evidence. Errata: COMPUTE-ERRATA round-7 addendum.
 5. Further new claims: rows R6.1, R6.2 formulas, stage2 R7-4 VERIFIED; stage2 R8-3 Lemma B0-1 TRUE but its reason has a SLIP (Pi is cubic
      in M: use the lam^3-coefficient); reg2 8.2 parameter charts complete (test systems not audited).
 6. THEOREM DC3 (verifyfl R7.3; no 3-dim doubly centred 4x5 space with defect in C m) for m = (1,2,-3,0,0), (1,1,-2,0,0), (1,w,w^2,0,0):
      VERIFIED as a characteristic-0 theorem modulo msolve. (a) gen_n1s cover audited: 254 cases = Schubert cells x image line cells x
      isotropic-line charts ab/z1/z2, complete, Galois-closed, no saturation; R7.1 (reduction char 0 -> F_pbar via properness of the
      Grassmannian, (F2_p) for p > 3) re-derived. (b) INDEPENDENT equations: my own permanent / coefficient code / bases of m^perp on
      gen_n1s's parametrisation give the SAME F_p-span in 254/254 cases for EACH of the three m. (c) the 252 easy m12m3 cases reproduced
      UNIT here. (d) hard cells: piv1 UNIT (coordinator); piv0 UNIT by verifyfl's subsystem cut (R7.2 and cut_cell.py audited); my
      cut-independent split: A UNIT (196 s), B' killed twice by my 2.5 GB cap -> queued as optional. Split-mode controls passed.
      Consequence: types (1,3), (0,4) of (SL_m) are excluded for these three m. NOT a statement for other m (see the symbolic-m caution in
      COMPUTE-ERRATA: the P^1-family is non-unit at two-column m; its elimination ideal must be computed over Q).
      (SL_m) generators gen_n3 [T22], gen_n2 [T31]: covers AUDITED complete; independent equations agree on 6/6 [T31] stage-a AND 6/6 stage-b
      cells and on the [T22] systems sampled (2 so far, run continues to ~20:52 UTC, log verify2/logs/t22_indep_eqs.log); verifyfl's [T22] chain: 84 verdicts all UNIT so far; [T31] chain CRASHED (empty msolve output, memory cap):
      no verdict yet (fail-safe parsing confirmed: a crashed msolve can never count as UNIT).
 Files: verify2/r7/{propII_check,m0_check,fc_subst,dc3_split,dc3_splitBp,dc3_split_ctrl,dc3_indep_eqs,dc3_indep_eqs_m,sl_indep_eqs}.py, verify2/r7/dc3rep/ (manifest),
      verify2/r7/fc_exact_*.{sing,out}, verify2/logs/{dc3rep_m12m3,dc3split_*,dc3_indep_eqs}.log; ledger rows updated in
      handover/HANDOVER-verify2.md; errata addendum in COMPUTE-ERRATA.md.

## RESULT ROUND 6 (verify2, 20:33; round STOPPED EARLY at 20:30 by change of plan) -- audit of the local runs VF-A / VF-B, spec sections, rows R5, stage2 R7
 HANDOVER for the next team: handover/HANDOVER-verify2.md (ledger of every named result with status, pitfalls, errata state, remaining work, scripts).
 Errata: COMPUTE-ERRATA.md, "ROUND 6 ADDENDUM" (20:26) + last block (20:32).
 1. LOCAL RUN VF-A (request A)                          gen.py = spec A line by line: NO ERROR. Verdict CONFIRMED and now a PROOF in char 0:
      own generator on ALL 18 coordinate charts (unit 18/18 for A1-A4 at two primes; CAL non-unit 19/19); homogeneous basis = 18 linear
      forms + E34^2, E32 E34, E32^2; and exact linear algebra mod p without Groebner bases (first-order rank 12 on the 16-dim A_m, binary
      quadrics of rank 3). The solution set is projective, so emptiness mod one prime proves emptiness over Q-bar. The single generic
      affine normalisation of gen.py WAS a gap for a proof; it is closed by these runs. Consequence (with PS, PR3, both verified in
      round 5): no principal (5,1) space for |supp m| = 3.   Scripts: verify2/vf/{own_gen_A.py, drive_A.sh, exact_A.py}.
 2. LOCAL RUN VF-B (request B)                          gen.py = spec B: NO ERROR; calibration REPRODUCED (Singular + own generator
      verify2/vf/own_gen_B.py in an exact chart gauge: unit / dim 0 vdim 24 / unit). Caveats: generic gauge is probabilistic (exact
      replacement given in the errata); after saturation the set is only quasi-projective, so mod-p unit = EVIDENCE, not proof.
      Main cases |P| = 4, 5: no result seen before the stop.
 3. COMPUTE-verifyfl NEXT                               (F1)-(F4), N6 logic VERIFIED. ERROR: "(SL_m) iff [DC3],[T22],[T31] empty" is only
      "if"; a non-unit [DC3] needs [T13] (3-dim doubly centred + one Y with s(Y) != 0) and [DC4]. Rigour note (v) sharpened (projectivity).
 4. COMPUTE-stage2 S4                                   closed form (i),(ii) VERIFIED (hand + 29750 random column pairs);
      ERRATUM: the normalisation sum nu + sum nu' = 0 is missing; data are modulo (kappa,-kappa') and scaling.
    COMPUTE-rows X4, X5                                 VERIFIED (X5 normal form re-derived), no error.
 5. rows R5.6 (SC1), R5.7 NCOL-P, R5.9 NCOL-P3, R5.11 P51 (i),(ii), R5.13 NCOL2-P (+ rigorous part of R5.12)      VERIFIED
    rows R5.2 Theorem DC (a) / NC'-DC (b)               ERROR, REPAIRED: "dim L' = rank c + rank s + dim L'_dc" is only "<=" (correct with
      rank(s restricted to ker c)); counterexample: the level line C(e_0 u^T + (e_1 - e_2) e_0^T), sum u = 0. The "<=" consequences
      stand; the reverse implications are not proved as stated. R5.3 (b) needs (DI_5;2).
 6. stage2 R7: Lemma (FO-r); cross family excluded for all a not in C1 incl. b = 0; the 25 cofactor formulas; pi_r(T_1(X)); R7-3 (a)   VERIFIED
      (slip: "(FO-r) can only fail if e(X) >= 2" should read >= 1).
 7. verifyfl R5.10: reduction for request A VERIFIED; (SL_C) => dim L' <= e + 3 VERIFIED; the "equivalent to" has the flaw of item 3.
 NOT DONE (stopped): verifyfl R5.9 (Props I-ALL, II-ALL: text read, nothing re-derived); stage3 round 7 final (Theorem Z22, Lemma DEG,
   sec. 26 (B'), F4b core M_0, (A5), (C6)-(C8)); reg2's hand proof of 20:08 (3-dim single-row part); rest of stage2 R7; rows R5.1,
   R5.4, R5.5, R5.8, R5.10. GB CPU used this round: about 3 minutes.

## RESULT ROUND 5 (verify2, 20:04) -- spec audit (COMPUTE-ERRATA.md) + rows R4.10/R4.14/R4.15, verifyfl R4/R5, stage2 R6, stage3 sec. 26, reg2
 PART 1: AUDIT of handoff/HANDOFF.md sec. 2, handoff/oracle.py, COMPUTE-{rows,verifyfl,stage3,reg2,stage2}.md -> /home/claude/work/L-gct-210/COMPUTE-ERRATA.md
  Six [A] items (would give a wrong conclusion or a meaningless run):
   A1 COMPUTE-stage3 sec. 0 says "Level spaces of dim 8 exist": false (largest known 7); two "calibrations at dim 8" cannot succeed.
   A2 COMPUTE-stage3 (5c): the pure-plane CLAIM is false. Counterexample: P_c = P_d = P_e = span(e_1, e_2 + e_3), P_a = P_b = span(e_2 - e_3, e_4),
      rho_a = rho_b = e_2 - e_3: all hypotheses hold, four columns used. N2-X is unaffected (it excludes P_c = P_d = P_e by (Q5J)/(P2));
      correct three-way conclusion given.
   A3 COMPUTE-verifyfl C/D (HANDOFF C3): the scripts under-sample (28/44/40/60/45 points vs 34/69/69/125 monomials) and the acceptance
      list has no fresh-point test: a spurious hit would be reported as a counterexample to (SL_m) or as a (5,1) space. Test added.
      (Empirically 19 of 19 hits for k = 3 were genuine: a risk, not an observed failure.)
   A4 "unit ideal modulo p" is evidence, not proof (HANDOFF C4, verifyfl A/B/E, stage3 2/5, rows X1-X4).
   A5 rows/clm.py samples N = 140 points: too few for d = 7 (210 quartic coefficients) and for 5x5 with d = 7, 8 (462, 792);
      run_clm.py does not pass N. reg2/ext7.py: 300 points vs 329.
   A6 "(S6') dim Omega <= 2 without a full free row" (HANDOFF branch 4, C2) is FALSE: reg2's exact family M* (confirmed by me: level
      exactly for 3 rational members; (dim T_1, dim Omega, rank, FO2) = (11, 4, 5, 8); no full free row). Target is (S6-FO2).
  [B]: A_m has dim 16, not 17 (verifyfl A: 13 unknowns; D: Gr(5,16)); "(NCOL_3) + (DI_4x4) => no (7,3)" needs (DI_5;2); C1 acceptance should
   be d - e >= 4; "7-dim 4x5" decides the gap only if e <= 3; FO2 on unpolished LM output under-estimates T_1.
  No errors: oracle.py (the conjugation is handled correctly; three spot runs), all definitions of COMPUTE-rows (re-derived incl. Walsh
   coordinates P_2 = 8 sum x^2, P_3 = 64 perm_3(x), padding, (X2)-(X4)), COMPUTE-reg2 (19:52 version), COMPUTE-stage2 (S3 formulas re-derived).
 PART 2: VERIFICATION (own re-derivation; no error found)
  rows R4.10 (a)-(d) transposed defect construction + padding lemma                     VERIFIED
  rows R4.14 Theorem NCOL-S (a), (b)                                                   VERIFIED (D^(1)(Y) m = -2S m + 4 c o m - 2(c.m) 1 recomputed)
  rows R4.15 (F1), (F2), (FS-DEC) with the lists for e = 1, 2, 3, (F1^T)               VERIFIED
  verifyfl R4.1 Lemma QB, R4.3 Theorem PS, R4.4 PR-RED, R4.5 THEOREM PR3               VERIFIED (all tau-values; det Q_m = -<m,m>/2; remark (i))
  verifyfl R5.1 Lemma C', R5.2 Lemma 3C, R5.3 Lemma NP                                 VERIFIED; the blueprint fact "7 pairs" confirmed numerically
  verifyfl R5.4 Lemma T, R5.5 Prop I', Prop V, R5.6 Theorem SL3-RED (extra)            VERIFIED (my ID8 reads -2<chi_3,u><chi_3,u'> + 2<chi_2,uu'>;
                                                                                        it agrees with the notes' form where it is used)
  stage2 R6-2 cross-family theorem                                                     VERIFIED (T_1 by hand for all b != 0, a not in C1; rank 5 by the
                                                                                        block argument + numerics; the polar formula of P_2 not recomputed)
  stage2 R6-5 (z_i = 3 => four minimal pairs), (T2), lam = 5 lemma, Lemma (z_i = 3)    VERIFIED
  stage3 sec. 26 (round 7): (c1)-(c5), (A1), (A2), (A3) F1, (A4) F3 and F4a, (B)       VERIFIED ((A4): every input of N2-X re-derived for the pair
                                                                                        with lam = 4; the isotropy count replaces (beta-0))
  stage3 sec. 26 (A5) F4b structure, (C5)-(C8)                                         (C5) checked; the rest NOT verified (open families)
  reg2 section 1 (L1-L5), 4.3 (M* level by hand + EC), RESULT C (S6-FO2 => no a_r = 2) VERIFIED; (S6') is false (see A6); the taxonomy F/NC/DR/M*
                                                                                        is numerical (not rerun beyond the 20 files of round 4 and M*)

## RESULT ROUND 4 (verify2, 19:27) -- stage2 RESULT-R5, stage3 sec. 24 (round 6), rows R4 + FL2* consequences, reg2
 Method as before. No error found. One statement is unproved as written ((Q-r)(iii) for columns; partial proof supplied), two wordings are
 imprecise, three numerical readings are tolerance-sensitive (conclusions unaffected).
 1. STAGE 2 RESULT-R5
    Lemma FO2                                                                   VERIFIED
      Exact statement: M a linear subspace of a level space L. T_1(M) = {t in C^{5x5} : <C(J+m), t> = 0 for all m in M} (C = matrix of 4x4
      subpermanents). q_m = Hessian of perm at J + m, a symmetric BILINEAR form on C^25 with entries perm_3((J+m) without rows i,k and
      columns j,l) (0 if i = k or j = l). Then L is inside T_1(M) and q_m(t,t') = 0 for t,t' in L; so for every q in span{q_m}:
      dim L <= dim T_1(M) - ceil(rank(G)/2), G = Gram matrix N^T Q N (plain transpose, NOT conjugate) of q on a basis N of T_1(M); the
      rank is the rank of the restricted form itself (= dim T_1(M) - dim of its radical), not modulo M or L. Proof: eps- and eps^2-
      coefficients of perm(J + m + eps t) = 120, polarisation on L, and "isotropic subspace <= dim - rank + floor(rank/2)".
      Addition: M lies in the radical of q_m on T_1(M), so rank <= dim T_1(M) - dim M and the bound is always >= dim M.
      Sanity with my own implementation (verify2/fo2lib.py, fo2_known.py): (dim T_1, rank, bound) = (8,1,7) for all nine 7-dim spaces of
      my collection, (6,1,5) for K5, with M = L; with random M of codimension 2 the bound is >= dim L in all cases. My first version
      had exactly the bug the author reports (conjugated null basis = hermitian restriction; bounds 5 < 7); fixed.
    Theorem FO-M* (dim T_1(M*) = 8 for ALL parameters) and R5-7 (a) (dim <= 7)   VERIFIED -- closes the GAP of my round 3
      (a)-(d) re-derived; the four exact facts confirmed with my own rational code (verify2/fo_mstar_exact.py): (s1) all perm_4 = 24;
      (s2); (s3) rank 17, T_1(W_7) = W_7 (+) C tau, also directly from 40 cofactor vectors; (s4) dim T' = 10 and the a_c-, a_e-
      coefficients of Q_a, Q_b vanish identically on T'. W_7 is parameter-free, so one exact computation covers all parameters.
      P_2(tau) = -8 checked. FO2 on M* at 5 parameter sets (2 complex): (8,1,7).
    Cases A and B of family (alpha) (R5-2)                                       VERIFIED
      "no zero column"; support analysis of Case A (wording: in (3,3,2) the 2-set either meets S_c cap S_d or meets S_c in ONE point --
      the text says "meets the triple intersection"); Xi* gives rho' = 0; Case B for 0, 1, 2, 3 nonzero h. L_a + L_b = M* follows.
    R5-3 kernel condition, R5-4 formulas (a)-(c)                                 VERIFIED
    Reduction of REG1 to (B1)/(B2)                                               VERIFIED (uses Lemma C, Theorem N and its transpose, S3-1, (Z3))
    Formulation (Q-r): (i), (ii), (iii) rows, (iv)                               VERIFIED
    (Q-r)(iii) columns "every column projection of L_r has dim <= 3"             GAP (no proof in the notes; Lemma C is about two rows)
      REPAIR (own proof): dim pi^c(L_r) <= 3 for every column c EXCEPT possibly one column c with kappa^r = e_c and kappa'^c = e_r
      (the entry (r,c) vanishes identically on L). Reason: pi_{row r + column c}(L) lies in the 9-dim cross space and is killed by the
      functionals <kappa^r, t_r> and <nu, t^c> (nu any annihilator of column c); they are independent unless both are multiples of
      t_rc, so dim(L_r cap L^c) >= 2. In the exceptional case only dim pi^c(L_r) <= 4 holds, and then L = L_r + L^c. Impact: none on
      the surveys (r5_Lr3/r5_Lr4 filter by row projections only); (iii) should be restated with the exception.
    Numerical applications recomputed with my code: N2 block examples (11,7,7) and (13,8,9); L_r candidates (9,3,7) and (10,5,7);
      r5_Lr3_1_0 is not level (the author's "spurious" output). r5_Lr_2_1 (inadmissible) contains 1e-6 singular values: (7,2,6) at
      tolerance 1e-9, (12,7,8) at 1e-5 (author: (11,6,8)). Cross family (R6-2/R6-3): (10,5,7) for b != 0, (13,8,9) for b = 0.
    STILL NUMERICAL (author's own flag): every diagonal block with a two-row column lies in family (alpha). Superseded by N2-X.
 2. STAGE 3 sec. 24 (round 6)
    Lemma S3-2 (b),(c); Lemma S3-3 (b); Lemma S3-4; "planes well defined"        VERIFIED
    Lemma S3-5                                                                   VERIFIED (all coefficient equations redone; the printed P_2 omits
      the term a c s(gam_y) s(p), which vanishes because y is level)
    Lemma 5V                                                                     VERIFIED with an OWN PROOF (the notes give a sketch only):
      three parallel vectors u: U^3 = 0, so u is a unit vector or 2-sparse and then U^2 V = 0 puts all five into C^{mn}; span of
      dim 2 without three parallel: the trilinear map vanishes on U (3, 4 or 5 distinct lines), so U is a coordinate plane; span of
      dim >= 3 without three parallel: impossible (pair with nonzero product, (G2), the two sub-cases "three distinct lines" and
      "two parallel" with |supp x| = 1, 2, 3, 4). Exact pattern filter (verify2/lemma5v_patterns.py): 736 support patterns, 615
      killed by a one-monomial coefficient, 44 inside the conclusion, 77 left to the hand proof.
    THEOREM PL4 (four planes and a line)                                          VERIFIED
      Part 1 ((PL4-1), shapes (I), (D), (B)); Part 2: concurrent-or-coplanar; (2B) v_0 = e_j and |supp v_0| >= 2; (2A)(i) incl. the
      sub-cases "P_k = C^T" and "P_k = P_l = C^T" that the text does not spell out (same computation); (2A)(ii) |R_w| = 4, 0, 1, 2, 3
      with the annihilator table of sec. 21 (the three spaces P_m P_r, w P_m, w P_r span Sym^2 V_3: checked).
      Own numerical probe (verify2/pl4_probe.py; s(w) = 0, |w| = 1, triple products of norm >= 0.5): 35 unconstrained starts gave 9
      exact solutions = 8 (3col) + 1 type I, none of another type; 8 starts with four prescribed non-vanishing columns: none converged.
      Slow solver (10-35 s per start): weak corroboration only.
    THEOREM S3-G and extension S3-G'                                              VERIFIED, given Lemma Q4-gen on L_e
      type I by S3-5; (3col) by the checked L157 (statement read: 3-row level space with zero row sums has dim <= q - 1); only
      gam(L_e) (not all of C(L_e)) is needed inside C^{N_3}. Q4-gen is applied to L_e with the incidence data of case N1 (3-dim row
      kernels, m in {1,2}, disjoint m = 2 pairs, no single-row element in L_e); I checked that these data hold, not the normal forms again.
      S3-G' (1) (one and two rank-one maps), (2), (3) re-derived.
    (C2), (G)(i)-(v)                                                             VERIFIED except the pigeonhole remark in (G)(iii) (not checked)
 3. ROWS R4 and FL2* consequences                                                VERIFIED
    R4.1 Hyperplane Lemma; R4.2 (a)-(d); R4.3 RS-HYP (e = 1, 2, 3; upstream L067 read: k dim W <= M for vanishing power sums 2..k);
    R4.7 Lifting Lemma, D-UP, C-UP; R4.11 ((D)_8 + (DI_5) <=> no 8-dim level space); FL2* (a) (dim(m o U') = 3 iff m has <= 1 zero;
    2 for two zeros), (b) both statements.  Not checked: R4.10, R4.14, R4.15 (not on my list), all numerics of R4.4-R4.13.
 4. REG2
    Phi(L_r) inside R_r^perp of dim a_r - 1                                      VERIFIED
    Omega criterion (dim L - dim L_r <= dim Omega(L_r) - 1)                       VERIFIED (tau_r in T_1(M): derivative of (1-4e)(1+e)^4 at 0)
    Numbers for the six-dim 4x5 spaces                                           CONFIRMED with my own code for all 20 (verify2/reg2_fo2.py):
      19 x (dim T_1, rank, FO2 bound, dim Omega) = (9, 3, 7, 2); rc45 = (10, 4, 8, 3). Caveat: three files (clm_p4_d6_defect3_s3,
      seed_d6_e3_t1, seed_d6_e3_t6) have a smallest kept singular value of 2e-7 .. 1e-9 relative in the cofactor system (their
      reduced bases contain entries of size 1e-7 that cannot be dropped: level error 4e-5 after dropping); read at tolerance 1e-6
      they give (10, 4, 8, 2). Either way the bound is < 9 and Omega = 2: none of the 20 known spaces is the L_r of a 9-dim level space.
      This does NOT close a_r = 2: it is a statement about the known spaces only; T_1 and the rank are semicontinuous, so a proof
      needs a classification of 6-dim 4x5 level spaces or a structural bound (reg2's target dim Omega <= 3).

## RESULT ROUND 3 (verify2, 18:49) -- stage3 sec. 21 (THEOREM N2-X), verifyfl DI5-R3, stage2 RESULT-R4, stage3 secs 18-20/22, rows DI + round 3
 Method as before (own re-derivation line by line; exact machine checks where a claim is computational). No error found; one textual
 slip, and one claim that is proved only at sampled parameters (so stated by its author).
 0. STAGE 3 sec. 21: THEOREM N2-X (family N2 does not occur)                 VERIFIED
    Inputs re-derived: (Q4) for the three 4-sets {a,b,k,l} (the fifth row i in S has L_i = Y_kl (+) X_li; forms (t1)/(t2) apply, incl. the
    triangle form when w || w'; ranks 16 from round 2); (Qb)/(Qa) (the form is antisymmetric under two transpositions, hence 0 on a
    2-dim space); (Q5) and (Q5J); (P2) (all three beta_ik alternating, g_cd = g_ce - g_de); (NT), (NT'); (M7) = (N2-d); pairwise
    meeting of P_c, P_d, P_e; lam_ab = 5 impossible; Lemma I3.
    Proof re-derived: STEP 0; (alpha)(1),(2); (A1) D and B; (A2); (beta-0) (the forced plane span(e_1-e_2, e_3-e_4) and the skew
    argument); polarity (S2 = V_3V_3 resp. PV_3); (beta-2) and (beta-1) for all six types.
    EXACT support (verify2/n2x_annihilators.py, n2x_annihilators2.py, n2x_scan.py; rational arithmetic): dim K(V_3V_3) = 3, 2, 1, 0, 1, 0
    for types (1,1), (1,2), (1,3), (1,4), (2,2), (2,3) (column scalings are automorphisms of A, so alpha = 1_A, beta = 1_B is general);
    K(PV_3) for EVERY plane P spanned by integer combinations with coefficients in -2..2 (349 planes per type): the dimension equals
    the value claimed for its sub-case, no deviation, and no one-dimensional K is spanned by a monomial; K = C H^* L_0 with
    Lam(u_0) = C l_0 and K = C Q_beta + y_x Lam(u_0) confirmed by exact membership.
    SECOND PASS (18:47, whole of sec. 21 re-derived once more from scratch): all annihilators now also by HAND for EVERY plane P, not
    only on the scanned ones: (2,3) Q = q12 y1y2 + y1 l1 + y2 l2 + Q_B: P = V_B gives C Q_beta; P = C u0 + C h gives H^* Lam(u0) with
    dim Lam(u0) = 1 (M_u invertible for zero-free u; for u = (beta_v,-beta_u,0) beta is not in im M_u and ker M_u = C u^*) and l0 never a
    unit vector; P = C u0 + C(h+u1) gives l in Lam(u0) cap Lam(u1) = {l : l.(A_B)_2 = 0} = 0, then Q = c Q_beta and c = 0. (2,2): e5 not in P
    gives P V_3 = V_3 V_3 (the kernel of Sym^2 V_3 -> A_2 is C e5^2), K = C H^*H'^*; P = C e5 + C(xh + x'h'): the six coefficient equations
    give L = 0 if x x' != 0 and L in C H^* if x' = 0. (1,3), (1,4), (1,2), (1,1) inside (A_N)_2 as in the text. Polarity statement
    (annihilator of P_k P_l in Sym^2 V_3^* is span(l_k^2, l_l^2); three squares of pairwise non-proportional forms are independent) and
    T0 (3x2 block: the quadric s(x)s(y) - <x,y> has rank 5 on the hyperplane, so isotropic spaces have dim <= 2) re-proved.
    Numerical probe of the core (verify2/n2x_planes.py: five planes with (Q4) for the three 4-sets, charts forcing the pivots; slow, 46
    starts): 11 solutions = 8 with P_c = P_d = P_e, 2 violating (NT), 1 inside three columns; 0 outside the classes of the theorem.
    CONSEQUENCE (THEOREM N): a 9-dim level space with all a_r = 1 and lam_rr' >= 3 for all row pairs contains a single-row element.
    Dependencies: (P), (G1), (G2); Theorem N1 (round 2 list); Theorem N2-X; upstream L156, L101.
 1. VERIFYFL DI5-R3: THEOREM SPLIT, FS, TS, Lemma HYP                         VERIFIED
    SPLIT is stated correctly: hypotheses "defect line C m, e_i m^T in L', <m,m> != 0". The third-kind space L'_3 (two-column m, ker kappa
    not strongly level) is NOT split (zeta = span(uh, z_1) contains no unit vector), so there is no conflict. For isotropic m the
    conclusion fails: verifyfl's saved spaces re-evaluated with my code (verify2/iso_check.py): split, defect line 1-dim, ker kappa not
    strongly level (0.73; 4.9; 5.6), L(L') level (<= 8e-11). Fresh test (verify2/split_test.py): 12 new 2-/3-dim split spaces with four
    non-isotropic m: ker kappa strongly level in all. (E4)(a) and the search statistics were not rerun.
 2. STAGE 2 RESULT-R4                                                          VERIFIED, except (FO) for all parameters = GAP (as its author says)
    (Z3) z_r <= 4 - e(L_r); Lemma N2-Z (A-D, incl. the new (n,k) = (4,4) computation and the reductions to N2-GEN, which do not use "no
    unit vector"); Theorem N2-Z' ((E0)-(E2), both inclusion-exclusion formulas, Cases A and B). Slip in (alpha2): the text says
    "rho'_4 = r/3"; correct is rho'_4 = 0 and then h_c = x r = 0, so r = 0 and rho' = 0 -- same conclusion.
    M*: level EXACTLY (polynomial identity) and dim T_1(M*) = 8 EXACTLY at 9 parameter sets incl. m_a = m_b, m_a = 0, m_a = m_b = 0, a sign
    change and a rational set (verify2/mstar_check.py). (FO) logic is correct (every level space containing M lies in T_1(M)). GAP: rank 17
    is not proved for all parameters; the chain "N2 with a diagonal block => M*" has two numerical links. All of this is now superseded by
    N2-X (N2 does not occur at all), so nothing downstream depends on the gap.
 3. STAGE 3 secs 18-20, 22                                                     VERIFIED, except (N2-g) (numerical, not rerun) and (N2-h) (steps (1)-(3) checked, (4)-(5) not; moot)
    (N2-a), (N2-b), (N2-c)/(Q5) with its consequences, (N2-d), (N2-e)/I3 with the Lefschetz and 3-support remarks, (N2-f)/(E1), sec. 19
    remarks, Lemma S3-1 (z_i <= 5 - lam_ri <= 2). (N2-h): steps (1)-(3) checked, (4)-(5) NOT checked; its premise is vacuous after N2-X.
 4. ROWS section DI and round 3                                                VERIFIED
    (I1); (I2); (I3) for k = 2, 3, 4 (k = 4 redone by hand: p_4 = -6 beta_R + 24 e_4^col - 2 sum_i beta_{R-i} y_i, counts 6+8+3+6+1 = 24, and beta_R = 0 by P_4 = 0); Lemma D; DDI; DI_3; Proposition O; Corollary H;
    Lemma B'; Lemma TC; SL_3 (a)-(d); FL2 normal form; FL2* (1)-(6) with Delta_1 recomputed; R3.1 (upstream L_gct_215 read: 4x5 level
    <= 7), Lemma EC, Tower Lemma, saturation principle. Not rerun: R3.4, R3.7 numerics and the census.


## RESULT ROUND 2 (verify2, 17:31) -- stage3 secs 13-16, verifyfl DI5, stage2 RESULT-R3: everything VERIFIED; R3-1 is now EXACT
 Same method as round 1 (own line-by-line re-derivation; scripts rerun and re-implemented where they carry weight). No error found.
 1. STAGE 3, secs 14-16                                              VERIFIED
    Lemma Q4-coll (normal form of L_e, the five mu-degrees, h = 0); MIN-D; MIN-E: (a) with the upstream statement of Gct/L156 read in the
    checkout (3 x q, P_1 = P_2 = P_3 = 0 => dim <= q+1; M^T is such a space with q = 5, dim 7); (b-alpha) all three support sizes, plus an
    exact pattern check of the case v_0 = e_j on three columns (verify2/minE_b_alpha.py: 103 patterns; the 6 loop/edge survivors of the
    monomial filter are exactly the ones the text kills); (b-beta) all four multiplicity patterns. (G1), (G2).
    Lemma Q4-gen / THEOREM N1: normal forms re-derived independently (A: one m = 2 pair, no triangle; B: one m = 2 pair, triangle -- here
    "w independent of p" is FORCED, the alternative w = 0 would put zeta in Y_cd; C: two m = 2 pairs, zeta = x^{ac}); the three rank-16
    claims confirmed with my own exact code (verify2/n1_rank.py, coefficient vectors over Q; stage3/q4_m2.py rerun: 16 in all forms).
    Dependency trace of N1: (P), (G1); P_i well defined; CA2 [my repaired proof, round 1]; T1; TR; MIN-A [rank 16]; Q4-coll; Q4-gen
    [rank 16 x 3]; TV; NT [3x2 level <= 2]; MIN-B; plane lemma |Z| = 0 [sec. 12 + my repair 2]; |Z| = 1 [sec. 15 (b)]; |Z| >= 2 [L156].
 2. VERIFYFL DI5: Lemma EQ, THEOREM TC5                               VERIFIED
    Normal form DI5.2 ((i), (ii), C2', C3', C4'), Lemmas Z, LAG, NB, (P1)-(P4) and all seven branches (N-a, N-b, c1, c3, c2-i, c2-ii, c2-iii)
    re-derived, including my own classification of the pairs with tau(v^2v') = tau(vv'^2) = 0 (3 antipodal + 4 zero-row pairs, each
    line in exactly one) and of the blueprint facts actually used (P-a/b, Lemma N, A1, G23, Q1-Q4). TC5 does NOT need Lemma SL itself.
    Simplification: in (c3) the appeal to "type IV is excluded (S6)" is unnecessary -- the u-column of N'' would sweep a 2-dim space,
    against Lemma N. Resultant (F1): confirmed exactly at 60 rational points (both sides have degree <= 24), closed forms E_t, P_t
    confirmed exactly from the definitions; the points at infinity (v or v' = chi_3), not covered by the parametrisation, checked by
    hand (no solution there). (verify2/tc5_checks.py)
 3. STAGE 2 RESULT-R3 and the earlier layers                           VERIFIED
    a. LEMMA N2-GEN (R3-5): Steps 0-3 re-derived line by line. In particular the two strata flagged by the author: |S| = 4, (1,1,1,1):
       all seven moment equations and be be_a be_b = 4c^2 recomputed, the two factorisations A tau (tau-B)(tau-h) = 0,
       B tau (tau-A)(tau-h) = 0 expanded by hand, all four ends (h = 0, tau = 0, tau = h, tau = A = B) contradictory; (2,1,1,1): AB = N,
       VN - F' = A N_b - F' = B N_a - F' = -3F_1, om pqr = -2, the three quadratic class sums give XY = XZ = YZ = -2 and the cubic one
       gives 1 + XY + XZ + YZ = 1: contradiction. Also (1,1,1,1,1) (B | l_b impossible), (3,2), |S| = 1, 2, 3.
       Machine support: the two elimination identities of |S| = 4 hold on the unisolvent 6^4 grid, the Lagrange moment facts and the
       class-sum product identities hold exactly (verify2/n2gen_identities.py); my own LM search on (i)-(iii) with a, b = exp(.)
       (verify2/n2gen_search.py): 96 starts, 58 zeros, 56 with a weight -> 0 or infinity, 2 with a unit vector in P, 0 genuine.
    b. R3-1 (exception triples) IS NOW EXACT. (E1)-(E3) re-derived. (E4) redone over Q(i) (verify2/r3_exact.py, six runs <= 137 s):
       1800 canonical configurations: 1668 excluded by (E1), 120 killed, 12 survive -- identical to stage2's floating-point survey.
       Every one of the 1320 cubics c_S carries an exact certificate: 151 have ell = 0 on Pi~_S (no condition); 673 have three distinct
       linear factors over Q(i), each verified exactly; 152 have one exact linear factor and a cofactor quadric of rank >= 3 on its
       kernel (irreducible); 344 have no linear factor, certified by a rational plane section that is a SMOOTH cubic (Jacobian ideal
       contains all 15 quartics, exact rank); uncertified: 0. DFS and admissibility tests with exact ranks.
       For the 12 survivors (verify2/r3_exact_leaves.py): exactly ONE maximal leaf, containing all others, and it EQUALS the family
       stated in (E4) (exact rank test): 6 x family (a), 3 x A, 2 x B, 1 x C. (E5) recomputed by hand: (a) E_1 = -(1+i) delta_h c_1 ell,
       and for delta_h = 0 perm_3 = c_1 ell^2; A, C (and B by exchanging rows 2,3; computation written out) coefficient of t_1 =
       ell [ i(b-a) + 2d(ell-a-b) ], be = 0 inadmissible. Independent float confirmation of the factor lists by a multiplicity-robust
       finder (r3_survey_robust.py: 2171 = 2171 factors, same verdicts).
    c. Lemma 4x3, Lemma H (incl. 3x3 subpermanents of the Hadamard matrix = +-2), GEN-1, GEN-3, (Y3), (Y5) (incl. the determinant identity
       and AB+AC+BC = e_1e_3 - 4e_4), GEN-7, GEN-8, one-zero layer R2-1 (Type I_0, nu_j0 = 0, no Type II; script r2_triple_onezero.py
       audited and rerun: 364 + 672 killed, 0 survivors): re-derived, correct.
 THEOREM GEN (now unconditional as far as this verification goes): no 9-dim level space of 5x5 matrices has all a_r = b_c = 1 and all row
 and column FK annihilators zero-free.   Proof chain and dependencies:
   (1) R0, ZBF+UFD, ThB, Lemma C (lam >= 2), Theorem A, C4                                  [chief; verified round 1]
   (2) C7/C7'' (minimal pairs are of Type I or II), tau-coordinates, T0                     [chief/stage2; verified round 1]
   (3) T1 (exact scripts t5, t10 + rank check + my re-implementation; T1' by hand), T2, T2'' => (S2)   [verified round 1]
   (4) R3-1: exception triples impossible => (S2*): X_ijk != 0 for all row triples          [exact: verify2/r3_exact*.py; (E5) by hand]
   (5) SR/SC (no single-line elements in GEN), S2-d/GEN-tri, GEN-0, GEN-lin, GEN-2 => no minimal pair: lam >= 3 for all row pairs
   (6) (P), (G1), (G2): all lam = 3 [N1] or exactly one lam_ab = 4 with m_cd = m_ce = m_de = 2 [N2]; lam_ab = 5 impossible
   (7) THEOREM N1 (dependencies in item 1 above; uses upstream Gct/L156) => a single-row element, contradiction with (5)
   (8) LEMMA N2-GEN excludes N2.
 Only the row side of (5) and zero-free column annihilators are used after (5).
 Residual risk, stated honestly: every link is a hand proof re-derived by one verifier (me) plus exact/numerical checks; the parts with
 the least machine support are the plane lemma for supports of size 3, 4 (sec. 12, hand algebra + weak numerics) and sec. 15 (b-beta).
 NOT verified in round 2: stage3 sec. 13 details beyond (II)'s exclusion, sec. 17-18 (family N2 outside GEN), verifyfl DI5.4-DI5.6
 (examples, assessments), stage2 R3 scripts other than those named.


## RESULT (verify2, 16:49) -- independent verification of N3', the ZBF foundations, the stage-2 triple layer / GEN-2, and MIN-A..MIN-C
Method: every proof below was RE-DERIVED by me line by line (not read for plausibility); every machine claim was rerun and, where it
carries weight, re-implemented independently; statements valid for all level spaces were tested on 11 level spaces (L080, ex1, ex2,
ex3, fam(2), fam(0.6+1.4i), K5, K4, rows' Lm(c=0), Lm(c=1), rows' second-kind space). NO ERROR FOUND that invalidates a downstream
statement. Two justifications needed repair (both repaired, items 4b, 4c), one script lacked a needed check (added, item 3c).

 1. THEOREM N3' (stage3 sec. 10)                                   VERIFIED (own proof = the four steps, each re-derived)
    Step 1 (cell factorisation; UFD on the linear space V'; rank <= 1 on the image => dim <= 2), Step 2 ((A) nondegenerate case,
    (D) rank M_u = 2 in BOTH degenerate shapes of u_r, equality iff Rad Q_u in V'', (E) all three sub-cases), Step 3 (kernel of
    multiplication by W^2 is a line), Step 4 ((a)-(e), incl. the explicit expansion in (c) and the transposed use of (b),(c) in (d)):
    all correct. No hidden use of b = J; the only uses of perm(b) != 0 are "no base point has a zero row/column" and k' != 0.
    Counterexample searches (all negative):
      - EXACT structured search (verify2/n3p_struct*.py): all 4-dim spans of 4 elements among the 45 matrices E_c, E_c +- E_c' (c, c' in
        a common line): 148995 subsets, 8934 distinct 4-dim spans inside {perm = 0}; for EVERY one of them perm vanishes identically
        on a complement of V_0 in B_V := {b : D_v D_v' perm(b) = 0 on V_0} (rational arithmetic), so no base point with perm(b) != 0
        exists at all. Controls: the pipeline accepts the 3-dim spaces (strictly upper triangular, b = I) and (3x3 level space,
        b = J); and on 1468 structured 3-dim spans the same criterion finds perm != 0 on the complement 842 times, with an explicit
        valid base point 209 times (verify2/n3p_struct_ctrl2.py) -- so "0 of 8934" in dimension 4 is not an artefact.
      - numerical (verify2/n3p_search.py, own formulation: Grassmannian chart + 60 sample points): 9 structured base points with
        perm(b) != 0: 4-dim 0/360 starts (residual floors >= 2), 3-dim found for every b. Unplanned calibration: for 3 base points
        with perm(b) = 0 the same search FINDS 4-dim spaces in 86/112 starts -- so the hypothesis perm(b) != 0 is essential and the
        search is able to find 4-dim spaces when they exist. With b free (perm(b) = 1): 0/77, only blow-ups (|b| ~ 100, a row -> 0).
    COROLLARY N3'-L                                                 VERIFIED (2 lines from GZ-a + N3'); 71 B1 blocks on 11 spaces, 0 violations.

 2. FOUNDATIONS (chief secs. 2-4)                                   VERIFIED
    R0; ZBF incl. the UFD step (ell != 0 on U: f_i = k_i ell^deg with k_1 k_2 = 120, both k_i != 0; ell = 0 on U: U in L and one
    factor vanishes -- every family to which the team applies it is a LINEAR subspace of L^, I checked each use in items 1-4);
    ThB; Lemma C; Theorem A; N3 (3x3 level <= 3 in 8 lines); C4 (B_x = 0 on the plane of a minimal (1,1) pair; no zero-freeness needed).
    Remark (strengthening, same proof): Lemma C's argument never uses dim L = 9. It proves for EVERY level space of n x n matrices and
    every pair of rows:  dim pi_{rr'}(L) <= 2n - 3,  i.e. dim(L cap {rows r, r' = 0}) >= dim L - (2n-3).  (n = 5: >= dim L - 7.)
    Tests (verify2/test_spaces.py, 11 spaces, both transposes): R0 33; general ZBF over ALL 250 blocks S x Z with |S|+|Z| = 5:
    326 cases with ell != 0 (f_1 = k ell^s, f_2 = k' ell^(5-s), kk' = 120) and 4926 with ell = 0 (f_1 = 0 or f_2 = 0); ThA 1038 + 346;
    ThB 71; CA2 214 + 32: 0 violations.

 3. STAGE 2: C7/C7'/C7'', T0, T1, T1', T2, T2'', S2, GEN-2           VERIFIED
    a. Pair rules re-derived in tau-coordinates (q_T ~ om_j a_j b_l + om_l a_l b_j on {a_j+a_l = b_j+b_l, rho.a + rho'.b = 0}); the
       classification "Type I or Type II" and the normal forms (c = 1/(K_1-K_2), sigma_0 = -K_2(1+c); y = (-1+eps i)/2, corner
       sigma = eps i s) are correct. Small addition: B1 needs k != 0, which gives sigma_j = sigma_l != 0 ALSO for pairs separated by
       both rho and rho' (chief's RP5 omits "!= 0"); harmless, both types already have it.
    b. T2 and T2'' (hand proofs): both cubics recomputed (2t(t a_1 + a_1a_2 + a_1a_3 - a_2a_3), Gram det 1/16; the T2'' cubic and its
       irreducibility), the n** argument and the final "functional of row 1 alone" step are correct. T1' (cyclic Type II triple):
       elimination redone by hand, correct (c = (1-i)/4 leaves -i/8). S2 follows.
    c. T1 scripts: t3, t5, t10, t13 reviewed and rerun (outputs as in the notes). t10 computes Pi_S as the kernel of five explicit
       annihilators but never checks that they are independent on C^15 (needed: otherwise I_3^perp would have an unknown fifth element
       and the certificate would be void). I checked it: rank 5 in all 2080 configurations (verify2/t10_rank.py). So t10 is valid.
       INDEPENDENT re-implementation (verify2/t1_indep.py, own enumeration: the (2,3) structure is found by testing all 315 structures
       against the ratio, not by stage2's shortcut): identical counts -- (I,I) 28 killed / 2 inadmissible; (I,II) 760 / 220;
       (II,I) 120 / 30; (II,II) 2168 killed, 32 survive the kernel test, 640 inadmissible; cube test on the 32: 26 killed, 6 survive =
       exactly the six cyclic triples.
    d. GEN-2 (R2-3) with its inputs SR, S2-d/GEN-tri (incl. |Sigma| != 2, != 5), GEN-0, GEN-lin: Steps 1-4 re-derived, correct
       (dim U = 6 for both types; Step 4 incl. the non-onto case Q_2 = {d} / Q_3 = {d}). r2_gen2_check.py rerun: 50 + 1500, dim 0.
    NOT verified by me (outside the assignment): GEN-1, Lemma 4x3, Lemma H, GEN-3, the one-zero layer R2-1, C8 / Type I', RESULT-R3.

 4. STAGE 3: MIN-A, TV, MIN-B, MIN-C (secs. 11-12)                  VERIFIED, with two repairs
    a. MIN-A: the rank claim re-computed exactly with my own code (verify2/minA_rank.py): 16 for 0 triangles (all 6^4 labellings and
       200 random line triples), 16 for 1 triangle (normal form + 200 random), 11 collapsed. TR, T1 (stage3), MIN-B, TV re-derived;
       dim K(P) <= 1 proved for each support size and checked on 780 planes (verify2/kp_check.py); "3x2 level <= 2" re-derived from
       P_1, P_2 (the hyperplane is nondegenerate: Q(n) = 24).
    b. REPAIR 1 (CA2, used by T1 and hence MIN-A). The stated reason "the 1x4 blocks {e} x (all but m) are not ell-supporting" is
       FALSE when kappa^e_m = 0 (then kappa^e itself is a sum-1 relation on that block) -- and zeros in kappa^e do occur in the
       minimal case (S3-D). The conclusion is still true: for xi in L_e and u in L^, the s^4-coefficient of perm(u + s xi) is
       <u_e, G(xi)>, and pi_e(L^) = C^5 when a_e = 1, so G(xi) = 0. (General form: G(xi) in pi_e(L^)^perp for any a_e; tested.)
    c. REPAIR 2 (MIN-C, (beta), type (2,3,0)). The text jumps from "no 4-set without pinned row" to "every 4-set has >= 2 pinned
       rows"; the case of a 4-set with 3 free rows and 1 pinned row d is not treated. It closes in one line: the coefficient of the
       free variable lam_d is tau(om_a,om_b,om_c) on V_beta^3, which is not identically 0. With that, every 4-set is all-pinned,
       as claimed. Everything else in MIN-C is correct as written: (alpha) supp v_0 = 3, 2, 1 with k = 4 (patterns (4), (3,1), (2,2),
       (2,1,1), (1,1,1,1)), k = 3, k <= 2; (beta) (2,2,1) (two free rows impossible; one free row; no free row).
    d. Extra check of (alpha), v_0 = e_j (verify2/alpha_ej_k2.py, alpha_ej_all.py, alpha_ej_lm.py): of the 736 support patterns of five
       vectors in C^4 (up to column permutations), 103 violate (NZ), 20 violate (NT), 560 are killed EXACTLY by a coefficient that is
       a single monomial; all 125 loop/edge patterns (k <= 2) are settled exactly (the 2 survivors of the monomial filter need three
       parallel edges with pairwise opposite ratios). The remaining 51 patterns (k = 3, 4) are covered by the hand argument; LM in
       logarithmic coordinates finds no bounded solution for the 49 I could run (corroboration only).
    Not verified: sec. 13 (configuration (II)), S3-A/B/C/D.

 Consequence for the team: N3', N3'-L, R0/ZBF/ThA/ThB/LC, C4, C7'', T1, T2, T2'', S2, GEN-2, MIN-A, TV, MIN-B, MIN-C can be used as
 stated. Lean-relevant: Lemma C in the general form above is a clean 2n-3 statement; CA2 should be formalised by the direct Laplace
 argument of 4b, not via ell-supporting blocks.

## Log
STATUS 16:09: started; reading BRIEF, chief secs 2-4, stage3 sec 10.
STATUS 16:13: N3' (all four steps), N3'-L, R0, ZBF, ThB, LC, ThA, N3 re-derived by hand: no error.
STATUS 16:18: stage2 layer re-derived by hand (C4, C7, C7', C7'', T0, T2, T2'', T1', S2, SR, S2-d, GEN-0, GEN-lin, GEN-2); t3, t5, t10, t13
 rerun; t10's missing independence check done (rank 5 in 2080/2080).
STATUS 16:24: stage3 secs 11-12 re-derived (TR, CA2, T1, TV, MIN-B, MIN-C); omitted sub-case in (beta)(2,3,0) found and closed; CA2's
 justification repaired.
STATUS 16:28: MIN-A ranks confirmed exactly; foundation tests on 11 level spaces: 0 violations; N3' numerical search negative with a
 positive calibration at perm(b) = 0.
STATUS 16:40: exact pattern check of MIN-C (alpha) k <= 2; dim K(P) check; free-b N3' search (only blow-ups).
STATUS 16:47: exact structured N3' search (8934 spans, none admits a base point); independent re-implementation of T1 reproduces all counts.
STATUS 16:49: RESULT written. Files: verify2/{test_spaces,vlib,minA_rank,t10_rank,t1_indep,n3p_search,n3p_free2,n3p_struct,n3p_struct2,
 n3p_struct3,n3p_struct_ctrl,alpha_ej_k2,alpha_ej_all,alpha_ej_lm,kp_check}.py, logs in verify2/logs/.

# ROUND 2 (start 16:49, budget 90 min -> ends ~18:19). Targets: (1) stage3 secs 13-16 (Q4-coll, (II), MIN-D, MIN-E, N1 + q4_m2.py);
#  (2) verifyfl DI5 (Lemma EQ, TC5); (3) stage2 RESULT-R3, R2-1, GEN-1, GEN-3, Lemma H.
STATUS 16:49: round 2 started; reading stage3 secs 13-16.
STATUS 16:53: stage3 secs 14-16 re-derived: Q4-coll, MIN-D, MIN-E ((a) with the checked L156 statement read in the checkout; (b-alpha), (b-beta)
 all four multiplicity patterns), (G1), (G2), Q4-gen (normal forms re-derived; ranks 16/16/16 by my own exact script n1_rank.py), N1: no
 error. Exact pattern check of (b-alpha) v_0 = e_j on 3 columns (minE_b_alpha.py). Next: verifyfl DI5.
STATUS 17:01: verifyfl DI5 re-derived by hand: DI5.2 normal form ((i),(ii), C2', C3', C4'), Lemma EQ, Lemma Z, LAG (a),(b), NB, TC5 (P1)-(P4) and all
 seven branches (N-a, N-b, c1, c3, c2-i, c2-ii, c2-iii), incl. my own derivation of the pair classification tau(v^2v') = tau(vv'^2) = 0 and of
 the blueprint facts actually used (P-a/b, A1, G23, Q1-Q4, Lemma N). Resultant (F1) confirmed exactly at 60 rational points (degree <= 24),
 closed forms E_t, P_t confirmed exactly (tc5_checks.py). No error. Next: stage2 RESULT-R3, R2-1, GEN-1, GEN-3, Lemma H.
STATUS 17:03: stage2 extras re-derived by hand: Lemma 4x3, Lemma H (V_4-Fourier argument), GEN-1, GEN-3 (a),(b),(c), R2-1 pair classification
 (Type I_0; nu_j0 = 0; no Type II): no error. Next: R3-1 (exception triples), R3-5 (N2-GEN), scripts.
STATUS 17:20: Lemma N2-GEN re-derived line by line (Steps 0-3; all seven moment equations of |S| = 4 (1,1,1,1) and all class-sum identities of
 (2,1,1,1) recomputed): no error. R3-1: (E1)-(E3) re-derived; (E5) both hand computations recomputed (family (a): E_1 = -(1+i) delta_h c_1 ell,
 then perm_3 = c_1 ell^2; families A/C: coefficient ell[i(b-a) + 2d(ell-a-b)]); (E4) redone EXACTLY over Q(i) (verify2/r3_exact.py):
 parts 0-4 of 6 done, 0 uncertified cubics; part 5 and the leaf identification running.
STATUS 17:26: exact R3-1 complete (6 parts, 0 uncertified cubics; 12 survivors = the 12 claimed families, unique maximal leaves).
STATUS 17:31: RESULT ROUND 2 written (moved to the top). New files: verify2/{n1_rank,minE_b_alpha,tc5_checks,r3_survey_robust,r3_stats,r3_exact,r3_exact_leaves,r3_e5}.py,
 logs in verify2/logs/ (r3_exact_p5.log, r3_leaves_b1.log, r3_leaves_b2.log).

# ROUND 3 (start 18:06, budget 90 min -> ends ~19:36). Targets: (1) verifyfl DI5-R3 (THEOREM SPLIT, TS, isotropic m); (2) stage2 RESULT-R4
#  (N2-Z, N2-Z', M*, FO, Z3); (3) stage3 secs 18-20; (4) rows section DI (DI_3, Lemma D, DDI, Prop O, Cor H, Lemma B', Lemma TC).
STATUS 18:06: round 3 started; reading verifyfl DI5-R3.
STATUS 18:11: verifyfl R3: SPLIT, FS, TS, HYP re-derived (correct; hypotheses of SPLIT are right: the third-kind space L'_3 is NOT split,
 zeta = span(uh, z_1) contains no unit vector); fresh 2-/3-dim split spaces with non-isotropic m: ker kappa strongly level in 11/11.
 stage2 R4: (Z3) and the logic of (FO) re-derived; M* level exactly and dim T_1(M*) = 8 exactly at 9 parameter sets (mstar_check.py).
STATUS (after restart): verifyfl's isotropic examples re-evaluated with my own code (verify2/iso_check.py): the 2-dim and both 4-dim spaces are
 split (e_3 m^T inside), m = (1,w,w^2,0,0) up to order, defect line 1-dim, ker kappa NOT strongly level (0.73, 4.9, 5.6), L(L') level (<= 8e-11).
 So <m,m> != 0 in THEOREM SPLIT is necessary and the theorem is stated correctly. stage2 R4: Lemma N2-Z and Theorem N2-Z' re-derived
 (one slip in the text of (alpha2): it should read rho'_4 = 0 and r = 0, conclusion unchanged). New top priority: stage3 sec. 21 (N2-X).
STATUS 18:27: stage3 sec. 21 THEOREM N2-X re-derived line by line: inputs ((Q4) for the 4-sets containing a,b via the (t1)/(t2) normal forms incl.
 the triangle case w || w'; (Qb) by total antisymmetry; (Q5)/(Q5J); (P2); (NT), (NT'); (M7); pairwise meeting; lam_ab = 5 impossible; Lemma I3);
 case (alpha) (A1: D, B; A2); case (beta) (beta-0; types (1,1), (1,2), (1,3), (1,4), (2,2), (2,3) for three distinct planes and for
 P_k = P_l). All annihilator claims K(V_3V_3), K(PV_3) confirmed EXACTLY (verify2/n2x_annihilators.py, n2x_annihilators2.py, rational
 arithmetic, incl. K = C H* L_0 and K = C Q_beta + y_x Lam(u_0)). No error. Next: rows section DI and round 3.
STATUS 18:30: rows section DI and round 3 re-derived: (I1)-(I3) for k = 2, 3, Lemma D (Rado induction), DDI, DI_3, Proposition O, Corollary H,
 Lemma B', Lemma TC, SL_3 (all of (a)-(d) recomputed), FL2 normal form, FL2* (steps 1-6, Delta_1 recomputed), R3.1 (upstream L_gct_215
 statement read: 4x5 level <= 7), EC, Tower Lemma, saturation principle: no error. Next: stage3 sec. 18 remainder, 19, 20, 22.
STATUS 18:38: RESULT ROUND 3 written at the top. New files: verify2/{split_test,split_test2,iso_check,mstar_check,n2x_annihilators,n2x_annihilators2,
 n2x_dbg,n2x_scan,n2x_planes}.py, logs/{split_iso,n2x_planes_s2}.log.
STATUS 18:49: second pass over sec. 21 finished (annihilators by hand for all planes; (I3) k = 4 redone). (N2-h): steps (1)-(3) checked,
 (4)-(5) not, and it is moot after N2-X. Handing back.

# ROUND 4 (start 18:57, budget 90 min -> ends ~20:27). Targets: (1) stage2 RESULT-R5 (FO2, FO-M*, Cases A/B of (alpha), REG1 -> (B1)/(B2), (Q-r));
#  (2) stage3 secs 22-24 (S3-5, PL4, S3-G); (3) rows R4 (R4.1, R4.2, R4.3, R4.7, C-UP, R4.11) + FL2* consequences; (4) reg2 (Phi(Y) remark, FO2 numbers).
STATUS 18:57: round 4 started; reading stage2 RESULT-R5.
STATUS 19:04: stage2 R5 checked: Lemma FO2 (statement + proof; bilinear restriction; own implementation verify2/fo2lib.py reproduces (8,1,7) on all
 nine known 7-dim spaces and (6,1,5) on K5 -- my first version had the conjugation bug the author describes, bounds 5 < 7, fixed); Theorem FO-M*
 for all parameters ((a)-(d) re-derived; (s1)-(s4) confirmed exactly, verify2/fo_mstar_exact.py: rank 17, dim T' = 10, linear parts in the a_d-
 direction only); R5-7 (a) (dim <= 7, P_2(tau) = -8); Cases A and B of family (alpha) by hand (one imprecise sentence in (3,3,2)); R5-4 formulas.
 OPEN POINT: (Q-r)(iii) "every column projection of L_r has dim <= 3" has no proof in the notes (rows: Lemma C; columns: ?).
STATUS 19:11: stage3 sec. 24 re-derived: Lemma S3-2 (b),(c); S3-3 (b); Lemma S3-4 (V-twisted, (QL)); planes well defined; Lemma S3-5 (all coefficient
 equations; the formula for P_2 omits the term a c s(gam_y) s(p), which is 0 because y is level); LEMMA 5V: OWN PROOF (three parallel => unit or
 2-plane; span 2-dim => T = 0 on U => coordinate plane; span >= 3 and no three parallel => contradiction via (G2), kernel types, the isotropy
 argument in three columns) + exact pattern filter (verify2/lemma5v_patterns.py: 736 patterns, 77 survive the monomial filter -- these are covered
 by the hand proof); THEOREM PL4 Part 1 ((I),(D),(B)), Part 2 (2B), (2A)(i),(ii) all sub-cases incl. the three sub-cases of "a plane equals C^T"
 that the text treats as one; THEOREM S3-G ((3col) step with the checked L157, statement read); S3-G' (1)-(3). No error.
STATUS 19:14: rows R4.1 (Hyperplane Lemma), R4.2 (a)-(d), R4.3 (RS-HYP; L067 statement read: k dim W <= M), R4.7 (Lifting Lemma, D-UP, C-UP),
 R4.11 (equivalence), FL2* consequences (a), (b) (dim(m o U') = 3 for <= 1 zero; = 2 for two zeros): all re-derived, no error. Next: reg2.
STATUS 19:18: reg2: (a) Phi(L_r) in R_r^perp (dim a_r - 1) re-derived; (b) the Omega criterion (tau_r = J - 5 e_r 1^T in T_1(M); 1 not in pi_r(L);
 dim L - dim M <= dim Omega(M) - 1) re-derived; (c) numbers recomputed with my own code (verify2/reg2_fo2.py) for ALL 20 six-dim 4x5 spaces:
 19 x (dim T_1, rank, bound, dim Omega) = (9, 3, 7, 2), rc45 = (10, 4, 8, 3): agree with reg2. Caveat: for clm_p4_d6_defect3_s3, seed_d6_e3_t1,
 seed_d6_e3_t6 the smallest kept singular value of the cofactor system is 2e-7 .. 1e-9 relative (entries of size 1e-7 in the reduced bases):
 at tolerance 1e-6 they read (10, 4, 8, 2). Bound < 9 and Omega = 2 either way.
 stage2 extras recomputed: L_r candidates /tmp/r5_Lr3_1_1 (9,3,7), r5_Lr3_1_2 (10,5,7) agree; r5_Lr3_1_0 is not level (the "spurious" one);
 r5_Lr_2_1 (inadmissible) has singular values 1e-6 in two row projections: (7,2,6) at tol 1e-9, (12,7,8) at tol 1e-5 (author: (11,6,8));
 N2 block examples: (11,7,7) and (13,8,9) agree; cross family X(a,b): (10,5,7) for b != 0, (13,8,9) for b = 0 agree (R6-2/R6-3).
 (Q-r)(iii) columns: OWN PROOF of "dim pi^c(L_r) <= 3 unless kappa^r = e_c and kappa'^c = e_r" (the functionals <kappa^r, t_r> and
 <kappa'^c, t^c> on the 9 cross coordinates are independent unless both are multiples of t_rc); the exceptional column is NOT excluded.
 Remark on FO2: M lies in the radical of q_m restricted to T_1(M) (q_m(m',t) = d/de D_t perm(J + m + e m') = 0), so rank <= dim T_1 - dim M.
 PL4 probe running (verify2/pl4_probe.py).
STATUS 19:27: PL4 probe finished (35 starts: 8 (3col), 1 type I, 26 not converged; variant with four non-vanishing columns: 0 of 8 converged).
 RESULT ROUND 4 written at the top. New files: verify2/{fo2lib,fo2_known,fo2_mstar,fo_mstar_exact,fo2_stage2_cands,reg2_fo2,reg2_limits,
 lemma5v_patterns,pl4_probe}.py, logs/pl4_probe_*.log. Handing back.

# ROUND 5 (start 19:33, budget 90 min -> ends ~21:03). (1) audit COMPUTE-{rows,verifyfl,stage3,reg2}.md + handoff/HANDOFF.md sec. 2 + oracle.py
#  -> COMPUTE-ERRATA.md; (2) rows R4.10, R4.14, R4.15; verifyfl round 4 (QB, PS, PR-RED, PR3) + round 5 (3C, NP); stage2 round 6 (R6-2, (T2),
#  lam = 5 lemma, "z_i = 3 forces four minimal pairs"); stage3 round 7; reg2 (S6'), Type F / Type NC.
STATUS 19:45: spec audit done -> /home/claude/work/L-gct-210/COMPUTE-ERRATA.md. [A] items: stage3 "level spaces of dim 8 exist" (false; breaks two
 calibrations); stage3 (5c) claim false as a plane statement (explicit counterexample P_c=P_d=P_e=span(e1,e2+e3), P_a=P_b=span(e2-e3,e4));
 verifyfl C/D acceptance lacks a fresh-point test while the scripts under-sample (28/44/40/60/45 points vs 34/69/69/125 monomials);
 mod-p unit ideals are not proofs; clm N = 140 too small for d = 7, 8. [B]: A_m has dim 16 not 17; (NCOL_3)+(DI_4x4) => no (7,3) needs
 (DI_5;2); C1 acceptance should be d - e >= 4. oracle.py: no errors. Now part (2): rows R4.10, R4.14, R4.15.
STATUS 19:47: rows R4.10 (a)-(d) (transposed defect construction, padding lemma), R4.14 (Theorem NCOL-S: formula D^(1)(Y) m = -2S m + 4 c o m
 - 2(c.m) 1 recomputed; (a), (b)), R4.15 ((F1), (F2), (FS-DEC) incl. the lists for e = 1, 2, 3, (F1^T)): re-derived, no error. Next: verifyfl R4/R5.
STATUS 19:50: verifyfl R4: Lemma QB, Theorem PS (a)-(c), PR-RED, THEOREM PR3 (steps (1)-(4), all tau-values, det Q_m = -<m,m>/2, remark (i))
 re-derived, no error. R5: Lemma C', Lemma 3C (identity ID10, cases r = 0, 1, >= 2, sign contradiction), Lemma NP (a), (b) re-derived; the
 blueprint fact "7 pairs" confirmed numerically (verify2/seven_pairs.py: 14 ordered solutions, 7 disjoint pairs: 4 zeta, 3 chi). Next: stage2 R6.
STATUS 19:52: stage2 R6: cross-family theorem R6-2 (permanent formula, all cofactors, <C(U),t>, degree 2/1/0 analysis -> T_1 of dim 10 for
 b != 0, a not in C1; block rank argument 2*2 + 1 = 5; numerics (10,5,7) from round 4; the polar formula for P_2 not recomputed), R6-5 (a),(b),
 (T2) (order-2 coefficient of <v, G(T(v)+xi)>), lam = 5 lemma (C Phi + Phi^T C = 0; diagonal argument), Lemma (z_i = 3): re-derived, no error.
STATUS 19:55: stage3 sec. 26 (round 7): counting tools (c1)-(c5); (A1); (A2) lam-patterns F1/F3/F4a/F4b; (A3) F1 (graph connectivity, (QL) with
 one/two/three rank-one maps); (A4) F3 and F4a: every input of N2-X re-derived for the pair with lam = 4 ((Q4) x 3 via (CA2) on L_m and the
 injectivity lemma, planes independent of m, (Qb), (Q5) by the hyperplane argument, (NT), (NT'), (M7)), and the isotropy count replacing
 (beta-0) (Q = (J_3 - I) (x) I_2 nondegenerate on P^3); (B) Lemma dim(U o U') >= 2 and its corollary: re-derived, no error. (A5), (C5)-(C8):
 structure statements read, (C5) checked, the rest not (open families).
STATUS 20:01: stage2 COMPUTE spec read; reg2's M* confirmed (verify2/reg2_mstar.py, reg2_mstar_exact.py); verifyfl R5.4-R5.6 verified; errata
 updated (A6, stage2, section F); RESULT ROUND 5 written. Lemma Z probe running (verify2/lemmaz_probe.py).
STATUS 20:04: Lemma Z probe: 0 constrained solutions in 9 starts, control 20/20 (17 with an exact zero row or column). Conjugation handling
 checked in all scripts that compute T_1 / Omega. Errata final (180+ lines). New files: verify2/{audit_verifyfl,audit_sampling,seven_pairs,
 reg2_mstar,reg2_mstar_exact,lemmaz_probe}.py, verify2/spot/ (one (4,1) hit of run_clm.py), logs/lemmaz_s*.log. Handing back.

# ROUND 6 (start 20:09, budget ~2 h -> ends ~22:09). (1) audit local session's exact runs /home/claude/coord/local/results/VF-A, VF-B;
#  (2) COMPUTE-verifyfl NEXT (N1-N6, (F1)-(F4)), COMPUTE-stage2 S4, COMPUTE-rows X4/X5; (3) rows R5 (NCOL-P3, P51, SC1, DC/NC'-DC, R5.13),
#  stage2 R7 ((FO-r), 25 cofactors, cross family), verifyfl R5.9, R5.10; (4) stage3 sec. 26 (A5), (C6)-(C8).
STATUS 20:18: VF-A audited line by line (gen.py = spec A; W basis, A_m parametrisation, coefficient extraction, cases, normalisation). The verdict is
 now established three ways: (i) local gen.py (generic chart, 4 primes); (ii) my OWN generator (verify2/vf/own_gen_A.py: 20 variables + linear
 constraints, squarefree-algebra expansion, N removed by two zero cells) on ALL 18 coordinate charts: unit in 18/18 for A1-A4 at two primes, CAL
 non-unit in 19/19; homogeneous Groebner basis = 18 linear forms + all three quadratic monomials of the two remaining variables; (iii) exact
 linear algebra mod p (verify2/vf/exact_A.py): first-order rank 12 (kernel = N + 2 directions), the x^2-coefficients on these two directions
 span all binary quadrics. Since the solution set is PROJECTIVE, emptiness mod one prime proves emptiness in characteristic 0 (a point over
 Q-bar reduces to a point mod P): request A is a THEOREM, not only evidence. VF-B: gen.py = spec B (parametrisation, (2), (3), saturation);
 calibration reproduced here with Singular (unit; dim 0 vdim 24) and with my OWN generator in an exact chart gauge (verify2/vf/own_gen_B.py).
STATUS 20:23: COMPUTE-verifyfl NEXT audited: (F1)-(F4) correct; "(SL_m) iff [DC3],[T22],[T31] empty" is only "if" ((SL_m) does not imply [DC3]; if
 [DC3] is non-unit, type (1,3) = 3-dim doubly centred + one more needs its own system); RIGOUR NOTE (v) can be sharpened: for a system covering ALL
 points of a PROJECTIVE variety, unit at one prime IS a proof in char 0 (not so with saturations / open conditions). COMPUTE-rows X4, X5 consistent
 (X5 normal form re-derived: f = phi v + eta n, t = 2 m_a m_b eta/(m_a - m_b), only m_c = 0 possible). COMPUTE-stage2 S4: the closed form (i), (ii)
 re-derived (radical vector = q-dual of c_1 R_1 + c_2 R_2, ell of it = a_T c_2) and gamma_check = pair_check on 29750 random sparse column pairs;
 but S4 omits the normalisation sum nu + sum nu' = 0 (and (nu,nu') is defined modulo (kappa,-kappa'), not modulo (kappa,0) and (0,kappa')).
 rows R5: (SC1), NCOL-P, NCOL-P3, P51 (i),(ii), NCOL2-P (R5.13) VERIFIED. Theorem DC (a) / NC'-DC (b): the "=" is wrong (counterexample: the level
 line C(e_0 u^T + (e_1 - e_2) e_0^T): rank c = rank s = 1, no dc part, dim 1); correct with rank(s restricted to ker c); the "<=" consequences stand.
STATUS 20:27: stage2 R7 verified ((FO-r), cross family incl. b = 0, 25 cofactor formulas, pi_r(T_1(X)), R7-3 (a)); round-6 addendum appended to
 COMPUTE-ERRATA.md.
STATUS 20:33: CHANGE OF PLAN from the coordinator (work moves to the local 24-core session): round stopped at 20:30, no new computations.
 Corrected one over-statement in the addendum (Props I-ALL / II-ALL are NOT verified by me); added the last errata block (stage2 R7-1 slip,
 rows R5.3 (b), state at stop). Wrote handover/HANDOVER-verify2.md (ledger, pitfalls, errata state, ranked remaining work, scripts) and
 RESULT ROUND 6 at the top of this file. Handing back.

# ROUND 7 (start 19:43 UTC = 20:43 CET on Kevin's 24-core machine; from here on all STATUS times are UTC). Targets: (1) verifyfl R5.9
#  Props I-ALL / II-ALL; (2) reg2 hand proof 20:08 (3-dim single-row part); (3) stage3 round 7 final (Z22 + Lemma DEG, sec 26 (B'), F4b core
#  M_0); (4) audit local results C1 / R6-1 / VF-B / LEAN-1 and new RUNS.md outputs against rule 3.3; (5) new [rigorous] claims.
#  Housekeeping: the workspace copies of NOTES-verify2.md, COMPUTE-ERRATA.md were OLDER than the cloud copies (round-6 RESULT block and
#  last errata block missing) and handover/HANDOVER-verify2.md was absent: restored from coord-L-gct-210/cloud/L-gct-210 (my own files).
#  NOTE to coordinator: the workspace copies of NOTES-stage2.md (81 lines short), COMPUTE-stage2.md (34), NOTES-leanfl.md, NOTES-reg2.md,
#  NOTES-rows.md, NOTES-verifyfl.md also differ from (are older than) coord-L-gct-210/cloud/L-gct-210; I read the newer cloud copies.
STATUS 19:44: round 7 started; own files synced from the cloud copy; reading verifyfl R5.9.
STATUS 19:50 (time corrected): verifyfl R5.9 PROP I-ALL and PROP II-ALL: VERIFIED (own line-by-line re-derivation). Pressed points: (I-ALL) M != P with |M| = |P| = 3
 forces a column of P in M, a column of P in {o,o'} and a neutral column in M (all three used, all true); the t^3/t^2 coefficient extractions of
 (C4'), (C3'_i), (C3'_o), (C3'_o') redone (rho = 0 first for x = e_j - e_k with j in M cap P, then for all x); ID8 re-derived by hand (each 2-set Q
 lies in exactly two of the three pairings: -24 + 32 = 8) and checked numerically; both bracket formulas and the x-quadratic comparison redone.
 (II-ALL) Step 0 (supp m odd => not both m_i + m_j, m_k + m_l vanish); ID11 = t^2-coefficient of T_c(Y+tZ) re-derived by hand as
 sum_{pairs} <z_a z_b, s - y_a - y_b - y_c> and checked numerically for all 120 placements (err 3e-14, verify2/r7/propII_check.py); the three
 placements are complete (o neutral -> (II'); o in P -> pairs {a,b},{n,n'} = (II) or {a,n},{b,n'} = (II''); zeta<->zb is the row swap 1<->2);
 every mu^2 / mu mu' / mu'^2 coefficient system solved again; (II) m_a != m_b (the extra relation <1_3,y_a - y_b> = 0 gives eta_a = eta_b and
 kills gam even faster) and m_a = m_b (all four (C2') column equations recomputed; eta_n(eta_n - s_2) = 0; 2 eta_a(3 eta_a - 2 s_2) = 0 resp.
 3 eta_a^2 + 2 eta_a s_2 + s_2^2 = 0; T_n, T_n' of zb l^T checked numerically). No gap. => the N3 calibrations "I-ALL/II-ALL planes give unit"
 rest on a verified statement.
STATUS 19:53 (time corrected): reg2 hand proof of 20:08 = THEOREM SP8 (NOTES-reg2 5.1-5.2): VERIFIED. 5.1(a) re-derived (Laplace along row i: <w, N(J'+pi_i t)> = 0,
 so C(L_i) in Z_i^perp cap 1^perp, of dim 4 - z_i since 1 is not in Z_i); U^perp cap 1^perp = C m. Case (a): TC5 as stated in DI5.3 ("defect
 inside C(e_a - e_b) => dim <= 4", which covers defect 0 via SL); case (b): e_i' m^T lies in L_i (row i zero), defect 0 -> SL, defect C m -> SPLIT
 (dim <= 4); then 5.1(b). Two wording points (no effect on the theorem): (i) 5.1(b) "dim W_i <= 4" is the FK fact a_i >= 1 (1 not in pi_i(L),
 from R0), not part of the 3-line proof; (ii) the remark "3-dim single-row part e_i (x) {1,m}^perp in a 9-dim level space <=> L_i is (5,1)/(6,1)
 with line C m" holds only "=>" (from L_i (5,1) with line m one gets only Z_i inside {1,m}^perp). Corollary: M*_1(x,y), M*_2 and every single EC
 move contain e_3 (x) {1, e_a - e_b}^perp EXACTLY (U = 1^perp minus the moved direction e_a - e_b), so SP8(a) alone excludes them, for all
 parameters [rigorous]. The DR3 application uses the numerically observed structure of four found spaces (m "two-column up to 1e-3"): as
 rigorous as that structure, i.e. it says nothing about unfound DR3 spaces (reg2 says so in its table).
STATUS 19:57 (time corrected): stage3 round 7 final: THEOREM Z22 incl. LEMMA DEG (sec 26 (B')): VERIFIED (own re-derivation of all four steps). Checked:
 U perp U' from sigma_2 (P_2(e_d u^T + e_e u'^T) = -<u,u'>), U' = (U + C1)^perp, V_3^perp = span(1,n) in (deg-1); STEP 1 = FL2* steps (1)-(4)
 redone from scratch (la la'-coefficient 4<c,u o u'>, la-coefficient -6<u,b+c> from the 3x3 expansion 6 + 2(S - c_j - c_l)); the Lemma of (B)
 (dim U o U' >= 2) re-proved for ALL 2-dim U in 1^perp, degenerate included (|T| <= 2 because 1 is not in a coordinate 3-space); STEP 2 (binary
 quadric factorisation; isotropic sum-zero vectors have >= 3 nonzero entries); STEP 3 (B symmetric with zero diagonal, z.T = 0 in A_4 <=> Bz = 0,
 range in V_3^perp, two-valued n => n = 0); STEP 4 (c2), (c5) instances, sigma_2 = (1/2) sum q(x_r) on zero-column-sum rows, (IND): all six
 cubic coefficients of (ga X - be V)(al U - ga X)(be V - al U) recomputed, the e_2(v) = 0 step gives v_j v_l = 0 so v = c' e_l or v || u;
 (DEP): Xi_r^2 = -2Q, Xi_r^3 = 0, s(xi_r) = 0, p_a = -2p_b = 4p_a. Inputs: FL2* (verified r3) only in case (nd), L101, (CA2) with a_d = a_e = 1
 (repaired form, r1). No gap.
 F4b core example M_0: CONFIRMED independently (verify2/r7/m0_check.py): perm(J+m) - 120 = 0 as a polynomial over Z[omega] (sympy, exact);
 dim 7, dim (M_0)_r = 5 for all r, lam_ab = lam_cd = 4, other lam = 3, z = (0,0,0,0,1); rank of 60 cofactor vectors at Z[omega]-points mod
 p = 2147483629 is 17, so dim T_1(M_0) <= 8 over C RIGOROUSLY (rank mod p <= rank in char 0), = 8 numerically (gap 7.6e-2 / 2.7e-16);
 (iii) fails (coefficient 2 n_2 n_3 w_4 = 6 omega^2 at y_1y_2y_3y_4 of e_1.n.n.w). So "the core's level conditions alone do not exclude F4b" is correct.
STATUS 20:03 (time corrected): AUDIT of the local results (target 4) -- no error that changes a verdict; details:
 C1 (c1multi.py + rows/clm.py, RESULT.md 19:27): residuals are formed PER HOMOGENEOUS DEGREE (p_k(Y)_j = P_k(Y^(j)), k = 1..4, defect
  condition degree by degree -- valid: scale Y -> tY), so the sample count needed is the homogeneous quartic count C(d+3,4) = 35/70/126/210
  for d = 4..7; N = 140/160/260/420 is >= 2x in every case (my errata A5 numbers were for this code; the C(d+4,4) count would be needed only
  for an inhomogeneous residual). Coordinates in 1^perp use the Hermitian-orthonormal basis correctly (coordinate extraction, not a
  pairing). Acceptance: res < 1e-9, cond < 1e6, polish, oracle (dim = d, 4x5 level < 1e-8, lift level < 1e-8 at fresh points), target iff
  CONFIRMED with d - e >= 4 (= lift of dim >= 8): matches errata [B]. PN (neutral column 0) adds P_k(Y^(0)) = 0 for k = 1..4: correct.
  Logs (19:59): calibrations (4,1) 183/500, (5,2) 82/500, (6,3) 20/500, seeded 98/300 and 62/300, nc 118/300 and 78/300, all hits oracle-
  confirmed; targets so far: seeded (4,1)->(5,1) 0/250, unseeded (5,1) 0/250. Remark (not an error): by Lemma HYP a (5,1) space has (4,1)
  hyperplanes, but a RANDOM (4,1) seed is a hyperplane of a (5,1) space only if (5,1) spaces are plentiful, so the seeded stream is a local
  unseeded search; a negative count is evidence only, as the RESULT says.
 R6-1 (rows/gb/x4gen.py): case A stopped (output "halt 1"; claim A is false anyway, rows/sle5_s1005.npy); A4, B, B3, C still running (empty
  outputs). Rigour label: B, B3, C are AFFINE (row sums normalised to (1,0,u), (0,1,v) in Walsh coordinates) AND saturated by the column
  ideals => a unit verdict is EVIDENCE ([modular]), never [exact], whatever the number of primes; the chart argument itself is complete
  (S_4 acts on (chi_1,chi_2,chi_3) by all permutations with signs, and a 2-dim S misses at least one coordinate axis). Calibrations A4, B3
  are non-unit controls only; a unit control is missing (suggest one hand-excluded configuration, e.g. a plane of a 4-dim strongly level
  space -- Lemma SL -- or B with a forced common zero row; optional).
 VF-B: m1-m3 (generic gauge) still running, no output. The new gen.py 'chart' mode implements my exact gauge (Zs[0][j0] = 1, Z[0][j0] = 0,
  saturation by the other columns only): correct (row permutations make Zs[0][j0] != 0 once column j0 of Zs is nonzero; Z -> Z + c Zs
  preserves (2), (3) and the column sums). Verdicts after saturation remain EVIDENCE (rule 3.3).
 [DC3] cells (runs/dc3, msolve 0.6.5): piv1 cell (18 unknowns) = UNIT in 42 s (".gb" = "[1]:", the msolve format of the unit ideal --
  checked on a toy system); piv0 still running. Generator audit (verifyfl/exact/gen_n1s.py): 254 cases = rho 2: 6 Schubert cells of Gr(1,6)
  x 9 chart pairs; rho 1: 15 cells of Gr(2,6) x (9 + 3); rho 0: 20 cells of Gr(3,6) -- complete; image line cells (1,al), (0,1) complete;
  isotropic-line charts 'ab' (v_0 = 1, one quadric), 'z1'/'z2' = (0,1,w,w^2)/(0,1,w^2,w) complete for v_0 = 0 and closed under Galois
  conjugation; equations = ALL coefficients of <w, C(Y) - 24> for w in m^perp (exact identity, no sampling); NO saturation, NO Rabinowitsch
  (split mode not used). The underlying set is a closed subscheme of a Grassmannian (projective); (Nn) and (Q1) hold in odd characteristic.
  So IF piv0 is also UNIT, [DC3] for m = (1,2,-3,0,0) is a THEOREM in char 0 from this one prime (rule 3.3 / UPDATE 10; the reduction of a
  Q-bar point lies in SOME stratum mod p, and all strata are unit). Caveats: (i) the other 252 verdicts come from verifyfl's manifests
  (msolve 0.10.1, other machine) -- I have not re-run them; (ii) no independent generator yet (substitution tests pass). [DC3] at one m kills
  only types (1,3)/(0,4) = (R4) for that m; (SL_m) also needs [T22], [T31] (generators not written).
 LEAN-1: read; nothing to verify mathematically (compile + axioms reported; guard REFUSED for namespace and "add_" line starts -- mechanical).
STATUS 20:06 (time corrected): target 5 (new [rigorous]/[exact] claims) -- all VERIFIED, no error:
 verifyfl R6.2 (kind (R4): Z_0 = chi_1 l^T with all l_j != 0 is impossible): Lemma T on K = N (l not || 1/m since sum 1/m_j != 0 for non-isotropic
  m), <y_n,y_n> = 4k^2 => k = 0 => v_n, v_n' || chi_3 => rho_n rho_n' not == 0: contradiction; remaining Z_0 = v(e_a - e_b)^T or vartheta(Z_0) != 0
  (via Lemma NP + (P-b)).  R6.3 (conditional reduction to the 2-dim classification): span(Z_0,Z_1) has one active neutral column and N_P = C Z_0;
  type I plane (M contains n, so M != P) -> I-ALL gives N inside chi_1 (x) Lam_M; type II -> the proof of II-ALL gives N = N_0 in every
  placement (also in the m_a = m_b sub-case: s = 0 forces s_1 = s_2 = 0); so dim N <= 2.  [uses the props verified above]
 rows R6.1 (X4 -> planes (PL)): restriction of the bijective s and of finitely many nonzero column maps to a generic plane. VERIFIED (trivial).
  rows R6.2 formulas P_2 = -sum_i e_2(rho_i), P_3 = 2 sum_i e_3(rho_i) for column-centred h: re-derived (column sums kill the cross terms).
 reg2 R2-2(a) (FO2 bound <= dim T_1 - 1): q_0 = Hessian at J = 12 P_2 (s^2-coefficient 3! P_2), tau_r = J - 5 e_r 1^T in T_1(M) and
  P_2(tau_r) = 6*20 - 4*20*4 = -200 != 0, so the restricted form has rank >= 1. VERIFIED.
 stage3 (A5) normalisation "ONE vector p": own argument -- in F4b, (c5) gives m_ac, m_ad, m_bc, m_bd >= 1 and lam_bd = 3; e_e w^T, x^{ae},
  x^{ce}, t = e_a u^T + e_c v^T all lie in X_bd (dim 3), so t = al e_e w^T + be x^{ae} + ga x^{ce} with be, ga != 0 (else a single-row element in
  row a or c, z = (1,0,0,0,0)), hence p_a in span(w, p_c) and x^{ae} can be rescaled / shifted by e_e w^T to p_a = p_c; m_re = 2 exactly ((A1),
  (c5) with l chosen in {a,b}); <y_r,w> = 0 from sigma_2. (A5') level identities of N: coefficient bookkeeping redone (non-squarefree
  monomials c_r c_T only from the second sum => eps(Y_T P) = 0, then eps(Y_T) = 0 for |T| >= 2, eps(Y_r) = -eps(P)). (i)-(iii) from (CA2) on
  L_e, L_a..L_d: re-derived, incl. the independence of the c-monomials modulo (sum c) in every (ga,de)-block. Free-column gauge: ka = -2 s(q_a),
  <q_a,q_b> = -s(q_a)^2, <q_a + q_b,p'> = 0, s(q_a) = 0 recomputed from the three sigma_2's.
 stage3 THEOREM FC [exact]: VERIFIED and REPRODUCED here: stage3/gb/fc_exact.py run from verify2/r7 (Singular 4.3.2 std over Q):
  IDENT23 UNIT 81/81 charts (23 s), FULL UNIT 81/81 (24 s). Generator audited line by line (rows of J + m, w_1 = 0, p_1 = -1, hinges
  t_b q_b[i] = 1, t_d q_d[i] = 1, gauge p'_{iw} = 0, charts q_a[0] = 1 by S_4 on N, q_c[i] = 1, w[i] = 1: 81 = 3^4, complete) and
  substitution-tested by me (verify2/r7/fc_subst.py, mod p with omega): M_0 satisfies all 126 LEVEL polynomials of chart 00000 and
  violates 6 of the 142 IDENT23 ones; a random point violates 126/126. Over Q a Rabinowitsch chart is legitimate (no reduction step).
 stage3 round 8 (B) (parallel y_r => free-column type): VERIFIED (s != 0: la_r equal, e_2 = e_3 = e_4 = 0, Y^4 = 0 => two zeros => y = s e_j;
  s = 0: all e_k = 0 => y = 0). => F4b is left exactly with y_a..y_d NOT all parallel (stage3's statement is correct).
STATUS 20:10 (time corrected): further items. stage3 sec 26 (C5) (r5), (C6): VERIFIED by hand (one floor down from 5.1(a): for t in X_re, z in Z,
 <z, N(t)> = 0 with N the deletion vector of the 4x5 matrix [row r = 1; J_3 + t'], sum N = perm(J+t) = 120, so the defect lies in
 (Z + C1)^perp = U'; e_3 >= 1 by SL_3 since lam_re >= 3; column sums of L_e lie in U' from the degree-1 la-coefficient -6<z,c>); (C7) is an
 explanatory remark, (C8) trivial. stage2 R7-4 (z = 3 reductions): VERIFIED (= SP8(b) + 5.1(a) + TC5 + HYP).
 stage2 R8-3 LEMMA B0-1 (Pi(x_0) = 0): TRUE, but the stated reason has a SLIP: Pi(M)_ij = perm_3(...) is CUBIC in M, not quadratic; the
 correct one-liner is the lam^3-coefficient of y^T Pi(alpha(w) + beta(y) + lam x_0) w = 0 (the c = 0 part of c perm_4(M) + y^T Pi(M) w = 120 c^5),
 which is y^T Pi(x_0) w. Conclusion unchanged. R8-2 (0)-(3): not checked (partial family analysis, not on the route).
 reg2 8.2 NC-FAM: the five parameter charts (1,1,1), (1,1,2), (1,2,1), (1,2,2), (1,2,3) are a complete cover up to S_4 (S_4 puts a_1 = 1, the
 stabiliser S_3 of column 1 reduces b to index 1 or 2, the remaining stabiliser reduces c); the Omega- and E_0-test systems themselves were
 NOT audited (gen_nc.py not read). 8.3 DR22: not audited.
 [DC3] reproduction (verify2/r7/dc3rep, gen_n1s.py at p = 2147483629, msolve 0.6.5, 20 s per case): running in the background.
STATUS 20:18: [DC3] m = (1,2,-3,0,0): (a) 252 easy cases REPRODUCED UNIT here (verify2/r7/dc3rep manifest; the two hard cells timed out at 20 s
 as expected). (b) INDEPENDENT EQUATION CHECK (verify2/r7/dc3_indep_eqs.py: gen_n1s's cell parametrisation, but my own polynomial
 arithmetic, my own 4x4 permanent, my own basis {(2,-1,0,0,0),(3,0,1,0,0),e_3,e_4} of m^perp, my own x-coefficient extraction, plus the chart
 quadrics): the F_p-span of my equations EQUALS that of gen_n1s in ALL 254/254 cases (incl. piv0: rank 77 = 77 = union). So the only shared
 ingredient left is the parametrisation, which I audited by reading (complete cover). (c) decisive cell piv0 (3,2,(0,),0,ab,ab): split A
 (plain + vartheta(Z_0) = 0) UNIT in 196 s; gen_n1s split B (Theta-normalised, 22 unknowns) died after 262 s (msolve ERROR, presumably the
 2.5 GB cap); now running split B' = plain + u*<z_0,z_0> = 1 (20 unknowns; A and B' cover the plain cell over F_p-bar). Controls for the
 split mode: k = 2 type I cell (2,1,(0,),0,ab,z1) split A NON-unit (86 elements); piv1 split A UNIT 0.4 s, split B UNIT 5.1 s.
 The coordinator's unsplit piv0 run (runs/dc3, msolve -t 6, since 19:42) is still running; either route closes the cell.
STATUS 20:20: verifyfl round 7 (this machine) R7.1 LEMMA RED-p, R7.2 SUBSYSTEM CUT, R7.3 THEOREM DC3 audited. R7.1 = my reduction argument
 (X_k closed in Gr over Z (Z[w]), proper; every F_pbar point lies in some case system of gen_n1s because (F2_p) holds for p > 3: degree-2 part
 of C_j on doubly centred Y is Q - 2<y_j,y_j> (re-derived), 3Q = 0, neutral columns isotropic, V nondegenerate mod p); open conditions only in
 the char-p case split: correct. For m in Z[w]^5 reduce at the prime above p where w is the run's cube root: correct. R7.2 correct
 (coefficients of x-monomials supported on S = equations of R_i(sum_{r in S} x_r B_r), so their GB lies in the cell ideal); verifyfl/r7/
 cut_cell.py read: S1/S2 selection by x-monomials, renaming S1 -> S2 checked as sets up to scalars, FULL asserted == gen_n1s.build(case),
 renamed GB strings substituted in one regex pass: no error. So piv0 is UNIT by the cut (verifyfl) AND by split A (mine, UNIT) + split B'
 (mine, pending). R7.3 for m = (1,2,-3,0,0): VERIFIED as a characteristic-0 theorem modulo msolve (cover audited, equations re-derived
 independently 254/254, easy cases reproduced, hard cells closed two ways). For m11m2 and iso my independent equation check is running.
STATUS 20:21: independent equation check extended (verify2/r7/dc3_indep_eqs_m.py, my bases of m^perp incl. (w,-1,0,0,0), (w^2,0,-1,0,0) for
 iso): SAME F_p-span as gen_n1s in 254/254 cases for m11m2 and 254/254 for iso as well. => THEOREM DC3 (verifyfl R7.3) for all three m rests
 on: the audited parametrisation, msolve, and (for the hard cells) verifyfl's cut, which I audited. Proactive audit of the NEW generators for
 (SL_m): gen_n3 [T22] (N by the 96 gen_n1s k = 2 cases = 9 + 72 + 15; S by the 3 cells of Gr(2,3); Y_r = s_r e_0^T + D(c_r) general; gauge
 matrix [ell_i(Z_j)] triangular with det 1 (pivot coordinate / column-3,4 entry at the chart row where v = 1); Gram equation = (B-ii') /
 (F4_p)) and gen_n2 [T31] ((F3_p): Zs in dcsub(P); 6 echelon cells; Y_r unique mod Zs for s = b_1, b_2 (b_3), gauge at the pivot D-coordinate;
 stage a (R = 2) suffices since every type-(3,1) K contains such a 3-dim space): both covers COMPLETE; with [DC3] they exhaust the types
 (3,1), (2,2), (1,3), (0,4) of a 4-dim K, so "all [DC3], [T22], [T31] cases UNIT at one p > 3" => (SL_m) in char 0 (R7.1). Equation code
 shared with gen_n1s (exactlib.equations), which my independent check covers for the [DC3] matrices only.
STATUS 20:28: split B' of piv0 also died (ERROR at 452 s, 2.5 GB cap); queued as OPTIONAL (QUEUE.md "DC3-piv0-SPLITB"); piv0 is closed by
 verifyfl's audited cut anyway. Independent equation check for the (SL_m) generators (verify2/r7/sl_indep_eqs.py): [T31] stage a: SAME span
 in 6/6 cells; [T22]: case 0 scell 0 SAME span (7 non-defect extras: gauge, Gram, quadrics); more [T22] systems and [T31] stage b running
 (about 3 min per system). Errata: symbolic-m caution added (the P^1-family is non-unit at the two-column values; elimination must be
 done over Q).
STATUS 20:29: verifyfl's running chains (read-only look): [T22] m12m3 n3_chain: 84 verdicts so far, all UNIT; [T31] n2_chain CRASHED with
 "ValueError: substring not found" in subcut.py (empty msolve output, most likely msolve killed by the 2.5 GB cap): NO [T31] verdict yet.
 Fail-safe checked: exactlib.run_msolve returns UNIT only with a "length of basis" header and body exactly "[1]:" (else ERROR/NONUNIT), and
 subcut.py raises on an empty file, so a crashed msolve can never be counted as UNIT. Suggest: run the [T31] chain under a larger memory
 cap via QUEUE.md.
STATUS 20:31: [T31] stage b independent equations: SAME span 6/6. Round 7 ends here (RESULT ROUND 7 at the top is final; ledger rows in
 handover/HANDOVER-verify2.md updated; errata round-7 addendum written). Still running (mine, 1 core, self-terminating ~20:52 UTC): the [T22]
 independent-equation sample (verify2/logs/t22_indep_eqs.log). Queued (optional): QUEUE.md "DC3-piv0-SPLITB". Handing back.

# ROUND 8 (start 20:35 UTC). Coordinator targets: (1) stage3 Theorem F4b-X (sec 28); (2) rows X5 (R7.3) + DC/NC'-DC repair (R7.2); (3) stage2 R9
#  (B(ind), D1, D0-3, D00); (4) reg2 REG2-T1 (sec 9) + 8.2/8.3 test systems; (5) audit [T22]/[T31]/DC3-P45/DC3X verdicts; (6) symbolic-m
#  elimination spec over Q; (7) open ledger rows.
STATUS 20:35: round 8 started; reading NOTES-stage3 sec 28 (F4b-X).
STATUS 20:42: stage3 THEOREM F4b-X (sec 28), hand part VERIFIED: (M1) generating function and the level conditions as Pi = 1 + s sum t_r,
 Pi_u = Pi + s(u) t_u (re-derived; equivalent to the closed form of (A5') verified in r7); (M2) both pointwise formulas re-derived from
 (1+x)^{-1}, (1+x)^{-2} mod squares (24 e_4 - 6 s e_3 = 0; 24 u_k pi_T - 6 s(u) pi_T - 6 s u_k e_2(v_k|T) = 0) and their membership in (i)-(iii);
 (M3) s != 0: log Pi = 0 => all moments vanish; dim U = 1 (y = 0 by (Y4)), U nondegenerate (no four pairwise orthogonal spanning vectors),
 rank 1 (three multiples of n, p_1 = p_2 = p_3 = 0 => >= 4 nonzero entries, fourth y = 0), totally isotropic (V = U + C1, span(w,p) = U,
 zero sets = parallel classes: (4) contradicts dim U = 2, (3,1)/(2,1,1) kill a y, (2,2) gives disjoint isotropic sum-zero z_1, z_2, (1^4) no
 zero set at all): all correct. (M4) thin/fat dichotomy and fat types re-derived by hand (v = (3/4)1 violates (Y4); 3 nonzero impossible;
 p_k = -1 resp. 0); COMPLETENESS checked by an EXACT enumeration of all fat configurations with f <= 3 (verify2/r8/f4b_classify.py, sympy GB
 with nonzero conditions): survivors are exactly f = 1 'O' with tau = 0 (= C1) and f = 3 'O + D + D on the same row pair'; in the latter the
 Pi_w identity sum_j w_j pi_{r}(v_j) = 0 forces both thin columns into ONE row with equal values (tau supported in one row) => C3 exactly;
 r1 in {b,c} by the dihedral symmetry (ordered within-pair and cross-pair choices are single orbits). C1 sub-cases (<= 2 nonzero u_r; two
 nonzero => 2 columns each and p' in C w) re-derived; C1G + C12ab + C12ac + C3b + C3c cover everything. (M5) generator gen9.py audited
 (normal forms, gauge g_a0 = g_c0 = 0, charts, nd minors = "g_b not in C y_b" which I re-derived from (A1) and dim M = 7, (i)-(iii) rows,
 stratified charts) and substitution-tested by me (M_0 in C1G chart 01111: LEVEL 0/180 nonzero, FULL 12 nonzero). Exact reproduction over Q
 of all five eliminations running (verify2/logs/f4b_chain{A,B}.log).
STATUS 20:49: (1) F4b-X EXACT PART REPRODUCED over Q with my own driver (verify2/r8/f4b_repro.py; Singular std, scripts in verify2/r8/sing):
 C3b LEVEL 16/16 UNIT, C12ab LEVEL 16/16, C3c FULL+nd 256/256, C12ac FULL+nd 256/256, C1G FULL+nd 192/192 (chart 11113 via its stratified
 system, legitimate: stratum inside chart, strata cover). => THEOREM F4b-X VERIFIED (hand part + exact part); with F1/F3/F4a (sec 26 (A3),
 (A4), verified r5): z = (1,0,0,0,0) IMPOSSIBLE in the regime (9-dim, all a_r = 1, all lam >= 3).
 (2) rows R7.2 (DC' / NC'-DC' exact identities, corrected chain): VERIFIED (rank-nullity twice; c(Y) in C since the degree-1 defect is -6c with
 S = 0; s3' >= s3; C-UP + hyperplane lemma; "generic hyperplane non-principal" via SL). rows R7.3 THEOREM X5: hand part (1) (A_c = P_v,
 B_a v = v via w = g - v isotropic and B_a(v^perp) in {v,w}^perp, R a rotation != +-1) and (2) (m_c phi = 0, (m_a - m_b)Rp = (m_a + m_b)p, all
 sub-cases incl. VF-A+PR3 / TC5 for m_a = m_b = 0, normal form with t = m_a(lam-1)eta = m_b(lam+1)eta) VERIFIED; x5gen.py audited; INDEPENDENT
 generator (verify2/r8/x5_indep.py: isotropic-line charts 'ab'/'z' (w^2+w+1 = 0), v from linear conditions with chart v_k = 1, <n,n'> != 0 by
 Rabinowitsch over Q, own Laplace permanent): UNIT over Q in 12/12 charts; line calibration NON-unit (first chart dim 2; rest running).
 rows R7.4 THEOREM PR5: hand part VERIFIED ((i) -2 m_a f = 0; (ii) B_b = -B_a, lam' = +-1 on P (non-isotropic vectors), degenerate P => B = +-1
 on V (re-proved: Bz = eps z + c u, c<z,u> = 0), nondegenerate => reflection => type (2,1), m_a = 0, f in X_a, Z = a m^T; (iii) (1,1,1) splits
 along orthogonal lines). INDEPENDENT generator (verify2/r8/pr5_indep.py: A_N in the 6 Schubert cells of Gr(2,4), type (2,1) via the rescaled
 projector (<x,x> sigma - <x,sigma> x, <x,sigma> x), x in charts x_k = 1, u<x,x> = 1): type (3) UNIT 6/6, type (2,1) UNIT 18/18 over Q;
 line calibrations NON-unit (type 3: 4/4 cells dim 2; type (2,1): 9/12 charts dim 3). => X5 and PR5 VERIFIED (two independent generators each).
STATUS 20:51: stage2 R9 (partial, by priority): LEMMA PROP (R9-5) VERIFIED (C_1j - C_2j = (rho-1) s_1 gam_j in D(X) => s gam_j, C_0j in D(X)).
 LEMMA N0-W (R9-3) VERIFIED (cubic parts of C_0m, C_1j, C_2j are s gq_m, s_2 gq_j, s_1 gq_j; eps-coefficient at xi_0 + eps eta gives
 sig(2A + B) = 0 on W; the quadratic part on W is 2A + 2B (h_m, C_3j, C_4j affine on W since p_0 = q_0 = s = 0; C_i0 = 2gam has quadratic
 part ab - <p',q'> = 0); so A = gq_m|W = 2 p_m q_m = 0). B-IND (R9-1): (a) structure (ker = C xi_d; Y totally isotropic for the form built
 from K = J - I, nondegenerate, so dim Y = 4) VERIFIED; (c) = N0-W with W = lift of Y_00 VERIFIED; (d) pattern split (S, T disjoint; |S| = 1
 impossible) and the M-pattern isotropy equations ga(4al - 1) = 0, be(4de - 1) = 0, 1 - al - de + 4(al de + be ga) = 0 and their two
 components re-derived exactly; Q0/P0 sub-derivations and [CRIT] (b) NOT re-derived; exact runs (e) not reproduced. Numerical cross-check
 with MY OWN T_1 code (verify2/r8/bind_num.py): 6 random FM members (both components) are level (1e-13) and have dim Omega = 2 < 5,
 consistent with B-IND. B(dep) D1, D0-3, D00 (R9-2/R9-6/R9-8): not checked this round. stage2's counterexample to the structural target
 (R9-4, a PROP space with FO2 bound 9 killed only by (T2)) noted, not re-checked.
STATUS 20:52: reg2 sec 9 (REG2-T1, pattern (2,1,1|2)): hand parts VERIFIED -- 9.1 case (i) empty (b, c in the line U_0'^perp cap H, b isotropic,
 P_3 = 2 y3 y4 (y1 <a', b o b> + y2 sum b^3) via e(u,b,c) with S = 0, Newton => b ~ chi_1, b^perp cap H = span(chi_1, chi_2), <a',chi_2> = 0
 => a' in C b); 9.2 case (iii) (h = beta r, P_3 = 2 beta y3 y4 <u', r o r>, r o r never in span(1, r) => beta = 0); 9.3 case (ii) (V forced,
 U_0 = span(5e_0 - 1, (0,a)), a = cross4(b,c) resp. cross4(b, b o b), (5e_0 - 1) perp (0, b o b) since <b,b> = 0). 9.4/9.6 exact runs: the chart
 cover (b_1 = 1 by S_4, c_1 or c_2 = 1 by the residual S_3, a_ja != 0 by Rabinowitsch over Q) is complete; the Omega-/E_0-test systems were
 NOT reproduced (time). 8.2/8.3 test systems: still not audited.
 Target 5 (verdicts): VF-DC3-P45 (gen_dc.py = gen_n1s generalised; same cover structure: image cell of Gr(rho,|Nt|) x N_P cells of dcsub(P)
 x line charts; for |supp m| = 5 it is the unstructured Gr(3,12) cover): first manifests only TIMEOUT/ERROR (memory) + 3 UNIT -- no verdict
 yet. VF-DC3X: 192+ UNIT, 2 cells ERROR (memory), rerun deferred -- consistent with DC3 (already verified). VF-T22H running. No new
 [T31] verdict. Independent X5 line calibrations: see next line.
STATUS 20:53: SPEC SYM-M (target 6; for verifyfl / the coordinator; not run by me).  Goal: [DC3] (then [T22], [T31]) for ALL m with |supp m| = 3,
 not only three sample m.
 (1) Parameter: m = (1, t, -1-t, 0, 0) (chart m_a = 1; covers every |supp m| = 3 line except m ~ (0,1,-1,0,0), a two-column point handled by
     TC5). Basis of m^perp polynomial in t and of rank 4 for EVERY t: e_3, e_4, (t,-1,0,0,0), (1+t,0,1,0,0). Special values: t = 0, -1 (two-
     column), t^2 + t + 1 = 0 (isotropic m; already THEOREM DC3 for iso), and repeated entries t = 1, t = -2, t = -1/2 (not special for [DC3],
     but they are the (R2) stratum for [T31]; keep them inside the family).
 (2) System per cell: gen_n1s cell unknowns + t; equations = all x-coefficients of R_i(sum_r x_r B_r) with the t-dependent W above, plus the
     chart quadrics (and the subsystem cut for the generic rank-2 cells). NO saturation.
 (3) Verdict: compute the ELIMINATION ideal I_cell cap Q[t] OVER Q (Singular eliminate / std with an elimination ordering, characteristic 0;
     not modStd unless its verification step is enabled). The set of m admitting a 3-dim doubly centred space with defect in C m is contained
     in the union of the zero sets V(I_cell cap Q[t]) (containment needs no properness). DECISION: if every elimination ideal is (1) or has all
     its roots among the special values, then [DC3] holds for every non-special |supp m| = 3 line (char-0 proof). A root outside the
     special set is a CANDIDATE m: extract it and run the single-m pipeline (THEOREM DC3 style) there.
 (4) Mod-p eliminations are EVIDENCE only (COMPUTE-ERRATA round 7): a char-0 solution with non-special algebraic t can reduce mod P onto a
     special value. If Q is too slow: run mod >= 3 primes first to locate the candidate roots, then certify over Q only the polynomial
     identities needed (e.g. a Q-polynomial f(t) in I_cell with special roots, verified by an explicit Q-linear combination / lift).
 (5) Calibrations: k = 2 cells containing the type V planes (exist for every non-isotropic m, NOTES-verifyfl R5.3) must give elimination
     ideal (0); SL (m-free) must stay unit; the two-column point must reappear as a root in [T22] (K_2).
 (6) Cost: one more variable than the single-m runs; the generic rank-2 cells were hard already (cut needed). Same scheme for [T22]/[T31];
     |supp m| = 4, 5 need 2 resp. 3 parameters (a P^2 / P^3 family) and should wait.
STATUS 20:59: (T2) (stage2 R6-7) RE-DERIVED: with a_r = 1, Laplace along row r + R0 give <v, G(T(v)+xi)> = 120 <kappa^r,v>^5 on L^; the
 v-degree-1 part gives G == 0 on L_r, the v-degree-2 part gives D_{T_k} G_j + D_{T_j} G_k == 0 (symmetrised), J in L^ gives T(1) = J' mod L_r;
 the test is independent of the section T because D_S G == 0 on L_r for S with values in L_r. Correct as a NECESSARY condition.
 stage2/r6_T2.py AUDITED: DG = perm_3 minors (correct), equation rows (k gets D[j], j gets D[k]; j = k doubled) correct, bilinear null space
 vh[r:].conj() correct (no conjugation error), J'-test by lstsq correct. SAMPLING: 30 points < 35 cubic monomials in the 5 coordinates of xi
 -> the sampled system is UNDER-determined, so the computed solution space can only be TOO LARGE: a "(T2) not solvable" verdict is robust
 (conservative), a "(T2) solvable" verdict is NOT reliable (could be spurious) -- e.g. (S1), (S2) "(T2) solvable" in R9-4 should be re-run
 with >= 70 points or exactly. Tolerance 1e-9*s[0] is the only risk for kills (a true null direction discarded) -- not realised for (S3):
 EXACT TEST (verify2/r8/t2_exact.py, Fractions, all cubic coefficients): X(S3) is exactly level, G == 0, and the (T2) system is INCONSISTENT
 for sg = 0, 1, 2, -3, 1/3 (rank 36 vs 37). SYMBOLIC (verify2/r8/t2_symbolic.py, sympy over Q(sg)): generic ranks 36 / 37 and a left null
 vector y with denominators only 2^k sg, y^T A == 0 identically and y.b = -1/sg; so y' = sg*y is a POLYNOMIAL certificate (y'^T A == 0,
 y'.b = -1) => (T2) FAILS for EVERY sg. => survivor (S3) is DEAD exactly (rigorous, for all sg); stage2's statement "(S3) dies only by (T2)"
 is confirmed in the strong form. (Its FO2 bound 9 is numerical and was not re-checked; irrelevant now.)
STATUS 21:00: rows R8.1 THEOREM T3 / LEMMA O3 VERIFIED (own re-derivation): V = sl_2 with tr(xy)/2, O(V) = +-Ad(SL_2); Phi(x) = x + c tr(x) 1,
 c = (s-1)/2; Choi(Phi) = Omega Omega^T + c I_4 has rank <= 3 (three terms (1 (x) g_j) Omega ((1 (x) g_j^{-T}) Omega)^T) and det = c^3 (c+2), so
 s in {1,-3} and det-product -1; s = -3: image Omega^perp = span(u_j), Omega^T u_j = tr g_j = 0, g_j^2 = -1, -Ad(g_j) reflections; s = 1: T = 1 (x) 1,
 g^{-1} = tr(g) 1 - g, symmetric => (sum eps t g - 1) = lambda 1, polarised det => lambda = 1, g_a(x)g_a + g_b(x)g_b = 1(x)1 + g_c(x)g_c; g_c scalar =>
 g_a = +-1; else (g_a,g_b) = (1,g_c)N, N in O(2), det = 1 gives C S t_c = 0 => B_a or B_b = 1, or B_c a reflection. Application via
 B_a + B_b + B_c = 1 (B_d = B_e = 1, rows' convention B = 1 - 2A) correct. => with PR5 + X5 (verified above): every principal (5,1) kernel
 lives on >= 4 columns; "no principal (5,1)" <= (PL) alone [rigorous reduction]. (PL) itself = R6-1 B/C or R7-X4K: open (computations).
STATUS 21:03: stage2 R9-4 survivors, exact: (S1) and (S2) are exactly level and EXACTLY (T2)-solvable (verify2/r8/t2_exact_S12.py; so the
 sampled verdicts happened to be right); (S1) EXACT FO2 bound 8 (verify2/r8/fo2_exact_S1.py: T' from 40 integer points (contains T_1),
 dim 12, rank of q_{m0} on T' = 7 over Q, Lemma FO2 is valid on any T' containing L) => (S1) is RIGOROUSLY not the L_r of a 9-dim level
 space. (S2) has a 3-dim single-row part (the z = 3 / (5,1) branch), as stage2 says. With (S3) dead exactly by (T2): all three R9-4
 survivors are now settled (S1, S3 rigorously dead; S2 inside the z = 3 branch).
STATUS 21:04: stage2 R9-2 B(dep) geometry VERIFIED (D-lam: p_0 = -lam q_0 - (1+lam)^2 a, s = (lam-1)q_0 + lam(1+lam)a; h = (1', -lam 1') with
 B(h,h) = -24 lam, so dim Y = 3 and the 2-dim kernel {(s_1,s_2,-lam c,c)} lies in X for lam != 0; H_0 degenerate with radical (1',0); D00 in the
 nondegenerate 1^perp x 1^perp, dim Y in {2,3}; D1: Q0/P0 violate rank <= 2 of (iii) through the a-direction; D1M parametrisation and
 isotropy lam(1-al) = ga(1-4al) re-derived). Exact verdicts (direct tool r9_direct.py over Q) NOT reproduced; numerical cross-check with
 my own T_1 code (verify2/r8/d1m_num.py): 6 random D1M members level (1e-13), dim Omega = 2 < 5, consistent. N1 (R9-8), D0-4, D00-3 not
 checked this round.
STATUS 21:04: RESULT ROUND 8 written at the top; ledger updated; no jobs of mine running. Handing back.

# ROUND 9 (start 21:05 UTC). Targets: (1) stage2 N1 (R9-8), D0-4 (R9-4), D00-3 (R9-6) + reproduction of their exact runs; (2) rows CHI1 (R8.2) +
#  non-principal (5,1); (3) reg2 9.4/9.6, 8.2/8.3, sec 11 test systems (sample, own generator); (4) verdict audits; (5) rows R5.1/4/5/8/10.
STATUS 21:05: round 9 started; reading NOTES-stage2 R9-4, R9-6, R9-8.
STATUS 21:11: TARGET 1 (stage2 N1 / D0-4 / D00-3). LEMMA N1 (R9-8) VERIFIED: on X_s, s = q_0 = 0, p_0 = -a; quadratic parts C_0m -> 2(2p_m q_m
 - a q_m) + 2a q_m = 4 p_m q_m, C_1j, C_2j -> 4 p_j q_j, C_3j, C_4j, C_i0 affine (ab - <p',q'> = 0) => (B); eps-coefficient of the cubic part
 (eta with s_1 = s_2 != 0 exists for non-PROP) => 2 g_m + sum T_j g_j = 0, with (B) => (A). Direct tool (stage2/r9_direct.py) audited: for each
 m in {1,2,3} unknowns t_ij (20) with C_0m + sum t_ij C_ij == 0 on X (all z-coefficients), level check included; Omega always contains e_0, 1, so
 v = e_1,e_2,e_3 decides Omega = C^5. D00-3 family cover audited (K2 over the 3 Schubert cells of Gr(2,3); V-chart made complete by the
 S_4-equivariance of the family; y3 = e34 never in a chart V; W/y3 as the two isotropic extensions). Eliminations = closures of projections:
 exclusion only (stage2's caveat is correct). REPRODUCED here (their scripts, Singular over Q): D003 Q0_A_3 -> (u1), P0_A_3 -> (u1), Q0_B_2 ->
 <1>, M_A_1 -> <1>, level checks 1 (log verify2/logs/st2_d003_rerun.log). INDEPENDENT numerical cross-check with my own T_1/Omega code
 (verify2/r8/d003_num.py, d04_num.py; members rebuilt from the definitions, level 1e-13): D00-3 -- all ten 'closed' families dim Omega <= 4 at
 random points AND at u1 = 0; Q0_A_3, P0_A_3: dim Omega = 5 exactly at u1 = 0 (their locus); M_A_3 at u1 = 0, k2 random: 4 (locus needs k2 = 1).
 D0-4 -- M_A_i: 5 at (f0,f3) = (2,2) and (0,0), 4 at random; M_B_i, M_A_ii, M_B_ii: 5 only at (0,0); P0_A_i: 5 at (0,0) and (2,0) (f3 = 0,
 f0 in {0,2}); Q0_B_i/ii: 2 at random and on F0 = 0 (even stronger than N1's conclusion). All consistent with R9-4, R9-6, R9-8.
 Still running / killed at the coordinator (no verdict): D003 Q0_B_3, P0_B_3; D04 Q0_B_i/ii, P0_B_ii elims (killed, memory) -- N1 handles
 Q0_B by hand. HIGH-STAKES NOTE: stage2 R10-3 (decisive test: a 5-dim X admits (T,kappa) with (**) <=> a 9-dim level space with L_r = X, a_r = 1)
 RE-DERIVED: correct ((b) => (a): J in L^ gives <kappa,1>^5 = 1, L = L^ cap ker ell is level of dim 9). The two R10-2 candidates
 cand_D003P_l1m1 (D003-PROP, l = (1,-1), A = C(1,-1,0,0)) and cand_D04P_a11m1m1 (D04-PROP, alpha = (1,1,-1,-1)) are EXACTLY level, G == 0,
 and EXACTLY (T2)-solvable (verify2/r8/t2_exact_cand.py; D04P at sg = 0, 1, 2, 3/10; D003P also for l = (1,0) with that A): they are genuine
 candidates up to second order; only (T3)-(T5) can decide them. stage2's D = 9 (and D = 8 for D003P) extension LM: residual floors 0.8-1.9.
STATUS 21:13: TARGET 2: rows R8.2 THEOREM CHI1: VERIFIED (exact part), hand part GAP REPAIRED. Exact: chigen.py audited (gauge Z[0][a] = 0 on M via
 chi_0 = 1; c(Z) = m; all (w,t)-coefficients of defect_j - m_j defect_K0; ii^2 = -1; sum m = 0; two charts m_0 = 1 / m_3 = 1 cover m != 0 by the
 symmetry of M and {d,e}); re-run over Q: chart 0 UNIT, chart 3 dim 0 non-unit, calibration (m = e_3 - e_4 imposed) non-unit, saturation by the
 other m's unit (log verify2/logs/chi1_rerun.log); MY OWN elimination of the z's in chart 3 (verify2/r8/chi3_elim.sing): minimal associated
 primes = {(m0, m1, m2, m4 + 1, ii^2 + 1)} only, i.e. m = e_3 - e_4 exactly, as stated. HAND PART slip: p_2(Y)_j = c_j^2 + s.y_j - |y_j|^2 +
 kappa(Y) with a j-INDEPENDENT kappa(Y) = (Q - Q_c - |s|^2)/2 (C = 0), whose polarisation kappa' = <w,alpha> - W beta is NOT zero; so the vector
 in C m is v(w) + kappa'(w) 1, not v(w) (the text's "v(w) lies in C m" is only "in C m + C 1", and the "differences supported on {a,b}" step
 fails for m with three equal entries off {a,b}). REPAIR (mine): with w = e_a, the j = a component gives lam_a m_a = 0; m_a != 0 on M =>
 alpha_j + alpha_a = beta for all j != a => alpha = 0; one zero of m on M => alpha = x 1 and beta = 5x = 2x => alpha = 0; two zeros on M => beta = 2 alpha_3
 and alpha = alpha_3 1 => alpha = 0; three zeros = two-column m (excluded). So the conclusion <chi, z_j> = 0 for all j stands. (The theorem
 itself rests on the exact part anyway.) R8.3 (non-principal (5,1) state): consistent with R7.2 and verifyfl's typed systems; no new claim.
STATUS 21:16: TARGET 3 (reg2 test systems, sample with MY OWN generator, exact over Q): verify2/r8/reg2_sample.py builds rational members from
 the stated definitions, checks level exactly at 12 random points, computes T' = annihilator of the cofactors at 30 integer points (T'
 contains T_1, so dim T' is a rigorous upper bound for that member) and dim Omega'. Results (all members level): 11.2 (2,1|3) three u: (9, 2);
 11.1a (3|2,1) p = 2, -3, 5: (9, 2); 11.3 b-i p = 2, -3: (9, 2); 11.4 V0 s = 2, -5: (9, 2); 11.5 A1 s = 2, -5: (9, 2); 8.2 NC member: (9, 2);
 8.3 DR22 mu = (0,1,2,5), (0,1,3,-2): (9, 2); special loci 9.4-D and DR22 mu = (0,1,0,1), (0,1,1,1): (10, 3) with EXACT rank q = 4 =>
 FO2 bound 8 (verify2/r8/reg2_fo2_special.py). All exactly as reg2 states. reg2's greedy-minor method (sec 11) re-derived: 16x16 minors
 of the FO matrix over Q[params] generating (1) => rank >= 16 everywhere => dim T_1 <= 9 for every member; sound. Hand case splits of
 sec 11 read, not re-derived line by line this round. OWN BUG (fixed, recorded for honesty): my first run of reg2_sample.py used a
 null-space routine that silently switched to FLOATS for integer input (x/pv), which made one member (V0, s = -5, entries 1/6) look
 non-level; a direct sympy check showed V0 is level for ALL s (symbolic), the routine now converts to Fractions, and the re-run is exact.
 (My other exact scripts feed Fractions throughout and are unaffected.)
STATUS 21:18: TARGET 4 (verdicts): nothing decisive -- R7-X4K (k3/k4/k5) still in Singular, t3 killed (memory; T3 is now proved by hand anyway);
 VF-T22H on m12m3 case 9; VF-DC3-P45-CUT: p4a cell 1 UNIT, cell 2 TIMEOUT, others pending; R8-B3cal (fibre-fixed + 4 slices): NONUNIT
 (183 elements) as a calibration must be -- slices are legitimate ONLY for calibrations, as rows states.
 TARGET 5 (open rows rows): R5.1 VERIFIED (Laplace along row r: perm(J - E + [[q,x],[w_0,0]]) = 5*24 + (1+x)^T Adj(q) w_0; level + W_0 perp C(L')
 <=> (1+x)^T Adj(q) w = 24 (1.w) on C1 + W_0; untwisted case => (TRI) by linearity on the affine space 1 + X; dim count dim L = dim Q + dim Xh
 + dim Wh - 1, so (NC') <=> dim Q + dim Xh + dim Wh <= 8). R5.10 VERIFIED (row sums sum m_j A_j f = 0; A_b = lam A_a on P with lam != 0, 1;
 isometry identities give (lam - lam^2)<A_a p, A_a p'> = 0 => A_a(P) totally isotropic => p_0 with A_a p_0 = A_b p_0 = 0, A_c p_0 = p_0: single-column
 element in the neutral column; z_c = 0 on N; Z_* has isotropic columns). R5.4, R5.5, R5.8: numerical census statements (not rerun; they
 are superseded as tools by PR5 + T3 for the principal kernels).
STATUS 21:25: *** stage2's R10-2 PROP CANDIDATES DO NOT EXTEND -- not even to dimension 8 (rigorous, char 0 via one prime). ***
 Method (verify2/r8/ext_T1.py, ext_q.py, ext_full_cell.py): every level L containing X lies in T' (annihilator of the cofactors at 40
 integer points; T' contains T_1(X)); write L = X + span(y_1..y_k), y in span(U) (integral complement of X in T'); the lam^2-part of
 perm(J + x + sum lam_i y_i) - 120 gives q_x(y_i,y_j) = 0 for ALL x in X (Hessian at every base point; all x-coefficients, degree <= 3 in x,
 quadratic in the cell coordinates). Schubert cells of Gr(k, 8 or 9) cover the Grassmannian; no saturation, no open condition; the
 incidence variety is closed in a Grassmannian over Z with integral equations => UNIT in every cell mod p = 2147483629 proves emptiness
 in char 0 (rule 3.3 / UPDATE 10). Where the q-system leaves points, SAMPLED full level equations (perm(J + x + sum lam y) - 120 at random
 numeric (x, lam) mod p; constant-coefficient combinations of the true equations, so still inside the full ideal) are added.
 CALIBRATION (both directions): X7 = random 5-dim rational subspace of L080 (dim T' = 9): k = 2 has exactly ONE non-unit cell (the one
 containing L080), and that cell stays NON-unit after adding sampled full equations.
 RESULTS (k = 3, i.e. NO 8-dim level space contains X; hence none of dim 9):
   D003P  l=(1,-1), A=C(1,-1,0,0)  [stage2 cand_D003P_l1m1]   dim T' 13: 56/56 cells UNIT (q-system)
   D003P  l=(1,-1), A=C(1,2,0,-3)                              13: 56/56 UNIT
   D003P  l=(1,-1), A=span((1,-1,0,0),(0,1,2,-3)) (dim A = 2)  13: 56/56 UNIT
   D003P  l=(1,0),  A=C(1,-1,0,0)                              13: 56/56 UNIT
   D04P   alpha=(1,1,-1,-1), sg=3/10 [stage2 cand_D04P_a11m1m1 at a rational sg]  14: 84/84 UNIT
   D04P   alpha=(1,-1,1,-1), sg=1                              14: 84/84 UNIT
   D04P   alpha=(1,-1,-1,1), sg=2                              14: 84/84 UNIT
   D04P   alpha=(1,1,-1,-1), sg=0                              14: 83/84 UNIT; cell (0,1,3): q-system 0-dim (vdim 8), + 3 sampled full eqs: UNIT
 So every tested member of both PROP families that passes (FO-r), FO2 and (T2) is EXCLUDED by an exact second-order-at-all-base-points
 test (one cell needed third+ order). CAVEATS: (i) member-wise, not yet for the whole parametric families (sg free; A free for D003P);
 (ii) msolve at one prime + my generator (calibrated as above; not yet an independent second generator). RECOMMENDATION: this "q at all
 base points on Gr(k, T'/X)" test is cheap (seconds per member) and strictly stronger than FO2 + (T2) here; stage2 should run it
 parametrically (sg, A as variables: T' over Q(params), or a fine net of rational members + the elimination ideal over Q).
STATUS 21:33: OVER-Q CONFIRMATION (verify2/r8/ext_qQ.py: same generator in integer arithmetic, Singular std over Q -- no prime involved):
 calibration CAL k=2: 5 UNIT + 1 NONUNIT (the L080 cell), as mod p; D003P (= stage2's cand_D003P_l1m1) k=3: 56/56 UNIT over Q;
 D04P alpha=(1,1,-1,-1), sg=3/10, k=3: 84/84 UNIT over Q. So stage2's saved candidate cand_D003P_l1m1 lies in NO level space of dimension
 >= 8, proved over Q (modulo my generator, calibrated). Running (2 cores): the whole D04-PROP alpha=(1,1,-1,-1) family with sg symbolic
 (T' over Q(sg): dim 14, complement denominators only sg; verify2/r8/ext_qsym.py) and the exceptional-sg locus (ext_sym_except.py).
STATUS 21:35: rows' new (PL)-route results (R8.6-R8.9, posted during this round): R8.8 LEMMA TR VERIFIED (Q = Omega Omega^T - K has Q Omega = Omega,
 Q^2 = I; S = 2 Omega Omega^T + c Q has eigenvalues 4 + c, -c, -c, +c, so U is invertible for c not in {0,-4}; U^T Q U = diag(eps)(2 p t^T + c I),
 p_j = eps_j t_j/(4+c) => t_j^2 = (4+c)(1 - c eps_j/2), tr Ad(g) = tr(g)^2 - 1) and PROPOSITION PL4(+---) VERIFIED (c = -2: the eps = -1 columns are
 reflections; B_0 = 2(P_1+P_2+P_3) - 1 symmetric orthogonal with trace 3 => B_0 = 1 => column 0 inactive). R8.6(a) frame equivalence: checked
 in its Lemma-O3 form (Phi(x) = (n-2)x + c tr(x) 1); the vec/Q bookkeeping not redone. R8.7 PL4(+++-) and R8.9 PL4(++++, ----) (Lemma ORB +
 exact GB over Q(sqrt 5), Q(sqrt -3)): NOT checked this round -- first on the next list (they carry (PL), the last input of "no principal (5,1)").
STATUS 21:37: coordinator additions. (a) stage2 R10-4 FO2-JOINT LEMMA VERIFIED (it is exactly the principle of my extension test): for y,y' in L,
 the lam-mu coefficient gives q_m(y,y') = 0 for every m in X; for xi in X, t in T_1(X): q_m(xi,t) = d/d eps [D_t perm(J + m + eps xi)] = 0, so X is in
 the radical of every q_m on T_1(X). R10-3 VERIFIED earlier this round. stage2's exact FO2-joint chart covers (70/70, 126/126, k = 4) are
 CONSISTENT with my independent k = 3 runs (which are stronger: no 8-dim extension) -- two independent generators now agree on these X.
 (b) stage3 LEMMA PFC VERIFIED (transpose: single-row part U = {w_i = 0, sum w = 0} or a full free row (FL); (Z3) gives defect in
 U^perp cap 1^perp = C(1 - 5e_i); SL excludes defect 0; FK gives dim (L^T)_j >= dim L - 4; so dim L >= 9 forces a (5,1) space with line
 C(1,1,1,1,-4)). Row-kernel bound (sec 30) VERIFIED (D_{y_r} perm(J+t) = 120 - 600/5 = 0 on L_r; P_2(y_r) = 20 e_2(e_r - 1/5) = -8 != 0, so y_r is in no
 level space; dim L <= dim T_1(L_r) - 1 and <= FO2_0(L_r)). ncdef exact certificates (31 (D)): the logic (fewer forms only enlarge the null
 cone K; a 3-dim L/N would be a plane in K; five rank-3 quadric surfaces contain no plane) is correct; runs not reproduced.
 (c) rows R8.8 (Lemma TR, PL4(+---)) VERIFIED (above); R8.9 base configurations B^0_j CONFIRMED exactly (orthogonal, sum 2I, det +-1, tr A_j = 3/4,
 sympy); Lemma ORB's classification (Parseval-frame argument) and R8.7 not yet re-derived.
STATUS 21:38: rows R8.7 PROPOSITION PL4(+++-) VERIFIED by hand, modulo its two tiny Groebner checks in (ii)/(iii) (not re-run). Point made explicit:
 "three squares with rank-2 span force g_j in <1, g_3>" holds because A = [g_0 g_1 g_2] of rank 3 is injective, so rank(AA^T) = 3 (Sylvester);
 hence rank A = 2 and im(AA^T) = im A. (i): rotations about u, t(n,n,n) = 24 x1 x2 x3 in Walsh coordinates => n, n' on the six lines; the
 (alpha/4) t((1-R_0)w,(1-R_1)w,u) part gives t(u,n,n) = 0; FINITE CHECK redone exactly: for all 30 ordered pairs with <n,n'> != 0,
 t(n x n', n, n) is in {+-8, +-16, +-8i} (my normalisation = 4x theirs), never 0. (ii) Ad(1+bN) formula, b_3 = b_0+b_1+b_2, e_2(b) = 0, columns
 0..2 in C N for sigma in N^perp (N^perp cap sigma^perp = C N) => t(N,N,N) = 0. (iii) c' = 0, WW^T = 0 for a 3x3 W => rank <= 1 (totally isotropic
 rows) => commuting. So for 4 active columns the patterns +++- (R8.7) and +--- (R8.8) are verified; ++++/---- (R8.9) need Lemma ORB (next).
STATUS 21:39: symbolic-sg attempt for the whole D04-PROP alpha=(1,1,-1,-1) family (T' over Q(sg): dim 14, complement denominators only sg;
 Gr(3,9) q-system with sg as a variable, Singular over Q): cells 1, 3, 4, 5, 6 UNIT for ALL sg; cells 0 and 2 (the largest) TIMEOUT at 300 s;
 stopped (budget). Exceptional-sg locus job stopped unfinished. => the family-wide statement needs the big-memory slot or a mod-p-then-certify
 scheme (spec in COMPUTE-ERRATA round 8/9 addendum [C]); member-wise exclusions stand. No jobs of mine running. Round 9 closing.

# ROUND 10 (start 21:41 UTC). Targets: (1) rows Lemma ORB (R8.9) + R8-Ksign verdicts; (2) stage3 round 11: N(w2,w3) level proof, exact null cone
#  H0-H2, (PR2-split') <=> (PR3); (3) parametric PROP exclusion as a QUEUE spec; (4) stage2 P0_B_ii / D00-3, [T22]/[T31]/p5b verdicts.
STATUS 21:41: round 10 started; Lemma ORB re-derived by hand (frame identity => Parseval frame => E = (H/2)M; base rotations consistent).
STATUS 21:42: verifyfl R8.8 THEOREM [T31-B] for m = (1,1,1,1,-4) VERIFIED (R8.1 normal-form facts re-derived: A_j^*A_j = 1 + 4m_j Psi from the pencil,
 A_j^* z_j = 0 by polarising (C2') with Z, sum A_j = -3; z_j non-isotropic => A_j(V) inside the nondegenerate plane z_j^perp => det(1+4Psi) =
 det(1-16Psi) = 0; common kernel vector x in all three cases for mu (generic; mu = 1/16 with P_1 = 5/4 on E; mu = -1/4 with N = 0 or N rank one
 c<f,.>f, f isotropic); Y_x = (x/2)(1,1,1,1,-2)^T; rank-one coefficients of C_4 + 4C_0 recomputed by hand: -6e_2, -12e_3, -(21/2)e_4 => x = 0).
 Valid for char p not in {2,3,5,7}. => for m = (1,1,1,1,-4), [T31] reduces to split A. stage3 31(A) MOMENT PROOF (N(w2,w3) level iff <w2,w3> = 0)
 VERIFIED: prod_j (1 + <t,x_.j>) = (1 + sum c_r t_r)(1 - al be <w2,w3> t_2 t_3) mod squares, so P_2 = -al be <w2,w3>, P_3 = -al be <w2,w3>(c_0 + c_1), P_4 = 0.
SPEC PROP-PARAM (target 3; for the big-memory slot; QUEUE line "verify2 | PROP-PARAM").  Goal: no level space of dim >= 8 contains ANY member of
 D04-PROP (alpha in {(1,1,-1,-1),(1,-1,1,-1),(1,-1,-1,1)}, sg free) -- and then D003-PROP (A free, l free).
 Step 1 (exact, cheap): T'(X(sg)) over Q(sg) (verify2/r8/ext_T1_sym.py: dim 14, complement U(sg) with denominators only sg; done for
  alpha = (1,1,-1,-1); same script with alpha changed for the other two).
 Step 2 (exceptional locus, exact): E(sg) := gcd of the 11x11 minors of the 40x25 cofactor matrix (T' jumps) times the gcd of the 14x14 minors
  of [X;U] (span drops) times sg (denominators): compute with Singular (minor(M,11) is too big -- use random integer projections R M C and
  gcd of their determinants, then check every root exactly); my sympy version did not finish in 20 min. Plus sg = -1/2 (PROP boundary).
 Step 3 (the cells, exact over Q): verify2/r8/ext_qsym.py 3 timeout=T on 84 cells of Gr(3,9) with sg a variable. Known: cells 1, 3, 4, 5, 6
  UNIT in < 10 min each; cells 0 (19 vars, 108 quadrics) and 2 (17 vars) TIMEOUT at 300 s under 2.5 GB. Ask: one Singular process per cell,
  8 GB, timeout 3 h, one at a time (alternating with Lean). For a non-unit cell: eliminate(G, c's) gives a polynomial f(sg); its roots join E.
 Step 4: every sg in E (finitely many, algebraic) gets the member-wise test (verify2/r8/ext_q.py / ext_qQ.py over Q(root) or by norms).
 Decision: all cells UNIT (or roots only in E) and every exceptional member excluded => D04-PROP excluded for all sg (char 0, exact).
 Cheaper alternative if Step 3 stalls: mod p with msolve (-t 4) to locate f(sg) in each hard cell, then certify f in the ideal over Q by an
 explicit lift (rational reconstruction + verification std), never relying on the mod-p unit alone (affine parameter sg: no properness).
STATUS 21:44: TARGET 2 (stage3 round 11): (a) N(w2,w3) moment proof VERIFIED (above). (b) EXACT null cone for H0-H2: INDEPENDENTLY CONFIRMED by my
 Schubert-cell test (verify2/r8/ext_q.py; T' dim 13 for all three, as stage3 found): k = 3 (8-dim extension): 56/56 cells UNIT for H0, H1, H2;
 k = 2: 9 of 28 cells NON-unit for each (7-dim extensions not excluded -- consistent with "dim <= 7" and with lines on the quadric surfaces).
 So "every level space containing N(w2,w3), (w2,w3) in {H0,H1,H2}, has dim <= 7" now has two independent exact derivations. (c) (PR2-split')
 <=> (PR3) VERIFIED: an N violating (PR2-split') has row-4 projection = Z, so N = X + e_4 (x) Z with X 3-dim, rows in 2-planes, no single-row
 element; Laplace along row 4: perm(J + x + e_4 z^T) = sum_j D_j(x) + <z, D(x)>, so N level <=> X level and Z perp 1, c(X), D_2(X), D_3(X); a 2-dim Z
 exists iff the 3-row defect span has dim <= 2. Equivalence exact (both directions).
STATUS 21:52: TARGET 1: rows THEOREM PL4 (no principal kernel on EXACTLY four active columns) VERIFIED, all five sign patterns:
 +++- (R8.7) and +--- (R8.8): hand, verified in round 9; ++++ / ---- (R8.9): LEMMA ORB re-derived by hand (frame identity => sum eps gamma gamma^T =
 -(c/2) Id, sum eps t gamma = 0, <gamma,gamma> = t^2/4 - 1 with Lemma TR's t^2 = 5/2 resp. -1/2; equal-norm Parseval frame |eta|^2 = 3/4 => EE^T = I -
 n n^T/(n.n) (symmetric idempotent, n non-isotropic), n_j^2 = (n.n)/4, t || n, flips => n = 1', E = (H/2)M, M in O(3); base rotations cos = 1/4 resp.
 -5/4 consistent) and the orbit computation REPRODUCED with an INDEPENDENT formulation (verify2/r10/orb_sing.py: R in O(3,C) by R^T R = I,
 B_j = R B0_j R^T, the four triple conditions, Singular over Q): ++++ UNIT, ---- UNIT; calibration 3-column (1,1,1) orbit NON-unit dim 2 (as rows).
 ++-- (R8.10): datum checked exactly (unit quaternions, sum B = 2I, dets (+,+,-,-), both orientations); uniqueness sketch re-derived (Parseval
 frame with norms (1/4,1/4,5/4,5/4), n = (sqrt3,sqrt3,i,i)/2, s || coefficients); orbit test with my own script (explicit B0 entries,
 r2^2 = 2, r3^2 = 3, ii^2 = -1): UNIT for inv = 0 AND inv = 1. => principal kernels live on <= 3 or on all 5 columns; principal (5,1) reduces to
 the 5-column K case (as rows states). Caveats: R8.7's two tiny GB checks and the vec/Q bookkeeping of R8.6(a) not redone. (Two Singular parsing
 pitfalls met and avoided on the way: "poly^2/8" parses as poly^(2/8); an entry-assigned matrix inside a sum gave a 3x8 result -- I now
 write explicit entries.)
STATUS 21:53: TARGET 4 (verdicts): none decisive yet -- R8-Ksign ks5_* outputs still empty; VF-P5B: 2 cells, both ERROR (memory-starved machine);
 [T22] m12m3 case 8 UNIT ("no N": its 2-dim doubly centred N-system is itself unit), case 7 in the big slot, case 9 waiting; stage2 D003 Q0_B_3,
 P0_B_3 and D04 P0_B_ii comps 2-4 still running (only level checks printed). PRE-AUDIT of rows/r8/x4ks.py (the R8-Ksign generator): formulation
 correct (free A_0..A_{NC-2}, A_{NC-1} = Id - sum; columns H(A_j S); all deletion permanents, coefficients of degree <= DEG in S (DEG = 3 is a
 relaxation, unit stays valid); det(B_j) = eps_j is a complete split since the degree-2 equations force B_j in O(3); saturation only for eps = +1
 columns, correct since an eps = -1 column cannot vanish). RIGOUR (rule 3.3): the system is AFFINE in the A_j (O(3,C) is not proper: rational
 orthogonal matrices have arbitrary denominators) and partly SATURATED, so a unit verdict at P1 = 2147483629 is EVIDENCE, not a proof; the
 5-column patterns must be confirmed over Q (as rows did for the 4-column orbit tests) before "(PL)" / "no principal (5,1)" is called a theorem.
STATUS 21:54: stage2 r10_FO2J_exact.py AUDITED (the exact pipeline behind R10-4's kills): T_1(X) exact over Q (all z-coefficients of sum t_k C_k);
 complement Qm; Hessian at J + m symbolic; the forms q_m replaced by the span of their z-coefficient matrices (equivalent); charts = the standard
 OPEN affine charts U_S of Gr(k, nq) (identity on S, free entries elsewhere) -- a complete cover; isotropy P = Lm F Lm^T for every basis form;
 Singular over Q, no saturation. Sound; the header's Lagrangian/operator remark is not used by the exported computation. Its 70/70 and
 126/126 unit verdicts (k = 4) and my k = 3 verdicts (Schubert cells, sampled T' containing T_1) are two independent exact derivations.
STATUS 21:55: verifyfl RESULT ROUND 8 read. K3 ([T31-B], m0) verified above (a char-0 hand proof). GAP in the LABEL of K1 ("[T31] split A EMPTY ...
 -> char 0 by Lemma RED-p" for m12m3, iso, m11m2): RED-p (their R7.1) transfers emptiness only for the WHOLE closed set X_4 (all 4-dim column-
 centred K with defect in C m, a closed subscheme of Gr(4, A_0)). Split A = {type (3,1), vartheta(Z) = 0} is NOT closed (q = 3 is an open rank
 condition), so a char-0 split-A K can reduce mod P to a K with q < 3 (a [T22]/[DC3] point), which the split-A systems never see. Hence
 "split A unit mod p" proves split A empty in char 0 only TOGETHER with [DC3] and ALL [T22] cases being unit at the SAME prime (for m12m3/iso:
 [DC3] done, [T22] 86-88/96 + pending hard cases), or by running the split-A systems over Q(i) directly. REPAIR options: (a) state K1 as
 "char 0, conditional on [T22] at p = 2147483629" until VF-T22H finishes; (b) regenerate the split-A systems with i as a variable (i^2 + 1)
 over Q -- they take 0.5 s mod p, so over Q should be cheap. Same caveat for any stratum-wise use of RED-p (e.g. "split B empty").
 [My own extension-test verdicts are NOT affected: each is one closed incidence variety in one Grassmannian, no strata.]
STATUS 22:04: stage3 31(B) H-locus description checked by hand: w2 o w3 = a w2 + b w3 <=> columnwise (x - b)(y - a) = ab (hyperbola through 0), and then
 <w2,w3> = a sum w2 + b sum w3 = 0 automatically; H0 (w2 o w3 = w2) and H1 (w2 o w3 = -(6/5) w2 + 6 w3, all four columns checked) lie on H.
 Running (2 cores): [T31] split A over Q(i) for m12m3 (8 min so far, 0.5 GB) and its 2-dim control span(Z,Y_1).
STATUS 22:05: stage2 R10-2 PROP CLASSIFICATION VERIFIED (it decides which families the exclusions must cover). PROP + xi_d forces s = 0 (ratio -1):
 so B(ind), D1, D0-3, D00-2, D0-4(i) have no PROP member. D04-PROP: row-3 projection = span{(-4;1'), (0;p'(Y_a))} and row-4 projection =
 span{(1;0) (from kappa'), (0;q'(Y_a))}, each <= 3 by (iii) => rank p'|Y_a, rank q'|Y_a <= 2. The "so split" step needs one more line, which holds:
 for the Lagrangian Y_a with P = p'(Y_a) of dim k, Y_a = {(p, om(p) + n): n in P^perp}, and isotropy makes (p,p') -> p.om(p') ANTISYMMETRIC on P;
 rank q' = (3 - k) + rank(om-bar) <= 2 gives rank(om-bar) <= k - 1, and a skew form of rank <= 1 on a 2-dim P is 0 (k = 1: trivially) => Y_a = A x A^perp.
 D003-PROP: (s_1,s_2)-image <= 1-dim forces kappa0 = (0,0,1,-1) in K2 and u1 = 0; same split argument. So the PROP families are exactly
 D04-PROP (A, sg) and D003-PROP (A, l) as stage2 states.
STATUS 22:07: stage3 ROUND 12 (sec 32, split A of [T31] for m0 = (1,1,1,1,-4)): LEMMA SA1 VERIFIED (l == 0 => b_j(K) in the degenerate plane z_j^perp cap V
 for z_j != 0 => rank b_j^*g <= 1; two nonzero columns with different m give rank s^*g <= 2 < 3; so l == 0 => z_4 = 0; any zero column forces l == 0
 since m0 has full support => split A = (alpha) z_4 = 0, l == 0  |  (beta) all columns nonzero). (beta-1) (rank-one Z) IMPOSSIBLE: VERIFIED (rank-one
 expansion with e_1(w) = e_2(w) = 0; e_3(w) = 0 => l || 1/m0, sum != 0; e_3(w) != 0 => e_4(w) = 0, e_3(l^(j)) = e_3 - l_j e_2 - l_j^3 summing to 2e_3 = 0;
 k = 0 parity; k != 0 system) and its certificate stage3/r12/beta1.sing RE-RUN over Q: unit. (alpha) normal form (E) read; (beta-2) open (heavy).
STATUS 22:08: stage3 32(E) step "the phi_j must span V" VERIFIED (else Y_s = (s/2)(1,1,1,1,-2)^T with y_4 = s - sum y_j, killed by R8.8's rank-one identity).
STATUS 22:12: verdict watch: rows' 5-column SUMQ ----- died at ~1.97 GB ("halt 14", 591 s), its msolve variant segfaulted (hash-table growth under
 the cap): no (PL) verdict yet. My [T31] split-A over Q(i) runs (m12m3 main + 2-dim control) still in Singular (12 min / 9 min).
STATUS 22:16: [T31] split-A over Q(i) (my own generator verify2/r10/t31A_Q.py, unstaged): the m12m3 main system and its 2-dim control span(Z,Y_1)
 both TIMED OUT over Q (20 / 15 min, ~0.5 GB): no verdict. The K1 label gap stands; repair = (a) K1 conditional on ALL [T22] cases unit at
 p = 2147483629 (VF-T22H), or (b) verifyfl's staged cut run over Q(i) on a bigger slot. No jobs of mine running. Round 10 closing.

# ROUND 11 (start 22:17 UTC). Targets: (1) rows R9.3 summed-cubic identity + Lemma TR5 + sumq.py (relaxation: only UNIT valid); (2) reg2 rounds 5-6
#  exact certificates ((2,2|1,1) BB/BD, (2,1,1|1,1), (1,1,1,1|2)(A), BLOCK/DOUBLE-BLOCK/RANK-ONE); (3) stage3 round 13 + verifyfl split-A for m0;
#  (4) stage2 round 11 (FO2-joint symbolic, exceptional sigma).
STATUS 22:17: round 11 started; reading NOTES-rows R9.
STATUS 22:19: TARGET 1 (rows R9.1-R9.3, sumq.py) VERIFIED, with one correction of the stated proof. R9.1 quaternion form (antisymmetric part
 <=> sum eps s v = 0; symmetric part <=> sum eps v v^T = (c/2) I, c = (sum eps - (n-2))/2), A_j formulas and activity criteria re-derived; LEMMA TR5
 re-derived (U~ diag(eps) U~^T = D since sum eps s^2 = 3 + c/2; P idempotent rank 4; I - P = rho (diag(eps) rho)^T/Lambda; diagonals give
 s_j^2 = (6+c)(2 - c eps_j + c rho_j^2/Lambda)/12). R9.3 SUMMED CUBIC: TRUE, but the per-j "g-form" quoted in its proof is NOT a polynomial identity
 (random data with sum g_k = 3 sigma: T_j/F_j not constant -- it can hold at most modulo the degree-2 relations). CORRECT one-line proof (mine,
 exact): sum_j e_3(y without j) = 2 e_3(all five), and Newton with P1 = sigma, P2 = (R - sigma^2)/4, P3 = (-4 sigma^3 + 3 sigma R - G3)/8 gives
       sum_j T_j = (3 c(sigma) - sum_k c(g_k)) / 12     (g_k = B_k sigma; only sum_k g_k = 3 sigma, i.e. the definition of s, is used),
 checked numerically to 1e-10 on random data (verify2/r11/sumcub_check.py) and on 12 points of six genuine strongly level spaces (1e-13).
 So the summed cubic is literally the SUM of the five cubic conditions: a valid consequence; inactive columns contribute c(sigma) each,
 giving sum over active = (n-2) c. sumq.py AUDITED line by line (unit quaternions s^2 + |v|^2 = 1; B_j = eps_j Rot(s_j, v_j) with the correct
 cross-product matrix; degree-2 equations exact: 6 of VV - (c/2) Id with c/2 = (sum eps - (NC-2))/4 and 3 of SV; summed cubic all x-coefficients;
 saturation by v_j only for eps = +1; default field Q). LOGIC: the system is a RELAXATION, so only UNIT is a valid verdict; UNIT OVER Q is a
 char-0 proof for that sign pattern (exact equivalent degree-2 data + a consequence + an activity saturation, all over Q); UNIT mod p is
 EVIDENCE (affine unit-quaternion variety, plus saturation). Calibrations (n = 3: ++- dim 1, --- dim 2, +-- unit) agree with Lemma O3's
 det-product rule.
STATUS 22:25: TARGET 2 (reg2 rounds 5-6) in progress.
 (a) Own exact sample check (verify2/r11/reg2_r56.py, Fractions, my generator; T' from 30 sample points = an upper bound on dim T_1, exact rank of
     q at 2 base points): BB p=2-type (10,4,8), BD v=(1,2,3,0,-6) (9,3,7), BLOCK (2,3) and (1,1) (10,4,8), DOUBLE-BLOCK (2,3) and (1,1) (10,4,8);
     all six level (10 random points each). Agrees with reg2 13.1 / 14.5 / 14.8.
 (b) Lift+Gram certificates audited line by line (gb/p2211_rank.py, pblock_rank_all.py, pdblock_rank.py, all cloned from p311): FO equations =
     all y-coefficients of sum cof_ij t_ij (exact); bases match 13.1/14.5/14.8 (BB chart x0 = 1 plus the point x = (0,0,1,-1) covers P^1 of
     {x_1 = 0, sum 0}, x' = Jx is the unique perpendicular, isotropic x included; BLOCK basis of {1,m}^perp needs s = t != 0 (localised); DBLOCK no
     restriction); pivot sets give an invertible normalisation modulo M + C d (checked by hand); 'lifts unique' = every lift coordinate reduces
     to a polynomial in the parameters modulo G, so V(G) is a graph over the elimination ideal = existence AND uniqueness for every chart point;
     Gram on span(d, tau, t, t') bilinear, rank on a subspace <= rank on T_1; FO2 bound = dim T_1 - ceil(rank/2) (L inside T_1, L/X isotropic).
     ONE STALE COMMENT, CODE RIGHT: p2211_rank.py says "d_0 (rows 3,-1,-1,-1)" but codes d_1 (3 in row 1). Which d_r lies in T_1 matters:
     D_{d_r} perm(J+m) = 4 perm(A_{r<-1}) - 480 (sum_i D_i = 600 by homogeneity), so d_r in T_1 iff perm(A_{r<-1}) = 120 on M, which holds when only
     single-row elements touch row r. BB: row 1 (column vectors have x_1 = x'_1 = 0) -> d_1 correct (d_0, d_2, d_3 are NOT in T_1 for BB:
     verify2/r11/d0_check.py, 60 points); BLOCK and DBLOCK: row 0 -> d_0 correct. [rigorous]
 (c) Re-ran the three certificates (my copies rr_*.py with private /tmp names): BB chart 1 (both pivot charts) and chart 0: lifts exist and are
     unique everywhere, rank<=2 locus = (1); BLOCK (all t != 0): same, unit. DBLOCK and my exact re-certification of the 12 special points running.
STATUS 22:27: TARGET 2 VERDICTS.
 (2,2|1,1) BB/BD: VERIFIED. Certificates re-run (rank<=2 locus = (1), lifts exist + unique, all charts); my exact re-certification of all 12 special
   points (verify2/r11/reg2_pts.py): BB x = (2,0,-1,-1), (0,0,1,-1), (1,0,1,-2), (1,0,-1,0): (10,4,8); BD v = (1,0,-1,0,0): (9,3,7), the other
   seven: (10,4,8) -- identical to reg2. WORDING REPAIR: the BD chart v = (1,v1,v2,0,-1-v1-v2) is complete only by the S_3 symmetry of columns
   0,1,2 (v_0 = v_1 = v_2 = 0 forces v = 0); reg2 does not say so. [rigorous]
 BLOCK: VERIFIED for t != 0 (lifts + Gram re-run unit; my gen_rank blockall with an independent seed (7): minors leave exactly t = 0, t = -1,
   inside reg2's exceptional set {0,-1} u {(1,0)}); t = 0, -1 rest on SP8(a) (two-column m; verified in an earlier round), a = 0 on (3,1|2).
 DOUBLE-BLOCK: VERIFIED, with an independent cover: my seed-7 minors do NOT generate (1) (they leave (a,b) = (0,1/3), (0,1), (0,0)); at those
   three points my exact sampled T' has dim 10 (a sampled T' contains T_1, so dim T_1 <= 10 there [rigorous]), so dim T_1 <= 10 on the whole
   family by my cover as well; rank q >= 3 by the re-run lift certificate (unit). FO2 <= 8.
 (2,1,1|1,1): exact samples (my generator) agree: (I-a) (9,3,7); (a,a) three x: (10,4,8); (II-2 beta) s = 2, 0, -3/2: (9,3,7). [Own slip
   while sampling: first (a,a) attempt used an x' that was not sum-zero -> not level; fixed.] The hand case split (I)-(IV) spot-checked
   (v3 = f_3 + 4 f_4, <v3,v4> = 3, <v3,v3> = 12, I-a orthogonality); IV-iso (over Q(sqrt -3)) and (a,b) not re-run. Verdict: VERIFIED at the
   level of samples + hand spot checks; the certificates p21111aa_rank / p21111iso_rank are clones of the audited lift+Gram template.
 (1,1,1,1|2)(A): log audit gb/runs/dr1111q.log: 48 Omega + 156 E_0 tests "1 1" (unit), 15 calibrations non-unit -- matches 13.3. Pipeline
   logic = the DR211 pipeline (audited round 9). Not re-run.
 RIGOUR NOTE for all point checks: a point with sampled dim T' = 10 and rank 4 gives FO2 <= 8 rigorously: either dim T_1 <= 9 (then 8.1(a)) or
   T_1 = T' and the rank is exact.
 (BL) is [numerical] as labelled; R6-3/R6-6 censuses not re-run.
STATUS 22:35: TARGET 3 (stage3 round 13, sec. 33) -- verdicts so far:
 33(A) CONIC COORDINATES: VERIFIED symbolically (verify2/r11/conic_sym.py, sympy exact): pairing -8 l_a l_b (t_a - t_b)^2, tau = 8 lll (e1 + 4 e2 e3),
   q4 formula, perm = pairings - 6 q4 (the last also for ARBITRARY sum-zero columns). The "WLOG t finite" orbit argument checked (6 special lines =
   orbit of t = infinity; the problem is invariant under row permutations).
 33(E) LEMMA S-SPEC: VERIFIED with an independent generator (verify2/r11/shapeS_mine.py: my own S_4 permanent expansion, t as a ring variable,
   coeffs() in Singular, a and b with all four coordinates + linear sum relations). Per chart a_i = 1 (i = 0,1,2; complete since a != 0 in V):
   line conditions 0-dimensional, vdim 12, and adding p3(b) = 0 leaves vdim 12, i.e. p3(b) lies IN the ideal (stronger than stated); with
   1 - u p3(b): unit. k = 3 WLOG by S_4 on columns 0..3 (fixes m0 and (1,1,1,1,-2)). [exact over Q]
 33(D) shape-S reduction re-derived by hand for |supp| = 4 (columns 0..2 = s/2 after <phi_0,s> = <phi_1,s> = <phi_2,s> = c, mu = -c/2; column 3 =
   s/2 + delta z_3, column 4 = -s - delta z_3 using z_0+z_1+z_2 = -z_3; delta = 0 is the excluded rank-one element) and for |supp| = 3 (b =
   (c_3/2) n_3). GAUGE CHECK: Y_s -> Y_s + (<psi,s>/2) Z shifts phi_j by psi ONLY for j in supp W (an off-support column would pick up
   n_j (e_j - e_4)^T, not in K); stage3's alpha0_small.py normalises phi_{min supp} = 0 and keeps the off-support phi free -- correct.
 33(F)/(G) |supp W| = 4: VERIFIED. Exact enumeration over Q(i) (verify2/r11/specialW_exact.py; stage3's special_W.py was numpy): exactly three W
   (line subsets {0,1,4,5}, {0,2,3,5}, {1,2,3,4}, lambda ~ (+-1, +-i)); the (p,p,q,q) condition fails for all 30 ordered pairs; the hand
   repetition cases re-derived (three distinct isotropic lines are independent). The three W in stage3's .sing files checked (columns isotropic,
   special, row and column sums 0, all taus 0, perm 0). Re-run of stage3's three systems: unit over Q(i) (218 equations, ~1 s).
   INDEPENDENT generator (verify2/r11/alpha0_mine.py; different s-parametrisation, sympy kernel, own expansion): full system unit for all
   three W; t-degree <= 3 already unit (82 equations); CALIBRATION t-degree <= 2: non-unit, dim 3 (matches stage3's cal2).
 33(H) |supp W| = 3: stage3's 36/36 unit (log a0s3.log); my independent generator (alpha0s3_mine.py) running on all 36 (v, n_3) choices.
 Dependencies not re-derived this round: 33(C) "|supp| = 3 => W = v l^T with e_3(v) = 0" (rank one: re-derived -- three isotropic vectors
   summing to 0 are pairwise orthogonal hence parallel; e_3 = p_3/3 for isotropic sum-zero v; the e_3 step itself uses R8.8's rank-one
   expansion, verified round 10) and the R12 normal forms (3) for (alpha).
 RIGOUR WARNING (m0 split A, for the coordinator): verifyfl's (beta) Z-only verdict (32/32 charts unit at P1) is an AFFINE system with
   the open condition u prod c_j = 1, so on its own it is EVIDENCE. It becomes a proof by RED-p only as part of the closed split-A variety
   X_A: X_A(F_p-bar) = (alpha)_p u (beta)_p (Lemma SA1 and the normal forms must hold in char p, fine for p > 5), so (alpha) must ALSO be
   unit at the SAME prime. Stage3's char-0 (alpha0) results do NOT combine with a mod-p (beta) into a proof. Two clean routes: (i) all
   of (alpha) at P1 (verifyfl's VF-M0-ALPHA), or (ii) (beta) over Q. verifyfl's own label ("char 0 once all pieces are in at this prime")
   is exactly right; the warning is about mixing the two teams' pieces.
 TARGET 4 (stage2 round 11) -- verdicts:
 R11-2 METHOD (msolve mod p on every chart of the proper Grassmannian, fixed rational data, p not dividing N): VERIFIED as an instance of RED-p
   (closed incidence scheme over Z[1/N], no saturation; forms = basis of the span of the coefficient forms of q_m over m in X, which is
   equivalent to "isotropic for every q_m"). The kills of cross a in C1 (70/70), K33 (70/70), (S2) at sigma = 2 (210/210), D04-PROP sigma = 0
   (126/126) are proofs given msolve; chart counts C(8,4) = 70, C(9,4) = 126, C(10,4) = 210 consistent.
 R11-1: the rank certificate (a compressed 11 x 11 determinant that is a nonzero constant) is a rigorous lower bound for every sigma. VERIFIED (logic).
 R11-2 "finite exceptional set" (closed in A^1 minus 0, misses sigma = 2): VERIFIED.
 R11-4/5 parametric D04-PROP: argument VERIFIED, and the label is right: mod-p projective reduction leaves exactly sigma_0 with negative
   valuation at every prime above p (the tau-chart has F_p-points at tau = 0); msolve char-0 is multimodular = evidence. A second prime
   does NOT close the loophole (it only adds a second divisibility condition). Clean closure = Singular over Q on the 126 affine
   sigma-charts (unit over Q on an affine chart is exact in char 0; the charts cover Gr). Agrees with stage2's round-12 target (3).
 R11-3: Bw formula VERIFIED numerically for random t, w, s, i (verify2/r11/bw_check.py); q affine in s because a single-row change enters every
   second-derivative term at most linearly. K33 member: exact level at 130 random rational points (126 monomials).
STATUS 22:37: CORRECTION OF MY OWN R9.3 REMARK (softened; no error in rows): rows' per-j g-form F_j = b(sigma - g_j, 3 sigma o sigma + 2 g_j o g_j - R)
 is not a polynomial identity in free data, but it is the cubic condition rewritten with the degree-2 relations: F_j = 0 holds on all six genuine
 strongly level spaces (|F_j| <= 1e-12), and SUM_j F_j = 24 SUM_j T_j holds as an EXACT polynomial identity for sum-zero columns (derived by hand
 via sum_k g_k o g_k = sigma o sigma + 4 sum_k y_k o y_k; checked numerically). Here T_j = sum over rows of e_3 of the other four entries =
 P_3(Y^(j))/2 because columns of a strongly level element are sum-zero (P_1 of the five deletions). So rows' proof is fine, and the identity
 also has a relation-free proof (mine). Verdict R9.3: VERIFIED (not "repaired").
STATUS 22:40: TARGET 3 (H) supp 3: my independent generator (alpha0s3_mine.py): 36/36 UNIT over Q(i), agreeing with stage3. NOTE: both generators
 are already unit at t-degree <= 2 (my run, and stage3's own file truncated with jet(.,2): verify2/r11/st3_s3_v0_n1_t2.sing), even with the
 Rabinowitsch dropped and even with n_3 replaced by a FREE sum-zero vector (alpha0s3_cal.py). t-degree <= 1: non-unit (dim 11). So the
 supp-3 configuration dies at degree 2 regardless of n_3 -- consistent across two generators, but it means the calibration for supp 3 is
 weak (the supp-4 runs, same code, are calibrated: t-deg <= 2 non-unit). The verdict depends on R12's normal form (3) for off-support columns.
 TARGET 2 addendum: re-ran reg2's (2,1,1|1,1) lift certificates p21111aa_rank / p21111iso_rank (my copies): chart 1 (x = (0,1,p,-1-p)): all four
 pivot charts: lifts exist (CAL = localisation only), unique, rank<=2 locus (1) -- VERIFIED. TOOL TRAP FOUND: their chart '0' option
 (x = (0,0,1,-1)) is VACUOUS: the pivot list keeps '13' although x_1 = 0 there, the normalised lift does not exist and the CAL elimination
 ideal is (1), so "rank<=2 locus = (1)" means nothing. reg2 does NOT rely on it (the x = (0,0,1,-1) sub-family is done by reg2/p21111x0.py,
 gcd of principal 3x3 minors over Q(s); re-running) -- but the option should be fixed (pivot 23, as in p2211_rank) or removed. RULE for all
 lift+Gram certificates: read the CAL line; it must be the chart localisation only. (Checked: BB c1/c0, BLOCK, DBLOCK all proper.)
STATUS 22:41: (2,1,1|1,1) x = (0,0,1,-1) sub-family: reg2/p21111x0.py re-run: level identity True, generic dim T_1 = 10, gcd of principal 3x3
 minors = 10368 (constant) -> rank q >= 3 for every s [logic: cleared-denominator kernel rows lie in T_1 identically]. rows R10.1 (summed
 cubic <=> P_3(h(sigma)) = 0) agrees with my identity; R10.6 pencil principle logic checked (distinct al give distinct H since Z_2 not in K),
 exact parts not re-run. Round 11 closing; RESULT block written; errata [F]-[I]; ledger rows added. No jobs of mine running.

# ROUND 12 (start 22:42 UTC). Targets: (1) stage3 R12 normal form (3) (supp-3 reduction) + verifyfl (alpha0)/(alpha1) at P1 for m0, build_alpha_kt;
#  (2) rows R10.2 (rank(A0 - 2I) = 7) and R10.6 (CHI2, extensions, pencil principle); (3) SUMQ5 verdicts (mod p = evidence; over-Q plans?);
#  (4) reg2 leftovers ((1,1,1,1|2)(A) re-run, IV-iso, (a,b) points) + reg2 round 7/8 deformation certificates.
STATUS 22:42: round 12 started; reading NOTES-stage3 sec. 32.
STATUS 22:44: TARGET 1a stage3 R12 normal form (E)/(C) for (alpha): VERIFIED by re-derivation: l == 0 => A_j^T z_j = 0; (C2'pol) (verified r10) gives
 A_j^*A_j = 1 + 4 Psi =: P_1 (j <= 3), A_4^*A_4 = 1 - 16 Psi = 5 - 4 P_1; sum_j b_j = 2s - 5s => sum A_j = -3; rank P_1 <= 1 because some j <= 3 has
 z_j != 0 and b_j(K) lies in the degenerate plane E_j (rank-1 form); P_1 = 0 => image of A_j totally isotropic in the 3-dim nondegenerate V =>
 A_j = n_j (x) phi_j, and for j in supp W isotropic vectors of E_j are multiples of z_j => n_j ~ z_j; y_4 formula from A_4 = -3 - sum A_j.
 33(C) supp 3 => W = v l^T, v special: re-derived (three isotropic vectors with sum 0 are pairwise orthogonal, hence parallel; rank-one expansion:
 t^3-defect vector 6 e_3(v) (0,0,0,l0l1l2,l0l1l2) must be ~ m0 => e_3(v) = 0 => p_3(v) = 0 => one of the 6 special lines; t^4 terms vanish
 because every deletion keeps a zero column).
 NEW HAND LEMMA (explains the weak supp-3 calibration of round 11): (alpha0) with |supp W| = 3 is impossible ALREADY IN DEGREE 2, for ANY
 isotropic n_3 and without S-SPEC. Proof: M := sum_{j<=3} A_j = v (x) psi + n_3 (x) phi_3 and A_4^*A_4 = 5 with A_4 = -3 - M give the form identity
 4 + 3(M + M^T) + M^T M = 0 on V. If <v,n_3> != 0 (scale to 1) take w perp v, n_3, <w,w> = 1; with a = <psi,v>, b = <phi_3,n_3>, c = <phi_3,v>,
 d = <psi,n_3>, p = <psi,w>, r = <phi_3,w>: (w,w): pr = -2; (v,v): c(6+2a) = 0; (v,w): (3+a) r + c p = 0; (v,n_3): 4 + 3a + 3b + ab + cd = 0.
 c = 0 => a = -3 (r != 0) => (v,n_3) reads -5 + 0 = 0, impossible; c != 0 => a = -3 => cp = 0 => p = 0, contradicting pr = -2.
 If <v,n_3> = 0 then n_3 ~ v, M = v (x) psi' has isotropic image, M^T M = 0, and 4 = -3(M + M^T) has rank <= 2: impossible.
 Exact check (verify2/r12/supp3_deg2.py, Singular over Q(i)): unit for v = w(t0), n_3 = w(t3) (t0 != t3), the two infinity charts, and n_3 = v
 (both charts); CALIBRATION with three independent isotropic directions (the supp-4 shape): non-unit, dim 3. [rigorous + exact]
 So supp 3 of (alpha0) now has a hand proof plus two machine checks; the stage3 36 systems are consistent with it.
STATUS 22:44: TARGET 1b verifyfl gen_m0a.build_alpha_kt AUDITED: COMPLETE parametrisation of (alpha) per INF chart, no error. z_j = k_j n_j (n_j = w(t_j)
 or chi_3), z_4 = 0, k_0 = 1 WLOG (S_4 on columns 0..3 makes z_0 != 0; then S_3 on 1..3 leaves the 8 INF patterns x,1,12,123,0,01,012,0123);
 k_1..k_3 may vanish (zero columns included: t_j is then a dummy, which only adds dimension); sum z_j = 0 linear in k (chi_1, chi_2, chi_3
 coefficients); Y_r = b_r e_0^T + doubly-centred part (12 coords) = the general column-centred element with s(Y_r) = b_r; gauge
 <col_0(Y_r), chi_3> = 0 (resp. chi_1 if 0 in INF) is valid because <z_0, chi_3> = <chi_1, chi_3> = 4 (resp. <chi_3,chi_1> = 4) != 0; l == 0 as
 <2 y_{r,j} - b_r, z_j> = 0; nY = 2 drops Y_3 (a relaxation: unit stays valid). No P_1-rank split, so (alpha0) and (alpha1) are both inside.
 verifyfl's R9.7 same-prime ledger is correct (split B by hand for p > 7; (beta) 32/32 at P1; (alpha) KT charts 12,123,01,012,0123 unit at P1,
 charts x, 1, 0 open). The case split (SA1) holds in char p > 5. My supp-3 hand lemma is char-free for p > 5 (divides by 2, 3; uses -5 != 0).
 => [T31] for m0 at P1 is complete once KT charts x, 1, 0 are unit.
STATUS 22:45: TARGET 2a rows R10.2: VERIFIED independently (verify2/r12/rank2_indep.py): own basis of the 7-dim harmonic cubics, exact det(A0|H_3 - 2):
 ++++ and its Galois conjugate: -3375 = -(240/16)^3 (matches rows' spectrum 1, -5/4 +- i sqrt71/4 x3); ---- and conjugate: -273375 = 3(-6)^3(15/2)^3
 (matches 5, -4 x3, 19/2 x3); ++-- both orientations: 820125. All nonzero. Data checked: each B_j orthogonal, det B_j = eps_j, sum B_j = 2I.
 Logic re-derived: summed cubic with B_j = R B^0_pi(j) R^{-1} becomes A0 (c o R) = 2 (c o R); pullbacks by orthogonal maps preserve
 Sym^3 = H_3 (+) |x|^2 V^*, A0 = (sum B_j)^T = 2 on |x|^2 V^*, c o R is a nonzero harmonic cubic, so 2 must be an eigenvalue on H_3 -- it is not.
 Rests on Lemma ORB (verified r10). Second certificate for PL4 (++++, ----, ++--) confirmed.
STATUS 22:48: TARGET 2b rows R10.6: VERIFIED.
 (a) EXTENSIONS: rows' extIIQ/extIQ re-run over Q (0.1 s): EXT-II radical = line through w e_4^T (y_04 = y_14 = y_24 = -y_34/3, rest 0); EXT-I: one
   prime, dim 1 = line through chi e_2^T. INDEPENDENT generators (verify2/r12/ext_chi2_mine.py: gauge on row 1 instead of row 0, constants in an
   algebraic extension (minpoly) instead of a variable, my own S_4 expansion): same two lines. Gauges valid (zeta_0 = zeta_1/w = 1 != 0, chi_1 = i).
 (b) THEOREM CHI2: rows' chi2Q re-run: dim 0, m4 = 0, (m2+1)(m3+1) = 0, m2^2 = m3^2 = 1 -> exactly m in {(1,-1,-1,1,0),(1,1,-1,-1,0),(1,-1,1,-1,0)};
   saturation by m1 m2 m3 m4: unit. MY version: projective defect condition (all 2x2 minors m_j F_k - m_k F_j, no m_0 = 1 chart) on ALL four charts
   m_k = 1 (k = 0..3; no symmetry argument needed, every admissible m has a nonzero entry in 0..3 since sum m = 0): dim 0 in every chart, the
   same three m up to scale, PLUS the trivial m = (1,1,1,1,1) (Z ~ J/4), which is excluded by sum m = S = 0 (P_1 of the 5x5 level space: the total
   sum of the 4x5 part vanishes). rows imposes 1 + m1 + m2 + m3 + m4 = 0 -- correct. My cover confirms rows' symmetry reduction.
 (c) PENCIL PRINCIPLE: logic re-checked (H_al pairwise distinct since Z_2 not in K; gauge-fixed representatives gf(Z_1) + al gf(Z_2) form a line
   with gf(Z_2) != 0, contradicting dim 0). Consequences: no (5,1) space with rank c = 1 over K_II (CHI2) or chi (x) C^M (CHI1, verified r9).
   Scope: rank c = 1 only; (d)'s "(1,2) DONE" also rests on Lemma SL's type classification (d = 2 => type I/II), verified as a blueprint earlier.
 TARGET 3 SUMQ5: big-slot outputs rows/r8/orb/sq5big_{-----,+----}.out still EMPTY (running). rows' over-Q plan exists (QUEUE R9-SUMQ5 line 43:
   sq5Qruns.sh, P = 0) but it runs under ulimit 2 GB, where every five-column pattern dies even mod p (591 s / 581 s) -> the over-Q runs need
   the big slot too (or a modular-then-certify scheme). Reminder: mod-p UNIT is evidence only (affine unit-quaternion variety + saturation by v_j).
STATUS 22:52: TARGET 4 (reg2 leftovers + deformation certificates).
 (1,1,1,1|2)(A): RE-RUN over Q with reg2's generator into my directory (verify2/r12/dr1111.log): 48 Omega UNIT, 156 E_0 UNIT, all 24 calibrations
   NON-unit. Logic re-checked: Omega cap W = 0 for the complement W = {rho_4 = 0, sum_{0..3} = 0} gives dim Omega <= 2; E_0-test = injectivity of
   the pivot projection; chart cover b_0 = 1 (S_4 on columns 0..3), c_1 = 1 suffices (S_3 on 1..3 fixing column 0; c sum-zero nonzero has a
   nonzero entry in 1..3), a_ja != 0 (4 charts). VERIFIED.
 IV-iso (7 points), (a,b) (12 points), (a,a) leftovers (9 points): my own exact Q(sqrt -3) arithmetic (verify2/r12/qr3_fo2.py, pair arithmetic,
   own permanent and elimination): all numbers identical to reg2 (IV-iso 7 x (10,4,8); (a,b) 8 x (9,3,7) + 4 x (10,4,8); (a,a) 9 x (10,4,8)). VERIFIED.
 Lemma SK (16.5): re-derived (P_1 = Sx + Sy, P_2 = Sx Sy - <x,y> for two-column matrices; polarised => skew on the sum-zero part; odd dimension
   => kernel line; rank one: P_2 = (1/2)((Sx)^2 - <x,x>)((Sv)^2 - <v,v>)). VERIFIED.
 omega_e0.py (R8-1 tool) AUDITED: Omega-test (X free, complement W of span(1,e_c), 4 charts) sound; E_0-test is sound even without d in T_1
   (it proves injectivity of the 7 pivot coordinates on E_0, hence dim E_0 <= 7); skew deformation J_v is skew (checked).
 GAP FOUND (coverage check broken) + REPAIRED for (2,1,1|2)(iii) row 0 -> 2: omega_e0.py's coverage print adds 'z' to the ideal and calls LIB inside
   an if-block, so the log shows "coverage 4 z" instead of a verdict -- the coverage was never actually checked. My re-run (rr_omega_e0.py, same
   seeds, same pivot sets) prints the ideal: V(Delta_1, Delta_2) = {t = 0, m3+m4 = 3} u {t = 0, m3 = 0} (undeformed, sec. 9.6)
   u {m4^2 - 3m4 + 3 = 0, m3+m4 = 3} x t (reg2's listed line, minors) u {m3 = 0, m4 = 2} x t u {m3 = 0, 3m4^2 - 2m4 + 3 = 0} x t.
   The last TWO lines are NOT in reg2's text. REPAIR (rr_oe0_line.py: relations added, pivot sets chosen ON the line): (0,2) x t: new pivot sets
   cover all t != 0, E_0-test unit (13+13 charts); (0, root) x t: coverage (1), E_0-test unit. With the Omega-test (unit for all parameters):
   dim T_1 <= 9 on both lines. So R8-1 for (2,1,1|2)(iii) holds, but its stated certificate was incomplete.
   The other four families of R8-1 are being re-run with the fixed coverage print (oe0_*.log).
STATUS 22:54: deformation re-runs with the fixed coverage print (NPIV = 2, as in reg2's log): 2121V0: uncovered s = -1 only (= reg2's statement);
 22_2: Omega-test elimination ideal (t(m3-m4), m3^2-m3, m4^2-m4) (= reg2); E_0 coverage with NPIV 2 leaves the PLANE m4 = 1, with NPIV 4 only the
 line mu = (0,1,0,1) x t (= reg2's statement, which says 4 pivot sets). 11121A1 (NPIV 2): uncovered s = +-1 x t (reg2 says "only t = 0");
 213def (NPIV 2): eleven components, reg2 lists 3 (t = 0 pieces and u ~ (3,-1,-1,-1)); the other seven lines (3u2^2+2u2+3 = 0 & 2u1+u2+1 = 0;
 u1^2+u1+1 = 0 & u2 = 0; (u1,u2) = (-1,0), (0,0), (1,-1), (1,1); u2^2+2u2+3 = 0 & u1 = 1) x t were NOT in reg2's text.
 REPAIR RUNS (rr_oe0_line.py, pivots chosen on each line, relations added): all 7 extra 213def lines: E_0-test unit, coverage (1) or only t = 0;
 11121A1 s = 1 and s = -1: coverage (1), E_0 unit. So dim T_1 <= 9 holds on all these lines -- the four level-for-all families of R8-1 are
 CLOSED after my repairs. Checking whether reg2's actual runs used NPIV = 4 (their text says "4 pivot sets" for 211iii and 22_2): re-running
 211iii, 11121A1, 213def at NPIV 4.
STATUS 22:56: TARGET 4 deformation verdicts (CORRECTION of my 22:5x wording: the "GAP" was in the SAVED EVIDENCE, not in reg2's claims).
 NPIV = 4 re-runs (fixed coverage print): 211iii: uncovered = finitely many t = 0 points u {m3+m4 = 3, m4^2-3m4+3 = 0} x t = exactly reg2's 16.2
 statement; 11121A1: uncovered {t = 0, s = +-1} (undeformed) = reg2's "only t = 0"; 213def: uncovered {u ~ (3,-1,-1,-1)} x t u one t = 0 point =
 reg2's statement. So reg2's statements match NPIV = 4 runs (their text says 4 pivot sets), while reg2/gb/runs/omega_e0.log is a stale
 NPIV = 2 log and the tool's coverage print is broken ('z' appended to the ideal, LIB inside an if-block: it prints "4 z" etc., never COVERED).
 My NPIV = 2 line repairs (all extra lines: E_0 unit) are an independent second confirmation. 2121V0 at s = -1: my gen_rank_defo re-run (seed 3,
 private /tmp name): 30 16x16 minors = (1). 22_2: NPIV 4 leaves only mu = (0,1,0,1) x t (= reg2).
 => R8-1 (four dim T_1 <= 9 families + 22_2's E_0 part): VERIFIED by re-run; reg2 must fix the coverage print and save the NPIV = 4 logs.
 R7-2 BB row deformations: lift certificates p2211def_rank re-run (JROW 1, 2; charts 1, 0): CAL = localisation only, lifts unique, rank<=2 locus (1);
   d_1 stays in T_1 (row 1 touched only by single-row elements -- for JROW = 1 the deformed part is removed by row 1 := 1 and the rest lies in the
   undeformed level BB); exact samples (verify2/r12/bbdef_sample.py): (p,t,j) = (2,3,1), (2,3,2), (-1/2,1,1), (1,1,2), (-3/5,7/2,1): all (10,4,8),
   level. VERIFIED (minor runs BBdef1/2 not re-run).
 R8-2 certify_defo methodology (generic dim over Q(t), minors at the fixed base point, gcd of principal minors on a cleared kernel basis,
   exact leftover points) sound; logs read (27 + 4 entries, all closed); not re-run.
STATUS 22:58: TARGET 1 cont.: stage3 33(J) (alpha0) |supp W| = 2 re-derived (s in S_2 = ker(phi_0 - phi_1), mu = -<phi_0,s>/2 kills columns 0,1 down to s/2, v
 cancels in column 4 because z_0 = -z_1; n_2, n_3 special by S-SPEC inside P2 or irrelevant; c_2 ~ c_3 would give a rank-one element; n_2 =
 chi_1 by row S_4). INDEPENDENT generator (verify2/r12/p2_mine.py; Gr(2,V) charts via the first three coordinates, own expansion): 18/18 UNIT
 over Q(i); calibration t-degree <= 2: non-unit, dim 3. => THEOREM (alpha0) for m0 VERIFIED in char 0 (supp 4: r11; supp 3: r11 + degree-2
 hand lemma; supp 2: now). stage3 R14(B): its conversion of all (alpha0) pieces to P1 (i = 1518275076, i^2 = -1 mod P1 checked) makes (alpha0)
 a valid piece of the same-prime cover; R14(C) is the same degree-2 lemma as mine (found independently). R14(D) (alpha1) normal form
 A_j = n_j (x) psi_j + u_j (x) f re-derived (A(f^perp) is totally isotropic and orthogonal to Im A => inside C n with n isotropic).
STATUS 23:10: ADDITION (coordinator): leanfl X5_mc (lean/fl/x5c.part; rows R7.3 step (2), first conclusion m_c = 0): paper argument VERIFIED.
 Re-derivation: Z in N = K' cap ker s has z_j = (kappa m_j/4) 1 + m_j B_j f (R5.7(3)/R5.9(2), verified earlier); row sums 0 and sum m = 0 give
 m_a B_a f + m_b B_b f + m_c B_c f + (m_d + m_e) f = 0 (inactive B = 1); pair with v using B_a v = B_b v = v (step (1)), B_c v = -v and B_a^T = B_a^{-1}:
 (m_a + m_b - m_c - m_a - m_b - m_c) <f,v> = -2 m_c <f,v> = 0. If m_c != 0: f(N) is inside v^perp. But <f_W,f_W'> = (3/4) kappa_W kappa_W' (polarised),
 so the form on f(N) has rank <= 1 (and f is injective, dim f(N) = dim N >= 2) -- a degenerate plane, while v^perp (v non-isotropic) is a
 NONDEGENERATE plane: contradiction (leanfl phrases it as v perp f_Z (non-isotropic) and f_Zs (isotropic, nonzero, perp f_Z) => v in C f_Zs =>
 v isotropic). Hence m_c = 0 with no case split. Lean text read: hypotheses = K' a (5,1)-type space (QBc), H <= K strongly level, rank of row
 sums 3, H supported on columns 0..2 (hsupp), column 2 = projector onto non-isotropic C v (hc2), dim(K cap ker rs) >= 2; the proof chooses
 Z1 (colsum_2 = m_2 => kappa = 1) and Zs (colsum_2 = 0 => kappa' = 0), f_Zs != 0 via H cap ker rs = 0, then span2_perp -- matches the paper
 argument. SCOPE: needs the kernel on THREE columns with the rank-one column (that is where B_a v = B_b v = v comes from); the coordinator's
 wording "every (5,1) space whose principal kernel has a rank-one column" should carry that hypothesis. CONSEQUENCE: rows' sub-cases of
 step (2) under m_c != 0 (R scalar / p = 0 / m_a = m_b = 0 via VF-A, TC5) are all subsumed; X5 no longer needs VF-A; TC5 is still used later in
 step (2) for m_a = m_b = m_c = 0 (two-column m on d, e). Not compiled (window 2), so [paper-verified], not [Lean].
STATUS 23:11: R7-2 minors re-run with my seed (11): BBdef1 leaves t = 0 points and the LINE p = -1/2 (any t) [reg2's seed left only a point there];
 my gen_rank_defo on that line (2211BB row 0 -> 1, fix p = -1/2, seed 5): 30 15x15 minors = (1). BBdef2 leaves only t = 0 points; BBdef1x unit;
 BBdef2x leaves t = 0. Extra: row 0 -> 2 at p = -1/2 and p = 1: minors (1). t = 0 = BB (13.1, verified r11). => dim T_1 <= 10 on both deformation
 families by my own cover; with the re-run lift certificates: R7-2 VERIFIED completely.
 stage3 R14(F) (alpha1) supp 3 setup audited from the notes (A_3 = n (x) phi + eps_3 rho e_3 (x) f covers the n = 0 line case; e_3 perp w(tau), <e_3,e_3> = 1
 checked); my independent generator a1s3_mine.py written (first version had a Singular INT-DIVISION bug: "(1)/2" evaluated as 0 -- own slip,
 fixed by dividing whole polynomial terms); its degree-2 calibration (stage3: non-unit, numerical solution) is still running.
STATUS 23:14: stage3 COMPUTE item 13 (cuts for verifyfl's KT charts, to be used INSIDE the P1 cover, so they must hold in char p): (C1) = 33(C)/34(E),
 re-derived (r12 above), valid for p > 5 (p_3 = 3 e_3 for isotropic sum-zero v; conic and cubic meet in the 6 distinct special lines mod P1).
 (C2) re-derived: with z_4 = 0 the cubic line condition reads (2 tau_0, .., 2 tau_3, 2 sum tau_j) ~ (1,1,1,1,-4) => all tau_j = T and 8T = -8T => T = 0;
 the quartic vector (0,0,0,0,perm W) ~ m0 => perm W = 0. Formulas at infinity checked symbolically: tau(w(a),w(b),chi_3) = -16ab(a+b) = 8(-2ab(a+b)),
 tau(w(a),chi_3,chi_3) = 8a, tau(chi_3^3) = 0, <w(a),chi_3> = 4, <chi_3,chi_3> = 0, <w(a),w(b)> = -8(a-b)^2. VERIFIED (valid for p > 3). (C3): statement only.
STATUS 23:14: rows R11.2 (column-centred (5,1) over chi (x) C^M and K_II), logic only: hyperplanes of L' through K form a P^1 of 4-dim column-centred
 spaces whose defect is nonzero (a 4-dim strongly level space contradicts Lemma SL) and lies in C m; finitely many extensions (K_II: finitely
 many lines, all with two-column m -> TC5) or none (chi (x) C^M: unit) => contradiction. Logic VERIFIED; exact runs (chi2cc.py, chi1cc.py) not
 re-run. R11.1/R11.4-R11.6 (two-column (2,1) family) not audited this round. alpha1 supp-3 batch: 6/48 so far, all unit.
STATUS 23:21: alpha1 supp-3 independent runs (a1s3_mine.py; 8 sign patterns with eps_0 = + suffice since (eps, rho) ~ (-eps, -rho) under the chart
 f_c = 1; x 3 f-charts x 2 n-charts = 48): 24/24 UNIT so far. Calibration (t-degree <= 2) over Q(i): no verdict within 900 s (positive-dimensional);
 re-running mod P1.
STATUS 23:27: ERRATUM E-MSOLVE-BIGCOEFF (coordinator): (1) MY FILES: scanned all 675 .ms files under verify2/ (chars 2147483629: 579, 2147483497: 96):
 NO coefficient >= p (exponents excluded). Writers: r8/ext_q.py and r8/ext_full_cell.py reduce every coefficient with % P; vf/own_gen_A.py works in
 F_p arithmetic (% p throughout); r7/dc3_split*.py emit through verifyfl's exactlib (mod p by construction). So none of my mod-p verdicts is affected.
 (2) stage2's mod-p chart kills are now PENDING until the patched re-run confirms them; status of stage2/r9/rerun_patched.log at 23:26:
 crossC1 70/70, K33 70/70, crossA 70/70, D003ptA 35/35, D003ptB 35/35 re-confirmed (non-unit 0); D04Pa sigma = 0 running; (S2) at sigma = 2 (210),
 D04-PROP sigma = 2, -3 and the parametric run not yet re-run. My round-11 verdict "R11-2 method sound" stands (it is a logic verdict); the
 individual kills are relabelled: re-confirmed (5 above) / pending (rest).
STATUS 23:29: stage3 R14(F) (alpha1) |supp W| = 3: my INDEPENDENT generator (verify2/r12/a1s3_mine.py; own expansion, s = (s0,s1,s2,-sum), halves applied
 to whole polynomial terms): 48/48 UNIT over Q(i) (8 sign patterns with eps_0 = + [the other 8 are equivalent via (eps, rho) -> (-eps, -rho) in the
 chart f_c = 1] x 3 f-charts x 2 n-charts). CALIBRATION: the t-degree <= 2 truncation (7 equations; Singular over Q(i) and mod P1 did not finish
 in 900 s / 7 min, positive-dimensional) has a numerical root with rho != 0, l1 not in {0,-1} (LM, residual 3.8e-13; verify2/r12/cal_num.py on the
 dumped equations E_cal.txt) -> non-unit, so the unit verdicts use the degree-3/4 conditions (agrees with stage3's numerical calibration).
 VERIFIED in char 0 (the P1 version is stage3's; same-prime use needs it at P1, which stage3 ran). Batch stopped after 48; no jobs of mine running.
 Round 12 closing.

# ROUND 13 (start 23:30 UTC). Targets: (1) PROOF-MAP.md (one-page proof tree with statuses, bases, sources, open leaves); (2) stage3 LEMMA S2
#  ((alpha1) supp 2) + supp 4; (3) stage2 patched re-runs + F2col cross-type ruling; (4) rows R11.1, R11.4-R11.6, R11.2 exact parts;
#  (5) reg2 round 9 (SIGMA/(d) lift_gram, double-deformation bound, Lemma SK2); (6) leanfl LAG_a/NB/TC5 statements vs paper.
STATUS 23:30: round 13 started; reading BRIEF.md for the branch structure.
STATUS 23:32: TARGET 1: PROOF-MAP.md written (L-gct-210/PROOF-MAP.md, ~85 lines): base, case split (A)/(B)/(C) per handoff sec. 1, branches 1-4 with
 node statuses (V-rN / CL / OPEN / RUN(job) / NUM), bases (c0 / P1 / Lean), sources, 11 OPEN leaves with size guesses, pending relabels.
 The case split itself is recorded as CL (from handoff sec. 1); its ingredients are verified.
STATUS 23:37: TARGET 3 stage2. (a) PATCHED RE-RUNS (stage2/r9/rerun_patched.log): crossC1 70/70, K33 70/70, crossA 70/70, D003ptA 35/35, D003ptB 35/35,
 D04-PROP sigma = 0 126/126, sigma = 2 126/126, (S2) sigma = 2 210/210 -- all RE-CONFIRMED (non-unit 0). sigma = -3 was a Singular-over-Q run
 (unaffected). Only the D04-PROP parametric run (sigma affine + tau chart) is still re-running. Relabel: those kills are back to proofs (given
 msolve with reduced coefficients). (b) F2col CROSS-TYPE RULING (R13-1, R13-2) AUDITED: chart a_4 = 1, D != 0 covers exactly m_4 not in {0, m_0}
 (m = a - ((a1+a2+a3+1)/5) 1: m_4 - m_0 = 1, m_4 = -D/5) and the S_4 on columns 1..4 brings every m there (if all m_k in {0, m_0} then sum m = 0 forces
 m = 0); rank-drop locus (a1+a2+a3+1)^2 = jump locus m_0 = 0 (dim T_1 = 15); the Lagrangian rulings of (S x S, <p0,p1'> + <p1,p0'>) re-derived (graphs
 of lam R with R skew; span{(w,0),(0,v)}, <v,w> = 0). LABEL: the 67/70 parametric verdicts are mod p with AFFINE parameters and a Rabinowitsch on D
 -> evidence, not a RED-p proof (stage2 says so: "p-denominator loophole"); 3 charts FAILED (allocation, not survivors); m_0 = 0 open. Status:
 RUNNING/OPEN, labels correct.
STATUS 23:39: TARGET 4 rows R11 (two-column (2,1) stratum):
 R11.1 VERIFIED: P_2(Y^(j)) = c_j^2 + s.y_j - |y_j|^2 + kappa(Y) re-derived (needs total sum 0); polarising with D = d_0(e_a - e_b)^T (s(D) = c(D) = 0)
   gives (beta, -beta, delta, delta, delta) with beta = <d_0, s_Z - P_Z>, delta = <d_0, D_Z>; in C m with sum m = 0 => delta = 0, beta != 0 => m two-column.
 R11.4 VERIFIED: K-K-Z cubic vector (0,0,T_d+T_e,T_c+T_e,T_c+T_d) (supports {a,b,t}); T_t via the distinct-index identity for sum-zero columns,
   first bracket 0 because K is Lagrangian for <x,y'> + <x',y>; m_a != 0 forces T_c = T_d = T_e = 0; generic Pi = V => z_t = (m_t/4) 1.
 R11.5/R11.6 VERIFIED: closed deletion formulas checked against direct permanents (exact, random data; verify2/r13/r11_generic.py); l == 0 by the
   omega-derivative argument (valid via continuity in t); the conclusion "m has a zero entry" checked by a Groebner basis over Q: with m_a = 1,
   sum m = 0 and u m_b m_c m_d m_e = 1 the system "C_j(tZ) - 24 = lam(t) m_j for all t" is the UNIT ideal (all t-coefficients, so degree 3 for the
   case m_a = m_b is included); calibration without the Rabinowitsch: non-unit.
 R11.6(c)/R11.7 VERIFIED: (U), (W), (D) with z_t constant reduce to <u,P_Z> = 0, <p,P_Z> = <e,D_Z>, <d,D_Z> = 0 (the W-difference and the D-sum are
   automatic since u, p, e, d are in V), plus the two column sums; the five functionals vanish on the gauge G and are independent (p in span(u,1)
   would give <p,p> = 0) => Z unique mod K => pencil => no (5,1) of rank c = 1 over a generic two-column (2,1) kernel with m_a or m_b != 0.
   Column-centred case: z_t = 0, deletion vector (0,0,-2w,-2w,-2w) re-derived, w == 0 gives a 4-dim isotropic subspace of a 6-dim split space.
 DEPENDENCY not re-derived: the explicit form of two-column (2,1) kernels (R10.7: u, d, p, e with the stated inner products). OPEN (rows'
 own list): special kernels (Pi < V: line d = u and finitely many points, R11.9 in progress), m_a = m_b = 0 (hand-off to verifyfl), three-column
 (2,1) kernels.
STATUS 23:47: TARGET 5 reg2 round 9:
 LEMMA SK2 VERIFIED (re-derived: the trilinear part of P_3 on (Y_w, Y_w', Z) takes one entry from row r and one from row j of the two P-elements and
   one from a third row of Z, = e(w,Bw',zeta) + e(w',Bw,zeta); for sum-zero w, Bw' the distinct-index identity gives -(S zeta)(<w,Bw'> + <w',Bw>)
   + 2(T(w,Bw',zeta) + T(w',Bw,zeta)); B skew kills the first term, so (w,w') -> <w o zeta, Bw'> is skew). The rank-<= 2 consequence is not proved (as stated).
 R9-1 lift_gram certificates (SIGMA_2 col 0->2, SIGMA_3 chart c2 col 0->3, (d) col 0->2) AUDITED from reg2/evidence/logs: CAL lines are the family
   relation + localisation only (non-vacuous), lifts unique, rank<=2 locus (1) on every pivot set. COVERAGE recomputed by me (minAssGTZ of the
   pivot minors + relation): SIGMA_2 uncovered = the point (b3,c3,t) = (1,-1,1/3) [reg2: exact (10,4,8)] and b = c isotropic (degenerate, a = 0);
   SIGMA_3: t = 0 (undeformed) and c ~ b (degenerate); (d): Delta_0, Delta_1 have no common zero on b3^2+b3+1 = 0 (6+6w at t = 1/3). All match reg2.
   lift_gram does NOT check d in T_1; for these column deformations d = d_0 is in T_1 because row 0 is touched only by single-row elements
   (the column groups and their deformations have row-0 entry 0). VERIFIED.
 R9-2 (double deformations, dim T_1 <= 10): CL (minors run not re-done); its rank q >= 3 part is reg2's open item.
STATUS 23:49: TARGET 2 (in progress): stage3 35(B) supp 4 and 35(C) supp 2 hand reductions RE-DERIVED (details below); LEMMA S2 independent runs
 (verify2/r13/s2_mine.py: standard coordinates, own expansion, a-charts v a_i = 1 for i = 0,1,2) running over Q(i) and at P1.
 35(B) |supp W| = 4 given S2: for s in f^perp, A_j s = c_j(s) z_j; with mu = -c_p(s)/2: Y = (s/2) m' + sum delta_j z_j (e_j - e_4), delta_p = 0 (uses z_4 = 0 and
   sum z_j = 0); points P_j = c_j|f^perp in the 2-dim dual (gauge translates all four); s in ker(P_q - P_p) gives an S2 element on the other two columns,
   delta_c = 0 iff P_c on the line P_p P_q. Configuration analysis checked: coincidence of >= 3 points, two coincident pairs, or 4 collinear points
   give a rank-one element (R8.8); (A) general position: every complementary pair parallel => W rank one; (B) exactly three collinear: the three
   pairs with P_3 give z_0 || z_1 || z_2 => rank one; (C) one coincidence P_0 = P_1 with P_0, P_2, P_3 non-collinear: z_0 = z_1 = z, then
   2<z_2,z_3> = <z_2+z_3,z_2+z_3> = <2z,2z> = 0 => z_2 || z_3 => rank one. Rank-one W with four nonzero entries is impossible (re-checked:
   t^4 vector 24 e_4(v)(0,0,0,0,prod l) forces e_4(v) = 0; t^3 vector forces either all l_j equal (contradicting sum l = 0) or e_3(v) = 0; then all
   e_k(v) = 0, so v = 0). The case list is exhaustive. VERIFIED (given S2).
 35(C) |supp W| = 2 given S2 + S-SPEC: the K_f columns (y_0 = s/2 + al0 v, y_1 = s/2 + (sig - al0) v, y_k = s/2 + gam_k n_k, y_4 = -s - sig v - sum gam_k n_k)
   re-derived from the (alpha1) normal form; S2 elements on {2,3} (ker sig, al0 = 0), {0,2} (ker gam_3, al0 = sig), {0,3} (ker gam_2); case analysis
   re-done: pairwise non-proportional => n_2 || n_3 || v and sig - gam_2 = a gam_3, sig - gam_3 = b gam_2 => a = b = 1, sig = gam_2 + gam_3, then
   gam_2 - gam_3 = c(gam_2 + gam_3) is impossible (char != 2); a zero form forces the other two equal (=> common kernel); (c1) sig || gam_2: n_2 = v,
   gam_2 = sig, n_3 special (shape S); (c2) symmetric; (c3) gam_2 || gam_3: n_2 = n_3, gam_2 = gam_3, v special. Exhaustive (three forms in a
   2-dim dual, not all proportional). INDEPENDENT generator for (c1)/(c3) (verify2/r13/c13_mine.py; Gr(2,V) charts via the first three
   coordinates, special vector chi_1 by row symmetry, free vector w(tau) | chi_3, u det(sig,gam) = 1): 12/12 UNIT over Q(i) (< 1 s each).
   (calibration t-deg <= 2 deferred: positive-dimensional and slow; stage3's d2 calibration is non-unit, dim 4.)
 CASE-SPLIT EXHAUSTIVENESS (asked by the coordinator): (alpha) = {z_4 = 0, l == 0}; rank P_1 <= 1 (normal form, V-r12) gives P_1 = 0 (alpha0) or
   rank 1 (alpha1); W != 0 with sum_{j<=3} z_j = 0 gives |supp W| in {2,3,4}. (alpha0): supp 4, 3, 2 V-r11/r12; (alpha1): supp 3 V-r12, supp 4 and 2
   above (given S2). EXHAUSTIVE.
 TARGET 6 (leanfl statements vs paper): LAG_a (lag.part) = paper LAG(a) in the paper's normalised basis (z0 isotropic in V, tau z1 = 1, <z1,z1> = 1,
   <z0,z1> = 0 encoded via e2, e2b; Ed z = E(z), Edb = E(z,z') match z0^2, z0 o (z1 - 1/2), z1 o (z1 - 1)); conclusion dim of the orthogonal <= 1 <=>
   dim E_zeta >= 2 in the 3-dim nondegenerate V. LAG_b: hypotheses n_i^4 = kappa, tau n = 0, <n,n> = 0, t3 n n n = 0 contain every chi_1-type vector;
   the conclusion (not orthogonal to both E(z0), E(z0,z1)) is the paper's proof content (stronger than (b)). NB3 / NB_plane / TC5_P1 descriptions
   match LEMMA NB and TC5 (P1). MATCH (statements read; nothing compiled yet; the reduction from a general zeta to the normalised basis must be
   in a wrapper -- not checked).
STATUS 23:57: ADDITION (coordinator): verifyfl R10.8 / R10.10 SYM-M ([DC3] uniform in m on the line of |supp m| <= 3 defect lines). AUDIT:
 CORRECT: charts A (m = (1,t,-1-t,0,0)) and B (m = (t,1,-1-t,0,0)) cover P(W_P) = P^1 (A misses only (0,1,-1) = B at t = 0); if some 4x4 minor of the
 polynomial basis of m^perp is a nonzero constant (p-unit), then "W(t) C = 0" is exactly "C in C m(t)" for every t in every char (needs that minor
 printed -- "rank 4 for every t" should be shown this way); X = {(N, m) : N in Gr(3,D), defect(N) in C m} is closed in Gr(3,D) x P^1, proper over
 Z_(p); a Q-bar point reduces to an F_pbar point of X_p; the [DC3] cover (gen_n1s cases) is a case split valid in char p for every m on the line
 (two-column points: one neutral column unused, still a valid split). So: ALL 254 cases UNIT in F_p[t,x] in BOTH charts at P1 => [DC3] for EVERY
 m with |supp m| <= 3 in char 0. [rigorous]
 GAP (same flaw as K1 in round 10): the PER-CASE consequence stated in R10.8/R10.10 and in RESULT M6 ("a case UNIT in both charts is empty for every m
 in char 0"; "252/254 ... these cases are empty for EVERY m with m_0 != 0") does NOT follow. The cases are locally closed strata (Schubert cells
 x line cells x isotropic charts), not closed; a char-0 point of a unit case can reduce mod p into a DIFFERENT, non-unit case (the echelon
 pattern / incidence type can change mod p). The reduction argument only gives "X(Q-bar) nonempty => X_p nonempty". Also, chart A alone (m_0 != 0)
 does not give the per-chart claim for the same reason. REPAIR: state the result as "[DC3] uniform in m holds in char 0 once all 254 cases are
 unit in both charts at the same prime (currently 252/254 in A and 249/254 in B; VF-SYM-DC3 and VF-SYM-DC3-B open)", or prove the remaining
 cases over Q (char-0 elimination in t), or show that each unit case is closed. Until then label SYM-M [DC3]: [modular, P1, 7 cells open], no
 char-0 content yet. (The "special value" caveat was only part of the issue; the stratum issue is the main one.)
STATUS 00:03: TARGET 2 -- LEMMA S2 VERIFIED AT P1 by an independent generator (verify2/r13/s2chi_mine.py): chi-coordinates with structure constants
 computed from chi_k(r) = i^{kr} (all rational, asserted), the column-centred permanent formula (my r11 identity) SELF-TESTED against a direct
 permanent on random data; same normalisations as stage3 (b2 = w(t2) by scale, b3 = be w(t3), both finite by the 6-point orbit; a-charts v a_k = 1).
 Results at P1: neq (u be (t2 - t3) = 1) charts 1, 2, 3: UNIT (122 s, 121 s, 96 s); par (t3 = t2, u be (be - 1) = 1) charts 1, 2, 3: UNIT (< 1 s);
 CALIBRATION (u be = 1, t2 = t3 allowed, chart 1): NON-unit, dim 1 (= the S2= family b2 = b3) -- matches stage3. Over Q: running (s2c_Q.log).
 (My first, standard-coordinate generator s2_mine.py was too slow (> 12 min per chart) and was stopped; no verdicts from it.)
 Reductions in the lemma checked: neq u par covers "both b nonzero and b3 != b2"; row S_4 moves both b-lines to finite t; S_4 on columns 0..3 transports
 S2 to any column pair {c,d}; a = s/2 != 0 in every use.
 (alpha1) supp 2 cases (c1)/(c3): my generator also at P1: 12/12 UNIT. (alpha1) supp 3: my 48 systems being re-run at P1 (a1p.log).
 => [T31] SPLIT A FOR m0 AT P1: (alpha0) [V-r11/r12 + stage3 P1 conversion], (alpha1) supp 3 [V-r12 c0; P1 stage3 + mine running], supp 4 [hand V-r13 +
 S2 at P1 V-r13], supp 2 [hand V-r13 + S2 + S-SPEC (P1, stage3) + (c1)/(c3) at P1 V-r13]; (beta) 32/32 at P1 (audited r11). With split B (hand, r10):
 [T31] for m0 is COMPLETE AT P1 (modulo my P1 re-run of supp 3, consistent with stage3's 96/96 at P1). (SL_m0) at P1 still needs [DC3] (6 cells)
 and [T22] (5 cells); then RED-p gives char 0.
STATUS 00:06: [T31] split A for m0 -- ALL PIECES RE-RUN AT P1 WITH MY OWN GENERATORS: (alpha1) supp 3 48/48 UNIT (a1p.log); (alpha1) supp 2 (c1)/(c3) 12/12;
 LEMMA S2 6/6 (+ calibration non-unit); (alpha0) supp 4 (3 W) 3/3, supp 3 36/36, supp 2 P2 18/18, Lemma S-SPEC 3/3 charts (verify2/r13/a0P1.log, 60/60).
 The special-W enumeration transfers to P1 (the six special lines stay distinct mod P1 = 1 mod 4; the deciding values -8, 2, lambda entries +-1, +-i
 are P1-units). Hand steps (shape S, S2 uses, supports, configurations) are valid for p > 7. Together with split B (hand, any p > 7) and (beta) 32/32
 at P1: [T31] for m0 is COMPLETE AT P1 by my independent verification of every piece.
STATUS 00:07: round 13 closing. RESULT block, PROOF-MAP.md, ledger and errata [L], [M] written. Running (mine): verify2/r13/run_s2c.sh over-Q
 stream for LEMMA S2 (6 systems, <= 28 min each, ulimit 2 GB, log s2c_Q.log). par chart 1 over Q had been running about 10 min with no verdict
 (mod p it takes 0.3 s).

# ROUND 14 (start 00:09 UTC). Targets: (1) PROOF-MAP current (T31 m0, SYM-M, rows 3COL, reg2 SK3, ncol chain); (2) reg2 r10 (SK3, six double
#  deformations, (ii-g) curves, double-deformation bound); (3) rows R12 (3COL, A1/A2 exact, R12.5 criterion); (4) ncol N1 (C1-C4) and the chain;
#  (5) Lemma S2 over Q.
STATUS 00:09: round 14 started.
STATUS 00:10: TARGET 4 ncol (NOTES-ncol RESULT round 1, N1):
 N1.0 descent VERIFIED (defect of a subspace <= defect; defects strictly decrease; (4,0) = SL).
 C1 / N1.1 VERIFIED: under (DI_5;e) the Hyperplane Lemma (R4.1, V) gives C(H) = C(L') for every hyperplane, so neutral columns of H = those of L'.
   "NCOL for SOME hyperplane" IS enough and is equivalent to (N_e+) for L' -- no weaker requirement, only freedom of choice. The chain
   (DI_5;e) + (N_e+) + (NC'_e at dim e+4) => (DI_5;e+1) is R7.2(c) (V-r8) restated.
 C2 / N1.2 VERIFIED: neutral n: dim Q >= 4 + e^col(Q) (R4.10(b)); (Q^T|0) is a (dim Q, e^col) space (R4.10(c)/R5.3(a)); e^col = 0: SL; 1, 2: (DI_5;3)
   via descent; 3: dim Q >= 7 > 6 = L_gct_214. R6.3(i) ERRATUM RESPECTED: (DI_5;3) (no (4,0), (5,1), (6,2)) is assumed explicitly; (DI_4x4) is
   correctly NOT needed separately (its e^col = 1, 2 cases are the floors, e^col = 3 is L_gct_214, e^col = 0 is padding/SL).
 C3 / N1.3 VERIFIED, ONE WORDING SLIP: the four configurations are right, but "saturated (X_n = (C^col + C1)^perp exactly)" holds for (a), (b), the
   dim Q = 5 option of (c) and (d); the dim Q = 6, X_n = 0 option of (c) is NOT saturated (3 - e^col = 1 != 0). Harmless for the list.
 C4 / N1.4 VERIFIED (hyperplane through e_i (x) C is (6,3) with C(H) = C; FS-DEC gives C = V_A + V_B, w ~ |B| 1_A - |A| 1_B; lift of dim 8 contains
   e_i (x) C (+) e_r (x) C w with C o w = C (w constant on the blocks), FL2* => dim <= 7). Isotropic w not covered (as stated).
 C5 / N1.5(a) VERIFIED (FS-DEC e = 2 list; neutral columns excluded; W = (C + C1)^perp 2-dim; e_a - e_b in C o W via x with x_a = x_b = 1 (exists since
   u is not ~ 1_A); u_A o W 2-dim (u_A zero-free, x_A determines x); dim(C o W) = 3 => FL2* => <= 7 < 8). (b) uses C4 + RS-HYP (V). VERIFIED.
 THEOREM N2 (configuration (a)): the computation is RED-p-valid (Q in Gr(3,8), all 56 Pluecker charts, integer coefficients reduced mod p, no
   saturation/open condition, 3 primes, calibration non-unit 32/56). The hand reduction N2.1-N2.3 (pencil argument (i)-(iv)) NOT re-derived
   this round -> CL.
STATUS 00:12: TARGET 2 reg2 round 10:
 LEMMA SK3 VERIFIED. (i) P_1 = S(Bw) = 0, P_2(X_w) = -<w,Bw> => B skew, unique 5x5 skew K with K1 = 0. (ii) the (2,1)-part of P_3 on (X_w,X_w,Z) is
   E(Bw,w,zeta) = 2 w^T diag(zeta) K w; DK - KD is symmetric with zero diagonal, a symmetric form vanishing on 1^perp is u1^T + 1u^T, diagonal => u = 0,
   so [diag(zeta),K] = 0. (iii) block-diagonal along level sets, rank K_S <= 2 floor((|S|-1)/2), total <= 2 for every partition with >= 2 parts.
   (iv) polarised P_2 (X_w, Z) = -<w, z_j + zeta> - <Kw, z_r + zeta>, z_r in C1 drops (S(Kw) = 0), so pi(z_j + zeta - K zeta) = 0 and with zeta constant
   z_j is constant; shape (iv) re-derived (lam = -a-b by P_1). Exact part: logs r10_sk3_{A,B,C,D} std = (1) (1-2 s); echelon pivot pairs
   (a,b),(a,p0),(b,p0),(p0,p1) cover Gr(2,7) up to S_5 (which preserves the shape); calibrations with the rank condition removed are still (1)
   (so the choice of Pfaffian is irrelevant). Scope: full 4-dim blocks only (as stated).
 18.1 DOUBLE DEFORMATIONS (six families), rank q >= 3: VERIFIED at log level: all CAL lines are localisations only (non-vacuous), lifts unique,
   rank<=2 locus (1) on every chart; chart unions cover t != 0 (row 0->3 + col 0->1: everywhere); t = 0 = single column deformation (16.6).
   d = d_1 in T_1 CHECKED by my criterion (d_r in T_1 iff M with row r zeroed is level): for row 0 -> 2, 3 row 1 carries only single-row
   elements; for row 0 -> 1 the zeroed space lies in the single column-deformed family (the t = 0 slice), which is level.
 Double-deformation bound dim T_1 <= 10: minors logs (r9_double_*, r10_double_*_0_3) leave only t2 = 0 (single row deformations, 16.2/16.6) and
   (0,0): VERIFIED at log level.
 18.5 (ii-g) curves: CL; parametrisation audited: b = <q,q> p - 2<p,q> q is the stereographic parametrisation of the isotropic conic from p (p not
   on the line of q's; s = -w^2 gives b ~ p; s = infinity gives (1,0,w^2,w)) -- complete. OPEN POINT (not addressed in the notes): c is taken
   as c_h(s) from the lex GB "c3 h(s) - g(s), ..."; at the (finitely many) roots of h(s) (and of the other leading coefficients) the fibre of
   rel01 over b = x(s0) may contain further c. Needs one more check (fibres over the roots of h), else the curve cover is incomplete there.
STATUS 00:15: TARGET 4 cont. (coordinator's specifics):
 THEOREM N2 (configuration (a)): INDEPENDENT GENERATOR (verify2/r14/iv2_mine.py): rows of Q in U = {sum 0, x_0 = x_1}; Q LEVEL via the full
   expansion perm(J4 + q) - 24 and every 3x4 row deletion level via P_1, P_2, P_3 computed DIRECTLY from subpermanents (not via the dot/tau
   identities ncol used); Q in Gr(3,8), all 56 Pluecker charts (identity on the 3 pivot coordinates). Result: UNIT in 56/56 charts at
   P1 = 2147483629 AND at 2147483497; CALIBRATION (U = span(chi, e_0 - e_3), i mod P1): NON-unit in 32/56 charts (same count as ncol), chart 024
   = the point C^{012} (x) chi (dim 0). RED-p STATUS: VALID -- the 56 standard charts cover Gr(3,8) (some 3x3 Pluecker minor is nonzero); the
   conditions are polynomial identities in y with integer coefficients (u1, u2 integral, no constants), the incidence set is closed, no
   saturation, no open condition; "two equal columns" = rows in U is a LINEAR (closed) condition. One prime suffices; two agree.
   Hand reduction N2.1-N2.3 re-derived: (L2)/(L3) by the deletion-sum trick; dim R = 1 forces rho_0 ~ chi (some coordinate projection of A is
   onto) and A = C^S (e_4(a) == 0 on a 3-dim A), giving the e = 3 space; dim R = 2: Adj(q) v = 0 from C(L') = U = {1,v}^perp, (D2) => beta(r_i, sigma - r_i)
   == 0; pencil cases (i) two squares => at most two nonzero rows on fixed lines, dim Q <= 2; (ii) common factor l => one nonzero row; (iii) a
   line inside the conic of squares cannot exist; (iv) beta = lambda g: d o U inside span(1,d); zero-free d gives b = 1 in U (impossible); two zeros
   give v ~ e_a - e_b, equal columns. (The one-zero and three-zero sub-cases of (iv) checked in outline only.) => THEOREM N2 VERIFIED.
 N3 DUALITY: TRI symmetric under (Q, Xh, Wh) -> (Q^T, Wh, Xh) because Adj(q^T) = Adj(q)^T and J^T = J -- correct as a symmetry of R5.1's criterion
   (R5.1 V-r9); the step "L'' := (Q^T|0) + (0|W_0) is level with C(L'') perp X" needs R5.1 in the form "level <=> TRI for Xh and SOME Wh containing
   C1 and contained in (C(L') + ...)^perp" -- plausible, not re-derived line by line -> CL. N3.3 ((b) always untwisted) VERIFIED: e^col = 1 gives
   <sigma(q),mu> m(q) == 0, C[Q] a domain, so sigma(q) perp mu; sigma(q) perp 1 because Q is level (S(q) = 0) and X_n perp 1; so sigma(q) in X_n.
   (b) excluded GIVEN N3.1 (dual is (5, <= 1)).
 => leaf 6 (PROOF-MAP): (7,3) <= (DI_5;3) + (N_3+) [V-r14]; (6,2) <= (DI_5;2) + (N_2+) + exclusion of (c), (d) [(a) V-r14 via N2; (b) CL via N3].
STATUS 00:16: TARGET 3 rows R12:
 R12.5 (5,1) CRITERION VERIFIED: the linear defect part sigma - s_j lies in C m, so its kernel in L has dim >= 4 and equals the column-centred part
   (s_j = sigma for all j forces sigma = 5 sigma = 0); a 4-dim L'' between K and that kernel has C(L'') = C m (nonzero by SL), m in 1^perp. So "no
   column-centred (4,1) extension of K" => "no (5,1) space contains K". Clean.
 R12.8 LEMMA 3COL: the main statement (a 3-dim strongly level K on exactly three columns has a rank-1 column) VERIFIED: the conditions on three
   columns are exactly pairwise-skew Gram forms + tau = 0 (degree 4 vanishes because of the zero columns); (i) A_a invertible => A_b, A_c are cross
   products, and the Lagrange identity gives 2(beta.gamma) I = beta gamma^T + gamma beta^T => a zero column; (ii) rank-2 columns share their
   kernel (radical of the nonzero skew B_ab, which is nonzero because two planes cannot be orthogonal in a 3-dim nondegenerate V); (iii) three
   rank-2 columns would have a common kernel. The COMPLETION (classification A1, A2, family B) rests on R12.3/R12.4 (not re-derived): CL.
 R12.6 A1/A2 EXCLUSION VERIFIED by re-running rows' kgen.py (mode cc, over Q) with the gauge printed: gauge det = 2 for A1 and A2 (valid; the
   R12.7 trap does not apply), K strongly level check 0, unit in charts m_a, m_c, m_d; m_b, m_e by the symmetries a <-> b, d <-> e of K. (The
   classification of type-(A) x (famA2.py: the ten lines) is CL.)
STATUS 00:19: rows R12.3/R12.4 (completion of 3COL) re-derived at the structural level: columns a, b in x^perp (polarised G_ac, G_bc); the (a,b)-image of K
 is beta-isotropic in the 4-dim nondegenerate (x^perp)^2, so dim <= 2 and x e_c^T lies in K, K = P (+) C x e_c^T; for type (2,1) the row-sum-zero element
 has no column-c part (gamma <x,x> = 0), so n = d(e_a - e_b) lies in P with d isotropic in x^perp; with w_k = a_k d + b_k d': <d, w_2 - w_1> = 0 gives
 b_1 = b_2 = b and <w_1,w_2> = 0 gives b(a_1 + a_2) = 0 => (A) span{d(e_a - e_b), d'(e_a + e_b), x e_c} or (B) span{d e_a, d e_b, x e_c}. The isotropic-x
 case (3COL text) leads to family (B). => LEMMA 3COL classification VERIFIED (the cubic conditions fixing x in (A), e.g. x ~ d x d', taken as stated).
 TARGET 5: S2 over Q: my std run (par chart 1) was time-bound (> 19 min, 190 MB) and was stopped; Singular modStd(I,1) gives 1 in 1.3 s but its
 final test is VACUOUS for a unit ideal (G = {1} passes trivially) -> not a proof; slimgb over Q (exact): par chart 1 UNIT in 89 s (179 MB).
 Remaining 5 charts with slimgb running (s2slim.log, <= 28 min each, 2 GB).
STATUS 00:25: OPEN POINT on reg2 (ii-g) RESOLVED by my own check (verify2/r14/g1/: reg2's g1_solve.sing system, rel01 with b = x(s), lex order c2 > c3 > s,
 Singular over Q(w)): the curve K is irreducible of dim 1 (minAssGTZ: one component); its lex GB has 3 elements: c3 h(s) - ..., c2 h2(s) + ..., and a
 quadratic one; h(s) = 3s^4 + (4w+8)s^3 + (4w+14)s^2 + 12s + (3 - 3w), h2(s) = s^2 - (2w+2)s - (w+2); K + (h) and K + (h2) are the UNIT ideal, so
 h, h2 never vanish on the curve and c is a FUNCTION of s there. The parametrisation c = c_h(s) misses nothing in this chart (the other c-chart is
 covered by reg2's closure argument). => R10-2 (ii-g) cover VERIFIED (cover logic + fibre check); minor runs at log level. Errata [P] closed.
STATUS 00:25: ncol N3.1 (duality) now VERIFIED: R5.1 (V-r9) characterises "L' = (Q|0) + (0|X) level with neutral column n and W_0 perp C(L')" by "Q level and
 TRI(C1 + X, C1 + W_0)" for an ARBITRARY W_0 inside 1^perp (it comes from the lift identity perm(J - E + [[q,x],[w_0,0]]) = 120 + (1+x)^T Adj(q) w_0, valid
 for every w_0). With Adj(q^T) = Adj(q)^T, TRI(Q; Xh, Wh) <=> TRI(Q^T; Wh, Xh), so L'' = (Q^T|0) + (0|W_0) is level with X perp C(L''): dim L'' =
 dim Q + 3 - e, e'' <= 3 - dim X. N3.2(a): (4, 0) -> SL; N3.2(b): (5, <= 1) -> no (5,1). => configurations (a) (second proof) and (b) EXCLUDED.
STATUS 00:37: TARGET 5 final for this round: LEMMA S2 over Q -- parallel case UNIT in all 3 a-charts (slimgb, exact over Q: 89 s, 9 s, 140 s;
 <= 202 MB) = an independent char-0 confirmation of that half (stage3's slimgb runs agree). Non-parallel case: chart 1 slimgb plateaus at
 1.4 GB after 15 min under the 2 GB cap (still running, last job of mine, ends by its 28-min timeout; log verify2/r13/s2slim.log); stage3's
 neq runs halted at their cap too. Big slot: QUEUE line "verify2 | S2-Q-NEQ" (6 GB, <= 1.5 h per chart, 3 charts), low priority because the
 proof of [T31]-m0 uses Lemma S2 at P1 inside the complete P1 case split (RED-p), not char 0.
 Round 14 closing: RESULT block, PROOF-MAP.md (leaf 6 chain, 3COL, SK3, double deformations, (ii-g)), ledger, errata [N]-[P] updated.

# ROUND 15 (start 00:38 UTC). Targets: (1) rows R13 (d = u line, family B, special locus, R12.9 incompleteness; is leaf 3 closed?); (2) stage2 target 3
#  (D003-PROP Case A) + F2col v3 rulings (RED-p / char-0 status); (3) stage3 sec. 36 ((PR3) stratum (II), leaf-8 case list); (4) ncol round 2
#  (R2.1-R2.6, (CC3) reductions); (5) Lean statements: leanzbf T1 vs T1Hyp, leanfl TC5_P3 vs DI5.3 (P3).
STATUS 00:38: round 15 started.
STATUS 00:45: TARGET 1 rows R13 (leaf 3):
 R10.7 normal form (two-column (2,1) kernels) now RE-DERIVED: on two columns strongly level = column-centred + beta-Lagrangian (beta = <y_a,y_b'> +
   <y_a',y_b>; in P = y_a + y_b, D = y_a - y_b: beta = (<P,P'> - <D,D'>)/2); type (2,1): L cap {P = 0} = C(0,2d), d isotropic; every D in the D-image is perp d,
   so the D-image (dim 3 - dim(L cap {D = 0})) lies in the plane d^perp and L contains (2u, 0), u isotropic (exactly one such line); the third generator
   gives (p+e, p-e) with u.p = d.e = 0, p.p = e.e. VERIFIED.
 R12.10 (generic two-column kernels, m_a = m_b = 0) VERIFIED by re-derivation: (1) K-K-Z with m_a = m_b = 0 gives z_t = m_t zeta; (2) the (1,1) vector is
   (0,0, m_t X - beta) with X = <k_a + k_b, zeta>, so 3 beta = 0 and the Lagrangian property gives z_a = z_b = 0 mod K; (3) the (2,0) part forces
   zeta isotropic; (4) e_2 != 0 gives zeta_r^2 const, hence zeta = 0; e_2 = 0 gives m ~ (1,w,w^2) on {c,d,e}; (5) the (1,3) part gives phi(k_a) = phi(k_b) = 0,
   (prod_{s != r} zeta_s)_r in C1, so zeta = 0. (The (1,2) component formula 2 e_2 tau taken as stated.)
 R13.1/R13.1' (family B) VERIFIED: the (1,1) vector of a single-column element y e_j re-derived (entries -<R - z_j - z_k, y>, 0 at j); chart A:
   all z_k perp d, Z mod K as stated; chart D: z_a, z_b in {d,x}^perp = C d, <z_t,d> = mu m_t, Z = d a^T + mu' s m^T; RE-RUN of rows' bred.py over Q:
   chart A (finite, infinity) and chart D (finite, infinity): UNIT after Z != 0 saturation (saturation by the irrelevant ideal of the Z-cone: fine).
   Cover: m_a (A), m_b by a <-> b, m_a = m_b = 0 with m_c (D), m on {d,e} two-column (TC5). Degenerate gamma = (1,2) stratum.
 R13.2 (line d = u) VERIFIED: chart m_a != 0 by hand (R12.11: z_k = tau_k u, z_a in u^perp, then the K-K-Z cubic with t(p,u,u), t(u,u,u) not both 0
   kills tau); charts B, C re-run over Q (ured.py): B unit (finite, infinity); C finite: after Z != 0 sat dim 1, after sat by m_d m_e unit (only
   two-column m -> TC5); C infinity unit.
 R13.3 special locus: classification CL (Groebner over Q(i) by rows, not re-run); the 16-point x 2 e-sign x 2 chart RED-p cover at P1 is RUNNING
   (kSP1.out: 11/64 unit so far, gauge dets printed nonzero); RED-p argument checked: finite point scheme over Z[1/2], Z-cone saturation is by the
   irrelevant ideal, m-charts m_a, m_c + the e-sign flip (a <-> b) and S_3 on {c,d,e} cover P^4.
 IS LEAF 3 CLOSED? NO. Remaining: (a) the 16 special points (RED-p cover at P1 running, 53 charts to go); (b) (2,1) kernels supported on FOUR or FIVE
 columns -- never classified (rows' own statement; numerical census R13.4 only). Everything else in leaf 3 (two-column generic, line d = u,
 three-column A1/A2/B) is now VERIFIED in char 0.
STATUS 00:48: TARGET 3 stage3 sec. 36 (round 16):
 Tools (i)-(iv) VERIFIED: orthogonality of single-row vectors of different rows (P_2 of a 2-row element) and tau = 0 for three rows (P_3);
   RANK-ONE FAMILY LEMMA (P_j(c (x) m) = j! e_j(c) e_j(m); the alpha c_T coefficient of sigma_{t+1} is t! (-1)^t <z, m^t> because e_t(m minus entry j) =
   (-1)^t m_j^t when e_1..e_t(m) = 0; t <= k for outside rows, t <= k-1 inside); e_1 = e_2 = e_3 = 0 => >= 4 distinct nonzero values (Vandermonde),
   so 1, m, m^2, m^3 independent with a LINE as orthogonal complement; e_1..e_4 = 0 => Fourier vector, powers a basis; dim(T o T) = 3 for totally
   isotropic T (Z22, V-r7) so tau|_T != 0.
 THEOREM SR5 VERIFIED: case split on the number of non-isotropic vectors re-done (>= 3 impossible by dimension; 2: three parallel isotropic + two
   non-isotropic in the line, contradiction; 1: k = 4 + outside vector; 0: plane T, distributions with a line of >= 4 (iii), (3,2) exact, and
   at most 2 per line -- I checked that tau vanishes on T for (2,2,1), (2,1,1,1), (1^5)). (3,2) by MY OWN generator (verify2/r15/sr32_mine.py:
   direct S_5 permanent expansion, all c-coefficients; charts m_k = 1 x minors of (m, m') != 0, no isotropy imposed): 20/20 UNIT over Q;
   calibrations (2,2), (3,1), (2,1): NON-unit (dims 2, 2, 4 in my normalisation).
 THEOREM SR2111 VERIFIED: Z nondegenerate (three orthogonal vectors in a nondegenerate plane are parallel isotropic; Z in the line); Z rank 1
   (at most one w with a y'-part; all along n gives k = 4 and z' parallel to n since n lies in the line orthogonal to 1, n, n^2, n^3); Z totally
   isotropic (three lines => tau|_Z = 0 against (iv)); remaining configuration C* by MY OWN generator (verify2/r15/c_star_mine.py: chart cover
   n_0 = 1 by S_5, gauge z'_0 = 0, z'_1 = 1 by S_4, w_k = 1, w not parallel to n via the minors): 20/20 UNIT over Q; calibration "drop row 3":
   NON-unit, dim 2.
 FOURIER LEMMA VERIFIED (coefficients <v + w, m^t> = 0 (t <= 3) and <v, m^s> = 0 (s = 1..4); dual relations <m^a, m^b> = 5 la^{a+b} delta; v = la' 1,
   w = -la' 1 + mu m; sigma_2(la'(e_o - e_j) (x) 1) = -20 la'^2).
 LEAF 8 now: impossible (1,1,1,1,1), (2,1,1,1,1) [SR5], (2,1,1,1,0) [SR2111], two 2's [Z22], (1,0,0,0,0) [F4b-X] -- all V; OPEN (1,1,0,0,0), (1,1,1,0,0),
   (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0), (2,0,0,0,0) = (S3-a).
STATUS 00:49: TARGET 4 ncol round 2:
 R2.1 VERIFIED (strong levelness is pointwise, so a generic strongly level 3-dim subspace of the 4-dim ker c would make ker c strongly level, against SL).
 R2.2 VERIFIED (Gamma(C) is a unital subalgebra of C^5 = span of block indicators; e = 3 nontrivial => two blocks, w ~ |B| 1_A - |A| 1_B, non-isotropic).
 R2.3 VERIFIED (on ker c, y^i = -alpha 1; alpha != 0 would give a zero row of J + Y, killing every deletion permanent against sum C_j = 120; the identity
   <u, C(Y) - 24*1> = <y^i, D_i(Y) u> uses that the cofactor matrix D_i(Y) is symmetric and D_i(Y) u lies in C, perp 1).
 R2.4 (A), (B) => (CC3) VERIFIED: (F1) (R4.15, V) gives d o u in C and d.u = 0, hence D_i perp U_i + U_i o w (since <d, u o w> = <d o u, w> = 0); (A) d o C in C
   forces d in Gamma(C) = C1 (isotropic w); (B) U_i + U_i o w = 1^perp; then R2.3 + (DI_5;3) make ker c a column-centred (4,1) space with a zero row, i.e.
   a column-centred 3x5 level space of dim 4 with defect <= 1 = (CC3). R2.4' (isotropic w, w not in U_i -> same) VERIFIED; case (C) open (as stated).
 R2.5 VERIFIED symbolically by hand: <nu_1,nu_1> = <nu_2,nu_2> = 0, <nu_1,nu_2> = 1, tau(nu_1^3) = 3, tau(nu_2^3) = 1/9, mixed taus 0 => P_2 = 3(sum a beta - AB),
   P_3 = 6(e_3(a) + e_3(beta)).
 R2.6 / R2.6' (degree-2 pencil analysis): case (i)/(I) re-derived (three pairwise independent rank-<=2 members force all factors into a 3-dim U,
   no member vanishes as lambda, mu are independent), case (III) re-derived; (II-a)/(II-b) (nodal cubic, pairing lines) read, not re-derived.
 THEOREM CC3 (R2.10): CL -- hand case analysis partly re-derived ((I), (III)); the three survivor systems (survivors.py) not re-run this round.
 R2.8 second route to "no (7,3)" (via (SR3)) VERIFIED as a reduction (Lifting R4.7: u_i <= 1 everywhere gives a single-row-free generic hyperplane).
STATUS 00:50: TARGET 2 stage2 (R14):
 D003-PROP Case A (R14-4, R14-5): coverage argument VERIFIED (S_4 on columns 1..4 gives alpha_1 = 1, a2 != 1, alpha_4 != 0 unless alpha has two zero entries,
   i.e. alpha ~ X0 = (1,-1,0,0), killed exactly in R10). RED-p / char-0 STATUS: the parametric runs use AFFINE parameters (a2, a3) with Rabinowitsch
   exclusions (a2 = 1, alpha_4 = 0, rank-jump (a2-1)^3), so the mod-p verdict (70/70) proves the kill only for alpha_0 that are integral at a prime
   above p AND whose reduction stays off the excluded loci (a2 - 1 and alpha_4 units at that prime) -- slightly more than the "p-denominator
   loophole" stage2 names. The char-0 run is msolve multimodular (70/70 [1]) = EVIDENCE, as stage2 itself says ("evidence-grade as in R11-5").
   So "TARGET 3 CLOSED" should read "closed at P1 for all but finitely many-prime-special alpha; char 0: evidence". A proof would need
   Singular/slimgb over Q on the 70 charts (affine unit over Q is exact in char 0) or a proper (projective) parameter formulation.
 F2col v3: ruling-2 slice (nu free, Z FIXED at a = (1/3, 2/5, -1/2)) 70/70; ruling-1 slice (lam free, Z fixed) 68/70 + 2 FAILED (memory). STATUS:
   these are one-parameter SLICES of a 4-parameter family (Z fixed), mod p with affine parameter + exclusions -> evidence for the slice, no
   statement about the family; the full family run (ST2-F2COL on v3) is RUNNING. No char-0 content yet.
STATUS 00:51: TARGET 5 Lean statements (read only, nothing compiled):
 leanzbf T1Hyp (lean/zbf/FrameR5.lean:7080) MATCHES stage2's T1 (sec. 4): Lev 5 L, finrank 9, three distinct rows with ZF (ZF r = "row projection
   of rank >= 4 and every annihilator kappa with kappa.1 = 1 is zero-free", i.e. a_r = 1 with zero-free annihilator; the a_r = 0 case is vacuous /
   excluded by FK), the three pair intersections of dim 2 (minimal pairs) => rowsZeroS L {r1,r2,r3} != 0 (= X_123 != 0). The proof term is t1_proof
   (round 7; compile pending in window 2).
 leanfl TC5_P3 (lean/fl/p3c.part) MATCHES DI5.3 (P3): for any K with defect line C(e_a - e_b) (DefLine K mTC), dim Nbar = dim (K cap ker rs) mapped by
   nbarL <= 2, i.e. dim Nbar = 3 is impossible. The statement does not assume dim L' = 5, which is fine because (P3)'s argument uses only the shape
   of a 3-dim Nbar. The chi_1-type pair (verifyfl correction 00:25) concerns the proof (three pairwise related lines), not the statement.
 TARGET 3 addendum: (PR3) formulas 36(A): D_2(x) = sum_i s_i r_i + 2 sum_{i<k} r_i o r_k re-derived from P_2 of the 3x4 deletions (total sum 0, constant part =
   P_2(x) = 0); c(x) = -(r_0 + r_1 + r_2) is the degree-1 part. D_3, stratum (II) on H and (F): not re-derived (no theorem is claimed there).
STATUS 00:52: round 15 closing. RESULT block, PROOF-MAP.md (leaf 3, leaf 8, leaf 6 round 2, Branch 3, Lean statements), ledger written. No jobs of mine
 running (S2 over-Q chart 1 halted at 1.42 GB after 1509 s; queued as S2-Q-NEQ).

# ROUND 16 (start 00:53 UTC). Targets: (1) ncol CC3 case (II) + three survivor GBs + R2.14 (split (5,1), zero-free m) vs leaf 1; (2) D003-PROP Case A over Q
#  (size 1-2 charts under 2 GB); (3) Lean audit of compiled R7s_t3 / FLn: stubbed hypotheses; (4) verifyfl SYM [DC3] 'ne' pieces, stage2 F2col v4,
#  reg2 round 11, stage3 (PR3) stratum (II).
STATUS 00:53: round 16 started.
STATUS 00:54: TARGET 1 ncol CC3 / R2.14:
 CC3 case (II) re-derived structurally: lambda = c mu; T = {j : m_j = -c}; off T {alpha_j, b_j} ~ factors of mu; on S'' (kernel of the factors, dim >= 2) a^ lives
   on T_a, beta^ on T_b; (II-a) c != 0: sigma_a ~ l, sigma_b ~ l', so on S'' both are sum-zero and F3 = e_3(a^) + e_3(beta^); dim S'' <= (|T_a|-1)_+ + (|T_b|-1)_+;
   spot checks: (3,1) gives e_3 != 0 on V_3; (4,0): on V_4, p_3 = 3(x_a+x_b)(x_a+x_c)(x_a+x_d) (checked), so a 2-dim image is a pairing plane -> survivor;
   (II-b) the cubic 9 p_3 = p_1^3 on P^2 has a single singular point (1:1:1) with two distinct tangents (ordinary node) -- checked: hence irreducible,
   no line; G(e_j) = 8/27 checked. Remaining (II-b) sub-cases taken as stated.
 The three survivor systems (ncol/cc3/survivors.py, sympy GB over Q) RE-RUN: (4,0) [1], (2,2) orient 0 [1], (2,2) orient 1 [1].
 => THEOREM CC3 VERIFIED (case analysis + survivor GBs), with the minor (II-b) sub-cases as stated.
 R2.14 VERIFIED given CC3: (F1) gives c^(i)(Y) in Gamma(C) = C1; R2.3 gives a zero row and defect in rad C (dim <= 1); dim ker c >= d - e >= 4 contradicts CC3.
   e = 1: Gamma(Cm) trivial iff m zero-free. LEAF-1 SCOPE: this covers exactly the SPLIT (5,1) spaces (a row carrying the defect line, i.e. e_i m^T in L')
   with |supp m| = 5, isotropic or not. Together with SPLIT (non-isotropic m, any support) and TC5 (|supp m| = 2), the split case is left only for
   ISOTROPIC m with |supp m| = 3 (one m up to symmetry: (1,w,w^2,0,0), covered by the iso typed systems at P1) or |supp m| = 4 (a 1-parameter family:
   OPEN). The NON-SPLIT (5,1) spaces for general m are untouched by R2.14.
STATUS 00:59: TOP PRIORITY (coordinator): verifyfl R11.6 (SYM-M targets (5,1) directly, whole cover at P1, no runs over Q). AUDIT:
 (a) PROPERNESS / SPECIALISATION: VERIFIED. Y_5 = {(L', m) : L' in Gr(5, 4x5), m in P(W_P), defect(L') in C m} is closed (rank[c(Y); m] <= 1 for all Y; level
   follows from sum_j C_j = 120 since m is in 1^perp), so proper over Z_(p); a Q-bar point reduces to an F_pbar point (L'', m''). If m'' is two-column:
   TC5 in char p. Otherwise the linear part sigma - s_j lies in C m'', so the column-centred part K of L'' has dim >= 4 (s_j = sigma for all j => 4 sigma = 0,
   p != 2), and any 4-dim K4 inside it is an F_pbar point (defect in C m'', possibly 0) of some [DC3]/[T22]/[T31] case system with m'' off the
   two-column points (types (0,4),(1,3),(2,2),(3,1) exhaust q + d = 4, q <= 3; (F2)-(F4) valid for p > 3). So: all case systems with no F_pbar point
   off t(t+1) = 0 in charts A and B (UNIT, or UNIT after adding u t(t+1) - 1 -- legitimate inside char p) + TC5_p => no (5,1) with |supp m| <= 3 in char 0.
   This is a WHOLE-COVER statement at one prime (no per-case transfer): consistent with errata [L],[M]. Charts A, B cover P(W_P) (A misses only
   (0,1,-1) = B at t = 0). |supp m| = 3 special values (iso, repeated entries) are inside the symbolic cover (R11.1) or handled by fixed-m systems
   at the same prime (R11.11). Column symmetry gives every 3-column support.
 (b) TC5 IN CHAR p: the two flagged steps RE-CHECKED by me mod P1 (verify2/r15/tc5p_mine.sing): gcd(th^4+4, th^8-56th^4+16) = 1, both squarefree,
   values 4, 16 at th = 0 (the chi_1-type pair th = 0 / inf is disjoint); the cubic (x+y)(y+z)(z+x) - xyz has affine singular locus {0} mod P1 (and
   in char 0), i.e. a SMOOTH plane cubic: irreducible, no line. EXTRA CHECK (mine): the S7 (II-a) / (P3) pair equations tau(v v'^2) = tau(v^2 v') = 0
   for v = w(a), v' = w(b) have the SAME zero-dimensional solution count over Q(i) and mod P1: finite chart vdim 17, the two infinity charts vdim 1
   each -- no extra related pairs appear mod P1. My scan of DI5.3 found no other non-algebraic step (all other steps: polynomial identities, ranks,
   nondegenerate forms, Newton with small divisors). REMAINING: blueprint S4-S8 is Lean-checked over C, which does NOT by itself transfer to
   char p; its pair list (S7 II-a) is now checked mod P1 as above; the other blueprint steps look algebraic but I have not read them line by
   line this round. Status: TC5_p VERIFIED modulo a char-p reading of blueprint S4, S6, S8 (S7's pair list is covered by the check above).
 (c) R11.11 VERIFIED: split A gives Z = v l^T with l supported on P; all l_j != 0 => v = chi_1 (symbolic chi_1 system); l = e_a - e_b: m_a != m_b and
   m_c != 0 => R8.2(ii) (hand, p > 3); m_c = 0 => two-column (exempt, TC5_p); m_a = m_b => m is the m11m2 point up to column permutation and scale,
   whose R2 systems are unit at P1 (round 8). So the symbolic R2 systems are not needed.
 (d) R11.8 certified minors VERIFIED from gen_sym.py's bases: chart A W = {e3, e4, (-t,1,0,0,0), (1+t,0,1,0,0)} (perp to (1,t,-1-t,0,0)), minor on columns
   1..4 is a permutation matrix (det +-1) for every t; chart B W = {e3, e4, (1,-t,0,0,0), (0,1+t,1,0,0)}, columns (0,2,3,4): det +-1. So "W C = 0 <=> C in C m"
   at every parameter value in every characteristic.
 CURRENT SYM-M LEDGER at P1 (verifyfl): [DC3] all unit except A0-ne, B0-ne (big slot); [T22] charts A/B cases 95..12 done except FAILs (A 21, 18;
   B 45, 21, 18) and cells 11..0 open; [T31] split A complete; split B not built. => (5,1) for |supp m| <= 3 in char 0 is OPEN pending these
   pieces + the S4/S6/S8 char-p reading.
STATUS 01:01: TARGET 3 Lean audit (what compiled, what is assumed):
 leanzbf R7s_t3.lean (window 2, exit 0, 921 s): a STUB TEST FILE -- 484 'sorry' occurrences (the supporting lemmas of earlier rounds, statements
   identical, proofs in earlier files), final theorem 'PEqualNP.Outside.L_gct_210 : True' (hence "does not depend on any axioms"). What it checks:
   the new blocks t3_trans (305 leaves) and the reductions T3Rest -> T1Rest3 -> T1Hyp and T3Rest2 -> T3Rest. T3Rest2 itself is a HYPOTHESIS here
   (t1_of_t3rest2 (h : T3Rest2) : T1Hyp); its proof (r7_1..r7_7: lemB, orientation bridges, t3f2_proof : T3F2, t1_proof : T1Hyp) is NOT compiled yet
   (window-3 files R9d.lean / R7c.lean). So "no sorry" is not accurate for R7s_t3; "0 errors" is. T1 in Lean = conditional on T3Rest2 until window 3.
 leanzbf R6t_stub.lean: compiled except the generated dispatch t1_IIi (4 heartbeat timeouts; repaired, recompile in window 3).
 leanfl FLn.lean: final theorem = SL /\ FL row /\ FL col (as FLk, which compiled with standard axioms); 0 sorry; HypS6/S7/S8/S7alg/IIa are Prop
   definitions that are PROVED in the file (not assumed). The new parts (x5b, tc5c, x5c: X5_mc, TC5 pieces) are standalone lemmas NOT used by the
   final theorem; 29 localized errors being fixed. So nothing new is Lean-proved from FLn yet.
 => PROOF-MAP Lean line: compiled = Zbf round-3 statement (R0, ZBF, ThB, ...), FLk (SL, FL), T2/T2'' blocks (R6t_stub), t3_trans + (T3Rest2 -> T1Hyp);
   pending = T3Rest2 proof (-> T1), TC5/X5 pieces, everything else.
STATUS 01:05: E-STALE-OUTPUT exposure assessment (coordinator UPDATE 14). Tool: verify2/r16/stale_audit.py (for every surviving msolve input X.ms
 with an output X.gb/X.ms.gb/X.out: genuine iff mtime(out) >= mtime(in); a crash leaves the output OLDER than the rewritten input).
 RESULT over verify2, verifyfl, stage3, rows, reg2, ncol, stage2: 45 dirs, 5800 input/output pairs, ALL genuine, 0 older-than-input.
 Wrapper classes:
  SAFE (output removed first, or Singular read from stdout): stage3 gb/gbl.py msolve() (removes; a crash raises, no verdict); stage2 r13_F2col_v2/v3/v4,
   r14_D3A(_fx), r15_iso2row(_c0), r14_tworow, r15_tworow_lib, r11_charts_msolve (remove); reg2 SK/SK2/SK3, deformation and lift+Gram runs (Singular
   stdout); ncol gb/runall.sh (exit code checked); CC3 survivors (Singular); ALL my P1 covers of rounds 11-16 (r11-r16 scripts: Singular stdout).
  PATH-KEYED, no removal/no exit code (stale only if the SAME path held an earlier system and the later msolve crashed): verifyfl exactlib.run_msolve
   (all gen_* chains: [T31] m0, SYM-M [DC3]/[T22], the DC3 theorem cells), verifyfl r9/run_beta.sh ((beta) 32/32), r11/rab_test.sh, r7/subcut.py,
   cut_cell.py; rows r7/*charts.sh; my r7/dc3_split.py (exactlib), r8/ext_q.py, r8/ext_full_cell.py, vf/drive_A.sh; reg2 gb/polylib.run_msolve
   (/tmp/gb_<tag>; only three distinct constant tags in gen_dr22: harmless). For all of these the LAST run of every surviving file is genuine
   by the mtime audit. Residual exposure: a verdict logged from an EARLIER run of a path that was later re-run (crash + older output from a run
   before it) -- realistic only for patched re-runs under the same file names (e.g. after E-MSOLVE-BIGCOEFF).
  SHARED OUTPUT (c.out, no removal) = genuinely exposed beyond the first chart per process: stage2 r13_F2col.py (v1), r13_crosscharts.py,
   r13_crosscharts_sat.py, r13_crosscharts_sat2.py. None of the PROOF-relevant P1 covers came through these (F2col v1 rulings and the cross-chart
   runs are evidence-level; D003-PROP P1 came through r14_D3A, which removes c.out).
 => Decisive P1 covers ([T31] m0, SYM-M [DC3], (alpha0)/(alpha1), the DC3 theorem): no evidence of a stale read; the last runs are genuine. For a
   proof-grade record I recommend ONE cheap re-run with a patched exactlib (remove X.gb first, check exit code and mtime): verifyfl [T31] m0 pieces
   (R10.6 42 + R10.7 9 + rank-3 + (beta) 32 via run_beta.sh), the DC3-theorem cells (gen_n1s m12m3, 254 + the split cells incl. my dc3split_*),
   SYM-M [DC3] charts A/B (gen_sym_dc chain) and the [T22] rab_test systems. (alpha0)/(alpha1): stage3's runs went through gbl.py (safe) and
   my a0P1 re-run used Singular (safe): no re-run needed.
STATUS 01:08: stage3 sec. 37 (E) (PR3)/(PR2-split') COUNTEREXAMPLE: VERIFIED with my own code (verify2/r16/pr3_cx_mine.py, permanents over injections,
 symbolic rho): perm(J+X) = 60 and perm(J+N) = 120 identically (level); dim N = 5; row projections (1,2,2,2); single-row parts (0,0,0,2) = e_3 (x) Z only,
 none in rows 0-2 for rho not in {0,-1} (rho = 0 / -1 create one in row 2 / row 1); defect of X = 2, span(e_1 - e_2, e_3 - e_4) (= (Z + C1)^perp); defect of N = 4.
 So (PR3) ("3-dim 3x5 level, rows in 2-planes, no single-row element => defect >= 3") and (PR2-split') are FALSE as stated (ERROR in the statements,
 counterexample in stratum (III)). "(S3-a) <=> (PR3)" (PROOF-MAP leaf 7) must go: only (PR2-split') => (S3-a) was ever a reduction, and its hypothesis fails.
 HARMLESS FOR (S3-a) at the explicit members, EXACT (pr3_cx_t1.py): rho = 1, 2, 7/3: dim T_1(N) = 10 (N in rows 0-3 of 5x5), sigma_1 vanishes on T_1,
 the sigma_2 form on T_1 has rank 4 => a level L containing N (L c T_1(N), sigma_2 == 0 on L, so L totally isotropic) has dim <= 6 + 2 = 8. Matches
 stage3 (F) (disjoint-support member: T_1 = 10, FO2_0 = 8). Generic members (T_1 = 9): numerical only (stage3).
 CORRECTED ROUTE for (S3-a): (i) (PR3) on strata (I),(II) (all row projections exactly 2); (ii) stratum (III) (some pi_s(X_re) 1-dim): a complete
 classification (stage3's "general family" is derived by hand -- completeness not yet argued in the notes) and (iii) a uniform T_1 / FO2_0 bound on it
 (exact rank computation with the family parameters symbolic, or a whole-family certificate). (S3-a) remains plausible (all probes 0, the new family
 does not extend at the exact points). PROOF-MAP leaf 7 and the z = (2,0,0,0,0) entry updated.
STATUS 01:12: R11.6 audit, SCEPTICAL ADDENDUM (what the char-p statement really needs):
 (e) TC5_p contains Lemma SL in char p (TC5 = DI5.3 uses SL and its classification S4-S8). SL is Lean-proved OVER C (FLk); a Lean proof over C does
   not transfer to F_pbar, and char 0 => char p has no effective prime bound (the integer N in 1 = sum g_i f_i + N over Z is unknown, P1 could divide it).
   So SL_p needs its own reading. The risky steps are exactly the "finite solution list / no common root" claims (each a resultant or Groebner
   computation over Q, whose integer content may vanish mod p: cf. th^4+4 vs th^8-56th^4+16, resultant a power of 2): in S4 (root4, pow4_iso, A1),
   S6 (roots5, moments5, caseC_alg), S7 (the pair list: checked by me mod P1 above), S8 (Qv, S8a/S8b). Recommendation: list these finite claims
   and re-check each mod P1 (cheap: one Singular std per claim), as verifyfl did for (P3) and (c1). Polynomial identities with denominators
   2, 3, 5, 7 are harmless for P1.
 (f) Defect-0 points: Y_5 ("defect in C m") contains spaces with ZERO defect; they are excluded in char p either by SL_p (5-dim strongly level) or
   by the case systems if those do not normalise C(Y) != 0. Either way SL_p is needed once more.
 (g) The case-split derivations ([DC3], [T22], [T31] cell covers, normal forms, (F2)-(F4), Newton) must be valid over F_pbar: this was ALREADY
   required by the whole-cover RED-p logic (rounds 12-13), so R11.6 adds nothing new there; p > 7 suffices for the divisions I know of.
 (h) Two-column exemption: chart A m = (1,t,-1-t), chart B m = (t,1,-1-t): two-column iff t(t+1) = 0 in both charts, so "u t (t+1) - 1" removes
   exactly the two-column points (and no |supp| = 3 point). Correct.
 VERDICT R11.6: the reduction is VERIFIED as logic. Its char-0 conclusion needs: every case system with no F_pbar point off t(t+1) = 0 at P1 (open
 pieces listed above) + TC5_p + SL_p, where SL_p / TC5_p = DI5.3 (flagged steps checked) + the finite claims of blueprint S4, S6, S8 re-checked mod P1.
STATUS 01:16: CORRECTION to my Lean audit above (my first count was truncated by a 'head -400'): R7s_t3.lean has 484 sorried declarations, INCLUDING
 ALL 98 generated (II,II,II) core lemmas t3p_* (3 of them compiled separately as samples in R6t_stub). What window 2 actually checked in R7s_t3:
 the 305-leaf dispatch t3_trans FROM the 98 core lemmas, and T3Rest2 => T3Rest => T1Rest3 => T1Hyp. Not yet Lean-checked: 95 t3p_* core lemmas,
 the proof of T3Rest2 (r7_1..r7_7), the repaired t1_IIi. This matches leanzbf's own note ("95 of the 98 t3p_* never compiled").
STATUS 01:16: E-STALE-OUTPUT addendum (verifyfl's truncation test) CONFIRMED by my own test (msolve on a 3.2 MB input, planted "[1]:" output):
 timeout kills at 0.05 s / 0.3 s (SIGTERM via timeout, and SIGKILL via python subprocess timeout) and allocation segfaults (ulimit -v 20 MB, 100 MB,
 300 MB; rc 139) ALL leave a 0-byte output, for "-g 2", "-g 2 -t 1" and "-e 4 -g 2 -t 1". msolve truncates the output before it even parses the
 input. The planted file survives only when msolve never starts (ulimit -v 5 MB / 1 MB: exec failure, rc 127), which no driver of ours reaches
 (caps 2-6 GB). A 0-byte output reads as ERROR (exactlib), FAILED/non-unit (stage2), non-unit (reg2 polylib): never as UNIT. => realistic exposure
 of recorded UNIT verdicts to stale outputs: NIL apart from exec failures / missing inputs. My re-run recommendation is DOWNGRADED to optional.
 The remaining mechanism (verdict-line reuse in gen_dc / gen_sym_dc 'resume' manifests) is verifyfl's check, pending.
STATUS 01:16: reg2 ROUND 11 (added by the coordinator):
 R11-2 (1,1,1|1,1,1): M111 VERIFIED exactly (verify2/r16/m111_mine.py): perm(J+Y) = 120 identically, dim 6, dim T_1 = 9, sigma_1 = 0 on T_1, sigma_2 form
   on T_1 of rank 3 => level L containing M111 has dim <= 6 + 1 = 7 (matches reg2's numerical FO2 = 7). Uniqueness (476/512 empty, 36 = one orbit) taken
   from incpat (calibrated on (2,2|2), (3|3), (3,1|2), (2,1,1|1,1); the earlier inc111.py/cal211.py logs are INVALID by the x%d%d variable clash and
   are marked so by reg2) -- not re-run by me.
 R11-3 (1,1,1,1|1,1) family '1111_11a' (u0 = (0,0,-1-a,1,a), u1 = (0,0,1-a,1+2a,-2-a), u2, u3, x0, x1): VERIFIED exactly (fam1111_mine.py,
   fam1111_special.py, fam1111_sig2.py, fam1111_pts.py): level identically in a; dim 6; rank of the T_1 matrix 16 off a(a+2)(a^2+a+1)^3 = 0 (16x16 minor,
   exact interpolation), and dim T_1 = 9 at a = 0, -2, omega (exact over Q(sqrt-3); omega^2 by conjugation) and a = infinity; sigma_2 on T_1: entries
   (polynomial basis over Q(a), vectors in T_1 for every a) have gcd 8a(a+2), and at a = 0, -2, infinity the rank is 3 => sigma_2 is never identically 0 on
   T_1, so no 9-dim level L contains a member (dim L <= 8). Completeness of the family within the pattern rests on incpat (not re-run).
 R11-5 / 19.3 finite-mechanism theorem: VERIFIED as a conditional reduction: if Pi(M) = M (BL), each piece splits as (P cap Lin) + genuine part, g(P_0) =
   rank B (dim X_0 - dim ker B, ker B = first line part), N adds <= 1 (codim P_0 <= 1, SK); rank B <= 2 for columns (SK) and for dim X_0 = 4 rows (SK3,
   V-r14), rank 3 only for dim X_0 = 3 rows (R3, OPEN). So (S6-FO2) <= (BL) + no R3 + (S6-FO2) per type family. The R2 shape (S4, 16.5(ii)) taken as stated.
 R11-4 (3-dim row blocks): rank 3 <=> R2 + R1 on the same pair: not re-derived this round; exact exclusion of (alpha), (I), (II) OPEN (reg2).
STATUS 01:20: R11.6 ADDENDUM (2): how far the Lean proof of SL (FLk) already gives SL_p, and a proof-grade route.
 Scan of lean/fl/FLk.lean (full, compiled): the only C-specific constructs are Complex.I (40 uses: a square root of -1, exists in F_pbar) and
 Complex.im, used three times only in r3_inj to show i != -1, i != -i, -1 != -i. All three hold in every field of characteristic != 2 with i^2 = -1.
 No abs/norm/Real/order/nlinarith/positivity; Polynomial and IsAlgClosed are not used. Steps: 408 linear_combination certificates (polynomial
 identities with rational coefficients), Vandermonde determinants, finite decide. Integer literals in FLk: 22 distinct, max 288, all prime factors
 <= 7. In FLn (TC5 pieces): additional prime factors 11, 13, 19 only. None is P1.
 => EVIDENCE that SL and TC5 hold over F_pbar for P1 (no literal can vanish mod P1). NOT a proof: numerals that norm_num/ring compute internally
 (e.g. a contradiction "c = 0" with c a computed integer) are invisible to a literal scan.
 PROOF-GRADE ROUTE (recommended to the coordinator, leanfl job): port FLk and the TC5 blocks from C to a general field K with hypotheses
 [Field K] (i : K) (hi : i*i = -1) (hN : (N : K) != 0 for N in a finite list). Lean then FORCES every place where the characteristic matters
 to show up as a numeral hypothesis; check that P1 divides none of them. Mechanical: Complex.I -> i, r3_inj by the char != 2 argument, and the
 ring/linear_combination steps that divide by numerals get the hN facts. This gives SL_p and TC5_p at P1 as Lean theorems, which R11.6 needs.
STATUS 01:21: target 4 items that landed:
 stage2 R15-2 K-REDUCTION LEMMA: VERIFIED (under its rank conditions). A combination B of the B_z of rank 6 descends to a NONDEGENERATE form on C/K
   (K = common kernel, dim 2), so the image of a 4-dim common isotropic L'' in C/K has dim <= 3 and L'' cap K != 0; k in L'' cap K is q_0-isotropic and in
   every ker B_z; L''/Ck is 3-dim isotropic in k^perp/Ck (6-dim, q_0 nondegenerate there since k is isotropic and q_0 nondegenerate on C): Lagrangian, and
   isotropic for all induced B_z. q_0|K has <= 2 isotropic lines unless q_0|K == 0. The degenerate loci (B-span rank < 6, kernel jumps, q_0|K == 0) must be
   covered separately -- as stage2 says. F2col v4 Gr(4,8) runs: FAILED x4 at 2 GB (no verdicts to check).
 stage2 E-MSSTR-RATIONAL (msstr truncates non-integer rationals): my D3A over-Q runs use that msstr; I asserted integrality (d3a_intchk.py, charts
   0-1-2-3, 0-1-2-6, 2-3-5-7: no assertion). Every entry of every form G appears alone as a coefficient in chart 0-1-2-3 (constant terms for the
   S x S block, y-linear terms for S x rest, y_ik y_jl (i != j) for rest x rest), and bad_poly is written in the same file, so ALL 70 charts are
   integral: my runs and stage2's D003-PROP P1 runs are unaffected.
 verifyfl SYM [DC3] 'ne' pieces: A1-ne, B1-ne UNIT at P1 at stage S1 (files r11/sc2/{A,B}1_ne_S1.ms(.gb): prime 2147483629, output newer than input,
   body [1]); A0-ne and B0-ne crashed at 2.5 GB (0-byte outputs, i.e. FAILED, correctly not counted) -> big slot. My own msolve re-run of A1/B1 ne
   needs more than 0.5 GB (segfault at that cap): deferred so as not to run two jobs above 0.5 GB.
 stage3 (PR3) stratum (II): sec. 37 (A)-(C) are numerical (x*-linear system of full rank at generic H-points); now the counterexample confines (PR3) to
   strata (I),(II); nothing exact to verify yet.
STATUS 01:25: TARGET 2 D003-PROP Case A over Q (sizing): 8 charts in 25 min (stopped at the 30-min cap). UNIT over Q: 0-1-2-3, 0-1-2-4, 0-1-2-5, 0-1-2-7 and 0-1-3-4, 0-1-3-5 in <= 3 s each;
    0-1-2-6 took 305 s / 0.6 GB and 0-1-2-7 178 s / 0.6 GB. 0-1-3-6 ran OUT OF MEMORY at 2 GB. 0-1-3-7 was at 584 s / 1.5 GB when stopped.
    All coefficients are integral (checked). VERDICT: the route works (exact slimgb over Q = proof per chart), but NOT within 2 GB for every chart.
    The coordinator should schedule the 70 charts with 6 GB / 30 min each (a hard chart is about 0.6-2+ GB); the easy charts take seconds.
    Script: verify2/r15/d3a_slim.py (CHARTS env; ulimit 2 GB inside; change the ulimit line for the big slot). d3a_std.py = the std variant (untested).
STATUS 01:29: verifyfl sc2 A1_ne_S1 / B1_ne_S1 RE-RUN by me (fresh output, exit code checked, 2 GB): both [1] at P1 (6 s / 85 MB; 47 s / 364 MB). CONFIRMED.
# ROUND 17 (start 01:29 UTC). Targets: (1) PROOF-MAP with a consolidated "what is left" list at the top; (2) audit leanfl's K-field port (list of N,
#  P1 divides none); (3) stage3 stratum (III): completeness + uniform T_1/FO2_0 bound -- what is missing; (4) rows R13 Lemma RS / k21sys; (5) reg2 incpat
#  splits + R11-1.
STATUS 01:29: D3A drivers for the pool / big slot: my round-16 wrapper did NOT count failures (its RESULT line said FAILED 0 even after an
 out-of-memory chart; the per-chart lines were right). FIXED: d3a_slim.py now = d3a_slim_v2.py (ulimit from env SV, default 2 GB; FAILED/NONUNIT counted
 from Singular's stdout and exit code; final line "FAILED CHARTS: ..."); d3a_slim6.py = same with SV default 6 GB (big slot). TMO from env (default 1500).
 Smoke tests: 0-1-2-3, 0-1-2-5 UNIT; 0-1-2-6 with TMO=3 reported FAILED (rc 124). Original kept as d3a_slim_r16orig.py.
STATUS 01:35: rows R13 (round-17 target 4):
 LEAF 3(a) the 16 special points: VERIFIED (P1, RED-p). rows/r12/kSP1.out: 64 DISTINCT charts (all sign choices of sqrt3 and i, i.e. Galois-covered),
   each "unit 1" in some run at p = 2147483629 (the 64th = the SIGSTOP-halted chart, rerun unit, 115 s, 0.25 GB); every gauge determinant nonzero mod P1;
   sqrt3^2 = 3 and i^2 = -1 mod P1 checked. The RED-p argument for this cover was verified in round 15. => leaf 3(a) closed in char 0.
 LEMMA RS (R13.6) (i)-(iii): VERIFIED by hand. (i) for column-centred Y, sigma_2 of the column-k deletion = (1/2)(||Y||^2 - ||y_k||^2 - ||rho - y_k||^2); all
   five vanish => summing gives (3/2)(||rho||^2 - ||Y||^2) = 0, hence <y_k, rho - y_k> = 0 for every k; polarised: A_k^T R + R^T A_k = 2 A_k^T A_k; with
   M_k = R - 2A_k: M_k^T M_k = R^T R and sum M_k = 5R - 2R = 3R. (ii) if P = rho(K) were nondegenerate, M_k e1, M_k e2 span a nondegenerate plane Q_k
   and M_k n is isotropic and in Q_k^perp (a nondegenerate line) => M_k n = 0 => A_k n = 0 for all k => n = 0: so P = u^perp, u isotropic. (iii) mutually
   orthogonal isotropic vectors of the nondegenerate plane m_k^perp lie on one isotropic line => M_k e1 = al_k f_k, M_k n = be_k f_k. (iv) (degree 3
   formula) not re-derived. Leaf 3(b) (supports 4, 5) remains OPEN; k21sys not yet run on support 4.
STATUS 01:35: reg2 incpat (round-17 target 5), INDEPENDENT RE-IMPLEMENTATION for (1,1,1|1,1,1) (verify2/r16/inc111_mine.py -> .sing/.log; my own level
 equations from perm_inj(J+Y) = 120, Singular sat over Q by "each line != 0", one system per S_3 x S_3 orbit): 36 orbits; 35 EMPTY (476 classes),
 ONE NONEMPTY orbit (size 36, representative 000001011, affine dim 6 = the scalings) -- EXACTLY reg2's 476/36. minAssGTZ of that class: ONE prime,
 LINEAR component = M111 up to the six scalings (u0 ~ (0,0,0,1,-1), u1 ~ (0,0,-2,1,1), u2 ~ (0,-3,1,1,1), x0 ~ (1,1,-3,1), x1 ~ (1,-2,0,1), x2 ~ (1,0,0,-1)).
 The incidence dichotomy itself checked: for sum-zero row/column lines the mixed sigma_2 term is (sum x - x_i)(sum u - u_m) = x_i u_m, and a product of
 two linear forms vanishing on a product of subspaces forces one factor to vanish on its subspace. => R11-2 (1,1,1|1,1,1) CLOSED, VERIFIED (with my exact
 T_1/FO2 bound dim L <= 7). Caveat: "line-spanned" (M = sum of its lines) is part of the pattern's definition.
STATUS 01:36: reg2 R11-1 (conic double deformation trivial): VERIFIED with my own membership test (verify2/r16/conic_mine.py): det G(V0) = Q, det G(U) = 125 Q,
 <V0,U> = 0 identically, all rows sum-zero; every 3x3 minor of [u0,u1,J_V v_k] and [v0,v1,J_U u_k] reduces to 0 modulo the ideal (Q) (Groebner, lex);
 exact points on the conic (m4 = 0, m3 = (1 +- 2 sqrt(-2))/3): rank [U | J_V V] = rank [V | J_U U] = 2 with rank U = 2. So on Q = 0 the deformations add
 only elements of M: M(t,t2) = M(0,0) (DR22). (The deformation map J(v1) = g12 v1 - g11 v2 is gen_rank_defo's, audited V-r14.)
STATUS 01:36: TARGET 3 -- stratum (III) / type (t2) of (S3-a): WHAT EXACTLY IS MISSING.
 Bookkeeping checked (stage3 sec. 37 (H)): dim pi_s(X_re) = 3 - m_kl with {k,l} = R - {r,s}. (t0): all m = 1 => all projections 2 => strata (I)/(II).
 (t1): choosing r in the m = 2 pair, no pair R - {r,s} equals it => strata (I)/(II). (t2): for every r, s = r's partner gives the other m = 2 pair =>
 dim pi_s(X_re) = 1 => stratum (III) for EVERY r. Correct: (t0), (t1) need only (PR3'); (t2) is the stratum-(III) problem. MISSING for (t2):
 (M1) CLASSIFICATION. stage3's "general family" is an ANSATZ: row 0 on the line C e_0 (p = e_0) and rows 1, 2 of the form (column-0 entry, (0,y)) resp.
   (column-0 entry, (0,z)). Inside the ansatz the hand computation (level <=> s(y) = s(z) = <y,z> = 0; defect <= 2 <=> y o z in span(y,z)) is fine. What is
   NOT shown: that every stratum-(III) X with no single-row element and defect <= 2 (needed for a 2-dim Z) has p proportional to a coordinate vector,
   and that K_0 (2-dim, row 0 zero) then has the (0,y), (0,z) shape. stage3 has numerical support only (probe: p = e_4) and the stratum-(II)
   special-locus computation, which points the same way (x* = w (x) e_j).
 (M2) UNIFORM BOUND. Needed: FO2_0(N) <= 8 for EVERY member (y on the cubic condition, all rho not in {0,-1}, degenerate members included). Exact so
   far: my 3 points (rho = 1, 2, 7/3 at y = (1,-1,0,0)); numerical: stage3's 19 members (T_1 in {9,10}). A proof-grade version is the method I used
   for reg2's 1111_11a family: the T_1 matrix with symbolic parameters, the common zero locus of its maximal minors (where T_1 jumps), and a lower
   bound for the sigma_2 rank on T_1, each exceptional locus checked separately. With y, z constrained by s(y) = s(z) = <y,z> = 0 and
   rank[y, z, y o z] <= 2, plus rho, this is a Groebner job of moderate size (needs (M1) first, otherwise it bounds only the ansatz).
 (M3) ALTERNATIVE that avoids (M1): stage3's (t2) core (sec. 30 (E)): X0 = Y_ab (+) Y_cd is level iff (X2)-(X4), 25 conditions on 22 parameters (expected
   dim -3; numerics 0/67). An exact emptiness proof of that core (over Q, or a whole-cover RED-p run at P1) would close (t2) directly, with no stratum-(III)
   classification. I recommend this as the main route, and (M1)+(M2) as the fallback.
 Also still open: (PR3') for strata (I) and (II). Stratum (II) reduces to "rank-drop locus of A(h) = special locus" (special locus EXACT empty for stratum (II)
 proper, sec. 37 (I)); stratum (I) has no approach yet (31 unknowns).
STATUS 01:44: Lemma RS (iv) (degree 3) CHECKED symbolically (verify2/r17/rs_iv_*.py, Singular reduction modulo the five degree-2 conditions; generic column-centred
 4x5 Y, t(a,b,c) = sum over the 4 rows of a b c -- the Walsh-coordinate reading fails, the row-coordinate one works):
   sigma_3(Y minus column k) = (1/4) E_k - (1/12) S   modulo the degree-2 conditions,  S := sum_k t(x_k,x_k,x_k) - 3 t(r,r,r),
   and  sum_k sigma_3(Y minus column k) = -(1/6) S  modulo the same.
 So the individual E_k are NOT proportional to the individual deletion cubics, but as SYSTEMS {sigma_3(Y_-k) = 0 for all k} <=> {E_k = 0 for all k}
 (all E_k = 0 gives sigma_3(Y_-k) = -S/12 for all k, summing gives -5S/12 = -S/6, so S = 0). The summed cubic sum_k t(x_k,x_k,x_k) = 3 t(r,r,r) holds.
 => Lemma RS (iv) VERIFIED as a statement about the system; rows should state it that way (the per-column wording is inaccurate).
STATUS 01:47: item 12 (top-level case split) -- a concrete question found while re-reading GEN: PROOF-MAP/handoff phrase (B) as "all annihilators zero-free
 => GEN; minimal pair's annihilators with zeros => branch 3". GEN-2's proof divides by the COLUMN-annihilator entries K'_ij at the three rows outside the pair
 (G_ij = zeta_j / K'_ij), and (S2*) needs zero-free ROW annihilators on triples. So the mixed case (pair's own annihilators zero-free, a zero elsewhere) must
 be covered by stage2's "GEN-type layers" / "zeros in the annihilators INVOLVED" (which I verified piecewise in rounds 4-9). Wording fixed in PROOF-MAP;
 exhaustiveness to be confirmed next round (owner verify2, S, hand).
STATUS 01:47: item 12 question RESOLVED: stage2's REG1 (all a_r = b_c = 1, no zero-freeness; RESULT-R4) reduces to (B1) "a minimal row or column pair -> L_r is a
 (Q-r) solution with 3-dim row projection passing (FO-r), FO2, (T2)" and (B2) "no minimal pair -> single-row/column elements" -- verified by me in round 5
 ("Reduction of REG1 to (B1)/(B2) VERIFIED"). (B1) needs no zero-freeness, so the mixed case is inside branch 3's (Q-r) program; GEN is an independent
 proof of the fully generic sub-case. PROOF-MAP wording corrected ((B) and the Branch 3 title). Top-level split: exhaustive given FK (a_r >= 1), Lemma C
 (lam >= 2), the transposition symmetry and Theorem N.
STATUS 01:48: stage3's stratum-(III) ANSATZ computation VERIFIED symbolically (verify2/r17/fam3_mine*.py, symbolic y, z, rho): the sigma coefficients are
 s(y), s(z), s(y)s(z) - <y,z> (times constants / rho / rho+1), so level <=> s(y) = s(z) = <y,z> = 0, and sigma_3 is then automatic; on that variety
 D_1(x) = -(column sums) = -(0, b y + c z), D_2 = (0, p_1 b y + p_2 c z + 2bc y o z), D_3 = 2 p_0 bc (0, y o z) exactly as stated. The bc-coefficient of D_2 is
 2 (0, y o z), so the defect span is span{(0,y), (0,z), (0, y o z)}: defect <= 2 <=> y o z in span(y,z). (M1) -- that every stratum-(III) X has this shape
 -- remains the missing step.
# ROUND 18 (start 01:50 UTC). Targets: (1) leanfl K-field port -> kfield_audit + N list vs P1; (2) ncol round 3: THEOREM PT2 (Gr(2,5) x Gr(2,5) x Gr(2,V5),
#  11 orbit charts x 3 primes, RED-p), E3P (e_3 vanishes on no 3-space; chart 012 over Q + S5-orbit argument), R3.3 reduction of (PROD) to three Gr(4,10)
#  chart types; (3) stage3 sec. 38 (A) rigid member of z = (1,1,1,1,0) -> free column -> PFC (cond. on (SL_m0)); "three m + w" closure complete?;
#  (4) rows support-4 cases (P2, P3, PP, G); (5) reg2 round 12 (R3 case (II), rows spaces, (3,1,1|1), (3,1,1,1|)) + stage2 R2 reduction / K-reduction loci.
STATUS 01:53: TARGET 1 -- leanfl's K-field port lean/fl/FLK_field.lean (7748 lines; 326 theorems = all 320 of FLk + helpers): STATIC AUDIT (kfield_audit.py)
 - Setting: variable {Kf} [Field Kf] [NeZero (2:Kf)] [NeZero (3:Kf)] [NeZero (5:Kf)] [NeZero (7:Kf)]; the main theorems add exactly two hypotheses,
   Fact (forall s : Finset Kf, s.card <= 20 -> exists t not in s)  (more than 20 elements; used by generic_t / generic_pt) and Fact (exists i, i^2 = -1)
   (Ii := choice; replaces Complex.I). No CharZero, CharP, IsAlgClosed, DecidableEq or other instance anywhere (grep of all instance binders).
 - N LIST: the only numeral assumptions are NeZero 2, 3, 5, 7; every other "(N : Kf) != 0" (4, 6, 8, ..., 128, 256, 288 -- 33 numerals) is DERIVED as a
   product of these (nz4 = nz2*nz2, ...). P1 = 2147483629 divides none of 2, 3, 5, 7. P1 = 1 mod 4, so i exists in F_P1; F_pbar is infinite.
 - Final statement SL_FL_field: Lemma SL + FL row + FL col over Kf, with the same Lev / SLev definitions; SL_FL_C instantiates Kf := C (C appears only there
   and in the L_gct_210 wrapper, 17 + 2 occurrences). No sorry / admit / axiom.
 - NOT YET COMPILED (no log). Lean's compile is the real test: a norm_num / ring / field step that secretly needs another numeral (or char 0) will fail
   there. VERDICT (static): the port's assumptions are exactly {char not in {2,3,5,7}, |K| > 20, sqrt(-1) in K}, all true for F_P1-bar. Once it compiles,
   SL_p (and FL_p) at P1 is a Lean theorem.
 - SCOPE: the port covers FLk only. Full TC5 (DI5.3; Lean in FLn/FLo/FLp, which have not compiled even over C) is NOT ported. TC5_p therefore rests on
   the hand proof DI5.3 (algebraic; its two flagged steps checked mod P1 in round 16) plus the SL classification lemmas, which ARE in the port.
STATUS 01:55: E-STALE-OUTPUT CLOSED for the proof-relevant manifest covers. verifyfl/r12/resolve.log (02:52 local): every UNIT line re-solved at P1 in a fresh
 directory with the guarded run_msolve (verifyfl/exact/exactlib_fixed.py: output removed first, ERROR on rc != 0 / missing / empty output): symA 252,
 symB 249, sym2 3, m0 dc_p5b 214, DC3 theorem m12m3 252, m11m2 252, iso 253 -- all UNIT again, 0 mismatches. Together with my mtime audit (round 16) and
 the msolve truncation test, these verdicts depend on no stale file, no carried-over manifest line and no generator change. The separate piv0/piv1
 cut-cell runs (logs, not manifests) passed the stale audit; A1-ne/B1-ne I re-ran myself (round 17).
STATUS 01:58: TARGET 2 -- ncol round 3.
 FORMULAS (verify2/r18/pt2_formulas.py, from the deletion permanents of Y with rows a w^k + b w^{2k}, w^2+w+1 = 0): P_2 = 3(a.b - AB), P_3 = 6(e_3(a)+e_3(b));
   D_2 = 3 d2 + P_2 * 1 with d2 = A b + B a - 2 a o b (so G.D_2 = 3 G.d2 for G in V5); D_3 = 6(d3a(a) + d3a(b)) + (const) e_3(a) + (const) e_3(b), no mixed
   a-b terms. All as ncol states (modulo the level relations, which are in the system).
 E3P: VERIFIED over Q. My own chart-012 system (10 cubic coefficient equations, 6 unknowns) has GB [1] over Q (Singular std); the 10 pivot triples of
   Gr(3,5) form ONE S5-orbit and e_3 is S5-invariant. Exact, char 0.
 PT2: S5 x Z2 orbits of the 1000 chart triples: 11, exactly ncol's list (my enumeration). The system is closed in Gr(2,5) x Gr(2,5) x Gr(2,V5) (pivot charts
   cover; G-charts: 2 free per row after g_r[p_r] = 1, g_r[p_{1-r}] = 0, sum 0), integer coefficients, no saturation: RED-p applies. INDEPENDENT GENERATOR
   (pt2_mine.py, my own D_2/D_3): running at P1 (see next STATUS). Calibration of MY equations at ncol's exact example (W_a = W_b = span(e0,(0,1,i,-1,-i)),
   G = D2^perp in chart 01, exact over Q(i), pt2_cal.py): 32/36 equations vanish, the 4 nonzero ones are D_3 equations (the example has e = 3) -- the same
   picture as ncol's point check.
 R3.3 reduction: VERIFIED (own argument). Block-diagonal S = W_a + W_b has p_I = 0 unless |I cap a| = 2; conversely, if every p_I with |I cap a| in {3,4} or
   |I cap b| in {3,4} vanishes, then rank pi_a <= 2 (rank 3 gives a basis s1..s3 with independent a-parts and s4 = (0,beta4), and p_I = det(A3) beta4_j != 0;
   rank 4 gives a 4-a-column minor) and likewise rank pi_b <= 2, so S = (S cap a) + (S cap b), 2 + 2. Orbit types under S5 x Z2: 0123, 0125 (b-index on one of
   the a-columns), 0128 (not): exactly three.
 *** RIGOUR FLAG for PROD-NCOL (queued at P1): "non-product" is an OPEN condition (some p_I != 0), so a P1 UNIT on the affine charts p_I = 1 does NOT give
   (PROD) in characteristic 0 (a char-0 non-product S can reduce to a product S). What it DOES give, with PT2 at the SAME prime: CC3-e2 in char 0, by the
   whole-cover RED-p argument on the CLOSED variety Y = {(S,G) in Gr(4,10) x Gr(2,V5): S level, G perp D(S)}: Y(F_pbar) = (product part: empty by PT2) u
   (non-product part: empty by PROD at P1) = empty => Y(C) = empty. So: PROD at P1 + PT2 at P1 => CC3-e2 (and hence CC3', R2.15 dead, a second proof of
   CC3) in char 0; (PROD) ITSELF stays evidence unless decided over Q. ncol's R3.9 wording "(PROD) + F4 => CC3-e2" should be phrased this way.
STATUS 01:59: TARGET 3 -- stage3 sec. 38 (A), rigid member of z = (1,1,1,1,0) ('three m + w', m = (1,i,-1,-i,0) on rows 0,1,2, w = (1,1,1,1,-4) on row 3):
 RE-RUN in my directory (copy of rigid_pairs.py writing to verify2/r18/rigid/; Singular over Q(i)): pair (0,1), 13 charts: 11 UNIT; charts xl4 and v4 are
 0-dimensional, vdim 2, RADICAL vdim 1, the single point being xi = (e_4 - e_2) (x) e_4 (row 4 col 4 = +-1, row 2 col 4 = -+1, all else 0) in both charts.
 The equations are ALL level coefficients (every monomial in al, c0..c3, sigma_1..sigma_5) of span(e_i (x) vec_i, i in S; xi): necessary conditions, so
 the deduction "xi = that column element" is valid; the gauge xl_0 = xn_0 = 0 uses m_0 = w_0 = 1; the 13 charts cover every nonzero xi. Pairs (0,2),
 (1,2) by the row symmetry of rows 0,1,2. The three column elements span {C (x) e_4 : supp C in {0,1,2,4}, sum C = 0}: a free column on four rows,
 so Lemma PFC (V-r9) gives dim L <= 8 CONDITIONAL on (5,1) for m0 = (1,1,1,1,-4) (the PFC exception). VERIFIED.
 IS THE 'three m + w' CLOSURE COMPLETE? Yes, modulo two inputs: (i) sec. 37 (K): the hand reduction (not re-derived by me) + the exact rank loci over
 Q (R2 fails only for m with a zero entry; R1 likewise, charts w0 rerun UNIT, w4 = w1 by the transposition (1 4)), which leave exactly the m with a
 zero entry; with e_1 = e_2 = e_3 = 0 the four nonzero entries are a scaled set of fourth roots of unity, i.e. m = (1,i,-1,-i,0) up to symmetry and
 conjugation, and w is then forced to (1,1,1,1,-4): ONE rigid member -- correct; (ii) (5,1) for m0 (PFC's condition) = what-is-left item 2.
 The other configurations of (1,1,1,1,0) (k_N = 2, 4, (2,2), (2,1,1)): generic members numerical only (sec. 38 (C)); special members open.
STATUS 02:00: TARGET 4 -- rows support-4 (R14):
 R14.0 CASE TREE: VERIFIED. With sum be_k f_k = 0, be_k != 0 on supp n, and the f_k isotropic: three distinct isotropic directions are independent (no three
   points of a smooth conic are collinear), so with <= 3 directions each direction-group sums to 0 and has size >= 2. Support 4: |supp n| = 2: P2;
   3: P3 (3 directions or (2,1) impossible); 4: P4 (one direction), PP (2+2), G (4 distinct). Complete. The chart at infinity: S_4 (rows) acts on the
   conic of V as the octahedral group, transitively on its 6 vertices (the isotropic points with a zero Walsh coordinate); a support-4 configuration uses
   <= 5 isotropic points, so a free vertex can be moved to the one missing point c(inf) = (1,i,0): one finite chart suffices. Correct.
 P3, PP: RE-RUN by me over Q(i) (case4.py output written to verify2/r18/rows4/, ii^2+1 in the ideal, Rabinowitsch only for be != 0): both "dim -1 unit 1"
   before any saturation, 1.5 s each, degree-<=2 parts implied. (Same generator, so a re-run, not an independent generator.)
 P2: UNIT mod P1 only; rows correctly say RED-p is NOT available (open conditions; the closed variety contains the existing 2-3-column kernels) -> needs the
   exact run R14-P2Q (queued, big slot). G: running. Leaf 3(b) support 4 = P2 (over Q) + G open; support 5 not started.
STATUS 02:07: K-FIELD PORT, final static audit (coordinator request; reported by SendMessage). FLK_field.lean (8006 lines) and leanfl/TrK11.lean (7531 lines):
 hypotheses exactly [Field Kf], NeZero 2, 3, 5, Fact (exists i, i^2 = -1), Fact (|Kf| > 20); no CharZero/CharP/IsAlgClosed/DecidableEq/Fintype/Infinite;
 sorry/admit/axiom 0; derived numerals (29) all products of 2, 3, 5; literal factor 7 only in Nat bounds "finrank <= 7"; no literal divisible by P1. F_P1
 (P1 = 1 mod 4, P1 > 20) and F_P1-bar satisfy all hypotheses. TrK11 = TC5 BLOCKS over Kf (TC5_P1/P2/P3/dims/c3, P4 pieces up to P4_c2_canon), NOT the
 assembled TC5: (c2-iii) (hypothesis Hiii), (c1), placement transports and the dispatcher are missing even over C. So after window 3: SL_p = Lean;
 TC5_p = Lean blocks + hand DI5.3 for the missing branches. Compile (window 3) is the real numeral test.
STATUS 02:08: PT2 INDEPENDENT GENERATOR RESULT (verify2/r18/pt2_mine.py, my own D_2/D_3 and charts; stale-safe msolve, 2 GB): ALL 11 orbit charts UNIT at P1
 (36 equations each). With the closed projective system (no saturation, integer coefficients) and RED-p: THEOREM PT2 VERIFIED in char 0 (independent of ncol's
 generator; calibration of my equations at the exact example: 32/36 vanish, the 4 D_3 equations do not, e = 3).
STATUS 02:08: stage3's NON-DEGENERATE X0 (stage3/r18/x0sol_hinge_2_1.npy) CHECKED INDEPENDENTLY (own permanent code, 45 fresh points at scales 0.3/1/4):
 basis rank 4 (singular values 1.54..1.36, well conditioned); level: |perm_inj(J+Y) - 120| / |Y|^4 <= 5.7e-14; row projections (2,2,2,2); NO single-row
 element in any row; exactly one single-column element, column 0, column vector (1,-1,0,0) = (e_a - e_b) (x) e_0; dim c(P_a) = 1, dim c(P_c) = 2; defect
 singular values 1, .11, .043, .027, 3e-15 => e = 4. So "X0 is empty" ((M3) as I stated it) is FALSE (numerically, convincingly).
 WHAT SURVIVES / EXACT TARGETS: (M3') the MAIN case dim c(P_a) = dim c(P_c) = 2 -- still expected dim -3, no example; (M3'') dim c(P_a) <= 1 means
 Y_ab = {(v, phi v)} contains (v, -v) (c(v) = v + phi v = 0) with <v,v> = s(v)^2 (2-row level); here v = e_0, a column element. Plausible exact target:
 "in (t2), c(v) = 0 forces v to be a coordinate vector" (both known (t2)-type families -- stratum (III) and this X0 -- carry a column element), after
 which the transposition route applies: L^T then has a single-row element with a NON-isotropic vector (e_a - e_b), and branch 2 (F4b-X, SR5, SR2111,
 Fourier, SPLIT-type arguments) acts on L^T. Not automatic: (v,-v) with <v,v> = s(v)^2 and v not a coordinate vector is not excluded by the 2-row conditions alone.
STATUS 02:09: ncol ROUND 4 (coordinator addition):
 THEOREM CC34 (no column-centred 3x4 level space of dim 4): VERIFIED with my OWN generator (verify2/r18/cc34_mine.py / cc34_p1.py: isotropic coordinates
   (a,b) in C^4 x C^4, P_2 = 3(a.b - AB), P_3 = 6(e3(a)+e3(b)) -- the formulas I derived for 5 columns are symmetric-function identities and hold for 4;
   Gr(4,8) Pluecker charts): S4 x Z2 orbits of the 70 charts = 6 (my enumeration: 0123, 0124, 0127, 0145, 0146, 0167 in a/b index form); ALL 6 UNIT at P1
   (msolve, stale-safe); chart 0123 also UNIT exactly over Q (Singular). Closed projective system, integer coefficients, no saturation -> RED-p -> char 0.
 R4.2: (a) checked by brute force: among the 6 orderings of (1,i,-1,-i) (up to scale) only v'' ~ v' is dot-orthogonal, so same-node pairs are W (+) W,
   W = span(e_k, chi_sigma): 5 x 6 = 30 spaces; (b) B(e_i,e_j) = -1: correct; (c) "finitely many" not separately checked (implied by R4.3).
 R4.3 (finiteness of the product-pair scheme, char 0 by semicontinuity): ARGUMENT VALID. The pair scheme Z (e3|W_a = e3|W_b = 0, B(W_a,W_b) = 0) is closed in
   Gr(2,5) x Gr(2,5) over Z; the 3 S5 x Z2 orbit charts (same / overlapping / disjoint pivot pairs) cover it; 0-dimensional in all three at P1 means
   dim Z_{F_pbar} = 0. If Z_Q had a component C of dim >= 1, its closure in Z is integral, dominant, hence flat over Z_(p) with fibres of dim = dim C, so
   Z_{F_pbar} would contain a positive-dimensional piece: contradiction. (Flatness of the closure also bounds the char-0 count by the P1 degrees.) Not re-run.
 R4.12 (CC45 refuted by ncol/ccn/cc_d4_s52_pol_e2.npy): CONFIRMED NUMERICALLY with oracle-style fresh points (my code): basis well conditioned (singular values
   4.2..1.5), column sums 3e-14, level |perm_inj(J+Y)-120|/|Y|^4 <= 1.3e-11 at 60 points (scales 0.5, 2, 8, orthonormal basis), defect singular values
   1, .25, 3e-12, 2e-12, 5e-13 => e = 2. Single-column parts: column 1 one-dim (to 2.5e-13); column 0 only APPROXIMATELY 2-dim (two singular values 5e-7,
   not 1e-12) -- so ncol's "single-column dims (2,1,0,0,0)" holds only to ~5e-7 (the point sits near, not on, that special locus). Exact confirmation:
   not done (entries not recognised). Verdict: (CC45) false with strong numerical evidence; it was only a proposed shortcut, so nothing proved depends on it.
STATUS 02:11: TARGET 5 -- reg2 round 12 and stage2 R15-4/R15-5:
 reg2 (3,1,1,1|) and (3,1,1|1)-101: hand reduction VERIFIED (V = 1^perp nondegenerate; U_1..U_3 lie in the line U_0^perp cap V = C n; u_1 perp u_2 => n
   isotropic; an isotropic n perp the 3-dim U_0 lies in U_0, else U_0 + Cn = V and n perp V; so U_0 = n^perp cap V); the exact systems use the generalised
   cross products (n_b - n_c, n_c - n_a, n_a - n_b) on triples, which span n^perp cap 1^perp whenever n is not proportional to 1 (kernel of a rank-2 2x5
   matrix is spanned by its triple-minor vectors): correct. RE-RAN reg2/p111/hand3111.sing, hand311_101.sing: after saturation by n, G = [1] (0.03 s).
 reg2 (2,2,2|): reduction VERIFIED (disjoint U_0, U_1 give U_0 + U_1 = V, so U_2 = 0; a 1-dim intersection leaves only the line (U_0+U_1)^perp for the
   2-dim U_2; so U_0 = U_1 = U_2 = T totally isotropic) + RE-RAN hand222.sing: G = [1] (8 s). => hit-free patterns: 26 of 29 settled per reg2; open
   (2,1,1,1|1) class 1001, (2,2,1|1) class 110, (2,2,1,1|) (queued).
 reg2 R12-1 (R3 case (II), two rational B): partial evidence only (general B open). R12-2 (rows-team spaces): a classification, exact families open.
 stage2 KERNEL KILL (R15-4): VERIFIED. With rank B_c = 7 on the 8-dim C and the constant common kernel k: B_c is nondegenerate on C/Ck, so a 4-dim common
   isotropic L'' meets Ck, k in L'' and q0(k,k) = 0; for corank-1 symmetric B_c, adj B_c = cof_77 k k^T, hence Phi_c = tr(G0 adj B_c) = cof_77(B_c) q0(k,k).
   (This SUPERSEDES the K-reduction of R15-2 on ruling R2: the kernel is 1-dim, not 2-dim; the K-reduction stays valid where its rank-6 hypothesis holds.)
 stage2 THEOREM-R2-GEN (R15-5): the common zero set of the four non-exceptional cofactor factors (c.a)(c.a - sum c)(sum c_z(a_z^2 - a_z)) for
   c = (1,2,3), (1,-1,2), (2,1,-1), (3,-2,1) is EXACTLY {0,1}^3 (my Singular minAssGTZ: 8 points, vdim 18 with multiplicity) -- VERIFIED, taking the four
   exact cofactor factorisations from stage2's logs. So off the setup loci an R2 survivor lies on H = {a1+2a2+2a3 = 6} or on the 4 lines a in {0,1}^3 with
   a1 = 1. Degenerate loci still to cover (stage2's list, correct as far as I can see): the 4 lines, nu = 0, a1 = 0, nu = -1, nu = 1/3, D = 0, nu = inf,
   chart a4 = 0, and the codim >= 2 T_1 rank-drop points (stage2's own caveat: the v4 rank-jump test certifies only the hypersurface part).
# ROUND 19 (start 02:12 UTC). Targets: (1) Lean window 3 logs: FLK_field exit 0 / 0 errors / 0 sorry / axioms -> SL_p in PROOF-MAP 1a; sorry counts of the
#  stub files; (2) stage2 jump-locus lemma (rank B_z = 7, W_z, l_w squares, k0 = e9 - e8, a1 = -8), Deg finite?; (3) rows R14P2Q / K21_*; (4) reg2 r13,
#  stage3 r18 items, esp. an exact form of "c(v) = 0 forces a coordinate vector".
STATUS 02:13: TARGET 2 -- stage2 R15-6 jump-locus lemma (ruling R1, lam = 0, nq = 10): LOGIC VERIFIED. With B_z of rank 7 (kernel W_z, dim 3), B_z is nondegenerate on
 C/W_z (7-dim), so the image of a 4-dim common isotropic L'' there has dim <= 3 and dim(L'' cap W_z) >= 1. On W_z each other B_w has rank <= 1, i.e. B_w|W_z = l_w^2;
 B_w(k,k) = 0 gives l_w(k) = 0 for both w != z. The constant common kernel k0 lies in W_z and in ker l_w (B_w(k0, .) = 0 forces l_w(k0) l_w = 0), so with l_w, l_w'
 independent, W_z cap ker l_w cap ker l_w' = C k0, k0 in L'' and q0(k0,k0) = a1 + 8 = 0. One working z suffices, so Deg = intersection over z of the failure sets
 -- r16_Kjump_deg.py builds exactly that, with SUPERSET certificates in the right direction ((a) rank < 7 => the 3 random 7x7 compressions vanish; (b) all
 3-minors of the cleared kernel basis N_z; (c) all 2-minors of the stack of N_z B_w N_z^T, after asserting rank <= 1 identically). At a point with rank B_z = 7
 and rank N_z = 3 the rows of N_z span ker B_z(pi): correct. IS Deg FINITE? NOT YET COMPUTED (no log of r16_Kjump_deg.py so far); stage2 expects finitely
 many points (then fixed-member kills). The a1 = -8 curve then needs L'' = C k0 + L3, L3 in Gr(3,9) (84 charts; ST2-JUMPK queued; one chart FAILED at 2 GB).
STATUS 02:14: stage3's SECOND X0 (r18/x0sol_hinge_3_0.npy) CHECKED INDEPENDENTLY (verify2/r18/x0check.py): basis singular values 2.1..1.1; level |perm_inj-120|/|Y|^4 <=
 7.1e-14 at 45 fresh points; row projections (2,2,2,2); NO single-row and NO single-column element; dim c(P_a) = dim c(P_c) = 2 (MAIN case); defect 4.
 Column-block shape confirmed: Y_ab vanishes in columns 2,3; Y_cd has equal entries in columns 0,1,4. So (M3') "main case empty" is FALSE too, and
 "every (t2)-type structure carries a column element" is FALSE at the level of X0 -- it can only hold for the stratum-(III) X_re (where all known examples
 carry one). stage3's (E) normal form checked: pi_a(Y_ab) = P_a and pi_c(Y_cd) = P_c, so x5 can be reduced to (0, g, 0, h) with g, h != 0 (else a single-row
 element): L_e = Y_ab + Y_cd + Y_bd. The decisive (t2) question is now EXTENSION: does some X0 extend by a 2-row element (0,g,0,h) to a level L_e with
 defect <= 2 and no single-row element? (numerical probe r18/t2Le.py running at stage3).
STATUS 02:34: LEAN WINDOW 3, first log: leanfl/TrK0_w0205.log (smoke test of the port, 1468 lines): exit 1, 2 errors, 0 sorry warnings, 1720 s, peak 5.6 GB.
 Both errors are at ONE place (Vp_finrank, line 1442): "(finrank_sumZero (Kf := Kf)) (n := 4)" -- Lean rejects the named argument n after the partial
 application ("Invalid argument name n"), and the goal is then left unsolved. A port SYNTAX issue (fix: finrank_sumZero (Kf := Kf) (n := 4) ... or positional),
 not mathematical. The same construction occurs in FLK_field.lean (lines 616, 960, 2979, 5165, 5328) and TrK11.lean (801, 2087, 3417, 4184, 4489), so expect the same
 error there (about 10 places, all mechanical). Many "automatically included section
 variable(s) unused" linter warnings (the NeZero instances are included in every theorem) -- harmless: extra hypotheses that F_P1 satisfies.
 FLK_field_w0233.log started 02:33 UTC (empty so far).
STATUS 02:35: FLK_field_w0233.log and TrK11_w0234.log: exit 143 after 48 s / ~30 s -- STOPPED by the coordinator (the files would hit the 60-min per-file timeout at
 TrK0's rate); NO verdict. SL_p waits for a dedicated window after leanfl fixes the finrank_sumZero syntax (7 + 5 places). Next logs: FLq, Tr11, leanzbf R9d,
 R12s_combo.
STATUS 02:37: reg2 ROUND 13 (target 4):
 21.1 ALL 29 HIT-FREE PATTERNS SETTLED: tools (O1)-(O4) and (PS) checked (Newton: p_1..p_4 = 0 => e_1..e_4 = 0 => entries are the roots of x^5 - e_5, distinct or
   all 0; with v_0 = 0 and p_1..p_3 = 0 the other four are c(1,i,-1,-i) up to order; then 1, v, v^2, v^3 are independent by Vandermonde). The (2,2,1,1|) case
   split A1 / A2 / B is correct (A2 and B die by (PS): the linear conditions sum, <.,u>, sum u^2 ., sum u^3 . cut V to C u). RE-RAN the exact parts:
   hand221_110_A/B, hand2111_1001_D1b/D1c/D2s1/D2s3: all EMPTY. => Leaf 11 item "every line-spanned 6-dim 4x5 level space satisfies (S6-FO2)" CLOSED
   (with M111 and the 1111_11a family, both certified exactly by me).
 21.4 !! reg2 FOUND A GAP IN ITS OWN DEFORMATION TABLE (rounds 8-10), which I had passed in rounds 12/14: defo_scan.py deformed only parts given by EXACTLY two
   basis elements; parts written with SPANNING SETS (213, 2121V*, 11121A1/B1/B2, 2211BD, 21111*) were never deformed. My earlier verdicts "all level-for-all
   and special-locus skew deformations V-r12" and "double deformations V-r14" covered the table AS LISTED, not its completeness -- I missed this.
   RELABEL: Branch 4 deformation items -> GAP (being closed): new level-for-all families 2121Vni, 2121Vnii_xinf, 2211BD (row 0->1) + many special loci;
   numerically (9,3,7); exact certificates (21.5) and a redone double-deformation scan pending.
 21.0 empty-output wrapper cause (warning truncation at 6000 chars when elim.lib + primdec.lib both load): their other drivers checked by reg2; my own
   drivers read full stdout or grep the verdict line -- not affected (my rows4 / rigid runs printed the tail; the full outputs end with the verdict).
 21.2 rows-team spaces re-classified at tolerance 1e-4: 6 line-spanned (closed), 6 with a free column on four rows (PFC, conditional on (5,1)_m0), 7 block spaces
   (presumably members of the new deformation families).
STATUS 02:38: stage3 sec. 39 (column-element route, exact formulation ST3-TWOCOL): RIGOUR NOTE (same type as my PROD flag): "x* has a second nonzero column" is an
 OPEN condition (Rabinowitsch u3 r_{I2,J2} = 1), so "UNIT on all 16 jobs at P1" proves the column-element statement only over F_pbar; in char 0 it is evidence,
 because a char-0 two-column solution may reduce to a one-column solution mod p. It becomes proof-grade inside a WHOLE-COVER argument at P1 for a CLOSED target
 (e.g. "no stratum-(III) X with defect <= 2 extends to an (S3-a) L", with the column-element part killed at the SAME prime by the transposition/branch-2
 systems), as in R11.6 -- or if run over Q. The 'colel' runs (x* = w (x) e_J) are over Q as well as P1: those are fine. Sec. 39 (B) D_3-linear closed form: not
 re-derived this round.
STATUS 02:55: AUDIT of ncol THEOREM SN (R5.4, R5.6-R5.11), coordinator request.
 (iv) THE LIFT -- VALID, with two clarifications. Let Y be the pair scheme (closed in Gr(2,5) x Gr(2,5) over Z). Y_p is 0-dimensional (p = 65521: degrees
   864/828/792 reproduced), and Y_Q is 0-dimensional by semicontinuity (R4.3), so Y x Spec Z_(p) is proper and quasi-finite, hence FINITE: Y = Spec A,
   A a finite Z_(p)-module. FLATNESS IS NOT NEEDED: for a finite Z_p-module N, dim_{Q_p} N(x)Q_p = rank N <= rank N + #torsion summands = dim_{F_p} N/pN,
   i.e. generic length <= special length, which is the direction used. Clarification 1: the localisation at the reduction s-bar of a same-node point must
   be taken over the COMPLETION Z_p (or a Henselisation), where a finite algebra splits as the product of its local factors; over Z_(p) itself it need not.
   Then N := (A (x) Z_p)_{s-bar} has special length 6 (computed mod p) and generic length = sum over the char-0 points specialising to s-bar of their local
   lengths. The same-node point s (defined over Q(i), and Q(i) embeds in Q_p because p = 1 mod 4) contributes its char-0 local length 6 (R5.4 over Q(i),
   one orbit). Any further char-0 point would push the generic length to >= 7 > 6: impossible. Clarification 2: the 18 (30) same-node points must reduce to
   DISTINCT points mod p (else the local length mod p would be >= 12) -- satisfied, since 18 distinct points of length 6 were found in the charts.
 RANDOM M IS ENOUGH: {e <= 3} is contained in {rank M <= 3} for EVERY combination M of the 12 defect generators (rank M <= e), so a random M only risks
   the test FAILING (extra points), never a false conclusion; the full minor ideal is not needed. The S5 x Z2 orbit reduction remains valid although
   det M is not symmetric: what is proved per orbit chart is {e <= 3} cap C_rep c {same-node points}, and both {e <= 3} and the same-node set are invariant.
 THE MOD-p STEP: in each orbit chart, vdim(G + det M) = sum of the local lengths of all points of the chart with rank M <= 3; if it equals 2 x (number of
   same-node points in the chart), every such point is same-node. Targets 24 / 12 / 0; verdicts: 01_02 = 12, 01_23 = 0 (ncol/gb/pairs/sing/q_01_02.out,
   q_01_23.out: VDIM_G 828 / 792 reproduced, VDIM_G_PLUS_DET 12 / 0); 01_01 pending. Loading msolve's reduced grevlex GB as a standard basis is fine
   (msolve's prime-field F4 is deterministic; same ordering and variable order; VDIM reproduced as a check); det by Laplace with reduction is a computation
   in the quotient ring: fine.
 CROSS-CHECK BY MULTIPLICATION MATRICES: NOT yet available. I ran ncol's lenmm.py on mm/c0102: it stops at its own commutativity assertion because
   mm/c0102.mm is INCOMPLETE (only M_1, M_2 present -- the generating Singular run mm_01_02.sing ended with "halt 1"); mm/c0101.mm has M_1..M_10 and part of
   M_11 (still being generated). So "cross-checked by multiplication matrices" is not yet true for any chart.
 VERDICT: THEOREM SN's logic is sound (no flatness needed; completion for the local splitting; random M suffices). It is proved once chart 01_01 gives 24.
STATUS 02:57: ncol chart 01_01 LANDED: sing/q_01_01.out VDIM_G 864, VDIM_G_PLUS_DET 24 = 12 same-node points x local length 2 (target 24). With 01_02 = 12 and
 01_23 = 0, every F_p-bar point (p = 65521) of the pair scheme with rank M <= 3 is a same-node point, and by the lift (audited above) THEOREM SN holds in char 0:
 a product-type column-centred 3x5 level 4-space has e <= 3 iff it is a same-node pair W (+) W (defect e_k^perp cap V5, column k neutral). VERIFIED (modular count
 + rigorous lift; counts taken from ncol's runs, method checked; the multiplication-matrix cross-check is still not available).
STATUS 02:58: LEAN WINDOW 3 -- leanfl/FLq_w0235.log (FLq.lean, 15610 lines, over C): exit 1, 19 errors, 0 "declaration uses sorry", 1384 s, peak 5.95 GB.
 Axioms line: 'PEqualNP.Outside.L_gct_210' depends on [propext, Classical.choice, Quot.sound] (the final theorem = SL + FL, as in FLk, which does not use
 the failing parts). The 19 errors sit in 8 declarations, ALL in the late TC5 blocks (from line 12330 on): TC5_P3 (1, typeclass stuck), P4_k2_conf (1),
 chi_t12 (1, no goals), cramer (2: unknown identifier div_add_div_same -- a Mathlib rename), P4_c2_canon (3), sig23 (5, "function expected"), c2iii_zeta (5),
 F1_w0 (1, max recursion). Everything before line 12330 (incl. the TC5 (P1)/(P2) blocks and the earlier P4 pieces) elaborated without error. So: the C-version
 TC5 is not yet Lean-checked either; the errors look local/mechanical (a renamed lemma, elaboration issues), but TC5_P3 itself is among them.
STATUS 03:14: LEAN WINDOW 3 -- leanfl/Tr11_w0258.log (Tr11.lean, 7411 lines, closure of the round-11 TC5 parts over C): exit 1, 20 errors, 0 sorry, 917 s,
 peak 5.3 GB. Errors in the SAME declarations as FLq -- TC5_P3, P4_k2_conf, cramer (div_add_div_same unknown), P4_c2_canon, sig23, c2iii_zeta, F1_w0 -- plus
 C2iiiLag_proof (2 x "no goals"). Consistent with FLq: the late TC5 blocks have about 8-9 broken declarations (mechanical-looking), nothing else.
 leanzbf R9d_w0313.log started 03:13; R12s_combo after it.
# ROUND 20 (start 03:15 UTC). Targets: (1) leanzbf R9d / R12s_combo logs, then leanfl Stage A (TrK0p, FLK_FL) + FLq rebuild; (2) stage2 R16/R17 (automatic kernel
#  kill on 18 families, symmetry cuts, T1cert over Q, Deg empty; is F2col = finitely many lines + fixed members?); (3) rows R15 plane-test reduction + exact
#  sub-cases; leaf 3 status; (4) reg2 new deformation families / R3 cones, stage3 round 19. Also re-check ncol's mm files.
STATUS 03:18: ncol MULTIPLICATION-MATRIX CROSS-CHECK now DONE by me with the regenerated (complete: 12 matrices each, commutativity asserted) files:
 lenmm.py mm/c0102 -> length 12 (rank of mult-by-det 816 of 828); mm/c0101 -> length 24 (840 of 864). Both agree with the std/vdim counts. THEOREM SN: two
 independent counting methods agree in both charts with same-node points (01_23 = 0 by std; its mm file c0123 is being generated).
STATUS 03:18: TARGET 2 -- stage2 R16/R17:
 Deg = EMPTY: VERIFIED from stage2's certificate polynomials (r16/jump_Deg.log): failures only via (a) rank B_z < 7, the polynomial being a_z^5 (a_z - 1)^4 (5a_z + 6)
   (I factored it: roots 0, 1, -6/5; for z = 3 the same in a3 = -1-a1-a2); (b), (c) never. Deg = triples with every a_z in {0, 1, -6/5} and a1+a2+a3 = -1:
   the possible sums are 0, 1, 2, 3, -6/5, -1/5, 4/5, -12/5, -7/5, -18/5 -- never -1. EMPTY.
 S_4 cut on the jump plane: survivors are S_4-invariant, and each image of the lemma gives a_i = -8 a_j or a_i = 0; all a_k != 0 would force a_1 = 64 a_1:
   impossible; so some a_k = 0, and the sub-family {a1 = 0} leaves the points a = (0,-8,7) (fixed data, 56/56 at P1, RED-p) and (0,0,-1) (exact): CLOSED.
 Special Z (R17-3, "big kernel" lemma): B_c nondegenerate on C/K (5-dim) => dim L'' cap K >= 2; a 2-dim q0-isotropic subspace of the 3-dim K forces q0|K
   degenerate; det q0|K = 5376 nu^2 (nu+1)^3 (3nu-1)^3: correct reasoning; exceptional nu handled by symmetry / fixed data. VERIFIED (as logic).
 T1cert over QQ (R17-1): proof-grade in form (Singular std over Q, injectivity charts unit; denominators = exceptional factors); not re-run by me.
 The 18 tree families: kernel kill automatic (r16_tree.py) -- not re-run; logic is the same lemma (verified R15-4).
 IS F2col NOW "finitely many 1-parameter lines + fixed members"? For ruling R2: YES modulo runs -- generic nu collapses (S_3 cut) to finitely many nu-lines
   (ST2-R2LINES / R2SYMLINES pending) and the invariant families A, J_A to points; jump locus and special Z CLOSED. NOT YET for ruling R1: same kernel kill
   (q0(k,k) = 2 lam (a1+2a2+2a3-6)), but its exact common rank-drop locus is still queued (ST2-R1COF). Cross-type chart 2-3-5-7: pending cross-check.
STATUS 03:19: TARGET 3 -- rows R15:
 PLANE TEST (R15.1): VERIFIED as a reduction. In the Lemma-RS normal form K_0 := span(e1, n) = rho^{-1}(C u) (rho(e1) = u, rho(n) = 0) is a strongly level plane
   inside K; its columns are (u - a_k n_k)/2 and -n_k/2 with n_k = be_k f_k, a_k = al_k/be_k (be_k != 0 on supp n), sum n_k = 0, and sum_k a_k n_k = sum M_k e1
   minus zero columns = 3u (support 5) or 3u - u = 2u (support 4, column 5 zero) -- consistent with rows' bug fix. If every n-column is nonzero, every
   support column of K_0 is nonzero, so "no such plane" excludes the case: a valid NECESSARY condition. The plane split for zero n-columns (R15.4) needs the
   separate rank-1-column sub-case rows mention.
 RE-RAN: pl5Q_P5.sing, pl5Q_S23.sing (support 5, exact over Q(i)): dim -1 unit 1; calibrations cal2 (support 2: dim 2) and cal3 (support 3: dim 1 after the
   column saturation): non-unit as they must be.
 LEAF 3 STATUS: closed in char 0 EXCEPT -- support 4: G (unit mod P1 only; exact pl4fQ out of memory at 0.87 GB -> big slot); support 5: P2 (mod P1 in all four
   sub-cases, exact in progress), G4-A, R4, R5 (big slot). That matches the coordinator's list. (mod-P1 units here are NOT char 0: open column conditions,
   as rows themselves state.)
STATUS 03:30: LEAN WINDOW 3 -- leanzbf/R9d_w0313.log (R9d.lean, 11973 lines; STUB TEST): exit 0, 0 errors, 469 "declaration uses sorry" (= 469 sorried declarations in
 the file, as designed), 880 s, peak 4.7 GB; final theorem True ("does not depend on any axioms" -- meaningless for a stub test). COMPILED IN FULL (no sorry in
 their own bodies): t1_proof : T1Hyp, t3f2_proof : T3F2, t3rest2_of_t3f2, t1_of_t3f2, lemB, orient1_noT0, orient2_noT0, a3w_o1, a3w_o2, and the REPAIRED
 dispatch t1_IIi. STUBBED there: all 98 t3p_* core lemmas, t3_trans and t1_of_t3rest2 (both compiled in full in R7s_t3, window 2), and the earlier lemmas.
 => T1 is now Lean-checked as a chain across stub files (R7s_t3 + R9d + R6t_stub + earlier full files), MODULO the 95 t3p_* core lemmas that have never been
 compiled (3 samples compiled in R6t_stub), and modulo the identity of statements between stub files (leanzbf's design; the full file R7c, 0 sorry, is the
 real test). R12s_combo_w0328.log started 03:28.
STATUS 03:32: ncol ROUND 6 -- SPLIT ISOTROPIC (5,1) (coordinator item):
 (a) COVERAGE: isotropic m in 1^perp has |supp m| in {3,4,5} (|supp| 2 gives <m,m> = 2c^2 != 0). Zero-free -> R2.14 (via CC3); one zero -> THEOREM R32; two
   zeros -> THEOREM Z2 (m = (1,w,w^2,0,0) up to S5 and scaling: the only isotropic 3-support line). Complete. R32 setup checked: R5.1 (alpha == 0 on ker c:
   otherwise row 0 of J + Y_1 is a multiple of e_n and C_n(Y_1) = 0, against the neutral column C_n == 24); L' = C e_0 m'^T + ker c, ker c in Gr(4, U),
   U = (V3)^4 + V4 (11-dim); CC34 (V-r18) gives a single-column element (0|y') in ker c; the incidence variety {(0|y') in L''} is a Gr(3, U/Cy')-bundle over
   P(V4), projective; the y'-chart uses S3 on rows 1..3 and the Plucker orbits only the residual Z2 (rows 2<->3) with S4 on columns: consistent; 8 orbits
   sum to C(10,3) = 120. Equations R_4 = 0 and m'_l R_k - m'_k R_l = 0 (defect in C(m',0), which implies level since sum m' = 0) + the m'-conic: closed.
   Z2 setup: Gamma(C m) = span(1, e_3, e_4), row 0 of ker c = -(alpha 1 + delta e_3 + delta' e_4); L'' in Gr(4,13); symmetries rows 2<->3 (a <-> b, since
   swapping rows 2,3 exchanges nu_1 and nu_2), columns 3<->4, cyclic (0 1 2) (m -> w^2 m, a scaling of the line): correct; 82 orbits (their script).
 (b) RED-p: both systems are closed and projective, NO saturation and NO Rabinowitsch; p = 65521 = 1 mod 12 puts w and i in F_p, and the coefficients lie in
   Z[w]: a char-0 solution reduces at a prime above p chosen compatibly with the chosen w mod p, so one computation covers both roots. The staged
   refinement (adding p_T = 0 for charts T in orbits verified empty earlier: single exchanges = entries, double exchanges = 2x2 minors) is sound by
   induction, with no circularity (stage order neutral -> one-delta -> delta-delta'). Calibration: smaller spans NONUNIT (d = e + 3 boundary). VALID.
   RE-RAN samples with fresh outputs: R32 charts c016_J2, c089_J0, c048_J1, c014_J3 -> [1]; two-zero z_0_1_6_12, z_0_3_4_10 (plain), z_1_2_3_9, z_1_2_3_4
   (refined) -> [1]. (Same generators -- re-runs, not independent generators.)
 (c) CC3 dependency of R2.14: CC3 is exact over Q (case analysis + three survivor GBs, V-r16); R2.14 itself is V-r16 given CC3. Fine.
 => COROLLARY SPLIT-ISO (no (5,1) space has a row carrying an isotropic defect line) holds in char 0, given CC3 (exact), CC34 (RED-p, my own generator),
   R32 and Z2 (RED-p at 65521, ncol's generators, samples re-run). With SPLIT (non-isotropic m): NO SPLIT (5,1) SPACE AT ALL.
STATUS 03:35: R31Hyp SIZE (coordinator item; leanzbf's per-configuration DFS = ~6 MB raw). DATA from my exact R3-1 code (verify2/r20/r3_minkill.py, an
 instrumented copy of verify2/r3_exact.py; log verify2/r20/r3_minkill.log, one CONF line per configuration with its factor counts and a MINIMAL killing
 subset of column triples): the same 1800 -> (E1) -> 120 killed + 12 survivors as round 2. EVERY one of the 120 killed configurations is already killed by
 the DFS restricted to AT MOST 3 of its constraining triples: 24 by 2 triples, 96 by 3 (vs 1069 constraining triples in total, ~9 per configuration).
 Factor-count patterns of the minimal subsets (0 = no linear factor, i.e. only the zero branch; 1; 3 = three linear factors): (3,0,0) 28, (3,3,3) 19,
 (3,3,0) 18, (3,1) 15, (3,3,1) 8, (3,1,1) 6, (1,3) 6, (0,3,0) 4, (3,0,3) 3, (0,1) 2, (0,0,3) 2, (3,0,1) 2, (3,1,0) 2, (1,1,1) 1, (0,0,0) 1.
 CONSEQUENCE for the Lean size: per killed configuration only <= 3 cubic certificates and a DFS with <= (1+3)^3 = 64 leaves are needed -- at most
 24*2 + 96*3 = 336 certified triples instead of ~453, and much smaller DFS trees. I see no single structural lemma in this data (no factor type kills
 uniformly); the minimal subsets are the best concrete lever. (Survivors: 12, killed by (E5) by hand, as before.)
STATUS 03:56: LEAF-3 AUDIT for closing (coordinator request; rows/leaf3/MANIFEST.txt, closing draft R16.3):
 (1) PLANE TEST + SPLIT: R15.1 verified earlier this round. The SUBZ/STAGED split for zero n-columns is COMPLETE: at a zero n-column k the plane column is
   y1 (u - al_k f_k)/2, either zero (sub-case z_k: al_k f_k = u, i.e. sigma_k = s0 and al_k = 1, and then column k of K is the rank-1 y2 (w - m_k)/2,
   handled with the full K system) or nonzero (sub-case A: saturate, plane stage, then the full system). Saturations are open conditions, but every char-0
   verdict here is an EXACT run over Q(i), so no RED-p issue.
 (2) CASE TREES: support 4 complete (V-r18). Support 5 complete: groups of equal isotropic direction with <= 3 directions must each sum to 0 (3 isotropic
   directions are independent), so groups have size >= 2: |supp n| = 2: P2; 3: P3; 4: P4, PP (2+2), G4 (4 distinct, one relation); 5: P5, S23 (2+3), R4
   (4 directions: the parallel pair must have nonzero combined coefficient, else 3 independent singletons would sum to 0), R5 (5 distinct). (2,2,1) and
   (3,1,1) are impossible. Complete.
 (3) CHARTS AT INFINITY / vert.py: the conic chart misses one octahedral vertex; S_4 (rows) acts transitively on the 6 vertices; a configuration with <= 5
   distinct isotropic points can be moved off it. Only R5 and G4 can have 6 distinct points (u + 5 distinct f's; u + 4 n-directions + f_5); every other
   shape has <= 5. vert.py: V = the 6 vertices (each isotropic with one zero coordinate: checked), u = vertex 0 WLOG, all 5! assignments, full plane
   system with the correct sums (sum n = 0, sum al_k f_k = 3u) and saturations (be's, plane column 5 for G4). RE-RAN over Q(i): R5 120/120 unit (3.2 s),
   G4 120/120 unit (2.7 s). VERIFIED.
 => Leaf 3 can be marked CLOSED in char 0 the moment R15GQ (support-4 G), R16P2z3 + R16P2A (support-5 P2), R15G4P/Q (G4-A), R15R4P/Q and R15R5P/Q land
   UNIT over Q(i).
STATUS 03:57: reg2 ROUND 15 (coordinator item):
 (1) 23.3 COMPLETENESS ARGUMENT: CORRECT as a statement of what must be checked. Given (BL) and Theorem 19.3 (verified as a conditional reduction, V-r19),
   M = Lin(M) + genuine parts of types R1/C1, R2/C2, N, [R3]; choosing genuine elements that span M mod Lin(M) gives a combinatorial type tau (line
   pattern (a|b), e, genuine parts with row/column pairs, types, incidences) with e + (chosen genuine dim) = 6; the set of types is finite, and EVERY
   6-dim level M is a point of the solution set of its type. So "solve every type exactly" is exhaustive given (BL) -- and given that the genuine-part
   list is complete, i.e. R3 is excluded or added as a type. Deformation scans only reach components ((G1)-(G5) are real limitations; (G4) occurs).
   Agreed: e = 6 complete (all line patterns, V-r19); e <= 5 NOT exhausted.
 (2) ntype1 (23.4) CHECKED INDEPENDENTLY (verify2/r20/ntype1_mine.py, exact over Q(sqrt(-3)) with DomainMatrix ranks; ntype1_num.py numerically):
   level identically, dim 6, dim T_1 = 10 -- agree. BUT rank q_Y on T_1 = 4, NOT 5, at both of reg2's Y = (1,2,-1,3,1,-2), (2,-1,1,1,-3,1) and a third Y
   (exact); numerically the singular values of q_Y are 1, 1, .25, .25, then 3e-15 (resp. 1, 1, .25, .083, then 1e-15). So reg2's "FO2 <= 7" is an ERROR
   (an overestimated rank -- probably sympy's symbolic zero test with sqrt(-3) in Matrix.rank); the correct bound from one q_Y is (10-4) + 2 = 8, which
   STILL gives (S6-FO2) for ntype1. Verdict: ntype1 closed with FO2 <= 8 (not 7). Recommendation: use DomainMatrix over QQ<sqrt(-3)> (or mod-p ranks) in
   q_rank_exact.py.
 (3) Leaf 10 size: L -- needs an automatic exact type solver (e = 5: 29 line patterns, 296 types before incidence splits; e <= 4: thousands) or cutting
   lemmas (e.g. "R1 => rank one isotropic", still a conjecture), plus (BL) and R3.
STATUS 03:59: LEAN WINDOW 3 -- leanzbf/R12s_combo_w0328.log (R12s_combo.lean, 16201 lines, STUB TEST with the round-10/11 blocks incl. the R31 setup): exit 1,
 43 errors (40 distinct lines), 371 "declaration uses sorry" (as designed), 1797 s, peak 5.7 GB. Errors in about 20 declarations, mostly MATHLIB RENAMES:
 Unknown constant Equiv.Perm.apply_inv_self / inv_apply_self (typeCl_perm x8, colPerm_inv, vecPerm_injective, zf_perm, piiBody_perm, pairI_perm, ...),
 Unknown constant Polynomial.coeff (quad_poly_ne), one heartbeat timeout, follow-on "unsolved goals"/type mismatches, and a kernel "unknown constant
 ZBF.fk_col" (consequence of an earlier failure). Affected R31 pieces: r31_of_canon, f13_cases_* (6), e3_final, finrank_ker_rho, dual_eq_pairDual,
 gen_col_ann, stest_gen. Nothing in R12s_combo compiled cleanly enough to add to the "compiled in full" list beyond what the log shows per declaration;
 the R31 setup is NOT yet Lean-checked. Window-3 summary: R9d clean (T1 chain modulo 95 t3p lemmas); FLq/Tr11/R12s_combo with localized, mostly
 mechanical errors; FLK_field/TrK11 postponed.
# ROUND 21 (start 04:00 UTC). Targets: (1) Lean logs: TrK0p_port, FLK_FL_port, FLq_rebuild (TC5_final over C), R14s_shape_x, R9f_window4 (full, 0 sorry);
#  (2) leaf 3 big-slot verdicts -> CLOSED when the last is unit; (3) ncol round 7: THEOREM R211-3 + K' census; (4) stage3 TWOCOL over Q, stage2 R2 symlines /
#  R1 cofinterp2; (5) PROOF-MAP top list incl. leaf-10 resizing.
STATUS 04:01: TARGET 3 -- ncol round 7:
 THEOREM R211-3 (conditional on the K' classification): the (L6) system checked -- K' fixed (rigid type over Z[w]), U_0 in Gr(2, t^perp cap V5) (3 charts),
   Z in P(V_Z/K') = P^8 (9 charts, INCLUDING the closure lam = 0, which RED-p needs since a char-0 point with lam = 1 may reduce to lam = 0), defect-in-C via
   the generalised cross product w' of 1, t, u_1, u_2 (never zero: t is non-isotropic, so t, u_1, u_2 are independent in V5), c^(0)(Z) in C1; closed,
   projective, coefficients in Z[w], no saturation: RED-p valid. RE-RAN all 27 charts (ncol/r7/l6/*.ms, p = 65521, fresh outputs): 27/27 [1].
   Calibration (5-dim part automatically level; noZ variant NONUNIT 15/15) as stated. VERIFIED -- CONDITIONAL on R7.2.
 K' CENSUS (R7.2): 6 numerical hits, all of ONE rigid type K'(p,q;s1,s2) = span(nu_1 (e_p-e_q)^T, nu_2 e_s1^T, nu_2 e_s2^T) (+ mirror); e = 1 exactly by
   Lemma SL_3 (V/Lean); the 60 points satisfy the exact chart systems and are reduced (Jacobian rank 24 mod p). EXACT classification NOT done (0-dim scheme
   in Gr(3,10) x P(V5): 015_J0 unit, other charts segfault at 2 GB). Plan (staged refinement + SN-type length argument) is sound in principle -- it would
   need the local lengths at the known points in char 0 and mod p (as in SN) and a whole-cover count. Status: R211-3 conditional; case (C) sub-case
   dim(U_i + U_i o w) = 2 not started.
STATUS 04:11: LEAN -- leanfl/TrK0p_port.log (TrK0p.lean, 1474 lines, port profile run): exit 1, 42 errors, 0 sorry, 729 s, 5.3 GB. ALL 42 are "unsolved goals"
 left by linear_combination (norm := first | field (disch := ...) | ring1) steps whose certificates divide by numerals (e.g. (1/9) (e1 - e2) - (1/72)(e3 - e4)
 at lines 731-734): over a general field Kf the normaliser does not close them (numeral inverses need explicit nonzero facts; the discharger
 'assumption | simp only [nzs]' does not finish). This is exactly the anticipated risk ("simp/norm_num calls that used CharZero silently"): an engineering
 obstacle of the port, not a mathematical one (the same certificates work over C, and the numerals involved have prime factors 2, 3 only). Fix for leanfl:
 multiply the certificates through by the common denominator, or close with field_simp [nz9, nz72, ...] then ring.
STATUS 04:12: PREP for the FLq rebuild audit: lean/fl/FLq.lean (16657 lines, 0 sorry, no axiom declarations) states TC5_final (K : Submodule C M45)
 (hdef : DefLine K mTC) : finrank K <= 4, with DefLine K m := every Y in K has P4_a(J+Y) = 24 + theta(Y) m_a and mTC = e_0 - e_1 -- exactly THEOREM TC5
 (no 5-dim 4x5 space with defect inside C(e_0 - e_1), defect 0 included); proof TC5_of_c1R C1R_proof, no Hyp arguments. NOTE: the file's final theorem
 L_gct_210 is still SL + FL only, and leancompile prints "#print axioms" only for that theorem; so for TC5_final the certificate is "0 errors + 0
 sorry-warnings + no axiom declarations in the file", not the axioms line.
STATUS 04:24: CHART B REDUNDANT FOR SYM-M UNDER R11.6 (coordinator check): CONFIRMED. P(W_P) for P = {0,1,2} is the line {(m0 : m1 : -m0-m1)}. Chart A
 (m0 = 1, m = (1, t, -1-t)) contains every point with m0 != 0; the only other point is (0 : 1 : -1), two-column. Inside chart A the zero entries occur exactly at
 t = 0 ((1,0,-1)) and t = -1 ((1,-1,0)), both two-column, and "u t(t+1) - 1" removes exactly these. In R11.6 the reduced point m'' lies in P(W_P)(F_pbar):
 two-column -> TC5_p; otherwise m'' is in chart A with t(t+1) != 0, and K4 is a point of a chart-A case system there. Chart A's cover is honest at every t
 (R11.8: the m^perp basis has a constant unit 4x4 minor; R11.1: (F2)/(F4) use only the neutral columns). So whole-cover RED-p needs NO chart-B systems.
 (Chart B would matter only if a chart-A case system used a normalisation degenerating at some t other than 0, -1 -- none is claimed, and chart B would not
 repair such a defect anyway.) Dropping SYMDC3V2_B0 and SYMT22_B45/B21/B18 is sound.
STATUS 05:16: (resumed after the usage-limit cut at ~04:25). The obsolete round-13 waiter task (s2slim) was killed by the harness for memory pressure while idle --
 harmless, not restarted.
STATUS 05:16: LEAN (big-slot extras) -- three logs:
 (a) leanfl/FLq_rebuild.log (FLq.lean, 16657 lines, over C): exit 1, 7 errors, 0 sorry, 1667 s, 7.3 GB; L_gct_210 (SL + FL) axioms standard. The 7 errors
   are ALL heartbeat timeouts (maxHeartbeats 200000) in THREE declarations: P4_c2_canon (3), F1_vprod (1), noline (3). My dependency scan (textual closure
   from TC5_final over the file's declarations) shows TC5_final DEPENDS ON ALL THREE. In Lean 4 a failed proof still enters the environment with sorryAx,
   so TC5_final elaborates but would depend on sorryAx: TC5 over C is NOT yet Lean-proved. Fix: set_option maxHeartbeats N in for these three (no
   mathematical issue reported). Everything else, including the 2 GB of earlier P1-P4 blocks, elaborated cleanly.
 (b) leanfl/FLK_FL_port.log (FLK_FL.lean, 712 lines, FL over Kf): exit 1, 1 error ("unsolved goals" in propR, the 120-normalisation lemma, line 552),
   0 sorry. FL over Kf depends on propR -> not yet clean; same family of issue as TrK0p (numeral/division normalisation over a general field).
 (c) leanzbf/R14s_shape_x.log (stub test): exit 1, 101 errors = 100 x "failed to synthesize Decidable ((fun i => i) <0,_> = 2 <-> 0 = 2) ..." at ONE line
   (4859, f13_cases_00012) + "maximum number of errors reached, exiting": the compile STOPPED there, so nothing after line 4859 was checked. 394 sorry.
   Mechanical: decide on an un-beta-reduced Fin proposition (fix: simp only / beta_reduce before decide, or Fin.decEq-based instance).
 R9f (window 4) not started yet. SYMDC3V2_A0 in the big slot since 05:11.
STATUS 05:17: ncol ROUND 8 -- THEOREM L6G and COROLLARY K'-KILL:
 L6G: RE-RAN all 39 charts (ncol/r7/l6g/*.ms, p = 65521, fresh outputs): 34 UNIT, 5 NONUNIT each with a LINEAR reduced Groebner basis (one point, lam = 0) --
   exactly ncol's pattern. Length argument checked (same as SN): the scheme {(U_0, Z)} is closed in Gr(2,3) x P(V/K') over Z_p[w]; special fibre = 3 points of
   length 1 (vdim 1 per chart); the 3 points are rational (denominators 3, so distinct mod p) with char-0 Jacobian rank 14 = full (length 1); generic length
   <= special length (finite Z_p-module, no flatness) => in char 0 these 3 points (single-column elements Z = x e_j^T, lam = 0) are the ONLY solutions. VERIFIED.
 K'-KILL: every Y in ker c is a solution with lam = 0, so P(ker c/K') lies in 3 points, dim(ker c / K') <= 1, rank c = 3, c(L') = C contains t, and a Z with
   c(Z) = t would be a solution with lam != 0: contradiction. VERIFIED as logic (uses R2.3: U_0 = C cap t^perp). Both remain CONDITIONAL on the K' classification
   (big slot NCOL-K3CLASS). Case (C) now down to the last piece (types a3, b22, b23 of dim(U_i + U_i o w) = 2, rank c = 3, rho = 2). ncol's erratum R8.4
   (under-sampled LM probes withdrawn) noted: none of my verdicts used those probes.
# ROUND 22 (start 05:18 UTC). Targets: (1) audit rows R17.5 reduction ((SM4) + (SM5) cover the remaining leaf-3 cases? identity chart honest?); (2) landings:
#  SYMDC3V2_A0, TrK0p rerun, R14t_shape, R9F, SM5P/SM4P; (3) stage2 R2 lines / R1COF2; (4) PROOF-MAP.
STATUS 05:19: TARGET 1 -- rows R17.5 (isotropic slice) AUDITED: VERIFIED as a reduction.
 (b) leaf 3: in the Lemma-RS normal form every element Y_ka = e1 + ka n of the plane K_0 has row sum rho(Y_ka) = u (rho(n) = 0), isotropic and nonzero, and
   is a strongly level MATRIX (every line of a strongly level space is). Column k of Y_ka is (u - (al_k + ka be_k) f_k)/2: for be_k != 0 it vanishes for at
   most ONE ka (only if f_k || u; never if u, f_k independent); for be_k = 0 it is (u - al_k f_k)/2, independent of ka. So for all but finitely many ka the
   support of Y_ka is exactly the plane support {be_k != 0} u {be_k = 0, al_k f_k != u}. Every remaining case has plane support >= 4: support-4 G (4),
   P2-A (4); support-5 G4-A (5), G4-z5 (4), R4 (5), R5 (5), P2-A (5), P2-z3 (4). So (SM4) + (SM5) exclude ALL of them; plane supports <= 3 are exactly the
   sub-cases already settled exactly. Correct.
 (a) (PL) <= (SM5), PL4 <= (SM4): Y_u = R^{-1} u has columns (u - B_k u)/2 (A_k = (R - M_k)/2, M_k = B_k R); column k vanishes iff u in Fix(B_k); for B_k != I
   (= column k nonzero on K) Fix(B_k) has dim <= 2 and contains <= 2 isotropic lines (no 2-dim totally isotropic subspace in 3-dim V); the isotropic cone has
   infinitely many lines, so a generic isotropic u gives all columns of K nonzero in Y_u. Correct.
 (c) degree 2 for one matrix: <y_k, f - y_k> = 0 <=> |f - 2y_k|^2 = |f|^2 = 0 (f isotropic): g_k isotropic; sum g_k = n f - 2 sum y_k = (n - 2) f. Correct.
 CHART: (SM_n) involves ONE isotropic point f (the row sum), normalised as f = c(s0); the conic chart misses only the vertex c(inf), and a row permutation
   (S_4 acts transitively on the octahedral vertices, and (SM_n) is invariant: strong levelness, column count, isotropy of the permuted row sum) moves f off
   it. Scaling: (SM_n) is about the line C Y (homogeneous P_k conditions), so fixing the scale of f is legitimate. ONE identity chart is honest.
 RIGOUR: the "columns nonzero" saturations are open conditions, so SM5P/SM4P at P1 are triage; char 0 needs R17SM5Q/SM4Q (over Q(i)), as queued.
STATUS 05:20: TARGET 3 -- stage2 R17 (RESULT-R17, 04:05): cross-type ruling CLOSED by stage2 (kernel kill + S_4 cut -> J u 5 points; 4 RED-p members + J) --
 same lemma as R15-4 (verified) and the same S_4-cut logic as the jump locus (verified); I have not re-run the 4 members. R2 nu-lines: "msolve CHAR 0 [M0] 70/70
 [1] on 11 lines" -- RIGOUR: msolve's char-0 mode is multimodular (stage2's own label: evidence-grade), so these are NOT proof grade; Singular over Q times
 out. A proof-grade route that avoids long Q runs for a UNIT verdict: an explicit certificate 1 = sum c_i f_i over Q (Singular lift mod several primes,
 rational reconstruction, then an EXACT check of the identity), or a whole cover at one prime that is genuinely closed (projective nu with the exceptional
 values decided at the same prime AND no denominators in the setup -- the T_1 rref denominators make the generic-line system non-closed, the same
 p-denominator loophole as D003-PROP). R1COF2 not landed.
STATUS 06:03: D3A OVER Q (my pool run d3a_slim.py, 04:03-06:00): RESULT 70 charts, non-unit 0, FAILED 6 -- 64/70 charts UNIT EXACTLY over Q (slimgb), the 6 FAILED
 = 0-1-3-6, 0-1-4-7, 0-1-6-7, 1-2-5-7, 1-3-4-7 (rc 14: out of memory at 2 GB) and 0-1-3-7 (rc 124: timeout). Biggest successful chart 1.5 GB.
 stage2's BIG-KERNEL route for Case A (R18-2): VERIFIED as logic: B-stack rank 5 with common kernel K (dim 3) = ker B_c for generic c, so B_c is nondegenerate
 on C/K (5-dim), the image of a 4-dim common isotropic L'' has dim <= 2, dim(L'' cap K) >= 2; L'' cap K is q0-isotropic, and a nondegenerate form on the 3-dim K
 has no 2-dim isotropic subspace; det q0|K = 353894400 (a2-1)^2 (a2+a3+1)^6 (recomputed with sympy from the stated 3x3 matrix: exactly this; the matrix itself is
 stage2's, not recomputed from the forms). Survivors only on a2 = 1 (WLOG
 excluded), a2 + a3 + 1 = 0 (alpha_4 = 0: S_4 / X0 coverage, verified V-r15) and the rank/kernel degeneracy set Deg (pending), plus T1cert for D3A.
 HOW THE TWO FIT: a parameter point off Deg is killed by the lemma (charts unnecessary there); a point IN Deg whose L'' lies in one of my 64 unit charts is killed
 by the exact chart verdict (valid wherever bad_poly != 0); the only uncovered set is (Deg) x (L'' lying only in the 6 failed charts). So: if Deg turns out
 EMPTY, Case A is closed without the 6 charts; if not, re-run just those 6 charts with the Deg equations added (far smaller) -- not the full 6 GB d3a_slim6 runs.
STATUS 06:04: rows R18.1 LEMMA CHAIN IS0-IS5 (the isotropic slice as lemmas) AUDITED:
 IS0 (single-matrix degree 2 <=> g_k = f - 2y_k isotropic, sum g_k = (n-2) f): correct. IS1 (B in O(3), B != I fixes <= 2 isotropic directions: Fix(B) has dim <= 2,
 a line has <= 1 isotropic direction, a plane carries a nonzero form since V has no totally isotropic plane, so 1 or 2 isotropic lines): correct. IS2 (principal:
 B_k = I - 2A_k R^{-1} orthogonal by Lemma RS(i); Y_u = R^{-1} u has columns (u - B_k u)/2): correct. IS3 ((2,1) kernels: plane support S_0 for all but
 finitely many ka; the list of cases with |S_0| >= 4 and the |S_0| <= 3 leftovers settled exactly): correct. IS4 (conic form f = c(sg), g_k = la_k c(ta_k), la_k = 0
 allowed: exactly the degree-2 solutions; <= n+1 points; S_4 rows act as T_d on V and as octahedral rotations on the conic, transitively on the 6 vertices, and
 preserve strong levelness; so one affine chart for n = 4, and for n = 5 only the all-vertex configuration needs enumeration): correct. RE-RAN smv.py over
 Q(i): 120/120 UNIT (1.2 s). IS5 = the big-slot computations R17SMC4/5 (P, then Q). => the chain is sound: (SM4) + (SM5) over Q(i) close (PL), PL4 and every
 remaining leaf-3 case.
STATUS 06:15: (1) D003-PROP CASE A CLOSED (stage2 R19-2/R19-3) -- AUDITED: VERIFIED (logic; the exact determinants are stage2's).
 Generic alpha (a2 != 1, alpha_4 != 0): K (dim 3) is the common kernel identically (rref, pivots 0,1,6, denominators 4(a2-1)); a nonzero 5x5 minor of B_c on the
   complement Q = {2,3,4,5,7} gives rank B_c >= 5, and K in ker B_c gives rank 5 and ker B_c = K; gcd over 3 random c = (a2-1)^2 (a2+a3+1)^10, residual common zeros
   inside a2 = 1: so the degeneracy set of the lemma = the setup-exceptional set (NOT the 6 failed charts' business); det q0|K (scaled rref basis) =
   815372697600 (a2-1)^6 (a2+a3+1)^6 != 0. With T1cert for D3A (Singular over Q 12/12, excluded a2 = 1, a2+a3+1 = 0 -- not re-run by me): killed.
 alpha_4 = 0 family (1, a2, -1-a2, 0): own setup; B-stack rank 5, K dim 3 = ker B_c, det q0|K = 28665446400 (a2-1)^2 (a2+1)^6; rank drop for all 4 random c only at
   a2 in {1, -1}; T_1 rank jump (a2-1)^3 univariate exact. a2 = 1 -> (1,1,-2,0) ~ (1,-2,1,0) by swapping coordinates 2, 3 = a2 = -2 on the same family: killed;
   a2 = -1 -> (1,-1,0,0) = X0: killed exactly (R14-5). Zero patterns: one zero moved to position 4 (alpha_1 != 0 kept), two zeros = X0 up to S_4, three
   impossible; a2 = 1 WLOG by S_4 (coverage verified V-r15). => Case A closed in char 0; my 64/70 Q charts are superseded (consistent cross-check).
 (2) Kt3 over quadratic fields (stage2 R19-1): q0|K = g(nu) M, M = [[-1,-7],[-7,-3]] (isotropic lines x = (-7 +- sqrt46) y: disc 46 correct) and [[-1,-9],[-9,-5]]
   (x = (-9 +- sqrt76) y: correct). s^2 - 46 and s^2 - 76 are irreducible over Q, so Singular's minpoly computes over the FIELD Q(s); the Galois automorphism
   s -> -s maps the ideal of one line to that of the other, so UNIT for one gives UNIT for both: the minpoly approach covers both conjugate lines. VERIFIED,
   with one check item: the zeros of g(nu) (where q0|K == 0 and every k in K is isotropic) must be among the excluded / separately handled nu.
 (3) stage3 sec. 42 (D): leaf-8 (1,1,1,1,0) special members include a NEW 1-parameter k_N = 2 family (numerical + exact jump check): "exactly the two known
   special members" is FALSE; noted in PROOF-MAP item 7.
STATUS 06:28: verifyfl R17.4 (lambda-word junk removal, A case 0 piece IV t0c-01/02/12) AUDITED: VERIFIED.
 (a) COVER: in t0c the columns of N are c_k = lam_k(Z) u_k (u_k in the 'ab' chart), lam_k(Z_r) = l_rk free variables. Per k the three options lam_k(Z_1) != 0 ('A'),
   lam_k(Z_1) = 0 & lam_k(Z_2) != 0 ('B'), lam_k(Z_1) = lam_k(Z_2) = 0 (column k of N identically zero) are exhaustive and disjoint; the 8 words = all points with
   no zero column. A point with lam_k == 0 on N is a point of the u_k = '0' piece of the SAME cover (R12.4: the 15 u-pairs containing a '0' -- all UNIT in
   all three S-cells -- and t0b ab:ab:0 for k = 2), decided at P1. So t0c = (8 words) u (decided '0'-pieces): complete. (The check-file content confirms
   genuine variables l00..l12 with Rabinowitsch lines l0k ul_k - 1 resp. l0k = 0, l1k ul_k - 1, plus urt t(t+1) - 1.)
 (b) OPEN CONDITIONS: the word Rabinowitsch conditions and the early urt t(t+1) = 1 are a char-p case split inside the whole cover at P1 (R11.6 form: no F_pbar
   point off the two-column points), so they are legitimate there; the perm relations R14.4/R14.5 are valid in every word (each lam_k is a nonzero linear
   form on N, so a product of them is a nonzero polynomial on N and can be cancelled).
 (c) RE-RAN with fresh outputs: t0c-01 all 8 words WITHOUT perm relations, t0c-02 and t0c-12 all 8 words WITH them: 24/24 [1] (0.01-0.5 s each).
 => piece IV items t0c-01/02/12 of A case 0 are DECIDED at P1 at the N level; the 10 GB rc4 jobs are not needed for them. NOT covered by this: t0c-ne
   (D != 0) and the other A-case-0 pieces (P1a/P1b/P2 open items), which need their own decision.
# ROUND 23 (start 06:29 UTC). Targets: (1) landings: SYMDC3V2_A0, TrK0p rerun, FLq2 (TC5_final axioms), R14t_shape, R17lint, rows W4P/W5P, stage2 ST2-R1COFSING;
#  (2) reg2 round 17 stage-1 kills (NOTES-reg2 25); (3) ncol H-a3-SL (66), H-b22-SL (132), case cover a3, CONJECTURE K0; (4) verifyfl junk removal extensions;
#  (5) PROOF-MAP.
STATUS 06:30: TARGET 2 -- reg2 ROUND 17 STAGE-1 KILLS (25.1) AUDITED: the stage-1 kill is a VALID EXACT NECESSARY CONDITION. For an e = 5 type, the five line
 elements span a 5-dim subspace of M, which is level (a subspace of a level space); stage 1 solves exactly that line configuration (all level equations of the five
 line elements, per incidence class, saturated by the part ranks) in Singular over Q (ring R = 0: twostage.py lines 89-90) -- char 0, no RED-p issue. LINES-EMPTY
 => no 6-dim M of that type and class. The incidence dichotomy (checked V-r17) and the orthogonality pre-kill orth_ok (two orthogonal row parts of dims 3 and
 >= 2 in the 4-dim V; a column part of dim 3 = all of V3, or two of dim 2 in V3: impossible since U perp W forces W in U^perp) are correct. Orbit reduction under
 the type's stabiliser in S_4 x S_5: fine. INDEPENDENT spot check: pattern 0000|11111 (five single-column lines) -- my own equations (perm_inj = 120 identically,
 25 coefficient equations, saturation by each line nonzero), Singular over Q: unit (EMPTY), as reg2's cache says. The 74 stage-1 TIMEOUTs and the stage-2 rank-drop
 subloci (366 LINEAR-GENERIC-KILL classes need the Fitting ideal) are the open parts; stage 2's "linear measure" is numerical (a measure, not a kill).
STATUS 06:32: TARGET 3 -- ncol H-a3-SL (R9.6) and H-b22-SL (R10.1): the K_0-fixed systems are closed projective (Y in P(V_0'/K_0), C on its P^1 charts T0/T2),
 0-dimensional fibres at 65521 => finite in char 0 by upper semicontinuity of fibre dimension (valid, as R4.3); "every Y in ker c is admissible, so P(ker c/K_0)
 finite, dim ker c <= 3 < 4": correct. 64/66 resp. 128/132 charts unit, the rest single points (x e_4^T; nu_1 e_0^T) -- not re-run this round.
 *** QUESTION (possible gap) on the input R9.5 (a) "e(K_0) = 0 => K_0 = span(nu_1(e_a-e_b)^T, nu_2(e_c-e_d)^T) (rigid SL_3 pair)", attributed to rows' Lemma
 SL_3 (c). rows' SL_3 (R3.8, verified by me in round 3) gives for a strongly level 3x5 space Pi: dim Pi = q + dim N with q = dim s(Pi) (s = ROW-SUM map of the
 3x5 part, values in V_3) and N = Pi cap {s = 0}; (c) classifies N (dim N = 2 iff N is the pair); (b) q = 2 forces N = 0; (d) excludes (q, dim N) = (1,2).
 So a 2-dim strongly level Pi can a priori have (q, dim N) = (2,0), (1,1) or (0,2), and only (0,2) is the rigid pair. ncol's K_0 = ker s with s = c^(0) (row 0
 of Y), i.e. "row 0 zero" -- that does NOT obviously force the 3x5 ROW SUMS of K_0 to vanish (q = 0). Unless q(K_0) = 0 is forced by the context, H-a3-SL /
 H-b22-SL as stated cover only the q = 0 strongly level K_0; the q = 1, 2 strongly level 2-dim K_0 would need their own K_0-fixed systems (or an argument
 that they do not occur here). Asking ncol (via the coordinator).
STATUS 06:33: RE-RAN ncol's K_0-fixed systems with fresh outputs: a3 (r9/k0s): 64/66 unit, the 2 others 0-dimensional (tp = -3 point; a non-reduced point) -- as
 stated; b22 (r10/k0b22): 128/132 unit, the 4 others with radical {single Y} x (tp free) or a single point -- i.e. one admissible Y for every C, as stated. The
 fibrewise finiteness transfers to char 0 by the closure/flatness argument applied over each C_0 (as in R4.3). VERIFIED -- still subject to the q(K_0) = 0
 question above. verifyfl R17.5 ('mu' junk removal for P2/P1a/P1b): logic checked -- mu_k = 0 for the isotropic generator means column k of it vanishes, i.e. a
 point of the u_k = '0' item of the same piece; induction on the number of '0' columns is sound once every item is UNIT. Running at verifyfl (201 items).
STATUS 06:33: stage2 confirmed the zeros of g(nu) (Kt3) lie in {0, -1, 1/3} = the exceptional nu's (handled separately): my check item is CLOSED.
STATUS 06:33: second independent stage-1 spot check: pattern 0000|21110 (a 2-dim column part in column 0 + lines in columns 1,2,3; my own equations, saturation by
 the 2x2 minors of the plane and by each line) -- Singular over Q: EMPTY, as reg2's stage 1 says. Two of two spot checks agree.
STATUS 06:34: my own (SM4) generator at P1 (verify2/r22/sm4_mine.py, conic form, 9 unknowns): TIMEOUT at 1700 s / 850 MB, no verdict (triage only; rows' big-slot runs will decide). Running my n = 3 calibration next.
STATUS 06:34: ncol CONFIRMS the q(K_0) gap (NOTES-ncol R10.5): in isotropic coordinates the 3x5 row sums are A nu_1 + B nu_2, the R7.2 K' types have B != 0, and the
 strongly level system for 2-dim zero-row column-centred 3x5 spaces (ncol/r10/slgen.py, all 3 orbit charts of Gr(2,10)) is NONUNIT of Krull dimension 1: strongly
 level K_0 come in 1-PARAMETER FAMILIES beyond the 30 rigid pairs. => THEOREM H-a3-SL / H-b22-SL are VERIFIED FOR q(K_0) = 0 ONLY; the q in {1,2} families are
 OPEN (ncol plans a family-parametrised K_0-fixed system). Recorded as a GAP (found by verify2, confirmed by ncol).
STATUS 06:35: my SM generator CALIBRATED: n = 3 (two zero columns) at P1 is NON-unit of dim 3 (5 s), matching rows' n = 3 calibration -- so the generator is not vacuous; its n = 4 run is simply too heavy for the 30-min pool box (the big slot runs rows' versions).
STATUS 06:46: verifyfl 'mu' sweep (nlam/pc_mu_all.log): 68 P-items done, 64 N-UNIT, 4 FAIL (P1a ab:ab:ab/{ne,01,02,12} at the 550 MB cap). RE-RAN 6 random unit items
 (P1a z1z1ab, z2z1ab, z2abz1, 0z2ab, 0abz1, z1abab) with fresh outputs: 6/6 [1]. The induction needs every excluded branch (mu_k = 0 => the item with u_k = '0')
 to be decided: the items with '0' labels are themselves in the sweep (e.g. 0z2ab, 0abz1 unit), so the induction closes once the 4 ab:ab:ab FAILs are decided.
STATUS 06:56: ncol R10.5-R10.9 (closing the q(K_0) gap) AUDITED: VERIFIED.
 (1) CLASSIFICATION of 2-dim strongly level zero-row column-centred 3x5 spaces by q: q = 0 rigid pairs (SL_3 (c)); q = 1 exact over Q (slq1.sing RE-RUN: lam = 0
   forced in every component, both row-sum charts); q = 2 via SL_3 (b): B_j in O(V_3) with sum B_j = -3 id (sum A_j = id). Reflection count r: the antidiagonal
   parts must cancel (sum c_j = sum 1/c_j = 0), the diagonal (rotation) parts must give -3 id. r = 1: c = 0, impossible; r = 4: one rotation with t = -3 and
   1/t = -3, impossible; r = 5: diagonal 0 != -3, impossible; r = 3: c ~ (1,w,w^2), t^2 + 3t + 1 = 0 -- possible a priori, decided by slq2.sing over Q(w): UNIT
   (RE-RUN); r = 2: slq2.sing over Q (RE-RUN): t = (-1,-1,-1), c d = 1 with c free = F2; r = 0: hand (e_3 of every 4-subset of alpha = (t+1)/2 vanishes => <= 2
   nonzero entries (a 4-subset containing 3 nonzero ones would have a nonzero e_3; all 5 nonzero forces equal entries and e_3 != 0) => t = (-1,-1,-1,tau,-tau) =
   F1, or V_3 (x) e_a): correct. => rigid pairs u F1 u F2, in char 0. COMPLETE.
 (2) FAMILY SYSTEMS: the finiteness criterion (fib/*.sing) uses a block order (Y-block first) and requires, for each Y-variable, a GB element whose FULL leading
   monomial equals var^deg -- i.e. the coefficient of the pure Y-power is a nonzero CONSTANT, so the Y-leading term survives EVERY specialisation of (h, tp): the
   fibre is finite over every parameter value, including the special ones. Correct criterion. RE-RAN all 112 checks (fib 60 + fibb22 52): 112/112 FIBRES_FINITE.
   Char 0 by the per-point closure/flatness argument over the projective parameter space ([h0:h1] in P^1, C in P^1, Y in P^10): valid.
 => THEOREM H-a3-SL and H-b22-SL hold for ALL strongly level K_0 (q = 0, 1, 2). The gap is CLOSED. CONJECTURE K0 stays open.
# ROUND 24 (start 06:57 UTC). Targets: (1) REMAINING-WORK TABLE at the top of PROOF-MAP; (2) landings after 08:11 (TrK0p rerun, DEFSBUILD2, FLq2, R14t_shape, R17lint, W4P/W5P, W4Q); (3) stage2 R1 (RD = line a = (1,1,1), RDcert, 10 R1 lines, J_A^R1 point); (4) stage3 equal-t case A, leaf-8 block families.
STATUS 06:58: TARGET 1 DONE: a REMAINING-WORK TABLE (12 rows: item, size, what it waits on, dependencies) now sits at the top of PROOF-MAP.md, with an honest
 summary: items 2, 5, 6, 7, 10 need new mathematics (L); items 1, 3, 4, 9 are computations in flight (S-M).
STATUS 06:58: TARGET 3 -- stage2 R1 (R20-1..R20-3):
 RD CERTIFICATE (r20_RDcert.py): I = c-coefficient ideal of det of the 7x7 principal minor (index 6 removed) of B_c = c1B1 + c2B2 + c3B3; V(I) = points where that
   minor vanishes for every c -- a SUPERSET of the true rank-drop locus (rank B_c < 7 for all c implies every 7x7 minor vanishes), which is the right direction.
   1 in I + (1 - w f EXC) for f in {a1-1, a2-1, a3-1}, EXC = lam a1 D, is radical membership of f*EXC in I, i.e. V(I) \ V(EXC) inside {f = 0} for each f, so
   RD \ V(EXC) is inside {a = (1,1,1)}. The method is SOUND; it is proof-grade once run over Q (mod 32003 so far: evidence; char-0 run queued).
 R1 lines (10): kernel bound kills (2,1,1), (3,0,1), (4,0,0); K2 for (4,0,1), (22/7,0,6/7), (11/3,0,7/6), (6,0,0) -- note: where its "msolve char-0 fallback"
   is used, that chart is evidence only; Kt3 for (1,1,1), (0,1,1); exceptional lam per line pending.
 J_A^R1 = {a1 = 0, a2+a3+a4 = 0} (2-parameter jump family; contains the cut point (0,1/7,-8/7)): OPEN -- no kernel lemma applies (K = Ck with q0|K of rank 1,
   B_1 of rank 2); stage2's candidate routes are reduced charts or the big slot.
STATUS 06:59: TARGET 4 -- stage3 sec. 43:
 (C) equal t's, case A, |S| = 3 ROW-HINGE sweep: the test "u * minor_ab(h_i, r_i) = 1" for all 10 2x2 minors of row i's spanning pair is exactly "row i's projection
   is 2-dim"; all 10 UNIT over Q (exact, char 0) means row i is a line on every solution of that chart. |F| = 0: all 30 chart combinations x 3 rows UNIT => every
   solution has all row projections 1-dim (single-row elements): excluded from (PR3') and from stratum (III). Logic VERIFIED (not re-run); |F| = 1 (row 2 always a
   line so far: stratum (III) at most) and |F| = 2 running; |S| = 4, 5 open.
 (A)/(B) leaf 8: the k_N = 2 parameter is genuine (no continuous symmetry; the only symmetry acting on P is the 3 <-> 4 reflection) -- argument checked; special members
   exist for (2,2) and (2,1,1) too, all of a 3+2 BLOCK type (single-row vectors in V_Z = {supported on B3, sum 0} or V_C = {constant on B3}); a block analogue of
   PFC (neutral columns) is the proposed route -- conjecture, numerical.
STATUS 07:03: (SM4) IS FALSE -- rows' counterexample VERIFIED EXACTLY over Q(sqrt3, i) (verify2/r24/cex4_mine.py, symbolic t): Y = H [y1 y2 y3 y4 0] with y1 =
 ((s+1)/2, -i(s-1)/2, 0), y2 = ((1-s)/2, i(s+1)/2, 0), y3 = (1/2, i/2, 0), y4 = -y3 (s = sqrt3, Walsh coordinates): column-centred, exactly 4 nonzero columns,
 row sum f = (1, i, 0) with <f,f> = 0, and perm(J + tY minus column j) - 24 == 0 IDENTICALLY in t for all 5 deletions. Mechanism (rows): all columns in the
 coordinate plane x3 = 0, where kappa = x1 x2 x3 vanishes, so every degree-3 condition is automatic.
 CONSEQUENCES: the IS0-IS4 REDUCTION is still correct (verified V-r22), but its hypothesis (SM4) is false, so the single-matrix route fails for 4 columns:
  - PL4 is unaffected (it has its own earlier proof, V-r8/r10); only the "second proof via SM4" is void.
  - Leaf 3, 4-column plane supports: support-4 G and support-5 G4-z5 (which reduces to the support-4 G plane) and support-5 P2-z3 need the case runs again (R15GQ, R16P2z3)
    or a RESTRICTED (SM4) for the matrices that actually occur (the pencil e1 + ka n, or the cone Y_u of a kernel -- families, not single matrices).
    Support-4 P2 (incl. A) is already exact (R15.11); support-4 P3, PP exact; P4 hand.
  - (SM5) must be re-checked for rank <= 2 configurations (all columns in a coordinate plane x_r = 0, where kappa vanishes) -- the same mechanism may give 5-column
    counterexamples; until R19W5P/W5Q decide, (PL) via (SM5) and the 5-column leaf-3 cases via (SM5) are open (fallback: R15G4*, R15R4*, R15R5*, R16P2A).
STATUS 07:04: (SM5) ON THE COORDINATE PLANES (the SM4-counterexample mechanism), EXACT over Q(i) (verify2/r24/sm5_plane.py): all columns in x3 = 0, f = (1,i,0) WLOG,
 g_k = al_k (1,i,0) or be_k (1,-i,0), sum g_k = 3f, sigma_4 of every deletion (degree 3 automatic since kappa = 0), all columns nonzero: ALL 6 type patterns UNIT.
 Calibration (sm4_plane_cal.py, n = 4, sum g = 2f): patterns 2a/2b and 1a/3b NON-unit of dim 1 -- they contain rows' counterexample (b, b, 0, a) -- the others unit.
 The octahedral group permutes the three coordinate planes, so: NO 5-column counterexample of the SM4 type exists. (SM5) stays open in general (W5P/W5Q).
STATUS 07:04: LANDED -- SYMDC3V2_A0 ([DC3] A0-ne, chart A, generic rank-2 cell, vartheta(Z_0) != 0 piece): GB of the plane subsystem S1 = 338 elements (6712 s),
 then the full system UNIT (3.1 s), p = 2147483629. CHECKED: re-ran Q_A0_ne_v2_FULLGB.ms with a fresh output: [1] (1.9 s); all 338 S1-GB elements are present
 verbatim in the FULLGB input, and every polynomial there lies in the cell's ideal (S1's GB generates ideal(S1)), so UNIT of the input implies UNIT of the cell.
 => SYM-M [DC3] for |supp m| <= 3 is COMPLETE at P1 in the R11.6 form (chart A; chart B redundant, V-r21).
STATUS 07:06: LANDED -- leanfl/TrK0p2_port.log (TrK0p.lean, the port smoke test over Kf, rerun after leanfl's fixes): exit 0, 0 errors, 0 "declaration uses sorry",
 160 s (was 1720 s), peak 7.8 GB. The finrank_sumZero syntax slip and the numeral-normalisation failures are fixed in this fragment. It is a FRAGMENT (no
 L_ theorem, so no axioms line); SL_p still needs the full FLK_field compile.
STATUS 07:07: (self-note) I used 'pkill -f v2_watch2.sh' and it killed my own shell (exit 144) -- the very pitfall in my handover notes; harmless (only my detached watcher died). Kill by PID only.
STATUS 07:07: LANDED -- DEFSBUILD2 (rebuild of the upstream PEqualNP.Defs modules): 'Build completed successfully (5125 jobs)', exit 0 (infrastructure; nothing to audit mathematically).
STATUS 07:20: UPSTREAM SURVEY (coordinator priority 1; table "UPSTREAM SHORTCUTS" in PROOF-MAP). I read the on-disk checkout lean/PEqualNP/{Outside,Gct}
 (main 67126d1) with no git (my rules forbid it). Every cited file has 0 sorry. No upstream lemma closes an open leaf (2-10), and none contradicts a verified step.
 - L_gct_215 = "4x5 level => dim <= 7", only (8,4) for (DI_5). Extras: a_r <= 3 (branch 4), and a cap of 7 on every 4x5 level subspace.
 - L_gct_217 (row-centred 4x4 <= 5) and L_gct_216 (DC 4x4 <= 3) give: the row-sum map is the degree-1 part of M(q) - 24*1 (times -6), so
   dim Q <= 5 + e^col and dim Q <= 3 + e^row + e^col. ncol (c)/(d) therefore need a NONZERO doubly-centred part Q_00 (a lead, not a kill).
 - L_gct_111/123: sum z_r <= 4, a one-line proof of the V-r15 kills (1,1,1,1,1), (2,1,1,1,1), (2,1,1,1,0), and the open z-list is complete.
 - L_gct_152 = the abstract kernel-kill core (for Lean).
 - "4x4 level <= 5" (L-gct-091) is NOT upstream.
STATUS 07:30: rows R21.4-R21.7 AUDITED.
 (1) REAL trick VERIFIED. The system in the chart parameters is literally the same polynomials. F has rational coefficients with fixed x_2-parity, because
     H diag(1,-1,1) = -(row permutation of H). So each generator is i^p x (rational polynomial).
     - UNIT over Q <=> UNIT over Q(i), by faithful flatness / i a unit. Rabinowitsch factors are rational.
     - The parity check in r2c.py is exact (ii a ring variable mod ii^2+1; g0 g1 = 0).
     - Cross-check with my OWN generator over Q(i) WITHOUT the trick (verify2/r24/r2/r2c_mine.py): n = 5, |S1| = 2 UNIT. Calibration with a zero 5th column: dim 1 (= rows' n = 4 calibration).
     - My Q(i) |S1| = 3, 4 runs are still running (verify2/r24/r2/run34.log).
     - rows' Q runs (REAL trick) stand: |S1| = 2, 3 UNIT. rows' own |S1| = 4 Q run hit their 480 MB rsscap, hence their hand split into (3,1), (2,2) UNIT + (2,1,1).
 (2) (SM5) rank <= 2, hand parts VERIFIED:
     - rank 1: P4 = 24 prod c prod (Hf); e3(Hx) = 8 kappa(x) (sympy); the root argument and the multiplicity patterns are re-derived.
     - Degenerate plane gives rank 1. The case split of U is complete.
     - Degree-2 normal form y = a f or f/2 + b f'. |S1| = 0, 1, 5 are trivial.
 (3) Hand claim (no case-G pencil in the coordinate-plane family) VERIFIED, with one correction: P4 = 2 w^2 (t^2 - 3), not -w^2 (3 - t^2)/2 (constant only; same zero set).
STATUS 07:33: CONJECTURE K0 IS FALSE, VERIFIED EXACTLY (my own code verify2/r24/k0_cex_mine.py, direct 4x4 permanent expansion over Q(omega)).
 - S = span((H nu1) a^T, (H nu2)(e0-e1)^T), a = (-3,-3,7,14,-21): row 0 zero, N(J4+Y) = 120 identically in (x,y), e = 1.
 - Defect line (49,49,-81,-36,19), zero-free. The b22 member (1,1,-3,-3,6) gives (-27,-27,33,33,-12).
 - PROOF-MAP item 5: "K0 + H-a3-SL => H-a3" (and b22) WITHDRAWN.
STATUS 07:36: rows R21.8 (support-4 CASE G BY HAND, char 0) VERIFIED.
 - I re-derived the ka^3/ka^2/ka^1 coefficients by hand. With sum be c = 0 and sum al c = 2u, they hold exactly on 5 random rational instances (verify2/r24/caseG_identity.py).
 - The kill chain C_T = 0 => B_kk = 0 => A_k = 0 is correct.
 - K(c(z),u(s),u(s)) = 4i(2s^3 z^2 + (s^4-1) z - 2s) is never identically 0 (and 4iz at u = c(inf)), so <= 2 roots, against 4 distinct s_k.
 - Case G = |supp n| = 4 with 4 distinct directions (all be != 0), from the R14.0 tree (V-r18). This also covers G4-z5. R15GQ / pgRFQ are not needed.
STATUS 07:31: LANDED -- FLq2: exit 0, 0 errors, 0 sorry warnings (log), 0 'sorry' tokens in lean/fl/FLq2.lean (16,660 lines), 1418 s, 8.95 GB.
 - #print axioms: TC5_final and L_gct_210 depend on [propext, Classical.choice, Quot.sound].
 - TC5_final : DefLine K mTC -> finrank <= 4, with DefLine = (P4 a (J+Y))_a in 24*1 + C m and mTC = e0 - e1: exactly TC5.
 - => TC5 over C is LEAN-COMPLETE. The Kf port (TC5_p) is still pending.
STATUS 07:42: ncol R11.11-R11.13 (member exclusion by K_0-fixed systems) AUDITED.
 - Properness: the system is closed in P^10 x P^1 (11 Y-charts; tp in A^1 plus the point at infinity), with no Rabinowitsch. The member is fixed over O_F, F = Q(omega, sqrt D).
 - 65521 = 1 mod 12, and -15, -39 are squares mod 65521. w and sqrt are chosen deterministically, so one prime above p is used in all 22 charts. Denominators are 2, 3, 4, 6, 8, 12.
 - kfix.log: 15 members x 22 = 330 UNIT; the calibration has 1 non-unit chart.
 - MY RE-RUN at a second prime, 1000081: 7 members x 22 = 154/154 UNIT, and the calibration again has 1 non-unit chart. => valid.
 - Open: completeness of the zero-free shaped e = 1 list (the census is mod-p triage under an open condition).
STATUS 07:43: stage2 F2COL-TABLE (R20 rows 1-21 + R21 FINAL ROWS) AUDITED (one pass).
 (a) SYMMETRY CUTS RE-IMPLEMENTED INDEPENDENTLY (verify2/r24/f2col_cut.py: exact intersections of S_3 / S_4 images of the piece arrangements, stratified by zero pattern).
     - R2 generic: region (1,1,1), (2,1,1); a2 = 0: (1,0,1), (3,0,1), (4,0,1), (22/7,0,6/7), (11/3,0,7/6); a2 = a3 = 0: a1 in {1,4,6}. = stage2 R16-5.
     - nu = 0: the same + J0. A family: J_A u (0,1,1); slice: (0,0,+-1); plus (0,0,0). J_A and J0 families: no survivors.
     - R1 generic: (1,1,1), (2,1,1); (3,0,1), (4,0,1), (22/7,0,6/7), (11/3,0,7/6); a1 in {4,6}. = R20-1.
     - Cross-type S_4: J u (1,1,1,1); boundary J u (0,1,1,1). = R17-5.
     => rows 3, 10, 12, 14, 16, 20a, 21 (cut) VERIFIED exactly.
 (b) LEMMAS VERIFIED as logic: kernel kill, general/recursive kernel bound, jump-type, big-kernel, rank-2 split (q = l1 l2, C[S] a domain).
     Also the row-S_3 orbits {0,-1,1}, {1/3,-1/3,inf}; the swap with Z re-charting; and the R1 special Z = the swap image of line (1,1,1) at lam' = -1/(3 lam).
 (c) RE-RUNS:
     - RD certificates (my copy rdcert2_v2.py, own /tmp names): generic R1 remainder 0, unit 1, J_Q 15 gens deg 6, tests a_i - 1 all [1].
       R1 a1 = 0: remainder 0, J_Q 12, both [1]. VERIFIED (exact over QQ).
     - R2 line (0,0,0) chain: stage2's r21_chain.py reproduced, plus MY OWN rank computation at nu = 2/7, -5/11, 13/3
       (rank B1 2 -> rank B2|ker 1 -> W dim 5, generic combination rank 5, need 3 > 2): KILL. nu = -1, 1/3 are symmetric images of nu = 0 (n swap-invariant).
 (d) LOGS: T1cert (generic + 18 tree families) all Singular [S]. K2 lines 20/20 Singular (no msolve fallback). nu = 0 members 9 x 70/70 at P1; cross members 3 x 70/70 at P1.
     Fixed data, so no Rabinowitsch (r17_charts.py). (2,1,1) at nu = -1/2: kernel lemma + 70/70.
     MISSING LOGS:
     - Kt3 on the 4 kap = 2 R2 lines (row 6): no RESULT log anywhere. I am RE-RUNNING it (verify2/r24/kt3/, after my Q(i) job).
     - nu = 0 member (0,0,1) 70/70 and the cross (0,0,1) member: no log line found.
     - Jump point (0,-8,7) 56/56: no log found.
 (e) NOT re-run by me: the J_A^R1 failure sets + cut, the R21-2 algebraic-point checks (one root per irreducible factor: method VERIFIED), the R1 T1certs.
 VERDICT: F2col VERIFIED as structure and logic. It is CLOSED once the Kt3 re-run lands and stage2 points to (or re-runs) the 3 missing RED-p logs.

# ROUND 25 (start 07:44 UTC). Targets: F2col closure (Kt3 + stage2's logs); D04-PROP char 0 + B(dep) points; stage3 leaf 8; Lean landings (R14t_shape, R17lint,
#  Tcert); reg2 27.1, ncol (1,1); remaining-work table.
STATUS 07:45: stopped my Q(i) rank-2 cross-check m5_3 (PID 762050, 18 min, 568 MB) to free the slot for the Kt3 re-run (priority). rows' Q results stand; the REAL trick is verified.
STATUS 07:50: D04-PROP CHAR-0 CLOSURE (stage2 R22-1) VERIFIED with my own code.
 - verify2/r24/chain_mine.py: the generic chain B1 > B2 > B3 > B9 > B6 (ranks 2,2,2,1,1) ends in dim 1, need 1, max isotropic 0. KILL at sg = 2/7, -5/11, 13/3, 7.
 - verify2/r24/chain_search(_full).py (exact DFS over kernel chains), at each exceptional sigma:
   sg = -2/3: B3 (r6) > B9 > B6: KILL.  sg = -1: B1 > B5 > B3 > B6: KILL.
   sg = (-3+sqrt-3)/6: B3 (r4) > B9 (r3) > B6: KILL; the conjugate follows by Galois.  sg = 0, own setup (cache_D04P0): B1 > B5 > B3 > B6: KILL.
 - Exceptional list = rank-drop gcds + basis degeneration + dens (10 sg); T_1 rank-jump constant (univariate, exact). sigma = inf is outside the family (V-r11).
 B(dep) P0_B_i points A, B: generic combination rank 7 on the 7-dim complement, so isotropic dim <= 3 < 4: DEAD (my re-check). This assumes stage2's caches encode the X bases correctly (mkspec_dir.py from r9).
STATUS 07:53: stage2's RED-p re-runs WITH logs (r21/redp_logs.log) CHECKED:
 - nu = 0 member (0,0,1): 70/70 at P1, rational-poly count 0. Cross member (0,0,1): 70/70.
 - Jump point (0,-8,7): k = e8 - e9, q0(k,k) = 0, eliminated via w_0 = -40, SAT=0 (no Rabinowitsch), Gr(3,8) 56/56.
 - All fixed data, closed, one prime: RED-p valid.
STATUS 07:55: stage3 LEAF 8 AUDITED.
 (A) Family B EXCLUDED: VERIFIED. pair (2,3), Q(a) with 6a^2+3a+1 (irreducible, so a field), t a ring variable.
     - I re-ran the 13 hinge-free charts (u0 = u1 = 0, t unrestricted, closed affine charts covering P^12 of third elements) and the 13 t = -1/2 charts: 26/26 UNIT.
     - The parametrisation covers every orthogonal basis of V_Z up to the block S_3, including the isotropic (2,2) member.
 (B) k_N = 2: M0 EXCLUDED: VERIFIED. Column elements in different columns need <c,c'> = 0 (sigma_2), and <r2-r4, r0-r4> = 1. The sigma_3 coefficient is <m, mbar> = 3; span_M0.sing re-run: 3 c0 c4 c5 + ...
     M1 -> free column -> PFC: span_M1.sing re-run, level.
     NOT re-run: the t-family reduction to M0/M1 (sec. 43 (D) sweeps) and the pair third-element lists.
 CAVEAT (stage3's own): the generic-member exclusion and the completeness of the special list are NUMERICAL. So: every KNOWN (1,1,1,1,0) special member is closed mod PFC/(SL_m0); leaf 8 is not closed.
STATUS 07:57: ncol (1,1) COMPLETENESS (R11.14-R11.16) VERIFIED.
 - Lemma Z re-derived: roots of h(t) = t^2 - A t + e2; cases r1 = r2, zero root, (2,2), (2,3), and n1 >= 2 with n2 = 0 giving |supp| = 2.
 - Case A (some k outside both supports gives m_k = 0) and Case B0 (= the R11.7 family) by hand: correct.
 - Case C split via F_i - F_j = (a_i - a_j)(quadratic factor): I re-ran all 32 sub-systems over Q. Non-unit exactly a3 EEQQ, QQEE, QQQQ and b22 EEEE, QQQQ, as claimed (the S4-type points); 27 UNIT.
 - B1 (exact, N-type only) not re-run. => H-a3 / H-b22 now need only the r_a = 2 Pluecker charts (NCOLK0Q).
STATUS 07:58: reg2 27.1 (rank-one lemma, PARTIAL) VERIFIED as stated.
 - P_2(G) = -(s^2 + <x,y>) and P_2(G, e_k u) = -<z,u> re-derived. Steps (1)-(5) are correct given the brute-force-checked P_3 formulas.
 - Open parts as reg2 lists them: dim U' <= 2, (3a)/(3b) both failing, and the N analogue of (4).
 - 27.5 (reg2's own gap in the R3 cone argument: Q-irreducible is not absolutely irreducible) is a correct catch, and the Hessian-rank >= 3 repair is right. Case (alpha) is still conditional.
STATUS 07:59: LEAN.
 - R14t_shape: exit 1, 7 errors (1 omega, 6 Eq.refl anonymous constructor), 395 sorry warnings (stub test).
 - R17lint: exit 1, 2 errors (no goals at 4393; type mismatch at 4541), 515 sorry warnings. Neither is a landing of a full proof.
 - Tcert (leanfl/cert/Tcert.lean, md5 e562ba8db2, 96 lines, 0 sorry tokens): exit 0, 0 errors, 0 sorry, 335 s. No #print axioms line.
   CONTENT CHECK: redp_valsub (a valuation subring B of C with p in its maximal ideal), proj_norm (normalise z != 0 by the coordinate of largest valuation, so all ratios lie in B),
   unit_contra (1 = p g impossible in B).
   CC34 chart 0123: an integral certificate 12 = sum c_j f_j over any CommRing (=> no C-point), and 1 = sum c_j f_j + P1 G (=> no B-point).
   MATCH WITH OUR RED-p: yes, at chart level.
   - The B-point statement is exactly "no solution with p-integral chart coordinates". proj_norm is the properness step.
   - Open conditions cannot be formalised this way (u = 1/h need not lie in B), which matches our "closed only" rule.
   - Number-field constants are integral, so they lie in every B. The prime of B over p is not chosen, which forces certificates for every prime above p, i.e. our "Galois-covered" rule.
   MISSING for a full RED-p proof in Lean:
   (i) the gluing theorem: every C-point of the projective variety lies, after proj_norm on its Pluecker vector, in some chart k with B-integral chart coordinates;
   (ii) certificates for EVERY chart of the cover at the same p (CC34 needs 6 orbit charts + the orbit symmetry, or all charts);
   (iii) a #print axioms line.
STATUS 08:00: Tcert, one more design point for leanfl.
 - proj_norm (normalise by the max-valuation coordinate) fits the STANDARD overlapping charts directly. For a Grassmannian chart [I | X], the X entries are Pluecker ratios p_J/p_I, so take I = the max-valuation Pluecker coordinate.
 - For STRATIFIED charts (x_j = 1, x_l = 0 for l < j, as in several of our runs) the normalised B-point only has x_l in m_B, not x_l = 0.
 - So the certificate must keep the x_l as generators, 1 = sum c f + sum d_l x_l + p G (the mod-p unit verdict with the x_l in the ideal gives exactly this), and the contradiction uses x_l, p in m_B.
 - Our mathematical RED-p is unaffected: every F_p-bar point of P^n lies in some stratum.
STATUS 07:58: F2col row 6 (Kt3) CLOSED. My re-run (verify2/r24/kt3/kt3.log): (1,0,0) and (0,0,1) 20/20 over Q(sqrt 46); (1,0,1) and (0,1,1) 20/20 over Q(sqrt 76); 0 Singular timeouts. stage2's own re-run (r21/redp_logs.log) agrees.
 F2col row 15 (special Z): my own check from cache r16/cache_8b37b704738a.pkl.
 - det q0|K = 5376 nu^2 (nu+1)^3 (3nu-1)^3, exactly as claimed. The K basis is polynomial and never degenerates (gcd of 3x3 minors = 2). Generic rank B_c = 5 for 3 c.
 - nu = inf is covered: by the column swap, special Z at nu = inf is line (1,1,1) at nu = 0, which is logged (nu0_points.log, 70/70).
 - Special Z at nu = 0 (its 70/70 RED-p) has NO LOG; it maps to line (1,1,1) at nu = inf, so it is not otherwise covered. Asked the coordinator for a logged re-run.
STATUS 08:05: F2col row 15 rank-drop: the gcd over 3 random c of all 5x5 minors of B_c is 1327104 (nu+1)^3 (3nu-1)^3, so rank B_c < 5 only at nu in {-1, 1/3}, exactly as claimed.
 Row 15 now needs only the logged nu = 0 member (requested).
STATUS 08:04: rows R21.9-R21.9'''' (G4-A CLOSED in char 0) VERIFIED.
 - verify2/r25/g4a_check.py: the deletion-j ka^3/ka^2/ka^1 coefficients with constant column 5 (w = g5, v = 2u - w) are exact on 4 random instances.
 - The x_i-coefficient of l(x) equals (u_j,w_j) M (u_k,w_k)^T with M = [[6,-3],[-3,2]].
 - Three pairwise M-orthogonal vectors in C^2 (det M = 3): either one is 0 (case (a), a common zero coordinate), or all lie on one isotropic line (case (b), w = mu u, mu^2 - 3mu + 3 = 0). w = 0 would force u = 0.
 - Case (b): deletion 5 at ka^0 gives 8 D_5 = k0 (4 - 3(3-mu) + (3-mu)^2) = k0 mod mu^2 - 3mu + 3 (checked), so kappa(u) = 0 and u is a vertex.
   For vertices, B^u = 2i(z-1)(z+1)^3, -2(z-1)^3(z+1), 8i z^3, 2i(z-i)(z+i)^3: a triple root, hence <= 2 distinct roots, against 4 distinct s_k.
 - Case (a): I re-ran rows' 4 certificates g4acert_{+-ii}_{+-1} over Q: all UNIT, 2.6-3.2 s. Distinct points enter via Rabinowitsch rz D - 1 (exact over Q; true configurations satisfy it).
 - => R15G4P/Q can be dropped. rows R21.12 (W5/SP5 relaxations are not unit): a correct reason to drop them (not re-run; it is a negative result about a method).
STATUS 08:04: F2col row 15 CLOSED: stage2's logged re-run (r21/redp_logs.log: special Z at nu = 0, cache_a017397a6081, 70/70 at P1, 0 rational polys).
 My exact check of the same cache: B_z ranks 2, 2, 3, common kernel dim 3, random B_c rank 5, det q0|K = 84 != 0, so the big-kernel lemma kills it in char 0 as well.
 J_A^R1 (row 21a), my own check (verify2/r25/jar1_mine.py): at (lam,a3) = (2/3,5/7), (-4/5,3/2), (7/2,-9/4), B1 has rank 2 and factors into 2 linear forms,
 and the recursive bound kills inside each hyperplane. stage2's exact failure sets and cut are logged (r21/JA_R1_deg.log, symcut_JA_R1*.log); I did not re-implement that cut (nonlinear pieces).
 => F2col CLOSED (V-r25). PROOF-MAP row 9a updated.
STATUS 08:04: Kevin ABORTED work on L-gct-210 (coordinator). None of my jobs are running: m5_3 was stopped at 07:45, and Kt3, the chains and the checks all finished.
 Final state is in PROOF-MAP (remaining-work table, round 25 final) and in handover/HANDOVER-verify2.md.
STOPPED 08:04 UTC
