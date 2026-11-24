# HANDOVER-verify2 — independent verification ledger for gap L-gct-210 (written 2026-11-23 20:33 CET, role "verify2"; ledger rows updated in round 7, ~20:15 UTC, on Kevin's machine — see NOTES-verify2.md ROUND 7)

Read this cold. Paths are relative to the workspace root (here /home/claude/work/L-gct-210/, on the other machine cloud/L-gct-210/
on the fork branch coord-L-gct-210). My own files: NOTES-verify2.md (RESULT blocks for rounds 1-5 at the top, round-6 block added
at stop), COMPUTE-ERRATA.md (errata of all compute specs; round-6 addendum at the end), verify2/ (scripts), this file.

Gap: every linear space L of 5x5 complex matrices with perm(J+t) = 120 on L (a "level space") has dim <= 8.
STATE: neither proved nor refuted. Largest level space known to anyone here has dim 7 (5x5) / 6 (4x5). No counterexample found.

What "VERIFIED" means below: I re-derived the proof line by line myself (not read for plausibility), reran or re-implemented every
script that carries weight, and tested "for all level spaces" statements on 11 known spaces. It is ONE verifier's re-derivation.
"not checked" = I never examined it (or only read it). Round stopped early at 20:30 by change of plan; section 5 lists what is left.

## 1. LEDGER (status by me; r1..r6 = round in which I checked it)

### 1.1 Foundations — NOTES-chief.md secs 2-4
| result | status | note |
|---|---|---|
| R0 (perm = 120 ell^5 on CJ+L), ZBF incl. UFD step, ThB, Theorem A, N3 (3x3 level <= 3), C4 | VERIFIED r1 | ZBF is applied only to LINEAR subfamilies of L^: checked at each use |
| Lemma C (lam >= 2) | VERIFIED r1 | proof never uses dim 9: for n x n, any two rows, dim pi_rr'(L) <= 2n-3 |
| CA2 (used by stage3 T1, MIN-A) | ERROR in justification, REPAIRED r1 | "blocks not ell-supporting" is false when kappa^e has a zero; correct: s^4-coefficient <u_e, G(xi)> and pi_e(L^) = C^5 |
| chief RP5 | slip r1 | B1 needs k != 0 (harmless) |

### 1.2 stage3 — NOTES-stage3.md
| result | status | note |
|---|---|---|
| sec 10 THEOREM N3', Cor N3'-L | VERIFIED r1 | also Lean-proved (coordinator); exact search 8934 spans: none |
| secs 11-12 MIN-A (rank 16), TR, T1, TV, MIN-B | VERIFIED r1 | ranks exact: verify2/minA_rank.py |
| sec 12 MIN-C | GAP REPAIRED r1 | (beta) type (2,3,0): case "3 free rows + 1 pinned" missing; closes in one line (coefficient tau(om_a,om_b,om_c)) |
| sec 13 configuration (II) excluded | VERIFIED r2 | other details of sec 13 and S3-A/B/C/D: not checked |
| secs 14-16 Q4-coll, MIN-D, MIN-E, (G1), (G2), Q4-gen, THEOREM N1 | VERIFIED r2 | uses upstream Gct/L156 (3 x q, P_1=P_2=P_3=0 => dim <= q+1; statement read) |
| secs 18-20, 22 (N2-a)..(N2-f), (Q5), I3, (E1), S3-1 | VERIFIED r3 | (N2-g) numerical, not rerun; (N2-h) steps (4)-(5) not checked (moot after N2-X) |
| sec 21 THEOREM N2-X (family N2 does not occur) | VERIFIED r3, two full passes | all annihilators by hand for every plane + exact scans (verify2/n2x_*.py) |
| => THEOREM N: 9-dim level, all a_r = 1, lam_rr' >= 3 for all row pairs => single-row element | VERIFIED | = N1 + N2-X + (P),(G1),(G2); upstream L156, L101 |
| sec 24 S3-2(b,c), S3-3(b), S3-4, S3-5 | VERIFIED r4 | |
| sec 24 Lemma 5V | VERIFIED r4, OWN PROOF | notes had a sketch only; my proof is in NOTES-verify2 RESULT ROUND 4 |
| sec 24 (J) THEOREM PL4, (K) THEOREM S3-G, S3-G' | VERIFIED r4 | S3-G given Q4-gen on L_e (incidence data checked); upstream L157 read |
| sec 24 (C2), (G)(i)-(v) | VERIFIED r4 | except the pigeonhole remark in (G)(iii): not checked |
| sec 26 (c1)-(c5), (A1), (A2), (A3) F1, (A4) F3 + F4a, (B), (C5) | VERIFIED r5 | |
| sec 26 (A5) F4b structure (one p, M = Phi + C e_e w + C G_ab + C G_cd), (A5') level identities, (i)-(iii), free-column gauge; (C6), (C8) | VERIFIED r7 | (C7) is a remark; F4b itself stays OPEN |
| round 7 final: Theorem Z22 incl. Lemma DEG (sec 26 (B')); F4b core example M_0 | VERIFIED r7 | M_0: exact level over Z[omega] (sympy), invariants, dim T_1 <= 8 rigorous (rank mod p), verify2/r7/m0_check.py |
| round 8: THEOREM FC (free-column sub-family of F4b) [exact]; (B) parallel y_r => free column | VERIFIED r7 | FC reproduced over Q here (81/81 UNIT, IDENT23 and FULL); generator substitution-tested with M_0 (verify2/r7/fc_subst.py) |
| round 9: THEOREM F4b-X (moment lemma (M1)-(M4) + exact eliminations (M5')) => z = (1,0,0,0,0) impossible in the regime | VERIFIED r8 | (M4) completeness by exact enumeration (verify2/r8/f4b_classify.py); all five eliminations REPRODUCED over Q (verify2/r8/f4b_repro.py); gen9 substitution-tested with M_0 |
| round 11: LEMMA PFC; sec 30 row-kernel bound dim L <= FO2_0(L_r) | VERIFIED r9 | ncdef exact certificates (31 D): logic checked, runs not reproduced |
| round 11: N(w2,w3) level iff <w2,w3> = 0; exact dim <= 7 for H0-H2; (PR2-split') <=> (PR3) | VERIFIED r10 | H0-H2 independently by my Schubert-cell test (k = 3 all unit) |
| COMPUTE-stage3 sec 0 "level spaces of dim 8 exist" | ERROR (errata A1) | false; two calibrations "at dim 8" cannot succeed |
| COMPUTE-stage3 (5c) pure-plane claim | ERROR (errata A2), repaired | counterexample + correct three-way conclusion in the errata; N2-X unaffected |
| r13 33(A) conic coordinates (pairing, tau, q4, perm = pairings - 6 q4) | VERIFIED r11 (sympy symbolic, verify2/r11/conic_sym.py) | perm identity holds for arbitrary sum-zero columns |
| r13 33(E) LEMMA S-SPEC | VERIFIED r11 (independent generator shapeS_mine.py, 3 charts over Q) | p3(b) lies in the ideal (vdim 12 unchanged) |
| r13 33(D),(F),(G) (alpha0) with supp W = 4 | VERIFIED r11 | exact Q(i) enumeration of W (3 sets), stage3 systems re-run, independent generator alpha0_mine.py unit (t-deg <= 3 suffices), calibration t-deg <= 2 non-unit; gauge only over supp W (checked) |
| r13 33(H) (alpha0) with supp W = 3 | see NOTES-verify2 r11 (independent 36-system run) | depends on R12 normal forms (3) (not re-derived) |
| m0 split A: mixing stage3 char-0 (alpha) with verifyfl mod-p (beta) | RIGOUR WARNING r11 | (beta) with u prod c = 1 is affine; proof only with all of (alpha) at the SAME prime (closed X_A) or (beta) over Q |
| R12 normal form (E)/(C) for (alpha) [A_j^T z_j = 0, A_j^*A_j = P_1 rank <= 1, sum A_j = -3, A_4^*A_4 = 5 - 4P_1; P_1 = 0 => A_j = n_j (x) phi_j] | VERIFIED r12 (re-derived) | uses (C2'pol), verified r10 |
| (alpha0) supp 3 dies in DEGREE 2 (any isotropic n_3) | VERIFIED r12: my hand proof + Singular check (supp3_deg2.py, calibrated); = stage3 R14(C) | explains the weak r11 calibration |
| 33(J) (alpha0) supp 2 plane P2 reduction | VERIFIED r12 (re-derived; independent generator 18/18 unit, calibration non-unit) | => THEOREM (alpha0) for m0 VERIFIED (char 0) |
| R14(B) (alpha0) at P1 (scripts converted, i = 1518275076 checked: i^2 = -1 mod P1) | logic OK r12 | combination with verifyfl's KT (alpha) charts at the same prime is valid |
| R14(F) (alpha1) supp 3 | VERIFIED r12 in char 0 (independent generator 48/48 unit; calibration: numerical degree-2 root) | supp 2, 4 open |
| COMPUTE-stage3 item 13 cuts (C1), (C2) | VERIFIED r12 (valid p > 5; tau formulas at infinity checked) | |
| sec 35 LEMMA S2 | VERIFIED r13 at P1 (independent chi-coordinate generator, self-tested formula; 6/6 unit, calibration non-unit dim 1) | over Q: my run in progress (s2c_Q.log) |
| sec 35 (B) (alpha1) supp 4, (C) supp 2 (hand given S2, S-SPEC; (c1)/(c3) systems) | VERIFIED r13 (hand re-derived; (c1)/(c3) 12/12 own generator over Q(i) and at P1) | |
| (alpha) case split (alpha0) + (alpha1 by supp 2,3,4) | EXHAUSTIVE (r13) | |
| => [T31] for m0 at P1 | COMPLETE r13: every piece re-run at P1 with my own generators (a0P1.log 60/60, a1p.log 48/48, S2, c13) + split B hand + (beta) 32/32 | (SL_m0) still needs [DC3] 6 cells, [T22] 5 cells at P1 |
| sec 36 THEOREM SR5, SR2111, rank-one family lemma, Fourier lemma | VERIFIED r15 (hand re-derived; own generators (3,2) 20/20, C* 20/20 over Q, calibrated) | leaf 8 open: (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0), (2,0,0,0,0) |
| sec 36 (A) (PR3) formulas | D_2, c re-derived r15 | D_3, stratum (II), (F) not re-derived (no theorem claimed) |

- r16: sec. 37 (E) (PR3)/(PR2-split') COUNTEREXAMPLE: VERIFIED (verify2/r16/pr3_cx_mine.py); does not extend to dim 9 at rho = 1, 2, 7/3 EXACT
  (pr3_cx_t1.py: T_1 = 10, sigma_2 rank 4 => dim L <= 8). Leaf 7 now: (PR3) on strata (I),(II) + classify / bound stratum (III).
- r17: (t2) analysis: (t0)/(t1) need only (PR3'); (t2) needs (M3) exact emptiness of the core X0 = Y_ab + Y_cd, or (M1) classification of stratum (III)
  (the family is an ansatz with p = e_0) + (M2) uniform FO2_0 certificate.
- r18/r19: both numerical X0 (x0sol_hinge_2_1: dim c(P_a)=1, column element; x0sol_hinge_3_0: MAIN case, no column element) checked independently
  (verify2/r18/x0check.py): (M3)/(M3') false; (t2) question = extension of X0 by (0,g,0,h) to a level L_e with defect <= 2 ((E) normal form checked).
### 1.3 stage2 — NOTES-stage2.md
| result | status | note |
|---|---|---|
| C7/C7'/C7'' (minimal pairs Type I/II), T0, T1 (scripts t3,t5,t10,t13), T1', T2, T2'', S2 | VERIFIED r1 | t10 lacked an independence check of its 5 annihilators: added (verify2/t10_rank.py, rank 5 in all 2080); own re-implementation t1_indep.py gives identical counts |
| GEN-2 (R2-3) with SR, S2-d/GEN-tri, GEN-0, GEN-lin | VERIFIED r1 | |
| R3-1 exception triples (E1)-(E5) | VERIFIED r2, made EXACT by me | verify2/r3_exact.py + r3_exact_leaves.py over Q(i): every one of 1320 cubics certified |
| Lemma N2-GEN (R3-5), Lemma 4x3, Lemma H, GEN-1, GEN-3, (Y3), (Y5), GEN-7, GEN-8, one-zero layer R2-1 | VERIFIED r2 | |
| => THEOREM GEN: no 9-dim level space with all a_r = b_c = 1 and all row/column FK annihilators zero-free | VERIFIED r2 | chain (1)-(8) in NOTES-verify2 RESULT ROUND 2 |
| R4: (Z3), Lemma N2-Z, Theorem N2-Z' | VERIFIED r3 | slip: "rho'_4 = r/3" must read rho'_4 = 0 (same conclusion) |
| R4: M* level exactly; (FO) for all parameters | GAP r3 -> closed r4 | by Theorem FO-M* |
| R5: Lemma FO2 (bilinear Gram N^T Q N, bound dim T_1 - ceil(rank/2)) | VERIFIED r4 | exact statement recorded in NOTES-verify2 RESULT ROUND 4 |
| R5: Theorem FO-M* (dim T_1(M*) = 8 all parameters), R5-7(a), Cases A/B of (alpha), R5-3, R5-4, REG1 -> (B1)/(B2), (Q-r)(i),(ii),(iii) rows,(iv) | VERIFIED r4 | verify2/fo_mstar_exact.py |
| (Q-r)(iii) columns "every column projection of L_r has dim <= 3" | GAP, REPAIRED r4 | true except possibly one column c with kappa^r = e_c, kappa'^c = e_r (then only <= 4); stage2 adopted the corrected statement |
| R6-2 cross-family theorem (b != 0), R6-5, (T2), lam = 5 lemma, Lemma (z_i = 3) | VERIFIED r5 | polar formula of P_2 not recomputed |
| R7: Lemma (FO-r); cross family excluded at first order for ALL a not in C1 incl. b = 0; the 25 cofactor formulas of the (2,4) block family; pi_r(T_1(X)) formula; R7-3(a) | VERIFIED r6 | slip: "(FO-r) can only fail if e(X) >= 2" should read >= 1 |
| rest of R7 (R7-2, R7-3 beyond (a), R7-4) | not checked | |
| "every diagonal block with a two-row column lies in family (alpha)" | NUMERICAL only | superseded by N2-X |
| COMPUTE-stage2 S3 formulas; S4 closed form (i),(ii) | VERIFIED r5/r6 | S4 ERRATUM: add sum nu + sum nu' = 0; data are modulo (kappa,-kappa') and scaling |
| R7-4 z = 3 reductions | VERIFIED r7 | = SP8(b) + (Z3) + TC5 + HYP |
| R8-3 Lemma B0-1 (Pi(x_0) = 0) | TRUE, reason has a SLIP r7 | Pi is cubic in M: use the lam^3-coefficient, not lam^2 |
| R6-7 (T2) | RE-DERIVED r8 (correct necessary condition) | r6_T2.py: no conjugation error; 30 < 35 points => 'not solvable' robust, 'solvable' unreliable |
| R9-4 survivors (S1), (S2), (S3) | settled r8 | (S3): (T2) fails for EVERY sg (exact polynomial certificate, verify2/r8/t2_symbolic.py); (S1): exact FO2 bound 8 (verify2/r8/fo2_exact_S1.py); (S2): exactly (T2)-solvable, z = 3 branch |
| R9-1 B-IND (a),(c),(d); R9-3 N0-W; R9-5 PROP; R9-2 B(dep) geometry | VERIFIED r8 | [CRIT] (b), Q0/P0 details and all exact runs not reproduced; FM, D1M members numerically consistent (own T_1 code) |
| R9-8 Lemma N1; direct tool r9_direct.py; D00-3 / D0-4 loci | VERIFIED r9 (N1 by hand; 4 D003 cells re-run over Q; loci numerically consistent with own T_1 code) | eliminations = closures (exclusion only); P0_B_ii, D003 Q0_B_3/P0_B_3 still without verdict |
| R10-3 decisive test (**) <=> 9-dim level space with L_r = X, a_r = 1 | VERIFIED r9 | |
| R10-2 PROP candidates (D003P, D04P) | EXCLUDED r9 by verify2 (member-wise) | exact (T2)-solvable, but NO 8-dim level space contains any of 8 tested members: q-at-all-base-points on Gr(3, T'/X), all cells UNIT mod p (+ sampled full eqs in one cell), calibrated on L080 (verify2/r8/ext_q.py) |
| R10-4 FO2-JOINT lemma | VERIFIED r9 | stage2's exact k = 4 covers consistent with my k = 3 runs |
| r10_FO2J_exact.py (exact pipeline) | AUDITED r10, sound | exact T_1, open charts of Gr(k,n), over Q, no saturation |
| R8-1, R8-2 | not checked | partial family analysis |
| R11-1 rank certificate; R11-2 msolve chart method (RED-p, fixed rational data) and kills cross-C1, K33, (S2) sg=2, D04P sg=0 | method VERIFIED r11 (logic); kills PENDING patched re-run (E-MSOLVE-BIGCOEFF) | re-confirmed 23:26: crossC1, K33, crossA, D003ptA/B; pending: D04P sg=0 (running), (S2) sg=2, D04P sg=2,-3, parametric |
| R11-4/5 parametric D04-PROP for all sigma | VERIFIED r11 as labelled | loophole (sigma_0 with p in all denominators) closed only by msolve char 0 = evidence; a second prime does not close it; Singular over Q on 126 affine charts would |
| R11-3 q_{s e_i w^T} = 12 P_2 + s Bw | VERIFIED r11 numerically (bw_check.py) | K33 exact level at 130 points |
| R13 patched re-runs (E-MSOLVE-BIGCOEFF) | CONFIRMED r13 (log): all fixed-data kills | D04-PROP parametric re-run pending |
| R13-1/R13-2 F2col cross-type ruling | AUDITED r13: chart cover, jump locus, rulings correct; 67/70 parametric = evidence (affine params + Rabinowitsch) | 3 charts failed (memory), m_0 = 0 open |
| R14-4/5 D003-PROP Case A (70/70 P1, msolve char 0) | coverage VERIFIED r15; status = P1 + EVIDENCE in char 0 | affine params + exclusions: P1 misses alpha reducing into bad loci; needs Singular over Q for a proof |
| F2col v3 slices (Z fixed) | evidence for the slices only (r15) | full family running |

- r19: R15-6 jump-locus lemma (ruling R1) VERIFIED as logic; Deg (r16_Kjump_deg.py, superset certificates correct) not yet computed.
- r18: R15-4 kernel kill + THEOREM-R2-GEN VERIFIED ({0,1}^3 by my minAssGTZ, verify2/r18/r2cof.sing); degenerate loci listed.
### 1.4 verifyfl — NOTES-verifyfl.md
| result | status | note |
|---|---|---|
| DI5: Lemma EQ, THEOREM TC5 (DI5.2 normal form, Lemmas Z, LAG, NB, (P1)-(P4), 7 branches) | VERIFIED r2 | does not need Lemma SL; resultant (F1) exact at 60 points (verify2/tc5_checks.py); DI5.4-DI5.6 not checked |
| DI5-R3: THEOREM SPLIT, FS, TS, Lemma HYP | VERIFIED r3 | SPLIT fails for isotropic m (as stated); (E4)(a), search statistics not rerun |
| R4.1 Lemma QB, R4.3 Theorem PS, R4.4 PR-RED, R4.5 THEOREM PR3 | VERIFIED r5 | det Q_m = -<m,m>/2 |
| R5.1 Lemma C', R5.2 Lemma 3C, R5.3 Lemma NP, R5.4 Lemma T, R5.5 Props I', V, R5.6 Theorem SL3-RED | VERIFIED r5 | "7 pairs" of isotropic lines: by hand r2 + numerically r5 (seven_pairs.py) |
| R5.9 Prop I-ALL, Prop II-ALL | VERIFIED r7 | all pressed points hold; ID8, ID11 (120 placements) checked numerically, verify2/r7/propII_check.py |
| R8.8 [T31-B] for m = (1,1,1,1,-4) (hand) | VERIFIED r10 | char p not in {2,3,5,7} |
| K1: [T31] split A empty (m12m3, iso, m11m2) 'char 0 by RED-p' | LABEL GAP r10 | stratum not closed: needs [T22] at the same prime or a run over Q(i) (my Q(i) run: see NOTES r10) |
| R6.2 (kind (R4): Z_0 != chi_1 l^T, l zero-free), R6.3 (reduction to the 2-dim classification) | VERIFIED r7 | |
| THEOREM DC3 (verifyfl R7.3) for m = (1,2,-3,0,0), (1,1,-2,0,0), (1,w,w^2,0,0) | VERIFIED r7 (char 0 modulo msolve) | cover audited; R7.1 (RED-p) and R7.2 (subsystem cut, cut_cell.py) audited; equations re-derived independently 254/254 for each m (verify2/r7/dc3_indep_eqs*.py); 252 easy m12m3 cases reproduced; piv0 split A UNIT (split B' needs > 2.5 GB, queued) |
| gen_n3 [T22], gen_n2 [T31] covers | AUDITED r7, complete | independent equations: [T31] 12/12 cells (stages a, b), [T22] sampled; verifyfl's [T31] chain crashed (memory), no verdict; symbolic-m caution in errata |
| R5.10 reduction for request A (PS + PR3 steps (1)-(4) => N = N(beta,xi)) | VERIFIED r6 | |
| Request A / VF-A: none of the four planes N(beta,xi), m = (1,w,w^2,0,0), extends to a 3-dim space with defect in Cm | VERIFIED r6 = THEOREM in char 0 | three independent ways, see 3.3; => no principal (5,1) for |supp m| = 3 (with PR3 for non-isotropic m) |
| R5.10 / COMPUTE NEXT "(SL_m) iff [DC3],[T22],[T31] empty" | ERROR r6 | only "if"; non-unit [DC3] does not refute (SL_m); then type (1,3) needs its own system [T13], and [DC4] |
| R5.10 (SL_C) => dim L' <= e+3; COMPUTE NEXT (F1)-(F4), N6 logic | VERIFIED r6 | |
| Request B / VF-B generator = spec; calibration | VERIFIED r6 (reproduced with Singular + own generator) | main cases |P| = 4, 5: no result seen; verdict will be EVIDENCE only (saturation), see 3.3 |
| COMPUTE-verifyfl C/D sampling | ERROR (errata A3) | under-sampling, no fresh-point test |
| Lean: Theorem FL / Lemma SL up to case S6 | not mine | reported by coordinator; NOTES-leanfl.md, NOTES-leanzbf.md never examined by me |
| gen_m0a.build_alpha_kt ((alpha) KT form, 8 INF patterns) | AUDITED r12, no error | complete per chart; nY = 2 relaxation; gauge valid; covers (alpha0)+(alpha1); charts x, 1, 0 open at P1 |
| R9.7 same-prime ledger for [T31] of m0 | VERIFIED r12 | |
| R10.8 / R10.10 SYM-M ([DC3] uniform in m, |supp m| <= 3) | properness argument VERIFIED for the whole cover; PER-CASE claim = GAP (errata [L]) | char-0 only when all 254 cases unit in both charts; 7 cells open |

- r16: R11.6 (SYM-M targets (5,1), whole cover at P1): logic VERIFIED; R11.8 minors, R11.11 VERIFIED; TC5_p flagged steps re-checked mod P1;
  NEEDS SL_p / TC5_p as proofs (Lean port to a field K with numeral hypotheses recommended). Open pieces: [DC3] A0-ne, B0-ne; [T22] cells; [T31] split B.
### 1.5 rows — NOTES-rows.md
| result | status | note |
|---|---|---|
| section DI: (I1),(I2),(I3) k=2,3,4, Lemma D, DDI, DI_3, Prop O, Cor H, Lemma B', Lemma TC | VERIFIED r3 | |
| round 3: SL_3 (a)-(d), FL2 normal form, FL2* (1)-(6), R3.1, Lemma EC, Tower Lemma, saturation principle | VERIFIED r3 | upstream L_gct_215 read (4x5 level <= 7); R3.4, R3.7 numerics, census not rerun |
| R4.1 Hyperplane Lemma, R4.2 (a)-(d), R4.3 RS-HYP, R4.7 Lifting Lemma, D-UP, C-UP, R4.11, FL2* (a),(b) | VERIFIED r4 | upstream L067 read |
| R4.10 (a)-(d) transposed defect + padding, R4.14 Theorem NCOL-S, R4.15 (F1),(F2),(FS-DEC),(F1^T) | VERIFIED r5 | |
| R5.6 (SC1), R5.7 NCOL-P, R5.9 Theorem NCOL-P3, R5.11 Theorem P51 (i),(ii), R5.13 NCOL2-P (+ rigorous part of R5.12) | VERIFIED r6 | |
| R5.2 Theorem DC (a), NC'-DC (b): "dim L' = rank c + rank s + dim L'_dc" | ERROR r6, REPAIRED | only "<=" (correct: rank(s restricted to ker c)); counterexample: level line C(e_0 u^T + (e_1-e_2) e_0^T), sum u = 0. "<=" consequences stand; the reverse implications "(DI_5) => ...", "(NC'_e) => (DC-COST)" are NOT proved as stated |
| R5.3(b) | GAP | C-UP needs (DI_5;2) as hypothesis |
| R5.1, R5.4, R5.5, R5.8, R5.10; all numerics R4.4-R4.13 | not checked | |
| "(NCOL_3) + (DI_4x4) => no (7,3)" (COMPUTE-rows) | GAP (errata [B]) | needs (DI_5;2) |
| rows/clm.py, run_clm.py sample sizes | ERROR (errata A5) | N = 140 < 210 / 462 / 792 quartic coefficients for d = 7, 8 |
| COMPUTE-rows definitions, X2-X5 | VERIFIED r5/r6 | no error |
| R6.1 reduction of X4 to planes (PL); R6.2 formulas P_2 = -sum e_2(rho_i), P_3 = 2 sum e_3(rho_i) | VERIFIED r7 | claim (A) is false (sle5_s1005.npy); R6-1 verdicts B/C will be evidence only (affine + saturation) |
| R7.2 DC'/NC'-DC' exact identities + corrected chain | VERIFIED r8 | replaces my r6 ERROR item |
| R7.3 THEOREM X5 | VERIFIED r8 | hand part + INDEPENDENT generator (verify2/r8/x5_indep.py, 12/12 UNIT over Q, calibration non-unit) |
| R7.4 THEOREM PR5 | VERIFIED r8 | hand part + INDEPENDENT generator (verify2/r8/pr5_indep.py, 24/24 UNIT over Q, calibrations non-unit) |
| R8.1 THEOREM T3 / LEMMA O3 | VERIFIED r8 | => principal (5,1) kernels live on >= 4 columns; 'no principal (5,1)' <= (PL) |
| THEOREM PL4 (R8.6-R8.10): no principal kernel on exactly 4 active columns | VERIFIED r10 (all 5 sign patterns; Lemma ORB by hand; orbit tests ++++, ----, ++-- independently over Q, calibration non-unit) | R8.7's two tiny GB checks and R8.6(a) vec/Q bookkeeping not redone; 5 active columns open (R8-Ksign: affine+saturated => evidence until over Q) |
| R8.2 THEOREM CHI1 | VERIFIED r9 (exact part re-run + own elimination: m = e_3 - e_4 only); hand part GAP REPAIRED | slip: the degree-2 defect has a j-independent term kappa(Y) with kappa' = <w,alpha> - W beta != 0; repaired case split gives alpha = 0 anyway |
| R5.1, R5.10 | VERIFIED r9 | R5.4, R5.5, R5.8 numerical census |
| R9.1 quaternion degree-2 form; LEMMA TR5 | VERIFIED r11 (re-derived) | |
| R9.3 SUMMED CUBIC identity | VERIFIED r11 (+ relation-free proof) | per-j g-form holds only modulo the degree-2 relations (true on genuine spaces); its sum = 24 sum_j P_3(Y^(j))/2 exactly; also: sum_j e_3(y w/o j) = 2 e_3 => sum_j T_j = (3 c(sigma) - sum c(g_k))/12 using only sum g_k = 3 sigma |
| rows/r8/orb/sumq.py | AUDITED r11, no error | relaxation: only UNIT counts; UNIT over Q = proof for the pattern, UNIT mod p = evidence (affine + saturation) |
| R10.2 second proof of PL4 (++++, ----, ++--) by rank(A0 - 2I) = 7 | VERIFIED r12 independently (det on H_3: -3375, -273375, 820125) | rests on Lemma ORB |
| R10.6 EXT-I/EXT-II uniqueness, THEOREM CHI2, pencil principle | VERIFIED r12 (rows' runs re-run + independent generators; CHI2 on all 4 charts) | scope rank c = 1 |
| R9-SUMQ5 | PENDING (big slot outputs empty at 22:56) | mod p = evidence; over-Q plan sq5Qruns.sh runs under 2 GB -> needs the big slot |
| R11.1, R11.4-R11.7 (generic two-column (2,1) stratum) | VERIFIED r13 (hand re-derived; Groebner check of R11.6 conclusion over Q; closed forms vs direct permanents) | uses R10.7 kernel form (not re-derived); special kernels / m_a = m_b = 0 / three-column open |
| R11.2 exact parts (chi2ccQ, c1cc_0, c1cc_3) | RE-RUN r13: K_II forces m = e_0 - e_1; chi (x) C^M unit in both m-charts | rows' scripts (not an independent generator) |
| R12.5 (5,1) criterion (no column-centred (4,1) extension => no (5,1)) | VERIFIED r14 | |
| R12.8 LEMMA 3COL + R12.3/R12.4 classification (A1, A2, family B) | VERIFIED r14 | cubic conditions fixing x in (A) taken as stated |
| R12.6 A1/A2 excluded over Q | VERIFIED r14 (kgen re-run, gauge det 2, unit in m_a, m_c, m_d; symmetries) | famA2 (ten lines) CL |
| R10.7 two-column (2,1) normal form | VERIFIED r15 (re-derived) | |
| R12.10 (generic two-column, m_a = m_b = 0) | VERIFIED r15 (hand) | (1,2)-component formula taken as stated |
| R13.1/R13.1' family B; R13.2 line d = u | VERIFIED r15 (reductions re-derived; bred.py A, D and ured.py B, C re-run over Q: as claimed) | |
| R13.3 special locus (line + 16 points) | classification CL; 16-point RED-p cover at P1 RUNNING (11/64 unit) | leaf 3 also open for (2,1) kernels on 4-5 columns |

- r17: leaf 3(a) 16 special points VERIFIED (kSP1.out: 64 distinct charts unit at P1, Galois-covered, gauges != 0; RED-p). Lemma RS (i)-(iii) VERIFIED
  by hand ((iv) see notes). Leaf 3(b) open.
### 1.6 reg2 — NOTES-reg2.md
| result | status | note |
|---|---|---|
| Phi(L_r) in R_r^perp (dim a_r - 1); Omega criterion dim L <= dim L_r + dim Omega(L_r) - 1 | VERIFIED r4 | |
| section 1 (L1-L5), 4.3 (M* level by hand + EC), RESULT C ((S6-FO2) => no a_r = 2) | VERIFIED r5 | |
| (S6') "dim Omega <= 2 without a full free row" | ERROR (errata A6) | FALSE: family M* has (dim T_1, dim Omega, rank, FO2) = (11,4,5,8), no full free row; the target is (S6-FO2) |
| FO2 numbers of the 20 known six-dim 4x5 spaces | CONFIRMED r4 (own code) | 19 x (9,3,7,2), rc45 (10,4,8,3); three files tolerance-sensitive; says nothing about unknown spaces |
| taxonomy F / NC / DR / M* | NUMERICAL | not rerun |
| hand proof (20:08) = THEOREM SP8 (+ 5.1 (Z3)) and its corollary for M*, EC moves | VERIFIED r7 | 5.1(b) needs FK (a_i >= 1); the remark "<=>" holds only "=>"; DR3 application only for the found spaces |
| R2-2(a) FO2 bound <= dim T_1 - 1 (P_2(tau_r) = -200) | VERIFIED r7 | |
| 8.2 NC-FAM, 8.3 DR22 [exact over Q] | parameter charts of 8.2 checked (complete); test systems NOT audited | |
| sec 9 REG2-T1: 9.1, 9.2, 9.3 hand parts; 9.4 chart cover | VERIFIED r8 | 9.4/9.6 exact test systems not reproduced |
| sec 11 (X1' patterns), 8.2 NC-FAM, 8.3 DR22, 9.4 special locus D: sample of rational members | CONFIRMED r9 exactly with own generator (verify2/r8/reg2_sample.py): dim T' = 9 generic, 10 with exact rank q = 4 (FO2 = 8) on the special loci | greedy-minor method sound; hand case splits of sec 11 not re-derived |
| R5-1 (2,2|1,1) BB/BD | VERIFIED r11 (certificates re-run; 12 special points re-certified with own code) | BD chart v_0 = 1 complete only by S_3 on columns 0,1,2 (wording) |
| R6-1 BLOCK family (t != 0); R6-5 DOUBLE-BLOCK | VERIFIED r11 | lift+Gram re-run; DBLOCK independent minors cover (seed 7 + 3 exact points); p2211_rank comment says d_0, code uses d_1 (correct: d_r in T_1 iff row r touched only by single-row elements) |
| R5-6 (2,1,1|1,1); R5-2 (1,1,1,1|2)(A) | samples VERIFIED r11 / log audited | IV-iso, (a,b) not re-run; dr1111q 48+156 unit, 15 calibrations non-unit |
| R6-6 (BL) | NUMERICAL (as labelled) | not re-run |
| (1,1,1,1|2)(A) pipeline | VERIFIED r12 (re-run over Q: 48 + 156 unit, 24 calibrations non-unit) | |
| IV-iso (7), (a,b) (12), (a,a) leftovers (9) points | VERIFIED r12 (own Q(sqrt -3) arithmetic) | |
| R8-4 Lemma SK | VERIFIED r12 (re-derived) | |
| R8-1 omega_e0 certificates (4 families dim T_1 <= 9; 22_2 E_0 part) | VERIFIED r12 by re-run (NPIV 4) + my line repairs | tool coverage print broken, saved log stale (errata [J]) |
| R7-2 BB row deformations | VERIFIED r12 completely (lift certs re-run, CAL proper; own-seed minors + line p = -1/2 closed; 5 exact samples) | |
| R8-2 certify_defo special loci | methodology sound, logs read | not re-run |
| R9-3 LEMMA SK2 | VERIFIED r13 (re-derived) | rank <= 2 consequence not proved (as stated) |
| R9-1 SIGMA / (d) column-deformation lift_gram | VERIFIED r13 (logs: CAL proper, unique, rank<=2 locus (1); coverage recomputed by me; d_0 in T_1 argued) | |
| R9-2 double deformations dim T_1 <= 10 | CL | rank part open (reg2) |
| R10-3 LEMMA SK3 (full 4-dim row block => rank B <= 2) | VERIFIED r14 (hand (i)-(iv); exact shape-(iv) logs, unit even without rank condition) | 3-dim row blocks not covered |
| R10-1 double deformations (six families) rank q >= 3 + dim T_1 <= 10 | VERIFIED r14 at log level (CAL non-vacuous; d_1 in T_1 by my criterion; minors leftovers t2 = 0) | |
| R10-2 (ii-g) row-deformation curves | VERIFIED r14 (stereographic parametrisation complete; fibres over the roots of h, h2 empty: K + (h), K + (h2) unit) | minor runs at log level |

- r16: M111 EXACT (m111_mine.py: T_1 = 9, dim L <= 7); (1,1,1,1|1,1) family '1111_11a' EXACT for all a in P^1 (fam1111_*.py: T_1 = 9, sigma_2 != 0
  on T_1); 19.3 finite-mechanism theorem VERIFIED as a conditional reduction. incpat uniqueness/emptiness not re-run.
- r17: (1,1,1|1,1,1) incidence split RE-IMPLEMENTED independently (verify2/r16/inc111_mine.py): 476 EMPTY / 36 NONEMPTY (one orbit), the component is
  linear = M111 -> CLOSED. R11-1 conic double deformation VERIFIED (conic_mine.py).
### 1.8 leanfl -- NOTES-leanfl.md
| result | status | note |
|---|---|---|
| X5_mc (lean/fl/x5c.part): rows R7.3 step (2) m_c = 0 without case split | PAPER-VERIFIED r12 (not compiled) | needs kernel on 3 columns with the rank-one column; removes X5's use of VF-A; TC5 still used for m_a = m_b = m_c = 0 |
| LAG_a, LAG_b, NB (NB3, NB_plane), TC5_P1 statements | MATCH the paper lemmas (r13, statements read) | normalised-basis reduction for LAG must be in a wrapper (not checked); not compiled |
| TC5_P3 statement | MATCHES DI5.3 (P3) (r15) | |

### 1.9 ncol -- NOTES-ncol.md
| result | status | note |
|---|---|---|
| N1.0 descent; C1 (SOME = EVERY hyperplane); C2 ((7,3) <= (DI_5;3) + (N_3+)); C4; C5 | VERIFIED r14 | R6.3 erratum respected; (DI_4x4) not needed |
| C3 ((6,2) residual configurations (a)-(d)) | VERIFIED r14 | wording: the dim Q = 6 option of (c) is not 'saturated' |
| THEOREM N2 (configuration (a)) | VERIFIED r14 (hand reduction + my independent Gr(3,8) generator: 56/56 unit at 2 primes, calibration 32/56) | RED-p valid (charts cover Gr, integer coefficients, closed, no saturation) |
| N3.1 transposition duality; N3.2(a),(b), N3.3 | VERIFIED r14 (R5.1 holds for arbitrary W_0; TRI symmetric) | configurations (a), (b) of C3 excluded |
| R2.1-R2.5; R2.4 (A),(B) -> (CC3); R2.8 (SR3) route | VERIFIED r15 | |
| THEOREM CC3 (R2.10) | CL (cases (I), (III) re-derived; (II) and the 3 survivor GBs not) | case (C) of R2.4 open |

- r16: CC3 VERIFIED (case (II) + survivors re-run [1] x3); R2.14 VERIFIED given CC3; scope: split (5,1), zero-free m only.
- r18: PT2 VERIFIED with my own generator (verify2/r18/pt2_mine.py, 11/11 at P1; calibration pt2_cal.py); E3P exact over Q; CC34 VERIFIED (cc34_p1.py 6/6 at P1,
  chart 0123 over Q); R3.3 reduction verified; PROD at P1 gives CC3-e2 (with PT2), NOT (PROD) in char 0. CC45 refuted numerically (fresh points).
- r23: GAP found by verify2, confirmed by ncol (R10.5): THEOREM H-a3-SL / H-b22-SL used "e(K_0) = 0 => K_0 = rigid SL_3 pair", which needs zero 3x5 row sums
  (q(K_0) = 0); rows' SL_3 also allows (q, dim N) = (2,0), (1,1), and ncol's strongly level system has 1-parameter families (Krull dim 1). Verified for q = 0 only.
- r21-r22: R211-3 (27/27), L6G (39/39), K'-KILL logic VERIFIED, conditional on the K' classification. Split isotropic (5,1) CLOSED (R2.14 + R32 + Z2).
- r23 (closed same round): ncol R10.5-R10.9 classification (rigid + F1 + F2) => H-a3-SL / H-b22-SL hold for all q.
- r24: CONJECTURE K0 FALSE (exact, verify2/r24/k0_cex_mine.py); "K0 + H-a3-SL => H-a3" WITHDRAWN. All 15 known zero-free members are excluded by K_0-fixed
  systems: ncol 330/330 at 65521, my re-run 154/154 at 1000081 (verify2/r24/kfix/). Properness argument checked. OPEN: completeness of the zero-free a3/b22 e = 1
  list ((1,1) over Q; r_a = 2 charts NCOLK0Q).
- r24 others: leaf 3 support-4 case G BY HAND (rows R21.8) VERIFIED. (SM4) false (exact). (SM5) rank <= 2 hand parts + REAL trick VERIFIED.
  FLq2: TC5 over C Lean-complete. F2col (stage2): structure, logic and cuts VERIFIED (own cut code verify2/r24/f2col_cut.py; RD certs re-run). 3 logs are
  missing (Kt3 rows: my re-run verify2/r24/kt3/kt3.log; nu=0/cross (0,0,1) RED-p; jump point (0,-8,7) RED-p).
  Upstream survey: PROOF-MAP "UPSTREAM SHORTCUTS" (read from the on-disk checkout; no git).
  Pool note: rows/verifyfl wrap Singular in verifyfl/r12/rsscap.py (480 MB). My own jobs use ulimit -v 2 GB (one job > 0.5 GB at a time).
- r25 (FINAL; work aborted by Kevin at 08:04 UTC). F2col CLOSED: Kt3 re-run verify2/r24/kt3/kt3.log; the row-15 special Z log in stage2/r21/redp_logs.log, plus an exact big-kernel check.
  D04-PROP CLOSED in char 0 (verify2/r24/chain_mine.py, chain_search*.py). B(dep) P0_B_i points dead exactly. Leaf 3: G4-A CLOSED (verify2/r25/g4a_check.py + rows' g4acert re-run).
  Leaf 8: family B EXCLUDED (26/26 re-run); k_N = 2: M0 excluded, M1 -> PFC. The generic exclusion and the completeness of the special list are still NUMERICAL.
  ncol (1,1) completeness VERIFIED (32/32 re-run); H-a3/H-b22 wait only on the r_a = 2 charts (NCOLK0Q). reg2 27.1 partial VERIFIED.
  Lean: Tcert matches RED-p at chart level. Missing: Pluecker gluing, all-chart certificates, axioms line. With stratified charts the certificate must keep the x_l.
  OPEN for a future team (see the PROOF-MAP table):
   - items 2, 5 (K' classification; r_a = 2 charts; b23; (c)/(d), where a nonzero DC part Q_00 is forced by L_gct_216/217), 6, 7, 8, 10;
   - leaf 3: P2-z3 + [(SM5) rank 3 or R4 + R5 + P2-A];
   - 1a SL_p / TC5_p ports; 1d [T22]; 1e [T31]; B(dep) eliminations in char 0.
### 1.10 leanzbf -- NOTES-leanzbf.md
| result | status | note |
|---|---|---|
| T1Hyp statement | MATCHES stage2 T1 (r15) | ZF = a_r = 1 with zero-free annihilator |

- r16: R7s_t3 = stub test (484 sorry incl. ALL 98 t3p_* core lemmas); compiled: t3_trans dispatch + T3Rest2 => T1Hyp. R7c (0 sorry) not compiled yet.
  FLk is the only leanfl full file that compiled (SL, FL); FLn / Tr8full (0 sorry) exit 1.
- r18: leanfl FLK_field.lean + TrK11.lean static audit (kfield_audit.py): NeZero 2,3,5 + sqrt(-1) + |K| > 20 only; TC5 blocks, not the assembled TC5.
### 1.7 handoff — handoff/HANDOFF.md, handoff/oracle.py
oracle.py: no error (conjugation correct; three spot runs). HANDOFF sec 2: errata A3, A4, A6 and [B] items (C1 acceptance d - e >= 4;
"7-dim 4x5 decides the gap only if e <= 3"). Local results C1 (c1multi.py + clm.py), R6-1, VF-B, LEAN-1: AUDITED r7, no error (see
COMPUTE-ERRATA round-7 addendum: C1 sampling >= 2x the per-degree count; R6-1 B/B3/C affine + saturated => evidence only; VF-B chart gauge correct).

## 2. What the verified bricks give (so the next team knows where it stands)
 - THEOREM GEN and THEOREM N (above) exclude the "generic" and the "all a_r = 1, lam >= 3" shapes of a 9-dim level space.
 - 4x5 side: (DI_5) <=> no (5,1), (6,2), (7,3) spaces (rows R4.11 with (D)_8). Proved: no PRINCIPAL (5,1) for |supp m| = 3
   (PR3 + request A); TC5 (two-column m, e = 1). Open: (SL_m)/(SL_C) in every full stratum, |supp m| = 4, 5, non-principal (5,1), (6,2), (7,3).
 - regular side: (S6-FO2) => no a_r = 2 (reg2 RESULT C). (S6-FO2) itself is open.
 I did not verify a complete reduction "these open items => the gap"; treat any such statement in other notes as unaudited.

## 3. Verification standards and pitfalls (each one bit somebody here)
 3.00 Singular modStd(I,1) = 1 is NOT a proof of the unit ideal (vacuous final test for G = {1}); use std/slimgb over Q.
 3.01 E-STALE-OUTPUT (round 16): never read an msolve output you did not delete first; check the exit code and mtime(out) >= mtime(in).
     After-the-fact audit tool: verify2/r16/stale_audit.py <dir> (round 16: 5800 surviving pairs, all genuine). Shared c.out drivers
     (stage2 r13_F2col.py v1, r13_crosscharts*.py) are exposed beyond the first chart per process.
3.0 msolve 0.6.5 mod p MIS-READS integer coefficients >= p (E-MSOLVE-BIGCOEFF): reduce every coefficient mod p before writing a .ms file.
     All 675 of my .ms files checked clean (r12).
 3.1 CONJUGATION. All pairings are BILINEAR (<x,y> = sum x_i y_i, isotropic vectors exist). Restricting a form to a null space from
     numpy SVD: use N = vh[r:].conj().T and the Gram matrix N.T @ Q @ N (plain transpose). The wrong version (vh[r:].T, or N^H Q N)
     gives FO2 bounds 5 < 7 on known 7-dim spaces. Sanity test for any FO2 code: (dim T_1, rank, bound) = (8,1,7) on a known 7-dim space.
 3.2 SAMPLING. A polynomial identity checked at N points needs N >= number of coefficients (quartics: 34/69/69/125 in verifyfl C/D,
     210 for d = 7, 329, 462, 792 for 5x5 d = 7, 8) AND a fresh-point test of every hit. Otherwise spurious "level spaces" appear.
 3.3 MOD-p GROEBNER VERDICTS. "Unit ideal mod p" is a PROOF in characteristic 0 only if (a) the system covers ALL points of a PROJECTIVE
     variety (homogeneous system, or every coordinate chart, or every Grassmannian cell and every case), (b) no saturation and no open
     condition, (c) all coefficients are integral at p (constants like i, sqrt 3, w realised mod p, and the set of cases closed under
     their Galois conjugations), (d) any hand lemma used to cut down the unknowns holds in characteristic p. Reason: a point over Q-bar
     scales to an integral point with a unit coordinate and reduces mod a prime above p. With a saturation (VF-B, typed systems with
     "!= 0") it is EVIDENCE only: run over Q or prove the boundary empty. A single generic affine normalisation is NOT a chart cover
     (misses cones in the hyperplane): use all charts or the homogeneous basis (must be: all variables nilpotent).
     VF-A is settled this way (18/18 charts unit for A1-A4 at two primes; homogeneous basis = 18 linear forms + all quadratic monomials
     of the last two variables; plus exact linear algebra without Groebner bases).
 3.4 LM / NUMERICAL ARTEFACTS. (i) negative search results count only with a positive control OF THE SAME KIND (verifyfl's typed
     Gr(4,14) search fails on its own control 0/34; di_ext finds no extension of chi_1 (x) Lam_M although one exists); (ii) unpolished
     LM output under-estimates dim T_1 and has singular values 1e-6..1e-9: report ranks at two tolerances; (iii) blow-ups (|b| ~ 100,
     a row -> 0) and near-level points are not solutions; (iv) rank/T_1 are semicontinuous: numbers on known spaces prove nothing
     about unknown ones.
 3.5 LOGIC SLIPS FOUND REPEATEDLY: "iff" where only one direction is proved (verifyfl NEXT); "=" where only "<=" holds (rows DC);
     a kernel computed from a fixed list of annihilators without checking their independence (stage2 t10); block arguments that
     silently assume an annihilator has no zero entry (CA2); a case of a case split not treated (MIN-C; PL4 sub-cases were fine).
 3.6 Scripts: print incrementally and run long ones in the background with a log; a killed foreground job loses everything.

## 4. Errata state — COMPUTE-ERRATA.md (about 285 lines)
 Round 5 part: summary of [A] items A1-A6 (listed in the ledger), [B] items, per-file sections, conjugation check, sample-size table.
 Round 6 addendum (dated header, end of file): VF-A (no error, now a proof), VF-B (no error in gen.py; [B] exact chart gauge
 "Zs[0][j0] = 1, Z[0][j0] = 0 for one fixed j0 in P, then saturate by the other columns"; evidence only), NEXT ("iff" -> "if",
 [T13]/[DC4]; rigour note (v) sharpened by 3.3), S4 normalisation, X4/X5 no error, rows Theorem DC. Corrected at stop: the addendum
 now says explicitly that Props I-ALL / II-ALL are NOT verified by me.
 Last block (20:32): stage2 R7-1 slip (e(X) >= 1), rows R5.3(b) hypothesis, and the list of what was not audited at stop.

## 5. What remains to verify, ranked
 1. VF-B main cases (|P| = 4, 5) when the local session reports them: audit the result files; insist on the exact chart gauge and on
    a characteristic-0 certificate (3.3). My generator verify2/vf/own_gen_B.py reproduces the calibration; |P| = 4 needs > 100 s.
 2. verifyfl R5.9 Props I-ALL, II-ALL (the N3 calibrations of the compute spec rest on them). Points to press: in I-ALL the claim
    "M != P => M contains a neutral column and a column of P, and so does {o,o'}"; the bracket formulas via (ID8) (my ID8 is
    -2<chi_3,u><chi_3,u'> + 2<chi_2,uu'>); in II-ALL the completeness of the three placements and the sub-case m_a = m_b.
 3. The typed systems of COMPUTE-verifyfl NEXT once run: [DC3] non-unit must trigger [T13] and [DC4] (ledger 1.4).
 4. reg2 hand proof of 20:08 (3-dim single-row part).
 5. stage3 round 7 final: Theorem Z22 + Lemma DEG, sec 26 (B'), F4b core M_0, (A5), (C6)-(C8).
 6. rows: reverse implications of Theorem DC / NC'-DC; R5.1, R5.4, R5.5, R5.8, R5.10; stage2 rest of R7; polar formula in R6-2.
 7. Never examined by me: NOTES-leanfl.md, NOTES-leanzbf.md (Lean side), local results C1 / LEAN-1 / R6-1, the early role notes
    (adversary, dc5, growth, hessmix, kbuild, lemmaz, lowd, methods, numerics, repr, split, zeros) beyond what the verified chains use.
 8. All numerics flagged "not rerun" in the ledger.

## 6. My scripts (verify2/; run as `python3 -I <script>` from that directory; numpy/scipy only; each < 3 min unless noted)
 Library: vlib.py (the known level spaces as complex numpy bases + linear algebra helpers), fo2lib.py (cof, hess, null [conj-correct], fo2).
 Runtimes below are from memory and approximate, except where a figure is quoted from my notes (r3_exact 137 s, exact_A 0.1 s,
 drive_A 6 s, own_gen_B timings); nothing exceeded the 3-minute rule. Scripts without arguments take none. Several scripts load
 other roles' saved spaces by absolute path under /home/claude/work/L-gct-210/ — adjust the root on the other machine.
 | script | purpose | runtime |
 |---|---|---|
 | test_spaces.py | R0, ZBF over all 250 blocks, ThA, ThB, CA2 on 11 level spaces | ~1 min |
 | n3p_struct*.py, n3p_struct_ctrl*.py, n3p_search.py | N3': exact structured search (8934 spans) + controls + numerical search | 1-3 min each |
 | t10_rank.py, t1_indep.py, t1prime.py | stage2 T1: independence check, independent re-implementation, T1' | < 1 min |
 | minA_rank.py, kp_check.py, alpha_ej_*.py, minE_b_alpha.py | stage3 MIN-A rank 16, K(P), MIN-C/MIN-E pattern filters (exact) | < 1 min |
 | n1_rank.py | Q4-gen: three rank-16 claims over Q | < 1 min |
 | n2gen_identities.py, n2gen_search.py | N2-GEN identities (exact) + LM search | 1-2 min |
 | r3_exact.py, r3_exact_leaves.py, r3_survey_robust.py, r3_e5.py | R3-1 exact over Q(i): 1800 configurations, cubic certificates | six runs <= 137 s each |
 | tc5_checks.py | TC5 resultant and closed forms, exact | < 1 min |
 | n2x_annihilators.py, n2x_annihilators2.py, n2x_scan.py, n2x_planes.py | N2-X: exact annihilator dimensions, 349 planes per type; numerical probe (slow) | < 2 min; probe ~3 min |
 | iso_check.py, split_test.py, split_test2.py | verifyfl SPLIT: isotropic failure, fresh split spaces | < 1 min |
 | mstar_check.py, fo_mstar_exact.py, fo2_mstar.py, reg2_mstar.py, reg2_mstar_exact.py | M*: level exactly, dim T_1 = 8, FO-M* facts (s1)-(s4), reg2's M* numbers | < 1 min |
 | fo2_known.py, fo2_stage2_cands.py, reg2_fo2.py, reg2_limits.py [--zero-only] | FO2 on known spaces, stage2 candidates, reg2's 20 six-dim spaces | < 1 min |
 | lemma5v_patterns.py, pl4_probe.py | Lemma 5V pattern filter (exact); PL4 numerical probe (slow, weak) | < 1 min; 10-35 s per start |
 | audit_verifyfl.py, audit_sampling.py, seven_pairs.py, lemmaz_probe.py | spec audit helpers: monomial counts vs sample sizes, the 7 pairs, Lemma Z probe | < 2 min |
 | vf/exact_A.py | request A WITHOUT Groebner bases: first-order rank 12, binary quadrics rank 3, exact mod p = 2147483629 | 0.1 s |
 | vf/own_gen_A.py P CASE MODE OUTPREFIX | own generator for request A; CASE in A1..A4, CAL; MODE charts or hom; writes msolve inputs | < 1 s |
 | vf/drive_A.sh P1 [P2 ...] | for each prime: all 18 charts + homogeneous system through /home/claude/tools/gb/msolve -g 2 (path hard-coded in the script) | ~6 s in total |
 | vf/own_gen_B.py P "m-spec" OUT [j0] | own generator for request B (Singular script; exact chart gauge, successive sat) | 1-2 s for |P| = 3; > 100 s for |P| = 4 |
 | vf/firstorder_A.py, vf/secondorder_A.py | floating-point preview of exact_A.py | < 1 s |
 Outputs: verify2/vf/run (msolve), verify2/vf/runB (Singular, incl. cal_*.sing = the local gen.py calibration reproduced), verify2/logs,
 verify2/spot. Engines used: /home/claude/tools/gb/msolve (input: variables line, characteristic, comma-separated polynomials; -g 2 =
 reduced DRL basis) and /home/claude/tools/gb/Singular (std, sat, dim, vdim). The vf/ scripts carry a usage line in their header
 comment; primes used: 2147483629, 2147483497 (A), 2147482921 (B) — all = 1 mod 12; the generators compute i, sqrt 3 and xi
 (xi^2 = -3/(32 beta)) mod p and assert that the roots exist. I did not re-verify the hard-coded path claim for scripts of rounds 1-4: grep for "/home/claude" before running.
