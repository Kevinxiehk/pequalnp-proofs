# HANDOVER-verify2 — independent verification ledger for gap L-gct-210 (written 2026-11-23 20:33 CET, role "verify2")

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
| sec 26 (A5) F4b structure, (C6)-(C8) | not checked | open families |
| round 7 final: Theorem Z22 incl. Lemma DEG, sec 26 (B'), F4b core M_0 | not checked | on my list when stopped |
| COMPUTE-stage3 sec 0 "level spaces of dim 8 exist" | ERROR (errata A1) | false; two calibrations "at dim 8" cannot succeed |
| COMPUTE-stage3 (5c) pure-plane claim | ERROR (errata A2), repaired | counterexample + correct three-way conclusion in the errata; N2-X unaffected |

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

### 1.4 verifyfl — NOTES-verifyfl.md
| result | status | note |
|---|---|---|
| DI5: Lemma EQ, THEOREM TC5 (DI5.2 normal form, Lemmas Z, LAG, NB, (P1)-(P4), 7 branches) | VERIFIED r2 | does not need Lemma SL; resultant (F1) exact at 60 points (verify2/tc5_checks.py); DI5.4-DI5.6 not checked |
| DI5-R3: THEOREM SPLIT, FS, TS, Lemma HYP | VERIFIED r3 | SPLIT fails for isotropic m (as stated); (E4)(a), search statistics not rerun |
| R4.1 Lemma QB, R4.3 Theorem PS, R4.4 PR-RED, R4.5 THEOREM PR3 | VERIFIED r5 | det Q_m = -<m,m>/2 |
| R5.1 Lemma C', R5.2 Lemma 3C, R5.3 Lemma NP, R5.4 Lemma T, R5.5 Props I', V, R5.6 Theorem SL3-RED | VERIFIED r5 | "7 pairs" of isotropic lines: by hand r2 + numerically r5 (seven_pairs.py) |
| R5.9 Prop I-ALL, Prop II-ALL | NOT CHECKED | text read only; top of the remaining list |
| R5.10 reduction for request A (PS + PR3 steps (1)-(4) => N = N(beta,xi)) | VERIFIED r6 | |
| Request A / VF-A: none of the four planes N(beta,xi), m = (1,w,w^2,0,0), extends to a 3-dim space with defect in Cm | VERIFIED r6 = THEOREM in char 0 | three independent ways, see 3.3; => no principal (5,1) for |supp m| = 3 (with PR3 for non-isotropic m) |
| R5.10 / COMPUTE NEXT "(SL_m) iff [DC3],[T22],[T31] empty" | ERROR r6 | only "if"; non-unit [DC3] does not refute (SL_m); then type (1,3) needs its own system [T13], and [DC4] |
| R5.10 (SL_C) => dim L' <= e+3; COMPUTE NEXT (F1)-(F4), N6 logic | VERIFIED r6 | |
| Request B / VF-B generator = spec; calibration | VERIFIED r6 (reproduced with Singular + own generator) | main cases |P| = 4, 5: no result seen; verdict will be EVIDENCE only (saturation), see 3.3 |
| COMPUTE-verifyfl C/D sampling | ERROR (errata A3) | under-sampling, no fresh-point test |
| Lean: Theorem FL / Lemma SL up to case S6 | not mine | reported by coordinator; NOTES-leanfl.md, NOTES-leanzbf.md never examined by me |

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

### 1.6 reg2 — NOTES-reg2.md
| result | status | note |
|---|---|---|
| Phi(L_r) in R_r^perp (dim a_r - 1); Omega criterion dim L <= dim L_r + dim Omega(L_r) - 1 | VERIFIED r4 | |
| section 1 (L1-L5), 4.3 (M* level by hand + EC), RESULT C ((S6-FO2) => no a_r = 2) | VERIFIED r5 | |
| (S6') "dim Omega <= 2 without a full free row" | ERROR (errata A6) | FALSE: family M* has (dim T_1, dim Omega, rank, FO2) = (11,4,5,8), no full free row; the target is (S6-FO2) |
| FO2 numbers of the 20 known six-dim 4x5 spaces | CONFIRMED r4 (own code) | 19 x (9,3,7,2), rc45 (10,4,8,3); three files tolerance-sensitive; says nothing about unknown spaces |
| taxonomy F / NC / DR / M* | NUMERICAL | not rerun |
| hand proof (20:08): families with a 3-dim single-row part cannot sit in a 9-dim level space | not checked | on my list when stopped |

### 1.7 handoff — handoff/HANDOFF.md, handoff/oracle.py
oracle.py: no error (conjugation correct; three spot runs). HANDOFF sec 2: errata A3, A4, A6 and [B] items (C1 acceptance d - e >= 4;
"7-dim 4x5 decides the gap only if e <= 3"). Local results /home/claude/coord/local/results/{C1, LEAN-1, R6-1}: not audited.

## 2. What the verified bricks give (so the next team knows where it stands)
 - THEOREM GEN and THEOREM N (above) exclude the "generic" and the "all a_r = 1, lam >= 3" shapes of a 9-dim level space.
 - 4x5 side: (DI_5) <=> no (5,1), (6,2), (7,3) spaces (rows R4.11 with (D)_8). Proved: no PRINCIPAL (5,1) for |supp m| = 3
   (PR3 + request A); TC5 (two-column m, e = 1). Open: (SL_m)/(SL_C) in every full stratum, |supp m| = 4, 5, non-principal (5,1), (6,2), (7,3).
 - regular side: (S6-FO2) => no a_r = 2 (reg2 RESULT C). (S6-FO2) itself is open.
 I did not verify a complete reduction "these open items => the gap"; treat any such statement in other notes as unaudited.

## 3. Verification standards and pitfalls (each one bit somebody here)
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
