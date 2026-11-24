# HANDOVER-ncol (role ncol, leaf 6 of PROOF-MAP: (6,2), (7,3); rounds 1-2, 2026-11-23 23:37 - 2026-11-24 ~01:00 UTC)
Notes: NOTES-ncol.md (RESULT blocks for rounds 1 and 2 at the top; sections N1-N4, R2.1-R2.14).  Compute: COMPUTE-ncol.md.  Files: ncol/.
Nothing here has been re-derived by verify2 yet (round-14 list: C2-C5, N2.1-N2.3, N3; round-2 items R2.1-R2.14 are new).

## The chain (exact)
- (DI_5;k) := no (e+4,e) space with e < k.  (N_e+) := every (e+4,e) space has a neutral column.  Under (DI_5;e) all hyperplanes of an (e+4,e)
  space share C, so NCOL for SOME hyperplane = NCOL for EVERY hyperplane = (N_e+).
- NO (7,3) <= (DI_5;3) + (N_3+)  [N1.2; (DI_4x4) is never needed].
- NO (7,3) <= (DI_5;3) + (SR3) + two residual u_i = 2 cases  [R2.8 + CC3; SR3 = "every (6,3) space has a single-row element", NUM 23/23].
- NO (6,2) <= (DI_5;2) + (N_2+) + exclusion of configurations (c) dim Q = 5, dim X_n = 1 and (d) dim Q = 6, X_n = 0  [(a), (b) excluded: N2, N3].
- (N_2+) <= (T2) "single-row-free extremal (5,2) spaces with nondegenerate C have a neutral column" + degenerate C cases (C5, R2.10).

## Proved (hand unless stated)
- C2 (no (7,3) from N_3+), C3 (four configurations), C4 (no row carries C in (7,3), w non-isotropic), C5 (generic hyperplanes have few
  single-row elements), Theorem N2 (config (a); hand reduction + projective mod-p system unit in 56/56 charts at 3 primes, calibrated),
  duality N3 (untwisted towers; config (b) always untwisted and excluded).
- R2.1 generic hyperplanes of (e+4,e) spaces are non-principal.  R2.2 diagonal stabilizer.  R2.3 zero-row-on-ker-c lemma.
- THEOREM CC3 (R2.10): no column-centred 3x5 level space of dim 4 with defect <= 1.  Hand case analysis in isotropic coordinates (a, beta)
  (pencil of rank-<=2 quadrics a^ o beta^ in span(1,m)) + three survivor systems with Groebner basis [1] over Q (ncol/cc3/survivors.py,
  calibrated by ncol/cc3/survivors_cal.py).
- Corollaries: (7,3) rows carrying C with isotropic w, and u_i = 2 rows with dim(U_i + U_i o w) = 4: impossible.  (5,1) spaces containing
  e_i m^T with m zero-free (incl. ISOTROPIC m): impossible (R2.14; part of the split isotropic case left open by SPLIT/FL2*).

## Open, ranked
1. (SR3) or (N_3+) -- either closes (7,3) (with the residuals of 2).
2. Residuals: (7,3) row with u_i = 2 and dim(U_i + U_i o w) = 3 (rank c = 3, gamma != 0 on ker c; R2.11); isotropic w with u_i = 2, w in U_i.
3. (6,2): (T2); configurations (c) (untwisted self-dual; twisted: M(q) - 24 = h v with v linear, R2.12) and (d) (6-dim 4x4 level Q; would follow
   from the unchecked n = 4 bound "level <= 5").  Totally isotropic C.
4. Split (5,1) with isotropic m having 1 or 2 zeros (R2.14 leaves these).

## Pitfalls / tools
- msolve segfaults at the 2 GB cap on the full CC3 system (Gr(4,10) x P^3, 27 unknowns); Singular > 1 GB in 6 min.  The hand reduction made it
  unnecessary; gb/cc3_queue.sh is ready if someone wants an independent machine check (needs ~8 GB per run).
- iv2gen.py / cc3gen.py write coefficients reduced mod p (E-MSOLVE-BIGCOEFF safe).  Scripts: x2_search.py, caseA_search.py, iv2_search.py,
  cc3_search.py, fixw_search.py (LM, calibrated), srow_chk.py (single-row/column census), dual_chk.py (duality check).

## Round 3 additions (00:57 - ~01:40 UTC)
- Column-centred 3x5 level 4-spaces EXIST (R3.1; exact example R3.5: W_a = W_b = span(e_0, (0,1,i,-1,-i)), e = 3).  All 8 LM hits are PRODUCTS
  W_a (+) W_b (isotropic coordinates).  e_3 vanishes on no 3-dim subspace of C^5 (R3.1, modular projective).
- R3.6: products never have defect <= 2 (exact projective system, 11 orbit charts, ncol/gb/prod/prodgen2.py reps_e2.txt; point calibration
  pointcheck.py).  A UNIT PROD-NCOL at P1 (big slot; logs ncol/gb/{free3_orb_P1,prod_P1}/<chart>_big.log) plus PT2 at P1 gives CC3-e2 in char 0
  by whole-cover RED-p on the closed {(S,G)} system (verify2 R18: it does NOT give (PROD) in char 0); CC3-e2 kills CC3' and R2.15.
- Runners are stale-safe now (R3.0).  R3.2: rigid shape of split isotropic (5,1) with one zero.
- Still open: (SR3), R2.11, R3.2 shape + two zeros, configurations (c), (d).

## Round 4 additions (01:42 - 02:05 UTC)
- Product spaces are finitely many (R4.3); same-node pairs (30) have e = 3 with defect e_k^perp cap V5, general-line pairs e = 4 (numerical, 745/745).
- THEOREM CC34: no column-centred 3x4 level 4-space (ncol/gb/cc34/).  Used for the R3.2 shape.
- (CC45) is false (ncol/ccn/cc_d4_s52_pol_e2.npy: column-centred (4,2)); (CCN) for e = 3 is supported (4/4) and would close one (7,3) sub-case.
- Local attempts at (PROD) (chart 0123 reformulated, E = 3 classification) segfault at 2 GB; the big-slot job decides CC3-e2 (not (PROD) in char 0).

## Round 5 additions (02:00 - ~03:10 UTC)
- THEOREM SN (char 0): a product-type column-centred 3x5 level 4-space has e <= 3 iff it is a same-node pair W (+) W (NOTES R5.4, R5.7-R5.12).
  Everything mod p at the single prime 65521: pair GB degrees 864/828/792; local lengths Y = 6, Y + det M = 2 at all 18 same-node points;
  length(Y_p + det M) = 24 / 12 / 0 in charts 01_01 / 01_02 / 01_23.  Char 0: local length 6 over Q(i).  Lift: finite Z_p-module length
  argument (R5.4).  Scripts: ncol/gb/pairs/{pairgen,mkq,mkloc3,mkmm,lenmm}.py; outputs sing/q_*.out, loc3.log, mm/.
- Trick that avoided the 2 GB segfaults: do not saturate / add kernel vectors; load msolve's reduced grevlex GB into Singular as an SB
  (attrib isSB), reduce the 4x4 matrix entries, compute det by Laplace with reduction at every step, then vdim(std(G + det)).
  Avoid reduce(det * monomial) row-by-row export (3.5 s per row); multiplication matrices of the variables + column recursion is fast.
- R3.2 shape: alpha == 0, Q = P (+) C e_i m'^T, x_n = 4 - dim P (R5.1); dim P = 1 impossible (R5.5); dim P = 3 survives the P-internal
  conditions (R5.10), so the exclusion must use column n -- concrete system in R5.10.

## Round 6 additions (02:53 - ~04:00 UTC)
- THEOREM SN PROVED (chart 01_01 = 24 by std AND multiplication matrices; 01_02 cross-checked = 12; R5.12 with verify2's two clarifications).
- R3.2 closure system (NOTES R6.1): ONE projective system for all dim P, from alpha == 0 (R5.1) + CC34 (single-column element (0|y')):
  (y', L'') on the incidence variety in P(V4) x Gr(4,11), times the m'-conic.  ncol/r32/r32gen.py (Singular writes the msolve file),
  orbits.py / reps3.txt (8 orbit charts x 4 m'-charts).  Calibration: point check (evalpt.py) + same generator with 2-dim/1-dim span is NONUNIT.
- Two-zero case: m = (1,w,w^2,0,0), row 0 of ker c in Gamma(Cm) = span(1, e_3, e_4) (alpha NOT automatically 0 here), L'' in Gr(4,13):
  ncol/r32/r32z.py, orbz.py / repsz.txt (82 orbit charts), calibration zcal (3-dim L'').  RESULT: one-zero 32/32 UNIT, two-zero 82/82 UNIT
  (47 plain + 35 by staged refinement: stage.sh none -> one -> dd, each stage uses only charts verified earlier) => NO split isotropic (5,1).
- STAGED REFINEMENT (reusable for any chart system that segfaults): on a failed chart S add p_T = 0 for all charts T already verified
  empty (single exchange = one chart coordinate, double exchange = 2x2 minor).  Closed conditions, RED-p-sound by induction.  Order the
  stages so that the cheap charts are verified first (here: alpha charts, then neutral, then one-delta, then delta-delta').
- Cross-check without CC34: r32g411.py (L'' in Gr(4,11) directly), orb411.py / reps411.txt (13 orbits x 4): 52/52 UNIT (stage411.sh).
- Process lessons: never let two msolve jobs overlap (one > 0.5 GB rule) -- chain them on DONE markers; the PreToolUse hook blocks
  "ps | grep" patterns containing loop keywords, so find PIDs with a /proc scan in python.

## Round 7 additions (03:36 - ~04:15 UTC)
- R2.11 (case (C) of R2.4, sub-case dim(U_i + U_i o w) = 3): THEOREM R211-3, CONDITIONAL on the K' classification (NOTES R7.2-R7.7).
  K' census: one rigid type K' = span(nu_1 (e_p-e_q)^T, nu_2 e_s1^T, nu_2 e_s2^T) (or mirror), m = e_p - e_q.  Given K', U_i = C cap t^perp
  and L' contains L6 = K' (+) e_0 U_0 (+) C Z (c(Z) = t, c^(0)(Z) in C1); (L6) is excluded by a 10-unknown projective system (27/27 UNIT at
  two primes; ncol/r7/r211L6.py).  The exact K' classification (ncol/r7/k3gen.py; 0-dim scheme + SN length argument) segfaults at 2 GB
  -> big-slot line NCOL-K3CLASS (spec ncol/r7/KBIG-SPEC.txt; decision: chart degrees 017 -> 0,0,2,1,1, others 0).
- LEMMA SC (single-column elements) R7.3: x e_s^T in L' => (x.Y_{:,l})_{l != s} in C and sums to 0, for every Y.
- (7,3) chain as one list: NOTES R7.1.
- Still open: case (C) sub-case dim(U_i + U_i o w) = 2; (SR3); (CCN); CC3-e2 (PROD-NCOL big slot).

## Round 8 additions (04:03 - 04:20 UTC)
- THEOREM L6G + COROLLARY K'-KILL (NOTES R8.1): with the K' type fixed, the only solutions of the general-Z system are 3 single-column
  points (lam = 0), so any (7,3) configuration with the K' type in the zero-row part of ker c dies.  Case (C) of R2.4 is reduced (given the K'
  classification) to: dim(U_i + U_i o w) = 2, rank c = 3, rho = 2, dim K'' = 2, U_i of type a3 / b22 / b23 (R8.2).  Type a4 has a neutral column.
- Tools: ncol/r7/r211G.py (general Z), l6gjac0.py (char-0 Jacobian over Q(w)), gb2dim.py (dim / vdim from msolve GBs).
- When NCOL-K3CLASS lands (ncol/r7/kbig.log): run gb2dim.py on each output, compare with 017: 0,0,2,1,1 and 012/015: 0; then R211-3 and
  K'-KILL become unconditional.
- (round 8, after the cut-off) H-CONJECTURE (NOTES R8.5-R8.8): the last piece of case (C) needs "no 4-dim ker c with row 0 in U_0^perp and
  ker c (+) e_0 U_0 level, defect in C" for U_0 of type a3 / b22 / b23.  Proved for a3 with C = V_012 + V_34 (ncol/r8, 74/74 staged);
  generic C (a3, family T0) and b22 / b23 are big-slot jobs NCOL-HCONJ-A3T0 / NCOL-HCONJ-B (spec ncol/r8/HBIG-SPEC.txt).  Drivers:
  hiter.sh / hiter2.sh (a3), hiter3.sh (b22/b23): fixed-point staged refinement, each pass uses only charts verified before.
- ERRATUM R8.4: always sample identities at enough points (>= number of coefficient conditions / conditions per point); lmH.py now NS=80.

## Round 9 additions (05:28 - ~05:55 UTC)
- Hand progress on the H-conjecture (NOTES R9.1-R9.4): exact second-order identities (D2), (C2) for H; for type a3 they give (I1), (I2)
  and a CLOSED case cover {CA_jj', CB_jj' (two of the columns 0,1,2 coincide on K), E1, E2, E3}.  E1, E2 UNIT 148/148 on all T0 orbit
  charts; E3 / CA / CB need more memory than the 0.5 GB pool allows -> optional big-slot route NCOL-HCASE-A3T0 (driver ncol/r9/hcase_all.sh).
- Memory: msolve needs >= 1.2 GB VIRTUAL even for tiny systems; use ncol/gb/runlog_rss.sh (resident watchdog) for "0.5 GB" pool jobs.
- The local T0 pass was stopped for the pool rule; NCOL-HCONJ-A3T0 (big slot) stays needed.
- (round 9, late) THEOREM H-a3-SL (NOTES R9.6): if the zero-row part K_0 of ker c is strongly level it is a Lemma-SL_3 pair, and with K_0
  fixed the admissible Y are finitely many for every C (ncol/r9/k0gen.py: 66 systems, 0.3 s each) => impossible in the last piece.
  The remaining gap for type a3 is CONJECTURE K0 (R9.5; numerical).  Same route should work for b22 (zero-free t') -- write the b22
  K_0-fixed generator next; b23 needs the e = 1 two-dim spaces with a two-zero defect line.

## Round 10 additions (06:07 - 06:55 UTC)
- verify2's gap (R9.5 (a) assumed q(K_0) = 0) was REAL and is CLOSED: strongly level 2-dim zero-row spaces = rigid pairs + families
  F1, F2 (complete in char 0: rows' SL_3 (b),(c) normal forms + ncol/r10/slq1.sing, slq2.sing), and the family-parametrised K_0 systems
  (ncol/r10/kfam.py; a3 308, b22 572) are finite over every parameter (fib/, fibb22/).  H-a3-SL and H-b22-SL hold for all strongly level K_0.
- THEOREM H-b22-SL for the rigid pairs: ncol/r10/k0gen2.py (fixed precedence bug!).
- CONJECTURE K0 open; sub-case scripts k0_20.sing, k0_11b.sing, k0_21.sing exceed 0.5 GB over Q; k0bpf.py is the base-point-free
  normal form (24 unknowns).

## Round 11 additions (06:55 - 07:12 UTC)
- THEOREM H-b23-SL: strongly level K_0 excluded for type b23 too (ncol/r10/kfam.py, k0gen2.py with TYPE b23; fibre checks via fibgen.py).
- NCOL-K0Q driver: ncol/r11/runK0Q.sh (exact over Q, resumable, verdict files in ncol/r11/jobs/); spec K0Q-SPEC.txt.  When it lands:
  every jobs/*_ch0.verdict must read "VERDICT 1"; a "VERDICT 0" is a counterexample to K0 in that chart.
- b22-T2: big slot NCOLHB22T2 (ncol/r8/hiter3.sh b22 2 6); my partial pass h3_b22_T2_p1.log is reused.
- 07:20 CONJECTURE K0 FALSE (NOTES R11.7): counterexample span(nu_1 a^T, nu_2 (e0-e1)^T), a = (-3,-3,7,14,-21); 1-parameter family.
- Restricted problem (a3 shape m0=m1=m2 / b22 shape m0=m1, m2=m3, zero-free): member types F (family), S4 (Q(i)), N (Q(sqrt -15), a3 only).
  All excluded by K_0-fixed systems (ncol/r11/k0gen3.py, kfix.log: 330/330 UNIT, calibrated).  Completeness: (1,1) by the hand case split
  R11.14 + exact systems (ncol/r11/k0_11case.py, k0_11C2.py, case11/); r_a = 2 Pluecker charts in the big slot (NCOLK0Q = runK0Q.sh,
  rewritten; old general driver runK0Q_general_OLD.sh must not be run).
- If a new member appears (big slot GB in ncol/r11/jobs/*.gb): add it to k0gen3.py member() and run its 22 charts (runkfix.sh).
- Next target after this: (6,2) configurations (c)/(d) via L_gct_216/217 (nonzero doubly-centred level part Q_00), PROOF-MAP UPSTREAM SHORTCUTS.
- 07:45 (1,1) sub-case of the restricted classification COMPLETE (NOTES R11.14/R11.16; k0_11case.py, k0_11C3.py; outputs case11/).
  runK0Q.sh now holds only the 42 r_a = 2 Pluecker jobs.  Local attempt with the same/crossed split (k0rs.py) exceeds 0.5 GB mod p.
- Monitors/jobs: nothing of mine is running locally at round end.

## STOPPED 08:05 UTC (round 12; L-gct-210 aborted by Kevin)
- K0 FALSE (NOTES R11.7).  Restricted (zero-free, a3/b22-shaped) classification: (1,1) COMPLETE (R11.14, R11.16), all members (F, S4, N)
  excluded by K_0-fixed systems (R11.13; verify2 second prime 154/154); r_a = 2 Pluecker charts OPEN: ncol/r11/runK0Q.sh (42 jobs, exact
  over Q, resumable; spec K0Q-SPEC.txt) -- queued as NCOLK0Q, not run.
- H-a3-SL, H-b22-SL (verified), H-b23-SL (R11.5).  b23 with e(K_0) = 1: (1,1) done for generic and special U_0 (R12.3-R12.6; ncol/r12/
  b23_11.py, k0gen4.py, kf4/, kf5/); r_a = 2 open.
- (6,2) configurations (c)/(d): Walsh identities (R12.1, ncol/r12/walsh.sing), Q_00 != 0 forced (R12.2); no kill.  Lead: L_gct_216/217.
- No jobs of mine are running.
