# HANDOVER — stage3 (written end of round 9, 2026-11-23 ~20:35 UTC; round-10 addendum at the end)

Cold-start brief for the next stage3 agent. Read TEAM-RULES.md and BRIEF.md first, then the RESULT blocks at the top of NOTES-stage3.md
(rounds 9, 8, 7) and sections 26-29. Scripts of this round: stage3/r9/.

## Where the (S3) regime stands  (9-dim level L, all a_r = 1, all lam_{rr'} >= 3, z = dims of the single-row parts)
| z pattern | status | where |
|---|---|---|
| z = 0 | impossible — Theorem N (N1 + N2-X), VERIFIED by verify2 | secs 16, 21 |
| z = (1,0,0,0,0) | impossible: F1, F3, F4a by hand (sec 26 (A3),(A4), not yet verified); **F4b by Theorem F4b-X (round 9)** | secs 26, 28 |
| two entries 2 | impossible — Theorem Z22 (next on verify2's list) | sec 26 (B') |
| z = (2,0,0,0,0) = (S3-a), (2,1,..), any z_e >= 2 | REDUCED (rigorous) to: no (5,1) space [rows' DI_5] AND dim T_1(L(L')) <= 8 for every (5,2) space L' (non-split ones for (S3-a)); census 27/27 known (5,2) spaces have T_1 = 8 | sec 29 (B) |
| single-row elements in >= 2 rows, all entries <= 1 | OPEN, not analysed; the first-order bound alone is NOT enough (T_1(L_e (+) C e_e w^T) = 9 occurs) | sec 29 probe |

## Theorem F4b-X (round 9) — what a verifier must check
1. F4b normal form (sec 26 (A5)): x^{re} = e_r y_r^T + e_e p^T with ONE p; M = Phi (+) C e_e w^T (+) C G_ab (+) C G_cd; (y_r, g_r) independent
   (else m_ae >= 3 against (A1)); identities (i)-(iii) of (A5') from (CA2).
2. Moment lemma, sec 28 (M1)-(M4): generating function prod_j (1 + <t, v_j>) mod squares; (Y4)/(YU) pointwise formulas; Lemma (M3) s != 0
   (uses w, p independent and y_r != 0); classification C1 / C3 for s = 1 (case analysis over the number f of fat columns).
3. Exact eliminations, sec 28 (M5'): stage3/r9/gen9.py builds the systems (LEVEL = all coefficients of perm(J+m) - 120; FULL = + (i)-(iii);
   nd = Rabinowitsch on the 2x2 minors of (y_b,g_b), (y_d,g_d)); exact9.py / exact9c.py = Singular std over Q per chart; records
   stage3/r9/exact_*.txt and gb/ex_*.sing.out. Calibration calib_gen9.py (M_0 satisfies all LEVEL polynomials mod 3 primes, violates 12 FULL).
   C1G uses the S_4 symmetry of columns 1..4 (chart g_{a,1} = 1); chart 11113 closed by its stratified version (first nonzero coordinate).
   Numerical completeness check of the classification: stage3/r9/mom_search.py (see the round-9 STATUS lines for its outcome).

## Next targets I propose (in order)
0. (S3-a) via (PR2) (sec 29 (D)): prove "no 5-dim 4x5 level space without single-row elements has all four row projections of dim 2".
   It is a statement inside the 8-dim space (+)_r e_r (x) P_r — the plane-lemma setting of secs 12, 15 — and it closes (S3-a) for every
   defect. Census: 50/50 stored 5-dim 4x5 spaces consistent. Numerical probe stage3/r9/pr2_search.py is NOT calibrated yet (log pr2_cal.log;
   it must find s9-type spaces with the rank-2 hinge before the no-single-row run means anything).
1. (S3-a) via first order (alternative to 0): prove dim T_1(L(L')) = 8 for the non-split (5,2) spaces (rows' LAW: C = V_S, |S| = 3, two neutral columns).
   Formula that helps (sec 29 (B) and my derivation): T_1(L(L')) = {(t_R; t_e)}: (1) D_x c(x)[t_R] in C + C1 for all x in L' (c = deletion
   vector), (2) <t_e, c(x) + 24 1> + D(x; t_R) = 0 for all x; so dim T_1 = 2 + dim{t_R : (1) and (2) solvable}, and one needs that to be 6.
2. Mixed patterns (1,1,..): set up the counting (c1)-(c5) as in sec 26 (A); the moment method of sec 28 may apply whenever rows are lines.
3. S3-1: plain LM cannot calibrate (singular solution points, sec 29 (A)); spec in COMPUTE-stage3.md item 6 (long runs / deflation).

## Pitfalls met this round
- `pkill -f PATTERN` / `pgrep -f PATTERN | kill` inside a bash -c whose own command line contains PATTERN kills the calling shell
  (exit 144, nothing after it runs). Use a bracket in the pattern (`'s3seed.py ca[l]7'`) or kill by PID.
- `date -u` is UTC; `ls` times are local (UTC+1).
- Singular std over Q can stall on single charts where msolve mod p takes 1 s: run one process per chart with a timeout and close stragglers
  by the stratified cover.
- LM hit threshold 1e-8 rejects true solutions here (floors 1e-8 .. 1e-5 at singular points).

## Round 10 addendum (21:10 UTC) — read NOTES-stage3.md RESULT ROUND 10 and section 30
- (PR2) not proved. Two sufficient 4x5 statements for (S3-a): (PR2) [for L_e] and (PR2-split') [for L_r = X_re (+) e_e Z, with NO other
  single-row element]. The version of (PR2-split) without that clause is FALSE numerically: eleven (2,1,0,0)/(2,2,2,2) spaces in
  stage3/r9/pr2_sol_*.npy, stage3/r10/pr2split_sol_*.npy (that is the L_r shape of the mixed pattern (2,1,..)).
- New cheap test (rigorous): dim L <= dim T_1(L_r) - 1, and dim L <= FO2_0(L_r) (largest sigma_2-isotropic subspace of T_1(L_r)).
  Census stage3/r10/t1_census5.py over 60 known 5-dim 4x5 spaces: all excluded as L_r of a 9-dim space except ncdef_d5_e2_k1_s1 (FO2 bound 9,
  verify2/fo2lib) — test it next (common isotropic subspace of all q_m, or a small Grassmannian search inside T_1).
- (t2) normal form: core X0 in closed form (sec 30 (E)); exact systems too heavy here (COMPUTE item 8); calibrated probes queued (item 9).
- Pitfall: rank decisions on LM-limited data (e.g. s9, accuracy 1e-7) need tolerances ~1e-5; with 1e-8 a rank 2 form looked like rank 6.

## Round 11 addendum (21:40 UTC) — NOTES-stage3.md RESULT ROUND 11 and section 31
- ncdef_d5_e2_k1_s1 = member of the explicit family N(w2,w3) = F_4 (+) C e_2 w2^T (+) C e_3 w3^T (level iff <w2,w3> = 0). T_1 jumps to 13 on
  H = {w2 o w3 in span(w2,w3)} (the stored member) and on D (w2 = w3 isotropic). EXACT (Singular over Q): three rational members of H lie in
  no level space of dim >= 8 (null cone = 5 rank-3 quadric surfaces). Pipeline: stage3/r11/ncdef_exact2.py W2 W3 TAG; plane_check.py TAG.
- Lemma PFC (rigorous reduction): partial free column on four rows => dim <= 8 unless a (5,1) space with defect line C(1,1,1,1,-4) exists.
  This is the cleanest way to close the whole family (COMPUTE item 10; verifyfl's (5,1)_m machinery).
- (PR2-split') <=> (PR3) (3-row defect >= 3 for 3-dim 3x5 level spaces with rows in planes, no single-row element): next exact target. [<< REFUTED r17: false as stated (counterexample, NOTES-stage3 sec. 37 (E)); only (PR3') with all row projections exactly 2-dim survives >>]
- Pitfalls hit this round: (i) basis of a span of forms from SVD = rows of vh, NOT vh.conj(); (ii) QR of a rank-deficient matrix does not give
  its column space (use SVD); both produced a false "calibration failure" before being fixed.

## Round 12 addendum (22:05 UTC) — NOTES-stage3.md RESULT ROUND 12 and section 32; COMPUTE-stage3.md item 12
- Target: [T31] split A for m0 = (1,1,1,1,-4) (verifyfl did split B by hand, R8.8). Lemma SA1 (zero column <=> Theta(.,Z) == 0, then z_4 = 0)
  splits it into (alpha) Z = [W|0] with linear side conditions and (beta) all columns nonzero; (beta-1) (rank-one Z) is excluded exactly;
  (beta-2) and (alpha) are specified as small systems for verifyfl. Numerics: no (beta) Z in calibrated hinged searches.
- Useful coordinates: isotropic columns z = u^2 chi_1 + 2uv chi_2 - 2v^2 chi_3 (chi_k the Z/4 characters); sum z_j = 0 <=> span(U,V) totally
  isotropic in C^5; tau and perm become polynomials in (U,V).
- Pitfalls: the defect condition for m0 at degree 0 is C_4 + 4 C_0 = 120 (not 0) -- forgetting it gives a fake unit ideal instantly; msolve
  can segfault under ulimit 2 GB on positive-dimensional charts.

## Round 13 addendum (22:40 UTC) — NOTES-stage3.md RESULT ROUND 13 and section 33
- (alpha0) of [T31] split A for m0 is IMPOSSIBLE: Lemma S-SPEC (exact) + shape-S reduction; |supp W| = 4: one special W (3 configs run),
  |supp| = 3: 36 systems, |supp| = 2: the v-free plane P2 (18 systems); all unit over Q(i); calibrated by a degree-<=2 truncation.
  Scripts stage3/r13/: shapeS.py (+ shapeS_p3_*.sing), special_W.py, alpha0_W4_sing.py, alpha0_small.py, alpha0_P2.py, walpha.sing.
- Left in split A: (alpha1) (rank P_1 = 1; on f^perp it looks like (alpha0) but f^perp is 2-dim) and (beta-2) (needs both line blocks).
- Conic coordinates (sec. 33 (A)) make the split-A Z-conditions rational; WLOG all t finite (6-point orbit of infinity).
- Singular syntax pitfalls: matrix entries are M[i,j] (declarations M[r][c]); generate long expressions in Python rather than Singular loops.

## Round 14 addendum (23:05 UTC) — NOTES-stage3.md RESULT ROUND 14 and section 34
- verifyfl's (beta) run covers (beta-2) MOD P1 = 2147483629; char 0 only via Lemma RED-p once all of (alpha) is unit at P1.
- (alpha0): unit at P1 too (r14/to_modp.py converts any stage3 Singular script to char P1; run_modp.sh; special_W_modp.py).
- (alpha1): normal form A_j = n_j (x) psi_j + eps_j rho e_j (x) f; |supp W| = 3: 96/96 unit in char 0 and at P1 (calibrated numerically);
  |supp W| = 2, 4: open -- full systems too heavy (1.5 GB in 2 min); reduced plane formulation alpha1_s2plane.py running/next.
- Memory rule kept: one job > 0.5 GB at a time (S2-dimension and calibration runs were stopped for that reason).

## Round 15 addendum — NOTES-stage3.md RESULT ROUND 15 and section 35; COMPUTE-stage3.md item 13 (+ update)
- (alpha1) |supp W| = 2 and 4 closed: LEMMA S2 (shape S2 with b2, b3 != 0 forces b2 = b3) + point-configuration argument (|supp 4|) and
  a forms case split (|supp 2|) leaving two 7-unknown systems (unit over Q and at P1). So (alpha) is unit at P1 in every piece.
- Lemma S2: unit at P1 (neq + par, 3 a-charts each); over Q the parallel half is unit (slimgb); non-parallel over Q: chart a1 timed out at 20 min (slimgb, 1.4 GB) -- needs a better formulation or the big slot;
  (r15/run_s2q.sh, s2q.log). Over Q use slimgb -- std was > 4 min where slimgb took 75 s.
- Tools: r15/chilib.py (chi-coordinate formulas for <,>, tau, q4 and the t^2, t^3, t^4 coefficients of perm(J + tX), all over Q, self-checked);
  r15/s2lemma.py (S2 systems), r15/s2red.py (reduced |supp 2| systems), r15/run_red.sh (red.log).
- Pitfall found by calibration: looping over 1..size(E) in Singular skips zero generators (size counts nonzero entries) -- use ncols(E).
- (PR3): only the stratification (sec. 35 (E)); stratum (II) is the natural first exact target.

## Round 16 addendum — NOTES-stage3.md RESULT ROUND 16 and section 36; COMPUTE-stage3.md item 14
- [T31] for m0 complete at P1 (verify2). Lemma S2 over Q is only a low-priority cross-check.
- Leaf 8: Theorems SR5 (no single-row elements in all five rows) and SR2111 (z = (2,1,1,1,0)) -- hand + tiny exact checks (r16/srow32.py,
  r16/srow2111.py). Key reusable tool: the RANK-ONE FAMILY LEMMA (sec. 36 (E)(ii)). Open: (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0).
- (PR3): r16/pr3lib.py (sigma_m and deletion vectors as Singular strings, self-checked); stratum-(II) generators strat2.py, strat2b.py (H-part),
  strat2f.py (full, with x* of zero column sums); numerics st2_num.py (H-part solvable, 4-dim), st2_full.py (too slow here), ex21.py (structure
  of the 14 stored defect-2 examples: K_1 = K_2). (PR3) must be proven over Q (no RED-p: open hypothesis, non-empty closed variety).
- Fourier lemma (sec. 36 (H)) and the (1,1,1,1,0) classification are the natural start for the remaining leaf-8 patterns.
- Pitfall: pkill -f patterns can hit other agents' jobs with similar names (st2_ = stage2's F2col msolve runs); kill by PID.

## Round 17 addendum — NOTES-stage3.md RESULT ROUND 17 and section 37
- (PR3) and (PR2-split') are FALSE as stated: explicit exact counterexample (stratum III, 0-indexed, column 0 free), r17/pr3_counter.py;
  harmless for 9-dim spaces (FO2_0 <= 8 on 19 family members, r17/counter_scan.log). Corrected (PR3') = all row projections exactly 2-dim.
  (S3-a): types (t0), (t1) of L_e reduce to (PR3'); type (t2) needs a new argument (FO2_0 <= 8 for (t2)-type L_r is the natural one).
- Stratum (II): special locus empty for stratum (II) proper (exact over Q, r17/spec_exact.py); open: rank-drop locus of A(h) = special locus.
- Item 14(a) NOT queued (non-unit by construction without row hinges); generator/driver kept (r16/st2_bigQ.py, r16/run_st2Q.sh).
- Leaf 8 (1,1,1,1,0): Fourier sub-case impossible; 'three m + w' excluded except the rigid member m = (1,i,-1,-i,0) (-> PFC lead, r17/rigid_check.py).
- Name clash: stage3's (PR3) is not verifyfl's THEOREM PR3.

## Round 18 addendum — NOTES-stage3.md RESULT ROUND 18 and section 38
- (M3) false numerically: two non-degenerate X0 cores (r18/x0sol_hinge_2_1.npy with a column element; r18/x0sol_hinge_3_0.npy, main case,
  column-block shape, no column element). ST3-X0MAIN asked to be cancelled in QUEUE.md (append-only line 02:13).
- Stratum (III) = r_0 || h_0 part of the hinge-free stratum-(II) system (sec. 38 (B)); special locus = family (E) exactly.
- Leaf 8: rigid member -> free column on four rows -> PFC (r18/rigid_pairs.py); generic members of all (1,1,1,1,0) configurations excluded
  numerically (r18/cfg_kernels.py); special members remain.
- Tools: r18/pairtest.py (generic outside-row pair test generator), r18/x0core.py, r18/x0main.py, r18/x0_num2.py, r18/offspecial.py.

## Round 19 addendum — NOTES-stage3.md RESULT ROUND 19 and section 39; COMPUTE-stage3.md item 16
- ST3-TWOCOL (16 charts) queued by the coordinator (P1 triage LOW); decisive run = over Q (r16/run_twocol.sh 0).
- Column-element locus: stratum (II) proper empty, sigma = 1 exact (64/64); sigma = 0 24/64 unit + 40 timeouts (rerun longer).
- (t2): seeded extension probes from both X0 shapes fail; leaf-8 special k_N = 4 member survives the outside-row test.
- Generator modes added to r16/st2_bigQ.py: 'twocol', 'colel' (optional stratum-(II) hinges c0 c1 c2).
- Pitfall again: pkill -f with a pattern that also occurs in the same command line (e.g. inside a heredoc) kills the calling shell.

## Round 20 addendum — NOTES-stage3.md RESULT ROUND 20 and section 40
- Staged chart refinement (BRIEF UPDATE 16) works well here: r20/staged_colel.py closed the colel sigma = 0 charts (64/64 with 14 computed);
  r20/staged_twocol.py is the QUEUE'd decisive TWOCOL run over Q.
- dim Delta = 1: hand proof -> special locus; exact (refined) -> stratum (III) only for ka = 0; ka = 1, equal t's and dim Delta = 0 open.
- Pitfall: chart normalisations must be WLOG (d = h_0 - h_2 has no free scale except the global one) -- an early "unit" was an artifact.

## Round 21 addendum — NOTES-stage3.md RESULT ROUND 21 and section 41
- dim Delta = 1, distinct t's: closed for stratum (II). Trick: when U' vanishes at a column j, X minus column j is a level 3x4 space; the
  rank-one family lemma on 4 columns then gives linear cuts that make the exact system tiny (r20/dlt1sp.py, ka = 1: unit over Q in 0.8 s).
- Leaf 8: the special k_N = 4 member closes under PFC (orthogonality of column elements in different columns).
- Open in strata (II)/(III): equal t's, dim Delta = 0 (structure in sec. 41 (E), (F)); TWOCOL (big slot).

## Round 22 addendum — NOTES-stage3.md RESULT ROUND 22 and section 42
- Equal t's: case B -> coordinate vector (hand); case A |S| = 2 empty (exact, r22/eqtA.py + staged_eqtA2.py); |S| = 3 only degenerate on the sampled
  components; |S| = 4, 5 open. dim Delta = 0 reduced to h = e_j or U' = W_h explicit.
- Leaf 8: new special k_N = 2 family (r22/special_find.py, r22/kn2_special.py) -- the "only two special members" hope is false; a block analogue of PFC
  would be needed.

## Addendum, round 23 (07:25 UTC)
- k_N = 2 (leaf 8, (1,1,1,1,0)) CLOSED: the round-22 "family" has a pair-(0,1) third element only at t in {0,-1/4,-1/3,1} (exact over Q(w), t a variable,
  r22/kn2_fam.py, kn2_elim.py, kn2fam_sweep.log); M0 excluded (orthogonality / sigma_3), M1 forces a free column in column 4 -> Lemma PFC.
  Tools: r22/kn2_pts.sh (0-dim pair varieties: dim, vdim, points; w as variable), r22/kn2_span_check.py (exact level check of a span).
- Family B (= (2,2) member + (2,1,1) member B; (2,1,1) member A is in the k_N = 2 family): r22/famB.py (Q(a), 6a^2+3a+1 = 0, t variable),
  r22/famB_sweep.sh r k 1. Pair (0,1): block charts only at t in {0,+-1,-2}; off-block charts xl3, xn3, xl4: 2-dim family of 2-column-block
  elements p (x) e_3 + q (x) e_4 for every t. Logs famB_01.log (xn4, v4 pending), famB_23/02/03.log (pool job, may have been cut by its 25-min timeout).
  NEXT: (i) finish the famB pair sweeps; (ii) a joint test: xi_01 = p (x) e_3 + q (x) e_4 plus the pair-(2,3)/(0,2) third elements, exact,
  few unknowns; (iii) a block-PFC: the 2-column part K = {p (x) e_3 + q (x) e_4 in L} is totally isotropic for <p,q'> + <q,p'> (dim <= 4) --
  try to push this into a contradiction with the regime counts.
- Case A |S| = 3: |F| = 0 excluded (r22/rowhinge_30.log, 30/30 unit). |F| = 1: r22/rowhinge_31.log (6/10 charts, row 2 always a line); resume
  with rowhinge_sweep2.py restricted to charts 11-14 (driver must stay < 30 min). |F| = 2, |S| = 4, 5: open.
- Upstream: L_gct_111 gives sum dim Z_i <= 4 (single-row parts) and its transpose for column parts; L_gct_110 is sufficiency only.

## Addendum, round 24 -- STOPPED 08:03 UTC (L-gct-210 aborted by Kevin via coordinator)
- Leaf 8 (1,1,1,1,0): all special members found are closed modulo Lemma PFC (family B excluded: r22/famB.py, famB_23.log; k_N = 2: sec. 43 (D), (E)).
  Still numerical: generic-member exclusion (sec. 38 (C)) and completeness of the special list; exact configuration varieties need > 0.5 GB (r24/cfgvar.py).
- Equal t's case A: |S| = 2 empty; |S| = 3 |F| = 0 excluded, |F| = 1 no (PR3') (r22/rowhinge_31.log); |S| = 4 |F| = 0 non-degenerate classes unit,
  |S| = 5 partly (r24/eqtA_cls.py, cls_sweep.sh, cls_40*.log, cls_50x.log); degenerate case be = 2 open (r24/degH.sing: 2-dim family of H).
- dim Delta = 0: function-of-h reduction (NOTES sec. 44 (E)); QUEUE ST3-DLT0D (r24/run_dlt0d.sh) queued, NOT run; r24/dlt0e.py pool split memory-outs.
- No jobs of mine running.
