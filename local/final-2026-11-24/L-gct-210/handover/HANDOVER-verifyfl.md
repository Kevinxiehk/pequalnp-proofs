# HANDOVER-verifyfl (cold-start brief; written by verifyfl at the end of round 7, 2026-11-23 ~20:40 UTC)

Read first: TEAM-RULES.md; NOTES-verifyfl.md (RESULT ROUND 7 at the top, then section DI5-R7); COMPUTE-verifyfl.md section NEXT
(the plan N1-N6); COMPUTE-ERRATA.md round-6 addendum (verify2's corrections).  All my files: verifyfl/ (scripts), verifyfl/exact/
(exact generators), verifyfl/r7/ (this round's drivers, logs, manifests).

## The goal of this branch
(DI_5) at e = 1, i.e. no 5-dim 4x5 space with a defect line C m (then the defect inequality excludes (5,1)), via
(SL_m): "a column-centred 4x5 space with defect in C m has dim <= 3" (m not two-column).  For fixed m, (SL_m) <== the three typed
systems [DC3] (no 3-dim doubly centred space with defect; kills types (1,3), (0,4)), [T22], [T31] are all empty.  (Only <==.)

## How a mod-p run becomes a char-0 proof (NOTES-verifyfl R7.1, LEMMA RED-p)
X_k = {spaces in Gr(k, A) with defect in C m} is closed in a Grassmannian over Z (resp. Z[w]) -> proper -> a C-point gives an
F_pbar-point for every p.  In char p > 3 the facts (F2) (neutral columns on isotropic lines), (C2'), (F3), (F4) still hold (only
char != 2, 3 is used), so every F_pbar-point lies in one of the case systems of gen_n1s/gen_dc ([DC3]), gen_n3 ([T22]), gen_n2 ([T31]).
So "all case systems unit at ONE prime p" is a char-0 proof.  Open conditions inside the char-p case split are harmless.

## State at hand-over (details and evidence: NOTES-verifyfl RESULT ROUND 7)
* THEOREM DC3 (char 0) for m = (1,2,-3,0,0) [two primes], (1,1,-2,0,0), (1,w,w^2,0,0) [one prime each]: all 254 structured cases unit.
  The two generic rank-2 cells needed the SUBSYSTEM CUT (verifyfl/r7/cut_cell.py): add GB of the plane subsystem S1 (and its
  column-swap image) to the cell.  verify2 re-derived the equation span of all 254 cases independently.
* [T22]: no non-unit case anywhere.  m12m3, m11m2: N-cases 95..10 UNIT; iso: 95..12 UNIT.  Cases 11, 10 work with the strategy
  "GB of the 2-dim N-system first (up to 15 min), then N+Y stages".  Case 9 (ab,ab) and rho = 2 (0-8) exceeded 2.5 GB; all my chains
  were STOPPED at hand-over (20:50).  Resume: `NTMO=900 ./n3_chain.sh M START END` or QUEUE VF-T22H (threads, 8 GB).
* [T31]: undecided.  Single-thread runs die at 2.5 GB.  QUEUE VF-T31 (cells 0 and 3 suffice by row symmetry).  Hand lead R7.5.
* QUEUE: DC3-STOP, VF-DC3X (the coordinator started it: runs/dc3x), VF-DC3-P45, VF-T31, VF-T22H.
* Do NOT edit r7/n3_chain.sh while a chain runs (bash reads scripts incrementally; an edit broke the iso chain's tail, harmlessly).

## Commands (cwd verifyfl/r7 unless stated; all single-thread, ulimit -v 2500000)
  python3 -I ../exact/gen_n1s.py P MSPEC 3 dc3 run timeout=90        # [DC3], 254 cases (|supp m| = 3, columns 3,4 neutral)
  python3 -I ../exact/gen_dc.py  P MSPEC 3 OUT run timeout=90         # [DC3] for ANY m (|supp m| = 4: 192 cases, 5: 220); == gen_n1s on {3,4}
  python3 -I cut_cell.py P MSPEC PIV ab ab cut/PREFIX                 # decide a timed-out generic rank-2 [DC3] cell by the cut
  ./n3_chain.sh MSPEC [START]                                          # [T22]: all 96 N-cases x 3 S-cells (n3_case.py), log n3_chain_MSPEC.log
  python3 -I n2_direct.py P MSPEC CELL a n2/PREFIX 1200               # [T31] stage a, one Zs-cell (Zs-GB then full)
  python3 -I n2_cell.py   P MSPEC CELL a n2/PREFIX 900                # [T31] degree-staged variant
  python3 -I subcut.py n3 P MSPEC -1 S n3/PREFIX "0,1,2;0,1,3;0,1,2,3" Nfix=II|IP|I034|II2|K2N   # [T22] calibrations
Tests (no engine): ../exact/test_gens.py, test_gens2.py, test_n2.py, test_n3.py, test_gen_dc.py — all must print ALL TESTS PASSED.
PITFALL: never `pkill -f PATTERN` / `pgrep -f PATTERN | xargs kill` when PATTERN also occurs in your own command line (it kills
your shell).  Use `ps aux | grep "[x]yz"` in a command that does not otherwise mention xyz, or kill by PID.

## Next targets (in order)
1. [T31] for m12m3 (6 Zs-cells; by the row-permutation symmetry only cells 0 and 3 are needed): if the direct run stalls, cut by
   (a) vartheta(Zs) = 0 / != 0 (char-p valid split), (b) the stage with Y_1 linear (first-order conditions), (c) more memory (QUEUE).
2. [T22], [T31] for m11m2 and iso (n3_chain.sh m11m2; ... iso).  For iso [DC3] is unit, so no [T13]/[DC4] is needed there.
3. [DC3] for |supp m| = 4, 5 with gen_dc.py (list of request B in COMPUTE-verifyfl.md), then gen_n2/gen_n3 for those supports
   (gen_n3 is written for columns 3,4 neutral only; generalise its nbasis() with gen_dc.build(keyed=True)).
4. Symbolic m (one parameter per support size): needs computations over Q (or certificates), because the reduction argument of
   R7.1 does not control the parameter line mod p (a char-0 parameter value can reduce onto a two-column value).
5. e = 2, 3 (N6 of COMPUTE-verifyfl): the same generators with W = basis of C^perp of rank 5 - e.

## Symmetry savings for the remaining hard [T22] cases (not yet used in the chains)
Swapping the neutral columns 3, 4 and the row swap (2 3) (which maps the chart z1 = (0,1,w,w^2) to z2 and keeps the 'ab' chart and a
pivot in row 0) are symmetries of the whole [T22] system (S-cells cover all planes, so the permuted S lands in some cell).  Hence among the
rho = 2 N-cases 0-8 only (ab,ab), (ab,z1), (z1,z1), (z1,z2) are needed, and among 9-11 only (ab,ab), (ab,z1).  State the symmetry
argument when citing such a reduced cover.

## Round 8 update (21:50 UTC) — read NOTES-verifyfl RESULT ROUND 8 and sections R8.0-R8.8 first
* [T31] = split A (vartheta(Z) = 0) + split B (vartheta(Z) != 0).  Split A: DONE (theorem) for m12m3, iso, m11m2
  (r8/t31e_stages.py A / R2:ab|z1|z2, stage labels "Z1;Z2;Z12", 0.5 s).  Split B: eigen normal form gen_t31e.py (distinct entries);
  for m = (1,1,1,1,-4) split B is a HAND theorem (R8.8).  Split B for m12m3/iso is the open computation (QUEUE VF-T31B-UPDATE; B0/B1 by
  omega; single-thread 2.5 GB is not enough).  Ideas not yet tried: decompose the degree-72 B0 Z-set into Galois orbits / S_4-orbits
  (msolve -P 1, factor the eliminating polynomial) and run per component; for B1 use A_n omega = -omega (A_n = -1 on omega, O(2) on
  omega^perp: one parameter per neutral column).
* m = (1,1,1,1,-4) (p5b; top priority from stage3's Lemma PFC): split A is open.  Hand reduction started (scratch, not in NOTES as a claim):
  if Theta(.,Z) = 0 then z_4 = 0 and s^*g + 4 vartheta has rank <= 1; in its rank-0 sub-case every Y in K has the form
  (s/2)(1,1,1,1,-2)^T + sum_{j<4} mu_j v_j (e_j - e_4)^T with fixed isotropic v_j: a ~20-unknown system.  If Theta(.,Z) != 0 then all five
  z_j are nonzero isotropic.  [DC3], [T22] for p5b: QUEUE VF-P5B-FIRST (gen_dc / gen_n3g).
* e = 2, 3: gen_dc 'C:v1;v2' mode works (QUEUE VF-E23-DC3).  SYM-M (verify2's spec, one parameter t, elimination over Q): not started.
* [T22] case 9: use r7/n3_case_split.py (al0 / alne).  m12m3 al0 UNIT; alne queued (VF-T22-C9).  Same split for m11m2, iso.
* All my jobs were stopped at the end of round 8 (21:56).

## Round 9 update (22:50 UTC) — read NOTES-verifyfl RESULT ROUND 9 and R9.1-R9.7
* SAME-PRIME RULE (R9.1, R9.7): every piece of a case split made after reduction mod p must be decided at the SAME prime P1 = 2147483629
  (or by a hand proof valid in all char p > 7).  Do not mix a char-0 piece with a mod-p open-condition piece.
* [T31] for m12m3 / iso / m11m2 at P1: split A THEOREM, split B0 DONE (components; r9/b0_all.log, b0g_*.log), split B1 OPEN (big slot
  VF-BIGQ-SWAP: t31e_stages kind B1:X:I, gen_t31b1.py).  Idea not tried: decompose the B1 3-column plane stage like B0 (its Z-locus may be
  finite: Y_omega lies in the 7-dim first-order kernel W(Z) intersected with the 9-dim 3-column space, and x parallel to omega adds 2 conditions).
* m0 = (1,1,1,1,-4) at P1: split B hand (R8.8); (beta) 32/32 UNIT; (alpha) KT charts 12, 123, 01, 012, 0123 UNIT, charts x, 1, 0 OPEN
  (VF-M0-ALPHA-UPDATE); [DC3] 214/220 + 6 hard cells (VF-P5B-DC3-HARD); [T22] r9/n3g_chain_p5b.log (generic driver n3g_case.py).
* Drivers: r8/t31e_stages.py (kinds E, E0, E1i, A, R2:*, AC:c, B0G, B1:X[:I], M0K:INF, M0R1:*, M0N:INF[/signs]; gfac=FILE:I:LIN for components),
  r9/factor_elim.py, r9/run_b0g.sh, r9/run_beta.sh, r9/run_alpha.sh, r9/run_alpha_nf.sh, r9/n3g_chain.sh.

## Round 10 update (23:56 UTC) — read NOTES-verifyfl RESULT ROUND 10, R10.1-R10.10
* SYM-M is the priority (PROOF-MAP leaf 1).  KEY (R10.8): put m on a PROJECTIVE line (charts A, B of gen_sym.py); the family is proper over
  P^1, so a case UNIT in F_p[t, x] in both charts is empty for EVERY m in char 0.  [DC3] |supp m| <= 3: A 252/254, B 249/254 UNIT; open: the
  generic rank-2 cells (symbolic cut r10/sym_cut.py, > 2.5 GB) and 3 chart-B cells (long timeout).  Next: the same for [T22] (gen_n3 with
  symbolic W) and [T31] (split A with the R2 systems for all pairs, B0/B1 generic forms - the eigen form needs distinct entries), then
  |supp m| = 4 (P^2 of lines: two parameters, charts) and 5 (P^3).
* m0 = (1,1,1,1,-4): [T31] complete at P1 with stage3's (alpha1)/(alpha0) (pending verify2); my structured (alpha) forms: rank one
  gen_m0a.build_alpha_r1s (42/42), rank two build_alpha_r2s (9/9), rank three plane-adapted build_alpha_s (partly).  [DC3], [T22] for m0 in the
  big slot (bigq3).
* B1 (omega != 0) for m12m3/iso/m11m2 not shrunk: plane stage > 2.5 GB, block elimination segfaults, Singular eliminate > 25 min.

## Round 11 update (00:56 UTC) — read NOTES-verifyfl RESULT ROUND 11, R11.1-R11.19
* RULE: properness gives char-0 content only for the WHOLE cover at one prime (verify2 [L],[M]); per-case claims are invalid.
* R11.6: target (5,1) directly; non-unit cases are fine iff their Rabinowitsch system (+ u t (t+1) - 1) is UNIT mod P1 (char-p statement), given
  TC5 in char p (R11.7, R11.9; audit pending).
* Open SYM-M pieces (|supp m| <= 3): [DC3] A0-ne, B0-ne (big slot, sym_cut2.py ne); [T22] chart A 21, 18, 11..0 and chart B 45, 21, 18, 11..0
  (big slot, n3sym_case.py with NTIMEOUT 7200); [T31] split B (plan R11.17: m is determined by Z, t-free systems; B0 by components of a curve,
  B1 three-column form).  Then supp 4, 5 with gen_sym_dc.py (P^2, P^3 charts).

## Round 12 update (02:10 UTC) — read NOTES-verifyfl RESULT ROUND 12 and R12.0-R12.6
* E-STALE-OUTPUT: guarded copies verifyfl/r7/subcut_fixed.py, verifyfl/exact/exactlib_fixed.py.  New drivers start with
  `import subcut_fixed as subcut; sys.modules['subcut'] = subcut` and set `X.run_msolve = exactlib_fixed.run_msolve`.  Audit tools
  r12/stale_audit.py, r12/manifest_check.py, r12/resolve.py (all proof-relevant manifests reproduced, 0 mismatches).  Swap the guarded
  versions into subcut.py / exactlib.py only when no job imports them (with a note).
* [DC3] SYM-M A0-ne / B0-ne: coordinator runs r11/sym_cut2_v2.py (SYMTMO env).  My alternative r12/sym_cut3.py (theta-orthogonal
  normalisation) is untested at full length: `SYMTMO=1500 python3 -I sym_cut3.py 2147483629 A 0 sc3/A0` (pool, 2.5 GB).
* [T22] hard cells, NEW COVER of the rho = 2 N-cases (R12.2-R12.5): pieces by vartheta on N.
  - piece (IV) vartheta == 0: r12/gen_t22t0.py (u_0,u_1 charts), gen_t22t0b.py (+ explicit u_2), gen_t22t0c.py (u's all 'ab': det split);
    drivers t0_cell.py / t0b_cell.py / t0c_cell.py (`python3 -I t0_cell.py P C CI OUTDIR TMO [items]`).  A case 0: 15/16 + 3/4 UNIT,
    det split see t0/A0c.log.
  - pieces (I)-(III): plan R12.5 = basis (Z_1, Z_a) with Z_a an isotropic-column element: r12/gen_t22iso.py + iso_cell.py (piece P2:
    vartheta(Z_1) != 0; 64 u-triples; the ab:ab:ab one will need the det split as in gen_t22t0c).  Piece P1 (vartheta(Z_1) = 0) = Z_1
    isotropic-column + Z_2 general (to write; contains piece IV).
  - rho = 1 pivot 0 (cases 9-11): piece IV generator r12/gen_t22t1.py + t1_cell.py (u_0 forced 'ab'); pieces with vartheta != 0 as R12.5.
* Pool chain r12/chain12.sh (one job at a time): t0c A0 -> t1 A10 -> iso A0 (2 triples) -> sym_cut3 A0; log r12/chain12.log.
* ncol R2.14 removes no typed case (R12.6).  [T31] split B symbolic and |supp m| = 4, 5 not started this round.

## Round 13 update (03:00 UTC) — read NOTES-verifyfl RESULT ROUND 13 and R13.0-R13.5
* CORRECTION: b_n(Y) = 2 y_n - s(Y) (R4.1), not column n.  R13.1/R13.4 flagged in place; R13.5 is the corrected radical form.
  Void tools (marked in their headers): anycell.py, sc0rad.py, pc_cell.py, and gen_t22pc.py's rad option (raises an error).
* Radical S-cells (corrected, calibrated on K_2 with r12/calib_rad.py): r12/gen_t22rad.py (nb = n3 | t0c | t0b | pc), drivers radcell.py
  (stages N+Y_1 | N+Y_2 | all) and radcell2.py (+ xn extras, stages N+Y_1 | all; env RCS=0,2 to run selected cells).
  `python3 -I radcell2.py 2147483629 A 0 t0c 01 rad/A0_t0c_01 600 t0/t0c_A_c0_01_None_N.ms.gb`
* [DC3] ne pieces: r12/sym_cut4.py (S1 per u-chart of Z_1'), sym_cut4_full.py (pairs).  S1 list for A0: chain13.out ("S1 A piv0").
* Pool chain r12/chain13e.sh (log chain13.log / chain13.out); watchdog13.sh stops everything when Lean window 3 opens (03:50 at the latest).
* Self-kill rule (again, twice this round): never `ps | grep "[x]name"` + kill in a command line that also contains "xname" anywhere.

## Round 14 update (03:55 UTC) — read NOTES-verifyfl RESULT ROUND 14 and R14.0-R14.8
* Radical S-cells now also have the OPEN chart {r_3 != 0}: rc4 (r = alp b1 + bet b2 + b3, s_2 = b1 + sig b2), rc5 (s_2 = b2); option gam0
  (rgam = 0) on rc0-rc3 gives the complementary stratum.  Cover of a piece = rc4, rc5, rc0..rc3 with gam0.
* Drivers (r12/): radcell3.py (fine stages + extra filtering; env RCS), radcell3g.py (+ GAM0=1), radcell3r.py (+ RSPLIT=v3|v4|gen),
  radcell3p.py (+ PERM34=1), radcell3q.py (+ PERMP=1); generator gen_t22rad.py (options xn, rsplit, perm34, permP, gam0, calib_rho1).
* t0c-01 (A case 0, piece IV, u_0 = u_1): only rc4 open.  Next: rc4 (pool 25-min stages or big slot), then t0c-02 / -12 / -ne the same way.
* Symbolic [T31] B0: gen_sym_b0.py + b0sym_run.py (Z-set GB instant, stage Z+Y_1 > 2.5 GB).
* Calibration: calib_rad.py (K_2 in rc0; K_2 has r_3 = 0, so rc4/rc5 are not calibrated by K_2 - use a row-permuted K_2 next round).

## Round 15 update (05:35 UTC, session end) — read NOTES-verifyfl RESULT ROUND 15 and R15.0-R15.8
* Chart B is redundant under R11.6 (R15.6, confirmed by verify2): work in chart A only.
* Radical-cell options in gen_t22rad.py: rc0-rc3 (echelon), rc4/rc5 (open chart r_3 != 0), rc6/rc7 (rational: S = span(w(tau), w'(tau)),
  r = chi_3), gam0 (r_3 = 0 stratum).  Calibrations: calib_rad.py (rc0), calib_rad4.py (rc4), calib_rad6.py (rc6) - all PASSED.
* Status of A case 0 piece IV: t0c-01/02/12 = only rc4 open (big slot VFRAD_A0_01_RC4 for t0c-01; add -02, -12 if 10 GB suffices);
  t0c-ne (D != 0): untested with radical cells ('nl' presentation available in gen_t22t0c).  Pieces P2/P1: 4 sample items, rc4 open in the
  two P2 items.  Remaining 60+ u-triples per piece not run.
* rc7 (r = chi_3) is special for t0c-01 (N+Y_1 non-unit) - investigate why (chi_3 is the quarter-turn eigenvector) before scaling.
* Symbolic [T31]: gen_sym_b0.py / b0sym_run.py (big slot VFB0SYM_A queued), gen_sym_b1.py / b1sym_run.py (not run).
* All my pool jobs and the watchdog were stopped at 05:33.  Chains: chain13*.sh, chain14*.sh, chain15*.sh, chain16.sh (logs chain13.log/.out).

## Round 16 update (06:10 UTC) — read NOTES-verifyfl RESULT ROUND 16 and R16.0-R16.5
* Pool rule while the big slot is busy: <= 0.5 GB.  Use r12/rsscap.py (RSS cap; msolve needs > 0.7 GB VIRTUAL to start, so ulimit
  cannot enforce 0.5 GB) and r12/killpat.py (kill by regex without killing your own shell).
* gen_t22rad options added: spec = e3 | e4 | gen (special radicals, R16.1), rab (early two-column Rabinowitsch, R16.2); drivers
  radcell3s.py (SPEC), radcell3t.py (SPEC, RAB).  b0sym_run.py: env RAB=1.
* Big slot queue (coordinator): VFB0SYM_A (RAB), VFRAD_A0_01_RC4 / 02 / 12 (radcell3t RCS=4 RAB=1).  If 01 fails at 10 GB, hold 02 and 12.
* N-sweep of P1a/P1b/P2 (A case 0): r12/nsw/A0.log; open items listed in NOTES R16.5.

## Round 17 update (07:05 UTC) — read NOTES-verifyfl RESULT ROUND 17 and R17.1-R17.6
* KEY TOOL: junk removal at the N level.  r12/nlam.py C CI NB NBARGS [perm] [mu] [TMO]:
  - piece IV (nb t0c / t0b): 8 lambda-words (gen_t22rad option lamch), early two-column Rabinowitsch (rab);
  - pieces P2/P1a/P1b (nb pc): option mu (isotropic-column generator's columns nonzero; their zero branches are the '0' items).
  N-UNIT in all words decides the item (given all '0' items decided and R11.6).  RSS cap via env NLAM_CAP (pool: 550).
* Whole rho = 2 case: r12/case_nlevel.sh CI (log nlam/case_<CI>.log).  Case 0 done except the generic all-'ab' items (batch
  nlam_batch1.sh, big slot VFNLAM_A0_1) and P2 (running, nlam/pc_mu_all.log).  Case 1 running.  Still to do: cases 4, 5 (2,3,6,7,8 by
  symmetry), rho = 1 cases 9-11 (needs P-pieces for rho = 1: generalise gen_t22pc/gen_t22t1 with the same junk removal), [DC3] A0-ne.
* verify2 is auditing R17.4 (coordinator).

## FINAL (STOPPED 08:04 UTC) — work on L-gct-210 aborted by Kevin
* All my jobs are stopped.  Final ledger: NOTES-verifyfl.md, SYM-M STATUS TABLE v2 (DI5-R18) and R18.8.
* State in one line: SYM-M [DC3] complete; [T22] case 0 down to the items of VFNLAM_A0_1/_2, case 1 piece IV done, case 9 partly; cases 4, 5,
  10, 11 and [T31] B0/B1 not done.  Key tools if resumed: r12/nlam.py + case_nlevel2.sh (rho 2), r12/nlam1.py + rho1cell.py (rho 1),
  junk removal R17.4/R17.5/R18.3, early two-column Rabinowitsch R16.2, rsscap.py (RSS cap), killpat.py (but see R18.8: killpat on a shared
  script name also hits other agents' jobs).
