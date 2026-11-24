# Team brief: gap L-gct-210 (hard, finite, either answer wanted)

You are one of several agents on ONE gap of the public pequalnp-proofs project (each gap is a
Lean 4 statement that counts only when a proof checker accepts it). Record:
/home/claude/work/L-gct-210/gap.json (read it).

## The question
Statement: every linear subspace L of 5 x 5 complex matrices with
sum over permutations f of prod_i (1 + t(i, f i)) = 120 (= perm(J + t) = 5!) for all t in L
has dim L <= 8. "It may be false": a REFUTATION is an explicit level space of dimension 9.
The largest known has dimension 7 (checked: Outside/L_gct_189.lean, and the general 2n-3
construction L080 in Gct/Helpers/LevelLow.lean).

Facts (all easy or checked):
- Level <=> P_1 = ... = P_5 = 0 on L, where P_k(t) = sum of all k x k subpermanents of t
  (perm(J+t) = sum_k (5-k)! P_k(t)).
- Write t = alpha_i + beta_j + gamma (alpha, beta sum-zero vectors in C^5, gamma doubly centred
  (DC), dims 4 + 4 + 16; the constant part is killed by P_1 = 0). Then
  2 P_2 = -20 sum alpha^2 - 20 sum beta^2 + sum gamma^2, a nondegenerate quadratic form on the
  24-dim space, so dim L <= 12 from P_2 alone. On DC matrices: P_2 = p_2/2, P_3 = (2/3) p_3,
  P_4 = (3/2)p_4 - (3/4)(sum_i r_i^2 + sum_j c_j^2) + p_2^2/8 + (1/4) tr((t t^T)^2)
  (r_i, c_j = row/column sums of squares; p_k = sum of k-th powers of entries).
- Checked bounds: 3x3 level <= 3 (Gct/L094); 3x3 DC <= 1 (Outside/L_gct_109); 4x4 DC <= 3
  (Outside/L_gct_216, 1300 lines); 4x4 row-centred <= 5 (Outside/L_gct_217); reduction to DC
  losing 2n (Gct/L092: all level <= DC bound + 2n); block-diagonal gluing (Outside/L_gct_110);
  power-sum tools: Kneser (L065), iterated Fermat (L067: if p_2..p_k vanish then k*dim <= N),
  L061 (p_2 = p_3 = 0 gives dim <= N/3), T3 (L163); product-type bounds (L090, L_gct_111/114/123).
  The n = 4 full bound (<= 5, "L-gct-091") is NOT checked; its helpers exist (Gct/Helpers/LS4).
- Previous team work on the general-n version (L-gct-086) is in /home/claude/work/L-gct-086/
  (NOTES-*.md: literature, smallcases, proof, construct, infra). Read NOTES-infra.md and
  NOTES-smallcases.md first. Tools there: smallcases/level.py (fast P_k + gradients via Ryser,
  exact checker), smallcases/search.py and extend.py (Levenberg-Marquardt searches),
  infra/Kit.lean and infra/KitFermat.lean (compiling Lean kits), infra/strip.py.
  Known pitfalls: p_4 need not vanish on DC level spaces (glue the 4x4 circulant line of
  L_gct_193); unstructured random search at n = 5 failed even to find dimension 7, so seed
  searches with known spaces; at n = 4 numerics suggest max level dim 5 and max DC dim 2.
- Evidence so far suggests the true maximum at n = 5 is 7 = 2n - 3 (so <= 8 has slack 1).

## Hard limits
- No heavy computation: no brute-force enumeration, no Groebner bases on large systems, no long
  solver runs; keep each run under ~3 minutes of CPU (2 cores shared by all agents). If a route
  clearly needs heavy computation, record that and drop it.
- Do not touch /home/claude/pequalnp-proofs (read only), no git, no contact with pequalnp.com.
  Python: python3 -I. Lean: compile only with
  /home/claude/tools/leancheck FILE /home/claude/work/L-gct-210/gap.json (about 50 s per run;
  helper test files may use a placeholder theorem; only the final file must state the gap).
- Final Lean file (if ever): imports only `import Mathlib` and `import PEqualNP.Defs`; checked
  lemmas from other files must be copied in; no comments, no double quotes, no # commands, no
  sorry/axiom/native_decide/instance/structure/attribute words; <= 512 KiB.

## Sharing
Work in /home/claude/work/L-gct-210/<role>/. Append concise findings to
/home/claude/work/L-gct-210/NOTES-<role>.md as you go; read the others' NOTES-*.md regularly.
Put a complete proof idea or a verified 9-dim space at the top of your notes under RESULT.
Check in by writing a line "STATUS <time>: ..." in your notes at least every 15 minutes.

## Report
When your budget ends (stated in your task) or you finish, reply with: what you established
(with evidence: exact or numerical), what you ruled out, and the best next step.

## UPDATE (round 2 state; read before anything else)
- Lean framework DONE: /home/claude/work/L-gct-210/lean/Frame210.lean (+ Frame210Fermat.lean), guide in
  NOTES-lean.md. It proves the d = 0 case and `gap_of_S_wlog`: the gap follows from r_A + d <= 4 under
  r_A <= r_B (r_A, r_B ranks of row-sum / column-sum maps on L, d = dim(L cap DC)). Also has polarization
  of P_3 (lev_T3), DC peeling, the P_3 coupling identity lev_P3_dc.
- Known 7-dim level spaces: L080, ex1, ex2, ex3, an exact 1-parameter family, a 4x2-block family (see
  NOTES-numerics.md, NOTES-split.md). None extends to 8 (first-order extension = L + one rank-one
  row/column-mean direction, which breaks P_2). No 8-dim level space found anywhere.
- KEY NEW LEAD (NOTES-lowd.md): numerically, P_2 = P_3 = 0 ALONE caps ANY subspace of the 24-dim
  sum-zero space at dim 7 (dim 8: 0 of 18 starts incl. seeded; dim 7: easy). Expected-dimension count
  for planes in V(quadric) ∩ V(cubic) in P^23 is negative from dim 8 on. So a sufficient (stronger)
  target is: NO 9-dim subspace of the sum-zero 5x5 matrices on which P_2 and P_3 both vanish.
  Exact formulas available: P_3 bidegree form and u = g - (3/2)a identities (NOTES-split.md),
  column-centred P_2..P_5 (NOTES-lowd.md), phi-identities (NOTES-methods.md), Hessian-image method
  (NOTES-dc5.md), stabilizer pattern of extremal examples (NOTES-dc5.md).
- Dead ends now: Fermat/Kneser directly (no commutative algebra structure; 45 coords give 15);
  naive growth Y4 >= 3d (fails on block-supported spaces); fixed-g relaxation alone (fails for
  block-supported g); small exact subsystems for d = 1.

## UPDATE 3 (supersedes the "KEY NEW LEAD" above)
- The P_2/P_3-only target is FALSE (NOTES-repr.md, exact): L9 = { x v^T + z e_4^T : x in C^5, sum z = 0 },
  v = (1, i, -1, -i, 0), is a 9-dim subspace with P_1 = P_2 = P_3 = 0 (not level: P_4, P_5 != 0).
  So any proof of the gap MUST use P_4 or P_5. Earlier LM "dim 8 impossible from P_2, P_3" was an artifact.
- Exact: the only level spaces containing the 3-row DC space K (dim 4) are K and five 5-dim extensions
  (NOTES-kbuild.md). Exact: a level space containing a full row/column block has r <= 7 (NOTES-hessmix.md).
- Special DC elements = singular points of perm_5; conjecture "Lemma Z": they have a zero row or column
  (NOTES-methods.md; agent lemmaz is on it).
- Growth data and product formulas: NOTES-growth.md (G1-G3 exact).
- LM negatives are unreliable at n = 5 unless the search passes a planted-solution calibration.

## UPDATE 4
- Theorem FL (NOTES-zeros.md; being independently verified by verifyfl): a level space containing a full free
  row or column has dim <= 7. Every known 7-dim space contains one.
- Observed law (NOTES-repr.md, 34 of 34 seven-dim spaces): exactly one row or column is "deletable"
  (zeroing it keeps the space level); equivalently y_c = 1 e_c^T - J/5 lies in the first-order extension
  space; this forces the column-mean coordinate beta_c = 0 on L. Conjecture (D): every level space of
  dim >= 7 has a deletable row or column. Exact identity (repr): perm(J + X V^T) = sum_a (5-|a|)! a! E_a(X) E_a(V).
- kbuild RESULT 2: local (single DC element, second order) mechanisms cannot bound the degenerate DC types.
- Lemma Z: ranks 1, 2 proved; ranks 3, 4 open; one-sided variant false (NOTES-lemmaz.md).

## UPDATE 5
- Theorem FL / Lemma SL are INDEPENDENTLY VERIFIED (NOTES-verifyfl.md: complete self-contained blueprint S0-S11):
  a level space containing a full free row/column has dim <= 7; a strongly level 4x5 space has dim <= 3.
- Shared checkout updated to the latest main project (c3037b0). Newly checked upstream: Outside/L_gct_214.lean
  (every 4x4 level space has dim <= 6), Gct/L218.lean. Read L_gct_214 if a 4x4 bound or its technique helps.
- chief final: ZBF tools, Lemma C, Theorem A, Theorem G, row-pair Types I, II, I' (NOTES-chief.md).
- rows: defect construction (NOTES-rows.md): deletable row r  <=>  L inside L' (+) e_r (x) (C(L') + C1)^perp.

## UPDATE 6 (state after cascade stages 2 and 3, round 1)
- stage2 (NOTES-stage2.md): chief's C4/C7 re-derived and correct; tau-coordinates; triple theorems T1, T2, T2'';
  Corollary S2: in the zero-free a = 1 regime a triple with X_ijk = 0 has exactly two minimal Type II pairs sharing
  a row. Open: minimal pairs themselves (Types I, II, I'), 21 Type-II/Type-II configurations, zero entries in
  annihilators, rows with a_r >= 2, pairs with lam >= 3.
- stage3 (NOTES-stage3.md): tools GZ, SR/SC, D2, D3, T1 (squarefree calculus), Q0, P2T; Theorem S3-A (ten B-type
  2-row elements are independent: a second 9-vs-10 pigeonhole); S3-B (conditional on HQ: single-row element);
  S3-D (minimal case forces block-type planes). Open statements O1-O5 (section 9).
- rows: (DI) proved for p = 3; working on the induction to p = 4, 5.

## UPDATE 7
- Newly checked upstream (shared checkout updated): Outside/L_gct_215.lean — a bound on the dimension of 4x5 level
  spaces (read its statement and proof technique: it concerns exactly the L' of rows' defect normal form), and
  Outside/L_gct_214.lean (4x4 level spaces have dim <= 6).
- stage2 round 2: Theorem GEN-2 (no triangular minimal pairs in the fully generic regime). stage3 round 2:
  Theorem N3' (lineality of perm_3 <= 3), MIN-A/B/C, configuration (II); round 3: (II) excluded under (NZ).
- verify2 has re-derived N3', N3'-L, R0, ZBF, ThB, LC, ThA with no error found so far.

## UPDATE 8 (17:40) — where everything now funnels
- THEOREM GEN is VERIFIED (NOTES-verify2.md, RESULT ROUND 2: full dependency list): no 9-dim level space has all
  a_r = b_c = 1 with zero-free row and column annihilators. Also verified: Theorem N1 (all a_r = 1, all lam = 3 =>
  single-row element), Lemma N2-GEN, R3-1 (exact), Lemma EQ, Theorem TC5 (no (5,1) space with defect line e_a - e_b).
- Lean (compiling): lean/zbf/Zbf.lean (R0, ZBF, UFD replacement, ThB, Lemma C general n, mixed coefficients);
  lean/fl/FL.lean (Theorem FL up to three remaining case lemmas HypS6-S8).
- THE CENTRAL OPEN STATEMENT is the defect problem: (DI_5) "a 4x5 level space L' has dim L' <= dim C(L') + 3".
  Since subspaces have smaller-or-equal defect and Lemma SL excludes (4,0), it suffices to exclude the pairs
  (dim, defect) = (5,1), (6,2), (7,3) ((8,4) is excluded by the checked upstream bound 4x5 level <= 7, L_gct_215).
  Known: (5,1) with two-column defect line is impossible (TC5). All 22 other known (4,1) spaces are "split"
  (contain e_i m^T). stage3 round 4: family N2 reduces (given the unproved (N2-unit)) to a transposed (5,1)/(6,1)
  space with an explicit defect line eta (NOTES-stage3.md sections 18-20).
- Still open besides (DI_5): (N2-unit); (S3) single-row element with z_r <= 2 when all a_r = 1; rows/columns with
  a_r >= 2 (Type I'); annihilators with zero entries (stage2 round 4 in progress); conjecture (D).
- New upstream (constructions/gluing only): Outside/L_gct_204 (block gluing, general), L_gct_206 (4x6 dim 7),
  L_gct_207 (5x7 dim 9).

## UPDATE 9 (20:20) — exact engines here, second machine, guard rules

* **Gröbner engines in this container:** `/home/claude/tools/gb/msolve` (0.x, `msolve -g 2 -f in.ms -o out` gives a reduced
  DRL basis mod p; input format: line 1 variables, line 2 characteristic, then polynomials separated by commas) and
  `/home/claude/tools/gb/Singular` (`Singular -q < script`; has `sat`, `std`, number fields via minpoly). Tested: the local
  session's VF-A run is reproduced here (unit ideal; calibration 83 elements) in 0.02 s. BUDGET: runs of seconds; at most
  ~2 CPU-minutes per run and ~10 per round; anything larger goes into your COMPUTE-<role>.md for the 24-core machine.
  A generator in the style of `/home/claude/coord/local/results/VF-A/gen.py` (pure Python modular polynomial arithmetic →
  msolve input) is the template. Rules (errata A4): unit mod p is evidence — repeat at ≥ 3 primes, on coordinate charts
  (not one generic affine normalisation), with a calibration that must come out non-unit; mark results [modular] or [exact].
* **Second machine (24 cores, msolve + Singular):** runs the tasks of `/home/claude/coord/cloud/REQUESTS.md`; its results
  appear under `/home/claude/coord/local/results/` (read-only for you). So far: VF-A unit ideal for the four isotropic planes
  (4 primes); VF-B calibration passed; C1 calibration (4,1) 183/500, (5,1)/(6,2)/(7,3) searches running.
* **Spec errata:** `COMPUTE-ERRATA.md` (verify2). No 8-dim level space is known. (S6′) is false; the target is (S6-FO2).
* **Lean guard rules:** helpers under namespace `PEqualNP.Outside.L_gct_210_aux`; no line beginning with `add_`.
  Kevin: keep formalizing everything, ignore the 512 KiB cap for now.
* **New verified / proved today (see the NOTES files):** (FO-r) (stage2 R7); dim L ≤ dim L_r + dim Ω(L_r) − 1 and family M*
  (reg2); NCOL-P3, P51, Theorem DC (rows R5); SL3-RED, Lemma NP, Props I-ALL / II-ALL, (SL_m) ⟺ [DC3], [T22], [T31]
  (verifyfl R5); Theorem Z22 and z = (1,0,0,0,0) except F4b (stage3 §26).

## UPDATE 10 (20:36) — when a modular verdict IS a proof (verify2)

If the system is HOMOGENEOUS (its solution set is a projective variety: unknowns up to a common scalar, no affine
normalisation) and has coefficients in the ring of integers of the number field localised away from finitely many primes,
then "no projective solution mod one good prime P" PROVES "no solution in characteristic 0": a point over Q-bar would
reduce to a point mod P (projective schemes are proper). So formulate emptiness claims projectively (all coordinate charts
x_i = 1, or: the homogeneous Gröbner basis contains a power of every variable) and say which primes are bad (those dividing
denominators or where the constants i, sqrt 3, omega, ... do not exist or collide). Then the label is [exact], not [modular].
Affine or saturated systems (after `sat`, Rabinowitsch) do not have this property automatically — say explicitly which is used.
First instance: verifyfl's request A is now a THEOREM (three independent derivations, NOTES-verify2.md STATUS 20:25):
no principal (5,1) space for m = (1, omega, omega^2, 0, 0); with PR3: none for any 3-support m.

UPDATE 11 (2026-11-23 19:45 UTC, coordinator = local session): the team moved to Kevin's 24-core machine. Workspace
/home/kevxhk/work/L-gct-210 (paths rewritten from /home/claude/work/...). READ TEAM-RULES.md (machine, engines, compute budget,
Lean slot, file and rigour rules). Running jobs: /home/kevxhk/work/RUNS.md; ask for big jobs via /home/kevxhk/work/QUEUE.md.
Today's settled items: VF-A is a THEOREM (no principal (5,1) for |supp m| = 3); R6-1 claim (A) is FALSE (rows/sle5_s1005.npy), so
R6-1 now runs cases B and C (A4, B3, A as calibrations); "(SL_m) <=> [DC3],[T22],[T31]" holds only <=; rows Theorem DC: inequality only.

UPDATE 12 (2026-11-23 21:30 UTC, coordinator): MEMORY IS THE HARD LIMIT. The Windows host has 15.7 GB, WSL already gets 12 GB
(+8 GB swap); swap filled completely at 21:21. Rules from now on: (1) your OWN jobs: at most ONE job above 0.5 GB at a time, cap
2 GB each (ulimit -v 2000000), plus small ones; everything bigger goes through /home/kevxhk/work/QUEUE.md with RAM stated; (2) Lean
compiles run in DEDICATED WINDOWS (first ~22:30 UTC): during a window no new big jobs start and long-timeout jobs are paused;
(3) big-memory Groebner jobs (7-8 GB) run one at a time in the shared big-memory slot (/home/kevxhk/work/tools/bigslot.sh).
Verified since UPDATE 11 (verify2): Props I-ALL/II-ALL, SP8, Z22 + Lemma DEG, FC, F4b-X, DC3 (char 0, three m), X5, PR5, T3/Lemma O3,
R7.2, (T2) (S3 dead by a symbolic certificate), Lemma N1. Principal (5,1) now needs only (PL) (R8-Ksign running).

## UPDATE 13 (2026-11-24 00:12 UTC, coordinator): QUEUE.md repaired
QUEUE.md had grown to 17 MB: every line's text was duplicated in place up to 2048 times (the last doubling was between about 22:24
and 22:45 UTC; lines added after that are clean). It is now de-duplicated (41 KB, all entries and status notes kept; backup of the
corrupted file in the coordinator's scratch directory). RULE: add queue lines ONLY by appending (`echo '...' >> /home/kevxhk/work/QUEUE.md`
or a Python open(..., 'a')). Never rewrite the file; only the coordinator edits existing lines.

## UPDATE 14 (2026-11-24 01:05 UTC, coordinator): stale msolve output = possible FALSE UNIT (COMPUTE-ERRATA E-STALE-OUTPUT)
If a driver reads an msolve output file that it did not delete first, a crashed msolve (allocation failure; no output written) leaves
the PREVIOUS file in place and the driver reads an old Groebner basis -- e.g. the previous chart's [1]. RULE for every driver:
  1. delete the output file before each msolve call (or use a fresh name per system),
  2. check msolve's exit code and that the output is newer than the input,
  3. count a missing/old output as FAILED, never as a verdict.
A heuristic grep flags 17 scripts (stage2 9, verifyfl 4, verify2 2, reg2 1, ncol 1), incl. verifyfl/r7/subcut.py msolve() (reads fn.gb
without removing it or checking the return code). Patch your own drivers now (new files, never edit a running script in place) and tell
the coordinator if any recorded verdict could have come from a crashed call.

## UPDATE 15 (2026-11-24 01:32 UTC, coordinator): two process pitfalls
- Do NOT pause (SIGSTOP) a job that runs under a wall-clock limit (the timeout utility or a Python subprocess timeout): the clock keeps
  running while it is stopped, so it is killed as TIMEOUT on resume (rows R13: a "halted" chart was exactly this).
- Never kill processes by command-line pattern matching: the pattern also matches your own shell's command line and kills it. Kill by PID.
- Upstream PEqualNP.Defs gained six modules (f3e69b7, additive only); the coordinator rebuilds them before the next Lean window. No change
  to any definition we use.

## UPDATE 16 (2026-11-24 03:35 UTC, coordinator): STAGED CHART REFINEMENT (ncol R6; verify2 auditing) -- use it on your 2 GB segfaults
When a Pluecker/Grassmann chart system segfaults at 2 GB: for a chart S, ADD p_T = 0 for every chart T whose symmetry orbit is ALREADY
verified empty (a single exchange gives one chart coordinate = 0; a double exchange a 2x2 minor). These are CLOSED conditions, so RED-p
still applies; it is sound by induction (each stage uses only charts verified in earlier stages). ncol turned 35 segfaulting charts into
sub-second UNITs this way. Code and how-to: ncol/r32/refine.py, stage.sh, stage411.sh; handover/HANDOVER-ncol.md round-6 section.

16a. (coordinator 05:45, from verifyfl R16) CAVEAT to item 16: staged refinement adds p_X = 0 only if the decided chart X is OPEN
    (X = {p_X != 0}). If X is a decided CLOSED cell (e.g. {r_3 != 0, s_2 prop. to b_2}), its emptiness gives only the open condition
    "not in X" (a Rabinowitsch factor), not a closed equation. Use open charts as seeds; otherwise split off special closed fibres
    (e.g. e_3 = 0, e_4 = 0) and run the generic piece with a Rabinowitsch factor.

17. (coordinator 06:27, from verifyfl R17.4) JUNK-BRANCH REMOVAL. If a system's equations only force a PRODUCT of linear forms to vanish
    (e.g. quartic permanent equations giving lambda_0 lambda_1 lambda_2 * y = 0), the solution set keeps whole "junk" components
    (a column vanishing, etc.) that belong to pieces ALREADY decided elsewhere. They bloat every Groebner basis. Split by charts on the
    linear forms (per factor: lambda_k(Z_1) != 0, or lambda_k(Z_1) = 0 and lambda_k(Z_2) != 0) so each word excludes the junk via a
    Rabinowitsch factor, and record that the excluded branches are exactly decided pieces. verifyfl: piece IV of A case 0 went from
    10 GB out-of-memory to UNIT in seconds at 550 MB. Check your hard systems for factored equations before asking for the big slot.

18. (coordinator 07:27) MEMORY DURING LEAN COMPILES. Big-slot Lean compiles peak at 7.5-8 GB. 9 helpers x 0.5 GB on top of that is
    more than the 12 GB host has. While an "EXTRA LEAN..." job runs in the big slot (see runs/bigq3_driver.log), run at most ONE pool job
    per helper, and cap the WHOLE process tree (python drivers too, not only msolve/Singular children). At 07:25 swap hit 100% and the
    coordinator had to kill two pool jobs to save FLq2.
