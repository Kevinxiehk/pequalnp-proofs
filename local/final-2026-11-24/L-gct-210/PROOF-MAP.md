# PROOF-MAP: L-gct-210 (every 5x5 level space L, i.e. perm(J+t) = 120 on L, has dim L <= 8)
Maintained by verify2, updated at the end of each round. Last update: round 25 (FINAL, work aborted), 2026-11-24 08:04 UTC.

Status key:
- **V-rN**: verified by verify2 in round N.
- **CL**: claimed by the author, not yet verified by verify2.
- **OPEN**: not solved.
- **RUN(job)**: a computation is running.
- **NUM**: numerical evidence only.

Basis key:
- **c0**: characteristic-0 proof (hand, or exact over Q / Q(i)).
- **P1**: mod-p computation at P1 = 2147483629. It is a proof only once the whole case split is done at P1 (Lemma RED-p).
- **Lean**: compiled in Lean.

Branch structure: handoff/HANDOFF.md section 1 ("Blocked (four open branches)"). The case split itself is CL as recorded there; I verified the ingredients.

## REMAINING-WORK TABLE (critical path to a complete proof; round 25 (FINAL, work aborted), 2026-11-24 08:04 UTC)
Sizes: S = hours, M = about a day, L = needs a new idea or several days.
**Bold** = blocks a whole branch. Big-slot job ids are in /home/kevxhk/work/runs/bigq_extra.txt.

| # | Open item | Size | Waits on | Depends on / notes |
|---|---|---|---|---|
| 1a | SL_p as a Lean theorem (FLK_field over a field K) | S-M | leanfl: fix finrank_sumZero syntax + numeral normalisation (TrK0p rerun); then a Lean window | Needed by R11.6. Hand alternative: char-p reading of FLk (strong evidence already) |
| 1b | TC5_p: the port of TC5 to Kf (TrK11); else hand DI5.3 | S | leanfl port window | **TC5 over C is LEAN-COMPLETE** (V-r24): FLq2 (lean/fl/FLq2.lean, 16,660 lines, 0 'sorry' tokens) gives exit 0, 0 errors, 0 sorry warnings, 1418 s, 8.95 GB. `#print axioms` for TC5_final and L_gct_210 is [propext, Classical.choice, Quot.sound]. TC5_final: DefLine K mTC => finrank K <= 4, with DefLine = (P4 a (J+Y))_a in 24*1 + C m and mTC = e0 - e1, i.e. exactly TC5. Needed by R11.6 only as TC5_p |
| 1c | ~~[DC3] A0-ne at P1~~ DONE (V-r24: UNIT at P1, full system re-run) | - | - | SYM-M [DC3] for \|supp m\| <= 3 is complete at P1 (R11.6 form) |
| 1d | **[T22] chart A, cases 21, 18, 11..0 at P1** | M | verifyfl pool sweeps + VFBATCH_P1_A0; A case 0: t0c-ne and 4 P1a ab:ab:ab items left | Junk removal (lambda / mu) verified V-r22/r23 |
| 1e | [T31] split B with symbolic m | S-M | big slot VFB0SYM_A | Split A is complete |
| 2 | **(5,1) for \|supp m\| = 4, 5, non-split (includes m0 for PFC)** | L | verifyfl gen_sym_dc s = 4, 5 (pilot 7/16 at 60 s); m0 alone: [DC3] 6 cells + [T22] 5 cells (big slot) | Split (5,1) is CLOSED for every m (V-r20). Needs a cover strategy that fits |
| 3 | (PL) on 5 columns, via (SM5) | M | rank 3 only: rows R19W5P (big slot), then W5Q over Q(i). Rank <= 2 (R21.5): hand parts V-r24; rows over Q have \|S1\| = 2, 3 UNIT, and \|S1\| = 4 is split into (3,1), (2,2) UNIT with (2,1,1) running; my own Q(i) runs (\|S1\| = 2 UNIT, 3, 4 running) | R17.5 reduction V-r22. (SM4) is FALSE (V-r24). Any (SM5) counterexample has rank 3 once rank 2 is closed over Q. REAL trick (x_2 -> i x_2) V-r24: UNIT over Q <=> UNIT over Q(i) |
| 4 | Leaf 3: (2,1) kernels on 4-5 columns | M | P2-z3 (REAL over Q, rows' pool) + [(SM5) in rank 3 (SMC5 P, then REAL Q), or R4 + R5 + P2-A (REAL Q jobs queued)] | BY HAND in char 0 (V-r24/r25): support-4 case G (R21.8), which also covers G4-z5; and G4-A (R21.9-R21.9''''). For G4-A: identities exact on random instances, l = 0 => M-orthogonal coordinate pairs, case (b) => kappa(u) = 0 => vertex => B^u has a triple root, against 4 distinct points; case (a) certificates re-run 4/4 UNIT over Q. R15GQ and R15G4P/Q are dropped. The W5/SP5 relaxations are not unit (rows R21.12), so they were dropped. Everything else in leaf 3 is closed |
| 5 | **(6,2) and (7,3)** | L | ncol: K' classification (NCOLK3CLASS, big slot), K0 is FALSE (V-r24), so: the r_a = 2 Pluecker charts of the restricted zero-free e = 1 K_0 classification (NCOLK0Q). The (1,1) sub-case is COMPLETE (V-r25: hand split checked, 32/32 Case-C systems re-run) and all its members are excluded (V-r24); type b23, case (C) dim-2 sub-case, configurations (c), (d), (SR3) or (CCN), CC3-e2 (PROD-NCOL) | R211-3, L6G, K'-KILL are verified but conditional on the K' classification. H-a3-SL and H-b22-SL are verified |
| 6 | **(S3-a) = z (2,0,0,0,0)** | L | stage3: (PR3') strata (I) and (II) (equal-t case A: \|S\| = 3, \|F\| = 0 excluded exactly; \|F\| >= 1 and \|S\| = 4, 5 open); the (t2) extension; ST3TWOCOLQ over Q (big slot) | (M3) is false; (t2) has no route yet |
| 7 | Other z patterns: (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0), mixed, multi-row (sum z <= 4 by L_gct_111) | M-L | stage3 hand work. (1,1,1,1,0): exact t-parametric pair tests over the whole configuration varieties (the generic exclusion and the completeness of the special list are still NUMERICAL) | (1,1,1,1,0), V-r25: every KNOWN special member is closed modulo PFC/(SL_m0). Family B is EXCLUDED (pair (2,3) UNIT for all t; my re-run of the 13 hinge-free charts and the 13 t = -1/2 charts gives 26/26). k_N = 2 reduces to M0, M1. M0 is excluded (orthogonality; sigma_3 coefficient <m, mbar> = 3, span_M0 re-run). M1 forces a free column, so PFC applies (span_M1 re-run, level) |
| 8 | O1: a uniform z_i = 3 exclusion | M | stage2 hand work | Every explicit survivor is killed |
| 9a | ~~F2col (both rulings)~~ **CLOSED (V-r25)** | - | - | Structure, lemmas and every symmetry cut VERIFIED (own code). RD certificates re-run exactly. Row 6 Kt3: my re-run 4 x 20/20. Rows 13/15/16/17: RED-p logs in stage2/r21/redp_logs.log, checked. Row 15 at nu = 0 is also killed exactly (my check: B_c rank 5, K dim 3, det q0|K = 84). J_A^R1: my own rank-2-split + recursive-bound check kills at 3 random points (stage2's failure sets + cut are logged in r21/, not re-implemented by me) |
| 9b | B(dep) eliminations in char 0 (the R12-1 eliminations are mod p) | S-M | stage2 / pool | **D04-PROP CLOSED in char 0** (V-r25). The generic sigma dies by the recursive kernel bound: my own code at 4 rational sigma. Every exceptional sigma (-2/3, -1, the roots of 3sg^2+3sg+1 over Q(sqrt -3), and sg = 0 with its own setup) is killed at the point by my own exact search. The B(dep) points P0_B_i A/B die exactly (generic combination rank 7 on the 7-dim complement, so isotropic dim <= 3 < 4; my re-check). D003-PROP Case A is CLOSED (V-r22) |
| 10 | **(S6-FO2) in general** | L | reg2: a proof of (BL); R3 cases (I), (alpha), general (II); e <= 5 types (stage-2 rank-drop loci, 74 timeouts); spanning-set deformation families; N/R1 families | e = 6 is complete; stage-1 kills are verified |
| 11 | Lean assembly of the whole proof | L | leanzbf: 95 t3p_* lemmas + full R7c (R14t_shape: 7 errors, R17lint: 2 errors, both stub tests); R31Hyp (over the size cap); leanfl: the Kf port; nothing yet for branches 2-4 | Not needed for the mathematics. Lean-complete: SL/FL (FLk), TC5 over C (FLq2, V-r24), and the round-3 statement. RED-p in Lean: the Tcert prototype (V-r25) matches our lemma at chart level; the projective gluing over a whole Pluecker cover is still to be written |
| 12 | Upstream (8,4) = L_gct_215 | external | outside this lemma | Used for (DI_5) at e = 4 |

Honest summary (final, 08:04 UTC, work ABORTED by Kevin): items 2, 5, 6, 7 and 10 need new mathematics (L). Items 1, 3, 4 and 9b are computation in flight (S-M). CLOSED this session: F2col (9a), D04-PROP char 0 (9b), leaf-3 case G and G4-A, TC5 over C in Lean (1b), [DC3] A0-ne (1c). FALSE and withdrawn: (SM4), CONJECTURE K0. On the computational items, nothing is known to be false.

## UPSTREAM SHORTCUTS (round 24 survey, 2026-11-24; verify2)
Source: the on-disk upstream checkout /home/kevxhk/code/pequalnp-proofs-2/lean/PEqualNP/{Outside,Gct} (main, 67126d1). I read the files and ran no git: my rules forbid it, so files newer than that checkout are not covered. All files below have 0 sorry. The statements are exact paraphrases. "Level" = all k x k sub-permanent sums vanish (sigma_1..sigma_min), i.e. perm(J+t) is constant.
**Verdict: no upstream lemma closes an open leaf (items 2-10), and none contradicts a verified step.** Partial uses:
| Lemma | Exact statement | Effect on our items |
|---|---|---|
| L_gct_215 | 4x5 level => dim <= 7 | Already used: (8,4), so (DI_5) at e = 4. It gives NOTHING for (5,1), (6,2), (7,3), because d = 7 is allowed. Extras: in branch 4, dim L_r = 4 + a_r <= 7, so a_r <= 3; every 4x5 level subspace has dim <= 7. Note: for the deletable-row lift (dim L <= d + 4 - e), dim 9 needs only "no (6,1), no (7,2)" (SL + 215 remove the rest). These are weaker than no (5,1) / (6,2), but PFC consumes (5,1)_{m0} itself, so the sharp form stays needed. |
| L_gct_214 | 4x4 level => dim <= 6 | Already used (ncol N1.2/N1.3: e^col = 3 and the bound in configuration (d)). |
| L_gct_217 | 4x4 level with all row sums 0 => dim <= 5 (sharp: L_gct_197 is 5-dim) | NEW constraint, no kill. The row-sum vector r(q) is the degree-1 part of M(q) - 24*1 (times -6), so dim Q <= 5 + e^col(Q), and by transpose dim Q <= 5 + e^row(Q). In (d) (dim Q = 6), both the row-sum map and the column-sum map are nonzero. |
| L_gct_216 | 4x4 level with all row and column sums 0 => dim <= 3 | NEW constraint, no kill: dim Q <= 3 + rank(q -> (r(q), c(q))) <= 3 + e^row + e^col. ncol's (c) and (d) need dim Q > e^row + e^col, hence a NONZERO doubly-centred level part Q_00 (dim 1-3). Killing Q_00 in (c)/(d) would close them. |
| L_gct_111 / 123 | n x n, rows (columns) in subspaces V_i (S_j) with perm(J+t) = n! => sum dim <= n-1 | Single-row parts: sum z_r <= 4 (likewise for columns). This is a second proof of the V-r15 kills (1,1,1,1,1), (2,1,1,1,1), (2,1,1,1,0), and it shows the open z-list (item 7) is complete up to sum z <= 4: every multi-row z with sum >= 5 is dead without analysis. |
| L_gct_114 | row part + column part: sum dim V_i + sum dim S_j <= 2n-2 = 8 | Mixed single-row + single-column parts total <= 8. Weak (FL already caps a full free line). |
| L_gct_202 | 4 x q (q >= 4) level matrix with a constant row c => c = 0 | No current leaf. Usable as a normalisation lemma. |
| L_gct_204 / 205 | 204: block-diagonal gluing of level-type spaces is level. 205: J is not in L + Z for L level and Z perm-zero | Constructions / R0-type facts. No leaf. Consistent with the bound 8: every 5x5 gluing gives at most 7 (blocks 4x5 + 1x0 <= 7 by 215, 4x4 + 1x1 <= 6, 3x5 + 2x0 <= 6 by L156). |
| L_gct_142 / 151 / 153 | 142: e_2j(w) = 0 for all j => dim <= 1. 151: a support-minimal y with sum y != 0 spans every element supported in supp y. 153: a 2-row isotropy bound | No leaf. |
| L_gct_152 | B nondegenerate symmetric, B(v,v) != 0, A totally isotropic inside v-perp => 2 dim A + 1 <= dim V | The abstract core of stage2's kernel kill / big-kernel / general kernel bound. It is ready to copy for a Lean version of the F2col kills (item 11). Mathematically standard, so no new leaf. |
| L_gct_109; Gct L094 | 3x3 doubly-centred level => dim <= 1; 3x3 level => dim <= 3 | Already in the base (N3'). |
| Gct L156 / L157 | 3 x q level => dim <= q+1; 3 x q row-centred level => dim <= q-1 | Row pairs: lam_rr' = dim(L cap {rows r, r' = 0}) <= 6 (row-centred: <= 4). Lemma C gives lam >= 2, so no leaf closes. |
| L_gct_189 / 180 / 206-208 | existence: a 7-dim 5x5 level space; a 6-dim row-centred 4x5 level space; 4x6, 5x7 constructions | Lower bounds only, consistent with dim <= 8. |
| L_gct_226 | no 4-dim 3x3 level space over ZMod 5 | Irrelevant (our primes are large). |
NOT upstream: the n = 4 bound "4x4 level <= 5" (L-gct-091), which would kill ncol configuration (d) outright. No theorem in Outside or Gct states it, and its helpers Gct/Helpers/LS4 are not a theorem.

## WHAT IS LEFT FOR A COMPLETE PROOF (round 17; owner, size S/M/L, kind)
Sizes: S = hours, M = a day of team work, L = new idea or multi-day. Kinds: C = compute, H = hand proof, Lean = formalisation.
1. **(5,1) with |supp m| <= 3, by the R11.6 route** (Branch 1.1). R11.6 itself is V-r16 as logic.
   - 1a. SL_p and TC5_p. Owner leanfl, then verify2. S-M. Lean.
     - SL_p: lean/fl/FLK_field.lean (8006 lines, all of FLk over Kf). Static audit V-r18: its hypotheses are exactly NeZero 2, 3, 5, |K| > 20 and sqrt(-1) in K, all true at P1. NOT YET COMPILED. Window 3 smoke test TrK0: one syntax error (finrank_sumZero named argument), which recurs at 7 places in FLK_field and 5 in TrK11. Both compiles were stopped and are waiting for a dedicated window (V-r19).
     - TC5_p: leanfl/TrK11.lean holds the TC5 blocks over Kf with the same hypotheses (static audit V-r18). The assembled TC5 is missing: (c1), (c2-iii), the placement transports and the dispatcher, even over C. So TC5_p = the Lean blocks (once compiled) + the hand proof DI5.3 for those branches.
   - 1b. [DC3] A0-ne at P1: DONE (V-r24; SYMDC3V2_A0 UNIT, full system re-run). SYM-M [DC3] is complete at P1. (B0-ne is not needed: chart B is redundant, V-r21.)
   - 1c. [T22] at P1: chart A cases 21, 18, 11..0, each with a Rabinowitsch test if non-unit. Chart B is NOT needed under R11.6 (V-r21: its only extra point (0,1,-1) is two-column, so TC5_p covers it). Owner verifyfl. M. C (big slot).
     - A case 0, piece IV, items t0c-01/02/12: DECIDED at the N level by the lambda-word cover (verifyfl R17.4; audited V-r22, 24/24 words re-run). The 10 GB rc4 jobs are not needed for them.
     - Still open in A case 0: t0c-ne and the open P1a/P1b/P2 items. The 'mu' junk removal (R17.5) for the P-items is logic-checked (V-r23): induction on the number of '0' columns. Running (201 items).
   - 1d. [T31] split B with symbolic m: build it, then run at P1. Owner verifyfl. S-M. C.
   - 1e. The 'resume'-manifest check (verdict-line reuse in gen_dc / gen_sym_dc). Owner verifyfl. S. C.
2. **(5,1) with |supp m| = 4, 5, NON-split** (includes m0 for PFC; every SPLIT (5,1) is now excluded, V-r20): the R11.6 route with gen_sym_dc on s = 4, 5, plus [T22]/[T31] analogues. For m0 alone, [DC3] has 6 hard cells and [T22] 5 cells left (big slot). Owner verifyfl. L. C (+H for the cover).
3. **(PL) on 5 columns** (principal kernel, the summed cubic): over-Q runs, or a hand proof. Owner rows. M. C/H. NEW: (PL) <= (SM5) by R17.5 (verified V-r22); exact SM5 over Q(i) is queued.
4. **(2,1) kernels** (Branch 1.1):
   - 4a. The 16 special points: DONE, V-r17 (64/64 distinct charts unit at P1, Galois-covered; RED-p => c0).
   - 4b. Kernels on 4-5 columns. Owner rows. M. H+C.
     - The case trees are V-r18 and the plane test (R15.1) is V-r20.
     - Support 4: P2, P3, PP exact over Q(i); P4 by hand; G BY HAND, c0 (rows R21.8, V-r24).
       - The argument: P3 of each deletion is one triple. Its ka^3, ka^2, ka^1 coefficients force C_T = 0, B_kk = 0, A_k = K(c(s_k),u,u) = 0.
       - z -> K(c(z),u,u) is a nonzero binary quadratic, because grad kappa(u) != 0 for an isotropic u != 0. So it has <= 2 roots, against 4 distinct s_k.
       - My checks: I re-derived the coefficient identities by hand, they hold exactly on 5 random rational instances (verify2/r24/caseG_identity.py), and the quadratic K(c(z),u(s),u(s)) = 4i(2s^3 z^2 + (s^4-1) z - 2s) is never identically zero.
       - This also covers support-5 G4-z5 (the same plane). R15GQ / pgRFQ are not needed.
     - Support 5: P3, P4, PP, P5, S23 exact over Q(i) (P5 and S23 re-run V-r20); P2 mod P1 only (exact in progress); G4-A, R4, R5 in the big slot.
     - Mod-P1 units are not c0 here (open column conditions).
     - NEW ROUTE (rows R17.5 / lemma chain IS0-IS5, verified V-r22): (SM4) + (SM5) exclude every remaining case, since each has plane support >= 4. They also give (PL) and PL4 (item 3).
       - (SM4) IS FALSE (V-r24; rows' counterexample, verified exactly over Q(sqrt3, i)). Its columns lie in the coordinate plane x3 = 0, where kappa vanishes.
       - The reduction stands, but the 4-column cases need the case runs (R15GQ, R16P2z3) or a RESTRICTED (SM4) for the pencils that actually occur.
       - PL4 keeps its earlier proof.
       - (SM5) must be re-checked in rank <= 2.
       - (SM_n) means "no strongly level 4x5 matrix with nonzero isotropic row sum has exactly n nonzero columns".
       - The single chart is honest; the all-vertex configurations for (SM5) are exact (I re-ran smv.py: 120/120).
       - Char 0 needs the over-Q(i) runs (R17SMC4Q/SMC5Q, or R17SM4Q/SM5Q); the runs at P1 are triage. Lemma RS is V-r17: (i)-(iii) by hand, and (iv) symbolically as a system (sigma_3(Y_-k) = E_k/4 - S/12 modulo the degree-2 conditions). The k21sys exact system for support 4 is too heavy so far.
5. **(6,2) and (7,3)** (Branch 1.2): (N_2+), (N_3+), configurations (c) and (d), and case (C) of R2.4. Owner ncol. L. H.
   - V-r18:
     - THEOREM PT2 and E3P are c0.
     - THEOREM CC34 is c0: my own generator gives 6/6 orbit charts unit at P1 (RED-p), and chart 0123 is exact over Q.
     - The (PROD) reduction is verified. PROD-NCOL at P1 + PT2 gives CC3-e2 in c0, but not (PROD) itself.
   - (CC45) is refuted numerically (a column-centred (4,2) space; my fresh-point check agrees). So the shortcut "no (5,1)/(6,2) from column-centred 4-spaces" is dead.
   - THEOREM SN ("e <= 3 => same node" for product type), audited V-r19.
     - Its logic is sound: the lift needs only finiteness, completion to Z_p and generic length <= special length (no flatness). A random M is enough.
     - Mod-p counts: 01_01 = 24, 01_02 = 12, 01_23 = 0, all on target. => THEOREM SN holds in c0 (V-r19).
     - The multiplication-matrix cross-check is not available yet (incomplete data files).
   - THEOREM R211-3 (case (C) of R2.4, sub-case dim(U_i + U_i o w) = 3): V-r21 CONDITIONAL on the exact K' classification. The (L6) projective system is 27/27 unit (my re-run), and RED-p is valid with the lam = 0 closure included.
     - The K' census: 6 numerical hits of one rigid type; the 60 points are exact and reduced. The exact classification is still blocked (2 GB).
   - THEOREM L6G + COROLLARY K'-KILL (V-r21: all 39 charts re-run; length argument checked): every case-(C) configuration whose zero-row part of ker c is 3-dim is impossible. Conditional on the K' classification (big slot NCOL-K3CLASS).
     - Last piece of case (C): types a3, b22, b23 (rank c = 3, rho = 2).
       - THEOREMS H-a3-SL and H-b22-SL: VERIFIED for ALL strongly level K_0 (V-r23).
         - The gap I found (q(K_0) = 0 is not forced) is closed by ncol R10.5-R10.9.
         - The char-0 classification is complete: rigid pairs, plus F1 and F2 (the slq1/slq2 re-runs and the reflection count both check out).
         - The family systems have finite fibres over every parameter value (112/112 re-run; the criterion is correct).
       - **CONJECTURE K0 IS FALSE (V-r24, exact, my own code verify2/r24/k0_cex_mine.py).** The route "K0 + H-a3-SL => H-a3" (and the same for b22) is WITHDRAWN.
         - Counterexample (ncol R11.7): S = span((H nu1) a^T, (H nu2) (e0 - e1)^T), a = (-3,-3,7,14,-21). By direct permanent expansion over Q(omega): row 0 is zero, N(J4+Y) = 120 identically, e = 1, and the defect line is (49,49,-81,-36,19), with no zero.
         - The b22-shape member a = (1,1,-3,-3,6) checks the same way: line (-27,-27,33,33,-12), zero-free and rational.
         - H-a3-SL, H-b22-SL (and H-b23-SL) still stand. They are statements about strongly level K_0, and the counterexample has e = 1.
         - New route: a restricted classification of zero-free e = 1 K_0 with a3/b22-shape defect lines (NCOLK0Q, rewritten), plus the K_0-fixed systems per member (ncol R11.10); or the full H-system runs (NCOLHCONJA3T0, NCOLHB22T2/T0). All are queued.
         - ncol R11.9 (mod p, triage) already finds members outside the R11.7 family, so the restricted classification must be exact (over Q).
         - ncol R11.11-R11.13: the mod-32003 census of the (1,1) charts is explained by three member types: F (the family), S4 (exact over Q(i), m = (1,1,1,1,-4)) and N (a3 only, over Q(sqrt -15)).
           - Every member (15, with conjugates and swaps) is EXCLUDED by its K_0-fixed system: 330/330 UNIT mod 65521.
           - V-r24, the properness argument is sound: the system is closed in P^10 x P^1 (11 Y-charts, tp in A^1 plus the point at infinity), with no Rabinowitsch.
           - Each member is fixed over O_F, F = Q(omega, sqrt D). 65521 = 1 mod 12, and -15, -39 are squares mod 65521, so one prime of F above p is fixed by the choices of w and sqrt, the same in all 22 charts. Denominators are 2, 3, 4, 6, 8, 12.
           - My re-run at a SECOND prime, 1000081: 7 members x 22 charts, 154/154 UNIT. The calibration (rigid pair 01|23) again has its single non-unit chart.
           - Still OPEN: completeness of the zero-free a3/b22-shaped e = 1 list. The mod-p census is triage, since zero-freeness is an open condition. Needed: (1,1) over Q (ncol, local) and the r_a = 2 Pluecker charts (NCOLK0Q).
       - b23 is open.
   - Still open: (CCN) (column-centred (4,3) spaces have a neutral column; 4/4 numerical), (SR3), case (C) sub-case dim(U_i + U_i o w) = 2, and CC3-e2 (PROD-NCOL). (The R3.2 shape is closed by THEOREM R32.)
6. **(S3-a) = z (2,0,0,0,0)** (Branch 2). Owner stage3. M-L. H + exact C.
   - Types (t0) and (t1) need only (PR3') for strata (I) and (II). Stratum (II) reduces to "rank-drop locus = special locus"; stratum (I) has no approach yet.
   - Type (t2) needs one of:
     - (M3) "the (t2) core X0 = Y_ab + Y_cd is empty" is FALSE, in BOTH cases (numerical; both examples checked independently, V-r18/V-r19).
       - stage3's first X0 has dim c(P_a) = 1 and a column element.
       - The second X0 is in the main case and has NO column element (a column-block shape).
       - So "every (t2) structure carries a column element" fails at the X0 level.
     - The decisive (t2) question is now EXTENSION. stage3's (E) normal form (checked) gives L_e = Y_ab + Y_cd + C(0,g,0,h). Does some X0 extend by such a 2-row element to a level L_e with defect <= 2 and no single-row element? The numerical probe is running.
     - The column-element / transposition route can still hold for the stratum-(III) X_re themselves. stage3 has an exact formulation (ST3-TWOCOL, sec. 39).
       - RIGOUR (V-r19): "a second nonzero column" is an open condition. So P1 units give the column-element statement only over F_pbar.
       - In char 0 it needs either runs over Q, or a whole-cover argument at P1 for a closed final target.
     - (M1) + (M2): classify stratum (III) (stage3's family is an ansatz with p = e_0; that p is a coordinate vector is not shown), then a uniform FO2_0 <= 8 certificate on the family. The computation inside the ansatz is V-r17.
7. **The other z patterns** (Branch 2): (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0), the mixed (2,1,..) patterns, and multi-row patterns. Owner stage3. M. H.
   - For (1,1,1,1,0): "three m + w" is closed (the rigid member goes to PFC, V-r18), and generic members of the other configurations are excluded numerically.
   - The special members are NOT just the two known ones (stage3 sec. 42 (D), V-r22 noted): there is a 1-parameter k_N = 2 family (m = (1,w^2,w,0,0), block structure, no single free column, so PFC does not apply directly).
   - stage3 sec. 43 (V-r24 noted): special members also exist for (2,2) and (2,1,1), all of a 3+2 block type. A block analogue of PFC (neutral columns) is the proposed route; it is a conjecture so far.
8. **O1, a uniform z_i = 3 exclusion** (Branch 2/3). Owner stage2. M. H.
9. **Branch 3 leftovers.** Owner stage2 (plus the coordinator's pool).
   - D003-PROP Case A: CLOSED (V-r22).
   - D04-PROP parametric char 0. S-M. C.
   - B(dep) eliminations. S. C.
   - F2col full family. M. C+H.
     - Ruling R2: the exact kernel kill (V-r18) plus the stage2 R16/R17 tree and symmetry cuts (V-r20 as logic).
       - The 18 exceptional families are handled automatically.
       - The S_3 cut leaves finitely many nu-lines (ST2-R2LINES/R2SYMLINES pending) plus points.
       - The special Z is closed. T1cert over Q passed (not re-run).
     - Jump locus: CLOSED. Deg = empty, which I verified from the certificate polynomials; the S_4 cut and the fixed points are killed.
     - Ruling R1: same kernel kill, but its exact rank-drop locus is still pending (ST2-R1COF).
     - Cross-type ruling: CLOSED by stage2 R17 (kernel kill + S_4 cut + 4 RED-p members; logic as verified, members not re-run).
     - R2 nu-lines: 12/13 at proof grade per stage2.
       - The four 2-dim-kernel lines are done over Q(sqrt46) / Q(sqrt76); the minpoly approach covers both conjugate lines (V-r22). The zeros of g(nu) are to be checked.
       - (0,0,0) via KU is pending. msolve char 0 alone is evidence.
   - The uniform statement. L. H.
10. **(S6-FO2) in general** (Branch 4). Size L (V-r20).
    - Completeness (reg2 23.3, checked): given (BL), every combinatorial type (line pattern + genuine parts R1/C1, R2/C2, N, R3) must be solved exactly; deformation scans reach only components.
    - e = 6 is done. For e <= 5, an automatic type solver or cutting lemmas are needed (e = 5: 296 types).
    - ntype1 is closed with FO2 <= 8. reg2's "<= 7" came from a wrong q-rank (5 vs the true 4): COMPUTE-ERRATA [R].
    - (BL). Owner reg2. L. H.
    - R3: exclude (alpha), (I), (II). Case (II) is done only for two rational B; general B and cases (I), (alpha) are open. Owner reg2. M. C.
    - Hit-free / line-spanned patterns: ALL 29 SETTLED (V-r19; reductions checked, exact parts re-run). Every line-spanned 6-dim space satisfies (S6-FO2).
    - NEW, from reg2 21.4: the deformation-table gap. Certify the spanning-set deformation families and redo the double-deformation scan. Owner reg2. M. C.
    - e = 5 type solver (reg2 R17, audited V-r23).
      - The stage-1 "LINES-EMPTY" kills (452 classes) are exact over Q and valid necessary conditions; I spot-checked 0000|11111 independently.
      - Open: 74 stage-1 timeouts, and the stage-2 rank-drop subloci (the 366 LINEAR-GENERIC-KILL classes are a numerical measure only; they need the Fitting ideal).
    - Certify the N/R1 families (incl. the 19 rows spaces). Owner reg2. M. C.
11. **Lean** (optional for the mathematics, needed for "Lean-checked"):
    - T1: the proof of T3Rest2 / t1_proof compiled in full in R9d (window 3). Left: the 95 never-compiled t3p_* core lemmas and the full candidate R7c. Owner leanzbf. M. Lean.
    - R31Hyp: the per-configuration DFS is about 6 MB raw, over the 512 KiB per-file cap (Kevin: ignore the cap for now).
      - My data (V-r20) shows every killed configuration dies with at most 3 triples, so at most 336 certified triples are needed (about 453 now).
      - No uniform (E4) lemma was found.
    - FLn and Tr8full errors. Owner leanfl. S. Lean.
12. **Bookkeeping:**
    - A final check of the top-level case split (handoff sec. 1, still CL as a whole). Owner verify2. S. H.
      - Question raised and RESOLVED (V-r17). Old wording of (B): "all annihilators zero-free => GEN; the pair's annihilators have zeros => branch 3". This seemed to leave out a mixed case (a zero only in another row's or column's annihilator, which GEN-2/(S2*) need).
      - The case is covered: stage2's REG1 reduction (V-r5) sends EVERY minimal pair, whatever its annihilators, to (B1) = the (Q-r) program of branch 3. GEN is then only an extra proof for the fully generic case.
      - So the split is exhaustive. Branch 3 should read "a minimal pair (any annihilators)".
    - The upstream dependency (8,4) = L_gct_215 must be in place. External.

## 0. Base (used everywhere)
- **V-r1 (Lean).** R0, ZBF, Theorem B, Lemma C (lam >= 2), FK (a_r >= 1), Theorem A, N3. Source: chief secs 2-4, lean/zbf.
- **V (Lean, FLk compiled).** Lemma SL (strongly level 4x5 => dim <= 3) and Theorem FL (a full free line => dim <= 7). Source: lean/fl.
- **V-r4.** Tools FO / FO2: L lies in T_1(M), and L/X is isotropic for q_m. Source: stage2 R4-R5.
- **V-r9.** FO2-joint. Source: stage2 R10-4.
- **V-r10.** RED-p for closed systems. Source: verifyfl R7.1.
- **V-r7.** 8.1(a): FO2 bound <= dim T_1 - 1. Source: reg2.
- **Lean status after window 2 (V-r16; Lean prints "declaration uses `sorry`" with backticks):**
  - (a) Blocks compiled IN FULL somewhere (no sorry in their own body), with the stubbed lemmas each one depends on:
    - leanfl FLk: a full file (0 sorry; exit 0; axioms propext, Classical.choice, Quot.sound). Proves Lemma SL, FL row and FL col. Depends on nothing stubbed.
    - leanzbf R3e (round 3): a full file with standard axioms. Proves the round-3 statement.
    - leanzbf R6t_stub (stub test, 283 sorry): compiled in full: r4_* (T2, T2''), r5_*, r6_0, the 10 t1p_* core lemmas, r6_2, r6_3, the generated wrappers, r6_5, r6_6, and 3 sample t3p_* lemmas.
      - Depends on: the earlier lemmas, stubbed with identical statements (their proofs compiled in R3e/R4-R5 files).
      - Failed: the dispatch t1_IIi (4 heartbeat timeouts; repaired, not recompiled).
    - leanzbf R7s_t3 (stub test, 484 sorry): compiled in full: the dispatch t3_trans (305 leaves), and T3Rest2 => T3Rest => T1Rest3 => T1Hyp.
    - leanzbf R9d (stub test, window 3, V-r20): exit 0, 0 errors, 469 sorry.
      - Compiled in full: t1_proof : T1Hyp, t3f2_proof, lemB, the orientation bridges, the wrappers, and the repaired t1_IIi.
      - Stubbed there: the 98 t3p_* core lemmas, t3_trans and t1_of_t3rest2 (the last two compiled in R7s_t3).
      - => T1 is Lean-checked across stub files, except the 95 never-compiled t3p_* core lemmas.
    - leanzbf R12s_combo (stub test, window 3, V-r20): exit 1, 43 errors (mostly renamed Mathlib constants: Equiv.Perm.apply_inv_self/inv_apply_self, Polynomial.coeff), 371 sorry. The R31 setup pieces are among the failures, so R31 is not Lean-checked yet.
      - Depends on: all 98 core lemmas t3p_* (stubbed; 3 compiled in R6t_stub, 95 never compiled) and the earlier lemmas (stubbed).
  - (b) Full candidate files (must have 0 sorry):
    - leanfl FLn (10,568 lines), FLo (12,714), FLp (14,287) and FLq (15,610): 0 sorry each. FLn compiled with errors (exit 1).
      - FLq, window 3 (V-r19): exit 1, 19 errors, 0 sorry; the final theorem (SL + FL) depends only on the standard axioms. All 19 errors sit in 8 late TC5 declarations (TC5_P3, P4_k2_conf, chi_t12, cramer (a renamed Mathlib lemma), P4_c2_canon, sig23, c2iii_zeta, F1_w0). Everything before line 12330 elaborated.
      - leanfl Tr11 (7,411 lines): exit 1, 20 errors in the same declarations plus C2iiiLag_proof; 0 sorry.
      - FLq REBUILD (V-r21): 7 errors, all heartbeat timeouts, in P4_c2_canon, F1_vprod and noline; 0 sorry; L_gct_210's axioms are standard.
        - TC5_final (the exact TC5 statement over C) DEPENDS on all three, so TC5 is still not Lean-proved. The fix is heartbeats only.
      - FLq2 (V-r24): exit 0, 0 errors, 0 sorry, standard axioms for TC5_final and L_gct_210. TC5 over C is Lean-proved. Only the port to Kf (TC5_p, TrK11) is left.
    - leanfl FLK_FL (FL over Kf): 1 error, in propR. TrK0p (port profile): 42 unsolved linear_combination goals with numeral denominators over Kf. The port needs numeral-normalisation fixes.
    - leanzbf R14s_shape: stopped at 100 Decidable-synthesis errors in f13_cases_00012 (mechanical). R9f (window 4) is pending.
    - leanfl FLK_field and TrK11 (the field port): stopped in window 3 (would exceed the timeout). The smoke test TrK0 had 2 errors from one syntax slip, which recurs at 7 + 5 places; it waits for a dedicated window.
    - leanfl Tr8full: 0 sorry; compiled with errors (exit 1).
    - leanzbf R7c (38,080 lines): 0 sorry; final theorem = old statement /\ T2Hyp /\ T2ppHyp /\ T1Hyp; NOT yet compiled (window 3; over the guard's size cap).
  - Honest count: the only full files that have compiled are FLk (SL, FL) and R3e. T2, T2'' and the t3_trans dispatch are checked only inside stub files. T1 (T3Rest2 and the 95 core lemmas) is not Lean-checked yet.
  - Statements matched to the paper (V-r12..r15): T1Hyp, TC5_P3, X5_mc (3-column hypothesis), LAG_a, LAG_b, NB, TC5_P1.

## 1. Case split for a hypothetical 9-dim L
Here a_r = 5 - dim pi_r(L), and lam is the dimension of a row pair's intersection.
- **(A)** Some a_r >= 2 or b_c >= 2: branch 4.
- **(B)** All a_r = b_c = 1, and some row or column pair is minimal (lam = 2):
  - if all FK annihilators are zero-free: THEOREM GEN, V-r2 c0;
  - otherwise: branch 3. Every minimal pair, whatever its annihilators, goes to the (Q-r) program (REG1 reduction (B1), V-r5). Checked V-r17.
- **(C)** All a_r = 1 and no minimal pair (all lam >= 3): THEOREM N (V-r2/r3 c0) gives a single-row element; then branch 2.
- Branches 2-4 reach 4x5 questions through the defect lift (Lemma S3-2 landing pairs, PFC, FL). Branch 1 is the 4x5 defect inequality.

## Branch 1: defect inequality (DI_5), d <= e + 3 for 4x5 level spaces
Excluding (5,1), (6,2), (7,3) suffices: (4,0) is Lemma SL; (8,4) is upstream L_gct_215.

**1.1 (5,1)**, defect line C m.
- **|supp m| = 2:** THEOREM TC5, V-r2 c0.
- **Principal kernel K** (strongly level, s(K) = V):
  - PR5 + T3 + PL4 (4 columns): V-r8/r10 c0.
  - (PL) on 5 columns, via the summed cubic (R9.3 V-r11; 7 equations): RUN(R9-SUMQ5, big slot), evidence only mod p. Needs over-Q runs (big slot).
  - |supp m| = 3: VF-A + PR3, V-r5/r6 c0.
- **Kernel strata, non-principal** (rows):
  - (1,2): CHI1, CHI2, EXT-I/II and the pencil principle, V-r9/r12 c0.
  - Column-centred case R11.2: logic V-r12; exact parts re-run V-r13 (K_II forces a two-column m, so TC5; chi (x) C^M unit).
  - (0,3): impossible (Lemma SL).
  - (5,1) criterion R12.5 (V-r14): no column-centred (4,1) extension of K implies no (5,1) space contains K.
  - Three-column (2,1) kernels:
    - Lemma 3COL (some column has rank 1): V-r14.
    - Classification into A1, A2 and family B: V-r14 (R12.3/R12.4 re-derived structurally).
    - A1, A2 excluded over Q (R12.6): V-r14, re-run with a valid gauge (det 2).
    - Family B: RUN.
  - (2,1): two-column generic case (Pi = V) by hand: R11.1, R11.4-R11.7 V-r13 c0 (NCOL_1; no (5,1) of rank c = 1 when m_a or m_b != 0; column-centred case excluded). Uses R10.7's kernel normal form (CL). Special kernels (Pi strictly inside V: the line d = u plus finitely many points, R11.9 in progress), m_a = m_b = 0 (handed to verifyfl), and three-column (2,1): OPEN.
- **Typed systems (SL_m)**, which imply no (5,1) for this m. The implication is one-way (only <=). Per sample m:
  - **m12m3, m11m2, iso** (|supp| 3, non-principal):
    - [DC3] THEOREM V-r7 c0.
    - [T22]: m12m3 cases 95..8 unit at P1 CL; open rank-2 cases 0, 1, 4, 5. m11m2 and iso 86-88/96. Hard cases RUN(VF-T22H, big slot).
    - [T31]: split A theorem V-r10 (RED-p label fixed); B0 at P1 CL (verifyfl R9 L1); B1 OPEN (big slot).
  - **m0 = (1,1,1,1,-4)** (needed by stage3 PFC, V-r9):
    - **[T31] for m0: COMPLETE at P1 (V-r13)**, made of: split B by hand (V-r10); (beta) 32/32; (alpha) entirely (lines below).
    - (beta): 32/32 at P1 (audit V-r11).
    - (alpha0): V-r11/r12, c0 and P1.
    - (alpha1): supp 3 V-r12 c0 and V-r13 P1 (48/48). Supp 4 and supp 2 (stage3 sec. 35, hand given LEMMA S2): hand steps V-r13; (c1)/(c3) 12/12 V-r13 c0 and P1 (independent generator).
    - LEMMA S2: V-r13 at P1 with an independent generator (all 6 charts unit; calibration non-unit, dim 1).
    - Over Q: parallel case V-r14 (slimgb). Non-parallel case > 2 GB, QUEUE S2-Q-NEQ. Not needed for the P1 proof.
    - Case split (alpha) = (alpha0) + (alpha1 by supp 2, 3, 4) checked EXHAUSTIVE V-r13. With S2 at P1, [T31] for m0 is complete at P1.
    - [DC3]: 214/220 at P1 CL, 6 hard cells queued.
    - [T22]: 61/66 at P1 CL (verifyfl R10 M3); 5 cells to the big slot.
  - **General m, |supp m| <= 3: verifyfl R11.6 route (V-r16).**
    - A char-0 (5,1) reduces to a char-p (5,1) at some m''. Two-column m'' are excluded by TC5_p. Every other m'' falls into a case system, so it suffices that every [DC3]/[T22]/[T31] case system with symbolic m has no F_pbar point off t(t+1) = 0 at P1. No runs over Q are needed.
    - TC5_p: the flagged steps are re-checked by me mod P1, and the S7 pair-equation counts agree over Q(i) and mod P1.
    - Still needed: Lemma SL and TC5 in char p. TC5 uses SL; also the zero-defect points need it.
      - Evidence: FLk uses C only through i (Complex.im only for i != -1, -i, valid when char != 2), and its integer literals have prime factors <= 7.
      - Proof-grade route (V-r16): port FLk and the TC5 blocks to a field K with i^2 = -1 and finitely many numeral hypotheses (N : K) != 0, then check that P1 divides no N. This is leanfl's job.
    - Ledger at P1: [DC3] done except A0-ne and B0-ne (big slot); [T22] open cells (A 21, 18, 11..0; B 45, 21, 18, 11..0); [T31] split A done, split B not built.
    - History: verifyfl R10.8/R10.10 ([DC3] on the line) had per-case char-0 claims, which are invalid (errata [L], [M]: cases are locally closed strata). Only the whole cover counts, as in R11.6.
    - A1-ne and B1-ne are UNIT at P1; I re-ran both myself (V-r16).
  - **General m, |supp m| = 4, 5:** OPEN.
  - **Split (5,1) spaces (e_i m^T in L'): CLOSED in c0 (V-r20).**
    - Non-isotropic m: SPLIT.
    - Isotropic m, zero-free: R2.14 via CC3 (V-r16).
    - Isotropic m, one zero: ncol THEOREM R32 (RED-p at 65521, 32/32; given CC34 and R5.1).
    - Isotropic m, two zeros: THEOREM Z2 (82/82 orbit charts, staged refinement sound).
    - Both RED-p systems are closed and projective with no saturation. I re-ran sample charts.
  - **|supp m| = 4, 5, [DC3]:** VF-DC3-P45 partial (paused / cut).

**1.2 (6,2) and (7,3)** (helper ncol, NOTES-ncol N1-N3).
- Chain: (DI_5;e) + (N_e+) + (NC'_e at dim e+4) => (DI_5;e+1). V-r8 (R7.2), restated V-r14.
  - "NCOL for SOME hyperplane" is equivalent to (N_e+), by the Hyperplane Lemma (C1, V-r14).
  - (DI_4x4) is needed at no e (V-r14). The R6.3 erratum is respected.
- **(7,3) <= (DI_5;3) + (N_3+)** (C2, V-r14 c0).
  - Also C4 (V-r14): with w non-isotropic, no row carries C.
- **(6,2) <= (DI_5;2) + (N_2+) + exclusion of configurations (a)-(d)** (C3, V-r14).
  - (a): THEOREM N2 V-r14. Hand reduction + projective Gr(3,8) system on all 56 charts; my independent generator is unit at 2 primes; calibration 32/56.
  - (b): untwisted (N3.3) and excluded via the duality N3.1, both V-r14.
  - (c), (d): OPEN.
  - C5 (V-r14): reduces (N_e+) for nondegenerate C to (T2)/(T3).
  - Round 2 (V-r15): R2.1-R2.5 verified; the reductions of row-carried isotropic C and of u_i = 2 (case B) in (7,3) to (CC3) verified; the (SR3) route R2.8 verified as a reduction.
  - THEOREM CC3: V-r16 (case (II) re-derived; the three survivor GBs re-run, [1] x3). R2.14 (split (5,1), zero-free m): V-r16 given CC3. Case (C) of R2.4: OPEN.
  - Round 3 (V-r18):
    - E3P is exact over Q (my chart-012 GB [1], one S5-orbit).
    - THEOREM PT2 is c0 by RED-p. My own independent generator gives 11/11 orbit charts unit at P1, and the orbit count and calibration agree.
    - The R3.3 reduction of (PROD) to the three Gr(4,10) chart types is verified.
    - RIGOUR: PROD-NCOL at P1 does NOT give (PROD) in char 0, because "non-product" is an open condition. It DOES give CC3-e2 in char 0 together with PT2, by whole-cover RED-p on the closed {(S,G)} variety.
- NCOL-P3, NCOL-S, P51, DC: V-r5/r6.
- (N_2+), (N_3+) (NCOL in general): OPEN (NUM 120/120; X2 test 0/461 with control 83/100).

## Branch 2: single-row elements (regime C)
Write z = (dims of the single-row parts).
- **z = (1,0,0,0,0):**
  - F1, F3, F4a: V-r5.
  - F4b: THEOREM F4b-X V-r8 c0 (FC V-r7).
  - Result: impossible.
- **z with two 2's:** THEOREM Z22 (+ Lemma DEG), V-r7: impossible.
- **z = (2,0,0,0,0)** = (S3-a):
  - Reduced to (PR2) or to (PR2-split') (V-r10).
  - **(PR3) and (PR2-split') are FALSE as stated** (stage3 sec. 37 (E); V-r16 exact, my own code verify2/r16/pr3_cx_mine.py).
    - The counterexample N = X + e_3 (x) Z is level, 5-dim, with row projections (1,2,2,2). Its only single-row part is e_3 (x) Z (2-dim). X has defect 2.
    - The failure is in stratum (III): some row projection is 1-dim, i.e. m_kl = 2. (PR3) can still hold in strata (I) and (II), where all row projections are 2-dim.
  - The counterexample does not extend to dim 9. EXACT at rho = 1, 2, 7/3 (pr3_cx_t1.py): dim T_1(N) = 10 and the sigma_2 form there has rank 4, so dim L <= 8. Generic members: NUM (stage3, T_1 = 9).
  - Corrected route needs three things:
    - (PR3) for strata (I) and (II);
    - a complete classification of stratum (III) (is stage3's family all of it?);
    - a T_1 / FO2_0 bound on all of stratum (III), uniform in the parameters (exact at 3 points so far).
  - (S3-a) itself is still plausible. Status: OPEN; NUM probes 0/133, 0/155.
- **Generic single row (S3-G, PL4):** V-r4.
- **Mixed patterns (2,1,..):** NUM (row-kernel FO2_0 census, V-r9 logic); OPEN as theorems.
- **z-vectors with single-row parts in several rows (at most one entry 2):** OPEN (not analysed).
- **SR5, SR2111 and the Fourier lemma** (stage3 sec. 36): V-r15 c0. Hand proofs re-derived; my own generators give (3,2) 20/20 and C* 20/20 unit over Q, calibrated.
  - These kill z = (1,1,1,1,1), (2,1,1,1,1) and (2,1,1,1,0).
  - OPEN: (1,1,0,0,0), (1,1,1,0,0), (1,1,1,1,0), (2,1,0,0,0), (2,1,1,0,0), (2,0,0,0,0).
- **z_i = 3** (split free line, O1; stage2):
  - Every explicit survivor is killed by FO2-joint (method V-r11). Patched re-run (E-MSOLVE-BIGCOEFF) re-confirmed all fixed-data kills: crossC1, K33, crossA, D003ptA/B, D04-PROP sigma = 0 and 2, (S2) sigma = 2 (V-r13 log check).
  - Uniform proof OPEN (lead: the B_w forms, stage2 R11-3 V-r11).
- **ncdef family:** reduces to (5,1)_{m0} by PFC (V-r9); see 1.1.

## Branch 3: a minimal row or column pair, (B1) of REG1 (stage2; any annihilators, via (Q-r))
- **V-r4 to r9:** C7/C7'' (minimal pairs), GEN-type layers, (Q-r), (FO-r), (T2), B-IND (a,c,d), PROP classification, R10-3 (**) test.
- **PROP candidates:**
  - Members excluded (V-r9, my extension test).
  - D04-PROP for all sigma: logic V-r11; char-0 loophole closed only by msolve char 0 (evidence); fixed-sigma kills re-confirmed; parametric re-run RUN.
  - D003-PROP Case A over P^2_alpha: 70/70 at P1. Coverage via S_4 + X0 is V-r15.
    - Affine parameters with exclusions, so the P1 verdict misses alpha reducing into the bad loci or with p in a denominator.
    - The char-0 run is msolve multimodular, i.e. evidence. A proof needs Singular over Q (70 charts).
    - Sizing over Q (V-r16, verify2/r15/d3a_slim.py, slimgb): 6 of 8 charts tried are UNIT, in seconds to 5 min. Chart 0-1-3-6 runs out of memory at 2 GB, and 0-1-3-7 passed 1.5 GB.
    - So the route is feasible only with the big slot (6 GB per chart). All coefficients are integral.
    - Pool run over Q (V-r22): 64/70 charts UNIT exactly. 6 FAILED: 0-1-3-6, 0-1-3-7, 0-1-4-7, 0-1-6-7, 1-2-5-7, 1-3-4-7.
    - **D003-PROP Case A CLOSED in c0** (stage2 R19-2/3, audited V-r22): the big-kernel lemma; its degeneracy set equals the setup-exceptional set; T1cert in Singular over Q; the alpha_4 = 0 family by its own kernel lemma; a2 = 1 and two zeros reduce to X0 (exact). The chart route is superseded.
- **B(dep) eliminations** (P0_B_ii comps, D00-3 Q0_B_3/P0_B_3): queued (ST2-ELIM-msolve); CL/OPEN.
- **F2col:**
  - Cross-type ruling: 67/70 mod p (evidence). v3 slices (Z fixed) 70/70 and 68/70: evidence for those slices only.
  - Full 4-parameter family: the Gr(4,8) formulation FAILED x4 at 2 GB. Next is stage2's K-reduction (VERIFIED logic, V-r16; degenerate loci to be covered), which needs Gr(3,6) with 9 variables.
  - Earlier: RUN (ST2-F2COL v3). Jump locus m_0 = 0: OPEN.
- **Uniform statement** "(Q-r) + FO2-joint => dead": OPEN.

## Branch 4: some a_r >= 2 (reg2)
- **RESULT C, 8.1(b):** (S6-FO2) + FL => no a_r >= 2. V-r5/r7 c0.
- **(S6-FO2)** says every level space containing a 6-dim 4x5 level space M has dim <= 8.
- **(S6-FO2) proved for:**
  - All 15 line-spanned patterns with census members (V-r5 to r11 samples / certificates);
  - BLOCK, DOUBLE-BLOCK and RANK-ONE families (V-r11);
  - Skew deformations: GAP, found by reg2 itself in round 13 (21.4). The table of rounds 8-10 deformed only parts given by two basis elements; parts written with spanning sets were never deformed. There are new level-for-all families (2121Vni, 2121Vnii_xinf, 2211BD) and special loci; exact certificates and a redone double-deformation scan are pending. My V-r12/V-r14 verdicts covered the table as listed, not its completeness.
  - Lemma SK (V-r12).
- **(S6-FO2) in general: OPEN.** It needs:
  - a proof of the structure law (BL) (NUM 187/187), or the multi-skew conjecture;
  - the remaining hit-free patterns: 6 partial patterns with TIMEOUT classes (reg2 19.6); 22 are EMPTY by the exact incidence split (reg2 R11-3; method calibrated, I have not re-run it).
  - R3, i.e. rank-3 3-dim row blocks (reg2 R11-4). The exact exclusion of the cases (alpha), (I), (II) is OPEN.
  - Exact certification of the N-type and R1-type families.
- **Round 11 (reg2), V-r16:**
  - (1,1,1|1,1,1): CLOSED, V-r17. My independent re-implementation of the incidence split (inc111_mine.py) gives 476 EMPTY and 36 NONEMPTY, one orbit; minAssGTZ shows one linear component = M111. My exact check (m111_mine.py): level, dim 6, dim T_1 = 9, sigma_2 rank 3 on T_1, so dim L <= 7.
  - (1,1,1,1|1,1) is NOT empty, although CE-1 had 0 hits. The certified family '1111_11a' is VERIFIED exactly by me (fam1111_*.py), so dim L <= 8 on the whole family:
    - level identically in a, dim 6;
    - dim T_1 = 9 for every a in P^1: the minor gcd is a(a+2)(a^2+a+1)^3, and a = 0, -2, omega and infinity are checked directly;
    - sigma_2 does not vanish on T_1 for any a: the entries have gcd 8a(a+2), and a = 0, -2, infinity have rank 3.
  - Is the family the whole pattern? That rests on incpat.
  - The earlier inc111.py / cal211.py logs are INVALID (variable clash); reg2 marked them.
  - Finite-mechanism theorem (reg2 19.3): VERIFIED as a conditional reduction. It assumes (BL) and no R3; then M = Lin(M) + genuine parts of the types R1/C1, R2/C2 and N, with finitely many types. The shape of (S4) is taken as stated.
- **Round 9 claims:**
  - Lemma SK2: V-r13.
  - SIGMA and (d) column-deformation lift_gram certificates: V-r13 (logs audited, coverage recomputed, d_0 in T_1 argued).
  - Double deformations (six families): dim T_1 <= 10 and rank q >= 3, V-r14 (logs; non-vacuous CAL lines; d_1 in T_1 checked).
  - LEMMA SK3 (full 4-dim row block => rank B <= 2): V-r14 (hand (i)-(iv) + exact shape-(iv) logs, unit even without the rank condition).
  - (ii-g) row curves: V-r14 (parametrisation complete; fibres over the roots of the lex leading coefficients are empty).
  - Conic double deformation: CLOSED by reg2 R11-1, V-r17 (my own membership test modulo (Q) and exact conic points). 3-dim row blocks: OPEN (R3).

## OPEN leaves (size guess: S = hours, M = a day of team work, L = new idea / multi-day)
1. (5,1) for general m: symbolic-m typed systems, |supp m| = 3, 4, 5 (Branch 1.1). **L.** This is the largest computational gap.
   - Progress: SYM-M [DC3] on |supp| <= 3 has 7 cells open.
   - That gives char-0 content only when ALL cells close.
2. (PL) on 5 columns certified over Q (Branch 1.1). **M.** Mod-p runs pending; a hand proof would be ideal.
3. (2,1) kernel stratum (Branch 1.1). **M.**
   - Done in char 0, V-r13/r14/r15: two-column kernels (generic, all m; line d = u), three-column kernels (A1, A2, family B).
   - (a) the 16 special points: CLOSED, V-r17 (64/64 unit at P1, RED-p).
   - Open (b): (2,1) kernels supported on 4 or 5 columns, never classified.
4. m0 completion (Branch 1.1). **S.** Same prime P1 throughout.
   - [T31]: COMPLETE at P1 (V-r13; every piece re-run at P1 with my own generators).
   - Left: [DC3] 6 hard cells and [T22] 5 cells, both in the big slot.
5. [T22] hard cases and [T31] B1 for the three sample m (Branch 1.1). **S-M.** Big slot.
6. (6,2), (7,3): (N_3+) closes (7,3); (N_2+) plus configurations (c), (d) close (6,2); (DI_4x4) is not needed (Branch 1.2). **L.**
7. (S3-a) (Branch 2). (PR3) is FALSE in stratum (III) (V-r16). Corrected route: (PR3) for strata (I) and (II), plus classify stratum (III) and bound it by T_1/FO2_0. **M-L.**
8. Multi-row z-vectors and mixed (2,1,..) (Branch 2). **M.**
9. O1, a uniform z_i = 3 exclusion (Branch 2/3). **M.**
10. Branch 3 leftovers: D003-PROP over P^2, B(dep), F2col, the uniform statement. **M.**
11. (S6-FO2) in general (Branch 4): a proof of (BL), R3, the TIMEOUT hit-free classes, and the N/R1 families. (1,1,1|1,1,1) is closed (V-r16). **L.**

## Pending relabels
- E-STALE-OUTPUT: CLOSED (V-r18).
  - verifyfl re-solved every UNIT manifest line at P1 with the guarded wrapper and found 0 mismatches: symA 252, symB 249, sym2 3, m0 dc_p5b 214, m12m3 252, m11m2 252, iso 253.
  - My mtime audit found 5800 genuine pairs, and msolve truncates its output on a crash.
- E-MSOLVE-BIGCOEFF: all of stage2's fixed-data kills are re-confirmed. Only the D04-PROP parametric re-run is still pending.
- K1 relabel waits for [T22] at P1.
- Every P1 verdict becomes c0 only when its whole case split is at P1.
