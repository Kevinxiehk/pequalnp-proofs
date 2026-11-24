# NOTES-stage2 (role: stage2; start 14:38, budget 90 min -> ends ~16:08)
## FINAL STATE (stage2, STOPPED 08:04 UTC on Kevin's abort of L-gct-210)
 F2col: CLOSED as structure and logic (verify2 audit); every row [S]/[E]/[RED-p]/lemma; log pointers in "F2COL-TABLE log pointers (R22)"
   + stage2/r21/redp_logs.log (incl. the special-Z nu = 0 member). D003-PROP Case A: CLOSED (verified). D04-PROP parametric: CLOSED in char 0 (R22-1;
   verify2 audit pending). B(dep): P0_B_i points exact (R22-2); the R12-1 eliminations are still mod p only. O1: isotropic two-row family closed
   (R23-1); open: the two-row classification char-0 certificate (ST2-TWOROW-CERT-BIG queued), the three-row classification (numerical only), and a
   uniform proof. No jobs of mine are running.
## RESULT-R22 (stage2 round 22, 07:38-08:00 UTC) -- details R22-1 .. R22-4; F2col table log pointers added.
 F2col: verify2 audited the consolidated table (VERIFIED as structure and logic); the four missing logs are re-run and saved (r21/redp_logs.log:
   nu = 0 (0,0,1) 70/70, cross-type (0,0,1) 70/70, jump point (0,-8,7) 56/56, special Z at nu = 0 70/70; Kt3 lines re-logged 20/20).
 D04-PROP parametric: CLOSED in char 0 by the recursive kernel bound (generic sigma) + exact exceptional sigma (r22_genset.py generic setup).
 B(dep): the two P0_B_i points are exact kills (nq = 7, generic combination nondegenerate -> isotropic dim <= 3); remaining: char-0 versions of the
   R12-1 eliminations.
 O1: two-row isotropic family: recursive bound kills at a random t (parametric run over Q(i)(t) in progress); classification gaps listed (R22-4).
 Lean note R22-3: the six abstract lemmas (meeting lemma, max-isotropic bound, kernel kill, big kernel, rank-2 split, recursive bound) + problem-specific inputs.
## RESULT-R21 (stage2 round 21, 07:09-07:42 UTC) -- details R21-1 .. R21-3; final F2col table rows at the end.  F2col CLOSED (pending verify2 audit).
 J_A^R1: RANK-2 SPLIT (B_1 = 2b l2 l5 over Q, so L'' lies in one of two hyperplanes) + recursive kernel bound (q0(w',w') = -400 lam (a3-7)) + S_3 cut
   (all exceptional curves cut; lam = -1 slice and the line (0,0,-1) killed exactly, incl. points over Q(sqrt 21), Q(sqrt 3)) + T1cert 10/10.
 RECURSIVE KERNEL BOUND kills every remaining line generically (6 R1 lines, R2 (0,0,0)); exceptional parameter values killed pointwise over number fields
   up to a cubic (Singular-driven recursion, or reduced charts over Q(sqrt 3) 20/20). KU (0,0,0) and the R1 K2/Kt3 chart runs are superseded.
 EXACT RD: factored-determinant certificate (r21_RDcert2.py) over QQ in 16 s: generic R1 RD = {(1,1,1)}, a1 = 0 family RD_A = {(1,1)}, a1 = a2 = 0: none.
   Big-slot ST2R1RDCERT dropped.  R1 a1 = 0 and a1 = a2 = 0 families: kernel kill + T1cert 12/12 + cut -> closed lines only.
 => Every row of the F2col table is [S]/[E]/[RED-p]/lemma.
## RESULT-R20 (stage2 round 20, 06:21-07:07 UTC) -- details R20-1 .. R20-3; consolidated F2COL-TABLE (R20) at the end.
 R1 rank-drop locus: mod-p structure (Singular sat + minAssGTZ, 1 min) = the single line a = (1,1,1) (generic R1), (a2,a3) = (1,1) in the a1 = 0 family.
   Exact certificate without primary decomposition (r20_RDcert.py: 1 in I + (1 - w f EXC) for f = a_i - 1): mod p all [1] in 44 s; char 0 queued.
   (ST2-R1COFSING's full minAssGTZ over Q ran out of memory at 1.5 GB.)
 R1 S_3 cut -> 10 lines: kernel bound kills (2,1,1), (3,0,1), (4,0,0); K2 for (4,0,1), (22/7,0,6/7), (11/3,0,7/6), (6,0,0) and Kt3 for (1,1,1), (0,1,1)
   running in Singular (per-chart timeout, msolve char-0 fallback); exceptional lam per line (4 combinations c) queued.
 OPEN: the R1 jump family J_A^R1 (a1 = 0, a2+a3+a4 = 0; B_z ranks 2,8,8 in nq = 10): no kernel lemma applies (recursive bound undecided);
   KU (0,0,0) Singular still running (last R2 line).
 F2COL-TABLE consolidated for verify2 (rows 1-21): everything [S]/[E]/[RED-p]/lemma except rows 8 (KU (0,0,0)), 20-21 (R1 generic: RD cert, lines,
   J_A^R1, R1 families a1 = 0 / D = 0).
## RESULT-R19 (stage2 round 19, 05:56-06:22 UTC) -- details R19-1 .. R19-4 at the end.
 R2 LINES: 12/13 at FULL PROOF GRADE. The four kap = 2 lines go through r18_Kt3.py: q0|K = g(nu) M with M constant, so k = (-b+s)K1 + aK2 over Q(s),
   s^2 in {46, 76} (both isotropic lines via minpoly), no Rabinowitsch for k_i, q0(k, L3) = 0 eliminated: Singular 20/20 [1] each, ~3 min, 70 MB.
   The 43 slow systems and the big-slot job LOW_ST2KTBIG are gone. verify2 checked the construction; zeros of g(nu) confirmed in {0,-1,1/3}.
   (0,0,0): KU Singular in progress (paused by the memory guard while the big slot is heavy).
 D003-PROP Case A: CLOSED (verified by verify2): big-kernel lemma with exact degeneracy set = setup-exceptional (Singular), T1cert Singular 12/12,
   the alpha_4 = 0 family by its own kernel lemma (a2 = 1 ~ a2 = -2 by S_4, a2 = -1 = X0), zero patterns by S_4. Chart-free.
 R1: the symbolic-c determinant (10666 terms, degree 25) takes seconds in Singular; exact RD queued as ST2-R1COFSING (<= 1.5 GB), replacing R1COF2.
## RESULT-R18 (stage2 round 18, 04:07-05:56 UTC, with a usage-limit gap 04:25-05:14) -- details R18-1, R18-2 at the end.
 R2 nu-LINES (13): GENERAL KERNEL BOUND (L'' meets ker B_c = K in dim >= 4 - floor(r/2); L'' cap K is q0-isotropic) + exact data per line:
   4 lines KILLED by the bound alone [E+lemma]: (1,1,1), (2,1,1), (3,0,1), (4,0,0); 4 lines (K = Ck, q0(k,k) = 0) Singular QQ 20/20 on reduced charts [S]:
   (4,0,1), (6,0,0), (22/7,0,6/7), (11/3,0,7/6); 4 lines (dim K = 2) via the parametrised-k reduction r18_Kt.py: Singular QQ [1] on all systems
   except 43 (each > 120 s), those 43 are [1] in msolve char 0, Singular 6 GB queued (ST2-KTBIG); (0,0,0) (dim K = 4, m = 2) via r18_KU.py: mod p 90/90,
   Singular rerun in progress. Exceptional nu on all lines: only the slices {0,-1,1/3} (done) and nu = -1/2 on (2,1,1) (killed by the lemma).
 D003-PROP Case A: the BIG-KERNEL lemma applies (common kernel dim 3 = ker B_c, det q0|K = 353894400 (a2-1)^2 (a2+a3+1)^6) -> generic member dead by
   linear algebra; degeneracy set and T1cert running (small-memory sequence). This avoids the 6-GB Singular charts of verify2's d3a route.
 R1: R1COF2 still interpolating in the pool; S_3-cut tool for nonlinear pieces ready and validated (r18_symcut_nl.py reproduces the R2 cut).
 Memory incident 05:28: stopped everything except R1COF2; now ONE small job at a time with a memory guard.
## RESULT-R17 (stage2 round 17, 04:05 UTC) -- details R17-1 .. R17-7, table F2COL-TABLE at the end.
 T1cert in SINGULAR over QQ (proof grade): generic R2 12/12, all 18 tree families, the R1 jump plane, generic R1 12/12, cross-type and its a1 = 0
   sub-family 12/12: T_1 has generic dimension off the exceptional hypersurfaces in every family (rref denominators checked to lie among them).
 CLOSED (rigorous modulo verify2): the JUMP LOCUS (Deg empty, S_4 cut, 2 points: RED-p / lemma), the SPECIAL Z n = (1,0,0,0) (new "big-kernel"
   lemma + 1 RED-p member), and the whole CROSS-TYPE ruling (standard kernel kill, S_4 cut -> J u 5 points, 4 RED-p members + J) -- the old
   chart 2-3-5-7 and the R1 slice are redundant (both big-slot extras dropped).
 R2: nu = 0 slice cut -> A u J0 u points; 12 nu = 0 fixed members killed (5 by the lemma, 7 by 70/70 RED-p charts); J0, J_A collapse by the cut.
   The 15 cut nu-lines: msolve CHAR 0 [M0] 70/70 [1] on 11 so far (incl. a = (1,0,0) whose 2 mod-p charts FAILED in the pool), the J_A line is
   killed by the jump-type lemma; Singular QQ times out on many line charts -> proof grade for lines needs a reduction (next round).
 R1: generic kill [E] + T1cert [S]; exact rank-drop locus still computing (R1COF stuck in sympy; lean r17_cofinterp2.py queued as ST2-R1COF2).
## RESULT-R16 (stage2 round 16, 03:05 UTC) -- details R16-1 .. R16-7 at the end.
 R2 EXCEPTIONAL FAMILIES: kernel kill on all of them (nu = 0, a1 = 0, nu = -1, nu = 1/3, D = 0, nu = 1, nu = -1/3 and 13 depth-2 sub-families via the
   automatic tree r16_tree.py; 18/18 handled, none manual): always k = e7 - e6 constant, survivors = an H-type plane + 0/1 points + sub-families;
   T_1-JUMP families (dim T_1 = 14) obey the JUMP-TYPE lemma (survivors e.g. a2+a3 = 7).
 SYMMETRY CUT (new): S_3 on columns 2,3,4 (nu fixed) collapses the generic-nu R2 survivors to finitely many nu-lines (ST2-R2LINES + ST2-R2SYMLINES)
   plus the S_3-invariant families A = {a1 = 0} and J_A = {a1 = 0, a2+a3+a4 = 0}, which collapse to points the same way; row-S_3 x column swap make the
   six special nu one orbit (checked: nu = 1, -1/3 setups identical to nu = 0, 1/3). The 3-parameter H run is now a cross-check (char 0: 35/35 [1]).
 JUMP LOCUS (R1, lam = 0): Deg computed exactly = EMPTY; survivors {a1 = -8} u {a1 = 0}; S_4 on columns 1..4 removes a1 = -8 -> finitely many points.
   The heavy Gr(4,10)/Gr(3,8) charts are not needed (ST2-JUMPK can be cancelled).
 T_1 CODIM >= 2 (target 3): r16_T1cert.py (pivot-column injectivity charts): generic R2 mod p finds exactly {nu = 1, a1+a2+a3 = -1} and
   {nu = -1/3, 4a1 = a2+a3+1} -- the symmetry images of the nu = 0 / 1/3 jump planes. Singular-QQ version = proof grade (next).
 R1 GENERIC: same kernel kill, q0(k,k) = 2 lam (a1+2a2+2a3-6) (same H); exact common rank-drop locus by lattice interpolation queued (ST2-R1COF).
 D04Pasym mod-p plain re-run: affine 126/126 [1], tau-chart non-units only (as R11). verify_all complete.
## RESULT-R15 (stage2 round 15, 02:00 UTC) -- details R15-1 .. R15-5 at the end.
 TOOLING: two driver bugs audited. E-STALE-OUTPUT (coordinator) and E-MSSTR-RATIONAL (mine: non-integer rational coefficients truncated) -> hardened
   *_fx.py drivers. Only r15_iso2row was hit by the rational bug (VOID); all other inputs integral. Re-verification with the _fx drivers (r15/verify_all.log):
   D003A, crossC1, K33, crossA, D003ptA/B, D04Pa sg0/sg2, S2s, tworowN, tworowI (both i), isoSpecA, D04Pasym char 0, D3A mod p: ALL re-confirmed, 0 FAILED.
 F2col RULING R2 (the 4-parameter run FAILED chart after chart): replaced by an EXACT KERNEL KILL [rigorous modulo listed setup loci]: the B_z share the
   constant kernel vector k, q0(k,k) = (nu+1)(3nu-1)(a1+2a2+2a3-6); rank B_c = 7 forces k in L''. Exact cofactors + Groebner: survivors only on
   H = {a1+2a2+2a3 = 6}, the 4 lines a in {(1,0,0),(1,0,1),(1,1,0),(1,1,1)}, and setup-exceptional 3-parameter families. H in reduced charts Gr(3,7):
   fixed member 35/35 [1]; parametric 15/35 [1] + 1 FAILED in my slot (pool: ST2-R2H, incl. Singular std over QQ); lines: ST2-R2LINES.
 JUMP LOCUS of R1 (nq = 10): second kernel lemma (L'' meets each 3-dim ker B_z; there the other B_w are squares of independent linear forms) =>
   k0 = e9 - e8 in L'' => survivors only on a1 = -8 (+ an exactly computable Deg, + a1 = 0); reduced charts Gr(3,9): ST2-JUMPK queued (one chart FAILS at 2 GB).
 CROSS-TYPE (lam = 0): fixed-driver re-run 67/70 [1] + FAILED exactly 2-3-4-7, 2-3-5-7, 2-4-5-7; big slot: 2-3-4-7, 2-4-5-7 genuine [1]; 2-3-5-7 pending.
 verify_all complete: also D3A char 0 70/70. R1 generic setup died at its 50-min timeout -> ST2-R1SETUP queued.
 TARGET 2 three-row with m free: no clean solution with >= 3 columns (numerical). Two-row char-0 certificate: chart A checks pass, rest queued.
## RESULT-R14 (stage2 round 14, 00:10 UTC) -- details R14-1 .. R14-3 at the end.
 VERDICTS: D04-PROP parametric re-run with the patched tool confirms R11-4/5 (affine 126/126, tau-chart non-units only at tau = 0). ST2-F2COL R2 still in
 its sympy phase (4-parameter rref) at 00:08; cross3_big not started -- nothing to report yet, no genuine non-unit so far.
 TARGET 2 (z = 3 planes P = X_ri): level of P (+) e_i Z reduces [rigorous] to: c(p) in Cm, P_2(p) = 0, (P_2(p minus col j))_j in span(1,m) (+ C4).
   * two-row P: classified (mod-p primary decomposition, two chart types by S_5): P = span{e_a m^T, (e_a - e_b) e_k^T} with m_k = 0. Killed by SPLIT
     for <m,m> != 0; for isotropic m (outside SPLIT) FO2-JOINT kills the member m = (0,1,i,-1,-i) EXACTLY (over Q(i), both embeddings, 70/70 each);
     the 1-parameter isotropic family is not yet done parametrically.
   * three-row P: C4 alone allows 3-5 columns, but with the level conditions no solution outside a 2-column block was found (numerical) -> F2col.
 UNIFORM STATEMENT: no proof. Heuristic why FO2-joint is so strong: a 4-dim common isotropic subspace of N >= 2 generic quadrics in 8 dims has expected
   dimension 16 - 10 N < 0; a uniform proof must show the span of {q_m} on T_1(X)/X never degenerates enough -- not achieved.
 TARGET 3 CLOSED: D003-PROP Case A over P^2_alpha with the full forms: 70/70 charts [1] mod p AND in char 0 (parameters free, bad loci excluded, X0 exact) (R14-5).
 F2col: ruling-2 slice (nu free, Z fixed) 70/70 [1]; ruling-1 slice (lam free) 68/70 + 2 FAILED (queued); fast generator r13_F2col_v3.py (ST2-F2COL on v3 since 00:18).
 NOT DONE: char-0 gap of the F2col rulings (their mod-p verdicts are not in yet); target 2 three-row case rigorously; isotropic two-row family.

## RESULT-R13 (stage2 round 13, 23:38 UTC) -- details R13-1 .. R13-4 at the end.
 TOOL BUG (E-MSOLVE-BIGCOEFF, R13-3): msolve 0.6.5 mis-reads integer coefficients >= p in mod-p mode (false non-unit seen). Repaired (coefficients
 reduced mod p; stale outputs deleted; crashes reported as FAILED). ALL earlier fixed-data kills RE-CONFIRMED with the patched tool (R13-4):
 crossC1, K33, crossA, D003ptA/B, D04-PROP sg = 0 and 2, (S2) sg = 2. Team audit (coordinator): no other team affected.
 F2col STRUCTURE (R13-2, rigorous): ruling 1 = graphs {(u, lam R u)} (lam = 0, infinity: cross-type), ruling 2 = {span{(w,0),(0,v)} : <v,w> = 0}
 (always K33-type). Cross-type ruling with general Z (3 parameters): explicit T_1 (dim 13 off the rank-jump locus m_0 = 0, where dim T_1 = 15);
 chart coverage by S_4 symmetry; parametric FO2-joint (D saturated, mod p): 67/70 charts [1], 3 charts FAIL (memory at 2 GB, also in Singular) ->
 queued for the big slot (6 GB). The full rulings R1 (lam, a), R2 (nu, a) and the jump locus run in the pool (ST2-F2COL, generator r13_F2col.py).
 NOT done: target 2 (z = 3 planes lie in a 2-column block; besides F2col, 2-row-supported planes must be excluded -- they force lam_{rc} = 5),
 target 3 (D003-PROP Case A over P^2_alpha).

## RESULT-R12 (stage2 round 12, 22:44 UTC) -- details R12-1 .. R12-4 at the end (+ verify2's PROP addendum under ROUND 12).
 CASE B of (2,4) at first order is CLOSED up to dead points: every X passing (FO-r) is PROP, or has a 3-dim single-row part, or is one of finitely
 many explicit points, all dead (S1 exact FO2 = 8 [verify2]; two D00-3 points FO2-joint EXACT; two P0_B_i points FO2 = 8 + (T2) fail [numerical]).
 The B(dep) leftovers came from msolve eliminations (mod p, evidence) after the Singular runs were killed (R12-1).
 z = 3 SHAPES: the Case-B z = 3 member crossA is dead (FO2-joint exact, 70/70). All z = 3 shapes found (K33, cross C1, crossA, D0Q c_a = 0) lie in
 ONE explicit family F2col = {P (+) e_i (x) Z : P a Lagrangian of the 4-dim quadric (S x S, <p_0,p_1>) in a 2-column block, Z in Gr(3,4)}
 [classification rigorous, R12-4]; every member tested passes (FO-r) and FO2 (bound 9) and FAILS FO2-joint (exact at 3 members, numerical at ~10).
 O1 (uniform): NOT proved. Route: (i) FO2-joint fails on all of F2col (4-parameter exact computation); (ii) every z = 3 plane X_ri lies in a
 2-column block. The B_w-form structure on T_1(X)/X is not uniform across shapes (R12-3), so (i) must use the explicit T_1 of F2col.
 Queue: ST2-CERT-D04P (Singular certificate for the D04-PROP char-0 step, ~4 h, low priority).

## RESULT-R11 (stage2 round 11, 22:20 UTC) -- details R11-1 .. R11-5 at the end.
 FAST EXACT FO2-JOINT: msolve mod p on all charts of the (proper) Grassmannian = proof for fixed rational data (UPDATE 10 argument); calibrated both
 ways; 70 charts in ~20 s (Singular: > 1 min per hard chart). Tool stage2/r11_charts_msolve.py.
 z = 3 SURVIVORS KILLED (exact): cross a in C1 (70/70 charts [1]); the (3,3) z = 3 member K33 (70/70); (S2) at sg = 2 (210/210). Together with
 R10 (X0; D04-PROP at sg = 2, -3) every explicit survivor of (Q-r)+(FO-r)+FO2+(T2) known to us is now dead by FO2-joint, including all z = 3 shapes.
 D04-PROP for all sigma: dim T_1 = 14 for every sigma and the complement degenerates only at 0 (R11-1); sigma = 0 dead (126/126); with a basis
 saturated at 0 the parametric run (both charts of P^1) is [1] on all affine charts mod p and the 25 non-unit tau-charts have char-0 elimination ideal
 (tau^e) -> no finite sigma admits an extension, rigorous except for sigma with p in all denominators; msolve CHAR 0 on all 126 affine charts: [1]
 (multimodular, evidence-grade certificate for that loophole; R11-5).
 STRUCTURE (R11-3): for a single-row element m = s e_i w^T, q_m = 12 P_2 + s Bw with Bw = 4 sum_j w_j P_2(t^(i) minus column j). For z_i = 3 FO2-joint
 forces (P_2(t^(i) minus column j))_j in span(1, m) for ALL t in L -- the quadratic part of the (5,1) defect condition on all of L: the lead for a
 uniform proof of O1. Numerically these single-row forms plus P_2 already obstruct (D04-PROP: 3 forms suffice).
 B(dep) eliminations: msolve-based replacement (r11_elim_msolve.py); comp2 -> PROP only; rest queued for after the Lean window.

## RESULT-R10 (stage2 round 10, 21:17 UTC) -- details R10-1 .. R10-5 at the end.
 (T2)   LEMMA [rigorous; re-derived by verify2]: if pi_r(L) is a hyperplane not containing 1, there are T_0..T_4 with sum T_k in J' + L_r and
        D_{T_k}G_j(xi) + D_{T_j}G_k(xi) = 0 on L_r (j <= k). Proof = degree-2-in-v part of chief's (**) (R10-1). EXACT tool r10_T2exact.py (no sampling).
 (**)   PROPOSITION [rigorous]: a 5-dim X is the L_r of a 9-dim level space  <=>  (**) has a solution T, kappa  <=>  (T1)-(T5) (R10-3).
 PROP   classified in Case B (R10-2): D04-PROP and D003-PROP (explicit, single-row parts (2,2), (1,2), (3,1), ...). All have Omega = C^5 and FO2 bound 9.
        (T2) EXACT: passes on D04-PROP alpha in {(1,1,-1,-1),(1,-1,1,-1),(1,-1,-1,1)} (fails on the rest, incl. (S3)) and on D003-PROP Case A
        (A = C(1,-1,0,0); general A running).  => the corrected target (T') "(FO-r)+FO2+(T2) => 3-dim single-row/column part" is FALSE.
        Target 3 ("FO2 <= 8 on Case A/PROP") is FALSE as stated (D003-PROP Case A has FO2 bound 9).
 FO2-J  NEW TEST [lemma rigorous, two lines]: L/X must be a COMMON isotropic subspace of all q_m = D^2 perm(J+m), m in X, on T_1(X)/X.
        EXACT kill (char-0 GB on all 70 charts of Gr(4,8)): the (FO-r)+FO2+(T2) survivor cand_D003P_l1m1 lies in NO 9-dim level space.
        NUMERICAL (LM on the Grassmannian, calibrated on L_r of ex1): FO2-joint excludes D = 9 for ALL 21 saved candidates incl. the z = 3 ones
        ((3,3) family, cross a in C1, (S2)): repeated floors 0.14 - 0.81.  => new uniform target: "(Q-r) + FO2-joint => dead".
 Running at hand-off (21:36): exact FO2J charts for cross a in C1 (z = 3; my slot, until 22:22, log r9/FO2J_charts_crossC1_k4.log, 5/70 charts
 unit so far), D04-PROP with sg symbolic (my slot, until 22:15, r9/FO2J_charts_D04Pasym_k4.log), (S2) (coordinator, queue ST2-FO2J).
 Queue: P0_B_ii components and D00-3 Q0_B_3 / P0_B_3 still running (no verdict yet).

## RESULT-R9 (stage2 round 9, 20:27 UTC, Kevin's machine) -- details R9-1 .. R9-6 at the end; specs COMPUTE-stage2.md S3', S7', S8.
 (2,4) BLOCK FAMILY, CASE B (ab = <p',q'>, s != 0), FIRST ORDER:
 B-IND  THEOREM [hand reductions rigorous + char-0 Groebner]: if a, b are independent on X, (FO-r) FAILS. (R9-1) The family FM is confirmed by
        an independent generator (raw permanents, r9_direct.py); the direct runs for FP0d/FQ0d exceed 400 s here (queued, QUEUE addendum 2).
 N0-W   LEMMA [rigorous]: in Case B, if some eta in X has s_1 = s_2 != 0 and (0,e_m) is in Omega, then p_m q_m = 0 on
        W = X cap {column 0 = 0, a = b = 0}. (R9-3)
 PROP   LEMMA [rigorous, 2 lines]: if rows 1, 2 are proportional on X with ratio != 1 (Case A is ratio -1), (FO-r) holds AUTOMATICALLY. (R9-5)
        So the (2,4) family splits into PROP (FO-r-blind; needs FO2/(T2)) and NON-PROP (N0-W applies).
 B-DEP  [exact, char 0]: NON-PROP Case B with a, b dependent is closed in the sub-cases D1 (lam != 0), D0-3, D00-2, D00-3 (all 18 charts except
        Q0_B_3, P0_B_3 running at the coordinator) and D0-4 M (all 4) ; the only first-order survivors are (a) X with a 3-dim single-row part (z = 3) and (b) one
        isolated point of D0-4 (M_A_i, f0 = f3 = 2) whose FO2 bound is 8 [numerical]. D0-4 Q0_B, P0_B, P0_A_i: queued (QUEUE ST2-S7').
 N1     LEMMA [rigorous] (lam = 0): sharper necessary condition on X_s = {s_1 = s_2 = 0}; with it D0-4 Q0_B (-> z = 3 only) and P0_A (-> Case A)
        are closed, P0_B case i leaves two points with FO2 bound 8 and failing (T2); P0_B case ii queued (6 small N1-components). (R9-8)
 COUNTEREXAMPLE to the structural target as stated [exact (FO-r), numerical FO2/(T2)]: (S3) = C kappa' + e_3 (x) span{(-4,1,1,1,1),(0,1,-1,0,0)}
        + e_4 (x) span{(0,0,0,1,-1),(0,1,1,-1,-1)} (kappa' = (sg,-1-sg,0,1) in column 0, rows 1..4) is a PROP (Q-r) solution with single-row parts
        (2,2), Omega = C^5, FO2 bound 9 (3 seeds x 3 sg), killed ONLY by (T2) (distance 0.5 - 1.4). So "(FO-r) + FO2 => 3-dim single-row part"
        is false; the target must include (T2) (or third order).  (R9-4)
 NOT DONE: (B0), B2 (no time); PROP survey (S8); Case A FO2 proof.

## [merged 20:38 from the cloud copy: the predecessor's round-8 RESULT block, written after the workspace was copied]
## RESULT-R8 (stage2 round 8, 20:30; STOPPED EARLY after 30 min for the handover) -- details in R8-1 .. R8-4 at the end;
## handover file: handover/HANDOVER-stage2.md.  Nothing in REG1 was closed in this round.
 1 [hand derivation, not machine-checked] graded form of (FO-r): (FO-r)_j <=> exists theta_j with D_{theta_j} P_k = P_{k-1}(xi^(j)) on
   L_r for k = 1..4 (P_k = sum of k x k subpermanents); obstruction only in k = 3, 4. The structural statement of target (1) is NOT proved.
 2 [rigorous + validated on 47 members] Case B, sub-case (B1), of the (2,4) family is parametrised completely (maximal isotropic Y_0,
   parameter mu) and Omega is reduced to a criterion on quadrics. CORRECTION of round 7: "Omega = span(e_0,1) in all of Case B" is FALSE
   on special loci (dim Omega = 3 when A' = n^perp with n two-valued, hand proof; dim Omega = 4 at one explicit member).
   Omega = C^5 never seen in genuine (B1), not proved; 3 Singular runs timed out (no verdict). Sub-case (B2) untouched.
 3 [rigorous] (B0a): Lemma B0-1 (all 3x3 subpermanents of the 4x4 block of x_0 vanish); the (2,4) family never has a 4-dim column
   projection, so it does not occur in (B0a). No contradiction and no candidate.
 4 Not reached: z = 3 with isotropic m.
## RESULT-R7 (stage2 round 7, 19:50) -- details in sections R7-1 .. R7-4 at the end; heavy-computation specs in COMPUTE-stage2.md.
 REG1 is NOT proved; (2,4) is settled only numerically; z = 3 is reduced, not closed.
 (FO-r) LEMMA [rigorous; sanity on the 10 full-projection lines of the known spaces]: for a line r with 4-dim projection, the projection
        of T_1(L_r) to line r is ALL of C^5; equivalently every column-deletion permanent G_j(J' + xi) is, on L_r, a first-order variation
        D_{t'} N(J' + xi) of the level function. Strictly sharper than "dim T_1 >= 9".
 CROSS  [rigorous]: for every cross space with a not in C1 the projection is 3-dim -- excluded at first order, INCLUDING the locus b = 0
        (3-dim single-column part) which FO2 could not exclude.
 (2,4)  [formulas rigorous, conclusion numerical]: explicit cofactors; (FO-r) <=> s * gam_j in D(X) for j = 1..4. Case A (s = 0): (FO-r)
        holds, FO2 bound 8 numerically. Case B (generic; all solutions with dim T_1 = 9): projection = C e_0 + C 1, dimension 2: dead at
        first order in all 20+ solutions; no proof (needs the parametrisation of Case B).
 TABLE  (stage2/r7_table.py): of all saved candidates the only ones passing (FO-r), FO2 and (T2) are of the form X_{ri} + e_i Z_i with
        z_i = 3 (four (3,3) solutions, cross with a in C1); none of the five tested extends to an 8-dim level space.
 z = 3  [rigorous reductions]: for non-isotropic m no other row carries a single-row element (P_2 + verifyfl's SPLIT), so L_i is a NON-SPLIT
        (5,1) space, not two-column (TC5), whose defect function is a first-order variation of N ((FO-r) for row i) -- as for all its
        hyperplanes, which are non-split (4,1) spaces (HYP); no such space is known. Not closed; isotropic m untouched.
 (iii)  corrected as verify2 found; none of my results used the column part; the exceptional case (an identically vanishing entry)
        is listed as (B0), no contradiction found.

## RESULT-R6 (stage2 round 6, 19:13) -- details in sections R6-1 .. R6-7 at the end. (Q-r) is NOT classified; REG1 is NOT proved.
 RIGOROUS: (1) THEOREM (cross family, R6-2): for the 5-dim level subspaces X(a,b) of a cross (one row + one column) with sparse parts of
     dim <= 2 (b != 0, a not in C1), T_1 is explicit (dim 10) and every level space containing X(a,b) has dim <= 7. On the two exceptional
     loci (b = 0; a in C1) X has a 3-dim single-column resp. single-row part and the FO2 bound is 9.
     (2) LEMMA (lam_{rr'} = 5): needs Phi in GL_5 with C(xi) Phi + Phi^T C(xi) = 0 on L_r; impossible if the ten 3x3 subpermanent cubics are
     independent. (3) (T2): the order-2 part of chief's (**) at v -> 0 is a LINEAR condition on T -- a cheap exact test for a candidate L_r.
     (4) z_i = 3 forces four minimal pairs through line i (so the split free line is a sub-case of (B1)) and dim T_1(M_i) >= 10 for the
     8-dim M_i = L_i + e_i Z_i. (5) every single-row element e_i w^T gives the relation 1_{rows != i} (x) w.
 NUMERICAL (all solutions verified on fresh points): census of (Q-r) solutions -- general search 6, inside FK(2,4) 9, FK(3,3) 7, FK(1,5) 1.
     Every solution found vanishes on a block s x t with s + t >= 6. After FO2 and (T2) the ONLY survivors have a 3-dim sparse part
     (split free line): cross with b = 0 or a in C1, and two FK(3,3) solutions. All solutions with a 3-dim row projection and sparse
     parts <= 2 (the L_r of a minimal pair) have FO2 bound 7 or 8.
 HYPOTHESIS for target (3): "no 3-dim single-row or single-column part in L_r" (forced by (H1) for the crossing family of lines, stage3
     S3-1, or by the exclusion of (5,1) spaces). Under it every candidate found has FO2 <= 8; I have a proof only for the cross family.
 NOT DONE: classification (non-FK solutions of (ii) exist; none found by LM); FO2 on L_r + L_r' for Types I, II, I_0 (no explicit
     candidates for the three other rows); FK(4,2); a proof for FK(2,4) (there dim T_1 = 9 in all 9 solutions).

## RESULT-R5 (stage2 round 5, 18:38) -- details in sections R5-1 .. R5-7 at the end. The theorem for REG1 is still NOT proved.
 (FO-M*) THEOREM [structural proof + exact parameter-free certificate]: T_1(M*) = W_7 (+) C(1 e_0^T - J/5) has dimension 8 for ALL parameters;
         W_7 = full free column + 3-dim strongly level part, M* a hyperplane of it. Corollary: every level space containing M* has dim <= 7.
 (R5-2)  Cases A and B of family (alpha) are now HAND proofs: inside family (alpha), N2 forces L_a + L_b = M*. With (FO-M*): family (alpha)
         is excluded at dimension 9 rigorously. Still numerical: that every diagonal block with a two-row column lies in family (alpha)
         (and I found a parameter count showing that isolated solutions could have been missed by the survey).
 (FO2)   LEMMA [rigorous] + applications [numerical]: L is totally isotropic for q_m = D^2 perm(J+m) on T_1(M), so
         dim L <= dim T_1(M) - ceil(rank/2). Reproduces "maximal" for all 7 known spaces. Excludes at dimension 8 and 9: all 26 generic
         non-diagonal level N2 blocks found (bound 7, from the 4-dim block alone), M* (7), and both admissible candidates for L_r (7).
 (Q-r)   UNIFORM FORMULATION: for every line with full projection, L_r is a 5-dim level space of 4x5 matrices with all 4x4 subpermanents
         identically zero, row/column projections of dim <= 3, and FO2 bound >= 9. Only 2 such candidates found (both cross-like, both
         fail FO2); the survey is thin.
 NEW INPUT: stage3's Theorem N2-X / Theorem N (not yet verified) removes N2 altogether; my N2 results are an independent confirmation on
         the sub-families. REMAINING in REG1: (B1) a minimal pair (then L contains the 8-dim level space L_r + L_r'); (B2) single-row and
         single-column elements with z <= 2. FO/FO2 on (B1) not done: no explicit candidates (the pair classification lives on the
         relation side). What carries over to a_r >= 2: section R5-6 C.

## RESULT-R4 (stage2 round 4, 18:00) -- regime REG1 := all a_r = b_c = 1 without zero-freeness. Details: sections R4-1 .. R4-6 at the end.
 The theorem for REG1 is NOT proved. Delivered: three rigorous reductions, one explicit obstruction, and the list of survivors.
 (N2-Z)  LEMMA [hand proof]: moment problem with zero weights. If every column of the N2 block has 3, 1 or 0 nonzero weights (every
         kappa'^j has at most one zero among the rows c,d,e), the block is (alpha1) or (alpha2): one column with entries sigma(p_i) and
         its two dominoes, the other columns proportional to one form mu.
 (N2-Z') THEOREM [hand proof; direct numerical confirmation]: N2 with a block (alpha1) or (alpha2) is impossible (vanishing of all 4x4
         subpermanents on L_a). So N2 is impossible whenever every column annihilator has at most one zero among c,d,e -- in particular
         for zero-free column annihilators with ARBITRARY row annihilators (Lemma N2-GEN no longer needs "no single-column element").
         Corollary: all a_r = 1, lam >= 3, column annihilators with at most one zero each => single-row element (uses stage3's N1).
 (M*)    EXPLICIT 6-dim LEVEL SPACE [exact integer check] of the N2 shape for L_a + L_b (block (alpha3)): the level condition and
         the vanishing subpermanents on L_a, L_b do not exclude N2. M* contains a split free column (3-dim space of single-column elements).
 (FO)    [added 18:04; section R4-6] FIRST-ORDER EXTENSION TEST: every level space containing M* lies in T_1(M*) := {t : D_t perm(J + m) = 0
         for all m in M*}, and dim T_1(M*) = 8 (exact rank 17 at one parameter set; rank 17 at 409 further parameter sets incl. the
         special loci). So M* lies in NO 9-dim level space: N2 with a diagonal block is impossible at dim 9 [num-assisted: the
         classification of two-row-column blocks and "Case B" for Xi with zeros are numerical; the parameter scan is not a proof for
         all parameters]. This does not use the (5,1) conjecture.
 (Z3)    single-row elements are a defect phenomenon: z_r <= 4 - e(L_r); in REG1 z_r <= 3, and z_r = 3 => L_r is a (5,1) space and L contains an 8-dim
         level space with a deletable line (rows' open (DI_5) at e = 1; TC5 covers two-column defect lines).
 SURVIVORS in REG1: (S-I) minimal pairs with a zero in the annihilators involved; (S-II) single-row/column elements with z = 1, 2 (and
         z = 3 = the (5,1) problem); (S-III) N2 with a non-diagonal block (some kappa'^j with >= 2 zeros among c,d,e, the column carrying
         two independent forms; extreme case: two identically vanishing cells). No uniform kill found for these three; the first-order
         extension test (FO) is the candidate uniform tool: build the forced sub-configuration, compute dim T_1, compare with 9.
 Correction to my round-3 handback text: the survey count sentence was garbled; the correct numbers are 346 solutions = 335 with a zero
         or infinite weight + 11 with a unit vector in P + 0 genuine.

## RESULT-R3 (stage2 round 3, 16:37; HEADLINE UPDATED 16:59) -- details in sections R3-1 .. R3-5 at the end
 HEADLINE (16:59): THEOREM GEN -- "a 9-dim level space cannot be fully generic" (GEN: all a_r = b_c = 1, all row and column FK
 annihilators zero-free) -- now has a COMPLETE PROOF CHAIN, but it is CONDITIONAL on two inputs that are not fully rigorous/verified:
   (a) my R3-1 (exception triples; num-assisted) -> GEN-6 (lam >= 3 for all row pairs);
   (b) stage3's round-3 section 16 (all a_r = 1, lam >= 3, no single-row element => all lam = 3 [Theorem N1: impossible] or the
       rigid family N2; hand proof + exact rank checks, "not yet independently verified" by stage3's own label).
   New here (section R3-5): LEMMA N2-GEN [hand proof, every step re-checked; numerically corroborated]: stage3's family N2 is
   impossible when the column annihilators are zero-free. Mechanism: X_ab = {(pi_c; a o pi_d; b o pi_e): pi_i in P, sum pi_i = 0} for ONE
   2-plane P and the weights a = K'_c/K'_d, b = K'_c/K'_e; the level condition on this 4-dim block alone is a moment problem
   (sum c_j lam_j^r = sigma^r for seven weight/degree pairs) which has no solution with zero-free weights and no unit vector in P.
 The text below (16:37) is the state BEFORE stage3's round-3 result and Lemma N2-GEN; it remains correct, and (E), (GEN-6) are inputs:
 GEN (all a_r = b_c = 1, all annihilators zero-free) was reduced to stage3's non-minimal regime (R3) on both the row and column side:
 (E)    The exception triples of (S2) are impossible [num-assisted: floating-point enumeration of the admissible fifth annihilators
        (132 configurations: 120 have none, 12 have one family each) + hand computation that every member of these 12 families
        violates the cube condition perm_3 = k ell^3; confirmed numerically]. Hence (S2*): ANY three rows with a = 1 and zero-free
        annihilators have X_ijk != 0 (no Type II proviso).
 (GEN-6) GEN => no minimal pair: lam >= 3 for all ten row pairs and all ten column pairs  [(E) + GEN-2].
 (Y3),(Y5) two general factorisation lemmas for 2-row elements (rigorous, tested on the examples); (GEN-7): in GEN a 2-row
        element spanning Y_ab (m_ab = 1) never has full column support.
 (GEN-8) stage3's configuration (II) (twisted partial free column) is impossible in GEN when some pair of its four rows has
        m = 1 [rigorous]; with stage3's MIN-C: GEN is not in the minimal case.
 REMAINING IN GEN at 16:37: all lam >= 3, and (some row lam >= 4 or some row m >= 2) and (some column lam >= 4 or some column m >= 2).
 [16:59: closed by stage3's N1/N2 reduction + Lemma N2-GEN, conditional on (a), (b) above.]
 One correction this round: the round-1 survey of exception configurations (21 survivors) used too weak an admissibility
        test and only part of the column triples; the corrected survey is stage2/r3_survey.py.

## RESULT-R2 (stage2 round 2, 16:02) -- headline of round 2 (details: sections R2-1 .. R2-5 at the end)
 (GEN-2) THEOREM [rigorous]. Let L be a 9-dim level space in the FULLY GENERIC regime GEN (all a_r = b_c = 1, all row and column
      FK annihilators zero-free). Then L has NO minimal Type I row pair and NO minimal Type I column pair; more generally no
      minimal pair (r,r') whose plane X_{rr'} meets all three {row i = 0} ("triangular"). Every minimal pair of L is a Type II
      pair with X_{rr'i} = 0 for some third row i, i.e. it lives in a (II,II,lam=3) exception triple of (S2).
      Mechanism: X_{rr'} is rank one in column-weighted coordinates (S2-d); the quadratic part of perm(u + x) = perm(u)
      factorises on suitable linear subspaces of L^ as (linear form) x (quadratic form in rows r,r'); zero-free column
      annihilators kill the linear factor; the quadratic factor vanishing contradicts dim(L cap {column d = 0}) = 5
      (|Sigma| = 3) or the explicit annihilators of I^_{rr'} (|Sigma| = 4: sigma_0 != 0 resp. y != -1).
 (GEN-3) LEMMA: in GEN a 2-row element opposite to a minimal pair has column support of size 2, 3 or 5, never 4.
 (ONE ZERO) First non-generic layer [rigorous + exact]: if kappa^r has exactly one zero entry (kappa^r' zero-free) a minimal pair
      is of "Type I_0" (Type I with the zero column inside one block; the zero column is FREE in row r; no Type II), and (T1)
      extends: three rows, one zero entry in one annihilator, all pairs minimal => X_123 != 0 (1036 configurations, exact).
 NOT achieved in round 2: "a 9-dim level space cannot be fully generic" (missing: non-triangular Type II pairs and the regime
      all lam >= 3); item O2 (the 21 Type II / Type II configurations) in general; two minimal pairs + lam = 3 in the one-zero layer.
 Two intermediate claims of mine were WRONG and are withdrawn (both caught by sanity scripts): "(Z-0): E empty" (round 1) and
      "for |Sigma| = 3 two rows of G coincide" (round 2).

## RESULT (stage2, 15:21; last update 15:26) -- Stage 2 is NOT closed (minimal row pairs are not excluded), but its PURPOSE is reached in the
## main case by a new route: "triples instead of pairs".  All statements rigorous unless marked [num].
 Setting: L level, dim L = 9, L^ = CJ + L, a_r = 5 - dim pi_r(L), X_{rr'} = L cap {rows r,r' = 0}, minimal pair := dim X_{rr'} = 2.
 (V)  Chief's C4, C7, C7'' re-derived by hand: CORRECT, no error. C4 does not need zero-free annihilators, and it extends
      to the mixed minimal pair (a_r,a_r') = (2,1): in EVERY minimal pair all 3x3 subpermanents vanish on the plane X_{rr'}.
 (G)  Unified pair criterion with zero entries allowed (2x2 matrices Gamma_T; section 2), machine-checked.
 (TAU) In coordinates tau_i = kappa^i o u_i the minimal types are kappa-free (section 3): on L every row has weighted sum 0 and
      Type I  <=> the weighted partial sums over a column block C of the two rows agree;
      Type II <=> (partial sum of row i over Q_3) + (partial sum of row i' over Q_2) = 0  (three cells Q_1,Q_2,Q_3).
 (T1) Three rows with a = 1 and zero-free annihilators whose three pairs are ALL minimal have a common kernel element:
      X_123 != 0.  [EXACT: 3x2 zero-block factorisation on I_3 = pi_123(L^) + exact Q / Q(i) linear algebra over all 3108
      type configurations (t5_triple_all.py; the 2080 all-Type-II ones with the full cube test, t10_typeII_exact.py) + a hand elimination for the one surviving "cyclic
      Type II" family, which contradicts J in L^.]
 (T2) Two minimal Type I pairs (1,2), (1,3) and dim X_23 = 3: again X_123 != 0.  [hand proof, section 4]
 (T2'') A minimal Type I pair (1,2), a minimal Type II pair (1,3) and dim X_23 = 3: again X_123 != 0.  [hand proof, section 5b]
 (S2) COROLLARY (fully rigorous). Let rows i,j,k have a = 1 and zero-free FK annihilators. If X_ijk = 0 then the triple has
      EXACTLY two minimal pairs, BOTH of Type II, sharing a row, and the third pair has dim X = 3.  In particular:
      (a) a minimal Type I pair (r,r') and ANY third row r'' with a = 1 (zero-free) have X_{rr'r''} != 0: the plane X_{rr'}
          contains a nonzero element whose row r'' vanishes;
      (b) if all five rows have 4-dim projections with zero-free annihilators and no minimal pair is of Type II, then EVERY
          triple of rows kills a nonzero element of L, i.e. every pair of rows carries a nonzero 2-row element of L.
      This is exactly what "lam_{rr'} >= 3 for all pairs" was meant to deliver to Stage 3 -- obtained without excluding Type I.
 (S2-c) Hence the plane X_{12} of a Type I pair (rows 3,4,5 with a = 1) has a common zero row, or contains a single-row
      element, or is {(mu' p'; mu p; (mu-mu') q)} with all 3x3 subpermanents of (p';p;q) zero.
 (S2-d) GENERIC REGIME "GEN" (all a_r = b_c = 1, all row AND column FK annihilators zero-free; then stage3's (SR) excludes
      single-row elements).  For a minimal Type I pair (1,2) the plane X_12 is a TRIANGLE of 2-row elements
      x_3 + x_4 = x_5 (x_i with rows 1,2,i zero), and in column-weighted coordinates (t_ij -> kappa'^j_i t_ij, kappa'^j = FK
      annihilator of column j) it is RANK ONE:   X_12 = { c zeta^T : c supported on rows 3,4,5, sum c = 0 }  for one vector
      zeta in C^5 with |supp zeta| >= 3, sum_j (kappa^i_j / kappa'^j_i) zeta_j = 0 (i = 3,4,5), and perm[(1/kappa'^j_i)] = 0 on
      rows 345 x any three columns of supp zeta.  (section 7)
 (M)  A minimal Type I pair (1,2) and a row 3 with a_3 = 2: (1,3) and (2,3) cannot both be minimal (Type I' would force
      K_1 = K_2 = 1/2, but Type I needs K_1 != K_2).
 [num] Two minimal Type II pairs sharing a row, third pair with lam = 3, X_123 = 0 (t8_two_minimal.py, floating point,
      necessary conditions only): 1668 excluded by a dimension count, 111 killed, 21 canonical configurations survive.
      (The same survey reproduces (T2), (T2'') numerically: all (I,I), (I,II), (II,I) configurations are killed.)
 [num] For all-Type-I minimal triples dim X_123 = 1 is NOT excluded by the same necessary conditions (75 of 105 pairs of
      partitions admit a sixth annihilator; t11_lam3.py), so "X_123 = X_12" could not be forced.
 Sanity: the 3x2-block factorisation (T0) holds on L080, ex1, ex2, ex3, two s-family members, K + E_0 (676 cases, 0 violations);
      Type I / II tau-forms pass the ThB pair test (15 + 300 structures); T1 reproduced numerically on synthetic Type I
      annihilator data at random kappa (105 pairs of partitions, each with >= 3 violating column triples).
 STILL OPEN (exact list):
  O1 the minimal pairs themselves: Type I, Type II (zero-free (1,1) pairs) and Type I' ((2,1) pairs) are not excluded; what is
     excluded is X_123 = 0 for the triples listed in (T1), (T2), (T2''), and the combination (M);
  O2 two minimal Type II pairs sharing a row, third pair lam = 3, X_123 = 0: OPEN (21 canonical configurations survive the
     necessary conditions of t8_two_minimal.py); this is the only way a zero-free a = 1 triple can have X_123 = 0;
  O3 annihilators WITH zero entries: no classification (the criterion (G) is ready; first consequences (Z-0), (Z-1) in section 6); the
     tau-coordinates need zero-free kappa, so (T1), (T2) do not cover such rows;
  O4 rows with a_r >= 2: only C8 (chief), the extension of C4, and (M); triples containing such a row are open;
  O5 pairs with dim X_{rr'} >= 3 are not constrained at pair level (dim Pi_T can be 1); they enter only through the count
     lam_ij + lam_ik <= 5 when X_ijk = 0.
 Files: stage2/pairlib.py, exactla.py, t1_verify.py (criterion), t2_triple.py (numeric T1), t3_triple_exact.py (Type I exact),
  t4_typeII_pair.py, t5_triple_all.py (exact, all types), t6_typeII_full.py, t10_typeII_exact.py (Q(i) exact), t7_sanity.py,
  t8_two_minimal.py, t9_cyclic.py, t11_lam3.py, t12_zeros.py, t13_T2pp.py (exact cubic identities of T2, T2'').  Every run < 30 s.
  Round 2: r2_onezero.py, r2_triple_onezero.py (exact), r2_gen_lemmas.py, r2_lemmaH.py, r2_gen2_check.py, r2_block_rank.py.
  Round 3: r3_survey.py (corrected exception survey), r3_cube2.py, r3_hand_check.py, r3_generic_fail.py, r3_Y3.py, r3_Y5.py
   (r3_leaves*.py, r3_two_minimal.py, r3_cube.py: exploratory; r3_cube.py and one r3_cube2.py run took 2m43s / 1m12s).
STATUS 14:50: BRIEF + NOTES-chief (all, incl. C7'', C8, section 7) read. Re-derived C4, C7 by hand (correct; details below).
 Working on: unified pair-level criterion (zeros allowed), cubic-level consequences (G = 0 on L_r), Types I / II / I'.
STATUS 15:03: (a) C4, C7, C7'' re-derived by hand: CORRECT (no error found); unified pair criterion with zeros (Gamma_T) proved and
 machine-checked (stage2/t1_verify.py: Type I passes for all 15 partitions; closed form agrees with the direct ThB test on
 3951 random degenerate data). (b) NEW: "tau-coordinates" make Type I kappa-free; TRIPLE THEOREM (T1 exact rational computer
 check of 210 sign configurations, T2 hand proof): three rows with 4-dim projections whose minimal pairs are of Type I always
 have a common kernel element: X_{rr'r''} != 0. Writing proofs; next: Type II in triples, Type I', zeros.

## 1. Verification of chief's C4 / C7 / C7'' (all re-derived by hand; no error)
 C4 (B_x = 0 on the plane X_{rr'} of a minimal (1,1) pair): a quadratic form z_1^T C z_2 vanishing on the codim-2 space I^ has
   rank <= 4, so rank C = 2, C = a b^T + b a^T with disjoint supports; I^ is the preimage of a maximal isotropic plane of
   alpha_1 beta_2 + beta_1 alpha_2 (alpha_i = z_i.a, beta_i = z_i.b); the family {alpha_1 = mu beta_1, alpha_2 = -mu beta_2} and
   the members mu = 0, infinity of the other family contain an annihilator supported on ONE row, impossible as both row
   projections of I^ are onto; the rest is as in chief's text. The proof does NOT use that kappa, kappa' have no zeros.
   ADDITION: the same holds for the mixed minimal pair (a_r, a_r') = (2,1), dim X = 2 (chief's C8 setting): there
   I^perp = span{(n,0),(kappa*,-kappa')} contains no element (0,n') and only the line C(n,0) of elements (n'',0); both members
   mu = 0, infinity of family 1 need a 2-dim space of one-row annihilators, the general member of family 1 needs none (but
   (n,0) is one), family 2 needs one of each kind. Hence B_x = 0 for all x in X_{rr'} in EVERY minimal pair (dim X = 2).
 C7'' (only Types I, II): re-derived: sigma-classes have <= 2 distinct points (rho_j,rho'_j); two points on an anti-diagonal
   admit as third point only one of the two corners (both corners would force y = y'); no anti-diagonal pair => all points on
   an axis-parallel line => rho or rho' constant. Correct.

## 2. Unified pair criterion (zeros allowed) [rigorous; machine-checked]
 Minimal (1,1) pair: I^perp = span{(kappa,-kappa'),(nu,nu')}. For T = {j,l} put p_i = (kappa_i,nu_i), p~_i = (-kappa'_i,nu'_i) in C^2
 (then sum_i (p_i + p~_i) = 0 encodes (1,1) in I^), R_T = [p_j p_l p~_j p~_l] (2x4), Gamma_T = p_j p~_l^T + p_l p~_j^T (2x2),
 G_T = sym(Gamma_T), a_T = (Gamma_12 - Gamma_21)/2. Then ThB for T is equivalent to:
   (i)  rank R_T <= 1  =>  (kappa_j,kappa_l,0,0) in rowspace(R_T)   [dim Pi_T >= 3 forces ell = 0 on Pi_T];
   (ii) rank R_T = 2 and (kappa_j,kappa_l,0,0) not in rowspace (type B1)  =>  G_T != 0, det G_T = 0, and (a_T = 0 or
        G_11 = G_12 = 0).   [G_T is the Gram matrix of q_T^{-1} on Pi_T^perp; rank q_T|Pi_T = rank G_T; the radical vector
        is the q-dual of c_1 R_1 + c_2 R_2 with G c = 0 and ell of it equals a_T c_2.]
 With no zeros this reproduces C7' (G_11 = -kappa_j kappa_l (omega_j+omega_l), ...). Not carried out: the full list of
 solutions with zero entries (see open list).

## 3. tau-COORDINATES: the minimal pair types become kappa-free  [rigorous]
 For a row i with a_i = 1 and kappa^i without zeros put tau_i := kappa^i o u_i (entrywise), f_i := sum_j tau_i(j). Then
 f_i = ell on L^ (FK annihilator), and for a minimal pair (i,i') (dim X_{ii'} = 2) the second relation of I^_{ii'} reads
   TYPE I  (columns = C + C^c):           sum_{j in C} (tau_i(j) - tau_i'(j)) = sigma_0 ell,   kappa^i' = c w kappa^i, w = +1 on C, -1 on C^c;
   TYPE II (cells Q_1,Q_2,Q_3, eps = +-1): sum_{Q_3} tau_i + sum_{Q_2} tau_i' = -y ell, y = (-1 + eps i)/2,
                                          kappa^i' = c w kappa^i, w = eps*i on Q_1, 1 on Q_2, -1 on Q_3.
 So ON L:  every row has weighted sum 0;  Type I: the weighted partial sums over the block C of the two rows AGREE;
 Type II: (partial sum of row i over Q_3) + (partial sum of row i' over Q_2) = 0.  (This is the "two-block structure" in its
 cleanest form: Ann(L) contains K o (e_i 1_C^T - e_i' 1_C^T), K = matrix of the FK annihilators.)  The set of Type II
 structures is symmetric under exchanging the two rows (Q_2 <-> Q_3). Both forms machine-checked against the ThB pair test
 (stage2/t1_verify.py: 15 partitions; t4_typeII_pair.py: all 300 Type II structures pass, wrong sign of y fails).
 Permanents: z_ij = tau_ij / kappa^i_j, so for rows i with kappa^i = c_i w_i kappa^1 (w_i with entries in {+-1,+-i}) and a column
 set S:  perm(u[rows; S]) = const * perm( (tau_ij / w_i(j)) ),  const != 0.   Everything below is linear algebra over Q(i).

## 4. TRIPLE THEOREM  [T1: exact computer check, rational/Gaussian arithmetic; T2: hand proof]
 Setting: dim L = 9, rows 1,2,3 with a = 1 and zero-free kappa^1 (then all minimal pairs among them are of Type I or II and all
 three kappa's are zero-free), X_123 := L cap {rows 1,2,3 = 0} (2-row elements), lam_ii' = dim X_ii'.
 (T0) I_3 := pi_123(L^) has dim 10 - dim X_123, and for a column triple S: U_S := {u in L^: rows 1,2,3 supported in S},
      Pi_S = I_3 cap C^{3xS} = U_S / X_123, and ZBF (3x2 zero block): perm(u) = perm(u[123;S]) perm(u[45;S^c]) on U_S. Hence
        ell != 0 on Pi_S  =>  perm_3 = k ell^3 on Pi_S (k != 0), in particular perm_3 = 0 on Pi_S cap ker(ell);
        ell  = 0 on Pi_S  =>  U_S in L and (perm_3 = 0 on Pi_S  or  perm(u[45;S^c]) = 0 on U_S).
 (T1) ALL THREE PAIRS MINIMAL and X_123 = 0 is impossible if at least one pair is of Type I; if all three are of Type II it
      is impossible except for ONE configuration (up to column permutations / complex conjugation): the CYCLIC TYPE II
      triple: columns = A + B + C,  w_2 = (i,1,-1), w_3 = (-1,1,i) on (A,B,C), and on L
            sum_C tau_1 + sum_B tau_2 = 0,   sum_A tau_1 + sum_B tau_3 = 0,   sum_A tau_2 + sum_C tau_3 = 0.
      Proof. If X_123 = 0 then dim I_3^perp = 5 and I_3^perp contains the 5 functionals f_1-f_2, f_1-f_3, g_12 - s_12 ell,
      g_13 - s_13 ell, g_23 - s_23 ell (g = the pair relations of section 3). Whenever the six functionals f_1,f_2,f_3,g_12,
      g_13,g_23 restricted to C^{3xS} are independent, these five are independent (so they span I_3^perp), ell != 0 on Pi_S
      for EVERY value of the constants s_ii', and Pi_S cap ker(ell) is the common kernel of the six (3-dim, defined over Q).
      By (T0) perm((tau_ij/w_i(j))) must vanish identically on that kernel.  stage2/t3_triple_exact.py (Type I only: all
      210 pairs of partitions) and t5_triple_all.py (canonical (1,2)-structure x all 315 (1,3)-structures x all admissible
      (2,3)-structures: 3108 configurations with admissible ratio kappa^3/kappa^2, exact Fractions / Gaussian units) find
      in every configuration with a Type I pair a triple S with independent functionals and a point of the kernel where
      the permanent is != 0  [(I,I) 28/28, (I,II) 760/760, (II,I) 120/120 killed].  For all-Type-II triples the constants
      s = -y are universal, so I_3 is completely explicit; the full cube test (t6_typeII_full.py, floating point, 2080
      configurations) leaves exactly the cyclic family (6 canonical members = the 6 compositions of 5 into block sizes);
      there perm_3 = k ell^3 does hold (|k| = 0.707) for S meeting A, B, C once each and ell = 0, perm_3 != 0 on Pi_S for the
      other S (so perm(u[45;S^c]) = 0 on U_S is forced there).   [all-II part: numerical survey, not exact]
 (T2) EXACTLY TWO MINIMAL PAIRS (1,2), (1,3), BOTH OF TYPE I, and X_123 = 0 is impossible.  [hand proof]
      X_12 + X_23 direct in L_2 (dim 5) gives lam_23 <= 3; lam_23 = 2 is (T1); so lam_23 = 3, dim I_23^perp = 3, and
      I_3^perp (dim 5) contains N_12 + N_13 (dim 4: look at the row-2 and row-3 components) and I_23^perp (dim 3), whose
      intersection therefore has dim >= 2: some a g^_12 + b g^_13 + x(f_1-f_2) + y(f_1-f_3), (a,b) != 0, has row-1 component
      a 1_{C12} + b 1_{C13} + (...) 1 = 0, so C13 = C12 or its complement; w.l.o.g. C12 = C13 = C (then kappa^2 = kappa^3), and
      I_3^perp = span{f_1-f_2, f_1-f_3, g^_12, g^_13, n**} with n** = (0,m_2,m_3) supported on rows 2,3.
      Take S = {p,q,s} with p in C, q,s not in C (or p not in C, q,s in C). The five known functionals are independent on
      C^{3xS}; K_S := their common kernel with ell = 0 is {tau_i = (t, a_i, -t-a_i), i = 1,2,3} (4-dim), and on K_S
            perm((tau_ij/w_i(j))) = perm[[t,a_1,-t-a_1],[t,-a_2,t+a_2],[t,-a_3,t+a_3]] = 2 t (t a_1 + a_1 a_2 + a_1 a_3 - a_2 a_3),
      t times an IRREDUCIBLE quadric (Gram determinant 1/16 != 0).  If n**|K_S != 0 then ell != 0 on Pi_S and
      Pi_S cap ker ell = K_S cap ker n**, so by (T0) the linear form n**|K_S divides this cubic: n**|K_S is a multiple of t.
      In both cases the coefficients of a_2, a_3 in n**|K_S vanish: m_2(q) = m_2(s), m_3(q) = m_3(s). Hence m_2, m_3 are constant
      on C and on C^c:  n** = (al_2 - be_2) sum_C tau_2 + (al_3 - be_3) sum_C tau_3 + (be_2 + be_3) ell on I_3; with
      sum_C tau_i = sum_C tau_1 - s_1i ell this is (al_2 - be_2 + al_3 - be_3) sum_C tau_1 + const * f_1, a functional of ROW 1
      alone vanishing on I_3; as pi_1(L^) = C^5 it is identically 0, i.e. n** lies in the span of the other four. Contradiction.
 COROLLARY (T). Let rows 1,2,3 have a = 1 and zero-free annihilators, and suppose none of their minimal pairs is of Type II.
      Then X_123 != 0: L contains a nonzero element supported on the other two rows, lying in X_12, X_13 and X_23.
      (If X_123 = 0 then lam_ij + lam_ik <= 5 for all i, so at most one pair has lam >= 3: case (T1) or (T2).)
      This is exactly the conclusion "L_{rr'r''} != 0" that chief's Stage 2 (lam >= 3) was meant to deliver to Stage 3,
      obtained WITHOUT excluding Type I.
STATUS 15:06: sections 3, 4 written (T1, T2, corollary T). Next: mixed cases with Type II when only two pairs are minimal;
 sanity run of (T0) on the exact examples; Type I'.

## 5. Completion of (T1), the case of two minimal pairs with Type II, and consequences
 (T1') THE CYCLIC TYPE II TRIPLE IS IMPOSSIBLE  [hand proof; numerics agree: stage2/t9_cyclic.py, residual floor 0.25-0.45].
      It contradicts J in L^ (tau_i = kappa^i must satisfy the three pair relations). With a, b, c' the sums of kappa^1 over
      A, B, C, kappa^2 = c_2 (i,1,-1) kappa^1, kappa^3 = c_3 (-1,1,i) kappa^1, y = (-1+i)/2:
         a + b + c' = 1,  c_2 (i a + b - c') = 1,  c_3 (-a + b + i c') = 1,  c' + c_2 b = -y,  a + c_3 b = -y,  i (c_2 a + c_3 c') = -y.
      Eliminating a, c':  b(1 - c_2 - c_3) = i;  c_2 (i + b(1 + c_2 - i c_3)) = 1;  c_3 (i + b(1 + c_3 - i c_2)) = 1;
      -y(c_2 + c_3) - 2 c_2 c_3 b = i y.  The difference of the middle two is (c_2 - c_3)(i + b(1 + c_2 + c_3)) = 0; the second
      factor together with the first equation gives b = 0, absurd; so c_2 = c_3 = c, b = i/(1-2c), and the remaining two
      equations become c^2 + i c - (1+i)/4 = 0 and c^2 + 2 i c - (1+i)/2 = 0, whose only possible common root c = (1-i)/4
      gives -i/8 != 0.  Hence:
 (T1) FINAL FORM. Three rows with a = 1 and zero-free annihilators, all three pairs minimal, X_123 = 0: IMPOSSIBLE.
      Status of the proof: 3108 - 32 configurations exact (t5_triple_all.py); 26 all-Type-II configurations only in floating
      point (t6_typeII_full.py: perm_3 is not k ell^3 on some Pi_S with ell != 0; margins O(1)); 6 cyclic ones by (T1').
 (T2') TWO MINIMAL PAIRS (1,2), (1,3), lam_23 = 3, X_123 = 0, with Type II involved [numerical survey, t8_two_minimal.py].
      As in (T2): the row-1 parts of the two pair relations (1_C for Type I, 1_{Q_3} for Type II) must agree up to complement
      (otherwise dim count); then I_3^perp = N_12 + N_13 + C n**, n** on rows 2,3, and for every S on which f_1,f_2,f_3,g_12,g_13
      are independent, n**|K_S is 0 or a linear factor of the cubic perm|K_S; moreover n**|K must not be the restriction of a
      one-row functional of row 1. Result: (I,I): 28 dim count + 2 killed (= the hand proof (T2)); (I,II): 556 + 44 killed;
      (II,I): 84 + 6 killed; (II,II): 1668 dim count, 111 killed, 21 canonical configurations SURVIVE these necessary conditions.
 CONSEQUENCES (rows with a = 1 and zero-free annihilators throughout):
 (S2-a) [superseded by (S2) in the RESULT block: now fully rigorous by section 5b] If a minimal pair (r,r') is of Type I and r'' is a third row with a = 1, then X_{rr'r''} != 0, i.e. the plane X_{rr'}
        contains a nonzero element whose row r'' vanishes.  [rigorous if the other minimal pairs of the triple are of Type I
        or if all three pairs are minimal; numerical ((T2') (I,II)) otherwise.]
 (S2-b) If all five rows have a = 1 with zero-free annihilators and no minimal pair is of Type II, then EVERY triple of rows
        kills a nonzero element of L: every pair of rows carries a nonzero 2-row element of L. [fully rigorous: only (T1) with
        Type I pairs (exact) and (T2) (hand) are used.]  This is the input Stage 3 needs; it replaces "lam >= 3".
 (S2-c) Shape of the plane X = X_{12} of a Type I minimal pair when rows 3,4,5 have a = 1 (from S2-a): X meets each of
        {row 3 = 0}, {row 4 = 0}, {row 5 = 0} nontrivially, so either (alpha) X has a common zero row (a plane of 2-row elements),
        or (beta) X contains a single-row element e_i w^T, or (gamma) X = {(mu' p' ; mu p ; (mu - mu') q)} (rows 3,4,5), three
        fixed vectors p', p, q with all 3x3 subpermanents of the matrix (p';p;q) equal to 0 (by C4).
 (M)  MIXED TRIPLE [rigorous, from C8]: if (1,2) is a minimal Type I pair (partition C) and a_3 = 2 (zero-free N_3-data), then
      (1,3) and (2,3) are NOT both minimal: Type I' for (3,1) and (3,2) gives N_3 = span(kappa^1|_D, kappa^1|_{D^c}) =
      span(kappa^2|_{D'}, kappa^2|_{D'^c}) with block sums 1/2; as kappa^2 = c(kappa^1|_C - kappa^1|_{C^c}) this forces D = D' = C
      (up to complement), hence K_1 = K_2 = 1/2, contradicting c = 1/(K_1 - K_2).
STATUS 15:13: (T1) complete (cyclic Type II family killed by hand), (T2') surveyed, consequences S2-a/b/c and (M) written.
 Next: make the 26 floating-point cases exact if cheap; then final RESULT block and open list.
STATUS 15:17: all-Type-II (2,2,2) triples now EXACT (t10_typeII_exact.py: 2074 of 2080 killed by exact non-cube certificates
 over Q(i); the 6 survivors are the cyclic family, killed by hand in (T1')). lam_3 = 1 survey done (not excluded). RESULT
 block written at the top.

## 5b. (T2'') Type I + Type II sharing a row  [hand proof; cubic identities checked exactly, stage2/t13_T2pp.py]
 Setting: (1,2) minimal of Type I (block C), (1,3) minimal of Type II, dim X_23 = 3, X_123 = 0. As in (T2), I_3^perp (dim 5)
 contains N_12 + N_13 (dim 4) and I_23^perp (dim 3), so some combination of the two pair relations has no row-1 part:
 1_{Q_3} = 1_C or 1 - 1_C; Type I is symmetric under C <-> C^c, so C = Q_3, D := C^c = Q_1 + Q_2, and
 I_3^perp = N_12 + N_13 + C n**, n** = (0,m_2,m_3). On K := {ell = 0} cap (N_12 + N_13)^perp:
      sum tau_i = 0 (i = 1,2,3),   sum_C tau_1 = sum_C tau_2 = - sum_{Q_2} tau_3.
 Take S = {p,q,s}, p in C, q in Q_1, s in Q_2 (exists always). The five functionals are independent on C^{3xS},
 K_S = { tau_1 = (t,a_1,-t-a_1), tau_2 = (t,a_2,-t-a_2), tau_3 = (a_3, t-a_3, -t) } and, with the weights 1/w
 (row 2: (+,-,-), row 3: (-1, -eps i, 1)),
      perm|K_S = (a_2 - a_1) t [ t - eps i (t - a_3) ] - a_3 [ t(a_1 + a_2) + 2 a_1 a_2 ]  =: c.
 c is IRREDUCIBLE: a linear factor lam restricts on {a_3 = 0} to a factor of (1 - eps i)(a_2 - a_1) t^2 and on {t = 0} to a
 factor of -2 a_1 a_2 a_3 (neither restriction of c vanishes); lam|{a_3=0} ~ t gives lam = al t + ga a_3 with al ga != 0, and
 on a_3 = theta t the monomial -2 theta t a_1 a_2 of c survives; lam|{a_3=0} ~ a_2 - a_1 gives lam|{t=0} with both a_1 and a_2:
 impossible. Hence (argument of (T2)) n**|K_S = 0 for all such S:
      m_2(q) = m_2(s),   m_3(p) = m_3(q),   m_2(p) - m_2(s) + m_3(q) - m_3(s) = 0     (p in C, q in Q_1, s in Q_2).
 So m_2 = al on C, al' on D; m_3 = be on C + Q_1, be' on Q_2, with al - al' + be - be' = 0, and on K
      n** = (al - al') sum_C tau_2 + (be' - be) sum_{Q_2} tau_3 = (al - al' + be - be') sum_C tau_1 = 0,
 i.e. n** lies in N_12 + N_13 + C ell, hence in N_12 + N_13: contradiction with dim I_3^perp = 5.  QED
 (Also checked exactly: the cubics for S = {p in C; q,s in Q_2} and {p,p' in C; q in Q_2} are -2t x (irreducible quadric), for
 S = {p in C; q,s in Q_1} it is -2 b a_1 a_2; not needed.)
 PROOF OF (S2): X_123 = 0 gives lam_ij + lam_ik <= 5 inside the 5-dim L_i, so at least two pairs are minimal and a third
 pair, if not minimal, has lam = 3. Three minimal pairs: (T1). Two minimal pairs (they share a row): (I,I) is (T2), (I,II)
 is (T2''); only (II,II) is left.

## 5c. Hand-checkable instance of (T1)
 C12 = {1}, C13 = {2} (so C23 = {3,4,5}), S = {1,2,3}: the six functionals are the three row sums, tau_1(1) - tau_2(1),
 tau_1(2) - tau_3(2), tau_2(3) - tau_3(3); common kernel: tau_1 = (x,y,-x-y), tau_2 = (x,b,-x-b), tau_3 = (x+b-y, y, -x-b);
 signs (+,+,+), (+,-,-), (-,+,-); at (x,y,b) = (1,0,1): perm[[1,0,-1],[1,-1,2],[-2,0,2]] = -4 != 0, while ell != 0 on Pi_S.

## 6. Zero entries: what the criterion (G) gives at once  [rigorous; sanity stage2/t12_zeros.py]
 Minimal (1,1) pair, E := {j : kappa_j kappa'_j != 0}, Z_0 := {j : kappa_j = kappa'_j = 0}, omega = kappa'/kappa, rho = nu/kappa,
 rho' = nu'/kappa', sigma = rho + rho' on E.
 (Z-0) If j in Z_0 and nu_j = nu'_j = 0 (column j free in both rows) then sigma_l != 0 for every l in E (otherwise
       Pi_{j,l} is 3-dim with ell != 0).   [an earlier stronger claim "E is empty" was WRONG and is withdrawn]
 (Z-1) If j in Z_0 and (nu_j,nu'_j) != 0 then for every l in E the pair {j,l} is of type B1 with G_11 = 0, hence
       nu'_j / nu_j = omega_l  and  sigma_l != 0:  omega is CONSTANT on E (no pair of E is separated by both rho and rho').
 (Z-2) Inside E the four pair rules of C7' hold verbatim, but rho, rho' need not be non-constant on E any more, so besides
       Types I, II restricted to E also "all points on an axis-parallel line" and "one point" occur. Full list: not done.
STATUS 15:21: (T2'') proved by hand (one irreducible cubic), so (S2) is fully rigorous; RESULT block updated; zero-entry
 consequences (Z-0), (Z-1) recorded (one wrong intermediate claim caught by the sanity script and withdrawn).

## 7. (S2-d): the plane of a Type I pair in the generic regime GEN  [rigorous, given stage3's (SR): a single-row element
##    e_a w^T with w_j != 0 forces a sum-1 annihilator of column j vanishing at a]
 GEN: all a_r = b_c = 1, all kappa^r and all column annihilators kappa'^c zero-free. Then L has no single-row element (SR).
 Let (1,2) be a minimal Type I pair, X = X_12 (plane, rows 3,4,5). By (S2)(a), V_i := X cap {row i = 0} != 0 for i = 3,4,5.
 V_i cap V_i' consists of single-row elements, so it is 0; three nonzero subspaces of a plane with pairwise zero
 intersections are three distinct lines C x_3, C x_4, C x_5, and after scaling x_5 = x_3 + x_4:
      x_3 = (0;p;q), x_4 = (p';0;-q), x_5 = (p';p;0)   (rows 3,4,5),   X = {(mu' p'; mu p; (mu - mu') q)}.
 Every column j of every x in X is orthogonal to kappa'^j, i.e. kappa'^j_3 mu' p'_j + kappa'^j_4 mu p_j + kappa'^j_5 (mu - mu') q_j = 0
 for all mu, mu'. With zeta_j := kappa'^j_4 p_j this gives p_j = zeta_j / kappa'^j_4, q_j = - zeta_j / kappa'^j_5, p'_j = - zeta_j / kappa'^j_3:
      x(c)_ij = c_i zeta_j / kappa'^j_i   (i = 3,4,5; c = (-mu', mu, mu' - mu), sum c = 0).
 Row annihilators: sum_j kappa^i_j zeta_j / kappa'^j_i = 0 (i = 3,4,5). C4 (all 3x3 subpermanents vanish on X):
 c_3 c_4 c_5 zeta_j zeta_l zeta_m perm[(1/kappa'^{j'}_i)]_{i in 345, j' in {j,l,m}} = 0. A 2-row element in GEN has >= 2 nonzero
 columns (a one-column element (xi kappa'^j_b e_a - xi kappa'^j_a e_b) e_j^T violates <kappa^a, x_a> = 0), so |supp zeta| >= 2.
 P_2 = 0 on X is equivalent to s_i s_i' = sum_j zeta_j^2 / (kappa'^j_i kappa'^j_i') for the three pairs i < i' in {3,4,5},
 s_i := sum_j zeta_j / kappa'^j_i.   No contradiction derived from these alone.
STATUS 15:24: (S2-d) added (uses stage3's (SR)); stage3 and rows notes read (stage3 already uses (S2) as its hypothesis (H2)).
 Final report follows.
 ADDENDUM to section 7: |supp zeta| >= 3. If supp zeta = {j,l}, X is a plane of 3x2-block matrices x(c)_ij = c_i zeta_j g_ij
 (g_ij := 1/kappa'^j_i) and P_2(x(c)) = zeta_j zeta_l sum_{i<i'} c_i c_i' (g_ij g_i'l + g_il g_i'j) = 0 on {sum c = 0}; a form
 sum_{i<i'} M_ii' c_i c_i' vanishing on that plane has all M_ii' = 0, so r_i + r_i' = 0 for the three pairs (r_i := g_il/g_ij != 0),
 which forces r = 0. Hence each of x_3, x_4, x_5 has >= 3 nonzero columns, so (stage3, GEN) Q_x != 0 for them: every such
 Type I pair produces "bad" 3x2 blocks for the row triples (1,2,i), i = 3,4,5 -- the place to look for the final contradiction
 in GEN (not done).
STATUS 15:26: addendum |supp zeta| >= 3 written. Handing back.

# ROUND 2 (start 15:29, budget 75 min -> ends ~16:44)
STATUS 15:35: round-2 brief + stage3 sections 2-9 read. Working on: (3) one zero entry (pair classification done by hand,
 being machine-checked), then extension of (T1) to that layer, then (1)/(2).

## R2-1. First non-generic layer: ONE zero entry  [rigorous hand proof + machine check, stage2/r2_onezero.py]
 Minimal (1,1) pair (r,r'), kappa := kappa^r has exactly one zero entry kappa_{j0} = 0, kappa' := kappa^{r'} zero-free; E := the other
 four columns. Criterion (G) for T = {j0,l}, l in E (R_T has rank 2, G_11 = -kappa_l kappa'_{j0} != 0, so B1 needs a_T = 0 and
 det G_T = 0):  either  (al) rho'_l = rho'_{j0} and [nu_{j0} = -kappa'_{j0} sigma_l / omega_l (B1)  or  nu_{j0} = 0, sigma_l != 0 (not B1)],
                or      (be) rho'_l != rho'_{j0}, rho_l = -rho'_{j0}, nu_{j0} = 0.
 If nu_{j0} != 0 every l is of kind (al), so rho' is constant and (kappa',nu') dependent: impossible. Hence nu_{j0} = 0: COLUMN j0
 IS FREE IN ROW r ((e_{j0},0) lies in pi_{rr'}(L): some t in L has t_r = e_{j0}, t_{r'} = 0). Gauge rho'_{j0} = 0: every point
 (rho_l,rho'_l), l in E, lies on the axes; rho must be non-constant on E and rho' not identically 0 on E; the C7' rules inside E
 leave only two points (x,0), (0,x) on an anti-diagonal (the L-shape would need the corner (0,0) with sigma = 0, impossible;
 an axis-parallel line makes rho or rho' constant). Result:
   TYPE I_0:  E = E_1 + E_2 (both nonempty), kappa' = c kappa on E_1, -c kappa on E_2 (kappa'_{j0} != 0 arbitrary), and on L
              sum_{E_1} tau_r + sum_{E_2} tau_{r'} = 0   (tau = kappa o t, tau' = kappa' o t)   <=>  Type I with block C = E_1 + {j0}.
   Type II does NOT occur in this layer. Checks: all 14 structures pass the ThB pair test; nu_{j0} != 0 or omega != +-c fail;
   a grid search over 19200 candidate data (rho, rho' in {0,1,2}, omega in +-c, nu_{j0}, rho'_{j0} in {0,1}) finds exactly the
   7 Type I_0 structures compatible with the gauge.
 (T1_0) [EXACT, stage2/r2_triple_onezero.py] Rows 1,2,3 with a = 1, kappa^1 with exactly one zero, kappa^2, kappa^3 zero-free, all
   three pairs minimal ((1,2), (1,3) of Type I_0; (2,3) of Type I or II with the forced ratio pattern): X_123 != 0.
   All 1036 configurations (364 with (2,3) of Type I, 672 of Type II) are killed by an exact non-vanishing certificate.
   (Coordinates: tau_1(j0) is a free coordinate, the weights are still units.)  Not done in this layer: two minimal pairs + lam = 3,
   two zero entries, zero in a row with a >= 2.

## R2-2. The fully generic regime GEN (all a_r = b_c = 1, all row and column FK annihilators zero-free)
 K_ij := kappa^i_j, K'_ij := kappa'^j_i (column annihilators). Tools: (SR) no single-row/column elements (stage3); every column j of
 every t in L is orthogonal to kappa'^j.  Call a minimal row pair (r,r') TRIANGULAR if X_{rr'} meets {row i = 0} nontrivially
 for each of the three other rows i. By (S2): Type I pairs are triangular; a Type II pair is triangular unless some triple
 containing it is the (II,II,lam=3) exception.
 (GEN-0) [rigorous] In GEN the block C of a Type I pair has |C| in {2,3}: for C = {j} the relation K_1j t_1j - K_2j t_2j = 0 would
      be an annihilator of column j with zero entries. For |C| = 2 the Type I relation is a relation of L supported on the 2x2
      block {1,2} x C; if the COLUMN pair C is minimal it is of column-Type I with row block {1,2} (column-Type II is
      impossible) and K/K' = gamma [[1,-1],[-1,1]] on the block ("2x2 block duality").
 (GEN-lin) [rigorous] In GEN, if b is supported off column d and (u_i.b) u_{i'd} + u_{id} (u_{i'}.b) = 0 for all u in L^, then b = 0.
      Proof: on the hyperplane {u_{id} = 0} of L^ one factor of (u_i.b) u_{i'd} vanishes identically; u_{i'd} = lam u_{id} on L^
      would be an annihilator of column d with zero entries; so u_i.b = mu u_{id} on L^, and pi_i(L^) = C^5 gives b = mu e_d, b = 0.
 (GEN-tri) [rigorous; = (S2-d) for any triangular pair] X_12 = { x(c) : x(c)_ij = c_i G_ij, i = 3,4,5, sum c = 0 }, G_ij = zeta_j / K'_ij
      on Sigma := supp zeta, with: equal row sums s (P_1), G_i.G_i' = s^2 (P_2), G_3 G_4 G_5 = 0 in the squarefree algebra (C4).
      |Sigma| = 5 is impossible (multiplication by a full-support G_5 is injective A_2 -> A_3, so G_3 G_4 = 0, impossible for
      zero-free rows on >= 3 columns); |Sigma| = 2 is impossible (addendum of section 7). So |Sigma| in {3,4}; and for
      |Sigma| = 3: s != 0 (s = 0 would make the three rows pairwise orthogonal in the 2-dim space 1^perp, hence all isotropic and
      parallel, and then perm = 6 t t' t'' n_1 n_2 n_3 != 0).
      [CORRECTION: an intermediate claim "for |Sigma| = 3 two rows of G coincide" was wrong (3 vectors in a plane only need a
      singular Gram matrix); caught by stage2/r2_gen_lemmas.py and not used.]
 (Lemma 4x3) [rigorous] No 4x3 matrix with all entries nonzero has equal row sums s, pairwise row products s^2 and all four 3x3
      permanents zero. Proof: s != 0, s = 1: rows 1/3 + v_i, v_i in 1^perp (2-dim), v_i.v_i' = 2/3; the Gram matrix (2/3)J + D of
      four vectors in a plane has rank <= 2, which forces at least three d_i = 0 (rank(D + 11^T) = rank D + 1 when D has a zero
      diagonal entry); for those three rows the differences are isotropic and pairwise non-orthogonal unless parallel, and
      v_i = v_2 + t n with v_2.v_i = 2/3 gives t = 0 (v_2.n = 0 would make v_2 isotropic): three EQUAL rows g, perm = 6 g_1 g_2 g_3 != 0.
      s = 0: four pairwise orthogonal vectors in the plane 1^perp are all isotropic and parallel: perm != 0 again.
 (Lemma H) [rigorous] No 4x4 matrix with all entries nonzero has all sixteen 3x3 subpermanents zero.
      Proof (squarefree algebra on 4 variables, V_4-Fourier): no two rows are parallel (g^2 G = 0 gives t_j + t_l + t_m = 0 for
      all triples, t = G/g, so t = 0). Scale columns so that row G_2 = e. Q := G_4 G_5 != 0 is killed by e, so Q_12 = Q_34 = al,
      Q_13 = Q_24 = be, Q_14 = Q_23 = ga, al + be + ga = 0, i.e. Q is a function phi on V_4 = {1,a,b,ab} with phi(1) = 0; G_3 Q = 0
      reads rho * phi = 0 (convolution, rho = G_3/G_2), i.e. rho^(chi) phi^(chi) = 0 for all characters, phi^ = (0, 2al, 2be, 2ga).
      As rho is not constant exactly one of al, be, ga vanishes, say ga, and rho is constant on {1,4} and on {2,3}; ga = 0 means
      (G_5/G_4)_1 = -(G_5/G_4)_4 and (G_5/G_4)_2 = -(G_5/G_4)_3. Applying this to every splitting of the four rows into two
      pairs: every ratio G_q/G_p is a constant times a balanced sign vector, so G = D_1 H D_2 with H the 4x4 Hadamard matrix,
      whose 3x3 subpermanents are all +-2. Contradiction.  (LM search: all 25 converged solutions of the 16 equations have a
      numerically zero entry, stage2/r2_lemmaH.py.)
 THEOREM GEN-1 [rigorous]. In GEN no row lies in two triangular minimal pairs; in particular NO ROW LIES IN TWO MINIMAL
      TYPE I PAIRS (the minimal Type I pairs of a fully generic 9-dim level space form a matching), and the same for columns.
      Proof. Let (1,2), (1,3) be triangular. X_123 = X_12 cap X_13 is the line of both triangles on rows 4,5, so the two zeta's
      are proportional: W := X_12 + X_13 = { c_i zeta_j / K'_ij : c on rows 2,3,4,5, sum c = 0 } (3-dim, inside L_1). With
      G = (zeta_j/K'_ij), rows 2..5, columns Sigma: P_1, P_2 on W give equal row sums s and G_i.G_i' = s^2 for all six pairs
      (the monomials c_i c_i' are independent on {sum c = 0}); the cubic part of perm(u + x(c)) = perm(u) gives
      perm(u with rows I replaced by G_I) = 0 for all four triples I and all u in L^ (the four cubic monomials are independent
      on {sum c = 0}); for I = 345, 245 this is C4; for I = 235: |Sigma| = 3: perm(G[235;Sigma]) q_{Sigma^c}(u_1,u_4) = 0 and u = J
      gives perm(G[235;Sigma]) = 0; |Sigma| = 4, Sigma^c = {d}: the identity is (u_1.b) u_4d + u_1d (u_4.b) = 0 with
      b_l = perm(G[235;Sigma - l]), so b = 0 by (GEN-lin); same for I = 234. So all 3x3 subpermanents of G vanish:
      |Sigma| = 3 contradicts Lemma 4x3, |Sigma| = 4 contradicts Lemma H.  QED
 CONSEQUENCE. If (1,2) is a minimal Type I pair in GEN, every pair (1,i), (2,i) (i = 3,4,5) has lam >= 3 or is a NON-triangular
      minimal Type II pair (then some triple through it is the (II,II,lam=3) exception).
 NOT achieved: "a 9-dim level space cannot be fully generic". Missing: a single triangular pair; Type II pairs; all lam >= 3
      (stage3's S3-D regime).
STATUS 15:50: R2-1 (one zero entry: Type I_0, T1_0) and R2-2 (GEN-0, GEN-lin, Lemma 4x3, Lemma H, Theorem GEN-1) written.

## R2-3. THEOREM GEN-2: a fully generic 9-dim level space has NO triangular minimal pair, hence NO minimal Type I pair
 [rigorous hand proof; the two linear-algebra steps machine-checked: stage2/r2_gen_lemmas.py (independence of the monomials),
  stage2/r2_gen2_check.py (no isotropy matrix B: 50 Type I and 1500 Type II cases, dim = 0 in all)]
 Setting GEN, (1,2) a triangular minimal pair, X_12 = {x(c)_ij = c_i G_ij}, G_ij = zeta_j/K'_ij (i = 3,4,5; j in Sigma), as in (GEN-tri).
 Step 1. perm(u + x(c)) = perm(u) on L^ for all c with c_3 + c_4 + c_5 = 0; its part of degree 2 in c gives (c_3c_4, c_3c_5, c_4c_5
   are independent on the plane)   P_ii'(u) := perm(u with rows i,i' replaced by G_i, G_i') = 0  for all u in L^, {i,i'} in {3,4,5}.
   Laplace along rows i,i':  P_45(u) = sum_{T in Sigma} Q_45[T] perm(u[123; T^c]),  Q_45 := G_4 G_5 != 0 (zero-free rows).
 Step 2. |Sigma| <= 2 and |Sigma| = 5 are impossible (GEN-tri).
 Step 3. |Sigma| = 3, Sigma^c = {d,e}. On V_i := {u in L^ : u_id = u_ie = 0} (dim 8; i = 3): perm(u[123;{p,d,e}]) = u_3p q_de(u_1,u_2), so
   P_45 = q_de(u_1,u_2) <Q*,u_3>, Q*_p := Q_45[Sigma - p] != 0. A product vanishing on a vector space has a vanishing factor;
   <Q*,u_3> = 0 on V_3 would give <Q*,u_3> = al u_3d + be u_3e on L^, impossible since pi_3(L^) = C^5. So q_de(u_1,u_2) = 0 on V_3:
   the image of V_3 in the 2x2 block [12;de] is totally isotropic for the nondegenerate form q_0, so it has dim <= 2 and
   {u in L^ : u[12i;de] = 0} has dim >= 6; the same for i = 4, 5 (use P_35, P_34).
   But U := {u in L^ : u[12;de] = 0} has dim exactly 6: no nonzero combination of the two annihilators of I^_12 (Type I or II)
   is supported on two columns [Type I: row 2 forces al = 0 or al = -be, row 1 then be sigma_0 = 0; Type II: row 2 forces
   al = 0 or (Sigma inside Q_2, al = be), row 1 then be y = 0 or be(1+y) = 0]. Hence all of U has u_id = u_ie = 0 for i = 3,4,5:
   columns d, e of every u in U vanish, U lies in L cap {column d = 0}, which has dim 9 - 4 = 5 < 6. Contradiction.
 Step 4. |Sigma| = 4, Sigma^c = {d}. On U_d := {u in L^ : u_1d = u_2d = 0}: perm(u[123;{p,q,d}]) = u_3d q_pq(u_1,u_2), so
   P_45 = u_3d Phi(u_1,u_2), Phi(z) = z_1^T B z_2, B[j,l] := Q_45[Sigma - {j,l}] (4x4 symmetric, zero diagonal, B != 0).
   u_3d = 0 on U_d would be a column-d annihilator (al,be,-1,0,0) with zeros. So Phi = 0 on I^d := {z in I^_12 : z_1d = z_2d = 0},
   a subspace of codimension exactly 2 of C^{2 x Sigma} (no annihilator of I^_12 is supported on one column: GEN-0 for Type I,
   direct for Type II). Then rank B = 2, B = a b^T + b a^T with disjoint supports A, B' and I^d is the preimage of a maximal
   isotropic plane; if both row projections of I^d are onto, I^d^perp = {(xa + yb, mu(-xa + yb))}, so kappa^2 = mu kappa^1 on A,
   -mu kappa^1 on B', and in tau-coordinates EVERY annihilator of I^d has the form (v,-v), v constant on A and on B'.
   Type I: the second annihilator is (1_{C cap Sigma} - sigma_0 1_Sigma, -1_{C cap Sigma}): needs sigma_0 = 0, false.
   Type II: the ratio kappa^2/kappa^1 takes two opposite values on Sigma, so Q_1 = {d}, {A,B'} = {Q_2,Q_3}, and the second
   annihilator (1_{Q_3} + y 1_Sigma, 1_{Q_2}) needs y = -1, false. If a row projection of I^d is not onto (only Type II with
   Q_2 = {d} or Q_3 = {d}): I^d = {<n,z_1> = 0, <kappa^2,z_2> = <kappa^1,z_1>} with n zero-free on Sigma and not parallel to
   kappa^1; then B z_1 = 0 for a dense set of z_1 in n^perp, so rank B <= 1, B = 0. Contradiction in all cases.   QED
 COROLLARIES (GEN):
   (i)   no minimal Type I row pair and (transpose) no minimal Type I column pair  [Type I pairs are triangular by (S2)];
   (ii)  every minimal pair is of Type II and NON-triangular: for a minimal pair (r,r') some third row i has X_{rr'i} = 0, and
         the triple (r,r',i) is the exception of (S2): a second minimal Type II pair through r or r' and a third pair with lam = 3;
   (iii) Theorem GEN-1 (R2-2) is a special case; Lemma 4x3 and Lemma H remain true but are no longer needed.
 So in GEN:  minimal pairs exist  <=>  one of the (II,II,lam=3) exception triples exists (the 21 canonical configurations of
 item O2, further restricted in GEN: no relation of L may be supported in one column, e.g. Q_2 = Q_2' = {j} is excluded).
 If these are excluded, GEN reduces to "all lam >= 3 for rows and columns" = stage3's hypothesis (H1) with all a_r = b_c = 1.
STATUS 15:55: Theorem GEN-2 proved and written (no minimal Type I pairs in the fully generic regime).

## R2-4. Lemma GEN-3 (2-row elements against a minimal pair) and the remaining minimal pairs in GEN  [rigorous]
 Steps 3 and 4 of GEN-2 use only ONE 2-row element. In GEN let (r,r') be a minimal pair, i a third row and y != 0 a 2-row
 element of L on the two remaining rows (so y lies in X_{rr'i}); Sigma_y := its column support, Q_y := the vector of its 2x2
 subpermanents. Since perm(u with the two rows replaced by those of y) = 0 on L^ (s^2-coefficient of perm(u + s y)):
   (a) |Sigma_y| = 4 is impossible (Step 4 verbatim; block-rank facts checked for all pair types, stage2/r2_block_rank.py);
   (b) if |Sigma_y| = 3, Sigma_y^c = {d,e}: every t in L with t[rr';de] = 0 also has t[i;de] = 0 (Step 3); in particular every
       x in X_{rr'} vanishes at the cells (i,d), (i,e);
   (c) |Sigma_y| >= 2 always (GEN), and Q_y != 0 iff |Sigma_y| >= 3.
 Use for a NON-triangular minimal pair (1,2) (Type II by GEN-2), V_i := X_12 cap {row i = 0}:
   two lines V_4 = C x_4, V_5 = C x_5 (V_3 = 0), supports Sigma' and Sigma: C4 gives Q_{x_5} G'_5 = 0 = Q_{x_4} G_4 (rows as elements of
   the squarefree algebra), so not both supports have size >= 3 with one of size 5; by (a) sizes lie in {2,3,5}; by (b) a
   support of size 3 contains the other support; (3,3) with equal supports puts {t in L : t[12;de] = 0} (dim 6) inside
   {column d = 0} (dim 5): impossible. Left: (|Sigma|,|Sigma'|) in {(2,2),(2,3),(3,2),(2,5),(5,2)}, one line only, a common zero
   row, or no line at all (three exception triples).  NOT finished.
 WHAT REMAINS IN GEN (exact): minimal pairs can only be non-triangular Type II pairs in the sub-cases just listed, each
 forcing at least one (II,II,lam=3) exception triple; if those are excluded, GEN is the regime "all lam >= 3 for rows and
 columns, all a_r = b_c = 1" (stage3's (H1): S3-A, S3-D apply; not closed).
STATUS 15:59: Lemma GEN-3 written. Items (2) (the 21 Type-II/Type-II configurations) NOT attacked computationally in round 2
 (only restricted in GEN). Updating the RESULT block and handing back.

## R2-5. Two more rigorous remarks for GEN
 (GEN-4) A minimal pair (1,2) whose plane X_12 has a common zero row (X_12 = plane of 2-row elements y(xi), xi in a 2-plane Xi,
      on rows 4,5): by (GEN-3)(a),(c) every nonzero element has support of size 2, 3 or 5; counting the zeros of the five
      coordinate forms on Xi leaves generic support 3 with three simple zeros, or generic support 5 with proportionality
      classes of sizes (2,3). Generic support 3 is impossible: P_2 = sum_T xi_j xi_l perm(K'[45;T]) vanishes on the plane
      Xi = {n.xi = 0} of C^3 (n zero-free), a squarefree quadric divisible by n.xi is 0, so perm(K'[45;T]) = 0 for all three
      pairs, impossible. So X_12 = span(y_A, y_B) with y_A of B-type on a 2x2 block [45;A] and y_B supported on the
      complementary three columns; and every t in L with t[12;A] = 0 has t[3;A] = 0.  (Not excluded.)
 (GEN-5) In an exception triple with Q_3 = Q_3' the difference of the two Type II relations is sum_{Q_2} tau_2 - sum_{Q_2'} tau_3 = 0
      on L; if Q_2 = Q_2' = {j} this is an annihilator of column j with zero entries: excluded in GEN. This removes 3 of the
      21 canonical survivors of t8_two_minimal.py ((0,1,2,2,2), (0,0,0,1,2), (0,0,1,2,2) paired with their conjugates); 18 remain.
STATUS 16:00: R2-5 added.
STATUS 16:05: round-2 final report sent. Best next steps: (i) in GEN finish the non-triangular Type II minimal pairs with
 (GEN-3) + C4 + P_2 (sub-cases listed in R2-4, R2-5), which would give "GEN => lam >= 3 for all row and column pairs";
 (ii) the 18 remaining (II,II,lam=3) configurations (full cube condition + J-relations; not attempted); (iii) transfer the
 product-factorisation argument of GEN-2 to rows/columns with one zero entry (Type I_0), where single-row elements can exist.

# ROUND 3 (start 16:09, budget 75 min -> ends ~17:24)
STATUS 16:12: stage3 round-2 RESULT read (N3', N3'-L, MIN-A/B/C, configuration (II)). Working on the exception triples.

## R3-1. THE EXCEPTION TRIPLES ARE IMPOSSIBLE  [num-assisted: the list of admissible fifth annihilators comes from a floating-point
##        search over exact combinatorial data; the final contradictions are hand computations, confirmed numerically]
 Setting (any 9-dim level L, not only GEN): rows 1,2,3 with a = 1 and zero-free annihilators, (1,2), (1,3) minimal Type II,
 dim X_23 = 3, X_123 = 0. Then I_3^perp = span(A0) + C n**, A0 = {f_1-f_2, f_1-f_3, g_12 + y_12 f_1, g_13 + y_13 f_1}, n** = (0,m_2,m_3).
 (E1) [rigorous] Dimension count: the row-1 parts 1_{Q_3}, 1_{Q_3'} agree up to complement (1668 of 1800 canonical pairs excluded).
 (E2) [rigorous lemma, as in (T2)] For EVERY column triple S with ell != 0 on Pi~_S := span(A0)^perp cap C^{3xS} (also when the
      pair functionals are dependent on S), with K_S := Pi~_S cap ker ell and c_S := perm|K_S:  n**|K_S = 0 or n**|K_S divides c_S.
 (E3) [rigorous] Admissibility: m_3 not in span(1, 1_{Q_2'}) and m_2 not in span(1, 1_{Q_2}) (otherwise n** would be equivalent to a
      functional of rows (1,2) or (1,3), giving I_12 or I_13 a third annihilator).  [Round 1's t8 survey used only "not a
      row-1 functional" and only the S with independent functionals; that is why it reported 21 survivors.]
 (E4) [floating point] stage2/r3_survey.py: of the 132 remaining canonical configurations 120 have no admissible n** at all;
      12 survive, each with exactly ONE maximal family ("leaf") of admissible n**:
        (a) the six CONJUGATE configurations (same cells Q_1,Q_2,Q_3, eps_2 = +1, eps_3 = -1):
              n** = sum_{Q_1}(tau_2 - i tau_3) + (1-i) sum_{Q_2} tau_2 - delta ell      (delta in C the only parameter);
        (b) six NON-CONJUGATE ones, in two column/row-swap classes:
              A: Q_1={0,1,2}, Q_2={3}, Q_3={4}; Q_1'={0,3}, Q_2'={1,2}:  n** = al tau_2(0) + be (tau_3(1) - tau_3(2)) + ga tau_2(3) - delta ell
              (B = A with rows 2,3 exchanged);
              C: Q_1=Q_2'={0,1}, Q_2=Q_1'={2,3}, Q_3={4}:               n** = al (tau_2(3) - tau_2(2)) + be (tau_3(0) - tau_3(1)) + ga (tau_2(2) + tau_2(3)) - delta ell.
 (E5) [hand; confirmed by stage2/r3_hand_check.py and r3_generic_fail.py: cube defect 1.0 in all 12 configurations]
      FULL CUBE CONDITION (perm_3 = k ell^3 on Pi_S whenever ell != 0 there) fails for every member of these families:
        (a) S = {p in Q_1, q in Q_2, s in Q_3}: Pi_S is parametrised by ell, a_1 = tau_1(p), c_1 = tau_1(s), a_3 = tau_3(p);
            the coefficient of a_1 in perm_3 is E_1 with quadratic part 0, A-coefficient 0 and c_1-coefficient -(1+i) delta_h
            (delta_h = delta + i), so delta_h = 0, and then perm_3 = (1+i)(1+ybar) c_1 ell^2 = c_1 ell^2, not a multiple of ell^3.
        (b) A and C: S = {the two columns of the 2-element cell carrying tau_3(.) - tau_3(.)} + {column 4}: on Pi_S
            tau_3 = (d ell, -d ell, ell) (d = delta/(2 be)), tau_1 = (t_1, (1+y) ell - t_1, -y ell), tau_2 = (a, b, ell - a - b), and the
            coefficient of t_1 in perm_3 is ell [ i(b - a) + 2d(ell - a - b) ], which vanishes identically only if i = 2d = -i;
            be = 0 is inadmissible by (E3).
 CONSEQUENCES.
 (S2*) [num-assisted] For ANY three rows with a = 1 and zero-free annihilators of a 9-dim level space: X_ijk != 0. So if all five
      rows have a = 1 and zero-free annihilators, every pair of rows carries a nonzero 2-row element (no hypothesis on Type II).
 (GEN-6) [num-assisted for the exception part, otherwise rigorous] A fully generic 9-dim level space has NO minimal pair:
      lam >= 3 for all ten row pairs and all ten column pairs. (A minimal pair would be triangular by (S2*), impossible by GEN-2.)

## R3-2. Two general factorisation lemmas for 2-row elements  [rigorous; sanity on the examples: stage2/r3_Y3.py (144 cases),
##        r3_Y5.py (90 cases), 0 violations]
 y != 0 a 2-row element of a 9-dim level L on rows a,b; {c,d,e} the other rows; Q_y[T] := 2x2 subpermanent of y on the column
 pair T. Always: perm(u with rows a,b replaced by y_a, y_b) = sum_T Q_y[T] perm(u[cde;T^c]) = 0 for all u in L^.
 (Y3) |Sigma_y| = 3, Sigma_y^c = {d',e'}, Q_y != 0, and a_i = 1 for i in {c,d,e}: on {u in L^ : u_id' = u_ie' = 0} the identity is
      q_{d'e'}(u_i',u_i'') <Q*,u_i>, the linear factor cannot vanish (pi_i(L^) = C^5), so the image of that 8-dim space in the 2x2
      block [i'i'';d'e'] is totally isotropic and  dim {u in L^ : u[cde;d'e'] = 0} >= 6  (generic value 4): the 3x2 block
      {c,d,e} x Sigma_y^c carries >= 2 independent relations of L^.  [No minimality needed; this is Step 3 of GEN-2.]
 (Y5) c a row with a_c = 1, j a column with kappa^c_j != 0, F := [5] - j, B^{y,j}[p,q] := Q_y[F - {p,q}] (4x4, symmetric, zero
      diagonal). On V_cj = {u in L^ : u_c in C e_j} (dim 6) the identity is u_cj * (u_d^T B^{y,j} u_e) (columns F), and u_cj != 0
      there, so the image W of V_cj in rows d,e, columns F is isotropic:  rank B^{y,j} <= 8 - dim W.  In GEN the kernel of
      V_cj -> W is Y_ab, so      rank B^{y,j} <= 2 + m_ab.
      For m_ab = 1: det B^{y,j} = 0, i.e. with pi_1, pi_2, pi_3 the products of Q_y over the three perfect matchings of F:
      pi_1^2 + pi_2^2 + pi_3^2 = 2(pi_1 pi_2 + pi_1 pi_3 + pi_2 pi_3).  In GEN Q_y[pq] = - xi_p xi_q K'_ap K'_aq (r_p + r_q), r := K'_b/K'_a, and the
      condition becomes (A,B,C the three matching sums of products of r)  AB + AC + BC = e_1 e_3 - 4 e_4 = 0, i.e.
            (sum_{x in F} r_x)(sum_{x in F} 1/r_x) = 4      for every 4-set F inside Sigma_y.
 (GEN-7) In GEN a 2-row element y with m_ab = 1 has |Sigma_y| <= 4.  Proof: for |Sigma_y| = 5 all five 4-sets satisfy the
      equation, so every r_j is a root of h x^2 - (sh - 3) x + s = 0 (s = sum r, h = sum 1/r; h = 0 gives r = 0): at most two
      values, with multiplicities (n_1,n_2), n_1 + n_2 = 5; a 4-set with k and 4-k of them needs k^2 + (4-k)^2 + k(4-k)(t + 1/t) = 4:
      k = 2: t + 1/t = -1; k = 1,3: t = -1; k = 0,4: impossible; (4,1) contains a (4,0) set, (3,2) contains both (2,2) and (3,1)
      sets. Contradiction. (LM search for five such numbers: residual floor 2.8, stage2/r3_Y5.py.)

## R3-3. Configuration (II) (stage3) is impossible in GEN  [rigorous given the lemmas above]
 (II): F = { sum_{i in N_4} c_i e_i rho_i^T : sum c = 0 } in L, N_4 four rows. In GEN the column annihilators give
 K'_ij rho_i(j) = zeta_j independent of i, so F is rank one in column-weighted coordinates, G := (rho_i(j)) = (zeta_j/K'_ij),
 zero-free on Sigma := supp zeta. P_1, P_2 on F: equal row sums s, rho_i.rho_k = s^2; lineality of F: perm(u with the rows of a
 triple I in N_4 replaced by rho_I) = 0 on L^.
   |Sigma| = 1: rho_i = c e_j is not orthogonal to kappa^i.   |Sigma| = 2: P_2 forces r_i + r_k = 0 for all pairs of four rows.
   |Sigma| = 3: the triple identity is perm(G[I;Sigma]) q_{Sigma^c}(u_d,u_e), and u = J gives perm(G[I;Sigma]) = 0 for all four
               triples: contradicts Lemma 4x3.
   |Sigma| = 4: the triple identity has the form of (GEN-lin), so all sixteen 3x3 subpermanents of G vanish: contradicts Lemma H.
   |Sigma| = 5: x^{ik} = e_i rho_i^T - e_k rho_k^T is a 2-row element with full support; if m_ik = 1 this contradicts (GEN-7).
 So (II) cannot occur in GEN when some pair inside N_4 has a 1-dimensional space of 2-row elements; in particular not in
 stage3's minimal case (all lam = 3, all m = 1). With stage3's MIN-C (minimal case + (NZ) => (II); (NZ) holds in GEN):
 (GEN-8) A fully generic 9-dim level space is NOT in the minimal case: some row pair has lam >= 4 or some row pair carries
      a >= 2-dim space of 2-row elements; and (transpose) the same for columns.

## R3-4. State of GEN after round 3 and the precise remaining list
 PROVED for a fully generic 9-dim level space L (all a_r = b_c = 1, all annihilators zero-free):
   (1) no single-row / single-column elements, no dominoes (stage3 SR/SC);   (2) no minimal Type I pair (GEN-2, rigorous);
   (3) no minimal pair at all, i.e. lam >= 3 for all row and column pairs (GEN-6; the exclusion of the exception triples is
       num-assisted, R3-1);   (4) every row pair and every column pair carries a nonzero 2-line element, each with >= 2 nonzero
       columns (rows);   (5) not the minimal case (GEN-8; uses stage3's MIN-C);   (6) constraints (Y3), (Y5), (GEN-3), (GEN-7) on
       every 2-row element.
 NOT PROVED: "a 9-dim level space cannot be fully generic". What survives in GEN is exactly stage3's (R3) on BOTH sides:
   rows:    some lam_{rr'} >= 4  or  some m_ab >= 2;        columns:  some lam^{cc'} >= 4  or  some m^{T} >= 2,
 with all lam >= 3, no sparse (one-line) elements, and the identities (Y3)/(Y5) for all 2-row and 2-column elements.
 Other open items (unchanged): making R3-1 exact (leaf enumeration over Q(i)); zero entries beyond one zero with all pairs
 minimal; rows with a_r >= 2 (Type I'); stage3's (R2), (R4), (R5).
STATUS 16:35: R3-1 .. R3-4 written.
STATUS 16:37: RESULT-R3 written at the top. Remaining time used for (R3) in GEN.
STATUS 16:41: stage3's round-3 RESULT read (N1: all lam = 3 => single-row element; otherwise the rigid family N2). Attacking N2 in GEN.

## R3-5. LEMMA N2-GEN (family N2 is impossible with zero-free column annihilators) and THEOREM GEN
##       [hand proof; numerics: stage2/r3_N2.py, r3_N2b.py, r3_N2c.py, r3_N2d.py]
 LEMMA N2-GEN. Let L be a level space (any dimension) and c,d,e three rows such that every column j has an FK annihilator kappa'^j
 with K'_ij := kappa'^j_i != 0 for i in {c,d,e}; L has no single-row element in rows c,d,e and no single-column element in rows c,d
 [both automatic in GEN]. Then it is IMPOSSIBLE that m_cd = m_ce = m_de = 2 and Y_de lies in Y_cd + Y_ce.
 [In stage3's case N2: lam_ab = 4, X_ab = Y_cd (+) Y_ce contains Y_de, all three m = 2.]
 Step 0 (normal form). 2-row elements obey the column annihilators: on (c,d) t_dj = -a_j t_cj, on (c,e) t_ej = -b_j t_cj, with
   a_j := K'_cj/K'_dj, b_j := K'_cj/K'_ej (all nonzero). Y_cd = {(v; -a o v): v in P_cd}, Y_ce = {(v'; -b o v'): v' in P_ce}, the sum
   is direct (no single-row element). An element of the sum with row c = 0 has v' = -v in P_cd cap P_ce; dim Y_de = 2 forces
   P_cd = P_ce =: P (a 2-plane), and     X := Y_cd + Y_ce = {(pi_c; a o pi_d; b o pi_e) : pi_i in P, pi_c + pi_d + pi_e = 0}.
   P contains no unit vector (e_j in P gives the single-column element (e_j; -a_j e_j) in Y_cd).
 Step 1 (level conditions). For t supported on three rows, perm(J + t) = 120 + 24 P_1 + 6 P_2 + 2 P_3 with (s_i = row sums)
   P_1 = sum t_ij, P_2 = sum_{i<k} (s_i s_k - <t_i,t_k>), P_3 = s_c s_d s_e - sum s_i <t_k,t_l> + 2 sum_j t_cj t_dj t_ej.
   Let lam_j be the coordinate functions on P and sigma := sum_j lam_j. P_1, P_2 on Y_cd, Y_ce, Y_de and P_3 on X give
     (i)   sum a_j lam_j = sum b_j lam_j = sigma;      (ii)  sum c_j lam_j^2 = sigma^2  for c in {a, b, ab};
     (iii) sum a_j b_j lam_j^3 = sigma^3
   [(iii): with (i),(ii) polarised, P_3 = 2 Phi(pi_c,pi_d,pi_e), Phi(x,y,z) := sum a_j b_j x_j y_j z_j - sigma(x)sigma(y)sigma(z);
   Phi(x,x,-2x) = 0 kills the cubic form]. Conversely (i)-(iii) are equivalent to "X level" (r3_N2c.py: 39 numerical solutions
   of (i)-(iii) give |perm(J+t) - 120| < 4e-9 on X; random data give 1e3).
 Step 2 (moment form). Take nu != 0 in ker(sigma|P), S := supp nu, eta in P - C nu, tau := sigma(eta), zeta_j := eta_j/nu_j (j in S),
   lam = s nu + t eta. Coefficients of s^i t^k (weights c: (M1) c in {1,a,b}; (M2) c in {a,b,ab}; W_j := a_j b_j nu_j^3 != 0):
     (M1) sum_S c nu = 0,                         sum_S c nu zeta   + sum_{S^c} c eta   = tau;
     (M2) sum_S c nu^2 zeta^r = 0 (r = 0,1),      sum_S c nu^2 zeta^2 + sum_{S^c} c eta^2 = tau^2;
     (M3) sum_S W zeta^r = 0 (r = 0,1,2),         sum_S W zeta^3    + sum_{S^c} ab eta^3 = tau^3.
   (V) If zeta takes k <= 3 distinct values on S, all class sums of W vanish (Vandermonde): no zeta-class is a singleton.
   (L) For k distinct points z_m, F := prod (z - z_m), om_m := 1/F'(z_m): sum om_m z_m^r = 0 (r <= k-2), = 1 (r = k-1); every vector on
       the points is om_m G(z_m) with deg G <= k-1, and the moments read off the top coefficients of G.
 Step 3 (cases: |S| and the partition of S into zeta-classes).
   |S| = 1: unit vector.   |S| = 2: (M1) gives nu_1 + nu_2 = 0 and a_1 = a_2, so sum a nu^2 = 2 a_1 nu_1^2 != 0, against (M2).
   |S| = 3: by (V) one class, so eta' := eta - zeta nu lives on S^c and has support exactly 2 (no unit vector). sigma(eta') = 0 is the
     case |S| = 2. Otherwise sigma(eta') = 1 and A_j := a_j eta'_j, B_j := b_j eta'_j (j = 4,5) satisfy sum eta' = sum A = sum B = 1,
     sum A eta' = sum B eta' = sum A B = 1, i.e. (2A_4-1)(2eta'_4-1) = (2B_4-1)(2eta'_4-1) = (2A_4-1)(2B_4-1) = 1, so (2A_4-1)^2 = 1
     and A_4 A_5 = 0. Contradiction.
   |S| = 4, S^c = {5}: by (V) the classes are (4) [eta - zeta nu in C e_5: unit vector], (2,2) or (1,1,1,1).
     (2,2), class {1,2}: the class sums of W and (two points, r = 0,1) of ab nu^2, a nu^2, b nu^2 vanish; W_1 + W_2 = 0 = V_1 + V_2
       gives nu_1 = nu_2, then a_1 = -a_2, b_1 = -b_2 and (ab nu^2)_1 + (ab nu^2)_2 = 2 a_1 b_1 nu_1^2 != 0. Contradiction.
     (1,1,1,1): by (L) W_j = c om_j (c != 0), ab nu^2 = om_j(al + be zeta_j), a nu^2 = om_j(al_a + be_a zeta_j), b nu^2 = om_j(al_b + be_b zeta_j);
       so nu_j = c/(al + be zeta_j), and (al_a + be_a z)(al_b + be_b z)(al + be z) - c^2 F'(z) is a cubic with four roots: be be_a be_b = 4c^2.
       With h := eta_5, A := a_5 h, B := b_5 h the remaining equations of (M1)-(M3) read
          4c/be = tau - h,  be_a be/c = tau - A,  be_b be/c = tau - B,  be_a = tau^2 - A h,  be_b = tau^2 - B h,  be = tau^2 - AB,  c = tau^3 - AB h.
       h = 0: 4 tau = tau and c = tau^3 = 0. h != 0: be_a be = c(tau - A) expands to A tau (tau - B)(tau - h) = 0, likewise
       B tau (tau - A)(tau - h) = 0; tau = 0 gives 5h = 0, tau = h gives c = 0; so tau = A = B, be_a be = 0, against be be_a be_b = 4c^2.
   |S| = 5: sigma is not 0 on P (else every nonzero vector of P would be zero-free by the cases above), ker = C nu, tau != 0, normalise
     tau = 1. By (V): (5) [eta in C nu]; (3,2) [P = C phi + C psi with disjoint supports, polarised (ii) gives sigma(phi) sigma(psi) =
     sum a phi psi = 0: a vector of ker sigma that is not zero-free]; (2,1,1,1); (1,1,1,1,1).
     (1,1,1,1,1): by (L) nu = om N, a nu = om N_a, b nu = om N_b (cubics, leading coefficient 1), a nu^2 = om A, b nu^2 = om B (monic
       quadratics), W = om (z + w_0); shift eta by a multiple of nu: w_0 = 0. (a nu^2)(b nu^2) = W nu gives AB = z N (degree <= 4, five
       roots). So z | A or z | B; by the symmetry a <-> b let A = z(z - al), N = (z - al) B. (b nu)(nu) = b nu^2 gives
       N_b N - F' B = F l_b, l_b linear with leading coefficient 1 - 5 = -4. Hence B [(z - al) N_b - F'] = F l_b; B(zeta_j) != 0 for all j,
       so B is prime to F and divides l_b: impossible (deg B = 2).
       [r3_N2d.py: this step needs BOTH a nu and b nu: the 16 moment equations for nu, a nu, b nu, a nu^2, b nu^2, ab nu^3 in 20
       unknowns have 0/120 LM solutions; without the two a nu equations 110/120 non-degenerate solutions (the branch z | B).]
     (2,1,1,1), double class {1,2} at z_1, F = (z - z_1) F_1: class sums W = om (constant 1); a nu^2, b nu^2, ab nu^2 <-> monic linear
       A, B, V; nu, a nu, b nu <-> monic quadratics N, N_a, N_b. At the three singleton points: AB = N; VN - F' = A N_b - F' =
       B N_a - F' = -3 F_1 (cubics, three roots, leading coefficient 1 - 4). So N_b = VB, N_a = VA, VAB = (z - z_1) F_1' - 2 F_1.
       With p,q,r := A,B,V at z_1 and om := 1/F_1(z_1): om p q r = -2, and the class sums over {1,2} are
          sum nu = om pq, sum a nu = om rp, sum b nu = om rq, sum a nu^2 = om p, sum b nu^2 = om q, sum ab nu^2 = om r, sum ab nu^3 = om.
       Put nu_i = om pq (1 +- Z)/2, a_i nu_i = om rp (1 +- X)/2, b_i nu_i = om rq (1 +- Y)/2: the quadratic sums give
       (1 + XZ)/2 = (1 + YZ)/2 = (1 + XY)/2 = 1/(om pqr) = -1/2 and the cubic sum gives (1 + XY + XZ + YZ)/4 = 1/(om pqr)^2 = 1/4,
       i.e. -5/4 = 1/4. Contradiction.                                                                                   QED
 Numerical corroboration of the whole lemma (r3_N2b.py, LM on (i)-(iii), 200 starts): 198 solutions, 191 with a zero or infinite
 weight a_j or b_j, 7 with a unit vector in P, 0 genuine. (The strata with a singleton class, (2,1,1,1) and |S| = 4 are
 overdetermined, so they are only covered by this survey, not by a separate underdetermined test.)

 THEOREM GEN [CONDITIONAL on (a), (b)]. A 9-dim level space is never fully generic.
 Proof. In GEN: lam >= 3 for all row pairs (GEN-6 = GEN-2 [rigorous] + R3-1 [num-assisted] = input (a)); no single-row element
 (zero-free column annihilators); all a_r = 1. stage3 sec. 16 = input (b): either all lam = 3, and then Theorem N1 produces a
 single-row element, or case N2: lam_ab = 4, m_cd = m_ce = m_de = 2, X_ab = Y_cd (+) Y_ce. Lemma N2-GEN excludes N2.   QED
 Only the ROW side of GEN-6 and the zero-freeness of the column annihilators at three rows are used after GEN-6.
 What I did NOT do: verify stage3's sections 12, 14, 15, 16 myself (I read section 16 and re-derived only (G1)/(G2)-type facts
 I use: X_ab = Y_cd (+) Y_ce and P_cd = P_ce); make R3-1 exact.
 REMAINING LIST (16:59): (1) verification of the two conditional inputs: R3-1 exact (leaf enumeration over Q(i)) and stage3's
 sections 12-16; an independent check of Lemma N2-GEN (short; a CAS elimination of the seven moment families would settle it);
 (2) family N2 OUTSIDE GEN (column annihilators with zero entries at the rows c,d,e, or b_c >= 2): the normal form of Step 0 changes;
 (3) zero entries in the annihilators beyond one zero with all pairs minimal; rows/columns with a_r >= 2 (Type I'); stage3's (S2), (S3).
 Runs to report: r3_N2.py first run (400 starts) hit its 170 s timeout with no output; r3_N2b.py hit its 150 s timeout in the
 second (exp-parametrised) half, the first half is the survey quoted above; r3_N2d.py symmetric run 1m49s. All others < 20 s.
STATUS 16:59: R3-5 written; headline updated. Final report follows.
STATUS 17:02: second survey seed for Lemma N2-GEN (r3_N2b.py 23 0 150 plain, 59 s): 148 solutions of (i)-(iii): 144 with a zero or
 infinite weight, 4 with a unit vector in P, 0 genuine (total over both seeds: 346 solutions, 0 genuine). Re-derived the elementary
 parts of stage3's reduction that Theorem GEN uses ((P), (G1), (G2), lam_ab = 5 impossible): correct; so input (b) is exactly
 stage3's Theorem N1 (all a_r = 1, all lam = 3 => single-row element). Round-3 final report sent.

# ROUND 4 (start 17:08, budget 90 min -> ends ~18:38). Target: regime REG1 := "all a_r = 1 and all b_c = 1", annihilators may have zeros.
STATUS 17:27: read rows' defect normal form / Corollary H, verifyfl's TC5, chief's RP6/RP7/RP9 (Lemma DS), stage3 sec. 16-17.
 Census of the known examples (stage2/r4_census.py): none is in REG1 (all have several lines with a >= 2), so REG1 has no examples to guide.
 Numerical exploration of the GENERAL N2 block X_ab = {(psi_c(p_c); psi_d(p_d); psi_e(p_e)): sum p_i = 0} (stage2/r4_block.py, 14 starts):
 level blocks exist with all five columns of generic type (three independent-ish forms, rank 2) and with all five columns diagonal
 (rank 1) -- the latter all have class structure (4,1), i.e. a unit vector in P (consistent with Lemma N2-GEN). So without zero-free
 column annihilators the block alone does not give a contradiction; N2 must be attacked with more of its structure (L_a, L_b).
 Session was interrupted once at ~17:26 (server restart); resumed.
STATUS 17:49: three results so far this round (sections R4-1..R4-3 below): the dictionary "zeros / single-row elements / defects" for
 REG1, the general normal form of the N2 block, and LEMMA N2-Z (moment problem with zero weights). Pattern survey for two-row columns running.

## R4-1. REG1 dictionary: what a zero of an annihilator and what a single-row element mean  [rigorous; mostly re-readings of chief RP6/RP9,
##       stage3 GZ/SR/SC and rows' defect construction, collected because they are the replacement for the tau-coordinates]
 REG1: dim L = 9, all a_r = b_c = 1; kappa^r, kappa'^c the unique FK annihilators (sum = 1). L_r := L cap {row r = 0} (dim 5).
 (Z1) kappa^r_j = 0  <=>  e_j in pi_r(L)  <=>  the 1x4 block {r} x ([5]-j) is ell-supporting. Then V_rj := {t in L : t_r in C e_j} has
      dim 6, and perm_4(t^(rj)) = 0 on V_rj (GZ-b; chief RP6 with v = e_j). If kappa^r_j != 0, V_rj is replaced by the 6-dim space
      {u in L^ : u_r in C e_j}, on which perm_4(u^(rj)) = 120 (kappa^r_j)^5 u_rj^4. Same for columns with kappa'.
      So the tau-coordinates tau_r(j) = kappa^r_j u_rj survive on supp(kappa^r); the columns j outside supp(kappa^r) are "free" coordinates of
      row r (ell does not see them), each carrying a 6-dim linear subspace of L with a vanishing 4x4 subpermanent.
 (Z2) (chief RP9) all five 4x4 subpermanents vanish identically on L_r (as 4x5 matrices), for every r; dually on every L^c.
 (Z3) SINGLE-ROW ELEMENTS = DEFECT (valid in every level space, every row): Z_r := {w : e_r w^T in L} lies in (C(L_r) + C 1)^perp, where
      C(L_r) is rows' defect space of the 4x5 level space L_r. [Lineality of e_r w^T on CJ + L_r: <w, G(cJ' + xi)> = 0, and
      G(cJ' + xi) = sum_k c^(4-k) (4-k)! p_k(xi).]  Hence z_r <= 4 - e(L_r), and L_r (+) e_r (x) Z_r is a level space with deletable row r.
      In REG1: dim L_r = 5, so e(L_r) >= 1 (zeros' Lemma SL: e = 0 forces dim <= 3) and z_r <= 3. z_r = 3 forces L_r to be a (5,1) space
      (an 8-dim level space with a deletable row would exist inside L): excluded by verifyfl's TC5 when the defect line is C(e_j - e_l),
      i.e. when Z_r = {w : sum w = 0, w_j = w_l}; excluded in general only by rows' open conjecture (DI_5).
      rows' Corollary H applied to L' = L_r: z_i <= e(L_r) and m_ij <= e(L_r) + 1 for all rows i, j != r. So
            max_{i != r} z_i  <=  e(L_r)  <=  4 - z_r      and      m_ij <= 5 - z_r   ({i,j} not containing r).
 (Z4) (stage3 SR/SC) e_a w^T in L, w_j != 0 => kappa'^j_a = 0; y e_j^T in L, y_a != 0 => kappa^a_j = 0.
 Census (stage2/r4_census.py): none of the known example spaces is in REG1 (every 7-dim example has several lines with a >= 2).

## R4-2. The N2 block without zero-freeness  [normal form rigorous; existence statements numerical]
 In stage3's family N2 (lam_ab = 4, m_cd = m_ce = m_de = 2, no single-row element) there are a 2-dim space P and injective maps
 psi_c, psi_d, psi_e : P -> C^5 with      X_ab = {(psi_c(p_c); psi_d(p_d); psi_e(p_e)) : p_i in P, p_c + p_d + p_e = 0}
 (Y_cd = graph on p_e = 0, etc.; the three rows play symmetric roles). Column j of X_ab is given by three linear forms
 (al_j, be_j, ga_j) on P. The column annihilator gives K'_cj al_j = K'_dj be_j = K'_ej ga_j, so every column is of one of the types
   D : three nonzero PROPORTIONAL forms (then (K'_cj,K'_dj,K'_ej) is zero-free or 0),
   0 : the column vanishes on X_ab,
   S : the column is supported on rows where kappa'^j vanishes (one row: S1; two rows: S2; three rows: S3),
 and a column whose three entries are independent functionals on X_ab forces kappa'^j in span(e_a, e_b).
 Level conditions in general: the three row-sum forms coincide (= sigma); <psi_i(p),psi_k(p)> = sigma(p)^2 for the three pairs, the
 alternating parts w_ik of <psi_i(p),psi_k(p')> - sigma(p)sigma(p') satisfy w_cd = w_ce - w_de; and P_3.
 Numerics (stage2/r4_block.py, r4_inspect.py, r4_inspect3.py; 14 starts): level blocks exist
   - with all five columns generic (three pairwise independent forms; 7 hits): no sparse element, every column projection 3-dim.
     In REG1 this forces all five kappa'^j into span(e_a,e_b); since dim A_ab = 1 + lam_ab = 5 these five relations span all relations on
     rows a,b, and then kappa^a = e_{j_a}, kappa^b = e_{j_b}: TWO IDENTICALLY VANISHING CELLS (a,j_a), (b,j_b) [rigorous deduction];
   - with all five columns of type D (5 hits): always the unit-vector configuration (alpha1) below.
 So, unlike in GEN, the block alone does not give a contradiction. Necessary conditions on M = L_a + L_b (level + (Z2) on L_a, L_b;
 stage2/r4_N2full.py, r4_N2inj.py, r4_N2fast.py): LM mostly runs into non-injective psi (not N2); one genuine solution found, with a
 3-dim space of single-column elements in one column (a "split free column"). Too few runs to conclude anything.

## R4-3. LEMMA N2-Z: the moment problem with zero weights  [hand proof; both families checked by direct permanent evaluation,
##       stage2/r4_alpha2.py: defects 2e-13 and 9e-14, control 99]
 DIAGONAL MODEL: no column of X_ab carries two independent forms, i.e. t_ij = g_ij lam_j(p_i) with a weight matrix g in C^{3x5}
 (zeros allowed; in the normalisation g_c = 1 of Lemma N2-GEN a zero weight is a weight 0 or infinity). Level conditions:
   (i) sum_{j: g_ij != 0} g_ij lam_j = sigma (i = c,d,e);   (ii) sum_j g_ij g_kj lam_j^2 = sigma^2 (three pairs);   (iii) sum_j g_cj g_dj g_ej lam_j^3 = sigma^3.
 A column with one nonzero weight (S1) enters only one equation of (i); a column with two nonzero weights enters two equations of (i)
 and one of (ii); only the FULL columns (three nonzero weights; set D, n = |D|) enter (iii).
 LEMMA N2-Z. Suppose every column has 3, 1 or 0 nonzero weights (in REG1: every kappa'^j has at most one zero among the rows c,d,e, or
 the column vanishes on X_ab) and psi_c, psi_d, psi_e are injective. Then, up to permuting rows and columns, X_ab is one of
   (alpha1) five full columns: one column j_1 with entries (sigma(p_c), sigma(p_d), sigma(p_e)), and four columns t with entries
            X_i(t) mu(p_i), where sigma, mu are independent forms and X_c, X_d, X_e in (C^*)^4 are orthogonal to 1, pairwise orthogonal
            (bilinear dot product) and sum_t X_c X_d X_e = 0;                         [= the unit-vector case of Lemma N2-GEN]
   (alpha2) four full columns and one single-row column: column j_1 as above, three columns (x mu(p_c), u_t mu(p_d), v_t mu(p_e)) with
            u, v in 1^perp (in C^3) zero-free and orthogonal, and a fifth column (-3x mu(p_c), 0, 0).
 In both cases X_ab CONTAINS THE TWO DOMINOES (e_c - e_d) e_{j_1}^T, (e_c - e_e) e_{j_1}^T (take p_i in ker mu); hence (SC)
 kappa^c_{j_1} = kappa^d_{j_1} = kappa^e_{j_1} = 0, and K'_{c j_1} = K'_{d j_1} = K'_{e j_1}.
 Proof. Classes of proportional forms among the full columns: mu_1, .., mu_k, lam_j = n_j mu_m; class sums A_m of g_c g_d g_e n^3 and
 B_m^{ik} of g_i g_k n^2. (iii): sum A_m mu_m^3 = sigma^3; (ii): sum B_m^{ik} mu_m^2 = sigma^2. Cubes (squares) of <= 4 (<= 3) pairwise
 non-proportional binary forms are independent.
  A. k >= 2. [k = 0: sigma = 0 and each row needs >= 3 single-row columns with forms summing to 0. k = 1: sigma in C mu_1 and each row
     needs >= 2 single-row columns whose forms sum into C mu_1. Both need more than 5 columns.]
  B. sigma != 0. [sigma = 0, k <= 4: all A_m = 0, so no singleton class: k = 2, then all B_m = 0, and a class {1,2} of size 2 has
     x_i x_k = -y_i y_k for the three pairs and x_c x_d x_e = -y_c y_d y_e (x_i = g_i1 n_1, y_i = g_i2 n_2): the product of the first three
     gives (x_c x_d x_e)^2 = -(y_c y_d y_e)^2, the last gives +: contradiction. sigma = 0, k = 5: five distinct points, case of N2-GEN.]
  C. sigma not proportional to any mu_m: then k >= 4. (n,k) = (5,4), (5,5): Lemma N2-GEN, cases (2,1,1,1) and (1,1,1,1,1).
     (n,k) = (4,4) [fifth column single-row or zero]: with nu in ker sigma, zeta_j = eta_j/nu_j on the four full columns (distinct),
     tau = sigma(eta) != 0: W_j = tau^3 om_j, c_j nu_j^2 = om_j(al_c + tau^2 zeta_j) for c = a, b, ab (the fifth column does not enter
     (ii), (iii)); (a nu^2)(b nu^2) = W nu and nu = W/(ab nu^2) give (al_a + tau^2 z)(al_b + tau^2 z)(al + tau^2 z) = tau^6 F'(z) at the
     four points: the difference is a cubic with leading coefficient tau^6 - 4 tau^6 != 0 and four roots. Contradiction.
  D. sigma = mu_1 (normalised). k <= 4, so A_1 = 1, A_m = 0 (m >= 2): the other classes have size >= 2, so k <= 3 and squares are
     independent: B_1 = 1, B_m = 0; a class of size 2 with A = B = 0 is impossible (as in B), so k = 2 with sizes (1,3), (1,4), (2,3).
     [k = 5 with sigma = mu_1 is the case |S| = 4, (1,1,1,1) of N2-GEN.]
     Class 1 = {j_1}: x_c x_d = x_c x_e = x_d x_e = x_c x_d x_e = 1 gives x = (1,1,1). Class 1 of size 2 (n = 5): the computation of
     N2-GEN, case |S| = 3, gives A_4 A_5 = 0. So class 1 is one column with entries sigma(p_i), and class 2 consists of 3 or 4 columns
     X_i(t) mu(p_i) with X_i pairwise orthogonal and sum X_c X_d X_e = 0; (i) says X_i is orthogonal to 1 for every row without
     single-row column. Size 4: (alpha1). Size 3: if the fifth column is zero, X_c, X_d, X_e are three pairwise orthogonal vectors of
     the nondegenerate plane 1^perp in C^3, hence all proportional to one isotropic vector n = (1,w,w^2), and sum X_c X_d X_e =
     3 x_c x_d x_e != 0; if the fifth column lives in row c: X_d, X_e in 1^perp, X_c orthogonal to both, and the triple sum forces
     X_c = x 1 (also when X_d, X_e are proportional and isotropic); (i) for row c gives the form -3x mu: (alpha2).              QED
 Calibration of the numerical pattern search (stage2/r4_patterns.py, 20 starts per pattern): pattern "four full + one single-row column":
 4 hits, all with a 2-dim domino space in one column; "five full": 6 hits, all (alpha1); "four full + zero column": 0 hits;
 "four full + one two-row column": 0 hits.
 COROLLARY (N2 in REG1, sub-regime "at most one zero of each kappa'^j among the rows c,d,e" [covers GEN_c := column annihilators
 zero-free, row annihilators arbitrary]): the block X_ab is (alpha1) or (alpha2); L contains two dominoes of one column j, and the row
 annihilators of c, d, e all vanish at j. In particular with zero-free ROW annihilators at (c,j), (d,j) or (e,j) N2 is impossible.
STATUS 17:58: pattern survey for two-row columns finished (4 batches); N2 inside the family (alpha) analysed by hand; explicit M* found.

## R4-4. N2 with a block of type (alpha): killed for (alpha1), (alpha2) by hand; ONE survivor (alpha3) = explicit 6-dim level space M*
 FAMILY (alpha) (contains (alpha1), (alpha2)): one column j_1 with entries sigma(p_i), four columns t with entries X_i(t) mu(p_i);
 Xi := [X_c; X_d; X_e] (3x4, rows nonzero, zeros allowed) with X_i orthogonal to 1, pairwise orthogonal, sum_t X_c X_d X_e = 0.
 Every such block is level and contains the two dominoes of column j_1.
 In N2: L_a = {(s rho_b; psi_c(p_c); psi_d(p_d); psi_e(p_e)) : sum p_i = s om} (dim 5), rho_b = rho_1 e_{j_1} + rho' != 0, and all
 4x4 subpermanents of these 4x5 matrices vanish ((Z2), a_a = 1). With p_i = y_i q_sigma + s_i q_mu (row i = y_i e_{j_1} + s_i X_i):
   deleting column j_1:  s s_c s_d s_e perm_4[rho'; X_c; X_d; X_e] = 0                                              => (E0)
   deleting a mu-column t, Laplace along column j_1, coefficients of y_c, y_d and the rest:
        perm_3[rho'; X_i; X_k] restricted to [4]-t vanishes for the three pairs and all t                           => (E1)
        rho_1 perm_3[X_c; X_d; X_e] restricted to [4]-t vanishes for all t                                          => (E2)
 Inclusion-exclusion with zero row sums and orthogonal rows:
        perm_3(Xi without column t) = -6 X_c(t) X_d(t) X_e(t),
        perm_3([rho';X_i;X_k] without column t) = (2r - 6 rho'_t) X_i(t) X_k(t) + h_k X_i(t) + h_i X_k(t) + 2 tau_ik,
   r = sum rho', h_i = <rho',X_i>, tau_ik = sum_t rho'_t X_i(t) X_k(t); summing (E1) over t gives tau_ik = 0.
 CASE A (rho_1 != 0): every column of Xi contains a zero. Impossible for (alpha1) (Xi zero-free) and for (alpha2) (three zero-free columns).
 CASE B (rho_1 = 0, rho' != 0):
   (alpha1): dividing (E1) by X_i(t) X_k(t): h_i/X_i(t) = 3 rho'_t - r for all i, t. Some h_i = 0 gives rho' = (r/3) 1, r = 4r/3, rho' = 0.
     All h_i != 0: X_i = h_i xi with xi = 1/(3 rho' - r 1), so the power sums p_1 = p_2 = p_3 of xi vanish, xi_t are the four roots of
     z^4 = const, sum 1/xi = 0, and <rho',xi> = (4 + r sum xi)/3 = 4/3, but h_i = h_i <rho',xi> needs 1. Contradiction.
   (alpha2) (X_c = x(1,1,1,-3), X_d = (u,0), X_e = (v,0)): (E1) at t = 4 gives h_d = h_e = 0; then at t <= 3 for the pair (d,e):
     rho'_t = r/3, and for (c,d): h_c = 0, i.e. rho'_4 = r/3; so rho' = (r/3) 1 = 0. Contradiction.
 THEOREM N2-Z' [rigorous by hand, given Lemma N2-GEN and Lemma N2-Z]. In stage3's family N2 the block X_ab is neither (alpha1) nor
 (alpha2). Hence N2 IS IMPOSSIBLE WHENEVER EVERY COLUMN HAS AN FK ANNIHILATOR WITH AT MOST ONE ZERO AMONG THE ROWS c, d, e -- in
 particular whenever all column annihilators are zero-free, with NO hypothesis on the row annihilators (this removes the hypothesis
 "no single-column element" of Lemma N2-GEN).
 COROLLARY. all a_r = 1, lam >= 3 for all row pairs, and every column has an FK annihilator with at most one zero entry  =>  L contains
 a single-row element e_a w^T (stage3 sec. 16 + N2-Z'; conditional on stage3's Theorem N1), and then (SR) row a is the zero of >= 2
 column annihilators.
 TWO-ROW COLUMNS (weights with two nonzero entries; kappa'^j with two zeros among c,d,e) [numerical]:
   - pattern survey stage2/r4_patterns.py: all 75 support patterns with a two-row column, 12 starts each (hit rate about 20-30% per start
     on patterns with known solutions): level blocks with injective psi found only for the patterns 011 011 111 111 111 and
     011 011 101 101 111 (rows c,d,e top to bottom, up to permutation), both in family (alpha) (2-dim domino space in the full column).
   - inside family (alpha) with zeros (stage2/r4_alphaN2.py, 60 starts each): CASE A has solutions, all of one shape
        (alpha3)  X_i = al (1,0,0,-1),  X_k = be (1,-1,-1,1),  X_l = ga (0,1,-1,0)      (one zero in every column of Xi);
     CASE B has none (0/60). For (alpha3), (E1) forces rho' = 0 (hand computation), so rho_a, rho_b are multiples of e_{j_1}.
 THE SURVIVOR M* [EXACT integer check, stage2/r4_Mstar.py: perm(J + m) = 120 at 400 random integer points of the 6-dim space, (Z2) on
 L_a and L_b at 200 points each, 0 violations]: with j_1 = 0, rows a..e = 0..4,
     M* = span{ -E_a0 + (e_0 + m_a al(e_1 - e_4)) in row c,   -E_b0 + (e_0 + m_b al(e_1 - e_4)) in row c,   (e_c - e_d)e_0^T,   (e_c - e_e)e_0^T,
                (al(e_1-e_4) ; -be(e_1-e_2-e_3+e_4)) on rows (c;d),    (al(e_1-e_4) ; -ga(e_2-e_3)) on rows (c;e) }
 is a 6-dim LEVEL space of exactly the N2 shape for L_a + L_b (lam_ab = 4, no single-row element, rows a, b supported in column 0).
 So N2 cannot be excluded from L_a + L_b alone. M* contains a 3-dim space of single-column elements of column 0
 ({y e_0^T : sum y = 0, m_a y_a + m_b y_b = 0}): a SPLIT FREE COLUMN. In a 9-dim L with b_0 = 1 this gives z'^0 = 3 and, by (Z3)
 transposed, L^0 is a (5,1) space with defect line (Z'^0 + C1)^perp: an 8-dim level space with a deletable column would exist.
 (The numerical solution found earlier by r4_N2inj.py is of this type.)
 Direct confirmation of the derivation (Z2) => (E0),(E1),(E2) (stage2/r4_alphaLa.py: the original condition "all 4x4 subpermanents
 vanish on L_a" evaluated at random points, family (alpha) with Xi, rho_b, om free; 40 starts): 10 solutions, ALL with one zero in every
 column of Xi, rho' = 0, rho_1 != 0 (= (alpha3)); 30 starts do not converge. So inside family (alpha), N2 means M*.

## R4-5. State of REG1 (all a_r = b_c = 1, dim 9) after round 4, and the precise list of surviving configurations
 The theorem "no 9-dim level space in REG1" is NOT proved. What is proved / reduced (zero-freeness no longer needed where stated):
  (1) [conditional as before: R3-1 num-assisted, stage3's N1] all annihilators zero-free: impossible (Theorem GEN).
  (2) [rigorous given N2-GEN, N2-Z; + stage3 sec. 16] all a_r = 1, lam >= 3 for all row pairs, every column annihilator with at most one
      zero: L contains a single-row element. (Transposed statement for columns.) So zero-free COLUMN annihilators + lam >= 3 on the row
      side is contradictory without any hypothesis on the row annihilators (no single-row element by SR).
  (3) [rigorous] a single-row element is a defect phenomenon: z_r <= 4 - e(L_r), z_r <= 3, and z_r = 3 => an 8-dim level space with a
      deletable row and a (5,1) space L_r exist (rows' open (DI_5) at e = 1; TC5 excludes the two-column defect lines).
  (4) [rigorous + numerical for two-row columns] N2 with a "diagonal" block (no column of X_ab carries two independent forms) forces
      L_a + L_b = M* (explicit), hence a split free column, hence again a (5,1) space.
 SURVIVING CONFIGURATIONS in REG1 (each also in transposed form):
  (S-I)   a MINIMAL PAIR (lam = 2) in which at least one annihilator of the pair, or one of the column annihilators used by GEN-2,
          has a zero. Known: one zero in one annihilator of the pair => Type I_0 (round 2). Not classified beyond that; the tool is
          criterion (G) (Gamma_T), which allows zeros.
  (S-II)  all row lam >= 3 and a SINGLE-ROW ELEMENT e_a w^T (this is what stage3's N1 produces): then z_a <= 3, every column in supp(w)
          has kappa'^j_a = 0, e(L_i) >= z_a for the other rows i, e(L_a) <= 4 - z_a. Sub-case z_a = 3: the (5,1) problem.
          Sub-cases z_a = 1, 2: L_a is a (5,e) space with e <= 3, 2 -- such 4x5 spaces exist ((5,2) occurs in the 7-dim examples), so
          defect theory alone does not exclude them; what is missing is a use of the other four rows having 4-dim projections.
  (S-III) all row lam >= 3, no single-row element: family N2 with
          (a) block (alpha3) / M*: contains a split free column (so it is (S-II) transposed with z' = 3: the (5,1) problem);
          (b) a NON-DIAGONAL block: some column of X_ab carries two independent forms, so that kappa'^j has >= 2 zeros among c,d,e; in
              the extreme case of five generic columns: all kappa'^j in span(e_a,e_b) and two identically vanishing cells (a,j_a), (b,j_b).
              Level blocks of this kind exist (numerically); not analysed further.
 THE COMMON CORE: every surviving configuration I can make explicit contains a partially free line (split free column in M*; the
 dominoes of (alpha1)/(alpha2)), i.e. lives in rows'/verifyfl's defect regime "(5,e) spaces with e <= 3"; the sharpest single open
 statement is: NO (5,1) SPACE (rows' (DI_5) at e = 1), which kills z = 3 and N2 with a diagonal block.
 NOT DONE: classification of minimal pairs with zeros (S-I); N2 with non-diagonal blocks (S-III b); (S-II) with z = 1, 2; a hand proof
 that Case B has no solution for Xi with zeros (numerical 0/60 and 0/40 only); exhaustive pattern survey with more starts.
 Runs to report (round 4): r4_block.py first run (60 starts) hit its 150 s timeout without output (1m28 CPU), rerun with 14 starts 22 s;
 r4_N2inj.py: one run interrupted by the session restart, one hit its 100 s timeout after 2 starts; r4_N2fast.py hit a 110 s timeout
 (1m40 CPU) with one start; r4_alphaN2.py (60 s) was started while batch 2 of r4_patterns.py was still running (two processes at once
 for about a minute -- against the one-run-at-a-time habit); the four r4_patterns.py batches took 100-125 s each.
STATUS 18:00: RESULT-R4 at the top; R4-5 written. Final report follows.

## R4-6. First-order extension test; M* lies in no 9-dim level space  [exact at one parameter set + numerical scan]
 For a linear subspace M of a level space L and t in L, m in M: perm(J + m + eps t) = 120, so sum_ij t_ij perm_4((J+m)^(ij)) = 0.
 Hence L lies in T_1(M) := annihilator of the span of the cofactor matrices C(J + m), m in M; and dim L <= dim T_1(M).
 (rows used the same space for the 7-dim examples.)
 M* (parameters m_a, m_b, al, be, ga; stage2/r4_Mstar_ext.py, r4_Mstar_scan.py): the cofactor matrices span a 17-dim space
   - exactly (rational arithmetic, 40 integer points) for (m_a,m_b,al,be,ga) = (1,2,1,1,1);
   - in floating point (relative 17th singular value >= 1e-3, 18th = 0) for 300 random integer parameter sets, 100 random complex ones
     and the special loci m_a = m_b, m_a = -m_b, m_a = 0, m_a = m_b = 0, sign changes of al, be, ga.
 So dim T_1(M*) = 8 and M* lies in no 9-dim level space. Consequence for REG1 (and for any 9-dim level space with all a_r = 1):
 family N2 with a DIAGONAL block is impossible  [chain: Lemma N2-Z (hand) / pattern survey for two-row columns (numerical) =>
 family (alpha); (Z2) on L_a => (alpha3) and rho' = 0 (hand for (alpha1), (alpha2); numerical for Xi with zeros) => M* => T_1].
 Remark: the test gives nothing on the 4-dim blocks alone (stage2/r4_T1.py: dim T_1(X_ab) = 11 for 8 generic blocks, 13 for 5 blocks of
 family (alpha)); it needs the 6-dim L_a + L_b.
 Updated survivor (S-III): only (b), N2 with a non-diagonal block, remains.
STATUS 18:04: R4-6 added; RESULT-R4 updated. Final report follows.
 Sanity of the test (stage2/r4_T1_sanity.py): for the 7 known example spaces and for random subspaces M of them, L lies in T_1(M)
 (pairings <= 6e-12) and dim T_1(L) = 8 for every 7-dim example (rows' "first-order extension space").
STATUS 18:04: sanity check of (FO) added. [R4-5's item (S-III)(a) is superseded by R4-6: M* is excluded at dim 9.] Round-4 final report sent.

# ROUND 5 (start 18:06, budget 90 min -> ends ~19:36). Targets: (1) (FO) for M* as a theorem for all parameters + hand proofs for the
# numerical parts of round 4; (2) FO on the survivors (S-III b), (S-I); (3) what remains in REG1, and what survives when some a_r >= 2.
STATUS 18:08: round-4 handback was not sent (the round-5 message arrived first); the round-4 results are in RESULT-R4 and R4-1..R4-6.
 Key observation for (1): M* is a hyperplane of the 7-dim level space W_7 = {full free column 0} (+) {(a_c X_c; a_d X_d; a_e X_e)}
 (X_c = e_1 - e_4, X_d = e_1 - e_2 - e_3 + e_4, X_e = e_2 - e_3 on rows c, d, e), a "free column + strongly level 3-dim" space;
 M* = W_7 cap {a_c/al + a_d/be + a_e/ga + m_a y_a + m_b y_b = 0}.
STATUS 18:12: (1) done for M* (theorem, exact certificate) and for Cases A/B of family (alpha) (hand proofs). Lemma N2-Z corroborated
 (stage2/r4_patterns.py, the 16 patterns with 3/1/0-weight columns, 22 starts each: solutions only for "five full" (5 hits) and "four full
 + one single-row column" (8 hits), all with the 2-dim domino space).

## R5-1. THEOREM FO-M*: dim T_1(M*) = 8 for ALL parameters  [structural proof + exact parameter-free certificate, stage2/r5_FO_Mstar.py]
 W := {t : column 0 = y in C^5; row c = y_c e_0 + a_c X_c, row d = y_d e_0 + a_d X_d, row e = y_e e_0 + a_e X_e; rows a,b in C e_0}
 (X_c = e_1 - e_4, X_d = e_1 - e_2 - e_3 + e_4, X_e = e_2 - e_3; coordinates (y,a) in C^5 x C^3), W_7 := W cap {sum y = 0}.
 (a) perm(J + w) = 120 + 24 sum y on W, so W_7 is a 7-dim level space (full free column 0 + a 3-dim strongly level part), and
     M* = W_7 cap ker(phi), phi = a_c/al + a_d/be + a_e/ga + m_a y_a + m_b y_b  (checked on the basis of M*).
 (b) For t in C^{5x5} and w = (y,a):  <C(J+w), t> = 24 tau_0 + sum_k (1 + y_k) Q_k^t(a),  tau_0 = sum_i t_i0,
     Q_k^t(a) = sum_{i != k} sum_{j=1..4} t_ij perm_3(N without rows i,k and column j), N = the 5x4 matrix of the columns 1..4 of J + w.
     Exact facts (rational polynomial arithmetic): (s1) all perm_4(N without row i) = 24; (s2) every Q_k is multilinear in (a_c,a_d,a_e)
     and Q_c, Q_d, Q_e do not involve a_c, a_d, a_e respectively (obvious from the definition); (s3) T_1(W_7) = {t : Q_k^t = -(24/5) tau_0 for
     all k} has dimension 8 (rank 17), = W_7 (+) C(1 e_0^T - J/5).
 (c) m := (m_a,m_b) != 0. On M*, for fixed a the vector y runs over an affine space with direction 1^perp cap m^perp; so t in T_1(M*) iff
     Q_k(a) = q(a) + m_k p(a) (k = a,b; m_k = 0 for k = c,d,e) and 24 tau_0 + 5q + (m_a + m_b - <mu^,a>) p = 0, mu^ = (1/al,1/be,1/ga).
     q = Q_c = Q_d = Q_e does not depend on a_c, a_d, a_e: q is constant. Then (m_a + m_b - <mu^,a>) p(a) is constant, so p = 0
     (mu^ != 0), and t lies in T_1(W_7).
 (d) m = 0. M* = 1^perp x {<mu^,a> = 0}: t in T_1(M*) iff all Q_k are equal to -(24/5) tau_0 on the plane <mu^,a> = 0. Q_c, Q_d, Q_e are
     functions of two variables and the plane projects onto each coordinate plane (mu^ zero-free): they are constant. Q_a, Q_b are
     multilinear and constant on the plane: Q - const = R <mu^,a> with R constant (degree 1 in each variable, mu^ zero-free).
     Exact (s4): on T' := {t : all conditions of (s3) except the linear coefficients of Q_a, Q_b} (dim 10) the linear parts of Q_a and
     Q_b are multiples of (0,1,0) (the a_d-direction) only; R mu^ = x(0,1,0) with mu^ zero-free forces R = 0. So t lies in T_1(W_7).
 THEOREM FO-M*. For all m_a, m_b in C and al, be, ga in C^*: T_1(M*) = T_1(W_7) = W_7 (+) C(1 e_0^T - J/5), of dimension 8.
 Hence every level space containing M* has dimension <= 8.                                                                    QED

## R5-2. Hand proofs for the numerical parts of R4-4 inside family (alpha)  [rigorous]
 Family (alpha): Xi = [X_c;X_d;X_e] 3x4, rows nonzero, orthogonal to 1, pairwise orthogonal, sum_t X_c X_d X_e = 0. Xi has no zero column
 (three nonzero pairwise orthogonal vectors of the nondegenerate plane 1^perp in C^3 are multiples of one isotropic n = (1,w,w^2), and
 then the triple sum is 3 x_c x_d x_e != 0).
 CASE A (every column of Xi has a zero) => Xi = Xi* := (al(e_p - e_q); be(1_{pq} - 1_{rs}); ga(e_r - e_s)) up to permutations.
   Supports S_i: |S_i| >= 2 (zero sum); |S_i cap S_k| != 1 (orthogonality); S_c cap S_d cap S_e empty. A row with full support forces the
   other two supports to be disjoint, hence complementary pairs, and the shape Xi*. Without a full row: (3,3,3) and (3,3,2): the
   2-set (or third 3-set) meets the triple intersection; (3,2,2): the two 2-sets lie in the 3-set, meet in 1 point or coincide;
   (2,2,2): two supports coincide and then X_i.X_k = 2 kappa kappa' != 0. All impossible.
   For Xi*: (E1) gives h_c = h_e = 0 (zeros of X_c, X_e against X_d), rho'_p = rho'_q, rho'_r = rho'_s, and the two remaining equations
   give rho' = 0 (R4-4).
 CASE B (rho_1 = 0, rho' != 0) IS IMPOSSIBLE for every Xi of the family. (E1) at a column t reads
       (2r - 6 rho'_t) X_i(t) X_k(t) + h_k X_i(t) + h_i X_k(t) = 0   (three pairs),  and tau_ik = 0.
   Consequences per column: three nonzero entries: h_i = (3 rho'_t - r) X_i(t) for all i; exactly X_l(t) = 0: h_l = 0 and
   h_i/X_i(t) + h_k/X_k(t) = 6 rho'_t - 2r; only X_i(t) != 0: h_k = h_l = 0.
   - all h = 0: rho'_t = r/3 on every column with >= 2 nonzero entries; for a column whose only nonzero entry is X_i(t): h_i = 0 reads
     sum over such columns of (rho'_t - r/3) X_i(t) = 0. A row cannot own two such columns (the other two rows would live on the two
     remaining columns and be proportional, not orthogonal), so rho' = (r/3) 1, r = 4r/3, rho' = 0.
   - h_c != 0: X_c is zero-free (a zero of X_c under a nonzero entry of another row gives h_c = 0; zero columns do not exist).
     All three h != 0: Xi zero-free, contradiction 4/3 = 1 (R4-4). h_c, h_d != 0 = h_e: a column with X_e(t) != 0 has three nonzero
     entries and h_e = 0 gives 3 rho'_t = r, hence h_c = 0; so X_e = 0. Contradiction. h_c != 0 = h_d = h_e: no column has three
     nonzero entries, so supp X_d, supp X_e are complementary pairs and Xi = Xi* with full row c; rho'_t = r/3 + h_c/(6 X_c(t)) for all t;
     summing: r = 0; then h_c = <rho',X_c> = (4/6) h_c, so h_c = 0. Contradiction.
 RESULT: inside family (alpha), N2 forces Xi = Xi* and rho_a, rho_b in C e_{j_1}, i.e. L_a + L_b = M*  -- now a HAND proof; with
 Theorem FO-M*: family (alpha) is excluded at dimension 9 for all parameters, rigorously (given Lemma N2-GEN / N2-Z for the reduction
 to family (alpha) when all columns have 3, 1 or 0 nonzero weights).
 STILL NUMERICAL: that every diagonal block with a TWO-ROW column lies in family (alpha) (pattern survey of R4-4). Caveat found now:
 for the pattern "four full columns + one two-row column" a parameter count gives 7 equations in 7 unknowns, so ISOLATED solutions
 are not excluded by a search with 12-20 starts. This part is therefore weaker than I stated in R4-4.
STATUS 18:28: session was cut off at ~18:15 (usage limit) and resumed 18:20 with 75 more minutes. New inputs read: stage3's Theorem N2-X
 (N2 does not occur; hence Theorem N: all a_r = 1, lam >= 3 => single-row element; not yet verified), Lemma S3-1 (z_i <= 2 under (H1)),
 verifyfl's SPLIT / FS / HYP. Consequence for my list: (S-III) is settled by stage3 if N2-X is verified; my results on N2 (N2-GEN, N2-Z,
 N2-Z', FO-M*) are an independent confirmation on the diagonal sub-families and no longer needed for the chain.

## R5-3. Consistency of M* with stage3's N2-X, and the kernel condition  [rigorous derivation; small numerics]
 M* is a 6-dim level space of N2 shape for L_a + L_b; N2-X says N2 does not occur in a 9-dim L with all a_r = 1. No conflict: in M* the
 planes P_c, P_d, P_e meet in the unit vector e_0 (stage3's case (alpha), sub-case v_0 = e_j), which stage3 excludes with conditions
 coming from L_c, L_d, L_e; and by Theorem FO-M* no 9-dim level space contains M*. The two exclusions are independent.
 KERNEL CONDITION (valid for every N2 block, diagonal or not): for x in X_ab let C(x) be the symmetric zero-diagonal 5x5 matrix
 C(x)_{jl} = perm_3(x[cde; [5]-{j,l}]). (Z2) on L_a at first order in the row-b parameter gives C(x) rho_b = 0 for all x in X_ab, and
 likewise C(x) rho_a = 0: the matrices C(x) have a common kernel vector. [(E1),(E2) of R4-4 are this condition in family (alpha).]
 Numerics (stage2/r5_kernel.py part 1): for 7 level blocks found by plain LM (4 generic non-diagonal, 3 of type (alpha1)) the common
 kernel is 0, so none of them is an N2 block. Part 2 (search for level blocks WITH a kernel vector) hit its 115 s timeout without
 output and was not repeated after N2-X arrived.

## R5-4. The first-order extension test for a row: general formulas  [rigorous; valid for every row of every level space]
 With perm(u) = <u_r, G(u')> (G = vector of the five 4x4 subpermanents of the other four rows) and t = (t_r; t'):
       D_t perm(u) = <t_r, G(u')> + <u_r, D_{t'} G(u')>.
 (a) X = L_r (row r = 0):  T_1(L_r) = {t : <t_r, G(J'+xi)> + D_{t'} N(J'+xi) = 0 for all xi in L_r},  N = sum_j G_j the 4x5 level function.
     It contains L_r (+) e_r (x) (C(L_r) + C1)^perp, of dimension dim L_r + 4 - e(L_r).
 (b) M_r := L_r (+) e_r (x) Z_r (always inside L; a level space with deletable row r):
       T_1(M_r) = {t : D_{t'} G(Y) in Z_r^perp and <t_r, G(Y)> + <1, D_{t'} G(Y)> = 0 for all Y in J' + L_r};
     it always contains M_r (+) C(e_r 1^T - J/5)  [D_{J'} G(Y) = 4 G(Y) - D_xi G(Y), D_xi G(Y) in C(L_r), <1,G> = 120], so
     dim T_1(M_r) >= dim L_r + z_r + 1, and L inside T_1(M_r) needs  dim L <= dim T_1(M_r).
     If z_r = 4 - e(L_r) (the free part is as large as L_r allows; e.g. z_r = 2 with L_r a (5,2) space) then dim M_r = dim L_r + 4 - e, and a
     9-dim L needs at least 9 - dim M_r - 1 first-order deformations t' of L_r, modulo L_r + C J', with D_{t'} G(J' + xi) in C(L_r) + C1
     for all xi ("first-order deformations preserving the defect space"). rows found dim T_1 = 8 for all 27 known 7-dim level spaces
     with a deletable line (types (3,0), (4,1), (5,2), (6,3)): these L' are rigid, so none of them is the L_r of a 9-dim level space with
     the full free part; in particular stage3's case z_i = 2 with L_i a (5,2) space of a known type is excluded.
 (c) Nothing here uses a_r = 1: the test applies verbatim to rows with a_r >= 2 (then dim L_r = 4 + a_r <= 7 by the checked L_gct_215,
     so a_r <= 3 in every 9-dim level space).
STATUS 18:37: second-order test (FO2) found, sanity-tested and applied; candidates for L_r surveyed. Writing up.

## R5-5. The second-order extension test (FO2)  [lemma rigorous (two lines); applications numerical; stage2/r5_FO2.py, r5_FO2_apply.py]
 LEMMA FO2. Let M be a linear subspace of a level space L. For m in M put q_m(t,t') := D_t D_t' perm(J + m) (the symmetric bilinear form
 with entries perm_3((J+m) without rows i,k and columns j,l)). Then L lies in T_1(M) and L is totally isotropic for every q_m, m in M
 (and for all their linear combinations). Hence
        dim L  <=  dim T_1(M) - ceil( rank(q restricted to T_1(M)) / 2 )        for every q in span{q_m : m in M}.
 Proof: perm(J + m + eps t) = 120 for t in L, m in M; the eps- and eps^2-coefficients vanish; polarise on the linear space L.   QED
 SANITY (bug caught here: my first version used the hermitian instead of the bilinear restriction and gave bounds 5 < 7 on ex1; fixed):
 on the 7 known example spaces, with M = L and with random subspaces M of codimension 2, the bound is >= dim L in all 14 cases, and it
 is EQUAL to dim L for M = L in all of them (dim T_1 = 8, rank 1, bound 7 for the six 7-dim spaces; 6, 1, 5 for K5): FO2 proves
 numerically that each known space is a maximal level space.
 APPLICATIONS (numerical; random m, random combinations of five q_m):
   - M* (three parameter sets): dim T_1 = 8, rank 1: every level space containing M* has dim <= 7 (so it is W_7 or M* itself).
   - generic NON-DIAGONAL level N2 blocks X_ab (4-dim; stage2/r4_block.py solutions; 26 blocks in two runs): dim T_1 = 11, rank 7,
     bound 7 in all 26: such a block lies in no level space of dimension 8 or 9. So the block alone already excludes them -- no use of L_a, L_b.
   - level N2 blocks of family (alpha) (10 blocks, one of them with two-row columns): dim T_1 = 13, rank 8, bound 9: not excluded at second order (they are excluded by
     hand, R4-4).
   - candidates for L_r, i.e. 5-dim level spaces of 4x5 matrices with all 4x4 subpermanents identically zero ((Z2); necessary for
     every row with a_r = 1 of a 9-dim level space), found by LM (stage2/r5_Lr.py, r5_Lr3.py; verified on fresh points):
       two with all row projections of dim <= 3 (as Lemma C requires): (dim T_1, rank) = (9,3) and (10,5): bound 7 and 7;
       one with two rows of 4-dim projection (not admissible): (11,6): bound 8.
     All three contain single-row and single-column elements ("cross" shape). A third LM output was spurious (not level on fresh
     points) -- the sample of 45 points was too small for a quartic in five variables; with 85 points 0 of 4 starts converged in 250
     iterations, so this survey is thin: 2 admissible candidates only.

## R5-6. What remains in REG1 after round 5, the uniform formulation, and what carries over to a_r >= 2
 A. UNIFORM FORMULATION (every row r with a_r = 1 of a 9-dim level space L; dually for columns with b_c = 1):
    (Q-r)  L_r is a 5-dim linear space of 4x5 matrices with  (i) sum_j perm_4((J' + xi)^(j)) = 120,  (ii) perm_4(xi^(j)) = 0 for all j
           and all xi in L_r,  (iii) every row projection of dim <= 3 (Lemma C) and every column projection of dim <= 3,
           (iv) FO2-bound(L_r) >= 9, and the same for M_r = L_r (+) e_r (x) Z_r.
    REG1 means: all five L_r and all five L^c are such spaces. The two admissible candidates found so far fail (iv).
    A classification of the solutions of (i)-(iii), or a proof that (iv) fails for all of them, would exclude every 9-dim level space
    having one line with full projection -- a statement about 4x5 matrices only.
 B. REMAINING CASES IN REG1 (using stage3's Theorem N, not yet verified, for B2):
    (B1) a MINIMAL PAIR (lam_{rr'} = 2, rows or columns). Then L contains the 8-dim level space L_r + L_r' (every element is a sum of
         an element with zero row r and one with zero row r'), both summands satisfying (Q-r); no 8-dim level space is known at all.
         Known: impossible if all annihilators are zero-free (Theorem GEN); one zero in one annihilator of the pair: Type I_0.
         FO/FO2 need explicit candidates for L_r, L_r'; I have none (the pair classification lives on the side of the relations).
    (B2) no minimal row pair: a single-row element exists (Theorem N), z_r <= 2 (stage3 S3-1), L_r is a (5,e) space with e <= 4 - z_r,
         and L lies in T_1(M_r) (R5-4): for z_r = 2 and L_r of type (5,2), L_r must have first-order deformations preserving its
         defect space; all 27 known deletable-line spaces are rigid (rows). Same for columns; if neither a minimal row pair nor a
         minimal column pair exists, L contains e_a w^T and y e_j^T with w_j y_a = 0 (P_2), kappa'^l_a = 0 on supp(w), kappa^i_j = 0 on supp(y).
    (B3) N2: excluded by stage3's N2-X (unverified). Independently excluded here on the sub-families: zero-free column weights
         (N2-GEN + N2-Z', hand), family (alpha) incl. M* (hand + Theorem FO-M*), generic non-diagonal blocks (FO2, numerical).
 C. WHAT CARRIES OVER WHEN SOME a_r >= 2:
    - valid for every level space, no hypothesis on a_r: FO and FO2 (Lemma FO2, Theorem FO-M*: no level space of dim >= 8... precisely:
      every level space containing M* lies in the 8-dim T_1(M*)); (Z3) z_r <= 4 - e(L_r) and R5-4; (Z1) in the form "a sub-block of row r
      is ell-supporting iff it contains the support of an annihilator of row r with sum 1"; the kernel condition is specific to N2.
    - a_r <= 3 for every row of a 9-dim level space (dim L_r = 4 + a_r <= 7 by the checked L_gct_215), and a_r = 3 makes L_r an
      EXTREMAL 7-dim 4x5 level space.
    - (Z2) weakens: for a row with a_r >= 2 one only gets G(xi) in pi_r(L^)^perp (dimension a_r - 1) for xi in L_r: the five 4x4
      subpermanents of L_r span at most an (a_r - 1)-dim space of functions' values. So (Q-r) has an analogue with (ii) replaced by
      "G(xi) lies in a fixed (a_r - 1)-dim subspace of 1^perp", dim L_r = 4 + a_r.
    - need all a_r = 1 (or at least a_r = 1 for the rows involved): Types I/II and GEN-2 (pairs of rows with a = 1; Type I' for (2,1)),
      R3-1, stage3's N1/N/N2-X, hence Theorem GEN and everything built on N2 (N2-GEN, N2-Z, N2-Z'); SR/SC keep the form "some annihilator
      of the line vanishes there" but lose the uniqueness that makes them zero-entry statements.

## R5-7. Two additions
 (a) COROLLARY of Theorem FO-M* [rigorous]: every level space containing M* has dimension <= 7. Proof: L lies in W_7 (+) C tau,
     tau = 1 e_0^T - J/5, and P_2 = 0 on L; an 8-dim L would be all of W_7 (+) C tau and contain tau, but P_2(tau) = (0 - 0 - 20 + 4)/2 = -8
     (P_2(t) = ((sum t)^2 - sum_i s_i^2 - sum_j c_j^2 + sum t_ij^2)/2 with row sums 0 and column sums (4,-1,-1,-1,-1)).
 (b) Shape of the two admissible candidates for L_r (R5-5): the first is a CROSS SPACE -- every element is supported on one row i and one
     column j of the 4x5 block (2-dim single-row part vanishing at column j, 2-dim single-column part vanishing at row i, one more
     element); the second has two rows that are multiples of e_j, a 2-dim single-column part in column j and one single-row element.
     Both are of type (B2) (sparse elements), and both fail FO2.
STATUS 18:38: R5-5 .. R5-7 written. Final report (rounds 4 and 5) follows.
STATUS 18:40: one more (Q-r) run (r5_Lr4.py, seed 21) reached its 118 s timeout with 0 of 3 starts converged; the survey stays at 2 admissible
 candidates. Runs to report (round 5): r5_kernel.py part 2 hit its 115 s timeout without output; r5_Lr3.py and r5_Lr4.py were each
 launched once with a clobbered trial/iteration count (ran nothing; I waited 100 s on the second before noticing); r5_Lr4.py with 85
 sample points: 0 of 4 starts in 110 s. All other round-5 runs < 60 s. Final report (rounds 4 and 5) sent.

# ROUND 6 (start 18:41, budget 90 min -> ends ~20:11). Target: classify the solutions of (Q-r), prove FO2 <= 8 on each component (or find
# the weakest hypothesis under which that is provable); (B1): FO2 for minimal pairs.
STATUS 18:46: plan. (Q-r) in the squarefree algebra A = C[y]/(y_j^2): rows Xi_i in A_1; (ii) <=> Xi_1 Xi_2 Xi_3 Xi_4 = 0 in A_4 on X; level <=>
 the coefficient sums of the elementary symmetric E_1, E_2, E_3 of the Xi_i vanish. Observed: all three solutions found so far vanish on an
 s x t block with s + t >= 6 (Frobenius-Koenig type); but non-FK solutions of (ii) exist (two rows on two columns of the form
 (x,y), (-x,y) plus two rows on the other three columns), so the classification is not just FK. First experiment: (B1) through the plane
 X_{rr'} of a minimal pair alone (2-dim, all 3x3 subpermanents identically 0, P_1 = P_2 = 0): sample such planes and compute FO2.
STATUS 18:58: cross family treated by hand (T_1 explicit, bound 7 for b != 0); the locus b = 0 is the split-free-line locus (bound 9 at
 second order, no 8-dim extension found); planes of minimal pairs alone give FO2 bounds 10-12 (not enough). Census batches running.

## R6-1. (Q-r) in the squarefree algebra; Frobenius-Koenig families  [rigorous remarks]
 A = C[y_1..y_5]/(y_j^2); a 4x5 matrix xi <-> its row forms Xi_1..Xi_4 in A_1. Then
   (ii)  all 4x4 column-deletion subpermanents vanish  <=>  Xi_1 Xi_2 Xi_3 Xi_4 = 0 in A_4;
   (i)   level  <=>  the coefficient sums of the elementary symmetric E_1, E_2, E_3 of the Xi_i vanish (E_4 = 0 by (ii)).
 (ii) holds identically on each of the following linear spaces of 4x5 matrices (zero block s x t with s + t >= 6):
   FK(1,5) a zero row;  FK(2,4) two rows supported in one common column j_0;  FK(3,3) three rows supported in two common columns;
   FK(4,2) two zero columns;  and on CROSS(i_0,j_0) = matrices supported on one row and one column (inside FK(2,4), zero block 3x4).
 But (ii) also has non-FK linear solutions (e.g. rows 1,2 = (x,y,0,0,0), (-x,y,0,0,0) and rows 3,4 supported on the last three columns),
 so a classification cannot be a pure zero-pattern statement. On FK(2,4) (rows i_1,i_2 = s_1 e_{j0}, s_2 e_{j0}; rows i_3,i_4 = p, q):
   P_1 = s + sum p + sum q,  P_2 = s(sum' p + sum' q) + sum p sum q - <p,q>,  P_3 = s (sum' p sum' q - <p,q>'),   s = s_1 + s_2, ' = without j_0,
 so a level subspace has s = 0 identically (a domino (e_{i1} - e_{i2}) e_{j0}^T direction plus a 2-row level space on rows i_3,i_4) or
 sum' p sum' q = <p,q>' identically. In a 9-dim L, an L_r of type FK(2,4) forces lam_{r i_1}, lam_{r i_2} >= 4 and m_{i_3 i_4} >= 3.

## R6-2. THEOREM (cross family): every level space containing X(a,b), b != 0, a not in C1, has dimension <= 7  [hand proof; formula for
##       T_1 and all ranks confirmed numerically for 6 random complex and 7 special parameter sets, stage2/r6_cross.py]
 Rows 0..4 with r = 0 (zero row), i_0 = 1, j_0 = 0. W' := {t(y,w): column 0 = y in C^5, row 1 = y_1 e_0 + w, w on columns 1..4};
 perm(J + t(y,w)) = 24(1 + y_1) + (24 + 6 sum w) sum_{i != 1}(1 + y_i); W_7' := {sum y = 0, sum w = 0} is a 7-dim level space (full free
 column 0 + three single-row elements of row 1).  CROSS FAMILY (the 5-dim level subspaces of CROSS(1,0) with zero row 0 whose row-1
 projection is 3-dim):     X(a,b) := {t(y,w) : y_0 = 0, sum y = 0, sum w = 0, b y_1 + <a,w> = 0},   (a mod C1, b) in P^3.
 [The other maximal level subspace of the cross, {sum_{i != 1} y_i = 0, y_1 + sum w = 0}, only gives X = (3-dim single-row space) (+)
 (2-dim single-column space), i.e. z = 3.]
 Cofactors of U = J + t(y,w) (direct Laplace expansions): C_i0 = 24 + 6 sum w (i != 1), C_10 = 24, C_1j = 24 + 6(sum y - y_1),
 C_ij = 6(1 + y_1) + 2(3 + sum w - w_j)(3 + sum y - y_i - y_1) (i != 1, j >= 1). On X(a,b), with S(t) = sum of all entries,
 rho_i = sum_{j>=1} t_ij, gamma_j = sum_{i != 1} t_ij, t_i' = (t_ij)_{j>=1}:
     <C(U),t> = 24 S - 6 <y,rho> - 6 <w,gamma> + 2 sum_{i=2,3,4} y_i <w,t_i'> + 2 y_1 <w,gamma>.
 Degree 2 on X (b != 0, a not in C1): t_i' = u + c_i 1 (i = 2,3,4) and gamma = u mod 1; degree 1: gamma in C1 + C a, rho_2 = rho_3 = rho_4
 = lam, rho_1 = lam + nu b; degree 0: S = 0. Result (dim 10):
     T_1(X(a,b)) = { column 0 arbitrary; row 1 arbitrary; row 0 on columns 1..4 = -2 nu a + c_0 1; rows 2,3,4 on columns 1..4 = nu a + c 1 }
                   with  sum_{j>=1} t_1j = nu (sigma_a + b) + 4c  and  S(t) = 0     = W_7' (+) (the three directions nu, c, c_0).
 Second order: P_2 vanishes on W_7', and for t in W_7', t' in T_1:  P_2(t,t') = -(1/2)[ y_0 (4c_0' - 4c' - 3 nu' sigma_a) + nu' (b y_1 + <a,v>) ].
 The functionals y_0 and b y_1 + <a,v> are independent on W_7' (their common kernel is X(a,b)), so the pairing has rank 2; the direction
 c = c_0 (which is 1 e_0^T - J/5 up to scale) pairs to 0 with W_7' and has P_2 = -8 != 0. Hence rank(P_2 on T_1) = 5 and
 dim L <= 10 - 3 = 7 for every level space L containing X(a,b).                                                                QED

## R6-3. The locus b = 0 (and a in C1): the split free line  [T_1 by hand; extension search numerical]
 X(a,0) = (3-dim space of single-column elements of column 0 on rows 1..4) (+) (2-dim space of single-row elements of row 1), so as an
 L_r it has z' = 3. Here T_1 is 13-dim (same computation: block rows 0,2,3,4 x columns 1..4 with all four rows in span(1,a)), a generic
 q_m has rank 8, FO2 bound 9: NOT excluded at second order. This is exactly the (5,1) / split-free-line situation (rows' (DI_5) at
 e = 1; excluded under (H1) for the other family of lines by stage3's S3-1). Direct search (stage2/r6_cross_b0.py, a = (1,2,3,5)): level
 spaces of dimension 7 containing X(a,0) are found at once (4/4 starts, residual 1e-10 .. 1e-7: W_7'), dimension 8: 6/6 starts end at
 the same residual 0.775. So no 8-dim level space through X(a,0) is visible; not a proof.
STATUS 19:05: censuses done for the general search and for FK(2,4), FK(3,3); FK(1,5), FK(4,2) running. Writing R6-4 .. R6-6.

## R6-4. Numerical census of (Q-r) solutions and their FO2 bounds  [numerical; every solution verified on fresh points]
 (a) GENERAL search (stage2/r5_Lr3.py, r6_census.py: 5-dim X, level + (ii), rows of rank <= 3; about 20 starts in four batches, LM often
     stuck at residual 0.75): 6 verified solutions. ALL vanish on a 2x4 block (type FK(2,4); one is a cross space):
        row proj [2,3,1,1] (three times): dim T_1 = 9, rank 3, bound 7;   [1,3,1,1] cross: (10,5), bound 7;
        [1,2,1,2]: (12,7), bound 8;   [3,1,1,3]: (12,7), bound 8.
     (One more solution of the unconstrained search has two rows of 4-dim projection, not admissible: (11,6), bound 8.)
 (b) inside FK(2,4) (stage2/r6_fk.py 24; only the level condition remains; 14 starts): 9 verified solutions, row projections
     (1,1,2,3), (1,1,3,3), (1,1,2,2), with 1-2 single-row and 1-2 single-column dimensions: ALL have dim T_1 = 9, rank 3, bound 7.
 (c) inside FK(3,3) (10 starts): 7 verified solutions, ALL with a 3-dim single-row space in the fourth row (z = 3):
     (dim T_1, rank, bound) = (12,7,8) twice, (11,6,8) twice, (13,8,9) three times.
 (d) cross family: R6-2 (bound 7 for z, z' <= 2) and R6-3 (z' = 3: bound 9).
 Solutions with a row of 3-dim projection (the L_r of a MINIMAL pair (r,i)) occur in (a), (b): all of them have bound 7.
 PICTURE: every solution found with all sparse parts of dimension <= 2 has FO2 bound <= 8 (mostly 7); the bound 9 occurs only with a
 3-dim single-row or single-column part. No non-FK solution was found, although non-FK solutions of (ii) exist (R6-1); LM from random
 starts finds the large components only, so this is NOT a classification.

## R6-5. The split free line (z = 3) is a sub-case of (B1); a relation given by every single-row element  [rigorous, short]
 (a) e_i (x) Z_i lies in L_r for every r != i, so z_i <= dim pi_i(L_r) = 5 - lam_{ri} when a_r = 1 (stage3's S3-1). Hence in REG1:
     z_i = 3  =>  lam_{ri} = 2 for ALL four rows r != i, and L_r = X_{ri} (+) e_i (x) Z_i:  a split free row is in four minimal pairs.
     So the only configurations on which FO2 gave bound 9 are minimal-pair configurations (B1) of a very rigid kind, and L_i is a (5,1) space.
 (b) For every single-row element e_i w^T of a level space L and every t in L:  <w, sum_{k != i} t_k> = 0  (polar form of P_2; sum w = 0).
     So each single-row element gives the relation 1_{rows != i} (x) w in the annihilator of L: the column sums over the other four rows
     are orthogonal to Z_i. For z_i = 3 they lie in the 2-dim space span(1, m), m the defect line.

## R6-6. (B1) with FO2
 - the plane X_{rr'} of a minimal pair alone (2-dim, all 3x3 subpermanents identically 0, level; stage2/r6_planes.py, 40 planes): FO2
   bounds 10-12 (dim T_1 = 19-22, rank 17-20). Not enough; and LM finds mostly degenerate planes (a zero row).
 - through (Q-r): L_r of a minimal pair (r,i) is a (Q-r) solution with a row of 3-dim projection. Those found (R6-4) have bound 7,
   except the z = 3 family (bounds 8-9).
 - FO2 on L_r + L_r' with the tau-coordinate descriptions of Types I, II, I_0: NOT done. The tau-descriptions give the relations on the
   two rows r, r', not the elements of L_r and L_r' in the other three rows; an explicit 8-dim candidate L_r + L_r' needs a solution
   of (Q-r) for both rows with a common 2-dim plane, which I did not construct.
STATUS 19:09: FK(1,5) census: 1 solution (lam = 5 type), bound 9; FK(4,2): no result (timeout). New linear test (T2) and the
 antisymmetry condition for lam = 5 found and applied.

## R6-7. Beyond (Q-r): the next order of chief's identity (**), and what survives  [conditions rigorous; applications numerical]
 For a_r = 1, L^ = {(v; T(v) + xi)}, <v, G(T(v) + xi)> = 120 <kappa^r, v>^5 for all v in C^5, xi in L_r (chief RP6). Expanding at v -> 0:
   order 1:  G(xi) = 0 on L_r                                                                      [= (ii) of (Q-r)];
   order 2:  (T2)  D_{T_k} G_j(xi) + D_{T_j} G_k(xi) = 0 for all j <= k, xi in L_r,  T_k = T(e_k),  sum_k T_k = J' mod L_r.
 (T2) is LINEAR in T, so it is a cheap exact test for a candidate L_r: solve the linear system and ask whether J' lies in
 {sum_k T_k} + L_r (stage2/r6_T2.py). Expanding at v -> 1 instead gives FO and FO2. So (Q-r), FO2 and (T2) are three independent
 consequences of the single statement "there is a linear T with (**)", which is EQUIVALENT to the existence of the 9-dim L.
 LEMMA (lam_{rr'} = 5, a_r = a_r' = 1) [rigorous]. Then L_r = L_r' =: X (a 5-dim level space on the other three rows, (ii) is void), row r'
 of u in L^ is Phi(u_r) with Phi in GL_5, Phi(1) = 1, and (T2) becomes   C(xi) Phi + Phi^T C(xi) = 0 for all xi in X,
 C(xi)_{jl} = perm_3(xi without columns j,l). In particular all C(xi) are singular, and if the ten cubics C(xi)_{jl} are linearly
 independent on X there is no such Phi (Phi would be diagonal with Phi_jj + Phi_mm = 0 for all j != m).
 RESULTS on the saved candidates (distance of J' from {sum_k T_k} + L_r; 0 = (T2) solvable):
   FK(2,4) [2,3,1,1] (two of them): 2.8 and 1.7 -> (T2) fails (they also fail FO2);   FK(2,4) [1,2,1,2]: solvable (fails FO2, bound 8);
   FK(1,5) (lam = 5, FO2 bound 9): 2.2 -> (T2) fails; the antisymmetry system has only Phi = 0 (stage2/r6_lam5.py);
   FK(3,3) with z = 3, FO2 bound 9 (three of them): 3.0 -> fails; 2e-14, 9e-15 -> solvable;
   cross spaces: solvable for all (a,b) (there D G = 0).   [Two older LM solutions give 4e-3, 3e-2: not accurate enough to decide.]
 SURVIVORS of (Q-r) + FO2 + (T2) among everything found:  the cross spaces with b = 0 or a in C1, and two FK(3,3) solutions -- all with
 a 3-DIM SPARSE PART (z = 3 or z' = 3), i.e. a split free line, which in REG1 means four minimal pairs through that line (R6-5).
 LEMMA (z_i = 3) [rigorous]. If z_i = 3 in a 9-dim level space, then M_i = L_i (+) e_i (x) Z_i is an 8-dim level space with deletable row i,
 L = M_i (+) C t_0, and t_0 is a first-order extension direction of M_i outside M_i (+) C(e_i 1^T - J/5):  dim T_1(M_i) >= 10.
 [T_1(M_i) contains M_i (+) C tau', tau' = e_i 1^T - J/5 (R5-4); P_2(tau' + m) = -8 - 4 s_i(m) = -8 for m in M_i since the row-i sum of m
 is 0; so a 9-dim level L cannot be M_i (+) C(tau' + m).]
STATUS 19:13: RESULT-R6 at the top. Runs to report (round 6): r6_census.py was launched once with clobbered parameters (crashed at once);
 census batch 32 overlapped for about 100 s with the FK(2,4) run (two processes at once); r6_fk.py for FK(1,5)+FK(4,2) hit its timeouts
 twice (first time without output; FK(4,2) gave no result); batches 32, 33 reached the 170-175 s timeout after 5 starts. Final report sent.

## R6-8. Additions after the first write-up (19:13 - 19:18)  [numerical]
 - second seeds (stage2/r6_fk.py): FK(2,4): 11 more solutions (total 20): (dim T_1, rank, bound) = (9,3,7) seventeen times, (12,7,8) twice,
   (8,3,6) once -- all <= 8, all with sparse parts <= 2.  FK(3,3): 8 more (total 15): the two with z = 2 have (10,5,7); the thirteen
   with z = 3 have bound 8 (seven) or 9 (six).  FK(4,2): 0 solutions in 6 starts.  General search, batch 33: one more FK(2,4) solution,
   row projections [3,1,1,3], (12,7,8) (already counted in R6-4).
 - direct extension search (stage2/r6_extend.py) for the two FK(3,3) solutions that survive FO2 and (T2): level spaces of dimension 8
   containing them: 8 starts, residual floors 0.77 - 1.2. With R6-3 (cross, b = 0: 6 starts, floor 0.775): none of the survivors is seen to
   extend even to dimension 8.
 - SANITY of (T2) (stage2/r6_T2_sanity.py): on the 7 known spaces, for all 10 lines with full projection (rows and columns), G = 0 on L_r
   and (T2) is solvable with sum_k T_k = J' (distance <= 5e-15); for random spaces of the same dimension 3 the distance is about 4.
STATUS 19:18: R6-8 added. Final report sent.

# ROUND 7 (start 19:33, budget 90 min -> ends ~21:03). Targets: (0) COMPUTE-stage2.md; (1) dim T_1 and "not level beyond" for the (2,4)
# family; (2) z = 3 in REG1; (3) what remains of REG1. Correction to (Q-r)(iii) from verify2: the column projections of L_r have dim <= 3
# except possibly for ONE column c with kappa^r = e_c, kappa'^c = e_r (entry (r,c) = 0 on L), where only <= 4 holds and L = L_r + L^c.
STATUS 19:36: /home/claude/work/L-gct-210/COMPUTE-stage2.md written (tasks S1-S6: census at scale, non-block solutions, exact FO2 for (2,4),
 minimal pairs with zeros as an exact problem, two-row-column blocks, z = 3). Starting (1).
STATUS 19:43: new first-order test (FO-r) found: it kills the generic (2,4) solutions and the whole cross family including the locus b = 0.

## R7-1. LEMMA (FO-r): the row-r projection of T_1(L_r) must be all of C^5  [rigorous; sharper than "dim T_1 >= 9"]
 Let r be a row with 4-dim projection of a level space L, X = L_r. Then T_1(X) contains L and tau = e_r 1^T - J/5 (R5-4), whose row r is
 (4/5) 1, not in pi_r(L) = (kappa^r)^perp. Hence  pi_r(T_1(X)) = C^5.  Explicitly (perm(u) = <u_r, G(u')>):
     t_0 in pi_r(T_1(X))   <=>   the function xi -> <t_0, G(J' + xi)> on X lies in D(X) := { xi -> D_{t'} N(J' + xi) : t' in C^{4x5} },
 so (FO-r) says: EVERY column-deletion permanent G_j(J' + xi) is, on L_r, a first-order variation of the level function N.
 [It is the order-1 part at v = 1 of chief's identity: G_j(J' + xi) + D_{T(e_j)} N(J' + xi) = 600 kappa^r_j.]
 Always: pi_r(T_1(X)) contains (C(X) + C1)^perp and 1, so its dimension is >= 5 - e(X); (FO-r) can only fail if e(X) >= 2.
 APPLIED to every saved candidate (stage2/r7_FOrow.py; dim T_1, dim of the row projection):
   cross X(a,b), b != 0: (10, 3) DEAD;   cross, b = 0 (3-dim single-column part): (13, 3) DEAD;   cross, a in C1 (3-dim single-row part): (13, 5) passes;
   (2,4) solutions with dim T_1 = 9 (all of "Case B" below; 6 saved): (9, 2) DEAD;   (2,4) "Case A" (3 saved): (12, 5) pass (FO2 bound 8);
   (3,3) solutions with z = 3 (6 saved): (13, 5) pass;   (1,5) candidate: (13, 5) passes (dead by (T2)).
 For the cross family this is a one-line proof from R6-2/R6-3: the row-0 part of T_1(X(a,b)) is (y_0 ; -2 nu a + c_0 1) for b != 0, and
 (y_0 ; span(1,a)) for b = 0: dimension 3 < 5 in both cases. So EVERY cross space with a not in C1 is excluded at first order [rigorous],
 including the split-free-column locus b = 0 that FO2 could not exclude.

## R7-2. The (2,4) family  [formulas rigorous and machine-checked (stage2/r7_fk24_formula.py); the last step of Case B numerical]
 Rows 0 (= r, zero on X), 1, 2 (= s_1 e_0, s_2 e_0), 3, 4 (= p, q). U = J + xi, P = 1 + p, Q = 1 + q, ' = columns 1..4, al = sum P', be = sum Q',
 gam = al be - <P',Q'>, al_j = al - P'_j, be_j = be - Q'_j, gam_j = al_j be_j - <P',Q'> + P'_j Q'_j, s = s_1 + s_2, h_j := 2 P_0 be_j + 2 Q_0 al_j.
 Cofactors:  C_00 = C_10 = C_20 = 2 gam,  C_30 = 6 be,  C_40 = 6 al,  and for j = 1..4:
     C_0j = (2 + s) gam_j + h_j,   C_1j = (2 + s_2) gam_j + h_j,   C_2j = (2 + s_1) gam_j + h_j,   C_3j = 2(3 + s) be_j + 6 Q_0,   C_4j = 2(3 + s) al_j + 6 P_0.
 Hence C_00 = C_10 and C_0j - C_1j = s_1 gam_j, C_1j - C_2j = (s_2 - s_1) gam_j, so
     pi_r(T_1(X)) = C e_0 (+) { t in C^4 : s * sum_j t_j gam_j restricted to X lies in D(X) }.
 Level conditions (R6-1): s = -(p_0 + a + q_0 + b),  p_0 a + q_0 b + a^2 + ab + b^2 + <p',q'> = 0,  s (ab - <p',q'>) = 0  (a = sum p', b = sum q').
 CASE A (s = 0 on X): rows 1,2 form a domino direction, (p,q) runs through a 2-row level space; pi_r(T_1(X)) = C^5: (FO-r) holds, no
   first-order obstruction. The three solutions found have dim T_1 = 12, rank 7, FO2 bound 8 (and one earlier (8,3,6)): dead by FO2
   numerically; not proved.
 CASE B (ab = <p',q'> on X, s not 0): then p_0 a + q_0 b + (a+b)^2 = 0, i.e. a u + b w = 0 with u = a + b + p_0, w = a + b + q_0; if a, b are
   independent on X this forces p_0 = -a - (1+mu) b, q_0 = (mu-1) a - b, s = (1-mu) a + (1+mu) b for a constant mu.
   (FO-r) requires s * gam_j in D(X) for every j. In all 6 saved Case-B solutions (and all 20 census solutions with dim T_1 = 9) the
   projection is only C e_0 (+) C 1: DEAD at first order. A proof needs the parametrisation of the 5-dim solutions of Case B
   (COMPUTE-stage2.md, S3); I did not obtain it.
 So "dim T_1 = 9" is explained: T_1(X) = (7-dim part with zero row r) (+) (2-dim row-r part e_0, 1); and "not level beyond" holds in the
 stronger form "no level space with a 4-dim row-r projection contains X as its L_r".

## R7-3. z_i = 3 in REG1 (split free line)  [reductions rigorous; NOT closed]
 Setting: 9-dim level L, a_i = 1, z_i = 3, Z := Z_i = (C1 + Cm)^perp, m orthogonal to 1 (the defect line of the (5,1) space L_i).
 (a) [P_2] single-row parts of different rows are orthogonal, so Z_k lies in Z^perp cap 1^perp = C m for every other row k: z_k <= 1, and a
     single-row element of another row is e_k m^T, which lies in L_i. If <m,m> != 0, verifyfl's Theorem SPLIT (a 4x5 space with defect line
     C m, <m,m> != 0, containing e_k m^T has dim <= 4) gives a contradiction. So for non-isotropic m:  z_k = 0 for all k != i, and L_i is a
     NON-SPLIT (5,1) space.  (rows' FL2*(a) and NCOL-S apply to split spaces only, so they give nothing more here.)
 (b) [TC5] m is not a two-column vector e_a - e_b.  [HYP] every hyperplane of L_i is a non-split (4,1) space with the same defect line; all
     known non-split (4,1) spaces have a two-column defect line (rows U5), so no such hyperplane is known.
 (c) [(FO-r) for row i] pi_i(T_1(L_i)) contains Z (+) C1 automatically; the fifth dimension requires the defect function g of L_i
     (G(J' + xi) = 24*1 + g(xi) m) to be a first-order variation of N on L_i: g = D_{t'} N(J' + .) + const for some t'. The same then holds on
     every hyperplane. All 27 known 7-dim level spaces with a deletable line are rigid (T_1 = M + C tau; rows), i.e. their defect
     functions are NOT such variations. So z_i = 3 needs a first-order FLEXIBLE non-split (5,1) space.
 (d) [R6-5, R6-7] four minimal pairs through row i, L_r = X_{ri} (+) e_i Z for r != i; column sums of all x in X_{ri} lie in C m; L = M_i (+) C t_0
     with dim T_1(M_i) >= 10; and on the 6-dim space Lam_0 = L_i (+) C Theta (Theta = rows != i of t_0): G(J' + eta) lies in span(1,m), with
     m-component 120 kappa_m - (1 - kappa_m s)(N(J'+eta) - 120)/s  (s = coordinate of Theta, kappa^i = 1/5 + kappa_m m).
 (e) Candidates: every (Q-r) solution found that passes (FO-r), FO2 and (T2) is of the form X_{ri} (+) e_i Z with z_i = 3 (four (3,3)
     solutions and the cross spaces with a in C1; table: stage2/r7_table.py). z_i = 3 would need an 8-dim level space M_i containing it;
     the direct search (stage2/r6_extend.py, D = 8) finds none for the five candidates tested (4 starts each, residual floors 0.8 - 1.6).
 NOT DONE: a proof. The statement that would finish z = 3 for non-isotropic m is verifyfl's (SL_m) / "every (4,1) space with a
 non-two-column defect line is split"; isotropic m is not touched.

## R7-4. Correction of (Q-r)(iii), the exceptional case, and what remains of REG1
 (iii) corrected (verify2): row projections of L_r have dim <= 3 (Lemma C); column projections have dim <= 3 except possibly for ONE
 column c, when kappa^r = e_c and kappa'^c = e_r (the entry (r,c) vanishes identically on L); then only <= 4 holds and L = L_r + L^c.
 None of my statements used the column part: the censuses impose row ranks only, and (FO-r), FO2, (T2), the cross theorem and the
 (2,4) formulas do not use (iii). In the exceptional case one has in addition: ell(u) = u_rc; for the four columns j != c the 6-dim
 spaces {t in L : t_r in C e_j} have vanishing (r,j)-deletion permanent (and dually for the four rows i != r in column c); and by (**)
 at v = e_c the image of L_r in the (r,c)-minor is a linear space of 4x4 matrices on which perm_4(B + .) = 120 is constant for a
 suitable B. I found no contradiction for this case and no candidate (no census solution has a 4-dim column projection).
 WHAT REMAINS OF REG1 (with stage3's Theorem N for (B2)):
   (B1) a minimal row or column pair. Sub-case z = 3: R7-3. General case: L_r is a (Q-r) solution with a 3-dim row projection passing
        (FO-r), FO2, (T2); the ones found are dead unless z = 3.
   (B2) no minimal pair on either side: single-row and single-column elements with z, z' <= 2; every L_r is a (Q-r) solution passing the
        three tests; all 40-odd solutions found with z, z' <= 2 fail at least one test (most already fail (FO-r) or FO2).
   (B0) the exceptional case of (iii): an identically vanishing entry.
 A proof of REG1 now needs: the classification of (Q-r) solutions (COMPUTE-stage2.md S1-S3) or a structural proof that a (Q-r) solution
 passing (FO-r) and FO2 contains a 3-dim single-row part; and the non-split (5,1) problem for z = 3.
STATUS 19:48: R7-1 .. R7-4 written. Table of all saved candidates: stage2/r7_table.py (ALIVE: four (3,3) solutions with z = 3 and the cross
 spaces with a in C1; all others dead).
 Sanity of (FO-r) (stage2/r7_FOrow_sanity.py): on the 7 known spaces all 10 lines with 4-dim projection have projection dimension 5.
 The four ALIVE (3,3) candidates are spanned by sparse elements only: X = C y e_0^T + C y' e_1^T + e_i Z (two single-column elements with
 <y,y'> = 0 and a 3-dim single-row space); their m is neither two-column nor isotropic.
STATUS 19:50: RESULT-R7 at the top. Runs: r6_extend.py on three files reached its 115 s timeout after two; r7 struct scripts < 40 s.
 Final report sent.

# ROUND 8 (start 19:59, about 2 hours -> ends ~21:59). Targets: (1) "a (Q-r) solution passing (FO-r) and FO2 contains a 3-dim single-row
# part"; (2) Case B of (2,4) by hand or as an exact ideal; (3) (B0) the identically vanishing entry; (4) z = 3 with isotropic m.
# New input: reg2's inequality dim L <= dim L_r + dim Omega(L_r) - 1 (Omega = row-r projection of T_1(L_r)) = (FO-r) from the other side.
STATUS 20:03: plan fixed. (B0) has a clean exact form: with the hook (row r, column c) free and u_0 = E_rc + B in L^,
 L^ = {u = [[c, w],[y, M]] : M = cB + alpha(w) + beta(y) + lam x_0} and  c perm_4(M) + y^T Pi(M) w = 120 c^5  (Pi = matrix of 3x3
 subpermanents of the 4x4 minor). Working on it, then on the graded form of (FO-r).
[merged 20:38 from the cloud copy (lines written after the workspace copy): round-8 sections R8-1 .. R8-4]
STATUS 20:30: ROUND 8 STOPPED EARLY on the coordinator's change of plan (handover to the 24-core session). No computation is running.
 What was reached in 30 minutes is written below (R8-1 .. R8-4); the handover is handover/HANDOVER-stage2.md.

## R8-1. Graded form of (FO-r)  [hand derivation; NOT yet checked by an independent script -- first thing to machine-check]
 X = L_r (4x5 matrices), P_k(xi) := sum of all k x k subpermanents of xi (P_0 = 1), xi^(j) := xi without column j, xi^[j] := column j of xi,
 tau_j := 1 e_j^T, N(A) = sum_j G_j(A) = perm of the 4x5 matrix, N(J'+xi) = sum_k (5-k)! P_k(xi), G_j(J'+xi) = sum_d (4-d)! P_d(xi^(j)).
 Level on X <=> P_1 = P_2 = P_3 = P_4 = 0 on X; (ii) <=> P_4(xi^(j)) = 0 on X for all j.
 (a) Column Euler identity: G_j(A) = N(A) - D_{A^[j]} N(A). On X: G_j(J'+xi) = D_{J'/4 - tau_j} N(J'+xi) - D_{xi^[j]} N(J'+xi).
     So (FO-r)_j <=> the column-scaling function xi -> D_{xi^[j]} N(J'+xi) lies in D(X) (reg2's description of Omega, same thing).
 (b) (FO-r)_j  <=>  there is theta_j in M_{4x5} with   D_{theta_j} P_k (xi) = P_{k-1}(xi^(j))   for all xi in X and k = 1,2,3,4
     (k = 1: sigma(theta_j) = 1).  Because D_{tau_j} P_k = (5-k) P_{k-1}(xi^(j)), this is
          theta_j  in  (tau_j/4 + K_1) cap (tau_j/3 + K_2) cap (tau_j/2 + K_3) cap (tau_j + K_4),   K_k(X) := {t' : D_{t'} P_k = 0 on X}.
     All K_k contain X; K_2, K_3, K_4 contain J'. Necessary: tau_j in K_3 + K_4, tau_j in K_2 + K_3, tau_j in K_2 + K_4 for every j.
 (c) K_2 = H^{-1} X^perp with H = Hessian of P_2 = I - (row sums) - (column sums) + (total sum), eigenvalues 1, -4, -3, 12: invertible.
     So degrees 0 and 1 never obstruct; the obstruction is in k = 3, 4: 15 + 35 linear conditions on <= 14 unknowns, for 4 columns.
 (d) Single-column elements linearise: if zeta = c e_0^T lies in X, every cofactor C_kj(J + xi + t zeta) is affine in t (constant for j = 0),
     so the T_1 condition splits into its t^0 and t^1 parts. Every (2,4)-type X contains such a zeta (R8-2).
 The structural statement of target (1) is NOT proved. It also needs the transposed alternative ("3-dim single-COLUMN part"): the spaces
 X = C_0 (+) Y of R8-2 (B2a) are level, satisfy (ii), (iii) and have a 3-dim single-column part; they were not tested.

## R8-2. Case B of the (2,4) family  [parametrisation and criterion: hand proofs, validated numerically (stage2/r8_caseB.py, r8_caseB2.py);
##       the round-7 claim "Omega = span(e_0, 1) in all of Case B" is CORRECTED: true generically, false on special loci]
 Notation as in R7-2: xi = [s_1 e_0; s_2 e_0; p; q], p = (p_0,p'), q = (q_0,q'), a = sum p', b = sum q', s = s_1 + s_2.
 Level <=> sigma = 0, q_1 := a u + b w = 0 (u = a+b+p_0, w = a+b+q_0), s q_2 = 0 with q_2 := a b - <p',q'> = p'^T K q', K = J - I.
 (0) [rigorous] In every case there is a linear relation among s_1, s_2, p_0, q_0 on X, so the column-0 projection of a (2,4)-type X has
     dim <= 3 (other columns <= 2): a (2,4)-type X never has a 4-dim column projection, so it is never the L_r of case (B0a).
 (1) [rigorous] Omega(X) contains e_0 and 1 for every (2,4)-type X (C_00 = C_10 = 2 gamma). (0,v) in Omega <=> s_1 gamma_v in D(X),
     gamma_v = sum_j v_j gamma_j. Case A (s = 0): Omega = C^5.
 (2) [rigorous] Sub-case (B1) (a, b independent on X): p_0 = -a-(1+mu) b, q_0 = (mu-1) a - b, s = (1-mu) a + (1+mu) b, and
     X = C xi_d (+) X_0, xi_d = (e_1 - e_2) e_0^T, X_0 = Y_0 := a MAXIMAL isotropic (4-dim) subspace of C^4 x C^4 for p'^T K q':
       Y_0 = {(p',q') : p' in A', (K q')|_A' = omega(p')},  k = dim A', omega skew on A',  B := Y_0 cap {p' = 0} = K^{-1} A'^perp.
     (iii) forces k in {1,2,3}, omega = 0 unless k = 3; k = 3 needs (1+mu) sigma_n = 0 (A' = n^perp) and, if omega != 0,
     (mu-1) a(w*) = 0; k = 1 needs mu = 1.  Split case omega = 0: Y_0 = A' (+) B.
 (3) [rigorous, validated] In (B1):  Omega = C e_0 (+) {(0,v) : s gamma_v in D_0},
       D_0 = C 1 + C a + C b + (3+s) Y_0^* + span{(2 + s/2) gamma_j + h_j : j = 1..4}   (functions on Y_0),
     and, for s != 0 on Y_0, criterion [CRIT]: (0,v) in Omega <=> there are e in C^4, x, y with
       g_e = 0 on Y_0   and   4 E_v + s (P_e + Q_e) - 2 p_0 Q_e - 2 q_0 P_e = s (x a + y b) on Y_0,
       g_e = sum_j e_j (2 p_j q_j - a q_j - b p_j),  E_v = 2 sum_j v_j p_j q_j + (1-mu) a (2 P_v + Q_v) + (1+mu) b (P_v + 2 Q_v),
       P_v = <v,p'>, Q_v = <v,q'>.   (quadrics on a 4-dim space; 20 linear equations in the 10 unknowns v, e, x, y.)
 (4) Split k = 3, mu = -1 (hand): w := 8v + 3e = x 1' + t n, and the (1,1)-part reads n_j^2 - c n_j - kappa = 0 for all j. Hence
     dim Omega = 3 when n takes exactly two values, 2 otherwise (confirmed: n = (2,2,2,5), (2,2,5,5), (1,1,1,3), (1,1,2,2), (0,1,1,1),
     (0,0,0,1) give 3; random n, (1,-1,2,5), (0,0,1,2), (1,2,3,-6) give 2). Mirror statement for k = 1, mu = 1.
 (5) [numerical] 47 members built: T_1 tool, D_0 form and [CRIT] agree except (i) n = (1,1,1,1.0001) (rank tolerance, near a = 0 on A')
     and (ii) two members with b = 0 on Y_0 and mu = 1, i.e. s = 0 (Case A, where [CRIT] does not apply; D_0 form and T_1 tool agree: 5).
     Largest dim Omega in genuine (B1): 4, at A' = span{(1,-1,0,0),(0,0,1,2)}, omega = 0, mu = -1 (dim T_1 = 10, rows (1,1,2,3)).
     Omega = C^5 was found in NO genuine (B1) member, but this is NOT proved.
 (6) Exact attempt: Singular std mod 32003 of the existential ideal "[CRIT] solvable for v = e_1, e_2, e_3" (18 linear unknowns and
     4 / 5 / 7 parameters for k = 1 / 2 / 3; generator stage2/r8_gen.py) did not finish in 100 s for any stratum: 3 runs, 3 timeouts,
     NO verdict. Better formulation for the 24-core machine: COMPUTE-stage2.md S3'.
 (7) NOT DONE: sub-case (B2) (a, b dependent). (B2a) a = b = 0 contains X = C_0 (+) Y, C_0 = {c e_0^T : sum c = 0} (full free column),
     Y a 2-dim isotropic subspace of 1'^perp x 1'^perp for <p',q'>: level, (ii), (iii) hold by the formulas above; s != 0. Untested.

## R8-3. (B0): the identically vanishing entry  [rigorous as far as it goes; no contradiction, no candidate]
 r = c = 0, entry (0,0) = 0 on L, ell(u) = u_00 on L^. (B0a): L = L_0 + L^0, L_0 cap L^0 = C x_0. Then (w, y) = (row 0, column 0) are free
 coordinates and  L^ = {[[c, w],[y, M]] : M = c B + alpha(w) + beta(y) + lam x_0},   c perm_4(M) + y^T Pi(M) w = 120 c^5,
 Pi(M)_ij = perm_3(M without row i, column j).
 (a) perm_4(c B + beta(y) + lam x_0) = 120 c^4 and perm_4(c B + alpha(w) + lam x_0) = 120 c^4 (ZBF with the 1x4 zero blocks).
 (b) LEMMA B0-1: Pi(x_0) = 0, i.e. all 3x3 subpermanents of the 4x4 block of x_0 vanish (lam^2-coefficient at c = 0; Pi is quadratic in M).
     Known solutions: at most 2 nonzero rows; at most 2 nonzero columns; A (+) A' with perm A = perm A' = 0. Classification not done.
 (c) Sketch for x_0 supported in two rows 3,4 with invertible B_x (B_x[j,l] = perm_2 of the two rows on the complementary columns):
     lam^1-part gives B_x (y_1 beta_2(y) + y_2 beta_1(y)) = 0, so rows 1,2 of L_0 are y_1 (1,v), y_2 (1,-v), v^T B_x v = 0, and G_j = 0
     forces v to have at least three zeros. [hand derivation, unchecked]
 (d) By R8-2 (0) the (2,4) family does not occur in (B0a). Whether ANY (Q-r) solution has a 4-dim column projection is open
     (census with the column forced: COMPUTE-stage2.md S7).

## R8-4. Not reached: target (4) (z = 3 with isotropic m), the combination of (FO-r) with verifyfl's (SL_m), and FO2 on (B1) pairs.
 Runs of this round: r8_caseB.py (5 s), r8_caseB2.py (15 s), 3 Singular runs of 100 s each (all timeouts, run one after another in the
 background while nothing else ran). First STATUS of this round was stamped 20:13 by mistake and corrected to 20:03.
STATUS 20:33: handover written (handover/HANDOVER-stage2.md); the 18 candidate arrays copied from /tmp to stage2/data/; COMPUTE-stage2.md
 extended by S3' and S7. Round 8 ends here. Nothing is running.

# ROUND 9 (new session on the 24-core machine; start 19:48 UTC, about 1.5 h). Targets: (1) Case B of the (2,4) family (ST2-S3'/S7) as
# exact computations; (2) (B0) and B2; (3) toward "(Q-r) + (FO-r) + FO2 => 3-dim single-row part". Times below are UTC.
# NOTE: the round-8 write-up (R8-1 ..) and the S3'/S7 specs were NOT saved in NOTES/COMPUTE (notes end at STATUS 20:03 local); only the   [SUPERSEDED 20:38: they existed in the cloud copy and are now merged above; R8-2 contains the original [CRIT] (same as R9-1(b)).]
# scripts stage2/r8_caseB.py, r8_caseB2.py, r8_gen.py survive. I re-derive their criterion [CRIT] below before using it.
STATUS 19:50: round 9 started; reading; re-deriving [CRIT] for Case B (B1) of the (2,4) family.

## R9-1. THEOREM B-IND: in Case B of the (2,4) family with a, b independent on X, (FO-r) FAILS for every X
##       [reductions rigorous (hand, below); final step exact: char-0 Groebner bases (Singular over QQ), stage2/r9_gen.py, r9/*.sing]
 Setting (R7-2): X = L_r (row r = row 0 zero), rows 1,2 = s_1 e_0, s_2 e_0, rows 3,4 = p, q; Case B: ab = <p',q'> on X, s = s_1+s_2 not 0;
 B(ind): a = sum p', b = sum q' linearly independent on X; then p_0 = -a-(1+mu)b, q_0 = (mu-1)a-b, s = (1-mu)a+(1+mu)b (mu constant).
 (a) STRUCTURE. The kernel of X -> Y := image in (p',q') consists of elements with p' = q' = 0, hence a = b = p_0 = q_0 = s = 0: it lies in
     C xi_d (xi_d = (e_1 - e_2) e_0^T, rows numbered 1..4 of the 4x5 block). Y is totally isotropic for the nondegenerate form p^T K q' + p'^T K q
     (K = J - I) on C^8, so dim Y <= 4; dim X = 5 forces dim Y = 4 and xi_d in X:  X = C xi_d (+) X_0, X_0 = {s_1 = s_2} ~ Y_0 (max. isotropic).
 (b) CRITERION [CRIT] (re-derived independently of the lost R8-2): with gam = 12 + 3(a+b) (uses <p',q'> = ab), gam_j = 6 + 2(a+b-p_j-q_j) + g_j,
     g_j = 2 p_j q_j - a q_j - b p_j, the d-coordinate (along xi_d) separates (cofactors depend on rows 1,2 only through s_1, s_2), and comparing
     homogeneous parts of degree 3, 2, 1, 0 of  s*gam_v = sum c_ij C_ij  on Y_0 gives:
        (0,v) in Omega  <=>  exists e in E_0 := {e in C^4 : g_e = 0 on Y_0} and x, y in C with
                             2 E_v + Phi(e) + s (x a + y b) = 0 on Y_0,
        E_v = 2 sum_j v_j p_j q_j + (1-mu) a (2P_v + Q_v) + (1+mu) b (P_v + 2Q_v),  Phi(e) = s(P_e+Q_e) - 2 p_0 Q_e - 2 q_0 P_e.
     (degree 3 forces A = 2(v+e), e in E_0; degree 1 is always solvable and makes the s*span(a,b) part free.) v = 1' always works (e = 0,
     E_1' = 2 s (a+b)); so Omega = C^5 <=> v = e_1, e_2, e_3 all work. r8_caseB2.py confirms [CRIT] = T_1 tool on 40 Case-B points (its
     three "mismatches" are two Case-A points (b = 0, mu = 1 gives s = 0) and one near-singular float point).
 (c) NECESSARY CONDITION (N0): restrict [CRIT] to Y_00 := Y_0 cap {a = b = 0} (dim 2): Phi(e), s(xa+yb) and the (1 -+ mu)-terms vanish there,
     so Omega = C^5 forces p_k q_k = 0 on Y_00 for k = 1..4: for each column k, p_k or q_k vanishes on Y_00.
 (d) PATTERNS. Let S (T) = columns where p (q) is not identically 0 on Y_00; S, T disjoint; p|Y_00 lies in C^S cap 1^perp, q|Y_00 in C^T cap 1^perp,
     and (p,q) is injective on Y_00. Hence exactly one of:
     Q0: q = 0 on Y_00 (V := p(Y_00) 2-dim in 1^perp). Isotropy with Y_00 gives q(Y_0) in V^perp = C1 + Cw. Solving the three remaining isotropy
         equations: either (Q0-1) Y_0 = A' x 0 (+) C(0,u), A' = {p : p^T K u = 0} (= stratum "S3 split"), or (Q0-2) p'(Y_0) = V + C1 + C P_b = C^4,
         which violates (Q-r)(iii) (row projections <= 3, Lemma C). In (Q0-1), (iii) for row p forces mu = -1 (the element (0,u) has p_0 = -(1+mu)).
     P0: p = 0 on Y_00: the mirror image (swap p <-> q, mu -> -mu): Y_0 = C(alpha,0) (+) 0 x K^{-1}alpha^perp (= stratum S1), mu = 1 forced by (iii).
     M:  |S| = |T| = 2, WLOG S = {1,2}, T = {3,4}: Y_00 = C(e_1-e_2, 0) + C(0, e_3-e_4); isotropy with Y_00 gives p_3 = p_4 = pi, q_1 = q_2 = ka on
         Y_0; in coordinates (zeta_1, zeta_2, a, b): pi = al a + be b, ka = ga a + de b and isotropy of Y_0 is exactly
         ga(4al-1) = 0, be(4de-1) = 0, 1 - de - al + 4(al de + be ga) = 0  (two components: be = ga = 0; or al = de = 1/4, be ga = -3/16); mu free.
     (|S| = 1 or |T| = 1 is impossible: a nonzero sum-zero vector has >= 2 entries.)  Charts: alpha_1 = 1 (FP0), n_4 = 1 for n = Ku (FQ0) are WLOG
     by the S_4 symmetry of columns 1..4 (Omega = C^5 is invariant).
 (e) EXACT VERDICT (Singular 4.3.2 over QQ, char 0, affine incidence ideals: unknowns e^(k) in C^4, x_k, y_k for each tested v = e_k, plus the
     family parameters; all coefficient equations of [CRIT] in the 4 coordinates of Y_0; plus the isotropy equations for M):
        FM, v in {e_1, e_3}:        std = <1>  (UNIT, 0 s).  [v = e_1 alone: only mu = 1, be = ga = 0, 2de^2+de-1 = 0; v = e_3 alone: only mu = -1.]
        FP0 (mu = 1), v = e_1,e_2,e_3:  std = <1>  (UNIT, 1 s).
        FQ0 (mu = -1), v = e_1,e_2,e_3: std = <1>  (UNIT, 1 s).
     A unit ideal over QQ is a proof (no complex point), no saturation, no open condition used. The scripts print an ISOTROPY CHECK (=1).
     Independent cross-check with the general T_1 tool (stage2/r9_check_fam.py, numerical): the FM points where v = e_1 (resp. e_3) works have
     dim Omega = 4 (not 5); generic FM, FP0, FQ0 points have dim Omega = 2.
 CONCLUSION [rigorous modulo the machine GB]: no X of Case B(ind) passes (FO-r); so no such X is the L_r of a level space with a 4-dim
 row-r projection. (Supersedes the predecessor's ST2-S3' mod-p runs on the strata S1/S2/S3, which timed out; those strata are covered.)
STATUS 20:02: R9-1 written: Case B(ind) of (2,4) CLOSED (exact). Next: Case B(dep) (a, b dependent) = presumably the lost "S7".

## R9-2. Case B with a, b DEPENDENT ("B(dep)"; presumably the lost S7) -- sub-cases, and what is closed
 Case B, a and b linearly dependent on X. Swapping rows p <-> q (mu -> -mu; a row permutation, harmless) reduces to:
   D-lam: b = lam a on X, a != 0;  then p_0 = -lam q_0 - (1+lam)^2 a, s = (lam-1) q_0 + lam(1+lam) a, q_0 a free linear form.
   D00:   a = b = 0 on X;  then s = -(p_0 + q_0), p_0, q_0 free.
 Geometry: Y (image in (p',q')) is isotropic and lies in H_lam = {sum q' = lam sum p'} = h^perp with h = (1, -3 lam 1) in (p, Kq) coordinates;
 (h,h) = -24 lam.  So for lam != 0, dim Y <= 3, hence dim Y = 3 and the kernel of X -> Y is the full 2-dim space {(s_1,s_2,-lam c, c):
 s_1+s_2 = (lam-1)c} (contains xi_d and kappa_1 = ((lam-1)/2,(lam-1)/2,-lam,1) in column 0). For lam = 0 the radical of H_0 is C(1',0):
 dim Y = 3, or dim Y = 4 and (1',0) in Y.  For D00, Y is isotropic in the nondegenerate 6-dim 1^perp x 1^perp: dim Y in {2, 3}.
 (iii) for D-lam, lam != 0: rank p'|Y <= 2 and rank q'|Y <= 2 (kappa_1 adds one dimension to both rows); for lam = 0, dim Y = 3: rank q'|Y <= 2.
 (N0) again holds on Y_00 = Y cap {a = 0} whenever xi_d in X (same degree-3 / degree-2 argument as R9-1(b),(c), carried out with the general
 cofactor formulas; the pure-y part of the degree-2 identity is 2 g_A + (multiples of a) for lam != 0 and 2 g_A + 2 a Q_A for lam = 0).
 Sub-cases and verdicts (DIRECT tool stage2/r9_direct.py: raw 4x4 permanents of J + xi, unknowns t_ij for the 20 cofactors of rows 1..4,
 tests (0,e_m) in Omega literally; independent of all cofactor formulas and of [CRIT]; Singular over QQ):
   VALIDATION: direct tool on the B(ind) family FM reproduces R9-1 exactly (v = e_1: same locus mu = 1, be = ga = 0, 5al+3de+1 = 0,
               2de^2+de-1 = 0; v in {e_1,e_3}: UNIT). So [CRIT] and the direct route agree.
   D1  (lam != 0): patterns Q0, P0 on Y_00 violate rank <= 2 (the a-direction adds a vector with nonzero coordinate sum); only M remains:
       p' = ((1-2al)a/2 + z_1, (1-2al)a/2 - z_1, al a, al a), q' = (ga a, ga a, (lam-2ga)a/2 + z_2, (lam-2ga)a/2 - z_2), isotropy
       lam(1-al) = ga(1-4al).  Family D1M (lam free, so it also covers the M-part of lam = 0, dim Y = 3): v = e_1 alone forces lam = ga = 0;
       v = e_1,e_2,e_3: UNIT.                                                                                        [exact, char 0]
   D0-3 (lam = 0, dim Y = 3; X = C xi_d + C kappa + lift(Y), kappa = (-1/2,-1/2,0,1) in column 0, lift with s_1 = s_2 = q_0 = 0, p_0 = -a):
       P0: q'(Y) = V' (2-dim in 1^perp), p' = a P, P in V'^perp, sum P = 1 (chart V' = rowspace[[1,0,r1,-1-r1],[0,1,r2,-1-r2]]): UNIT.
       M:  inside D1M: UNIT.
       Q0: A' = n^perp (chart n_4 = 1), q' = c_a a w, w = n - (sum n/4) 1, isotropy c_a sum(n) = 0: NOT unit; eliminating the t's:
           Omega = C^5  <=>  c_a = 0.  For c_a = 0: q' = 0, so rows 1, 2 and 4 are supported in column 0 and the three lifts are
           SINGLE-ROW elements of row 3:  X = e_3 (x) {(-sum p', p') : p' in A'} (+) (2-dim column-0 part):  a 3-dim single-row part
           (z = 3), exactly the exceptional shape of the structural target (= the ALIVE "X_ri + e_i Z_i, z_i = 3" of R7-3(e)).
   OPEN in B(dep): D0-4 (lam = 0, dim Y = 4, (1',0) in Y) and D00 (a = b = 0, dim Y = 2 or 3).
STATUS 20:16: R9-2: B(dep) D1 and D0-3 done exactly (only survivor: c_a = 0 with a 3-dim single-row part). Open: D0-4, D00.
STATUS 20:15 (actual `date -u`; the line "STATUS 20:16" above was written at ~20:11): D00 with dim Y = 2 also closed (below).

## R9-3. LEMMA N0-W (general (2,4) member, Case B) and the sub-case D00 with dim Y = 2   [rigorous; exact]
 LEMMA N0-W. Let X be any 5-dim space of the (2,4) family (rows 1,2 = s_1 e_0, s_2 e_0) in Case B (<p',q'> = ab on X, s not 0), m in {1..4},
 and suppose some eta in X has s_1(eta) = s_2(eta) != 0. If (0, e_m) lies in Omega(X), then p_m q_m vanishes identically on
     W := X cap {s_1 = s_2 = p_0 = q_0 = 0, a = b = 0}.
 Proof. Let F = C_0m + sum_{i>=1} t_ij C_ij = 0 on X. Write gq_j for the quadratic part of gam_j (= g_j in Case B). Cubic part of F:
 s gq_m + sum_j (t_1j s_2 + t_2j s_1) gq_j (only C_0m, C_1j, C_2j have cubic parts: (2+s)gam_m, (2+s_2)gam_j, (2+s_1)gam_j). Expanding at
 xi_0 + eps eta, xi_0 in W (where s, s_1, s_2 vanish), the eps^1 coefficient gives, with s_1(eta) = s_2(eta) = sig:
     sig (2 gq_m + sum_j (t_1j + t_2j) gq_j) = 0 on W.
 On W itself P_0 = Q_0 = 1, s = s_1 = s_2 = 0, al = be = 4, <p,q> = ab = 0, so the quadratic part of F|W is 2 gq_m + 2 sum_j (t_1j + t_2j) gq_j
 (C_i0 = 2 gam has quadratic part -2<p,q> = 0 on W; C_3j, C_4j, h_j are affine-linear on W). Subtracting: gq_m = 0 on W, and gq_m|W = 2 p_m q_m. QED
 (In Case B(ind), D1, D0-3 this is the (N0) of R9-1/R9-2, with W = lift of Y_00.)  The hypothesis on eta holds whenever xi_d in X and s != 0.
 D00, dim Y = 2: X = (column-0 space {s_1+s_2+p_0+q_0 = 0}, contains xi_d) (+) Y (zero column 0); W = Y; N0-W gives the patterns
 Q0 (Y = V x 0), P0 (Y = 0 x V'), M (Y = C(e_1-e_2,0) + C(0,e_3-e_4)) (isotropy automatic). Direct tool, v = e_1,e_2,e_3, over QQ:
 D00Q: UNIT, D00P: UNIT, D00M: UNIT.                                                                                     [exact]
 Numerical landscape of the remaining sub-cases (stage2/r9_dep_num.py, T_1 tool): D0-4 (12 random strata) dim Omega = 2; D00-3 dim Omega 2-3
 except two points with dim Omega = 5, which have s = 0 identically (they are Case A, row-3 projection 4: not Case B and not (iii)).
 STRUCTURE for the rest: in D0-4, Y = C(1',0) (+) Y_a with Y_a = Y cap {a = 0} a MAXIMAL isotropic 3-space of 1^perp x 1^perp -- the same
 object as Y in D00-3. Given the 2-dim W (pattern Q0/P0/M), Y_a is one of exactly two extensions (the two isotropic lines of W^perp/W).
 OPEN: D0-4, D00-3 (finite list of small families, spec in COMPUTE-stage2.md S7'), and the "proportional rows" exception of N0-W
 (s_2 = rho s_1 on X with rho != 1).

## R9-4. D0-4 (lam = 0, dim Y = 4): families, exact loci, and two survivors of (FO-r)   [exact loci (char 0, elimination); FO2/T2 numerical]
 Structure: Y = C h (+) Y_a, h = (1',0), Y_a = Y cap {a = 0} maximal isotropic in 1^perp x 1^perp. Column 0: case (i) xi_d in X, lift with
 q_0 = phi, s_1 = s_2 = -phi/2, p_0 = -a (s = -phi, phi != 0); case (ii) xi_d not in X, kappa' = (sg,-1-sg,0,1), lift q_0 = 0, s_1 = -s_2 = d,
 p_0 = -a. N0-W applies in case (i), and in case (ii) unless d = 0 and sg != -1/2 ("PROP": rows 1, 2 proportional with ratio != 1).
 W = Y_a cap ker(phi or d) (2-dim) carries pattern Q0/P0/M; Y_a = W + C y3 with y3 one of the two isotropic lines of W^perp/W:
   M: y3 = ((-1,-1,1,1),0) [A] or (0,(1,1,-1,-1)) [B];  Q0: Y_a = 1^perp x 0 [A] or V x 0 + C(0,w), w in V^perp cap 1^perp [B];
   P0: mirror.  phi (resp. d) vanishes on W, free on h and y3 (f0, f3 resp. d0, d3). Families D04_<pat>_<A|B>_<i|ii> in r9_direct.py.
 (iii) eliminates: Q0_A entirely (p' has rank 4), P0_A_ii (q-row rank 4), and forces f0 = 0 in P0_A_i.
 Exact loci where Omega = C^5 can hold (Zariski closure of the projection, after eliminating the t's; outside it Omega != C^5 for sure):
   M_A_i : {f0 = f3 = 0} (s = 0: Case A, not B) and the POINT f0 = f3 = 2.
   M_B_i : {f0 = f3 = 0} only (Case A)  -> no Case-B member passes.
   M_A_ii: {d0 = d3 = 0} (sg free; at sg = -1/2 numerically dim Omega = 4, a closure point).
   M_B_ii: {d0 = d3 = 0} (sg free; at sg = -1/2 dim Omega = 2).
   Q0_B, P0_B, P0_A_i: running at 20:22 (see STATUS).
 The survivors, tested numerically (stage2/r9_cand.py, r9_cand2.py; T_1 tool, FO2 = r5_FO2.FO2, (T2) = r6_T2.T2test):
   (S1) M_A_i at f0 = f3 = 2 (integer basis saved: stage2/r9/cand_D04_MAi_f2.npy): rows (1,1,3,2), single-row parts (0,0,2,1), dim T_1 = 12,
        Omega = C^5 (confirmed), FO2 (12, 7, 8) -> bound 8: DEAD by FO2 [numerical], (T2) solvable.
   (S2) M_A_ii, d = 0: X = C kappa' + e_3 (x) span{(-4,1,1,1,1),(0,1,-1,0,0),(0,-1,-1,1,1)} + e_4 (x) (0,0,0,1,-1): a 3-dim single-row part
        (z = 3), FO2 bound 10, (T2) solvable: ALIVE, but of the exceptional z = 3 shape.
   (S3) M_B_ii, d = 0, sg != -1/2:  X = C kappa' (+) e_3 (x) span{(-4,1,1,1,1), (0,1,-1,0,0)} (+) e_4 (x) span{(0,0,0,1,-1), (0,1,1,-1,-1)},
        kappa' = (sg, -1-sg, 0, 1) in column 0 (rows 1..4).  Single-row parts (2, 2): NO 3-dim single-row part; Omega = C^5, dim T_1 = 13,
        FO2 (13, 8, 9) -> bound 9: passes FO2!; (T2) NOT solvable (distance 1.4 - 2.8): DEAD only by (T2).
 CONSEQUENCE for the structural target: the statement "(Q-r) + (FO-r) + FO2 => 3-dim single-row part" is FALSE as stated: (S3) is a
 counterexample [numerical FO2; exact (FO-r)]. The correct target must include (T2) (or a third-order test). (S3) is the first known (Q-r)
 solution with z <= 2 passing (FO-r) and FO2. It is built from two 2-dim single-row parts, so it belongs to the (B2) regime.

## R9-5. LEMMA PROP: proportional rows 1,2 make (FO-r) automatic; the clean split of the (2,4) family   [rigorous, two lines]
 LEMMA PROP. If on X the rows 1, 2 are proportional with ratio rho != 1 (s_2 = rho s_1, or s_1 = 0), then Omega(X) = C^5.
 Proof. From the verified cofactors (R7-2): C_1j - C_2j = (s_2 - s_1) gam_j = (rho - 1) s_1 gam_j lies in D(X), so s_1 gam_j lies in D(X), and
 C_0j = C_1j + s_1 gam_j lies in D(X) for j = 1..4 (for s_1 = 0: C_0j = C_1j). With C_00 = C_10 this gives Omega = C^5.  QED
 Case A (s = 0, rho = -1) is the special case rho = -1; this explains R7-2 "Case A: (FO-r) holds".
 SPLIT. Every (2,4) member X is either PROP (rows 1, 2 proportional with ratio != 1, incl. Case A and "one of rows 1,2 zero") -- then (FO-r) is
 BLIND and only FO2 / (T2) / higher order can decide -- or NON-PROP: the image of (s_1,s_2) is 2-dim or the diagonal; then some eta has
 s_1 = s_2 != 0 and LEMMA N0-W applies in Case B.
 Status of NON-PROP Case B after this round: B(ind) closed (R9-1); D1, D0-3, D00-2 closed except the c_a = 0 locus of D0-3/Q0 (3-dim single-row
 part); D0-4: M_A_i (only the point f0 = f3 = 2, FO2 bound 8), M_B_i (none); Q0_B, P0_B, P0_A_i still running; D00-3 not started (spec S7').
 PROP Case B members seen: (S2), (S3) of R9-4 (d = 0 in M_A_ii / M_B_ii). (S3) passes FO2 (bound 9) and dies by (T2) only.

## R9-6. D00-3 (a = b = 0, dim Y = 3), NON-PROP: exact loci   [char-0 elimination; stage2/r9/run_d003.sh, logs run_d003_*.log]
 X = K2 (+) lift(W) (+) C lift(y3): K2 = 2-dim subspace of the column-0 space C3 (charts 1, 2, 3 of Gr(2,3)), W = Y cap ker(lambda) with
 pattern Q0/P0/M (N0-W), Y = W + C y3 maximal isotropic (choices A/B as in D0-4), lift(y3) has column 0 = u1 * (complement of K2).
 Loci where Omega = C^5 can hold (closure):
   M_A_1, M_A_2, M_B_1, M_B_2, Q0_A_1, P0_A_1, Q0_B_1, P0_B_1, Q0_B_2, P0_B_2: <1> (closed).
   M_A_3, M_B_3: {u1 = 0, k2 = 1}: then (s_1,s_2) has image C(1+k1/2, -1+k1/2): PROP (k1 = 0: Case A). No non-PROP survivor.
   Q0_A_2: {u1 = 0}: (iii) forces k1 = 0, and then X = span(xi_d, kappa_q) + e_3 (x) (0; 1^perp): 3-dim single-row part (z = 3).
   P0_A_2: {u1 = 0}: kappa_q-type element gives q-row rank 4: violates (iii).
   Q0_A_3: {u1 = 0}: K2 contains c2 - k2 c3 with p_0 = 1 and p' of rank 3: violates (iii).
   P0_A_3: {u1 = 0}: (iii) forces k1 = k2 = 0, then X = span(xi_d, kappa_p) + e_4 (x) (0; 1^perp): z = 3.
   Q0_B_3, P0_B_3: running at 20:27.
 So D00-3 (non-PROP) has no first-order survivor except z = 3 shapes (pending the last two charts).
STATUS 20:28: RESULT-R9 at top; COMPUTE S3'/S7'/S8 + QUEUE line written. Waiting for D00-3 Q0_B_3/P0_B_3 and D04 P0_B_i.
STATUS 20:32: handover/HANDOVER-stage2.md written; N0-W numerical sanity passed (stage2/r9_N0W_sanity.py: 1e-16 on W for v in Omega, O(1) control); running: direct FP0d/FQ0d (independent check of R9-1), D00-3 Q0_B_3/P0_B_3.
STATUS 20:38: coordinator runs ST2-S7' (runs/st2s7_*.log); its D00-3 results reproduce mine (Q0_A_3, P0_A_3: u1 = 0; Q0_B_2, P0_B_2: unit). Three D04 scripts were missing at its start -> regenerated, QUEUE addendum. My duplicate Q0_B_3 run stopped.
STATUS 20:38: merged the cloud's missing 81 NOTES lines (RESULT-R8, R8-1..R8-4) and COMPUTE S3'/S7 (backups in stage2/r9/*.backup-2045.md); label clash noted: cloud S7 = (B0a) census (not run), my ST2-S7' = B(dep) exact runs.

## R9-7. Where the structural target stands after round 9
 Target as given ("(Q-r) + (FO-r) + FO2 => 3-dim single-row part"): FALSE by (S3) [exact (FO-r), numerical FO2 (13,8,9), robust over 3 seeds and
 3 values of sg]. Proposed corrected target (T'): "(Q-r) + (FO-r) + FO2 + (T2) => a 3-dim single-row OR single-column part" (the column
 alternative was already flagged by the predecessor, R8-1). Evidence for (T') inside the (2,4) family:
   NON-PROP Case B: exact up to the queued families; survivors: z = 3 shapes, and the point S1 (FO2 = 8).
   PROP (incl. Case A): (FO-r) is blind (Lemma PROP); FO2 and (T2) do the work: Case A FO2 = 8 (numerical, R7-2), (S3) dies by (T2),
   (S2) has z = 3. A PROP census (COMPUTE S8) is the next piece of evidence; a PROOF for PROP needs a second-order argument.
 (T2) carries weight now: (S3) is excluded ONLY by it; r6_T2.py's condition should be re-derived by verify2 (R6-7 says "conditions rigorous").
 Saved: stage2/r9/cand_S3_sg.npy (sg = 0.3+0.4i), cand_S3_sg2.npy (sg = 2), cand_D04_MAi_f2.npy (S1).

## R9-8. A sharper necessary condition (N1) for lam = 0, and D0-4 Q0_B, P0_A, P0_B   [N1 rigorous; loci exact (char 0); FO2/T2 numerical]
 LEMMA N1. Case B, b = 0 on X (lam = 0), non-PROP, (0,e_m) in Omega. On X_s := X cap {s_1 = s_2 = 0} one has s = q_0 = 0, p_0 = -a, and there is
 T in C^4 (T_j = t_1j + t_2j) with
     (A) 2 p_m q_m - 2 a q_m - a Q_T = 0,      (B) p_m q_m + sum_j T_j p_j q_j = 0      identically on X_s.
 Proof: on X_s the quadratic part of F = C_0m + sum t_ij C_ij is 4 p_m q_m + 4 sum_j T_j p_j q_j (C_0m, C_1j, C_2j: 2 g + quadratic part 2 a q of
 h with P_0 = 1 - a; C_3j, C_4j, C_i0 affine) -> (B); the eps^1 part of the cubic part at xi_0 in X_s along eta with s_1 = s_2 != 0 gives
 2 g_m + sum T_j g_j = 0, g_j = 2 p_j q_j - a q_j -> with (B) this is (A). QED  (N1 contains N0-W: set a = 0.)
 Applied (stage2/r9_N1.py; T's eliminated over QQ; F0, F3 = phi or d on h and y3):
   calibration: M_A -> F0 = +-F3 (contains the known point f0 = f3 = 2); M_B -> F0 = F3 = 0 (as the full system).
   Q0_B -> F0 = 0: then lift(h) has column 0 = (0,0,-4,0) and is a single-row element: z_3 = 3. So Q0_B (cases i, ii) has NO non-PROP survivor
           other than z = 3 shapes.                                                                                    [rigorous + exact]
   P0_A -> F3 = 0; with (iii) (f0 = 0 in case i; case ii impossible) phi = 0, s = 0: Case A. P0_A CLOSED.
   P0_B -> F0 = F3 = 0 (Case A / PROP) or ten 1-parameter components (V' special: r1 or r2 in {0,-1} or r1 = r2, F3 linear in F0). The FULL
           direct system restricted to these components (stage2/r9/run_P0B_comp.sh): case i leaves only Case A and TWO POINTS
           (r1 = r2 = -1, f0 = f3 = 2) and (r1 = r2 = 0, f0 = 2, f3 = -2): both have Omega = C^5 but FO2 (12,7,8) -> bound 8 and (T2) fails
           (distance 2.8): DEAD [numerical]. Case ii: 6 component runs > 400 s here -> QUEUE ST2-S7' addendum 3.
 So D0-4 is reduced to: z = 3 shapes, PROP, three isolated points with FO2 bound 8 (S1 and the two P0_B_i points), and P0_B_ii (running).
STATUS 20:50: P0_B case ii components > 400 s each; queued (QUEUE addendum 3). Writing the final report.

# ROUND 10 (start 20:53 UTC, about 1-1.5 h). Targets: (1) collect queued verdicts, push non-PROP points through r9_D04num.py; (2) (T2): crisp
# statement + proof for verify2, then the corrected target on the PROP family (S8); (3) FO2 <= 8 on Case A / PROP; (4) (B0a), B2.
STATUS 20:53: round 10 started. Queue: P0_B_ii comps 2-4 running (runs/st2_Dir_*), D00-3 Q0_B_3 / P0_B_3 running (runs/st2s7_*).

## R10-1. LEMMA (T2): statement and proof (for verify2), and the EXACT death of survivor (S3)
 SETTING. L a level space (perm(J + t) = 120 on L), r a row with pi_r(L) a hyperplane not containing 1 (a_r = 1), L^ = C J (+) L,
 ell(cJ + t) = c, L_r = {t in L : t_r = 0} viewed as 4x5 matrices (rows != r), G(Y) = (perm_4(Y without column j))_{j=0..4} for Y in C^{4x5}.
 LEMMA (T2). There are T_0, ..., T_4 in C^{4x5} with  sum_k T_k in J' + L_r  (J' = all-ones 4x5)  such that for all xi in L_r and all j <= k:
        D_{T_k} G_j (xi) + D_{T_j} G_k (xi) = 0.
 PROOF. (i) R0: perm(u) = 120 ell(u)^5 on L^ (homogeneity of perm and level). (ii) Laplace along row r: perm(u) = <u_r, G(u')>, u' = rows != r.
 (iii) pi_r(L^) = pi_r(L) + C 1 = C^5, so there is a linear T : C^5 -> C^{4x5} with L^ = {(v ; T(v) + xi) : v in C^5, xi in L_r}; T(1) - J' lies
 in L_r because J in L^ has row r = 1 (choose T(1) = J'); ell((v ; T(v) + xi)) = <kappa, v> for a fixed kappa. Hence (chief RP6)
        <v, G(T(v) + xi)> = 120 <kappa, v>^5   for all v in C^5, xi in L_r.                                              (**)
 (iv) Replace v by eps v and use G(xi + eps T(v)) = G(xi) + eps D_{T(v)} G(xi) + O(eps^2) (G is a polynomial map):
      eps^1: <v, G(xi)> = 0 for all v, i.e. G = 0 on L_r ((Q-r)(ii));   eps^2: <v, D_{T(v)} G(xi)> = 0 for all v, i.e. the quadratic form
      v -> sum_{j,k} v_j v_k D_{T_k} G_j(xi) vanishes; its polarisation is the displayed identity (T_k = T(e_k)), and sum_k T_k = T(1) = J'. QED
 Remarks. Changing T_k by elements of L_r does not change the identity (D_{xi'} G(xi) = 0 for xi, xi' in L_r since G = 0 on L_r), so (T2) is a
 well-posed LINEAR condition on X = L_r: "J' lies in {sum_k T_k : T solves the homogeneous system} + X". It needs only a_r = 1 (any dim L).
 Numerical tool: stage2/r6_T2.py (null space at 30 random points, then least-squares distance of J'). EXACT tool (new): stage2/r10_T2exact.py
 (Singular over QQ; unknowns T (100), c (5) for J' = sum T_k - sum c_m B_m, parameters allowed; unit ideal = (T2) fails for all parameters).
 RESULTS (exact, char 0):  (S3) [parameter sg]: UNIT -> (T2) fails for EVERY sg: (S3) is RIGOROUSLY not an L_r (given Lemma (T2)).
   controls: (S2) (z = 3) solvable for all sg; S1 (D04 M_A_i point) solvable -- both agree with r6_T2.py (distances 1e-14).
 Also from the queue: D04 P0_A_i rerun (runs/st2s7_..._rerun.log): locus f3 = 0, f0 in {0, 2}; f0 = 2 breaks (iii) (q-row rank 4), f0 = 0 is
 Case A: P0_A_i closed (agrees with R9-8).

## R10-2. The PROP family of Case B, classified; (T') is FALSE too; first PROP candidates passing (FO-r) + FO2 + (T2) with z, z' <= 2
 CLASSIFICATION [rigorous, from R9-2 geometry]: a PROP member (rows 1,2 proportional with ratio != 1) cannot contain xi_d unless s = 0, so
 Case B(ind), D1, D0-3, D00-2 and D0-4 case (i) contain no PROP member. Remaining:
   D04-PROP (= D0-4 case (ii), d = 0): (iii) forces rank q'|Y_a <= 2 and rank p'|Y_a <= 2, so Y_a = A x A^perp (split; A in 1^perp, dim A in {1,2},
     A^perp := A^perp cap 1^perp):  X = C kappa'(sg) (+) e_3 (x) span{(-4;1'), (0;A)} (+) e_4 (x) (0;A^perp),  kappa' = (sg,-1-sg,0,1) in column 0.
     dim A = 2: z = (3,1) (exceptional shape);  dim A = 1: z = (2,2) [(S3) is A = C(1,-1,0,0)].
   D003-PROP (a = b = 0, PROP): K2 must contain kappa0 = (0,0,1,-1) (column 0, rows 1..4); the lift has zero column 0 (otherwise the (s_1,s_2)
     image is 2-dim); again Y = A x A^perp:  X = span(kappa0, kappa_l) (+) e_3 (x) (0;A) (+) e_4 (x) (0;A^perp),  kappa_l = (l1,l2,0,-l1-l2);
     z = (1,2) or (2,1), single-column part 2 (column 0). Case A inside it: l = (1,-1).  [all members level: a = b = 0, A perp A^perp]
 TESTS (numerical: r10_prop.py; exact (T2): r10_T2exact.py):
   all members: Omega = C^5 (Lemma PROP), dim T_1 = 13, FO2 (13,8,9) -> bound 9 (every member tested, ~20).
   (T2) exact on D04-PROP dim A = 1 (alpha = (1,a2,a3,.), parameter sg): solvable EXACTLY on alpha in {(1,-1,1,-1), (1,1,-1,-1), (1,-1,-1,1)}
        (all sg); fails elsewhere (incl. (S3)). Numerically D04-PROP dim A = 2 with random A fails (T2) (0.8), the special (S2) passes.
   (T2) numerical on D003-PROP: generic l fails; l = (1,-1) (Case A) PASSES for random A (dim A = 1 and 2; distances 4e-15 .. 2e-14);
        l = (1,0) passes only for special A (e.g. C(1,-1,0,0)).
 CONSEQUENCE: the corrected target (T') "(FO-r) + FO2 + (T2) => 3-dim single-row or single-column part" is FALSE [numerical FO2 and (T2),
 exact (T2) for the D04 family]:  e.g. X = span{(0,1,-1,0,0)^T e_0^T... } -- concretely, in 4x5 form (rows 1..4):
        column-0 part {(s, -s, pi, -pi)}  (+)  e_3 (x) (0; A)  (+)  e_4 (x) (0; A^perp cap 1^perp),   any A = C alpha, alpha in 1^perp,
 and D04-PROP with alpha = (1,1,-1,-1). These are the FIRST known (Q-r) solutions with all single-row/column parts <= 2 that pass (FO-r),
 FO2 and (T2). (T2) is weak on such sparse X: its solution space has dim 82-86 of 100.
 DECISIVE TEST for a candidate X (rigorous equivalence, R10-3 below): a 9-dim level L with L_r = X exists iff the full chief identity (**) has
 a solution T, kappa; equivalently (T1)-(T5). Running: calibrated extension LM (stage2/r10_extend.py; calibration ex1, D = 7: 3/3 hits) with
 D = 9 on cand_D003P_l1m1.npy and cand_D04P_a11m1m1.npy (logs stage2/r9/ext10_*).

## R10-3. The decisive test for a candidate L_r: (**) <=> 9-dim level space, graded as (T1)-(T5)   [rigorous]
 PROPOSITION. For a 5-dim space X of 4x5 matrices TFAE: (a) there is a 9-dim level space L with a row r such that pi_r(L) is a hyperplane not
 containing 1 and L_r = X; (b) there are a linear T : C^5 -> C^{4x5} with T(1) in J' + X and kappa in C^5 with
        <v, G(T(v) + xi)> = 120 <kappa, v>^5   for all v in C^5, xi in X.                                                  (**)
 Proof. (a) => (b): chief RP6 (R10-1 (i)-(iii)). (b) => (a): put L^ = {(v ; T(v) + xi)} (dim 10), ell(v ; T(v)+xi) = <kappa,v>. Laplace along row r
 gives perm = 120 ell^5 on L^. v = 1, xi = 0: 120 = perm(J) = 120 <kappa,1>^5, so omega := <kappa,1> != 0. L := L^ cap ker(ell) has dim 9, J + L lies in
 L^ with ell = omega, so perm(J + t) = 120 omega^5 = 120 on L; pi_r(L) = kappa^perp (1 not in it) and L_r = X.  QED
 Grading by the degree in v (G(T(v)+xi) = sum_n D^n G(xi)[T(v)^n]/n!, degree n+1 in v):
   (T1) G = 0 on X;  (T2) <v, D G(xi)[T(v)]> = 0;  (T3) <v, D^2 G(xi)[T(v),T(v)]> = 0;  (T4) <v, D^3 G(xi)[T(v)^3]> = 0;  (T5) <v, G(T(v))> = 120 <kappa,v>^5.
 (T2) is linear in T, (T3) quadratic, (T4) cubic, (T5) quartic; (FO-r) and FO2 are consequences at v -> 1. So for each candidate of R10-2 the
 complete question is the polynomial system (T3)-(T5) on the (T2)-solution space (61 free parameters modulo X for cand_D003P_l1m1) -- equivalent
 to the extension search inside T_1(X) that r10_extend.py does numerically.
 Target 3 of this round ("FO2 <= 8 on Case A / PROP") is FALSE as stated: the D003-PROP Case-A members (l = (1,-1)) have FO2 bound 9 (R10-2);
 Case A solutions of the earlier census (bound 8) are a different stratum.

## R10-4. verify2's caveat applied; exact (T2) for the new candidates; FO2-JOINT, a sharper second-order test
 verify2 (round 8): (T2) re-derived and correct; (S3) dead rigorously (certificate over Q(sg)); S1 dead rigorously (exact FO2 = 8); r6_T2.py's
 SOLVABLE verdicts are unreliable (30 points < 35 cubic monomials). My r10_T2exact.py has no sampling (coefficients of the cubic identities in
 all monomials), so its verdicts are exact. Status of the R10-2 candidates under the EXACT test:
   D04-PROP, alpha in {(1,-1,1,-1),(1,1,-1,-1),(1,-1,-1,1)}: (T2) solvable [exact, R10-2 locus];   D003-PROP Case A, A = C(1,-1,0,0): (T2) solvable
   [exact: T2x_D003A.sing, non-unit];  D003-PROP Case A with general A: exact run T2x_D003Agen (running).  The numerical "dim 82-86" of the
   (T2) solution space is inflated by under-sampling and must not be quoted.
 FO2-JOINT (new test) [lemma rigorous]: if L is level and X in L, then L lies in T_1(X) and is totally isotropic for q_m = D^2 perm(J+m) for EVERY
 m in X simultaneously (FO2 uses one generic combination). X lies in the radical of each q_m on T_1(X) (differentiate D_t perm(J+m) = 0 along X).
 So L/X must be a COMMON isotropic subspace of the span S of {q_m} on T_1(X)/X.  If dim L = dim X + (1/2) dim T_1/X (Lagrangian case) and S
 contains a nondegenerate Q1, then L/X is invariant under all Q1^{-1}F (F in S): if these generate the full matrix algebra, no such L exists.
 Numerical (stage2/r10_FO2J.py): cand_D003P_l1m1: dim T_1/X = 8, dim S = 8, common radical 0; LM for a common isotropic 4-space (D = 9) floors at
 0.376 (repeated), 3-space (D = 8) at 0.105 (repeated); calibration ex1 (D = 7) 3/3. Exact (stage2/r10_FO2J_exact.py, sympy over QQ): running.
 Extension LM inside T_1(X) (r10_extend.py; calibration ex1 D = 7 3/3): no 9-dim (floors 1.6 - 1.9) and no 8-dim (floors 0.78, 1.22) level space
 contains cand_D003P_l1m1; none of dim 9 contains cand_D04P_a11m1m1 (floors 1.15, 1.55). [numerical, repeated floors]
STATUS 21:09: exact FO2-joint on cand_D003P_l1m1 running; exact (T2) for general A running.
 EXACT FO2-JOINT for cand_D003P_l1m1 (X0 = column-0 part {(s,-s,pi,-pi)} + e_3 (x) (0;1,-1,0,0) + e_4 (x) (0; span{(0,0,1,-1),(1,1,-1,-1)})):
   sympy over QQ: dim T_1(X0) = 13, complement 8, span of the q_m (m in X0) on T_1/X0 has dim 8; the algebra generated by Q1^{-1}F has dim 26 (not
   full: reducible), so the invariant-subspace shortcut does not apply; instead ALL 70 charts of Gr(4,8): Singular over QQ, the ideal "L'' isotropic
   for all 8 forms" is <1> in every chart (r9/FO2J_charts_D003A_k4.sing, < 1 min).  =>  NO 9-dim level space contains X0  [rigorous: FO2-joint
   lemma + exact T_1 + char-0 GB on all charts of a projective variety].  This candidate passes (FO-r), FO2 and (T2) exactly, so FO2-JOINT is
   strictly stronger than the three tests together.
STATUS 21:16: RESULT-R10 at top. FO2-joint exact kill of cand_D003P_l1m1; exact exports for D04Pa (sg=2) and S2 (sg=2) running.

## R10-5. FO2-JOINT: exact kills, numerical census, and what it suggests
 EXACT (sympy T_1 and forms over QQ, then Singular over QQ on ALL charts of Gr(4, dim T_1/X); unit everywhere = no common isotropic 4-space):
   cand_D003P_l1m1 (D003-PROP Case A, A = C(1,-1,0,0)):     70/70 charts unit   -> no 9-dim level space contains it.
   cand D04-PROP alpha = (1,1,-1,-1), sg = 2 and sg = -3:  126/126 charts unit -> no 9-dim level space contains it (for these sg).
   (S2) (z = 3), sg = 2: Gr(4,10), 210 charts, running (r9/FO2J_charts_S2s_k4.log).
 NUMERICAL census (r10_FO2J.py, LM on the Grassmannian; calibration: L_r of ex1 row 3, need a common isotropic 4-space in a 14-dim complement:
   residual 1.9e-6 / 3e-3, i.e. found): for all 18 saved candidates of rounds 5-7 (stage2/data/, copied from the cloud) and the 3 new ones, no
   common isotropic 4-space: repeated floors 0.14 (cross a in C1) .. 0.81. This includes the z = 3 survivors of R6/R7 ((3,3) family, cross a in C1)
   that passed (Q-r), (FO-r), FO2 and (T2).  [r9/FO2J_census.log]
 Algebra shortcut (r10_FO2J_alg.py): full matrix algebra for 4 of the (3,3) candidates (=> no common invariant, hence no common Lagrangian subspace,
   when dim T_1/X = 8); not full (dim 17-27) for X0, cross, two (3,3) candidates -> there the chart computation is needed.
 SUGGESTED TARGET (replaces (T')): "every (Q-r) solution X fails FO2-joint at D = 9", i.e. T_1(X)/X has no 4-dim subspace isotropic for all
 q_m, m in X. It is a statement about one explicit linear system of quadrics per X, exactly checkable family by family (charts or the algebra test),
 and it would also close the z = 3 branch (predecessor's O1) if it holds on the (3,3) and cross families.
 Caveat: the FO2-joint exact runs used fixed rational parameter values (sg = 2, -3); a parameter-symbolic version (T_1 over Q(sg)) is the next step.
STATUS 21:28: exact FO2-joint chart runs for (S2) (z=3, Gr(4,10)) and cross a in C1 (z=3, Gr(4,8), only 4 forms) running 12 / 7 min; queue (P0_B_ii comps, D00-3 Q0_B_3/P0_B_3) still without verdict.
STATUS 21:33: crossC1 exact FO2J chart run (with progress) started, chart 1/70 unit after 20 s; S2s run ends by 21:42.
 UPDATE 21:36: (a) D04-PROP alpha = (1,1,-1,-1) with sg SYMBOLIC: T_1 over Q(sg) has dim 14 (complement 9, span of forms 11), the chart script with sg
   as a ring variable is running (r9/FO2J_charts_D04Pasym_k4.log, progress per chart; chart 1 unit). A unit result in all 126 charts proves the kill
   for all sg outside the finite set where the cleared-denominator complement basis degenerates or dim T_1 jumps (to be listed; sg = 2, -3 are done
   exactly). The three alpha's {(1,1,-1,-1),(1,-1,1,-1),(1,-1,-1,1)} are permutations of columns 2,3,4 of each other, so one suffices.
 (b) cross a in C1 (z = 3): exact chart run with progress in my slot (r9/FO2J_charts_crossC1_k4.log; 3 of 70 charts unit by 21:34, none non-unit).
 (c) (S2) (z = 3): the coordinator runs FO2J_charts_S2s_k4.sing from the queue (timeout 3 h); my duplicate run was stopped.
STATUS 21:36: round-10 final report being sent; two chart runs continue in my slot (logs above).

# ROUND 11 (start 21:37 UTC, ~1-1.5 h). Targets: (1) FO2-joint exactly with symbolic parameters (exceptional sigma incl. 0, -1 for D04-PROP; general A
# of D003-PROP Case A; (3,3) z = 3 family; cross a in C1; (S2); Case-A census family); (2) structural proof "every (Q-r) solution fails FO2-joint at
# D = 9"; (3) queue verdicts; (4) (B0a), B2. Memory rule: one own job > 0.5 GB at a time, cap 2 GB.
STATUS 21:37: round 11 started; my cross-C1 chart run kept (coordinator asked to drop its duplicate); D04Pasym chart run continues.

## R11-1. D04-PROP (alpha = (1,1,-1,-1)) for ALL sigma: exceptional set, and why the symbolic chart run was stopped
 Exceptional set (stage2/r11_exceptional.py, exact sympy; gcd of determinants of random integer compressions, a rigorous SUPERSET of the bad set):
   rank of the T_1 system is 11 for EVERY sigma (test polynomial = nonzero constant)  =>  dim T_1(X_sigma) = 14 for all sigma;
   the cleared-denominator complement basis used by the symbolic export degenerates only at sigma = 0 (test polynomial 2 sigma^2).
 So the symbolic chart computation (sigma a ring variable, all 126 charts unit) would prove the kill for all sigma != 0. It is too slow: chart 2 did
 not finish in 9 min (chart 1 unit in seconds), so 126 charts are out of reach this way. Stopped at 21:45.
 sigma = 0 (row 1 of X vanishes): the span of the forms drops to dim 7; exact chart run at sigma = 0 is running.
 Exact fixed values done: sigma = 2, -3 (126/126 unit each).

## R11-2. Fast exact chart test with msolve (projective argument) -- cross a in C1 (z = 3) and D04-PROP sigma = 0 are DEAD
 METHOD (stage2/r11_charts_msolve.py): for FIXED rational data the common-isotropic variety V = {L'' in Gr(k,nq) : F_i|L'' = 0} is a closed
 subscheme of the proper Grassmannian over Z[1/N] (N = lcm of denominators). If msolve (-g 2, mod p, p not dividing N) returns the GB [1] on
 every standard chart, V has no point over F_p-bar, hence none over Q-bar (a Q-bar point reduces mod a prime above p by properness): a PROOF
 (BRIEF UPDATE 10). Calibration both ways: D003A forms -> 70/70 [1] (agrees with Singular over QQ); D003A with only one form -> non-unit
 (single quadric has Lagrangians). Speed: 70 charts in ~20 s (vs. > 1 min per hard chart in Singular).
 RESULTS (p = 2147483629):
   cross a in C1 (X = column 0 {(0,0,y2,y3,y4)} + row 1 {(0;w)}, z = 3 in row 1, z' = 2): 70/70 charts [1]  ->  NO 9-dim level space contains it.
       This is one of the z = 3 ("split free line") survivors that passed (Q-r), (FO-r), FO2 and (T2) (R6-3, R7-1).
   D04-PROP alpha = (1,1,-1,-1), sigma = 0 (the only exceptional sigma of R11-1): 126/126 charts [1] (N = 5) -> dead.
 RIGOROUS CONSEQUENCE for D04-PROP (alpha = (1,1,-1,-1), hence all three special alpha by column symmetry): the set of sigma admitting a 9-dim
 extension is closed in A^1 \ {0} (projection of a closed subset of A^1 x Gr, Gr proper) and misses sigma = 2, so it is FINITE; sigma = 0 is dead.
 The parametric msolve run (sigma affine + the chart tau = 1/sigma with homogenised forms; both charts of P^1) decides the finite set; queued in my
 slot after (S2).

## R11-3. The (3,3) z = 3 family is killed by FO2-joint too (explicit member, exact); what FO2-joint says when z_i = 3
 Family [rigorous level check by hand + numerics]: X(y,y',Z) = C y e_0^T + C y' e_1^T + e_4 (x) Z, with y, y' supported in rows 1..3 (y_4 = y'_4 = 0),
 sum y = sum y' = 0, <y,y'> = 0, Z a 3-dim subspace of 1^perp in C^5 (P_1, P_2, P_3 cross terms vanish: (sum y)(.) = 0 and <y,y'> = 0; (ii) holds since
 rows 1-3 live in two columns). This is the FK(3,3) z = 3 shape of R6/R7 (ALIVE there).
 Member y = (1,-1,0,0), y' = (1,1,-2,0), Z = span{(1,2,-3,0,0),(0,1,1,-2,0),(2,0,1,1,-4)} (stage2/r9/cand_K33_z3.npy): level err 9e-14, dim T_1 = 13,
 Omega = C^5, FO2 (13,8,9) -> alive under (FO-r) and FO2;  FO2-JOINT exact: span of forms dim 4, msolve 70/70 charts [1] -> NO 9-dim extension.
 OBSERVATION (towards a structural lemma for z_i = 3): for a single-row element m = s e_i w^T the form q_m is AFFINE in s:
   q_{s e_i w^T}(t,t) = q_0(t,t) + s Bw(t,t),  q_0 = 12 P_2,  Bw(t,t) = -2 sum_{i' != k, both != i} sum_{j != l} (w_j + w_l) t_{i'j} t_{kl}
   = 4 sum_j w_j P_2(t^(i) without column j)   (sum w = 0; t^(i) = t without row i).
 So if e_i (x) Z lies in L with dim Z = 3 (Z = (C1 + Cm)^perp), FO2-joint forces, for EVERY t in L, the vector (P_2(t^(i) minus column j))_j to lie in
 span(1, m): the quadratic part of the (5,1)-defect condition "G(J' + .) in span(1,m)" (R7-3) holds on the projection of ALL of L, not only on L_i.
 For K33 and D04-PROP these single-row forms (plus P_2) already have no common isotropic 4-space (numerically for D04-PROP: m restricted to the
 single-row part, N = 3, floor 0.07). This is the most promising route to a uniform proof of O1 (z = 3).

## R11-4. D04-PROP for ALL sigma: saturated basis + parametric msolve on both charts of P^1
 (S2) at sigma = 2: msolve 210/210 charts [1] (N = 10) -> dead at sigma = 2 (z = 3 member).
 Parametric run, first attempt (unsaturated basis): 23 non-unit charts; msolve elimination (-e) on chart (0,1,2,4), mod p AND in char 0 (msolve
 multimodular), gives the elimination ideal (sg): all those solutions sit at sigma = 0, where that basis is invalid -> artifacts. To make the
 argument proof-grade without a char-0 elimination per chart, the complement basis was SATURATED at sigma = 0 (two steps: replace a row by
 (c^T [X;Qm](sigma))/sigma for c in the left kernel at sigma = 0; stage2/r9/r10_FO2J_exact_sat.py): now [X; Qm] has full rank 14 for every sigma
 and dim T_1 = 14 for every sigma (R11-1), so T_1 = X (+) span(Qm(sigma)) for ALL sigma in C.
 ARGUMENT: V = {(sigma, L'') : F_i(sigma)|L'' = 0} closed in P^1 x Gr(4,9) (tau = 1/sigma chart with homogenised forms). A complex 9-dim extension
 at some sigma_0 gives a Q-bar point of V (sigma_0 algebraic: V's sigma-projection is a closed subset defined over Q), which reduces mod a prime above p
 to an F_p-bar point of V in one of the two sigma-charts. So "[1] in all 2 x 126 charts mod p" proves: NO sigma admits a 9-dim level space containing
 the D04-PROP member (alpha = (1,1,-1,-1), hence all three special alpha). Run: r9/run_msolve_param_sat.log (running 21:59).

## R11-5. Status of the parametric D04-PROP proof, and the B(dep) eliminations via msolve
 Saturated parametric run mod p (r9/run_msolve_param_sat.log): affine sigma-chart 126/126 [1]; tau-chart 101/126 [1], 25 non-unit, and for ALL 25 the
 char-0 elimination ideal (msolve -e, multimodular) is (tau) or (tau^3): every solution sits at tau = 0 (sigma = infinity, outside the family).
 What this proves RIGOROUSLY (projective reduction argument, p = 2147483629): no sigma_0 admits a 9-dim extension unless sigma_0 is algebraic with
 negative valuation at every prime above p (transcendental sigma_0 is excluded because the exceptional set is closed, defined over Q and misses 2);
 together with the exact runs at sigma = 0, 2, -3. The remaining loophole (sigma_0 with p in the denominator at all primes above p) is closed by a char-0
 computation: msolve char 0 on all 126 affine sigma-charts is running (r9/run_msolve_param_sat_char0.log; msolve's char-0 GB is multimodular, i.e.
 strong evidence, not a certificate); a Singular char-0 certification per chart is too slow (> 2 min per hard chart).
 B(dep) eliminations: the coordinator killed the stalled Singular eliminations (swap). Replacement tool stage2/r11_elim_msolve.py (Singular only dumps
 the incidence ideal, msolve -e eliminates the 60 t's; seconds): P0_B_ii comp2 -> {d0 = d3 = 0, r2 = -1}, i.e. PROP only (mod p, evidence).
 The other comps and D00-3 Q0_B_3 / P0_B_3 are queued for after the Lean window (msolve needs ~1.5 GB virtual memory; segfault under 0.5 GB).
 UPDATE 22:18: msolve in CHARACTERISTIC 0 on all 126 affine sigma-charts (saturated basis): all [1] (r9/run_msolve_param_sat_char0.log).
 => D04-PROP with alpha in {(1,1,-1,-1),(1,-1,1,-1),(1,-1,-1,1)}: NO sigma in C admits a 9-dim level space containing X_sigma
    [rigorous mod-p projective argument for all sigma except those with p in every denominator; that loophole closed by msolve char 0 (multimodular,
    evidence-grade); a Singular certification would remove the caveat].
STATUS 22:18: round 11 final report being sent. No own jobs running. Queue: ST2-ELIM-msolve (after the Lean window).

# ROUND 12 (start 22:20 UTC, ~1-1.5 h). Targets: (1) structural proof of O1 via the B_w forms; (2) parametric FO2-joint for D003-PROP Case A over
# P^2_alpha and the (3,3) z = 3 family; (3) Singular certificates for the char-0 msolve steps (D04-PROP); (4) ST2-ELIM-msolve verdicts.
 ADDENDUM to R10-2 (verify2's missing line): in the PROP classification, a maximal isotropic Y_a = {(p, omega(p) + n) : p in A, n in A^perp} has the
 bilinear form (p, p') -> <p, omega(p')> ANTISYMMETRIC on A; "rank q'|Y_a <= 2" with dim A = 2 gives rank(omega) <= 1, and an antisymmetric form of
 rank <= 1 is zero, so omega = 0 and Y_a = A x A^perp (split). (For dim A = 1 omega = 0 trivially; dim A = 3 or 0 is excluded by the rank bounds.)
STATUS 22:21: round 12 started.

## R12-1. ST2-ELIM-msolve verdicts (B(dep) leftovers) -- Case B of (2,4) is now closed at first order up to FO2/FO2J-dead points
 msolve -e (mod 2147483629, evidence; mod 536870909 for the Singular primary decomposition):
   D04 P0_B_ii comp2, comp3, comp4, comp5: elimination ideal {d0 = d3 = 0, ...} -> PROP only.  compB10, compB11 (full system segfaults at 2 GB):
   with v = e_1 alone already {d0 = d3 = 0, r1 = r2} -> PROP only (v = e_1 is a necessary subsystem).
   D00-3 Q0_B_3: v = e_1 and v = e_2 subsystems (v = e_3 and the full system segfault); minimal primes of E1 + E2 (Singular mod 536870909):
     [1] k2 = 1, u1 = 0: PROP;  [2]-[7] six points (k1 = 0; (r1,r2) in {(0,1),(1,0),(-1,-2),(-2,-1)} with k2 = 1/3, u1 = 0, and (0,0), (-1,-1) with
     k2 = 1/2, u1 = -1 resp. 1);  [8] r1 = r2 = -1/2, u1 = 0 (2-dim).
     Numerically (r12_D003num.py, T_1 tool): the four k2 = 1/3 points and component [8] have Omega of dim 2 resp. 4 (fail (FO-r) by v = e_3);
     the two k2 = 1/2 points have Omega = C^5 and FO2 (12,7,8); FO2-JOINT EXACT (msolve, 35/35 charts of Gr(4,7) [1]) -> both DEAD.
   D00-3 P0_B_3 (segfault): it is the mirror image (rows 3 <-> 4, p <-> q) of Q0_B in charts 2/3 of K2, both done -> covered.
 SUMMARY of Case B of (2,4) at first order: every X passing (FO-r) is PROP, or has a 3-dim single-row part, or is one of finitely many explicit points,
 all of which are dead (S1: exact FO2 = 8 by verify2; P0_B_i points: FO2 = 8 and (T2) fail [numerical]; D00-3 points: FO2-joint exact).
 [Status of the modular parts: mod-p eliminations are evidence; the loci found are then checked directly.]

## R12-2. z = 3 shapes inside Case B are dead too
 The (FO-r)-passing z = 3 members of Case B are cross-type: X = (2-dim column-0 space on the rows != r,i, sum 0) (+) e_i (x) Z.
   D00-3 Q0_A_2 (k1 = u1 = 0) = "crossA": X = span(xi_d, kappa_q) + e_3 (x) (0; 1^perp): FO2-joint EXACT, msolve 70/70 charts [1] -> DEAD.
   D00-3 P0_A_3 (k1 = k2 = 0): mirror image of crossA -> DEAD.
   D0Q (c_a = 0) family: X = span(xi_d, kappa_q) + e_3 (x) {(-sum p'; p') : p' in n^perp} (3 parameters n; crossA is n = (1,1,1,1)): FO2-joint
   numerically obstructs for 3 random n (floors 0.30 - 0.33, N = 4 forms = P_2 and the B_z); parametric proof not done.
   D04-PROP dim A = 2 (S2 type): (S2) at sg = 2 exact; general (A, sg): (T2) fails numerically for random A (R10-2), FO2J numerically.

## R12-3. Toward a uniform O1 proof via the B_w forms: what holds, what does not
 (a) For K33-type members (random y, Z) the span of ALL q_m (m in X) EQUALS span{P_2, B_z : z in Z} (N = 4 both ways), and FO2-joint fails
     numerically (floors 0.28 - 0.33): the obstruction is carried by the single-row forms alone.  Same for the cross-type family.
 (b) Form structure on T_1(X)/X is NOT uniform across shapes (r12_forms_struct.py): q_0 = 12 P_2 nondegenerate in all cases; B_z of rank 6 with a
     2-dim common kernel (K33), rank 2 with a 4-dim common kernel (cross C1), ranks 4-9 with a 1-dim kernel (S2). So a uniform proof cannot be a
     rank count on the B_z alone; it must use T_1(X), i.e. the shape of the plane P = X_ri.
 (c) Relation to the (5,1) structure: FO2-joint relative to the single-row part e_i (x) Z alone (X' = e_i Z) gives, for all t in L,
     c(t^(i)) in span(1,m) (first order) and (P_2(t^(i) minus column j))_j in span(1,m) (second order); both are already consequences of
     R7-3(d) (G(J' + eta) in span(1,m) on Lambda_0 = pi(L)). The extra force of the kills comes from T_1(L_r), i.e. from the plane X_ri.
 (d) Hence the concrete route to O1: classify the planes P = X_ri occurring with z_i = 3 (non-isotropic m: no single-row elements of other rows by
     SPLIT, so P = X_ri lives on the three rows != r,i, column sums in Cm, all 3x3 subpermanents vanish (C4), and "G(J''+p) in span(1,m),
     <1,G> = 120" (level of X)); every shape found so far is spanned by single-column elements (K33: two columns; cross: one column). If that
     classification holds, O1 reduces to the two parametric families (K33: y in P^1, Z in Gr(3,4); cross-type: Z) -- both killed at every member
     tested exactly (K33, cross C1, crossA) and numerically at random members. A numerical census of general planes P (r12_Pcensus.py) found only
     slowly converging near-solutions (fresh error ~1e-6, T_1 unreliable) -- inconclusive.
STATUS 22:41: R12-1..R12-3 written.

## R12-4. The two-column z = 3 family F2col: classification [rigorous] and FO2-joint [numerical; exact at 3 members]
 Setting: X = P (+) e_4 (x) Z (row r = 0 zero, single-row row i = 4), Z a 3-dim subspace of 1^perp in C^5, P a 2-dim space of matrices supported in
 rows 1..3 and in TWO columns {0,1} (columns p_0, p_1 in C^3; c_j = sum of p_j). Then (ii) holds (rows 1-3 live in 2 columns) and
   P_1 = c_0 + c_1;  P_2 = (c_0 c_1 - <p_0,p_1>) - c_0 (z_0 - z_1) (using c_1 = -c_0);  P_3 = (c_0 c_1 - <p_0,p_1>)(-(z_0 + z_1));  P_4 = P_5 = 0
 (P-rows occupy only two columns). Hence X is level  <=>  c_0 + c_1 = 0, <p_0,p_1> = -c_0^2 on P, and c_0 (z_0 - z_1) = 0 on P x Z.
 GENERIC Z (z_0 - z_1 not identically 0 on Z): c_0 = c_1 = 0 and P is a LAGRANGIAN (2-dim totally isotropic) subspace of the nondegenerate 4-dim
 quadric (S x S, <p_0,p_1>), S = sum-zero vectors of C^3: two P^1-families (rulings). One ruling contains P = {(0,u)} = 2-dim single-column space
 (the CROSS-type shape); the other contains P = span{(y,0),(0,y')}, <y,y'> = 0 (the K33 shape). SPECIAL Z = {sum z = 0, z_0 = z_1}: P any 2-dim
 subspace of {c_0 + c_1 = 0, <p_0,p_1> = -c_0^2}. So K33, cross C1 / crossA and the D0Q (c_a = 0) family are all members of one explicit family F2col
 with 1 + 3 parameters (ruling, lambda in P^1, Z in Gr(3,4)).
 Census inside the 2-column block (r12_Pcensus2col.py, LM, all 8/8 starts converge to 1e-13, fresh-point verified): members with and without
 single-column elements; all have dim T_1 = 13, Omega = C^5, FO2 (13,8,9) -- alive under (FO-r) and FO2 -- and FO2-joint fails (floors 0.29-0.31,
 N = 4 forms = P_2 + B_z). The unrestricted census (P with 3-5 columns, r12_Pcensus.py) produced only slowly converging near-solutions (fresh error
 ~1e-6) -- no clean member outside F2col found.
 => PROPOSED THEOREM (target for the next round): FO2-joint fails at D = 9 on every member of F2col (4-parameter exact computation: saturation +
 msolve charts over P^1 x Gr(3,4), or a hand argument with the explicit T_1). Together with "every z = 3 plane X_ri lies in a 2-column block"
 (needs proof) this would close O1 (z = 3) in REG1.
STATUS 22:42: R12-4 written (F2col classification). Writing RESULT-R12 and final message.
STATUS 22:42: round 12 final report sent via SendMessage (SubagentHandback already used in round 9).

# ROUND 13 (start 22:45 UTC, ~1-1.5 h). Targets: (1) FO2-joint on ALL of F2col exactly; (2) z = 3 planes X_ri lie in a 2-column block;
# (3) parametric D003-PROP Case A; (4) ST2-CERT-D04P.
STATUS 22:46: round 13 started; computing the explicit T_1 of F2col.

## R13-1. The cross-type ruling of F2col: explicit T_1 and a parametric FO2-joint run (in progress)
 Family: X = (column 0, rows 1..3, sum 0) (+) e_4 (x) Z, Z = {z in 1^perp : sum_{k>=1} a_k z_k = 0}, chart a_4 = 1 (3 parameters a1, a2, a3).
 Chart coverage [rigorous]: writing Z = (C1 + Cm)^perp, the chart a_4 = 1 with D := a1+a2+a3-4 != 0 covers exactly the m with m_4 not in {0, m_0}; since
 some k >= 1 always has m_k not in {0, m_0} (otherwise m = 0), S_4 on columns 1..4 brings every member into the chart with D != 0.
 T_1 (sympy over Q(a), r13_crossfam.py): dim 13; equations: rows 1,2,3 coincide in columns 1..4 (t_1j = t_2j = t_3j =: u_j), and t00, t01, t02, t03 are
 explicit affine combinations (denominator D) of t04, sigma = t10+t20+t30, u_j and s4 = sum_l t4l. Coordinates on T_1/X:
 (sigma, s4, ph4 = sum_k a_k t4k, u1..u4, t04).  Forms (r13_crossforms.py): P_2 and B_z (z = z^(1..3) basis of Z), rational with denominator D;
 ph4 enters only P_2 (it is in the kernel of all B_z).  Parametric chart run (r13_crosscharts.py: forms times D, a1,a2,a3 as msolve variables,
 all 70 charts of Gr(4,8), mod p, eliminating the chart variables on non-unit charts): running; first non-unit chart has a3 = 1, a1 + a2 = 3, i.e. D = 0
 (outside the valid chart). Rank-drop check of the T_1 system (r13_crossrank.py): running.
STATUS 23:02: cross-type ruling of F2col: explicit T_1 + forms done; parametric msolve chart run and rank check running.

## R13-2. F2col structure made explicit; the cross-type ruling nearly closed; generator for the full family
 RULINGS [rigorous]: S = sum-zero vectors of C^3 with <,>; R : S -> S with R e = f, R f = -3e (e = (1,-1,0), f = (1,1,-2)) is skew (<u,Ru> = 0).
 Lagrangians of (S x S, <p_0,p_1>): ruling 1 = graphs {(u, lam R u)} (lam in P^1; lam = 0, infinity: single-column planes = cross-type);
 ruling 2 = {span{(w,0),(0,v)} : <v,w> = 0} (two single-column elements = K33-type; the isotropic v gives w = v). Every ruling-2 member is K33-type
 (for <v,v> != 0, w^perp = Cv forces the second generator into Cv).
 CROSS-TYPE (ruling 1, lam = 0), parameters a in the chart a_4 = 1:
   rank-drop locus of the T_1 system (r13_crossrank.py, gcd of compressions): (a1+a2+a3+1)^2, i.e. only on Sigma_k a_k = 0 <=> m_0 = 0, where indeed
   dim T_1 = 15 (checked at a = (1/3, 2/7, -34/21)); elsewhere (D != 0) dim T_1 = 13 with the explicit coordinates of R13-1.
   Parametric msolve run with D saturated (Rabinowitsch w D = 1), mod p (r9/cross_sat_modp.log): 67/70 charts [1]; charts (2,3,4,7), (2,3,5,7),
   (2,4,5,7) crash msolve under the 2 GB cap (no verdict; Singular mod 536870909 running on (2,3,4,7)).
   Still to do for a proof: those 3 charts; the jump locus m_0 = 0 (2 parameters, dim T_1 = 15, Gr(4,10)); the p-denominator loophole (char 0).
 GENERATOR for all of F2col: stage2/r13_F2col.py RULING CH [fixed params] (T_1 over Q(params) by rref, 8 or 10 complement coordinates chosen
 automatically, forms P_2 and B_z, Rabinowitsch exclusion of denominators and of the complement determinant (SAT=1), msolve on all Grassmannian
 charts). Validated on a fixed ruling-2 member (70/70 [1]).
STATUS 23:18: cross-type ruling 67/70 charts unit (parametric, D saturated); 3 charts crash msolve at 2 GB; jump locus m_0 = 0 found.

## R13-3. ERRATUM / TOOL BUG: msolve 0.6.5 mis-reads integer coefficients >= p in mod-p mode
 Found while debugging a paradox (ruling-2 parametric run returned a mod-p solution with nu = 1/3 although the Rabinowitsch polynomial vanishes there).
 Minimal test (stage2 log): the system {3x - 1, -3c x w + c w - 1} is inconsistent for every c, yet msolve -g 2 mod 2147483629 returns a NON-unit GB
 whenever 3c >= p (c = 8e8, 1e9, 2147483647, ...), and [1] for 3c < p. In characteristic 0 msolve is correct (tested up to 6e10).
 Consequences and repair:
   - Every msolve input is now written with coefficients reduced mod p (helper msstr in r11_charts_msolve.py, r13_F2col.py, r13_crosscharts_sat.py).
   - The bug can produce FALSE non-unit verdicts (seen) and, in principle, false unit verdicts (corrupted coefficients make a system generic).
     All earlier mod-p chart kills are being RE-RUN with the patched tool (r9/rerun_patched.log): crossC1, K33, crossA, D003ptA/B, D04Pa (sg = 0, 2),
     S2s, and the D04-PROP parametric run. Verdicts in characteristic 0 (D04-PROP affine charts, the tau-chart eliminations) are unaffected.
   - The calibration D003A (agrees with Singular over QQ) passes with the patched tool; the B(dep) elimination inputs had no coefficient >= p
     (checked comp2; Singular dumps are integral and small).
   - The cross-type parametric run of R13-2 (67/70) is being redone (r9/cross_sat_modp_v2.log); the first R2 run is void.
 Request to verify2 / coordinator: any other team member using msolve mod p with large coefficients should reduce them mod p first.
STATUS 23:25: msolve mod-p coefficient bug found and patched; all mod-p kills being re-run.

## R13-4. Re-run of all mod-p chart kills with the patched tool (coefficients reduced mod p; stale outputs deleted; crashes reported as FAILED)
 r9/rerun_patched.log (p = 2147483629):  crossC1 70/70 [1];  K33 70/70;  crossA 70/70;  D003ptA 35/35;  D003ptB 35/35;  D04-PROP sg = 0 126/126;
 D04-PROP sg = 2 126/126;  (S2) sg = 2 210/210.  => every earlier fixed-data kill is CONFIRMED (the coordinator's audit found no coefficient >= p
 in the other teams' 4104 .ms files; recorded as E-MSOLVE-BIGCOEFF in COMPUTE-ERRATA.md).  D04-PROP parametric (sg affine + tau chart) re-run: running.
 Cross-type ruling, parametric (D saturated), patched (r9/cross_sat_modp_v2.log): 67/70 charts [1]; charts (2,3,4,7), (2,3,5,7), (2,4,5,7) FAIL (msolve
 allocation failure at the 2 GB cap) -- these are failures, NOT survivors. Retry with the rank-jump locus also saturated (r13_crosscharts_sat2.py) running;
 big-slot request queued (MSV = 6 GB).  Tools hardened: r11_charts_msolve.py and the new r13_F2col_v2.py (MSV cap, CHARTS list, FAILED counted
 separately) -- the coordinator's ST2-F2COL runs the earlier r13_F2col.py (already with msstr and the rank-jump exclusion).
STATUS 23:33: all fixed mod-p kills re-confirmed with patched tool; cross-type ruling 67/70 + 3 FAILED (memory); F2col R1/R2 running in the pool.
STATUS 23:38: RESULT-R13 written; final message follows. My D04-PROP parametric re-run continues (r9/rerun_patched.log).

# ROUND 14 (start 23:40 UTC, ~1-1.5 h). Targets: (1) collect ST2-F2COL / cross3_big verdicts; (2) close the char-0 / p-denominator gap for both
# parametric rulings; (3) target 2 (lambda = 5 lemma for planes on two rows; classification of planes with all 3x3 subpermanents vanishing);
# (4) target 3 (parametric D003-PROP Case A, full forms); also: think about a uniform "(Q-r) + FO2-joint => dead".
STATUS 23:41: round 14 started.

## R14-1. Collected verdicts
 D04-PROP parametric re-run with the patched tool (r9/rerun_patched.log): affine sigma-charts 126/126 [1], tau-charts 101/126 [1] + 25 non-unit (all at
 tau = 0 in char 0, R11-5) -> R11-4/5 CONFIRMED. ST2-F2COL (pool, r13_F2col_v2.py): R2 still in the sympy T_1 phase at 23:50; cross3_big not started yet.

## R14-2. Target 2: what the level conditions say about P = X_ri, and planes with all 3x3 subpermanents vanishing
 Reduction [rigorous]: for X = P (+) e_i (x) Z (P on the three rows a,b,c != r,i, Z = (C1+Cm)^perp) with C4 (all ten 3x3 subpermanents vanish on P):
   level of X  <=>  (L) column sums c(p) in Cm,  (Q0) P_2(p) = 0,  (Q) (P_2(p minus column j))_j in span(1, m)   for all p in P,
 since G_j(J''+p) = 24 + 6(C - c_j) + 2 P_2(p minus column j) (the cubic term vanishes by C4; each pair of cells avoiding column j is counted twice)
 and sum_j P_2(p minus column j) = 3 P_2(p); (ii) is implied by C4.
 C4 ALONE does not force a 2-column block (r14_perm3planes*.py, LM, exact residuals 1e-16): the generic C4-plane lives on 2 rows; with three nonzero rows
 there are C4-planes on 3, 4 and 5 columns. But with the LEVEL conditions added (r12_Pcensus.py variants on X = P + e_4 Z, Z fixed random): forcing three
 nonzero rows and >= 3 columns gives NO solution (10 starts, floors 0.47 - 1.4), while the unconstrained run finds 2-column solutions at once (8/8)
 [numerical evidence for "P lies in a 2-column block or has a zero row"].
## R14-3. Target 2, the two-row case: exact (Singular primary decomposition mod 536870909), in progress
 Two-row P = {(A, mu(A) m - A)} (A in a 2-dim space Acal; injectivity of A <- no single-row element of row b), conditions (E1) <A,B> = -sigma_A^2,
 (E2) -A o A + sigma_A A + mu(A) m o A in span(1,m) (polarised) -- all column-symmetric, so by S_5 only TWO chart types occur (m-pivot inside / outside
 the Acal pivots). Charts ((0,1),0), ((0,1),1), ((3,4),4) [pivot inside]: ONE component each: P = span{ e_a (x) m , (e_a - e_b) (x) e_k } with m_k = 0,
 i.e. P CONTAINS THE SINGLE-ROW ELEMENT e_a m^T -- excluded by verifyfl's SPLIT when <m,m> != 0 (R7-3(a)). Chart type "pivot outside": running.
STATUS 23:55: target 2: level reduction written; two-row case: pivot-inside charts force e_a m^T (SPLIT kills for non-isotropic m); other chart type running.
 UPDATE 00:05 (R14-3 continued): chart type "pivot outside" ((0,1), m_2 = 1): TWO components, symmetric under swapping the Acal pivots, each again
 P = span{ e_a (x) m , (e_a - e_b) (x) e_k } with m_k = 0 (here k = 0 resp. 1).  By S_5 on columns (the conditions are column-symmetric) the two chart
 types cover all 50 charts, so: EVERY two-row P satisfying the level conditions has this shape [mod 536870909 primary decomposition; char-0 run
 r14/tworow_c0_{A,B}.log in progress]. Consequences: for <m,m> != 0 it contains e_a m^T and is excluded by SPLIT; for ISOTROPIC m (not covered by SPLIT)
 the shape passes (FO-r) (Omega = C^5) and FO2 (13,8,9) but FO2-JOINT kills it:
   non-isotropic member m = (0,1,2,-1,-2): msolve 70/70 charts [1] (exact);  isotropic member m = (0,1,i,-1,-i) over Q(i): msolve mod p = 2147483629
   (p = 1 mod 4) with i -> both square roots of -1 (629208553 and p - 629208553): 70/70 [1] each (exact: both primes of Z[i] above p, Galois conjugates
   covered).  The isotropic two-row family has one projective parameter (m on the conic {m_0 = 0, sum m = 0, <m,m> = 0}); parametric run not done.
 SUMMARY target 2: z = 3 planes P = X_ri with a zero row -> the two-row shape (dead: SPLIT or FO2-joint at the member tested); with three nonzero rows ->
 numerically forced into a 2-column block (F2col). Missing for a proof: (a) the three-row case rigorously, (b) the isotropic two-row family parametrically.
STATUS 00:08: target 2: two-row case classified (mod p), killed by SPLIT / FO2-joint (exact at members incl. isotropic over Q(i)).
STATUS 00:08: RESULT-R14 written; final message follows. Char-0 decompositions r14/tworow_c0_{A,B} still running.

## R14-4. Faster exact linear algebra (r13_F2col_v3.py); target 3 parametric run started
 The 4-parameter sympy rref / rank-jump determinants of r13_F2col_v2.py do not finish (ST2-F2COL R2 stuck > 35 min in that phase). v3 replaces them by
 sympy DomainMatrix over QQ(params) / QQ[params]: on the slice R2 (nu free, a fixed) rref + rank-jump take seconds (rank-jump polynomial 1). Coordinator
 asked to restart ST2-F2COL on v3. Slice run r14/F2col_v3_R2_nu.log (bad loci nu in {0, -1, 1/3} excluded) in progress.
 TARGET 3 (D003-PROP Case A over P^2_alpha, FULL forms, stage2/r14_D3A.py): validated at X0 (alpha = (1,-1,0,0)): 70/70 [1]. Parametric (a2, a3), mod p:
 dim T_1 = 13; rank-jump polynomial (a2 - 1)^3 (a2 = 1 is outside the chart anyway); complement valid off (a2-1)^2 (a2+a3+1); 9 coefficient forms.
 Coverage: by S_4 on columns 1..4 every alpha (not proportional to 1) has a chart with alpha_1 = 1, a2 != 1, and alpha_4 != 0 unless alpha has two zero
 entries, i.e. alpha ~ (1,-1,0,0) = X0, which is dead exactly (R10). Charts running: r14/D3A_param_modp.log.
STATUS 00:21: v3 generator (fast); D3A parametric charts and R2-nu slice running.

## R14-5. Target 3 DONE mod p; F2col 1-parameter slices
 D003-PROP Case A over P^2_alpha (r14_D3A.py, FULL forms, parameters a2, a3 free, Rabinowitsch exclusion of a2 = 1, a2+a3+1 = 0 and the rank-jump
 polynomial): msolve mod 2147483629 (coefficients reduced): 70/70 charts [1], 0 FAILED (r14/D3A_param_modp.log).  With the S_4 coverage of R14-4 and the
 exact X0 kill this gives: NO member of the D003-PROP Case-A family lies in a 9-dim level space [mod-p projective-type argument as in R11-4: rigorous for
 all alpha integral at a prime above p; the p-denominator loophole is being closed by the same run in CHARACTERISTIC 0: r14/D3A_param_char0.log].
 F2col slices (r13_F2col_v3.py, Z fixed by a = (1/3, 2/5, -1/2)):
   ruling 2 (K33-type), nu free (bad loci nu in {0, -1, 1/3}): 70/70 charts [1], 0 FAILED (r14/F2col_v3_R2_nu.log);
   ruling 1, lam free (bad locus lam = 0 = cross-type, done separately): running; charts (0,2,5,6), (0,2,5,7) FAILED (memory) so far.
 The coordinator restarted ST2-F2COL on v3 at 00:18 (4-parameter rref done within minutes).
STATUS 00:31: target 3 mod p done (70/70); char-0 run going; R1 lambda slice running.
 UPDATE 00:40: D003-PROP Case A in CHARACTERISTIC 0 (r14/D3A_param_char0.log): 70/70 charts [1], 0 FAILED -> the p-denominator loophole is closed
 (msolve char 0 = multimodular, evidence-grade certificate as in R11-5). TARGET 3 CLOSED: FO2-joint excludes every member of the D003-PROP Case-A family.
 Ruling-1 slice (lam free, Z fixed): 68/70 [1], 2 FAILED (memory) -> queued (ST2-F2COL-slice-FAILED, 6 GB).
STATUS 00:40: target 3 closed (mod p + char 0); final message follows.

# ROUND 15 (start 00:42 UTC, ~1-1.5 h). Targets: (1) collect F2col v3 / big-slot verdicts, char-0 reruns, proof-grade route per family;
# (2) isotropic two-row family parametrically over Q(i) + char-0 two-row classification; (3) three-row C4 planes classification + level.
STATUS 00:42: round 15 started.

## R15-1. TWO DRIVER BUGS, audit and repair (E-STALE-OUTPUT found by the coordinator; E-MSSTR-RATIONAL found by me)
 (a) Stale output: r13_crosscharts{,_sat,_sat2}.py and r11_charts_msolve.py before 23:33 UTC never deleted wd/c.out; a crash on chart k could have shown
     chart k-1's [1]. Affected: the cross-type 67/70 runs, the big-slot 3-chart run (chart 2 unverifiable, being re-run by the coordinator), all r11
     fixed-data kills made before 23:33 (incl. my 23:24-23:40 re-runs). Observed crashes always left an EMPTY output (reported non-unit/FAILED), so no
     false unit is known -- but this is evidence only.
 (b) msstr (my msolve writer since 23:25) truncated NON-INTEGER rational coefficients (int(c) % p, Integer(c) in char 0). Audit: F2col v4 forms integral
     (0 rational polynomials on a member); cross-type forms integral; r11 fixed-data inputs integral by construction; r15_iso2row AFFECTED (Rabinowitsch
     polynomial t^2 - t - 1/2 etc.) -> its runs (incl. the chart (0,1,2,3) mod-p/char-0 contradiction) are VOID.
 Repair: *_fx.py copies of all drivers: per-polynomial denominator clearing (asserting p does not divide), output deleted before each call, output must exist
 and be newer than the input, otherwise FAILED; the RESULT line reports how many polynomials had rational coefficients.
 Re-verification of every verdict with the _fx drivers: r15/verify_all.log (running since 01:01); cross-type full re-run requested in the pool.
STATUS 01:03: two driver bugs audited; hardened *_fx drivers; full re-verification running (r15/verify_all.log).

## R15-2. F2col full rulings: the 4-parameter Gr(4,8) formulation does not fit (FAILED x4 at 2 GB); a K-REDUCTION lemma for the next formulation
 Observed on all generic F2col members (K33 family, cross-type with random Z; r12_forms_struct.py): on C = T_1/X (dim 8) q_0 = 12 P_2 is nondegenerate,
 the span of {B_z : z in Z} has generic rank 6 and common kernel K of dim 2.
 LEMMA (K-reduction) [rigorous under these rank conditions]: a 4-dim common isotropic L'' contains a nonzero k in K with q_0(k,k) = 0, and L''/Ck is a
 Lagrangian (3-dim) subspace of (k^perp_q0 / Ck, q_0) isotropic for all B_z. Proof: the image of L'' in C/K is isotropic for a nondegenerate form on a
 6-dim space, hence of dim <= 3, so L'' cap K != 0; such k is q_0-isotropic and lies in the kernel of every B_z.
 => k lies on <= 2 lines of K (unless q_0|K = 0), and the chart problem becomes Gr(3,6) (9 variables, 20 charts) instead of Gr(4,8) (16 variables).
 The degenerate loci (rank/kernel jumps of the B-span, q_0|K = 0) are explicit and must be treated separately. Implementation: next round.
 Isotropic two-row family (r15_iso2row.py): first runs VOID (E-MSSTR-RATIONAL); setup facts stand: dim T_1 = 13 generically, rank jumps exactly where a
 coordinate u_k of m vanishes (m = (0,0,1,w,w^2) up to S_4 and conjugation) -- that special member is killed EXACTLY (isoSpecA: 126/126 charts, Q(sqrt(-3))
 via i and sqrt(3) mod p; its conjugate is a column permutation). The generic family is to be re-run with r15_iso2row_fx.py.

## R15-3. Target 2, three-row case, with m free (r15_threerow.py): reduced conditions (L),(Q0),(Q),(C4) directly, m a variable
 Calibration (three nonzero rows, no column forcing): near-solutions at residual 3e-8, 9e-8 (slow convergence, as for the 2-column solutions);
 forced >= 3 columns: running (r15/threerow_3col.log).
STATUS 01:07: K-reduction lemma for F2col recorded; verification batch, two-row certificate, three-row census running.
 R15-3 update: forced >= 3 columns with m free (r15/threerow_3col.log, 8 starts): 7 starts end at residual exactly 1.00 (a row forced to zero, i.e. the
 solver lands on a two-row configuration violating one row normalisation), 1 start at 1.8e-8 that does not decrease further (refined 40000 steps,
 r15_threerow_v2.py): its X has level error 3.6e-7 and rows b,c supported in two columns with opposite signs in one -- a near-boundary configuration,
 not a solution. [numerical evidence for "three nonzero rows => P in a 2-column block"; no proof]
STATUS 01:13: three-row census (m free): no clean solution outside 2 columns; K-hypothesis exact check and two-row certificate running.

## R15-4. CORRECTION of R15-2 and a stronger result: on ruling R2 the common kernel of the B_z is 1-dimensional and CONSTANT -> generic R2 member killed by linear algebra
 Exact over Q(nu,a1,a2,a3) from the cached v4 setup (r16_Khyp.py, r16_Kfast.py; logs r15/Kfast_R2.log):
   rank q0 = 8 (det q0 = -55296 nu^2 (nu+1)^6 (3nu-1)^6 (a1+a2+a3-4)^4 * quartic); rank of the B-stack = 7 (NOT 6 as the numerics of R15-2 on
   a different cross-type sample suggested); rank B1+2B2+3B3 = 7; the common kernel is spanned by the CONSTANT vector k = e7 - e6 (complement coords);
   q0(k,k) = (nu+1)(3nu-1)(a1+2a2+2a3-6).
 LEMMA (kernel kill) [rigorous, pointwise]: at a parameter point pi with rank B_c(pi) = 7 for some c, every 4-dim L'' in C (dim 8) isotropic for q0 and
   all B_z contains k (the image of L'' in C/Ck is isotropic for the nondegenerate form induced by B_c on a 7-dim space, so has dim <= 3), hence
   q0(k,k)(pi) = 0. Equivalently Phi_c := tr(G0 adj B_c) = cof_77(B_c) * q0(k,k) must vanish (polynomial identity, since adj B_c = cof_77 k k^T).
 => R2 SURVIVORS lie in  {a1+2a2+2a3 = 6}  U  {cof_77(B_c) = 0 for the sampled c}  U  setup-exceptional loci
    {nu a1 = 0 (detX)} U {(nu+1)(3nu-1)(a1+a2+a3-4) = 0 (dens)} U {nu = infinity} U {Z chart a4 = 0} U {codim>=2 T_1 rank-jump points}.
 CAVEAT (found while doing this): the v4 rank-jump test is a gcd of 3 random compressions; it certifies only the HYPERSURFACE part of the T_1
   rank-drop locus (rkjump = constant on R2), codim>=2 rank-drop points are not excluded and need the exact minor/Fitting ideal.
 Consequence: the remaining R2 work is 3-parameter subfamilies, and on {a1+2a2+2a3 = 6} (where generically rank B_c = 7 still) the chart problem
   reduces to L'' = Ck + L3 with L3 in Gr(3,7) (35 charts, 12 variables, plus the linear conditions q0(k,L3) = 0): r16_F2col_K.py (next round).
STATUS 01:31: R2 kernel kill (exact): generic R2 member has no FO2-joint L''; survivors in explicit 3-parameter loci; cofactors running; R1 setup paused (core budget).

## R15-5. R2: the common rank-drop locus is exact, and the 3-parameter survivor hyperplane H is cheap in the reduced charts
 (a) Exact cofactors (r16_Kfast.py; r15/Kfast_R2.log, Kfast_R2_c3.log): for c = (1,2,3), (1,-1,2), (2,1,-1), (3,-2,1)
     cof_77(B_c) = 53747712 c1c2c3 nu^2 (nu+1)^5 (3nu-1)^5 D^5 (c.a)^2 (c.a - (c1+c2+c3)) (sum_z c_z (a_z^2 - a_z)),   D = a1+a2+a3-4
     (pattern read off the 4 exact factorisations, NOT proved for symbolic c; the proof below uses only the 4 exact ones). Individual B_z: rank 5.
     r16_cofint.py (Groebner over Q): the intersection over the 4 samples of the non-exceptional zero sets is EXACTLY {a in {0,1}^3} x (nu-line).
 => THEOREM-R2-GEN [rigorous, modulo the setup items listed in R15-4]: an R2 member with nu a1 (nu+1)(3nu-1) D != 0 (chart a4 = 1, nu finite, generic
    dim T_1) can carry a FO2-joint L'' only if  a1 + 2a2 + 2a3 = 6  (hyperplane H)  or  a in {(1,0,0),(1,0,1),(1,1,0),(1,1,1)}  (a1 = 0 is exceptional).
 (b) On H the reduction L'' = Ck + L3, L3 in Gr(3,7), is valid at every non-exceptional point (H contains no {0,1}^3 point: a1+2a2+2a3 <= 5 there).
     r16_F2col_K.py: fixed member (nu,a2,a3) = (1/2,1/3,2/5): 35/35 charts [1] mod p (RED-p kill of that member); negative calibration (q0 only):
     non-unit as it must be; the parametric 3-parameter H system: chart (0,1,2) [1] in 5 s, 54 MB -- full mod p and char-0 runs: r15/K_R2_H_*.log.
     msolve note: msolve needs ~1.5-2 GB of VIRTUAL address space even for tiny systems; with ulimit -v 1000000 it segfaults (FAILED, correctly caught).
 Remaining for a complete R2 (all <= 3 parameters, each again open to the kernel kill): the 4 lines a in {(1,0,0),(1,0,1),(1,1,0),(1,1,1)} (nu free;
 v4_fx with FIXPAR, 1 parameter, univariate rank-jump test exact); the exceptional 3-parameter families nu = 0, a1 = 0, nu = -1, nu = 1/3, D = 0
 (v4_fx SETUPONLY with FIXPAR, then r16_Kfast); nu = infinity ~ nu = 0 by the column swap 0<->1 (with Z re-charted); the Z chart a4 = 0 (S_3 on
 columns 2,3,4 and the swap cover it except n = (0,1,0,0,0) mod 1); the exact T_1 rank-drop ideal (codim >= 2).
STATUS 01:43: R2 reduced to H + 4 lines + exceptional 3-param families; H charts running (mod p, char 0); R1 setup paused while H runs.
STATUS 01:56: RESULT-R15 written; H run in pool queue (ST2-R2H), lines queued (ST2-R2LINES); R1 setup to resume.

## R15-6. Jump locus of R1 (lam = 0, a3 = -1-a1-a2; nq = 10): a second kernel lemma (the coordinator's Gr(4,10) pool run FAILED all charts)
 Exact (r16_Kranks.py, r16_Kjump.py): rank q0 = 10, rank B_z = 7 (ker B_z = W_z, dim 3), rank of any pair stack 8, B-stack 9; the common kernel is the
 CONSTANT k0 = e9 - e8; q0(k0,k0) = a1 + 8; on W_z the other two B_w have rank 1 (B_w|W_z = l_w^2), with l_w, l_w' independent over Q(a1,a2).
 LEMMA [rigorous, pointwise]: a 4-dim common isotropic L'' meets W_z (dim L'' cap W_z >= 4 - floor(7/2) = 1); a k in L'' cap W_z has
   B_w(k,k) = l_w(k)^2 = 0 for both w != z, so k in W_z cap {l_w = l_w' = 0} = C k0 (when independent), hence q0(k0,k0) = a1 + 8 = 0.
 => jump-locus survivors lie in {a1 = -8} (a 1-parameter curve, then L'' = C k0 + L3, L3 in Gr(3,9), 84 charts) U Deg U {a1 = 0 (detX)}, where Deg is
    the set where the lemma fails for ALL three z (rank B_z < 7, or the basis of W_z degenerates, or l_w, l_w' dependent): r16_Kjump_deg.py computes it
    exactly (Groebner over Q; expected finitely many points -> fixed-member kills).  rank B_z < 7 gcd parts: a_z in {0, 1, -6/5} (a3 = -1-a1-a2).
 Tests (r16_F2col_K.py, reduced charts): 2-parameter system chart (0,1,2) [1], chart (3,5,7) FAILED at 2 GB; with a1 = -8 substituted: r15 test running.
STATUS 02:10: round 15 closed; queued ST2-R2H (running), ST2-R2LINES, ST2-JUMPK, ST2-R1SETUP, ST2-TWOROW-CERT.
STATUS 02:12: round 16 started (targets: R2 exceptional families + Z-chart a4=0 by kernel kill; jump-locus Deg + Gr(3,8); T_1 codim>=2 rank drop; R1 kernel analysis; char 0).

## R16-1. R2 exceptional families by the kernel kill (r16_F2col_setup.py = v4_fx setup with fixed nu / nu = infinity / explicit Z basis, cache in r16/;
##        r16_Kauto.py = ranks, k, q0(k,k), cofactors for 4 sampled c, exact Groebner common rank-drop locus; batch r16/fam_batch.sh)
 nu = 0 (P = span{(f,0),(0,e)}; r16/Kauto_R2_nu0.log): T_1 dim 13; rank-jump hypersurface a1+a2+a3+1 = 0 (NEW: inside nu = 0 the T_1 dimension
   jumps -- a codim-2 jump of the 4-parameter family, invisible to the 4-parameter gcd test); complement det 2 a1; denominators D = a1+a2+a3-4.
   Same structure as generic R2: rank q0 = 8, B_z rank 5, B-stack 7, k = e7 - e6 constant, q0(k,k) = a1+2a2+2a3-6, cofactors identical up to the
   constant, common rank-drop locus {0,1}^3.  Survivors: H cap {nu=0} (2 params), the 4 points a in {(1,0,0),(1,0,1),(1,1,0),(1,1,1)}, and the
   sub-families a1 = 0, D = 0, a1+a2+a3 = -1 (all inside nu = 0).
 a1 = 0 (nu, a2, a3; r16/fam_batch1.log): T_1 dim 13, rank-jump (a2+a3+1)^2, detX 4 a2 nu, dens (nu+1)(3nu-1)(a2+a3-4). B_1 rank 2 (!), B_2, B_3 rank 5,
   B-stack 7, k = e7 - e6, q0(k,k) = (nu+1)(3nu-1)(a2+2a3-6). Common rank-drop locus (non-exceptional): (a2,a3) in {(1,0),(1,1)} (nu free).
   Survivors: {a2+2a3 = 6} (2 params), lines (a2,a3) = (1,0), (1,1), sub-families nu in {0,-1,1/3}, a2 = 0, a2+a3 = 4, a2+a3 = -1.
 nu = -1: rank-jump a1+a2+a3+1; detX 4a1; dens D. Same structure; q0(k,k) = 2(a1+2a2+2a3-6); rank-drop locus inside {0,1}^3.
 nu = 1/3: rank-jump 4a1-a2-a3-1 (new); detX -4a1/3; dens D. Same structure; q0(k,k) = 2(a1+2a2+2a3-6); rank-drop locus {0,1}^3.
 PATTERN so far: on every exceptional family the kernel kill applies verbatim (constant k = e7 - e6), the survivors are always the analogue of H
   plus 0/1 points, and the only genuinely new phenomena are T_1 rank-jump hypersurfaces (a1+a2+a3 = -1 at nu in {0,-1}; 4a1 = a2+a3+1 at nu = 1/3;
   a2+a3 = -1 at a1 = 0), which the 4-parameter gcd test could not see (codim 2).
 D = 0 (a1 = 4-a2-a3): rank-jump const; detX 4 nu (a2+a3-4); dens (a3-1)(nu+1)(3nu-1). B_z ranks 4,4,5; B-stack 7; k = e7 - e6;
   q0(k,k) = -(nu+1)(3nu-1)(a2-7a3+6); common rank-drop locus: the single line (a2,a3) = (-4,4) (a1 = 4). Survivors: {a2 = 7a3-6}, that line, subfamilies.
 nu = 0 & a1 = 0: same structure, survivors {a2+2a3 = 6}, points (a2,a3) in {(1,0),(1,1)}; nu = 0 & D = 0: survivors {a2 = 7a3-6}, point (-4,4).
 nu = 0 & a1+a2+a3 = -1 (the T_1 JUMP family, dim T_1 = 14, nq = 9): B_z rank 6, B-stack 8, common kernel k = e8 - e7 (constant), q0(k,k) = 7-a2-a3;
   on each W_z = ker B_z (dim 3) the other two B_w are rank-1 squares with independent linear forms => JUMP-TYPE LEMMA (as R15-6): k in L'',
   survivors only on a2+a3 = 7 (+ its Deg + exceptional a2+a3 = -1, which is empty here). r16_Kauto.py now applies this lemma automatically.
 D04Pasym mod-p plain re-run (hardened driver, no head): affine charts 126/126 [1]; tau-charts 25 non-units -- as in R11-4/5, where the char-0
   elimination put all tau-chart solutions at tau = 0 (sigma = infinity, outside the family). Verdict unchanged.
 AUTOMATION: r16_tree.py = BFS over linear exceptional factors (setup + r16_Kauto per family, dedup by rref of the constraints, state in
   r16/tree_R2.json); running at depth 2 from the roots nu, a1, nu+1, 3nu-1, D (r16/tree_R2.log).
STATUS 02:27: R2 exceptional families: kernel kill applies on all 5 + 3 sub-families; tree running; jump locus K2 (Gr(3,8)) on a1=-8 running.

## R16-2. Generic ruling R1 (P_lam = span{(e, lam f), (f, -3 lam e)}): the SAME kernel kill (setup cached by ST2-R1SETUP; r16/Kauto_R1.log)
 T_1 dim 13 (nq = 8), rank-jump gcd constant, detX 4 a1 lam, dens 2 lam D. rank q0 = 8; B_z ranks 5, 6, 6; B-stack 7; B_(1,2,3) rank 7;
 k = e7 - e6 (constant); q0(k,k) = 2 lam (a1 + 2a2 + 2a3 - 6)   -- the SAME hyperplane H as for R2.
 Cofactors: one linear factor (c.a) plus a large quartic (in lam, a) per sample c; the exact common rank-drop locus is being computed.
 => generic R1 member survives only on H (lam, a2, a3 free: K2 run, 3 parameters), on the common rank-drop locus, and on lam = 0 (cross-type,
    treated separately: 67/70 + 2 big-slot [1] + 1 pending), a1 = 0, D = 0.

## R16-3. Codimension >= 2 rank drops of T_1 (target 3)
 Fact: they EXIST -- e.g. {nu = 0, a1+a2+a3 = -1} in R2 has dim T_1 = 14 although the 4-parameter gcd test is constant; likewise {nu = -1,
   a1+a2+a3 = -1}, {nu = 1/3, 4a1 = a2+a3+1}, {a1 = 0, a2+a3 = -1}. All found so far lie INSIDE a setup-exceptional hypersurface of the parent, whose own
   setup recomputes T_1 exactly and sees the jump as a hypersurface of the child (then the jump-type lemma applies, e.g. survivors a2+a3 = 7).
 What covers the rest [method, rigorous]: r16_T1cert.py. Lower semicontinuity gives rank Am(pi) <= r; and rank Am(pi) = r as soon as the r generic pivot
   columns Am[:,piv](pi) are independent. So the full rank-drop locus (any codimension) lies in the projection of {(pi, x) : Am[:,piv](pi) x = 0,
   x in P^(r-1)}. Charts x_j = 1, x_l = 0 (l < j) (a disjoint cover), plus a Rabinowitsch variable for the family's exceptional hypersurfaces (rref
   denominators, forms' denominators, detX, the gcd polynomial). All charts [1] => T_1 has generic dimension at every non-exceptional point of the
   family. Mod p is evidence (the parameters are affine); Singular std over QQ (ENGINE=sing) is the proof. Run per family of the tree.

## R16-4. R2 survivor hyperplane H (pool ST2-R2H, r15/H_R2.log): mod p 33/35 [1] + FAILED 1-2-3, 1-2-4 (2 GB); msolve CHAR 0: 35/35 [1], 0 FAILED
 => H = {a1+2a2+2a3 = 6} (3 parameters, kernel-reduced charts) carries no FO2-joint L'' [char 0, msolve multimodular = evidence-grade];
    Singular std over QQ (proof grade) running in the pool. Together with THEOREM-R2-GEN: the generic R2 member and H are done.
 Jump locus with elimination (r16_F2col_K2.py, Gr(3,8), a1 = -8): mod p chart (1,4,5) FAILED at 2 GB as well -> the elimination alone does not
   rescue the heavy charts; char 0 msolve (which passed the H charts that FAILED mod p) is the next try.
STATUS 02:46: H char0 35/35 [1]; R1 generic kernel kill (same H); exact R1 rank-drop locus queued (ST2-R1COF); tree running.

## R16-5. SYMMETRY CUT (new idea): S_3 on columns 2,3,4 shrinks the R2 survivor set to finitely many nu-lines (r16_symcut*.py)
 FO2-joint survival is invariant under permuting columns 2,3,4 (P lives in columns 0,1; nu is fixed), which permutes (a2,a3,a4) of the Z-normal
 n = (a1,a2,a3,a4) (column-0 entry normalised to 0). The kernel kill gives, at every point sigma(n) in the chart a4 = 1 with nu generic,
 sigma(n) in X := H u A u D u Pts  (H: a1+2a2+2a3 = 6a4, A: a1 = 0, D: a1+a2+a3 = 4a4, Pts: the four 0/1 points). Hence a survivor with a2a3a4 != 0
 lies in  INTERSECTION_{sigma in S_3} sigma^{-1}(X)  -- exact linear algebra over Q:
   region a2 a3 a4 != 0:   A  u  {a = (1,1,1)}  u  {a = (2,1,1)}      (H itself is NOT needed: only its S_3-stable point (2,1,1), which lies on D);
   slice a2 = 0 (any zero moved to position 2 by S_3; residual swap of columns 3,4), a3 a4 != 0: finitely many points
     (a1:a3:a4) in {(1:1:1), (3:1:1), (4:1:1), (22:6:7), (22:7:6)} (+ A);   a2 = a3 = 0: a1 in {1, 4, 6} (+ A);
   inside A (a1 = 0; its own analysis: H_A, a2 = 0, a2+a3 = 4a4, the T_1-jump plane a2+a3+a4 = 0, points): finitely many points PLUS the whole
     S_3-invariant jump family J_A = {a1 = 0, a2+a3+a4 = 0} (2 parameters, dim T_1 = 14; jump-type lemma expected).
 Validity: for generic nu (nu not in {0,-1,1/3,infinity}), MODULO the T_1 generic-dimension certificate of the generic family (R16-3), since the
 kernel kill at sigma(n) needs the generic T_1. The nu-exceptional slices have the same S_3 symmetry (nu fixed) and the same cut applies;
 nu = -1 <-> nu = 1/3 and nu = 0 <-> nu = infinity under the column swap 0 <-> 1.
 => R2 is reduced to: ~10 one-parameter nu-lines (full Gr(4,8) charts, 1 parameter -- the size that always fit), the family J_A, the slices
    nu in {0,-1,1/3} (same cut), the special Z n = (1,0,0,0), and T1cert. The 3-parameter H runs become a cross-check (char 0 already 35/35 [1]).
STATUS 02:55: symmetry cut found: R2 survivors -> finitely many nu-lines + J_A (+ nu-slices); tree + jump K2 running.

## R16-6. T1cert on generic R2 (r16/T1cert_R2_modp.log; mod p, evidence): 10/12 charts [1]; 2 non-unit charts, parameter loci (char 32003, minAssGTZ):
   {nu = 1, a1+a2+a3 = -1}   and   {nu = -1/3, 4a1 = a2+a3+1}   -- codim-2 T_1 jumps OUTSIDE the excluded hypersurfaces (exactly the missing pieces).
 Explanation (symmetry): permutations of rows 1..3 act on the R2 parameter nu (the column-0 vector f - 3 nu e in 1^perp of C^3), and the column swap
   0 <-> 1 acts by nu -> -1/(3nu). The special values {0, -1, 1} (column-0 vector proportional to 3e_r - 1) form one row-orbit, {1/3, -1/3, infinity}
   another, and the swap exchanges them. So ALL six special slices are isomorphic to nu = 0 (with Z unchanged under row permutations): the jump plane
   a1+a2+a3 = -1 seen at nu in {0,-1} reappears at nu = 1, and its swap image 4a1 = a2+a3+1 at nu in {1/3,-1/3}. Check: setups nu = 1, nu = -1/3 running
   (r16/fam_batch2.log). Consequence: only the slice nu = 0 (with its sub-families) needs analysis; the other five follow by symmetry.

## R16-7. JUMP LOCUS (R1, lam = 0, a1+a2+a3 = -1) essentially CLOSED without the heavy charts: Deg = EMPTY + S_4 symmetry
 r16_Kjump_deg.py (r16/jump_Deg.log, exact Groebner over Q): the lemma of R15-6 fails via z only on (a) rank B_z < 7: a_z in {0, 1, -6/5}
   (for z = 3: a1+a2 in {-1,-2,1/5}); (b) basis degeneration: never ([1]); (c) l_w dependence: never ([1]). Intersection over z: EMPTY.
 => [rigorous, pointwise] jump-locus survivors lie in {a1 = -8} u {a1 = 0}.
 SYMMETRY: the cross-type family (P in column 0) is invariant under S_4 on columns 1..4, which permutes (a1,a2,a3,a4); the jump plane
   a1+a2+a3+a4 = 0 is S_4-invariant. A survivor with all a_k != 0 would satisfy a_i = -8 a_j for all i != j: impossible. So survivors have some a_k = 0;
   by S_4 move it to a1 = 0: the sub-family {lam = 0, a1 = 0, a3 = -1-a2} (dim T_1 = 15, nq = 10; B_2, B_3 rank 7 with the jump-type structure,
   k = e9 - e8, q0(k,k) = a2 + 8) -> survivors only at a2 = -8 (+ a2 = 0 + its Deg): FINITELY MANY POINTS, e.g. a = (0,-8,7) up to S_4.
 => the Gr(4,10) charts that FAILED at 2 GB (pool run, and K/K2 versions 3-5-7, 1-4-5, 1-5-6) are NOT needed; remaining: fixed members.
 The same S_4/S_3 cut applies to the whole cross-type ruling (pending chart 2-3-5-7 in the big slot becomes a cross-check).
STATUS 03:01: jump locus reduced to finitely many points (Deg empty + S_4 cut); writing the round report.
STATUS 03:01: round 16 closed; RESULT-R16 written.
STATUS 03:04: round 17 started (T1cert Singular-QQ; symmetry cuts in nu=0, J0, J_A, jump points; Deg of jump families; special Z; R1 tree; F2col table).

## R17-1. T1cert in Singular std over QQ (PROOF GRADE) -- T_1 has generic dimension off the exceptional hypersurfaces, any codimension
 generic R2 (excluded: nu, nu+1, 3nu-1, a1, D, and nu-1, 3nu+1 = the row/swap-symmetry images of the nu = 0, 1/3 slices): 12/12 charts [1]
   (r17/T1cert_R2_sing.log; mod p also 12/12);  all 18 tree families (r17/t1cert_tree.log): every chart [1] (10-12 charts each);
   R1 jump plane {lam = 0, a1+a2+a3 = -1} (excluded a1): 10/10 [1].  r17/rden_check.py: in every family the rref denominators are products of the
   family's exceptional factors (nothing extra was excluded).  1-parameter families: the univariate gcd test is exact.

## R17-2. The JUMP LOCUS is CLOSED
 Generic jump plane: jump-type lemma + Deg = EMPTY (R16-7) -> survivors in {a1 = -8} u {a1 = 0};  S_4 cut (r17_symcut.py 'jump'): NO component
   in the region (all a_k != 0).  Boundary (some a_k = 0, moved to a1 by S_4): sub-family {lam=0, a1=0, a3=-1-a2}: Deg = EMPTY (r17_Kjump_deg.py),
   survivors a2 = -8 and a2 = 0 (detX):
     a = (0,-8,7): reduced charts Gr(3,8), fixed data: 56/56 [1] mod p  (RED-p kill);
     a = (0,0,-1): jump-type lemma at the point (z = 3 usable, q0(k,k) = 7 != 0): KILLED exactly.
   Other zero patterns are S_4-images; T_1 genericity: jump plane by Singular T1cert, the 1-parameter sub-family by the exact univariate gcd test.

## R17-3. Special Z n = (1,0,0,0) (Z = {z1 = 0}) is CLOSED: a third lemma ("big kernel")
 Here the B-stack has rank 5, common kernel K of dim 3 = ker B_c. A 4-dim L'' meets ker B_c in dim >= 4 - floor(5/2) = 2; a 2-dim q0-isotropic subspace
 of K needs q0|K degenerate. det q0|K = 5376 nu^2 (nu+1)^3 (3nu-1)^3 (polynomial basis, never degenerate); rank B_c < 5 only at nu in {-1, 1/3}
 (exact, one variable). => killed for nu not in {0,-1,1/3}; nu = infinity (R2inf): det q0|K = 112/3 != 0, killed exactly; nu = 0: full Gr(4,8)
 charts, fixed data, 70/70 [1] mod p (r17_charts.py; RED-p kill); nu = -1, 1/3 are row-symmetry images of nu = 0, infinity (Z unchanged).

## R17-4. Symmetry cuts inside the invariant families (r17_symcut.py)
 nu = 0 slice (pieces H, A, D, J0 = {a1+a2+a3+a4 = 0}, 0/1 points; S_3): region survivors in A u J0 u {(1,1,1), (2,1,1)} (all other in-region
   components lie inside A or J0).
 J0 (nu = 0 jump family; Deg = EMPTY, r17/jumpdeg_all.log): pieces {a2+a3 = 7a4}, A -> region survivors only in A cap J0.
 J_A = {a1 = 0, a2+a3+a4 = 0}: Deg lies inside nu in {0,-1,1/3} (handled by the slices); pieces {a3 = 7a4} -> NO region survivor.
STATUS 03:13: T1cert Singular-QQ: generic R2 + 18 families + jump plane all [1]; jump locus and special Z closed; cuts inside nu=0, J0, J_A done.

## F2COL-TABLE (for verify2, R17): what is proved where.  Grades: [E] exact symbolic (sympy over Q(params) / Groebner over Q);
##   [S] Singular std over QQ (proof); [RED-p] msolve mod p on FIXED rational data, all charts (proof, p not dividing denominators);
##   [M0] msolve char 0 multimodular (evidence); [Mp] msolve mod p with free parameters (evidence).  "lemma" = pointwise linear algebra, rigorous.
 F2col: X = P (+) e_4 (x) Z, P Lagrangian in a 2-column block (columns 0,1; rows 1..3), Z in Gr(3,4); rulings R1 (lam in P^1), R2 (nu in P^1) [R13-2].
 Symmetries used: S_3 on columns 2,3,4 (S_4 on columns 1..4 when P is in column 0); row-S_3 (rows 1..3) acting on nu / lam; column swap 0<->1
 (nu -> -1/(3nu), lam -> -1/(3lam)).  Coverage of Z: chart a4 = 1 + S_3 (+ swap) covers all Z except n = (1,0,0,0).
 piece                                   | method                                                        | grade
 ----------------------------------------|---------------------------------------------------------------|---------------------------------
 R2 generic nu (chart a4=1)              | kernel kill: k = e7-e6, q0(k,k), cofactors, Groebner (R15-4/5)| [E] + lemma
   T_1 generic dim off exceptional       | T1cert, 12 charts (R17-1)                                     | [S]
   survivors -> finitely many nu-lines   | S_3 symmetry cut (R16-5)                                      | [E]
   the nu-lines (13)                     | ST2-R2LINES (4) + ST2-R2SYMLINES (9), Gr(4,8), 1 parameter     | [Mp] pending (char 0 next)
   H (3 params; now only a cross-check)  | reduced charts Gr(3,7)                                        | [M0] 35/35, [Mp] 33/35; [S] running
 R2 exceptional families (18, tree)      | kernel kill / jump-type lemma per family (R16-1)              | [E] + lemma
   their T_1                             | T1cert per family (R17-1)                                     | [S] all charts [1]
 R2 nu-slices {0,-1,1,1/3,-1/3,inf}      | one orbit under row-S_3 x swap; nu = 0 analysed               | lemma (symmetry)
   nu = 0 slice                          | S_3 cut -> A u J0 u 2 points (R17-4)                           | [E]
   nu = 0 fixed members (12)             | kernel/jump lemma at the point (5), full charts 70/70 (7)      | lemma / [RED-p]
   J0, J_A (jump families)               | jump-type lemma, Deg = EMPTY / special nu only, S_3 cut        | [E] + lemma
 R2 a1 = 0 family (A), generic nu        | kernel kill + S_3 cut -> points (in ST2-R2SYMLINES) + J_A      | [E]
 R2 special Z n = (1,0,0,0)              | big-kernel lemma (det q0|K) + nu = 0 charts 70/70 (R17-3)      | lemma + [E] + [RED-p]
 R1 generic lam                          | same kernel kill, same H (R16-2)                              | [E] + lemma
   R1 rank-drop locus                    | exact interpolation (ST2-R1COF)                               | [E] in progress
   R1 tree, T1cert, symmetry cut         | running / next                                                | --
 R1 lam = 0, inf (cross-type)            | parametric Gr(4,8) charts: 67/70 + 2 big-slot [1], 1 pending   | [Mp] (no char-0 / proof yet)
   cross-type jump plane                 | jump-type lemma, Deg = EMPTY, S_4 cut, 2 points (R17-2)        | [E] + lemma + [RED-p]; T_1 [S]
 Open for a complete proof: the 13 R2 nu-lines (and their char-0 / proof grade), R1 (tree + cut + RD), the cross-type ruling in proof grade,
 boundary slices (zero coordinates) inside the nu = 0 / A cuts (finite point lists), and the fixed members' RED-p primes recorded per run.
STATUS 03:22: F2col table written; nu=0 fixed members 12/12 killed; R1 interpolation finishing; R1 tree running.

## R17-5. The CROSS-TYPE ruling (R1 lam = 0, inf) is now PROVABLE without the pending chart: kernel kill + S_4 cut + T1cert + 5 fixed members
 Setup r16_F2col_setup.py R1 lam=0 (P = span{(e,0),(f,0)}, column 0; r17/cross_batch.log): T_1 dim 13, detX -2a1, dens D, rank-jump (a1+a2+a3+1)^2
   (= the jump plane J). Standard kernel structure: rank q0 = 8, B_z rank 5, B-stack 7, k = e7 - e6, q0(k,k) = a1+2a2+2a3-6, common rank-drop {0,1}^3.
   (The R15-2 numerics "B-span rank 6, kernel 2" were for another sample; exact data supersede them.)
 T1cert, Singular QQ: lam = 0 family 12/12 [1] (excluded A, D, J); sub-family a1 = 0: 12/12 [1].
 S_4 cut (S_4 on columns 1..4 permutes all of n = (a1,a2,a3,a4); chart a4 = 1 + S_4 covers EVERY Z): region survivors (all n_k != 0) lie in
   J u {n = (1,1,1,1)}  (every other in-region component has coordinate sum 0, i.e. lies in J).  J is closed (R17-2).
 Boundary (some n_k = 0 -> a1 = 0 by S_4): sub-family {a1 = 0}: kernel kill (q0(k,k) = a2+2a3-6, rank-drop (a2,a3) in {(1,0),(1,1)}, exceptional a2 = 0,
   a2+a3 = 4, a2+a3 = -1) + residual S_3 cut (identical to r16_symcut3) -> J u {n = (0,1,1,1)};  second zero {a1 = a2 = 0} (1 parameter; univariate
   gcd exact): survivors a3 in {6, 1} u exceptional {4, 0, -1}; the residual swap (columns 3,4) kills a3 = 6, 4 (their images 1/6, 1/4 are not
   survivors) -> n = (0,0,1,1), (0,0,0,1), (0,0,-1,1) in J.
 Fixed members, full Gr(4,8) charts, fixed data, mod p (RED-p): a = (1,1,1), (0,1,1), (0,0,0), (0,0,1): 70/70 [1] each (r17/cross_points.log).
 lam = infinity is the column-swap image of lam = 0.  => cross-type ruling: rigorous modulo verify2's check of these steps.
STATUS 03:31: cross-type ruling closed by kernel kill + S_4 cut + T1cert + 4 RED-p members; R1 tree stopped (sympy Groebner too slow on quartic cofactors, wait for R1COF).

## R17-6. PROOF GRADE for the R2 nu-lines is cheap: Singular std over QQ on every chart (r17_charts.py ENGINE=sing)
 On a line (a fixed, nu free) the T_1 setup is exact (univariate rank-jump gcd = exact jump test) and a Gr(4,8) chart with nu and the Rabinowitsch
 variable takes ~5 s in Singular over QQ (test: 2 charts of a = (1,1,1) in 9.8 s, 49 MB). So all cut lines get [S] directly, which makes the queued
 mod-p jobs ST2-R2LINES / ST2-R2SYMLINES cross-checks. Running in my slot: r17/lines_sing_{A,B}.log (8 lines); the other 7 lines next.
 Line list after the cuts (S_3 orbit representatives; (1,1,0) ~ (1,0,1) dropped): (1,0,0), (1,0,1), (1,1,1), (2,1,1), (3,0,1), (4,0,1), (4,0,0),
 (6,0,0), (22/7,0,6/7), (11/3,0,7/6), (0,1,1), (0,1/7,-8/7), (0,0,1), (0,0,0), (0,0,-1).
 Excluded points on the lines: nu in {0,-1,1/3} (slices; nu = 0 members run in R17-4/nu0_points: 12 done, (0,0,1), (0,0,0), (0,0,-1) next).

## R17-7. R1 status
 Generic R1: kernel kill [E] (R16-2) and T1cert Singular QQ 12/12 [1] (excluded lam, a1, D only -- no extra special lam needed).
 The exact rank-drop locus RD: ST2-R1COF finished its 36 lattice determinants but has been stuck > 30 min in sympy post-processing (it also factors the
   full P(c), which is not needed). Lean replacement r17_cofinterp2.py (caches the determinants, divides out lam^m D^n first, no factoring, writes a
   Singular minAssGTZ script) queued as ST2-R1COF2. The R1 tree was stopped (its Kauto calls hit the same sympy Groebner bottleneck on the quartic
   cofactor factors); R1 will go: exact RD -> S_3 cut (pieces H, A, D, RD_lam) -> lines/points -> Singular charts, as for R2.
STATUS 03:47: Singular line runs (8 lines, per-chart 60 s timeout with msolve char-0 fallback) in progress; R1COF slow, lean backup queued.
 R17-6 CORRECTION: the 5 s Singular charts were the easy ones; on the lines a = (1,0,0) and (3,0,1) most charts of the form (0,1,*,6|7), (0,2,3,6) etc.
   exceed 60 s in Singular std over QQ (r17/lines_sing_{A,B}.log). Proof grade for the lines therefore needs another route (next round): (i) a
   kernel-lemma variant on the lines (the lines are rank-drop points: B-stack rank < 7, common kernel of dim >= 2 -> L'' meets it -> reduced charts),
   or (ii) RED-p on a proper family (nu homogenised; needs dens-free forms on the line). Meanwhile msolve CHAR 0 is fast on the lines (the 2 charts
   0-3-5-7, 0-4-5-7 of a = (1,0,0) that FAILED mod p in the pool: both [1] in char 0 in 1.7 s): all 15 lines in char 0 running (r17/lines_c0_{A,B}.log).

## R17-8. R2 lines and remaining nu = 0 pieces (r17/lines_c0_{A,B}.log, r17/nu0_points2.sh output, J0 cap A)
 The 15 cut nu-lines (nu free, nu in {0,-1,1/3} excluded): 13 lines msolve CHAR 0 70/70 [1] each [M0]: (1,0,0), (1,0,1), (1,1,1), (2,1,1), (3,0,1),
   (4,0,1), (4,0,0), (6,0,0), (22/7,0,6/7), (11/3,0,7/6), (0,1,1), (0,0,1), (0,0,0); the 2 lines inside J_A are killed by the JUMP-TYPE lemma
   [E + lemma]: (0,1/7,-8/7) (J_A survivors only a3 = 7), (0,0,-1) (q0(k,k) = 7(nu+1)(3nu-1), Deg inside nu in {0,-1,1/3}).
   Pool (mod p, cross-check): ST2-R2LINES 4/4 lines 70/70 (2 FAILED charts on (1,0,0), both [1] in char 0); ST2-R2SYMLINES running ((2,1,1) 70/70).
 nu = 0 fixed members: 15/15 killed ((0,0,1), (0,0,0): 70/70 RED-p; (0,0,-1): jump-type lemma).  J0 cap A at nu = 0 (1 parameter): jump-type
   lemma, Deg EMPTY -> survivors a3 = 7 (point (0,-8,7), removed by the S_3 cut: its image (0,-1/8,-7/8) is not a survivor) and a3 = -1 (done).
 => R2 is reduced to: proof grade for 13 lines (now [M0]) + verify2's check of the cut/lemma chain. Every other R2 piece is [E]/lemma/[S]/[RED-p].

## F2COL-TABLE update (R17, 04:10): rows changed
 R2 nu-lines (15)                        | 13 x msolve char 0 70/70; 2 x jump-type lemma                 | [M0] / lemma  (proof grade: next)
 R2 nu = 0 slice: all fixed members (15)  | lemma (6) / full charts 70/70 (9)                              | lemma / [RED-p]
 R2 J0, J_A, J0 cap A                    | jump-type lemma, Deg exact, S_3 cut                           | [E] + lemma
 R2 special Z                            | big-kernel lemma + RED-p                                       | CLOSED
 R1 cross-type ruling (lam = 0, inf)     | kernel kill + S_4 cut + T1cert + 4 RED-p members + J           | CLOSED (was [Mp])
 R1 jump plane                           | Deg empty + S_4 cut + 2 points                                 | CLOSED
 R1 generic lam                          | kernel kill [E] + T1cert [S]; exact RD pending (ST2-R1COF/2)   | open: RD, cut, lines
STATUS 04:07: round 17 closed: T1cert [S] everywhere; cross-type, jump locus, special Z closed; R2 down to 13 lines at [M0]; R1 waits for RD.
STATUS 04:08: round 18 started (proof grade for 13 R2 lines via kernel-lemma variants; R1 after R1COF2; branch-3 items; table).

## R18-1. Proof grade for the 13 R2 nu-lines: GENERAL KERNEL BOUND + reduced charts in Singular over QQ (r18_linerank.py, r18_lineexc.py)
 General bound [rigorous, pointwise]: if B_c has rank r and ker B_c = K (common kernel, dim kap), a 4-dim common isotropic L'' meets K in dimension
   >= m := 4 - floor(r/2), and L'' cap K is q0-isotropic, so m <= (kap - rho) + floor(rho/2), rho = rank q0|K. (Standard kill: kap = 1; big-kernel: kap = 3.)
 Exact data on the 13 lines (nu free); exceptional nu (rank drop of B_c, kernel-basis degeneration, det q0|K = 0, setup) are ONLY nu in {0,-1,1/3}
   (the slices), plus nu = -1/2 on the line (2,1,1):
   KILLED by the bound (no charts): (1,1,1) [kap 3, rho 3, need 2 > 1], (2,1,1), (3,0,1), (4,0,0) [kap 1, q0(k,k) != 0].
   kap = 1 with q0(k,k) = 0 identically -> k in L'', reduced charts Gr(3,6) (r16_F2col_K2.py), SINGULAR QQ 20/20 [1] each:
     (4,0,1), (6,0,0), (22/7,0,6/7), (11/3,0,7/6)   [S]
   kap = 2, rho = 2 (q0|K proportional to [[1,7],[7,3]] or [[1,9],[9,5]]: two isotropic lines over Q(sqrt 46) / Q(sqrt 19)): k parametrised in K
     (chart k = K_j0 + t K_j, q0(k,k) = 0), L'' = Ck + L3 (r18_Kt.py): (1,0,0) mod p 280/280 [1] in 112 s; Singular QQ runs for (1,0,0), (1,0,1),
     (0,1,1), (0,0,1) in progress (r18/ktlines_{A,B}.log).
   kap = 4, rho = 4, m = 2: L'' contains a 2-dim q0-isotropic U in K (r18_KU.py; K in rref, U-charts Gr(2,4), L'-charts Gr(2,6)): (0,0,0) mod p 90/90 [1]
     in 44 s; Singular QQ chained (r18/ku000.log).
 Remaining fixed member: (nu = -1/2, a = (2,1,1)).
STATUS 04:17: 8/13 lines proof grade (4 by the kernel bound, 4 by Singular reduced charts); 5 lines in Singular via Kt/KU reductions; R1COF2 running in pool.

## R18-2. D003-PROP Case A: the BIG-KERNEL lemma applies -> a route that avoids the heavy Singular charts (r18_D3A_kernel.py, cache r18/cache_D3A.pkl)
 Forms of r14_D3A_fx.py (q0 = z^0 coefficient form, 8 further coefficient forms), nq = 8: rank q0 = 8; B-form ranks 3,3,4,4,4,3,3,4; B-stack rank 5,
   common kernel K of dim 3 = ker B_c (generic c, rank 5). L'' meets K in dim >= 4 - floor(5/2) = 2.
   q0|K = (a2+a3+1)^2 [[-11520, 384, 2112(a2-1)], [384, 0, 96(a2-1)], [2112(a2-1), 96(a2-1), -624(a2-1)^2]],
   det q0|K = 353894400 (a2-1)^2 (a2+a3+1)^6  (by hand from the matrix; recomputed exactly in r18_D3A_deg.py).
 => [rigorous, pointwise] off a2 = 1 (WLOG excluded in the D3A chart), a2+a3+1 = 0 (alpha_4 = 0: a zero coordinate -> S_4 / X0 coverage), and the
    rank/kernel degeneracy set (r18_D3A_deg.py, pending), NO 4-dim common isotropic L'' exists: D003-PROP Case A dies by linear algebra.
    Remaining for proof grade: the degeneracy set (exact), T1cert for D3A in Singular (r18_T1cert_D3A.py), and the alpha with a zero coordinate.
STATUS 05:15: resumed after the usage-limit cut; Kt lines (1,0,0) 276/280, (1,0,1) 202/210, (0,1,1) 266/280 [S] + Singular timeouts being re-run (STO 600); (0,0,1) Kt and (0,0,0) KU running.
 R18-1 update (05:19): Kt reductions in SINGULAR QQ (per-system timeout 120 s): (1,0,0) 276/280 [1] + 4 timeouts; (1,0,1) 202/210 + 8; (0,1,1) 266/280
   + 14; (0,0,1) 333/350 + 17; NO non-unit anywhere. The 43 timeout systems: msolve char 0 now (r18/kt_c0*.log), Singular with 6 GB / 1 h queued in
   the big slot (ST2-KTBIG). (0,0,0) via KU (m = 2) in Singular: running (r18/ku000.log). Fixed member (nu = -1/2, (2,1,1)): r18/fm211.log.
 R18-1 update (05:31): the 43 Singular-timeout systems of the four kap = 2 lines are all [1] in msolve char 0 (4 + 8 + 14 + 17; r18/kt_c0.log,
   r18/seq_small.log). Fixed member (nu = -1/2, a = (2,1,1)): killed by the kernel lemma at the point (and 70/70 charts).
   MEMORY INCIDENT 05:28 (coordinator): host < 1 GB available -> I stopped the two-row certificate (ST2-TWOROW-CERT), the pool R2SYMLINES chain
   (redundant), my D3A degeneracy run, my KU (0,0,0) Singular run and the kt_c0 chains; only R1COF2 kept. Restarted as ONE small job at a time
   (r18/seq_small.sh) with a memory guard (r18/memguard.sh: pause below 1.5 GB available).
 LINE STATUS (13): proof grade [E]/lemma or [S]: (1,1,1), (2,1,1), (3,0,1), (4,0,0) [kernel bound]; (4,0,1), (6,0,0), (22/7,0,6/7), (11/3,0,7/6)
   [reduced charts, Singular 20/20]; (1,0,0), (1,0,1), (0,1,1), (0,0,1) [Kt reduction: Singular on all systems except 43, those msolve char 0;
   Singular big slot queued]; (0,0,0) [KU: mod p 90/90, Singular rerun pending]. Plus the 2 J_A lines by the jump-type lemma.

## F2COL-TABLE update (R18, 05:50): rows changed
 R2 nu-lines (13 + 2)       | kernel bound (4); reduced charts K2 (4); Kt reduction (4); KU reduction (1); jump-type lemma (2)  |
                            | [E]+lemma: 4+2 lines; [S] Singular QQ: 4 lines complete, 4 lines except 43 systems ([M0], big slot ST2-KTBIG queued);  |
                            | (0,0,0): KU mod p 90/90, Singular rerun running (small-memory sequence)                                                    |
 R2 fixed member (nu = -1/2, (2,1,1)) | kernel lemma at the point | lemma
 D003-PROP Case A (branch 3) | BIG-KERNEL lemma (det q0|K = 353894400 (a2-1)^2 (a2+a3+1)^6) + degeneracy set + T1cert running | [E]+lemma (pending)
 R1 generic                 | RD: R1COF2 (pool) still interpolating                                                              | open
STATUS 05:52: lines: 8 complete proof grade + 4 lines all-but-43-systems [S] + (0,0,0) pending; D3A big-kernel route: degeneracy/T1cert running; R1COF2 running.
STATUS 05:56: round 19 started (43 Kt systems; D3A degeneracy/T1cert/zero alpha; R1 after R1COF2; KU (0,0,0)).

## R19-1. The kap = 2 lines without timeouts: Kt reduction over a QUADRATIC FIELD (r18_Kt3.py)
 On these lines q0|K = g(nu) * M with M CONSTANT ([[-1,-7],[-7,-3]], disc 46; [[-1,-9],[-9,-5]], disc 76): the two q0-isotropic lines of K are
 k = (-b + s) K1 + a K2, s^2 = D, handled at once by Singular over Q(s) (minpoly s^2 - D; the conjugate system has no solution iff this one has none).
 With k explicit, the complement index i (k_i = nonzero element of Q(s) times excluded factors) needs no Rabinowitsch, and q0(k, L3) = 0 is eliminated
 (j0 with w_j0 admissible): charts Gr(3,6), 9 chart variables, nu, w.
   (1,0,0): 20/20 [1] over Q(sqrt 46), 162 s, 70 MB.   (1,0,1): 20/20 [1] over Q(sqrt 76).   (0,1,1), (0,0,1): running.
 => these replace the Kt runs (and their 43 Singular timeouts): proof grade [S] with no big-slot work.
 D3A: verify2's d3a_slim over Q ended 06:00 with 64/70 [1] and 6 FAILED (0-1-3-6, 0-1-3-7, 0-1-4-7, 0-1-6-7, 1-2-5-7, 1-3-4-7; verify2/r15/d3a_slim_all70.log).
   The big-kernel route is chart-free, so it does not depend on those charts.

## R19-2. D003-PROP Case A: the degeneracy set of the big-kernel kill is EXACTLY the setup-exceptional set (r18_D3A_deg3.py, Singular over Q)
 With K in rref (pivots 0,1,6; denominators 4(a2-1)) and Q = {2,3,4,5,7} its coordinate complement: for 3 random c,
   gcd of det B_c[Q,Q] = (a2-1)^2 (a2+a3+1)^10, residual common zeros of the reduced determinants: {a2 = 1, a3^2 + 2a3 = 0} (inside a2 = 1);
   det q0|K (rref basis scaled by 4(a2-1)) = 815372697600 (a2-1)^6 (a2+a3+1)^6.
 => [rigorous, pointwise] for every alpha = (1, a2, a3, -1-a2-a3) with a2 != 1 and alpha_4 != 0 (and generic T_1, T1cert running): rank B_c = 5,
    ker B_c = K (dim 3), q0|K nondegenerate, so no 4-dim common isotropic L'' exists. D003-PROP Case A dies by linear algebra.
 Left: T1cert for D3A (Singular; running in the small sequence), the zero-coordinate family alpha_4 = 0 (and its S_4 images), a2 = 1 is WLOG.
 Kt3 audit request for verify2: the agent is not reachable by name from here; the request text is in this section's companion R19-1 (please relay).

## R19-3. D003-PROP Case A is CLOSED by the big-kernel lemma (chart-free)
 T1cert for D3A, Singular std over QQ: 12/12 [1] (excluded a2 = 1, a2+a3+1 = 0; rref denominators 4(a2+a3+1)) [S]  (r18/seq_small2.log).
 Generic alpha (a2 != 1, alpha_4 != 0): big-kernel lemma with exact degeneracy set = setup-exceptional set (R19-2)  [E + lemma + S].
 alpha_4 = 0 family alpha = (1, a2, -1-a2, 0) (r18_D3A_kernel2.py, cache r18/cache_D3A_a40.pkl): T_1 dim 13, rank-jump (a2-1)^3 (univariate: exact),
   detX -(a2-1)^2 (a2+1), dens 4(a2+1); B-stack rank 5, common kernel dim 3 = ker B_c, det q0|K = 28665446400 (a2-1)^2 (a2+1)^6, K basis never
   degenerate; rank B_c < 5 for all of 4 random c only at a2 in {1, -1} (gcd (a2-1)^3 (a2+1)^10).  => killed for a2 not in {1, -1}.
   a2 = 1: alpha = (1,1,-2,0) ~ (1,-2,1,0) by S_4, i.e. a2 = -2 on the same family: killed.  a2 = -1: alpha = (1,-1,0,0) = X0, killed exactly (R14-5).
 Zero patterns: one zero -> moved to position 4 by S_4 (alpha_1 != 0 kept); two zeros -> (1,-1,0,0) = X0; a2 = 1 is WLOG by S_4 (R14-4).
 => D003-PROP Case A: rigorous modulo verify2's check of the lemma chain; verify2's d3a_slim (64/70 + 6 FAILED) is superseded as a proof route.
STATUS 06:13: D003-PROP Case A closed (big-kernel lemma + T1cert Singular + alpha_4=0 family + X0); 12/13 R2 lines proof grade; KU (0,0,0) running.
 R19-1 CHECK ITEM (verify2): zeros of g(nu) in q0|K = g(nu) M on the four Kt3 lines:
   (1,0,0): g = 288 (nu+1)(3nu-1);  (1,0,1): g = 64 (nu+1)(3nu-1);  (0,1,1): g = 64 nu^2 (nu+1)(3nu-1);  (0,0,1): g = 288 nu^2 (nu+1)(3nu-1).
   All zeros lie in {0, -1, 1/3}: excluded in every Kt3 run (Rabinowitsch factor nu (nu+1)(3nu-1), printed in the logs) and handled separately as
   the nu-slices: nu = 0 by the fixed members (R17-4/R17-8: (1,0,0), (1,0,1), (0,1,1), (0,0,1) at nu = 0 all killed, 70/70 RED-p or lemma), and
   nu = -1, 1/3 as row-S_3 images of nu = 0 and nu = infinity (swap image of nu = 0, Z re-charted). CONFIRMED.

## R19-4. R1 rank-drop locus: Singular route (r19_R1cof_sing.py)
 det of the 7x7 principal minor (index 6 removed) of B_c with SYMBOLIC c: 10666 terms, total degree 25, computed by Singular in seconds (sympy R1COF/R1COF2
 spent hours in post-processing). Coefficients in c -> ideal; saturation by lam*a1*D; minAssGTZ over QQ. Stopped at 834 MB in my slot (memory rule);
 queued as ST2-R1COFSING (<= 1.5 GB) to replace R1COF2. Then: S_3 cut (r18_symcut_nl.py; P0 = lam, pieces H, A, D, RD components, EXC = lam*a1*D).
STATUS 06:19: R1 RD via Singular queued (ST2-R1COFSING); KU (0,0,0) paused by the guard; D3A closed and verified by verify2.
STATUS 06:21: round 20 started (R1 RD + cut; KU (0,0,0); consolidated F2COL-TABLE; B(dep)/uniform).

## F2COL-TABLE (CONSOLIDATED, R20, for one verify2 audit). Grades: [S] Singular std over QQ (or over Q(s) with minpoly); [E] exact symbolic
## (sympy over Q(params) / Groebner over Q / exact univariate gcds); [RED-p] msolve mod p on fixed rational data, all charts; lemma = pointwise
## linear algebra (kernel kill R15-4, general kernel bound R18-1, jump-type lemma R15-6, big-kernel lemma R17-3). [M0]/[Mp] = evidence only.
 F2col = {X = P (+) e_4 (x) Z : P Lagrangian in the 2-column block (columns 0,1; rows 1..3), Z in Gr(3,4)}; rulings R1 (lam in P^1), R2 (nu in P^1)
 [R13-2, rigorous]. Z-coverage: chart a4 = 1 (Z-normal n = (a1,a2,a3,a4), column-0 entry 0) + S_3 on columns 2,3,4 + column swap 0<->1 covers every Z
 except n = (1,0,0,0); when P lies in ONE column (cross-type) S_4 on columns 1..4 covers every Z.
 No. | piece                                                   | argument                                                         | grade        | ref
 ----|---------------------------------------------------------|------------------------------------------------------------------|--------------|-----------
 R2  |                                                         |                                                                  |              |
  1  | T_1 generic dimension (generic R2, 18 tree families)    | T1cert: pivot-column injectivity charts + Rabinowitsch            | [S]          | R17-1
  2  | generic nu, chart a4 = 1                                | kernel kill: k = e7-e6 constant, q0(k,k) linear, cofactors        | [E] + lemma  | R15-4/5
  3  | -> survivors                                            | S_3 symmetry cut (pieces H, A, D, 0/1 points)                     | [E]          | R16-5, R17-8
  4  | 15 cut nu-lines: (1,1,1),(2,1,1),(3,0,1),(4,0,0)         | general kernel bound                                             | [E] + lemma  | R18-1
  5  |   (4,0,1),(6,0,0),(22/7,0,6/7),(11/3,0,7/6)               | K2 reduced charts Gr(3,6), 20/20                                  | [S]          | R18-1
  6  |   (1,0,0),(1,0,1),(0,1,1),(0,0,1)                         | Kt3 over Q(sqrt 46)/Q(sqrt 76), 20/20 (verify2-checked)           | [S]          | R19-1
  7  |   (0,1/7,-8/7),(0,0,-1) (inside J_A)                      | jump-type lemma, Deg in special nu only                           | [E] + lemma  | R17-8
  8  |   (0,0,0)                                                | KU reduction (2-dim isotropic U in K), mod p 90/90                 | [S] PENDING  | R18-1
  9  |   exceptional nu on the lines                            | only {0,-1,1/3} (+ nu = -1/2 on (2,1,1): lemma at the point)      | [E] + lemma  | R18-1
 10  | A = {a1 = 0}, J_A (S_3-invariant families)              | kernel kill / jump-type lemma, Deg, S_3 cut                       | [E] + lemma  | R16-5, R17-4
 11  | special nu {0,-1,1,1/3,-1/3,inf}                        | one orbit of row-S_3 x column swap                               | lemma        | R16-6
 12  | nu = 0 slice                                            | kernel kill + T1cert + S_3 cut -> A u J0 u points                  | [E][S]       | R16-1, R17-4
 13  |   its 15 fixed members                                  | lemma at the point (6) / full charts 70/70 (9)                    | lemma/[RED-p]| R17-4, R17-8
 14  |   J0, J0 cap A                                          | jump-type lemma, Deg = EMPTY, S_3 cut                             | [E] + lemma  | R17-4, R17-8
 15  | special Z n = (1,0,0,0)                                 | big-kernel lemma (det q0|K) + nu = 0 70/70                         | [E]+lemma+[RED-p] | R17-3
 R1  |                                                         |                                                                  |              |
 16  | cross-type lam = 0 (and lam = inf by the swap)          | kernel kill + S_4 cut + T1cert + 4 fixed members 70/70            | [E][S][RED-p]| R17-5
 17  | jump plane {lam = 0, sum a = -1}                        | jump-type lemma, Deg = EMPTY, S_4 cut, 2 points, T1cert            | [E][S][RED-p]| R17-2
 18  | generic lam, T_1                                        | T1cert 12/12 (excluded lam, a1, D only)                           | [S]          | R17-7
 19  | generic lam                                             | kernel kill: k = e7-e6, q0(k,k) = 2 lam (a1+2a2+2a3-6)            | [E] + lemma  | R16-2
 20  | -> rank-drop locus RD, S_3 cut, lines                   | ST2-R1COFSING (Singular, symbolic c), then r18_symcut_nl.py        | OPEN         | R19-4
 21  | R1 families a1 = 0, D = 0 (and their T1cert)            | to do (the R1 tree stalled on sympy Groebner; redo with Singular)  | OPEN         | R17-7
 Cross-checks (not needed for the proof): R2 H 3-parameter run char 0 35/35 [M0]; R2LINES/SYMLINES mod p; verify2's D3A charts.
 => F2col is CLOSED except rows 8 (pending Singular), 20, 21 (R1 generic: RD + cut + the families a1 = 0, D = 0).

## R20-1. Generic R1: rank-drop locus and symmetry cut (char-p STRUCTURE, exact confirmation by ST2-R1COFSING pending)
 r20_Ksing_p.py (Singular char 32003, c-coefficient ideal of det(c1 B1 + c2 B2 + c3 B3)[7x7], sat() by lam*a1*D, minAssGTZ; ~1 min):
   generic R1: RD = { a = (1,1,1) } (lam free) -- one line.   R1 a1 = 0 family: RD = { (a2,a3) = (1,1) }.
 S_3 cut for generic R1 with pieces H, A, D, (1,1,1) (r17_symcut.py): region survivors A u {(1,1,1)} u {(2,1,1)}; slice a2 = 0: (3,0,1), (4,0,1),
   (22/7,0,6/7), (11/3,0,7/6) (+ A); slice a2 = a3 = 0: a1 in {4, 6} (+ A).  Same list as R2 minus the 0/1 points other than (1,1,1).
 R1 a1 = 0 family (A): kernel structure standard (k = e7-e6, q0(k,k) = 2 lam (a2+2a3-6)); exceptional a2, a2+a3-4, a2+a3+1 (T_1 jump), lam; its cut
   (as R16 symcut3) leaves (0,1,1), the orbit of (0,1,-8,7) and the jump plane J_A^R1 = {a1 = 0, a2+a3+a4 = 0}.
 R1 lines (lam free): (1,1,1), (2,1,1), (3,0,1), (4,0,1), (22/7,0,6/7), (11/3,0,7/6), (4,0,0), (6,0,0), (0,1,1), (0,1/7,-8/7): kernel bound +
   exceptional lam running (r20/r1lines.log); then K2 / Kt3 / KU reductions in Singular as for R2.
STATUS 06:39: R1 RD (char p) = one line (1,1,1); cut -> 10 R1 lines; kernel-bound batch running; ST2-R1COFSING (exact) still running in pool; KU (0,0,0) running.

## R20-2. RD certificate over Q without primary decomposition (r20_RDcert.py) and the R1 line pipeline
 ST2-R1COFSING (full minAssGTZ over QQ) ran out of memory at 1.5 GB. Lighter certificate: with I = c-coefficient ideal of det(c1B1+c2B2+c3B3)[7x7],
   test 1 in I + (1 - w f EXC) for f in {a1-1, a2-1, a3-1}, EXC = lam a1 D  =>  V(I) \ V(EXC) inside {a = (1,1,1)}. Mod 32003: all [1] in 44 s, 83 MB;
   char 0 run queued after the line reductions (r20/r1red.sh).
 R1 lines (lam free), general kernel bound (r20/r1lines.log): KILLED (2,1,1), (3,0,1), (4,0,0); K = Ck, q0(k,k) = 0 -> K2: (4,0,1), (22/7,0,6/7),
   (11/3,0,7/6), (6,0,0) (Singular with per-chart timeout and msolve char-0 fallback: r20_F2col_K2b.py); dim K = 2 -> Kt3: (1,1,1), (0,1,1).
   Exceptional lam on each line with 4 combinations c (r20_lineexc_mc.py, r20/r1exc.log) pending (several lines lie in D, outside the generic RD result).
## R20-3. OPEN piece: the R1 jump family J_A^R1 = {a1 = 0, a2+a3+a4 = 0} (lam, a3 free; dim T_1 = 15, nq = 10)
 B_1 rank 2, B_2, B_3 rank 8, B-stack 9 (K = Ck), q0|K rank 1. The (recursive) kernel bound gives only L'' cap ker B_1 >= 3 (r20_kbound_rec.py): not decided.
 Unlike R2's J_A (B_z rank 7 -> jump-type lemma), no lemma applies; candidate routes: charts in the reduced space (L'' cap W_1 = 3-dim), the S_3 cut once
 any survivor superset is known, or the big slot. The cut point (0,1/7,-8/7) of generic R1 lies in this family.
STATUS 06:55: R1: RD = (1,1,1) (mod p, cert char 0 pending); 10 lines in reduction; open: J_A^R1 (2-param jump family) and KU (0,0,0).
 R20-2 update (07:08): R1 line (4,0,1) K2: 20/20 [1] -- 12 charts Singular QQ [S], 8 charts Singular > 120 s -> msolve char 0 [M0] ((0,2,3),(0,2,4),(0,4,5),(1,2,3),(1,2,4),(1,2,5),(1,3,5),(1,4,5)); Rabinowitsch lam only. Remaining R1 K2/Kt3 lines running (r20/r1red.log).
STATUS 07:08: round 20 report sent; R1 line reductions, R1 RD char-0 certificate, KU (0,0,0) continue in my slot.
STATUS 07:09: round 21 started (J_A^R1; KU (0,0,0) via split quaternary; R1 lines/RD cert; B(dep)).

## R21-1. J_A^R1 is CLOSED by a RANK-2 SPLIT + recursive kernel bound (r21_rank2.py, r21_kbound_hyp.py, r21_JA_deg.py, r21_algpoint.py)
 LEMMA (rank-2 split) [rigorous]: if B has rank 2 then B = l1 l2 (two linear forms, here RATIONAL: B_1 = 2b (row 2 of B_1)(row 5 of B_1),
   b = -1/(60 lam (lam+1))), and a subspace of dim >= 2 is B-isotropic iff it lies in {l1 = 0} or {l2 = 0}. So L'' lies in H_2 or H_5 (dim 9).
 In each H_j (generic over Q(lam, a3)): B_2|H has rank 7 -> L'' meets its 2-dim kernel W; B_3|W has rank 1 -> L'' contains w' = ker(B_3|W);
   q0(w', w') = -400 lam (a3 - 7) != 0 -> CONTRADICTION. Both branches -> the generic member of J_A^R1 is dead.
 Exact failure sets (Groebner / gcds over Q): branch 2: lam (lam+1) (a3+1)(a3+2) C1 (a3-7); branch 5: lam (a3+1)(a3+2) C2 (a3-7), with C1, C2 explicit
   conics in (lam, a3); no basis degeneration. S_3 cut of these pieces (r18_symcut_nl.py, J_A is S_3-invariant): every leaf lies in lam = -1.
 lam = -1 slice: the split uses rows 3, 5 (N = [[0,1/40],[1/40,0]]); both branches die generically; failure set {a3 in {-1,-2}} u {35a3^2-112a3+153 = 0}
   u {a3^2-2a3+3 = 0} u {a3 = 7}; its S_3 cut: NO leaf.
 Boundary (a zero among a2, a3, a4): the S_3-orbit of n = (0,0,-1,1), i.e. the R1 line a = (0,0,-1) (lam free; nq = 10): rank-2 split, both branches die
   generically (B_2|H rank 3, B_3|ker rank 5, q0(w',w') = 2800 lam); exceptional lam: 0 (closed), -1 and the roots of 3lam^2-3lam-1 / 3lam^2-6lam-1:
   all killed pointwise by exact linear algebra over Q, Q(sqrt 21), Q(sqrt 3) (r21_algpoint.py; Galois conjugates identical).
 T1cert for J_A^R1 in Singular: 10/10 [1] (excluded lam, a3+1).  => J_A^R1 CLOSED [E + lemma + S].
STATUS 07:15: J_A^R1 CLOSED (rank-2 split + recursive bound + S_3 cut + exact points).

## R21-2. RECURSIVE KERNEL BOUND kills the remaining lines with no charts (r20_kbound_rec.py; r21_chain.py adds the exact exceptional set)
 A totally isotropic L (dim m) meets ker(G) in dim >= m - floor(rank G / 2); recurse into that kernel with all forms restricted; contradiction when the
 required dimension exceeds the maximal isotropic dimension (dim - rho) + floor(rho/2) of the restricted forms (rho = rank of a generic combination).
 Using INDIVIDUAL forms (not only B_c) this is strictly stronger than R18-1: generic kills found for
   R1 (4,0,1), (22/7,0,6/7), (11/3,0,7/6), (6,0,0): ker B1 (rank 5) -> need 2 in dim 3, max isotropic 1;
   R1 (1,1,1): ker B1 (rank 4) > ker B2 (rank 1): need 2 in dim 3;  R1 (0,1,1): ker B1 (rank 2) > ker B2 (rank 3): need 2 in dim 3;
   R2 (0,0,0): ker B1 (rank 2) > ker B2 (rank 1): need 3 in dim 5, max isotropic 2.
 r21_chain.py: exceptional parameter values of the chain (rank drops via univariate gcds, kernel-basis degeneration, final rho) and a pointwise check at
 one root of each irreducible factor over the number field. R1 (4,0,1): exceptional lam = roots of 3lam^2+6lam-1 (killed at the point) and lam = 0
 (cross-type, closed). The other lines: r21/chains.log (running). The slow K2/Kt3 chart runs for the R1 lines are superseded and were stopped.
STATUS 07:17: recursive kernel bound kills all remaining lines generically (R1 x 6, R2 (0,0,0)); exceptional points being checked (r21/chains.log).
 R21-2 results (r21/chains.log + pointwise follow-ups):
   every remaining line is killed GENERICALLY by the recursive bound; exceptional parameter values (exact, univariate), each checked at one root:
   R1 (4,0,1): 3lam^2+6lam-1 -> killed (recursion at the point);  (6,0,0): 3lam^2+6lam-1 -> killed;  (1,1,1): 3lam-1 -> killed;
   (0,1,1): 8091lam^2+31226lam-2697 -> killed;  (3,0,1), (4,0,0): 3lam^2-6lam-1 -> killed;
   (22/7,0,6/7) at 3lam^2-6lam-1 and (11/3,0,7/6) at 3lam^2+6lam-1: recursion undecided there (B1 rank drops to 4) -> k in L'' (B_c rank 7, K = Ck,
     q0(k,k) = 0) -> reduced charts Gr(3,6) over Q(sqrt 3) (r21_algK2.py): 20/20 [1] each [S];
   (2,1,1) at the cubic 27lam^3+15lam^2+21lam+1: recursion done in Singular over Q(theta) (r21_algpoint_sing.py): ker B1 (rank 4) > ker B2 (rank 1):
     need 2 in dim 3 -> KILLED;   lam = 0 everywhere: the cross-type ruling (closed, R17-5).
   R2 (0,0,0): exceptional nu in {0, -1, 1/3}: nu = 0 killed at the point; nu = -1, 1/3 are the symmetric slices (row-S_3 / swap images of nu = 0, and
     n = (0,0,0,0,1) is swap-invariant) -> the LAST R2 LINE IS CLOSED [E + lemma] (KU Singular run superseded).
 => All R1 cut lines and all 13 R2 lines are closed. Remaining for R1: the exact (char-0) certificates of RD for generic R1 and the a1 = 0 family,
    T1cert for a1 = 0, and the a1 = a2 = 0 family (r21/r1rest.log).
STATUS 07:26: all R1 lines and the last R2 line (0,0,0) closed; R1 RD char-0 certificates and the a1=a2=0 family running.

## R21-3. EXACT RD certificates in seconds (r21_RDcert2.py) and the rest of R1 -> F2col CLOSED (pending verify2's audit)
 P(c) = det(c1 B1 + c2 B2 + c3 B3)[7x7] (symbolic c, Singular) is divided EXACTLY by its known factor DIV (remainder 0, unit 1); the c-coefficients of the
 quotient generate J_Q; {P(c) = 0 for all c} = {DIV vanishes for all c} u V(J_Q), and the Rabinowitsch tests 1 in J_Q + (1 - w f EXC) run over QQ:
   generic R1: DIV = lam^6 D^5 (c.a); J_Q 15 generators, degree <= 6; tests a1-1, a2-1, a3-1 all [1] (16.5 s, 49 MB)
     => RD \ V(lam a1 D) = {a = (1,1,1)} EXACTLY (DIV part: lam = 0, D = 0 or a = 0, all excluded/handled).
   R1 a1 = 0: DIV = lam^6 (a2+a3-4)^5 (c2 a2 + c3 a3); J_Q 12 generators; tests a2-1, a3-1 [1] => RD_A = {(a2,a3) = (1,1)} EXACTLY.
   R1 a1 = a2 = 0: plain certificate 1 in I + (1 - w EXC) [1] over QQ => no common rank drop.
 T1cert Singular: R1 a1 = 0 12/12, R1 a1 = a2 = 0 12/12, J_A^R1 10/10.
 R1 a1 = 0 family: kernel kill (q0(k,k) = 2 lam (a2+2a3-6)); S_3 cut with pieces H_A, a2, D_A, J_A^R1, (0,1,1): region survivors (0,1,1,1) [line (0,1,1),
   closed], the orbit of (0,1,-8,7) [in J_A^R1, closed], J_A^R1 [closed]; boundary -> the a1 = a2 = 0 family.
 R1 a1 = a2 = 0 family: kernel kill (q0(k,k) = 2 lam (a3-6), no rank drop) -> a3 = 6 (killed by the swap: a3 = 1/6 is not a survivor), exceptional
   a3 = 4 (swap-killed), a3 = 0 (line (0,0,0): recursive bound, exceptional 3lam^2-6lam-1 killed at the point), a3 = -1 (line (0,0,-1), R21-1).
 R1 special Z n = (1,0,0,0): column-swap image of the line (1,1,1) at lam' = -1/(3 lam) (closed); lam = inf <-> lam = 0 (cross-type, closed).

## F2COL-TABLE (R21 FINAL ROWS; replaces rows 8, 20, 21 of the consolidated R20 table)
  8  | R2 line (0,0,0)                                    | recursive kernel bound; exceptional nu in {0,-1,1/3} (nu = 0 at the point;    | [E] + lemma  | R21-2
     |                                                    | -1, 1/3 symmetric slices)                                                     |              |
 20  | R1 generic: RD                                     | factored determinant + Rabinowitsch over QQ: RD = {(1,1,1)}                   | [S]          | R21-3
 20a | R1 generic: S_3 cut -> 10 lines                    | linear algebra (pieces H, A, D, (1,1,1))                                       | [E]          | R20-1
 20b | R1 lines (2,1,1),(3,0,1),(4,0,0),(4,0,1),(6,0,0),   | recursive kernel bound (generic) + exceptional lam killed at one root each     | [E] + lemma  | R21-2
     |   (1,1,1),(0,1,1),(22/7,0,6/7),(11/3,0,7/6)        |   (number fields up to cubic); 2 points by reduced charts over Q(sqrt 3) 20/20  | [S]          |
 21  | R1 a1 = 0 family + cut                             | kernel kill + T1cert + exact RD_A + S_3 cut                                    | [E][S]       | R21-3
 21a | R1 jump family J_A^R1 (incl. line (0,1/7,-8/7))     | rank-2 split + recursive bound + S_3 cut + exact points + T1cert               | [E][S] lemma | R21-1
 21b | R1 a1 = a2 = 0 family, lines (0,0,0), (0,0,-1)      | kernel kill (no rank drop, exact) + swap cut + recursive bound + points        | [E][S] lemma | R21-1, R21-3
 21c | R1 special Z, lam = inf                            | column swap images of closed pieces                                            | lemma        | R21-3
 => EVERY ROW of the F2col table is now [S]/[E]/[RED-p]/lemma: F2col is CLOSED, pending verify2's single audit.
STATUS 07:38: F2col CLOSED pending verify2 audit (R1 RD exact in 16 s; J_A^R1 by rank-2 split; all lines by the recursive bound).
STATUS 07:39: round 22 started (O1 uniform z=3 exclusion via kernel bounds; D04-PROP char 0; B(dep); uniform statement; Lean note).

## R22-1. D04-PROP parametric: CLOSED in char 0 by the recursive kernel bound (r22_genset.py generic setup; r22/spec_D04P.py, sigma symbolic)
 Generic setup (all 17 non-constant coefficient forms of Q H(J+m) Q^T; dim T_1 = 14, nq = 9; rank-jump test constant (univariate: exact);
 complement scaled by 10 sg): chain V > ker B1 (rank 2) > ker B2 (rank 2) > ker B3 (rank 2) > ker B9 (rank 1) > ker B6 (rank 1): need 1 in dim 1,
 max isotropic 0 -> generic sigma DEAD [E + lemma]. Exceptional sigma (r21_chain.py, exact): roots of 3sg+2, 3sg^2+3sg+1, sg+1 -> killed at the point
 (recursion over Q / Q(sqrt -3)); sg = 0 -> own setup (r22/spec_D04P0.py): chain ker B1 > ker B5 > ker B3 > ker B6 -> killed exactly.
 => D04-PROP for all sigma: proof grade [E + lemma], replacing the msolve char-0 evidence (V-r11 logic unchanged).

## R22-2. B(dep): the two P0_B_i points are now EXACT kills (were "FO2 = 8 + (T2) fail [numerical]")
 X bases rebuilt from r9/Dir_D04_P0_B_i_c0_v123.sing (r22/mkspec_dir.py) at (r1,r2,f0,f3) = (-1,-1,2,2) and (0,0,2,-2): dim T_1 = 12 (nq = 7), and a
 generic combination of the forms is nondegenerate on the 7-dim complement, so a common isotropic L'' has dim <= 3 < 4 -> DEAD exactly [E]
 (this is the FO2 bound 8 in exact form). Remaining B(dep) gap: the eliminations of R12-1 are mod p (evidence) -> char-0 versions
 (the full systems segfaulted at 2 GB in msolve; candidates: Singular with the v = e_1, e_2 subsystems, which already sufficed mod p).

## R22-3. Lean note (for leanfl): the lemmas behind the F2col / D3A / D04-PROP kills
 Abstract linear algebra (field of char 0, V finite-dim, forms symmetric bilinear):
  (L1) MEETING LEMMA: B of rank r, L totally B-isotropic => dim(L cap ker B) >= dim L - floor(r/2).  [isotropic subspaces of a nondegenerate
       form on V/ker B have dim <= floor(r/2)]
  (L2) MAX-ISOTROPIC BOUND: a family of forms whose generic combination has rank rho on W admits no common isotropic subspace of dim
       > (dim W - rho) + floor(rho/2).
  (L3) KERNEL KILL: common kernel C k of {B_z}, some B_c of rank dim V - 1, L common isotropic for q0 and the B_z, dim L >= 2 => k in L, so q0(k,k) = 0.
  (L4) BIG KERNEL: as (L1)+(L2) with W = common kernel of dim 3 and q0|W nondegenerate.
  (L5) RANK-2 SPLIT: B of rank 2 is l1 l2 (over the base field when the 2x2 middle matrix has square discriminant, here off-diagonal); an isotropic
       subspace of dim >= 2 lies in ker l1 or ker l2.
  (L6) RECURSIVE BOUND: iterate (L1) inside kernels; terminate with (L2).
 Problem-specific: (P1) FO2-joint necessity (L level, X in L => L in T_1(X) and L/X isotropic for every q_m, m in X) -- upstream L_gct_152 is the
  abstract core; (P2) invariance of level spaces under row/column permutations and the induced action on the parameters (nu, lam, Z-normal);
  (P3) the F2col structure theorem (R13-2) and Z-coverage; (P4) T1cert semantics (pivot-column injectivity => generic rank).
 Computational inputs a Lean proof would need as certificates: generic ranks over Q(params) (exact linear algebra), the exceptional polynomials
  (gcds / Groebner bases), and every "std = 1" claim as a Nullstellensatz certificate (explicit cofactors) -- Singular can export them (lift).
STATUS 07:43: D04-PROP closed in char 0 (recursive bound); B(dep) P0_B_i points exact; Lean note written.

## F2COL-TABLE log pointers (R22, for verify2)
 RED-p members re-run with logs (stage2/r21/redp_logs.log, script r21/redp_logs.sh):
   R2 nu = 0, a = (0,0,1): 70/70 [1] (cache r16/cache_92c32b1aa4fb.pkl)      [row 13]
   R1 cross-type lam = 0, a = (0,0,1): 70/70 [1] (cache r16/cache_1fce7c69a711.pkl)      [row 16]
   R1 jump point lam = 0, a = (0,-8,7): reduced charts Gr(3,8) 56/56 [1] (cache r16/cache_8967677ebd48.pkl, a2 = -8)      [row 17]
 Kt3 lines [row 6]: re-run with logs into the same file (r18_Kt3.py, 20 charts each); original runs: task outputs of R19 (not saved as files).
 Other row logs: rows 1, 18 T1cert r17/T1cert_R2_sing.log, r17/t1cert_tree.log; rows 4/5/9 r18 line logs (r18/k2lines_*.log); rows 12-14 r17/nu0_points*.log
 (the nu0_points2 run printed to the terminal; its three members are in redp_logs / R17-8); row 15 r17 (big-kernel data) + r17_charts at nu = 0;
 row 16 r17/cross_batch.log, r17/cross_points.log; row 17 r16/jump_Deg.log, r17/jumpdeg_all.log; rows 20/21 r21/chains.log, r21 RDcert2 outputs
 (/tmp/st2_rdc2_*.out, values in R21-3), r21/pieces_JA_R1*.py + r18_symcut_nl.py outputs (R21-1).

## R22-4. O1 (uniform z_i = 3 exclusion): status and a concrete reduction
 What O1 needs = (a) the classification of z = 3 level X (target 2: two-row P classified mod p + char-0 certificate pending (ST2-TWOROW-CERT stopped in
 the memory incident); three-row P: numerical evidence only), plus (b) killing every class:
   F2col (2-column P): CLOSED (verified by verify2 pending its last log check);  D003-PROP Case A, D04-PROP: CLOSED;  two-row non-isotropic: SPLIT;
   two-row ISOTROPIC family (m = (0,u), u isotropic, t in P^1 over Q(i)): generic setup over Q(i)(t) (r22_genset.py with QI): dim T_1 = 13, nq = 8;
   at t = 2/3 the recursive bound kills (ker B1 rank 5 -> need 2 in dim 3, max isotropic 1); the parametric recursion over Q(i)(t) is running
   (r22_kbound_qi.py; slow in sympy), then exceptional t via r21_chain-type exact gcds and pointwise checks.
 A uniform argument would have to explain WHY the single-row forms always leave a small kernel: in every z = 3 family so far some single-row form B has
 rank <= 5 with a kernel on which q0 (or the other forms) is "too nondegenerate". Candidate statement for a uniform proof (not proved): for every level
 X with z_i = 3, the form B_w (w in Z generic) restricted to T_1(X)/X has rank <= 5 and its kernel meets ... -- to be extracted from the families.
STATUS 08:01: round 23 started (O1 uniform; iso two-row parametric; B(dep) char 0; TWOROW-CERT big slot).

## R23-1. Isotropic two-row family (O1 piece): generic kill over Q(i)(t) EXACT, exceptional t = the special members
 r23_iso_chain.py / r23_iso_deg.py (Singular over Q(i)[t], minpoly i^2+1): one-step chains via B1, B2, B3 (rank 5: L'' meets the 3-dim kernel in dim 2)
 and B9, B10, B11 (rank 3: meets the 5-dim kernel in dim 3), each with a combination of all forms nondegenerate on the kernel (isotropic dim floor(d/2)).
 gcd over all 12 (chain, combination) failure polynomials = (t^2 + t - 1/2)^16 (t^2 + i t + 1/2)^16 -- only setup-exceptional t (complement/rank-jump
 factors, together with (2t^2-2t-1)(2t^2-2it+1)), i.e. the members where a coordinate of u vanishes = the special members m = (0,0,1,w,w^2) up to S_4 and
 conjugation, killed exactly earlier (isoSpecA 126/126). t = infinity (u ~ (i,-i,-1,1)): own setup, recursive bound kills (ker B1 rank 5) [exact].
 => isotropic two-row family CLOSED [E + lemma] modulo verify2 (and modulo the two-row classification certificate, queued ST2-TWOROW-CERT-BIG).
## R23-2. Queued, not run: ST2-TWOROW-CERT-BIG (r23_tworow_cert.py, SING_ULIM env). B(dep) char-0 eliminations: not started. O1 uniform proof: not found.
STOPPED 08:04 UTC
