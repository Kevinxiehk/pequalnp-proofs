# HANDOVER-rows -- ROUND 19 (06:35 UTC)
* Read first: rows/r18/w4p.big.out, w5p.big.out (Walsh relaxations of (SM4''), (SM5): unit = decided mod P1), then w4q/w5q (Q: exact char 0),
  then rows/r18/sp*.big.out, rows/r17/smc*.big.out.  Unit W4 + W5 at P1 and Q => (PL), PL4, and leaf 3 closed via IS2/IS3 (R18.1); then
  demote the R15*/R16*/SMC/SP jobs to cross-checks and finalise R16.3.
* Hand-proof leads for (SM4''): R19.2 (square-zero algebra: (A^2+B^2+C^2)e = 0, ABC = 0), R19.3 (g-form / cube-linearity), R19.4 (needs all
  four triples).
* Generators: rows/r18/sm5w.py (Walsh, rational), smphi.py (conic cubic, rational).

# HANDOVER-rows -- ROUND 18 (06:15 UTC)
* Read first: rows/r18/sp5.big.out, sp4.big.out (cubic relaxation mod P1; unit decides (SM_n)), rows/r17/smc5.big.out, smc4.big.out (full
  conic form), then the Q versions (spQ*.big.out decide in char 0).  If SP5P/SP4P are unit: tell the coordinator to demote R17SMC*P to
  cross-checks, and the leaf-3 R15*/R16* jobs too (IS3); then finalise R16.3 with the isotropic slice.
* Lemma chain for verify2: NOTES-rows R18.1 (IS0-IS5).  Generators: rows/r18/smphi.py (cubic, over Q), rows/r17/smc.py, smv.py.
* (SM4'') 12-variable test: rows/r18/sm4w*.sing (chart f_1 = 1); pool run output rows/r18/sm4wc_p.out (may have finished).

# HANDOVER-rows -- ROUND 17 (05:25 UTC)
* KEY: the isotropic slice (R17.5): (SM4) + (SM5) => (PL), PL4, and all remaining leaf-3 cases.  Big-slot jobs: R17SM5P/SM4P (y-form) and
  R17SMC5P/SMC4P (conic form, preferred), then Q(i) versions R17SM*Q / R17SMC*Q; outputs rows/r17/*.big.out.  Verdict: last "after column k
  nonzero: dim -1 unit 1".  If SMC5P/SMC4P are unit: tell the coordinator which leaf-3 / V5 jobs become redundant (R17.5(b)).
* Generators: rows/r17/sm5.py (y-form), smc.py (conic), smv.py (all-vertex), single_num.py / sm5_num.py (numerics).
* Host memory is tight; keep pool jobs <= 0.45 GB while the big slot runs.

# HANDOVER-rows -- ROUND 16 (03:55 UTC)
* Leaf 3: everything not in the big slot is char 0 (see RESULT ROUND 16; manifest rows/leaf3/MANIFEST.txt; closing statement draft R16.3).
  Big-slot pieces to read first: rows/r15/pl4fQ.big.out (support-4 G, Q(i)), pl5_G4_5f / pl5Q_G4_5f, pl5_R4 / pl5Q_R4, pl5_R5 / pl5Q_R5
  (.big.out), rows/r13/bq5[a]_P2_z3.big.out, bq5[a]_P2_A.big.out.  Verdict lines: "PLANE ... dim -1 unit 1" / last "after saturation ...
  unit 1".  A non-unit plane test => ask the coordinator to restore the full-K job for that case.
* (PL): Veronese SUMQ (rows/r13/sumqv.py) 5-7x faster than sumq.py; six 5-column jobs R16V5* in the big slot.
* Audit lesson (R16.7): check every Rabinowitsch "nonzero" factor against the case definition.

# HANDOVER-rows -- ROUND 15 (03:15 UTC)
* PLANE TEST (R15.1, rows/r15/plane.py) and plane split (rows/r13/case4.py / case5.py options SUBZ=, STAGED, FAM, ADD).
* Support 4: char 0 except G (plane test mod P1; big slot R15GQ).  Support 5: P3, P4, PP, P5, S23 exact; P2 mod P1 (exact runs
  rows/r13/runS5Q2.sh -> kS5Q.out, may still be running); G4-A, R4, R5 in the big slot (R15G4P/Q, R15R4P/Q, R15R5P/M/Q; outputs
  rows/r15/*.big.out).  Check those outputs first next round.
* Bugs this round: 2u vs 3u row sum for 5 columns (plane.py; fixed); driver argument order (fixed).

# HANDOVER-rows -- ROUND 14 (02:10 UTC)
* Leaf 3 (b): support-4 case tree (R14.0): P2 unit mod P1 (exact queued R14-P2Q), P3 and PP exact over Q(i), P4 by hand, G OPEN (P1 run times
  out; family e_2 = 0, e_4 = -1, R14.7).  Support 5: case5.py, nine cases, all queued (R14-K21BIG, rows/r13/runS5big.sh -> c*_*.big.out).
* Generators rows/r13/case4.py (cases P2, P3, PP, G; options ADD, MOB=) and case5.py.  Calibrations: k21sys.py supports 2, 3.
* Idea for G: in the binary model (V = binary quadrics, f_k = l_k^2) the four points satisfy sg(f_i,f_j) ~ l_l l_m; combine with the mixed
  (n,n,Y) conditions, which are then linear conditions pairing y_l with l_l l_m-type vectors -- a hand reduction may make G small.

# HANDOVER-rows -- ROUND 13 FINAL (01:30 UTC)
* Leaf 3 (a) CLOSED: RED-p cover of the 16 special points 64/64 unit at P1 (rows/r12/kSP1.out; runSP1.sh + gsel.py + runSP1fix.sh).
* Leaf 3 (b) OPEN: (2,1) kernels on 4-5 columns.  Start from NOTES-rows R13.6 (Lemma RS), R13.8 (Lemma U, case P4, case G reduction),
  tools rows/r13/k21sys.py (exact normal form; calibrated SUP=2 dim 2, SUP=3 dim 1; SUP=4 heavy), k21cr.py (Cramer variant, heavier),
  k21redF.py (forced-support census), caseG4.sing, tfac.sing.  Suggested next step: the case tree for support 4 (n parallel with
  |supp n| = 2, 3; case G) via the MIXED triple conditions (linear in the columns of Y), each as a small exact system.
* Do not use SIGSTOP on jobs run under `timeout` (the clock keeps running: that is what "halted" one RED-p chart).

# HANDOVER-rows -- ROUND 13 ADDENDUM (00:55 UTC)
* (2,1) stratum on <= 3 columns in CHARACTERISTIC 0: family B (rows/r12/bred.py charts A, D; R13.1'), the line d = u (ured.py; R13.2),
  A1/A2 (round 12, over Q); special locus classified exactly (speclocQ.sing, speclocInf.sing; R13.3).
* R12.9 was INCOMPLETE (only 4 of the 8 special points per i: the factor (1 - ii) was missing); flagged in place.  Repair: RED-p cover of all
  16 geometric points x 2 e-signs x charts m0, m2 at P1 = 2147483629 (runSP1.sh -> kSP1.out, then runSP1fix.sh reruns unfinished items).
* GAP for leaf 3: (2,1) kernels on FOUR or FIVE columns were never treated (R13.4; census k21five.py found none in 7 starts).
* Five columns: Veronese-variable SUMQ (rows/r13/sumqv.py: Q_j = q_j q_j^T, B_j linear in Q_j, cubic of degree 3 instead of 6, sign symmetry
  2^NC removed) written; calibration on 3-4 columns pending (v_++-, v_---, v_---- in rows/r13).
* Lesson: never kill by pattern with pgrep/ps|grep when the pattern also occurs in your own command line (3 self-kills this round); kill PIDs.

# HANDOVER-rows -- ROUND 12 ADDENDUM (00:10 UTC)
* (5,1) CRITERION (R12.5, 4 lines): no column-centred (4,1) extension of a strongly level K (sum m = 0)  =>  no (5,1) space contains K.
  Tool: rows/r12/kgen.py (explicit kernels; modes cc/cs; charts m_K0 = 1; prints the gauge determinant and a strong-levelness self-check;
  options num=<sqrt3>,<i> for numeric roots mod p = 1 mod 12, gnum= for numeric gamma, mz= to zero m-entries settled in another chart).
* LEMMA 3COL (R12.8, hand): three-column strongly level 3-spaces have a rank-1 column => three-column (2,1) kernels are A1, A2 (exact list,
  famA2.py) and family B.  A1, A2 excluded EXACTLY over Q (kA_Q.out).  Family B and the special line d = u: kgen cc runs, chained
  runB2.sh -> runU.sh -> runBU23.sh (outputs kBpar.out, kU.out, kBU23.out); isolated special points: runS2.sh -> kS2.out.
* Generic two-column (2,1) kernels with m_a = m_b = 0: hand proof R12.10 (Lagrangian => Z = zeta m^T; zeta isotropic; degree-3/4 parts kill
  zeta).  The hand-off (H) to verifyfl is withdrawn (R9.0 ADDENDUM-2).
* Gauge bug (R12.7): c21s.py point charts had a vanishing gauge determinant for 4 of the 16 point kernels; always print det before trusting units.
* Open: exact (over Q) versions of the special-point / B / U runs; five columns (R12.12: moment reformulation only).

# HANDOVER-rows -- ROUND 11 ADDENDUM (23:05 UTC)
* (q,d) = (1,2) kernel stratum (chi (x) C^M, K_II): settled for (4,1) and ALL (5,1) (R10.6 + R11.2; exact over Q).
* Two-column (2,1) kernels: generic case (Pi = V) settled BY HAND (R11.4 - R11.7): NCOL_1 for (4,1), unique extension => no (5,1) of rank c = 1
  (pencil), no column-centred extension (m_a or m_b != 0).  Key tools: the K-K-Z cubic forces z_t orthogonal to Pi; then rows agree outside the
  kernel columns and the deletion vectors have closed forms in (t, <y_a, y_b>).  Exact cross-check rows/r11/c21gk.py (chart m_0 = 1; heavy).
* Special two-column (2,1) kernels (R11.9): the line d = u (K = u^perp e_a + C u e_b; exact test chi3gen.py running) and finitely many isolated
  (u, d) pairs (still to do).
* Open: m_a = m_b = 0 (|supp m| = 3, verifyfl); three-column (2,1) kernels; five-column (PL) (big slot).

# HANDOVER-rows -- ROUND 10 ADDENDUM (22:50 UTC)
* Summed cubic = P_3 of the 4x5 matrix (R10.1).  PL4's ++++, ----, ++-- re-proved by EXACT linear algebra: 2 is not an eigenvalue of
  sum rho_3(B^0_j) on harmonic cubics (rows/r10/rank2.py) -- the template for a hand proof on five columns (eigenvalue 3 with an octahedral
  eigenvector; the 3-dim moduli make it a family problem; moment-matrix rank <= n is the other lead, R10.5).
* THEOREM CHI2 + uniqueness of strongly level extensions of type-I/II planes + PENCIL PRINCIPLE (R10.6): the (q,d) = (1,2) kernel stratum is
  settled for (4,1) (neutral column) and for (5,1) with rank c = 1.  Scripts rows/r10/chi2gen.py, extI.py, extII.py.
* Open on rows' side: the (2,1) kernel stratum (exists on 2 and 3 columns; two-column family explicit, R10.7; exact test needs a gauge for Z);
  column-centred (5,1) over these kernels; five-column (PL) (big slot runs, sq5big_*.out).

# HANDOVER-rows -- ROUND 9 ADDENDUM (22:05 UTC)
* Five columns (what is left of (PL), K version): degree-2 data = quaternion frame (R9.1), 6-dim per sign pattern (7 for ++++-), all six
  patterns exist; Lemma TR5 (traces depend on the kernel vector rho of the 4x5 frame) -- no single orbit, so the PL4 orbit trick does not
  transfer directly.
* KEY NEW CUT (R9.3): the SUMMED CUBIC sum_j c(B_j s) = (n-2) c(s) (c = x1x2x3, Walsh; = spin-3 identity sum rho_3(B_j) c = (n-2) c), 7
  equations, proved from the g-form of the cubic and checked on genuine spaces.  With degree 2 it is calibrated (3 columns ++- dim 1,
  --- dim 2) and already UNIT for 4 columns (----, ++--, 140 s, 0.13 GB).  Five columns: sq5runs.sh / sq5Qruns.sh (rows/r8/orb/),
  ----- reached 1.3 GB at 5 min locally; queue R9-SUMQ5.
* Numerics: degree 2 + cubic alone: 0/9 on five columns; degree 2 + summed cubic alone: 0/6 on 4 and 5 columns (3-column control 6/6).
* Division of labour proposed to verifyfl in NOTES-rows R9.0 (rows: principal stratum + strongly-level-kernel hand cases; verifyfl: typed
  (SL_m) systems).  CHI1 hand slip repaired by verify2 (flagged in R8.2).
* Next: if R9-SUMQ5 is unit at 3 primes / over Q, (PL) is done and NO PRINCIPAL (5,1) holds; then target the non-principal strata with
  verifyfl, and a representation-theoretic hand proof of the summed-cubic exclusion (sum eps_j Sym^6(g_j) f = (n-2) f with
  sum eps_j g_j (x) g_j = (n-2) Pi_sym + s Pi_alt).

# HANDOVER-rows -- ROUND 8 ADDENDUM (21:20 UTC)
* (T3) PROVED (Lemma O3, verified by verify2): every 3-column principal kernel has a column of rank <= 1 => with PR5 every principal (5,1)
  kernel lives on >= 4 columns; "no principal (5,1)" and NCOL-P3 need only (PL) in the K VERSION (3-dim K, s(K) = V), not the plane version.
* THEOREM PL4 (R8.10, hand + exact over Q): NO principal kernel on exactly four columns (all five sign patterns: +++-, +--- by hand;
  ++++, ----, ++-- by Lemma ORB = single O(3)-orbit + 9-unknown orbit test, rows/r8/orb/).  So principal kernels live on <= 3 or 5 columns;
  principal (5,1) kernels on 5 columns.  NEXT: the same frame method for FIVE columns (sum eps_j u_j u_j^T = 3 Omega Omega^T + c Q, five
  vectors in C^4: one linear relation; use the coordinator's ks5_* runs as data/backup).
* (superseded by PL4) (PL) K version, 4 active columns: Choi FRAME sum eps_j u_j u_j^T = 2 Omega Omega^T + c Q (R8.6); sign patterns +++- (R8.7, hand + tiny
  exact checks) and +--- (R8.8, degree 2) EXCLUDED; ++++, ++--, ---- remain, with forced traces tr A_j (Lemma TR) -> queue R8-Ksign
  (rows/r8/ksruns.sh; x4ks.py = sign-split X4K, deg <= 3 relaxation, trace equations).  5 active columns: six sign patterns, not analysed.
* Theorem CHI1 [exact over Q]: (4,1) with ker c = chi (x) C^M has two-column m (rows/r8/chi/chigen.py).
* Compute lessons: msolve segfaults under ulimit -v when its hash table grows (all B/B3 charts); calibrate positive-dim systems with random
  slices; Singular is slower but does not crash.  Plane charts (x4c2.py, c2/c3charts.sh) work but are heavy; the K-version route is preferred.
* Next hand targets: patterns ++++, ++--, ---- on 4 columns using the forced traces + cubic (octahedral structure: the cubic vanishes on the
  isotropic conic exactly at the six lines (0,1,+-i), ...); 5-column patterns; then non-principal (5,1) jointly with verifyfl's (SL_m).

# HANDOVER-rows -- ROUND 7 ADDENDUM (20:45 UTC, 23 Nov; Kevin's 24-core machine; workspace /home/kevxhk/work/L-gct-210)
New since the round-6 handover below (details: NOTES-rows.md section R7 and RESULT ROUND 7):
* THEOREM X5 [exact over Q]: no (5,1) space contains a strongly level K (s(K) = V) of column type (2,2,1), any m.  Scripts rows/r7/x5/
  (x5gen.py P CHART OUT [cal]; x5Q_*.out over Q; nfcheck.py; calpt10.py + x5cal10_point_4.npy = oracle-confirmed calibration point).
  Hand lemma inside: a 3-column K with a rank-one column is of type (1,1,1) or (2,2,1).  Needs verify2's re-derivation (one generator only).
* THEOREM PR5 [hand + exact over Q] (R7.4): a principal (5,1) kernel lives on >= 4 columns or on 3 columns with all column ranks >= 2.
  Hence "no principal (5,1)" <= (PL) + (T3).  Scripts rows/r7/rep/x51r.py (types (3), (2,1); 'cal' = N a line).
* C REDESIGN (coordinator's Singular C died of memory): rows/r7/x4c2.py generic-h charts (C 21, B 15, B3 10 charts; verified against
  direct coefficients), driver rows/r7/c2charts.sh; queued R7-C2, R7-B3cal, R7-B2; cheap cut R7-C1 (S_5 = cone over a curve near the
  known point; C <=> P(S_5) has a line component).  Local tests: one old B chart > 5 min; k3 (K version, 3 columns) > 10 min.
* THEOREM DC' / NC'-DC' (R7.2): the exact identities use rank(s|ker c) and rank(kappa|ker rho); (DC-COST') is the exact form of (NC'_e).
* R6-1 (R7.1): B and C both needed for (PL); A4 non-unit is now certain numerically (S_4 = 4-dim cone); B is "lines on the 3-fold P(S_4)";
  the plain formulation is too heavy (one msolve chart > 5 min; Singular std silent ~1 h).  Queued: R7-B-charts (rows/r7/bcharts.sh, 126 charts
  up to column symmetry), R7-X4K (rows/r7/t3/kruns.sh: K version for 4 / 5 active columns, 3-column calibration, plus T3 = "every 3-column K
  has a column of rank <= 1", which closes the type list for P51 + X5).
* Updated ranked open list: (0) read the R7-C2 / R7-B2 / R7-B3cal / R7-C1 results; (1) (PL) via those, or by hand (structure: pi_ab := y_a * y_b is orthogonal to the other two
  columns; Gram pattern g01 = g23 etc.; quartic alpha^2+beta^2+gamma^2 = 6 Pi); (2) DONE by PR5 (repeated entries included); (3) T3 (closes principal (5,1) together with (PL)); (4) non-principal
  (5,1) (column-centred, and ker c strongly level of row-sum rank < 3); (5) (DC-COST') for e = 1 with a neutral column.
* STATUS lines in NOTES-rows.md from 20:12 to 20:26 were written a few minutes ahead of the real UTC clock (corrected in later lines).

# HANDOVER-rows — the defect inequality (DI_5) for L-gct-210   (written 20:33, 23 Nov; role "rows", rounds 1–6)

Paths are relative to this workspace (`cloud/L-gct-210/` on the fork branch `coord-L-gct-210`). My notes: `NOTES-rows.md`
(RESULT blocks of rounds 6..1 at the top, then sections D, S, D', DI, R3, R4, R5, R6). My code and data: `rows/`.

## 1. Role and question
L-gct-210: is every linear space L of complex 5x5 matrices with perm(J + t) = 120 on L ("level space") of dimension <= 8?
(Largest known: 7. No 8-dim level space is known.) My branch is the DEFECT NORMAL FORM. For a 4x5 matrix Y put
c(Y)_j := perm(J + Y without column j) − 24; a 4x5 space L' is level if sum_j c(Y)_j = 0 on L'; C(L') := span{c(Y)} (inside 1^perp of C^5),
e := dim C(L'); "(d,e) space" = d-dim 4x5 level space with defect dimension e; EXTREMAL = (e+3, e).
Lift: L' (rows != r) + e_r (x) (C(L') + C1)^perp is a 5x5 level space of dim d + 4 − e, and every level space with a deletable row
arises inside such a lift. **(DI_5): d <= e + 3**, i.e. no (5,1), (6,2), (7,3) space. It says "a level space with a deletable
line has dim <= 7"; stage2 (z = 3) and reg2 (a_r >= 2) reduce to it. Column n of L' is NEUTRAL if c(Y)_n = 0 on L'.
Notation used below: c(Y), s(Y) = column / row sums; V = 1^perp in C^4; K strongly level = c(Y) = 0 on K (then dim K <= 3, Lean-checked
Lemma SL); N = L' cap ker s; X_n = single-column elements in column n; U_i = single-row elements in row i; W = (C + C1)^perp.

## 2. Results
### PROVED (hand proofs; "V2" = re-derived by verify2, see NOTES-verify2.md)
| result | where | status |
|---|---|---|
| Defect construction (lift; converse; dim <= d + 4 − e) | sec. D | used and re-derived by stage2 (Z3), verifyfl |
| DI_3: 2 x q level space has dim <= e + 1; Lemma D (Rado): p x q space with sum_j prod_i (1+x_ij) = q has dim <= q − 1; DDI; deletion formulas I1–I3; Prop. O; Cor. H (single-row part <= e, two-row part <= e+1); Lemma B'; Lemma TC | sec. DI | V2 |
| Lemma SL_3: a 3x5 space all of whose 3x4 column deletions are level has dim <= 2 | R3.8 | V2 |
| Theorem FL2*: level L containing e_i(x)U + e_r(x)U', U cap U' = 0, has dim <= 10 − dim(U o U') | R3.9 | V2 |
| From checked L_gct_215: 3x5 level <= e+3; dim(L cap {row r = 0}) <= 7; (8,3),(8,4),(9,4) excluded | R3.1 | V2 |
| Hyperplane Lemma: if no (e'+4,e') for e' < e, every hyperplane of an (e+4,e) space is extremal with the SAME C | R4.1 | V2 |
| U_i in C, U_i perp U_k, u_i + u_k <= e+1; RS-HYP (generic hyperplane of a minimal (e+4,e) space is not fully row-split) | R4.2, R4.3 | V2 |
| Lifting Lemma; D-UP ((D)_d => (D)_{d+1}, so (D) <=> (D)_7); C-UP | R4.7 | V2 |
| Transposed defect construction for a neutral column: L' = (Q|x), dim L' <= dim Q + 3 − e^col(Q); padding lemma | R4.10 | V2 |
| Theorem NCOL-S: defect line Cm, <m,m> != 0, e_i m^T in L', m without zero entry => dim L' <= 3 | R4.14 | V2 |
| (F1) c^(i)(Y).u = 0, c^(i)(Y) o u in C; (F2) U_i o U_k in C; (FS-DEC); (F1^T) | R4.15 | V2 |
| Theorem DC: dim L' = rank c + rank s + dim L'_dc; NC'-DC slack identity dim L' = e + 3 + delta − s1 − s2 − s3 | R5.2 | not yet verified |
| (SC1): for x e_n^T in L': <x, s(Y) − y_n> = 0 and (<x,y_j>)_{j != n} in C cap e_n^perp | R5.6 | not yet verified |
| **Theorem NCOL-P3**: defect line Cm (any m), K in L' strongly level 3-dim, s(K) = V, K on columns a,b,c, some Z with s(Z) = 0, c(Z) != 0 => m_a m_b m_c = 0 | R5.9 (contains R5.7) | not yet verified |
| **Theorem P51**: m with 5 distinct entries: no (5,1) space containing such a K that is spanned by single-column elements or lives on two columns | R5.11 | not yet verified |
| (R-LAW) for kernels spanned by single-column elements: rows of every Z in N lie in C; Prop. NCOL2-P (needs hypothesis (G)) | R5.12, R5.13 | not yet verified |
| (NCOL_3) + (DI_4x4) + no (5,1) + no (6,2) => no (7,3)  [erratum: R5.3(b) omitted the last two hypotheses] | R5.3, R6.3 | erratum by verify2 |
| X4 reduces to strongly level PLANES (PL); row-wise form of "strongly level" | R6.1, R6.2 | not verified; (S4) formula unchecked |

### EXACT / MODULAR
* Exact (integer / rational arithmetic): free-line-free 7-dim level spaces L_m and the second-kind space (`rows/exact7.py`, `exact7b.py`);
  identities I1–I3 (`di_ident.py`); FL2 toolbox (`fl2_ident.py`).
* Modular: none of mine finished. The calibration A4 of R6-1 did not finish in 100 s here (Singular std; msolve with localisation).

### NUMERICAL (complex LM, `rows/clm.py`; "found" = residual < 1e-9, fresh-point check)
* Existence: (4,1), (5,2), (6,3) found often; (5,1): 0/52 unseeded + 0/38 seeded; (6,2): 0/37; (7,3): 0/24; no 7-dim 4x5 level space.
  With one neutral column: (5,1) 0/8 [(4,1) 5/11], (6,2) 0/15 [(5,2) 3/5], dim 7 0/25 [dim 6 7/29]; two neutral: dim 6 0/22 [dim 5 12/25].
* **(NCOL)**: every extremal space has a neutral column: 87/87 mine + 33/33 seven-dim spaces of other agents; (6,3) with defect space
  fixed generic 0/46 vs control 4/19; block pattern (3,2) 0/30.
* Double tower: L = Q + [column n: 3 − e^col(Q)] + [row r: 4 − e^row(Q)], dim Q = e^row(Q) + e^col(Q) in all extremal examples;
  Q (4x4) again has a deletable line (120/120).
* 4x4 (via zero-column padding): (5,1) 0/14 [(4,1) 9/17]; (6,2) 0/15 [(5,2) 2/10]; any 6-dim 4x4 level space 0/15.
* Principal census: in 90 of 95 extremal spaces ker c is a strongly level 3-space with s = V; it always lives on <= 3 columns
  (types by column ranks (1,1,1), (2,1), (3), (3,2), (2,2,1)); also 49/49 fresh strongly level 3-spaces, 128/128 with a forced zero column,
  169/169 strongly level planes with injective row sums.
* (R-LAW): rows of N lie in C in 90/90 principal extremal spaces. (LAW) C = sum U_i + two-column part: 68/68. All 28 principal (4,1) are split.
* Slack census: delta = 0 in 126 of 135 tower positions; delta > 0 always paid exactly by s3 or s1; s2 = 0 always.

### REFUTED / DEAD (do not retry)
* "Extremal spaces are fully row-split": false (15 of 68). "dim(L'/{y_a = y_b}) <= 1" (EQ induction): false on all (6,3) tested.
* "Column-centred 4x5 level spaces have dim <= 3": false (dim 4 exists). "dim L <= e_row(L) + e_col(L)": false (padded circ(1,i,−i,−1)).
* "Every 7-dim level space contains a full free line": false (L_m). Round-1 target (A) (degenerate 4x5 spaces <= 4): false.
* "A strongly level MATRIX has <= 3 nonzero columns": false (4 columns common; `rows/sle5_s1005.npy` has 5). The true statement is about planes.
* (PRIN) "extremal with rank c = e => ker c strongly level": false for `rows/clm_p4_d5_defect2_s9.npy`.
* Row-centred 4x4 space with one-dimensional defect has dim <= 3: false for two-column defect lines (1 hit of 34).
* Hypothesis (G) of R5.13 fails for all known defect planes. Black-box use of L_gct_214/216/217 does not give (DC-COST).

## 3. OPEN, ranked by promise
1. **(PL) / X4: a strongly level plane with injective row sums has <= 3 nonzero columns.** Makes NCOL-P3 unconditional for every (4,1)
   whose ker c is strongly level with s = V. Next step: run R6-1 (cases B, C) on the 24-core machine; by hand, use R6.2 (three columns:
   pairwise orthogonal + one cubic; four columns: Gram pattern g_12 = g_34 etc., all triple products 0, one quartic). Effort: minutes
   of machine time if the Groebner basis terminates; otherwise 1–2 days by hand.
2. **Principal (5,1), remaining strata.** After TC5, PR3 (verifyfl), VF-A [modular] and P51: (i) kernel type (2,2,1) (exact system X5);
   (ii) kernel types (1,1,1), (2,1), (3), (3,2) with m having one zero and a REPEATED nonzero entry, e.g. (1,2,−4,1,0), (1,1,−1,−1,0),
   (1,1,1,−3,0). Approach for (ii): in P51's proof the cubic c(X) no longer vanishes identically; for x in X_n it gives
   <x,E_2(a)> = −3 mu <x,E_3(a)> (mu = the repeated value) plus one more linear relation; add the second-order cross terms. Each stratum is
   a small exact ideal (N = a (x) m is rank one). Effort: hours.
3. **My best idea — principal normal form for all e.** With (PL) and (R-LAW) an extremal principal space is L' = K + N, K one of five explicit
   types on <= 3 columns, N an e-dim subspace of C^4 (x) C mapped isomorphically onto C by column sums. Prove (R-LAW) type by type (it is
   equivalent to sum_j w_j <z_j, h_j> = 0 for h in K, w in C^perp; for single-column kernels it is R5.12; for two-column kernels start from
   the identity <z_d + z_e + z_f, h_a o h'_b + h_b o h'_a> = 0 obtained from the K-K-Z part of the cubic). Then (NCOL_e) and the exclusion of
   (e+4,e) in the principal strata become finite lists of small ideals indexed by (kernel type, e): unknowns = parameters of K, a basis of C,
   and N inside C^4 (x) C. For e = 1 this is exactly how NCOL-P3 and P51 were found. Effort: days; high value because it covers 90 of 95
   known extremal spaces.
4. **Non-principal strata.** (4,1): column-centred spaces (two-column m: exist) and ker c strongly level of row-sum rank < 3 (zeros' types,
   missed by LM). verifyfl's (SL_m) and its typed systems [DC3], [T22], [T31] cover dim 4 column-centred spaces. For e >= 2 the five
   non-principal extremal examples (kc_chk.py lists them) are the models to understand first.
5. **(NC'_e) = (DC-COST): delta <= s1 + s2 + s3** (R5.2). Needs the classification of doubly centred 4x4 level spaces (X1, Walsh
   coordinates, <= 18 unknowns) and then "each doubly centred direction is paid". The 4x4 statement (DI_4x4) (X3) is a sub-case.
6. **(NCOL_2), (NCOL_3) outside the principal normal form**: only (FS-DEC) (e = 3 row-carried defect: block sizes (4,1) or (3,2), X2) and R5.13.
7. **(D)_7**: every 7-dim level space has a deletable line (then (D) holds in all dimensions by D-UP). Only numerics (H5).

## 4. Pitfalls
* LM solutions on singular components are accurate only to ~1e-7 as subspaces: ranks decided at 1e-5 produce artefacts ("e^col = 4",
  "no deletable line", spurious single-row elements). Re-polish or use absolute thresholds; treat (n1, n2) column counts at 1e-3 / 1e-8.
* `clm.Problem` samples N = 140 points: too few for d >= 7 (COMPUTE-ERRATA A5). My d = 7 negatives stay valid (fewer constraints), hits would not.
* LM misses non-generic components (zeros' strongly level spaces of row-sum rank 1): a negative is evidence only with a positive control of the same kind.
* All pairings are BILINEAR (no conjugation); numpy SVD null vectors must be conjugated (`vh[r:].conj()`).
* "Principal" in my notes = ker c is a strongly level 3-space with s = V (then (DI_5) is automatic); verifyfl's "principal (5,1)" = ker c
  CONTAINS such a space. P51 is about the latter.
* `seeded.py` overwrites `seed_dD_eE_tT.npy`; `build7.build` mishandles e = 0; scripts insert an absolute `sys.path` (run without `-I` elsewhere).
* Unit ideal mod p is evidence, not proof; use >= 3 primes, coordinate charts and a non-unit calibration. One chart suffices in R6-1 because
  row permutations act on Walsh coordinates by signed permutations.
* STATUS time stamps in NOTES-rows.md are a few minutes ahead of the real clock in places. 

## 5. Files
Notes: `NOTES-rows.md` — D (defect construction), DI (round 2), R3, R4 (R4.1 hyperplane, R4.7 lifting, R4.8 NCOL, R4.10 transposed, R4.14–15),
R5 (R5.2 DC, R5.6 SC1, R5.9 NCOL-P3, R5.11 P51, R5.12 R-LAW), R6. Compute requests: `COMPUTE-rows.md`.
Scripts in `rows/` (numpy only; 2–8 s per LM start on one core):
* `clm.py` solver (modes level / deg / defect); `run_clm.py p d mode e s0 s1 tmax`; `seeded.py 'PAT' e_old d e ntrials tmax`.
* Searches: `nc_search.py d k s0 s1 tmax` (k neutral columns); `ncdef_search.py d e k s0 s1 tmax`; `fixC_search.py d e s0 s1 tmax [1|b32]`;
  `q44_search.py d e s0 s1 tmax [save] [cc]` (4x4 via padding); `cc_search.py`; `sle_chk.py d s0 s1 tmax`, `sl3col_chk.py`, `sl44_chk.py` (strongly level).
* Checks on saved spaces (`'PATTERN'` arguments, seconds each): `ext_chk.py` (neutral columns, deletable rows), `ncol_ext.py` (7-dim 5x5 spaces),
  `q44_chk.py` (tower laws), `slack_chk.py`, `kc_chk.py` (principal?), `tower_chk.py`, `rlaw_chk.py`, `sc1_chk.py`, `uiuk_chk.py`,
  `ncol1_chk.py`, `ncolp_chk.py`, `ncolp3_chk.py`, `sym_chk.py`, `r4_census.py`.
* Exact: `exact7.py`, `exact7b.py`, `di_ident.py`, `fl2_ident.py`. Groebner generator: `gb/x4gen.py P CASE OUT [CHART]`.
Data in `rows/`: extremal spaces `clm_p4_d{4,5,6}_defect{1,2,3}_s*.npy`, `seed_d*_e*_t*.npy`, `c52_*.npy`, `nc_d*_k*_s*.npy`, `ncdef_*.npy`;
4x4: `q44*_d*_e*_s*.npy`; strongly level: `sl3_s*.npy`, `sle_d{1,2}_s*.npy`, `sle5_s1005.npy`; column-centred: `cc_d*_s*.npy`.

## 6. Pending compute tasks (full specs in COMPUTE-rows.md)
| task | what | decision rule |
|---|---|---|
| R6-1 (first) | strongly level planes: cases B (4 columns), C (5 columns); calibrations A4, B3 must be non-unit | B and C unit at >= 3 primes => (PL) [modular] => NCOL-P3 unconditional for principal (4,1). Non-unit => send a point: new kind of plane |
| X5 | principal (5,1), kernel type (2,2,1) | unit => that stratum is empty |
| X4 | original 3-dim formulation (36 unknowns) | superseded by R6-1 |
| X1 | all doubly centred 4x4 level spaces of dim 1, 2, 3 (Walsh, Gr(k,9)) | list of components; input for (DC-COST) |
| X2 | (6,3) with one row carrying C = V_{012} + V_{34} | non-unit => (NCOL_3) false; unit => (NCOL_3) for row-carried defect |
| X3 | row-centred 4-dim 4x4 space with defect line not two-column | unit => no 4x4 (5,1) => step towards (DI_4x4) |
| H1 | LM: (5,1), (6,2), (7,3), unseeded / neutral column / seeded, >= 20 000 starts, raise N for d = 7 | any oracle-confirmed hit refutes (DI_5) and gives an 8-dim level space |
| H2, H3, H3b | census of 6-/7-dim 4x5 spaces; (NCOL), tower laws, (R-LAW) on fresh extremal spaces | one confirmed violation refutes the law; send the file |
| H4 | 4x4: (5,1), (6,2), any dim 6 | hit refutes (DI_4x4) |
| H5 | 7- and 8-dim 5x5 level spaces; deletable lines | a 7-dim space without deletable line refutes (D)_7 |

## Addendum, rounds 20-21 (rows; 06:20-07:25 UTC)
- *** (SM4) IS FALSE *** (NOTES R21.3; rows/r21/cex4.py; verified exactly over Q(sqrt3, i) by verify2).  Rank-2 counterexample on the
  Walsh coordinate plane x3 = 0 (kappa vanishes there): y1 = ((s+1)/2, -i(s-1)/2, 0), y2 = ((1-s)/2, i(s+1)/2, 0), y3 = (1/2, i/2, 0),
  y4 = -y3, s = sqrt 3; f = (1, i, 0).  (SM4'') (no P_4, any f) fails with real points.  All SM4 jobs dropped; PL4 unaffected (own proof).
- Corrected chain R21.6: |S_0| = 4 leaf-3 cases need direct proofs (remaining: support-4 G plane in char 0; R16P2z3); |S_0| = 5 cases
  follow from (SM5), which is still open but SETTLED IN RANK <= 2 (R21.5: rank 1 by hand, nondegenerate plane via rows/r21/r2c.py).
- Case-G pencils: none inside the coordinate-plane family (R21.4, hand).  The family does contain non-G IS3 pencils.
- REAL trick (R21.7): x_2 -> i x_2 makes the conic rational and every condition (power of i) x (rational); rows/r21/planeG.py (REAL, FAM,
  LAG, STAGED), rows/r21/realify.py (post-processor for existing Q(i) .sing files: realsplit() per generator, parity check printed).
  Case-G plane mod P1: 14 s / 45 MB (was 30 s / 0.07 GB).  REAL files for the big-slot Q(i) jobs: rows/r21/*R*.sing (and *_p.sing mod P1).
- Rank-2 generators: rows/r21/smfull.py (permanent-based (SM_n), RANK2/PLANE/GRAPH options; slow), rows/r21/r2c.py (rational, fast).
- Lesson: the main-chart numerics (y1, y2, y3 a basis) were blind to the rank-2 component; always enumerate the degenerate charts first.
- (round 22) Case G proved by hand (R21.8: ka-coefficient chain C_T = 0 -> B_kk = 0 -> K(c(s_k),u,u) = 0 at 4 distinct points, impossible).
  (SM5) proved in rank <= 2 in char 0 (R21.10).  G4-A: hand chain gives l = 0 (R21.9), case (b) excluded by hand (R21.9''), cases (a1-a3)
  UNIT mod P1, Q runs g4c_a*.sing in progress (log rows/r21/kPG.out).  P2-z3 REAL over Q: rows/r21/bq5R_P2_z3.sing (log kR2C.out).
  Open: R4, R5 planes (no hand chain; general 5-column identity R21.11), (SM5) rank 3, R16P2A.
- (round 22, 07:58) G4-A CLOSED (R21.9''''; exact certificate rows/r21/g4acert.py).  W5/SP5 can never be unit (R21.12, cex5relax.py):
  (SM5) needs P_4; rank-3 triage files rows/r21/w5r3_*.sing.  Still running at hand-off: bq5R_P2_z3.sing over Q (PID 768245, verdict line
  appended to rows/r21/kR2C.out by watchP2z3.sh; raw output bq5R_P2_z3.out); REAL validations bq5R_P2_A_p, pl5R_R4_p, pl5R_R5_p,
  smcR5_p (rows/r21/kPG.out).
- STOPPED 08:04 UTC (L-gct-210 aborted).  All rows jobs/watchers killed (bq5R_P2_z3 over Q stopped without verdict after 32 min).
  Final state: NOTES-rows.md "FINAL STATE" + RESULT ROUNDS 21-22.  Leaf 3 open pieces: P2-z3, and (SM5) rank 3 or R4 + R5 + P2-A.
  Unpursued idea: (Z5) (zero row sum, 5 nonzero columns) would kill R4/R5/P5/S23 at once (NOTES R23.0).
