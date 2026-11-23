# HANDOVER-reg2 (written 20:45, 23 Nov 2026) -- regime "some row or column projection of dimension <= 3" of L-gct-210

Workspace = cloud/L-gct-210/ on the fork branch coord-L-gct-210. Full notes: NOTES-reg2.md (RESULT blocks at top; sections 1-8).
Heavy-compute spec: COMPUTE-reg2.md (sections 0, 3b, 6, 7 are current). Scripts and data: reg2/ and reg2/gb/.

## 1. Role and question
L-gct-210: every linear space L of 5x5 complex matrices with perm(J + t) = 120 on L ("level") has dim <= 8. For a hypothetical 9-dim L
and a row r put W_r = row-r projection of L, a_r = 5 - dim W_r (>= 1), L_r = L cap {row r = 0}: a level space of 4x5 matrices of
dimension 4 + a_r. My regime: some a_r >= 2 (rows; columns by transposition), i.e. L_r is a 4x5 level space M of dimension 6 or 7
(dim <= 7 is Lean-checked upstream, Outside/L_gct_215). Goal: show no 9-dim L has such a row. Status: NOT closed; reduced to one
statement about 6-dim 4x5 level spaces, (S6-FO2) below, proved on several explicit families and supported by about 250 spaces.

Notation used everywhere: J' = 4x5 all-ones; N_j(X) = perm_4(X without column j); F = sum_j N_j (M level <=> F(J'+Y) = 120 on M);
C(M) = span{N(J'+Y) - 24*1} (defect space, e = dim); M is embedded in 5x5 with zero row r (r = 4 in all scripts);
T_1(M) = {t : sum t_ij cof_ij(J + (Y;0)) = 0 for all Y in M} (contains every level space containing M);
Omega(M) = row-r projection of T_1(M);  E_0(M) = {X 4x5 : (X;0) in T_1(M)};  dim T_1 = dim E_0 + dim Omega;
FO2 bound(M) = dim T_1(M) - ceil(rank/2), rank = rank on T_1(M) of a form q_Y = D^2 perm(J + (Y;0)), Y in M (stage2's Lemma FO2);
single-row part of row i: U_i = {w : e_i w^T in M}; "full free row" = U_i is all sum-zero vectors (dim 4).

## 2. Results

### 2.1 PROVED by hand (rigorous)
P1  CRITERION A (NOTES-reg2 section 1, L1-L4; VERIFIED by verify2). tau_r = J - 5 e_r 1^T lies in T_1(M) for every level M, so the
    all-ones vector is in Omega(M); W_r lies in Omega(L_r) and never contains the all-ones vector (a zero row gives perm = 0). Hence
    for every level L and row r:  dim L = dim L_r + dim W_r <= dim L_r + dim Omega(L_r) - 1.  Also dim Omega = (4 - e) + g, 1 <= g <= e+1.
P2  (section 1, L5; verified) Phi(Y) := N(Y) for Y in L_r is orthogonal to the row-r projection of CJ + L: for a_r = 2, Phi(L_r) lies
    on one line C k and the row-r projection of CJ + L is k^perp. Omega(M) is orthogonal to Phi(M).
P3  (L3; verified) <s,N(X)> = (sum s) F(X) - D_{X D_s} F(X). So Omega(M) = {s : Y -> D_{Y D_s}F(J'+Y) on M equals some Y -> D_X F(J'+Y)}:
    infinitesimal column scalings that keep M level to first order up to a translation. Euler form (D1)-(D4) in L3.
P4  (section 5.1 = stage2's (Z3)) for every row i of a level L: L_i is a 4x5 level space with C(L_i) inside U_i^perp cap 1^perp, and
    dim L = dim L_i + dim W_i <= dim L_i + 4. In a 9-dim L every L_i has type (dim, defect) = (4 + a_i, <= 4 - dim U_i).
P5  THEOREM SP8 (section 5.2, written 20:08; NOT yet re-derived by verify2). Let L be a level space of 5x5 matrices containing
    e_i (x) U, U = {w in C^5 : sum w = 0, <m,w> = 0} (dim 3), m a nonzero sum-zero vector. If (a) m = e_a - e_b, or (b) <m,m> != 0
    (bilinear) and L contains e_i' m^T for some row i' != i, then dim L_i <= 4 and dim L <= 8.
    Proof: by P4, L_i is level with defect inside C m. (a) verifyfl's Theorem TC5 (a 4x5 space with defect line inside C(e_a - e_b)
    has dim <= 4; verified by verify2). (b) e_i' m^T is in L_i; defect 0: Lemma SL (dim <= 3, verified); defect line C m: verifyfl's
    Theorem SPLIT (NOTES-verifyfl R3.1: split, non-isotropic => dim <= 4; I do not know whether verify2 re-derived SPLIT). Then P4.
    Consequence: L_r can never be a member of the families M*_1, M*_2, a single "EC move" of a Type F space, or a DR3 space with its
    split element (section 2.3 below) -- for all parameters, no computation.
P6  (section 8.1; (b) noted by verify2) (a) FO2 bound(M) <= dim T_1(M) - 1 for every M: q_0 = D^2 perm(J) = 12 P_2 and P_2(tau_r) = -200.
    So dim T_1(M) <= 9 implies: every level space containing M has dim <= 8.
    (b) (S6-FO2) + Theorem FL exclude a_r = 2 AND a_r = 3: take a 6-dim subspace M_6 of L_r; if it contains a full free row, FL gives
    dim L <= 7; otherwise FO2 bound(M_6) <= 8 and L contains M_6.
P7  LEMMA DL / PROP MAX (sections 7.1-7.3; not yet verified). Row i deletable (the 3x5 projection is level) <=> d_i = (e_i - 1/4)(x)1 in
    E_0(M). Column c neutral (N_c(J'+Y) = 24 on M) => d^c = 1 (x) (e_c - 1/5) in E_0(M). P_2(d_i + Y) = -15/2, P_2(d^c + Y) = -24/5.
    So a level M with a deletable row or neutral column and dim E_0 = dim M + 1 is a maximal 4x5 level space. A 7-dim 4x5 level space
    has no full free row (rows), no two equal columns (upstream eI), and each 6-dim subspace with a deletable row / neutral column has
    dim E_0 >= 8.
P8  (new, not in the notes) a level 4x5 space with an identically zero column c has that column neutral: with f(s) = perm_4(J_4 + s Y^(c)),
    level + Euler give 5 f(s) - s f'(s) = 120, hence f = 24.
P9  Level proofs of the exact families (hand): NC family (section 2.5), M* (section 4.3; VERIFIED by verify2), pattern (2,2|2)
    (section 8.3 (i): P_1, P_2 force the shape; level for all parameters is an exact expansion, see E2).

### 2.2 EXACT (char 0, Singular) / MODULAR (msolve) -- all with every chart and a non-unit calibration; scripts reg2/gb/
E1  NC family M(w0,w1,w3) = {x e_0^T : sum x = 0} + C e_0 (0,w0)^T + C e_1 (0,w1)^T + C e_3 (0,w3)^T, w_i in C^4 sum-zero, pairwise
    orthogonal, sum_c w0_c w1_c w3_c = 0 (pattern (1,1,1|3)): for EVERY member Omega = span(1,e_0), E_0 = M + C d^0, dim T_1 = 9.
    [EXACT over Q: 85 unit ideals; also mod 65521, 2147483629, 1073741789.]  => dim L <= 7 if L_r = M; <= 8 if L contains M.
E2  Pattern (2,2|2): M(mu) = e_0 (x) U_0 + e_1 (x) U_1 + V (x) e_0, U_0 = {w_0 = 0, sum w = 0, <mu,w> = 0}, U_1 = span(5e_0 - 1,
    (0,mu) - mean), V = {x_1 = 0, sum x = 0}; chart mu = (0,1,m3,m4). [EXACT] level for every mu; E_0 = M + C d_1 for every mu;
    Omega = span(1,e_0) unless m3, m4 in {0,1} (elimination ideal (m3^2-m3, m4^2-m4) in all four rho-charts); at the four 0/1 members
    exact certificates: dim T_1 = 10, dim Omega = 3, rank q = 4, bound 8. So (S6-FO2) holds on the whole pattern.
E3  Pattern (2,1,1|2), incidence case (iii) (V = {x_1 = 0}, row 1: 5e_0 - 1, row 2: (0, mu - mean_4), row 0: U_0 as in E2):
    [EXACT] level for every mu, Omega = span(1,e_0) and E_0 = M + C d_1 for EVERY mu (no special members). gen_dr211.py.
    Case (ii) (V = {x_0 = 0}; rows 1, 2: (0,b), (0,c); row 0: span(5e_0 - 1, (0,a)); a, b, c pairwise orthogonal sum-zero):
    [EXACT] the level conditions are the P_2 relations plus sum a_j b_j c_j = 0; calibration non-unit in the five charts.
    WARNING, UNDECIDED: the Omega-test over Q (finished at 20:32, only its last lines were kept) is NON-UNIT in chart (1,2,3) for
    rho_2 = 1, rho_3 = 1, rho_4 = 1 (basis sizes 123-124): some members -- possibly all -- of this family have Omega NOT inside
    span(1,e_0). Their (dim T_1, dim Omega, FO2) are UNKNOWN: this is the first thing to compute (task T1). Case (i) (isotropic) not done.
E4  Exact certificates in Fractions (reg2/exact_T1.py, exact_fo2.py, mstar2_fo2.py, dr22_exact.py): M*_1 for (x,y) = ((1,-1,0),(1,1,-2)),
    ((2,-1,-1),(0,1,-1)), ((1,2,-3),(5,-4,-1)) and M*_2: dim ker 11, Omega inside (e_1-e_2)^perp, rank 5, bound 8;
    Type F parent "free row + {x e_4^T}": 12, Omega = C^5, rank 6, bound 9; L080 row-0 kernel and one NC member: dim ker 9.

### 2.3 NUMERICAL (LM / SVD; relative rank tolerance 1e-4 on LM output)
N1  Taxonomy of 6-dim 4x5 level spaces (about 250 found by five differently biased searches), invariants (dim Omega, dim T_1, FO2):
    F   full free row + 2-dim part, e = 4: (3,10,8) [rc45] or (5,12,9) [line-kernels of L080, ex2, ex3, fam2, s-family];
    NC  exactly one neutral column c, e = 3, Omega = span(1,e_c): (2,9,7) [all 19 files of rows, their sparse limits];
    DR2 deletable row with 2-dim free part, e = 4, no neutral column: (2,9,7); special members (3,10,8);
    DR3 deletable row with 3-dim free part U = {1,m}^perp and split element e_i' m^T: (3,10,8) for 3-column m;
    M*  = EC move of a Type F space: M*_1(x,y) = e_3 (x) {sum w = 0, w_1 = w_2} + C x e_0^T + C y e_3^T + C e_2 (e_1-e_2)^T
        (x, y in C^3 on rows 0-2, sums 0, <x,y> = 0), M*_2 the same with {x e_4^T : sum x = 0}: (4,11,8), Phi = 0. 54 single moves all
        (4,11,8); 15 double moves all (3,10,8). Chain F -> one move -> two moves: Omega 5,4,3; T_1 12,11,10; FO2 9,8,8.
    In everything found: FO2 = 9 <=> full free row. Every space has a deletable row or neutral column and dim E_0 = 7.
N2  No 7-dim 4x5 level space: extension search through 45 known 3-,4-,5-dim spaces 0/132 (N = 330 sample points: borderline, errata A5).
N3  No 8-dim 5x5 level space through M* (0/82, 6 unknowns), the special (2,2|2) members (0/40 each), DR3 spaces, rc45 (0/12 each);
    7-dim level spaces through each of them exist (same code: 4-9 of 10-12 starts).
N4  EMPIRICAL LAW (EL) (section 7.5): for 6-dim M and each row i with U_i != 0: Omega(M) lies in A(U_i) = {s : U_i o s in U_i + C1}
    (55 rows of 29 spaces, 0 violations, equality in 47).
N5  FILTER for regime 1 (section 6): a row with a_r = 1 needs Phi = 0 on L_r and Omega(L_r) = C^5. Generic hyperplanes of the Type F
    spaces with Omega = C^5 pass (and have FO2 = 9); they contain a 3-dim piece of a free row with a generic line m, so by P4 they are
    candidates exactly if a (5,1) space with that line exists. Hyperplanes of M* fail the filter or are excluded by SP8.

### 2.4 REFUTED / DEAD (do not retry)
D1  "Every 6-dim 4x5 level space contains a full free row or column": FALSE (NC, DR, M* families).
D2  (S6') "no full free row => dim Omega <= 2" and its weak form "<= 3": FALSE (M*: dim Omega = 4). The first-order criterion alone
    cannot close the regime. The dichotomy "Type F or Type NC" is FALSE (DR2, DR3, M*).
D3  "Omega(M) is a subalgebra of C^5 (spanned by indicators of a column partition)": false in general (4-dim spaces with defect
    line m have Omega = m^perp); true on every 6-dim space seen.
D4  (EL) as a formal consequence of "e_i w^T in M": FALSE (fails on a 3-dim subspace of a (2,2|2)-type space; lemA_test.py).
D5  Sub-configurations of M* (split pair alone, split pair + one column element) have FO2 >= 10: only the full 6-dim space has 8;
    FO2 alone never excludes the Type F spaces with Omega = C^5 (bound 9) -- FL is needed; rows' FL2* gives only 9 for two-column m.
D6  Lemma C-type zero-block pigeonholes in the regime only reproduce chief's Type I' (section 1, L6).
D7  Upstream L_gct_215 contains NO structure statement for 6- or 7-dim spaces (case tree for dim 8 only; its 7-dim lemmas are all
    under the equal-columns hypothesis). Useful general tool there: d + r_i <= p_ij + p_ik + u_l (aBu).
D8  Unseeded LM on Gr(6,20) with rows/clm.py at 300 iterations: 0 of 10; do not trust its negatives.

## 3. OPEN, ranked by promise
O1  (S6-FO2): every 6-dim 4x5 level space without a full free row has FO2 bound <= 8. With FL this closes a_r >= 2 (P6). By P6(a) it
    suffices to show dim T_1 <= 9, or (10, rank >= 3), or (11, rank >= 5).
    MY BEST IDEA: do not classify all 6-dim spaces; work inside the regime, where M = L_r satisfies much more than level:
    k^perp (dim 4) lies in Omega(M), and exactly: for every rho in k^perp, perm[A(rho) + Y ; rho] = 120 lambda(rho)^5 for Y in M
    (A linear), i.e. M D_rho^{-1} is level at the base point A(rho) D_rho^{-1} for a 4-dim LINEAR family of column scalings.
    Step 1: prove (EL) for such M from this exact family (first order on subspaces is not enough, D4; the identity to exploit is
    perm[pi_i(J+Y) ; w o rho] = sum_k perm[pi_i(J+Y) with row k replaced by X_k - rho - Y_k o rho ; w] of section 7.5).
    Step 2: (EL) + "Omega contains k^perp" force every single-row part of L outside row r to be 0, C k, k^perp cap 1^perp or everything, with
    k = e_a - e_b; the last two are dead (SP8(a), FL). Step 3: with k = e_a - e_b all of CJ + L has equal entries (r,a), (r,b), and
    the L_i have two-column defect: verifyfl's symmetrised normal form (DI5.2) and TC5 machinery apply. Step 4: the case with no
    single-row element outside row r: transposed argument on the neutral column (P4 for columns). Effort: several days; Step 1 is the crux.
O2  STRUCTURE: every 6-dim 4x5 level space has a deletable row or a neutral column, and dim E_0 = 7. Gives O1 family by family, and
    "4x5 level <= 6" (P7). Approach: the spaces are defect extensions of extremal smaller spaces (3x5 of type (4,2), (3,1), (2,0);
    4x4 of dim 5, 4, 3 with row-defect 2, 1, 0): prove that an extremal 4x5 space has a row meeting it only in its single-row part
    or a zero-defect column, by upstream's case tree on (u_i, p_ij) with P4 in each case. Effort: large (weeks) by hand; the exact
    line-spanned classification (task X1) is the first finite piece (hours on 24 cores).
O3  NO TWIST: for NC and DR2 spaces Omega = span(1,e_c) (then dim T_1 = 9). Structural proof via L2: all defect vectors p_k(Y) must be
    weighted column sums of relations among the gradient spans G_0..G_3; or per family exactly as in E1-E3. Effort: hours per family.
O4  DR3 with isotropic or non-split m: none found; by P4 it needs "no (5,1) space with line C m" (verifyfl's open case).
O5  8-dim level spaces: none known; exact solve of "M* + 2-plane in T_1(M*)/M* level" (task X2) would settle it for M*. Minutes.
O6  Regime 1: use FILTER N5 on every candidate L_r; survivors reduce to (5,1) via P4.

## 4. Pitfalls
- LM solutions are often reached by singular convergence: residual 1e-12 but the space only 1e-6 accurate. Decide ranks with relative
  tolerance 1e-4..1e-5 or round to the sparse limit (reg2/a5.py rref_tol) and re-check level error; I misread types twice.
- ext6.classify knows only F / NC / OTHER; always print (dim Omega, dim T_1, FO2).
- FO2 uses the BILINEAR restriction of the Hessian (not hermitian); stage2/r5_FO2.py is correct.
- Sample counts: a quartic in v variables needs >= C(v+4,4) points (330 for 7 variables); ext7.py uses exactly 330: raise to >= 400.
- "Unit ideal mod p" is evidence; E1-E3 were also run over Q. Elimination ideals describe the closure of the projection: a member
  outside the zero set has no solution, a member inside must be checked separately (done for the four 0/1 members of E2).
- Normalisations in the exact tests must be valid on the whole chart (E3 needs two normalisations, valid for S != 0 and S != 4).
- gen_nc.py prints "ALL CHARTS UNIT" also in calibration mode: ignore that line there; calibration lines must say unit=False.
- mstar2_fo2.py and ecmove.py run their main code on import (exact_fo2.py, ecmove3.py print it first).
- All scripts insert absolute paths /home/claude/work/L-gct-210/{reg2,reg2/gb,stage2,chief} into sys.path and read ../rows/*.npy:
  run from reg2/ (or reg2/gb/) and adapt the prefix; polylib.py hard-codes /home/claude/tools/gb/msolve and Singular.

## 5. Files
Notes: NOTES-reg2.md: RESULT ROUND 2 and RESULT (round 1) at top; section 1 rigorous lemmas L1-L6; 2 data and NC family; 3 superseded;
4 DR families, M*, EC moves, exact certificates; 5 SP8 and status table; 6 FILTER; 7 Lemma DL, MAX, 7-dim, upstream tree, (EL);
8 exact results. COMPUTE-reg2.md: definitions (0), censuses (1-3b), exact items (4), 8-dim (5), decisions (6), round-2 tasks (7).
Scripts in reg2/ (python3 -I, numpy only, each < 3 min):
  t.py, a1.py, a5.py, a6.py, a9.py   helpers: level_err, rowpart/colpart, defect, T1, E0, Omega, rref_tol
  a10.py, a12.py, a13.py             line-kernels of the seven 7-dim spaces; maximality table (no arguments; ~30 s)
  chk_lemma.py                       sanity of P1-P3 on 70 lines (20 s)
  ext6.py SEED TMAX; ext6c.py SEED TMAX sub|ker; ext5.py SEED TMAX; ext7.py SEED TMAX   extension censuses to dim 6 / 5 / 7
  linespan.py SEED TMAX              census of spaces spanned by single-row / single-column elements (45 patterns, 150 s)
  drsearch.py U SEED TMAX            M = e_3 (x) U + N with dim U = U (found DR3, M*)
  ecmove.py, ecmove2.py, ecmove3.py  EC moves of Type F spaces and their invariants (seconds)
  ext55.py M SEED files; ext55b.py M SEED NSTARTS files   level spaces M + m-plane inside T_1(M) (m = 1: dim 7; 2: dim 8; 3: dim 9)
  exact_T1.py, exact_fo2.py, mstar2.py, mstar2_fo2.py, dr22_exact.py   exact certificates in Fractions (seconds)
  fam_nc.py, fam_nc2.py, dr22_num.py numerical members of the exact families;  autest.py (EL);  lemA_test.py;  pfr_chk.py;  filter1.py
  gb/polylib.py, gb/famtool.py       exact polynomial arithmetic, msolve / Singular runners, class Family (level + FO equations)
  gb/gen_nc.py P [cal|e0|e0cal]      E1 (P = prime, 0 = Q); 4-25 s
  gb/gen_dr22.py P lev|cal|om|e0|elim J   E2; seconds.   gb/gen_dr211.py P lev|cal|elim|e0   E3 case (iii); seconds
  gb/gen_dr211b.py P lev|cal|om      E3 case (ii); "0 om" runs 20 Singular jobs over Q in 2 min (result: non-unit charts, see E3 WARNING)
  dr211b_num.py                      numerical invariants of random members of that family (written at handover, NOT run)
Data in reg2/: Mstar2.npy (rational M*_1), M_L080_col0.npy, M_ex2_row4.npy (Type F, Omega = C^5), dr_u3_*.npy (DR3),
  ec_*.npy, ec2_*.npy (EC moves), linespan_other_*.npy (DR2), dr22_special_*.npy, ext_*.npy (NC), cand7 (none).

## 6. Pending compute tasks and decision rules
T1  FIRST: pattern (2,1,1|2) case (ii) (see E3 WARNING). (a) `python3 -I dr211b_num.py` in reg2/ (written at handover, NOT run, 10 s):
    invariants of six random members. (b) `python3 -I gen_dr211b.py PRIME om` in reg2/gb/ for three primes (the script prints every
    chart; over Q it needs 2 minutes), then the elimination ideal in (a,b,c) of each non-unit chart. Decision: generic members with
    dim T_1 = 9 and non-unit charts only on a proper sub-locus => treat the special members as in E2 (v); members WITHOUT full free
    row (none of this family has one) with FO2 bound >= 9 => genuine candidate L_r: run ext55b.py with m = 3 and m = 2 at once.
T2  Task X1 of COMPUTE-reg2.md section 7: the remaining line-spanned patterns (3|3), (3|2,1), (3|1,1,1), (2,1|3), (2,1|2,1),
    (2,1|1,1,1), (1,1,1|2,1), (2,1,1|2) case (i), (3,1|2) and (3,1|1,1) with isotropic m, and existence in the other patterns.
    Decision: a member without full free row with bound >= 9 is a genuine candidate L_r -> run ext55b.py with m = 3 (a solution with
    fresh level error < 1e-10 REFUTES the gap) and m = 2 (an 8-dim level space, new object). Otherwise (S6-FO2) holds on the pattern.
T3  Censuses A, B, E of COMPUTE-reg2.md (sections 1, 2, 3b; REG2-C in local/STATUS.md is queued): for each 6-dim solution report
    (dim Omega, dim T_1, rank q, bound), deletable rows, neutral columns, dim E_0, and the (EL) test (X3). Wanted: no full free row and
    bound >= 9; no deletable row and no neutral column; dim E_0 >= 8; a violation of (EL); any 7-dim 4x5 level space (N >= 400).
T4  X2: exact solve of the 8-dim extensions of M* (2-planes in the 5-dim T_1(M*)/M*): unit ideal in the 10 Pluecker charts => M* lies
    in no 8-dim level space; a solution => first 8-dim level space.
T5  verify2: re-derive SP8 (P5), Lemma DL / MAX (P7), P8, and the pattern analysis 8.3 (i).
