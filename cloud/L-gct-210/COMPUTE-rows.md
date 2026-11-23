# COMPUTE-rows — heavy computations that would most help (DI_5)   (written by "rows", 19:40)

Self-contained. Conventions are those of `handoff/oracle.py` (use it to validate every hit).

## 0. Definitions (everything over C; J = all-ones matrix; indices 0-based as in the scripts)

* perm = permanent. For a p x q matrix A with p <= q:  N(A) := sum over all p-subsets T of the columns of perm(A[:,T]);
  for p > q transpose.
* 5x5 level space: linear space L of 5x5 matrices with perm(J + t) = 120 for all t in L.
* 4x5 level space: linear space L' of 4x5 matrices with N(J + Y) = 120 for all Y in L'.
  Equivalent polynomial identities: P_k(Y) = 0 for k = 1..4, where P_k(Y) := sum of the permanents of all k x k submatrices of Y.
* Deletion vector of a 4x5 matrix Y:  c(Y)_j := perm(J + Y^(j)) - 24, Y^(j) = Y without column j (j = 0..4).
  L' is level iff sum_j c(Y)_j = 0 on L'.  Homogeneous parts: p_k(Y)_j = (4-k)! * P_k(Y^(j)), k = 1..4; p_1(Y) = -6 * (column sums of Y) on a level space.
* Defect space C(L') := span{ c(Y) : Y in L' } = span{ p_k(Y) } (a subspace of 1^perp in C^5), e := dim C(L').
  "(d,e) space" := 4x5 level space of dimension d with defect dimension e.   EXTREMAL := d = e + 3.
* Lift: L(L') := L' (placed in the rows != r) (+) e_r (x) (C(L') + C*1)^perp  is a 5x5 level space of dimension d + 4 - e.
* (DI_5): every (d,e) space has d <= e + 3.  Equivalent: there is NO (5,1), NO (6,2), NO (7,3) space.
  [(4,0) is excluded by the Lean-checked Lemma SL; (8,.) by the checked bound "4x5 level => dim <= 7".]
  A (5,1), (6,2) or (7,3) space lifts to an 8-dim 5x5 level space; none is known (the largest known 5x5 level spaces have dim 7).
* Column n of L' is NEUTRAL if c(Y)_n = 0 for all Y in L' (i.e. L' minus column n is a 4x4 level space: perm(J4 + q) = 24).
  (NCOL): every extremal (e+3,e) space, e = 1,2,3, has a neutral column.   [120 of 120 known spaces.]
  (NC'):  a 4x5 level space with a neutral column has d <= e + 3.          (DI_5) follows from (NCOL) + (NC')  [rigorous reduction].
* 4x4 level space Q: perm(J4 + q) = 24 on Q.  Row-deletion vector M(q)_i := N(J + q without row i) (3x4), sum_i M_i = 96;
  e^col(Q) := dim span{M(q) - 24*1}.  Column-deletion vector R(q)_j := N(J + q without column j); e^row(Q) := dim span{R(q) - 24*1}.
  (DI_4x4): dim Q <= e^col(Q) + 3, i.e. no 4x4 level space with (dim, e^col) = (5,1) or (6,2).  [(4,0) is excluded rigorously.]
  Padding: (Q^T | 0) is a 4x5 level space with a zero column and defect dimension e^col(Q); so (DI_4x4) is (DI_5) for spaces with a zero column.
  Rigorous: (NCOL_3) + (DI_4x4) => no (7,3).

## 1. The solver (numpy only)

All scripts are in `/home/claude/work/L-gct-210/rows/`. Copy the whole directory; every script does
`sys.path.insert(0,'/home/claude/work/L-gct-210/rows')` in its first line — change that path (or run from the directory WITHOUT `python3 -I`).
Core: `clm.py` (no other dependency).  `run_clm.py` and `seeded.py` also import `rect.py` (same directory).

`clm.Problem(p, d, mode, e, seed)`: the unknown is a d-dim subspace of C^(p x 5), in the Grassmannian chart [I_d W] * Pi (Pi = random unitary
fixed by the seed). Residuals are evaluated at N = 140 random unit vectors of the coefficient space (holomorphic, so polynomial identities on
the space <=> all residuals 0):  mode 'level': P_1..P_p;  mode 'defect' (p = 4): sum_j p_k(Y)_j (k = 1..4) and the components of p_k(Y)
outside an UNKNOWN e-dim subspace of 1^perp (chart [I_e T]); so 'defect e' finds (d, e') spaces with e' <= e.
`clm.solve(P, iters=250)` = complex Levenberg-Marquardt with analytic Jacobian, returns (z, residual norm); `P.basis(z)` has shape (d,p,5).
HIT := residual < 1e-9 and cond(basis) < 1e6.  One start costs 2-8 s on one core (numpy single thread: set OMP_NUM_THREADS=1 and run one
process per core with disjoint seed ranges).  Near misses: keep every start ending with residual < 1e-5; restart them with iters=2000
(singular solutions converge only linearly and stall near 1e-7..1e-10; they still count if the oracle confirms them after polishing in
higher precision, e.g. mpmath Newton on the same residuals).
Every hit: run `handoff/oracle.py file.npy` -> prints (d,e), level error, dimension and level error of the lift.

## 2. Tasks (in order of value)

### H1 — the decisive existence searches (would refute (DI_5) and give an 8-dim 5x5 level space)
 Unseeded, command `python3 run_clm.py 4 D defect E S0 S1 TMAX` (saves `clm_p4_dD_defectE_sSEED.npy` for hits):
   targets      (D,E) = (5,1), (6,2), (7,3)                — at least 20 000 starts each;
   calibrations (D,E) = (4,1), (5,2), (6,3)                — 500 starts each FIRST; they must give hits (in my runs of a few dozen
                                                              starts: 10, 3 and 3 hits; exact rates not recorded). Report the rates.
 With one neutral column (smaller target if (NCOL) is true), command `python3 ncdef_search.py D E 1 S0 S1 TMAX`:
   targets (5,1), (6,2), (7,3) — 20 000 starts each;  calibrations (4,1): 5 of 11, (5,2): 3 of 5, (6,3) — here.
 Seeded at known extremal spaces (all files `clm_p4_d*_defect*_s*.npy`, `seed_d*_e*_t*.npy`, `c52_*.npy`, `nc_d*_k*_s*.npy`, `ncdef_*.npy`):
   (run it in a fresh working directory: it writes seed_dD_eE_tTRIAL.npy and would overwrite existing files of that name)
   `python3 seeded.py 'PATTERN' E_OLD D E NTRIALS TMAX`, e.g. `seeded.py 'clm_p4_d4_defect1_s*.npy' 1 5 1 2000 36000`
   (starts from a known (D-1, E_OLD) space plus a random extra vector); pairs (E_OLD -> D,E): (1 -> 5,1), (2 -> 6,2), (3 -> 7,3), (1 -> 5,2)
   as calibration [seeding (5,2) at (4,1) spaces produced 15 hits here].  If `describe` (rect.py) fails for some input, delete that print.
 DECISION: any oracle-confirmed hit of a target = counterexample to (DI_5); lift it (oracle prints the lift) -> 8-dim level space: STOP and
   report the .npy.  No hit: record (#starts, calibration rate); this is evidence, not proof.

### H2 — 6- and 7-dimensional 4x5 level spaces (census; decides whether (7,3) is vacuous)
 `python3 run_clm.py 4 7 level 0 S0 S1 TMAX` (20 000 starts; calibration `4 6 level 0`, several hundred starts, rate to be reported).
 For every 6-dim hit print (d,e) (oracle), neutral columns and deletable rows: `python3 ext_chk.py 'clm_p4_d6_level0_s*.npy'`
 (ext_chk prints the table (d,e,#deletable rows,#neutral columns) for extremal spaces; modify the line `if d!=e+3: continue` to see all).
 DECISION: a 7-dim 4x5 level space would be new (upstream bound is 7, none known); a 6-dim space with e <= 2 refutes (DI_5);
   a 6-dim space with e = 3 and no neutral column refutes (NCOL_3). Expected: every 6-dim 4x5 level space is (6,3) with exactly one neutral
   column or (6,4).

### H3 — independent large-scale test of (NCOL) and of the tower laws on FRESH extremal spaces
 Generate >= 2000 hits in each class with `run_clm.py 4 4 defect 1`, `4 5 defect 2`, `4 6 defect 3` (and plain `4 D level 0`, D = 4,5,6),
 then run on all saved files:
   `python3 ext_chk.py 'PATTERNS'`      -> count of extremal spaces "without deletable line" must be 0; table of #neutral columns;
   `python3 q44_chk.py 'PATTERNS'`      -> laws  e^row(Q) = e,  dim X_n = 3 - e^col(Q),  dim Q = e^row(Q) + e^col(Q)  (flagged "VIOLATION" otherwise;
                                           LM-limited files with singular values ~1e-6 at the rank cut are artefacts — re-polish them first);
   `python3 slack_chk.py 'PATTERNS'`    -> dim Q_dc and the three slacks; the identity column must be True;
   `python3 kc_chk.py 'PATTERNS'`       -> is ker(column sums) a strongly level 3-space (principal case)? (90 of 95 here);
   `python3 tower_chk.py 'PATTERNS'`    -> does Q have a deletable row or column again (yes in all cases here);
   `python3 r4_census.py`               -> single-row parts, (LAW) C = sum U_i + two-column part (edit the patterns in __main__).
 Direct test with the defect space FIXED: `python3 fixC_search.py 6 3 S0 S1 TMAX` (generic 3-dim C0: 0 of 46 here) against the control
 `python3 fixC_search.py 6 3 S0 S1 TMAX 1` (C0 = e_0^perp cap 1^perp: 4 of 19 here): >= 5000 starts for the test.
 DECISION: one confirmed extremal space without neutral column refutes (NCOL) — send it. Otherwise report the tables.

### H4 — the 4x4 defect problem (decides (7,3) given (NCOL_3); also the base of all double towers)
 Numerical: `python3 q44_search.py D E S0 S1 TMAX save` searches 4x5 level spaces with column 4 identically zero and defect dim <= E,
 i.e. (Q^T | 0) with dim Q = D, e^col(Q) <= E.
   targets (5,1), (6,2), (6,3) [= any 6-dim 4x4 level space; upstream bound is 6, none found: 0 of 15] — 20 000 starts each;
   calibrations (4,1): 9 of 17, (5,2): 2 of 10 here.
 Centred variant (add the word `cc`): Q row-centred.  (3,1): 14 of 16;  (4,1): 1 of 34, and that hit has the TWO-COLUMN defect line e_0 - e_1.
   Claim to test: a row-centred 4x4 level space of dim 4 with e^col <= 1 has a two-column defect line (two-column lines are excluded
   at dim 5 by the proved Theorem TC5). Run `q44_search.py 4 1 S0 S1 TMAX cc save` with 20 000 starts and print the defect line of every hit.
 Exact (Groebner / msolve / numerical irreducible decomposition), smallest useful systems:
   (X1) Doubly centred 4x4 level spaces. Walsh coordinates: H = [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]; a doubly centred 4x4 matrix is
        t = H x H^T with x a 3x3 matrix. A linear space S of 3x3 matrices gives a doubly centred LEVEL space iff identically on S:
        sum_ab x_ab^2 = 0,  perm_3(x) = 0,  perm_4(H x H^T) = 0   (checked upstream: then dim S <= 3).
        Wanted: ALL S of dimension 1, 2, 3 (points of the level variety in P^8; Gr(2,9): 14 unknowns; Gr(3,9): 18 unknowns), as a list of
        irreducible components up to row/column permutations and transposition of t, each with a generic point; and for each the two
        vectors M^(2)(t)_i = -2 <row_i, row_i>, R^(2)(t)_j = -2 <col_j, col_j> and whether ALL row- and column-deletion vectors are
        constant ("doubly strongly level", e.g. t = circ(1, i, -i, -1)).  Why: by my Theorem NC'-DC, dim L' <= e + 3 + dim Q_dc -
        (slacks), so (NC') is exactly a statement about the doubly centred elements of Q.
   (X2) FS-type (6,3) spaces with block pattern (3,2) (decides (NCOL_3) when one row carries the defect). Fix A = {0,1,2}, B = {3,4},
        C = {u in C^5 : u_0+u_1+u_2 = 0, u_3+u_4 = 0}. Unknown: a 3-dim space N of 4x5 matrices such that for all Y in N:
        (i) row 0 of Y = -(sum of rows 1,2,3 of Y) and lies in span{(1,1,1,0,0),(0,0,0,1,1)};  (ii) c(Y) = 0 (all five 4x4 deletion
        permanents equal 24);  (iii) D(Y)u lies in C for all u in C, where D(Y) is the symmetric 5x5 matrix with
        D_jk := perm_3((J+Y) without row 0 and without columns j,k) for j != k and D_jj := 0.   Then L' = N (+) e_0 (x) C is a (6,3) space WITHOUT neutral column. Wanted: existence (numerically: Gr(3,12)
        inside the 12-dim linear space cut out by (i); positive control: the same with A = {0,1,2,3}, B = {4}, where solutions exist).
   (X3) (5,1) for 4x4, reduced: row-centred 4x4 matrices = 4 rows in V = 1^perp of C^4 (12-dim space R). Unknown: a 4-dim subspace S of R and
        a vector mu in 1^perp of C^4, NOT of the form e_a - e_b, with: perm(J + t) = 24 and M(t) in 24*1 + C*mu for all t in S.
        If no such S exists, there is no 4x4 level space with (dim, e^col) = (5,1) [because the row-sum map has rank <= e^col].

   (X4) Principal strongly level 3-spaces. V := 1^perp in C^4 with the standard bilinear form. Unknown: linear maps A_0..A_4 : V -> V with
        sum_j A_j = id such that K := { h(sigma) = (A_0 sigma | ... | A_4 sigma) : sigma in V } (a 3-dim space of 4x5 matrices with row-sum
        vector sigma) is strongly level: c(h(sigma)) = 0 for all sigma (i.e. all five 4x4 deletion permanents of J + h(sigma) equal 24;
        the quadratic part says exactly that B_j := id - 2A_j are isometries of V). 45 - 9 unknowns, polynomial identities of degree 2,3,4
        in sigma. Wanted: the list of all solutions up to row/column permutations, and in particular whether ALWAYS at least two of the
        A_j vanish (K lives on <= 3 columns; true in 90 of 90 numerical examples, types by column ranks (1,1,1), (2,1), (3), (3,2), (2,2,1)).
        Why: my Theorem NCOL-P3 proves (NCOL_1) for every (4,1) space whose kernel of the column-sum map is such a K on <= 3 columns.
        Numerical version: `python3 run_clm.py 4 3 defect 0 S0 S1 TMAX` (strongly level 3-spaces; hits are frequent), keep those with
        row-sum rank 3, and count the zero columns of each (e.g. with the column-rank lines of rows/nc_look.py).

   (X5) Principal (5,1) spaces, kernel type (2,2,1) (the only observed kernel type not covered by my Theorem P51). Data: v in V non-isotropic,
        R a rotation of the plane v^perp (inside V) with isotropic eigenvector n, R n = lam n; K = C v e_c^T + {((1-R)y/2 at column a,
        (1+R)y/2 at column b) : y in v^perp}; m with m_c = 0 and lam = (m_a+m_b)/(m_a-m_b). Candidates for the row-centred part:
        N = {a m^T + t n (e_a - e_b)^T}, a = (kappa/4)1 + phi v + eta n, t = 2 m_a m_b eta/(m_a - m_b), kappa^2 = (4/3) phi^2 <v,v>.
        Question: can K (+) N (N of dim 2) be level with all deletion vectors in 24*1 + C m (and K strongly level, which needs
        sum_i (h_a)_i (h_b)_i (h_c)_i = 0 on K)? Small exact system in (v, R, m, phi, eta); a "no" removes this type.

### H3b — test of (R-LAW) at scale
 For every fresh extremal space with ker(column sums) a strongly level 3-space (kc_chk.py): are all rows of all elements of
 N = L' cap {row sums = 0} in the defect space C?  `python3 rlaw_chk.py 'PATTERNS'` prints, per (e, principal?, kernel type), the maximal
 relative distance of those rows from C and lists every violation in a principal space (90 of 90 principal spaces satisfy it here).

### H5 — (D)_7 and dimension 8 for 5x5 directly
 `python3 run_clm.py 5 7 level 0 S0 S1 TMAX` (census of 7-dim 5x5 level spaces; report the hit rate) and `python3 run_clm.py 5 8 level 0 ...`
 (20 000 starts; decisive for "no 8-dim level space" at the usual uncertified level; the 7-dim run is its calibration).
 For every 7-dim hit: `python3 ncol_ext.py 'clm_p5_d7_level0_s*.npy'` prints, per space, the (d,e,#deletable rows,#neutral columns) of the rest after
 deleting its deletable line, and the list "no deletable line" (two LM-limited files needed the rank cut 1e-3 instead of 1e-5 in `proj`).
 DECISION: a confirmed 7-dim level space with NO deletable row/column refutes conjecture (D)_7 (and (D)); a deletable line whose rest has no
   neutral line of the other kind refutes (NCOL). By my lifting lemma (D)_7 implies (D) in all dimensions >= 7.

### H6 — exact certificates for the positive side (lower priority)
 Recognise exactly (algebraic numbers) one space of each extremal type: (4,1) with 1, 2, 3 neutral columns; (5,2) with u-type (1,1,0,0),
 (2,0,0,0), (0,0,0,0); (6,3) FS-type and column-type; and verify perm(J + t) = 120 symbolically on the lifts. Known exact examples:
 rows/exact7.py, rows/exact7b.py.

## NEW (round 6) — queue these first (written 20:22)

### R6-1 (replaces X4 by a much smaller system): strongly level planes live on <= 3 columns
 REDUCTION (rigorous, rows NOTES R6.1): a principal K (3-dim strongly level, s(K) = 1^perp) with >= 4 nonzero columns contains a 2-dim
 strongly level subspace with the SAME nonzero columns on which the row-sum map s is injective; and a space with 5 nonzero columns
 contains a single strongly level matrix with 5 nonzero columns. So X4 follows from the two claims
   (A) [FALSE as stated, found 20:27: rows/sle5_s1005.npy is a strongly level matrix with five nonzero columns, error 2e-16;
       so five columns need the PLANE version, case C of the generator: planes with five nonzero columns and independent row sums]
       there is no strongly level 4x5 MATRIX with five nonzero columns   (15 unknowns, 15 homogeneous equations of degree 2,3,4);
   (B) there is no strongly level PLANE {s h + t h'} with column 4 identically zero, the other four columns nonzero, and s(h), s(h')
       linearly independent   (20 unknowns after normalising the row sums to (1,0,u), (0,1,v) in Walsh coordinates; 33 equations).
 ("strongly level": c(Y) = 0 for every Y of the space, i.e. all five 4x4 deletion permanents of J + Y equal 24.)
 Walsh coordinates: a column with zero sum is sum_p x_p chi_p, chi_1 = (1,1,-1,-1), chi_2 = (1,-1,1,-1), chi_3 = (1,-1,-1,1).
 The chart in (B) is enough: the row permutations act on the Walsh coordinates by all signed permutations with an even number of signs,
 so every plane of row sums can be moved to one whose projection to the first two Walsh coordinates is bijective.
 Generator (pure Python, writes a Singular script and, with a 4th argument, an msolve file with Rabinowitsch localisations):
   `python3 rows/gb/x4gen.py P CASE OUT [CHART]`,  CASE in {A, A4, B, B3, C}  (see the header of the file):
     A  = claim (A);   A4 = one matrix with four nonzero columns (CALIBRATION: must be NON-unit, such matrices exist numerically);
     B  = claim (B);   B3 = the same with three nonzero columns (CALIBRATION: must be NON-unit: kernel types (1,1,1), (2,2,1));
     C  = planes with five nonzero columns (only needed if (A) is not the unit ideal).
   The Singular script computes std(I) and then saturates successively by the column ideals (sat from elim.lib) and prints
   "RESULT case .. : 1" if the saturated ideal is the unit ideal.  CHART = one character per active column: a digit k (the k-th
   coordinate of that column is inverted), r (a pseudo-random linear combination is inverted), - (no condition); output OUT.ms.
 Here (2 shared cores) std(I) for A4 did not finish in 100 s, neither in Singular nor in msolve with CHART rrrr; so run A, A4, B, B3 on
 the 24-core machine at >= 3 primes (e.g. 2147483629, 2147483497, 2147483077).  DECISION (corrected): B unit and C unit, with the calibrations A4, B3 (and A) non-unit
 => every principal K lives on <= 3 columns [modular], which makes Theorem NCOL-P3 unconditional for principal (4,1) spaces.
 If B is NOT unit: send the primary decomposition / a point (it would be a new kind of strongly level plane).

## 3. What to send back
 For each task: number of starts, hit rate of the calibration, hit rate of the target, the .npy of every target hit or law violation
 (with oracle output), and the tables printed by the checking scripts.
