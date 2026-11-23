# COMPUTE-stage2 — heavy computations that would most help the regime REG1   (written by "stage2", 19:35)

Self-contained. Everything over C. J = all-ones 5x5 matrix, J' = all-ones 4x5 matrix. Indices 0-based as in the scripts.

## 0. Definitions

* perm = permanent. 5x5 LEVEL SPACE: linear space L of 5x5 matrices with perm(J + t) = 120 for all t in L.
* For a 4x5 matrix Y:  G(Y)_j := perm(Y without column j)  (j = 0..4; five 4x4 permanents),  N(Y) := sum_j G(Y)_j.
  4x5 LEVEL SPACE: linear X with N(J' + xi) = 120 on X.
* REG1: a 9-dim 5x5 level space L in which every row and every column projection of L is 4-dimensional.
  L_r := {t in L : row r = 0} (dim 5), viewed as 4x5 matrices (rows != r).  Z_i := {w : e_i w^T in L}, z_i := dim Z_i (single-row part).
* (Q-r)  [necessary for X = L_r, every row r with 4-dim projection; rigorous]: X is a 5-dim linear space of 4x5 matrices with
    (i)   N(J' + xi) = 120 for all xi in X;
    (ii)  G(xi) = 0 for all xi in X  (all five column-deletion 4x4 permanents vanish identically);
    (iii) every ROW projection of X has dim <= 3; every COLUMN projection (in C^4) has dim <= 3, except possibly ONE column c
          (the case "entry (r,c) vanishes identically on L"), where only <= 4 holds  [exception found by verify2].
* BLOCK TYPE (s,t): X vanishes identically on an s x t block of cells. (ii) holds automatically if s + t >= 6:
  (1,5) zero row; (2,4) two rows supported in one common column; (3,3) three rows supported in two common columns;
  (4,2) two zero columns. CROSS: supported on one row and one column. NON-BLOCK solution: (i),(ii) hold and no such block exists.
* FIRST/SECOND ORDER TESTS for a linear subspace M of a 5x5 level space L (here M = X placed in rows 1..4, row 0 = 0):
    T_1(M) := {t in C^(5x5) : sum_ij t_ij * perm((J+m) without row i, column j) = 0 for all m in M}       (L lies in T_1(M));
    q_m(t,t') := sum over i != k, j != l of t_ij t'_kl * perm((J+m) without rows i,k and columns j,l)       (symmetric BILINEAR form);
    FO2 bound(M) := dim T_1(M) - ceil(rank(q restricted to T_1(M)) / 2), q a generic linear combination of q_m, m in M.
  Every level space containing M has dimension <= FO2 bound(M).  [Lemma FO2, verified by verify2.]
* (T2) for a candidate X = L_r: unknown T_0..T_4 in C^(4x5);  D_T G_j(xi) := derivative of G_j at xi in direction T.
    (T2): D_{T_k} G_j(xi) + D_{T_j} G_k(xi) = 0 for all j <= k and all xi in X;   solvable := some solution has sum_k T_k in J' + X.
  Necessary for X = L_r (order 2 at v = 0 of chief's identity <v, G(T(v) + xi)> = 120 <kappa,v>^5).  Linear in T.
* A candidate X is DEAD if FO2 bound <= 8 or (T2) is not solvable; ALIVE otherwise.  So far: 49 verified solutions, all of block
  type; alive: only solutions with a 3-dim single-row or single-column part (cross spaces on two special loci, two (3,3) solutions).

## 1. Scripts (numpy + scipy only; directory /home/claude/work/L-gct-210/stage2/)

Copy the whole directory. The scripts `exec` each other through ABSOLUTE paths and were run as `python3 -I`; on another machine
replace the prefix once:  `sed -i 's#/home/claude/work/L-gct-210/stage2#NEWDIR#g; s#/home/claude/work/L-gct-210/chief#NEWCHIEF#g' *.py`
(chief/core.py is only needed by the sanity scripts). Outputs are written to /tmp.  One process per core, disjoint seeds.
* `r6_census.py SEED NTR MAXIT [DM]` — LM (scipy least_squares, numerical Jacobian) for (Q-r)(i),(ii) with every row of rank <= 3
  (rows parametrised as U_i V_i; DM = four digits = maximal row ranks, default 3333). Residuals at 50 + 28 random points; EVERY
  solution is re-checked at 80 fresh points (a quartic in 5 variables has 70 coefficients — raise NL, NG to 140, 80 on the big machine).
  Prints row/column projection dims, single-row/column dims, largest zero block, dim T_1, rank, FO2 bound; saves
  `/tmp/r6_census_SEED_TRIAL.npy` (array (5,4,5) = basis of X).  One start = 15-30 s here; about 30% of the starts converge.
* `r6_fk.py KIND SEED NTR MAXIT` — the same inside a block family, KIND in {24, 33, 15, 42}; only (i) remains. Rates here:
  24: 20 of 28 starts; 33: 15 of 20; 15: 1 of 5; 42: 0 of 6.  Saves only solutions with FO2 bound >= 9 (`/tmp/r6_fk_KIND_SEED_TRIAL.npy`).
* `r5_FO2.py` — function `FO2(Mb, rg)` (Mb = list/array of 5x5 matrices spanning M) -> (dim T_1, rank, bound). Running the file
  prints the sanity table on the 7 known spaces (bound must be >= dim L; it is 7 for the six 7-dim spaces).
* `r6_T2.py` — function `T2test(B, rg)` (B = (5,4,5) basis) -> (dim of the solution space, distance of J' from {sum_k T_k} + X);
  distance < 1e-9 = solvable. `r6_T2_sanity.py` = sanity on the known spaces.
* `r6_extend.py FILE1,FILE2,.. D NTRIAL` — direct LM search for a level space of dimension D containing a saved X (inside T_1(X)).
* `r6_cross.py` (cross family, formula for T_1), `r6_lam5.py` (case lam = 5), `r5_FO_Mstar.py` (exact certificate for M*).

## 2. Tasks (in order of value)

### S1 — (Q-r) census at scale, with calibration
 Run `r6_census.py SEED 40 400` for at least 5000 seeds (after raising NL, NG) and `r6_fk.py KIND SEED 40 400` for KIND = 24, 33, 15, 42,
 1000 seeds each.  CALIBRATION FIRST: 200 seeds of `r6_fk.py 24` and `r6_fk.py 33` must reproduce the rates above (about 70%) and
 the table: (2,4): (dim T_1, rank, bound) = (9,3,7) mostly, sometimes (12,7,8), (8,3,6); (3,3): z = 2 -> (10,5,7), z = 3 -> bound 8 or 9.
 Near misses (final residual < 1e-5): restart with MAXIT 3000 (singular solutions converge linearly).
 For every verified solution record: block type, row/column projection dims, z (single-row dims), z' (single-column dims),
 dim T_1, rank, FO2 bound, (T2) distance, and for ALIVE solutions the result of `r6_extend.py` with D = 8 and D = 9 (20 starts each).
 DECISION: (a) an ALIVE solution with all z, z' <= 2 = a candidate L_r that the present tests do not exclude: send the .npy (it is
 the next thing to exclude, or the seed of a construction); (b) a solution for which `r6_extend.py` with D = 8 or 9 converges
 (residual < 1e-9, confirm with exact/high precision) = an 8- or 9-dim level space: STOP and report; (c) none: evidence for
 "every (Q-r) solution with z, z' <= 2 is dead", the statement that would exclude every 9-dim level space with z <= 2 on a
 full-projection line.

### S2 — non-block solutions of (ii)
 Question: is there a 5-dim X with (i), (ii), (iii) that does NOT vanish on any s x t block with s + t >= 6?  (In the fully generic regime
 the L_r would have to be of this kind; their absence re-proves "no minimal pair" there.)  The plain census finds block solutions
 only. Two ways:
 (a) numerical: in `r6_census.py` add to the residual a repulsion from the block loci (e.g. require the 20 "cell norms"
     n_ij := sum over the basis of |B[k,i,j]|^2 to be >= 0.05 by a slack parametrisation n_ij = 0.05 + w_ij^2), 20 000 starts;
     also the same with dim X = 4 and 3 as calibration (non-block solutions of (ii) alone exist: rows 0,1 = (x,y,0,0,0), (-x,y,0,0,0),
     rows 2,3 supported on the last three columns — a level 5-dim subspace of that 8-dim space is a legitimate non-block candidate;
     search inside it separately: 5-dim level subspaces of {(x,y; -x,y) (+) two rows on columns 2,3,4}).
 (b) exact (Macaulay2 / Singular / msolve / Bertini): chart of Gr(5,20): X = rowspace[I_5 | W], W a 5x15 matrix of unknowns after a
     random permutation of the 20 cells; equations = all coefficients (in the 5 parameters c) of G_j(sum c_k B_k) (5 quartics, 70
     coefficients each) and of N(J' + sum c_k B_k) - 120 (126 coefficients). Wanted: the irreducible components (numerical irreducible
     decomposition is enough), their dimensions, and for a generic point of each: block type, z, z', FO2 bound, (T2).
     Smaller exact warm-up with the same structure: all 2-dim spaces of 3x5 matrices on which the ten 3x3 subpermanents vanish
     identically and P_1 = P_2 = 0 (the plane X_{rr'} of a minimal pair): Gr(2,15), 40 cubic + 5 low-degree coefficient equations.
 DECISION: a non-block component with z, z' <= 2 and FO2 bound >= 9 and (T2) solvable is a genuine new candidate; if every component
 is of block type the classification of (Q-r) reduces to the four block families.

### S3 — exact FO2 for the block family (2,4)   (all solutions of the general census live here)
 Coordinates: rows 0,1 of X = s_1 e_0, s_2 e_0 (multiples of the unit vector of column 0); rows 2,3 = p, q in C^5; p = (p_0, p'), q = (q_0, q').
 With a = sum p', b = sum q', the level conditions on a linear subspace are EXACTLY:
     s_1 + s_2 = -(p_0 + a + q_0 + b);    p_0 a + q_0 b + a^2 + a b + b^2 + <p',q'> = 0;    (p_0 + a + q_0 + b)(a b - <p',q'>) = 0.
 Wanted (Sage/Macaulay2): the components of the variety of 5-dim subspaces X of C^12 = {(s_1,s_2,p,q)} satisfying these identities and
 rank(p-projection) <= 3, rank(q-projection) <= 3; for a generic point and for the special strata of each component the exact
 dim T_1 and rank (symbolic, over the function field of the component). Conjecture from 20 numerical solutions: dim T_1 = 9 (rank 3),
 rarely 12 (rank 7) or 8 (rank 3); bound <= 8 always when z, z' <= 2.  DECISION: a stratum with bound >= 9 and z, z' <= 2 = candidate.

### S4 — minimal pairs with zero entries in the annihilators, as an exact problem
 Data of a minimal row pair: kappa, kappa' in C^5 (sum = 1 each), (nu, nu') in C^5 x C^5 (defined modulo (kappa,0), (0,kappa') and
 scaling). For a column pair T = {j,l}: p_i := (kappa_i, nu_i), pt_i := (-kappa'_i, nu'_i) in C^2,  R_T := [p_j p_l pt_j pt_l] (2x4),
 Gamma_T := p_j pt_l^T + p_l pt_j^T (2x2), G_T := (Gamma_T + Gamma_T^T)/2, a_T := (Gamma_12 - Gamma_21)/2.  Condition for T:
   rank R_T <= 1:  (kappa_j, kappa_l, 0, 0) lies in the row space of R_T;
   rank R_T = 2 and (kappa_j, kappa_l, 0, 0) not in the row space:  G_T != 0, det G_T = 0, and (a_T = 0 or G_11 = G_12 = 0);
   rank R_T = 2 and (kappa_j, kappa_l, 0, 0) in the row space: no condition.
 (Closed form `gamma_check` and the independent test `pair_check` in `pairlib.py`.)  Wanted: for every zero pattern of (kappa, kappa')
 (subsets of {0..4} for each, up to simultaneous column permutation and swapping the rows; at least one zero overall) the complete
 solution set of "the condition holds for all ten T" (exact elimination per pattern and per assignment of the three cases to
 the ten T, or a numerical irreducible decomposition), as a list of normal forms.  Known: no zeros -> Types I, II; one zero in kappa,
 kappa' zero-free -> Type I_0 (7 structures).  DECISION: the list of types is the input for the triple arguments of the
 non-generic regime; an empty list for a pattern excludes minimal pairs with that pattern.

### S5 — diagonal N2 blocks with a two-row column (only needed if stage3's Theorem N2-X fails verification)
 Unknown: weights g in C^(3x5) with a prescribed support pattern, binary linear forms lam_0..lam_4 (not all proportional), a form sigma:
   sum_j g_ij lam_j = sigma (i = 0,1,2);   sum_j g_ij g_kj lam_j^2 = sigma^2 (three pairs);   sum_j g_0j g_1j g_2j lam_j^3 = sigma^3,
 with each of the three row maps p -> (g_ij lam_j(p))_j injective. For each of the 75 support patterns having a column with exactly
 two nonzero weights (list: `r4_patterns.py SEED 0 75 12 two` prints them): exact solution set. Numerically (12 starts each) only the
 patterns 011 011 111 111 111 and 011 011 101 101 111 have solutions; "four full columns + one two-row column" has 7 equations in
 7 unknowns, so isolated solutions may have been missed.

### S6 — the split free line (z_i = 3)
 In REG1, z_i = 3 forces L_i to be a (5,1) space in rows' sense (COMPUTE-rows.md, H1) and L = M_i (+) C t_0 with
 M_i = L_i (+) e_i (x) Z_i an 8-dim level space. So every hit of rows' H1 for (5,1) should be passed to `r5_FO2.py` (FO2 of the lift) and
 to the extension search with D = 9. No extra script.

Return for every task: counts (#starts, #verified solutions per type), the tables above, and all .npy files of ALIVE solutions.
