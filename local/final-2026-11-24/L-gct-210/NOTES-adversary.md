# NOTES-adversary (role: adversary)
STATUS 12:08: started; reading tools.
STATUS 12:24: support-restricted LM (adversary/supp.py). Calibration: 2rows+1col (13 entries) d=6 found; 2rows+2cols (16 entries) d=7 found (res 7e-12).
STATUS 12:20: support LM d=8 NOT found: 2rows+2cols (16 entries, 8 starts, best res 1.19), 1row+3cols (17, 5 starts, 1.72), 3rows+2cols (19, 3 starts, 1.75); d=7 found easily in 2rows+2cols (ext dim 8, deformation tangent 11). Now: symmetric (g-invariant) LM, adversary/symm.py.
STATUS 12:25: no 8 found yet. Calibration warning: support LM r5c345 (17 entries) did NOT find d=7
 although L0 lies in that support (4 starts, res .79) -> LM negatives for >=17-entry supports are weak.
## Exact reduction for the 2-rows+2-cols cover (rows {1,2} u cols {1,2}; adversary/red22chk.py, verified to 2e-13)
 t = [[Z (2x2), X (2x3)], [Y (3x2), 0]]. Column block X enters only via prod_j(1+X_1j x1+X_2j x2)
 = 1 + s1 x1 + s2 x2 + q x1x2 (s = row sums of X, q = s1 s2 - X_1.X_2); Y likewise via c = col sums,
 qY = c1 c2 - Y^1.Y^2. With R_i/K_j row/col sums of Z, perm Z = Z11Z22+Z12Z21:
   P1 = s1+s2+sum Z+c1+c2
   P2 = q + qY + (s1+s2)(c1+c2) + s1 R2 + s2 R1 + perm Z + c1 K2 + c2 K1
   P3 = c1(s1 Z22 + s2 Z12) + c2(s1 Z21 + s2 Z11) + (s1+s2) qY + (c1+c2) q
   P4 = q qY,   P5 = 0.
 P4: q qY = 0 on L forces qY == 0 or q == 0 (WLOG qY == 0 by transpose). Fibre count: with
 I = image of L in the 8 linear coords (Z,s,c), rho_X = rank of G_X = (2/3)s1s2+F on I,
 rho_Y = rank of (2/3)c1c2 on I:  dim L <= dim I + (4-rho_X)/2 + (4-rho_Y)/2.
 Branch c == 0: G_X has rank 6 on C^6, so dim I + (4-rho_X)/2 <= 5 for every I => dim L <= 7 (exact).
 Branch c != 0 (numerical, Grassmannian-chart LM in the 7-dim reduced space, adversary/red22g.py):
 dim-4 I on the cubic exist (always with c1,c2 dependent), dim-5 I NOT found (4 starts, res >= 35);
 dim-4 I with G_X == 0 not found. => this support class gives <= 7 (exact in branch c=0, numerical
 otherwise). PITFALL: LM without a chart (normalised rows) returns rank-deficient "solutions"
 (I first got fake dim-5/6 hits; red22lm*.py are WRONG for that reason, ignore them).
STATUS 12:33: S4xS4-invariant (symmetry group of L0) search, adversary/s4s4.py (exact isotypic param, few params, LM reliable: dim 7 L0-type found 3/4 starts): ALL dim-8 and dim-9 invariant configs fail (res >= 16, 4 starts each): (w0;ur,uc) = (2;2,0),(2;1,1),(3;2,0),(3;1,1),(0;2,1),(1;2,1)[10]. So no 8-dim level space has L0's S4xS4 symmetry.
STATUS 12:41: S3xS3-invariant search (adversary/skk.py k=3; rows/cols 1-3 permuted, isotypic param
 W in C^9 (triv), U_r,U_c in C^3 (std copies), optional 3x3-block DC piece). Calibration: L0-type
 (w0=3;1,1) dim 7 reached res 2.6e-4 (slow but converging). ALL dim-8 configs fail (3 starts each):
 (4;2,0) 11, (4;1,1) 1.29 [best, 4 starts], (2;3,0) 46, (2;2,1) 4.9, (0;3,1) 45, (0;2,2) 13,
 (6;1,0) 18, (2;1,0;+DC) 17, (0;2,0;+DC) 20, (0;1,1;+DC) 17, (4;0,0;+DC) 20, (8;0,0) 65.

## SUMMARY (adversary) -- no RESULT: no 8- or 9-dim level space found
Ruled out (numerically unless marked exact):
 1. Supports with small vertex cover: 2rows+1col <= 6 found (13 entries); 2rows+2cols: d=7 found
    in 4/4 starts (a positive-dimensional family: deformation tangent 11, ext dim 8), d=8 never
    (8 starts); exact reduction above shows <= 7 in its branch c=0, numerics (reliable reduced
    7-dim model) show <= 7 in the other branch. 1row+3cols, 3rows+2cols: d=8 not found (weak:
    d=7 also not found there by LM).
 2. Any vertex-cover-2 support (matching number 2) gives <= 7 (exact, trivial: 2 rows -> LS(2,5)=4;
    row+col -> P2 = (sum row)(sum col) forces 7).
 3. S4xS4-invariant spaces (L0's symmetry group): every isotypic configuration of dim 8, 9, 10
    fails (reliable: <= 6 parameters per search, L0 recovered 3/4 starts).
 4. S3xS3-invariant spaces: every dim-8 isotypic configuration fails.
 5. Cyclic weight constructions (5th roots of unity): torus/character spaces t = sum c_rs w^(ri+sj)
    and (sigma,id), (sigma,sigma) eigenspaces: P5 = perm on each eigenspace is a product/quintic that
    forces <= 4 per eigenspace and mixed weights (1,2,2),(1,1,1,2) reappear in P3,P4; best <= ~4-5.
    Rank-<=2 spaces with fixed column space U (t = u1 b^T + u2 c^T): level iff
    sum_{p+q=k} p!q! E_pq(u1,u2) e_pq(b,c) = 0 (k=1..5), E_pq/e_pq mixed elementary symmetric
    functions of rows/columns; best choices (u = powers of a 5th root of unity) give <= 5.
 Mechanism found (useful for the proof side): a block of columns supported on a single row i
 enters perm(J+t) only through its sum (factor 1 + sigma x_i), so its sum-zero part is a FREE
 fibre of dim (#cols - 1); same for rows. L0 = 1 core dim + 3 + 3 free fibres. Any "pendant"
 support (core a x b + single-row columns + single-column rows) gives dim = LE(core) + 10 - a - b
 - #sigma - #tau, which is <= 7 in all cases I checked (a,b <= 2).  Two-row column blocks enter
 through (s1, s2, q), q = s1 s2 - X1.X2; fibre bound kappa <= (fibre dim - rank)/2.
 PITFALL for everyone: LM with normalised rows (no Grassmannian chart) returns rank-deficient
 fake solutions; always use a chart [I|X]Q or check the basis singular values.
 6. Seeded full-ambient LM (all 8 vectors free, numerics/core.lm_space_inner) from a member of the
    2rows+2cols 7-dim family + its unique first-order extension direction (+5% noise): stalls at
    res 0.42-0.56 (5 starts, adversary/seed8.py). Not found.
STATUS 12:46: done (budget). Best next step for the refutation side: nothing promising left at
 small parameter count; if anyone continues, do Sk x Sk / (Sk x S_{5-k}) isotypic searches for
 k = 2 (more multiplicity, still few parameters) and the transpose-twisted symmetric groups.
 For the proof side: the free-fibre mechanism (single-row column blocks) is exactly where L0's
 dimension comes from; a bound argument might induct on the number of "non-pendant" lines.
