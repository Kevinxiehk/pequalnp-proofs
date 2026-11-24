# NOTES-methods (role: methods, started 12:07, budget 50 min -> ends ~12:57)

## CORRECTION 13:20 (read first): the numerical "caps" quoted in the TOP FINDING below for GOOD g are
## ARTIFACTS of the expected-dimension threshold, not evidence. Calibration (methods/calib.py, rlx.py):
## at a generic element x of the genuine 7-dim space ex1 (= rc45p1), L/x IS a 6-dim common isotropic
## subspace of the 4 forms (verified to 1e-12), yet 12 LM starts (analytic Jacobian) never find a 6-dim
## one (best 1e-3). With 4 nondegenerate forms on C^19, d-dim solutions are generically expected only
## for d(19-d) >= 4 d(d+1)/2, i.e. d <= 5; LM finds those and nothing beyond. So "dim 6, 7, 8 not
## found" says NOTHING. Only the POSITIVE result for the bad g (relaxation admits 9) is robust.
## TOP FINDING (methods, 12:36) - a promising, cheap-to-test route for the k >= 1 case
Gap <=> "level L with L cap DC != 0 has dim <= 8" (k = 0 gives dim = dim pi(L) <= 8 for free).
Fixed-DC-line relaxation (Step 3A below): for g in L cap DC, L contains g, lies in U_g (codim 5,
the s^0..s^4 coefficients of grad perm(J + s g) are perpendicular to L) and is totally isotropic for
the 4 Hessian coefficient forms H_0..H_3 of perm at J + s g. On U_g/Cg (dim 19) all 4 forms are
nondegenerate. Numerics (methods/relax.py, LM on Grassmannian charts, two random g in the
checked-numeric DC level plane sol_n5_d2_dc_s5): common isotropic subspaces of U_g/Cg of dim 5
found (res 1e-9, both g); dim 6 NOT found (g0: 6 starts best 6.7e-3; g1: 4 starts, all stall at
1.1e-2..1.3e-2); dim 7, 8 not found (8e-2, 2.5e-1). So for these g the RELAXATION ALONE gives
dim L <= 1 + 5 = 6 = 2n-3-1, matching the coupling conjecture (C*) and leaving slack 2 for the
gap. A proof only needs "common isotropic dim on U_g/Cg <= 7" for every nonzero DC level g:
a statement about 4 explicit quadrics depending on one 5x5 matrix g, no longer about L.
UPDATE 12:50 (IMPORTANT, weakens the above): for g in the DC part of split's GENUINE 7-dim space
split/rc45p1.npy (checked here: level err 1e-13, k = 2, m = 5, ranks (1,4)), the gradient
coefficients have rank 3 (not 5), U_g/Cg has dim 21, and the relaxation ADMITS common isotropic
subspaces of dim 6, 7 AND 8 (res 4e-10, 4e-14, 2e-13), i.e. it allows dim L = 9. So the
fixed-g relaxation is strong for generic g but useless for special g (here g comes from a
4x5 row-centred block). Route 3A must add constraints from a second element of L (e.g. the
mixed Hessians P_4(g, s, ., .), P_5(g, g, s, ., .) for s in L) or split off the special g.
Diagnosis (12:55): the bad g of rc45p1 is supported on a 3x4 block (rows 0-2, cols 0-3; rank 2,
two zero rows, one zero column). Good g so far: random g in the sol_n5_d2 DC plane (full support,
rank 4; relaxation max = 5 in U_g/Cg => dim L <= 6) and g in the exact weight space W5 (DC part
of numerics/S4_r1d3.npy, rank 3, gradient rank 5): relaxation dim 7 and 8 NOT found (3 starts
each, stall at 5e-2 and 3e-1) => dim L <= 7 for that g, so <= 8 holds.
=> Refined Step 3A: case split on K = L cap DC:
   (3A-i) K has an element g whose 5 gradient coefficients are independent (no zero row/column
          block structure) -> prove "4-quadric common isotropic dim on U_g/Cg <= 7" (needs new
          idea, but it is a per-g statement in a fixed 19-dim space; generic numerics say <= 5);
   (3A-ii) every element of K is block-supported (zero rows/columns, as in rc45p1) -> rectangular
          gluing/structure argument (rectangular small cases, L_gct_110 gluing, 217-style atoms).
ALSO: (C*) below is FALSE: rc45p1 has m + 2k = 9 > 7. The weaker "k >= 1 => k + m <= 8"
(what the gap needs) still holds on all data (rc45p1: 7).

STATUS 12:50: final (see TOP FINDING + UPDATE, plan at end).
STATUS 12:17: summaries done (below). Two numeric findings (methods/orth.py, alg.py):
 (F1) CORRECTION to L-gct-086 smallcases notes: ext_w5_4.npy ("dc weight space dim 3 extended to
      dim 7") is NOT a 7-dim level space. Its basis has singular values 7.96, 4.98, 4.31, 2.67,
      2.4e-4, 3.9e-5, 1.6e-6; along the 3 tiny right-singular directions |perm(J+v)-120| = 1e-2..4
      (unit v). Genuine part: a 4-dim level space with DC part 3 and rank(row/col sums) = 1.
      Same for ext_w4_3 (claimed 5, genuinely 3) and ext_w4_4 (not level at all).
      So the ONLY certified dim-7 example at n=5 is the border space (L080 = L_gct_189), which has
      DC part k = 0, projection to (row sums, col sums) of dim m = 7, rank_alpha 4, rank_beta 3,
      L = (row-centred part, 3) (+) (column-centred part, 4).  The genuine n=4 dim-5 space
      sol_n4_d5_full_s0 also has k = 0, m = 5 (ranks 3, 3, row-centred part 2, col-centred 2).
 (F2) No Fermat/Kneser shortcut on the full 24-dim space with M = 24: the operators
      A_v = Q^{-1} P_3(v,.,.) do NOT commute (||[A_v,A_w]|| = 76 vs ||A_v A_w|| = 98), so (P_2,P_3)
      is not the trace form of a commutative semisimple algebra C^24. The natural equivariant
      25-coordinate ansatz phi(t) = gamma + a alpha + b beta also fails (on row-constant matrices
      P_2 = -2 sum t^2, P_3 = 4 sum t^3 vs DC P_2 = sum t^2/2, P_3 = 2/3 sum t^3: needs a^2 = -4
      and a^3 = 6). Fermat with M >= 27 cannot give <= 8; M = 25, 26 non-equivariant not tested.

## KEY OBSERVATION (structural, from reading all checked proofs)
Every checked small-case upper bound is "isotropic maximum minus ONE": it only excludes a
LAGRANGIAN (maximal totally isotropic) subspace of the P_2-form. None of the methods excludes
"maximum minus 2 or more".
  case                       ambient (after P_1)   max isotropic (P_2)   checked bound   slack
  3x3 DC     (L_gct_109)     4                     2                     1               1
  3x3 full   (L094)          8                     4                     3               1
  4x4 DC     (L_gct_216)     9 (Walsh coords)      4                     3               1
  4x4 row-centred (217)      12                    6                     5               1
  4x4 full   (L-gct-091)     15                    7                     5   UNCHECKED   2
  5x5 full   (this gap)      24                    12                    8               4
  5x5 DC                     16                    8                     (truth ~3?)     -
So the target needs slack 4; the project never even reached slack 2 (n = 4 full is open).
The near-maximality is USED essentially: 217 needs dim >= 6 to get L + R = L^perp (so every
row-centred x orthogonal to L is in L); L094 needs dim 4 = Lagrangian to write L as a graph of a
skew 4x4 array over a coordinate chart; 216 needs dim 4 in C^9 for kernel-vector counting
(row restriction has a kernel, two rows/cols are "full"); 109 needs dim 2 to use Pluecker coords.

## Per-proof mathematical summaries

### Outside/L_gct_109 (3x3 DC <= 1), 347 lines
- DC 3x3 = 4 coords (top-left 2x2 block a,b,c,d). perm(J+t) - 6 = q(a,b,c,d) + c(a,b,c,d)
  (P_2 quadric q and P_3 cubic c, both explicit).
- Suppose v, w in K independent. For every linear form l, l(w)v - l(v)w in K; its coords are linear
  in the six Pluecker coords p = v ^ w. So q and c vanish on the 4-parameter family of such
  vectors; an explicit Nullstellensatz certificate (`core`, linear_combination exp := 4) shows
  each p_ij^4 is in the ideal => p = 0 => v, w dependent.
- Uses P_2, P_3. Method = "no line on {q = c = 0} in P^3": Grassmannian Gr(2,4) + certificate.

### Gct/L094 + Helpers/LevelThree (3x3 full <= 3), ~1650 lines
- Fourier coordinates for Z3 x Z3 (cyclic row/col shifts, w^2+w+1 = 0): entry-sum-zero 3x3
  matrices = 8 coords (P_1 = 0 kills the constant); perm(J+t) = 6 + 3 c6(x), c6 = quadratic +
  cubic. Quadratic = 4 hyperbolic pairs.
- L totally isotropic => dim <= 4. If dim 4: `exists_chart` gives a coordinate chart (one coord
  from each hyperbolic pair, 16 charts) on which L is a graph; Lagrangian => graph of a SKEW
  4x4 array s (6 unknowns). The cubic vanishing on L = 20 polynomial eqs in 6 unknowns; for each
  chart an explicit unit-ideal certificate (kern_0000..kern_1111). So dim <= 3.
- Uses P_2 (isotropy, hyperbolic normal form), P_3 (cubic). Method = "Lagrangian Grassmannian
  in charts + Nullstellensatz". Needs Lagrangian (graph = skew matrix).

### Gct/L092 (reduction), 34 lines
- phi = (row sums, col sums); L cap ker phi is DC level; rank-nullity: dim L <= G + dim phi(L)
  <= G + 2n. Crude: phi(L) actually lies in the (2n-2)-dim space alpha (+) beta (sum-zero, after
  P_1) and is further constrained by P_2..P_n (not exploited). At n = 5: dim L <= DC bound + 8
  (with the sharper target space) - useless for <= 8 unless DC bound is 0.

### Outside/L_gct_216 (4x4 DC <= 3), 1307 lines
- Walsh coordinates: DC 4x4 t = H x H^T, H the 4x3 matrix of the nontrivial characters of
  Z2 x Z2, x in C^{3x3} (9 coords). Exact: perm(J + s t) = 24 + 16 s^2 (x.x) + 64 s^3 perm_3(x)
  + s^4 F(x), F(x) = perm_4(H x H^T). So DC level <=> W (= image) totally isotropic for the
  Frobenius form, perm_3 = 0 on W, F = 0 on W. Isotropy => dim <= 4; exclude dim 4.
- Step A (uses only isotropy + perm_3, `pure_exists`): W (dim 4) contains a "pure" element
  (supported on one row or one column of the 3x3). Proof: if no pure element, rank counting
  (dim 4 > 3) gives at least two "full" rows and two full columns (projection onto the row is
  onto C^3); for a full row i, a kernel vector (row i = 0) plus polarization of perm_3 gives
  u_a v_b + u_b v_a = 0 between the other two rows => a "block" element with support exactly
  the 2x2 complement of (row i, column j); two block elements with distinct excluded row AND
  column meet in exactly one cell, contradicting orthogonality (`rook`); Fano-type pigeonhole
  (`fano_from_blocks`).
- Step B (uses F = P_4, `rowLocal`, `pureReduction`, `spectrum`): pure row element srow_i(z),
  z isotropic. F on srow_i(z) + c t, expanded in c (rank-one-plus-perturbation of a 4x4
  permanent, `fd`): forces all z_j != 0 and every t in W (with z.t_i = 0) to have row i
  proportional to z. So W = C srow_i(z) (+) emb(K), K in C^{2x3}, dim K >= 3, K isotropic for
  udot and for the twisted form udot(op_z x, y) (from perm_3 = 0). Pencil of two symmetric forms
  with a common 3-dim isotropic space in C^6 => common eigenvector w in K (`specEigenIn`), and
  `spec_no_iso` kills it. Column case by transpose (`colFalse`).
- Uses P_2, P_3, P_4. Method = bespoke structure theory of a Lagrangian; "pencil of quadrics"
  common-isotropic argument is the reusable idea.

### Outside/L_gct_217 (4x4 row-centred <= 5), 560 lines
- `no_one_column`: perm(J - t) = sum_k (-1)^k (n-k)! M_k(t) = n! on a level space, so no t in L
  has a column of ones (J - t would have a zero column). [Frobenius-Koenig obstruction; general n.]
- Form b(t,u) = sum_{i,l}(colsum_l(t) - t_il) u_il is nondegenerate on C^16, = -2 P_2 on
  row-centred; R = {constant-row matrices} (dim 4) is orthogonal to row-centred matrices.
  dim L >= 6 => L + R = L^perp (`maximal217`): every row-centred x orthogonal to L lies in L.
- `extract217`: for each column j, some z != 0 with rowAtom_j(z) = z (x) (4 e_j - 1) in L
  (column-j projection of L avoids the ones vector, so its annihilator contains a vector that
  produces an orthogonal row-centred matrix, which is then in L by maximality).
- `rowAtom_sparse`: P_2, P_3, P_4 of a rank-one z (x) w give e_2(z) = e_3(z) = e_4(z) = 0
  (L089-type: M_k(u v^T) = k! e_k(u) e_k(v)), so z has exactly one nonzero entry.
- `align_rows`: all these atoms sit in the same row r: L contains e_r (x) (all sum-zero rows)
  (3 dims) and every t in L has column sums = row r.
- `residual_bound`: the rest of L maps injectively into C^3 x C^3 with image a PROPER subspace
  (a P_3 relation), so dim L <= 5.
- Uses P_2 (maximality), P_3, P_4 on rank-one atoms, Frobenius-Koenig. Method = "near-Lagrangian
  => contains rank-one atoms => atoms are sparse => explicit structure => count".

### Gct/Helpers/LS4/* (n = 4 full <= 5, UNFINISHED; no assembly file)
- Plan visible from headers: split by r = dim(L cap DC). For r <= 1: L has large non-centred part;
  identities on column-centred W_c (WcIdentity: perm(J+t) - 24 = -2 sum_i e2(row i) + 2 sum_i
  e3(row i) + perm t), odd-part (OddPart: perm(J+A+R) - perm(J-A+R) = 4(w0 y_r + w1 z_r) for a
  two-column A and one-row R) and four-sign polarization (TwoTwo) identities show certain
  "one-row", "two-column", "two-row" level spaces cannot coexist in a level space (no_glue_*),
  with S4 x S4 x transpose symmetry (Symmetry) to normalize positions. The case r >= 2 would
  use L_gct_216 (DC <= 3). The classification of the large non-centred pieces (which would show
  L contains such one-row/two-column spaces) is NOT in the repo. So even at n = 4 the
  "non-centred part + DC part" coupling was never finished.

### Other helpers
- BlockIsotropic (L055): 3x3 level => isotropic for nondegenerate P_2 on C^9 => dim <= 4. Pure
  isotropy.
- CornerLemma (L169): 4x4, W with perm = 0, dim >= 7: the members vanishing on a 2x2 block
  (dim >= 3) have perm = product of two 2x2 permanents, ad + bc has no 3-dim zero space => a
  member with two zero rows or columns. Reusable idea: zero-block restriction + Laplace
  factorization + "2x2 permanent kills no 3-space".
- ColumnCore (L175): rows-fixed column-product core, Rado induction. Product-type only.
- CubicAssembly: unrelated (border-complexity assembly).

## STATUS 12:31: exact identities + reduction + coupling conjecture (all numeric checks in methods/)
(E1) Exact full P_3 at n = 5 (lstsq fit on 40 random points, 6 invariants, residual 3e-13; the
     invariant list is forced by the graph rule: no alpha-alpha-gamma / alpha-alpha-beta terms):
     t = alpha_i + beta_j + gamma_ij (alpha = rowsums/5, beta = colsums/5, total 0, gamma DC):
       P_2 = p2(gamma)/2 - 10 p2(alpha) - 10 p2(beta)
       P_3 = (2/3) p3(gamma) - 3 sum_i alpha_i r_i(gamma) - 3 sum_j beta_j c_j(gamma)
             + 9 sum_ij alpha_i beta_j gamma_ij + 20 p3(alpha) + 20 p3(beta)
     (r_i, c_j = row/col sums of SQUARES of gamma).  methods/p3full.py
(E2) Fermat-type identity (methods/phi.py, err 7e-14): for 5x5 t with entry sum 0, with row sums
     r_i, column sums c_j and phi(t)_ij = t_ij - (r_i + c_j)/2:
       sum phi^2 = 2 P_2(t) + (5/4)(sum r_i^2 + sum c_j^2)
       sum phi^3 = (3/2) P_3(t) - (3/8)(sum r_i^3 + sum c_j^3).
     So on a level space p2, p3 of phi(t) are controlled by the 8-dim projection pi(t) = (r, c)
     only; all cross terms alpha-gamma, beta-gamma, alpha-beta-gamma are matched exactly. On the
     DC part phi = id (Fermat L061 gives only dim K <= 25/3, i.e. 8 = isotropy). Killing the
     defect needs >= 2 extra copies of (r, c) (a^2+b^2 = -5/4, a^3+b^3 = 3/8), M = 45: Fermat
     then gives 15. => Fermat/Kneser cannot reach 8 at n = 5 (dead as a stand-alone route).
(E3) REDUCTION (trivial, worth stating): P_1 = 0 => pi(L) lies in sumzero (+) sumzero (dim 2n-2 = 8),
     so dim L = k + m with k = dim(L cap DC), m = dim pi(L) <= 8. Hence
        k = 0  =>  dim L <= 8 automatically.
     The gap is EXACTLY: "a level space with a nonzero doubly centred member has dim <= 8".
     (dim 9 forces k >= 1, and (k, m) in {(1,8), (2,7), ..., (8,1)}; k <= 8 by isotropy.)
(E4) COUPLING CONJECTURE (C*) [REFUTED 12:50 by split/rc45p1.npy: (k,m) = (2,5), m+2k = 9]:
        m + 2k <= 2n - 3      (dim pi(L) + 2 dim(L cap DC) <= 2n - 3)
     data (k, m):  n=4: (0,5) (2,1) (2,1) (1,2) (2,0) (1,0)  -> m+2k = 5,5,5,4,4,2 <= 5
                   n=5: L080 (0,7) -> 7;  genuine 4-dim part of ext_w5_4 (2,2) or (3,1) by
                   tolerance -> 6 or 7;  DC plane (2,0) -> 4.   All <= 7.  (methods/inv3.py)
     (C*) implies dim L <= 2n - 3 - k, DC dim <= n - 2 (= 3 at n = 5, tight for the weight
     construction), and with (E3) gives the gap with slack: k >= 1 => dim L <= 6.
     The gap only needs the much weaker  k >= 1  =>  k + m <= 8.
(E5) Gradient-span growth (L083 route, methods/grad.py, grad2.py): W(L) = span grad perm(J+t),
     t in L; level <=> L perp W(L), so a 9-dim level L needs dim W(L) <= 16. Values: L080 (d=7)
     dim W = 17 (= 25-7-1: one first-order extension direction); genuine 4-dim (k>=2) space:
     W = 21 = L^perp (first-order rigid). A pure growth lemma "dim W(L) >= 17 for every 9-dim L"
     is FALSE for non-level spaces: two-row support (d = 9): W = 15; 3x3 block (d = 8): W = 15;
     one row (d = 3): W = 4. So any Kneser-type growth theorem for permanent polarizations must
     have a "block-supported" exception (analogue of the stabilizer term), to be handled by the
     rectangular small cases (L101 2 x q <= q-1, L156 3 x q <= q+1, L094).

## WHICH CHECKED TECHNIQUES SCALE TO 5x5 (verdicts)
- Pure isotropy (P_2; BlockIsotropic, L092): exhausted at 12. With K = L cap DC, P = pi(L),
  N = L cap {gamma = 0}: isotropy only forces N isotropic in E, N perp P, and P/N isometric
  (x20) into K^perp/K, i.e. m + r_P - 2 nu <= 16 - 2k, m + r_P <= 8: compatible with k + m = 12.
- Fermat/Kneser (L061, L065, L067, L163): DC <= 8 (= isotropy), full space needs M >= 45
  coordinates (E2) -> <= 15. Useless alone at n = 5 (it only beats isotropy for n >= ~7).
  Possibly useful as a COMPONENT (S*K perp S + 1 for S = phi(L), K the DC part: gives k <= 7).
- Chart + Nullstellensatz certificate (L094, L_gct_109): only excludes a Lagrangian (graph of a
  skew form). At n = 5 even the Lagrangian case has OG(12,24) charts with 66 unknowns and 4096
  charts; dim 9 has no graph normal form. Infeasible under the brief's compute limits.
- Bespoke structure at the top dimension (L_gct_216: Walsh coords + pure elements + pencil
  eigenvector; L_gct_217: maximality => rank-one atoms => sparse => count): all their counting
  steps need dim = isotropic max (kernel vectors, L + R = L^perp). Do not scale to slack 4.
  REUSABLE pieces: (i) pencil lemma (216 `specEigenIn`: L isotropic for Q and Q(A.,.) and
  Lagrangian => A-stable => eigenvector in L); (ii) rank-one atoms: P_k(u v^T) = k! e_k(u) e_k(v)
  (L089) force sparsity; (iii) Frobenius-Koenig obstruction (217 `no_one_column`: perm(J - t) =
  n! on level L, so J + c t never has a zero (p x q) block with p + q = n + 1, any c);
  (iv) odd-part / four-sign identities (LS4) for "these two pieces cannot coexist" arguments.
- Gluing / rectangular small cases (L_gct_110, L101, L156): needed for the block-supported
  exceptions of any growth argument (E5).

## PROOF PLAN for 5x5, dim L <= 8  (attackable steps; status in brackets)
Notation: r, c = row/col sums; pi(t) = (r, c) in E (dim 8); K = L cap DC, k = dim K;
m = dim pi(L); g always a nonzero element of K.
Step 0 [ALREADY CHECKED] level => P_1..P_5 = 0 on L (Kit086 `level_Mk_zero`), S5 x S5 x
   transpose symmetry (LS4/Symmetry), rank-nullity skeleton (L092).
Step 1 [PLAUSIBLE AND EASY, ~50-100 Lean lines] sharpened L092: dim L <= k + 8 (image of
   (r, c) lies in {sum r = 0 = sum c} because P_1 = 0). => the gap reduces to: k >= 1 => dim <= 8.
Step 2 [PLAUSIBLE AND EASY, routine identities] (E1)/(E2) and the DC P_4 formula as Lean lemmas
   (polynomial identities in 25 variables via injForm L088 + ring / linear_combination).
Step 3 [NEEDS NEW IDEA; the whole difficulty] k >= 1 => dim L <= 8. Two sub-routes:
 3A "fixed DC line relaxation" [new; numerically testable now]: for g in K, L contains g and
   is totally isotropic for the four Hessian forms H_0 = Q, H_1 = P_3(g,.,.), H_2 = P_4(g,g,.,.),
   H_3 = P_5(g,g,g,.,.) (coefficients in s of Hess perm at J + s g) and lies in
   U_g = {x : x perp grad-coefficients of perm(J + s g), s^0..s^4} (codim 5 in C^25).
   For a generic DC level line g (from the checked-numeric DC level plane), U_g/Cg has dim 19
   and all four forms are nondegenerate there (methods/relax.py). Q alone gives dim L <= 1 + 9
   = 10. Claim to prove: common isotropic subspaces of {H_0..H_3} on U_g/Cg have dim <= 7
   (=> dim L <= 8). Tools: pencil lemma (216 specEigenIn) generalised to near-Lagrangian
   subspaces (A L subset L^perp, dim L^perp/L = 1 when d = 9 in 19 dims => A-chain gives an
   A-stable subspace of dim >= ... ), Reid-type bound for pencils (generic pencil on C^N:
   max common isotropic floor((N-1)/2) = 9 here, i.e. pencil alone gives only dim L <= 10).
   Weak point: special g (rank-one u v^T of the weight family, block-glued 4x4 circulant line)
   may make H_1..H_3 degenerate -> case split by the type of g.
 3B "coupling via (C*)" [new]: prove m + 2k <= 7, or the weaker  k + m <= 8  for k >= 1, by
   the LS4-style split: column-centred part L_C (beta = 0) and row-centred part L_R; show that
   a level space cannot contain both a large one/two-column piece and a large one/two-row piece
   (odd-part/four-sign identities generalised to n = 5) together with a DC element g.
   The n = 4 analogue (LS4, slack 2) is itself unfinished -> doing n = 4 first is the natural
   testbed for the technique.
 3C "Kneser growth for W(L)" [new, research-level]: dim W(L) >= 2 dim L - 1 unless L has a
   large block-supported part; then L perp W(L) (L083, checked) gives dim <= 8 in the generic
   branch, rectangular small cases (L101, L156, L094) in the block branch. (E5) shows the
   exceptions are real (2-row, 3x3-block spaces have small W).
Recommended order: 3A numerics first (cheap; tells whether the relaxation is strong enough
for generic g and which special g break it), then Step 1 in Lean, then 3A for special g.


## FOR lowd/hessmix  (methods, second task, 12:48-13:45)
1. Do NOT trust negative LM results for overdetermined isotropy/levelness systems (see CORRECTION at
   top): count unknowns d(N-d) vs equations; above the threshold LM misses even planted solutions.
   Calibrate every search with a planted solution of the same size (e.g. L/x for x in ex1, ex2, L080).
2. Gradient coefficients of perm(J + a g) are (5-k)! grad P_k(g), k = 1..5; grad P_5(g)_{ij} is the
   permanent of the 4x4 minor (i,j), grad P_4(g)_{ij} = sum of 3x3 subpermanents avoiding row i, col j.
   Hessian coefficients: H_0 = Hess P_2 (pair form), H_1 ~ P_3(g,.,.), H_2 ~ P_4(g,g,.,.),
   H_3 ~ P_5(g,g,g,.,.) with H_3(x,y) = sum over x_e y_f (e,f in distinct rows/cols) of the 3x3
   subpermanent of g on the complementary rows/cols.  Tools: methods/rlx.py (setup(x) -> quotient
   basis + forms; search(...) analytic-Jacobian LM), methods/spaces.py (exact bases: ex1, ex2,
   ex1DC, rank1weight, circ4, L080; all level to 1e-13).
3. SIGNATURE TABLE (methods/sig.py; random element of each space; ranks of H_0..H_3 on C^25 / on U_g/Cg):
     DC plane sol_n5_d2   rank 4  3x3,4x4 subperms != 0  gradrank 5  [25,25,25,25] / [19,19,19,19]
     W5 (DC weight)       rank 3  != 0, != 0             gradrank 5  [25,25,25,25] / [17,18,19,19]
     rank1weight u v^T    rank 1  != 0, != 0             gradrank 5  [25,20,25,10] / [18,16,18, 6]
     circ4 (4x4 padded)   rank 3  3x3 != 0, ALL 4x4 = 0   gradrank 3  [25,16,22, 8] / [21,12,18, 6]
     ex1 DC plane         rank 2  ALL 3x3 = 0, 4x4 = 0    gradrank 3  [25,12,12, 0] / [21, 8,10, 0]
     ex1 generic (7-dim)  rank 4  != 0                   gradrank 5  [25,25,23,22] / [19,19,18,16]
     ex2 generic (7-dim)  rank 3  != 0                   gradrank 5  [25,25,22,12] / [19,19,17, 8]
     L080 generic         rank 2  ALL 3x3 = 0             gradrank 3  [25,23,16, 0] / [21,19,14, 0]
     W5+1 (4-dim)         rank 5  != 0                   gradrank 5  [25,25,25,25] / [19,19,19,19]
   The fixed-g relaxation admits dim 9 exactly where low-rank H_1..H_3 appear (ex1 DC plane:
   ranks 8, 10, 0 on the quotient).  "Special" <=> grad P_5(g) = 0 <=> all 4x4 subpermanents of g
   vanish (gradient rank drops 5 -> 3 in every case seen).
4. CLASSIFICATION CONJECTURE for special DC level lines (methods/special.py: LM on DC g with
   P_2 = P_3 = P_5 = 0 and all 25 4x4 subpermanents = 0 (this already gives P_4 = 0); 17 of 17 solutions):
   every such g has a ZERO ROW or a ZERO COLUMN (support in a 4x5 or 5x4 block), rank <= 3.
   Seen sub-types: one zero row (4x5 block), zero row AND column (4x4 block, e.g. circ4), two zero
   rows plus a zero column (3x4 block, the ex1 DC plane: there even all 3x3 subperms vanish).
   EXACT consequence for a subspace: if every element of K = L cap DC is special, then K has a COMMON
   zero row or column (K lies in the finite union of the linear spaces {row i = 0}, {col j = 0},
   so it lies in one of them).  So the special branch of route 3A is: "K supported in a 4x5 block"
   -> rectangular problem (L cap {row 4 = 0} is a 4x5 level space containing K; LS(4,5) >= 6).
5. Adversary's free-fibre mechanism (columns supported in a single row enter only via their sum,
   factor 1 + sigma x_i) explains all three known 7-dim spaces: ex1 = (4x5 row-centred, dim 6:
   K + free row 3) + column 4; ex2 similar; L080 = free row fibre + free column fibre.
   In ex1/ex2 the DC part sits in the rows {0,1,2} complementary to the free row 3.
6. Suggested proof skeleton for k >= 1 (all steps open):
   (i) K contains a non-special g (some 4x4 subpermanent nonzero): need a real bound on common
       isotropic subspaces of H_0..H_3 on U_g/Cg (dim 19, all forms nondegenerate in the generic
       case); numerics CANNOT decide this (see 1); a theoretical pencil argument is required, or add
       cubic conditions (P_3(s), P_4(g,s,s,s), P_5(g,g,s,s,s) on L) and redo the count:
       with the 3 cubic forms added, unknowns 8*11 = 88 vs 4*36 + 3*120 = 504 equations for dim 9.
   (ii) every g in K special: K has a common zero line (exact, item 4, modulo the classification
       conjecture); then split L by its row-4 part as in ex1 (free fibre + 4x5 rectangular part).
7. (13:25) SPECIAL g = SINGULAR POINTS OF THE PERMANENT.  grad P_5(g) = (4x4 minor permanents), so
   "special" (gradient rank drop via grad P_5 = 0) <=> perm(g) = 0 and grad perm(g) = 0 <=> g in
   Sing(perm_5).  LEMMA Z (conjecture): a 5x5 DOUBLY CENTRED matrix in Sing(perm_5) has a zero row or
   a zero column.  Evidence: methods/special_nolevel.py (no level conditions) 14/14 LM solutions,
   methods/special.py (with P_2, P_3, P_5 = 0) 17/17; all rank 3, all with a zero line.  Support-type
   singular points collapse under DC (2 rows + 1 col or 1 row + 2 cols supports force zero lines);
   a zero 3x3 block is NOT singular (minor perm = 4 a1 a2 b1 b2).  Literature: components of
   Sing(perm_n) are NOT fully known; codim of Sing(perm_5) is open (Boralevi-Carlini-Michalek-Ventura,
   arXiv 2402.17839: codim >= 4 in general, >= 6 for k >= 6; 4x5 case: all components codim 5,
   one Kirkup component + cones over P_{3,5}).  So Lemma Z is a self-contained algebra problem
   (DC is a 16-dim space; Sing condition = 25 quartics) -- a good target for an exact proof
   (e.g. by Groebner on the 16 DC coordinates: moderate size, maybe too heavy for the brief).
   With Lemma Z: K inside Sing(perm) => K has a common zero line (union-of-subspaces argument, exact).
8. (13:25) Cubic-augmented relaxation tool methods/rlx3.py: adds the 3 cubic coefficient forms
   (P_3(s,s,s), P_4(g,s,s,s), P_5(g,g,s,s,s)); forms verified (ex1 satisfies all to 1e-14). But LM
   cannot find even the planted 6-dim solution at the special g of ex1 (2 starts, res 1.1); so it is
   unusable for negative conclusions without planted/homotopy starts.
9. (13:45) Lemma Z holomorphic test (methods/lemmaZ3.py): DC g, all 25 4x4 minor permanents = 0,
   plus ONE normalisation prod_i lam_i(row i) * prod_j mu_j(col j) = 1 (excludes zero lines).
   Calibration (column 4 allowed to vanish): exact solutions found at once (zero column, all other
   lines nonzero). Test (no zero line allowed): 7 starts, residuals stall at 3e-5..1e-4 with slow
   drift (typical of solutions only "at infinity", i.e. degenerating to a zero line). Supports
   Lemma Z; not a proof. (Real-norm versions lemmaZ.py / lemmaZ2.py were mis-calibrated: ignore.)
STATUS 13:46: second task done; report sent.
