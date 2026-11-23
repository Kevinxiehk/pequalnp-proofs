# NOTES-leanzbf (role: leanzbf; start 16:38, budget 2 h -> ends ~18:38)
## ROUND 2 RESULT (final, 19:42) -- file lean/zbf/Zbf11.lean (5227 lines, 256 KB) = Zbf.lean (round 1) + round-2 sections
leancheck: lean exit code 0; axioms [propext, Classical.choice, Quot.sound]; format quotes/hash/import/banned/comments all 0.
Checker sanity test (19:32): the same file with one deliberately false lemma appended gives exactly ONE error (that lemma) and
exit code 1 (lean/zbf/sanity.log) -- so "exit 0" really means every declaration of the file was checked.
Snapshots of every compiling state: Zbf2_v1..v5_ok, Zbf3_v1..v3_ok, Zbf4_v1_ok, ..., Zbf11_v1_ok (.lean, same folder; Zbf11 = current).
Combined file with the Frame210 kit: lean/zbf/FrameZbf2.lean (6604 lines, 323 KB; log frame2.log): COMPILES (exit 0, axioms ok,
format 0) = Frame210 kit (MethodCeiling, Helpers.Minc, Helpers.RankOne, Kit086, F210) + the whole ZBF210 namespace of Zbf11 +
bridge ZBF210.lev_iff_F210 + the final theorem. (The round-1 files Zbf.lean / FrameZbf.lean are unchanged.)
No sorry, no axiom, NO REMAINING EXPLICIT-HYPOTHESIS HOLE in targets (1)-(4). EVERYTHING BELOW IS COMPILED unless marked NOT DONE.
 target                         | status   | Lean name(s)                         | remarks
 (1) Theorem N3'                | COMPILED | n3prime                              | unconditional. b 3x3, pm b != 0, pm (b + eta) = pm b on V0 => finrank V0 <= 3.
     Corollary N3'-L            | COMPILED | n3prime_L_full                       | unconditional (any n, any 3x3 block with ell(u0) = 1).
     (also the whole chain R0 -> ZBF -> ThB -> Lemma C at an ARBITRARY base point b: BLev, lemmaC_genB, lemmaC_col_genB, ...)
 (2) C4                         | COMPILED | c4                                   | unconditional; valid for every dim L (pair minimal for Lemma C,
                                |          |                                      | a_r = a_r' = 1); NEW PROOF, shorter than the paper's (STATUS 19:00).
 (3) C7 / C7''                  | COMPILED | c7_final   (statement about L only)  | Lev 5 L, r != r', finrank L = finrank X_{rr'} + 7, row ranks >= 4  ==>
     Type I / Type II           |          | c7_rows_ind, c7_rows_full, c7_rows   | EXISTS annihilator data kappa, kappa', nu, nu' (the two relations of I^)
                                |          | (for ANY annihilator data)           | such that, IF kappa and kappa' have no zero entry, the points
                                |          | c7_types, c7_sep (combinatorics)     | (rho_m, rho'_m) = (nu_m/kappa_m, nu'_m/kappa'_m) are of Type I or II:
                                |          | c7_tau, c7_pair_x, c7_pair_thB       | exists a, b separated in both coordinates with sigma_a = sigma_b, and every
                                |          | c7_lift, c7_hI, second_relation,     | column m sits at P_a (omega_m = omega_a), at P_b (omega_m = -omega_a) or
                                |          | fk_annihilator, dot_zero_of_row      | at the corner (rho_a, rho'_b) with sigma_a != 0, omega_m^2 = -omega_a^2,
                                |          |                                      | sigma_corner^2 = -sigma_a^2, omega_a sigma_a + omega_m sigma_corner = 0.
                                |          |                                      | (Type I = no column at the corner; Type II = some column at the corner.)
 (4) (P), (G1), (G2)            | COMPILED | rows_submodular, cells_submodular,   | (P): submodularity + rank formulas; (G1): rows_disjoint_bound,
                                |          | rows_rank, cells_rank, rows_inj_bound,| rows_inj_bound; (G2): stage3_G2 (with rows relabelled by rho).
                                |          | rows_disjoint_bound, dS_*, stage3_G2 |
 (5) Theorem G                  | PARTLY   | pm_mask_sum, pm_mask_zero,           | COMPILED: the generalised Laplace identity (sum over row sets A of
                                |          | pm_mask_factor, thG_term, thG_masked | size m and column sets of products of complementary minors of two
                                |          | perp_bound, rank_one_bound           | elements of L^ = n! C(n,m) c1^(n-m) c2^m), and the linear-algebra
                                |          |                                      | core of the inequality (A, B in C^N with dot pairing a.b = f(a) g(b)
                                |          |                                      | on A x B  =>  dim A + dim B <= N + 1). NOT DONE: assembling these
                                |          |                                      | into rho_k + rho_(5-k) <= C(5,k)^2 + 1 (index bookkeeping over
                                |          |                                      | pairs (A,T)) and dim K_2 >= 5.
NOT DONE inside (3) (none of it is needed for the classification statement): (i) condition (c) of C7' (sigma != 0 for two columns
 at the same point), hence "sigma_0 != 0" in Type I; (ii) the normalisations c = 1/(K_1 - K_2), sigma_0 = -K_2 (1 + c) and the final
 tau-relations on L of NOTES-stage2 section 3 (they follow from sum kappa = sum kappa' = 1 and sum nu + sum nu' = 0, all available
 as conjuncts of c7_final); (iii) the case of zero entries in kappa / kappa' (excluded by hypothesis, as in the paper's C7'').
NO PAPER STEP FAILED in round 2. Remarks for the authors of the paper proofs:
 - C7'': the Lean proof uses exactly the corrected form of (d) (pair separated by both rho and rho' => omega_j + omega_l = 0 AND
   sigma_j = sigma_l); the classification needs only (a), (b), (d) and omega != 0; condition (c) and "at most 2 points per
   anti-diagonal" are not needed as separate steps (the three-point case is excluded directly by 2 omega_a = 0).
 - C7'' does NOT need a_r = a_r' = 1 beyond: both row ranks >= 4 (used only to show rho, rho' non-constant) -- c7_rows_full shows the
   classification for ANY two independent relations with rho, rho' non-constant on a minimal pair.
 - C4 and N3': Lean proofs differ from the paper proofs (see STATUS 18:45, 19:00); the paper statements are confirmed.

## ROUND 2 API guide (additions; namespace PEqualNP.Gct.ZBF210)
 BLev b kappa L                  : kappa != 0 and pm (c b + t) = kappa c^n for all c, t in L   (level space at base point b)
 blev_of_lev, blev_of_const      : Lev n L -> BLev J n! L;   (pm b != 0, pm (b + eta) = pm b on V0) -> BLev b (pm b) V0
 lemmaC_genB hL r1 r2 hr         : BLev b kappa L (n = m+2) -> finrank L <= finrank (rowsZero L r1 r2) + (2m+1);  lemmaC_col_genB (columns)
 n3prime b V0 hb h               : finrank V0 <= 3            n3prime_weak : <= 4 (short proof, Lemma C only)
 n3prime_L_full hL r c u0 hu0 h0 : r c : alpha + Fin 3 = Fin n, u0 in blockSpace L r c with ell(u0) = 1 ->
                                   finrank (blockSpace L r c cap ker ell) <= 3 + finrank (colsOff L c)
 rowsZeroS L S, cellsZero L K    : L cap {rows in S = 0}, L cap {cells in K = 0} (Finset S, Finset K); mem_rowsZeroS, mem_cellsZero
 rows_submodular L S S'          : dim X_S + dim X_S' <= dim X_{S cap S'} + dim X_{S cup S'};   cells_submodular likewise
 rows_rank L S r                 : dim X_S = dim X_{S + r} + dim row_r(X_S);   cells_rank L K : dim L = dim cellsZero + dim (L.map (cellProj K))
 rows_disjoint_bound, rows_inj_bound : (G1)-type bounds when X_{S cup S'} = 0 / X_{S + c} = 0
 dS L rho S := finrank (rowsZeroS L (S.map rho));  dS_submodular, dS_inj_bound, dS_disjoint_bound, stage3_G2 (statement of (G2))
 blev_line, blev_mix, blev_rows  : mixed-coefficient identities at base point b
 maskAT A T u, thG_masked, thG_term : Theorem G identity (masked matrices; thG_term identifies a term with a product of two blk's)
 Bx r p x j q                    : 3x3 subpermanent of x on rows != r, r.succAbove p and columns != j, j.succAbove q
 thA5 hL r p x hx c t ht         : ThA for n = 5:  sum_j sum_q (c + t(r,j)) (c + t(r',j.succAbove q)) Bx r p x j q = 0   (x in X_{rr'})
 row_onto hL e hrank v           : finrank row_e(L) >= m+1 (n = m+2) -> every v in C^n is gamma 1 + row_e(t), t in L   (row_e(L^) = C^n)
 c4_left / c4_right              : t in L with row r' = 0 (resp. row r = 0): its row r (resp. r') is in the left (right) kernel of B_x
 c4_cols                         : B_x[j0,l0] != 0 and pair minimal -> L contains t with row r = any prescribed vector supported on {j0,l0}
 c4 hL r p hmin ha ha' x hx j0 q0: Bx r p x j0 q0 = 0      (hmin: finrank L = finrank (rowsZero L r r') + 7; ha, ha': row ranks = 4)
 dotL kappa z = sum_m z m * kappa m (linear in z); dotL_single, dotL_two, dotL_comb; dual_eq_dotL (every functional is a dotL)
 relM alpha beta z = dotL alpha z.1 - dotL beta z.2;  relP alpha beta z = dotL alpha z.1 + dotL beta z.2  (functionals on C^n x C^n)
 fk_annihilator hL r             : exists kappa, (forall t in L, dotL kappa (row_r t) = 0) and dotL kappa 1 = 1      (any level space)
 second_relation                 : minimal pair, f1 vanishing on I^ with f1 v1 != 0 -> exists g vanishing on I^ and on v1, g != 0
 c7_lift                         : minimal pair, f1, f2 vanishing on I^ and independent (f1 v1 != 0, f1 v2 = 0, f2 v2 != 0) ->
                                   every z with f1 z = f2 z = 0 is (c + row_r t, c + row_r' t), t in L   (I^ = ker f1 cap ker f2; dim count)
 c7_hI                           : the lifting localised to a column pair {j,l}, with ell = <kappa, z_1>, landing in pairSpace L r r' j l
 dot_zero_of_row                 : row rank >= 4 and mu annihilates row_e(L) and 1 -> mu = 0
 c7_pair_thB                     : ThB for the pair T = {j,l}: (ell = 0 on Pi_T) or (exists k, q_T = k ell^2 on Pi_T)
 c7_tau / c7_pair_x              : pair criterion (a), (b), (d) of C7' (tau-coordinates / original coordinates), by explicit test vectors
 c7_sep, c7_types rho rho' omega : plane combinatorics of C7'' for ANY index type
 c7_rows                         : classification given the lifting hypothesis hI;   c7_rows_full : given annihilator data (S1)-(S3),
                                   zero-free kappa, omega, and rho, rho' non-constant;   c7_rows_ind : same with (row ranks >= 4 and
                                   "(nu,nu') is not a multiple of (kappa,-kappa')") instead of non-constancy
 c7_final hL r r' hr hmin ha ha' : the statement about L only (existence of the data + classification when kappa, kappa' zero-free)
 dotD, perp_bound A B h          : A, B in C^N with sum_m b m * a m = 0 on A x B -> finrank A + finrank B <= N
 rank_one_bound A B f g h        : sum_m b m * a m = f a * g b on A x B (f linear) -> finrank A + finrank B <= N + 1   (core of ThG)
 Final placeholder theorem PEqualNP.Outside.L_gct_210_zbf (Zbf11.lean): R0 + Lemma C (rows, columns) + N3' + C4.

## RESULT (final, 17:40) -- ONE FILE, EVERYTHING BELOW IS COMPILED (no sketch, no hole, no failure)
File: /home/claude/work/L-gct-210/lean/zbf/Zbf.lean  (2015 lines, 97 KB; backups Zbf_v1..v9_ok.lean, v9 = current; log last.log)
leancheck: lean exit code 0; axioms [propext, Classical.choice, Quot.sound]; format quotes/hash/import/banned/comments all 0;
12 warnings (deprecated if_pos/if_neg, unused simp args). "statement verbatim: False" as expected (placeholder theorem).
Also: /home/claude/work/L-gct-210/lean/zbf/FrameZbf.lean = Frame210.lean (Kit + F210, its last theorem removed) + the whole
ZBF210 namespace + bridge ZBF210.lev_iff_F210 (Iff.rfl) + the same final theorem: compiles (exit 0, 164 KB, log frame.log), so the
P_k tools of Frame210 and the ZBF tools can be used together in one file (no name clashes).
Self-contained: imports Mathlib + PEqualNP.Defs only, does NOT need the Kit / Frame210 (R0 is proved by scaling + a polynomial
identity, so no P_k bridge is used). Namespace PEqualNP.Gct.ZBF210. Final placeholder theorem
  PEqualNP.Outside.L_gct_210_zbf : for L with the gap hypothesis:  (forall c, t in L: sum_f prod_i (c + t(i, f i)) = 120 c^5)
     AND (forall rows r1 != r2: finrank L <= finrank (rowsZero L r1 r2) + 7) AND (same for columns, colsZero).

| target | status | Lean names |
| 1. R0  perm(cJ + t) = n! c^n (any n), gap form 120 c^5; perm(u + s x) independent of s; FK | COMPILED | lev_scale, lev_scale_emb, lev_line, lev_line_const, lev_FK, lev_FK_row, lev_FK_block |
| 2. ZBF perm(u) = perm(u[S,Z^c]) perm(u[S^c,Z]) over a zero block (general index types; finset form; 1+k and 2+m instances) | COMPILED | perm_sum_block, perm_submatrix_equiv, perm_zero_block, perm_zero_block', pm_zero_block, pm_zero_block_sets, exists_block_equivs, pm_zero_of_big_block |
| 3. UFD replacement by a LINE lemma, both cases of chief's (ZBF) | COMPILED | poly_const_of_mul, line_const, ufd_unit_ne, ufd_unit, ufd_zero, zbf_prod, zbf_ufd, zbf_zero, zbf_lineality (GZ-a) |
| 4a. Theorem B: (B1) q_T = kappa ell^2, dim Pi <= 2, dim U_T <= 2 + dim L_{rr'}; trichotomy B1 / B2 / q0 | COMPILED | thB_quad, thB_ker, thB_img, thB_dim, thB_cases, thB_pair (equiv-free form for rows r1 != r2, columns c1 != c2) |
| 4b. Lemma C in verify2's GENERAL form, for every n = m+2: dim L <= dim(L cap {rows r,r' = 0}) + 2n-3; rows and columns; n = 5: + 7; dim 9 => >= 2 | COMPILED | lemmaC_gen, lemmaC_col_gen, lemmaC, lemmaC_col, lemmaC_nine |
| 4c. N3: every 3x3 level space has dim <= 3 (test of the tools; 230 lines instead of L094's 1650) | COMPILED | n3 (+ n3_alg, n3_row, n3_col, ...) |
| extra: Laplace expansion along one row / two rows (derived from ZBF + row linearity) | COMPILED | pm_row_expand, pm_laplace_row, pm_laplace_two |
| extra: CA2 by the DIRECT Laplace argument (coordinator note b), general and full form | COMPILED | ca2, ca2_full |
| extra: Theorem A (affine isotropy u_r^T B_x u_r' = 0) | COMPILED | thA |
| extra: SR (single-row lemma of stage3) | COMPILED | single_row_SR |
| extra: all mixed Taylor coefficients: coefficient of s^m of perm(u + s v), u, v in L^ (row-subset form of Theorem G's identity) | COMPILED | mix, pm_line_expand, lev_mix, lev_mix_hat |
| extra (17:40): C1 pigeonhole, row projections <= n-1, block witness lemma (generalises SR, gives stage3's D2), C2-type corollaries of ThB, column versions of CA2 / ThA, polarization in "rows A from x, the others from u" form | COMPILED | rows_pigeon, row_proj_le, zbf_witness, zbf_witness', q0_isotropic_bound, thB_img_or, thB_Bx, blk_tr, ca2_col, thA_col, mix_eq_sum_pm, lev_mix_pm, lev_rows |
NOT done (not attempted, so no information about their correctness): Theorem G in subpermanent-product form and the rho_k
inequality; C4/C7; N3'; column versions of SR / thB_pair / lev_rows (obtain by lev_tr + the row versions, as lemmaC_col_gen,
ca2_col, thA_col do); the converse of R0.

### Did any paper step fail to formalize?  NO.
R0, ZBF incl. the UFD step, ThB (B1 and the trichotomy), Lemma C (general 2n-3 form), ThA, CA2 (direct Laplace form), SR, GZ-a, N3
all went through; I found no wrong or incomplete step. Remarks on where the Lean proof differs from the paper:
 (i) UFD is not needed anywhere. Case ell != 0 on U: for u0 in U with ell = 1 and v in U cap ker ell, f_1(u0 + s v) f_2(u0 + s v) = n!
     for all s, so each factor is a constant polynomial in s (degree count in C[s]); homogeneity gives f_i = f_i(u0) ell^deg where
     ell != 0, and one more "polynomial vanishing off s = 0" argument gives it where ell = 0. Case ell = 0 on U: if f(a) != 0 and
     g(b) != 0, restrict f g = 0 to the line through a, b (C[s] is a domain). Both are a few lines (ufd_unit, ufd_zero).
 (ii) ThB: the kernel of U_T -> 2x2 block is identified WITHOUT FK: block zero => q = 0 = kappa ell^2 => ell = 0 (thB_ker).
 (iii) Lemma C: in "pick j with (n_r)_j != 0, l with (n_r')_l != 0 and T containing j, l" the case j = l needs a second column
     (any other one); handled by exists_col_perm. The annihilators n_r are avoided: with A = {t in L : row r' = 0}, the map
     (gamma, a) -> gamma 1 + a_r is onto C^n by a dimension count (row_surj), which gives the column j (exists_col).
 (iv) N3 is proved by a shorter route than chief's three cases: Lemma C (rows, columns) at n = 3 gives directly a nonzero
     single-row element in every row and a nonzero single-column element in every column as soon as dim L >= 4; then the
     relation x_rj y_rj = 0 (one explicit 3x3 identity, 9 cases generated by lean/zbf/py/gen_n3.py) and the pigeonhole.
 (v) P_1..P_5 = 0 are never used; lev_mix replaces them (coefficient of s^m of perm(u + s x) vanishes for m >= 1).

## API guide (namespace PEqualNP.Gct.ZBF210; `open Finset`)
Conventions: matrices are t : Fin n x Fin n -> C, entry t (i, j).
- pm u := (Matrix.of fun i j => u (i, j)).permanent;  pm_perm : pm u = sum_sigma prod_i u (i, sigma i);  pm_emb : = sum over
  embeddings f of prod_i u (i, f i) (the gap's form);  pm_tr : pm (fun p => u (p.2, p.1)) = pm u.
- blk rho kappa u := permanent of the block (fun i j : m => u (rho i, kappa j)), m any Fintype (rho, kappa : m -> Fin n need not be
  injective);  blk_smul, blk_unit (m = Unit: the entry), blk_two (m = Fin 2: q0 of blockProj), blk_zero_col, polyLine_blk.
- Lev n L := forall t in L, sum_{f : Fin n -> Fin n embedding} prod_i (1 + t (i, f i)) = n!   (same definition as F210.Lev);
  lev_five L hL : Lev 5 L from the gap hypothesis;  lev_tr : Lev n (L.map (trE n)) (transpose; trE_apply).
- L^ = CJ (+) L is modelled by PAIRS w = (c, t) : C x (Fin n x Fin n -> C), ell w = w.1, hat n w = fun p => w.1 + w.2 p (linear).
R0:   lev_scale hL c t ht : pm (fun p => c + t p) = n! * c ^ n          lev_scale_emb : the same as the embedding sum
      lev_line hL c s t x ht hx : pm (fun p => c + t p + s * x p) = n! * c ^ n     lev_line_const : = pm (fun p => c + t p)
      lev_FK hL c t ht (h : pm (fun p => c + t p) = 0) : c = 0       lev_FK_row (a zero row of cJ + t)   lev_FK_block (FK block)
ZBF:  r c : alpha (+) beta = Fin n (equivalences). ROWS r (inl a), COLUMNS c (inr b) carry the zero block:
      pm_zero_block u r c (h : forall a b, u (r (inl a), c (inr b)) = 0) :
          pm u = blk (r o inl) (c o inl) u * blk (r o inr) (c o inr) u
      (Matrix versions perm_zero_block', and perm_zero_block for the block rows r (inr b) x columns c (inl a).)
      pm_zero_block_sets u S Z eS eZ h : finset form, S x Z zero, eS : S = Z^c, eZ : S^c = Z any equivalences
      (exists_block_equivs S Z (S.card + Z.card = n) gives them). Ready-made equivalences:
        sa e : Fin k (+) Unit = Fin (k+1)   (inl b -> e.succAbove b, inr -> e;  sa_inl, sa_inr)
        e2m m : Fin 2 (+) Fin m = Fin (m+2) (inl 0 -> 0, inl 1 -> 1; e2m_inl0, e2m_inl1, e2m_inr); compose with a permutation
        from exists_perm2 r1 r2 (r1 != r2) : exists rho, rho 0 = r1 and rho 1 = r2  to reach any two rows / columns.
      blockSpace L r c : Submodule of pairs = {w | w.2 in L and forall a b, w.1 + w.2 (r (inl a), c (inr b)) = 0} (= U_{S,Z});
      mem_blockSpace (Iff.rfl);  blockSpace_finrank_ge : finrank L + 1 <= finrank (blockSpace L r c) + card alpha * card beta.
UFD:  zbf_prod hL r c w hw : blkA (hat n w) * blkB (hat n w) = n! * w.1 ^ n
      zbf_ufd hL r c u0 hu0 (h0 : u0.1 = 1) w hw : blkA (hat n w) = blkA (hat n u0) * w.1 ^ card alpha  and  the same for B
      zbf_zero (hn : n != 0) hL r c (hU : forall w in U, w.1 = 0) : (forall w in U, blkA (hat n w) = 0) or (forall w in U, blkB .. = 0)
      zbf_lineality : blkA, blkB are unchanged under w -> w + x, x in U with x.1 = 0 (GZ-a).
      Abstract versions for any module V, U : Submodule, ell linear, f g : V -> C with PolyLine f, PolyLine g (polynomial along
      every line): ufd_unit (f g = k ell^N on U, k != 0, f homogeneous of degree df, u0 in U, ell u0 = 1 => f = f(u0) ell^df on U),
      ufd_zero (f g = 0 on U => f = 0 on U or g = 0 on U), line_const, poly_const_of_mul (P Q = nonzero constant => P constant).
ThB:  for r c : Fin 2 (+) beta = Fin n (rows r (inl 0), r (inl 1); columns T = {c (inl 0), c (inl 1)}), u0 in U, u0.1 = 1:
      thB_quad : q0 (blockProj r c u0) != 0 and forall w in U, q0 (blockProj r c w) = q0 (blockProj r c u0) * w.1 ^ 2
      thB_img  : finrank (U.map (blockProj r c)) <= 2          thB_dim : finrank U <= 2 + finrank (rowsZero L (r (inl 0)) (r (inl 1)))
      thB_cases (no u0): (exists u0 in U, u0.1 = 1) or (ell = 0 on U and (q0 = 0 on the image or the complementary block perm = 0 on U))
      thB_pair hL r1 r2 c1 c2 (r1 != r2) (c1 != c2) u0 (hu0 : u0 in pairSpace L r1 r2 c1 c2) (u0.1 = 1) : the same three facts for
      pairSpace L r1 r2 c1 c2 = {w | w.2 in L and forall j != c1, c2: w.1 + w.2 (r1, j) = 0 and w.1 + w.2 (r2, j) = 0}  (n = m + 2).
LC:   rowsZero L r1 r2 := L inf ker (rowMap r1) inf ker (rowMap r2) (mem_rowsZero), colsZero likewise (mem_colsZero).
      lemmaC_gen (hL : Lev (m+2) L) r1 r2 (r1 != r2) : finrank L <= finrank (rowsZero L r1 r2) + (2 * m + 1)     [2n - 3]
      lemmaC_col_gen (columns);  lemmaC, lemmaC_col (n = 5, + 7);  lemmaC_nine (finrank L = 9 => both >= 2).
Laplace: pm_laplace_row u e : pm u = sum_j u (e, j) * blk e.succAbove j.succAbove u            (u : Fin (k+1) x Fin (k+1) -> C)
      pm_laplace_two u r p : pm u = sum_j sum_q u (r, j) * u (r.succAbove p, j.succAbove q) *
                                  blk (r.succAbove o p.succAbove) (j.succAbove o q.succAbove) u   (second row r' = r.succAbove p)
CA2:  ca2 (hk : k != 0) hL e xi (xi in L) (row e of xi zero) c t (t in L) : sum_j (c + t (e, j)) * blk e.succAbove j.succAbove xi = 0
      (G(xi) is orthogonal to the row-e projection of L^, any a_e);   ca2_full (hrank : m + 1 <= finrank (L.map (rowMap e))) :
      forall j, blk e.succAbove j.succAbove xi = 0   (all (n-1) x (n-1) subpermanents of xi vanish when a_e = 1).
ThA:  thA (hk : k != 0) hL r p x (x in L) (rows r and r.succAbove p of x zero) c t (t in L) :
      sum_j sum_q (c + t (r, j)) * (c + t (r.succAbove p, j.succAbove q)) * blk (..) (..) x = 0        (n = k + 2 >= 3)
SR:   single_row_SR hL a j x (x in L) (column j of x supported at row a) (x (a, j) != 0) c t (t in L)
      (forall b, c + t (a.succAbove b, j) = 0) : c = 0 and blk a.succAbove j.succAbove t = 0.
Mixed coefficients: mix m u x := sum_sigma sum_{A, |A| = m} (prod_{a in A} x (a, sigma a)) * prod_{a in A^c} u (a, sigma a);
      pm_line_expand : pm (u + s . x) = sum_{m <= n} s^m * mix m u x;   lev_mix (1 <= m <= n) : mix m (cJ + t) x = 0 for t, x in L;
      lev_mix_hat : mix m (c1 J + t1) (c2 J + t2) = n! * (C(n,m) * c1^(n-m) * c2^m)   (Theorem G's identity, row-subset form).
      mix_eq_sum_pm : mix m u x = sum_{A, |A| = m} pm (fun p => if p.1 in A then x p else u p)   (rows A from x, the others from u);
      lev_mix_pm : that sum is 0 for u = cJ + t, t, x in L, 1 <= m <= n;
      lev_rows hL R (R nonempty) x (x in L, x zero outside the rows R) c t : pm (fun p => if p.1 in R then x p else c + t p) = 0
      (perm[x_R; u_{R^c}] = 0: stage3's S12, first part; CA2 and ThA are the cases |R| = n-1, n-2 after Laplace).
Witness: zbf_witness (n != 0) hL r c x (x in U, x.1 = 0) (card beta != 0) (blkB (hat n x) != 0) : ell = 0 on U and blkA = 0 on U;
      zbf_witness' the same with the roles of the two blocks exchanged.  (SR: beta = Unit. D2: the 2x2 block q_T(x) != 0.)
More ThB: q0_isotropic_bound (q0 = 0 on P => finrank P <= 2); thB_img_or : dim Pi_T <= 2 or type B2;
      thB_Bx (card beta != 0) x in U, x.1 = 0 : complementary block perm of x is 0, or the block is of type q0.
Rows: row_proj_le : finrank (L.map (rowMap r)) <= m + 1 (n = m+2);  rows_pigeon : finrank L <= finrank (rowsZero L r1 r2) +
      finrank (L.map (rowMap r1)) + finrank (L.map (rowMap r2)).   Columns: blk_tr, ca2_col, thA_col (via lev_tr).
Linear algebra helpers: rank_nullity L f : finrank L = finrank (L inf ker f) + finrank (L.map f) (any finite-dim V);
      b_perp_bound (polar form of q0 on C^4), finrank_sup_one, one_not_mem_row, poly_zero_of_ne, poly_top, poly_coeff_zero, poly_coeff_eq.
Practical: leancheck takes 30-80 s for this file. Traps met: Polynomial.eval_finsetSum / finsetSum_coeff (new names),
 Lemma instances at (m := 1) produce Fin (1 + 2), which omega treats as a different atom from Fin 3 -- give the `have` its type.

STATUS 16:50: read BRIEF, NOTES-lean, NOTES-chief secs 2-4, Frame210. Plan: self-contained file Zbf.lean (no Kit needed):
 pm = Matrix.permanent of the pair-function; R0 by scaling + polynomial identity (no P_5 bridge needed); ZBF from
 Mathlib's sumCongrHom range lemma (same shape as det_fromBlocks_zero); UFD step replaced by a LINE lemma
 (P*Q = nonzero constant in C[s] => P constant) giving f_1 = k ell^|S| on U directly, and the domain property along lines for the ell = 0 case.
STATUS 17:00: Zbf.lean compiles (840 lines): R0, ZBF, UFD replacement, ThB(B1), Lemma C (general form, rows, n = 5). Backup Zbf_v1_ok.lean.
 Next: column version (transpose), general n (2n-3), Laplace along a row + CA2 by the direct Laplace argument, ThB trichotomy.
STATUS 17:17: Zbf.lean (1560 lines) compiles with, in addition: Lemma C for general n = m+2 (dim L <= dim L_{rr'} + 2n-3, rows and
 columns, lemmaC_gen / lemmaC_col_gen), dim-9 corollary lemmaC_nine, ThB trichotomy thB_cases, Laplace along a row pm_laplace_row and
 along two rows pm_laplace_two (both derived from ZBF + row linearity), CA2 by the direct Laplace argument (ca2, ca2_full), Theorem A
 (thA), GZ-a lineality (zbf_lineality), SR single-row lemma (single_row_SR), and N3 (3x3 level => dim <= 3, theorem n3) proved from
 Lemma C + one explicit 3x3 identity. Backups Zbf_v1..v4_ok.lean. No paper step failed so far.
STATUS 17:30: Zbf.lean v6 (1832 lines) compiles; adds lev_mix / lev_mix_hat (all mixed coefficients), thB_pair (equiv-free ThB),
 pm_zero_block_sets (finset ZBF), FK block lemma. RESULT table and API guide written above.
STATUS 17:40: FINAL. Zbf.lean v9 (2015 lines) and FrameZbf.lean both compile (exit 0, standard axioms, format 0). Added since 17:30:
 zbf_witness(') (D2/SR in general form), rows_pigeon, row_proj_le, thB_img_or, thB_Bx, q0_isotropic_bound, column versions ca2_col,
 thA_col, and mix_eq_sum_pm / lev_mix_pm / lev_rows. All four targets of the task are COMPILED; no paper step failed.
 Best next Lean steps: (1) C4 (needs the classification of symmetric zero-diagonal C of rank 2 with z_1^T C z_2 = 0 on a codim-2
 space); (2) Theorem G in subpermanent form (needs the generalised Laplace expansion grouping sigma by sigma(A)); (3) n = 4 testbed
 L-gct-091 with lemmaC_gen (m := 2): dim L >= 6 forces a nonzero 2-row element for every row pair and a 2-column element for every
 column pair.

## ROUND 2 (start 17:48, budget 2 h -> ends ~19:48); file lean/zbf/Zbf2.lean = Zbf.lean + new sections (same namespace)
STATUS 17:58 (round 2): Zbf2.lean v1 compiles. NEW: the whole chain R0 -> ZBF/UFD -> ThB -> Lemma C now also for an ARBITRARY BASE POINT b
 (BLev b kappa L := kappa != 0 and pm(c b + t) = kappa c^n for t in L; blev_of_const from "pm(b + t) = pm b != 0 on L"):
 zbf_prodB, zbf_ufdB, zbf_zeroB, thB_quadB/kerB/imgB/dimB, lemmaC_genB, lemmaC_col_genB. Consequence: Steps 1-2 of N3' are replaced by
 Lemma C at n = 3 for the base point b (n3p_row, n3p_col), and N3' is reduced to the explicit hypothesis N3Core (= Steps 3-4 of
 stage3 sec. 10: dim V_0 = 4 exactly, a nonzero single-row element in every row and a single-column element in every column => False):
 theorem n3prime_of_core (hcore : N3Core) b V0 (pm b != 0) (pm(b + eta) = pm b on V0) : finrank V0 <= 3.
STATUS 18:20 (round 2): Zbf2.lean v5 compiles (3112 lines, exit 0, standard axioms, format 0; snapshots Zbf2_v1..v5_ok.lean). Added since 17:58:
 - n3prime_L (Corollary N3'-L, for any n = |alpha| + 3, CONDITIONAL on the statement of N3' passed as hypothesis hN3):
   finrank (blockSpace L r c inf ker fst) <= 3 + finrank (colsOff L c)   [= dim{t in L : t[rr';T^c] = 0} <= 3 + m^T].
 - n3prime_weak (UNCONDITIONAL): perm(b) != 0, perm(b + eta) = perm(b) on V0  =>  finrank V0 <= 4  (Lemma C at the base point b for
   the three row pairs + independence of the three single-row spaces). So only "4 is impossible" (= N3Core) is missing for N3'.
 - (P): rowsZeroS L S (X_S), rows_submodular (d_S + d_S' <= d_{S cap S'} + d_{S cup S'}), rows_rank (rank-nullity for one more row),
   rowsZeroS_empty/_pair/_mono/_insert; same for arbitrary CELL sets: cellsZero, cells_submodular, cells_rank.
   (G1): rows_disjoint_bound, rows_inj_bound.  (G2): stage3_G2 (concrete, rows relabelled by a permutation rho of Fin 5, dS L rho S).
 - Theorem G, identity part: pm_mask_sum (generalised Laplace along a row set A: pm u = sum_T pm (maskAT A T u)), pm_mask_zero
   (|T| != |A| gives 0), pm_mask_factor / thG_term (the term is perm(v[A,T]) * perm(u[A^c,T^c])), thG_masked
   (sum_{|A| = m} sum_T ... = n! C(n,m) c1^(n-m) c2^m). The rho_k inequalities are NOT done.
 - base-point versions of the polarization identities: blev_line, blev_mix, blev_rows.
STATUS 18:45 (round 2): *** THEOREM N3' IS FULLY PROVED IN LEAN (unconditional), and so is Corollary N3'-L. ***
 File lean/zbf/Zbf3.lean (= Zbf2.lean + N3' sections; 4060 lines; exit 0; axioms propext/Classical.choice/Quot.sound; format 0;
 snapshots Zbf3_v1..v3_ok.lean). The final theorem PEqualNP.Outside.L_gct_210_zbf now also contains N3' in definition-free form:
   forall b V0, (sum_{f : Fin 3 emb Fin 3} prod_i b(i, f i)) != 0 -> (forall eta in V0, perm(b + eta) = perm(b)) -> finrank V0 <= 3.
 Names: n3prime (N3'), n3prime_L_full (N3'-L: finrank (blockSpace L r c inf ker fst) <= 3 + finrank (colsOff L c), any n = |alpha|+3).
 THE LEAN PROOF IS NOT THE PAPER PROOF (no step of the paper's Steps 1-4 was contradicted; they were bypassed):
  Steps 1-2 -> Lemma C at the base point b (lemmaC_genB, n = 3): if dim V0 >= 4 every row carries a nonzero single-row element x_r
     and every column a nonzero single-column element y_j (n3p_row, n3p_col); reduce to dim V0 = 4 (exists_sub_finrank).
  Steps 3-4 -> explicit algebra (n3core_of_alg, n3alg). W(r,j) := x_r(r,j), Y(i,j) := y_j(i,j). Bad b W Y := perm(b) != 0 and
     perm(b + D_alpha W + Y D_beta) = perm(b) for all alpha, beta, rows of W and columns of Y nonzero. K := {(alpha,beta) :
     D_alpha W = Y D_beta} has dim >= 6 - 4 = 2 (relMap). Three coefficient lemmas at canonical positions (bad_X1c: two cells
     E_00, E_01 in V0 are impossible [= the content of the paper's Step 3]; bad_X3c: two single-entry rows of W in different columns
     are impossible [= paper's 4(c)]; bad_X4c: a single-entry row r0 at column j0 forces W_il Y_i'm = 0 on the complementary 2x2
     block [= the leading form of 4(e)]), each proved by Moebius extraction of coefficients of the multi-affine polynomial
     (certificates generated and numerically checked by lean/zbf/py/gen_alg.py, gen_n3p.py), transported to arbitrary positions by
     row/column permutations and transposition (bad_rel, bad_tr, bad_X1, bad_XX, bad_X4). Structure: take k^0, k^1, k^2 in K nonzero
     with alpha-coordinate r equal to 0 for k^r; n3_SE2 (a row c with alpha_c != 0 in two elements whose zero sets cover the other two
     rows is single-entry, with the matching column of Y a multiple of e_c), n3_block (a single-entry row c and an element of K with
     alpha_c = 0 and both other coordinates nonzero is impossible), n3_XX (two single-entry rows are impossible); a 9-atom
     propositional case analysis finishes (checked by brute force in gen_n3p.py before compiling).
 Also: N3' with the weaker bound 4 has a 20-line proof (n3prime_weak) and N3Core / N3Alg remain in the file as named statements.
STATUS 19:00 (round 2): *** C4 IS FULLY PROVED IN LEAN (unconditional) *** : lean/zbf/Zbf4.lean (4313 lines, 210 KB, exit 0,
 axioms ok, format 0; snapshot Zbf4_v1_ok.lean). Statement `c4`: Lev 5 L, rows r != r' = r.succAbove p,
 finrank L = finrank (rowsZero L r r') + 7 (pair minimal for Lemma C; any dim L, not only 9), finrank row_r(L) = finrank row_r'(L) = 4
 (a_r = a_r' = 1)  ==>  for all x in X_{rr'}, all j0, q0 : Bx r p x j0 q0 = 0 (the 3x3 subpermanent of x on the other three rows and
 the columns other than j0, j0.succAbove q0).
 THE LEAN PROOF IS NOT THE PAPER PROOF (no classification of C = a b^T + b a^T, no maximal isotropic subspaces, no mu, beta):
   suppose B_x[T] != 0, T = {j0, l0}. (i) ZBF witness (zbf_witness) for rows {r,r'} x columns T^c: ell = 0 on U_T, so U_T in L and
   dim U_T >= dim L - 5. (ii) c4_right (ThA + row_r(L^) = C^5): every t in L with row r = 0 has row r' in the right kernel of B_x;
   so an element of U_T whose row r vanishes has row r' = 0 on T (B_x[T] != 0 and its row r' is supported on T): it lies in X.
   Hence row r maps U_T ONTO C^T (dim U_T - dim X >= 2): e_j0, e_l0 in row_r(L). (iii) c4_left: N := row_r(L cap {row r' = 0})
   (dim = dim L - 4 - dim X = 3) is in the left kernel of B_x, and e_j0, e_l0 are independent modulo that kernel (B_x[j0,l0] != 0,
   zero diagonal). So dim row_r(L) >= 5 > 4. Contradiction.  No paper step failed; the paper proof was simply not needed.
STATUS 19:20 (round 2): Zbf6.lean compiles (4614 lines; snapshot Zbf6_v1_ok.lean). C7/C7'' formalized modulo ONE explicit hypothesis
 (c7_rows, hypothesis hI): c7_pair_thB (ThB => pair alternative), c7_tau / c7_pair_x (pair criterion (a),(b),(d) of C7' by explicit test
 vectors z*, z_0, z_0 + z*; no division), c7_sep / c7_types (plane combinatorics => Type I / II, general index type). The corrected form of
 (d) in C7'' (omega_j + omega_l = 0 AND sigma_j = sigma_l) is what the Lean proof derives and uses. RESULT table + API guide for round 2
 are at the top of this file. Next (time permitting): derive hI from the dimension count (c7_lift).
STATUS 19:36 (round 2): Zbf10.lean compiles (5177 lines, 253 KB; snapshots Zbf7..Zbf10_v1_ok). C7/C7'' is now COMPLETE with no
 explicit-hypothesis hole: c7_lift (dimension count: I^ = L.map(row pair) + C(1,1) has dim 8 = dim of the space cut out by two independent
 relations), c7_hI, c7_rows_full, c7_rows_ind (non-constancy of rho, rho' from row ranks >= 4 + independence), fk_annihilator and
 second_relation (existence of the annihilator data via Mathlib's Submodule.exists_dual_map_eq_bot_of_notMem), c7_final (statement
 about L only). The final placeholder theorem now also contains C4. Checker sanity test passed (a deliberately false lemma is rejected).
 FrameZbf2.lean (Frame210 kit + current ZBF210 namespace + bridge lev_iff_F210 + final theorem) assembled; compile result below.
STATUS 19:36 (cont.): FrameZbf2.lean COMPILES (exit 0, axioms ok, format 0; 6554 lines, 320 KB; log lean/zbf/frame2.log): the P_k tools of
 Frame210 (namespaces MethodCeiling, Helpers.Minc, Helpers.RankOne, Kit086, F210) and all ZBF210 results of rounds 1-2 coexist in one file.
STATUS 19:42 (round 2, FINAL): Zbf11.lean (5227 lines, 256 KB) and FrameZbf2.lean (6604 lines, 323 KB) both compile: exit 0, axioms
 [propext, Classical.choice, Quot.sound], format counts 0. Added since 19:36: dotD, perp_bound, rank_one_bound (linear-algebra core of the
 ThG inequality). Round-2 targets: (1) N3' + N3'-L COMPILED; (2) C4 COMPILED; (3) C7/C7'' COMPILED (c7_final); (4) (P),(G1),(G2) COMPILED;
 (5) ThG identity + rank-one bound COMPILED, the rho_k / K_2 inequalities NOT assembled. No paper step failed.
 Best next steps for a continuation: (a) ThG: define A_k(u) on the index type {(A,T)} and combine thG_masked + pm_mask_factor +
 rank_one_bound (generalise rank_one_bound from Fin N to a Fintype index); (b) Type I / II normal forms of stage2 section 3 from c7_final
 (sum kappa = sum kappa' = 1, sum nu + sum nu' = 0 are available as conjuncts); (c) T0 / T1 / T2 of stage2 (triples) on top of zbf_prod for
 3x2 blocks and n3prime_L_full; (d) column versions of c4 / c7 by transposition (lev_tr, as done for lemmaC_col_gen).
