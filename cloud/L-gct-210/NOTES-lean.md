# NOTES-lean (role: lean, start 12:29, budget 90 min -> ends ~13:59)

## RESULT (lean framework, all files compile with leancheck: exit 0, axioms propext/choice/Quot.sound, format all 0)
Files in /home/claude/work/L-gct-210/lean/ :
- Frame210.lean (67 KB): Kit.lean (MethodCeiling + Minc + RankOne + Kit086, unchanged) + NEW namespace
  PEqualNP.Gct.F210 (all lemmas below) + placeholder theorem PEqualNP.Outside.L_gct_210_frame (= dc_zero).
- Frame210Fermat.lean (120 KB): same + KitFermat body (Kneser L065 `PEqualNP.Gct.Kit086.kneser`, iterated Fermat
  L067 `PEqualNP.Gct.Kit086.fermat_iter`, `PEqualNP.Gct.Helpers.perp_bound` (dot-product orthogonality:
  V ⊥ W => dim V + dim W <= card ι)). Use this one if you need Kneser/Fermat/perp_bound.
- Pieces: KitBase.part (Kit without its test theorem), F210.part (new namespace + placeholder). Rebuild:
  cat KitBase.part F210.part > Frame210.lean.
PROVED (Lean-checked): the case d = 0 (L ∩ DC = 0 => dim L <= 8), the reduction gap <= (S), the WLOG
  transpose version of (S), the exact split dim L = d + r_A + rank(colSum on L ∩ ker rowSum), the sufficient
  conditions "row-centred part of L has dim <= 4" / "column-centred part <= 4", full polarization of P_3 on L,
  and the explicit P_3 coupling identity between L ∩ DC and L (section 4). Nothing about (S) itself.

### How to finish the gap once (S) is proved
Final file = Frame210.lean with the last theorem replaced by
  theorem PEqualNP.Outside.L_gct_210 : <gap statement verbatim> := by
    exact PEqualNP.Gct.F210.gap_of_S S_proof        (or gap_of_S_wlog S'_proof)
where S_proof is your proof of the hypothesis of gap_of_S (copy your lemmas into the file before it;
no comments / quotes / # / banned words).

## Conventions (namespace PEqualNP.Gct.F210; `open Finset PEqualNP.Gct.Helpers.Minc` inside it)
- Matrices: t : Fin n × Fin n → ℂ, entry t (i, j). Frobenius products written ∑ p, t p * u p (p over pairs).
- Level condition of the gap is used verbatim:  hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120.
  General n:  def Lev (n) (L) : Prop := ∀ t ∈ L, (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i))) = (Nat.factorial n : ℂ)
  lev_five L hL : Lev 5 L     (converts the gap hypothesis).
- rowSum n, colSum n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)   (row / column SUMS; alpha_i = rowSum/5, i.e.
  "rowMean" = (1/5) rowSum, same kernel and rank, so r_A, r_B below are the ranks of the row/col-mean maps).
  rowSum_apply : rowSum n t i = ∑ j, t (i, j);   colSum_apply : colSum n t j = ∑ i, t (i, j)
- DC n : Submodule := LinearMap.ker ((rowSum n).prod (colSum n))
  mem_DC_iff t : t ∈ DC n ↔ rowSum n t = 0 ∧ colSum n t = 0
  mem_DC t     : t ∈ DC n ↔ (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0)
- sumZero n : Submodule ℂ (Fin n → ℂ) := ker (∑ i, proj i);  mem_sumZero v : v ∈ sumZero n ↔ ∑ i, v i = 0
- The three numbers of the split:  d = finrank ℂ (L ⊓ DC 5 : Submodule ℂ _),
  r_A = finrank ℂ (L.map (rowSum 5)),  r_B = finrank ℂ (L.map (colSum 5)).

## 1. Bridge lemmas (homogeneous parts vanish)
- gap_eq_perm n t : (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i))) = MvPolynomial.eval (fun p => 1 + t p) (permPoly ℂ n)
- lev_perm  (hL : Lev n L) : ∀ t ∈ L, eval (1+t) (permPoly ℂ n) = n!      (Kit/L092 form)
- lev_Mk    (hL : Lev n L) : ∀ t ∈ L, ∀ k, 1 ≤ k → k ≤ n → Mk n k t = 0
     Mk n k t = ∑ S T : k-subsets, perm of the k x k submatrix (P_k = sum of k x k subpermanents)
- lev_inj   (hL : Lev n L) : ∀ t ∈ L, ∀ k, 1 ≤ k → k ≤ n → ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, t (i a, j a) = 0
     (= k! * Mk n k t by RankOne.injForm; injective-pair form, matches Outside/L_gct_134 for k = 4)
- lev_of_Mk t (h : ∀ k, 1 ≤ k → k ≤ n → Mk n k t = 0) : (∑ f, ∏ i, (1 + t (i, f i))) = n!   (converse, for refutations)
- lev_sum   (hL : Lev n L) (hn : 1 ≤ n) : ∀ t ∈ L, ∑ p, t p = 0                       (P_1)
- inj_two n t : ∑ i j : Fin 2 ↪ Fin n, ∏ a, t (i a, j a) = (∑ p, t p)^2 - ∑ i, (∑ j, t (i, j))^2 - ∑ j, (∑ i, t (i, j))^2 + ∑ p, t p^2
- lev_two   (hL) (hn : 2 ≤ n) : ∀ t ∈ L, ∑ p, t p ^ 2 = ∑ i, rowSum n t i ^ 2 + ∑ j, colSum n t j ^ 2   (P_2 with P_1)
- lev_two_pol (hL) (hn : 2 ≤ n) : ∀ t ∈ L, ∀ u ∈ L, ∑ p, t p * u p = ∑ i, rowSum n t i * rowSum n u i + ∑ j, colSum n t j * colSum n u j
- dc_orth   (hL) (hn : 2 ≤ n) : ∀ d ∈ L ⊓ DC n, ∀ u ∈ L, ∑ p, d p * u p = 0     (DC part ⊥ all of L)
- POLARIZATION (all P_k, two vectors):
  def polSum n k m t u := ∑ i j : Fin k ↪ Fin n, ∑ A ∈ univ.filter (fun A : Finset (Fin k) => A.card = m),
                            (∏ a ∈ A, u (i a, j a)) * ∏ a ∈ Aᶜ, t (i a, j a)
  lev_pol (hL : Lev n L) t u (ht : t ∈ L) (hu : u ∈ L) k (1 ≤ k) (k ≤ n) m (m ≤ k) : polSum n k m t u = 0
  (= coefficient of s^m in the injective sum of t + s u; m = 1 is "u ⊥ grad P_k(t)", m = 2 the Hessian
   H^k_t(u,u); three-vector forms follow by applying it to u = s + s' etc.)
  helper prod_add_smul x y s : ∏ a, (x a + s * y a) = ∑ m ∈ range (k+1), s^m * ∑ A (card m), (∏_A y) * ∏_{Aᶜ} x
- dcPart n t := fun p => t p - rowSum n t p.1 / n - colSum n t p.2 / n;
  dcPart_decomp : t (i, j) = rowSum n t i / n + colSum n t j / n + dcPart n t (i, j)
  dcPart_mem (hn : 1 ≤ n) t (h : ∑ p, t p = 0) : dcPart n t ∈ DC n      (t = alpha_i + beta_j + gamma)

## 2. Decomposition
- finrank_sumZero (hn : 1 ≤ n) : finrank ℂ (sumZero n) ≤ n - 1
- map_rowSum_le / map_colSum_le (hL : Lev n L) (hn : 1 ≤ n) : L.map (rowSum n) ≤ sumZero n   (images in the hyperplane, by P_1)
- rA_le / rB_le (hL : Lev n L) (hn : 1 ≤ n) : finrank ℂ (L.map (rowSum n)) ≤ n - 1   (resp. colSum)
- finrank_split L : finrank ℂ L = finrank ℂ (L ⊓ DC n) + finrank ℂ (L.map ((rowSum n).prod (colSum n)))   (exact)
- finrank_map_prod_le L f g : finrank (L.map (f.prod g)) ≤ finrank (L.map f) + finrank (L.map g)
- dim_le L : finrank ℂ L ≤ finrank ℂ (L ⊓ DC n) + finrank ℂ (L.map (rowSum n)) + finrank ℂ (L.map (colSum n))
- skeleton_le L hL (n = 5, gap form) : finrank L ≤ d + r_A + r_B ∧ r_A ≤ 4 ∧ r_B ≤ 4

## 3. d = 0 and the skeleton (n = 5, gap form of hL)
- dc_zero L hL (hd : L ⊓ DC 5 = ⊥) : finrank ℂ L ≤ 8                        [the easy case, PROVED]
- skeleton L hL (hS : min r_A r_B + d ≤ 4) : finrank ℂ L ≤ 8
- gap_of_S (hS : ∀ L, hL-form → min r_A r_B + d ≤ 4) : ∀ L, hL-form → finrank ℂ L ≤ 8   (= the gap statement)
- gap_of_S_wlog (hS : ∀ L, hL-form → r_A ≤ r_B → r_A + d ≤ 4) : same conclusion
  (uses transpose: trE n : ≃ₗ, trE_apply : trE n t (i, j) = t (j, i); gap_swap; lev_tr : Lev n L → Lev n (L.map trE);
   rowSum_tr, colSum_tr, map_tr_rowSum, map_tr_colSum, finrank_tr_DC : d(L) ≤ d(L.map trE)).
  Exact Lean form of the WLOG hypothesis:
   ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
     Module.finrank ℂ (L.map (rowSum 5)) ≤ Module.finrank ℂ (L.map (colSum 5)) →
     Module.finrank ℂ (L.map (rowSum 5)) + Module.finrank ℂ (L ⊓ DC 5 : Submodule ℂ _) ≤ 4

## 4. Extra tools (all in Frame210.lean, namespace F210)
- lev_mono (hL : Lev n L) (hK : K ≤ L) : Lev n K
- rank_nullity L f : finrank L = finrank (L ⊓ ker f) + finrank (L.map f)      (f any linear map out of matrices)
- finrank_exact L : finrank L = finrank (L ⊓ DC n) + finrank (L.map (rowSum n))
                               + finrank ((L ⊓ LinearMap.ker (rowSum n)).map (colSum n))       (EXACT, no inequality)
- rowCentred_suff L hL (h : finrank (L ⊓ LinearMap.ker (rowSum 5) : Submodule ℂ _) ≤ 4) : finrank L ≤ 8
  colCentred_suff L hL (h : finrank (L ⊓ LinearMap.ker (colSum 5) : Submodule ℂ _) ≤ 4) : finrank L ≤ 8
  (dim L = r_A + dim(row-centred part); NB the 4x5 row-centred space padded has row-centred part 6, so these only
   help in combination with case splits)
- Trilinear P_3:  def T3 n x y z := ∑ i j : Fin 3 ↪ Fin n, x (i 0, j 0) * y (i 1, j 1) * z (i 2, j 2)
  T3_add1/2/3, T3_smul1/2/3 (multilinear), T3_swap12 : T3 n x y z = T3 n y x z, T3_swap23 : T3 n x y z = T3 n x z y,
  T3_diag : T3 n t t t = ∑ i j : Fin 3 ↪ Fin n, ∏ a, t (i a, j a)
  lev_T3 (hL : Lev n L) (hn : 3 ≤ n) : ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L, T3 n x y z = 0      (FULL polarization of P_3)
- sum_emb_perm σ F : ∑ i : Fin k ↪ Fin n, F (σ.toEmbedding.trans i) = ∑ i, F i        (slot permutation)
- sum_emb_succ Φ : ∑ i : Fin (k+1) ↪ Fin n, Φ (i 0) (fun b => i b.succ)
                   = ∑ e : Fin k ↪ Fin n, ∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a), Φ a e   (peel one slot)
- dc_compl d (hd : d ∈ DC n) p q : ∑ a ∈ filter p, ∑ x ∈ filter q, d (a, x) = ∑ a ∈ filter ¬p, ∑ x ∈ filter ¬q, d (a, x)
- sum_range_emb e g : ∑ a ∈ univ.filter (fun a => ¬ ∀ b, e b ≠ a), g a = ∑ b, g (e b)
- DC PEELING (any k): inj_dc_peel d (hd : d ∈ DC n) H :
    ∑ i j : Fin (k+1) ↪ Fin n, d (i 0, j 0) * H (fun b => i b.succ) (fun b => j b.succ)
      = ∑ e f : Fin k ↪ Fin n, H e f * ∑ b, ∑ c, d (e b, f c)
  MkPol_dc_peel ts (hd : ts 0 ∈ DC n) : RankOne.MkPol n (k+1) ts = ∑ e f : Fin k ↪ Fin n, (∏ b, ts b.succ (e b, f b)) * ∑ b, ∑ c, ts 0 (e b, f c)
  (MkPol n k ts = ∑ i j : Fin k ↪ Fin n, ∏ a, ts a (i a, j a) is Kit's full polarization of k! P_k)
- T3_dc d y z (hd) : T3 n d y z = ∑ e f : Fin 2 ↪ Fin n, y (e 0, f 0) * z (e 1, f 1) * (d (e 0, f 0) + d (e 0, f 1) + d (e 1, f 0) + d (e 1, f 1))
  lev_T3_dc : the same sum = 0 for d ∈ L ⊓ DC n, y z ∈ L.
  offdiag2 F (two-index off-diagonal expansion), T3_dc_sums (4 multi-index sums), dcA1a..dcA4 (factorisations),
  T3_dc_closed d y z (hd) (general closed form, with the S(y), S(z) terms).
- P_3 COUPLING IDENTITY (closed form, n >= 3):
  lev_P3_dc (hL : Lev n L) (hn : 3 ≤ n) : ∀ d ∈ L ⊓ DC n, ∀ y ∈ L, ∀ z ∈ L,
      ∑ a, ∑ w, d (a, w) * (rowSum n y a * colSum n z w) + ∑ b, ∑ x, d (b, x) * (rowSum n z b * colSum n y x)
      + ∑ a, ∑ x, 4 * (d (a, x) * y (a, x) * z (a, x))
    = ∑ a, 2 * ((∑ x, d (a, x) * y (a, x)) * rowSum n z a + rowSum n y a * (∑ w, d (a, w) * z (a, w)))
      + ∑ x, 2 * ((∑ a, d (a, x) * y (a, x)) * colSum n z x + colSum n y x * (∑ b, d (b, x) * z (b, x)))
  i.e.  4<d, y∘z> + d(r_y, c_z) + d(r_z, c_y) = 2(<r_{d∘y}, r_z> + <r_y, r_{d∘z}> + <c_{d∘y}, c_z> + <c_y, c_{d∘z}>)
  (r = row-sum vector, c = column-sum vector, d(u, v) = Σ d_aw u_a v_w, ∘ = Hadamard). For y, z both DC it
  reduces to <d, y∘z> = 0 (so L∩DC ⊥ (L∩DC)∘(L∩DC)); the row/column terms are (presumably) the split agent's
  "(1,2)-coupling". Sanity check: lean/py/chk_p3dc.py (brute-force T3 vs T3_dc_closed, err 3e-13; identity on ex.1).

## Practical notes for whoever writes the (S) proof in Lean
- Work inside `namespace PEqualNP.Gct.F210` after the existing lemmas, or refer to them with full names.
- To get P_k facts for t in L: `lev_inj (lev_five L hL) t ht k (by norm_num) (by norm_num)`; for mixed terms
  `lev_pol (lev_five L hL) t u ht hu k _ _ m _`, for P_3 with three different arguments `lev_T3`, with a DC
  argument the closed form `lev_P3_dc`. NOT done: closed forms of P_3 without a DC slot, of P_4/P_5 (use
  MkPol_dc_peel + sum_emb_two/offdiag2 as templates), and full polarization for k = 4, 5 (only the
  two-vector Taylor coefficients lev_pol exist).
- Format traps: `#` is banned, so no `#s` card notation; no `--` (also not inside identifiers); `instance`,
  `structure`, `attribute`, `notation` are banned words anywhere (also inside longer names).
- Each leancheck run ~60 s (Frame210) / ~90 s (Frame210Fermat).

STATUS 12:33: read brief, Kit.lean; planning Frame210.lean (bridge + decomposition + d=0 + skeleton).
STATUS 12:38: Frame210.lean draft compiles except 2 small errors; fixing.
STATUS 12:47: Frame210.lean v2 (dcPart, transpose WLOG, polarization lev_pol) compiles. Guide written.
STATUS 13:04: Frame210 v3 compiles (adds finrank_exact, row/colCentred_suff, T3 full polarization lev_T3, DC peeling inj_dc_peel/MkPol_dc_peel, P3 coupling identity lev_P3_dc). Updating guide.
STATUS 13:10: Frame210.lean and Frame210Fermat.lean (both with all of the above) compile, exit 0, format 0. Guide final. Done.
