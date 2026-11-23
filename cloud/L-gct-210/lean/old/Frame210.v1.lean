import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Gct.MethodCeiling

open Finset

variable {m : ℕ}

theorem perm_updateRow_eq (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) (v : Fin m → ℂ) :
    (M.updateRow r v).permanent =
      ∑ σ : Equiv.Perm (Fin m), v (σ.symm r) * ∏ i ∈ univ.erase (σ.symm r), M (σ i) i := by
  unfold Matrix.permanent
  refine sum_congr rfl fun σ _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ (σ.symm r))]
  simp only [Equiv.apply_symm_apply, Matrix.updateRow_self]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  have hne : σ i ≠ r := by
    intro h
    exact (mem_erase.1 hi).1 (by rw [← h, Equiv.symm_apply_apply])
  rw [Matrix.updateRow_ne hne]

noncomputable def rowFun (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) : (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun v := (M.updateRow r v).permanent
  map_add' u v := by
    simp only [perm_updateRow_eq, Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' c v := by
    simp only [perm_updateRow_eq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum,
      mul_assoc]

theorem rowFun_apply (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) (v : Fin m → ℂ) :
    rowFun M r v = (M.updateRow r v).permanent := rfl

theorem perm_eq_zero_of_row (M : Matrix (Fin m) (Fin m) ℂ) (r : Fin m) (h : ∀ j, M r j = 0) :
    M.permanent = 0 := by
  unfold Matrix.permanent
  refine sum_eq_zero fun σ _ => prod_eq_zero (mem_univ (σ.symm r)) ?_
  simp [h]

theorem perm_rowScale (M : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) :
    (Matrix.of fun i j => d i * M i j).permanent = (∏ i, d i) * M.permanent := by
  unfold Matrix.permanent
  rw [mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp σ d

theorem eval_permPoly (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

noncomputable def rowEmb (S : Fin m → Submodule ℂ (Fin m → ℂ)) :
    (∀ i, S i) →ₗ[ℂ] (Fin m × Fin m → ℂ) :=
  LinearMap.pi fun p => LinearMap.proj p.2 ∘ₗ (S p.1).subtype ∘ₗ LinearMap.proj p.1

theorem rowEmb_apply (S : Fin m → Submodule ℂ (Fin m → ℂ)) (x : ∀ i, S i) (i j : Fin m) :
    rowEmb S x (i, j) = (x i : Fin m → ℂ) j := rfl

theorem rowEmb_injective (S : Fin m → Submodule ℂ (Fin m → ℂ)) :
    Function.Injective (rowEmb S) := by
  intro a b h
  funext i
  apply Subtype.ext
  funext j
  exact congrFun h (i, j)

theorem finrank_range_rowEmb (S : Fin m → Submodule ℂ (Fin m → ℂ)) :
    Module.finrank ℂ (LinearMap.range (rowEmb S)) = ∑ i, Module.finrank ℂ (S i) := by
  rw [LinearMap.finrank_range_of_inj (rowEmb_injective S), Module.finrank_pi_fintype]

theorem sum_lower (f : Fin m → ℕ) (r : Fin m) (a b : ℕ) (ha : ∀ i, i ≠ r → a ≤ f i)
    (hb : b ≤ f r) : (m - 1) * a + b ≤ ∑ i, f i := by
  rw [← add_sum_erase univ f (mem_univ r)]
  have h := card_nsmul_le_sum (univ.erase r) f a fun i hi => ha i (mem_erase.1 hi).1
  rw [card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin, smul_eq_mul] at h
  have h' : (m - 1) * a ≤ ∑ x ∈ univ.erase r, f x := h
  omega

end PEqualNP.Gct.MethodCeiling

namespace PEqualNP.Gct.Helpers.Minc

open Finset

def res {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) : Fin k ↪ Fin n :=
  ⟨fun a => σ (e a), σ.injective.comp e.injective⟩

@[simp] theorem res_apply {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) (a : Fin k) :
    res e σ a = σ (e a) := rfl

def emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Fin k ↪ Fin n :=
  ⟨fun a => R.1.orderEmbOfFin R.2 (τ a), (R.1.orderEmbOfFin R.2).injective.comp τ.injective⟩

@[simp] theorem emb_apply {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k})
    (τ : Equiv.Perm (Fin k)) (a : Fin k) : emb R τ a = R.1.orderEmbOfFin R.2 (τ a) := rfl

theorem card_extend {n k : ℕ} (e f : Fin k ↪ Fin n)
    [Fintype {σ : Equiv.Perm (Fin n) // res e σ = f}] :
    Fintype.card {σ : Equiv.Perm (Fin n) // res e σ = f} = (n - k).factorial := by
  classical
  let φ : Set.range e ≃ Set.range f :=
    (Equiv.ofInjective e e.injective).symm.trans (Equiv.ofInjective f f.injective)
  let σ0 : Equiv.Perm (Fin n) := φ.extendSubtype
  have hσ0 : ∀ a, σ0 (e a) = f a := by
    intro a
    have h1 := φ.extendSubtype_apply_of_mem (e a) (Set.mem_range_self a)
    have h2 : (Equiv.ofInjective e e.injective).symm ⟨e a, Set.mem_range_self a⟩ = a :=
      Equiv.ofInjective_symm_apply e.injective a
    simp only [σ0, h1, φ, Equiv.trans_apply, h2, Equiv.ofInjective_apply]
  have hres : ∀ σ : Equiv.Perm (Fin n), res e σ = f ↔ ∀ a, σ (e a) = f a := by
    intro σ
    constructor
    · intro h a
      have := DFunLike.congr_fun h a
      simpa using this
    · intro h
      ext a
      simp [h a]
  let E : {σ : Equiv.Perm (Fin n) // res e σ = f} ≃
      {τ : Equiv.Perm (Fin n) // ∀ x, ¬ (x ∉ Set.range e) → τ x = x} :=
    { toFun := fun σ => ⟨σ0⁻¹ * σ.1, by
        intro x hx
        rw [not_not] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [Equiv.Perm.mul_apply, (hres σ.1).1 σ.2 a, ← hσ0 a]
        simp⟩
      invFun := fun τ => ⟨σ0 * τ.1, by
        rw [hres]
        intro a
        rw [Equiv.Perm.mul_apply, τ.2 (e a) (by simp), hσ0]⟩
      left_inv := fun σ => Subtype.ext (by simp)
      right_inv := fun τ => Subtype.ext (by simp) }
  rw [Fintype.card_congr E, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm _),
    Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin,
    Fintype.card_fin]

theorem sum_perm_res {n k : ℕ} (e : Fin k ↪ Fin n) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), F (res e σ) = ((n - k).factorial : ℂ) * ∑ f, F f := by
  classical
  rw [← Fintype.sum_fiberwise' (fun σ : Equiv.Perm (Fin n) => res e σ) F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_const, Finset.card_univ, card_extend, nsmul_eq_mul]

theorem range_emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Set.range (emb R τ) = (R.1 : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact Finset.orderEmbOfFin_mem R.1 R.2 _
  · intro hx
    rw [← Finset.range_orderEmbOfFin R.1 R.2] at hx
    obtain ⟨b, rfl⟩ := hx
    exact ⟨τ⁻¹ b, by simp⟩

theorem emb_bijective {n k : ℕ} :
    Function.Bijective
      (fun x : (Σ _ : {R : Finset (Fin n) // R.card = k}, Equiv.Perm (Fin k)) => emb x.1 x.2) := by
  constructor
  · rintro ⟨R, τ⟩ ⟨R', τ'⟩ h
    have h' : emb R τ = emb R' τ' := h
    have hRR : R = R' := by
      have := congrArg (fun g : Fin k ↪ Fin n => Set.range g) h'
      simp only [range_emb, Finset.coe_inj] at this
      exact Subtype.ext this
    subst hRR
    have hττ : τ = τ' := by
      ext a
      have := DFunLike.congr_fun h' a
      simp only [emb_apply] at this
      rw [(R.1.orderEmbOfFin R.2).injective this]
    subst hττ
    rfl
  · intro f
    have hc : (univ.map f).card = k := by simp
    have hm : ∀ a, f a ∈ univ.map f := fun a => by simp
    let g : Fin k → Fin k := fun a => ((univ.map f).orderIsoOfFin hc).symm ⟨f a, hm a⟩
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at hab
      exact hab
    refine ⟨⟨⟨univ.map f, hc⟩, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)⟩, ?_⟩
    ext a
    simp only [emb_apply, Equiv.ofBijective_apply, g]
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem sum_embedding {n k : ℕ} (G : (Fin k ↪ Fin n) → ℂ) :
    ∑ f, G f = ∑ R : {R : Finset (Fin n) // R.card = k}, ∑ τ : Equiv.Perm (Fin k),
      G (emb R τ) := by
  rw [← (emb_bijective (n := n) (k := k)).sum_comp G]
  exact Fintype.sum_sigma _

theorem prod_orderEmb {n k : ℕ} (C : Finset (Fin n)) (hC : C.card = k) (h : Fin n → ℂ) :
    ∏ j ∈ C, h j = ∏ a, h (C.orderEmbOfFin hC a) := by
  rw [← Finset.prod_coe_sort]
  exact (Fintype.prod_equiv (C.orderIsoOfFin hC).toEquiv _ _
    (fun a => by simp [Finset.coe_orderIsoOfFin_apply])).symm

theorem sum_perm_cols {n k : ℕ} (t : Fin n × Fin n → ℂ) (C : Finset (Fin n)) (hC : C.card = k) :
    ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) =
      ((n - k).factorial : ℂ) * ∑ R : {R : Finset (Fin n) // R.card = k},
        Matrix.permanent (Matrix.of fun i j : Fin k =>
          t (R.1.orderEmbOfFin R.2 i, C.orderEmbOfFin hC j)) := by
  calc ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j)
      = ∑ σ : Equiv.Perm (Fin n), (fun g : Fin k ↪ Fin n => ∏ a, t (g a, C.orderEmbOfFin hC a))
          (res (C.orderEmbOfFin hC).toEmbedding σ) :=
        Finset.sum_congr rfl fun σ _ => prod_orderEmb C hC _
    _ = ((n - k).factorial : ℂ) * ∑ g : Fin k ↪ Fin n, ∏ a, t (g a, C.orderEmbOfFin hC a) :=
        sum_perm_res (C.orderEmbOfFin hC).toEmbedding
          (fun g : Fin k ↪ Fin n => ∏ a, t (g a, C.orderEmbOfFin hC a))
    _ = _ := by rw [sum_embedding]; rfl

theorem eval_one_add (n : ℕ) (t : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      ∑ C : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) := by
  rw [PEqualNP.Gct.MethodCeiling.eval_permPoly, Matrix.permanent]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [Finset.sum_comm]

theorem sum_by_card {n : ℕ} (G : Finset (Fin n) → ℂ) :
    ∑ C : Finset (Fin n), G C =
      ∑ k ∈ range (n + 1), ∑ C : {C : Finset (Fin n) // C.card = k}, G C.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1))
    (fun C _ => by
      have := Finset.card_le_univ C
      rw [Fintype.card_fin] at this
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le this))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_subtype _ (by simp) G

noncomputable def Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k},
    Matrix.permanent (Matrix.of fun i j : Fin k =>
      t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j))

theorem minc_Mk (n : ℕ) (t : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) * Mk n k t := by
  rw [eval_one_add, sum_by_card]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [fun C : {C : Finset (Fin n) // C.card = k} => sum_perm_cols t C.1 C.2]
  rw [← Finset.mul_sum, Mk, Finset.sum_comm]

theorem Mk_zero (n : ℕ) (t : Fin n × Fin n → ℂ) : Mk n 0 t = 1 := by
  have hu : ∀ S : {S : Finset (Fin n) // S.card = 0}, S = ⟨∅, Finset.card_empty⟩ :=
    fun S => Subtype.ext (Finset.card_eq_zero.mp S.2)
  rw [Mk, Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Matrix.permanent_isEmpty]

theorem single_bijective (n : ℕ) :
    Function.Bijective
      (fun i : Fin n => (⟨{i}, Finset.card_singleton i⟩ : {S : Finset (Fin n) // S.card = 1})) := by
  constructor
  · intro i j h
    simpa using congrArg Subtype.val h
  · rintro ⟨S, hS⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
    exact ⟨a, rfl⟩

theorem Mk_one (n : ℕ) (t : Fin n × Fin n → ℂ) : Mk n 1 t = ∑ p, t p := by
  rw [Mk, Fintype.sum_prod_type]
  symm
  refine Fintype.sum_bijective _ (single_bijective n) _ _ (fun i => ?_)
  refine Fintype.sum_bijective _ (single_bijective n) _ _ (fun j => ?_)
  rw [Matrix.permanent_unique]
  simp [Finset.orderEmbOfFin_singleton]

theorem minc_expansion :
    ∀ (n : ℕ) (t : Fin n × Fin n → ℂ),
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
        ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) *
          ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k},
            Matrix.permanent (Matrix.of fun i j : Fin k =>
              t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j)) :=
  fun n t => minc_Mk n t

end PEqualNP.Gct.Helpers.Minc


namespace PEqualNP.Gct.Helpers.RankOne

open Finset

abbrev KSub (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

noncomputable def Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ S : KSub n k, ∑ T : KSub n k,
    Matrix.permanent (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i,
      T.1.orderEmbOfFin T.2 j))

def emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) : Fin k ↪ Fin n :=
  ⟨fun b => S.1.orderEmbOfFin S.2 (σ b), (S.1.orderEmbOfFin S.2).injective.comp σ.injective⟩

theorem range_emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) :
    Set.range (emb S σ) = (S.1 : Set (Fin n)) := by
  change Set.range ((S.1.orderEmbOfFin S.2) ∘ σ) = _
  rw [σ.surjective.range_comp, Finset.range_orderEmbOfFin]

theorem emb_bijective (n k : ℕ) :
    Function.Bijective (fun p : KSub n k × Equiv.Perm (Fin k) => emb p.1 p.2) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    simp only at h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_emb S σ, ← range_emb T τ, h]
    subst hST
    have hστ : σ = τ := by
      ext b
      have := DFunLike.congr_fun h b
      exact congrArg Fin.val ((S.1.orderEmbOfFin S.2).injective this)
    rw [hστ]
  · intro i
    let S : KSub n k := ⟨Finset.univ.map i, by simp⟩
    have hmem : ∀ b, i b ∈ S.1 := fun b => by simp [S]
    let f : Fin k → Fin k := fun b => (S.1.orderIsoOfFin S.2).symm ⟨i b, hmem b⟩
    have hf : Function.Injective f := by
      intro b c hbc
      have := congrArg (fun x => ((S.1.orderIsoOfFin S.2 x : S.1) : Fin n)) hbc
      simp only [f, OrderIso.apply_symm_apply] at this
      exact i.injective this
    refine ⟨(S, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)), ?_⟩
    ext b
    simp only [emb, Function.Embedding.coeFn_mk, Equiv.ofBijective_apply]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [f]

theorem sum_emb (n k : ℕ) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ i, F i = ∑ S : KSub n k, ∑ σ : Equiv.Perm (Fin k), F (emb S σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (emb_bijective n k) (fun p => F (emb p.1 p.2)) F
    (fun _ => rfl)).symm

theorem sum_perm_perm (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) :
    ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a)
      = (k.factorial : ℂ) * M.permanent := by
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin k),
      ∑ σ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a) = M.permanent := by
    intro τ
    have h1 : ∀ σ : Equiv.Perm (Fin k),
        ∏ a, M (σ a) (τ a) = ∏ b, M ((σ * τ⁻¹) b) b := by
      intro σ
      exact Fintype.prod_equiv τ _ _ (fun a => by simp)
    simp_rw [h1]
    unfold Matrix.permanent
    exact Fintype.sum_equiv (Equiv.mulRight τ⁻¹) _ _ (fun _ => rfl)
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem injForm (n k : ℕ) (t : Fin n × Fin n → ℂ) :
    (k.factorial : ℂ) * Mk n k t
      = ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, t (i a, j a) := by
  rw [sum_emb n k]
  simp_rw [sum_emb n k (fun j => ∏ a, t (_, j a))]
  rw [Mk, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← sum_perm_perm]
  rfl

noncomputable def MkPol (n k : ℕ) (ts : Fin k → Fin n × Fin n → ℂ) : ℂ :=
  ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, ts a (i a, j a)

theorem MkPol_diag (n k : ℕ) (t : Fin n × Fin n → ℂ) :
    MkPol n k (fun _ => t) = (k.factorial : ℂ) * Mk n k t :=
  (injForm n k t).symm

noncomputable def Inj (n k : ℕ) (x : Fin k → Fin n → ℂ) : ℂ :=
  ∑ i : Fin k ↪ Fin n, ∏ a, x a (i a)

theorem MkPol_rankOne (n k : ℕ) (u w : Fin k → Fin n → ℂ) :
    MkPol n k (fun a p => u a p.1 * w a p.2) = Inj n k u * Inj n k w := by
  simp only [MkPol, Inj, Finset.prod_mul_distrib, Finset.sum_mul_sum]

theorem Inj_const (n k : ℕ) (x : Fin n → ℂ) :
    Inj n k (fun _ => x) = (k.factorial : ℂ) * ∑ S : KSub n k, ∏ i ∈ S.1, x i := by
  rw [Inj, sum_emb n k, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have h1 : ∀ σ : Equiv.Perm (Fin k),
      ∏ a, x (emb S σ a) = ∏ i ∈ S.1, x i := by
    intro σ
    have h2 : ∏ a, x (emb S σ a) = ∏ b, x (S.1.orderEmbOfFin S.2 b) :=
      Fintype.prod_equiv σ _ _ (fun _ => rfl)
    rw [h2]
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S.1 S.2, Finset.prod_map]
    rfl
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem Mk_rankOne (n k : ℕ) (x y : Fin n → ℂ) :
    Mk n k (fun p => x p.1 * y p.2)
      = (k.factorial : ℂ) * (∑ S : KSub n k, ∏ i ∈ S.1, x i)
          * (∑ T : KSub n k, ∏ j ∈ T.1, y j) := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h := MkPol_rankOne n k (fun _ => x) (fun _ => y)
  rw [MkPol_diag, Inj_const, Inj_const] at h
  apply mul_left_cancel₀ hk
  rw [h]
  ring

end PEqualNP.Gct.Helpers.RankOne


namespace PEqualNP.Gct.Kit086

open Finset PEqualNP.Gct.Helpers.Minc

theorem Mk_smul (n k : ℕ) (s : ℂ) (t : Fin n × Fin n → ℂ) :
    Mk n k (s • t) = s ^ k * Mk n k t := by
  unfold Mk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  have h : (Matrix.of fun i j : Fin k => (s • t) (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j))
      = s • (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j)) := by
    ext i j
    simp
  rw [h, Matrix.permanent_smul, Fintype.card_fin]

theorem level_Mk_zero (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) :
    ∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n → Mk n k t = 0 := by
  intro t ht k hk1 hkn
  let P : Polynomial ℂ := ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (((n - j).factorial : ℂ) * Mk n j t) * Polynomial.X ^ j
  have hP : ∀ s : ℂ, P.eval s = (Polynomial.C (Nat.factorial n : ℂ)).eval s := by
    intro s
    have h1 := hL (s • t) (L.smul_mem s ht)
    rw [minc_Mk] at h1
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Mk_smul]
    ring
  have hPeq : P = Polynomial.C (Nat.factorial n : ℂ) := Polynomial.funext hP
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff k) hPeq
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C] at hc
  rw [Finset.sum_eq_single k] at hc
  · have hk0 : k ≠ 0 := by omega
    simpa [hk0, Nat.factorial_ne_zero] using hc
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hk
    exact absurd (Finset.mem_range.mpr (by omega)) hk

theorem level_of_Mk_zero (n : ℕ) (t : Fin n × Fin n → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ n → Mk n k t = 0) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ) := by
  rw [minc_Mk, Finset.sum_eq_single 0]
  · simp [Mk_zero]
  · intro k hk hk0
    rw [h k (by omega) (by simpa [Nat.lt_succ_iff] using hk), mul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

theorem reduce_dc : ∀ (n G : ℕ), (∀ K : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ K, (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0)) → (∀ t ∈ K, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → Module.finrank ℂ K ≤ G) → ∀ L : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → Module.finrank ℂ L ≤ G + 2 * n := by
  intro n G hG L hL
  let phi : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin n → ℂ) :=
    LinearMap.prod (LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j))
      (LinearMap.pi fun j => ∑ i, LinearMap.proj (i, j))
  have hK : Module.finrank ℂ (L ⊓ LinearMap.ker phi : Submodule ℂ _) ≤ G := by
    apply hG
    · intro t ht
      have h0 : phi t = 0 := ht.2
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have := congrFun (congrArg Prod.fst h0) i
        simpa [phi, LinearMap.sum_apply] using this
      · have := congrFun (congrArg Prod.snd h0) j
        simpa [phi, LinearMap.sum_apply] using this
    · intro t ht
      exact hL t ht.1
  have hrn : Module.finrank ℂ (L.map phi) + Module.finrank ℂ (L ⊓ LinearMap.ker phi : Submodule ℂ _)
      = Module.finrank ℂ L := by
    rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
      ← (phi.submoduleMap L).finrank_range_add_finrank_ker,
      LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]
    simp
  have hmap : Module.finrank ℂ (L.map phi) ≤ 2 * n := by
    have := Submodule.finrank_le (L.map phi)
    simpa [Module.finrank_prod, two_mul] using this
  omega

theorem level_inj_zero (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) :
    ∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, t (i a, j a) = 0 := by
  intro t ht k hk1 hkn
  rw [← PEqualNP.Gct.Helpers.RankOne.injForm]
  have h := level_Mk_zero n L hL t ht k hk1 hkn
  have he : PEqualNP.Gct.Helpers.RankOne.Mk n k t = Mk n k t := rfl
  rw [he, h, mul_zero]

end PEqualNP.Gct.Kit086


namespace PEqualNP.Gct.F210

open Finset PEqualNP.Gct.Helpers.Minc

def Lev (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) : Prop :=
  ∀ t ∈ L, (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i))) = (Nat.factorial n : ℂ)

theorem gap_eq_perm (n : ℕ) (t : Fin n × Fin n → ℂ) :
    (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i))) =
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) := by
  rw [PEqualNP.Gct.MethodCeiling.eval_permPoly, ← Matrix.permanent_transpose, Matrix.permanent]
  have hb : Function.Bijective (fun σ : Equiv.Perm (Fin n) => σ.toEmbedding) :=
    ⟨fun σ τ h => Equiv.ext fun x => DFunLike.congr_fun h x,
      fun e => ⟨e.equivOfFiniteSelfEmbedding, e.toEmbedding_equivOfFiniteSelfEmbedding⟩⟩
  rw [← Fintype.sum_bijective _ hb (fun σ : Equiv.Perm (Fin n) => ∏ i, (1 + t (i, σ i)))
    (fun f : Fin n ↪ Fin n => ∏ i, (1 + t (i, f i))) (fun σ => rfl)]
  simp [Matrix.transpose_apply]

theorem lev_five (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) : Lev 5 L := by
  intro t ht
  rw [hL t ht]
  norm_num [Nat.factorial]

theorem lev_perm {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ) := by
  intro t ht
  rw [← gap_eq_perm]
  exact hL t ht

theorem lev_Mk {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    ∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n → Mk n k t = 0 :=
  PEqualNP.Gct.Kit086.level_Mk_zero n L (lev_perm hL)

theorem lev_inj {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    ∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, ∏ a, t (i a, j a) = 0 :=
  PEqualNP.Gct.Kit086.level_inj_zero n L (lev_perm hL)

theorem lev_of_Mk {n : ℕ} (t : Fin n × Fin n → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ n → Mk n k t = 0) :
    (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i))) = (Nat.factorial n : ℂ) := by
  rw [gap_eq_perm]
  exact PEqualNP.Gct.Kit086.level_of_Mk_zero n t h

theorem lev_sum {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 1 ≤ n) :
    ∀ t ∈ L, ∑ p, t p = 0 := by
  intro t ht
  have h := lev_Mk hL t ht 1 le_rfl hn
  rwa [Mk_one] at h

theorem ite_zero_sub (p : Prop) [Decidable p] (X : ℂ) :
    (if p then 0 else X) = X - if p then X else 0 := by
  split_ifs <;> simp

theorem offdiag_sum {n : ℕ} (F : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, (if a = b then 0 else F a b) = ∑ a, ∑ b, F a b - ∑ a, F a a := by
  simp_rw [ite_zero_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem inj_two_iff {n : ℕ} (f : Fin 2 → Fin n) : Function.Injective f ↔ f 0 ≠ f 1 := by
  constructor
  · intro h h01
    exact absurd (h h01) (by decide)
  · intro h x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact absurd hxy h
    · exact absurd hxy.symm h
    · rfl

theorem sum_emb_two {n : ℕ} (F : Fin n → Fin n → ℂ) :
    ∑ i : Fin 2 ↪ Fin n, F (i 0) (i 1) =
      ∑ a : Fin n, ∑ b : Fin n, if a = b then 0 else F a b := by
  classical
  rw [← (Equiv.subtypeInjectiveEquivEmbedding (Fin 2) (Fin n)).sum_comp]
  have h1 : ∑ f : {f : Fin 2 → Fin n // Function.Injective f},
      F ((Equiv.subtypeInjectiveEquivEmbedding (Fin 2) (Fin n)) f 0)
        ((Equiv.subtypeInjectiveEquivEmbedding (Fin 2) (Fin n)) f 1) =
      ∑ f ∈ univ.filter (fun f : Fin 2 → Fin n => Function.Injective f), F (f 0) (f 1) := by
    rw [Finset.sum_subtype (p := fun f : Fin 2 → Fin n => Function.Injective f)
      (univ.filter (fun f : Fin 2 → Fin n => Function.Injective f))
      (fun f => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun f => F (f 0) (f 1))]
    rfl
  rw [h1, Finset.sum_filter, ← (piFinTwoEquiv fun _ => Fin n).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h0 : (piFinTwoEquiv fun _ => Fin n).symm (a, b) 0 = a := rfl
  have h1' : (piFinTwoEquiv fun _ => Fin n).symm (a, b) 1 = b := rfl
  by_cases hab : a = b
  · rw [if_pos hab, if_neg]
    intro hinj
    exact (inj_two_iff _).mp hinj (h0.trans (hab.trans h1'.symm))
  · rw [if_neg hab, if_pos ((inj_two_iff _).mpr (by rw [h0, h1']; exact hab)), h0, h1']

theorem inj_two (n : ℕ) (t : Fin n × Fin n → ℂ) :
    ∑ i : Fin 2 ↪ Fin n, ∑ j : Fin 2 ↪ Fin n, ∏ a, t (i a, j a) =
      (∑ p, t p) ^ 2 - ∑ i, (∑ j, t (i, j)) ^ 2 - ∑ j, (∑ i, t (i, j)) ^ 2 + ∑ p, t p ^ 2 := by
  have hin : ∀ i : Fin 2 ↪ Fin n, ∑ j : Fin 2 ↪ Fin n, ∏ a, t (i a, j a) =
      ∑ c, ∑ d, if c = d then 0 else t (i 0, c) * t (i 1, d) := fun i =>
    (Finset.sum_congr rfl fun j _ => Fin.prod_univ_two _).trans
      (sum_emb_two (fun c d => t (i 0, c) * t (i 1, d)))
  refine ((Finset.sum_congr rfl fun i _ => hin i).trans
    (sum_emb_two (fun a b => ∑ c, ∑ d, if c = d then 0 else t (a, c) * t (b, d)))).trans ?_
  simp only [offdiag_sum, Finset.sum_sub_distrib, Fintype.sum_prod_type]
  have hA : ∑ a, ∑ b, ∑ c, ∑ d, t (a, c) * t (b, d) = (∑ a, ∑ c, t (a, c)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul_sum]
  have hB : ∑ a, ∑ b, ∑ c, t (a, c) * t (b, c) = ∑ c, (∑ a, t (a, c)) ^ 2 := by
    calc ∑ a, ∑ b, ∑ c, t (a, c) * t (b, c) = ∑ a, ∑ c, ∑ b, t (a, c) * t (b, c) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, t (a, c) * t (b, c) := Finset.sum_comm
      _ = ∑ c, (∑ a, t (a, c)) ^ 2 :=
          Finset.sum_congr rfl fun c _ => by rw [sq, Finset.sum_mul_sum]
  have hC : ∑ a, ∑ c, ∑ d, t (a, c) * t (a, d) = ∑ a, (∑ c, t (a, c)) ^ 2 :=
    Finset.sum_congr rfl fun a _ => by rw [sq, Finset.sum_mul_sum]
  have hD : ∑ a, ∑ c, t (a, c) * t (a, c) = ∑ a, ∑ c, t (a, c) ^ 2 :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => (sq _).symm
  rw [hA, hB, hC, hD]
  ring

noncomputable def rowSum (n : ℕ) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j)

noncomputable def colSum (n : ℕ) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun j => ∑ i, LinearMap.proj (i, j)

theorem rowSum_apply (n : ℕ) (t : Fin n × Fin n → ℂ) (i : Fin n) :
    rowSum n t i = ∑ j, t (i, j) := by
  simp [rowSum, LinearMap.sum_apply]

theorem colSum_apply (n : ℕ) (t : Fin n × Fin n → ℂ) (j : Fin n) :
    colSum n t j = ∑ i, t (i, j) := by
  simp [colSum, LinearMap.sum_apply]

noncomputable def DC (n : ℕ) : Submodule ℂ (Fin n × Fin n → ℂ) :=
  LinearMap.ker ((rowSum n).prod (colSum n))

theorem mem_DC_iff {n : ℕ} (t : Fin n × Fin n → ℂ) :
    t ∈ DC n ↔ rowSum n t = 0 ∧ colSum n t = 0 := by
  rw [DC, LinearMap.mem_ker]
  exact Prod.ext_iff

theorem mem_DC {n : ℕ} (t : Fin n × Fin n → ℂ) :
    t ∈ DC n ↔ (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0) := by
  rw [mem_DC_iff, funext_iff, funext_iff]
  simp only [rowSum_apply, colSum_apply, Pi.zero_apply]

noncomputable def sumZero (n : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  LinearMap.ker (∑ i, (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ))

theorem mem_sumZero {n : ℕ} (v : Fin n → ℂ) : v ∈ sumZero n ↔ ∑ i, v i = 0 := by
  simp [sumZero, LinearMap.sum_apply]

theorem finrank_sumZero {n : ℕ} (hn : 1 ≤ n) : Module.finrank ℂ (sumZero n) ≤ n - 1 := by
  have hne : sumZero n ≠ ⊤ := by
    intro h
    have hm : (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℂ)) ∈ sumZero n := h ▸ Submodule.mem_top
    rw [mem_sumZero] at hm
    simp at hm
  have := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at this
  omega

theorem lev_two {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 2 ≤ n) :
    ∀ t ∈ L, ∑ p, t p ^ 2 = ∑ i, rowSum n t i ^ 2 + ∑ j, colSum n t j ^ 2 := by
  intro t ht
  have h2 := lev_inj hL t ht 2 (by norm_num) hn
  have h1 := lev_sum hL (by omega) t ht
  rw [inj_two, h1] at h2
  simp only [rowSum_apply, colSum_apply]
  linear_combination h2

theorem sum_add_sq {ι : Type} [Fintype ι] (a b : ι → ℂ) :
    ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
  have h : ∀ i, (a i + b i) ^ 2 = a i ^ 2 + 2 * (a i * b i) + b i ^ 2 := fun i => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem lev_two_pol {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 2 ≤ n) :
    ∀ t ∈ L, ∀ u ∈ L, ∑ p, t p * u p =
      ∑ i, rowSum n t i * rowSum n u i + ∑ j, colSum n t j * colSum n u j := by
  intro t ht u hu
  have ht2 := lev_two hL hn t ht
  have hu2 := lev_two hL hn u hu
  have htu := lev_two hL hn (t + u) (L.add_mem ht hu)
  simp only [map_add, Pi.add_apply] at htu
  rw [sum_add_sq, sum_add_sq, sum_add_sq] at htu
  linear_combination (1 / 2 : ℂ) * (htu - ht2 - hu2)

theorem dc_orth {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 2 ≤ n) :
    ∀ d ∈ L ⊓ DC n, ∀ u ∈ L, ∑ p, d p * u p = 0 := by
  intro d hd u hu
  rw [lev_two_pol hL hn d hd.1 u hu]
  have h0 := (mem_DC_iff d).mp hd.2
  simp [h0.1, h0.2]

theorem rowSum_mem {n : ℕ} (t : Fin n × Fin n → ℂ) (h : ∑ p, t p = 0) :
    rowSum n t ∈ sumZero n := by
  rw [mem_sumZero]
  simp only [rowSum_apply]
  rw [Fintype.sum_prod_type] at h
  exact h

theorem colSum_mem {n : ℕ} (t : Fin n × Fin n → ℂ) (h : ∑ p, t p = 0) :
    colSum n t ∈ sumZero n := by
  rw [mem_sumZero]
  simp only [colSum_apply]
  rw [Fintype.sum_prod_type_right] at h
  exact h

theorem map_rowSum_le {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (hn : 1 ≤ n) : L.map (rowSum n) ≤ sumZero n := by
  rintro _ ⟨t, ht, rfl⟩
  exact rowSum_mem t (lev_sum hL hn t ht)

theorem map_colSum_le {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (hn : 1 ≤ n) : L.map (colSum n) ≤ sumZero n := by
  rintro _ ⟨t, ht, rfl⟩
  exact colSum_mem t (lev_sum hL hn t ht)

theorem rA_le {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 1 ≤ n) :
    Module.finrank ℂ (L.map (rowSum n)) ≤ n - 1 :=
  (Submodule.finrank_mono (map_rowSum_le hL hn)).trans (finrank_sumZero hn)

theorem rB_le {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 1 ≤ n) :
    Module.finrank ℂ (L.map (colSum n)) ≤ n - 1 :=
  (Submodule.finrank_mono (map_colSum_le hL hn)).trans (finrank_sumZero hn)

theorem finrank_split {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    Module.finrank ℂ L = Module.finrank ℂ (L ⊓ DC n : Submodule ℂ _) +
      Module.finrank ℂ (L.map ((rowSum n).prod (colSum n))) := by
  have hrn : Module.finrank ℂ (L.map ((rowSum n).prod (colSum n))) +
      Module.finrank ℂ (L ⊓ LinearMap.ker ((rowSum n).prod (colSum n)) : Submodule ℂ _)
      = Module.finrank ℂ L := by
    rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
      ← (((rowSum n).prod (colSum n)).submoduleMap L).finrank_range_add_finrank_ker,
      LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]
    simp
  rw [DC]
  omega

theorem finrank_map_prod_le {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (f g : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    Module.finrank ℂ (L.map (f.prod g)) ≤
      Module.finrank ℂ (L.map f) + Module.finrank ℂ (L.map g) := by
  have hle : L.map (f.prod g) ≤ (L.map f).map (LinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ)) ⊔
      (L.map g).map (LinearMap.inr ℂ (Fin n → ℂ) (Fin n → ℂ)) := by
    rintro _ ⟨x, hx, rfl⟩
    have he : (f.prod g) x = LinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ) (f x) +
        LinearMap.inr ℂ (Fin n → ℂ) (Fin n → ℂ) (g x) := by simp
    rw [he]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hx))
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hx))
  calc Module.finrank ℂ (L.map (f.prod g))
      ≤ Module.finrank ℂ ((L.map f).map (LinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ)) ⊔
          (L.map g).map (LinearMap.inr ℂ (Fin n → ℂ) (Fin n → ℂ)) : Submodule ℂ _) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ ((L.map f).map (LinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ))) +
          Module.finrank ℂ ((L.map g).map (LinearMap.inr ℂ (Fin n → ℂ) (Fin n → ℂ))) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ _ := add_le_add (Submodule.finrank_map_le _ _) (Submodule.finrank_map_le _ _)

theorem dim_le {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (L ⊓ DC n : Submodule ℂ _) +
      Module.finrank ℂ (L.map (rowSum n)) + Module.finrank ℂ (L.map (colSum n)) := by
  have h1 := finrank_split L
  have h2 := finrank_map_prod_le L (rowSum n) (colSum n)
  omega

theorem skeleton_le (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (L ⊓ DC 5 : Submodule ℂ _) +
      Module.finrank ℂ (L.map (rowSum 5)) + Module.finrank ℂ (L.map (colSum 5)) ∧
    Module.finrank ℂ (L.map (rowSum 5)) ≤ 4 ∧ Module.finrank ℂ (L.map (colSum 5)) ≤ 4 :=
  ⟨dim_le L, rA_le (lev_five L hL) (by norm_num), rB_le (lev_five L hL) (by norm_num)⟩

theorem skeleton (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (hS : min (Module.finrank ℂ (L.map (rowSum 5))) (Module.finrank ℂ (L.map (colSum 5))) +
      Module.finrank ℂ (L ⊓ DC 5 : Submodule ℂ _) ≤ 4) :
    Module.finrank ℂ L ≤ 8 := by
  obtain ⟨h1, h2, h3⟩ := skeleton_le L hL
  rcases le_total (Module.finrank ℂ (L.map (rowSum 5))) (Module.finrank ℂ (L.map (colSum 5)))
    with h | h
  · rw [min_eq_left h] at hS
    omega
  · rw [min_eq_right h] at hS
    omega

theorem dc_zero (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (hd : L ⊓ DC 5 = ⊥) : Module.finrank ℂ L ≤ 8 := by
  obtain ⟨h1, h2, h3⟩ := skeleton_le L hL
  rw [hd, finrank_bot] at h1
  omega

theorem gap_of_S
    (hS : ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      min (Module.finrank ℂ (L.map (rowSum 5))) (Module.finrank ℂ (L.map (colSum 5))) +
        Module.finrank ℂ (L ⊓ DC 5 : Submodule ℂ _) ≤ 4) :
    ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      Module.finrank ℂ L ≤ 8 :=
  fun L hL => skeleton L hL (hS L hL)

end PEqualNP.Gct.F210

theorem PEqualNP.Outside.L_gct_210_frame : ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) → L ⊓ PEqualNP.Gct.F210.DC 5 = ⊥ → Module.finrank ℂ L ≤ 8 :=
  PEqualNP.Gct.F210.dc_zero
