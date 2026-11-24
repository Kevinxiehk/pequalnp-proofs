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


namespace PEqualNP.Gct.Helpers.Kneser

namespace Fin

open scoped Classical in

theorem levelSet_indicator_mem {K ι : Type*} [Field K] [Fintype ι]
    (A : Subalgebra K (ι → K)) {x : ι → K} (hx : x ∈ A) (c : K) :
    Set.indicator {j | x j = c} (1 : ι → K) ∈ A := by
  have key : Set.indicator {j | x j = c} (1 : ι → K)
      = ∏ μ ∈ (Finset.univ.image x).erase c,
          ((c - μ)⁻¹ • (x - algebraMap K (ι → K) μ)) := by
    funext j
    rw [Finset.prod_apply]
    by_cases h : x j = c
    · rw [Set.indicator_of_mem (by exact h)]
      symm
      apply Finset.prod_eq_one
      intro μ hμ
      have hne : c - μ ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hμ).symm
      simp [h, hne]
    · rw [Set.indicator_of_notMem (by exact h)]
      symm
      apply Finset.prod_eq_zero (i := x j)
      · exact Finset.mem_erase.mpr ⟨h, Finset.mem_image_of_mem x (Finset.mem_univ j)⟩
      · simp
  rw [key]
  exact A.prod_mem fun μ _ => A.smul_mem (A.sub_mem hx (A.algebraMap_mem μ)) _

open scoped Classical in

theorem eq_sum_levelSet_indicator {K ι : Type*} [Field K] [Fintype ι] (x : ι → K) :
    x = ∑ c ∈ Finset.univ.image x, c • Set.indicator {j | x j = c} (1 : ι → K) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (x j)]
  · simp
  · intro c _ hc
    have : j ∉ {j | x j = c} := fun h => hc (Eq.symm h)
    simp [Set.indicator_of_notMem this]
  · intro h
    exact absurd (Finset.mem_image_of_mem x (Finset.mem_univ j)) h

def indicatorSets {K ι : Type*} [Field K] (A : Subalgebra K (ι → K)) : Set (Set ι) :=
  {S | Set.indicator S (1 : ι → K) ∈ A}

theorem le_of_indicatorSets_subset {K ι : Type*} [Field K] [Fintype ι]
    {A B : Subalgebra K (ι → K)} (h : indicatorSets A ⊆ indicatorSets B) : A ≤ B := by
  classical
  intro x hx
  rw [eq_sum_levelSet_indicator x]
  exact B.sum_mem fun c _ => B.smul_mem (h (levelSet_indicator_mem A hx c)) c

theorem indicatorSets_injective {K ι : Type*} [Field K] [Fintype ι] :
    Function.Injective (indicatorSets : Subalgebra K (ι → K) → Set (Set ι)) :=
  fun _ _ h => le_antisymm (le_of_indicatorSets_subset h.le) (le_of_indicatorSets_subset h.ge)

theorem finite_subalgebra_pi (K ι : Type*) [Field K] [Fintype ι] :
    Finite (Subalgebra K (ι → K)) :=
  Finite.of_injective _ indicatorSets_injective

end Fin

theorem finite_subalgebra (n : ℕ) : Finite (Subalgebra ℂ (Fin n → ℂ)) :=
  Fin.finite_subalgebra_pi ℂ (_root_.Fin n)

end PEqualNP.Gct.Helpers.Kneser

namespace PEqualNP.Gct.Helpers.Kneser

namespace ETr

open Module

variable {n : ℕ}

theorem mulLeft_injective {e : Fin n → ℂ} (he : IsUnit e) :
    Function.Injective (LinearMap.mulLeft ℂ e) := by
  obtain ⟨u, rfl⟩ := he
  intro a b h
  have h' : (u : Fin n → ℂ) * a = u * b := h
  have := congrArg (fun z => ((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * z) h'
  simpa using this

theorem mulLeft_surjective {e : Fin n → ℂ} (he : IsUnit e) :
    Function.Surjective (LinearMap.mulLeft ℂ e) := by
  obtain ⟨u, rfl⟩ := he
  intro b
  exact ⟨((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * b, by simp⟩

theorem finrank_map_mulLeft {e : Fin n → ℂ} (he : IsUnit e) (S : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S.map (LinearMap.mulLeft ℂ e)) = finrank ℂ S :=
  (Submodule.equivMapOfInjective _ (mulLeft_injective he) S).finrank_eq.symm

theorem finrank_comap_mulLeft {e : Fin n → ℂ} (he : IsUnit e) (S : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S.comap (LinearMap.mulLeft ℂ e)) = finrank ℂ S := by
  rw [← finrank_map_mulLeft he (S.comap (LinearMap.mulLeft ℂ e)),
    Submodule.map_comap_eq_of_surjective (mulLeft_surjective he)]

theorem le_span_units (T : Submodule ℂ (Fin n → ℂ)) (h1 : (1 : Fin n → ℂ) ∈ T) :
    T ≤ Submodule.span ℂ {e | e ∈ T ∧ IsUnit e} := by
  intro v hv
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert (0 : ℂ) (Finset.univ.image (fun i => - v i)))
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hci : ∀ i, v i + c ≠ 0 := by
    intro i h
    apply hc
    have : c = - v i := by linear_combination h
    rw [this]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hu1 : IsUnit (c • (1 : Fin n → ℂ)) := by
    rw [Pi.isUnit_iff]
    intro i
    simpa using hc0
  have hu2 : IsUnit (v + c • (1 : Fin n → ℂ)) := by
    rw [Pi.isUnit_iff]
    intro i
    simpa using hci i
  have hv' : v = (v + c • (1 : Fin n → ℂ)) - c • (1 : Fin n → ℂ) := by simp
  rw [hv']
  exact Submodule.sub_mem _
    (Submodule.subset_span ⟨T.add_mem hv (T.smul_mem c h1), hu2⟩)
    (Submodule.subset_span ⟨T.smul_mem c h1, hu1⟩)

theorem core_stable (S T : Submodule ℂ (Fin n → ℂ)) (hS : (1 : Fin n → ℂ) ∈ S)
    (hT : (1 : Fin n → ℂ) ∈ T)
    (hA : ∀ e ∈ T, IsUnit e → S ≤ T.comap (LinearMap.mulLeft ℂ e)) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) := by
  have hST : ∀ s ∈ S, ∀ t ∈ T, s * t ∈ T := by
    intro s hs t ht
    have hle : Submodule.span ℂ {e | e ∈ T ∧ IsUnit e} ≤ T.comap (LinearMap.mulLeft ℂ s) := by
      rw [Submodule.span_le]
      rintro e ⟨heT, heu⟩
      have := hA e heT heu hs
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at this
      simpa [mul_comm] using this
    have := hle (le_span_units T hT ht)
    simpa using this
  refine ⟨Algebra.adjoin ℂ (S : Set (Fin n → ℂ)), T, ?_, le_rfl, ?_, ?_⟩
  · intro h hh
    induction hh using Algebra.adjoin_induction with
    | mem x hx => exact fun v hv => hST x hx v hv
    | algebraMap r =>
      intro v hv
      rw [← Algebra.smul_def]
      exact T.smul_mem r hv
    | add x y _ _ ihx ihy =>
      intro v hv
      rw [add_mul]
      exact T.add_mem (ihx v hv) (ihy v hv)
    | mul x y _ _ ihx ihy =>
      intro v hv
      rw [mul_assoc]
      exact ihx _ (ihy v hv)
  · intro t ht
    have := Submodule.mul_mem_mul hS ht
    simpa using this
  · have hle : S ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (S : Set (Fin n → ℂ))) :=
      fun s hs => Algebra.subset_adjoin hs
    have := Submodule.finrank_mono hle
    omega

theorem finrank_transform (S T : Submodule ℂ (Fin n → ℂ)) {e : Fin n → ℂ} (he : IsUnit e) :
    finrank ℂ (S ⊓ T.comap (LinearMap.mulLeft ℂ e) : Submodule ℂ (Fin n → ℂ)) +
      finrank ℂ (T ⊔ S.map (LinearMap.mulLeft ℂ e) : Submodule ℂ (Fin n → ℂ)) =
    finrank ℂ S + finrank ℂ T := by
  have hinf : T ⊓ S.map (LinearMap.mulLeft ℂ e) =
      (S ⊓ T.comap (LinearMap.mulLeft ℂ e)).map (LinearMap.mulLeft ℂ e) := by
    ext y
    simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨hy, s, hs, rfl⟩
      exact ⟨s, ⟨hs, hy⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hy⟩, rfl⟩
      exact ⟨hy, s, hs, rfl⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T (S.map (LinearMap.mulLeft ℂ e))
  rw [hinf, finrank_map_mulLeft he, finrank_map_mulLeft he] at h1
  omega

theorem transform_mul_le (S T : Submodule ℂ (Fin n → ℂ)) (e : Fin n → ℂ) :
    (S ⊓ T.comap (LinearMap.mulLeft ℂ e)) * (T ⊔ S.map (LinearMap.mulLeft ℂ e)) ≤ S * T := by
  rw [Submodule.mul_le]
  intro s hs m hm
  have hmem : T ⊔ S.map (LinearMap.mulLeft ℂ e) ≤ (S * T).comap (LinearMap.mulLeft ℂ s) := by
    refine sup_le ?_ ?_
    · intro t ht
      exact Submodule.mul_mem_mul hs.1 ht
    · rintro _ ⟨s0, hs0, rfl⟩
      have h2 : e * s ∈ T := hs.2
      have := Submodule.mul_mem_mul hs0 h2
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have heq : s * (e * s0) = s0 * (e * s) := by ring
      rw [heq]
      exact this
  exact hmem hm

theorem core (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (hS : (1 : Fin n → ℂ) ∈ S)
    (hT : (1 : Fin n → ℂ) ∈ T) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) := by
  suffices key : ∀ k : ℕ, ∀ S T : Submodule ℂ (Fin n → ℂ), finrank ℂ S = k →
      (1 : Fin n → ℂ) ∈ S → (1 : Fin n → ℂ) ∈ T →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
        finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) from
    key _ S T rfl hS hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S T hk hS hT
    by_cases hA : ∀ e ∈ T, IsUnit e → S ≤ T.comap (LinearMap.mulLeft ℂ e)
    · exact core_stable S T hS hT hA
    · push Not at hA
      obtain ⟨e, heT, heu, hne⟩ := hA
      have hlt : S ⊓ T.comap (LinearMap.mulLeft ℂ e) < S := inf_lt_left.mpr hne
      have hdim := Submodule.finrank_lt_finrank_of_lt hlt
      have h1S : (1 : Fin n → ℂ) ∈ S ⊓ T.comap (LinearMap.mulLeft ℂ e) := by
        refine ⟨hS, ?_⟩
        simpa using heT
      have h1T : (1 : Fin n → ℂ) ∈ T ⊔ S.map (LinearMap.mulLeft ℂ e) :=
        (le_sup_left : T ≤ _) hT
      obtain ⟨H, V, hHV, hTV, hVle, hfin⟩ :=
        ih _ (hk ▸ hdim) (S ⊓ T.comap (LinearMap.mulLeft ℂ e))
          (T ⊔ S.map (LinearMap.mulLeft ℂ e)) rfl h1S h1T
      refine ⟨H, V, hHV, le_trans le_sup_left hTV, le_trans hVle (transform_mul_le S T e), ?_⟩
      have := finrank_transform S T heu
      omega

end ETr

open Module in

theorem etransform (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ)
    (hx : x ∈ S) (hxu : IsUnit x) (hT : ∃ t ∈ T, IsUnit t) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
      Module.finrank ℂ S + Module.finrank ℂ T ≤
        Module.finrank ℂ V + Module.finrank ℂ (Subalgebra.toSubmodule H) := by
  obtain ⟨t, ht, htu⟩ := hT
  have h1S : (1 : Fin n → ℂ) ∈ S.comap (LinearMap.mulLeft ℂ x) := by simpa using hx
  have h1T : (1 : Fin n → ℂ) ∈ T.comap (LinearMap.mulLeft ℂ t) := by simpa using ht
  obtain ⟨H, V0, hHV, hTV, hVle, hfin⟩ := ETr.core n _ _ h1S h1T
  have hxt : IsUnit (x * t) := hxu.mul htu
  refine ⟨H, V0.map (LinearMap.mulLeft ℂ (x * t)), ?_, ?_, ?_, ?_⟩
  · rintro h hh _ ⟨v, hv, rfl⟩
    refine ⟨h * v, hHV h hh v hv, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    ring
  · intro t' ht'
    obtain ⟨u, rfl⟩ := htu
    refine ⟨((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * t', hTV ?_, ?_⟩
    · simpa using ht'
    · simp only [LinearMap.mulLeft_apply]
      rw [mul_assoc, Units.mul_inv_cancel_left]
  · rw [Submodule.map_le_iff_le_comap]
    refine le_trans hVle ?_
    rw [Submodule.mul_le]
    intro s0 hs0 t0 ht0
    have h1 : x * s0 ∈ S := hs0
    have h2 : t * t0 ∈ T := ht0
    have := Submodule.mul_mem_mul h1 h2
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
    have heq : x * t * (s0 * t0) = x * s0 * (t * t0) := by ring
    rw [heq]
    exact this
  · rw [ETr.finrank_map_mulLeft hxt, ← ETr.finrank_comap_mulLeft hxu S,
      ← ETr.finrank_comap_mulLeft htu T]
    exact hfin

end PEqualNP.Gct.Helpers.Kneser

namespace PEqualNP.Gct.Helpers.Kneser

open Module

namespace Asm

theorem exists_isUnit_of_support {n : ℕ} (U : Submodule ℂ (Fin n → ℂ))
    (hU : ∀ i, ∃ u ∈ U, u i ≠ 0) : ∃ u ∈ U, IsUnit u := by
  by_contra hno
  push Not at hno
  let P : Fin n → Submodule ℂ U := fun i =>
    (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap U.subtype
  have hcov : ⋃ i, (P i : Set U) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    have h1 := hno u.1 u.2
    rw [Pi.isUnit_iff] at h1
    push Not at h1
    obtain ⟨i, hi⟩ := h1
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have h0 : u.1 i = 0 := by
      by_contra hne
      exact hi (isUnit_iff_ne_zero.2 hne)
    show U.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    rw [LinearMap.mem_ker]
    exact h0
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  obtain ⟨u, hu, hui⟩ := hU i
  have hmem : (⟨u, hu⟩ : U) ∈ P i := by
    rw [hi]
    exact Submodule.mem_top
  have h0 : U.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) := hmem
  rw [LinearMap.mem_ker] at h0
  exact hui h0

theorem full_of {n : ℕ} (hfin : Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H))
    (S T : Submodule ℂ (Fin n → ℂ)) (hS0 : S ≠ ⊥) (hS : ∀ i, ∃ s ∈ S, s i ≠ 0)
    (hT : ∃ t ∈ T, IsUnit t) :
    ∃ H : Subalgebra ℂ (Fin n → ℂ), (∀ h ∈ H, ∀ v ∈ S * T, h * v ∈ S * T) ∧
      finrank ℂ S + finrank ℂ T ≤
        finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) +
          finrank ℂ (Subalgebra.toSubmodule H) := by

  let G : Subalgebra ℂ (Fin n → ℂ) → Set (Fin n → ℂ) := fun H =>
    {x | x ∈ S ∧ ∃ V : Submodule ℂ (Fin n → ℂ),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H)}
  let P : Fin n ⊕ Subalgebra ℂ (Fin n → ℂ) → Submodule ℂ S := fun j =>
    Sum.elim
      (fun i => (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap S.subtype)
      (fun H => (Submodule.span ℂ (G H)).comap S.subtype) j
  have hcov : ⋃ j, (P j : Set S) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    by_cases hu : IsUnit u.1
    · obtain ⟨H, V, h1, h2, h3, h4⟩ := hetr S T u.1 u.2 hu hT
      refine Set.mem_iUnion.2 ⟨Sum.inr H, ?_⟩
      show S.subtype u ∈ Submodule.span ℂ (G H)
      exact Submodule.subset_span ⟨u.2, V, h1, h2, h3, h4⟩
    · rw [Pi.isUnit_iff] at hu
      push Not at hu
      obtain ⟨i, hi⟩ := hu
      refine Set.mem_iUnion.2 ⟨Sum.inl i, ?_⟩
      have h0 : u.1 i = 0 := by
        by_contra hne
        exact hi (isUnit_iff_ne_zero.2 hne)
      show S.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
      rw [LinearMap.mem_ker]
      exact h0
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  rcases j with i | H
  · exfalso
    obtain ⟨u, hu, hui⟩ := hS i
    have hmem : (⟨u, hu⟩ : S) ∈ P (Sum.inl i) := by
      rw [hj]
      exact Submodule.mem_top
    have h0 : S.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) :=
      hmem
    rw [LinearMap.mem_ker] at h0
    exact hui h0
  · have hspan : S ≤ Submodule.span ℂ (G H) := by
      intro s hs
      have hmem : (⟨s, hs⟩ : S) ∈ P (Sum.inr H) := by
        rw [hj]
        exact Submodule.mem_top
      exact hmem

    let M : Submodule ℂ (Fin n → ℂ) :=
      sSup {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T}
    have hM_le : M ≤ S * T := sSup_le fun V hV => hV.2
    have hM_stab : ∀ h ∈ H, ∀ v ∈ M, h * v ∈ M := by
      intro h hh
      have hle : M ≤ M.comap (LinearMap.mulLeft ℂ h) := by
        refine sSup_le fun V hV v hv => ?_
        show (LinearMap.mulLeft ℂ h) v ∈ M
        rw [LinearMap.mulLeft_apply]
        exact (le_sSup hV : V ≤ M) (hV.1 h hh v hv)
      intro v hv
      have h1 := hle hv
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
      exact h1
    have hST_le : S * T ≤ M := by
      rw [Submodule.mul_le]
      intro s hs t ht
      have hle : Submodule.span ℂ (G H) ≤ M.comap (LinearMap.mulRight ℂ t) := by
        rw [Submodule.span_le]
        rintro x ⟨_, V, h1, h2, h3, _⟩
        show (LinearMap.mulRight ℂ t) x ∈ M
        rw [LinearMap.mulRight_apply]
        exact (le_sSup (show V ∈ {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T} from
          ⟨h1, h3⟩) : V ≤ M) (h2 t ht)
      have h1 := hle (hspan hs)
      rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h1
      exact h1
    have hne : (G H).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hS0
      rw [eq_bot_iff]
      intro s hs
      have h1 := hspan hs
      rw [hemp, Submodule.span_empty] at h1
      exact h1
    obtain ⟨x, _, V, _, _, h3, h4⟩ := hne
    have hVle : finrank ℂ V ≤ finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) :=
      Submodule.finrank_mono h3
    refine ⟨H, fun h hh v hv => hM_le (hM_stab h hh v (hST_le hv)), ?_⟩
    omega

def offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0}
  add_mem' := by
    intro a b ha hb i h1 h2
    simp [ha i h1 h2, hb i h1 h2]
  zero_mem' := by
    intro i _ _
    rfl
  smul_mem' := by
    intro c a ha i h1 h2
    simp [ha i h1 h2]

theorem mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ} :
    x ∈ offSupp S T ↔ ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0 :=
  Iff.rfl

theorem mul_mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ offSupp S T) (a : Fin n → ℂ) : a * x ∈ offSupp S T := by
  intro i h1 h2
  simp [hx i h1 h2]

theorem mul_apply_eq_zero {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ}
    (hv : v ∈ S * T) (i : Fin n) (hi : ¬((∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0))) :
    v i = 0 := by
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro s hs t ht
    by_contra hne
    rw [Pi.mul_apply] at hne
    exact hi ⟨⟨s, hs, left_ne_zero_of_mul hne⟩, ⟨t, ht, right_ne_zero_of_mul hne⟩⟩
  · intro a b ha hb
    simp [ha, hb]

theorem support_sup_offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ S ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ s ∈ S, s i ≠ 0
  · obtain ⟨s, hs, hsi⟩ := hK
    exact ⟨s, (le_sup_left : S ≤ S ⊔ offSupp S T) hs, hsi⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ S ⊔ offSupp S T) ?_, by simp⟩
    intro j h1 _
    by_cases hji : j = i
    · subst hji
      exact absurd h1 hK
    · simp [hji]

theorem support_sup_offSupp' {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ T ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ t ∈ T, t i ≠ 0
  · obtain ⟨t, ht, hti⟩ := hK
    exact ⟨t, (le_sup_left : T ≤ T ⊔ offSupp S T) ht, hti⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ T ⊔ offSupp S T) ?_, by simp⟩
    intro j _ h2
    by_cases hji : j = i
    · subst hji
      exact absurd h2 hK
    · simp [hji]

theorem sup_mul_sup_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    (S ⊔ offSupp S T) * (T ⊔ offSupp S T) ≤ S * T ⊔ offSupp S T := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.1 hb
  have h1 : s * t ∈ S * T := Submodule.mul_mem_mul hs ht
  have h2 : s * w' + w * t + w * w' ∈ offSupp S T := by
    refine Submodule.add_mem _ (Submodule.add_mem _ (mul_mem_offSupp hw' s) ?_)
      (mul_mem_offSupp hw' w)
    rw [mul_comm]
    exact mul_mem_offSupp hw t
  have h3 : (s + w) * (t + w') = s * t + (s * w' + w * t + w * w') := by ring
  rw [h3]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

theorem finrank_inf_offSupp_add_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) +
      finrank ℂ (T ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) ≤ finrank ℂ (offSupp S T) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ offSupp S T) (T ⊓ offSupp S T)
  have h2 : (S ⊓ offSupp S T) ⊓ (T ⊓ offSupp S T) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxS, hxW⟩, ⟨hxT, _⟩⟩
    rw [Submodule.mem_bot]
    funext i
    by_contra hne
    exact hne (hxW i ⟨x, hxS, hne⟩ ⟨x, hxT, hne⟩)
  have h3 : finrank ℂ ((S ⊓ offSupp S T) ⊔ (T ⊓ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (offSupp S T) :=
    Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
  rw [h2, finrank_bot] at h1
  omega

end Asm

open Asm in

theorem kneser_of
    (hfin : ∀ n : ℕ, Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        Module.finrank ℂ S + Module.finrank ℂ T ≤
          Module.finrank ℂ V + Module.finrank ℂ (Subalgebra.toSubmodule H)) :
    ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
      Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St := by
  intro n S T St hS _ hSt
  have hS' : S ⊔ offSupp S T ≠ ⊥ := by
    intro h
    apply hS
    rw [eq_bot_iff, ← h]
    exact le_sup_left
  obtain ⟨H, hH, hdim⟩ := full_of (hfin n) (hetr n) (S ⊔ offSupp S T) (T ⊔ offSupp S T) hS'
    (support_sup_offSupp S T) (exists_isUnit_of_support _ (support_sup_offSupp' S T))

  have hHSt : Subalgebra.toSubmodule H ≤ St := by
    intro h hh
    rw [hSt]
    intro v hv
    have hv' : v ∈ (S ⊔ offSupp S T) * (T ⊔ offSupp S T) :=
      (Submodule.mul_le.2 fun s hs t ht =>
        Submodule.mul_mem_mul (Submodule.mem_sup_left hs) (Submodule.mem_sup_left ht)) hv
    obtain ⟨a, ha, w, hw, hsum⟩ :=
      Submodule.mem_sup.1 (sup_mul_sup_le S T (hH h ((Subalgebra.mem_toSubmodule _).1 hh) v hv'))
    have hw0 : w = 0 := by
      funext i
      by_cases hK : (∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0)
      · exact hw i hK.1 hK.2
      · have e1 : a i + w i = h i * v i := by
          rw [← Pi.add_apply, hsum, Pi.mul_apply]
        rw [mul_apply_eq_zero ha i hK, mul_apply_eq_zero hv i hK] at e1
        simpa using e1
    rw [hw0, add_zero] at hsum
    rw [← hsum]
    exact ha
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq S (offSupp S T)
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq T (offSupp S T)
  have d3 := finrank_inf_offSupp_add_le S T
  have d4 : finrank ℂ ((S ⊔ offSupp S T) * (T ⊔ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) + finrank ℂ (offSupp S T) :=
    (Submodule.finrank_mono (sup_mul_sup_le S T)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have d5 : finrank ℂ (Subalgebra.toSubmodule H) ≤ finrank ℂ St := Submodule.finrank_mono hHSt
  omega

end PEqualNP.Gct.Helpers.Kneser

namespace PEqualNP.Gct.Helpers

open Module Finset

section General

variable {ι : Type} [Fintype ι]

def FermatIso (W : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∑ i, u i * v i * z i = 0)

def KneserFor (ι : Type) [Fintype ι] : Prop :=
  ∀ S T St : Submodule ℂ (ι → ℂ), S ≠ ⊥ → T ≠ ⊥ →
    (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ (S * T) + finrank ℂ St

def stab (V : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {x | ∀ v ∈ V, x * v ∈ V}
  add_mem' {a b} ha hb v hv := by rw [add_mul]; exact V.add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := by rw [zero_mul]; exact V.zero_mem
  smul_mem' c x hx v hv := by rw [smul_mul_assoc]; exact V.smul_mem c (hx v hv)

omit [Fintype ι] in
theorem mem_stab {V : Submodule ℂ (ι → ℂ)} {x : ι → ℂ} : x ∈ stab V ↔ ∀ v ∈ V, x * v ∈ V :=
  Iff.rfl

omit [Fintype ι] in
theorem one_mem_stab (V : Submodule ℂ (ι → ℂ)) : (1 : ι → ℂ) ∈ stab V := fun v hv => by
  rwa [one_mul]

omit [Fintype ι] in
theorem mul_mem_stab {V : Submodule ℂ (ι → ℂ)} {x y : ι → ℂ} (hx : x ∈ stab V)
    (hy : y ∈ stab V) : x * y ∈ stab V := fun v hv => by
  rw [mul_assoc]; exact hx _ (hy v hv)

noncomputable def dotDual : (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
  LinearMap.mk₂ ℂ (fun v z => ∑ i, v i * z i)
    (fun a b z => by simp only [Pi.add_apply, add_mul, sum_add_distrib])
    (fun c a z => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum])
    (fun v a b => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c v a => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by ring)

theorem dotDual_apply (v z : ι → ℂ) : dotDual v z = ∑ i, v i * z i := rfl

theorem dotDual_injective : Function.Injective (dotDual (ι := ι)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  funext j
  have h := LinearMap.congr_fun hv (Pi.single j 1)
  rw [dotDual_apply] at h
  simpa [Pi.single_apply] using h

theorem perp_bound (V W : Submodule ℂ (ι → ℂ)) (h : ∀ v ∈ V, ∀ z ∈ W, ∑ i, v i * z i = 0) :
    finrank ℂ V + finrank ℂ W ≤ Fintype.card ι := by
  have hle : V.map dotDual ≤ W.dualAnnihilator := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h v hv z hz
  have e1 : finrank ℂ (V.map dotDual) = finrank ℂ V :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ dotDual_injective V)).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have e3 := Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card] at e2
  omega

theorem exists_indicator {V : Submodule ℂ (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ stab V) (i : ι) :
    ∃ e ∈ stab V, ∀ k, e k = if x k = x i then 1 else 0 := by
  classical
  refine ⟨∏ c ∈ (univ.image x).erase (x i), (x i - c)⁻¹ • (x - c • 1), ?_, ?_⟩
  · refine Finset.prod_induction _ (· ∈ stab V) (fun a b ha hb => mul_mem_stab ha hb)
      (one_mem_stab V) fun c _ => ?_
    exact (stab V).smul_mem _ ((stab V).sub_mem hx ((stab V).smul_mem _ (one_mem_stab V)))
  · intro k
    rw [Finset.prod_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
    split_ifs with hk
    · refine Finset.prod_eq_one fun c hc => ?_
      have hc' : c ≠ x i := (Finset.mem_erase.1 hc).1
      rw [hk]
      exact inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hc'))
    · refine Finset.prod_eq_zero (i := x k) ?_ (by rw [sub_self, mul_zero])
      exact Finset.mem_erase.2 ⟨hk, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

noncomputable def restr (p : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ({k // p k = 1} → ℂ) :=
  LinearMap.funLeft ℂ ℂ Subtype.val

omit [Fintype ι] in
theorem restr_apply (p u : ι → ℂ) (k : {k // p k = 1}) : restr p u k = u k := rfl

theorem sum_restr (p : ι → ℂ) (hp : ∀ k, p k = 0 ∨ p k = 1) (f : ι → ℂ) :
    ∑ k : {k // p k = 1}, f k = ∑ k, p k * f k := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => p k = 1) (fun k => p k * f k)]
  have h2 : ∑ k : {k // ¬ p k = 1}, p k * f k = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hp k with h | h
    · rw [h, zero_mul]
    · exact absurd h k.2
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun k _ => by rw [k.2, one_mul]

noncomputable def vSpan (W : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  (W ⊔ Submodule.span ℂ {1}) * W

omit [Fintype ι] in
theorem le_vSpan (W : Submodule ℂ (ι → ℂ)) {u : ι → ℂ} (hu : u ∈ W) : u ∈ vSpan W := by
  have := Submodule.mul_mem_mul
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self (1 : ι → ℂ)) :
      (1 : ι → ℂ) ∈ W ⊔ Submodule.span ℂ {1}) hu
  rwa [one_mul] at this

omit [Fintype ι] in
theorem mul_mem_vSpan (W : Submodule ℂ (ι → ℂ)) {u v : ι → ℂ} (hu : u ∈ W) (hv : v ∈ W) :
    u * v ∈ vSpan W :=
  Submodule.mul_mem_mul (Submodule.mem_sup_left hu) hv

theorem vSpan_perp {W : Submodule ℂ (ι → ℂ)} (hW : FermatIso W) :
    ∀ v ∈ vSpan W, ∀ z ∈ W, ∑ i, v i * z i = 0 := by
  intro v hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro m hm n hn z hz
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hm
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 := hW.2 y hy n hn z hz
    have h2 := hW.1 n hn z hz
    calc ∑ i, ((y + c • 1) * n) i * z i
        = ∑ i, y i * n i * z i + c * ∑ i, n i * z i := by
          rw [mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
          ring
      _ = 0 := by rw [h1, h2, mul_zero, add_zero]
  · intro a b ha hb z hz
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha z hz, hb z hz, add_zero]

theorem restr_iso {W : Submodule ℂ (ι → ℂ)} (hW : FermatIso W) {p : ι → ℂ}
    (hp : p ∈ stab (vSpan W)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    FermatIso (W.map (restr p)) := by
  have hperp := vSpan_perp hW
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have := hperp _ (hp _ (le_vSpan W hu)) v hv
    simpa only [Pi.mul_apply, mul_assoc] using this
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * z k)]
    have := hperp _ (hp _ (mul_mem_vSpan W hu hv)) z hz
    simpa only [Pi.mul_apply, mul_assoc] using this

theorem finrank_split (W : Submodule ℂ (ι → ℂ)) (e f : ι → ℂ) (hef : ∀ k, e k = 1 ∨ f k = 1) :
    finrank ℂ W ≤ finrank ℂ (W.map (restr e)) + finrank ℂ (W.map (restr f)) := by
  let R := (restr e).prod (restr f)
  have hR : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    rcases hef k with h | h
    · have := congr_fun (congr_arg Prod.fst hu) ⟨k, h⟩
      simpa [R, restr_apply] using this
    · have := congr_fun (congr_arg Prod.snd hu) ⟨k, h⟩
      simpa [R, restr_apply] using this
  have e1 : finrank ℂ (W.map R) = finrank ℂ W :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hR W)).symm
  let A := {k // e k = 1} → ℂ
  let B := {k // f k = 1} → ℂ
  have hle : W.map R ≤ (W.map (restr e)).map (LinearMap.inl ℂ A B) ⊔
      (W.map (restr f)).map (LinearMap.inr ℂ A B) := by
    rintro _ ⟨u, hu, rfl⟩
    have : R u = LinearMap.inl ℂ A B (restr e u) + LinearMap.inr ℂ A B (restr f u) := by
      simp [R]
    rw [this]
    exact Submodule.add_mem_sup ⟨_, ⟨u, hu, rfl⟩, rfl⟩ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((W.map (restr e)).map (LinearMap.inl ℂ A B)) ((W.map (restr f)).map (LinearMap.inr ℂ A B))
  have h3 := Submodule.finrank_map_le (LinearMap.inl ℂ A B) (W.map (restr e))
  have h4 := Submodule.finrank_map_le (LinearMap.inr ℂ A B) (W.map (restr f))
  rw [← e1]
  exact h1.trans (h2.trans (add_le_add h3 h4))

end General

theorem kneserFor_of_fin
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St)
    (ι : Type) [Fintype ι] : KneserFor ι := by
  intro S T St hS hT hSt
  let Φ : (ι → ℂ) ≃ₐ[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    AlgEquiv.piCongrLeft' ℂ (fun _ => ℂ) (Fintype.equivFin ι)
  have hfr : ∀ X : Submodule ℂ (ι → ℂ),
      finrank ℂ (X.map Φ.toLinearMap) = finrank ℂ X := fun X =>
    LinearEquiv.finrank_map_eq Φ.toLinearEquiv X
  have hne : ∀ X : Submodule ℂ (ι → ℂ), X ≠ ⊥ → X.map Φ.toLinearMap ≠ ⊥ := by
    intro X hX h
    apply hX
    rw [← Submodule.finrank_eq_zero, ← hfr X, h, finrank_bot]
  have hmul := Submodule.map_mul S T Φ.toAlgHom
  have key := hK _ (S.map Φ.toLinearMap) (T.map Φ.toLinearMap) (St.map Φ.toLinearMap)
    (hne S hS) (hne T hT) ?_
  · rw [hfr, hfr, hfr] at key
    erw [← hmul, hfr] at key
    exact key
  · intro x
    have hmul' : (S * T).map Φ.toLinearMap =
        S.map Φ.toLinearMap * T.map Φ.toLinearMap := hmul
    rw [← hmul']
    constructor
    · rintro ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
      refine ⟨y * w, (hSt y).1 hy w hw, ?_⟩
      simp
    · intro h
      refine ⟨Φ.symm x, (hSt _).2 fun w hw => ?_, by simp⟩
      obtain ⟨w', hw', he⟩ := h (Φ w) ⟨w, hw, rfl⟩
      have : w' = Φ.symm x * w := by
        apply Φ.injective
        simp only [AlgEquiv.toLinearMap_apply] at he
        rw [he, map_mul, AlgEquiv.apply_symm_apply]
      rw [← this]
      exact hw'

theorem fermat_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), FermatIso W → 3 * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  have hone : (1 : ι → ℂ) ∉ W := by
    intro h
    have := hW.1 1 h 1 h
    simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  set V := vSpan W with hVdef
  by_cases hconst : ∀ x ∈ stab V, ∀ j k, x j = x k
  ·
    have hSt : finrank ℂ (stab V) ≤ 1 := by
      have : stab V ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x hx i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hU : finrank ℂ ↥(W ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) = finrank ℂ W + 1 := by
      have hinf : W ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxW, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := W.smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hUne : W ⊔ Submodule.span ℂ {(1 : ι → ℂ)} ≠ ⊥ := by
      intro h
      have : (1 : ι → ℂ) ∈ W ⊔ Submodule.span ℂ {(1 : ι → ℂ)} :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      rw [h, Submodule.mem_bot] at this
      exact one_ne_zero this
    have hk := hK ι _ W (stab V) hUne hW0 (fun x => Iff.rfl)
    have hp := perp_bound V W (vSpan_perp hW)
    change _ + _ ≤ finrank ℂ V + _ at hk
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab V := (stab V).sub_mem (one_mem_stab V) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_iso hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_iso hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    omega

theorem fermat_of_kneser
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St) :
    ∀ (M : ℕ) (W : Submodule ℂ (Fin M → ℂ)), (∀ x ∈ W, ∑ i, x i ^ 2 = 0) →
      (∀ x ∈ W, ∑ i, x i ^ 3 = 0) → 3 * Module.finrank ℂ W ≤ M := by
  intro M W h2 h3
  have hQ : ∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0 := by
    intro u hu v hv
    have key : ∑ i, (2 : ℂ) * (u i * v i) =
        (∑ i, (u + v) i ^ 2) - (∑ i, u i ^ 2) - (∑ i, v i ^ 2) := by
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h2 _ (W.add_mem hu hv), h2 u hu, h2 v hv, ← mul_sum] at key
    simpa using key
  have hC : ∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∑ i, u i * v i * z i = 0 := by
    intro u hu v hv z hz
    have key : ∑ i, (6 : ℂ) * (u i * v i * z i) =
        (∑ i, (u + v + z) i ^ 3) - (∑ i, (u + v) i ^ 3) - (∑ i, (u + z) i ^ 3)
          - (∑ i, (v + z) i ^ 3) + (∑ i, u i ^ 3) + (∑ i, v i ^ 3) + (∑ i, z i ^ 3) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h3 _ (W.add_mem (W.add_mem hu hv) hz), h3 _ (W.add_mem hu hv), h3 _ (W.add_mem hu hz),
      h3 _ (W.add_mem hv hz), h3 u hu, h3 v hv, h3 z hz, ← mul_sum] at key
    have h6 : (6 : ℂ) ≠ 0 := by norm_num
    simpa [h6] using key
  have := fermat_general (kneserFor_of_fin hK) M (Fin M) (Fintype.card_fin M) W ⟨hQ, hC⟩
  exact this

end PEqualNP.Gct.Helpers

namespace PEqualNP.Gct.Helpers.FermatIter

open Module Finset PEqualNP.Gct.Helpers

section General

variable {ι : Type} [Fintype ι]

noncomputable def vChain (W : Submodule ℂ (ι → ℂ)) (a : ℕ) : Submodule ℂ (ι → ℂ) :=
  (W + 1) ^ a * W

def perp (W : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {v | ∀ z ∈ W, ∑ i, v i * z i = 0}
  add_mem' {a b} ha hb z hz := by
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha z hz, hb z hz, add_zero]
  zero_mem' z _ := by simp
  smul_mem' c x hx z hz := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, hx z hz, mul_zero]

theorem mem_perp {W : Submodule ℂ (ι → ℂ)} {v : ι → ℂ} :
    v ∈ perp W ↔ ∀ z ∈ W, ∑ i, v i * z i = 0 := Iff.rfl

theorem polar_step (W : Submodule ℂ (ι → ℂ)) (c : ι → ℂ) (n : ℕ)
    (h : ∀ x ∈ W, ∑ i, x i ^ (n + 1) * c i = 0) :
    ∀ x ∈ W, ∀ y ∈ W, ∑ i, x i ^ n * (y i * c i) = 0 := by
  intro x hx y hy
  let q : Polynomial ℂ := ∑ i, Polynomial.C (c i) *
    (Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X) ^ (n + 1)
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have := h (x + t • y) (W.add_mem hx (W.smul_mem t hy))
    simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← this]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hd : Polynomial.eval 0 (Polynomial.derivative q) = 0 := by
    rw [hq]; simp
  have hd2 : Polynomial.eval 0 (Polynomial.derivative q) =
      ((n : ℂ) + 1) * ∑ i, x i ^ n * (y i * c i) := by
    simp only [q, Polynomial.derivative_sum, Polynomial.eval_finsetSum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp [Polynomial.derivative_pow]
    ring
  rw [hd2] at hd
  exact (mul_eq_zero.1 hd).resolve_left (Nat.cast_add_one_ne_zero n)

theorem pow_perp (W : Submodule ℂ (ι → ℂ)) (k : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ r n : ℕ, 2 ≤ n + r → n + r ≤ k → ∀ c ∈ W ^ r, ∀ x ∈ W, ∑ i, x i ^ n * c i = 0 := by
  intro r
  induction r with
  | zero =>
    intro n h2 hk c hc x hx
    rw [pow_zero, Submodule.one_eq_span] at hc
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hc
    have := h n h2 hk x hx
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, ← sum_mul, this, zero_mul]
  | succ r ih =>
    intro n h2 hk c hc
    rw [pow_succ] at hc
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro c' hc' y hy x hx
      have := polar_step W c' n (ih (n + 1) (by omega) (by omega) c' hc') x hx y hy
      refine (sum_congr rfl fun i _ => ?_).trans this
      rw [Pi.mul_apply, mul_comm (c' i)]
    · intro a b ha hb x hx
      simp only [Pi.add_apply, mul_add, sum_add_distrib, ha x hx, hb x hx, add_zero]

theorem chain_le_perp (W : Submodule ℂ (ι → ℂ)) (k : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ a b : ℕ, 1 ≤ b → a + b + 1 ≤ k → (W + 1) ^ a * W ^ b ≤ perp W := by
  intro a
  induction a with
  | zero =>
    intro b hb hk v hv z hz
    rw [pow_zero, one_mul] at hv
    have := pow_perp W k h b 1 (by omega) (by omega) v hv z hz
    refine (sum_congr rfl fun i _ => ?_).trans this
    rw [pow_one, mul_comm]
  | succ a ih =>
    intro b hb hk
    have e : (W + 1) ^ (a + 1) * W ^ b = (W + 1) ^ a * W ^ (b + 1) + (W + 1) ^ a * W ^ b := by
      ring
    rw [e, Submodule.add_eq_sup]
    exact sup_le (ih (b + 1) (by omega) (by omega)) (ih b hb (by omega))

theorem vChain_perp_of_psum (W : Submodule ℂ (ι → ℂ)) (a : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ a + 2 → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0 := by
  intro v hv
  have := chain_le_perp W (a + 2) h a 1 le_rfl le_rfl
  rw [pow_one] at this
  exact this hv

omit [Fintype ι] in
theorem one_mem_add_one (W : Submodule ℂ (ι → ℂ)) : (1 : ι → ℂ) ∈ W + 1 :=
  Submodule.one_le.1 (le_sup_right : (1 : Submodule ℂ (ι → ℂ)) ≤ W ⊔ 1)

omit [Fintype ι] in
theorem vChain_zero (W : Submodule ℂ (ι → ℂ)) : vChain W 0 = W := by
  unfold vChain; rw [pow_zero, one_mul]

omit [Fintype ι] in
theorem vChain_succ (W : Submodule ℂ (ι → ℂ)) (a : ℕ) :
    vChain W (a + 1) = (W + 1) * vChain W a := by
  unfold vChain; rw [pow_succ', mul_assoc]

omit [Fintype ι] in
theorem le_vChain (W : Submodule ℂ (ι → ℂ)) (a : ℕ) : W ≤ vChain W a := by
  induction a with
  | zero => rw [vChain_zero]
  | succ a ih =>
    intro u hu
    rw [vChain_succ]
    have := Submodule.mul_mem_mul (one_mem_add_one W) (ih hu)
    rwa [one_mul] at this

omit [Fintype ι] in

theorem stab_le_stab_mul (S X : Submodule ℂ (ι → ℂ)) : stab X ≤ stab (S * X) := by
  intro x hx v hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro s hs t ht
    rw [mul_left_comm]
    exact Submodule.mul_mem_mul hs (hx t ht)
  · intro a b ha hb
    rw [mul_add]
    exact Submodule.add_mem _ ha hb

omit [Fintype ι] in
theorem stab_vChain_mono (W : Submodule ℂ (ι → ℂ)) {a b : ℕ} (h : a ≤ b) :
    stab (vChain W a) ≤ stab (vChain W b) := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    rw [vChain_succ]
    exact ih.trans (stab_le_stab_mul _ _)

noncomputable def restrAlg (p : ι → ℂ) : (ι → ℂ) →ₐ[ℂ] ({k // p k = 1} → ℂ) where
  toFun u k := u k
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype ι] in
theorem restrAlg_toLinearMap (p : ι → ℂ) : (restrAlg p).toLinearMap = restr p := rfl

omit [Fintype ι] in

theorem vChain_map (W : Submodule ℂ (ι → ℂ)) (p : ι → ℂ) (a : ℕ) :
    vChain (W.map (restr p)) a = (vChain W a).map (restr p) := by
  unfold vChain
  rw [← restrAlg_toLinearMap, Submodule.map_mul, Submodule.map_pow]
  simp only [Submodule.add_eq_sup, Submodule.map_sup, Submodule.map_one]

theorem restr_perp {W : Submodule ℂ (ι → ℂ)} {a : ℕ}
    (hW : ∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0) {p : ι → ℂ}
    (hp : p ∈ stab (vChain W a)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    ∀ v ∈ vChain (W.map (restr p)) a, ∀ z ∈ W.map (restr p), ∑ i, v i * z i = 0 := by
  intro v hv z hz
  rw [vChain_map] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  obtain ⟨z, hz, rfl⟩ := hz
  simp only [restr_apply]
  rw [sum_restr p hp01 (fun k => v k * z k)]
  have := hW _ (hp _ hv) z hz
  simpa only [Pi.mul_apply, mul_assoc] using this

end General

theorem fermat_iter_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) (a : ℕ) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), (∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0) →
        (a + 2) * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; simp
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  have hone : (1 : ι → ℂ) ∉ W := by
    intro h
    have := hW 1 (le_vChain W a h) 1 h
    simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  by_cases hconst : ∀ x ∈ stab (vChain W a), ∀ j k, x j = x k
  ·
    have hSt : ∀ b, b ≤ a → finrank ℂ (stab (vChain W b)) ≤ 1 := by
      intro b hb
      have : stab (vChain W b) ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x (stab_vChain_mono W hb hx) i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hS : W + 1 = W ⊔ Submodule.span ℂ {(1 : ι → ℂ)} := by
      rw [Submodule.add_eq_sup, Submodule.one_eq_span]
    have hU : finrank ℂ ↥(W + 1) = finrank ℂ W + 1 := by
      rw [hS]
      have hinf : W ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxW, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := W.smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hUne : W + 1 ≠ ⊥ := by
      intro h
      have := one_mem_add_one W
      rw [h, Submodule.mem_bot] at this
      exact one_ne_zero this
    have hVne : ∀ b, vChain W b ≠ ⊥ := by
      intro b h
      apply hW0
      rw [eq_bot_iff, ← h]
      exact le_vChain W b
    have grow : ∀ b, b ≤ a → (b + 1) * finrank ℂ W ≤ finrank ℂ (vChain W b) := by
      intro b
      induction b with
      | zero => intro _; rw [vChain_zero]; simp
      | succ b ih =>
        intro hb
        have ih' := ih (by omega)
        have hk := hK ι (W + 1) (vChain W b) (stab ((W + 1) * vChain W b)) hUne (hVne b)
          (fun x => Iff.rfl)
        rw [← vChain_succ] at hk
        have hs := hSt (b + 1) hb
        have e : (b + 1 + 1) * finrank ℂ W = (b + 1) * finrank ℂ W + finrank ℂ W := by ring
        rw [e]
        omega
    have hg := grow a le_rfl
    have hp := perp_bound (vChain W a) W hW
    have e : (a + 2) * finrank ℂ W = (a + 1) * finrank ℂ W + finrank ℂ W := by ring
    rw [e]
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab (vChain W a) :=
      (stab (vChain W a)).sub_mem (one_mem_stab (vChain W a)) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_perp hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_perp hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    calc (a + 2) * finrank ℂ W
        ≤ (a + 2) * (finrank ℂ (W.map (restr e)) + finrank ℂ (W.map (restr f))) :=
          Nat.mul_le_mul_left _ h3
      _ = (a + 2) * finrank ℂ (W.map (restr e)) + (a + 2) * finrank ℂ (W.map (restr f)) :=
          Nat.mul_add _ _ _
      _ ≤ n := by omega

theorem fermat_iter_of_kneser
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St) :
    ∀ (M k : ℕ) (W : Submodule ℂ (Fin M → ℂ)), 2 ≤ k →
      (∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) → k * Module.finrank ℂ W ≤ M := by
  intro M k W hk h
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 2 := ⟨k - 2, by omega⟩
  exact fermat_iter_general (kneserFor_of_fin hK) a M (Fin M) (Fintype.card_fin M) W
    (vChain_perp_of_psum W a h)

end PEqualNP.Gct.Helpers.FermatIter

theorem PEqualNP.Gct.Kit086.kneser : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ → (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) → Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St :=
  PEqualNP.Gct.Helpers.Kneser.kneser_of PEqualNP.Gct.Helpers.Kneser.finite_subalgebra
    PEqualNP.Gct.Helpers.Kneser.etransform

theorem PEqualNP.Gct.Kit086.fermat_iter : ∀ (M k : ℕ) (W : Submodule ℂ (Fin M → ℂ)), 2 ≤ k → (∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) → k * Module.finrank ℂ W ≤ M :=
  PEqualNP.Gct.Helpers.FermatIter.fermat_iter_of_kneser PEqualNP.Gct.Kit086.kneser




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

noncomputable def dcPart (n : ℕ) (t : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => t p - rowSum n t p.1 / n - colSum n t p.2 / n

theorem dcPart_decomp (n : ℕ) (t : Fin n × Fin n → ℂ) (i j : Fin n) :
    t (i, j) = rowSum n t i / n + colSum n t j / n + dcPart n t (i, j) := by
  simp only [dcPart]
  ring

theorem dcPart_mem {n : ℕ} (hn : 1 ≤ n) (t : Fin n × Fin n → ℂ) (h : ∑ p, t p = 0) :
    dcPart n t ∈ DC n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hr : ∑ i, rowSum n t i = 0 := (mem_sumZero _).mp (rowSum_mem t h)
  have hc : ∑ j, colSum n t j = 0 := (mem_sumZero _).mp (colSum_mem t h)
  rw [mem_DC]
  constructor
  · intro i
    simp only [dcPart, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, hc, ← rowSum_apply]
    field_simp
    ring
  · intro j
    simp only [dcPart, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, hr, ← colSum_apply]
    field_simp
    ring

noncomputable def trE (n : ℕ) : (Fin n × Fin n → ℂ) ≃ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodComm (Fin n) (Fin n))

theorem trE_apply (n : ℕ) (t : Fin n × Fin n → ℂ) (i j : Fin n) : trE n t (i, j) = t (j, i) :=
  rfl

theorem gap_swap (n : ℕ) (t : Fin n × Fin n → ℂ) :
    (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (f i, i))) = ∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i)) := by
  have h := gap_eq_perm n (fun p => t (p.2, p.1))
  simp only at h
  rw [h, gap_eq_perm, PEqualNP.Gct.MethodCeiling.eval_permPoly,
    PEqualNP.Gct.MethodCeiling.eval_permPoly, ← Matrix.permanent_transpose]
  rfl

theorem lev_tr {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    Lev n (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))) := by
  rintro _ ⟨t, ht, rfl⟩
  rw [← hL t ht, ← gap_swap]
  rfl

theorem rowSum_tr (n : ℕ) (t : Fin n × Fin n → ℂ) : rowSum n (trE n t) = colSum n t := by
  funext i
  rw [rowSum_apply, colSum_apply]
  rfl

theorem colSum_tr (n : ℕ) (t : Fin n × Fin n → ℂ) : colSum n (trE n t) = rowSum n t := by
  funext j
  rw [rowSum_apply, colSum_apply]
  rfl

theorem map_tr_rowSum (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))).map (rowSum n) =
      L.map (colSum n) := by
  rw [← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun t => rowSum_tr n t

theorem map_tr_colSum (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))).map (colSum n) =
      L.map (rowSum n) := by
  rw [← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun t => colSum_tr n t

theorem finrank_tr_DC (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    Module.finrank ℂ (L ⊓ DC n : Submodule ℂ _) ≤
      Module.finrank ℂ (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)) ⊓ DC n :
        Submodule ℂ _) := by
  have hle : (L ⊓ DC n).map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)) ≤
      L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)) ⊓ DC n := by
    rintro _ ⟨t, ⟨htL, htD⟩, rfl⟩
    refine ⟨⟨t, htL, rfl⟩, ?_⟩
    have htD' := (mem_DC_iff t).mp htD
    exact (mem_DC_iff _).mpr ⟨(rowSum_tr n t).trans htD'.2, (colSum_tr n t).trans htD'.1⟩
  rw [← LinearEquiv.finrank_map_eq (trE n) (L ⊓ DC n)]
  exact Submodule.finrank_mono hle

theorem gap_of_S_wlog
    (hS : ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      Module.finrank ℂ (L.map (rowSum 5)) ≤ Module.finrank ℂ (L.map (colSum 5)) →
      Module.finrank ℂ (L.map (rowSum 5)) + Module.finrank ℂ (L ⊓ DC 5 : Submodule ℂ _) ≤ 4) :
    ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      Module.finrank ℂ L ≤ 8 := by
  intro L hL
  apply skeleton L hL
  rcases le_total (Module.finrank ℂ (L.map (rowSum 5))) (Module.finrank ℂ (L.map (colSum 5)))
    with h | h
  · rw [min_eq_left h]
    exact hS L hL h
  · rw [min_eq_right h]
    have hL' : ∀ t ∈ L.map (trE 5 : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ)),
        (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120 := by
      intro t ht
      rw [lev_tr (lev_five L hL) t ht]
      norm_num [Nat.factorial]
    have h1 := hS _ hL' (by rw [map_tr_rowSum, map_tr_colSum]; exact h)
    rw [map_tr_rowSum] at h1
    have h2 := finrank_tr_DC 5 L
    omega

theorem prod_add_smul {k : ℕ} (x y : Fin k → ℂ) (s : ℂ) :
    ∏ a, (x a + s * y a) = ∑ m ∈ range (k + 1), s ^ m *
      ∑ A ∈ (univ : Finset (Finset (Fin k))).filter (fun A => A.card = m),
        (∏ a ∈ A, y a) * ∏ a ∈ Aᶜ, x a := by
  rw [show (∏ a, (x a + s * y a)) = ∏ a, (s * y a + x a) from
    Finset.prod_congr rfl fun a _ => add_comm _ _, Fintype.prod_add]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (k + 1))
    (fun A _ => by
      have := Finset.card_le_univ A
      rw [Fintype.card_fin] at this
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le this))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_filter.mp hA).2]
  ring

noncomputable def polSum (n k m : ℕ) (t u : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n,
    ∑ A ∈ (univ : Finset (Finset (Fin k))).filter (fun A => A.card = m),
      (∏ a ∈ A, u (i a, j a)) * ∏ a ∈ Aᶜ, t (i a, j a)

theorem lev_pol {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (t u : Fin n × Fin n → ℂ) (ht : t ∈ L) (hu : u ∈ L) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (m : ℕ) (hm : m ≤ k) : polSum n k m t u = 0 := by
  have key : ∀ s : ℂ, ∑ m ∈ range (k + 1), polSum n k m t u * s ^ m = 0 := by
    intro s
    have h1 := lev_inj hL (t + s • u) (L.add_mem ht (L.smul_mem s hu)) k hk1 hkn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, prod_add_smul] at h1
    rw [← h1]
    symm
    calc _ = ∑ i : Fin k ↪ Fin n, ∑ m ∈ range (k + 1), ∑ j : Fin k ↪ Fin n, s ^ m *
          ∑ A ∈ (univ : Finset (Finset (Fin k))).filter (fun A => A.card = m),
            (∏ a ∈ A, u (i a, j a)) * ∏ a ∈ Aᶜ, t (i a, j a) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ m ∈ range (k + 1), ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin n, s ^ m *
          ∑ A ∈ (univ : Finset (Finset (Fin k))).filter (fun A => A.card = m),
            (∏ a ∈ A, u (i a, j a)) * ∏ a ∈ Aᶜ, t (i a, j a) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [polSum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let P : Polynomial ℂ := ∑ j ∈ range (k + 1), Polynomial.C (polSum n k j t u) * Polynomial.X ^ j
  have hP : ∀ s : ℂ, P.eval s = (0 : Polynomial ℂ).eval s := by
    intro s
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    exact key s
  have hPeq : P = 0 := Polynomial.funext hP
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff m) hPeq
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single m] at hc
  · simpa using hc
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hm'
    exact absurd (Finset.mem_range.mpr (by omega)) hm'

theorem lev_mono {n : ℕ} {L K : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hK : K ≤ L) :
    Lev n K :=
  fun t ht => hL t (hK ht)

theorem rank_nullity {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Submodule ℂ (Fin n × Fin n → ℂ)) (f : (Fin n × Fin n → ℂ) →ₗ[ℂ] V) :
    Module.finrank ℂ L = Module.finrank ℂ (L ⊓ LinearMap.ker f : Submodule ℂ _) +
      Module.finrank ℂ (L.map f) := by
  have hrn : Module.finrank ℂ (L.map f) +
      Module.finrank ℂ (L ⊓ LinearMap.ker f : Submodule ℂ _) = Module.finrank ℂ L := by
    rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
      ← (f.submoduleMap L).finrank_range_add_finrank_ker,
      LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]
    simp
  omega

theorem finrank_exact {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    Module.finrank ℂ L = Module.finrank ℂ (L ⊓ DC n : Submodule ℂ _) +
      Module.finrank ℂ (L.map (rowSum n)) +
      Module.finrank ℂ ((L ⊓ LinearMap.ker (rowSum n)).map (colSum n)) := by
  have h1 := rank_nullity L (rowSum n)
  have h2 := rank_nullity (L ⊓ LinearMap.ker (rowSum n)) (colSum n)
  have h3 : L ⊓ LinearMap.ker (rowSum n) ⊓ LinearMap.ker (colSum n) = L ⊓ DC n := by
    rw [DC, LinearMap.ker_prod, inf_assoc]
  rw [h3] at h2
  omega

theorem rowCentred_suff (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (h : Module.finrank ℂ (L ⊓ LinearMap.ker (rowSum 5) : Submodule ℂ _) ≤ 4) :
    Module.finrank ℂ L ≤ 8 := by
  have h1 := rank_nullity L (rowSum 5)
  have h2 := rA_le (lev_five L hL) (by norm_num)
  omega

theorem colCentred_suff (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (h : Module.finrank ℂ (L ⊓ LinearMap.ker (colSum 5) : Submodule ℂ _) ≤ 4) :
    Module.finrank ℂ L ≤ 8 := by
  have h1 := rank_nullity L (colSum 5)
  have h2 := rB_le (lev_five L hL) (by norm_num)
  omega

noncomputable def T3 (n : ℕ) (x y z : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i : Fin 3 ↪ Fin n, ∑ j : Fin 3 ↪ Fin n, x (i 0, j 0) * y (i 1, j 1) * z (i 2, j 2)

theorem T3_add1 (n : ℕ) (x x' y z : Fin n × Fin n → ℂ) :
    T3 n (x + x') y z = T3 n x y z + T3 n x' y z := by
  simp only [T3, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem T3_add2 (n : ℕ) (x y y' z : Fin n × Fin n → ℂ) :
    T3 n x (y + y') z = T3 n x y z + T3 n x y' z := by
  simp only [T3, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem T3_add3 (n : ℕ) (x y z z' : Fin n × Fin n → ℂ) :
    T3 n x y (z + z') = T3 n x y z + T3 n x y z' := by
  simp only [T3, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem T3_smul1 (n : ℕ) (c : ℂ) (x y z : Fin n × Fin n → ℂ) :
    T3 n (c • x) y z = c * T3 n x y z := by
  simp only [T3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem T3_smul2 (n : ℕ) (c : ℂ) (x y z : Fin n × Fin n → ℂ) :
    T3 n x (c • y) z = c * T3 n x y z := by
  simp only [T3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem T3_smul3 (n : ℕ) (c : ℂ) (x y z : Fin n × Fin n → ℂ) :
    T3 n x y (c • z) = c * T3 n x y z := by
  simp only [T3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_emb_perm {n k : ℕ} (σ : Equiv.Perm (Fin k)) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ i : Fin k ↪ Fin n, F (σ.toEmbedding.trans i) = ∑ i : Fin k ↪ Fin n, F i := by
  refine Fintype.sum_bijective (fun i => σ.toEmbedding.trans i)
    ⟨fun i i' h => ?_, fun i => ⟨σ.symm.toEmbedding.trans i, ?_⟩⟩ _ _ (fun i => rfl)
  · refine Function.Embedding.ext fun a => ?_
    have h' := DFunLike.congr_fun h (σ.symm a)
    simpa using h'
  · ext a
    simp

theorem T3_swap12 (n : ℕ) (x y z : Fin n × Fin n → ℂ) : T3 n x y z = T3 n y x z := by
  unfold T3
  rw [← sum_emb_perm (Equiv.swap 0 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_emb_perm (Equiv.swap 0 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.swap_apply_left,
    Equiv.swap_apply_right, h2]
  ring

theorem T3_swap23 (n : ℕ) (x y z : Fin n × Fin n → ℂ) : T3 n x y z = T3 n x z y := by
  unfold T3
  rw [← sum_emb_perm (Equiv.swap 1 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_emb_perm (Equiv.swap 1 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.swap_apply_left,
    Equiv.swap_apply_right, h0]
  ring

theorem T3_diag (n : ℕ) (t : Fin n × Fin n → ℂ) :
    T3 n t t t = ∑ i : Fin 3 ↪ Fin n, ∑ j : Fin 3 ↪ Fin n, ∏ a, t (i a, j a) := by
  simp only [T3, Fin.prod_univ_three]

theorem lev_T3 {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 3 ≤ n) :
    ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L, T3 n x y z = 0 := by
  have hC : ∀ t ∈ L, T3 n t t t = 0 := fun t ht => by
    rw [T3_diag]
    exact lev_inj hL t ht 3 (by norm_num) hn
  have h1 : ∀ t ∈ L, ∀ u ∈ L, T3 n t t u = 0 := by
    intro t ht u hu
    have e1 := hC (t + u) (L.add_mem ht hu)
    have e2 := hC (t + (-1 : ℂ) • u) (L.add_mem ht (L.smul_mem _ hu))
    have hCu := hC u hu
    have hCt := hC t ht
    have s1 : T3 n t u t = T3 n t t u := T3_swap23 n t u t
    have s2 : T3 n u t t = T3 n t t u := (T3_swap12 n u t t).trans (T3_swap23 n t u t)
    have s3 : T3 n u t u = T3 n t u u := T3_swap12 n u t u
    have s4 : T3 n u u t = T3 n t u u := (T3_swap23 n u u t).trans (T3_swap12 n u t u)
    simp only [T3_add1, T3_add2, T3_add3, T3_smul1, T3_smul2, T3_smul3] at e1 e2
    simp only [s1, s2, s3, s4] at e1 e2
    linear_combination (1 / 6 : ℂ) * e1 - (1 / 6 : ℂ) * e2 - (1 / 3 : ℂ) * hCu
  intro x hx y hy z hz
  have e := h1 (x + y) (L.add_mem hx hy) z hz
  simp only [T3_add1, T3_add2] at e
  rw [h1 x hx z hz, h1 y hy z hz, ← T3_swap12 n x y z] at e
  linear_combination (1 / 2 : ℂ) * e

theorem sum_emb_succ {n k : ℕ} (Φ : Fin n → (Fin k → Fin n) → ℂ) :
    ∑ i : Fin (k + 1) ↪ Fin n, Φ (i 0) (fun b => i b.succ) =
      ∑ e : Fin k ↪ Fin n, ∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a), Φ a e := by
  classical
  rw [← (Equiv.embeddingFinSucc k (Fin n)).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ => ?_
  symm
  rw [Finset.sum_subtype (p := fun a => a ∉ Set.range e) (univ.filter (fun a => ∀ b, e b ≠ a))
    (fun a => by simp [Set.mem_range]) (fun a => Φ a e)]
  refine Fintype.sum_congr _ _ fun a => ?_
  simp only [Equiv.coe_embeddingFinSucc_symm, Fin.cons_zero, Fin.cons_succ]

theorem dc_compl {n : ℕ} (d : Fin n × Fin n → ℂ) (hd : d ∈ DC n) (p q : Fin n → Prop)
    [DecidablePred p] [DecidablePred q] :
    ∑ a ∈ univ.filter p, ∑ x ∈ univ.filter q, d (a, x) =
      ∑ a ∈ univ.filter (fun a => ¬ p a), ∑ x ∈ univ.filter (fun x => ¬ q x), d (a, x) := by
  have hr := ((mem_DC d).mp hd).1
  have hc := ((mem_DC d).mp hd).2
  have row : ∀ a, ∑ x ∈ univ.filter q, d (a, x) =
      -∑ x ∈ univ.filter (fun x => ¬ q x), d (a, x) := by
    intro a
    have h := Finset.sum_filter_add_sum_filter_not univ q (fun x => d (a, x))
    rw [hr a] at h
    linear_combination h
  have col : ∀ x, ∑ a ∈ univ.filter p, d (a, x) =
      -∑ a ∈ univ.filter (fun a => ¬ p a), d (a, x) := by
    intro x
    have h := Finset.sum_filter_add_sum_filter_not univ p (fun a => d (a, x))
    rw [hc x] at h
    linear_combination h
  calc ∑ a ∈ univ.filter p, ∑ x ∈ univ.filter q, d (a, x)
      = ∑ a ∈ univ.filter p, -∑ x ∈ univ.filter (fun x => ¬ q x), d (a, x) :=
        Finset.sum_congr rfl fun a _ => row a
    _ = -∑ x ∈ univ.filter (fun x => ¬ q x), ∑ a ∈ univ.filter p, d (a, x) := by
        rw [Finset.sum_neg_distrib, Finset.sum_comm]
    _ = -∑ x ∈ univ.filter (fun x => ¬ q x), -∑ a ∈ univ.filter (fun a => ¬ p a), d (a, x) := by
        rw [Finset.sum_congr rfl fun x _ => col x]
    _ = _ := by rw [Finset.sum_neg_distrib, neg_neg, Finset.sum_comm]

theorem sum_range_emb {n k : ℕ} (e : Fin k ↪ Fin n) (g : Fin n → ℂ) :
    ∑ a ∈ univ.filter (fun a => ¬ ∀ b, e b ≠ a), g a = ∑ b, g (e b) := by
  have h : univ.filter (fun a => ¬ ∀ b, e b ≠ a) = univ.map e := by
    ext a
    simp
  rw [h, Finset.sum_map]

theorem T3_dc {n : ℕ} (d y z : Fin n × Fin n → ℂ) (hd : d ∈ DC n) :
    T3 n d y z = ∑ e : Fin 2 ↪ Fin n, ∑ f : Fin 2 ↪ Fin n, y (e 0, f 0) * z (e 1, f 1) *
      (d (e 0, f 0) + d (e 0, f 1) + d (e 1, f 0) + d (e 1, f 1)) := by
  have step1 : ∀ i : Fin 3 ↪ Fin n,
      ∑ j : Fin 3 ↪ Fin n, d (i 0, j 0) * y (i 1, j 1) * z (i 2, j 2) =
        ∑ f : Fin 2 ↪ Fin n, ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
          d (i 0, x) * y (i 1, f 0) * z (i 2, f 1) :=
    fun i => sum_emb_succ (fun x g => d (i 0, x) * y (i 1, g 0) * z (i 2, g 1))
  have step2 : ∑ i : Fin 3 ↪ Fin n, ∑ f : Fin 2 ↪ Fin n, ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
        d (i 0, x) * y (i 1, f 0) * z (i 2, f 1) =
      ∑ e : Fin 2 ↪ Fin n, ∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a),
        ∑ f : Fin 2 ↪ Fin n, ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
          d (a, x) * y (e 0, f 0) * z (e 1, f 1) :=
    sum_emb_succ (fun a g => ∑ f : Fin 2 ↪ Fin n, ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
      d (a, x) * y (g 0, f 0) * z (g 1, f 1))
  rw [T3, Finset.sum_congr rfl fun i _ => step1 i, step2]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm (s := univ.filter (fun a => ∀ b, e b ≠ a))]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h3 : ∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a), ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
        d (a, x) * y (e 0, f 0) * z (e 1, f 1) =
      (∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a), ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
        d (a, x)) * (y (e 0, f 0) * z (e 1, f 1)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
  rw [h3, dc_compl d hd, Finset.sum_congr rfl fun a _ => sum_range_emb f (fun x => d (a, x)),
    sum_range_emb e (fun a => ∑ c, d (a, f c)), Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  ring

theorem lev_T3_dc {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 3 ≤ n) :
    ∀ d ∈ L ⊓ DC n, ∀ y ∈ L, ∀ z ∈ L,
      ∑ e : Fin 2 ↪ Fin n, ∑ f : Fin 2 ↪ Fin n, y (e 0, f 0) * z (e 1, f 1) *
        (d (e 0, f 0) + d (e 0, f 1) + d (e 1, f 0) + d (e 1, f 1)) = 0 := by
  intro d hd y hy z hz
  rw [← T3_dc d y z hd.2]
  exact lev_T3 hL hn d hd.1 y hy z hz

theorem offdiag2 {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, (if a = b then 0 else ∑ x, ∑ w, if x = w then 0 else F a b x w) =
      ∑ a, ∑ b, ∑ x, ∑ w, F a b x w - ∑ a, ∑ x, ∑ w, F a a x w - ∑ a, ∑ b, ∑ x, F a b x x +
        ∑ a, ∑ x, F a a x x := by
  simp only [offdiag_sum, Finset.sum_sub_distrib]
  ring

theorem T3_dc_sums {n : ℕ} (d y z : Fin n × Fin n → ℂ) (hd : d ∈ DC n) :
    T3 n d y z =
      ∑ a, ∑ b, ∑ x, ∑ w, y (a, x) * z (b, w) * (d (a, x) + d (a, w) + d (b, x) + d (b, w)) -
      ∑ a, ∑ x, ∑ w, y (a, x) * z (a, w) * (d (a, x) + d (a, w) + d (a, x) + d (a, w)) -
      ∑ a, ∑ b, ∑ x, y (a, x) * z (b, x) * (d (a, x) + d (a, x) + d (b, x) + d (b, x)) +
      ∑ a, ∑ x, y (a, x) * z (a, x) * (d (a, x) + d (a, x) + d (a, x) + d (a, x)) := by
  rw [T3_dc d y z hd]
  refine ((Finset.sum_congr rfl fun e _ => sum_emb_two (fun x w => y (e 0, x) * z (e 1, w) *
    (d (e 0, x) + d (e 0, w) + d (e 1, x) + d (e 1, w)))).trans
    (sum_emb_two (fun a b => ∑ x, ∑ w, if x = w then 0 else y (a, x) * z (b, w) *
      (d (a, x) + d (a, w) + d (b, x) + d (b, w))))).trans ?_
  exact offdiag2 (fun a b x w => y (a, x) * z (b, w) * (d (a, x) + d (a, w) + d (b, x) + d (b, w)))

theorem dcA1a {n : ℕ} (d y z : Fin n × Fin n → ℂ) :
    ∑ a, ∑ b, ∑ x, ∑ w, y (a, x) * z (b, w) * d (a, x) =
      (∑ a, ∑ x, d (a, x) * y (a, x)) * (∑ b, ∑ w, z (b, w)) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by ring

theorem dcA1d {n : ℕ} (d y z : Fin n × Fin n → ℂ) :
    ∑ a, ∑ b, ∑ x, ∑ w, y (a, x) * z (b, w) * d (b, w) =
      (∑ a, ∑ x, y (a, x)) * (∑ b, ∑ w, d (b, w) * z (b, w)) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by ring

theorem dcA1b {n : ℕ} (d y z : Fin n × Fin n → ℂ) :
    ∑ a, ∑ b, ∑ x, ∑ w, y (a, x) * z (b, w) * d (a, w) =
      ∑ a, ∑ w, d (a, w) * ((∑ x, y (a, x)) * (∑ b, z (b, w))) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ x, ∑ w, y (a, x) * z (b, w) * d (a, w)
      = ∑ b, ∑ w, ∑ x, y (a, x) * z (b, w) * d (a, w) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ w, ∑ b, ∑ x, y (a, x) * z (b, w) * d (a, w) := Finset.sum_comm
    _ = ∑ w, ∑ x, ∑ b, y (a, x) * z (b, w) * d (a, w) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

theorem dcA1c {n : ℕ} (d y z : Fin n × Fin n → ℂ) :
    ∑ a, ∑ b, ∑ x, ∑ w, y (a, x) * z (b, w) * d (b, x) =
      ∑ b, ∑ x, d (b, x) * ((∑ w, z (b, w)) * (∑ a, y (a, x))) := by
  calc ∑ a, ∑ b, ∑ x, ∑ w, y (a, x) * z (b, w) * d (b, x)
      = ∑ b, ∑ a, ∑ x, ∑ w, y (a, x) * z (b, w) * d (b, x) := Finset.sum_comm
    _ = ∑ b, ∑ x, ∑ a, ∑ w, y (a, x) * z (b, w) * d (b, x) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ x, ∑ w, ∑ a, y (a, x) * z (b, w) * d (b, x) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring

theorem dcA2 {n : ℕ} (d y z : Fin n × Fin n → ℂ) :
    ∑ a, ∑ x, ∑ w, y (a, x) * z (a, w) * (d (a, x) + d (a, w) + d (a, x) + d (a, w)) =
      ∑ a, 2 * ((∑ x, d (a, x) * y (a, x)) * (∑ w, z (a, w)) +
        (∑ x, y (a, x)) * (∑ w, d (a, w) * z (a, w))) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem dcA3 {n : ℕ} (d y z : Fin n × Fin n → ℂ) :
    ∑ a, ∑ b, ∑ x, y (a, x) * z (b, x) * (d (a, x) + d (a, x) + d (b, x) + d (b, x)) =
      ∑ x, 2 * ((∑ a, d (a, x) * y (a, x)) * (∑ b, z (b, x)) +
        (∑ a, y (a, x)) * (∑ b, d (b, x) * z (b, x))) := by
  calc ∑ a, ∑ b, ∑ x, y (a, x) * z (b, x) * (d (a, x) + d (a, x) + d (b, x) + d (b, x))
      = ∑ a, ∑ x, ∑ b, y (a, x) * z (b, x) * (d (a, x) + d (a, x) + d (b, x) + d (b, x)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ b, y (a, x) * z (b, x) * (d (a, x) + d (a, x) + d (b, x) + d (b, x)) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

theorem dcA4 {n : ℕ} (d y z : Fin n × Fin n → ℂ) :
    ∑ a, ∑ x, y (a, x) * z (a, x) * (d (a, x) + d (a, x) + d (a, x) + d (a, x)) =
      ∑ a, ∑ x, 4 * (d (a, x) * y (a, x) * z (a, x)) :=
  Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => by ring

theorem T3_dc_closed {n : ℕ} (d y z : Fin n × Fin n → ℂ) (hd : d ∈ DC n) :
    T3 n d y z =
      (∑ a, ∑ x, d (a, x) * y (a, x)) * (∑ b, ∑ w, z (b, w)) +
      (∑ a, ∑ x, y (a, x)) * (∑ b, ∑ w, d (b, w) * z (b, w)) +
      ∑ a, ∑ w, d (a, w) * ((∑ x, y (a, x)) * (∑ b, z (b, w))) +
      ∑ b, ∑ x, d (b, x) * ((∑ w, z (b, w)) * (∑ a, y (a, x))) -
      ∑ a, 2 * ((∑ x, d (a, x) * y (a, x)) * (∑ w, z (a, w)) +
        (∑ x, y (a, x)) * (∑ w, d (a, w) * z (a, w))) -
      ∑ x, 2 * ((∑ a, d (a, x) * y (a, x)) * (∑ b, z (b, x)) +
        (∑ a, y (a, x)) * (∑ b, d (b, x) * z (b, x))) +
      ∑ a, ∑ x, 4 * (d (a, x) * y (a, x) * z (a, x)) := by
  rw [T3_dc_sums d y z hd, dcA2, dcA3, dcA4, ← dcA1a, ← dcA1b, ← dcA1c, ← dcA1d]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem lev_P3_dc {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (hn : 3 ≤ n) :
    ∀ d ∈ L ⊓ DC n, ∀ y ∈ L, ∀ z ∈ L,
      ∑ a, ∑ w, d (a, w) * (rowSum n y a * colSum n z w) +
      ∑ b, ∑ x, d (b, x) * (rowSum n z b * colSum n y x) +
      ∑ a, ∑ x, 4 * (d (a, x) * y (a, x) * z (a, x)) =
      ∑ a, 2 * ((∑ x, d (a, x) * y (a, x)) * rowSum n z a +
        rowSum n y a * (∑ w, d (a, w) * z (a, w))) +
      ∑ x, 2 * ((∑ a, d (a, x) * y (a, x)) * colSum n z x +
        colSum n y x * (∑ b, d (b, x) * z (b, x))) := by
  intro d hd y hy z hz
  have h0 := lev_T3 hL hn d hd.1 y hy z hz
  have hy0 := lev_sum hL (by omega) y hy
  have hz0 := lev_sum hL (by omega) z hz
  rw [Fintype.sum_prod_type] at hy0 hz0
  rw [T3_dc_closed d y z hd.2, hy0, hz0] at h0
  simp only [rowSum_apply, colSum_apply]
  linear_combination h0

theorem inj_dc_peel {n k : ℕ} (d : Fin n × Fin n → ℂ) (hd : d ∈ DC n)
    (H : (Fin k → Fin n) → (Fin k → Fin n) → ℂ) :
    ∑ i : Fin (k + 1) ↪ Fin n, ∑ j : Fin (k + 1) ↪ Fin n,
        d (i 0, j 0) * H (fun b => i b.succ) (fun b => j b.succ) =
      ∑ e : Fin k ↪ Fin n, ∑ f : Fin k ↪ Fin n, H e f * ∑ b, ∑ c, d (e b, f c) := by
  have step1 : ∀ i : Fin (k + 1) ↪ Fin n,
      ∑ j : Fin (k + 1) ↪ Fin n, d (i 0, j 0) * H (fun b => i b.succ) (fun b => j b.succ) =
        ∑ f : Fin k ↪ Fin n, ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
          d (i 0, x) * H (fun b => i b.succ) f :=
    fun i => sum_emb_succ (fun x g => d (i 0, x) * H (fun b => i b.succ) g)
  have step2 : ∑ i : Fin (k + 1) ↪ Fin n, ∑ f : Fin k ↪ Fin n,
        ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x), d (i 0, x) * H (fun b => i b.succ) f =
      ∑ e : Fin k ↪ Fin n, ∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a),
        ∑ f : Fin k ↪ Fin n, ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x), d (a, x) * H e f :=
    sum_emb_succ (fun a g => ∑ f : Fin k ↪ Fin n, ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
      d (a, x) * H g f)
  rw [Finset.sum_congr rfl fun i _ => step1 i, step2]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm (s := univ.filter (fun a => ∀ b, e b ≠ a))]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h3 : ∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a), ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
        d (a, x) * H e f =
      (∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a), ∑ x ∈ univ.filter (fun x => ∀ b, f b ≠ x),
        d (a, x)) * H e f := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  rw [h3, dc_compl d hd, Finset.sum_congr rfl fun a _ => sum_range_emb f (fun x => d (a, x)),
    sum_range_emb e (fun a => ∑ c, d (a, f c)), mul_comm]

theorem MkPol_dc_peel {n k : ℕ} (ts : Fin (k + 1) → Fin n × Fin n → ℂ) (hd : ts 0 ∈ DC n) :
    PEqualNP.Gct.Helpers.RankOne.MkPol n (k + 1) ts =
      ∑ e : Fin k ↪ Fin n, ∑ f : Fin k ↪ Fin n,
        (∏ b, ts b.succ (e b, f b)) * ∑ b, ∑ c, ts 0 (e b, f c) := by
  rw [← inj_dc_peel (ts 0) hd (fun e f => ∏ b, ts b.succ (e b, f b))]
  unfold PEqualNP.Gct.Helpers.RankOne.MkPol
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Fin.prod_univ_succ _

end PEqualNP.Gct.F210

theorem PEqualNP.Outside.L_gct_210_framefermat : ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) → L ⊓ PEqualNP.Gct.F210.DC 5 = ⊥ → Module.finrank ℂ L ≤ 8 :=
  PEqualNP.Gct.F210.dc_zero
