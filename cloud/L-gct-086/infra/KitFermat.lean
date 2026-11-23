import Mathlib
import PEqualNP.Defs

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


theorem PEqualNP.Outside.L_gct_086_kit2 : ∀ (M k : ℕ) (W : Submodule ℂ (Fin M → ℂ)), 2 ≤ k → (∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) → k * Module.finrank ℂ W ≤ M :=
  PEqualNP.Gct.Kit086.fermat_iter
