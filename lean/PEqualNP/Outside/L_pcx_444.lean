import Mathlib
import PEqualNP.Defs

/-!
# At most one adaptive parity transcript attains minimum quadratic rank with no residual mask

Each query cuts the current direction space `W` to `W' = W ∩ ker ℓ`. The rank of the polar on
the direction space drops by at most two, and it drops at all only when `ℓ` vanishes on the old
radical and is nonzero on `W`. In that case the old radical stays inside the new one, and a dual
vector `w` with `B w = ℓ` on `W` enters the new radical. The two answers have opposite
derivatives along `w`, so at most one child of a clear node is clear, and a masked node has only
masked children.
-/

namespace PEqualNP.Outside.L_pcx_444_aux

open Submodule Module

abbrev Xs (n : ℕ) : Type := Fin n → ZMod 2

lemma z2_add_eq_zero : ∀ x y : ZMod 2, x + y = 0 ↔ x = y := by decide
lemma z2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
lemma z2_two : ∀ c : ZMod 2, c + c = 0 := by decide
lemma z2_ne : ∀ a c : ZMod 2, a ≠ c → a + c = 1 := by decide
lemma z2_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
lemma z2_aux : ∀ a b c : ZMod 2, a + a + b + c = 0 → b = c := by decide
lemma z2_aux2 : ∀ a c : ZMod 2, a + a + c + c ≠ 1 := by decide

section Basic

variable {n : ℕ}

lemma xs_two (x : Xs n) : x + x = 0 := funext fun i => z2_two (x i)

lemma natCard_sub {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M] :
    Nat.card M = 2 ^ finrank (ZMod 2) M := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

lemma card_X : Nat.card (Xs n) = 2 ^ n := by
  rw [natCard_sub, Module.finrank_fin_fun]

lemma fr_le (A C : Submodule (ZMod 2) (Xs n)) (a0 : Xs n)
    (h : ∀ v ∈ A, v ∈ C ∨ v + a0 ∈ C) : finrank (ZMod 2) A ≤ finrank (ZMod 2) C + 1 := by
  have hle : A ≤ C ⊔ span (ZMod 2) {a0} := by
    intro v hv
    rcases h v hv with h1 | h1
    · exact Submodule.mem_sup_left h1
    · have key : (v + a0) + a0 ∈ C ⊔ span (ZMod 2) {a0} :=
        Submodule.add_mem _ (Submodule.mem_sup_left h1)
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a0))
      rwa [add_assoc, xs_two, add_zero] at key
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank C (span (ZMod 2) {a0})
  have h3 : finrank (ZMod 2) (span (ZMod 2) ({a0} : Set (Xs n))) ≤ 1 := by
    simpa using finrank_span_le_card ({a0} : Set (Xs n))
  omega

variable (W W' : Submodule (ZMod 2) (Xs n)) (ℓ : Xs n →ₗ[ZMod 2] ZMod 2)
  (hW' : ∀ u, u ∈ W' ↔ u ∈ W ∧ ℓ u = 0)
include hW'

lemma dimW_le : finrank (ZMod 2) W ≤ finrank (ZMod 2) W' + 1 := by
  by_cases h : ∃ w0 ∈ W, ℓ w0 ≠ 0
  · obtain ⟨w0, hw0, hl0⟩ := h
    apply fr_le W W' w0
    intro v hv
    rcases z2_cases (ℓ v) with h1 | h1
    · exact Or.inl ((hW' v).2 ⟨hv, h1⟩)
    · right
      refine (hW' _).2 ⟨W.add_mem hv hw0, ?_⟩
      rw [map_add, h1, z2_ne_zero _ hl0]
      decide
  · push_neg at h
    apply fr_le W W' 0
    intro v hv
    exact Or.inl ((hW' v).2 ⟨hv, h v hv⟩)

lemma dimW_eq (h : ∃ w0 ∈ W, ℓ w0 ≠ 0) : finrank (ZMod 2) W' + 1 = finrank (ZMod 2) W := by
  have hlt : W' < W := by
    refine lt_of_le_of_ne (fun u hu => ((hW' u).1 hu).1) ?_
    obtain ⟨w0, hw0, hl0⟩ := h
    intro heq
    have : w0 ∈ W' := by rw [heq]; exact hw0
    exact hl0 ((hW' w0).1 this).2
  have := Submodule.finrank_lt_finrank_of_lt hlt
  have := dimW_le W W' ℓ hW'
  omega

lemma W_eq (h : ∀ w ∈ W, ℓ w = 0) : W' = W := by
  ext u
  rw [hW']
  exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, h u h1⟩⟩

lemma zero_or_eq (g : Xs n →ₗ[ZMod 2] ZMod 2) (hg : ∀ v ∈ W', g v = 0) (v1 : Xs n)
    (hv1 : v1 ∈ W) (hg1 : g v1 ≠ 0) : ∀ v ∈ W, g v = ℓ v := by
  have hl1 : ℓ v1 ≠ 0 := fun h0 => hg1 (hg v1 ((hW' v1).2 ⟨hv1, h0⟩))
  intro v hv
  rcases z2_cases (ℓ v) with h1 | h1
  · rw [h1]
    exact hg v ((hW' v).2 ⟨hv, h1⟩)
  · have h2 : g (v + v1) = 0 := hg _ ((hW' _).2 ⟨W.add_mem hv hv1, by
      rw [map_add, h1, z2_ne_zero _ hl1]
      decide⟩)
    rw [map_add, z2_ne_zero _ hg1] at h2
    rw [h1]
    exact (z2_add_eq_zero _ _).1 h2

end Basic

/-! ### The polar form and radicals -/

section Quad

variable {n : ℕ}

/-- The polar form. -/
def Bq (f : Xs n → ZMod 2) (u v : Xs n) : ZMod 2 := f (u+v) + f u + f v + f 0

variable (f : Xs n → ZMod 2)

lemma Bq_symm (u v : Xs n) : Bq f u v = Bq f v u := by
  unfold Bq
  rw [add_comm u v]
  ring

lemma Bq_zero_left (v : Xs n) : Bq f 0 v = 0 := by
  unfold Bq
  rw [zero_add]
  have key : ∀ x y : ZMod 2, x + y + x + y = 0 := by decide
  exact key _ _

lemma Bq_self (u : Xs n) : Bq f u u = 0 := by
  unfold Bq
  rw [xs_two]
  have key : ∀ x y : ZMod 2, x + y + y + x = 0 := by decide
  exact key _ _

variable (hf : ∀ p u v : Xs n, f (p+u+v) + f (p+u) + f (p+v) + f p = Bq f u v)
include hf

lemma Bq_add_left (u u' v : Xs n) : Bq f (u + u') v = Bq f u v + Bq f u' v := by
  have h := hf u u' v
  unfold Bq at h ⊢
  grind

lemma Bq_add_right (u v v' : Xs n) : Bq f u (v + v') = Bq f u v + Bq f u v' := by
  rw [Bq_symm, Bq_add_left f hf, Bq_symm f v, Bq_symm f v']

/-- The polar form as a functional in its second argument. -/
def Bl (u : Xs n) : Xs n →ₗ[ZMod 2] ZMod 2 where
  toFun v := Bq f u v
  map_add' v v' := Bq_add_right f hf u v v'
  map_smul' c v := by
    rcases z2_cases c with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      rw [Bq_symm, Bq_zero_left]
    · simp

omit hf in
lemma Bl_apply' (hf : ∀ p u v : Xs n, f (p+u+v) + f (p+u) + f (p+v) + f p = Bq f u v)
    (u v : Xs n) : Bl f hf u v = Bq f u v := rfl

/-- The polar map from a subspace into its dual. -/
def Phi (W : Submodule (ZMod 2) (Xs n)) : W →ₗ[ZMod 2] Module.Dual (ZMod 2) W where
  toFun w := (Bl f hf w).comp W.subtype
  map_add' w w' := by
    ext v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.add_apply,
      Submodule.coe_add, Bl_apply' f hf]
    exact Bq_add_left f hf _ _ _
  map_smul' c w := by
    ext v
    rcases z2_cases c with rfl | rfl
    · simp only [LinearMap.comp_apply, Submodule.subtype_apply, zero_smul, RingHom.id_apply,
        Submodule.coe_zero, LinearMap.zero_apply, Bl_apply' f hf]
      exact Bq_zero_left f _
    · simp

lemma rad_sum (W : Submodule (ZMod 2) (Xs n)) {u u' : Xs n}
    (hu : u ∈ W ∧ ∀ v ∈ W, Bq f u v = 0) (hu' : u' ∈ W ∧ ∀ v ∈ W, Bq f u' v = 0) :
    u + u' ∈ W ∧ ∀ v ∈ W, Bq f (u + u') v = 0 := by
  refine ⟨W.add_mem hu.1 hu'.1, fun v hv => ?_⟩
  rw [Bq_add_left f hf, hu.2 v hv, hu'.2 v hv, add_zero]

omit hf in
lemma rad_zero (W : Submodule (ZMod 2) (Xs n)) :
    (0 : Xs n) ∈ W ∧ ∀ v ∈ W, Bq f 0 v = 0 :=
  ⟨W.zero_mem, fun v _ => Bq_zero_left f v⟩

omit hf in
lemma rad_smul (W : Submodule (ZMod 2) (Xs n)) (c : ZMod 2) {u : Xs n}
    (hu : u ∈ W ∧ ∀ v ∈ W, Bq f u v = 0) :
    c • u ∈ W ∧ ∀ v ∈ W, Bq f (c • u) v = 0 := by
  rcases z2_cases c with rfl | rfl
  · rw [zero_smul]
    exact rad_zero f W
  · rw [one_smul]
    exact hu

/-- The radical of the polar restricted to `W`. -/
def Rad (W : Submodule (ZMod 2) (Xs n)) : Submodule (ZMod 2) (Xs n) :=
  ⟨⟨⟨{u | u ∈ W ∧ ∀ v ∈ W, Bq f u v = 0}, fun hu hv => rad_sum f hf W hu hv⟩,
    rad_zero f W⟩, fun c _ hu => rad_smul f W c hu⟩

lemma mem_Rad (W : Submodule (ZMod 2) (Xs n)) (u : Xs n) :
    u ∈ Rad f hf W ↔ u ∈ W ∧ ∀ v ∈ W, Bq f u v = 0 := Iff.rfl

lemma Rad_le (W : Submodule (ZMod 2) (Xs n)) : Rad f hf W ≤ W :=
  fun u hu => ((mem_Rad f hf W u).1 hu).1

/-- A functional vanishing on the radical is a polar functional on `W`. -/
lemma exists_dual (W : Submodule (ZMod 2) (Xs n)) (ℓ : Xs n →ₗ[ZMod 2] ZMod 2)
    (hℓ : ∀ r ∈ Rad f hf W, ℓ r = 0) : ∃ w ∈ W, ∀ v ∈ W, Bq f w v = ℓ v := by
  have hmem : ℓ.comp W.subtype ∈ (LinearMap.ker (Phi f hf W)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hR : (w : Xs n) ∈ Rad f hf W := by
      refine (mem_Rad f hf W _).2 ⟨w.2, fun v hv => ?_⟩
      have := LinearMap.congr_fun hw ⟨v, hv⟩
      simpa [Phi, Bl_apply' f hf] using this
    simpa using hℓ _ hR
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨Λ, hΛ⟩ := hmem
  set w0 : W := (Module.evalEquiv (ZMod 2) W).symm Λ with hw0
  refine ⟨(w0 : Xs n), w0.2, fun v hv => ?_⟩
  have h1 := LinearMap.congr_fun hΛ ⟨v, hv⟩
  rw [LinearMap.dualMap_apply] at h1
  have h2 := Module.apply_evalEquiv_symm_apply (R := ZMod 2) (M := W) (Phi f hf W ⟨v, hv⟩) Λ
  rw [← h2, ← hw0] at h1
  simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    Submodule.subtype_apply, Bl_apply' f hf] at h1
  rw [Bq_symm]
  exact h1

section Step

variable (W W' : Submodule (ZMod 2) (Xs n)) (ℓ : Xs n →ₗ[ZMod 2] ZMod 2)
  (hW' : ∀ u, u ∈ W' ↔ u ∈ W ∧ ℓ u = 0)
include hW'

lemma radW_le : finrank (ZMod 2) (Rad f hf W') ≤ finrank (ZMod 2) (Rad f hf W) + 1 := by
  by_cases h : ∃ s0 ∈ Rad f hf W', s0 ∉ Rad f hf W
  · obtain ⟨s0, hs0, hs0'⟩ := h
    have key : ∀ x ∈ Rad f hf W', x ∉ Rad f hf W → ∀ v ∈ W, Bq f x v = ℓ v := by
      intro x hx hx'
      have hxW : x ∈ W := ((hW' x).1 ((mem_Rad f hf W' x).1 hx).1).1
      have hex : ∃ v1 ∈ W, Bq f x v1 ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx' ((mem_Rad f hf W x).2 ⟨hxW, hcon⟩)
      obtain ⟨v1, hv1, hne⟩ := hex
      exact zero_or_eq W W' ℓ hW' (Bl f hf x)
        (fun v hv => ((mem_Rad f hf W' x).1 hx).2 v hv) v1 hv1 hne
    apply fr_le _ _ s0
    intro u hu
    by_cases hu' : u ∈ Rad f hf W
    · exact Or.inl hu'
    · right
      have hu1 := key u hu hu'
      have hs1 := key s0 hs0 hs0'
      have huW : u ∈ W := ((hW' u).1 ((mem_Rad f hf W' u).1 hu).1).1
      have hsW : s0 ∈ W := ((hW' s0).1 ((mem_Rad f hf W' s0).1 hs0).1).1
      refine (mem_Rad f hf W _).2 ⟨W.add_mem huW hsW, fun v hv => ?_⟩
      rw [Bq_add_left f hf, hu1 v hv, hs1 v hv, z2_two]
  · push_neg at h
    apply fr_le _ _ 0
    intro u hu
    exact Or.inl (h u hu)

lemma radW_lt (h : ∃ r ∈ Rad f hf W, ℓ r ≠ 0) :
    finrank (ZMod 2) (Rad f hf W') + 1 ≤ finrank (ZMod 2) (Rad f hf W) := by
  obtain ⟨r, hr, hlr⟩ := h
  have hrW := ((mem_Rad f hf W r).1 hr).1
  have hle : Rad f hf W' ≤ Rad f hf W := by
    intro u hu
    obtain ⟨huW', hu0⟩ := (mem_Rad f hf W' u).1 hu
    have huW := ((hW' u).1 huW').1
    refine (mem_Rad f hf W u).2 ⟨huW, fun v hv => ?_⟩
    rcases z2_cases (ℓ v) with h1 | h1
    · exact hu0 v ((hW' v).2 ⟨hv, h1⟩)
    · have h2 := hu0 (v + r) ((hW' _).2 ⟨W.add_mem hv hrW, by
        rw [map_add, h1, z2_ne_zero _ hlr]
        decide⟩)
      have h3 : Bq f u r = 0 := by
        rw [Bq_symm]
        exact ((mem_Rad f hf W r).1 hr).2 u huW
      rw [Bq_add_right f hf, h3, add_zero] at h2
      exact h2
  have hlt : Rad f hf W' < Rad f hf W := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have : r ∈ Rad f hf W' := by rw [heq]; exact hr
    exact hlr ((hW' r).1 ((mem_Rad f hf W' r).1 this).1).2
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

lemma rad_mono (hP : ∀ r ∈ Rad f hf W, ℓ r = 0) : Rad f hf W ≤ Rad f hf W' := by
  intro u hu
  obtain ⟨huW, hu0⟩ := (mem_Rad f hf W u).1 hu
  exact (mem_Rad f hf W' u).2 ⟨(hW' u).2 ⟨huW, hP u hu⟩, fun v hv => hu0 v ((hW' v).1 hv).1⟩

lemma dual_vec (hP : ∀ r ∈ Rad f hf W, ℓ r = 0) :
    ∃ w ∈ Rad f hf W', ∀ v ∈ W, Bq f w v = ℓ v := by
  obtain ⟨w, hw, hwv⟩ := exists_dual f hf W ℓ hP
  refine ⟨w, (mem_Rad f hf W' w).2 ⟨(hW' w).2 ⟨hw, ?_⟩, fun v hv => ?_⟩, hwv⟩
  · rw [← hwv w hw, Bq_self]
  · rw [hwv v ((hW' v).1 hv).1]
    exact ((hW' v).1 hv).2

end Step

end Quad

/-! ### Adaptive transcripts -/

section Adaptive

variable {n D : ℕ}

/-- The answers given before a stage. -/
def pst (b : Fin D → ZMod 2) (stage : Fin D) (j : Fin stage.val) : ZMod 2 :=
  b ⟨j.val, Nat.lt_trans j.isLt stage.isLt⟩

variable (ask : (step : Fin D) → (Fin step.val → ZMod 2) → Xs n →ₗ[ZMod 2] ZMod 2)

lemma wk_add (b : Fin D → ZMod 2) (s : ℕ) {x y : Xs n}
    (hx : ∀ t : Fin D, t.val < s → ask t (pst b t) x = 0)
    (hy : ∀ t : Fin D, t.val < s → ask t (pst b t) y = 0) :
    ∀ t : Fin D, t.val < s → ask t (pst b t) (x + y) = 0 := by
  intro t ht
  rw [map_add, hx t ht, hy t ht, add_zero]

lemma wk_smul (b : Fin D → ZMod 2) (s : ℕ) (c : ZMod 2) {x : Xs n}
    (hx : ∀ t : Fin D, t.val < s → ask t (pst b t) x = 0) :
    ∀ t : Fin D, t.val < s → ask t (pst b t) (c • x) = 0 := by
  intro t ht
  rw [map_smul, hx t ht, smul_zero]

/-- The directions after the first `s` queries. -/
def Wk (b : Fin D → ZMod 2) (s : ℕ) : Submodule (ZMod 2) (Xs n) :=
  ⟨⟨⟨{u | ∀ t : Fin D, t.val < s → ask t (pst b t) u = 0},
    fun hx hy => wk_add ask b s hx hy⟩, fun t _ => map_zero _⟩,
    fun c _ hx => wk_smul ask b s c hx⟩

lemma mem_Wk (b : Fin D → ZMod 2) (s : ℕ) (u : Xs n) :
    u ∈ Wk ask b s ↔ ∀ t : Fin D, t.val < s → ask t (pst b t) u = 0 := Iff.rfl

lemma Wk_succ (b : Fin D → ZMod 2) (t : Fin D) (u : Xs n) :
    u ∈ Wk ask b (t.val + 1) ↔ u ∈ Wk ask b t.val ∧ ask t (pst b t) u = 0 := by
  rw [mem_Wk, mem_Wk]
  constructor
  · intro h
    exact ⟨fun t' ht' => h t' (by omega), h t (by omega)⟩
  · rintro ⟨h1, h2⟩ t' ht'
    by_cases hts : t'.val < t.val
    · exact h1 t' hts
    · have : t' = t := Fin.ext (by omega)
      subst this
      exact h2

lemma Wk_zero (b : Fin D → ZMod 2) : Wk ask b 0 = ⊤ :=
  eq_top_iff.2 fun u _ => (mem_Wk ask b 0 u).2 fun _ ht => absurd ht (Nat.not_lt_zero _)

lemma fW0 (b : Fin D → ZMod 2) : finrank (ZMod 2) (Wk ask b 0) = n := by
  rw [Wk_zero, finrank_top, Module.finrank_fin_fun]

omit ask in
lemma pst_eq (b b' : Fin D → ZMod 2) (k : ℕ) (hag : ∀ i : Fin D, i.val < k → b i = b' i)
    (t : Fin D) (ht : t.val ≤ k) : pst b t = pst b' t := by
  funext j
  exact hag _ (lt_of_lt_of_le j.isLt ht)

lemma Wk_eq (b b' : Fin D → ZMod 2) (k : ℕ) (hag : ∀ i : Fin D, i.val < k → b i = b' i)
    (s : ℕ) (hs : s ≤ k + 1) : Wk ask b s = Wk ask b' s := by
  ext u
  rw [mem_Wk, mem_Wk]
  constructor
  · intro h t ht
    rw [← pst_eq b b' k hag t (by omega)]
    exact h t ht
  · intro h t ht
    rw [pst_eq b b' k hag t (by omega)]
    exact h t ht

lemma card_W (b : Fin D → ZMod 2) :
    Nat.card {u : Xs n // ∀ turn, ask turn (pst b turn) u = 0} =
      2 ^ finrank (ZMod 2) (Wk ask b D) := by
  rw [← natCard_sub (M := ↥(Wk ask b D))]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun u =>
    ⟨fun h t _ => h t, fun h t => h t t.isLt⟩))

lemma card_cell (b : Fin D → ZMod 2) (x0 : Xs n)
    (hx0 : ∀ turn, ask turn (pst b turn) x0 = b turn) :
    Nat.card {x : Xs n // ∀ turn, ask turn (pst b turn) x = b turn} =
      2 ^ finrank (ZMod 2) (Wk ask b D) := by
  rw [← natCard_sub (M := ↥(Wk ask b D))]
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨x.1 + x0, (mem_Wk ask b D _).2 fun t _ => by
        rw [map_add, x.2 t, hx0 t, z2_two]⟩
      invFun := fun w => ⟨w.1 + x0, fun t => by
        rw [map_add, (mem_Wk ask b D _).1 w.2 t t.isLt, hx0 t, zero_add]⟩
      left_inv := fun x => Subtype.ext (by
        show x.1 + x0 + x0 = x.1
        rw [add_assoc, xs_two, add_zero])
      right_inv := fun w => Subtype.ext (by
        show w.1 + x0 + x0 = w.1
        rw [add_assoc, xs_two, add_zero]) }

end Adaptive

/-! ### The quantities in the statement -/

/-- Half the rank of the polar on the final direction space. -/
noncomputable def PR {n D : ℕ} (f : Xs n → ZMod 2)
    (ask : (step : Fin D) → (Fin step.val → ZMod 2) → Xs n →ₗ[ZMod 2] ZMod 2)
    (b : Fin D → ZMod 2) : ℕ :=
  ((Nat.card {u : Xs n // ∀ turn, ask turn (pst b turn) u = 0}).log2 -
    (Nat.card {u : Xs n // (∀ turn, ask turn (pst b turn) u = 0) ∧
      ∀ v, (∀ turn, ask turn (pst b turn) v = 0) → Bq f u v = 0}).log2)/2

/-- Half the rank of the polar. -/
noncomputable def MM {n : ℕ} (f : Xs n → ZMod 2) : ℕ :=
  (n - (Nat.card {u : Xs n // ∀ v : Xs n, Bq f u v = 0}).log2)/2

/-- A transcript of minimum rank with no residual mask. -/
def Good {n D : ℕ} (f : Xs n → ZMod 2)
    (ask : (step : Fin D) → (Fin step.val → ZMod 2) → Xs n →ₗ[ZMod 2] ZMod 2)
    (b : Fin D → ZMod 2) : Prop :=
  PR f ask b = MM f - D ∧ ∃ x : Xs n, (∀ turn, ask turn (pst b turn) x = b turn) ∧
    ∀ u, ((∀ turn, ask turn (pst b turn) u = 0) ∧
      ∀ v, (∀ turn, ask turn (pst b turn) v = 0) → Bq f u v = 0) → f (x+u) = f x

section Main

variable {n D : ℕ} (f : Xs n → ZMod 2)
  (hf : ∀ p u v : Xs n, f (p+u+v) + f (p+u) + f (p+v) + f p = Bq f u v)
  (ask : (step : Fin D) → (Fin step.val → ZMod 2) → Xs n →ₗ[ZMod 2] ZMod 2)
include hf

/-- The query at turn `t` drops one polar pair. -/
def Pp (b : Fin D → ZMod 2) (t : Fin D) : Prop :=
  (∀ r ∈ Rad f hf (Wk ask b t.val), ask t (pst b t) r = 0) ∧
    ∃ w ∈ Wk ask b t.val, ask t (pst b t) w ≠ 0

/-- The node after `s` answers is clear. -/
def Cl (b : Fin D → ZMod 2) (s : ℕ) : Prop :=
  ∃ x : Xs n, (∀ t : Fin D, t.val < s → ask t (pst b t) x = b t) ∧
    ∀ u ∈ Rad f hf (Wk ask b s), f (x+u) = f x

lemma card_R (b : Fin D → ZMod 2) :
    Nat.card {u : Xs n // (∀ turn, ask turn (pst b turn) u = 0) ∧
      ∀ v, (∀ turn, ask turn (pst b turn) v = 0) → Bq f u v = 0} =
      2 ^ finrank (ZMod 2) (Rad f hf (Wk ask b D)) := by
  rw [← natCard_sub (M := ↥(Rad f hf (Wk ask b D)))]
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun u => ?_))
  rw [mem_Rad, mem_Wk]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun t _ => h1 t, fun v hv => h2 v (fun t => (mem_Wk ask b D v).1 hv t t.isLt)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun t => h1 t t.isLt, fun v hv => h2 v ((mem_Wk ask b D v).2 fun t _ => hv t)⟩

lemma card_R0 (b : Fin D → ZMod 2) :
    Nat.card {u : Xs n // ∀ v : Xs n, Bq f u v = 0} =
      2 ^ finrank (ZMod 2) (Rad f hf (Wk ask b 0)) := by
  rw [← natCard_sub (M := ↥(Rad f hf (Wk ask b 0)))]
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun u => ?_))
  rw [mem_Rad, Wk_zero]
  exact ⟨fun h => ⟨Submodule.mem_top, fun v _ => h v⟩, fun h v => h.2 v Submodule.mem_top⟩

lemma PR_eq (b : Fin D → ZMod 2) : PR f ask b =
    (finrank (ZMod 2) (Wk ask b D) - finrank (ZMod 2) (Rad f hf (Wk ask b D)))/2 := by
  unfold PR
  rw [card_W ask b, card_R f hf ask b, Nat.log2_two_pow, Nat.log2_two_pow]

lemma MM_eq (b : Fin D → ZMod 2) : MM f = (n - finrank (ZMod 2) (Rad f hf (Wk ask b 0)))/2 := by
  unfold MM
  rw [card_R0 f hf ask b, Nat.log2_two_pow]

lemma step_facts (b : Fin D → ZMod 2) (s : ℕ) (hs : s < D) :
    finrank (ZMod 2) (Wk ask b s) ≤ finrank (ZMod 2) (Wk ask b (s+1)) + 1 ∧
    finrank (ZMod 2) (Rad f hf (Wk ask b (s+1))) ≤
      finrank (ZMod 2) (Rad f hf (Wk ask b s)) + 1 ∧
    (¬ Pp f hf ask b ⟨s, hs⟩ → finrank (ZMod 2) (Wk ask b s) +
      finrank (ZMod 2) (Rad f hf (Wk ask b (s+1))) ≤
      finrank (ZMod 2) (Wk ask b (s+1)) + finrank (ZMod 2) (Rad f hf (Wk ask b s))) ∧
    (Pp f hf ask b ⟨s, hs⟩ →
      finrank (ZMod 2) (Wk ask b (s+1)) + 1 = finrank (ZMod 2) (Wk ask b s)) := by
  have hW' : ∀ u, u ∈ Wk ask b (s+1) ↔
      u ∈ Wk ask b s ∧ ask ⟨s, hs⟩ (pst b ⟨s, hs⟩) u = 0 :=
    Wk_succ ask b ⟨s, hs⟩
  have a1 := dimW_le (Wk ask b s) (Wk ask b (s+1)) _ hW'
  have a2 := radW_le f hf (Wk ask b s) (Wk ask b (s+1)) _ hW'
  refine ⟨a1, a2, fun hnp => ?_, fun hP => dimW_eq _ _ _ hW' hP.2⟩
  by_cases hP1 : ∀ r ∈ Rad f hf (Wk ask b s), ask ⟨s, hs⟩ (pst b ⟨s, hs⟩) r = 0
  · have hP2 : ∀ w ∈ Wk ask b s, ask ⟨s, hs⟩ (pst b ⟨s, hs⟩) w = 0 := by
      intro w hw
      by_contra hne
      exact hnp ⟨hP1, w, hw, hne⟩
    have heq := W_eq (Wk ask b s) (Wk ask b (s+1)) _ hW' hP2
    have e1 : finrank (ZMod 2) (Wk ask b (s+1)) = finrank (ZMod 2) (Wk ask b s) := by
      rw [heq]
    have e2 : finrank (ZMod 2) (Rad f hf (Wk ask b (s+1))) =
        finrank (ZMod 2) (Rad f hf (Wk ask b s)) := by
      rw [heq]
    omega
  · push_neg at hP1
    have := radW_lt f hf (Wk ask b s) (Wk ask b (s+1)) _ hW' hP1
    omega

lemma chain (b : Fin D → ZMod 2) : ∀ s, s ≤ D →
    (n + finrank (ZMod 2) (Rad f hf (Wk ask b s)) ≤
      finrank (ZMod 2) (Wk ask b s) + finrank (ZMod 2) (Rad f hf (Wk ask b 0)) + 2 * s) ∧
    ((∃ t : Fin D, t.val < s ∧ ¬ Pp f hf ask b t) →
      n + finrank (ZMod 2) (Rad f hf (Wk ask b s)) + 2 ≤
      finrank (ZMod 2) (Wk ask b s) + finrank (ZMod 2) (Rad f hf (Wk ask b 0)) + 2 * s) ∧
    ((∀ t : Fin D, t.val < s → Pp f hf ask b t) → finrank (ZMod 2) (Wk ask b s) + s = n) := by
  intro s
  induction s with
  | zero =>
    intro _
    have h0 := fW0 ask b
    refine ⟨by omega, fun ⟨_, ht, _⟩ => absurd ht (Nat.not_lt_zero _), fun _ => by omega⟩
  | succ s ih =>
    intro hs
    have hsD : s < D := by omega
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    obtain ⟨a1, a2, a3, a4⟩ := step_facts f hf ask b s hsD
    refine ⟨by omega, ?_, ?_⟩
    · rintro ⟨t, ht, hnp⟩
      by_cases hts : t.val < s
      · have := i2 ⟨t, hts, hnp⟩
        omega
      · obtain rfl : t = ⟨s, hsD⟩ := Fin.ext (by show t.val = s; omega)
        have := a3 hnp
        omega
    · intro hall
      have := i3 (fun t ht => hall t (by omega))
      have := a4 (hall ⟨s, hsD⟩ (by show s < s + 1; omega))
      omega

lemma allP (b : Fin D → ZMod 2) (hD : D ≤ MM f) (hp : PR f ask b = MM f - D) :
    (∀ t : Fin D, Pp f hf ask b t) ∧ finrank (ZMod 2) (Wk ask b D) + D = n := by
  rw [PR_eq f hf ask b, MM_eq f hf ask b] at hp
  rw [MM_eq f hf ask b] at hD
  obtain ⟨_, c2, c3⟩ := chain f hf ask b D le_rfl
  have h1 := Submodule.finrank_mono (Rad_le f hf (Wk ask b 0))
  rw [fW0] at h1
  have hall : ∀ t : Fin D, Pp f hf ask b t := by
    by_contra hcon
    obtain ⟨t, ht⟩ := not_forall.1 hcon
    have := c2 ⟨t, t.isLt, ht⟩
    omega
  exact ⟨hall, c3 (fun t _ => hall t)⟩

lemma Cl_D (b : Fin D → ZMod 2) (x : Xs n) (hxc : ∀ turn, ask turn (pst b turn) x = b turn)
    (hxr : ∀ u, ((∀ turn, ask turn (pst b turn) u = 0) ∧
      ∀ v, (∀ turn, ask turn (pst b turn) v = 0) → Bq f u v = 0) → f (x+u) = f x) :
    Cl f hf ask b D := by
  refine ⟨x, fun t _ => hxc t, fun u hu => hxr u ⟨fun t => ?_, fun v hv => ?_⟩⟩
  · exact (mem_Wk ask b D u).1 ((mem_Rad f hf _ u).1 hu).1 t t.isLt
  · exact ((mem_Rad f hf _ u).1 hu).2 v ((mem_Wk ask b D v).2 fun t _ => hv t)

lemma Cl_all (b : Fin D → ZMod 2) (hall : ∀ t : Fin D, Pp f hf ask b t)
    (hD : Cl f hf ask b D) : ∀ k, k ≤ D → Cl f hf ask b (D - k) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Nat.sub_zero]
    exact hD
  | succ k ih =>
    intro hk
    obtain ⟨x, hx1, hx2⟩ := ih (by omega)
    have hs : D - (k+1) < D := by omega
    have e : D - k = D - (k+1) + 1 := by omega
    rw [e] at hx1 hx2
    refine ⟨x, fun t ht => hx1 t (by omega), fun u hu => hx2 u ?_⟩
    exact rad_mono f hf _ _ _ (Wk_succ ask b ⟨D - (k+1), hs⟩) (hall ⟨D - (k+1), hs⟩).1 hu

lemma good_clear (b : Fin D → ZMod 2) (hD : D ≤ MM f) (hb : Good f ask b) :
    ∀ u : Xs n, (∀ v, Bq f u v = 0) → f u = f 0 := by
  obtain ⟨hp, x, hxc, hxr⟩ := hb
  obtain ⟨hall, -⟩ := allP f hf ask b hD hp
  have h0 := Cl_all f hf ask b hall (Cl_D f hf ask b x hxc hxr) D le_rfl
  rw [Nat.sub_self] at h0
  obtain ⟨y, -, hy⟩ := h0
  intro u hu
  have hR : u ∈ Rad f hf (Wk ask b 0) :=
    (mem_Rad f hf _ u).2 ⟨(mem_Wk ask b 0 u).2 (fun _ ht => absurd ht (Nat.not_lt_zero _)),
      fun v _ => hu v⟩
  have e1 := hy u hR
  have key := hf 0 y u
  simp only [zero_add] at key
  rw [Bq_symm, hu y, e1] at key
  exact z2_aux _ _ _ key

lemma good_unique (b b' : Fin D → ZMod 2) (hD : D ≤ MM f) (hb : Good f ask b)
    (hb' : Good f ask b') : b = b' := by
  classical
  by_contra hne
  have hex : ∃ k, ∃ hk : k < D, b ⟨k, hk⟩ ≠ b' ⟨k, hk⟩ := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext fun i => hcon i.val i.isLt)
  obtain ⟨k, ⟨hk, hbk⟩, hmin⟩ : ∃ k, (∃ hk : k < D, b ⟨k, hk⟩ ≠ b' ⟨k, hk⟩) ∧
      ∀ j < k, ¬ ∃ hj : j < D, b ⟨j, hj⟩ ≠ b' ⟨j, hj⟩ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hag : ∀ i : Fin D, i.val < k → b i = b' i := by
    intro i hi
    have := hmin i.val hi
    push_neg at this
    exact this i.isLt
  obtain ⟨t0, rfl⟩ : ∃ t0 : Fin D, t0.val = k := ⟨⟨k, hk⟩, rfl⟩
  have hbk' : b t0 ≠ b' t0 := hbk
  obtain ⟨hp, x, hxc, hxr⟩ := hb
  obtain ⟨hp', x', hxc', hxr'⟩ := hb'
  obtain ⟨hall, -⟩ := allP f hf ask b hD hp
  obtain ⟨hall', -⟩ := allP f hf ask b' hD hp'
  have hClb := Cl_all f hf ask b hall (Cl_D f hf ask b x hxc hxr) (D - (t0.val+1)) (by omega)
  have hClb' := Cl_all f hf ask b' hall' (Cl_D f hf ask b' x' hxc' hxr')
    (D - (t0.val+1)) (by omega)
  have e : D - (D - (t0.val+1)) = t0.val + 1 := by omega
  rw [e] at hClb hClb'
  obtain ⟨y, hyc, hyr⟩ := hClb
  obtain ⟨y', hyc', hyr'⟩ := hClb'
  obtain ⟨w, hw, hwv⟩ := dual_vec f hf (Wk ask b t0.val) (Wk ask b (t0.val+1))
    (ask t0 (pst b t0)) (Wk_succ ask b t0) (hall t0).1
  have hWe := Wk_eq ask b b' t0.val hag (t0.val+1) le_rfl
  have hw' : w ∈ Rad f hf (Wk ask b' (t0.val+1)) := by rw [← hWe]; exact hw
  have e1 := hyr w hw
  have e2 := hyr' w hw'
  have hℓ : ask t0 (pst b t0) = ask t0 (pst b' t0) := by
    rw [pst_eq b b' t0.val hag t0 le_rfl]
  have hv : y' + y ∈ Wk ask b t0.val := by
    refine (mem_Wk ask b t0.val _).2 fun i hi => ?_
    rw [map_add, hyc i (by omega), pst_eq b b' t0.val hag i hi.le, hyc' i (by omega),
      hag i hi, z2_two]
  have hlv : ask t0 (pst b t0) (y' + y) = 1 := by
    rw [map_add, hyc t0 (by omega), hℓ, hyc' t0 (by omega)]
    exact z2_ne _ _ (Ne.symm hbk')
  have key := hf y (y' + y) w
  have hyy : y + (y' + y) = y' := by
    rw [add_comm y' y, ← add_assoc, xs_two, zero_add]
  rw [hyy, Bq_symm, hwv _ hv, hlv, e1, e2] at key
  exact z2_aux2 _ _ key

theorem main (hD : D ≤ MM f) :
    (∀ b : Fin D → ZMod 2, (∃ x, ∀ turn, ask turn (pst b turn) x = b turn) →
      MM f - D ≤ PR f ask b) ∧
    (∀ b : Fin D → ZMod 2, (∃ x, ∀ turn, ask turn (pst b turn) x = b turn) →
      PR f ask b = MM f - D →
      2^D * Nat.card {x : Xs n // ∀ turn, ask turn (pst b turn) x = b turn} =
        Nat.card (Xs n)) ∧
    Nat.card {b : Fin D → ZMod 2 // Good f ask b} ≤ 1 ∧
    (¬ (∀ u : Xs n, (∀ v, Bq f u v = 0) → f u = f 0) →
      Nat.card {b : Fin D → ZMod 2 // Good f ask b} = 0) := by
  refine ⟨fun b _ => ?_, fun b ⟨x0, hx0⟩ hp => ?_, ?_, fun hnc => ?_⟩
  · rw [PR_eq f hf ask b, MM_eq f hf ask b]
    obtain ⟨c1, -, -⟩ := chain f hf ask b D le_rfl
    have h1 := Submodule.finrank_mono (Rad_le f hf (Wk ask b 0))
    rw [fW0] at h1
    omega
  · obtain ⟨-, hdim⟩ := allP f hf ask b hD hp
    rw [card_cell ask b x0 hx0, card_X, ← pow_add]
    congr 1
    omega
  · rw [Finite.card_le_one_iff_subsingleton]
    constructor
    rintro ⟨b, hb⟩ ⟨b', hb'⟩
    exact Subtype.ext (good_unique f hf ask b b' hD hb hb')
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨b, hb⟩
    exact hnc (good_clear f hf ask b hD hb)

end Main

end PEqualNP.Outside.L_pcx_444_aux

theorem PEqualNP.Outside.L_pcx_444 : ∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ (f : X → F),
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) →
    let m := (n - (Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    let clear := ∀ u : X, (∀ v : X, B u v=0) → f u=f 0
    ∀ D : ℕ, D ≤ m →
      let A := Fin D → F
      let past := fun (b : A) (stage : Fin D) (j : Fin stage.val) =>
        b ⟨j.val, Nat.lt_trans j.isLt stage.isLt⟩
      ∀ (ask : (step : Fin D) → (Fin step.val → F) → X →ₗ[F] F),
        let cell := fun (b : A) (x : X) => ∀ turn, ask turn (past b turn) x=b turn
        let dir := fun (b : A) (u : X) => ∀ turn, ask turn (past b turn) u=0
        let rad := fun (b : A) (u : X) => dir b u ∧ ∀ v, dir b v → B u v=0
        let pairs := fun b : A =>
          ((Nat.card {u : X // dir b u}).log2 - (Nat.card {u : X // rad b u}).log2)/2
        let good := fun b : A => pairs b=m-D ∧
          ∃ x : X, cell b x ∧ ∀ u, rad b u → f (x+u)=f x
        (∀ b : A, (∃ x, cell b x) → m-D ≤ pairs b) ∧
        (∀ b : A, (∃ x, cell b x) → pairs b=m-D →
          2^D * Nat.card {x : X // cell b x} = Nat.card X) ∧
        Nat.card {b : A // good b} ≤ 1 ∧
        (¬ clear → Nat.card {b : A // good b} = 0) := by
  intro n F X f B hf m clear D hD A past ask cell dir rad pairs good
  exact PEqualNP.Outside.L_pcx_444_aux.main f hf ask hD
