import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Gct.ZBF210

open Finset

noncomputable def blk {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (u : Fin n × Fin n → ℂ) : ℂ :=
  (Matrix.of fun i j : m => u (ρ i, κ j)).permanent

noncomputable def pm {n : ℕ} (u : Fin n × Fin n → ℂ) : ℂ :=
  (Matrix.of fun i j => u (i, j)).permanent

theorem pm_perm {n : ℕ} (u : Fin n × Fin n → ℂ) :
    pm u = ∑ σ : Equiv.Perm (Fin n), ∏ i, u (i, σ i) := by
  unfold pm
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simp [Matrix.transpose_apply]

theorem sum_emb_eq_sum_perm {n : ℕ} (F : (Fin n → Fin n) → ℂ) :
    (∑ f : Fin n ↪ Fin n, F f) = ∑ σ : Equiv.Perm (Fin n), F σ := by
  have hb : Function.Bijective (fun σ : Equiv.Perm (Fin n) => σ.toEmbedding) :=
    ⟨fun σ τ h => Equiv.ext fun x => DFunLike.congr_fun h x,
      fun e => ⟨e.equivOfFiniteSelfEmbedding, e.toEmbedding_equivOfFiniteSelfEmbedding⟩⟩
  exact (Fintype.sum_bijective _ hb (fun σ : Equiv.Perm (Fin n) => F σ)
    (fun f : Fin n ↪ Fin n => F f) (fun σ => rfl)).symm

theorem pm_emb {n : ℕ} (u : Fin n × Fin n → ℂ) :
    pm u = ∑ f : Fin n ↪ Fin n, ∏ i, u (i, f i) := by
  rw [pm_perm, sum_emb_eq_sum_perm (fun g => ∏ i, u (i, g i))]

def Lev (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) : Prop :=
  ∀ t ∈ L, (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i))) = (Nat.factorial n : ℂ)

theorem lev_five (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) : Lev 5 L := by
  intro t ht
  rw [hL t ht]
  norm_num [Nat.factorial]

theorem poly_zero_of_ne (P : Polynomial ℂ) (h : ∀ c : ℂ, c ≠ 0 → P.eval c = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
  intro c hc
  exact h c hc

theorem lev_scale_ne {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (hc : c ≠ 0) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => c + t p) = (Nat.factorial n : ℂ) * c ^ n := by
  have h1 := hL (c⁻¹ • t) (L.smul_mem _ ht)
  have h2 : ∀ f : Fin n ↪ Fin n,
      ∏ i, (c + t (i, f i)) = c ^ n * ∏ i, (1 + (c⁻¹ • t) (i, f i)) := by
    intro f
    have h3 : c ^ n = ∏ _i : Fin n, c := by simp
    rw [h3, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [pm_emb]
  simp_rw [h2]
  rw [← Finset.mul_sum, h1]
  ring

theorem lev_scale {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => c + t p) = (Nat.factorial n : ℂ) * c ^ n := by
  have hP : ∀ a : ℂ, (∑ f : Fin n ↪ Fin n,
      ∏ i, (Polynomial.X + Polynomial.C (t (i, f i))) -
        Polynomial.C (Nat.factorial n : ℂ) * Polynomial.X ^ n).eval a =
      pm (fun p => a + t p) - (Nat.factorial n : ℂ) * a ^ n := by
    intro a
    simp only [pm_emb, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_pow]
  have hP0 := poly_zero_of_ne _ (fun a ha => by rw [hP a, lev_scale_ne hL a ha t ht, sub_self])
  have h4 := hP c
  rw [hP0, Polynomial.eval_zero] at h4
  exact sub_eq_zero.mp h4.symm

theorem lev_scale_emb {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    (∑ f : Fin n ↪ Fin n, ∏ i, (c + t (i, f i))) = (Nat.factorial n : ℂ) * c ^ n := by
  rw [← lev_scale hL c t ht, pm_emb]

theorem lev_line {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c s : ℂ) (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) :
    pm (fun p => c + t p + s * x p) = (Nat.factorial n : ℂ) * c ^ n := by
  have h := lev_scale hL c (t + s • x) (L.add_mem ht (L.smul_mem s hx))
  have e : (fun p => c + t p + s * x p) = (fun p => c + (t + s • x) p) := by
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, h]

theorem lev_line_const {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c s : ℂ) (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) :
    pm (fun p => c + t p + s * x p) = pm (fun p => c + t p) := by
  rw [lev_line hL c s t x ht hx, lev_scale hL c t ht]

theorem lev_FK {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) (h : pm (fun p => c + t p) = 0) : c = 0 := by
  rw [lev_scale hL c t ht] at h
  by_contra hc
  rcases mul_eq_zero.mp h with h1 | h1
  · exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h1
  · exact (pow_ne_zero n hc) h1

theorem perm_sum_block {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) ℂ) (h : ∀ a b, M (Sum.inr b) (Sum.inl a) = 0) :
    M.permanent =
      (M.submatrix Sum.inl Sum.inl).permanent * (M.submatrix Sum.inr Sum.inr).permanent := by
  unfold Matrix.permanent
  have hR : (∑ σ : Equiv.Perm α, ∏ i, M.submatrix Sum.inl Sum.inl (σ i) i) *
      (∑ τ : Equiv.Perm β, ∏ i, M.submatrix Sum.inr Sum.inr (τ i) i) =
      ∑ p : Equiv.Perm α × Equiv.Perm β,
        (∏ i, M (Sum.inl (p.1 i)) (Sum.inl i)) * (∏ i, M (Sum.inr (p.2 i)) (Sum.inr i)) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    rfl
  rw [hR]
  symm
  refine Fintype.sum_of_injective
    (fun p : Equiv.Perm α × Equiv.Perm β => Equiv.sumCongr p.1 p.2) ?_ _ _ ?_ ?_
  · intro p1 p2 hh
    exact Equiv.Perm.sumCongrHom_injective hh
  · intro σ hσ
    have h1 : ¬ Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
      intro hm
      obtain ⟨p, hp⟩ :=
        MonoidHom.mem_range.mp (Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm)
      exact hσ ⟨p, hp⟩
    have h2 : ∃ a, ∀ a', σ (Sum.inl a) ≠ Sum.inl a' := by
      by_contra hcon
      apply h1
      rintro _ ⟨a, rfl⟩
      by_contra hcon2
      exact hcon ⟨a, fun a' ha' => hcon2 ⟨a', ha'.symm⟩⟩
    obtain ⟨a, ha⟩ := h2
    rcases hx : σ (Sum.inl a) with a2 | b
    · exact absurd hx (ha a2)
    · exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)) (by rw [hx]; exact h a b)
  · rintro ⟨σ1, σ2⟩
    rw [Fintype.prod_sum_type]
    rfl

theorem perm_submatrix_equiv {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (r c : m ≃ n) : (M.submatrix r c).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.equivCongr c r) _ _ (fun σ => ?_)
  refine Fintype.prod_equiv c _ _ (fun i => ?_)
  simp

theorem perm_zero_block {n α β : Type} [Fintype n] [DecidableEq n] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix n n ℂ) (r c : α ⊕ β ≃ n)
    (h : ∀ a b, M (r (Sum.inr b)) (c (Sum.inl a)) = 0) :
    M.permanent =
      (M.submatrix (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a))).permanent *
        (M.submatrix (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b))).permanent := by
  rw [← perm_submatrix_equiv M r c, perm_sum_block (M.submatrix r c) (fun a b => h a b)]
  rfl

theorem perm_zero_block' {n α β : Type} [Fintype n] [DecidableEq n] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix n n ℂ) (r c : α ⊕ β ≃ n)
    (h : ∀ a b, M (r (Sum.inl a)) (c (Sum.inr b)) = 0) :
    M.permanent =
      (M.submatrix (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a))).permanent *
        (M.submatrix (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b))).permanent := by
  have h1 := perm_zero_block M.transpose c r (fun a b => h a b)
  rw [Matrix.permanent_transpose] at h1
  rw [h1]
  congr 1
  · exact Matrix.permanent_transpose
      (M.submatrix (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)))
  · exact Matrix.permanent_transpose
      (M.submatrix (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)))

theorem pm_zero_block {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (u : Fin n × Fin n → ℂ) (r c : α ⊕ β ≃ Fin n)
    (h : ∀ a b, u (r (Sum.inl a), c (Sum.inr b)) = 0) :
    pm u = blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) u *
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) u := by
  unfold pm blk
  rw [perm_zero_block' (Matrix.of fun i j => u (i, j)) r c (fun a b => h a b)]
  rfl

theorem poly_const_of_mul (P Q : Polynomial ℂ) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ s : ℂ, P.eval s * Q.eval s = k) : ∀ s : ℂ, P.eval s = P.eval 0 := by
  have hPQ : P * Q = Polynomial.C k := Polynomial.funext (fun s => by simp [h s])
  have hd : (P * Q).natDegree = 0 := by rw [hPQ]; exact Polynomial.natDegree_C k
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hPQ
    exact hk (Polynomial.C_eq_zero.mp hPQ.symm)
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hPQ
    exact hk (Polynomial.C_eq_zero.mp hPQ.symm)
  rw [Polynomial.natDegree_mul hP0 hQ0] at hd
  have hPd : P.natDegree = 0 := by omega
  have hPC := Polynomial.eq_C_of_natDegree_eq_zero hPd
  intro s
  rw [hPC, Polynomial.eval_C, Polynomial.eval_C]

def PolyLine {V : Type} [AddCommGroup V] [Module ℂ V] (f : V → ℂ) : Prop :=
  ∀ u v : V, ∃ P : Polynomial ℂ, ∀ s : ℂ, f (u + s • v) = P.eval s

theorem polyLine_comp {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (φ : V →ₗ[ℂ] W) (f : W → ℂ) (hf : PolyLine f) : PolyLine (fun v => f (φ v)) := by
  intro u v
  obtain ⟨P, hP⟩ := hf (φ u) (φ v)
  refine ⟨P, fun s => ?_⟩
  show f (φ (u + s • v)) = P.eval s
  rw [map_add, map_smul, hP s]

theorem polyLine_blk {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n) :
    PolyLine (blk ρ κ) := by
  intro u v
  refine ⟨∑ σ : Equiv.Perm m, ∏ i, (Polynomial.C (u (ρ (σ i), κ i)) +
    Polynomial.X * Polynomial.C (v (ρ (σ i), κ i))), fun s => ?_⟩
  simp only [blk, Matrix.permanent, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

theorem blk_smul {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n) (a : ℂ)
    (u : Fin n × Fin n → ℂ) : blk ρ κ (a • u) = a ^ Fintype.card m * blk ρ κ u := by
  unfold blk
  have e : (Matrix.of fun i j : m => (a • u) (ρ i, κ j)) =
      a • (Matrix.of fun i j : m => u (ρ i, κ j)) := by
    ext i j
    simp
  rw [e, Matrix.permanent_smul]

theorem line_const {V : Type} [AddCommGroup V] [Module ℂ V] (f g : V → ℂ) (hf : PolyLine f)
    (hg : PolyLine g) (u v : V) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ s : ℂ, f (u + s • v) * g (u + s • v) = k) : ∀ s : ℂ, f (u + s • v) = f u := by
  obtain ⟨P, hP⟩ := hf u v
  obtain ⟨Q, hQ⟩ := hg u v
  have h1 := poly_const_of_mul P Q k hk (fun s => by rw [← hP, ← hQ]; exact h s)
  intro s
  have h2 := hP 0
  rw [zero_smul, add_zero] at h2
  rw [hP s, h1 s, ← h2]

theorem ufd_unit_ne {V : Type} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V)
    (ell : V →ₗ[ℂ] ℂ) (f g : V → ℂ) (hf : PolyLine f) (hg : PolyLine g) (df N : ℕ)
    (hfh : ∀ (a : ℂ) (w : V), f (a • w) = a ^ df * f w) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ w ∈ U, f w * g w = k * ell w ^ N) (u0 : V) (hu0 : u0 ∈ U) (h0 : ell u0 = 1)
    (w : V) (hw : w ∈ U) (hc : ell w ≠ 0) : f w = f u0 * ell w ^ df := by
  have hv : (ell w)⁻¹ • w - u0 ∈ U := U.sub_mem (U.smul_mem _ hw) hu0
  have hline : ∀ s : ℂ, f (u0 + s • ((ell w)⁻¹ • w - u0)) * g (u0 + s • ((ell w)⁻¹ • w - u0)) =
      k := by
    intro s
    have hm : u0 + s • ((ell w)⁻¹ • w - u0) ∈ U := U.add_mem hu0 (U.smul_mem s hv)
    rw [h _ hm]
    have h5 : ell (u0 + s • ((ell w)⁻¹ • w - u0)) = 1 := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h0]
      rw [inv_mul_cancel₀ hc]
      ring
    rw [h5, one_pow, mul_one]
  have h1 := line_const f g hf hg u0 ((ell w)⁻¹ • w - u0) k hk hline 1
  rw [one_smul, add_sub_cancel, hfh] at h1
  have h6 : ell w ^ df * (ell w)⁻¹ ^ df = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  calc f w = (ell w ^ df * (ell w)⁻¹ ^ df) * f w := by rw [h6, one_mul]
    _ = ((ell w)⁻¹ ^ df * f w) * ell w ^ df := by ring
    _ = f u0 * ell w ^ df := by rw [h1]

theorem ufd_unit {V : Type} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V)
    (ell : V →ₗ[ℂ] ℂ) (f g : V → ℂ) (hf : PolyLine f) (hg : PolyLine g) (df N : ℕ)
    (hfh : ∀ (a : ℂ) (w : V), f (a • w) = a ^ df * f w) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ w ∈ U, f w * g w = k * ell w ^ N) (u0 : V) (hu0 : u0 ∈ U) (h0 : ell u0 = 1)
    (w : V) (hw : w ∈ U) : f w = f u0 * ell w ^ df := by
  by_cases hc : ell w = 0
  · obtain ⟨P, hP⟩ := hf w u0
    have hPz : P - Polynomial.C (f u0) * Polynomial.X ^ df = 0 := by
      apply poly_zero_of_ne
      intro s hs
      have hm : w + s • u0 ∈ U := U.add_mem hw (U.smul_mem s hu0)
      have hes : ell (w + s • u0) = s := by
        rw [map_add, map_smul, hc, h0, smul_eq_mul, mul_one, zero_add]
      have h2 := ufd_unit_ne U ell f g hf hg df N hfh k hk h u0 hu0 h0 (w + s • u0) hm
        (by rw [hes]; exact hs)
      rw [hes] at h2
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, ← hP s, h2, sub_self]
    have h3 := hP 0
    rw [zero_smul, add_zero] at h3
    rw [h3, hc, sub_eq_zero.mp hPz]
    simp
  · exact ufd_unit_ne U ell f g hf hg df N hfh k hk h u0 hu0 h0 w hw hc

theorem ufd_zero {V : Type} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V)
    (f g : V → ℂ) (hf : PolyLine f) (hg : PolyLine g) (h : ∀ w ∈ U, f w * g w = 0) :
    (∀ w ∈ U, f w = 0) ∨ (∀ w ∈ U, g w = 0) := by
  by_contra hcon
  have hcf : ∃ a, a ∈ U ∧ f a ≠ 0 := by
    by_contra h1
    exact hcon (Or.inl fun w hw => by
      by_contra h2
      exact h1 ⟨w, hw, h2⟩)
  have hcg : ∃ b, b ∈ U ∧ g b ≠ 0 := by
    by_contra h1
    exact hcon (Or.inr fun w hw => by
      by_contra h2
      exact h1 ⟨w, hw, h2⟩)
  obtain ⟨a, ha, hfa⟩ := hcf
  obtain ⟨b, hb, hgb⟩ := hcg
  obtain ⟨P, hP⟩ := hf a (b - a)
  obtain ⟨Q, hQ⟩ := hg a (b - a)
  have hPQ : P * Q = 0 := Polynomial.funext (fun s => by
    rw [Polynomial.eval_mul, ← hP, ← hQ, Polynomial.eval_zero]
    exact h _ (U.add_mem ha (U.smul_mem s (U.sub_mem hb ha))))
  rcases mul_eq_zero.mp hPQ with h0 | h0
  · apply hfa
    have h3 := hP 0
    rw [zero_smul, add_zero] at h3
    rw [h3, h0, Polynomial.eval_zero]
  · apply hgb
    have h3 := hQ 1
    rw [one_smul, add_sub_cancel] at h3
    rw [h3, h0, Polynomial.eval_zero]

noncomputable def hat (n : ℕ) : ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) where
  toFun w := fun p => w.1 + w.2 p
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hat_eq (n : ℕ) (w : ℂ × (Fin n × Fin n → ℂ)) : hat n w = fun p => w.1 + w.2 p := rfl

theorem hat_apply (n : ℕ) (w : ℂ × (Fin n × Fin n → ℂ)) (p : Fin n × Fin n) :
    hat n w p = w.1 + w.2 p := rfl

def blockSpace {n : ℕ} {α β : Type} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (r c : α ⊕ β ≃ Fin n) : Submodule ℂ (ℂ × (Fin n × Fin n → ℂ)) where
  carrier := {w | w.2 ∈ L ∧ ∀ a b, w.1 + w.2 (r (Sum.inl a), c (Sum.inr b)) = 0}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨L.add_mem hx1 hy1, fun a b => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    linear_combination hx2 a b + hy2 a b
  zero_mem' := ⟨L.zero_mem, fun a b => by simp⟩
  smul_mem' := by
    rintro k x ⟨hx1, hx2⟩
    refine ⟨L.smul_mem k hx1, fun a b => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    linear_combination k * hx2 a b

theorem mem_blockSpace {n : ℕ} {α β : Type} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (r c : α ⊕ β ≃ Fin n) (w : ℂ × (Fin n × Fin n → ℂ)) :
    w ∈ blockSpace L r c ↔
      w.2 ∈ L ∧ ∀ a b, w.1 + w.2 (r (Sum.inl a), c (Sum.inr b)) = 0 := Iff.rfl

theorem zbf_prod {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) *
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) =
      (Nat.factorial n : ℂ) * (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ) w) ^ n := by
  have hw' := (mem_blockSpace L r c w).mp hw
  rw [← pm_zero_block (hat n w) r c (fun a b => hw'.2 a b), hat_eq]
  exact lev_scale hL w.1 w.2 hw'.1

theorem zbf_ufd {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) =
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n u0) *
          w.1 ^ Fintype.card α ∧
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) =
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n u0) *
          w.1 ^ Fintype.card β := by
  have hk : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hpA : PolyLine (fun x : ℂ × (Fin n × Fin n → ℂ) =>
      blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n x)) :=
    polyLine_comp (hat n) _ (polyLine_blk _ _)
  have hpB : PolyLine (fun x : ℂ × (Fin n × Fin n → ℂ) =>
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x)) :=
    polyLine_comp (hat n) _ (polyLine_blk _ _)
  constructor
  · exact ufd_unit (blockSpace L r c) (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))
      (fun x => blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n x))
      (fun x => blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x))
      hpA hpB (Fintype.card α) n
      (fun a x => by rw [map_smul]; exact blk_smul _ _ a _)
      (Nat.factorial n : ℂ) hk (fun x hx => zbf_prod hL r c x hx) u0 hu0 h0 w hw
  · exact ufd_unit (blockSpace L r c) (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))
      (fun x => blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x))
      (fun x => blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n x))
      hpB hpA (Fintype.card β) n
      (fun a x => by rw [map_smul]; exact blk_smul _ _ a _)
      (Nat.factorial n : ℂ) hk
      (fun x hx => by rw [mul_comm]; exact zbf_prod hL r c x hx) u0 hu0 h0 w hw

theorem zbf_zero {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (r c : α ⊕ β ≃ Fin n) (hU : ∀ w ∈ blockSpace L r c, w.1 = 0) :
    (∀ w ∈ blockSpace L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) = 0) ∨
      (∀ w ∈ blockSpace L r c,
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0) := by
  refine ufd_zero (blockSpace L r c)
    (fun x => blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n x))
    (fun x => blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x))
    (polyLine_comp (hat n) _ (polyLine_blk _ _)) (polyLine_comp (hat n) _ (polyLine_blk _ _))
    (fun x hx => ?_)
  have h1 := zbf_prod hL r c x hx
  rw [LinearMap.fst_apply, hU x hx, zero_pow hn, mul_zero] at h1
  exact h1

theorem rank_nullity {V W : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [AddCommGroup W] [Module ℂ W] (L : Submodule ℂ V) (f : V →ₗ[ℂ] W) :
    Module.finrank ℂ L = Module.finrank ℂ (L ⊓ LinearMap.ker f : Submodule ℂ V) +
      Module.finrank ℂ (L.map f) := by
  have hrn : Module.finrank ℂ (L.map f) +
      Module.finrank ℂ (L ⊓ LinearMap.ker f : Submodule ℂ V) = Module.finrank ℂ L := by
    rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
      ← (f.submoduleMap L).finrank_range_add_finrank_ker,
      LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]
    simp
  omega

def rowMap {n : ℕ} (r : Fin n) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun t := fun j => t (r, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rowMap_apply {n : ℕ} (r : Fin n) (t : Fin n × Fin n → ℂ) (j : Fin n) :
    rowMap r t j = t (r, j) := rfl

def rowsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    Submodule ℂ (Fin n × Fin n → ℂ) :=
  L ⊓ LinearMap.ker (rowMap r1) ⊓ LinearMap.ker (rowMap r2)

theorem mem_rowsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n)
    (t : Fin n × Fin n → ℂ) :
    t ∈ rowsZero L r1 r2 ↔ t ∈ L ∧ (∀ j, t (r1, j) = 0) ∧ ∀ j, t (r2, j) = 0 := by
  unfold rowsZero
  rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun j => congrFun h2 j, fun j => congrFun h3 j⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, funext h2, funext h3⟩

theorem rowsZero_comm {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    rowsZero L r1 r2 = rowsZero L r2 r1 := by
  unfold rowsZero
  exact inf_right_comm _ _ _

theorem pm_zero_row {n : ℕ} (u : Fin n × Fin n → ℂ) (r : Fin n) (h : ∀ j, u (r, j) = 0) :
    pm u = 0 := by
  rw [pm_perm]
  exact Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero (Finset.mem_univ r) (h (σ r))

theorem lev_FK_row {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) (r : Fin n) (h : ∀ j, c + t (r, j) = 0) :
    c = 0 :=
  lev_FK hL c t ht (pm_zero_row _ r h)

def q0 (z : Fin 2 × Fin 2 → ℂ) : ℂ := z (0, 0) * z (1, 1) + z (0, 1) * z (1, 0)

theorem permanent_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A.permanent = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
  have hu : (univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  unfold Matrix.permanent
  rw [hu, sum_insert (by decide), sum_singleton]
  simp only [Fin.prod_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.Perm.one_apply]
  ring

noncomputable def blockProj {n : ℕ} {β : Type} (r c : Fin 2 ⊕ β ≃ Fin n) :
    ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin 2 × Fin 2 → ℂ) where
  toFun w := fun p => w.1 + w.2 (r (Sum.inl p.1), c (Sum.inl p.2))
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem blockProj_apply {n : ℕ} {β : Type} (r c : Fin 2 ⊕ β ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) (a a' : Fin 2) :
    blockProj r c w (a, a') = w.1 + w.2 (r (Sum.inl a), c (Sum.inl a')) := rfl

theorem blk_two {n : ℕ} {β : Type} (r c : Fin 2 ⊕ β ≃ Fin n) (w : ℂ × (Fin n × Fin n → ℂ)) :
    blk (fun a : Fin 2 => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) =
      q0 (blockProj r c w) := by
  unfold blk
  rw [permanent_two]
  rfl

noncomputable def bDual : (Fin 2 × Fin 2 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 2 × Fin 2 → ℂ) :=
  LinearMap.mk₂ ℂ (fun v z => v (0, 0) * z (1, 1) + v (1, 1) * z (0, 0) + v (0, 1) * z (1, 0) +
      v (1, 0) * z (0, 1))
    (fun a b z => by simp only [Pi.add_apply]; ring)
    (fun k a z => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun v a b => by simp only [Pi.add_apply]; ring)
    (fun k v a => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem bDual_apply (v z : Fin 2 × Fin 2 → ℂ) :
    bDual v z = v (0, 0) * z (1, 1) + v (1, 1) * z (0, 0) + v (0, 1) * z (1, 0) +
      v (1, 0) * z (0, 1) := rfl

theorem q0_polar (z z' : Fin 2 × Fin 2 → ℂ) : q0 (z + z') - q0 z - q0 z' = bDual z z' := by
  rw [bDual_apply]
  unfold q0
  simp only [Pi.add_apply]
  ring

theorem bDual_injective : Function.Injective bDual := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h00 := LinearMap.congr_fun hv (Pi.single (1, 1) 1)
  have h11 := LinearMap.congr_fun hv (Pi.single (0, 0) 1)
  have h01 := LinearMap.congr_fun hv (Pi.single (1, 0) 1)
  have h10 := LinearMap.congr_fun hv (Pi.single (0, 1) 1)
  rw [bDual_apply] at h00 h11 h01 h10
  simp [Pi.single_apply] at h00 h11 h01 h10
  have hall : ∀ i j : Fin 2, v (i, j) = 0 := by
    rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      exact ⟨h00, h01⟩
    · rw [Fin.forall_fin_two]
      exact ⟨h10, h11⟩
  funext p
  exact hall p.1 p.2

theorem b_perp_bound (K P : Submodule ℂ (Fin 2 × Fin 2 → ℂ))
    (h : ∀ v ∈ K, ∀ z ∈ P, bDual v z = 0) :
    Module.finrank ℂ K + Module.finrank ℂ P ≤ 4 := by
  have hle : K.map bDual ≤ P.dualAnnihilator := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h v hv z hz
  have e1 : Module.finrank ℂ (K.map bDual) = Module.finrank ℂ K :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ bDual_injective K)).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq P
  have e3 := Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card] at e2
  simp only [Fintype.card_prod, Fintype.card_fin] at e2
  omega

theorem finrank_span_one_le {V : Type} [AddCommGroup V] [Module ℂ V] (v : V) :
    Module.finrank ℂ (Submodule.span ℂ {v}) ≤ 1 := by
  by_cases hv : v = 0
  · rw [hv, Submodule.span_zero_singleton, finrank_bot]
    omega
  · rw [finrank_span_singleton hv]

theorem thB_quad {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    q0 (blockProj r c u0) ≠ 0 ∧
      ∀ w ∈ blockSpace L r c, q0 (blockProj r c w) = q0 (blockProj r c u0) * w.1 ^ 2 := by
  constructor
  · intro hz
    have h1 := zbf_prod hL r c u0 hu0
    rw [blk_two, hz, zero_mul, LinearMap.fst_apply, h0, one_pow, mul_one] at h1
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h1.symm
  · intro w hw
    have h1 := (zbf_ufd hL r c u0 hu0 h0 w hw).1
    rw [blk_two, blk_two] at h1
    simpa using h1

theorem thB_ker {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c) (hk : blockProj r c w = 0) :
    w.1 = 0 ∧ w.2 ∈ rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1)) := by
  obtain ⟨hκ, hq⟩ := thB_quad hL r c u0 hu0 h0
  have h1 := hq w hw
  rw [hk] at h1
  have hq00 : q0 (0 : Fin 2 × Fin 2 → ℂ) = 0 := by simp [q0]
  rw [hq00] at h1
  have hw1 : w.1 = 0 := by
    by_contra hne
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · exact hκ h2
    · exact (pow_ne_zero 2 hne) h2
  refine ⟨hw1, ?_⟩
  have hw' := (mem_blockSpace L r c w).mp hw
  rw [mem_rowsZero]
  refine ⟨hw'.1, fun j => ?_, fun j => ?_⟩
  · obtain ⟨x, rfl⟩ := c.surjective j
    rcases x with a | b
    · have h3 : w.1 + w.2 (r (Sum.inl 0), c (Sum.inl a)) = 0 := congrFun hk (0, a)
      rw [hw1, zero_add] at h3
      exact h3
    · have h3 := hw'.2 0 b
      rw [hw1, zero_add] at h3
      exact h3
  · obtain ⟨x, rfl⟩ := c.surjective j
    rcases x with a | b
    · have h3 : w.1 + w.2 (r (Sum.inl 1), c (Sum.inl a)) = 0 := congrFun hk (1, a)
      rw [hw1, zero_add] at h3
      exact h3
    · have h3 := hw'.2 1 b
      rw [hw1, zero_add] at h3
      exact h3

theorem thB_img {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ ((blockSpace L r c).map (blockProj r c)) ≤ 2 := by
  obtain ⟨hκ, hq⟩ := thB_quad hL r c u0 hu0 h0
  have hperp : ∀ v ∈ (blockSpace L r c ⊓
        LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))).map (blockProj r c),
      ∀ z ∈ (blockSpace L r c).map (blockProj r c), bDual v z = 0 := by
    rintro _ ⟨w, ⟨hwU, hwk⟩, rfl⟩ _ ⟨w', hw'U, rfl⟩
    have hw1 : w.1 = 0 := LinearMap.mem_ker.mp hwk
    rw [← q0_polar, ← map_add, hq w hwU, hq w' hw'U,
      hq (w + w') ((blockSpace L r c).add_mem hwU hw'U), Prod.fst_add, hw1]
    ring
  have h1 := b_perp_bound _ _ hperp
  have hsup : (blockSpace L r c).map (blockProj r c) ≤
      (blockSpace L r c ⊓
        LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))).map (blockProj r c) ⊔
        Submodule.span ℂ {blockProj r c u0} := by
    rintro _ ⟨w, hwU, rfl⟩
    have hd : blockProj r c w = blockProj r c (w - w.1 • u0) + w.1 • blockProj r c u0 := by
      rw [← map_smul, ← map_add, sub_add_cancel]
    rw [hd]
    refine Submodule.add_mem_sup (Submodule.mem_map_of_mem ⟨(blockSpace L r c).sub_mem hwU
      ((blockSpace L r c).smul_mem _ hu0), ?_⟩)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    show (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ)) (w - w.1 • u0) = 0
    rw [map_sub, map_smul, LinearMap.fst_apply, LinearMap.fst_apply, h0,
      smul_eq_mul, mul_one, sub_self]
  have h2 := Submodule.finrank_mono hsup
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    ((blockSpace L r c ⊓
      LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))).map (blockProj r c))
    (Submodule.span ℂ {blockProj r c u0})
  have h4 := finrank_span_one_le (blockProj r c u0)
  omega

theorem thB_dim {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ (blockSpace L r c) ≤
      2 + Module.finrank ℂ (rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1))) := by
  have hrn := rank_nullity (blockSpace L r c) (blockProj r c)
  have himg := thB_img hL r c u0 hu0 h0
  have hrn2 := rank_nullity (blockSpace L r c ⊓ LinearMap.ker (blockProj r c))
    (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ))
  have hbot : (blockSpace L r c ⊓ LinearMap.ker (blockProj r c)) ⊓
      LinearMap.ker (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ)) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨hwU, hwk⟩, hws⟩
    have hw1 := (thB_ker hL r c u0 hu0 h0 w hwU (LinearMap.mem_ker.mp hwk)).1
    have hw2 : w.2 = 0 := LinearMap.mem_ker.mp hws
    rw [Submodule.mem_bot]
    exact Prod.ext hw1 hw2
  have hle : (blockSpace L r c ⊓ LinearMap.ker (blockProj r c)).map
      (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ)) ≤ rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1)) := by
    rintro _ ⟨w, ⟨hwU, hwk⟩, rfl⟩
    exact (thB_ker hL r c u0 hu0 h0 w hwU (LinearMap.mem_ker.mp hwk)).2
  have h5 := Submodule.finrank_mono hle
  rw [hbot, finrank_bot, zero_add] at hrn2
  omega

noncomputable def zeroMap {n : ℕ} {α β : Type} (r c : α ⊕ β ≃ Fin n) :
    ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (α × β → ℂ) where
  toFun w := fun p => w.1 + w.2 (r (Sum.inl p.1), c (Sum.inr p.2))
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem blockSpace_finrank_ge {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r c : α ⊕ β ≃ Fin n) :
    Module.finrank ℂ L + 1 ≤
      Module.finrank ℂ (blockSpace L r c) + Fintype.card α * Fintype.card β := by
  have hφ : Function.Injective
      (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype) := by
    intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    exact Prod.ext h1 (Subtype.ext h2)
  have h1 := rank_nullity
    (LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)) (zeroMap r c)
  have h2 : Module.finrank ℂ
      (LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)) =
      Module.finrank ℂ L + 1 := by
    rw [LinearMap.finrank_range_of_inj hφ, Module.finrank_prod, Module.finrank_self]
    omega
  have h3 : Module.finrank ℂ
      ((LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)).map
        (zeroMap r c)) ≤ Fintype.card α * Fintype.card β := by
    have h6 := Submodule.finrank_le
      ((LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)).map
        (zeroMap r c))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] at h6
    exact h6
  have h4 : LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype) ⊓
      LinearMap.ker (zeroMap r c) ≤ blockSpace L r c := by
    rintro w ⟨⟨x, rfl⟩, hk⟩
    rw [mem_blockSpace]
    refine ⟨x.2.2, fun a b => ?_⟩
    exact congrFun (LinearMap.mem_ker.mp hk) (a, b)
  have h5 := Submodule.finrank_mono h4
  omega

theorem one_not_mem_row {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (A : Submodule ℂ (Fin n × Fin n → ℂ)) (hA : A ≤ L) (r : Fin n) :
    (1 : Fin n → ℂ) ∉ A.map (rowMap r) := by
  rintro ⟨t, ht, h1⟩
  have h2 := lev_FK_row hL (-1) t (hA ht) r (fun j => by
    have h3 := congrFun h1 j
    rw [rowMap_apply, Pi.one_apply] at h3
    rw [h3]
    ring)
  norm_num at h2

theorem finrank_sup_one {m : ℕ} (W : Submodule ℂ (Fin (m + 2) → ℂ))
    (h1 : (1 : Fin (m + 2) → ℂ) ∉ W) :
    Module.finrank ℂ (W ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} :
      Submodule ℂ (Fin (m + 2) → ℂ)) = Module.finrank ℂ W + 1 := by
  have hne : (1 : Fin (m + 2) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  have hinf : W ⊓ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxW, hx1⟩
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hx1
    rw [Submodule.mem_bot]
    by_contra hk
    have hk' : k ≠ 0 := by
      rintro rfl
      exact hk (zero_smul _ _)
    apply h1
    have h2 := W.smul_mem k⁻¹ hxW
    rwa [smul_smul, inv_mul_cancel₀ hk', one_smul] at h2
  have h := Submodule.finrank_sup_add_finrank_inf_eq W
    (Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hne] at h
  exact h

theorem row_surj {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L)
    (v : Fin (m + 2) → ℂ) :
    ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧ ∃ γ : ℂ, ∀ j, v j = a (r1, j) + γ := by
  have h5 : Module.finrank ℂ (Fin (m + 2) → ℂ) = m + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hW2 : Module.finrank ℂ (L.map (rowMap r2)) ≤ m + 1 := by
    have h1 := finrank_sup_one _ (one_not_mem_row hL L le_rfl r2)
    have h2 := Submodule.finrank_le
      (L.map (rowMap r2) ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)})
    rw [h5] at h2
    omega
  have hA := rank_nullity L (rowMap r2)
  have hA2 := rank_nullity (L ⊓ LinearMap.ker (rowMap r2)) (rowMap r1)
  have hX : (L ⊓ LinearMap.ker (rowMap r2)) ⊓ LinearMap.ker (rowMap r1) = rowsZero L r1 r2 := by
    unfold rowsZero
    exact inf_right_comm _ _ _
  rw [hX] at hA2
  have h1 := finrank_sup_one _
    (one_not_mem_row hL (L ⊓ LinearMap.ker (rowMap r2)) inf_le_left r1)
  have h2 := Submodule.finrank_le ((L ⊓ LinearMap.ker (rowMap r2)).map (rowMap r1) ⊔
    Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)})
  rw [h5] at h2
  have htop : (L ⊓ LinearMap.ker (rowMap r2)).map (rowMap r1) ⊔
      Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h5]
    omega
  have hv : v ∈ (L ⊓ LinearMap.ker (rowMap r2)).map (rowMap r1) ⊔
      Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have ha' := Submodule.mem_inf.mp ha
  refine ⟨a, ha'.1, fun j => congrFun (LinearMap.mem_ker.mp ha'.2) j, γ, fun j => ?_⟩
  rw [← hyz]
  simp [rowMap_apply]

theorem exists_col {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L) :
    ∃ k : Fin (m + 2), ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧ ∀ j, j ≠ k → 1 + a (r1, j) = 0 := by
  by_contra hcon
  have hall : ∀ k : Fin (m + 2), ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧
      ∀ j, (Pi.single k 1 : Fin (m + 2) → ℂ) j = a (r1, j) := by
    intro k
    obtain ⟨a, haL, ha2, γ, hγ⟩ := row_surj hL r1 r2 hd (Pi.single k 1)
    by_cases hg : γ = 0
    · exact ⟨a, haL, ha2, fun j => by rw [hγ j, hg, add_zero]⟩
    · exfalso
      apply hcon
      refine ⟨k, γ⁻¹ • a, L.smul_mem _ haL, fun j => by simp [ha2 j], fun j hj => ?_⟩
      have h1 := hγ j
      rw [Pi.single_apply, if_neg hj] at h1
      have h3 : a (r1, j) = -γ := by linear_combination -h1
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h3, mul_neg, inv_mul_cancel₀ hg]
      ring
  choose a haL ha2 ha1 using hall
  have h2 := lev_FK_row hL (-1) (∑ k, a k) (L.sum_mem fun k _ => haL k) r1 (fun j => by
    rw [Finset.sum_apply]
    have h4 : ∑ k, a k (r1, j) = ∑ k, (Pi.single k 1 : Fin (m + 2) → ℂ) j :=
      Finset.sum_congr rfl fun k _ => (ha1 k j).symm
    rw [h4]
    simp [Pi.single_apply])
  norm_num at h2

theorem exists_perm2 {m : ℕ} (r1 r2 : Fin (m + 2)) (h : r1 ≠ r2) :
    ∃ ρ : Equiv.Perm (Fin (m + 2)), ρ 0 = r1 ∧ ρ 1 = r2 := by
  refine ⟨(Equiv.swap 0 r1).trans (Equiv.swap (Equiv.swap 0 r1 1) r2), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ h
    intro h1
    have h2 : Equiv.swap (0 : Fin (m + 2)) r1 0 = Equiv.swap 0 r1 1 := by
      rw [Equiv.swap_apply_left]
      exact h1
    exact absurd ((Equiv.swap (0 : Fin (m + 2)) r1).injective h2) Fin.zero_ne_one
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem exists_col_perm {m : ℕ} (k1 k2 : Fin (m + 2)) :
    ∃ κ : Equiv.Perm (Fin (m + 2)), ∀ x : Fin (m + 2), κ x = k1 ∨ κ x = k2 → x = 0 ∨ x = 1 := by
  by_cases h : k1 = k2
  · obtain ⟨k', hk'⟩ := exists_ne k1
    obtain ⟨κ, h0, h1⟩ := exists_perm2 k1 k' hk'.symm
    refine ⟨κ, fun x hx => Or.inl ?_⟩
    apply κ.injective
    rcases hx with hx | hx
    · rw [hx, h0]
    · rw [hx, h0, h]
  · obtain ⟨κ, h0, h1⟩ := exists_perm2 k1 k2 h
    refine ⟨κ, fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact Or.inl (κ.injective (by rw [hx, h0]))
    · exact Or.inr (κ.injective (by rw [hx, h1]))

def e2m (m : ℕ) : Fin 2 ⊕ Fin m ≃ Fin (m + 2) :=
  finSumFinEquiv.trans (finCongr (add_comm 2 m))

theorem e2m_inl_val (m : ℕ) (a : Fin 2) : ((e2m m (Sum.inl a) : Fin (m + 2)) : ℕ) = a := by
  simp [e2m]

theorem e2m_inr_val (m : ℕ) (b : Fin m) : ((e2m m (Sum.inr b) : Fin (m + 2)) : ℕ) = 2 + b := by
  simp [e2m]
  omega

theorem e2m_inl0 (m : ℕ) : e2m m (Sum.inl 0) = 0 := by
  apply Fin.ext
  rw [e2m_inl_val]
  simp

theorem e2m_inl1 (m : ℕ) : e2m m (Sum.inl 1) = 1 := by
  apply Fin.ext
  rw [e2m_inl_val]
  simp

theorem e2m_inr (m : ℕ) (b : Fin m) : ¬ (e2m m (Sum.inr b) = 0 ∨ e2m m (Sum.inr b) = 1) := by
  intro h
  rcases h with h | h
  · have h1 := congrArg Fin.val h
    rw [e2m_inr_val] at h1
    simp at h1
  · have h1 := congrArg Fin.val h
    rw [e2m_inr_val] at h1
    simp at h1
    omega

theorem lemmaC_gen {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r1 r2 : Fin (m + 2)) (hr : r1 ≠ r2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 1) := by
  by_contra hcon
  have hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L := by omega
  have hd' : Module.finrank ℂ (rowsZero L r2 r1) + (2 * m + 2) ≤ Module.finrank ℂ L := by
    rw [rowsZero_comm]
    exact hd
  obtain ⟨k1, a, haL, ha2, ha1⟩ := exists_col hL r1 r2 hd
  obtain ⟨k2, b, hbL, hb1, hb2⟩ := exists_col hL r2 r1 hd'
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_perm2 r1 r2 hr
  obtain ⟨κ, hκ⟩ := exists_col_perm k1 k2
  have hr0 : ((e2m m).trans ρ) (Sum.inl 0) = r1 := by
    rw [Equiv.trans_apply, e2m_inl0, hρ0]
  have hr1 : ((e2m m).trans ρ) (Sum.inl 1) = r2 := by
    rw [Equiv.trans_apply, e2m_inl1, hρ1]
  have hu0 : ((1 : ℂ), a + b) ∈ blockSpace L ((e2m m).trans ρ) ((e2m m).trans κ) := by
    rw [mem_blockSpace]
    refine ⟨L.add_mem haL hbL, fun a' b' => ?_⟩
    have hc1 : ((e2m m).trans κ) (Sum.inr b') ≠ k1 := by
      intro h1
      exact e2m_inr m b' (hκ (e2m m (Sum.inr b')) (Or.inl h1))
    have hc2 : ((e2m m).trans κ) (Sum.inr b') ≠ k2 := by
      intro h1
      exact e2m_inr m b' (hκ (e2m m (Sum.inr b')) (Or.inr h1))
    have hboth : ∀ a'' : Fin 2, (1 : ℂ) +
        (a + b) (((e2m m).trans ρ) (Sum.inl a''), ((e2m m).trans κ) (Sum.inr b')) = 0 := by
      rw [Fin.forall_fin_two]
      constructor
      · rw [hr0, Pi.add_apply, hb1, add_zero]
        exact ha1 _ hc1
      · rw [hr1, Pi.add_apply, ha2, zero_add]
        exact hb2 _ hc2
    exact hboth a'
  have hB := thB_dim hL ((e2m m).trans ρ) ((e2m m).trans κ) (1, a + b) hu0 rfl
  rw [hr0, hr1] at hB
  have hlow := blockSpace_finrank_ge L ((e2m m).trans ρ) ((e2m m).trans κ)
  simp only [Fintype.card_fin] at hlow
  omega

theorem lemmaC {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r1 r2 : Fin 5)
    (hr : r1 ≠ r2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) + 7 :=
  lemmaC_gen (m := 3) hL r1 r2 hr

theorem pm_tr {n : ℕ} (u : Fin n × Fin n → ℂ) : pm (fun p => u (p.2, p.1)) = pm u := by
  unfold pm
  rw [← Matrix.permanent_transpose]
  rfl

noncomputable def trE (n : ℕ) : (Fin n × Fin n → ℂ) ≃ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodComm (Fin n) (Fin n))

theorem trE_apply (n : ℕ) (t : Fin n × Fin n → ℂ) (i j : Fin n) : trE n t (i, j) = t (j, i) :=
  rfl

theorem lev_tr {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    Lev n (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))) := by
  rintro _ ⟨t, ht, rfl⟩
  have h1 : pm (fun p => 1 + t (p.2, p.1)) = pm (fun p => 1 + t p) := pm_tr (fun p => 1 + t p)
  have h2 := pm_emb (fun p => 1 + t (p.2, p.1))
  have h3 := pm_emb (fun p => 1 + t p)
  simp only at h2 h3
  have h4 := hL t ht
  rw [← h3, ← h1, h2] at h4
  exact h4

def colMap {n : ℕ} (c : Fin n) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun t := fun i => t (i, c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem colMap_apply {n : ℕ} (c : Fin n) (t : Fin n × Fin n → ℂ) (i : Fin n) :
    colMap c t i = t (i, c) := rfl

def colsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c1 c2 : Fin n) :
    Submodule ℂ (Fin n × Fin n → ℂ) :=
  L ⊓ LinearMap.ker (colMap c1) ⊓ LinearMap.ker (colMap c2)

theorem mem_colsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c1 c2 : Fin n)
    (t : Fin n × Fin n → ℂ) :
    t ∈ colsZero L c1 c2 ↔ t ∈ L ∧ (∀ i, t (i, c1) = 0) ∧ ∀ i, t (i, c2) = 0 := by
  unfold colsZero
  rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun j => congrFun h2 j, fun j => congrFun h3 j⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, funext h2, funext h3⟩

theorem lemmaC_col_gen {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (c1 c2 : Fin (m + 2)) (hc : c1 ≠ c2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (colsZero L c1 c2) + (2 * m + 1) := by
  have h1 := lemmaC_gen (lev_tr hL) c1 c2 hc
  have h2 := LinearEquiv.finrank_map_eq (trE (m + 2)) L
  have h3 := LinearEquiv.finrank_map_eq (trE (m + 2)) (colsZero L c1 c2)
  have h4 : rowsZero (L.map (trE (m + 2) :
      (Fin (m + 2) × Fin (m + 2) → ℂ) →ₗ[ℂ] (Fin (m + 2) × Fin (m + 2) → ℂ))) c1 c2 ≤
      (colsZero L c1 c2).map (trE (m + 2) :
        (Fin (m + 2) × Fin (m + 2) → ℂ) →ₗ[ℂ] (Fin (m + 2) × Fin (m + 2) → ℂ)) := by
    intro t' ht'
    obtain ⟨⟨t, ht, rfl⟩, hz1, hz2⟩ := (mem_rowsZero _ c1 c2 t').mp ht'
    refine Submodule.mem_map_of_mem ((mem_colsZero L c1 c2 t).mpr ⟨ht, fun i => ?_, fun i => ?_⟩)
    · exact hz1 i
    · exact hz2 i
  have h5 := Submodule.finrank_mono h4
  omega

theorem lemmaC_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c1 c2 : Fin 5)
    (hc : c1 ≠ c2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (colsZero L c1 c2) + 7 :=
  lemmaC_col_gen (m := 3) hL c1 c2 hc

theorem lemmaC_nine {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) :
    (∀ r1 r2 : Fin 5, r1 ≠ r2 → 2 ≤ Module.finrank ℂ (rowsZero L r1 r2)) ∧
      ∀ c1 c2 : Fin 5, c1 ≠ c2 → 2 ≤ Module.finrank ℂ (colsZero L c1 c2) := by
  constructor
  · intro r1 r2 hr
    have h := lemmaC hL r1 r2 hr
    omega
  · intro c1 c2 hc
    have h := lemmaC_col hL c1 c2 hc
    omega

theorem thB_cases {n : ℕ} (hn : n ≠ 0) {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n) :
    (∃ u0 ∈ blockSpace L r c, u0.1 = 1) ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧
        ((∀ w ∈ blockSpace L r c, q0 (blockProj r c w) = 0) ∨
          ∀ w ∈ blockSpace L r c,
            blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0)) := by
  by_cases h : ∀ w ∈ blockSpace L r c, w.1 = 0
  · right
    refine ⟨h, ?_⟩
    rcases zbf_zero hn hL r c h with h1 | h1
    · left
      intro w hw
      rw [← blk_two]
      exact h1 w hw
    · right
      exact h1
  · left
    have h' : ∃ w, w ∈ blockSpace L r c ∧ w.1 ≠ 0 := by
      by_contra hcon
      apply h
      intro w hw
      by_contra hw1
      exact hcon ⟨w, hw, hw1⟩
    obtain ⟨w, hw, hw1⟩ := h'
    refine ⟨w.1⁻¹ • w, (blockSpace L r c).smul_mem _ hw, ?_⟩
    rw [Prod.smul_fst, smul_eq_mul, inv_mul_cancel₀ hw1]

def sa {k : ℕ} (e : Fin (k + 1)) : Fin k ⊕ Unit ≃ Fin (k + 1) :=
  (Equiv.optionEquivSumPUnit (Fin k)).symm.trans (finSuccEquiv' e).symm

theorem sa_inl {k : ℕ} (e : Fin (k + 1)) (b : Fin k) : sa e (Sum.inl b) = e.succAbove b :=
  finSuccEquiv'_symm_some e b

theorem sa_inr {k : ℕ} (e : Fin (k + 1)) (x : Unit) : sa e (Sum.inr x) = e :=
  finSuccEquiv'_symm_none e

def rowRepl {n : ℕ} (u : Fin n × Fin n → ℂ) (e : Fin n) (v : Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => if p.1 = e then v p.2 else u p

theorem pm_rowRepl {n : ℕ} (u : Fin n × Fin n → ℂ) (e : Fin n) (v : Fin n → ℂ) :
    pm (rowRepl u e v) =
      ∑ σ : Equiv.Perm (Fin n), v (σ e) * ∏ i ∈ univ.erase e, u (i, σ i) := by
  rw [pm_perm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ e)]
  congr 1
  · simp [rowRepl]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [rowRepl, (Finset.mem_erase.mp hi).1]

theorem pm_row_expand {n : ℕ} (u : Fin n × Fin n → ℂ) (e : Fin n) :
    pm u = ∑ j, u (e, j) * pm (rowRepl u e (Pi.single j 1)) := by
  have h1 : pm u = pm (rowRepl u e (fun j => u (e, j))) := by
    congr 1
    funext p
    unfold rowRepl
    split_ifs with h
    · rw [← h]
    · rfl
  rw [h1, pm_rowRepl]
  simp_rw [pm_rowRepl, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single (σ e)]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pm_laplace_row {k : ℕ} (u : Fin (k + 1) × Fin (k + 1) → ℂ) (e : Fin (k + 1)) :
    pm u = ∑ j, u (e, j) * blk e.succAbove j.succAbove u := by
  rw [pm_row_expand u e]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hz : ∀ (a : Fin k) (b : Unit),
      (Matrix.of fun i j' => rowRepl u e (Pi.single j 1) (i, j')) (sa e (Sum.inr b))
        (sa j (Sum.inl a)) = 0 := by
    intro a b
    rw [sa_inr, sa_inl]
    simp [rowRepl, Pi.single_apply, Fin.succAbove_ne]
  have h2 := perm_zero_block (Matrix.of fun i j' => rowRepl u e (Pi.single j 1) (i, j'))
    (sa e) (sa j) hz
  have h3 : ((Matrix.of fun i j' => rowRepl u e (Pi.single j 1) (i, j')).submatrix
      (fun b : Unit => sa e (Sum.inr b)) (fun b : Unit => sa j (Sum.inr b))).permanent = 1 := by
    rw [Matrix.permanent_unique]
    simp [sa_inr, rowRepl]
  have h4 : ((Matrix.of fun i j' => rowRepl u e (Pi.single j 1) (i, j')).submatrix
      (fun a : Fin k => sa e (Sum.inl a)) (fun a : Fin k => sa j (Sum.inl a))).permanent =
      blk e.succAbove j.succAbove u := by
    unfold blk
    congr 1
    ext a a'
    simp [sa_inl, rowRepl, Fin.succAbove_ne]
  unfold pm
  rw [h2, h3, h4, mul_one]

theorem pm_laplace_two {k : ℕ} (u : Fin (k + 2) × Fin (k + 2) → ℂ) (r : Fin (k + 2))
    (p : Fin (k + 1)) :
    pm u = ∑ j, ∑ q, u (r, j) * u (r.succAbove p, j.succAbove q) *
      blk (fun a => r.succAbove (p.succAbove a)) (fun b => j.succAbove (q.succAbove b)) u := by
  rw [pm_laplace_row u r]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : blk r.succAbove j.succAbove u =
      pm (fun z : Fin (k + 1) × Fin (k + 1) => u (r.succAbove z.1, j.succAbove z.2)) := rfl
  rw [h1, pm_laplace_row _ p, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_assoc]
  rfl

theorem poly_top {Q : Polynomial ℂ} (A : ℂ) (d e : ℕ) (he : e ≠ 0)
    (h : ∀ τ : ℂ, τ ^ d * Q.eval τ = A * τ ^ (d + e)) : Q.eval 0 = 0 := by
  have hQ : Q - Polynomial.C A * Polynomial.X ^ e = 0 := by
    apply poly_zero_of_ne
    intro τ hτ
    have h2 : τ ^ d * Q.eval τ = τ ^ d * (A * τ ^ e) := by
      rw [h τ, pow_add]
      ring
    have h3 := mul_left_cancel₀ (pow_ne_zero d hτ) h2
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, h3, sub_self]
  have h0 := sub_eq_zero.mp hQ
  rw [h0, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow he, mul_zero]

theorem ca2 {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hL : Lev (k + 1) L) (e : Fin (k + 1)) (ξ : Fin (k + 1) × Fin (k + 1) → ℂ) (hξ : ξ ∈ L)
    (hξe : ∀ j, ξ (e, j) = 0) (c : ℂ) (t : Fin (k + 1) × Fin (k + 1) → ℂ) (ht : t ∈ L) :
    ∑ j, (c + t (e, j)) * blk e.succAbove j.succAbove ξ = 0 := by
  choose P hP using fun j : Fin (k + 1) =>
    polyLine_blk (n := k + 1) e.succAbove j.succAbove ξ (fun p => c + t p)
  have hlev : ∀ τ : ℂ, pm (ξ + τ • fun p => c + t p) =
      (Nat.factorial (k + 1) : ℂ) * (τ * c) ^ (k + 1) := by
    intro τ
    have h1 := lev_scale hL (τ * c) (τ • t + ξ) (L.add_mem (L.smul_mem τ ht) hξ)
    have e1 : (ξ + τ • fun p => c + t p) = fun p => τ * c + (τ • t + ξ) p := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, h1]
  have hkey : ∀ τ : ℂ, τ ^ 1 * (∑ j, Polynomial.C (c + t (e, j)) * P j).eval τ =
      ((Nat.factorial (k + 1) : ℂ) * c ^ (k + 1)) * τ ^ (1 + k) := by
    intro τ
    have h2 : (Nat.factorial (k + 1) : ℂ) * c ^ (k + 1) * τ ^ (1 + k) =
        (Nat.factorial (k + 1) : ℂ) * (τ * c) ^ (k + 1) := by ring
    rw [h2, ← hlev τ, pm_laplace_row _ e, Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← hP j τ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hξe j, zero_add, pow_one]
    ring
  have h0 := poly_top _ 1 k hk hkey
  rw [Polynomial.eval_finsetSum] at h0
  refine Eq.trans ?_ h0
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← hP j 0, zero_smul, add_zero]

theorem ca2_full {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (e : Fin (m + 2))
    (hrank : m + 1 ≤ Module.finrank ℂ (L.map (rowMap e)))
    (ξ : Fin (m + 2) × Fin (m + 2) → ℂ) (hξ : ξ ∈ L) (hξe : ∀ j, ξ (e, j) = 0)
    (j : Fin (m + 2)) : blk e.succAbove j.succAbove ξ = 0 := by
  have h5 : Module.finrank ℂ (Fin (m + 2) → ℂ) = m + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h1 := finrank_sup_one _ (one_not_mem_row hL L le_rfl e)
  have htop : L.map (rowMap e) ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h2 := Submodule.finrank_le
      (L.map (rowMap e) ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)})
    rw [h5] at h2
    rw [h5]
    omega
  have hv : (Pi.single j 1 : Fin (m + 2) → ℂ) ∈
      L.map (rowMap e) ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have h3 := ca2 (k := m + 1) (Nat.succ_ne_zero m) hL e ξ hξ hξe γ t ht
  have h4 : ∀ j' : Fin (m + 2), γ + t (e, j') = (Pi.single j 1 : Fin (m + 2) → ℂ) j' := by
    intro j'
    rw [← hyz]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, rowMap_apply]
    ring
  rw [Finset.sum_eq_single j] at h3
  · rw [h4 j, Pi.single_eq_same, one_mul] at h3
    exact h3
  · intro j' _ hj'
    rw [h4 j', Pi.single_apply, if_neg hj', zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem thA {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ)}
    (hL : Lev (k + 2) L) (r : Fin (k + 2)) (p : Fin (k + 1))
    (x : Fin (k + 2) × Fin (k + 2) → ℂ) (hx : x ∈ L) (hx1 : ∀ j, x (r, j) = 0)
    (hx2 : ∀ j, x (r.succAbove p, j) = 0) (c : ℂ) (t : Fin (k + 2) × Fin (k + 2) → ℂ)
    (ht : t ∈ L) :
    ∑ j, ∑ q, (c + t (r, j)) * (c + t (r.succAbove p, j.succAbove q)) *
      blk (fun a => r.succAbove (p.succAbove a)) (fun b => j.succAbove (q.succAbove b)) x =
      0 := by
  choose P hP using fun (j : Fin (k + 2)) (q : Fin (k + 1)) =>
    polyLine_blk (n := k + 2) (fun a => r.succAbove (p.succAbove a))
      (fun b => j.succAbove (q.succAbove b)) x (fun z => c + t z)
  have hlev : ∀ τ : ℂ, pm (x + τ • fun z => c + t z) =
      (Nat.factorial (k + 2) : ℂ) * (τ * c) ^ (k + 2) := by
    intro τ
    have h1 := lev_scale hL (τ * c) (τ • t + x) (L.add_mem (L.smul_mem τ ht) hx)
    have e1 : (x + τ • fun z => c + t z) = fun z => τ * c + (τ • t + x) z := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, h1]
  have hkey : ∀ τ : ℂ, τ ^ 2 * (∑ j, ∑ q,
      Polynomial.C ((c + t (r, j)) * (c + t (r.succAbove p, j.succAbove q))) * P j q).eval τ =
      ((Nat.factorial (k + 2) : ℂ) * c ^ (k + 2)) * τ ^ (2 + k) := by
    intro τ
    have h2 : (Nat.factorial (k + 2) : ℂ) * c ^ (k + 2) * τ ^ (2 + k) =
        (Nat.factorial (k + 2) : ℂ) * (τ * c) ^ (k + 2) := by ring
    rw [h2, ← hlev τ, pm_laplace_two _ r p, Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← hP j q τ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx1 j, hx2 (j.succAbove q), zero_add]
    ring
  have h0 := poly_top _ 2 k hk hkey
  rw [Polynomial.eval_finsetSum] at h0
  refine Eq.trans ?_ h0
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← hP j q 0, zero_smul, add_zero]

theorem zbf_lineality {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c)
    (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c) (hx1 : x.1 = 0) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n (w + x)) =
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) ∧
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n (w + x)) =
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) := by
  have h1 := zbf_ufd hL r c u0 hu0 h0 (w + x) ((blockSpace L r c).add_mem hw hx)
  have h2 := zbf_ufd hL r c u0 hu0 h0 w hw
  rw [Prod.fst_add, hx1, add_zero] at h1
  exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩

theorem blk_unit {n : ℕ} (ρ κ : Unit → Fin n) (u : Fin n × Fin n → ℂ) :
    blk ρ κ u = u (ρ (), κ ()) := by
  unfold blk
  rw [Matrix.permanent_unique]
  rfl

theorem single_row_SR {k : ℕ} {L : Submodule ℂ (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hL : Lev (k + 1) L) (a j : Fin (k + 1)) (x : Fin (k + 1) × Fin (k + 1) → ℂ) (hx : x ∈ L)
    (hxc : ∀ b : Fin k, x (a.succAbove b, j) = 0) (hxj : x (a, j) ≠ 0)
    (c : ℂ) (t : Fin (k + 1) × Fin (k + 1) → ℂ) (ht : t ∈ L)
    (htc : ∀ b : Fin k, c + t (a.succAbove b, j) = 0) :
    c = 0 ∧ blk a.succAbove j.succAbove t = 0 := by
  have hxU : ((0 : ℂ), x) ∈ blockSpace L (sa a) (sa j) := by
    rw [mem_blockSpace]
    refine ⟨hx, fun b u => ?_⟩
    show (0 : ℂ) + x (sa a (Sum.inl b), sa j (Sum.inr u)) = 0
    rw [sa_inl, sa_inr, zero_add]
    exact hxc b
  have hwU : (c, t) ∈ blockSpace L (sa a) (sa j) := by
    rw [mem_blockSpace]
    refine ⟨ht, fun b u => ?_⟩
    show c + t (sa a (Sum.inl b), sa j (Sum.inr u)) = 0
    rw [sa_inl, sa_inr]
    exact htc b
  have hxb : blk (fun b : Unit => sa a (Sum.inr b)) (fun b : Unit => sa j (Sum.inr b))
      (hat (k + 1) ((0 : ℂ), x)) = x (a, j) := by
    rw [blk_unit, sa_inr, sa_inr]
    show (0 : ℂ) + x (a, j) = x (a, j)
    rw [zero_add]
  have hall : ∀ w ∈ blockSpace L (sa a) (sa j), w.1 = 0 := by
    intro w hw
    by_contra hw1
    have hu0 : w.1⁻¹ • w ∈ blockSpace L (sa a) (sa j) :=
      (blockSpace L (sa a) (sa j)).smul_mem _ hw
    have h0 : (w.1⁻¹ • w).1 = 1 := by
      rw [Prod.smul_fst, smul_eq_mul, inv_mul_cancel₀ hw1]
    have h1 := (zbf_ufd hL (sa a) (sa j) _ hu0 h0 _ hxU).2
    rw [hxb] at h1
    simp at h1
    exact hxj h1
  rcases zbf_zero (Nat.succ_ne_zero k) hL (sa a) (sa j) hall with h1 | h1
  · have hc : c = 0 := hall _ hwU
    refine ⟨hc, ?_⟩
    have h2 := h1 _ hwU
    have e1 : hat (k + 1) (c, t) = t := by
      funext p
      show c + t p = t p
      rw [hc, zero_add]
    have e2 : (fun b : Fin k => sa a (Sum.inl b)) = a.succAbove := funext fun b => sa_inl a b
    have e3 : (fun b : Fin k => sa j (Sum.inl b)) = j.succAbove := funext fun b => sa_inl j b
    rw [e1, e2, e3] at h2
    exact h2
  · exfalso
    have h2 := h1 _ hxU
    rw [hxb] at h2
    exact hxj h2

theorem permanent_three (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent = A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 + A 0 2 * A 1 1 * A 2 0 := by
  have hu : (univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  unfold Matrix.permanent
  rw [hu, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [Fin.prod_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.Perm.one_apply]
  simp
  ring

theorem fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  revert a
  decide

theorem n3_rowsum (x : Fin 3 × Fin 3 → ℂ) (r3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)
    (h1 : pm (fun p => 1 + x p) = 6) : x (r3, 0) + x (r3, 1) + x (r3, 2) = 0 := by
  simp only [pm, permanent_three, Matrix.of_apply] at h1
  rcases fin3_cases r3 with rfl | rfl | rfl
  · simp only [hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1
    linear_combination h1 / 2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1
    linear_combination h1 / 2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), add_zero] at h1
    linear_combination h1 / 2

theorem n3_colsum (y : Fin 3 × Fin 3 → ℂ) (c3 : Fin 3) (hy : ∀ i j, j ≠ c3 → y (i, j) = 0)
    (h2 : pm (fun p => 1 + y p) = 6) : y (0, c3) + y (1, c3) + y (2, c3) = 0 := by
  simp only [pm, permanent_three, Matrix.of_apply] at h2
  rcases fin3_cases c3 with rfl | rfl | rfl
  · simp only [hy 0 1 (by decide), hy 0 2 (by decide), hy 1 1 (by decide), hy 1 2 (by decide), hy 2 1 (by decide), hy 2 2 (by decide), add_zero] at h2
    linear_combination h2 / 2
  · simp only [hy 0 0 (by decide), hy 0 2 (by decide), hy 1 0 (by decide), hy 1 2 (by decide), hy 2 0 (by decide), hy 2 2 (by decide), add_zero] at h2
    linear_combination h2 / 2
  · simp only [hy 0 0 (by decide), hy 0 1 (by decide), hy 1 0 (by decide), hy 1 1 (by decide), hy 2 0 (by decide), hy 2 1 (by decide), add_zero] at h2
    linear_combination h2 / 2

theorem n3_alg (x y : Fin 3 × Fin 3 → ℂ) (r3 c3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)
    (hy : ∀ i j, j ≠ c3 → y (i, j) = 0) (h1 : pm (fun p => 1 + x p) = 6)
    (h2 : pm (fun p => 1 + y p) = 6) (h3 : pm (fun p => 1 + x p + y p) = 6) :
    x (r3, c3) * y (r3, c3) = 0 := by
  simp only [pm, permanent_three, Matrix.of_apply] at h1 h2 h3
  rcases fin3_cases r3 with rfl | rfl | rfl <;> rcases fin3_cases c3 with rfl | rfl | rfl
  · simp only [hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 1 (by decide), hy 0 2 (by decide), hy 1 1 (by decide), hy 1 2 (by decide), hy 2 1 (by decide), hy 2 2 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 0) + y (1, 0) + y (2, 0)) / 2 - y (0, 0) / 2) * h1 - (1 - x (0, 0) / 2) * h2
  · simp only [hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 0 (by decide), hy 0 2 (by decide), hy 1 0 (by decide), hy 1 2 (by decide), hy 2 0 (by decide), hy 2 2 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 1) + y (1, 1) + y (2, 1)) / 2 - y (0, 1) / 2) * h1 - (1 - x (0, 1) / 2) * h2
  · simp only [hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 0 (by decide), hy 0 1 (by decide), hy 1 0 (by decide), hy 1 1 (by decide), hy 2 0 (by decide), hy 2 1 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 2) + y (1, 2) + y (2, 2)) / 2 - y (0, 2) / 2) * h1 - (1 - x (0, 2) / 2) * h2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 1 (by decide), hy 0 2 (by decide), hy 1 1 (by decide), hy 1 2 (by decide), hy 2 1 (by decide), hy 2 2 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 0) + y (1, 0) + y (2, 0)) / 2 - y (1, 0) / 2) * h1 - (1 - x (1, 0) / 2) * h2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 0 (by decide), hy 0 2 (by decide), hy 1 0 (by decide), hy 1 2 (by decide), hy 2 0 (by decide), hy 2 2 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 1) + y (1, 1) + y (2, 1)) / 2 - y (1, 1) / 2) * h1 - (1 - x (1, 1) / 2) * h2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 2 0 (by decide), hx 2 1 (by decide), hx 2 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 0 (by decide), hy 0 1 (by decide), hy 1 0 (by decide), hy 1 1 (by decide), hy 2 0 (by decide), hy 2 1 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 2) + y (1, 2) + y (2, 2)) / 2 - y (1, 2) / 2) * h1 - (1 - x (1, 2) / 2) * h2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 1 (by decide), hy 0 2 (by decide), hy 1 1 (by decide), hy 1 2 (by decide), hy 2 1 (by decide), hy 2 2 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 0) + y (1, 0) + y (2, 0)) / 2 - y (2, 0) / 2) * h1 - (1 - x (2, 0) / 2) * h2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 0 (by decide), hy 0 2 (by decide), hy 1 0 (by decide), hy 1 2 (by decide), hy 2 0 (by decide), hy 2 2 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 1) + y (1, 1) + y (2, 1)) / 2 - y (2, 1) / 2) * h1 - (1 - x (2, 1) / 2) * h2
  · simp only [hx 0 0 (by decide), hx 0 1 (by decide), hx 0 2 (by decide), hx 1 0 (by decide), hx 1 1 (by decide), hx 1 2 (by decide), add_zero] at h1 h3
    simp only [hy 0 0 (by decide), hy 0 1 (by decide), hy 1 0 (by decide), hy 1 1 (by decide), hy 2 0 (by decide), hy 2 1 (by decide), add_zero] at h2 h3
    linear_combination h3 - (1 + (y (0, 2) + y (1, 2) + y (2, 2)) / 2 - y (2, 2) / 2) * h1 - (1 - x (2, 2) / 2) * h2

theorem n3_others (r3 : Fin 3) :
    ∃ r1 r2 : Fin 3, r1 ≠ r2 ∧ ∀ i, i ≠ r3 → i = r1 ∨ i = r2 := by
  revert r3
  decide

theorem n3_row {L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)} (hL : Lev 3 L)
    (h4 : 4 ≤ Module.finrank ℂ L) (r3 : Fin 3) :
    ∃ x ∈ L, x ≠ 0 ∧ ∀ i j, i ≠ r3 → x (i, j) = 0 := by
  obtain ⟨r1, r2, h12, hall⟩ := n3_others r3
  have h : Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) + 3 :=
    lemmaC_gen (m := 1) hL r1 r2 h12
  have hpos : 0 < Module.finrank ℂ (rowsZero L r1 r2) := by omega
  obtain ⟨⟨x, hxm⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨hxL, hx1, hx2⟩ := (mem_rowsZero L r1 r2 x).mp hxm
  refine ⟨x, hxL, ?_, fun i j hi => ?_⟩
  · intro h0
    apply hx0
    exact Subtype.ext h0
  · rcases hall i hi with rfl | rfl
    · exact hx1 j
    · exact hx2 j

theorem n3_col {L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)} (hL : Lev 3 L)
    (h4 : 4 ≤ Module.finrank ℂ L) (c3 : Fin 3) :
    ∃ y ∈ L, y ≠ 0 ∧ ∀ i j, j ≠ c3 → y (i, j) = 0 := by
  obtain ⟨c1, c2, h12, hall⟩ := n3_others c3
  have h : Module.finrank ℂ L ≤ Module.finrank ℂ (colsZero L c1 c2) + 3 :=
    lemmaC_col_gen (m := 1) hL c1 c2 h12
  have hpos : 0 < Module.finrank ℂ (colsZero L c1 c2) := by omega
  obtain ⟨⟨y, hym⟩, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨hyL, hy1, hy2⟩ := (mem_colsZero L c1 c2 y).mp hym
  refine ⟨y, hyL, ?_, fun i j hj => ?_⟩
  · intro h0
    apply hy0
    exact Subtype.ext h0
  · rcases hall j hj with rfl | rfl
    · exact hy1 i
    · exact hy2 i

theorem n3_two_row (x : Fin 3 × Fin 3 → ℂ) (r3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)
    (hx0 : x ≠ 0) (hs : x (r3, 0) + x (r3, 1) + x (r3, 2) = 0) :
    ∃ j1 j2 : Fin 3, j1 ≠ j2 ∧ x (r3, j1) ≠ 0 ∧ x (r3, j2) ≠ 0 := by
  have h1 : ∃ p, x p ≠ 0 := by
    by_contra hcon
    apply hx0
    funext p
    by_contra hp
    exact hcon ⟨p, hp⟩
  obtain ⟨⟨i, j⟩, hp⟩ := h1
  have hi : i = r3 := by
    by_contra hi
    exact hp (hx i j hi)
  subst hi
  by_contra hcon
  have hz : ∀ j2, j2 ≠ j → x (i, j2) = 0 := by
    intro j2 hj2
    by_contra h2
    exact hcon ⟨j, j2, Ne.symm hj2, hp, h2⟩
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [hz 1 (by decide), hz 2 (by decide), add_zero, add_zero] at hs
    exact hp hs
  · rw [hz 0 (by decide), hz 2 (by decide), zero_add, add_zero] at hs
    exact hp hs
  · rw [hz 0 (by decide), hz 1 (by decide), zero_add, zero_add] at hs
    exact hp hs

theorem n3_two_col (y : Fin 3 × Fin 3 → ℂ) (c3 : Fin 3) (hy : ∀ i j, j ≠ c3 → y (i, j) = 0)
    (hy0 : y ≠ 0) (hs : y (0, c3) + y (1, c3) + y (2, c3) = 0) :
    ∃ i1 i2 : Fin 3, i1 ≠ i2 ∧ y (i1, c3) ≠ 0 ∧ y (i2, c3) ≠ 0 := by
  have h1 : ∃ p, y p ≠ 0 := by
    by_contra hcon
    apply hy0
    funext p
    by_contra hp
    exact hcon ⟨p, hp⟩
  obtain ⟨⟨i, j⟩, hp⟩ := h1
  have hj : j = c3 := by
    by_contra hj
    exact hp (hy i j hj)
  subst hj
  by_contra hcon
  have hz : ∀ i2, i2 ≠ i → y (i2, j) = 0 := by
    intro i2 hi2
    by_contra h2
    exact hcon ⟨i, i2, Ne.symm hi2, hp, h2⟩
  rcases fin3_cases i with rfl | rfl | rfl
  · rw [hz 1 (by decide), hz 2 (by decide), add_zero, add_zero] at hs
    exact hp hs
  · rw [hz 0 (by decide), hz 2 (by decide), zero_add, add_zero] at hs
    exact hp hs
  · rw [hz 0 (by decide), hz 1 (by decide), zero_add, zero_add] at hs
    exact hp hs

theorem fin3_pick (i1 i2 : Fin 3) (h12 : i1 ≠ i2) (h1 : i1 ≠ 0) (h2 : i2 ≠ 0) :
    i1 = 1 ∨ i2 = 1 := by
  revert i1 i2
  decide

theorem fin3_pigeon (j1 j2 j3 j4 : Fin 3) (h12 : j1 ≠ j2) (h31 : j3 ≠ j1) (h32 : j3 ≠ j2)
    (h41 : j4 ≠ j1) (h42 : j4 ≠ j2) : j3 = j4 := by
  revert j1 j2 j3 j4
  decide

theorem n3 {L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)} (hL : Lev 3 L) :
    Module.finrank ℂ L ≤ 3 := by
  by_contra hcon
  have h4 : 4 ≤ Module.finrank ℂ L := by omega
  choose x hxL hx0 hx using fun r3 => n3_row hL h4 r3
  choose y hyL hy0 hy using fun c3 => n3_col hL h4 c3
  have h6 : ∀ t ∈ L, pm (fun p => 1 + t p) = 6 := by
    intro t ht
    have h := lev_scale hL 1 t ht
    rw [h]
    norm_num [Nat.factorial]
  have hrel : ∀ i j, x i (i, j) * y j (i, j) = 0 := by
    intro i j
    have h3 := h6 (x i + y j) (L.add_mem (hxL i) (hyL j))
    have e : (fun p => 1 + (x i + y j) p) = (fun p => 1 + x i p + y j p) := by
      funext p
      simp only [Pi.add_apply]
      ring
    rw [e] at h3
    exact n3_alg (x i) (y j) i j (hx i) (hy j) (h6 _ (hxL i)) (h6 _ (hyL j)) h3
  have hrow : ∀ i, ∃ j1 j2 : Fin 3, j1 ≠ j2 ∧ x i (i, j1) ≠ 0 ∧ x i (i, j2) ≠ 0 := fun i =>
    n3_two_row (x i) i (hx i) (hx0 i) (n3_rowsum (x i) i (hx i) (h6 _ (hxL i)))
  have hcol : ∀ j, ∃ i1 i2 : Fin 3, i1 ≠ i2 ∧ y j (i1, j) ≠ 0 ∧ y j (i2, j) ≠ 0 := fun j =>
    n3_two_col (y j) j (hy j) (hy0 j) (n3_colsum (y j) j (hy j) (h6 _ (hyL j)))
  have hkill : ∀ j, x 0 (0, j) ≠ 0 → x 1 (1, j) = 0 := by
    intro j ha
    have hb : y j (0, j) = 0 := by
      rcases mul_eq_zero.mp (hrel 0 j) with h | h
      · exact absurd h ha
      · exact h
    obtain ⟨i1, i2, hi12, hy1, hy2⟩ := hcol j
    have hi1 : i1 ≠ 0 := by
      rintro rfl
      exact hy1 hb
    have hi2 : i2 ≠ 0 := by
      rintro rfl
      exact hy2 hb
    have hc : y j (1, j) ≠ 0 := by
      rcases fin3_pick i1 i2 hi12 hi1 hi2 with rfl | rfl
      · exact hy1
      · exact hy2
    rcases mul_eq_zero.mp (hrel 1 j) with h | h
    · exact h
    · exact absurd h hc
  obtain ⟨j1, j2, hj12, ha1, ha2⟩ := hrow 0
  obtain ⟨j3, j4, hj34, ha3, ha4⟩ := hrow 1
  have h31 : j3 ≠ j1 := by
    rintro rfl
    exact ha3 (hkill _ ha1)
  have h32 : j3 ≠ j2 := by
    rintro rfl
    exact ha3 (hkill _ ha2)
  have h41 : j4 ≠ j1 := by
    rintro rfl
    exact ha4 (hkill _ ha1)
  have h42 : j4 ≠ j2 := by
    rintro rfl
    exact ha4 (hkill _ ha2)
  exact hj34 (fin3_pigeon j1 j2 j3 j4 hj12 h31 h32 h41 h42)

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

noncomputable def mix {n : ℕ} (m : ℕ) (u x : Fin n × Fin n → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n),
    ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      (∏ a ∈ A, x (a, σ a)) * ∏ a ∈ Aᶜ, u (a, σ a)

theorem pm_line_expand {n : ℕ} (u x : Fin n × Fin n → ℂ) (s : ℂ) :
    pm (u + s • x) = ∑ m ∈ range (n + 1), s ^ m * mix m u x := by
  rw [pm_perm]
  have h1 : ∀ σ : Equiv.Perm (Fin n), ∏ i, (u + s • x) (i, σ i) =
      ∑ m ∈ range (n + 1), s ^ m *
        ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
          (∏ a ∈ A, x (a, σ a)) * ∏ a ∈ Aᶜ, u (a, σ a) := by
    intro σ
    refine (Finset.prod_congr rfl fun i _ => ?_).trans
      (prod_add_smul (fun a => u (a, σ a)) (fun a => x (a, σ a)) s)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold mix
  rw [Finset.mul_sum]

theorem poly_coeff_zero (a : ℕ → ℂ) (N : ℕ) (K : ℂ)
    (h : ∀ s : ℂ, ∑ m ∈ range (N + 1), s ^ m * a m = K) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    a m = 0 := by
  have hQ : (∑ i ∈ range (N + 1), Polynomial.C (a i) * Polynomial.X ^ i) = Polynomial.C K := by
    apply Polynomial.funext
    intro s
    rw [Polynomial.eval_finsetSum, Polynomial.eval_C, ← h s]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have h2 : (∑ i ∈ range (N + 1), Polynomial.C (a i) * Polynomial.X ^ i).coeff m =
      (Polynomial.C K).coeff m := by rw [hQ]
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_C, if_neg (by omega)] at h2
  refine Eq.trans ?_ h2
  rw [Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro i _ hi
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hi)]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

theorem lev_mix {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (c : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    mix m (fun p => c + t p) x = 0 := by
  refine poly_coeff_zero (fun m => mix m (fun p => c + t p) x) n
    ((Nat.factorial n : ℂ) * c ^ n) (fun s => ?_) m hm1 hmn
  show ∑ m ∈ range (n + 1), s ^ m * mix m (fun p => c + t p) x = (Nat.factorial n : ℂ) * c ^ n
  rw [← pm_line_expand, ← lev_line hL c s t x ht hx]
  congr 1

def pairSpace {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 c1 c2 : Fin n) :
    Submodule ℂ (ℂ × (Fin n × Fin n → ℂ)) where
  carrier := {w | w.2 ∈ L ∧ ∀ j, j ≠ c1 → j ≠ c2 →
    w.1 + w.2 (r1, j) = 0 ∧ w.1 + w.2 (r2, j) = 0}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨L.add_mem hx1 hy1, fun j h1 h2 => ⟨?_, ?_⟩⟩
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      linear_combination (hx2 j h1 h2).1 + (hy2 j h1 h2).1
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      linear_combination (hx2 j h1 h2).2 + (hy2 j h1 h2).2
  zero_mem' := ⟨L.zero_mem, fun j _ _ => by simp⟩
  smul_mem' := by
    rintro k x ⟨hx1, hx2⟩
    refine ⟨L.smul_mem k hx1, fun j h1 h2 => ⟨?_, ?_⟩⟩
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      linear_combination k * (hx2 j h1 h2).1
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      linear_combination k * (hx2 j h1 h2).2

theorem mem_pairSpace {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 c1 c2 : Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) :
    w ∈ pairSpace L r1 r2 c1 c2 ↔ w.2 ∈ L ∧ ∀ j, j ≠ c1 → j ≠ c2 →
      w.1 + w.2 (r1, j) = 0 ∧ w.1 + w.2 (r2, j) = 0 := Iff.rfl

theorem pairSpace_eq {m : ℕ} (L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ))
    (ρ κ : Equiv.Perm (Fin (m + 2))) :
    pairSpace L (ρ 0) (ρ 1) (κ 0) (κ 1) = blockSpace L ((e2m m).trans ρ) ((e2m m).trans κ) := by
  have hr0 : ((e2m m).trans ρ) (Sum.inl 0) = ρ 0 := by
    rw [Equiv.trans_apply, e2m_inl0]
  have hr1 : ((e2m m).trans ρ) (Sum.inl 1) = ρ 1 := by
    rw [Equiv.trans_apply, e2m_inl1]
  have hc0 : ((e2m m).trans κ) (Sum.inl 0) = κ 0 := by
    rw [Equiv.trans_apply, e2m_inl0]
  have hc1 : ((e2m m).trans κ) (Sum.inl 1) = κ 1 := by
    rw [Equiv.trans_apply, e2m_inl1]
  ext w
  rw [mem_pairSpace, mem_blockSpace]
  constructor
  · rintro ⟨hw1, hw2⟩
    refine ⟨hw1, fun a b => ?_⟩
    have hne0 : ((e2m m).trans κ) (Sum.inr b) ≠ κ 0 := by
      rw [← hc0]
      intro h
      have h' := ((e2m m).trans κ).injective h
      cases h'
    have hne1 : ((e2m m).trans κ) (Sum.inr b) ≠ κ 1 := by
      rw [← hc1]
      intro h
      have h' := ((e2m m).trans κ).injective h
      cases h'
    have h3 := hw2 _ hne0 hne1
    have hboth : ∀ a' : Fin 2, w.1 + w.2 (((e2m m).trans ρ) (Sum.inl a'),
        ((e2m m).trans κ) (Sum.inr b)) = 0 := by
      rw [Fin.forall_fin_two]
      constructor
      · rw [hr0]
        exact h3.1
      · rw [hr1]
        exact h3.2
    exact hboth a
  · rintro ⟨hw1, hw2⟩
    refine ⟨hw1, fun j hj0 hj1 => ?_⟩
    obtain ⟨y, rfl⟩ := ((e2m m).trans κ).surjective j
    rcases y with a | b
    · exfalso
      have hcase : ∀ a' : Fin 2, ((e2m m).trans κ) (Sum.inl a') ≠ κ 0 →
          ((e2m m).trans κ) (Sum.inl a') ≠ κ 1 → False := by
        rw [Fin.forall_fin_two]
        constructor
        · intro h _
          exact h hc0
        · intro _ h
          exact h hc1
      exact hcase a hj0 hj1
    · have h0 := hw2 0 b
      have h1 := hw2 1 b
      rw [hr0] at h0
      rw [hr1] at h1
      exact ⟨h0, h1⟩

theorem thB_pair {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r1 r2 c1 c2 : Fin (m + 2)) (hr : r1 ≠ r2) (hc : c1 ≠ c2)
    (u0 : ℂ × (Fin (m + 2) × Fin (m + 2) → ℂ)) (hu0 : u0 ∈ pairSpace L r1 r2 c1 c2)
    (h0 : u0.1 = 1) :
    Module.finrank ℂ (pairSpace L r1 r2 c1 c2) ≤ 2 + Module.finrank ℂ (rowsZero L r1 r2) ∧
      ((u0.1 + u0.2 (r1, c1)) * (u0.1 + u0.2 (r2, c2)) +
        (u0.1 + u0.2 (r1, c2)) * (u0.1 + u0.2 (r2, c1)) ≠ 0) ∧
      ∀ w ∈ pairSpace L r1 r2 c1 c2,
        (w.1 + w.2 (r1, c1)) * (w.1 + w.2 (r2, c2)) +
          (w.1 + w.2 (r1, c2)) * (w.1 + w.2 (r2, c1)) =
        ((u0.1 + u0.2 (r1, c1)) * (u0.1 + u0.2 (r2, c2)) +
          (u0.1 + u0.2 (r1, c2)) * (u0.1 + u0.2 (r2, c1))) * w.1 ^ 2 := by
  obtain ⟨ρ, rfl, rfl⟩ := exists_perm2 r1 r2 hr
  obtain ⟨κ, rfl, rfl⟩ := exists_perm2 c1 c2 hc
  rw [pairSpace_eq] at hu0 ⊢
  have hr0 : ((e2m m).trans ρ) (Sum.inl 0) = ρ 0 := by
    rw [Equiv.trans_apply, e2m_inl0]
  have hr1 : ((e2m m).trans ρ) (Sum.inl 1) = ρ 1 := by
    rw [Equiv.trans_apply, e2m_inl1]
  have hc0 : ((e2m m).trans κ) (Sum.inl 0) = κ 0 := by
    rw [Equiv.trans_apply, e2m_inl0]
  have hc1 : ((e2m m).trans κ) (Sum.inl 1) = κ 1 := by
    rw [Equiv.trans_apply, e2m_inl1]
  have hq : ∀ w : ℂ × (Fin (m + 2) × Fin (m + 2) → ℂ),
      q0 (blockProj ((e2m m).trans ρ) ((e2m m).trans κ) w) =
        (w.1 + w.2 (ρ 0, κ 0)) * (w.1 + w.2 (ρ 1, κ 1)) +
          (w.1 + w.2 (ρ 0, κ 1)) * (w.1 + w.2 (ρ 1, κ 0)) := by
    intro w
    unfold q0
    rw [blockProj_apply, blockProj_apply, blockProj_apply, blockProj_apply, hr0, hr1, hc0, hc1]
  have hB := thB_dim hL ((e2m m).trans ρ) ((e2m m).trans κ) u0 hu0 h0
  rw [hr0, hr1] at hB
  obtain ⟨hκ, hquad⟩ := thB_quad hL ((e2m m).trans ρ) ((e2m m).trans κ) u0 hu0 h0
  rw [hq] at hκ
  refine ⟨hB, hκ, fun w hw => ?_⟩
  have h1 := hquad w hw
  rw [hq, hq] at h1
  exact h1

theorem poly_coeff_eq (a b : ℕ → ℂ) (N : ℕ)
    (h : ∀ s : ℂ, ∑ m ∈ range (N + 1), s ^ m * a m = ∑ m ∈ range (N + 1), s ^ m * b m)
    (m : ℕ) (hmN : m ≤ N) : a m = b m := by
  have e : ∀ (d : ℕ → ℂ) (s : ℂ),
      (∑ i ∈ range (N + 1), Polynomial.C (d i) * Polynomial.X ^ i).eval s =
        ∑ i ∈ range (N + 1), s ^ i * d i := by
    intro d s
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hQ : (∑ i ∈ range (N + 1), Polynomial.C (a i) * Polynomial.X ^ i) =
      ∑ i ∈ range (N + 1), Polynomial.C (b i) * Polynomial.X ^ i := by
    apply Polynomial.funext
    intro s
    rw [e a s, e b s, h s]
  have hc : ∀ d : ℕ → ℂ,
      (∑ i ∈ range (N + 1), Polynomial.C (d i) * Polynomial.X ^ i).coeff m = d m := by
    intro d
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro i _ hi
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hi)]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  rw [← hc a, ← hc b, hQ]

theorem lev_mix_hat {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c1 c2 : ℂ) (t1 t2 : Fin n × Fin n → ℂ) (h1 : t1 ∈ L) (h2 : t2 ∈ L) (m : ℕ) (hmn : m ≤ n) :
    mix m (fun p => c1 + t1 p) (fun p => c2 + t2 p) =
      (Nat.factorial n : ℂ) * ((n.choose m : ℂ) * c1 ^ (n - m) * c2 ^ m) := by
  refine poly_coeff_eq (fun m => mix m (fun p => c1 + t1 p) (fun p => c2 + t2 p))
    (fun m => (Nat.factorial n : ℂ) * ((n.choose m : ℂ) * c1 ^ (n - m) * c2 ^ m)) n
    (fun s => ?_) m hmn
  show ∑ m ∈ range (n + 1), s ^ m * mix m (fun p => c1 + t1 p) (fun p => c2 + t2 p) =
    ∑ m ∈ range (n + 1),
      s ^ m * ((Nat.factorial n : ℂ) * ((n.choose m : ℂ) * c1 ^ (n - m) * c2 ^ m))
  rw [← pm_line_expand]
  have h3 := lev_scale hL (c1 + s * c2) (t1 + s • t2) (L.add_mem h1 (L.smul_mem s h2))
  have e : ((fun p => c1 + t1 p) + s • fun p => c2 + t2 p) =
      fun p => (c1 + s * c2) + (t1 + s • t2) p := by
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, h3, add_comm c1 (s * c2), add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  ring

theorem blk_zero_col {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (u : Fin n × Fin n → ℂ) (a0 : m) (h : ∀ i, u (ρ i, κ a0) = 0) : blk ρ κ u = 0 := by
  unfold blk Matrix.permanent
  exact Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero (Finset.mem_univ a0) (h (σ a0))

theorem pm_zero_of_big_block {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (u : Fin n × Fin n → ℂ) (r c : α ⊕ β ≃ Fin n)
    (h : ∀ a b, u (r (Sum.inl a), c (Sum.inr b)) = 0) (a0 : α)
    (h0 : ∀ a, u (r (Sum.inl a), c (Sum.inl a0)) = 0) : pm u = 0 := by
  rw [pm_zero_block u r c h, blk_zero_col _ _ u a0 h0, zero_mul]

theorem lev_FK_block {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c) (a0 : α)
    (h0 : ∀ a, w.1 + w.2 (r (Sum.inl a), c (Sum.inl a0)) = 0) : w.1 = 0 := by
  have hw' := (mem_blockSpace L r c w).mp hw
  exact lev_FK hL w.1 w.2 hw'.1
    (pm_zero_of_big_block (fun p => w.1 + w.2 p) r c (fun a b => hw'.2 a b) a0 h0)

theorem pm_zero_block_sets {n : ℕ} (u : Fin n × Fin n → ℂ) (S Z : Finset (Fin n))
    (eS : {x // x ∈ S} ≃ {x // x ∉ Z}) (eZ : {x // x ∉ S} ≃ {x // x ∈ Z})
    (h : ∀ i ∈ S, ∀ j ∈ Z, u (i, j) = 0) :
    pm u = blk (fun a : {x // x ∈ S} => (a : Fin n))
        (fun a => ((eS a : {x // x ∉ Z}) : Fin n)) u *
      blk (fun b : {x // x ∉ S} => (b : Fin n)) (fun b => ((eZ b : {x // x ∈ Z}) : Fin n)) u := by
  have h1 := pm_zero_block u (Equiv.sumCompl (fun x => x ∈ S))
    ((Equiv.sumCongr eS eZ).trans ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun x => x ∈ Z))))
    (fun a b => h a.1 a.2 _ (eZ b).2)
  exact h1

theorem exists_block_equivs {n : ℕ} (S Z : Finset (Fin n)) (hcard : S.card + Z.card = n) :
    Nonempty ({x // x ∈ S} ≃ {x // x ∉ Z}) ∧ Nonempty ({x // x ∉ S} ≃ {x // x ∈ Z}) := by
  constructor
  · apply Fintype.card_eq.mp
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin]
    omega
  · apply Fintype.card_eq.mp
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin]
    omega

theorem row_proj_le {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r : Fin (m + 2)) :
    Module.finrank ℂ (L.map (rowMap r)) ≤ m + 1 := by
  have h5 : Module.finrank ℂ (Fin (m + 2) → ℂ) = m + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h1 := finrank_sup_one _ (one_not_mem_row hL L le_rfl r)
  have h2 := Submodule.finrank_le
    (L.map (rowMap r) ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)})
  rw [h5] at h2
  omega

theorem rows_pigeon {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) +
      Module.finrank ℂ (L.map (rowMap r1)) + Module.finrank ℂ (L.map (rowMap r2)) := by
  have h1 := rank_nullity L (rowMap r1)
  have h2 := rank_nullity (L ⊓ LinearMap.ker (rowMap r1)) (rowMap r2)
  have h3 : Module.finrank ℂ ((L ⊓ LinearMap.ker (rowMap r1)).map (rowMap r2)) ≤
      Module.finrank ℂ (L.map (rowMap r2)) :=
    Submodule.finrank_mono (Submodule.map_mono inf_le_left)
  have h4 : (L ⊓ LinearMap.ker (rowMap r1)) ⊓ LinearMap.ker (rowMap r2) = rowsZero L r1 r2 := rfl
  rw [h4] at h2
  omega

theorem zbf_witness {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c) (hx1 : x.1 = 0)
    (hβ : Fintype.card β ≠ 0)
    (hxb : blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x) ≠ 0) :
    (∀ w ∈ blockSpace L r c, w.1 = 0) ∧
      ∀ w ∈ blockSpace L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) = 0 := by
  have hall : ∀ w ∈ blockSpace L r c, w.1 = 0 := by
    intro w hw
    by_contra hw1
    have hu0 : w.1⁻¹ • w ∈ blockSpace L r c := (blockSpace L r c).smul_mem _ hw
    have h0 : (w.1⁻¹ • w).1 = 1 := by
      rw [Prod.smul_fst, smul_eq_mul, inv_mul_cancel₀ hw1]
    have h1 := (zbf_ufd hL r c _ hu0 h0 x hx).2
    rw [hx1, zero_pow hβ, mul_zero] at h1
    exact hxb h1
  refine ⟨hall, ?_⟩
  rcases zbf_zero hn hL r c hall with h1 | h1
  · exact h1
  · exact absurd (h1 x hx) hxb

theorem zbf_witness' {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c) (hx1 : x.1 = 0)
    (hα : Fintype.card α ≠ 0)
    (hxa : blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n x) ≠ 0) :
    (∀ w ∈ blockSpace L r c, w.1 = 0) ∧
      ∀ w ∈ blockSpace L r c,
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0 := by
  have hall : ∀ w ∈ blockSpace L r c, w.1 = 0 := by
    intro w hw
    by_contra hw1
    have hu0 : w.1⁻¹ • w ∈ blockSpace L r c := (blockSpace L r c).smul_mem _ hw
    have h0 : (w.1⁻¹ • w).1 = 1 := by
      rw [Prod.smul_fst, smul_eq_mul, inv_mul_cancel₀ hw1]
    have h1 := (zbf_ufd hL r c _ hu0 h0 x hx).1
    rw [hx1, zero_pow hα, mul_zero] at h1
    exact hxa h1
  refine ⟨hall, ?_⟩
  rcases zbf_zero hn hL r c hall with h1 | h1
  · exact absurd (h1 x hx) hxa
  · exact h1

theorem blk_tr {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (t : Fin n × Fin n → ℂ) : blk ρ κ (trE n t) = blk κ ρ t := by
  unfold blk
  rw [← Matrix.permanent_transpose]
  rfl

theorem ca2_col {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hL : Lev (k + 1) L) (e : Fin (k + 1)) (ξ : Fin (k + 1) × Fin (k + 1) → ℂ) (hξ : ξ ∈ L)
    (hξe : ∀ i, ξ (i, e) = 0) (c : ℂ) (t : Fin (k + 1) × Fin (k + 1) → ℂ) (ht : t ∈ L) :
    ∑ i, (c + t (i, e)) * blk i.succAbove e.succAbove ξ = 0 := by
  have h := ca2 hk (lev_tr hL) e (trE (k + 1) ξ) (Submodule.mem_map_of_mem hξ)
    (fun j => hξe j) c (trE (k + 1) t) (Submodule.mem_map_of_mem ht)
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blk_tr]
  rfl

theorem thA_col {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ)}
    (hL : Lev (k + 2) L) (r : Fin (k + 2)) (p : Fin (k + 1))
    (x : Fin (k + 2) × Fin (k + 2) → ℂ) (hx : x ∈ L) (hx1 : ∀ i, x (i, r) = 0)
    (hx2 : ∀ i, x (i, r.succAbove p) = 0) (c : ℂ) (t : Fin (k + 2) × Fin (k + 2) → ℂ)
    (ht : t ∈ L) :
    ∑ j, ∑ q, (c + t (j, r)) * (c + t (j.succAbove q, r.succAbove p)) *
      blk (fun b => j.succAbove (q.succAbove b)) (fun a => r.succAbove (p.succAbove a)) x =
      0 := by
  have h := thA hk (lev_tr hL) r p (trE (k + 2) x) (Submodule.mem_map_of_mem hx)
    (fun j => hx1 j) (fun j => hx2 j) c (trE (k + 2) t) (Submodule.mem_map_of_mem ht)
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [blk_tr]
  rfl

theorem q0_isotropic_bound (P : Submodule ℂ (Fin 2 × Fin 2 → ℂ)) (h : ∀ z ∈ P, q0 z = 0) :
    Module.finrank ℂ P ≤ 2 := by
  have h1 := b_perp_bound P P (fun v hv z hz => by
    rw [← q0_polar, h v hv, h z hz, h (v + z) (P.add_mem hv hz)]
    ring)
  omega

theorem thB_img_or {n : ℕ} (hn : n ≠ 0) {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n) :
    Module.finrank ℂ ((blockSpace L r c).map (blockProj r c)) ≤ 2 ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧ ∀ w ∈ blockSpace L r c,
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0) := by
  rcases thB_cases hn hL r c with ⟨u0, hu0, h0⟩ | ⟨hall, h1 | h1⟩
  · exact Or.inl (thB_img hL r c u0 hu0 h0)
  · left
    apply q0_isotropic_bound
    rintro _ ⟨w, hw, rfl⟩
    exact h1 w hw
  · exact Or.inr ⟨hall, h1⟩

theorem thB_Bx {n : ℕ} (hn : n ≠ 0) {β : Type} [Fintype β] [DecidableEq β]
    (hβ : Fintype.card β ≠ 0) {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (r c : Fin 2 ⊕ β ≃ Fin n) (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c)
    (hx1 : x.1 = 0) :
    blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x) = 0 ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧
        ∀ w ∈ blockSpace L r c, q0 (blockProj r c w) = 0) := by
  rcases thB_cases hn hL r c with ⟨u0, hu0, h0⟩ | ⟨hall, h1 | h1⟩
  · left
    have h2 := (zbf_ufd hL r c u0 hu0 h0 x hx).2
    rw [hx1, zero_pow hβ, mul_zero] at h2
    exact h2
  · exact Or.inr ⟨hall, h1⟩
  · exact Or.inl (h1 x hx)

theorem mix_eq_sum_pm {n : ℕ} (m : ℕ) (u x : Fin n × Fin n → ℂ) :
    mix m u x = ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      pm (fun p => if p.1 ∈ A then x p else u p) := by
  unfold mix
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [pm_perm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  refine Eq.trans ?_ (Finset.prod_mul_prod_compl A _)
  congr 1
  · exact Finset.prod_congr rfl fun i hi => (if_pos hi).symm
  · exact Finset.prod_congr rfl fun i hi => (if_neg (Finset.mem_compl.mp hi)).symm

theorem lev_mix_pm {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (c : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      pm (fun p => if p.1 ∈ A then x p else c + t p) = 0 := by
  rw [← mix_eq_sum_pm]
  exact lev_mix hL c t x ht hx m hm1 hmn

theorem lev_rows {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (R : Finset (Fin n)) (hR : R.Nonempty) (x : Fin n × Fin n → ℂ) (hx : x ∈ L)
    (hx0 : ∀ i, i ∉ R → ∀ j, x (i, j) = 0) (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => if p.1 ∈ R then x p else c + t p) = 0 := by
  have h := lev_mix_pm hL c t x ht hx R.card (Finset.card_pos.mpr hR) (by
    have h1 := Finset.card_le_univ R
    rwa [Fintype.card_fin] at h1)
  rw [Finset.sum_eq_single R] at h
  · exact h
  · intro A hA hAR
    have hcard : A.card = R.card := (Finset.mem_filter.mp hA).2
    have hex : ∃ a ∈ A, a ∉ R := by
      by_contra hcon
      apply hAR
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        by_contra haR
        exact hcon ⟨a, ha, haR⟩
      · exact le_of_eq hcard.symm
    obtain ⟨a, ha, haR⟩ := hex
    apply pm_zero_row _ a
    intro j
    show (if a ∈ A then x (a, j) else c + t (a, j)) = 0
    rw [if_pos ha]
    exact hx0 a haR j
  · intro hR'
    exact (hR' (Finset.mem_filter.mpr ⟨Finset.mem_univ R, rfl⟩)).elim

end PEqualNP.Gct.ZBF210

theorem PEqualNP.Outside.L_gct_210_zbf : ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) → (∀ (c : ℂ), ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (c + t (i, f i))) = 120 * c ^ 5) ∧ (∀ r1 r2 : Fin 5, r1 ≠ r2 → Module.finrank ℂ L ≤ Module.finrank ℂ (PEqualNP.Gct.ZBF210.rowsZero L r1 r2) + 7) ∧ ∀ c1 c2 : Fin 5, c1 ≠ c2 → Module.finrank ℂ L ≤ Module.finrank ℂ (PEqualNP.Gct.ZBF210.colsZero L c1 c2) + 7 := by
  intro L hL
  refine ⟨fun c t ht => ?_, fun r1 r2 hr => ?_, fun c1 c2 hc => ?_⟩
  · have h := PEqualNP.Gct.ZBF210.lev_scale_emb (PEqualNP.Gct.ZBF210.lev_five L hL) c t ht
    rw [h]
    norm_num [Nat.factorial]
  · exact PEqualNP.Gct.ZBF210.lemmaC (PEqualNP.Gct.ZBF210.lev_five L hL) r1 r2 hr
  · exact PEqualNP.Gct.ZBF210.lemmaC_col (PEqualNP.Gct.ZBF210.lev_five L hL) c1 c2 hc
