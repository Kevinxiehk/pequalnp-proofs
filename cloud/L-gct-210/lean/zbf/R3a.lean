import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_210_aux.ZBF

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
  carrier := {w | w.2 ∈ L ∧ ∀ a b, w.1 + w.2 (r (Sum.inl a), c (Sum.inr b)) = 0}; add_mem' := by
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
    w.1 + w.2 (r1, j) = 0 ∧ w.1 + w.2 (r2, j) = 0}; add_mem' := by
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

theorem pm_smul {n : ℕ} (a : ℂ) (u : Fin n × Fin n → ℂ) : pm (a • u) = a ^ n * pm u := by
  have h := blk_smul (m := Fin n) (fun i => i) (fun j => j) a u
  rw [Fintype.card_fin] at h
  exact h

def BLev {n : ℕ} (b : Fin n × Fin n → ℂ) (κ : ℂ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) : Prop :=
  κ ≠ 0 ∧ ∀ c : ℂ, ∀ t ∈ L, pm (fun p => c * b p + t p) = κ * c ^ n

theorem blev_of_lev {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    BLev (fun _ => (1 : ℂ)) (Nat.factorial n : ℂ) L := by
  refine ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n), fun c t ht => ?_⟩
  have h := lev_scale hL c t ht
  simpa using h

theorem blev_of_const {n : ℕ} (b : Fin n × Fin n → ℂ) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hb : pm b ≠ 0) (h : ∀ t ∈ L, pm (b + t) = pm b) : BLev b (pm b) L := by
  refine ⟨hb, fun c t ht => ?_⟩
  have key : ∀ a : ℂ, a ≠ 0 → pm (fun p => a * b p + t p) = pm b * a ^ n := by
    intro a ha
    have h1 := h (a⁻¹ • t) (L.smul_mem _ ht)
    have e : (fun p => a * b p + t p) = a • (b + a⁻¹ • t) := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [e, pm_smul, h1]
    ring
  have hP : ∀ a : ℂ, (∑ σ : Equiv.Perm (Fin n),
      ∏ i, (Polynomial.X * Polynomial.C (b (i, σ i)) + Polynomial.C (t (i, σ i))) -
        Polynomial.C (pm b) * Polynomial.X ^ n).eval a =
      pm (fun p => a * b p + t p) - pm b * a ^ n := by
    intro a
    rw [pm_perm (fun p => a * b p + t p)]
    simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_pow]
  have hP0 := poly_zero_of_ne _ (fun a ha => by rw [hP a, key a ha, sub_self])
  have h4 := hP c
  rw [hP0, Polynomial.eval_zero] at h4
  exact sub_eq_zero.mp h4.symm

theorem blev_mono {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L K : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (hK : K ≤ L) : BLev b κ K :=
  ⟨hL.1, fun c t ht => hL.2 c t (hK ht)⟩

noncomputable def hatB {n : ℕ} (b : Fin n × Fin n → ℂ) :
    ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) where
  toFun w := fun p => w.1 * b p + w.2 p
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hatB_eq {n : ℕ} (b : Fin n × Fin n → ℂ) (w : ℂ × (Fin n × Fin n → ℂ)) :
    hatB b w = fun p => w.1 * b p + w.2 p := rfl

def blockSpaceB {n : ℕ} {α β : Type} (b : Fin n × Fin n → ℂ)
    (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r c : α ⊕ β ≃ Fin n) :
    Submodule ℂ (ℂ × (Fin n × Fin n → ℂ)) where
  carrier := {w | w.2 ∈ L ∧ ∀ a a', w.1 * b (r (Sum.inl a), c (Sum.inr a')) +
    w.2 (r (Sum.inl a), c (Sum.inr a')) = 0}; add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨L.add_mem hx1 hy1, fun a a' => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    linear_combination hx2 a a' + hy2 a a'
  zero_mem' := ⟨L.zero_mem, fun a a' => by simp⟩
  smul_mem' := by
    rintro k x ⟨hx1, hx2⟩
    refine ⟨L.smul_mem k hx1, fun a a' => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    linear_combination k * hx2 a a'

theorem mem_blockSpaceB {n : ℕ} {α β : Type} (b : Fin n × Fin n → ℂ)
    (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r c : α ⊕ β ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) :
    w ∈ blockSpaceB b L r c ↔ w.2 ∈ L ∧ ∀ a a', w.1 * b (r (Sum.inl a), c (Sum.inr a')) +
      w.2 (r (Sum.inl a), c (Sum.inr a')) = 0 := Iff.rfl

theorem zbf_prodB {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {b : Fin n × Fin n → ℂ} {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L)
    (r c : α ⊕ β ≃ Fin n) (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpaceB b L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b w) *
      blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b w) =
      κ * (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ) w) ^ n := by
  have hw' := (mem_blockSpaceB b L r c w).mp hw
  rw [← pm_zero_block (hatB b w) r c (fun a a' => hw'.2 a a'), hatB_eq]
  exact hL.2 w.1 w.2 hw'.1

theorem zbf_ufdB {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {b : Fin n × Fin n → ℂ} {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L)
    (r c : α ⊕ β ≃ Fin n) (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c)
    (h0 : u0.1 = 1) (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpaceB b L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b w) =
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b u0) *
          w.1 ^ Fintype.card α ∧
      blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b w) =
        blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b u0) *
          w.1 ^ Fintype.card β := by
  have hpA : PolyLine (fun x : ℂ × (Fin n × Fin n → ℂ) =>
      blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b x)) :=
    polyLine_comp (hatB b) _ (polyLine_blk _ _)
  have hpB : PolyLine (fun x : ℂ × (Fin n × Fin n → ℂ) =>
      blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b x)) :=
    polyLine_comp (hatB b) _ (polyLine_blk _ _)
  constructor
  · exact ufd_unit (blockSpaceB b L r c) (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))
      (fun x => blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b x))
      (fun x => blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b x))
      hpA hpB (Fintype.card α) n
      (fun a x => by rw [map_smul]; exact blk_smul _ _ a _)
      κ hL.1 (fun x hx => zbf_prodB hL r c x hx) u0 hu0 h0 w hw
  · exact ufd_unit (blockSpaceB b L r c) (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))
      (fun x => blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b x))
      (fun x => blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b x))
      hpB hpA (Fintype.card β) n
      (fun a x => by rw [map_smul]; exact blk_smul _ _ a _)
      κ hL.1
      (fun x hx => by rw [mul_comm]; exact zbf_prodB hL r c x hx) u0 hu0 h0 w hw

theorem zbf_zeroB {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {b : Fin n × Fin n → ℂ} {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)}
    (hL : BLev b κ L) (r c : α ⊕ β ≃ Fin n) (hU : ∀ w ∈ blockSpaceB b L r c, w.1 = 0) :
    (∀ w ∈ blockSpaceB b L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b w) = 0) ∨
      (∀ w ∈ blockSpaceB b L r c,
        blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b w) = 0) := by
  refine ufd_zero (blockSpaceB b L r c)
    (fun x => blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b x))
    (fun x => blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b x))
    (polyLine_comp (hatB b) _ (polyLine_blk _ _)) (polyLine_comp (hatB b) _ (polyLine_blk _ _))
    (fun x hx => ?_)
  have h1 := zbf_prodB hL r c x hx
  rw [LinearMap.fst_apply, hU x hx, zero_pow hn, mul_zero] at h1
  exact h1

noncomputable def blockProjB {n : ℕ} {β : Type} (b : Fin n × Fin n → ℂ)
    (r c : Fin 2 ⊕ β ≃ Fin n) : ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin 2 × Fin 2 → ℂ) where
  toFun w := fun p => w.1 * b (r (Sum.inl p.1), c (Sum.inl p.2)) +
    w.2 (r (Sum.inl p.1), c (Sum.inl p.2))
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem blk_twoB {n : ℕ} {β : Type} (b : Fin n × Fin n → ℂ) (r c : Fin 2 ⊕ β ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) :
    blk (fun a : Fin 2 => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b w) =
      q0 (blockProjB b r c w) := by
  unfold blk
  rw [permanent_two]
  rfl

theorem thB_quadB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1) :
    q0 (blockProjB b r c u0) ≠ 0 ∧
      ∀ w ∈ blockSpaceB b L r c,
        q0 (blockProjB b r c w) = q0 (blockProjB b r c u0) * w.1 ^ 2 := by
  constructor
  · intro hz
    have h1 := zbf_prodB hL r c u0 hu0
    rw [blk_twoB, hz, zero_mul, LinearMap.fst_apply, h0, one_pow, mul_one] at h1
    exact hL.1 h1.symm
  · intro w hw
    have h1 := (zbf_ufdB hL r c u0 hu0 h0 w hw).1
    rw [blk_twoB, blk_twoB] at h1
    simpa using h1

theorem thB_kerB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpaceB b L r c)
    (hk : blockProjB b r c w = 0) :
    w.1 = 0 ∧ w.2 ∈ rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1)) := by
  obtain ⟨hκ, hq⟩ := thB_quadB hL r c u0 hu0 h0
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
  have hw' := (mem_blockSpaceB b L r c w).mp hw
  rw [mem_rowsZero]
  refine ⟨hw'.1, fun j => ?_, fun j => ?_⟩
  · obtain ⟨x, rfl⟩ := c.surjective j
    rcases x with a | a'
    · have h3 : w.1 * b (r (Sum.inl 0), c (Sum.inl a)) +
          w.2 (r (Sum.inl 0), c (Sum.inl a)) = 0 := congrFun hk (0, a)
      rw [hw1, zero_mul, zero_add] at h3
      exact h3
    · have h3 := hw'.2 0 a'
      rw [hw1, zero_mul, zero_add] at h3
      exact h3
  · obtain ⟨x, rfl⟩ := c.surjective j
    rcases x with a | a'
    · have h3 : w.1 * b (r (Sum.inl 1), c (Sum.inl a)) +
          w.2 (r (Sum.inl 1), c (Sum.inl a)) = 0 := congrFun hk (1, a)
      rw [hw1, zero_mul, zero_add] at h3
      exact h3
    · have h3 := hw'.2 1 a'
      rw [hw1, zero_mul, zero_add] at h3
      exact h3

theorem thB_imgB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ ((blockSpaceB b L r c).map (blockProjB b r c)) ≤ 2 := by
  obtain ⟨hκ, hq⟩ := thB_quadB hL r c u0 hu0 h0
  have hperp : ∀ v ∈ (blockSpaceB b L r c ⊓
        LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))).map (blockProjB b r c),
      ∀ z ∈ (blockSpaceB b L r c).map (blockProjB b r c), bDual v z = 0 := by
    rintro _ ⟨w, ⟨hwU, hwk⟩, rfl⟩ _ ⟨w', hw'U, rfl⟩
    have hw1 : w.1 = 0 := LinearMap.mem_ker.mp hwk
    rw [← q0_polar, ← map_add, hq w hwU, hq w' hw'U,
      hq (w + w') ((blockSpaceB b L r c).add_mem hwU hw'U), Prod.fst_add, hw1]
    ring
  have h1 := b_perp_bound _ _ hperp
  have hsup : (blockSpaceB b L r c).map (blockProjB b r c) ≤
      (blockSpaceB b L r c ⊓
        LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))).map (blockProjB b r c) ⊔
        Submodule.span ℂ {blockProjB b r c u0} := by
    rintro _ ⟨w, hwU, rfl⟩
    have hd : blockProjB b r c w =
        blockProjB b r c (w - w.1 • u0) + w.1 • blockProjB b r c u0 := by
      rw [← map_smul, ← map_add, sub_add_cancel]
    rw [hd]
    refine Submodule.add_mem_sup (Submodule.mem_map_of_mem ⟨(blockSpaceB b L r c).sub_mem hwU
      ((blockSpaceB b L r c).smul_mem _ hu0), ?_⟩)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    show (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ)) (w - w.1 • u0) = 0
    rw [map_sub, map_smul, LinearMap.fst_apply, LinearMap.fst_apply, h0,
      smul_eq_mul, mul_one, sub_self]
  have h2 := Submodule.finrank_mono hsup
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    ((blockSpaceB b L r c ⊓
      LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))).map (blockProjB b r c))
    (Submodule.span ℂ {blockProjB b r c u0})
  have h4 := finrank_span_one_le (blockProjB b r c u0)
  omega

theorem thB_dimB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ (blockSpaceB b L r c) ≤
      2 + Module.finrank ℂ (rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1))) := by
  have hrn := rank_nullity (blockSpaceB b L r c) (blockProjB b r c)
  have himg := thB_imgB hL r c u0 hu0 h0
  have hrn2 := rank_nullity (blockSpaceB b L r c ⊓ LinearMap.ker (blockProjB b r c))
    (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ))
  have hbot : (blockSpaceB b L r c ⊓ LinearMap.ker (blockProjB b r c)) ⊓
      LinearMap.ker (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ)) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨hwU, hwk⟩, hws⟩
    have hw1 := (thB_kerB hL r c u0 hu0 h0 w hwU (LinearMap.mem_ker.mp hwk)).1
    have hw2 : w.2 = 0 := LinearMap.mem_ker.mp hws
    rw [Submodule.mem_bot]
    exact Prod.ext hw1 hw2
  have hle : (blockSpaceB b L r c ⊓ LinearMap.ker (blockProjB b r c)).map
      (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ)) ≤ rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1)) := by
    rintro _ ⟨w, ⟨hwU, hwk⟩, rfl⟩
    exact (thB_kerB hL r c u0 hu0 h0 w hwU (LinearMap.mem_ker.mp hwk)).2
  have h5 := Submodule.finrank_mono hle
  rw [hbot, finrank_bot, zero_add] at hrn2
  omega

noncomputable def zeroMapB {n : ℕ} {α β : Type} (b : Fin n × Fin n → ℂ)
    (r c : α ⊕ β ≃ Fin n) : ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (α × β → ℂ) where
  toFun w := fun p => w.1 * b (r (Sum.inl p.1), c (Sum.inr p.2)) +
    w.2 (r (Sum.inl p.1), c (Sum.inr p.2))
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem blockSpaceB_finrank_ge {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (b : Fin n × Fin n → ℂ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r c : α ⊕ β ≃ Fin n) :
    Module.finrank ℂ L + 1 ≤
      Module.finrank ℂ (blockSpaceB b L r c) + Fintype.card α * Fintype.card β := by
  have hφ : Function.Injective
      (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype) := by
    intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    exact Prod.ext h1 (Subtype.ext h2)
  have h1 := rank_nullity
    (LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)) (zeroMapB b r c)
  have h2 : Module.finrank ℂ
      (LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)) =
      Module.finrank ℂ L + 1 := by
    rw [LinearMap.finrank_range_of_inj hφ, Module.finrank_prod, Module.finrank_self]
    omega
  have h3 : Module.finrank ℂ
      ((LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)).map
        (zeroMapB b r c)) ≤ Fintype.card α * Fintype.card β := by
    have h6 := Submodule.finrank_le
      ((LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype)).map
        (zeroMapB b r c))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] at h6
    exact h6
  have h4 : LinearMap.range (LinearMap.prodMap (LinearMap.id : ℂ →ₗ[ℂ] ℂ) L.subtype) ⊓
      LinearMap.ker (zeroMapB b r c) ≤ blockSpaceB b L r c := by
    rintro w ⟨⟨x, rfl⟩, hk⟩
    rw [mem_blockSpaceB]
    refine ⟨x.2.2, fun a a' => ?_⟩
    exact congrFun (LinearMap.mem_ker.mp hk) (a, a')
  have h5 := Submodule.finrank_mono h4
  omega

theorem blev_FK_row {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (c : ℂ)
    (t : Fin n × Fin n → ℂ) (ht : t ∈ L) (r : Fin n)
    (h : ∀ j, c * b (r, j) + t (r, j) = 0) : c = 0 := by
  have h1 := hL.2 c t ht
  rw [pm_zero_row _ r h] at h1
  by_contra hc
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · exact hL.1 h2
  · exact (pow_ne_zero n hc) h2

theorem row_not_mem {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L)
    (A : Submodule ℂ (Fin n × Fin n → ℂ)) (hA : A ≤ L) (r : Fin n) :
    rowMap r b ∉ A.map (rowMap r) := by
  rintro ⟨t, ht, h1⟩
  have h2 := blev_FK_row hL (-1) t (hA ht) r (fun j => by
    have h3 := congrFun h1 j
    rw [rowMap_apply, rowMap_apply] at h3
    rw [h3]
    ring)
  norm_num at h2

theorem finrank_sup_vec {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (W : Submodule ℂ V) (v : V) (h1 : v ∉ W) :
    Module.finrank ℂ (W ⊔ Submodule.span ℂ {v} : Submodule ℂ V) = Module.finrank ℂ W + 1 := by
  have hne : v ≠ 0 := by
    rintro rfl
    exact h1 W.zero_mem
  have hinf : W ⊓ Submodule.span ℂ {v} = ⊥ := by
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
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {v})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hne] at h
  exact h

theorem row_surjB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L)
    (v : Fin (m + 2) → ℂ) :
    ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧ ∃ γ : ℂ, ∀ j, v j = a (r1, j) + γ * b (r1, j) := by
  have h5 : Module.finrank ℂ (Fin (m + 2) → ℂ) = m + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hW2 : Module.finrank ℂ (L.map (rowMap r2)) ≤ m + 1 := by
    have h1 := finrank_sup_vec _ _ (row_not_mem hL L le_rfl r2)
    have h2 := Submodule.finrank_le
      (L.map (rowMap r2) ⊔ Submodule.span ℂ {rowMap r2 b})
    rw [h5] at h2
    omega
  have hA := rank_nullity L (rowMap r2)
  have hA2 := rank_nullity (L ⊓ LinearMap.ker (rowMap r2)) (rowMap r1)
  have hX : (L ⊓ LinearMap.ker (rowMap r2)) ⊓ LinearMap.ker (rowMap r1) = rowsZero L r1 r2 := by
    unfold rowsZero
    exact inf_right_comm _ _ _
  rw [hX] at hA2
  have h1 := finrank_sup_vec _ _
    (row_not_mem hL (L ⊓ LinearMap.ker (rowMap r2)) inf_le_left r1)
  have h2 := Submodule.finrank_le ((L ⊓ LinearMap.ker (rowMap r2)).map (rowMap r1) ⊔
    Submodule.span ℂ {rowMap r1 b})
  rw [h5] at h2
  have htop : (L ⊓ LinearMap.ker (rowMap r2)).map (rowMap r1) ⊔
      Submodule.span ℂ {rowMap r1 b} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h5]
    omega
  have hv : v ∈ (L ⊓ LinearMap.ker (rowMap r2)).map (rowMap r1) ⊔
      Submodule.span ℂ {rowMap r1 b} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have ha' := Submodule.mem_inf.mp ha
  refine ⟨a, ha'.1, fun j => congrFun (LinearMap.mem_ker.mp ha'.2) j, γ, fun j => ?_⟩
  rw [← hyz]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rowMap_apply]

theorem exists_colB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L) :
    ∃ k : Fin (m + 2), ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧
      ∀ j, j ≠ k → b (r1, j) + a (r1, j) = 0 := by
  by_contra hcon
  have hall : ∀ k : Fin (m + 2), ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧
      ∀ j, (Pi.single k 1 : Fin (m + 2) → ℂ) j = a (r1, j) := by
    intro k
    obtain ⟨a, haL, ha2, γ, hγ⟩ := row_surjB hL r1 r2 hd (Pi.single k 1)
    by_cases hg : γ = 0
    · exact ⟨a, haL, ha2, fun j => by rw [hγ j, hg, zero_mul, add_zero]⟩
    · exfalso
      apply hcon
      refine ⟨k, γ⁻¹ • a, L.smul_mem _ haL, fun j => by simp [ha2 j], fun j hj => ?_⟩
      have h1 := hγ j
      rw [Pi.single_apply, if_neg hj] at h1
      have h3 : a (r1, j) = -(γ * b (r1, j)) := by linear_combination -h1
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h3, mul_neg, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
      ring
  choose a haL ha2 ha1 using hall
  have h2 := blev_FK_row hL (-1) (∑ k, b (r1, k) • a k)
    (L.sum_mem fun k _ => L.smul_mem _ (haL k)) r1 (fun j => by
    rw [Finset.sum_apply]
    have h4 : ∑ k, (b (r1, k) • a k) (r1, j) =
        ∑ k, b (r1, k) * (Pi.single k 1 : Fin (m + 2) → ℂ) j :=
      Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, ha1 k j]
    rw [h4]
    simp [Pi.single_apply])
  norm_num at h2

theorem lemmaC_genB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (r1 r2 : Fin (m + 2)) (hr : r1 ≠ r2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 1) := by
  by_contra hcon
  have hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L := by omega
  have hd' : Module.finrank ℂ (rowsZero L r2 r1) + (2 * m + 2) ≤ Module.finrank ℂ L := by
    rw [rowsZero_comm]
    exact hd
  obtain ⟨k1, a, haL, ha2, ha1⟩ := exists_colB hL r1 r2 hd
  obtain ⟨k2, a2, hbL, hb1, hb2⟩ := exists_colB hL r2 r1 hd'
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_perm2 r1 r2 hr
  obtain ⟨κ', hκ⟩ := exists_col_perm k1 k2
  have hr0 : ((e2m m).trans ρ) (Sum.inl 0) = r1 := by
    rw [Equiv.trans_apply, e2m_inl0, hρ0]
  have hr1 : ((e2m m).trans ρ) (Sum.inl 1) = r2 := by
    rw [Equiv.trans_apply, e2m_inl1, hρ1]
  have hu0 : ((1 : ℂ), a + a2) ∈ blockSpaceB b L ((e2m m).trans ρ) ((e2m m).trans κ') := by
    rw [mem_blockSpaceB]
    refine ⟨L.add_mem haL hbL, fun a' b' => ?_⟩
    have hc1 : ((e2m m).trans κ') (Sum.inr b') ≠ k1 := by
      intro h1
      exact e2m_inr m b' (hκ (e2m m (Sum.inr b')) (Or.inl h1))
    have hc2 : ((e2m m).trans κ') (Sum.inr b') ≠ k2 := by
      intro h1
      exact e2m_inr m b' (hκ (e2m m (Sum.inr b')) (Or.inr h1))
    have hboth : ∀ a'' : Fin 2, (1 : ℂ) *
        b (((e2m m).trans ρ) (Sum.inl a''), ((e2m m).trans κ') (Sum.inr b')) +
        (a + a2) (((e2m m).trans ρ) (Sum.inl a''), ((e2m m).trans κ') (Sum.inr b')) = 0 := by
      rw [Fin.forall_fin_two]
      constructor
      · rw [hr0, Pi.add_apply, hb1, add_zero, one_mul]
        exact ha1 _ hc1
      · rw [hr1, Pi.add_apply, ha2, zero_add, one_mul]
        exact hb2 _ hc2
    exact hboth a'
  have hB := thB_dimB hL ((e2m m).trans ρ) ((e2m m).trans κ') (1, a + a2) hu0 rfl
  rw [hr0, hr1] at hB
  have hlow := blockSpaceB_finrank_ge b L ((e2m m).trans ρ) ((e2m m).trans κ')
  simp only [Fintype.card_fin] at hlow
  omega

theorem blev_tr {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) :
    BLev (trE n b) κ (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))) := by
  refine ⟨hL.1, ?_⟩
  rintro c _ ⟨t, ht, rfl⟩
  have h1 := pm_tr (fun p => c * b p + t p)
  rw [← hL.2 c t ht, ← h1]
  rfl

theorem lemmaC_col_genB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (c1 c2 : Fin (m + 2)) (hc : c1 ≠ c2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (colsZero L c1 c2) + (2 * m + 1) := by
  have h1 := lemmaC_genB (blev_tr hL) c1 c2 hc
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

theorem exists_sub_finrank {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (W : Submodule ℂ V) (k : ℕ) (hk : k ≤ Module.finrank ℂ W) :
    ∃ W' : Submodule ℂ V, W' ≤ W ∧ Module.finrank ℂ W' = k := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hk
  refine ⟨(Submodule.span ℂ (Set.range f)).map W.subtype, Submodule.map_subtype_le W _, ?_⟩
  rw [Submodule.finrank_map_subtype_eq, finrank_span_eq_card hf, Fintype.card_fin]

theorem n3p_row {b : Fin 3 × Fin 3 → ℂ} {κ : ℂ} {V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)}
    (hL : BLev b κ V0) (h4 : 4 ≤ Module.finrank ℂ V0) (r3 : Fin 3) :
    ∃ x ∈ V0, x ≠ 0 ∧ ∀ i j, i ≠ r3 → x (i, j) = 0 := by
  obtain ⟨r1, r2, h12, hall⟩ := n3_others r3
  have h : Module.finrank ℂ V0 ≤ Module.finrank ℂ (rowsZero V0 r1 r2) + 3 :=
    lemmaC_genB (m := 1) hL r1 r2 h12
  have hpos : 0 < Module.finrank ℂ (rowsZero V0 r1 r2) := by omega
  obtain ⟨⟨x, hxm⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨hxL, hx1, hx2⟩ := (mem_rowsZero V0 r1 r2 x).mp hxm
  refine ⟨x, hxL, ?_, fun i j hi => ?_⟩
  · intro h0
    apply hx0
    exact Subtype.ext h0
  · rcases hall i hi with rfl | rfl
    · exact hx1 j
    · exact hx2 j

theorem n3p_col {b : Fin 3 × Fin 3 → ℂ} {κ : ℂ} {V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)}
    (hL : BLev b κ V0) (h4 : 4 ≤ Module.finrank ℂ V0) (c3 : Fin 3) :
    ∃ y ∈ V0, y ≠ 0 ∧ ∀ i j, j ≠ c3 → y (i, j) = 0 := by
  obtain ⟨c1, c2, h12, hall⟩ := n3_others c3
  have h : Module.finrank ℂ V0 ≤ Module.finrank ℂ (colsZero V0 c1 c2) + 3 :=
    lemmaC_col_genB (m := 1) hL c1 c2 h12
  have hpos : 0 < Module.finrank ℂ (colsZero V0 c1 c2) := by omega
  obtain ⟨⟨y, hym⟩, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨hyL, hy1, hy2⟩ := (mem_colsZero V0 c1 c2 y).mp hym
  refine ⟨y, hyL, ?_, fun i j hj => ?_⟩
  · intro h0
    apply hy0
    exact Subtype.ext h0
  · rcases hall j hj with rfl | rfl
    · exact hy1 i
    · exact hy2 i

def N3Core : Prop :=
  ∀ (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)), pm b ≠ 0 →
    (∀ η ∈ V0, pm (b + η) = pm b) → Module.finrank ℂ V0 = 4 →
    (∀ r : Fin 3, ∃ x ∈ V0, x ≠ 0 ∧ ∀ i j, i ≠ r → x (i, j) = 0) →
    (∀ c : Fin 3, ∃ y ∈ V0, y ≠ 0 ∧ ∀ i j, j ≠ c → y (i, j) = 0) → False

theorem n3prime_of_core (hcore : N3Core) (b : Fin 3 × Fin 3 → ℂ)
    (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)) (hb : pm b ≠ 0)
    (h : ∀ η ∈ V0, pm (b + η) = pm b) : Module.finrank ℂ V0 ≤ 3 := by
  by_contra hcon
  obtain ⟨V1, hV1, hd⟩ := exists_sub_finrank V0 4 (by omega)
  have h1 : ∀ η ∈ V1, pm (b + η) = pm b := fun η hη => h η (hV1 hη)
  have hL := blev_of_const b V1 hb h1
  exact hcore b V1 hb h1 hd (fun r => n3p_row hL (by omega) r) (fun c => n3p_col hL (by omega) c)

noncomputable def blockProj3 {n : ℕ} {α : Type} (r c : α ⊕ Fin 3 ≃ Fin n) :
    ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) where
  toFun w := fun p => w.1 + w.2 (r (Sum.inr p.1), c (Sum.inr p.2))
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem blk_three {n : ℕ} {α : Type} (r c : α ⊕ Fin 3 ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) :
    blk (fun b : Fin 3 => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) =
      pm (blockProj3 r c w) := rfl

def colsOff {n : ℕ} {α β : Type} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (c : α ⊕ β ≃ Fin n) : Submodule ℂ (Fin n × Fin n → ℂ) where
  carrier := {t | t ∈ L ∧ ∀ (i : Fin n) (a' : β), t (i, c (Sum.inr a')) = 0}; add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨L.add_mem hx1 hy1, fun i a' => ?_⟩
    rw [Pi.add_apply, hx2 i a', hy2 i a', add_zero]
  zero_mem' := ⟨L.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro k x ⟨hx1, hx2⟩
    refine ⟨L.smul_mem k hx1, fun i a' => ?_⟩
    rw [Pi.smul_apply, hx2 i a', smul_zero]

theorem n3prime_L {α : Type} [Fintype α] [DecidableEq α]
    (hN3 : ∀ (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)), pm b ≠ 0 →
      (∀ η ∈ V0, pm (b + η) = pm b) → Module.finrank ℂ V0 ≤ 3)
    {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ Fin 3 ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ (blockSpace L r c ⊓
        LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ)) : Submodule ℂ _) ≤
      3 + Module.finrank ℂ (colsOff L c) := by
  have hb : pm (blockProj3 r c u0) ≠ 0 := by
    intro hz
    have h1 := zbf_prod hL r c u0 hu0
    rw [blk_three, hz, mul_zero, LinearMap.fst_apply, h0, one_pow, mul_one] at h1
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h1.symm
  have himg : Module.finrank ℂ ((blockSpace L r c ⊓
      LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))).map (blockProj3 r c)) ≤ 3 := by
    apply hN3 (blockProj3 r c u0) _ hb
    rintro _ ⟨w, ⟨hwU, hwk⟩, rfl⟩
    have hw1 : w.1 = 0 := LinearMap.mem_ker.mp hwk
    have h2 := (zbf_lineality hL r c u0 hu0 h0 u0 hu0 w hwU hw1).2
    rw [blk_three, blk_three, map_add] at h2
    exact h2
  have hrn := rank_nullity (blockSpace L r c ⊓
    LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))) (blockProj3 r c)
  have hrn2 := rank_nullity ((blockSpace L r c ⊓
    LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))) ⊓ LinearMap.ker (blockProj3 r c))
    (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ))
  have hbot : ((blockSpace L r c ⊓ LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))) ⊓
      LinearMap.ker (blockProj3 r c)) ⊓
      LinearMap.ker (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ)) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨⟨hwU, hwk⟩, hwp⟩, hws⟩
    rw [Submodule.mem_bot]
    exact Prod.ext (LinearMap.mem_ker.mp hwk) (LinearMap.mem_ker.mp hws)
  have hle : ((blockSpace L r c ⊓ LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ))) ⊓
      LinearMap.ker (blockProj3 r c)).map (LinearMap.snd ℂ ℂ (Fin n × Fin n → ℂ)) ≤
      colsOff L c := by
    rintro _ ⟨w, ⟨⟨hwU, hwk⟩, hwp⟩, rfl⟩
    have hw1 : w.1 = 0 := LinearMap.mem_ker.mp hwk
    have hw' := (mem_blockSpace L r c w).mp hwU
    refine ⟨hw'.1, fun i a' => ?_⟩
    obtain ⟨x, rfl⟩ := r.surjective i
    rcases x with a | b'
    · have h3 := hw'.2 a a'
      rw [hw1, zero_add] at h3
      exact h3
    · have h3 : w.1 + w.2 (r (Sum.inr b'), c (Sum.inr a')) = 0 :=
        congrFun (LinearMap.mem_ker.mp hwp) (b', a')
      rw [hw1, zero_add] at h3
      exact h3
  have h5 := Submodule.finrank_mono hle
  rw [hbot, finrank_bot, zero_add] at hrn2
  omega

def rowsZeroS {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S : Finset (Fin n)) :
    Submodule ℂ (Fin n × Fin n → ℂ) where
  carrier := {t | t ∈ L ∧ ∀ r ∈ S, ∀ j, t (r, j) = 0}; add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨L.add_mem hx1 hy1, fun r hr j => ?_⟩
    rw [Pi.add_apply, hx2 r hr j, hy2 r hr j, add_zero]
  zero_mem' := ⟨L.zero_mem, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro k x ⟨hx1, hx2⟩
    refine ⟨L.smul_mem k hx1, fun r hr j => ?_⟩
    rw [Pi.smul_apply, hx2 r hr j, smul_zero]

theorem mem_rowsZeroS {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S : Finset (Fin n))
    (t : Fin n × Fin n → ℂ) :
    t ∈ rowsZeroS L S ↔ t ∈ L ∧ ∀ r ∈ S, ∀ j, t (r, j) = 0 := Iff.rfl

theorem rowsZeroS_inf {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S S' : Finset (Fin n)) :
    rowsZeroS L S ⊓ rowsZeroS L S' = rowsZeroS L (S ∪ S') := by
  ext t
  rw [Submodule.mem_inf, mem_rowsZeroS, mem_rowsZeroS, mem_rowsZeroS]
  constructor
  · rintro ⟨⟨h1, h2⟩, _, h3⟩
    refine ⟨h1, fun r hr j => ?_⟩
    rcases Finset.mem_union.mp hr with h | h
    · exact h2 r h j
    · exact h3 r h j
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun r hr j => h2 r (Finset.mem_union_left _ hr) j⟩, h1,
      fun r hr j => h2 r (Finset.mem_union_right _ hr) j⟩

theorem rowsZeroS_sup_le {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (S S' : Finset (Fin n)) : rowsZeroS L S ⊔ rowsZeroS L S' ≤ rowsZeroS L (S ∩ S') := by
  apply sup_le
  · rintro t ⟨h1, h2⟩
    exact ⟨h1, fun r hr j => h2 r (Finset.mem_of_mem_inter_left hr) j⟩
  · rintro t ⟨h1, h2⟩
    exact ⟨h1, fun r hr j => h2 r (Finset.mem_of_mem_inter_right hr) j⟩

theorem rows_submodular {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S S' : Finset (Fin n)) :
    Module.finrank ℂ (rowsZeroS L S) + Module.finrank ℂ (rowsZeroS L S') ≤
      Module.finrank ℂ (rowsZeroS L (S ∩ S')) + Module.finrank ℂ (rowsZeroS L (S ∪ S')) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (rowsZeroS L S) (rowsZeroS L S')
  rw [rowsZeroS_inf] at h1
  have h2 := Submodule.finrank_mono (rowsZeroS_sup_le L S S')
  omega

theorem rowsZeroS_empty {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    rowsZeroS L (∅ : Finset (Fin n)) = L := by
  ext t
  rw [mem_rowsZeroS]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun r hr => by simp at hr⟩

theorem rowsZeroS_pair {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    rowsZeroS L {r1, r2} = rowsZero L r1 r2 := by
  ext t
  rw [mem_rowsZeroS, mem_rowsZero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 r1 (by simp), h2 r2 (by simp)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun r hr j => ?_⟩
    rcases Finset.mem_insert.mp hr with h | h
    · rw [h]
      exact h2 j
    · rw [Finset.mem_singleton.mp h]
      exact h3 j

theorem rowsZeroS_mono {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) {S S' : Finset (Fin n)}
    (h : S ⊆ S') : rowsZeroS L S' ≤ rowsZeroS L S := by
  rintro t ⟨h1, h2⟩
  exact ⟨h1, fun r hr j => h2 r (h hr) j⟩

theorem rowsZeroS_insert {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S : Finset (Fin n))
    (r : Fin n) : rowsZeroS L S ⊓ LinearMap.ker (rowMap r) = rowsZeroS L (insert r S) := by
  ext t
  rw [Submodule.mem_inf, LinearMap.mem_ker, mem_rowsZeroS, mem_rowsZeroS]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun r' hr' j => ?_⟩
    rcases Finset.mem_insert.mp hr' with h | h
    · rw [h]
      exact congrFun h3 j
    · exact h2 r' h j
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun r' hr' j => h2 r' (Finset.mem_insert_of_mem hr') j⟩,
      funext fun j => h2 r (Finset.mem_insert_self r S) j⟩

theorem rows_rank {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S : Finset (Fin n))
    (r : Fin n) :
    Module.finrank ℂ (rowsZeroS L S) = Module.finrank ℂ (rowsZeroS L (insert r S)) +
      Module.finrank ℂ ((rowsZeroS L S).map (rowMap r)) := by
  have h := rank_nullity (rowsZeroS L S) (rowMap r)
  rw [rowsZeroS_insert] at h
  exact h

theorem rows_inj_bound {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S S' : Finset (Fin n))
    (c : Fin n) (hSS : S' ⊆ S) (h0 : rowsZeroS L (insert c S) = ⊥) :
    Module.finrank ℂ (rowsZeroS L S) + Module.finrank ℂ (rowsZeroS L (insert c S')) ≤
      Module.finrank ℂ (rowsZeroS L S') := by
  have h1 := rows_rank L S c
  have h2 := rows_rank L S' c
  have h3 : Module.finrank ℂ ((rowsZeroS L S).map (rowMap c)) ≤
      Module.finrank ℂ ((rowsZeroS L S').map (rowMap c)) :=
    Submodule.finrank_mono (Submodule.map_mono (rowsZeroS_mono L hSS))
  rw [h0, finrank_bot] at h1
  omega

theorem rows_disjoint_bound {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (S S' : Finset (Fin n)) (h0 : rowsZeroS L (S ∪ S') = ⊥) :
    Module.finrank ℂ (rowsZeroS L S) + Module.finrank ℂ (rowsZeroS L S') ≤
      Module.finrank ℂ (rowsZeroS L (S ∩ S')) := by
  have h := rows_submodular L S S'
  rw [h0, finrank_bot] at h
  omega

noncomputable def dS (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S : Finset (Fin 5)) : ℕ :=
  Module.finrank ℂ (rowsZeroS L (S.map ρ.toEmbedding))

theorem dS_submodular (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S S' : Finset (Fin 5)) :
    dS L ρ S + dS L ρ S' ≤ dS L ρ (S ∩ S') + dS L ρ (S ∪ S') := by
  unfold dS
  rw [Finset.map_inter, Finset.map_union]
  exact rows_submodular L _ _

theorem dS_inj_bound (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S S' : Finset (Fin 5)) (c : Fin 5) (hSS : S' ⊆ S) (h0 : dS L ρ (insert c S) = 0) :
    dS L ρ S + dS L ρ (insert c S') ≤ dS L ρ S' := by
  unfold dS at h0 ⊢
  rw [Finset.map_insert] at h0 ⊢
  have hbot : rowsZeroS L (insert (ρ.toEmbedding c) (S.map ρ.toEmbedding)) = ⊥ :=
    Submodule.finrank_eq_zero.mp h0
  exact rows_inj_bound L _ _ _ (Finset.map_subset_map.mpr hSS) hbot

theorem dS_disjoint_bound (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S S' : Finset (Fin 5)) (h0 : dS L ρ (S ∪ S') = 0) :
    dS L ρ S + dS L ρ S' ≤ dS L ρ (S ∩ S') := by
  have h := dS_submodular L ρ S S'
  omega

theorem stage3_G2 (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (ha : ∀ i : Fin 5, dS L ρ {i} = 5)
    (hz : ∀ S : Finset (Fin 5), S.card = 4 → dS L ρ S = 0)
    (hlam : ∀ S : Finset (Fin 5), S.card = 2 → 3 ≤ dS L ρ S)
    (h4 : 4 ≤ dS L ρ {0, 1}) :
    dS L ρ {0, 1, 4} = 2 ∧ dS L ρ {0, 1, 3} = 2 ∧ dS L ρ {0, 1, 2} = 2 ∧
      ∀ S : Finset (Fin 5), S.card = 2 → S ≠ {0, 1} → dS L ρ S = 3 := by
  have hl4 := dS_submodular L ρ {0, 1} {0, 4}
  rw [show (({0, 1} : Finset (Fin 5)) ∩ {0, 4}) = {0} by decide,
    show (({0, 1} : Finset (Fin 5)) ∪ {0, 4}) = {0, 1, 4} by decide] at hl4
  have hp4 := hlam {0, 4} (by decide)
  have hl3 := dS_submodular L ρ {0, 1} {0, 3}
  rw [show (({0, 1} : Finset (Fin 5)) ∩ {0, 3}) = {0} by decide,
    show (({0, 1} : Finset (Fin 5)) ∪ {0, 3}) = {0, 1, 3} by decide] at hl3
  have hp3 := hlam {0, 3} (by decide)
  have hl2 := dS_submodular L ρ {0, 1} {0, 2}
  rw [show (({0, 1} : Finset (Fin 5)) ∩ {0, 2}) = {0} by decide,
    show (({0, 1} : Finset (Fin 5)) ∪ {0, 2}) = {0, 1, 2} by decide] at hl2
  have hp2 := hlam {0, 2} (by decide)
  have ha0 := ha 0
  have hi1 := dS_inj_bound L ρ {0, 1, 4} {0} 2 (by decide) (hz _ (by decide))
  have hq1 := hlam (insert 2 {0}) (by decide)
  have hr1 := ha 0
  have hi2 := dS_inj_bound L ρ {0, 1, 4} {1} 2 (by decide) (hz _ (by decide))
  have hq2 := hlam (insert 2 {1}) (by decide)
  have hr2 := ha 1
  have hi3 := dS_inj_bound L ρ {0, 1, 4} {4} 2 (by decide) (hz _ (by decide))
  have hq3 := hlam (insert 2 {4}) (by decide)
  have hr3 := ha 4
  have hi4 := dS_inj_bound L ρ {0, 1, 4} {0} 3 (by decide) (hz _ (by decide))
  have hq4 := hlam (insert 3 {0}) (by decide)
  have hr4 := ha 0
  have hi5 := dS_inj_bound L ρ {0, 1, 4} {1} 3 (by decide) (hz _ (by decide))
  have hq5 := hlam (insert 3 {1}) (by decide)
  have hr5 := ha 1
  have hi6 := dS_inj_bound L ρ {0, 1, 4} {4} 3 (by decide) (hz _ (by decide))
  have hq6 := hlam (insert 3 {4}) (by decide)
  have hr6 := ha 4
  have hi7 := dS_inj_bound L ρ {0, 1, 3} {3} 2 (by decide) (hz _ (by decide))
  have hq7 := hlam (insert 2 {3}) (by decide)
  have hr7 := ha 3
  have hi8 := dS_inj_bound L ρ {0, 1, 3} {0} 4 (by decide) (hz _ (by decide))
  have hq8 := hlam (insert 4 {0}) (by decide)
  have hr8 := ha 0
  have hi9 := dS_inj_bound L ρ {0, 1, 3} {1} 4 (by decide) (hz _ (by decide))
  have hq9 := hlam (insert 4 {1}) (by decide)
  have hr9 := ha 1
  have hi10 := dS_inj_bound L ρ {0, 1, 3} {3} 4 (by decide) (hz _ (by decide))
  have hq10 := hlam (insert 4 {3}) (by decide)
  have hr10 := ha 3
  have hi11 := dS_inj_bound L ρ {0, 1, 2} {2} 4 (by decide) (hz _ (by decide))
  have hq11 := hlam (insert 4 {2}) (by decide)
  have hr11 := ha 2
  refine ⟨by omega, by omega, by omega, fun S hS hne => ?_⟩
  have hcases : S = insert 2 {0} ∨ S = insert 2 {1} ∨ S = insert 2 {4} ∨ S = insert 3 {0} ∨ S = insert 3 {1} ∨ S = insert 3 {4} ∨ S = insert 2 {3} ∨ S = insert 4 {0} ∨ S = insert 4 {1} ∨ S = insert 4 {3} ∨ S = insert 4 {2} := by
    revert S
    decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem blev_line {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (c s : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) :
    pm (fun p => c * b p + t p + s * x p) = κ * c ^ n := by
  have h := hL.2 c (t + s • x) (L.add_mem ht (L.smul_mem s hx))
  have e : (fun p => c * b p + t p + s * x p) = (fun p => c * b p + (t + s • x) p) := by
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, h]

theorem blev_mix {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (c : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    mix m (fun p => c * b p + t p) x = 0 := by
  refine poly_coeff_zero (fun m => mix m (fun p => c * b p + t p) x) n
    (κ * c ^ n) (fun s => ?_) m hm1 hmn
  show ∑ m ∈ range (n + 1), s ^ m * mix m (fun p => c * b p + t p) x = κ * c ^ n
  rw [← pm_line_expand, ← blev_line hL c s t x ht hx]
  congr 1

theorem blev_rows {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L)
    (R : Finset (Fin n)) (hR : R.Nonempty) (x : Fin n × Fin n → ℂ) (hx : x ∈ L)
    (hx0 : ∀ i, i ∉ R → ∀ j, x (i, j) = 0) (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => if p.1 ∈ R then x p else c * b p + t p) = 0 := by
  have h := blev_mix hL c t x ht hx R.card (Finset.card_pos.mpr hR) (by
    have h1 := Finset.card_le_univ R
    rwa [Fintype.card_fin] at h1)
  rw [mix_eq_sum_pm, Finset.sum_eq_single R] at h
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
    show (if a ∈ A then x (a, j) else c * b (a, j) + t (a, j)) = 0
    rw [if_pos ha]
    exact hx0 a haR j
  · intro hR'
    exact (hR' (Finset.mem_filter.mpr ⟨Finset.mem_univ R, rfl⟩)).elim

def maskAT {n : ℕ} (A T : Finset (Fin n)) (u : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => if (p.1 ∈ A ↔ p.2 ∈ T) then u p else 0

theorem pm_mask_term {n : ℕ} (A T : Finset (Fin n)) (u : Fin n × Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (hT : T ≠ A.map σ.toEmbedding) :
    ∏ i, maskAT A T u (i, σ i) = 0 := by
  have hex : ∃ i, ¬ (i ∈ A ↔ σ i ∈ T) := by
    by_contra hcon
    have hall : ∀ i, (i ∈ A ↔ σ i ∈ T) := by
      intro i
      by_contra h
      exact hcon ⟨i, h⟩
    apply hT
    ext j
    constructor
    · intro hj
      have h1 : σ.symm j ∈ A := (hall (σ.symm j)).mpr (by
        rw [Equiv.apply_symm_apply]
        exact hj)
      exact Finset.mem_map.mpr ⟨σ.symm j, h1, Equiv.apply_symm_apply σ j⟩
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      exact (hall i).mp hi
  obtain ⟨i, hi⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem pm_mask_sum {n : ℕ} (A : Finset (Fin n)) (u : Fin n × Fin n → ℂ) :
    pm u = ∑ T : Finset (Fin n), pm (maskAT A T u) := by
  simp_rw [pm_perm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single (A.map σ.toEmbedding)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hc : (i ∈ A ↔ σ i ∈ A.map σ.toEmbedding) := (Finset.mem_map' σ.toEmbedding).symm
    exact (if_pos hc).symm
  · intro T _ hT
    exact pm_mask_term A T u σ hT
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem pm_mask_zero {n : ℕ} (A T : Finset (Fin n)) (u : Fin n × Fin n → ℂ)
    (h : T.card ≠ A.card) : pm (maskAT A T u) = 0 := by
  rw [pm_perm]
  refine Finset.sum_eq_zero fun σ _ => pm_mask_term A T u σ ?_
  rintro rfl
  exact h (Finset.card_map _)

theorem blk_congr {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (u v : Fin n × Fin n → ℂ) (h : ∀ i j, u (ρ i, κ j) = v (ρ i, κ j)) :
    blk ρ κ u = blk ρ κ v := by
  unfold blk
  congr 1
  ext i j
  exact h i j

theorem pm_mask_factor {n : ℕ} (A Z : Finset (Fin n)) (u : Fin n × Fin n → ℂ)
    (eS : {x // x ∈ A} ≃ {x // x ∉ Z}) (eZ : {x // x ∉ A} ≃ {x // x ∈ Z}) :
    pm (maskAT A Zᶜ u) =
      blk (fun a : {x // x ∈ A} => (a : Fin n)) (fun a => ((eS a : {x // x ∉ Z}) : Fin n)) u *
        blk (fun a' : {x // x ∉ A} => (a' : Fin n))
          (fun a' => ((eZ a' : {x // x ∈ Z}) : Fin n)) u := by
  rw [pm_zero_block_sets (maskAT A Zᶜ u) A Z eS eZ
    (fun i hi j hj => if_neg (fun h => (Finset.mem_compl.mp (h.mp hi)) hj))]
  congr 1
  · refine blk_congr _ _ _ _ fun i j => ?_
    exact if_pos ⟨fun _ => Finset.mem_compl.mpr (eS j).2, fun _ => i.2⟩
  · refine blk_congr _ _ _ _ fun i j => ?_
    exact if_pos ⟨fun h => absurd h i.2, fun h => absurd (eZ j).2 (Finset.mem_compl.mp h)⟩

theorem thG_masked {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c1 c2 : ℂ) (t1 t2 : Fin n × Fin n → ℂ) (h1 : t1 ∈ L) (h2 : t2 ∈ L) (m : ℕ) (hmn : m ≤ n) :
    ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      ∑ T : Finset (Fin n),
        pm (maskAT A T (fun p => if p.1 ∈ A then c2 + t2 p else c1 + t1 p)) =
      (Nat.factorial n : ℂ) * ((n.choose m : ℂ) * c1 ^ (n - m) * c2 ^ m) := by
  rw [← lev_mix_hat hL c1 c2 t1 t2 h1 h2 m hmn, mix_eq_sum_pm]
  refine Finset.sum_congr rfl fun A _ => ?_
  exact (pm_mask_sum A _).symm

theorem thG_term {n : ℕ} (A Z : Finset (Fin n)) (u v : Fin n × Fin n → ℂ)
    (eS : {x // x ∈ A} ≃ {x // x ∉ Z}) (eZ : {x // x ∉ A} ≃ {x // x ∈ Z}) :
    pm (maskAT A Zᶜ (fun p => if p.1 ∈ A then v p else u p)) =
      blk (fun a : {x // x ∈ A} => (a : Fin n)) (fun a => ((eS a : {x // x ∉ Z}) : Fin n)) v *
        blk (fun a' : {x // x ∉ A} => (a' : Fin n))
          (fun a' => ((eZ a' : {x // x ∈ Z}) : Fin n)) u := by
  rw [pm_mask_factor A Z _ eS eZ]
  congr 1
  · refine blk_congr _ _ _ _ fun i j => ?_
    exact if_pos i.2
  · refine blk_congr _ _ _ _ fun i j => ?_
    exact if_neg i.2

theorem rowsZeroS_all_bot (L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)) :
    rowsZeroS L ({0, 1, 2} : Finset (Fin 3)) = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨_, h2⟩
  rw [Submodule.mem_bot]
  funext p
  obtain ⟨i, j⟩ := p
  exact h2 i (by revert i; decide) j

theorem n3prime_weak (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (hb : pm b ≠ 0) (h : ∀ η ∈ V0, pm (b + η) = pm b) : Module.finrank ℂ V0 ≤ 4 := by
  by_contra hcon
  obtain ⟨V1, hV1, hd⟩ := exists_sub_finrank V0 5 (by omega)
  have hL := blev_of_const b V1 hb (fun η hη => h η (hV1 hη))
  have ha : Module.finrank ℂ V1 ≤ Module.finrank ℂ (rowsZero V1 1 2) + 3 :=
    lemmaC_genB (m := 1) hL 1 2 (by decide)
  have hb' : Module.finrank ℂ V1 ≤ Module.finrank ℂ (rowsZero V1 0 2) + 3 :=
    lemmaC_genB (m := 1) hL 0 2 (by decide)
  have hc : Module.finrank ℂ V1 ≤ Module.finrank ℂ (rowsZero V1 0 1) + 3 :=
    lemmaC_genB (m := 1) hL 0 1 (by decide)
  rw [← rowsZeroS_pair] at ha hb' hc
  have s1 := rows_submodular V1 {1, 2} {0, 2}
  have s2 := rows_submodular V1 {2} {0, 1}
  rw [show (({1, 2} : Finset (Fin 3)) ∩ {0, 2}) = {2} by decide,
    show (({1, 2} : Finset (Fin 3)) ∪ {0, 2}) = {0, 1, 2} by decide,
    rowsZeroS_all_bot, finrank_bot] at s1
  rw [show (({2} : Finset (Fin 3)) ∩ {0, 1}) = ∅ by decide,
    show (({2} : Finset (Fin 3)) ∪ {0, 1}) = {0, 1, 2} by decide,
    rowsZeroS_all_bot, finrank_bot, rowsZeroS_empty] at s2
  omega

def cellsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (K : Finset (Fin n × Fin n)) :
    Submodule ℂ (Fin n × Fin n → ℂ) where
  carrier := {t | t ∈ L ∧ ∀ p ∈ K, t p = 0}; add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨L.add_mem hx1 hy1, fun p hp => ?_⟩
    rw [Pi.add_apply, hx2 p hp, hy2 p hp, add_zero]
  zero_mem' := ⟨L.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro k x ⟨hx1, hx2⟩
    refine ⟨L.smul_mem k hx1, fun p hp => ?_⟩
    rw [Pi.smul_apply, hx2 p hp, smul_zero]

theorem mem_cellsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (K : Finset (Fin n × Fin n)) (t : Fin n × Fin n → ℂ) :
    t ∈ cellsZero L K ↔ t ∈ L ∧ ∀ p ∈ K, t p = 0 := Iff.rfl

theorem cells_submodular {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (K K' : Finset (Fin n × Fin n)) :
    Module.finrank ℂ (cellsZero L K) + Module.finrank ℂ (cellsZero L K') ≤
      Module.finrank ℂ (cellsZero L (K ∩ K')) + Module.finrank ℂ (cellsZero L (K ∪ K')) := by
  have hinf : cellsZero L K ⊓ cellsZero L K' = cellsZero L (K ∪ K') := by
    ext t
    rw [Submodule.mem_inf, mem_cellsZero, mem_cellsZero, mem_cellsZero]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h3⟩
      refine ⟨h1, fun p hp => ?_⟩
      rcases Finset.mem_union.mp hp with h | h
      · exact h2 p h
      · exact h3 p h
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun p hp => h2 p (Finset.mem_union_left _ hp)⟩, h1,
        fun p hp => h2 p (Finset.mem_union_right _ hp)⟩
  have hsup : cellsZero L K ⊔ cellsZero L K' ≤ cellsZero L (K ∩ K') := by
    apply sup_le
    · rintro t ⟨h1, h2⟩
      exact ⟨h1, fun p hp => h2 p (Finset.mem_of_mem_inter_left hp)⟩
    · rintro t ⟨h1, h2⟩
      exact ⟨h1, fun p hp => h2 p (Finset.mem_of_mem_inter_right hp)⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (cellsZero L K) (cellsZero L K')
  rw [hinf] at h1
  have h2 := Submodule.finrank_mono hsup
  omega

def cellProj {n : ℕ} (K : Finset (Fin n × Fin n)) :
    (Fin n × Fin n → ℂ) →ₗ[ℂ] ({p // p ∈ K} → ℂ) where
  toFun t := fun p => t p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cellsZero_eq {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (K : Finset (Fin n × Fin n)) : L ⊓ LinearMap.ker (cellProj K) = cellsZero L K := by
  ext t
  rw [Submodule.mem_inf, LinearMap.mem_ker, mem_cellsZero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p hp => congrFun h2 ⟨p, hp⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun p => h2 p.1 p.2⟩

theorem cells_rank {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (K : Finset (Fin n × Fin n)) :
    Module.finrank ℂ L = Module.finrank ℂ (cellsZero L K) +
      Module.finrank ℂ (L.map (cellProj K)) := by
  have h := rank_nullity L (cellProj K)
  rw [cellsZero_eq] at h
  exact h

def vec3 (a0 a1 a2 : ℂ) : Fin 3 → ℂ := fun i => if i = 0 then a0 else if i = 1 then a1 else a2

theorem vec3_0 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 0 = a0 := by simp [vec3]

theorem vec3_1 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 1 = a1 := by simp [vec3]

theorem vec3_2 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 2 = a2 := by simp [vec3]

def Bad (b W Y : Fin 3 × Fin 3 → ℂ) : Prop :=
  pm b ≠ 0 ∧ (∀ α β : Fin 3 → ℂ, pm (fun p => b p + α p.1 * W p + β p.2 * Y p) = pm b) ∧
    (∀ r, ∃ j, W (r, j) ≠ 0) ∧ ∀ j, ∃ i, Y (i, j) ≠ 0

theorem bad_expand {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (a0 a1 a2 c0 c1 c2 : ℂ) :
    (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 1) + a0 * W (0, 1) + c1 * Y (0, 1)) * (b (1, 0) + a1 * W (1, 0) + c0 * Y (1, 0)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 1) + a0 * W (0, 1) + c1 * Y (0, 1)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) + (b (0, 2) + a0 * W (0, 2) + c2 * Y (0, 2)) * (b (1, 0) + a1 * W (1, 0) + c0 * Y (1, 0)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 2) + a0 * W (0, 2) + c2 * Y (0, 2)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) =
      b (0, 0) * b (1, 1) * b (2, 2) + b (0, 0) * b (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * b (2, 2) + b (0, 1) * b (1, 2) * b (2, 0) + b (0, 2) * b (1, 0) * b (2, 1) + b (0, 2) * b (1, 1) * b (2, 0) := by
  have h1 := h.2.1 (vec3 a0 a1 a2) (vec3 c0 c1 c2)
  simp only [pm, permanent_three, Matrix.of_apply, vec3_0, vec3_1, vec3_2] at h1
  linear_combination h1

theorem bad_pm {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) :
    b (0, 0) * b (1, 1) * b (2, 2) + b (0, 0) * b (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * b (2, 2) + b (0, 1) * b (1, 2) * b (2, 0) + b (0, 2) * b (1, 0) * b (2, 1) + b (0, 2) * b (1, 1) * b (2, 0) ≠ 0 := by
  have h1 := h.1
  simp only [pm, permanent_three, Matrix.of_apply] at h1
  intro h0
  exact h1 (by linear_combination h0)

theorem cancel_left {x y : ℂ} (hx : x ≠ 0) (h : x * y = 0) : y = 0 :=
  (mul_eq_zero.mp h).resolve_left hx

theorem bad_X4c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hW01 : W (0, 1) = 0)
    (hW02 : W (0, 2) = 0) (hW00 : W (0, 0) ≠ 0) : W (1, 1) * Y (2, 2) = 0 := by
  have hexp : ∀ a0 a1 a2 c0 c1 c2 : ℂ,
      (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 1) + a0 * 0 + c1 * Y (0, 1)) * (b (1, 0) + a1 * W (1, 0) + c0 * Y (1, 0)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 1) + a0 * 0 + c1 * Y (0, 1)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) + (b (0, 2) + a0 * 0 + c2 * Y (0, 2)) * (b (1, 0) + a1 * W (1, 0) + c0 * Y (1, 0)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 2) + a0 * 0 + c2 * Y (0, 2)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) =
        b (0, 0) * b (1, 1) * b (2, 2) + b (0, 0) * b (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * b (2, 2) + b (0, 1) * b (1, 2) * b (2, 0) + b (0, 2) * b (1, 0) * b (2, 1) + b (0, 2) * b (1, 1) * b (2, 0) := by
    intro a0 a1 a2 c0 c1 c2
    have t := bad_expand h a0 a1 a2 c0 c1 c2
    rw [hW01, hW02] at t
    exact t
  have k1 : W (0, 0) * W (1, 1) * Y (2, 2) = 0 := by
    linear_combination hexp 1 0 0 0 0 0 + hexp 0 1 0 0 0 0 + hexp 0 0 0 0 0 1 - hexp 1 1 0 0 0 0 - hexp 1 0 0 0 0 1 - hexp 0 1 0 0 0 1 + hexp 1 1 0 0 0 1
  have k2 : W (0, 0) * (W (1, 1) * Y (2, 2)) = 0 := by linear_combination k1
  exact cancel_left hW00 k2

theorem bad_X3c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hW01 : W (0, 1) = 0)
    (hW02 : W (0, 2) = 0) (hW10 : W (1, 0) = 0) (hW12 : W (1, 2) = 0) : False := by
  have hb := bad_pm h
  have hW00 : W (0, 0) ≠ 0 := by
    obtain ⟨j, hj⟩ := h.2.2.1 0
    rcases fin3_cases j with rfl | rfl | rfl
    · exact hj
    · exact absurd hW01 hj
    · exact absurd hW02 hj
  have hW11 : W (1, 1) ≠ 0 := by
    obtain ⟨j, hj⟩ := h.2.2.1 1
    rcases fin3_cases j with rfl | rfl | rfl
    · exact absurd hW10 hj
    · exact hj
    · exact absurd hW12 hj
  have hexp : ∀ a0 a1 a2 c0 c1 c2 : ℂ,
      (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 2) + a1 * 0 + c2 * Y (1, 2)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 1) + a0 * 0 + c1 * Y (0, 1)) * (b (1, 0) + a1 * 0 + c0 * Y (1, 0)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 1) + a0 * 0 + c1 * Y (0, 1)) * (b (1, 2) + a1 * 0 + c2 * Y (1, 2)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) + (b (0, 2) + a0 * 0 + c2 * Y (0, 2)) * (b (1, 0) + a1 * 0 + c0 * Y (1, 0)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 2) + a0 * 0 + c2 * Y (0, 2)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) =
        b (0, 0) * b (1, 1) * b (2, 2) + b (0, 0) * b (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * b (2, 2) + b (0, 1) * b (1, 2) * b (2, 0) + b (0, 2) * b (1, 0) * b (2, 1) + b (0, 2) * b (1, 1) * b (2, 0) := by
    intro a0 a1 a2 c0 c1 c2
    have t := bad_expand h a0 a1 a2 c0 c1 c2
    rw [hW01, hW02, hW10, hW12] at t
    exact t
  have k01 : W (0, 0) * W (1, 1) * b (2, 2) = 0 := by
    linear_combination - hexp 1 0 0 0 0 0 - hexp 0 1 0 0 0 0 + hexp 1 1 0 0 0 0
  have k012 : W (0, 0) * W (1, 1) * W (2, 2) = 0 := by
    linear_combination hexp 1 0 0 0 0 0 + hexp 0 1 0 0 0 0 + hexp 0 0 1 0 0 0 - hexp 1 1 0 0 0 0 - hexp 1 0 1 0 0 0 - hexp 0 1 1 0 0 0 + hexp 1 1 1 0 0 0
  have k01c : W (0, 0) * W (1, 1) * Y (2, 2) = 0 := by
    linear_combination hexp 1 0 0 0 0 0 + hexp 0 1 0 0 0 0 + hexp 0 0 0 0 0 1 - hexp 1 1 0 0 0 0 - hexp 1 0 0 0 0 1 - hexp 0 1 0 0 0 1 + hexp 1 1 0 0 0 1
  have k0 : W (0, 0) * b (1, 1) * b (2, 2) + W (0, 0) * b (1, 2) * b (2, 1) = 0 := by
    linear_combination hexp 1 0 0 0 0 0
  have k02 : W (0, 0) * b (1, 1) * W (2, 2) + W (0, 0) * b (1, 2) * W (2, 1) = 0 := by
    linear_combination - hexp 1 0 0 0 0 0 - hexp 0 0 1 0 0 0 + hexp 1 0 1 0 0 0
  have k0c : W (0, 0) * b (1, 1) * Y (2, 2) + W (0, 0) * Y (1, 2) * b (2, 1) = 0 := by
    linear_combination - hexp 1 0 0 0 0 0 - hexp 0 0 0 0 0 1 + hexp 1 0 0 0 0 1
  have k02c : W (0, 0) * Y (1, 2) * W (2, 1) = 0 := by
    linear_combination hexp 1 0 0 0 0 0 + hexp 0 0 1 0 0 0 + hexp 0 0 0 0 0 1 - hexp 1 0 1 0 0 0 - hexp 1 0 0 0 0 1 - hexp 0 0 1 0 0 1 + hexp 1 0 1 0 0 1
  have k1 : b (0, 0) * W (1, 1) * b (2, 2) + b (0, 2) * W (1, 1) * b (2, 0) = 0 := by
    linear_combination hexp 0 1 0 0 0 0
  have k12 : b (0, 0) * W (1, 1) * W (2, 2) + b (0, 2) * W (1, 1) * W (2, 0) = 0 := by
    linear_combination - hexp 0 1 0 0 0 0 - hexp 0 0 1 0 0 0 + hexp 0 1 1 0 0 0
  have k1c : b (0, 0) * W (1, 1) * Y (2, 2) + Y (0, 2) * W (1, 1) * b (2, 0) = 0 := by
    linear_combination - hexp 0 1 0 0 0 0 - hexp 0 0 0 0 0 1 + hexp 0 1 0 0 0 1
  have k12c : Y (0, 2) * W (1, 1) * W (2, 0) = 0 := by
    linear_combination hexp 0 1 0 0 0 0 + hexp 0 0 1 0 0 0 + hexp 0 0 0 0 0 1 - hexp 0 1 1 0 0 0 - hexp 0 1 0 0 0 1 - hexp 0 0 1 0 0 1 + hexp 0 1 1 0 0 1
  have kc : b (0, 0) * b (1, 1) * Y (2, 2) + b (0, 0) * Y (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * Y (2, 2) + b (0, 1) * Y (1, 2) * b (2, 0) + Y (0, 2) * b (1, 0) * b (2, 1) + Y (0, 2) * b (1, 1) * b (2, 0) = 0 := by
    linear_combination hexp 0 0 0 0 0 1
  have hb22 : b (2, 2) = 0 := by
    have e : W (0, 0) * (W (1, 1) * b (2, 2)) = 0 := by linear_combination k01
    exact cancel_left hW11 (cancel_left hW00 e)
  have hW22 : W (2, 2) = 0 := by
    have e : W (0, 0) * (W (1, 1) * W (2, 2)) = 0 := by linear_combination k012
    exact cancel_left hW11 (cancel_left hW00 e)
  have hY22 : Y (2, 2) = 0 := by
    have e : W (0, 0) * (W (1, 1) * Y (2, 2)) = 0 := by linear_combination k01c
    exact cancel_left hW11 (cancel_left hW00 e)
  have e2 : b (1, 2) * W (2, 1) = 0 := by
    have e : W (0, 0) * (b (1, 2) * W (2, 1)) = 0 := by
      linear_combination k02 - W (0, 0) * b (1, 1) * hW22
    exact cancel_left hW00 e
  have e3 : Y (1, 2) * b (2, 1) = 0 := by
    have e : W (0, 0) * (Y (1, 2) * b (2, 1)) = 0 := by
      linear_combination k0c - W (0, 0) * b (1, 1) * hY22
    exact cancel_left hW00 e
  have e4 : Y (1, 2) * W (2, 1) = 0 := by
    have e : W (0, 0) * (Y (1, 2) * W (2, 1)) = 0 := by linear_combination k02c
    exact cancel_left hW00 e
  have f2 : b (0, 2) * W (2, 0) = 0 := by
    have e : W (1, 1) * (b (0, 2) * W (2, 0)) = 0 := by
      linear_combination k12 - b (0, 0) * W (1, 1) * hW22
    exact cancel_left hW11 e
  have f3 : Y (0, 2) * b (2, 0) = 0 := by
    have e : W (1, 1) * (Y (0, 2) * b (2, 0)) = 0 := by
      linear_combination k1c - b (0, 0) * W (1, 1) * hY22
    exact cancel_left hW11 e
  have f4 : Y (0, 2) * W (2, 0) = 0 := by
    have e : W (1, 1) * (Y (0, 2) * W (2, 0)) = 0 := by linear_combination k12c
    exact cancel_left hW11 e
  have g : Y (0, 2) * (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) +
      Y (1, 2) * (b (0, 0) * b (2, 1) + b (0, 1) * b (2, 0)) = 0 := by
    linear_combination kc - (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * hY22
  have hrow2 : W (2, 0) ≠ 0 ∨ W (2, 1) ≠ 0 := by
    obtain ⟨j, hj⟩ := h.2.2.1 2
    rcases fin3_cases j with rfl | rfl | rfl
    · exact Or.inl hj
    · exact Or.inr hj
    · exact absurd hW22 hj
  have hcol2 : Y (0, 2) ≠ 0 ∨ Y (1, 2) ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.2.2 2
    rcases fin3_cases i with rfl | rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
    · exact absurd hY22 hi
  by_cases hW21 : W (2, 1) = 0
  · have hW20 : W (2, 0) ≠ 0 := hrow2.resolve_right (not_not.mpr hW21)
    have hY02 : Y (0, 2) = 0 := (mul_eq_zero.mp f4).resolve_right hW20
    have hb02 : b (0, 2) = 0 := (mul_eq_zero.mp f2).resolve_right hW20
    have hY12 : Y (1, 2) ≠ 0 := hcol2.resolve_left (not_not.mpr hY02)
    have hb21 : b (2, 1) = 0 := cancel_left hY12 e3
    have hE : b (0, 1) * b (2, 0) = 0 := by
      have e : Y (1, 2) * (b (0, 1) * b (2, 0)) = 0 := by
        linear_combination g - (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) * hY02 -
          Y (1, 2) * b (0, 0) * hb21
      exact cancel_left hY12 e
    apply hb
    linear_combination (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * hb22 +
      b (0, 0) * b (1, 2) * hb21 + b (1, 2) * hE +
      (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) * hb02
  · have hY12 : Y (1, 2) = 0 := (mul_eq_zero.mp e4).resolve_right hW21
    have hb12 : b (1, 2) = 0 := (mul_eq_zero.mp e2).resolve_right hW21
    have hY02 : Y (0, 2) ≠ 0 := hcol2.resolve_right (not_not.mpr hY12)
    have hb20 : b (2, 0) = 0 := cancel_left hY02 f3
    have hE : b (1, 0) * b (2, 1) = 0 := by
      have e : Y (0, 2) * (b (1, 0) * b (2, 1)) = 0 := by
        linear_combination g - Y (0, 2) * b (1, 1) * hb20 -
          (b (0, 0) * b (2, 1) + b (0, 1) * b (2, 0)) * hY12
      exact cancel_left hY02 e
    apply hb
    linear_combination (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * hb22 +
      (b (0, 0) * b (2, 1) + b (0, 1) * b (2, 0)) * hb12 + b (0, 2) * hE +
      b (0, 2) * b (1, 1) * hb20

theorem bad_X1c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hY10 : Y (1, 0) = 0)
    (hY20 : Y (2, 0) = 0) (hY11 : Y (1, 1) = 0) (hY21 : Y (2, 1) = 0) : False := by
  have hb := bad_pm h
  have hY00 : Y (0, 0) ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.2.2 0
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hi
    · exact absurd hY10 hi
    · exact absurd hY20 hi
  have hY01 : Y (0, 1) ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.2.2 1
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hi
    · exact absurd hY11 hi
    · exact absurd hY21 hi
  have hexp : ∀ a0 a1 a2 c0 c1 c2 : ℂ,
      (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 1) + a1 * W (1, 1) + c1 * 0) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 1) + a2 * W (2, 1) + c1 * 0) + (b (0, 1) + a0 * W (0, 1) + c1 * Y (0, 1)) * (b (1, 0) + a1 * W (1, 0) + c0 * 0) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 1) + a0 * W (0, 1) + c1 * Y (0, 1)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 0) + a2 * W (2, 0) + c0 * 0) + (b (0, 2) + a0 * W (0, 2) + c2 * Y (0, 2)) * (b (1, 0) + a1 * W (1, 0) + c0 * 0) * (b (2, 1) + a2 * W (2, 1) + c1 * 0) + (b (0, 2) + a0 * W (0, 2) + c2 * Y (0, 2)) * (b (1, 1) + a1 * W (1, 1) + c1 * 0) * (b (2, 0) + a2 * W (2, 0) + c0 * 0) =
        b (0, 0) * b (1, 1) * b (2, 2) + b (0, 0) * b (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * b (2, 2) + b (0, 1) * b (1, 2) * b (2, 0) + b (0, 2) * b (1, 0) * b (2, 1) + b (0, 2) * b (1, 1) * b (2, 0) := by
    intro a0 a1 a2 c0 c1 c2
    have t := bad_expand h a0 a1 a2 c0 c1 c2
    rw [hY10, hY20, hY11, hY21] at t
    exact t
  have k1 : b (0, 0) * W (1, 1) * b (2, 2) + b (0, 0) * W (1, 2) * b (2, 1) + b (0, 1) * W (1, 0) * b (2, 2) + b (0, 1) * W (1, 2) * b (2, 0) + b (0, 2) * W (1, 0) * b (2, 1) + b (0, 2) * W (1, 1) * b (2, 0) = 0 := by
    linear_combination hexp 0 1 0 0 0 0
  have k1c0 : Y (0, 0) * W (1, 1) * b (2, 2) + Y (0, 0) * W (1, 2) * b (2, 1) = 0 := by
    linear_combination - hexp 0 1 0 0 0 0 - hexp 0 0 0 1 0 0 + hexp 0 1 0 1 0 0
  have k1c1 : Y (0, 1) * W (1, 0) * b (2, 2) + Y (0, 1) * W (1, 2) * b (2, 0) = 0 := by
    linear_combination - hexp 0 1 0 0 0 0 - hexp 0 0 0 0 1 0 + hexp 0 1 0 0 1 0
  have k12 : b (0, 0) * W (1, 1) * W (2, 2) + b (0, 0) * W (1, 2) * W (2, 1) + b (0, 1) * W (1, 0) * W (2, 2) + b (0, 1) * W (1, 2) * W (2, 0) + b (0, 2) * W (1, 0) * W (2, 1) + b (0, 2) * W (1, 1) * W (2, 0) = 0 := by
    linear_combination - hexp 0 1 0 0 0 0 - hexp 0 0 1 0 0 0 + hexp 0 1 1 0 0 0
  have k12c0 : Y (0, 0) * W (1, 1) * W (2, 2) + Y (0, 0) * W (1, 2) * W (2, 1) = 0 := by
    linear_combination hexp 0 1 0 0 0 0 + hexp 0 0 1 0 0 0 + hexp 0 0 0 1 0 0 - hexp 0 1 1 0 0 0 - hexp 0 1 0 1 0 0 - hexp 0 0 1 1 0 0 + hexp 0 1 1 1 0 0
  have k12c1 : Y (0, 1) * W (1, 0) * W (2, 2) + Y (0, 1) * W (1, 2) * W (2, 0) = 0 := by
    linear_combination hexp 0 1 0 0 0 0 + hexp 0 0 1 0 0 0 + hexp 0 0 0 0 1 0 - hexp 0 1 1 0 0 0 - hexp 0 1 0 0 1 0 - hexp 0 0 1 0 1 0 + hexp 0 1 1 0 1 0
  have hb02 : b (0, 2) ≠ 0 := by
    intro hb02
    have d0 : -(b (0, 0)) / Y (0, 0) * Y (0, 0) = -(b (0, 0)) := by field_simp
    have d1 : -(b (0, 1)) / Y (0, 1) * Y (0, 1) = -(b (0, 1)) := by field_simp
    apply hb
    linear_combination (-1 : ℂ) * hexp 0 0 0 (-(b (0, 0)) / Y (0, 0)) (-(b (0, 1)) / Y (0, 1)) 0 +
      (b (1, 1) * b (2, 2) + b (1, 2) * b (2, 1)) * d0 +
      (b (1, 0) * b (2, 2) + b (1, 2) * b (2, 0)) * d1 +
      (b (1, 0) * b (2, 1) + b (1, 1) * b (2, 0)) * hb02
  have i_b : W (1, 1) * b (2, 2) + W (1, 2) * b (2, 1) = 0 := by
    have e : Y (0, 0) * (W (1, 1) * b (2, 2) + W (1, 2) * b (2, 1)) = 0 := by
      linear_combination k1c0
    exact cancel_left hY00 e
  have ii_b : W (1, 0) * b (2, 2) + W (1, 2) * b (2, 0) = 0 := by
    have e : Y (0, 1) * (W (1, 0) * b (2, 2) + W (1, 2) * b (2, 0)) = 0 := by
      linear_combination k1c1
    exact cancel_left hY01 e
  have iii_b : W (1, 0) * b (2, 1) + W (1, 1) * b (2, 0) = 0 := by
    have e : b (0, 2) * (W (1, 0) * b (2, 1) + W (1, 1) * b (2, 0)) = 0 := by
      linear_combination k1 - b (0, 0) * i_b - b (0, 1) * ii_b
    exact cancel_left hb02 e
  have i_w : W (1, 1) * W (2, 2) + W (1, 2) * W (2, 1) = 0 := by
    have e : Y (0, 0) * (W (1, 1) * W (2, 2) + W (1, 2) * W (2, 1)) = 0 := by
      linear_combination k12c0
    exact cancel_left hY00 e
  have ii_w : W (1, 0) * W (2, 2) + W (1, 2) * W (2, 0) = 0 := by
    have e : Y (0, 1) * (W (1, 0) * W (2, 2) + W (1, 2) * W (2, 0)) = 0 := by
      linear_combination k12c1
    exact cancel_left hY01 e
  have iii_w : W (1, 0) * W (2, 1) + W (1, 1) * W (2, 0) = 0 := by
    have e : b (0, 2) * (W (1, 0) * W (2, 1) + W (1, 1) * W (2, 0)) = 0 := by
      linear_combination k12 - b (0, 0) * i_w - b (0, 1) * ii_w
    exact cancel_left hb02 e
  have key : ∃ lam : ℂ, b (2, 0) + -lam * W (2, 0) = 0 ∧ b (2, 1) + -lam * W (2, 1) = 0 ∧
      b (2, 2) + -lam * W (2, 2) = 0 := by
    obtain ⟨j2, hj2⟩ := h.2.2.1 2
    by_cases hA : W (1, 0) = 0
    · by_cases hB : W (1, 1) = 0
      · have hW12 : W (1, 2) ≠ 0 := by
          obtain ⟨j, hj⟩ := h.2.2.1 1
          rcases fin3_cases j with rfl | rfl | rfl
          · exact absurd hA hj
          · exact absurd hB hj
          · exact hj
        have hb21 : b (2, 1) = 0 :=
          cancel_left hW12 (by linear_combination i_b - b (2, 2) * hB)
        have hb20 : b (2, 0) = 0 :=
          cancel_left hW12 (by linear_combination ii_b - b (2, 2) * hA)
        have hW21 : W (2, 1) = 0 :=
          cancel_left hW12 (by linear_combination i_w - W (2, 2) * hB)
        have hW20 : W (2, 0) = 0 :=
          cancel_left hW12 (by linear_combination ii_w - W (2, 2) * hA)
        have hW22 : W (2, 2) ≠ 0 := by
          rcases fin3_cases j2 with rfl | rfl | rfl
          · exact absurd hW20 hj2
          · exact absurd hW21 hj2
          · exact hj2
        have d : b (2, 2) / W (2, 2) * W (2, 2) = b (2, 2) := by field_simp
        refine ⟨b (2, 2) / W (2, 2), ?_, ?_, ?_⟩
        · rw [hb20, hW20]
          ring
        · rw [hb21, hW21]
          ring
        · linear_combination (-1 : ℂ) * d
      · have hb20 : b (2, 0) = 0 :=
          cancel_left hB (by linear_combination iii_b - b (2, 1) * hA)
        have hW20 : W (2, 0) = 0 :=
          cancel_left hB (by linear_combination iii_w - W (2, 1) * hA)
        have hW21 : W (2, 1) ≠ 0 := by
          intro h0
          have hW22 : W (2, 2) = 0 :=
            cancel_left hB (by linear_combination i_w - W (1, 2) * h0)
          rcases fin3_cases j2 with rfl | rfl | rfl
          · exact hj2 hW20
          · exact hj2 h0
          · exact hj2 hW22
        have hx : b (2, 2) * W (2, 1) = b (2, 1) * W (2, 2) := by
          have e : W (1, 1) * (b (2, 2) * W (2, 1) - b (2, 1) * W (2, 2)) = 0 := by
            linear_combination W (2, 1) * i_b - b (2, 1) * i_w
          exact sub_eq_zero.mp (cancel_left hB e)
        have d : b (2, 1) / W (2, 1) * W (2, 1) = b (2, 1) := by field_simp
        refine ⟨b (2, 1) / W (2, 1), ?_, ?_, ?_⟩
        · rw [hb20, hW20]
          ring
        · linear_combination (-1 : ℂ) * d
        · have e : (b (2, 2) + -(b (2, 1) / W (2, 1)) * W (2, 2)) * W (2, 1) = 0 := by
            linear_combination hx - W (2, 2) * d
          exact (mul_eq_zero.mp e).resolve_right hW21
    · have hW20 : W (2, 0) ≠ 0 := by
        intro h0
        have hW22 : W (2, 2) = 0 :=
          cancel_left hA (by linear_combination ii_w - W (1, 2) * h0)
        have hW21 : W (2, 1) = 0 :=
          cancel_left hA (by linear_combination iii_w - W (1, 1) * h0)
        rcases fin3_cases j2 with rfl | rfl | rfl
        · exact hj2 h0
        · exact hj2 hW21
        · exact hj2 hW22
      have hx1 : b (2, 1) * W (2, 0) = b (2, 0) * W (2, 1) := by
        have e : W (1, 0) * (b (2, 1) * W (2, 0) - b (2, 0) * W (2, 1)) = 0 := by
          linear_combination W (2, 0) * iii_b - b (2, 0) * iii_w
        exact sub_eq_zero.mp (cancel_left hA e)
      have hx2 : b (2, 2) * W (2, 0) = b (2, 0) * W (2, 2) := by
        have e : W (1, 0) * (b (2, 2) * W (2, 0) - b (2, 0) * W (2, 2)) = 0 := by
          linear_combination W (2, 0) * ii_b - b (2, 0) * ii_w
        exact sub_eq_zero.mp (cancel_left hA e)
      have d : b (2, 0) / W (2, 0) * W (2, 0) = b (2, 0) := by field_simp
      refine ⟨b (2, 0) / W (2, 0), ?_, ?_, ?_⟩
      · linear_combination (-1 : ℂ) * d
      · have e : (b (2, 1) + -(b (2, 0) / W (2, 0)) * W (2, 1)) * W (2, 0) = 0 := by
          linear_combination hx1 - W (2, 1) * d
        exact (mul_eq_zero.mp e).resolve_right hW20
      · have e : (b (2, 2) + -(b (2, 0) / W (2, 0)) * W (2, 2)) * W (2, 0) = 0 := by
          linear_combination hx2 - W (2, 2) * d
        exact (mul_eq_zero.mp e).resolve_right hW20
  obtain ⟨lam, e0, e1, e2⟩ := key
  apply hb
  linear_combination (-1 : ℂ) * hexp 0 0 (-lam) 0 0 0 +
    (b (0, 0) * b (1, 1) + b (0, 1) * b (1, 0)) * e2 +
    (b (0, 0) * b (1, 2) + b (0, 2) * b (1, 0)) * e1 +
    (b (0, 1) * b (1, 2) + b (0, 2) * b (1, 1)) * e0

theorem pm_rel (ρ κ : Equiv.Perm (Fin 3)) (u : Fin 3 × Fin 3 → ℂ) :
    pm (fun p => u (ρ p.1, κ p.2)) = pm u := by
  unfold pm
  exact perm_submatrix_equiv (Matrix.of fun i j => u (i, j)) ρ κ

theorem bad_rel {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (ρ κ : Equiv.Perm (Fin 3)) :
    Bad (fun p => b (ρ p.1, κ p.2)) (fun p => W (ρ p.1, κ p.2)) (fun p => Y (ρ p.1, κ p.2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pm_rel ρ κ b]
    exact h.1
  · intro α β
    have h1 := pm_rel ρ κ (fun q : Fin 3 × Fin 3 =>
      b q + α (ρ.symm q.1) * W q + β (κ.symm q.2) * Y q)
    simp only [Equiv.symm_apply_apply] at h1
    refine h1.trans ?_
    rw [pm_rel ρ κ b]
    exact h.2.1 (fun i => α (ρ.symm i)) (fun j => β (κ.symm j))
  · intro r
    obtain ⟨j, hj⟩ := h.2.2.1 (ρ r)
    exact ⟨κ.symm j, by simpa using hj⟩
  · intro j
    obtain ⟨i, hi⟩ := h.2.2.2 (κ j)
    exact ⟨ρ.symm i, by simpa using hi⟩

theorem bad_tr {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) :
    Bad (fun p => b (p.2, p.1)) (fun p => Y (p.2, p.1)) (fun p => W (p.2, p.1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pm_tr b]
    exact h.1
  · intro α β
    have h1 : pm (fun p : Fin 3 × Fin 3 =>
        b (p.2, p.1) + β p.2 * W (p.2, p.1) + α p.1 * Y (p.2, p.1)) =
        pm (fun q : Fin 3 × Fin 3 => b q + β q.1 * W q + α q.2 * Y q) :=
      pm_tr (fun q : Fin 3 × Fin 3 => b q + β q.1 * W q + α q.2 * Y q)
    have h2 := h.2.1 β α
    show pm (fun p : Fin 3 × Fin 3 =>
      b (p.2, p.1) + α p.1 * Y (p.2, p.1) + β p.2 * W (p.2, p.1)) =
      pm (fun p : Fin 3 × Fin 3 => b (p.2, p.1))
    rw [pm_tr b, ← h2, ← h1]
    congr 1
    funext p
    ring
  · intro r
    obtain ⟨i, hi⟩ := h.2.2.2 r
    exact ⟨i, hi⟩
  · intro j
    obtain ⟨i, hi⟩ := h.2.2.1 j
    exact ⟨i, hi⟩

theorem fin3_two (a b c i : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hi : i ≠ c) :
    i = a ∨ i = b := by
  revert a b c i
  decide

theorem fin3_third (a b : Fin 3) : ∃ m : Fin 3, m ≠ a ∧ m ≠ b := by
  revert a b
  decide

theorem perm3_two (ρ : Equiv.Perm (Fin 3)) : ρ 2 ≠ ρ 0 ∧ ρ 2 ≠ ρ 1 :=
  ⟨fun hh => absurd (ρ.injective hh) (by decide), fun hh => absurd (ρ.injective hh) (by decide)⟩

theorem bad_X4 {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (r0 j0 i i' l m : Fin 3)
    (hcell : W (r0, j0) ≠ 0) (hrow : ∀ j, j ≠ j0 → W (r0, j) = 0) (hi : i ≠ r0) (hi' : i' ≠ r0)
    (hii : i ≠ i') (hl : l ≠ j0) (hm : m ≠ j0) (hlm : l ≠ m) : W (i, l) * Y (i', m) = 0 := by
  obtain ⟨ρ, hρ0, hρ1⟩ : ∃ ρ : Equiv.Perm (Fin 3), ρ 0 = r0 ∧ ρ 1 = i :=
    exists_perm2 (m := 1) r0 i (Ne.symm hi)
  obtain ⟨κ, hκ0, hκ1⟩ : ∃ κ : Equiv.Perm (Fin 3), κ 0 = j0 ∧ κ 1 = l :=
    exists_perm2 (m := 1) j0 l (Ne.symm hl)
  have hρ2 : ρ 2 = i' := by
    have h2 := perm3_two ρ
    rw [hρ0, hρ1] at h2
    exact fin3_pigeon r0 i (ρ 2) i' (Ne.symm hi) h2.1 h2.2 hi' (Ne.symm hii)
  have hκ2 : κ 2 = m := by
    have h2 := perm3_two κ
    rw [hκ0, hκ1] at h2
    exact fin3_pigeon j0 l (κ 2) m (Ne.symm hl) h2.1 h2.2 hm (Ne.symm hlm)
  have h1 : W (ρ 1, κ 1) * Y (ρ 2, κ 2) = 0 := bad_X4c (bad_rel h ρ κ)
    (by
      show W (ρ 0, κ 1) = 0
      rw [hρ0, hκ1]
      exact hrow l hl)
    (by
      show W (ρ 0, κ 2) = 0
      rw [hρ0, hκ2]
      exact hrow m hm)
    (by
      show W (ρ 0, κ 0) ≠ 0
      rw [hρ0, hκ0]
      exact hcell)
  rw [hρ1, hκ1, hρ2, hκ2] at h1
  exact h1

theorem bad_X1 {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (r j l : Fin 3) (hjl : j ≠ l)
    (hj : ∀ i, i ≠ r → Y (i, j) = 0) (hl : ∀ i, i ≠ r → Y (i, l) = 0) : False := by
  obtain ⟨κ, hκ0, hκ1⟩ : ∃ κ : Equiv.Perm (Fin 3), κ 0 = j ∧ κ 1 = l :=
    exists_perm2 (m := 1) j l hjl
  have hρ : ∀ x : Fin 3, x ≠ 0 → (Equiv.swap (0 : Fin 3) r) x ≠ r := by
    intro x hx hh
    have h2 : (Equiv.swap (0 : Fin 3) r) x = (Equiv.swap (0 : Fin 3) r) 0 := by
      rw [hh, Equiv.swap_apply_left]
    exact hx ((Equiv.swap (0 : Fin 3) r).injective h2)
  exact bad_X1c (bad_rel h (Equiv.swap (0 : Fin 3) r) κ)
    (by
      show Y ((Equiv.swap (0 : Fin 3) r) 1, κ 0) = 0
      rw [hκ0]
      exact hj _ (hρ 1 (by decide)))
    (by
      show Y ((Equiv.swap (0 : Fin 3) r) 2, κ 0) = 0
      rw [hκ0]
      exact hj _ (hρ 2 (by decide)))
    (by
      show Y ((Equiv.swap (0 : Fin 3) r) 1, κ 1) = 0
      rw [hκ1]
      exact hl _ (hρ 1 (by decide)))
    (by
      show Y ((Equiv.swap (0 : Fin 3) r) 2, κ 1) = 0
      rw [hκ1]
      exact hl _ (hρ 2 (by decide)))

theorem bad_XX {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (r0 r1 j0 j1 : Fin 3) (hr : r0 ≠ r1)
    (h0 : ∀ j, j ≠ j0 → W (r0, j) = 0) (h1 : ∀ j, j ≠ j1 → W (r1, j) = 0) : False := by
  by_cases hj : j0 = j1
  · exact bad_X1 (bad_tr h) j0 r0 r1 hr (fun i hi => h0 i hi) (fun i hi => by
      rw [hj] at hi
      exact h1 i hi)
  · obtain ⟨ρ, hρ0, hρ1⟩ : ∃ ρ : Equiv.Perm (Fin 3), ρ 0 = r0 ∧ ρ 1 = r1 :=
      exists_perm2 (m := 1) r0 r1 hr
    obtain ⟨κ, hκ0, hκ1⟩ : ∃ κ : Equiv.Perm (Fin 3), κ 0 = j0 ∧ κ 1 = j1 :=
      exists_perm2 (m := 1) j0 j1 hj
    have h2 := perm3_two κ
    rw [hκ0, hκ1] at h2
    exact bad_X3c (bad_rel h ρ κ)
      (by
        show W (ρ 0, κ 1) = 0
        rw [hρ0, hκ1]
        exact h0 j1 (Ne.symm hj))
      (by
        show W (ρ 0, κ 2) = 0
        rw [hρ0]
        exact h0 _ h2.1)
      (by
        show W (ρ 1, κ 0) = 0
        rw [hρ1, hκ0]
        exact h1 j0 hj)
      (by
        show W (ρ 1, κ 2) = 0
        rw [hρ1]
        exact h1 _ h2.2)

def SE (W Y : Fin 3 × Fin 3 → ℂ) (c : Fin 3) : Prop :=
  ∃ j, W (c, j) ≠ 0 ∧ (∀ l, l ≠ j → W (c, l) = 0) ∧ ∀ i, i ≠ c → Y (i, j) = 0

theorem n3_SE2 {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y)
    (K : Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)))
    (hK : ∀ k ∈ K, ∀ r j, k.1 r * W (r, j) = k.2 j * Y (r, j))
    (k k' : (Fin 3 → ℂ) × (Fin 3 → ℂ)) (hk : k ∈ K) (hk' : k' ∈ K) (a b' c : Fin 3)
    (hab : a ≠ b') (hac : a ≠ c) (hbc : b' ≠ c) (hc : k.1 c ≠ 0) (hc' : k'.1 c ≠ 0)
    (hb0 : k.1 b' = 0) (ha0 : k'.1 a = 0) : SE W Y c := by
  have hcol : ∀ j, W (c, j) ≠ 0 → ∀ i, i ≠ c → Y (i, j) = 0 := by
    intro j hj i hi
    have hβ : k.2 j ≠ 0 := by
      intro h0
      have h1 := hK k hk c j
      rw [h0, zero_mul] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hc h2
      · exact hj h2
    have hβ' : k'.2 j ≠ 0 := by
      intro h0
      have h1 := hK k' hk' c j
      rw [h0, zero_mul] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hc' h2
      · exact hj h2
    rcases fin3_two a b' c i hab hac hbc hi with h3 | h3
    · rw [h3]
      have h1 := hK k' hk' a j
      rw [ha0, zero_mul] at h1
      rcases mul_eq_zero.mp h1.symm with h2 | h2
      · exact absurd h2 hβ'
      · exact h2
    · rw [h3]
      have h1 := hK k hk b' j
      rw [hb0, zero_mul] at h1
      rcases mul_eq_zero.mp h1.symm with h2 | h2
      · exact absurd h2 hβ
      · exact h2
  obtain ⟨j, hj⟩ := h.2.2.1 c
  refine ⟨j, hj, fun l hl => ?_, hcol j hj⟩
  by_contra hl0
  exact bad_X1 h c j l (Ne.symm hl) (hcol j hj) (hcol l hl0)

theorem n3_XX {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (c c' : Fin 3) (hcc : c ≠ c')
    (s : SE W Y c) (s' : SE W Y c') : False := by
  obtain ⟨j, _, h0, _⟩ := s
  obtain ⟨j', _, h1, _⟩ := s'
  exact bad_XX h c c' j j' hcc h0 h1

theorem n3_block {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y)
    (K : Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)))
    (hK : ∀ k ∈ K, ∀ r j, k.1 r * W (r, j) = k.2 j * Y (r, j))
    (k : (Fin 3 → ℂ) × (Fin 3 → ℂ)) (hk : k ∈ K) (c a b' : Fin 3) (hca : c ≠ a) (hcb : c ≠ b')
    (hab : a ≠ b') (s : SE W Y c) (hc0 : k.1 c = 0) (ha : k.1 a ≠ 0) (hb : k.1 b' ≠ 0) :
    False := by
  obtain ⟨j0, hcell1, hcell2, hcell3⟩ := s
  have hY0 : Y (c, j0) ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.2.2 j0
    by_cases hic : i = c
    · rw [← hic]
      exact hi
    · exact absurd (hcell3 i hic) hi
  have hβ0 : k.2 j0 = 0 := by
    have h1 := hK k hk c j0
    rw [hc0, zero_mul] at h1
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · exact h2
    · exact absurd h2 hY0
  have hWa0 : W (a, j0) = 0 := by
    have h1 := hK k hk a j0
    rw [hβ0, zero_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 ha
    · exact h2
  have hWb0 : W (b', j0) = 0 := by
    have h1 := hK k hk b' j0
    rw [hβ0, zero_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hb
    · exact h2
  have hKb : ∀ i, k.1 i ≠ 0 → ∀ j, W (i, j) ≠ 0 → Y (i, j) ≠ 0 := by
    intro i hi j hj h0
    have h1 := hK k hk i j
    rw [h0, mul_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hi h2
    · exact hj h2
  obtain ⟨l, hl⟩ := h.2.2.1 a
  have hlj0 : l ≠ j0 := by
    rintro rfl
    exact hl hWa0
  obtain ⟨m, hm1, hm2⟩ := fin3_third j0 l
  have h1 := bad_X4 h c j0 b' a m l hcell1 hcell2 (Ne.symm hcb) (Ne.symm hca) (Ne.symm hab)
    hm1 hlj0 hm2
  have hWbm : W (b', m) = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (hKb a ha l hl)
  obtain ⟨j', hj'⟩ := h.2.2.1 b'
  have hj'l : j' = l := fin3_pigeon j0 m j' l (Ne.symm hm1)
    (by
      rintro rfl
      exact hj' hWb0)
    (by
      rintro rfl
      exact hj' hWbm) hlj0 (Ne.symm hm2)
  rw [hj'l] at hj'
  have h2 := bad_X4 h c j0 a b' m l hcell1 hcell2 (Ne.symm hca) (Ne.symm hcb) hab hm1 hlj0 hm2
  have hWam : W (a, m) = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 (hKb b' hb l hj')
  refine bad_XX h c a j0 l hca hcell2 (fun j hj => ?_)
  rcases fin3_two j0 m l j (Ne.symm hm1) (Ne.symm hlj0) hm2 hj with h3 | h3
  · rw [h3]
    exact hWa0
  · rw [h3]
    exact hWam

noncomputable def relMap (W Y : Fin 3 × Fin 3 → ℂ) :
    ((Fin 3 → ℂ) × (Fin 3 → ℂ)) →ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) where
  toFun k := fun p => k.1 p.1 * W p - k.2 p.2 * Y p
  map_add' x y := by
    funext p
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext p
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def N3Alg : Prop :=
  ∀ (b W Y : Fin 3 × Fin 3 → ℂ) (K : Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ))),
    Bad b W Y → 2 ≤ Module.finrank ℂ K →
    (∀ k ∈ K, ∀ r j, k.1 r * W (r, j) = k.2 j * Y (r, j)) → False

theorem n3alg : N3Alg := by
  intro b W Y K h hK2 hK
  have hKa : ∀ k ∈ K, k ≠ 0 → k.1 ≠ 0 := by
    intro k hk hk0 h1
    apply hk0
    refine Prod.ext h1 ?_
    funext j
    obtain ⟨i, hi⟩ := h.2.2.2 j
    have h2 := hK k hk i j
    rw [h1, Pi.zero_apply, zero_mul] at h2
    rcases mul_eq_zero.mp h2.symm with h3 | h3
    · exact h3
    · exact absurd h3 hi
  have hex : ∀ r : Fin 3, ∃ k ∈ K, k ≠ 0 ∧ k.1 r = 0 := by
    intro r
    have h1 := rank_nullity K
      ((LinearMap.proj r).comp (LinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ)))
    have h2 := Submodule.finrank_le
      (K.map ((LinearMap.proj r).comp (LinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ))))
    rw [Module.finrank_self] at h2
    have hpos : 0 < Module.finrank ℂ (K ⊓ LinearMap.ker
        ((LinearMap.proj r).comp (LinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ))) :
          Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ))) := by omega
    obtain ⟨⟨k, hk⟩, hk0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hk' := Submodule.mem_inf.mp hk
    exact ⟨k, hk'.1, fun h0 => hk0 (Subtype.ext h0), LinearMap.mem_ker.mp hk'.2⟩
  obtain ⟨k0, hk0, hne0, hz0⟩ := hex 0
  obtain ⟨k1, hk1, hne1, hz1⟩ := hex 1
  obtain ⟨k2, hk2, hne2, hz2⟩ := hex 2
  have N0 : k0.1 1 ≠ 0 ∨ k0.1 2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hKa k0 hk0 hne0
    funext i
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hz0
    · exact hcon.1
    · exact hcon.2
  have N1 : k1.1 0 ≠ 0 ∨ k1.1 2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hKa k1 hk1 hne1
    funext i
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hcon.1
    · exact hz1
    · exact hcon.2
  have N2 : k2.1 0 ≠ 0 ∨ k2.1 1 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hKa k2 hk2 hne2
    funext i
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hcon.1
    · exact hcon.2
    · exact hz2
  have A0 : k1.1 0 ≠ 0 → k2.1 0 ≠ 0 → SE W Y 0 := fun q1 q2 =>
    n3_SE2 h K hK k1 k2 hk1 hk2 2 1 0 (by decide) (by decide) (by decide) q1 q2 hz1 hz2
  have U01 : k0.1 1 ≠ 0 → k0.1 2 = 0 → SE W Y 1 := fun q1 q2 =>
    n3_SE2 h K hK k0 k0 hk0 hk0 2 0 1 (by decide) (by decide) (by decide) q1 q1 hz0 q2
  have U02 : k0.1 2 ≠ 0 → k0.1 1 = 0 → SE W Y 2 := fun q1 q2 =>
    n3_SE2 h K hK k0 k0 hk0 hk0 1 0 2 (by decide) (by decide) (by decide) q1 q1 hz0 q2
  have U10 : k1.1 0 ≠ 0 → k1.1 2 = 0 → SE W Y 0 := fun q1 q2 =>
    n3_SE2 h K hK k1 k1 hk1 hk1 2 1 0 (by decide) (by decide) (by decide) q1 q1 hz1 q2
  have U12 : k1.1 2 ≠ 0 → k1.1 0 = 0 → SE W Y 2 := fun q1 q2 =>
    n3_SE2 h K hK k1 k1 hk1 hk1 0 1 2 (by decide) (by decide) (by decide) q1 q1 hz1 q2
  have U20 : k2.1 0 ≠ 0 → k2.1 1 = 0 → SE W Y 0 := fun q1 q2 =>
    n3_SE2 h K hK k2 k2 hk2 hk2 1 2 0 (by decide) (by decide) (by decide) q1 q1 hz2 q2
  have U21 : k2.1 1 ≠ 0 → k2.1 0 = 0 → SE W Y 1 := fun q1 q2 =>
    n3_SE2 h K hK k2 k2 hk2 hk2 0 2 1 (by decide) (by decide) (by decide) q1 q1 hz2 q2
  have hS : SE W Y 0 ∨ SE W Y 1 ∨ SE W Y 2 := by
    by_cases q10 : k1.1 0 = 0
    · right
      right
      exact U12 (N1.resolve_left (not_not.mpr q10)) q10
    · by_cases q20 : k2.1 0 = 0
      · right
        left
        exact U21 (N2.resolve_left (not_not.mpr q20)) q20
      · left
        exact A0 q10 q20
  rcases hS with s0 | s1 | s2
  · by_cases q01 : k0.1 1 = 0
    · exact n3_XX h 0 2 (by decide) s0 (U02 (N0.resolve_left (not_not.mpr q01)) q01)
    · by_cases q02 : k0.1 2 = 0
      · exact n3_XX h 0 1 (by decide) s0 (U01 q01 q02)
      · exact n3_block h K hK k0 hk0 0 1 2 (by decide) (by decide) (by decide) s0 hz0 q01 q02
  · by_cases q10 : k1.1 0 = 0
    · exact n3_XX h 1 2 (by decide) s1 (U12 (N1.resolve_left (not_not.mpr q10)) q10)
    · by_cases q12 : k1.1 2 = 0
      · exact n3_XX h 0 1 (by decide) (U10 q10 q12) s1
      · exact n3_block h K hK k1 hk1 1 0 2 (by decide) (by decide) (by decide) s1 hz1 q10 q12
  · by_cases q20 : k2.1 0 = 0
    · exact n3_XX h 1 2 (by decide) (U21 (N2.resolve_left (not_not.mpr q20)) q20) s2
    · by_cases q21 : k2.1 1 = 0
      · exact n3_XX h 0 2 (by decide) (U20 q20 q21) s2
      · exact n3_block h K hK k2 hk2 2 0 1 (by decide) (by decide) (by decide) s2 hz2 q20 q21

theorem n3core_of_alg (halg : N3Alg) : N3Core := by
  intro b V0 hb h hd hrow hcol
  choose x hxV hx0 hxs using hrow
  choose y hyV hy0 hys using hcol
  have hsx : ∀ (α : Fin 3 → ℂ) (i j : Fin 3), (∑ r, α r • x r) (i, j) = α i * x i (i, j) := by
    intro α i j
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · rfl
    · intro r _ hr
      rw [Pi.smul_apply, hxs r i j (Ne.symm hr), smul_zero]
    · intro hne
      exact (hne (Finset.mem_univ _)).elim
  have hsy : ∀ (β : Fin 3 → ℂ) (i j : Fin 3), (∑ c, β c • y c) (i, j) = β j * y j (i, j) := by
    intro β i j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rfl
    · intro c _ hc
      rw [Pi.smul_apply, hys c i j (Ne.symm hc), smul_zero]
    · intro hne
      exact (hne (Finset.mem_univ _)).elim
  have hbad : Bad b (fun p => x p.1 p) (fun p => y p.2 p) := by
    refine ⟨hb, ?_, ?_, ?_⟩
    · intro α β
      have hη : (∑ r, α r • x r) + (∑ c, β c • y c) ∈ V0 :=
        V0.add_mem (V0.sum_mem fun r _ => V0.smul_mem _ (hxV r))
          (V0.sum_mem fun c _ => V0.smul_mem _ (hyV c))
      have h1 := h _ hη
      have e : (fun p : Fin 3 × Fin 3 => b p + α p.1 * x p.1 p + β p.2 * y p.2 p) =
          b + ((∑ r, α r • x r) + ∑ c, β c • y c) := by
        funext p
        obtain ⟨i, j⟩ := p
        rw [Pi.add_apply, Pi.add_apply, hsx, hsy]
        ring
      show pm (fun p : Fin 3 × Fin 3 => b p + α p.1 * x p.1 p + β p.2 * y p.2 p) = pm b
      rw [e, h1]
    · intro r
      have h1 : ∃ p, x r p ≠ 0 := by
        by_contra hc
        apply hx0 r
        funext p
        by_contra hp
        exact hc ⟨p, hp⟩
      obtain ⟨⟨i, j⟩, hp⟩ := h1
      have hi : i = r := by
        by_contra hi
        exact hp (hxs r i j hi)
      rw [hi] at hp
      exact ⟨j, hp⟩
    · intro c
      have h1 : ∃ p, y c p ≠ 0 := by
        by_contra hc'
        apply hy0 c
        funext p
        by_contra hp
        exact hc' ⟨p, hp⟩
      obtain ⟨⟨i, j⟩, hp⟩ := h1
      have hj : j = c := by
        by_contra hj
        exact hp (hys c i j hj)
      rw [hj] at hp
      exact ⟨i, hp⟩
  have hrange : LinearMap.range (relMap (fun p => x p.1 p) (fun p => y p.2 p)) ≤ V0 := by
    rintro _ ⟨k, rfl⟩
    have e : relMap (fun p => x p.1 p) (fun p => y p.2 p) k =
        (∑ r, k.1 r • x r) - ∑ c, k.2 c • y c := by
      funext p
      obtain ⟨i, j⟩ := p
      rw [Pi.sub_apply, hsx, hsy]
      rfl
    rw [e]
    exact V0.sub_mem (V0.sum_mem fun r _ => V0.smul_mem _ (hxV r))
      (V0.sum_mem fun c _ => V0.smul_mem _ (hyV c))
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (relMap (fun p => x p.1 p) (fun p => y p.2 p))
  have h2 := Submodule.finrank_mono hrange
  have h3 : Module.finrank ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)) = 6 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  refine halg b (fun p => x p.1 p) (fun p => y p.2 p)
    (LinearMap.ker (relMap (fun p => x p.1 p) (fun p => y p.2 p))) hbad (by omega) ?_
  intro k hk r j
  have h4 := congrFun (LinearMap.mem_ker.mp hk) (r, j)
  exact sub_eq_zero.mp h4

theorem n3prime (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (hb : pm b ≠ 0) (h : ∀ η ∈ V0, pm (b + η) = pm b) : Module.finrank ℂ V0 ≤ 3 :=
  n3prime_of_core (n3core_of_alg n3alg) b V0 hb h

theorem n3prime_L_full {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ Fin 3 ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ (blockSpace L r c ⊓
        LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ)) : Submodule ℂ _) ≤
      3 + Module.finrank ℂ (colsOff L c) :=
  n3prime_L n3prime hL r c u0 hu0 h0

theorem row_onto {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (e : Fin (m + 2))
    (hrank : m + 1 ≤ Module.finrank ℂ (L.map (rowMap e))) (v : Fin (m + 2) → ℂ) :
    ∃ t ∈ L, ∃ γ : ℂ, ∀ j, v j = γ + t (e, j) := by
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
  have hv : v ∈ L.map (rowMap e) ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.mp hz
  refine ⟨t, ht, γ, fun j => ?_⟩
  rw [← hyz]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, rowMap_apply]
  ring

noncomputable def Bx (r : Fin 5) (p : Fin 4) (x : Fin 5 × Fin 5 → ℂ) (j : Fin 5) (q : Fin 4) : ℂ :=
  blk (fun a : Fin 3 => r.succAbove (p.succAbove a)) (fun b : Fin 3 => j.succAbove (q.succAbove b)) x

theorem thA5 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p)) (c : ℂ)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) :
    ∑ j : Fin 5, ∑ q : Fin 4,
      (c + t (r, j)) * (c + t (r.succAbove p, j.succAbove q)) * Bx r p x j q = 0 := by
  obtain ⟨hxL, hx1, hx2⟩ := (mem_rowsZero L r (r.succAbove p) x).mp hx
  exact thA (k := 3) (by norm_num) hL r p x hxL hx1 hx2 c t ht

theorem c4_left {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (ha' : 4 ≤ Module.finrank ℂ (L.map (rowMap (r.succAbove p))))
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p))
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) (ht0 : ∀ m, t (r.succAbove p, m) = 0)
    (z2 : Fin 5 → ℂ) :
    ∑ j : Fin 5, t (r, j) * ∑ q : Fin 4, z2 (j.succAbove q) * Bx r p x j q = 0 := by
  obtain ⟨u, hu, γ, hγ⟩ := row_onto (m := 3) hL (r.succAbove p) ha' z2
  have h1 := thA5 hL r p x hx γ (u + t) (L.add_mem hu ht)
  have h2 := thA5 hL r p x hx γ u hu
  have h3 : ∑ j : Fin 5, t (r, j) * ∑ q : Fin 4, z2 (j.succAbove q) * Bx r p x j q =
      (∑ j : Fin 5, ∑ q : Fin 4, (γ + (u + t) (r, j)) *
        (γ + (u + t) (r.succAbove p, j.succAbove q)) * Bx r p x j q) -
      ∑ j : Fin 5, ∑ q : Fin 4, (γ + u (r, j)) *
        (γ + u (r.succAbove p, j.succAbove q)) * Bx r p x j q := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (j.succAbove q), Pi.add_apply, Pi.add_apply, ht0 (j.succAbove q)]
    ring
  rw [h3, h1, h2, sub_zero]

theorem c4_right {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (ha : 4 ≤ Module.finrank ℂ (L.map (rowMap r)))
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p))
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) (ht0 : ∀ m, t (r, m) = 0) (z1 : Fin 5 → ℂ) :
    ∑ j : Fin 5, z1 j * ∑ q : Fin 4, t (r.succAbove p, j.succAbove q) * Bx r p x j q = 0 := by
  obtain ⟨u, hu, γ, hγ⟩ := row_onto (m := 3) hL r ha z1
  have h1 := thA5 hL r p x hx γ (u + t) (L.add_mem hu ht)
  have h2 := thA5 hL r p x hx γ u hu
  have h3 : ∑ j : Fin 5, z1 j * ∑ q : Fin 4, t (r.succAbove p, j.succAbove q) * Bx r p x j q =
      (∑ j : Fin 5, ∑ q : Fin 4, (γ + (u + t) (r, j)) *
        (γ + (u + t) (r.succAbove p, j.succAbove q)) * Bx r p x j q) -
      ∑ j : Fin 5, ∑ q : Fin 4, (γ + u (r, j)) *
        (γ + u (r.succAbove p, j.succAbove q)) * Bx r p x j q := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hγ j, Pi.add_apply, Pi.add_apply, ht0 j]
    ring
  rw [h3, h1, h2, sub_zero]

theorem sum_single_mul {n : ℕ} (a : Fin n) (G : Fin n → ℂ) :
    ∑ j, (Pi.single a 1 : Fin n → ℂ) j * G j = G a := by
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, one_mul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem sum_succAbove_single' (l : Fin 5) (q' : Fin 4) (j : Fin 5) (h : l.succAbove q' = j)
    (G : Fin 4 → ℂ) : ∑ q, (Pi.single j 1 : Fin 5 → ℂ) (l.succAbove q) * G q = G q' := by
  rw [Finset.sum_eq_single q']
  · rw [h, Pi.single_eq_same, one_mul]
  · intro q _ hq
    rw [Pi.single_eq_of_ne (fun h2 => hq (Fin.succAbove_right_injective (h2.trans h.symm))),
      zero_mul]
  · intro h2
    exact (h2 (Finset.mem_univ _)).elim

theorem sum_succAbove_single (j : Fin 5) (q0 : Fin 4) (G : Fin 4 → ℂ) :
    ∑ q, (Pi.single (j.succAbove q0) 1 : Fin 5 → ℂ) (j.succAbove q) * G q = G q0 :=
  sum_succAbove_single' j q0 (j.succAbove q0) rfl G

theorem sum_succAbove_self (j : Fin 5) (G : Fin 4 → ℂ) :
    ∑ q, (Pi.single j 1 : Fin 5 → ℂ) (j.succAbove q) * G q = 0 := by
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [Pi.single_eq_of_ne (Fin.succAbove_ne j q), zero_mul]

theorem sym5 : ∀ (j : Fin 5) (q q' : Fin 4), (j.succAbove q).succAbove q' = j →
    ∀ b : Fin 3, (j.succAbove q).succAbove (q'.succAbove b) = j.succAbove (q.succAbove b) := by
  decide

theorem Bx_symm (r : Fin 5) (p : Fin 4) (x : Fin 5 × Fin 5 → ℂ) (j : Fin 5) (q q' : Fin 4)
    (h : (j.succAbove q).succAbove q' = j) : Bx r p x (j.succAbove q) q' = Bx r p x j q := by
  unfold Bx
  have e : (fun b : Fin 3 => (j.succAbove q).succAbove (q'.succAbove b)) =
      fun b : Fin 3 => j.succAbove (q.succAbove b) := funext (sym5 j q q' h)
  rw [e]

def sa2 (r : Fin 5) (p : Fin 4) : (Unit ⊕ Unit) ⊕ Fin 3 ≃ Fin 5 :=
  (Equiv.sumAssoc Unit Unit (Fin 3)).trans
    ((Equiv.sumCongr (Equiv.refl Unit) ((Equiv.sumComm Unit (Fin 3)).trans (sa p))).trans
      ((Equiv.sumComm Unit (Fin 4)).trans (sa r)))

theorem sa2_inr (r : Fin 5) (p : Fin 4) (a : Fin 3) :
    sa2 r p (Sum.inr a) = r.succAbove (p.succAbove a) := by
  show sa r (Sum.inl (sa p (Sum.inl a))) = r.succAbove (p.succAbove a)
  rw [sa_inl, sa_inl]

theorem sa2_ll (r : Fin 5) (p : Fin 4) (u : Unit) : sa2 r p (Sum.inl (Sum.inl u)) = r := by
  show sa r (Sum.inr u) = r
  exact sa_inr r u

theorem sa2_lr (r : Fin 5) (p : Fin 4) (u : Unit) :
    sa2 r p (Sum.inl (Sum.inr u)) = r.succAbove p := by
  show sa r (Sum.inl (sa p (Sum.inr u))) = r.succAbove p
  rw [sa_inr, sa_inl]

theorem sa2_other (j0 : Fin 5) (q0 : Fin 4) (m : Fin 5) (h1 : m ≠ j0)
    (h2 : m ≠ j0.succAbove q0) : ∃ b : Fin 3, sa2 j0 q0 (Sum.inr b) = m := by
  obtain ⟨y, rfl⟩ := (sa2 j0 q0).surjective m
  rcases y with (u | u) | b
  · exact absurd (sa2_ll j0 q0 u) h1
  · exact absurd (sa2_lr j0 q0 u) h2
  · exact ⟨b, rfl⟩

noncomputable def rowT {n : ℕ} {α β : Type} (r : Fin n) (c : α ⊕ β ≃ Fin n) :
    ℂ × (Fin n × Fin n → ℂ) →ₗ[ℂ] (α → ℂ) where
  toFun w := fun a => w.1 + w.2 (r, c (Sum.inl a))
  map_add' x y := by
    funext a
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' k x := by
    funext a
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem c4_cols {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r (r.succAbove p)) + 7)
    (ha : 4 ≤ Module.finrank ℂ (L.map (rowMap r)))
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p)) (j0 : Fin 5) (q0 q' : Fin 4)
    (hq' : (j0.succAbove q0).succAbove q' = j0) (hne : Bx r p x j0 q0 ≠ 0)
    (f : Unit ⊕ Unit → ℂ) :
    ∃ t ∈ L, t (r, j0) = f (Sum.inl ()) ∧ t (r, j0.succAbove q0) = f (Sum.inr ()) ∧
      ∀ b : Fin 3, t (r, j0.succAbove (q0.succAbove b)) = 0 := by
  obtain ⟨hxL, hx1, hx2⟩ := (mem_rowsZero L r (r.succAbove p) x).mp hx
  have hne' : Bx r p x (j0.succAbove q0) q' ≠ 0 := by
    rw [Bx_symm r p x j0 q0 q' hq']
    exact hne
  have hxU : ((0 : ℂ), x) ∈ blockSpace L (sa2 r p) (sa2 j0 q0) := by
    rw [mem_blockSpace]
    refine ⟨hxL, fun a b => ?_⟩
    show (0 : ℂ) + x (sa2 r p (Sum.inl a), sa2 j0 q0 (Sum.inr b)) = 0
    rcases a with u | u
    · rw [sa2_ll, hx1, add_zero]
    · rw [sa2_lr, hx2, add_zero]
  have hblk : blk (fun b : Fin 3 => sa2 r p (Sum.inr b)) (fun b : Fin 3 => sa2 j0 q0 (Sum.inr b))
      (hat 5 ((0 : ℂ), x)) = Bx r p x j0 q0 := by
    have e1 : (fun b : Fin 3 => sa2 r p (Sum.inr b)) =
        fun a : Fin 3 => r.succAbove (p.succAbove a) := funext fun a => sa2_inr r p a
    have e2 : (fun b : Fin 3 => sa2 j0 q0 (Sum.inr b)) =
        fun b : Fin 3 => j0.succAbove (q0.succAbove b) := funext fun b => sa2_inr j0 q0 b
    have e3 : hat 5 ((0 : ℂ), x) = x := by
      funext p'
      show (0 : ℂ) + x p' = x p'
      rw [zero_add]
    rw [e1, e2, e3]
    rfl
  have hwit := (zbf_witness (n := 5) (by norm_num) hL (sa2 r p) (sa2 j0 q0) ((0 : ℂ), x) hxU rfl
    (by simp) (fun h0 => hne (hblk.symm.trans h0))).1
  have hdim := blockSpace_finrank_ge L (sa2 r p) (sa2 j0 q0)
  have hcard : Fintype.card (Unit ⊕ Unit) * Fintype.card (Fin 3) = 6 := by simp
  rw [hcard] at hdim
  have hrn := rank_nullity (blockSpace L (sa2 r p) (sa2 j0 q0)) (rowT r (sa2 j0 q0))
  have hrn2 := rank_nullity
    (blockSpace L (sa2 r p) (sa2 j0 q0) ⊓ LinearMap.ker (rowT r (sa2 j0 q0)))
    (LinearMap.snd ℂ ℂ (Fin 5 × Fin 5 → ℂ))
  have hbot : (blockSpace L (sa2 r p) (sa2 j0 q0) ⊓ LinearMap.ker (rowT r (sa2 j0 q0))) ⊓
      LinearMap.ker (LinearMap.snd ℂ ℂ (Fin 5 × Fin 5 → ℂ)) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨hwU, _⟩, hws⟩
    rw [Submodule.mem_bot]
    exact Prod.ext (hwit w hwU) (LinearMap.mem_ker.mp hws)
  have hle : (blockSpace L (sa2 r p) (sa2 j0 q0) ⊓ LinearMap.ker (rowT r (sa2 j0 q0))).map
      (LinearMap.snd ℂ ℂ (Fin 5 × Fin 5 → ℂ)) ≤ rowsZero L r (r.succAbove p) := by
    rintro _ ⟨w, ⟨hwU, hwk⟩, rfl⟩
    have hw1 := hwit w hwU
    have hw' := (mem_blockSpace L (sa2 r p) (sa2 j0 q0) w).mp hwU
    have hr0 : ∀ m, w.2 (r, m) = 0 := by
      intro m
      obtain ⟨y, rfl⟩ := (sa2 j0 q0).surjective m
      rcases y with a | b
      · have h3 : w.1 + w.2 (r, sa2 j0 q0 (Sum.inl a)) = 0 :=
          congrFun (LinearMap.mem_ker.mp hwk) a
        rw [hw1, zero_add] at h3
        exact h3
      · have h3 := hw'.2 (Sum.inl ()) b
        rw [sa2_ll, hw1, zero_add] at h3
        exact h3
    have hr'blk : ∀ b : Fin 3, w.2 (r.succAbove p, sa2 j0 q0 (Sum.inr b)) = 0 := by
      intro b
      have h3 := hw'.2 (Sum.inr ()) b
      rw [sa2_lr, hw1, zero_add] at h3
      exact h3
    have hR := c4_right hL r p ha x hx w.2 hw'.1 hr0
    have hl0 : w.2 (r.succAbove p, j0.succAbove q0) = 0 := by
      have h4 := hR (Pi.single j0 1)
      rw [sum_single_mul, Finset.sum_eq_single q0] at h4
      · exact (mul_eq_zero.mp h4).resolve_right hne
      · intro q _ hq
        obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hq
        rw [← hb, ← sa2_inr j0 q0 b, hr'blk b, zero_mul]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    have hj0 : w.2 (r.succAbove p, j0) = 0 := by
      have h4 := hR (Pi.single (j0.succAbove q0) 1)
      rw [sum_single_mul, Finset.sum_eq_single q'] at h4
      · rw [hq'] at h4
        exact (mul_eq_zero.mp h4).resolve_right hne'
      · intro q _ hq
        have hm1 : (j0.succAbove q0).succAbove q ≠ j0 := fun h =>
          hq (Fin.succAbove_right_injective (h.trans hq'.symm))
        have hm2 : (j0.succAbove q0).succAbove q ≠ j0.succAbove q0 := Fin.succAbove_ne _ _
        obtain ⟨b, hb⟩ := sa2_other j0 q0 _ hm1 hm2
        rw [← hb, hr'blk b, zero_mul]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [mem_rowsZero]
    refine ⟨hw'.1, hr0, fun m => ?_⟩
    obtain ⟨y, rfl⟩ := (sa2 j0 q0).surjective m
    rcases y with (u | u) | b
    · rw [sa2_ll]
      exact hj0
    · rw [sa2_lr]
      exact hl0
    · exact hr'blk b
  have h5 := Submodule.finrank_mono hle
  rw [hbot, finrank_bot, zero_add] at hrn2
  have h6 := Submodule.finrank_le
    ((blockSpace L (sa2 r p) (sa2 j0 q0)).map (rowT r (sa2 j0 q0)))
  have h7 : Module.finrank ℂ (Unit ⊕ Unit → ℂ) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [h7] at h6
  have htop : (blockSpace L (sa2 r p) (sa2 j0 q0)).map (rowT r (sa2 j0 q0)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [h7]
    omega
  have hf : f ∈ (blockSpace L (sa2 r p) (sa2 j0 q0)).map (rowT r (sa2 j0 q0)) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨w, hwU, hwf⟩ := hf
  have hw1 := hwit w hwU
  have hw' := (mem_blockSpace L (sa2 r p) (sa2 j0 q0) w).mp hwU
  refine ⟨w.2, hw'.1, ?_, ?_, fun b => ?_⟩
  · have h3 : w.1 + w.2 (r, sa2 j0 q0 (Sum.inl (Sum.inl ()))) = f (Sum.inl ()) :=
      congrFun hwf (Sum.inl ())
    rw [hw1, zero_add, sa2_ll] at h3
    exact h3
  · have h3 : w.1 + w.2 (r, sa2 j0 q0 (Sum.inl (Sum.inr ()))) = f (Sum.inr ()) :=
      congrFun hwf (Sum.inr ())
    rw [hw1, zero_add, sa2_lr] at h3
    exact h3
  · have h3 := hw'.2 (Sum.inl ()) b
    rw [sa2_ll, hw1, zero_add, sa2_inr] at h3
    exact h3

theorem c4 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r (r.succAbove p)) + 7)
    (ha : Module.finrank ℂ (L.map (rowMap r)) = 4)
    (ha' : Module.finrank ℂ (L.map (rowMap (r.succAbove p))) = 4)
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p)) (j0 : Fin 5) (q0 : Fin 4) :
    Bx r p x j0 q0 = 0 := by
  by_contra hne
  obtain ⟨q', hq'⟩ : ∃ q' : Fin 4, (j0.succAbove q0).succAbove q' = j0 :=
    Fin.exists_succAbove_eq (Fin.succAbove_ne j0 q0).symm
  have hne' : Bx r p x (j0.succAbove q0) q' ≠ 0 := by
    rw [Bx_symm r p x j0 q0 q' hq']
    exact hne
  have hA := rank_nullity L (rowMap (r.succAbove p))
  have hA2 := rank_nullity (L ⊓ LinearMap.ker (rowMap (r.succAbove p))) (rowMap r)
  have hX : (L ⊓ LinearMap.ker (rowMap (r.succAbove p))) ⊓ LinearMap.ker (rowMap r) =
      rowsZero L r (r.succAbove p) := by
    unfold rowsZero
    exact inf_right_comm _ _ _
  rw [hX] at hA2
  have hN1ker : ∀ t ∈ L ⊓ LinearMap.ker (rowMap (r.succAbove p)), ∀ z2 : Fin 5 → ℂ,
      ∑ j : Fin 5, t (r, j) * ∑ q : Fin 4, z2 (j.succAbove q) * Bx r p x j q = 0 := by
    intro t ht z2
    have ht' := Submodule.mem_inf.mp ht
    exact c4_left hL r p (le_of_eq ha'.symm) x hx t ht'.1
      (fun m => congrFun (LinearMap.mem_ker.mp ht'.2) m) z2
  have hnot1 : (Pi.single j0 1 : Fin 5 → ℂ) ∉
      (L ⊓ LinearMap.ker (rowMap (r.succAbove p))).map (rowMap r) := by
    rintro ⟨t, ht, he⟩
    have h1 := hN1ker t ht (Pi.single (j0.succAbove q0) 1)
    have h2 : ∑ j : Fin 5, (Pi.single j0 1 : Fin 5 → ℂ) j * ∑ q : Fin 4,
        (Pi.single (j0.succAbove q0) 1 : Fin 5 → ℂ) (j.succAbove q) * Bx r p x j q = 0 := by
      refine Eq.trans ?_ h1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← he]
      rfl
    rw [sum_single_mul, sum_succAbove_single] at h2
    exact hne h2
  have hnot2 : (Pi.single (j0.succAbove q0) 1 : Fin 5 → ℂ) ∉
      (L ⊓ LinearMap.ker (rowMap (r.succAbove p))).map (rowMap r) ⊔
        Submodule.span ℂ {(Pi.single j0 1 : Fin 5 → ℂ)} := by
    intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨t, ht, rfl⟩ := hy
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have h1 := hN1ker t ht (Pi.single j0 1)
    have htr : ∀ j, t (r, j) = (Pi.single (j0.succAbove q0) 1 : Fin 5 → ℂ) j -
        α * (Pi.single j0 1 : Fin 5 → ℂ) j := by
      intro j
      have h3 := congrFun hyz j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rowMap_apply] at h3
      linear_combination h3
    have h2 : (∑ j : Fin 5, (Pi.single (j0.succAbove q0) 1 : Fin 5 → ℂ) j * ∑ q : Fin 4,
        (Pi.single j0 1 : Fin 5 → ℂ) (j.succAbove q) * Bx r p x j q) -
        α * ∑ j : Fin 5, (Pi.single j0 1 : Fin 5 → ℂ) j * ∑ q : Fin 4,
          (Pi.single j0 1 : Fin 5 → ℂ) (j.succAbove q) * Bx r p x j q = 0 := by
      refine Eq.trans ?_ h1
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htr j]
      ring
    rw [sum_single_mul, sum_single_mul, sum_succAbove_self, mul_zero, sub_zero,
      sum_succAbove_single' (j0.succAbove q0) q' j0 hq'] at h2
    exact hne' h2
  have hmem1 : (Pi.single j0 1 : Fin 5 → ℂ) ∈ L.map (rowMap r) := by
    obtain ⟨t, htL, h1, h2, h3⟩ := c4_cols hL r p hmin (le_of_eq ha.symm) x hx j0 q0 q' hq' hne
      (Pi.single (Sum.inl ()) 1)
    refine ⟨t, htL, ?_⟩
    funext m
    obtain ⟨y, rfl⟩ := (sa2 j0 q0).surjective m
    rcases y with (u | u) | b
    · rw [sa2_ll, rowMap_apply, h1]
      simp
    · rw [sa2_lr, rowMap_apply, h2]
      simp [Pi.single_apply, Fin.succAbove_ne]
    · rw [sa2_inr, rowMap_apply, h3]
      simp [Pi.single_apply, Fin.succAbove_ne]
  have hmem2 : (Pi.single (j0.succAbove q0) 1 : Fin 5 → ℂ) ∈ L.map (rowMap r) := by
    obtain ⟨t, htL, h1, h2, h3⟩ := c4_cols hL r p hmin (le_of_eq ha.symm) x hx j0 q0 q' hq' hne
      (Pi.single (Sum.inr ()) 1)
    refine ⟨t, htL, ?_⟩
    funext m
    obtain ⟨y, rfl⟩ := (sa2 j0 q0).surjective m
    rcases y with (u | u) | b
    · rw [sa2_ll, rowMap_apply, h1]
      simp [Pi.single_apply, (Fin.succAbove_ne j0 q0).symm]
    · rw [sa2_lr, rowMap_apply, h2]
      simp
    · rw [sa2_inr, rowMap_apply, h3]
      simp [Pi.single_apply, Fin.succAbove_ne]
  have hf1 := finrank_sup_vec _ _ hnot1
  have hf2 := finrank_sup_vec _ _ hnot2
  have hle : ((L ⊓ LinearMap.ker (rowMap (r.succAbove p))).map (rowMap r) ⊔
      Submodule.span ℂ {(Pi.single j0 1 : Fin 5 → ℂ)}) ⊔
      Submodule.span ℂ {(Pi.single (j0.succAbove q0) 1 : Fin 5 → ℂ)} ≤ L.map (rowMap r) := by
    refine sup_le (sup_le (Submodule.map_mono inf_le_left) ?_) ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hmem1
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hmem2
  have h8 := Submodule.finrank_mono hle
  have e1 : Module.finrank ℂ L =
      Module.finrank ℂ (L ⊓ LinearMap.ker (rowMap (r.succAbove p)) :
        Submodule ℂ (Fin 5 × Fin 5 → ℂ)) +
      Module.finrank ℂ (L.map (rowMap (r.succAbove p))) := hA
  have e2 : Module.finrank ℂ (L ⊓ LinearMap.ker (rowMap (r.succAbove p)) :
        Submodule ℂ (Fin 5 × Fin 5 → ℂ)) =
      Module.finrank ℂ (rowsZero L r (r.succAbove p)) +
      Module.finrank ℂ ((L ⊓ LinearMap.ker (rowMap (r.succAbove p))).map (rowMap r)) := hA2
  clear hA hA2
  omega

theorem c7_sep {ι : Type} (ρ ρ' ω : ι → ℂ) (hω : ∀ j, ω j ≠ 0)
    (hd : ∀ j l, ρ j ≠ ρ l → ρ' j ≠ ρ' l → ω j + ω l = 0 ∧ ρ j + ρ' j = ρ l + ρ' l)
    (h1 : ∃ j l, ρ j ≠ ρ l) (h2 : ∃ j l, ρ' j ≠ ρ' l) :
    ∃ a b, ρ a ≠ ρ b ∧ ρ' a ≠ ρ' b ∧ ω a + ω b = 0 ∧ ρ a + ρ' a = ρ b + ρ' b ∧
      ∀ m, (ρ m = ρ a ∧ ρ' m = ρ' a) ∨ (ρ m = ρ b ∧ ρ' m = ρ' b) ∨
        (ρ m = ρ a ∧ ρ' m = ρ' b) := by
  have hex : ∃ a b, ρ a ≠ ρ b ∧ ρ' a ≠ ρ' b := by
    by_contra hno
    have hno' : ∀ a b, ρ a ≠ ρ b → ρ' a = ρ' b := by
      intro a b hab
      by_contra hab'
      exact hno ⟨a, b, hab, hab'⟩
    obtain ⟨j, l, hjl⟩ := h1
    obtain ⟨p, q, hpq⟩ := h2
    have hc : ∀ m, ρ' m = ρ' j := by
      intro m
      by_cases hm : ρ m = ρ j
      · have h3 : ρ m ≠ ρ l := by
          rw [hm]
          exact hjl
        exact (hno' m l h3).trans (hno' j l hjl).symm
      · exact hno' m j hm
    exact hpq ((hc p).trans (hc q).symm)
  obtain ⟨a, b, hab, hab'⟩ := hex
  obtain ⟨hωab, hσab⟩ := hd a b hab hab'
  have hfour : ∀ m, (ρ m = ρ a ∧ ρ' m = ρ' a) ∨ (ρ m = ρ b ∧ ρ' m = ρ' b) ∨
      (ρ m = ρ a ∧ ρ' m = ρ' b) ∨ (ρ m = ρ b ∧ ρ' m = ρ' a) := by
    intro m
    by_cases e1 : ρ m = ρ a
    · by_cases e2 : ρ' m = ρ' a
      · exact Or.inl ⟨e1, e2⟩
      · by_cases e4 : ρ' m = ρ' b
        · exact Or.inr (Or.inr (Or.inl ⟨e1, e4⟩))
        · have e3 : ρ m ≠ ρ b := by
            rw [e1]
            exact hab
          have h5 := (hd m b e3 e4).2
          have h6 : ρ' m = ρ' a := by linear_combination h5 - hσab - e1
          exact absurd h6 e2
    · by_cases e2 : ρ' m = ρ' a
      · by_cases e3 : ρ m = ρ b
        · exact Or.inr (Or.inr (Or.inr ⟨e3, e2⟩))
        · have e4 : ρ' m ≠ ρ' b := by
            rw [e2]
            exact hab'
          have h5 := (hd m b e3 e4).2
          have h6 : ρ m = ρ a := by linear_combination h5 - hσab - e2
          exact absurd h6 e1
      · obtain ⟨h7, h8⟩ := hd m a e1 e2
        by_cases e3 : ρ m = ρ b
        · have h6 : ρ' m = ρ' b := by linear_combination h8 + hσab - e3
          exact Or.inr (Or.inl ⟨e3, h6⟩)
        · by_cases e4 : ρ' m = ρ' b
          · have h6 : ρ m = ρ b := by linear_combination h8 + hσab - e4
            exact absurd h6 e3
          · obtain ⟨h9, _⟩ := hd m b e3 e4
            have h10 : (2 : ℂ) * ω a = 0 := by linear_combination h7 - h9 + hωab
            exact absurd ((mul_eq_zero.mp h10).resolve_left two_ne_zero) (hω a)
  by_cases hc2 : ∃ m2, ρ m2 = ρ b ∧ ρ' m2 = ρ' a
  · obtain ⟨m2, hm2, hm2'⟩ := hc2
    have hωba : ω b + ω a = 0 := by linear_combination hωab
    refine ⟨b, a, hab.symm, hab'.symm, hωba, hσab.symm, fun m => ?_⟩
    rcases hfour m with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exfalso
      have e1 : ρ m ≠ ρ m2 := by
        rw [h.1, hm2]
        exact hab
      have e2 : ρ' m ≠ ρ' m2 := by
        rw [h.2, hm2']
        exact hab'.symm
      have h5 := (hd m m2 e1 e2).2
      rw [h.1, h.2, hm2, hm2'] at h5
      have h6 : (2 : ℂ) * (ρ' a - ρ' b) = 0 := by linear_combination hσab - h5
      exact hab' (sub_eq_zero.mp ((mul_eq_zero.mp h6).resolve_left two_ne_zero))
    · exact Or.inr (Or.inr h)
  · refine ⟨a, b, hab, hab', hωab, hσab, fun m => ?_⟩
    rcases hfour m with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd ⟨m, h⟩ hc2

theorem c7_types {ι : Type} (ρ ρ' ω : ι → ℂ) (hω : ∀ j, ω j ≠ 0)
    (ha : ∀ j l, ρ j = ρ l → ρ' j ≠ ρ' l →
      ω j * (ρ j + ρ' j) + ω l * (ρ l + ρ' l) = 0)
    (hb : ∀ j l, ρ j ≠ ρ l → ρ' j = ρ' l →
      ω l * (ρ j + ρ' j) + ω j * (ρ l + ρ' l) = 0)
    (hd : ∀ j l, ρ j ≠ ρ l → ρ' j ≠ ρ' l → ω j + ω l = 0 ∧ ρ j + ρ' j = ρ l + ρ' l)
    (h1 : ∃ j l, ρ j ≠ ρ l) (h2 : ∃ j l, ρ' j ≠ ρ' l) :
    ∃ a b, ρ a ≠ ρ b ∧ ρ' a ≠ ρ' b ∧ ρ a + ρ' a = ρ b + ρ' b ∧
      ∀ m, (ρ m = ρ a ∧ ρ' m = ρ' a ∧ ω m = ω a) ∨
        (ρ m = ρ b ∧ ρ' m = ρ' b ∧ ω m = - ω a) ∨
        (ρ m = ρ a ∧ ρ' m = ρ' b ∧ ρ a + ρ' a ≠ 0 ∧ ω m ^ 2 = - ω a ^ 2 ∧
          (ρ a + ρ' b) ^ 2 = - (ρ a + ρ' a) ^ 2 ∧
          ω a * (ρ a + ρ' a) + ω m * (ρ a + ρ' b) = 0) := by
  obtain ⟨a, b, hab, hab', hωab, hσab, hall⟩ := c7_sep ρ ρ' ω hω hd h1 h2
  have corner : ∀ m, ρ m = ρ a → ρ' m = ρ' b →
      (ρ a + ρ' a ≠ 0 ∧ ω m ^ 2 = - ω a ^ 2 ∧ (ρ a + ρ' b) ^ 2 = - (ρ a + ρ' a) ^ 2 ∧
          ω a * (ρ a + ρ' a) + ω m * (ρ a + ρ' b) = 0) := by
    intro m hm hm'
    have e2 : ρ' a ≠ ρ' m := by
      rw [hm']
      exact hab'
    have h3 := ha a m hm.symm e2
    have e1 : ρ b ≠ ρ m := by
      rw [hm]
      exact hab.symm
    have h4 := hb b m e1 hm'.symm
    rw [hm, hm'] at h3 h4
    have h4' : ω m * (ρ a + ρ' a) - ω a * (ρ a + ρ' b) = 0 := by
      linear_combination h4 + ω m * hσab - (ρ a + ρ' b) * hωab
    have hs1 : ω a * ((ρ a + ρ' a) ^ 2 + (ρ a + ρ' b) ^ 2) = 0 := by
      linear_combination (ρ a + ρ' a) * h3 - (ρ a + ρ' b) * h4'
    have hs2 := (mul_eq_zero.mp hs1).resolve_left (hω a)
    have hst : (ρ a + ρ' b) ^ 2 = - (ρ a + ρ' a) ^ 2 := by linear_combination hs2
    have hsne : ρ a + ρ' a ≠ 0 := by
      intro h0
      have ht : (ρ a + ρ' b) * (ρ a + ρ' b) = 0 := by
        linear_combination hst - (ρ a + ρ' a) * h0
      have ht' := mul_self_eq_zero.mp ht
      apply hab'
      linear_combination h0 - ht'
    have hm1 : (ρ a + ρ' a) * (ω m ^ 2 + ω a ^ 2) = 0 := by
      linear_combination ω m * h4' + ω a * h3
    have hm2 := (mul_eq_zero.mp hm1).resolve_left hsne
    exact ⟨hsne, by linear_combination hm2, hst, h3⟩
  refine ⟨a, b, hab, hab', hσab, fun m => ?_⟩
  rcases hall m with h | h | h
  · refine Or.inl ⟨h.1, h.2, ?_⟩
    have e1 : ρ m ≠ ρ b := by
      rw [h.1]
      exact hab
    have e2 : ρ' m ≠ ρ' b := by
      rw [h.2]
      exact hab'
    have h3 := (hd m b e1 e2).1
    linear_combination h3 - hωab
  · refine Or.inr (Or.inl ⟨h.1, h.2, ?_⟩)
    have e1 : ρ m ≠ ρ a := by
      rw [h.1]
      exact hab.symm
    have e2 : ρ' m ≠ ρ' a := by
      rw [h.2]
      exact hab'.symm
    have h3 := (hd m a e1 e2).1
    linear_combination h3
  · exact Or.inr (Or.inr ⟨h.1, h.2, corner m h.1 h.2⟩)

theorem c7_tau (ρj ρl ρj' ρl' ωj ωl : ℂ) (hωj : ωj ≠ 0)
    (H : (∀ a1 a2 b1 b2 : ℂ, a1 + a2 = b1 + b2 →
          ρj * a1 + ρl * a2 + ρj' * b1 + ρl' * b2 = 0 → a1 + a2 = 0) ∨
        ∃ k : ℂ, ∀ a1 a2 b1 b2 : ℂ, a1 + a2 = b1 + b2 →
          ρj * a1 + ρl * a2 + ρj' * b1 + ρl' * b2 = 0 →
          ωj * a1 * b2 + ωl * a2 * b1 = k * (a1 + a2) ^ 2) :
    (ρj = ρl → ρj' ≠ ρl' → ωj * (ρj + ρj') + ωl * (ρl + ρl') = 0) ∧
      (ρj ≠ ρl → ρj' = ρl' → ωl * (ρj + ρj') + ωj * (ρl + ρl') = 0) ∧
      (ρj ≠ ρl → ρj' ≠ ρl' → ωj + ωl = 0 ∧ ρj + ρj' = ρl + ρl') := by
  refine ⟨fun e1 e2 => ?_, fun e1 e2 => ?_, fun e1 e2 => ?_⟩
  · subst e1
    rcases H with H | ⟨k, H⟩
    · have h := H (ρl' - ρj') 0 (ρj + ρl') (-(ρj + ρj')) (by ring) (by ring)
      have h2 : ρj' = ρl' := by linear_combination -h
      exact absurd h2 e2
    · have h0 := H (ρl' - ρj') 0 (ρj + ρl') (-(ρj + ρj')) (by ring) (by ring)
      have h1 := H (ρl' - ρj' + 1) (-1) (ρj + ρl') (-(ρj + ρj')) (by ring) (by ring)
      linear_combination h0 - h1
  · subst e2
    rcases H with H | ⟨k, H⟩
    · have h := H (ρl + ρj') (-(ρj + ρj')) (ρl - ρj) 0 (by ring) (by ring)
      have h2 : ρj = ρl := by linear_combination -h
      exact absurd h2 e1
    · have h0 := H (ρl + ρj') (-(ρj + ρj')) (ρl - ρj) 0 (by ring) (by ring)
      have h1 := H (ρl + ρj') (-(ρj + ρj')) (ρl - ρj + 1) (-1) (by ring) (by ring)
      linear_combination h0 - h1
  · rcases H with H | ⟨k, H⟩
    · have h := H (-ρl - ρj') (ρj + ρj') (ρj - ρl) 0 (by ring) (by ring)
      have h2 : ρj = ρl := by linear_combination h
      exact absurd h2 e1
    · have hs := H (ρj' - ρl') (-(ρj' - ρl')) (ρl - ρj) (-(ρl - ρj)) (by ring) (by ring)
      have h0 := H (-ρl - ρj') (ρj + ρj') (ρj - ρl) 0 (by ring) (by ring)
      have h1 := H (-ρl - ρj' + (ρj' - ρl')) (ρj + ρj' - (ρj' - ρl')) (ρj - ρl + (ρl - ρj))
        (-(ρl - ρj)) (by ring) (by ring)
      have hA : (ρj' - ρl') * ((ρl - ρj) * (ωj + ωl)) = 0 := by linear_combination -hs
      have hω0 : ωj + ωl = 0 := by
        rcases mul_eq_zero.mp hA with h3 | h3
        · exact absurd (sub_eq_zero.mp h3) e2
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd (sub_eq_zero.mp h4).symm e1
          · exact h4
      have hB : (ρj - ρl) * (ωj * (ρl + ρl' - (ρj + ρj'))) = 0 := by
        linear_combination h0 - h1 - (ρj - ρl) * (ρj + ρj') * hω0
      refine ⟨hω0, ?_⟩
      rcases mul_eq_zero.mp hB with h3 | h3
      · exact absurd (sub_eq_zero.mp h3) e1
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 hωj
        · linear_combination -h4

theorem c7_pair_x (kj kl ωj ωl ρj ρl ρj' ρl' : ℂ) (hkj : kj ≠ 0) (hkl : kl ≠ 0) (hωj : ωj ≠ 0)
    (hωl : ωl ≠ 0)
    (H : (∀ x1 x2 y1 y2 : ℂ, kj * x1 + kl * x2 = ωj * kj * y1 + ωl * kl * y2 →
          ρj * kj * x1 + ρl * kl * x2 + ρj' * (ωj * kj) * y1 + ρl' * (ωl * kl) * y2 = 0 →
          kj * x1 + kl * x2 = 0) ∨
        ∃ k : ℂ, ∀ x1 x2 y1 y2 : ℂ, kj * x1 + kl * x2 = ωj * kj * y1 + ωl * kl * y2 →
          ρj * kj * x1 + ρl * kl * x2 + ρj' * (ωj * kj) * y1 + ρl' * (ωl * kl) * y2 = 0 →
          x1 * y2 + x2 * y1 = k * (kj * x1 + kl * x2) ^ 2) :
    (ρj = ρl → ρj' ≠ ρl' → ωj * (ρj + ρj') + ωl * (ρl + ρl') = 0) ∧
      (ρj ≠ ρl → ρj' = ρl' → ωl * (ρj + ρj') + ωj * (ρl + ρl') = 0) ∧
      (ρj ≠ ρl → ρj' ≠ ρl' → ωj + ωl = 0 ∧ ρj + ρj' = ρl + ρl') := by
  have hP : kj * kl * ωj * ωl ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hkj hkl) hωj) hωl
  apply c7_tau ρj ρl ρj' ρl' ωj ωl hωj
  rcases H with H | ⟨k, H⟩
  · left
    intro a1 a2 b1 b2 h1 h2
    have h := H (a1 * (kl * ωj * ωl)) (a2 * (kj * ωj * ωl)) (b1 * (kl * ωl)) (b2 * (kj * ωj))
      (by linear_combination (kj * kl * ωj * ωl) * h1)
      (by linear_combination (kj * kl * ωj * ωl) * h2)
    have h3 : (kj * kl * ωj * ωl) * (a1 + a2) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h3).resolve_left hP
  · right
    refine ⟨k * (kj * kl * ωj * ωl), fun a1 a2 b1 b2 h1 h2 => ?_⟩
    have h := H (a1 * (kl * ωj * ωl)) (a2 * (kj * ωj * ωl)) (b1 * (kl * ωl)) (b2 * (kj * ωj))
      (by linear_combination (kj * kl * ωj * ωl) * h1)
      (by linear_combination (kj * kl * ωj * ωl) * h2)
    have h3 : (kj * kl * ωj * ωl) * (ωj * a1 * b2 + ωl * a2 * b1 -
        k * (kj * kl * ωj * ωl) * (a1 + a2) ^ 2) = 0 := by linear_combination h
    have h4 := (mul_eq_zero.mp h3).resolve_left hP
    linear_combination h4

theorem c7_pair_thB {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' j l : Fin 5)
    (hr : r ≠ r') (hjl : j ≠ l) (kj kl kj' kl' nj nl nj' nl' : ℂ)
    (hI : ∀ x1 x2 y1 y2 : ℂ, kj * x1 + kl * x2 = kj' * y1 + kl' * y2 →
      nj * x1 + nl * x2 + nj' * y1 + nl' * y2 = 0 →
      ∃ w ∈ pairSpace L r r' j l, w.1 = kj * x1 + kl * x2 ∧ w.1 + w.2 (r, j) = x1 ∧
        w.1 + w.2 (r, l) = x2 ∧ w.1 + w.2 (r', j) = y1 ∧ w.1 + w.2 (r', l) = y2) :
    (∀ x1 x2 y1 y2 : ℂ, kj * x1 + kl * x2 = kj' * y1 + kl' * y2 →
        nj * x1 + nl * x2 + nj' * y1 + nl' * y2 = 0 → kj * x1 + kl * x2 = 0) ∨
      ∃ k : ℂ, ∀ x1 x2 y1 y2 : ℂ, kj * x1 + kl * x2 = kj' * y1 + kl' * y2 →
        nj * x1 + nl * x2 + nj' * y1 + nl' * y2 = 0 →
        x1 * y2 + x2 * y1 = k * (kj * x1 + kl * x2) ^ 2 := by
  by_cases hex : ∃ u0 ∈ pairSpace L r r' j l, u0.1 = 1
  · obtain ⟨u0, hu0, h0⟩ := hex
    have hq : ∀ w ∈ pairSpace L r r' j l,
        (w.1 + w.2 (r, j)) * (w.1 + w.2 (r', l)) + (w.1 + w.2 (r, l)) * (w.1 + w.2 (r', j)) =
          ((u0.1 + u0.2 (r, j)) * (u0.1 + u0.2 (r', l)) +
            (u0.1 + u0.2 (r, l)) * (u0.1 + u0.2 (r', j))) * w.1 ^ 2 :=
      (thB_pair (m := 3) hL r r' j l hr hjl u0 hu0 h0).2.2
    right
    refine ⟨(u0.1 + u0.2 (r, j)) * (u0.1 + u0.2 (r', l)) +
      (u0.1 + u0.2 (r, l)) * (u0.1 + u0.2 (r', j)), fun x1 x2 y1 y2 c1 c2 => ?_⟩
    obtain ⟨w, hw, hw1, e1, e2, e3, e4⟩ := hI x1 x2 y1 y2 c1 c2
    have h := hq w hw
    rw [e1, e2, e3, e4, hw1] at h
    exact h
  · left
    intro x1 x2 y1 y2 c1 c2
    obtain ⟨w, hw, hw1, _⟩ := hI x1 x2 y1 y2 c1 c2
    by_contra hne
    apply hex
    refine ⟨w.1⁻¹ • w, (pairSpace L r r' j l).smul_mem _ hw, ?_⟩
    rw [Prod.smul_fst, smul_eq_mul, inv_mul_cancel₀]
    rw [hw1]
    exact hne

theorem c7_rows {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r') (κ ω ρ ρ' : Fin 5 → ℂ) (hκ : ∀ j, κ j ≠ 0) (hω : ∀ j, ω j ≠ 0)
    (hI : ∀ j l, j ≠ l → ∀ x1 x2 y1 y2 : ℂ,
      κ j * x1 + κ l * x2 = ω j * κ j * y1 + ω l * κ l * y2 →
      ρ j * κ j * x1 + ρ l * κ l * x2 + ρ' j * (ω j * κ j) * y1 + ρ' l * (ω l * κ l) * y2 = 0 →
      ∃ w ∈ pairSpace L r r' j l, w.1 = κ j * x1 + κ l * x2 ∧ w.1 + w.2 (r, j) = x1 ∧
        w.1 + w.2 (r, l) = x2 ∧ w.1 + w.2 (r', j) = y1 ∧ w.1 + w.2 (r', l) = y2)
    (h1 : ∃ j l, ρ j ≠ ρ l) (h2 : ∃ j l, ρ' j ≠ ρ' l) :
    ∃ a b, ρ a ≠ ρ b ∧ ρ' a ≠ ρ' b ∧ ρ a + ρ' a = ρ b + ρ' b ∧
      ∀ m, (ρ m = ρ a ∧ ρ' m = ρ' a ∧ ω m = ω a) ∨
        (ρ m = ρ b ∧ ρ' m = ρ' b ∧ ω m = - ω a) ∨
        (ρ m = ρ a ∧ ρ' m = ρ' b ∧ ρ a + ρ' a ≠ 0 ∧ ω m ^ 2 = - ω a ^ 2 ∧
          (ρ a + ρ' b) ^ 2 = - (ρ a + ρ' a) ^ 2 ∧
          ω a * (ρ a + ρ' a) + ω m * (ρ a + ρ' b) = 0) := by
  have hpair : ∀ j l, j ≠ l →
      (ρ j = ρ l → ρ' j ≠ ρ' l → ω j * (ρ j + ρ' j) + ω l * (ρ l + ρ' l) = 0) ∧
      (ρ j ≠ ρ l → ρ' j = ρ' l → ω l * (ρ j + ρ' j) + ω j * (ρ l + ρ' l) = 0) ∧
      (ρ j ≠ ρ l → ρ' j ≠ ρ' l → ω j + ω l = 0 ∧ ρ j + ρ' j = ρ l + ρ' l) := by
    intro j l hjl
    exact c7_pair_x (κ j) (κ l) (ω j) (ω l) (ρ j) (ρ l) (ρ' j) (ρ' l) (hκ j) (hκ l) (hω j)
      (hω l) (c7_pair_thB hL r r' j l hr hjl (κ j) (κ l) (ω j * κ j) (ω l * κ l) (ρ j * κ j)
        (ρ l * κ l) (ρ' j * (ω j * κ j)) (ρ' l * (ω l * κ l)) (hI j l hjl))
  refine c7_types ρ ρ' ω hω (fun j l e1 e2 => ?_) (fun j l e1 e2 => ?_) (fun j l e1 e2 => ?_)
    h1 h2
  · have hjl : j ≠ l := by
      rintro rfl
      exact e2 rfl
    exact (hpair j l hjl).1 e1 e2
  · have hjl : j ≠ l := by
      rintro rfl
      exact e1 rfl
    exact (hpair j l hjl).2.1 e1 e2
  · have hjl : j ≠ l := by
      rintro rfl
      exact e1 rfl
    exact (hpair j l hjl).2.2 e1 e2

theorem c7_lift {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (f1 f2 : (Fin 5 → ℂ) × (Fin 5 → ℂ) →ₗ[ℂ] ℂ)
    (hf1 : ∀ t ∈ L, f1 (rowMap r t, rowMap r' t) = 0)
    (hf1J : f1 ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0)
    (hf2 : ∀ t ∈ L, f2 (rowMap r t, rowMap r' t) = 0)
    (hf2J : f2 ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0)
    (v1 v2 : (Fin 5 → ℂ) × (Fin 5 → ℂ)) (hv1 : f1 v1 ≠ 0) (hv21 : f1 v2 = 0) (hv22 : f2 v2 ≠ 0)
    (z : (Fin 5 → ℂ) × (Fin 5 → ℂ)) (hz1 : f1 z = 0) (hz2 : f2 z = 0) :
    ∃ c : ℂ, ∃ t ∈ L, (∀ m, z.1 m = c + t (r, m)) ∧ ∀ m, z.2 m = c + t (r', m) := by
  have hk : L ⊓ LinearMap.ker ((rowMap r).prod (rowMap r')) = rowsZero L r r' := by
    unfold rowsZero
    rw [LinearMap.ker_prod]
    exact (inf_assoc _ _ _).symm
  have hrn : Module.finrank ℂ L =
      Module.finrank ℂ (L ⊓ LinearMap.ker ((rowMap r).prod (rowMap r')) :
        Submodule ℂ (Fin 5 × Fin 5 → ℂ)) +
      Module.finrank ℂ (L.map ((rowMap r).prod (rowMap r'))) := rank_nullity L _
  rw [hk] at hrn
  have hJ : (((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) : (Fin 5 → ℂ) × (Fin 5 → ℂ)) ∉
      L.map ((rowMap r).prod (rowMap r')) := by
    rintro ⟨t, ht, h⟩
    exact one_not_mem_row hL L le_rfl r ⟨t, ht, congrArg Prod.fst h⟩
  have hJ1 := finrank_sup_vec _ _ hJ
  obtain ⟨I0, hI0⟩ : ∃ I0 : Submodule ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)),
      I0 = L.map ((rowMap r).prod (rowMap r')) ⊔
        Submodule.span ℂ {(((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) : (Fin 5 → ℂ) × (Fin 5 → ℂ))} :=
    ⟨_, rfl⟩
  rw [← hI0] at hJ1
  have hfin : Module.finrank ℂ I0 = 8 := by omega
  have hI1 : I0 ≤ LinearMap.ker f1 := by
    rw [hI0]
    refine sup_le ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      rw [LinearMap.mem_ker]
      exact hf1 t ht
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact hf1J
  have hI2 : I0 ≤ LinearMap.ker f2 := by
    rw [hI0]
    refine sup_le ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      rw [LinearMap.mem_ker]
      exact hf2 t ht
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact hf2J
  by_cases hz : z ∈ I0
  · rw [hI0] at hz
    obtain ⟨y, hy, x, hx, hyx⟩ := Submodule.mem_sup.mp hz
    obtain ⟨t, ht, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨c, t, ht, fun m => ?_, fun m => ?_⟩
    · have h3 : t (r, m) + c * 1 = z.1 m := congrFun (congrArg Prod.fst hyx) m
      rw [← h3]
      ring
    · have h3 : t (r', m) + c * 1 = z.2 m := congrFun (congrArg Prod.snd hyx) m
      rw [← h3]
      ring
  · exfalso
    have h9 := finrank_sup_vec I0 z hz
    have hA1 : I0 ⊔ Submodule.span ℂ {z} ≤ LinearMap.ker f1 := by
      refine sup_le hI1 ?_
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact hz1
    have hA2 : I0 ⊔ Submodule.span ℂ {z} ≤ LinearMap.ker f2 := by
      refine sup_le hI2 ?_
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact hz2
    have hv2n : v2 ∉ I0 ⊔ Submodule.span ℂ {z} := fun h => hv22 (LinearMap.mem_ker.mp (hA2 h))
    have h10 := finrank_sup_vec _ v2 hv2n
    have hB1 : (I0 ⊔ Submodule.span ℂ {z}) ⊔ Submodule.span ℂ {v2} ≤ LinearMap.ker f1 := by
      refine sup_le hA1 ?_
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact hv21
    have hv1n : v1 ∉ (I0 ⊔ Submodule.span ℂ {z}) ⊔ Submodule.span ℂ {v2} :=
      fun h => hv1 (LinearMap.mem_ker.mp (hB1 h))
    have h11 := finrank_sup_vec _ v1 hv1n
    have h12 := Submodule.finrank_le
      (((I0 ⊔ Submodule.span ℂ {z}) ⊔ Submodule.span ℂ {v2}) ⊔ Submodule.span ℂ {v1})
    have hV : Module.finrank ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)) = 5 + 5 := by
      rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega

noncomputable def dotL {n : ℕ} (κ : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ m, z m * κ m
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' k x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem dotL_apply {n : ℕ} (κ z : Fin n → ℂ) : dotL κ z = ∑ m, z m * κ m := rfl

theorem dotL_single {n : ℕ} (κ : Fin n → ℂ) (a : Fin n) :
    dotL κ (Pi.single a 1) = κ a := sum_single_mul a κ

theorem dotL_two {n : ℕ} (κ : Fin n → ℂ) (j l : Fin n) (x1 x2 : ℂ) :
    dotL κ (x1 • (Pi.single j 1 : Fin n → ℂ) + x2 • (Pi.single l 1 : Fin n → ℂ)) =
      x1 * κ j + x2 * κ l := by
  rw [map_add, map_smul, map_smul, dotL_single, dotL_single, smul_eq_mul, smul_eq_mul]

noncomputable def relM {n : ℕ} (α β : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (dotL α).comp (LinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ)) -
    (dotL β).comp (LinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))

theorem relM_apply {n : ℕ} (α β : Fin n → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    relM α β z = dotL α z.1 - dotL β z.2 := rfl

noncomputable def relP {n : ℕ} (α β : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (dotL α).comp (LinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ)) +
    (dotL β).comp (LinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))

theorem relP_apply {n : ℕ} (α β : Fin n → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    relP α β z = dotL α z.1 + dotL β z.2 := rfl

theorem two_single_eval (j l : Fin 5) (hjl : j ≠ l) (x1 x2 : ℂ) :
    (x1 • (Pi.single j 1 : Fin 5 → ℂ) + x2 • (Pi.single l 1 : Fin 5 → ℂ)) j = x1 ∧
      (x1 • (Pi.single j 1 : Fin 5 → ℂ) + x2 • (Pi.single l 1 : Fin 5 → ℂ)) l = x2 ∧
      ∀ m, m ≠ j → m ≠ l →
        (x1 • (Pi.single j 1 : Fin 5 → ℂ) + x2 • (Pi.single l 1 : Fin 5 → ℂ)) m = 0 := by
  refine ⟨?_, ?_, fun m h1 h2 => ?_⟩
  · simp [Pi.single_apply, hjl]
  · simp [Pi.single_apply, hjl.symm]
  · simp [Pi.single_apply, h1, h2]

theorem c7_hI {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (κ κ' ν ν' : Fin 5 → ℂ)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0) (hκ1 : dotL κ 1 = 1)
    (hκ'L : ∀ t ∈ L, dotL κ' (rowMap r' t) = 0) (hκ'1 : dotL κ' 1 = 1)
    (hνL : ∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0)
    (hν1 : dotL ν 1 + dotL ν' 1 = 0)
    (j0 j1 l1 : Fin 5) (hκj0 : κ j0 ≠ 0) (hdet : κ l1 * ν j1 - κ j1 * ν l1 ≠ 0)
    (j l : Fin 5) (hjl : j ≠ l) (x1 x2 y1 y2 : ℂ)
    (c1 : κ j * x1 + κ l * x2 = κ' j * y1 + κ' l * y2)
    (c2 : ν j * x1 + ν l * x2 + ν' j * y1 + ν' l * y2 = 0) :
    ∃ w ∈ pairSpace L r r' j l, w.1 = κ j * x1 + κ l * x2 ∧ w.1 + w.2 (r, j) = x1 ∧
      w.1 + w.2 (r, l) = x2 ∧ w.1 + w.2 (r', j) = y1 ∧ w.1 + w.2 (r', l) = y2 := by
  obtain ⟨za, hza⟩ : ∃ za : Fin 5 → ℂ,
      za = x1 • (Pi.single j 1 : Fin 5 → ℂ) + x2 • (Pi.single l 1 : Fin 5 → ℂ) := ⟨_, rfl⟩
  obtain ⟨zb, hzb⟩ : ∃ zb : Fin 5 → ℂ,
      zb = y1 • (Pi.single j 1 : Fin 5 → ℂ) + y2 • (Pi.single l 1 : Fin 5 → ℂ) := ⟨_, rfl⟩
  have hda : ∀ α : Fin 5 → ℂ, dotL α za = x1 * α j + x2 * α l := by
    intro α
    rw [hza, dotL_two]
  have hdb : ∀ α : Fin 5 → ℂ, dotL α zb = y1 * α j + y2 * α l := by
    intro α
    rw [hzb, dotL_two]
  have hz1 : relM κ κ' (za, zb) = 0 := by
    rw [relM_apply, hda, hdb]
    linear_combination c1
  have hz2 : relP ν ν' (za, zb) = 0 := by
    rw [relP_apply, hda, hdb]
    linear_combination c2
  have hf1 : ∀ t ∈ L, relM κ κ' (rowMap r t, rowMap r' t) = 0 := by
    intro t ht
    rw [relM_apply, hκL t ht, hκ'L t ht, sub_zero]
  have hf1J : relM κ κ' ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0 := by
    rw [relM_apply, hκ1, hκ'1, sub_self]
  have hf2 : ∀ t ∈ L, relP ν ν' (rowMap r t, rowMap r' t) = 0 := by
    intro t ht
    rw [relP_apply]
    exact hνL t ht
  have hf2J : relP ν ν' ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0 := by
    rw [relP_apply]
    exact hν1
  have hv1 : relM κ κ' ((Pi.single j0 1 : Fin 5 → ℂ), (0 : Fin 5 → ℂ)) ≠ 0 := by
    rw [relM_apply, dotL_single, map_zero, sub_zero]
    exact hκj0
  have hv21 : relM κ κ' (κ l1 • (Pi.single j1 1 : Fin 5 → ℂ) +
      (-κ j1) • (Pi.single l1 1 : Fin 5 → ℂ), (0 : Fin 5 → ℂ)) = 0 := by
    rw [relM_apply, dotL_two, map_zero]
    ring
  have hv22 : relP ν ν' (κ l1 • (Pi.single j1 1 : Fin 5 → ℂ) +
      (-κ j1) • (Pi.single l1 1 : Fin 5 → ℂ), (0 : Fin 5 → ℂ)) ≠ 0 := by
    rw [relP_apply, dotL_two, map_zero]
    intro h
    apply hdet
    linear_combination h
  obtain ⟨c, t, ht, hr1, hr2⟩ := c7_lift hL r r' hmin (relM κ κ') (relP ν ν') hf1 hf1J hf2 hf2J
    _ _ hv1 hv21 hv22 (za, zb) hz1 hz2
  have hr1' : ∀ m, za m = c + t (r, m) := hr1
  have hr2' : ∀ m, zb m = c + t (r', m) := hr2
  have hea := two_single_eval j l hjl x1 x2
  have heb := two_single_eval j l hjl y1 y2
  rw [← hza] at hea
  rw [← hzb] at heb
  have hzeq : za = c • (1 : Fin 5 → ℂ) + rowMap r t := by
    funext m
    rw [hr1' m]
    simp [rowMap_apply]
  have hc : c = κ j * x1 + κ l * x2 := by
    have h5 := hda κ
    rw [hzeq, map_add, map_smul, hκ1, hκL t ht, smul_eq_mul, mul_one, add_zero] at h5
    linear_combination h5
  refine ⟨(c, t), ?_, hc, ?_, ?_, ?_, ?_⟩
  · refine (mem_pairSpace L r r' j l (c, t)).mpr ⟨ht, fun m h1 h2 => ⟨?_, ?_⟩⟩
    · show c + t (r, m) = 0
      rw [← hr1' m]
      exact hea.2.2 m h1 h2
    · show c + t (r', m) = 0
      rw [← hr2' m]
      exact heb.2.2 m h1 h2
  · show c + t (r, j) = x1
    rw [← hr1' j]
    exact hea.1
  · show c + t (r, l) = x2
    rw [← hr1' l]
    exact hea.2.1
  · show c + t (r', j) = y1
    rw [← hr2' j]
    exact heb.1
  · show c + t (r', l) = y2
    rw [← hr2' l]
    exact heb.2.1

theorem c7_rows_full {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (κ ω ρ ρ' : Fin 5 → ℂ) (hκ : ∀ j, κ j ≠ 0) (hω : ∀ j, ω j ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0) (hκ1 : dotL κ 1 = 1)
    (hκ'L : ∀ t ∈ L, dotL (fun m => ω m * κ m) (rowMap r' t) = 0)
    (hκ'1 : dotL (fun m => ω m * κ m) 1 = 1)
    (hνL : ∀ t ∈ L, dotL (fun m => ρ m * κ m) (rowMap r t) +
      dotL (fun m => ρ' m * (ω m * κ m)) (rowMap r' t) = 0)
    (hν1 : dotL (fun m => ρ m * κ m) 1 + dotL (fun m => ρ' m * (ω m * κ m)) 1 = 0)
    (h1 : ∃ j l, ρ j ≠ ρ l) (h2 : ∃ j l, ρ' j ≠ ρ' l) :
    ∃ a b, ρ a ≠ ρ b ∧ ρ' a ≠ ρ' b ∧ ρ a + ρ' a = ρ b + ρ' b ∧
      ∀ m, (ρ m = ρ a ∧ ρ' m = ρ' a ∧ ω m = ω a) ∨
        (ρ m = ρ b ∧ ρ' m = ρ' b ∧ ω m = - ω a) ∨
        (ρ m = ρ a ∧ ρ' m = ρ' b ∧ ρ a + ρ' a ≠ 0 ∧ ω m ^ 2 = - ω a ^ 2 ∧
          (ρ a + ρ' b) ^ 2 = - (ρ a + ρ' a) ^ 2 ∧
          ω a * (ρ a + ρ' a) + ω m * (ρ a + ρ' b) = 0) := by
  obtain ⟨j1, l1, hjl1⟩ := h1
  have hdet : κ l1 * (ρ j1 * κ j1) - κ j1 * (ρ l1 * κ l1) ≠ 0 := by
    intro h
    have h3 : κ j1 * (κ l1 * (ρ j1 - ρ l1)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hκ j1 h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact hκ l1 h5
      · exact hjl1 (sub_eq_zero.mp h5)
  refine c7_rows hL r r' hr κ ω ρ ρ' hκ hω (fun j l hjl x1 x2 y1 y2 c1 c2 => ?_)
    ⟨j1, l1, hjl1⟩ h2
  exact c7_hI hL r r' hmin κ (fun m => ω m * κ m) (fun m => ρ m * κ m)
    (fun m => ρ' m * (ω m * κ m)) hκL hκ1 hκ'L hκ'1 hνL hν1 j1 j1 l1 (hκ j1) hdet j l hjl
    x1 x2 y1 y2 c1 c2

theorem dot_zero_of_row {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (e : Fin 5)
    (hrank : 4 ≤ Module.finrank ℂ (L.map (rowMap e))) (μ : Fin 5 → ℂ)
    (hμL : ∀ t ∈ L, dotL μ (rowMap e t) = 0) (hμ1 : dotL μ 1 = 0) : ∀ m, μ m = 0 := by
  intro m
  obtain ⟨t, ht, γ, hγ⟩ := row_onto (m := 3) hL e hrank (Pi.single m 1)
  have hv : (Pi.single m 1 : Fin 5 → ℂ) = γ • (1 : Fin 5 → ℂ) + rowMap e t := by
    funext j
    rw [hγ j]
    simp [rowMap_apply]
  have h := dotL_single μ m
  rw [hv, map_add, map_smul, hμ1, hμL t ht, smul_zero, add_zero] at h
  exact h.symm

theorem dotL_comb {n : ℕ} (α β : Fin n → ℂ) (s : ℂ) (z : Fin n → ℂ) :
    dotL (fun m => α m + s * β m) z = dotL α z + s * dotL β z := by
  rw [dotL_apply, dotL_apply, dotL_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem c7_rows_ind {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (ha : 4 ≤ Module.finrank ℂ (L.map (rowMap r)))
    (ha' : 4 ≤ Module.finrank ℂ (L.map (rowMap r')))
    (κ ω ρ ρ' : Fin 5 → ℂ) (hκ : ∀ j, κ j ≠ 0) (hω : ∀ j, ω j ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0) (hκ1 : dotL κ 1 = 1)
    (hκ'L : ∀ t ∈ L, dotL (fun m => ω m * κ m) (rowMap r' t) = 0)
    (hκ'1 : dotL (fun m => ω m * κ m) 1 = 1)
    (hνL : ∀ t ∈ L, dotL (fun m => ρ m * κ m) (rowMap r t) +
      dotL (fun m => ρ' m * (ω m * κ m)) (rowMap r' t) = 0)
    (hν1 : dotL (fun m => ρ m * κ m) 1 + dotL (fun m => ρ' m * (ω m * κ m)) 1 = 0)
    (hind : ¬ ∃ s : ℂ, (∀ m, ρ m = s) ∧ ∀ m, ρ' m = -s) :
    ∃ a b, ρ a ≠ ρ b ∧ ρ' a ≠ ρ' b ∧ ρ a + ρ' a = ρ b + ρ' b ∧
      ∀ m, (ρ m = ρ a ∧ ρ' m = ρ' a ∧ ω m = ω a) ∨
        (ρ m = ρ b ∧ ρ' m = ρ' b ∧ ω m = - ω a) ∨
        (ρ m = ρ a ∧ ρ' m = ρ' b ∧ ρ a + ρ' a ≠ 0 ∧ ω m ^ 2 = - ω a ^ 2 ∧
          (ρ a + ρ' b) ^ 2 = - (ρ a + ρ' a) ^ 2 ∧
          ω a * (ρ a + ρ' a) + ω m * (ρ a + ρ' b) = 0) := by
  have h1 : ∃ j l, ρ j ≠ ρ l := by
    by_contra hno
    have hc : ∀ m, ρ m = ρ 0 := fun m => by
      by_contra hm
      exact hno ⟨m, 0, hm⟩
    have hνs : ∀ z, dotL (fun m => ρ m * κ m) z = ρ 0 * dotL κ z := by
      intro z
      rw [dotL_apply, dotL_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc m]
      ring
    have hL0 : ∀ t ∈ L, dotL (fun m => ρ' m * (ω m * κ m) + ρ 0 * (ω m * κ m))
        (rowMap r' t) = 0 := by
      intro t ht
      have e := dotL_comb (fun m => ρ' m * (ω m * κ m)) (fun m => ω m * κ m) (ρ 0)
        (rowMap r' t)
      have h5 := hνL t ht
      rw [hνs, hκL t ht, mul_zero, zero_add] at h5
      exact e.trans (by rw [h5, hκ'L t ht, mul_zero, add_zero])
    have h10 : dotL (fun m => ρ' m * (ω m * κ m) + ρ 0 * (ω m * κ m)) 1 = 0 := by
      have e := dotL_comb (fun m => ρ' m * (ω m * κ m)) (fun m => ω m * κ m) (ρ 0) 1
      have h5 := hν1
      rw [hνs, hκ1, mul_one] at h5
      exact e.trans (by rw [hκ'1, mul_one]; linear_combination h5)
    apply hind
    refine ⟨ρ 0, hc, fun m => ?_⟩
    have hμ : ρ' m * (ω m * κ m) + ρ 0 * (ω m * κ m) = 0 :=
      dot_zero_of_row hL r' ha' _ hL0 h10 m
    have h6 : (ρ' m + ρ 0) * (ω m * κ m) = 0 := by linear_combination hμ
    rcases mul_eq_zero.mp h6 with h7 | h7
    · linear_combination h7
    · exact absurd h7 (mul_ne_zero (hω m) (hκ m))
  have h2 : ∃ j l, ρ' j ≠ ρ' l := by
    by_contra hno
    have hc : ∀ m, ρ' m = ρ' 0 := fun m => by
      by_contra hm
      exact hno ⟨m, 0, hm⟩
    have hνs : ∀ z, dotL (fun m => ρ' m * (ω m * κ m)) z =
        ρ' 0 * dotL (fun m => ω m * κ m) z := by
      intro z
      rw [dotL_apply, dotL_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc m]
      ring
    have hL0 : ∀ t ∈ L, dotL (fun m => ρ m * κ m + ρ' 0 * κ m) (rowMap r t) = 0 := by
      intro t ht
      have e := dotL_comb (fun m => ρ m * κ m) κ (ρ' 0) (rowMap r t)
      have h5 := hνL t ht
      rw [hνs, hκ'L t ht, mul_zero, add_zero] at h5
      exact e.trans (by rw [h5, hκL t ht, mul_zero, add_zero])
    have h10 : dotL (fun m => ρ m * κ m + ρ' 0 * κ m) 1 = 0 := by
      have e := dotL_comb (fun m => ρ m * κ m) κ (ρ' 0) 1
      have h5 := hν1
      rw [hνs, hκ'1, mul_one] at h5
      exact e.trans (by rw [hκ1, mul_one]; exact h5)
    apply hind
    refine ⟨-ρ' 0, fun m => ?_, fun m => ?_⟩
    · have hμ : ρ m * κ m + ρ' 0 * κ m = 0 := dot_zero_of_row hL r ha _ hL0 h10 m
      have h6 : (ρ m + ρ' 0) * κ m = 0 := by linear_combination hμ
      rcases mul_eq_zero.mp h6 with h7 | h7
      · linear_combination h7
      · exact absurd h7 (hκ m)
    · rw [neg_neg]
      exact hc m
  exact c7_rows_full hL r r' hr hmin κ ω ρ ρ' hκ hω hκL hκ1 hκ'L hκ'1 hνL hν1 h1 h2

theorem dual_eq_dotL {n : ℕ} (φ : (Fin n → ℂ) →ₗ[ℂ] ℂ) (z : Fin n → ℂ) :
    φ z = dotL (fun i => φ (Pi.single i 1)) z := by
  have hz : φ z = φ (∑ i, z i • (Pi.single i 1 : Fin n → ℂ)) :=
    congrArg (fun y => φ y) (pi_eq_sum_univ' z)
  rw [hz, map_sum, dotL_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

theorem fk_annihilator {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) :
    ∃ κ : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 := by
  obtain ⟨φ, hφ1, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (one_not_mem_row hL L le_rfl r) inferInstance
  have hφL : ∀ t ∈ L, φ (rowMap r t) = 0 := by
    intro t ht
    have h3 : φ (rowMap r t) ∈ (L.map (rowMap r)).map φ := ⟨rowMap r t, ⟨t, ht, rfl⟩, rfl⟩
    rw [hφ0] at h3
    exact (Submodule.mem_bot ℂ).mp h3
  refine ⟨fun i => ((φ 1)⁻¹ • φ) (Pi.single i 1), fun t ht => ?_, ?_⟩
  · exact (dual_eq_dotL ((φ 1)⁻¹ • φ) (rowMap r t)).symm.trans
      (by rw [LinearMap.smul_apply, hφL t ht, smul_zero])
  · exact (dual_eq_dotL ((φ 1)⁻¹ • φ) 1).symm.trans
      (by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ1])

theorem second_relation {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (f1 : (Fin 5 → ℂ) × (Fin 5 → ℂ) →ₗ[ℂ] ℂ)
    (hf1 : ∀ t ∈ L, f1 (rowMap r t, rowMap r' t) = 0)
    (hf1J : f1 ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0)
    (v1 : (Fin 5 → ℂ) × (Fin 5 → ℂ)) (hv1 : f1 v1 ≠ 0) :
    ∃ g : (Fin 5 → ℂ) × (Fin 5 → ℂ) →ₗ[ℂ] ℂ,
      (∀ t ∈ L, g (rowMap r t, rowMap r' t) = 0) ∧
      g ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0 ∧ g v1 = 0 ∧ ∃ x, g x ≠ 0 := by
  have hk : L ⊓ LinearMap.ker ((rowMap r).prod (rowMap r')) = rowsZero L r r' := by
    unfold rowsZero
    rw [LinearMap.ker_prod]
    exact (inf_assoc _ _ _).symm
  have hrn : Module.finrank ℂ L =
      Module.finrank ℂ (L ⊓ LinearMap.ker ((rowMap r).prod (rowMap r')) :
        Submodule ℂ (Fin 5 × Fin 5 → ℂ)) +
      Module.finrank ℂ (L.map ((rowMap r).prod (rowMap r'))) := rank_nullity L _
  rw [hk] at hrn
  have hJ : (((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) : (Fin 5 → ℂ) × (Fin 5 → ℂ)) ∉
      L.map ((rowMap r).prod (rowMap r')) := by
    rintro ⟨t, ht, h⟩
    exact one_not_mem_row hL L le_rfl r ⟨t, ht, congrArg Prod.fst h⟩
  have hJ1 := finrank_sup_vec _ _ hJ
  obtain ⟨I0, hI0⟩ : ∃ I0 : Submodule ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)),
      I0 = L.map ((rowMap r).prod (rowMap r')) ⊔
        Submodule.span ℂ {(((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) : (Fin 5 → ℂ) × (Fin 5 → ℂ))} :=
    ⟨_, rfl⟩
  rw [← hI0] at hJ1
  have hfin : Module.finrank ℂ I0 = 8 := by omega
  have hI1 : I0 ≤ LinearMap.ker f1 := by
    rw [hI0]
    refine sup_le ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      rw [LinearMap.mem_ker]
      exact hf1 t ht
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact hf1J
  have hv1n : v1 ∉ I0 := fun h => hv1 (LinearMap.mem_ker.mp (hI1 h))
  have h9 := finrank_sup_vec I0 v1 hv1n
  obtain ⟨I1, hI1def⟩ : ∃ I1 : Submodule ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)),
      I1 = I0 ⊔ Submodule.span ℂ {v1} := ⟨_, rfl⟩
  rw [← hI1def] at h9
  have hV : Module.finrank ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)) = 5 + 5 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ I1 := by
    by_contra hno
    have hall : ∀ x, x ∈ I1 := fun x => by
      by_contra hx
      exact hno ⟨x, hx⟩
    have htop : I1 = ⊤ := Submodule.eq_top_iff'.mpr hall
    have h13 : Module.finrank ℂ I1 = Module.finrank ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)) := by
      rw [htop, finrank_top]
    omega
  obtain ⟨g, hgx, hg0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hgI : ∀ y ∈ I1, g y = 0 := by
    intro y hy
    have h3 : g y ∈ I1.map g := ⟨y, hy, rfl⟩
    rw [hg0] at h3
    exact (Submodule.mem_bot ℂ).mp h3
  have hI0le : I0 ≤ I1 := by
    rw [hI1def]
    exact le_sup_left
  refine ⟨g, fun t ht => ?_, ?_, ?_, x, hgx⟩
  · apply hgI
    apply hI0le
    rw [hI0]
    exact Submodule.mem_sup_left ⟨t, ht, rfl⟩
  · apply hgI
    apply hI0le
    rw [hI0]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · apply hgI
    rw [hI1def]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem c7_final {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (ha : 4 ≤ Module.finrank ℂ (L.map (rowMap r)))
    (ha' : 4 ≤ Module.finrank ℂ (L.map (rowMap r'))) :
    ∃ κ κ' ν ν' : Fin 5 → ℂ,
      (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
      (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧
      (∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0) ∧
      dotL ν 1 + dotL ν' 1 = 0 ∧
      ((∀ j, κ j ≠ 0) → (∀ j, κ' j ≠ 0) →
        ∃ a b, ν a / κ a ≠ ν b / κ b ∧ ν' a / κ' a ≠ ν' b / κ' b ∧
          ν a / κ a + ν' a / κ' a = ν b / κ b + ν' b / κ' b ∧
          ∀ m, (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' a / κ' a ∧
              κ' m / κ m = κ' a / κ a) ∨
            (ν m / κ m = ν b / κ b ∧ ν' m / κ' m = ν' b / κ' b ∧
              κ' m / κ m = - (κ' a / κ a)) ∨
            (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b ∧
              ν a / κ a + ν' a / κ' a ≠ 0 ∧ (κ' m / κ m) ^ 2 = - (κ' a / κ a) ^ 2 ∧
              (ν a / κ a + ν' b / κ' b) ^ 2 = - (ν a / κ a + ν' a / κ' a) ^ 2 ∧
              κ' a / κ a * (ν a / κ a + ν' a / κ' a) +
                κ' m / κ m * (ν a / κ a + ν' b / κ' b) = 0)) := by
  obtain ⟨κ, hκL, hκ1⟩ := fk_annihilator hL r
  obtain ⟨κ', hκ'L, hκ'1⟩ := fk_annihilator hL r'
  have hf1 : ∀ t ∈ L, relM κ κ' (rowMap r t, rowMap r' t) = 0 := by
    intro t ht
    rw [relM_apply, hκL t ht, hκ'L t ht, sub_zero]
  have hf1J : relM κ κ' ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0 := by
    rw [relM_apply, hκ1, hκ'1, sub_self]
  have hv1 : relM κ κ' ((1 : Fin 5 → ℂ), (0 : Fin 5 → ℂ)) = 1 := by
    rw [relM_apply, hκ1, map_zero, sub_zero]
  obtain ⟨g, hgL, hgJ, hgv1, x, hgx⟩ := second_relation hL r r' hmin (relM κ κ') hf1 hf1J
    ((1 : Fin 5 → ℂ), (0 : Fin 5 → ℂ)) (by rw [hv1]; exact one_ne_zero)
  have hgrel : ∀ z : (Fin 5 → ℂ) × (Fin 5 → ℂ), g z =
      dotL (fun i => g (LinearMap.inl ℂ (Fin 5 → ℂ) (Fin 5 → ℂ) (Pi.single i 1))) z.1 +
      dotL (fun i => g (LinearMap.inr ℂ (Fin 5 → ℂ) (Fin 5 → ℂ) (Pi.single i 1))) z.2 := by
    intro z
    have e1 := dual_eq_dotL (g.comp (LinearMap.inl ℂ (Fin 5 → ℂ) (Fin 5 → ℂ))) z.1
    have e2 := dual_eq_dotL (g.comp (LinearMap.inr ℂ (Fin 5 → ℂ) (Fin 5 → ℂ))) z.2
    have e3 : g z = g (LinearMap.inl ℂ (Fin 5 → ℂ) (Fin 5 → ℂ) z.1) +
        g (LinearMap.inr ℂ (Fin 5 → ℂ) (Fin 5 → ℂ) z.2) := by
      rw [← map_add]
      congr 1
      rw [LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
    rw [e3]
    exact congrArg₂ (· + ·) e1 e2
  obtain ⟨ν, hν⟩ : ∃ ν : Fin 5 → ℂ,
      ν = fun i => g (LinearMap.inl ℂ (Fin 5 → ℂ) (Fin 5 → ℂ) (Pi.single i 1)) := ⟨_, rfl⟩
  obtain ⟨ν', hν'⟩ : ∃ ν' : Fin 5 → ℂ,
      ν' = fun i => g (LinearMap.inr ℂ (Fin 5 → ℂ) (Fin 5 → ℂ) (Pi.single i 1)) := ⟨_, rfl⟩
  rw [← hν, ← hν'] at hgrel
  have hνL : ∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0 := by
    intro t ht
    have h := hgL t ht
    rw [hgrel] at h
    exact h
  have hν1 : dotL ν 1 + dotL ν' 1 = 0 := by
    have h := hgJ
    rw [hgrel] at h
    exact h
  refine ⟨κ, κ', ν, ν', hκL, hκ1, hκ'L, hκ'1, hνL, hν1, fun hκ0 hκ'0 => ?_⟩
  have e1 : (fun m => κ' m / κ m * κ m) = κ' := funext fun m => div_mul_cancel₀ _ (hκ0 m)
  have e2 : (fun m => ν m / κ m * κ m) = ν := funext fun m => div_mul_cancel₀ _ (hκ0 m)
  have e3 : (fun m => ν' m / κ' m * (κ' m / κ m * κ m)) = ν' := funext fun m => by
    rw [div_mul_cancel₀ _ (hκ0 m), div_mul_cancel₀ _ (hκ'0 m)]
  have hω : ∀ j, κ' j / κ j ≠ 0 := fun j => div_ne_zero (hκ'0 j) (hκ0 j)
  have q1 : ∀ t ∈ L, dotL (fun m => κ' m / κ m * κ m) (rowMap r' t) = 0 := by
    rw [e1]
    exact hκ'L
  have q2 : dotL (fun m => κ' m / κ m * κ m) 1 = 1 := by
    rw [e1]
    exact hκ'1
  have q3 : ∀ t ∈ L, dotL (fun m => ν m / κ m * κ m) (rowMap r t) +
      dotL (fun m => ν' m / κ' m * (κ' m / κ m * κ m)) (rowMap r' t) = 0 := by
    rw [e2, e3]
    exact hνL
  have q4 : dotL (fun m => ν m / κ m * κ m) 1 +
      dotL (fun m => ν' m / κ' m * (κ' m / κ m * κ m)) 1 = 0 := by
    rw [e2, e3]
    exact hν1
  have hind : ¬ ∃ s : ℂ, (∀ m, ν m / κ m = s) ∧ ∀ m, ν' m / κ' m = -s := by
    rintro ⟨s, hs1, hs2⟩
    have hνs : ∀ z, dotL ν z = s * dotL κ z := by
      intro z
      rw [dotL_apply, dotL_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h4 : ν m = s * κ m := by
        rw [← hs1 m, div_mul_cancel₀ _ (hκ0 m)]
      rw [h4]
      ring
    have hν's : ∀ z, dotL ν' z = -s * dotL κ' z := by
      intro z
      rw [dotL_apply, dotL_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h4 : ν' m = -s * κ' m := by
        rw [← hs2 m, div_mul_cancel₀ _ (hκ'0 m)]
      rw [h4]
      ring
    have hgs : ∀ z, g z = s * relM κ κ' z := by
      intro z
      rw [hgrel, hνs, hν's, relM_apply]
      ring
    have h5 := hgs ((1 : Fin 5 → ℂ), (0 : Fin 5 → ℂ))
    rw [hgv1, hv1, mul_one] at h5
    apply hgx
    rw [hgs, ← h5, zero_mul]
  exact c7_rows_ind hL r r' hr hmin ha ha' κ (fun m => κ' m / κ m) (fun m => ν m / κ m)
    (fun m => ν' m / κ' m) hκ0 hω hκL hκ1 q1 q2 q3 q4 hind

noncomputable def dotD {N : ℕ} : (Fin N → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin N → ℂ) :=
  LinearMap.mk₂ ℂ (fun a z => ∑ m, z m * a m)
    (fun a b z => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun k a z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)
    (fun a z z' => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun k a z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)

theorem dotD_apply {N : ℕ} (a z : Fin N → ℂ) : dotD a z = ∑ m, z m * a m := rfl

theorem dotD_injective {N : ℕ} : Function.Injective (dotD (N := N)) := by
  intro a b hab
  funext m
  have h : dotD a (Pi.single m 1) = dotD b (Pi.single m 1) := by rw [hab]
  rw [dotD_apply, dotD_apply, sum_single_mul, sum_single_mul] at h
  exact h

theorem perp_bound {N : ℕ} (A B : Submodule ℂ (Fin N → ℂ))
    (h : ∀ a ∈ A, ∀ b ∈ B, ∑ m, b m * a m = 0) :
    Module.finrank ℂ A + Module.finrank ℂ B ≤ N := by
  have hle : A.map dotD ≤ B.dualAnnihilator := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro b hb
    exact h a ha b hb
  have e1 : Module.finrank ℂ (A.map dotD) = Module.finrank ℂ A :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ dotD_injective A)).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq B
  have e3 := Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at e2
  omega

theorem rank_one_bound {N : ℕ} (A B : Submodule ℂ (Fin N → ℂ)) (f : (Fin N → ℂ) →ₗ[ℂ] ℂ)
    (g : (Fin N → ℂ) → ℂ) (h : ∀ a ∈ A, ∀ b ∈ B, ∑ m, b m * a m = f a * g b) :
    Module.finrank ℂ A + Module.finrank ℂ B ≤ N + 1 := by
  have h1 := perp_bound (A ⊓ LinearMap.ker f) B (fun a ha b hb => by
    rw [h a (Submodule.mem_inf.mp ha).1 b hb, LinearMap.mem_ker.mp (Submodule.mem_inf.mp ha).2,
      zero_mul])
  have h2 : Module.finrank ℂ A =
      Module.finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ (Fin N → ℂ)) +
      Module.finrank ℂ (A.map f) := rank_nullity A f
  have h3 := Submodule.finrank_le (A.map f)
  rw [Module.finrank_self] at h3
  omega

end PEqualNP.Outside.L_gct_210_aux.ZBF

theorem PEqualNP.Outside.L_gct_210_zbf : (∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) → (∀ (c : ℂ), ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (c + t (i, f i))) = 120 * c ^ 5) ∧ (∀ r1 r2 : Fin 5, r1 ≠ r2 → Module.finrank ℂ L ≤ Module.finrank ℂ (PEqualNP.Outside.L_gct_210_aux.ZBF.rowsZero L r1 r2) + 7) ∧ ∀ c1 c2 : Fin 5, c1 ≠ c2 → Module.finrank ℂ L ≤ Module.finrank ℂ (PEqualNP.Outside.L_gct_210_aux.ZBF.colsZero L c1 c2) + 7) ∧ (∀ (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)), (∑ f : Fin 3 ↪ Fin 3, ∏ i, b (i, f i)) ≠ 0 → (∀ η ∈ V0, (∑ f : Fin 3 ↪ Fin 3, ∏ i, (b (i, f i) + η (i, f i))) = ∑ f : Fin 3 ↪ Fin 3, ∏ i, b (i, f i)) → Module.finrank ℂ V0 ≤ 3) ∧ ∀ (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r : Fin 5) (p : Fin 4), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) → Module.finrank ℂ L = Module.finrank ℂ (PEqualNP.Outside.L_gct_210_aux.ZBF.rowsZero L r (r.succAbove p)) + 7 → Module.finrank ℂ (L.map (PEqualNP.Outside.L_gct_210_aux.ZBF.rowMap r)) = 4 → Module.finrank ℂ (L.map (PEqualNP.Outside.L_gct_210_aux.ZBF.rowMap (r.succAbove p))) = 4 → ∀ x ∈ PEqualNP.Outside.L_gct_210_aux.ZBF.rowsZero L r (r.succAbove p), ∀ (j0 : Fin 5) (q0 : Fin 4), PEqualNP.Outside.L_gct_210_aux.ZBF.Bx r p x j0 q0 = 0 := by
  refine ⟨fun L hL => ⟨fun c t ht => ?_, fun r1 r2 hr => ?_, fun c1 c2 hc => ?_⟩, fun b V0 hb h => ?_,
    fun L r p hL hmin ha ha' x hx j0 q0 => ?_⟩
  · have h := PEqualNP.Outside.L_gct_210_aux.ZBF.lev_scale_emb (PEqualNP.Outside.L_gct_210_aux.ZBF.lev_five L hL) c t ht
    rw [h]
    norm_num [Nat.factorial]
  · exact PEqualNP.Outside.L_gct_210_aux.ZBF.lemmaC (PEqualNP.Outside.L_gct_210_aux.ZBF.lev_five L hL) r1 r2 hr
  · exact PEqualNP.Outside.L_gct_210_aux.ZBF.lemmaC_col (PEqualNP.Outside.L_gct_210_aux.ZBF.lev_five L hL) c1 c2 hc
  · rw [← PEqualNP.Outside.L_gct_210_aux.ZBF.pm_emb b] at hb
    refine PEqualNP.Outside.L_gct_210_aux.ZBF.n3prime b V0 hb (fun η hη => ?_)
    have h1 := h η hη
    rw [← PEqualNP.Outside.L_gct_210_aux.ZBF.pm_emb b] at h1
    rw [← h1, PEqualNP.Outside.L_gct_210_aux.ZBF.pm_emb (b + η)]
    rfl
  · exact PEqualNP.Outside.L_gct_210_aux.ZBF.c4 (PEqualNP.Outside.L_gct_210_aux.ZBF.lev_five L hL) r p hmin ha ha' x hx j0 q0
