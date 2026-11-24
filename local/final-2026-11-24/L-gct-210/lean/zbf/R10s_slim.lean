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
  sorry

theorem sum_emb_eq_sum_perm {n : ℕ} (F : (Fin n → Fin n) → ℂ) :
    (∑ f : Fin n ↪ Fin n, F f) = ∑ σ : Equiv.Perm (Fin n), F σ := by
  sorry

theorem pm_emb {n : ℕ} (u : Fin n × Fin n → ℂ) :
    pm u = ∑ f : Fin n ↪ Fin n, ∏ i, u (i, f i) := by
  sorry

def Lev (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) : Prop :=
  ∀ t ∈ L, (∑ f : Fin n ↪ Fin n, ∏ i, (1 + t (i, f i))) = (Nat.factorial n : ℂ)

theorem lev_five (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) : Lev 5 L := by
  sorry

theorem poly_zero_of_ne (P : Polynomial ℂ) (h : ∀ c : ℂ, c ≠ 0 → P.eval c = 0) : P = 0 := by
  sorry

theorem lev_scale_ne {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (hc : c ≠ 0) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => c + t p) = (Nat.factorial n : ℂ) * c ^ n := by
  sorry

theorem lev_scale {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => c + t p) = (Nat.factorial n : ℂ) * c ^ n := by
  sorry

theorem lev_scale_emb {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    (∑ f : Fin n ↪ Fin n, ∏ i, (c + t (i, f i))) = (Nat.factorial n : ℂ) * c ^ n := by
  sorry

theorem lev_line {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c s : ℂ) (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) :
    pm (fun p => c + t p + s * x p) = (Nat.factorial n : ℂ) * c ^ n := by
  sorry

theorem lev_line_const {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c s : ℂ) (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) :
    pm (fun p => c + t p + s * x p) = pm (fun p => c + t p) := by
  sorry

theorem lev_FK {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) (h : pm (fun p => c + t p) = 0) : c = 0 := by
  sorry

theorem perm_sum_block {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) ℂ) (h : ∀ a b, M (Sum.inr b) (Sum.inl a) = 0) :
    M.permanent =
      (M.submatrix Sum.inl Sum.inl).permanent * (M.submatrix Sum.inr Sum.inr).permanent := by
  sorry

theorem perm_submatrix_equiv {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (r c : m ≃ n) : (M.submatrix r c).permanent = M.permanent := by
  sorry

theorem perm_zero_block {n α β : Type} [Fintype n] [DecidableEq n] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix n n ℂ) (r c : α ⊕ β ≃ n)
    (h : ∀ a b, M (r (Sum.inr b)) (c (Sum.inl a)) = 0) :
    M.permanent =
      (M.submatrix (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a))).permanent *
        (M.submatrix (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b))).permanent := by
  sorry

theorem perm_zero_block' {n α β : Type} [Fintype n] [DecidableEq n] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix n n ℂ) (r c : α ⊕ β ≃ n)
    (h : ∀ a b, M (r (Sum.inl a)) (c (Sum.inr b)) = 0) :
    M.permanent =
      (M.submatrix (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a))).permanent *
        (M.submatrix (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b))).permanent := by
  sorry

theorem pm_zero_block {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (u : Fin n × Fin n → ℂ) (r c : α ⊕ β ≃ Fin n)
    (h : ∀ a b, u (r (Sum.inl a), c (Sum.inr b)) = 0) :
    pm u = blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) u *
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) u := by
  sorry

theorem poly_const_of_mul (P Q : Polynomial ℂ) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ s : ℂ, P.eval s * Q.eval s = k) : ∀ s : ℂ, P.eval s = P.eval 0 := by
  sorry

def PolyLine {V : Type} [AddCommGroup V] [Module ℂ V] (f : V → ℂ) : Prop :=
  ∀ u v : V, ∃ P : Polynomial ℂ, ∀ s : ℂ, f (u + s • v) = P.eval s

theorem polyLine_comp {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (φ : V →ₗ[ℂ] W) (f : W → ℂ) (hf : PolyLine f) : PolyLine (fun v => f (φ v)) := by
  sorry

theorem polyLine_blk {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n) :
    PolyLine (blk ρ κ) := by
  sorry

theorem blk_smul {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n) (a : ℂ)
    (u : Fin n × Fin n → ℂ) : blk ρ κ (a • u) = a ^ Fintype.card m * blk ρ κ u := by
  sorry

theorem line_const {V : Type} [AddCommGroup V] [Module ℂ V] (f g : V → ℂ) (hf : PolyLine f)
    (hg : PolyLine g) (u v : V) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ s : ℂ, f (u + s • v) * g (u + s • v) = k) : ∀ s : ℂ, f (u + s • v) = f u := by
  sorry

theorem ufd_unit_ne {V : Type} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V)
    (ell : V →ₗ[ℂ] ℂ) (f g : V → ℂ) (hf : PolyLine f) (hg : PolyLine g) (df N : ℕ)
    (hfh : ∀ (a : ℂ) (w : V), f (a • w) = a ^ df * f w) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ w ∈ U, f w * g w = k * ell w ^ N) (u0 : V) (hu0 : u0 ∈ U) (h0 : ell u0 = 1)
    (w : V) (hw : w ∈ U) (hc : ell w ≠ 0) : f w = f u0 * ell w ^ df := by
  sorry

theorem ufd_unit {V : Type} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V)
    (ell : V →ₗ[ℂ] ℂ) (f g : V → ℂ) (hf : PolyLine f) (hg : PolyLine g) (df N : ℕ)
    (hfh : ∀ (a : ℂ) (w : V), f (a • w) = a ^ df * f w) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ w ∈ U, f w * g w = k * ell w ^ N) (u0 : V) (hu0 : u0 ∈ U) (h0 : ell u0 = 1)
    (w : V) (hw : w ∈ U) : f w = f u0 * ell w ^ df := by
  sorry

theorem ufd_zero {V : Type} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V)
    (f g : V → ℂ) (hf : PolyLine f) (hg : PolyLine g) (h : ∀ w ∈ U, f w * g w = 0) :
    (∀ w ∈ U, f w = 0) ∨ (∀ w ∈ U, g w = 0) := by
  sorry

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

theorem hat_eq (n : ℕ) (w : ℂ × (Fin n × Fin n → ℂ)) : hat n w = fun p => w.1 + w.2 p := by
  sorry

theorem hat_apply (n : ℕ) (w : ℂ × (Fin n × Fin n → ℂ)) (p : Fin n × Fin n) :
    hat n w p = w.1 + w.2 p := by
  sorry

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
      w.2 ∈ L ∧ ∀ a b, w.1 + w.2 (r (Sum.inl a), c (Sum.inr b)) = 0 := by
  sorry

theorem zbf_prod {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) *
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) =
      (Nat.factorial n : ℂ) * (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ) w) ^ n := by
  sorry

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
  sorry

theorem zbf_zero {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (r c : α ⊕ β ≃ Fin n) (hU : ∀ w ∈ blockSpace L r c, w.1 = 0) :
    (∀ w ∈ blockSpace L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) = 0) ∨
      (∀ w ∈ blockSpace L r c,
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0) := by
  sorry

theorem rank_nullity {V W : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [AddCommGroup W] [Module ℂ W] (L : Submodule ℂ V) (f : V →ₗ[ℂ] W) :
    Module.finrank ℂ L = Module.finrank ℂ (L ⊓ LinearMap.ker f : Submodule ℂ V) +
      Module.finrank ℂ (L.map f) := by
  sorry

def rowMap {n : ℕ} (r : Fin n) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun t := fun j => t (r, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rowMap_apply {n : ℕ} (r : Fin n) (t : Fin n × Fin n → ℂ) (j : Fin n) :
    rowMap r t j = t (r, j) := by
  sorry

def rowsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    Submodule ℂ (Fin n × Fin n → ℂ) :=
  L ⊓ LinearMap.ker (rowMap r1) ⊓ LinearMap.ker (rowMap r2)

theorem mem_rowsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n)
    (t : Fin n × Fin n → ℂ) :
    t ∈ rowsZero L r1 r2 ↔ t ∈ L ∧ (∀ j, t (r1, j) = 0) ∧ ∀ j, t (r2, j) = 0 := by
  sorry

theorem rowsZero_comm {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    rowsZero L r1 r2 = rowsZero L r2 r1 := by
  sorry

theorem pm_zero_row {n : ℕ} (u : Fin n × Fin n → ℂ) (r : Fin n) (h : ∀ j, u (r, j) = 0) :
    pm u = 0 := by
  sorry

theorem lev_FK_row {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) (r : Fin n) (h : ∀ j, c + t (r, j) = 0) :
    c = 0 := by
  sorry

def q0 (z : Fin 2 × Fin 2 → ℂ) : ℂ := z (0, 0) * z (1, 1) + z (0, 1) * z (1, 0)

theorem permanent_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A.permanent = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
  sorry

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
    blockProj r c w (a, a') = w.1 + w.2 (r (Sum.inl a), c (Sum.inl a')) := by
  sorry

theorem blk_two {n : ℕ} {β : Type} (r c : Fin 2 ⊕ β ≃ Fin n) (w : ℂ × (Fin n × Fin n → ℂ)) :
    blk (fun a : Fin 2 => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) =
      q0 (blockProj r c w) := by
  sorry

noncomputable def bDual : (Fin 2 × Fin 2 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 2 × Fin 2 → ℂ) :=
  LinearMap.mk₂ ℂ (fun v z => v (0, 0) * z (1, 1) + v (1, 1) * z (0, 0) + v (0, 1) * z (1, 0) +
      v (1, 0) * z (0, 1))
    (fun a b z => by simp only [Pi.add_apply]; ring)
    (fun k a z => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun v a b => by simp only [Pi.add_apply]; ring)
    (fun k v a => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem bDual_apply (v z : Fin 2 × Fin 2 → ℂ) :
    bDual v z = v (0, 0) * z (1, 1) + v (1, 1) * z (0, 0) + v (0, 1) * z (1, 0) +
      v (1, 0) * z (0, 1) := by
  sorry

theorem q0_polar (z z' : Fin 2 × Fin 2 → ℂ) : q0 (z + z') - q0 z - q0 z' = bDual z z' := by
  sorry

theorem bDual_injective : Function.Injective bDual := by
  sorry

theorem b_perp_bound (K P : Submodule ℂ (Fin 2 × Fin 2 → ℂ))
    (h : ∀ v ∈ K, ∀ z ∈ P, bDual v z = 0) :
    Module.finrank ℂ K + Module.finrank ℂ P ≤ 4 := by
  sorry

theorem finrank_span_one_le {V : Type} [AddCommGroup V] [Module ℂ V] (v : V) :
    Module.finrank ℂ (Submodule.span ℂ {v}) ≤ 1 := by
  sorry

theorem thB_quad {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    q0 (blockProj r c u0) ≠ 0 ∧
      ∀ w ∈ blockSpace L r c, q0 (blockProj r c w) = q0 (blockProj r c u0) * w.1 ^ 2 := by
  sorry

theorem thB_ker {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c) (hk : blockProj r c w = 0) :
    w.1 = 0 ∧ w.2 ∈ rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1)) := by
  sorry

theorem thB_img {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ ((blockSpace L r c).map (blockProj r c)) ≤ 2 := by
  sorry

theorem thB_dim {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ (blockSpace L r c) ≤
      2 + Module.finrank ℂ (rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1))) := by
  sorry

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
  sorry

theorem one_not_mem_row {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (A : Submodule ℂ (Fin n × Fin n → ℂ)) (hA : A ≤ L) (r : Fin n) :
    (1 : Fin n → ℂ) ∉ A.map (rowMap r) := by
  sorry

theorem finrank_sup_one {m : ℕ} (W : Submodule ℂ (Fin (m + 2) → ℂ))
    (h1 : (1 : Fin (m + 2) → ℂ) ∉ W) :
    Module.finrank ℂ (W ⊔ Submodule.span ℂ {(1 : Fin (m + 2) → ℂ)} :
      Submodule ℂ (Fin (m + 2) → ℂ)) = Module.finrank ℂ W + 1 := by
  sorry

theorem row_surj {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L)
    (v : Fin (m + 2) → ℂ) :
    ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧ ∃ γ : ℂ, ∀ j, v j = a (r1, j) + γ := by
  sorry

theorem exists_col {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L) :
    ∃ k : Fin (m + 2), ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧ ∀ j, j ≠ k → 1 + a (r1, j) = 0 := by
  sorry

theorem exists_perm2 {m : ℕ} (r1 r2 : Fin (m + 2)) (h : r1 ≠ r2) :
    ∃ ρ : Equiv.Perm (Fin (m + 2)), ρ 0 = r1 ∧ ρ 1 = r2 := by
  sorry

theorem exists_col_perm {m : ℕ} (k1 k2 : Fin (m + 2)) :
    ∃ κ : Equiv.Perm (Fin (m + 2)), ∀ x : Fin (m + 2), κ x = k1 ∨ κ x = k2 → x = 0 ∨ x = 1 := by
  sorry

def e2m (m : ℕ) : Fin 2 ⊕ Fin m ≃ Fin (m + 2) :=
  finSumFinEquiv.trans (finCongr (add_comm 2 m))

theorem e2m_inl_val (m : ℕ) (a : Fin 2) : ((e2m m (Sum.inl a) : Fin (m + 2)) : ℕ) = a := by
  sorry

theorem e2m_inr_val (m : ℕ) (b : Fin m) : ((e2m m (Sum.inr b) : Fin (m + 2)) : ℕ) = 2 + b := by
  sorry

theorem e2m_inl0 (m : ℕ) : e2m m (Sum.inl 0) = 0 := by
  sorry

theorem e2m_inl1 (m : ℕ) : e2m m (Sum.inl 1) = 1 := by
  sorry

theorem e2m_inr (m : ℕ) (b : Fin m) : ¬ (e2m m (Sum.inr b) = 0 ∨ e2m m (Sum.inr b) = 1) := by
  sorry

theorem lemmaC_gen {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r1 r2 : Fin (m + 2)) (hr : r1 ≠ r2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 1) := by
  sorry

theorem lemmaC {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r1 r2 : Fin 5)
    (hr : r1 ≠ r2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) + 7 := by
  sorry

theorem pm_tr {n : ℕ} (u : Fin n × Fin n → ℂ) : pm (fun p => u (p.2, p.1)) = pm u := by
  sorry

noncomputable def trE (n : ℕ) : (Fin n × Fin n → ℂ) ≃ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodComm (Fin n) (Fin n))

theorem trE_apply (n : ℕ) (t : Fin n × Fin n → ℂ) (i j : Fin n) : trE n t (i, j) = t (j, i) := by
  sorry

theorem lev_tr {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    Lev n (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))) := by
  sorry

def colMap {n : ℕ} (c : Fin n) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun t := fun i => t (i, c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem colMap_apply {n : ℕ} (c : Fin n) (t : Fin n × Fin n → ℂ) (i : Fin n) :
    colMap c t i = t (i, c) := by
  sorry

def colsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c1 c2 : Fin n) :
    Submodule ℂ (Fin n × Fin n → ℂ) :=
  L ⊓ LinearMap.ker (colMap c1) ⊓ LinearMap.ker (colMap c2)

theorem mem_colsZero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c1 c2 : Fin n)
    (t : Fin n × Fin n → ℂ) :
    t ∈ colsZero L c1 c2 ↔ t ∈ L ∧ (∀ i, t (i, c1) = 0) ∧ ∀ i, t (i, c2) = 0 := by
  sorry

theorem lemmaC_col_gen {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (c1 c2 : Fin (m + 2)) (hc : c1 ≠ c2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (colsZero L c1 c2) + (2 * m + 1) := by
  sorry

theorem lemmaC_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c1 c2 : Fin 5)
    (hc : c1 ≠ c2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (colsZero L c1 c2) + 7 := by
  sorry

theorem lemmaC_nine {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) :
    (∀ r1 r2 : Fin 5, r1 ≠ r2 → 2 ≤ Module.finrank ℂ (rowsZero L r1 r2)) ∧
      ∀ c1 c2 : Fin 5, c1 ≠ c2 → 2 ≤ Module.finrank ℂ (colsZero L c1 c2) := by
  sorry

theorem thB_cases {n : ℕ} (hn : n ≠ 0) {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n) :
    (∃ u0 ∈ blockSpace L r c, u0.1 = 1) ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧
        ((∀ w ∈ blockSpace L r c, q0 (blockProj r c w) = 0) ∨
          ∀ w ∈ blockSpace L r c,
            blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0)) := by
  sorry

def sa {k : ℕ} (e : Fin (k + 1)) : Fin k ⊕ Unit ≃ Fin (k + 1) :=
  (Equiv.optionEquivSumPUnit (Fin k)).symm.trans (finSuccEquiv' e).symm

theorem sa_inl {k : ℕ} (e : Fin (k + 1)) (b : Fin k) : sa e (Sum.inl b) = e.succAbove b := by
  sorry

theorem sa_inr {k : ℕ} (e : Fin (k + 1)) (x : Unit) : sa e (Sum.inr x) = e := by
  sorry

def rowRepl {n : ℕ} (u : Fin n × Fin n → ℂ) (e : Fin n) (v : Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => if p.1 = e then v p.2 else u p

theorem pm_rowRepl {n : ℕ} (u : Fin n × Fin n → ℂ) (e : Fin n) (v : Fin n → ℂ) :
    pm (rowRepl u e v) =
      ∑ σ : Equiv.Perm (Fin n), v (σ e) * ∏ i ∈ univ.erase e, u (i, σ i) := by
  sorry

theorem pm_row_expand {n : ℕ} (u : Fin n × Fin n → ℂ) (e : Fin n) :
    pm u = ∑ j, u (e, j) * pm (rowRepl u e (Pi.single j 1)) := by
  sorry

theorem pm_laplace_row {k : ℕ} (u : Fin (k + 1) × Fin (k + 1) → ℂ) (e : Fin (k + 1)) :
    pm u = ∑ j, u (e, j) * blk e.succAbove j.succAbove u := by
  sorry

theorem pm_laplace_two {k : ℕ} (u : Fin (k + 2) × Fin (k + 2) → ℂ) (r : Fin (k + 2))
    (p : Fin (k + 1)) :
    pm u = ∑ j, ∑ q, u (r, j) * u (r.succAbove p, j.succAbove q) *
      blk (fun a => r.succAbove (p.succAbove a)) (fun b => j.succAbove (q.succAbove b)) u := by
  sorry

theorem poly_top {Q : Polynomial ℂ} (A : ℂ) (d e : ℕ) (he : e ≠ 0)
    (h : ∀ τ : ℂ, τ ^ d * Q.eval τ = A * τ ^ (d + e)) : Q.eval 0 = 0 := by
  sorry

theorem ca2 {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hL : Lev (k + 1) L) (e : Fin (k + 1)) (ξ : Fin (k + 1) × Fin (k + 1) → ℂ) (hξ : ξ ∈ L)
    (hξe : ∀ j, ξ (e, j) = 0) (c : ℂ) (t : Fin (k + 1) × Fin (k + 1) → ℂ) (ht : t ∈ L) :
    ∑ j, (c + t (e, j)) * blk e.succAbove j.succAbove ξ = 0 := by
  sorry

theorem ca2_full {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (e : Fin (m + 2))
    (hrank : m + 1 ≤ Module.finrank ℂ (L.map (rowMap e)))
    (ξ : Fin (m + 2) × Fin (m + 2) → ℂ) (hξ : ξ ∈ L) (hξe : ∀ j, ξ (e, j) = 0)
    (j : Fin (m + 2)) : blk e.succAbove j.succAbove ξ = 0 := by
  sorry

theorem thA {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ)}
    (hL : Lev (k + 2) L) (r : Fin (k + 2)) (p : Fin (k + 1))
    (x : Fin (k + 2) × Fin (k + 2) → ℂ) (hx : x ∈ L) (hx1 : ∀ j, x (r, j) = 0)
    (hx2 : ∀ j, x (r.succAbove p, j) = 0) (c : ℂ) (t : Fin (k + 2) × Fin (k + 2) → ℂ)
    (ht : t ∈ L) :
    ∑ j, ∑ q, (c + t (r, j)) * (c + t (r.succAbove p, j.succAbove q)) *
      blk (fun a => r.succAbove (p.succAbove a)) (fun b => j.succAbove (q.succAbove b)) x =
      0 := by
  sorry

theorem zbf_lineality {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c)
    (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c) (hx1 : x.1 = 0) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n (w + x)) =
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) ∧
      blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n (w + x)) =
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) := by
  sorry

theorem blk_unit {n : ℕ} (ρ κ : Unit → Fin n) (u : Fin n × Fin n → ℂ) :
    blk ρ κ u = u (ρ (), κ ()) := by
  sorry

theorem single_row_SR {k : ℕ} {L : Submodule ℂ (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hL : Lev (k + 1) L) (a j : Fin (k + 1)) (x : Fin (k + 1) × Fin (k + 1) → ℂ) (hx : x ∈ L)
    (hxc : ∀ b : Fin k, x (a.succAbove b, j) = 0) (hxj : x (a, j) ≠ 0)
    (c : ℂ) (t : Fin (k + 1) × Fin (k + 1) → ℂ) (ht : t ∈ L)
    (htc : ∀ b : Fin k, c + t (a.succAbove b, j) = 0) :
    c = 0 ∧ blk a.succAbove j.succAbove t = 0 := by
  sorry

theorem permanent_three (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent = A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 + A 0 2 * A 1 1 * A 2 0 := by
  sorry

theorem fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  sorry

theorem n3_rowsum (x : Fin 3 × Fin 3 → ℂ) (r3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)
    (h1 : pm (fun p => 1 + x p) = 6) : x (r3, 0) + x (r3, 1) + x (r3, 2) = 0 := by
  sorry

theorem n3_colsum (y : Fin 3 × Fin 3 → ℂ) (c3 : Fin 3) (hy : ∀ i j, j ≠ c3 → y (i, j) = 0)
    (h2 : pm (fun p => 1 + y p) = 6) : y (0, c3) + y (1, c3) + y (2, c3) = 0 := by
  sorry

theorem n3_alg (x y : Fin 3 × Fin 3 → ℂ) (r3 c3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)
    (hy : ∀ i j, j ≠ c3 → y (i, j) = 0) (h1 : pm (fun p => 1 + x p) = 6)
    (h2 : pm (fun p => 1 + y p) = 6) (h3 : pm (fun p => 1 + x p + y p) = 6) :
    x (r3, c3) * y (r3, c3) = 0 := by
  sorry

theorem n3_others (r3 : Fin 3) :
    ∃ r1 r2 : Fin 3, r1 ≠ r2 ∧ ∀ i, i ≠ r3 → i = r1 ∨ i = r2 := by
  sorry

theorem n3_row {L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)} (hL : Lev 3 L)
    (h4 : 4 ≤ Module.finrank ℂ L) (r3 : Fin 3) :
    ∃ x ∈ L, x ≠ 0 ∧ ∀ i j, i ≠ r3 → x (i, j) = 0 := by
  sorry

theorem n3_col {L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)} (hL : Lev 3 L)
    (h4 : 4 ≤ Module.finrank ℂ L) (c3 : Fin 3) :
    ∃ y ∈ L, y ≠ 0 ∧ ∀ i j, j ≠ c3 → y (i, j) = 0 := by
  sorry

theorem n3_two_row (x : Fin 3 × Fin 3 → ℂ) (r3 : Fin 3) (hx : ∀ i j, i ≠ r3 → x (i, j) = 0)
    (hx0 : x ≠ 0) (hs : x (r3, 0) + x (r3, 1) + x (r3, 2) = 0) :
    ∃ j1 j2 : Fin 3, j1 ≠ j2 ∧ x (r3, j1) ≠ 0 ∧ x (r3, j2) ≠ 0 := by
  sorry

theorem n3_two_col (y : Fin 3 × Fin 3 → ℂ) (c3 : Fin 3) (hy : ∀ i j, j ≠ c3 → y (i, j) = 0)
    (hy0 : y ≠ 0) (hs : y (0, c3) + y (1, c3) + y (2, c3) = 0) :
    ∃ i1 i2 : Fin 3, i1 ≠ i2 ∧ y (i1, c3) ≠ 0 ∧ y (i2, c3) ≠ 0 := by
  sorry

theorem fin3_pick (i1 i2 : Fin 3) (h12 : i1 ≠ i2) (h1 : i1 ≠ 0) (h2 : i2 ≠ 0) :
    i1 = 1 ∨ i2 = 1 := by
  sorry

theorem fin3_pigeon (j1 j2 j3 j4 : Fin 3) (h12 : j1 ≠ j2) (h31 : j3 ≠ j1) (h32 : j3 ≠ j2)
    (h41 : j4 ≠ j1) (h42 : j4 ≠ j2) : j3 = j4 := by
  sorry

theorem n3 {L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)} (hL : Lev 3 L) :
    Module.finrank ℂ L ≤ 3 := by
  sorry

theorem prod_add_smul {k : ℕ} (x y : Fin k → ℂ) (s : ℂ) :
    ∏ a, (x a + s * y a) = ∑ m ∈ range (k + 1), s ^ m *
      ∑ A ∈ (univ : Finset (Finset (Fin k))).filter (fun A => A.card = m),
        (∏ a ∈ A, y a) * ∏ a ∈ Aᶜ, x a := by
  sorry

noncomputable def mix {n : ℕ} (m : ℕ) (u x : Fin n × Fin n → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n),
    ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      (∏ a ∈ A, x (a, σ a)) * ∏ a ∈ Aᶜ, u (a, σ a)

theorem pm_line_expand {n : ℕ} (u x : Fin n × Fin n → ℂ) (s : ℂ) :
    pm (u + s • x) = ∑ m ∈ range (n + 1), s ^ m * mix m u x := by
  sorry

theorem poly_coeff_zero (a : ℕ → ℂ) (N : ℕ) (K : ℂ)
    (h : ∀ s : ℂ, ∑ m ∈ range (N + 1), s ^ m * a m = K) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    a m = 0 := by
  sorry

theorem lev_mix {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (c : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    mix m (fun p => c + t p) x = 0 := by
  sorry

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
      w.1 + w.2 (r1, j) = 0 ∧ w.1 + w.2 (r2, j) = 0 := by
  sorry

theorem pairSpace_eq {m : ℕ} (L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ))
    (ρ κ : Equiv.Perm (Fin (m + 2))) :
    pairSpace L (ρ 0) (ρ 1) (κ 0) (κ 1) = blockSpace L ((e2m m).trans ρ) ((e2m m).trans κ) := by
  sorry

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
  sorry

theorem poly_coeff_eq (a b : ℕ → ℂ) (N : ℕ)
    (h : ∀ s : ℂ, ∑ m ∈ range (N + 1), s ^ m * a m = ∑ m ∈ range (N + 1), s ^ m * b m)
    (m : ℕ) (hmN : m ≤ N) : a m = b m := by
  sorry

theorem lev_mix_hat {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c1 c2 : ℂ) (t1 t2 : Fin n × Fin n → ℂ) (h1 : t1 ∈ L) (h2 : t2 ∈ L) (m : ℕ) (hmn : m ≤ n) :
    mix m (fun p => c1 + t1 p) (fun p => c2 + t2 p) =
      (Nat.factorial n : ℂ) * ((n.choose m : ℂ) * c1 ^ (n - m) * c2 ^ m) := by
  sorry

theorem blk_zero_col {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (u : Fin n × Fin n → ℂ) (a0 : m) (h : ∀ i, u (ρ i, κ a0) = 0) : blk ρ κ u = 0 := by
  sorry

theorem pm_zero_of_big_block {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (u : Fin n × Fin n → ℂ) (r c : α ⊕ β ≃ Fin n)
    (h : ∀ a b, u (r (Sum.inl a), c (Sum.inr b)) = 0) (a0 : α)
    (h0 : ∀ a, u (r (Sum.inl a), c (Sum.inl a0)) = 0) : pm u = 0 := by
  sorry

theorem lev_FK_block {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpace L r c) (a0 : α)
    (h0 : ∀ a, w.1 + w.2 (r (Sum.inl a), c (Sum.inl a0)) = 0) : w.1 = 0 := by
  sorry

theorem pm_zero_block_sets {n : ℕ} (u : Fin n × Fin n → ℂ) (S Z : Finset (Fin n))
    (eS : {x // x ∈ S} ≃ {x // x ∉ Z}) (eZ : {x // x ∉ S} ≃ {x // x ∈ Z})
    (h : ∀ i ∈ S, ∀ j ∈ Z, u (i, j) = 0) :
    pm u = blk (fun a : {x // x ∈ S} => (a : Fin n))
        (fun a => ((eS a : {x // x ∉ Z}) : Fin n)) u *
      blk (fun b : {x // x ∉ S} => (b : Fin n)) (fun b => ((eZ b : {x // x ∈ Z}) : Fin n)) u := by
  sorry

theorem exists_block_equivs {n : ℕ} (S Z : Finset (Fin n)) (hcard : S.card + Z.card = n) :
    Nonempty ({x // x ∈ S} ≃ {x // x ∉ Z}) ∧ Nonempty ({x // x ∉ S} ≃ {x // x ∈ Z}) := by
  sorry

theorem row_proj_le {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (r : Fin (m + 2)) :
    Module.finrank ℂ (L.map (rowMap r)) ≤ m + 1 := by
  sorry

theorem rows_pigeon {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) +
      Module.finrank ℂ (L.map (rowMap r1)) + Module.finrank ℂ (L.map (rowMap r2)) := by
  sorry

theorem zbf_witness {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c) (hx1 : x.1 = 0)
    (hβ : Fintype.card β ≠ 0)
    (hxb : blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x) ≠ 0) :
    (∀ w ∈ blockSpace L r c, w.1 = 0) ∧
      ∀ w ∈ blockSpace L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) = 0 := by
  sorry

theorem zbf_witness' {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ β ≃ Fin n)
    (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c) (hx1 : x.1 = 0)
    (hα : Fintype.card α ≠ 0)
    (hxa : blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n x) ≠ 0) :
    (∀ w ∈ blockSpace L r c, w.1 = 0) ∧
      ∀ w ∈ blockSpace L r c,
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0 := by
  sorry

theorem blk_tr {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (t : Fin n × Fin n → ℂ) : blk ρ κ (trE n t) = blk κ ρ t := by
  sorry

theorem ca2_col {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hL : Lev (k + 1) L) (e : Fin (k + 1)) (ξ : Fin (k + 1) × Fin (k + 1) → ℂ) (hξ : ξ ∈ L)
    (hξe : ∀ i, ξ (i, e) = 0) (c : ℂ) (t : Fin (k + 1) × Fin (k + 1) → ℂ) (ht : t ∈ L) :
    ∑ i, (c + t (i, e)) * blk i.succAbove e.succAbove ξ = 0 := by
  sorry

theorem thA_col {k : ℕ} (hk : k ≠ 0) {L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ)}
    (hL : Lev (k + 2) L) (r : Fin (k + 2)) (p : Fin (k + 1))
    (x : Fin (k + 2) × Fin (k + 2) → ℂ) (hx : x ∈ L) (hx1 : ∀ i, x (i, r) = 0)
    (hx2 : ∀ i, x (i, r.succAbove p) = 0) (c : ℂ) (t : Fin (k + 2) × Fin (k + 2) → ℂ)
    (ht : t ∈ L) :
    ∑ j, ∑ q, (c + t (j, r)) * (c + t (j.succAbove q, r.succAbove p)) *
      blk (fun b => j.succAbove (q.succAbove b)) (fun a => r.succAbove (p.succAbove a)) x =
      0 := by
  sorry

theorem q0_isotropic_bound (P : Submodule ℂ (Fin 2 × Fin 2 → ℂ)) (h : ∀ z ∈ P, q0 z = 0) :
    Module.finrank ℂ P ≤ 2 := by
  sorry

theorem thB_img_or {n : ℕ} (hn : n ≠ 0) {β : Type} [Fintype β] [DecidableEq β]
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : Fin 2 ⊕ β ≃ Fin n) :
    Module.finrank ℂ ((blockSpace L r c).map (blockProj r c)) ≤ 2 ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧ ∀ w ∈ blockSpace L r c,
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0) := by
  sorry

theorem thB_Bx {n : ℕ} (hn : n ≠ 0) {β : Type} [Fintype β] [DecidableEq β]
    (hβ : Fintype.card β ≠ 0) {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (r c : Fin 2 ⊕ β ≃ Fin n) (x : ℂ × (Fin n × Fin n → ℂ)) (hx : x ∈ blockSpace L r c)
    (hx1 : x.1 = 0) :
    blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n x) = 0 ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧
        ∀ w ∈ blockSpace L r c, q0 (blockProj r c w) = 0) := by
  sorry

theorem mix_eq_sum_pm {n : ℕ} (m : ℕ) (u x : Fin n × Fin n → ℂ) :
    mix m u x = ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      pm (fun p => if p.1 ∈ A then x p else u p) := by
  sorry

theorem lev_mix_pm {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (c : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      pm (fun p => if p.1 ∈ A then x p else c + t p) = 0 := by
  sorry

theorem lev_rows {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (R : Finset (Fin n)) (hR : R.Nonempty) (x : Fin n × Fin n → ℂ) (hx : x ∈ L)
    (hx0 : ∀ i, i ∉ R → ∀ j, x (i, j) = 0) (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => if p.1 ∈ R then x p else c + t p) = 0 := by
  sorry

theorem pm_smul {n : ℕ} (a : ℂ) (u : Fin n × Fin n → ℂ) : pm (a • u) = a ^ n * pm u := by
  sorry

def BLev {n : ℕ} (b : Fin n × Fin n → ℂ) (κ : ℂ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) : Prop :=
  κ ≠ 0 ∧ ∀ c : ℂ, ∀ t ∈ L, pm (fun p => c * b p + t p) = κ * c ^ n

theorem blev_of_lev {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) :
    BLev (fun _ => (1 : ℂ)) (Nat.factorial n : ℂ) L := by
  sorry

theorem blev_of_const {n : ℕ} (b : Fin n × Fin n → ℂ) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hb : pm b ≠ 0) (h : ∀ t ∈ L, pm (b + t) = pm b) : BLev b (pm b) L := by
  sorry

theorem blev_mono {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L K : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (hK : K ≤ L) : BLev b κ K := by
  sorry

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
    hatB b w = fun p => w.1 * b p + w.2 p := by
  sorry

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
      w.2 (r (Sum.inl a), c (Sum.inr a')) = 0 := by
  sorry

theorem zbf_prodB {n : ℕ} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {b : Fin n × Fin n → ℂ} {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L)
    (r c : α ⊕ β ≃ Fin n) (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpaceB b L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b w) *
      blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b w) =
      κ * (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ) w) ^ n := by
  sorry

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
  sorry

theorem zbf_zeroB {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {b : Fin n × Fin n → ℂ} {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)}
    (hL : BLev b κ L) (r c : α ⊕ β ≃ Fin n) (hU : ∀ w ∈ blockSpaceB b L r c, w.1 = 0) :
    (∀ w ∈ blockSpaceB b L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hatB b w) = 0) ∨
      (∀ w ∈ blockSpaceB b L r c,
        blk (fun a' => r (Sum.inr a')) (fun a' => c (Sum.inr a')) (hatB b w) = 0) := by
  sorry

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
  sorry

theorem thB_quadB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1) :
    q0 (blockProjB b r c u0) ≠ 0 ∧
      ∀ w ∈ blockSpaceB b L r c,
        q0 (blockProjB b r c w) = q0 (blockProjB b r c u0) * w.1 ^ 2 := by
  sorry

theorem thB_kerB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1)
    (w : ℂ × (Fin n × Fin n → ℂ)) (hw : w ∈ blockSpaceB b L r c)
    (hk : blockProjB b r c w = 0) :
    w.1 = 0 ∧ w.2 ∈ rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1)) := by
  sorry

theorem thB_imgB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ ((blockSpaceB b L r c).map (blockProjB b r c)) ≤ 2 := by
  sorry

theorem thB_dimB {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] {b : Fin n × Fin n → ℂ}
    {κ : ℂ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (r c : Fin 2 ⊕ β ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpaceB b L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ (blockSpaceB b L r c) ≤
      2 + Module.finrank ℂ (rowsZero L (r (Sum.inl 0)) (r (Sum.inl 1))) := by
  sorry

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
  sorry

theorem blev_FK_row {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (c : ℂ)
    (t : Fin n × Fin n → ℂ) (ht : t ∈ L) (r : Fin n)
    (h : ∀ j, c * b (r, j) + t (r, j) = 0) : c = 0 := by
  sorry

theorem row_not_mem {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L)
    (A : Submodule ℂ (Fin n × Fin n → ℂ)) (hA : A ≤ L) (r : Fin n) :
    rowMap r b ∉ A.map (rowMap r) := by
  sorry

theorem finrank_sup_vec {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (W : Submodule ℂ V) (v : V) (h1 : v ∉ W) :
    Module.finrank ℂ (W ⊔ Submodule.span ℂ {v} : Submodule ℂ V) = Module.finrank ℂ W + 1 := by
  sorry

theorem row_surjB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L)
    (v : Fin (m + 2) → ℂ) :
    ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧ ∃ γ : ℂ, ∀ j, v j = a (r1, j) + γ * b (r1, j) := by
  sorry

theorem exists_colB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (r1 r2 : Fin (m + 2))
    (hd : Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 2) ≤ Module.finrank ℂ L) :
    ∃ k : Fin (m + 2), ∃ a ∈ L, (∀ j, a (r2, j) = 0) ∧
      ∀ j, j ≠ k → b (r1, j) + a (r1, j) = 0 := by
  sorry

theorem lemmaC_genB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (r1 r2 : Fin (m + 2)) (hr : r1 ≠ r2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (rowsZero L r1 r2) + (2 * m + 1) := by
  sorry

theorem blev_tr {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) :
    BLev (trE n b) κ (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))) := by
  sorry

theorem lemmaC_col_genB {m : ℕ} {b : Fin (m + 2) × Fin (m + 2) → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)} (hL : BLev b κ L)
    (c1 c2 : Fin (m + 2)) (hc : c1 ≠ c2) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (colsZero L c1 c2) + (2 * m + 1) := by
  sorry

theorem exists_sub_finrank {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (W : Submodule ℂ V) (k : ℕ) (hk : k ≤ Module.finrank ℂ W) :
    ∃ W' : Submodule ℂ V, W' ≤ W ∧ Module.finrank ℂ W' = k := by
  sorry

theorem n3p_row {b : Fin 3 × Fin 3 → ℂ} {κ : ℂ} {V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)}
    (hL : BLev b κ V0) (h4 : 4 ≤ Module.finrank ℂ V0) (r3 : Fin 3) :
    ∃ x ∈ V0, x ≠ 0 ∧ ∀ i j, i ≠ r3 → x (i, j) = 0 := by
  sorry

theorem n3p_col {b : Fin 3 × Fin 3 → ℂ} {κ : ℂ} {V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)}
    (hL : BLev b κ V0) (h4 : 4 ≤ Module.finrank ℂ V0) (c3 : Fin 3) :
    ∃ y ∈ V0, y ≠ 0 ∧ ∀ i j, j ≠ c3 → y (i, j) = 0 := by
  sorry

def N3Core : Prop :=
  ∀ (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)), pm b ≠ 0 →
    (∀ η ∈ V0, pm (b + η) = pm b) → Module.finrank ℂ V0 = 4 →
    (∀ r : Fin 3, ∃ x ∈ V0, x ≠ 0 ∧ ∀ i j, i ≠ r → x (i, j) = 0) →
    (∀ c : Fin 3, ∃ y ∈ V0, y ≠ 0 ∧ ∀ i j, j ≠ c → y (i, j) = 0) → False

theorem n3prime_of_core (hcore : N3Core) (b : Fin 3 × Fin 3 → ℂ)
    (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ)) (hb : pm b ≠ 0)
    (h : ∀ η ∈ V0, pm (b + η) = pm b) : Module.finrank ℂ V0 ≤ 3 := by
  sorry

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
      pm (blockProj3 r c w) := by
  sorry

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
  sorry

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
    t ∈ rowsZeroS L S ↔ t ∈ L ∧ ∀ r ∈ S, ∀ j, t (r, j) = 0 := by
  sorry

theorem rowsZeroS_inf {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S S' : Finset (Fin n)) :
    rowsZeroS L S ⊓ rowsZeroS L S' = rowsZeroS L (S ∪ S') := by
  sorry

theorem rowsZeroS_sup_le {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (S S' : Finset (Fin n)) : rowsZeroS L S ⊔ rowsZeroS L S' ≤ rowsZeroS L (S ∩ S') := by
  sorry

theorem rows_submodular {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S S' : Finset (Fin n)) :
    Module.finrank ℂ (rowsZeroS L S) + Module.finrank ℂ (rowsZeroS L S') ≤
      Module.finrank ℂ (rowsZeroS L (S ∩ S')) + Module.finrank ℂ (rowsZeroS L (S ∪ S')) := by
  sorry

theorem rowsZeroS_empty {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    rowsZeroS L (∅ : Finset (Fin n)) = L := by
  sorry

theorem rowsZeroS_pair {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r1 r2 : Fin n) :
    rowsZeroS L {r1, r2} = rowsZero L r1 r2 := by
  sorry

theorem rowsZeroS_mono {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) {S S' : Finset (Fin n)}
    (h : S ⊆ S') : rowsZeroS L S' ≤ rowsZeroS L S := by
  sorry

theorem rowsZeroS_insert {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S : Finset (Fin n))
    (r : Fin n) : rowsZeroS L S ⊓ LinearMap.ker (rowMap r) = rowsZeroS L (insert r S) := by
  sorry

theorem rows_rank {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S : Finset (Fin n))
    (r : Fin n) :
    Module.finrank ℂ (rowsZeroS L S) = Module.finrank ℂ (rowsZeroS L (insert r S)) +
      Module.finrank ℂ ((rowsZeroS L S).map (rowMap r)) := by
  sorry

theorem rows_inj_bound {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (S S' : Finset (Fin n))
    (c : Fin n) (hSS : S' ⊆ S) (h0 : rowsZeroS L (insert c S) = ⊥) :
    Module.finrank ℂ (rowsZeroS L S) + Module.finrank ℂ (rowsZeroS L (insert c S')) ≤
      Module.finrank ℂ (rowsZeroS L S') := by
  sorry

theorem rows_disjoint_bound {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (S S' : Finset (Fin n)) (h0 : rowsZeroS L (S ∪ S') = ⊥) :
    Module.finrank ℂ (rowsZeroS L S) + Module.finrank ℂ (rowsZeroS L S') ≤
      Module.finrank ℂ (rowsZeroS L (S ∩ S')) := by
  sorry

noncomputable def dS (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S : Finset (Fin 5)) : ℕ :=
  Module.finrank ℂ (rowsZeroS L (S.map ρ.toEmbedding))

theorem dS_submodular (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S S' : Finset (Fin 5)) :
    dS L ρ S + dS L ρ S' ≤ dS L ρ (S ∩ S') + dS L ρ (S ∪ S') := by
  sorry

theorem dS_inj_bound (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S S' : Finset (Fin 5)) (c : Fin 5) (hSS : S' ⊆ S) (h0 : dS L ρ (insert c S) = 0) :
    dS L ρ S + dS L ρ (insert c S') ≤ dS L ρ S' := by
  sorry

theorem dS_disjoint_bound (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (S S' : Finset (Fin 5)) (h0 : dS L ρ (S ∪ S') = 0) :
    dS L ρ S + dS L ρ S' ≤ dS L ρ (S ∩ S') := by
  sorry

theorem stage3_G2 (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (ρ : Equiv.Perm (Fin 5))
    (ha : ∀ i : Fin 5, dS L ρ {i} = 5)
    (hz : ∀ S : Finset (Fin 5), S.card = 4 → dS L ρ S = 0)
    (hlam : ∀ S : Finset (Fin 5), S.card = 2 → 3 ≤ dS L ρ S)
    (h4 : 4 ≤ dS L ρ {0, 1}) :
    dS L ρ {0, 1, 4} = 2 ∧ dS L ρ {0, 1, 3} = 2 ∧ dS L ρ {0, 1, 2} = 2 ∧
      ∀ S : Finset (Fin 5), S.card = 2 → S ≠ {0, 1} → dS L ρ S = 3 := by
  sorry

theorem blev_line {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (c s : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) :
    pm (fun p => c * b p + t p + s * x p) = κ * c ^ n := by
  sorry

theorem blev_mix {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L) (c : ℂ)
    (t x : Fin n × Fin n → ℂ) (ht : t ∈ L) (hx : x ∈ L) (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    mix m (fun p => c * b p + t p) x = 0 := by
  sorry

theorem blev_rows {n : ℕ} {b : Fin n × Fin n → ℂ} {κ : ℂ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : BLev b κ L)
    (R : Finset (Fin n)) (hR : R.Nonempty) (x : Fin n × Fin n → ℂ) (hx : x ∈ L)
    (hx0 : ∀ i, i ∉ R → ∀ j, x (i, j) = 0) (c : ℂ) (t : Fin n × Fin n → ℂ) (ht : t ∈ L) :
    pm (fun p => if p.1 ∈ R then x p else c * b p + t p) = 0 := by
  sorry

def maskAT {n : ℕ} (A T : Finset (Fin n)) (u : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => if (p.1 ∈ A ↔ p.2 ∈ T) then u p else 0

theorem pm_mask_term {n : ℕ} (A T : Finset (Fin n)) (u : Fin n × Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (hT : T ≠ A.map σ.toEmbedding) :
    ∏ i, maskAT A T u (i, σ i) = 0 := by
  sorry

theorem pm_mask_sum {n : ℕ} (A : Finset (Fin n)) (u : Fin n × Fin n → ℂ) :
    pm u = ∑ T : Finset (Fin n), pm (maskAT A T u) := by
  sorry

theorem pm_mask_zero {n : ℕ} (A T : Finset (Fin n)) (u : Fin n × Fin n → ℂ)
    (h : T.card ≠ A.card) : pm (maskAT A T u) = 0 := by
  sorry

theorem blk_congr {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (u v : Fin n × Fin n → ℂ) (h : ∀ i j, u (ρ i, κ j) = v (ρ i, κ j)) :
    blk ρ κ u = blk ρ κ v := by
  sorry

theorem pm_mask_factor {n : ℕ} (A Z : Finset (Fin n)) (u : Fin n × Fin n → ℂ)
    (eS : {x // x ∈ A} ≃ {x // x ∉ Z}) (eZ : {x // x ∉ A} ≃ {x // x ∈ Z}) :
    pm (maskAT A Zᶜ u) =
      blk (fun a : {x // x ∈ A} => (a : Fin n)) (fun a => ((eS a : {x // x ∉ Z}) : Fin n)) u *
        blk (fun a' : {x // x ∉ A} => (a' : Fin n))
          (fun a' => ((eZ a' : {x // x ∈ Z}) : Fin n)) u := by
  sorry

theorem thG_masked {n : ℕ} {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (c1 c2 : ℂ) (t1 t2 : Fin n × Fin n → ℂ) (h1 : t1 ∈ L) (h2 : t2 ∈ L) (m : ℕ) (hmn : m ≤ n) :
    ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card = m),
      ∑ T : Finset (Fin n),
        pm (maskAT A T (fun p => if p.1 ∈ A then c2 + t2 p else c1 + t1 p)) =
      (Nat.factorial n : ℂ) * ((n.choose m : ℂ) * c1 ^ (n - m) * c2 ^ m) := by
  sorry

theorem thG_term {n : ℕ} (A Z : Finset (Fin n)) (u v : Fin n × Fin n → ℂ)
    (eS : {x // x ∈ A} ≃ {x // x ∉ Z}) (eZ : {x // x ∉ A} ≃ {x // x ∈ Z}) :
    pm (maskAT A Zᶜ (fun p => if p.1 ∈ A then v p else u p)) =
      blk (fun a : {x // x ∈ A} => (a : Fin n)) (fun a => ((eS a : {x // x ∉ Z}) : Fin n)) v *
        blk (fun a' : {x // x ∉ A} => (a' : Fin n))
          (fun a' => ((eZ a' : {x // x ∈ Z}) : Fin n)) u := by
  sorry

theorem rowsZeroS_all_bot (L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)) :
    rowsZeroS L ({0, 1, 2} : Finset (Fin 3)) = ⊥ := by
  sorry

theorem n3prime_weak (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (hb : pm b ≠ 0) (h : ∀ η ∈ V0, pm (b + η) = pm b) : Module.finrank ℂ V0 ≤ 4 := by
  sorry

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
    t ∈ cellsZero L K ↔ t ∈ L ∧ ∀ p ∈ K, t p = 0 := by
  sorry

theorem cells_submodular {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (K K' : Finset (Fin n × Fin n)) :
    Module.finrank ℂ (cellsZero L K) + Module.finrank ℂ (cellsZero L K') ≤
      Module.finrank ℂ (cellsZero L (K ∩ K')) + Module.finrank ℂ (cellsZero L (K ∪ K')) := by
  sorry

def cellProj {n : ℕ} (K : Finset (Fin n × Fin n)) :
    (Fin n × Fin n → ℂ) →ₗ[ℂ] ({p // p ∈ K} → ℂ) where
  toFun t := fun p => t p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cellsZero_eq {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (K : Finset (Fin n × Fin n)) : L ⊓ LinearMap.ker (cellProj K) = cellsZero L K := by
  sorry

theorem cells_rank {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (K : Finset (Fin n × Fin n)) :
    Module.finrank ℂ L = Module.finrank ℂ (cellsZero L K) +
      Module.finrank ℂ (L.map (cellProj K)) := by
  sorry

def vec3 (a0 a1 a2 : ℂ) : Fin 3 → ℂ := fun i => if i = 0 then a0 else if i = 1 then a1 else a2

theorem vec3_0 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 0 = a0 := by
  sorry

theorem vec3_1 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 1 = a1 := by
  sorry

theorem vec3_2 (a0 a1 a2 : ℂ) : vec3 a0 a1 a2 2 = a2 := by
  sorry

def Bad (b W Y : Fin 3 × Fin 3 → ℂ) : Prop :=
  pm b ≠ 0 ∧ (∀ α β : Fin 3 → ℂ, pm (fun p => b p + α p.1 * W p + β p.2 * Y p) = pm b) ∧
    (∀ r, ∃ j, W (r, j) ≠ 0) ∧ ∀ j, ∃ i, Y (i, j) ≠ 0

theorem bad_expand {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (a0 a1 a2 c0 c1 c2 : ℂ) :
    (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 0) + a0 * W (0, 0) + c0 * Y (0, 0)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 1) + a0 * W (0, 1) + c1 * Y (0, 1)) * (b (1, 0) + a1 * W (1, 0) + c0 * Y (1, 0)) * (b (2, 2) + a2 * W (2, 2) + c2 * Y (2, 2)) + (b (0, 1) + a0 * W (0, 1) + c1 * Y (0, 1)) * (b (1, 2) + a1 * W (1, 2) + c2 * Y (1, 2)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) + (b (0, 2) + a0 * W (0, 2) + c2 * Y (0, 2)) * (b (1, 0) + a1 * W (1, 0) + c0 * Y (1, 0)) * (b (2, 1) + a2 * W (2, 1) + c1 * Y (2, 1)) + (b (0, 2) + a0 * W (0, 2) + c2 * Y (0, 2)) * (b (1, 1) + a1 * W (1, 1) + c1 * Y (1, 1)) * (b (2, 0) + a2 * W (2, 0) + c0 * Y (2, 0)) =
      b (0, 0) * b (1, 1) * b (2, 2) + b (0, 0) * b (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * b (2, 2) + b (0, 1) * b (1, 2) * b (2, 0) + b (0, 2) * b (1, 0) * b (2, 1) + b (0, 2) * b (1, 1) * b (2, 0) := by
  sorry

theorem bad_pm {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) :
    b (0, 0) * b (1, 1) * b (2, 2) + b (0, 0) * b (1, 2) * b (2, 1) + b (0, 1) * b (1, 0) * b (2, 2) + b (0, 1) * b (1, 2) * b (2, 0) + b (0, 2) * b (1, 0) * b (2, 1) + b (0, 2) * b (1, 1) * b (2, 0) ≠ 0 := by
  sorry

theorem cancel_left {x y : ℂ} (hx : x ≠ 0) (h : x * y = 0) : y = 0 := by
  sorry

theorem bad_X4c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hW01 : W (0, 1) = 0)
    (hW02 : W (0, 2) = 0) (hW00 : W (0, 0) ≠ 0) : W (1, 1) * Y (2, 2) = 0 := by
  sorry

theorem bad_X3c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hW01 : W (0, 1) = 0)
    (hW02 : W (0, 2) = 0) (hW10 : W (1, 0) = 0) (hW12 : W (1, 2) = 0) : False := by
  sorry

theorem bad_X1c {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (hY10 : Y (1, 0) = 0)
    (hY20 : Y (2, 0) = 0) (hY11 : Y (1, 1) = 0) (hY21 : Y (2, 1) = 0) : False := by
  sorry

theorem pm_rel (ρ κ : Equiv.Perm (Fin 3)) (u : Fin 3 × Fin 3 → ℂ) :
    pm (fun p => u (ρ p.1, κ p.2)) = pm u := by
  sorry

theorem bad_rel {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (ρ κ : Equiv.Perm (Fin 3)) :
    Bad (fun p => b (ρ p.1, κ p.2)) (fun p => W (ρ p.1, κ p.2)) (fun p => Y (ρ p.1, κ p.2)) := by
  sorry

theorem bad_tr {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) :
    Bad (fun p => b (p.2, p.1)) (fun p => Y (p.2, p.1)) (fun p => W (p.2, p.1)) := by
  sorry

theorem fin3_two (a b c i : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hi : i ≠ c) :
    i = a ∨ i = b := by
  sorry

theorem fin3_third (a b : Fin 3) : ∃ m : Fin 3, m ≠ a ∧ m ≠ b := by
  sorry

theorem perm3_two (ρ : Equiv.Perm (Fin 3)) : ρ 2 ≠ ρ 0 ∧ ρ 2 ≠ ρ 1 := by
  sorry

theorem bad_X4 {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (r0 j0 i i' l m : Fin 3)
    (hcell : W (r0, j0) ≠ 0) (hrow : ∀ j, j ≠ j0 → W (r0, j) = 0) (hi : i ≠ r0) (hi' : i' ≠ r0)
    (hii : i ≠ i') (hl : l ≠ j0) (hm : m ≠ j0) (hlm : l ≠ m) : W (i, l) * Y (i', m) = 0 := by
  sorry

theorem bad_X1 {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (r j l : Fin 3) (hjl : j ≠ l)
    (hj : ∀ i, i ≠ r → Y (i, j) = 0) (hl : ∀ i, i ≠ r → Y (i, l) = 0) : False := by
  sorry

theorem bad_XX {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (r0 r1 j0 j1 : Fin 3) (hr : r0 ≠ r1)
    (h0 : ∀ j, j ≠ j0 → W (r0, j) = 0) (h1 : ∀ j, j ≠ j1 → W (r1, j) = 0) : False := by
  sorry

def SE (W Y : Fin 3 × Fin 3 → ℂ) (c : Fin 3) : Prop :=
  ∃ j, W (c, j) ≠ 0 ∧ (∀ l, l ≠ j → W (c, l) = 0) ∧ ∀ i, i ≠ c → Y (i, j) = 0

theorem n3_SE2 {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y)
    (K : Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)))
    (hK : ∀ k ∈ K, ∀ r j, k.1 r * W (r, j) = k.2 j * Y (r, j))
    (k k' : (Fin 3 → ℂ) × (Fin 3 → ℂ)) (hk : k ∈ K) (hk' : k' ∈ K) (a b' c : Fin 3)
    (hab : a ≠ b') (hac : a ≠ c) (hbc : b' ≠ c) (hc : k.1 c ≠ 0) (hc' : k'.1 c ≠ 0)
    (hb0 : k.1 b' = 0) (ha0 : k'.1 a = 0) : SE W Y c := by
  sorry

theorem n3_XX {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y) (c c' : Fin 3) (hcc : c ≠ c')
    (s : SE W Y c) (s' : SE W Y c') : False := by
  sorry

theorem n3_block {b W Y : Fin 3 × Fin 3 → ℂ} (h : Bad b W Y)
    (K : Submodule ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)))
    (hK : ∀ k ∈ K, ∀ r j, k.1 r * W (r, j) = k.2 j * Y (r, j))
    (k : (Fin 3 → ℂ) × (Fin 3 → ℂ)) (hk : k ∈ K) (c a b' : Fin 3) (hca : c ≠ a) (hcb : c ≠ b')
    (hab : a ≠ b') (s : SE W Y c) (hc0 : k.1 c = 0) (ha : k.1 a ≠ 0) (hb : k.1 b' ≠ 0) :
    False := by
  sorry

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
  sorry

theorem n3core_of_alg (halg : N3Alg) : N3Core := by
  sorry

theorem n3prime (b : Fin 3 × Fin 3 → ℂ) (V0 : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (hb : pm b ≠ 0) (h : ∀ η ∈ V0, pm (b + η) = pm b) : Module.finrank ℂ V0 ≤ 3 := by
  sorry

theorem n3prime_L_full {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L) (r c : α ⊕ Fin 3 ≃ Fin n)
    (u0 : ℂ × (Fin n × Fin n → ℂ)) (hu0 : u0 ∈ blockSpace L r c) (h0 : u0.1 = 1) :
    Module.finrank ℂ (blockSpace L r c ⊓
        LinearMap.ker (LinearMap.fst ℂ ℂ (Fin n × Fin n → ℂ)) : Submodule ℂ _) ≤
      3 + Module.finrank ℂ (colsOff L c) := by
  sorry

theorem row_onto {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (e : Fin (m + 2))
    (hrank : m + 1 ≤ Module.finrank ℂ (L.map (rowMap e))) (v : Fin (m + 2) → ℂ) :
    ∃ t ∈ L, ∃ γ : ℂ, ∀ j, v j = γ + t (e, j) := by
  sorry

noncomputable def Bx (r : Fin 5) (p : Fin 4) (x : Fin 5 × Fin 5 → ℂ) (j : Fin 5) (q : Fin 4) : ℂ :=
  blk (fun a : Fin 3 => r.succAbove (p.succAbove a)) (fun b : Fin 3 => j.succAbove (q.succAbove b)) x

theorem thA5 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p)) (c : ℂ)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) :
    ∑ j : Fin 5, ∑ q : Fin 4,
      (c + t (r, j)) * (c + t (r.succAbove p, j.succAbove q)) * Bx r p x j q = 0 := by
  sorry

theorem c4_left {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (ha' : 4 ≤ Module.finrank ℂ (L.map (rowMap (r.succAbove p))))
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p))
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) (ht0 : ∀ m, t (r.succAbove p, m) = 0)
    (z2 : Fin 5 → ℂ) :
    ∑ j : Fin 5, t (r, j) * ∑ q : Fin 4, z2 (j.succAbove q) * Bx r p x j q = 0 := by
  sorry

theorem c4_right {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (ha : 4 ≤ Module.finrank ℂ (L.map (rowMap r)))
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p))
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) (ht0 : ∀ m, t (r, m) = 0) (z1 : Fin 5 → ℂ) :
    ∑ j : Fin 5, z1 j * ∑ q : Fin 4, t (r.succAbove p, j.succAbove q) * Bx r p x j q = 0 := by
  sorry

theorem sum_single_mul {n : ℕ} (a : Fin n) (G : Fin n → ℂ) :
    ∑ j, (Pi.single a 1 : Fin n → ℂ) j * G j = G a := by
  sorry

theorem sum_succAbove_single' (l : Fin 5) (q' : Fin 4) (j : Fin 5) (h : l.succAbove q' = j)
    (G : Fin 4 → ℂ) : ∑ q, (Pi.single j 1 : Fin 5 → ℂ) (l.succAbove q) * G q = G q' := by
  sorry

theorem sum_succAbove_single (j : Fin 5) (q0 : Fin 4) (G : Fin 4 → ℂ) :
    ∑ q, (Pi.single (j.succAbove q0) 1 : Fin 5 → ℂ) (j.succAbove q) * G q = G q0 := by
  sorry

theorem sum_succAbove_self (j : Fin 5) (G : Fin 4 → ℂ) :
    ∑ q, (Pi.single j 1 : Fin 5 → ℂ) (j.succAbove q) * G q = 0 := by
  sorry

theorem sym5 : ∀ (j : Fin 5) (q q' : Fin 4), (j.succAbove q).succAbove q' = j →
    ∀ b : Fin 3, (j.succAbove q).succAbove (q'.succAbove b) = j.succAbove (q.succAbove b) := by
  sorry

theorem Bx_symm (r : Fin 5) (p : Fin 4) (x : Fin 5 × Fin 5 → ℂ) (j : Fin 5) (q q' : Fin 4)
    (h : (j.succAbove q).succAbove q' = j) : Bx r p x (j.succAbove q) q' = Bx r p x j q := by
  sorry

def sa2 (r : Fin 5) (p : Fin 4) : (Unit ⊕ Unit) ⊕ Fin 3 ≃ Fin 5 :=
  (Equiv.sumAssoc Unit Unit (Fin 3)).trans
    ((Equiv.sumCongr (Equiv.refl Unit) ((Equiv.sumComm Unit (Fin 3)).trans (sa p))).trans
      ((Equiv.sumComm Unit (Fin 4)).trans (sa r)))

theorem sa2_inr (r : Fin 5) (p : Fin 4) (a : Fin 3) :
    sa2 r p (Sum.inr a) = r.succAbove (p.succAbove a) := by
  sorry

theorem sa2_ll (r : Fin 5) (p : Fin 4) (u : Unit) : sa2 r p (Sum.inl (Sum.inl u)) = r := by
  sorry

theorem sa2_lr (r : Fin 5) (p : Fin 4) (u : Unit) :
    sa2 r p (Sum.inl (Sum.inr u)) = r.succAbove p := by
  sorry

theorem sa2_other (j0 : Fin 5) (q0 : Fin 4) (m : Fin 5) (h1 : m ≠ j0)
    (h2 : m ≠ j0.succAbove q0) : ∃ b : Fin 3, sa2 j0 q0 (Sum.inr b) = m := by
  sorry

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
  sorry

theorem c4 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) (p : Fin 4)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r (r.succAbove p)) + 7)
    (ha : Module.finrank ℂ (L.map (rowMap r)) = 4)
    (ha' : Module.finrank ℂ (L.map (rowMap (r.succAbove p))) = 4)
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ rowsZero L r (r.succAbove p)) (j0 : Fin 5) (q0 : Fin 4) :
    Bx r p x j0 q0 = 0 := by
  sorry

theorem c7_sep {ι : Type} (ρ ρ' ω : ι → ℂ) (hω : ∀ j, ω j ≠ 0)
    (hd : ∀ j l, ρ j ≠ ρ l → ρ' j ≠ ρ' l → ω j + ω l = 0 ∧ ρ j + ρ' j = ρ l + ρ' l)
    (h1 : ∃ j l, ρ j ≠ ρ l) (h2 : ∃ j l, ρ' j ≠ ρ' l) :
    ∃ a b, ρ a ≠ ρ b ∧ ρ' a ≠ ρ' b ∧ ω a + ω b = 0 ∧ ρ a + ρ' a = ρ b + ρ' b ∧
      ∀ m, (ρ m = ρ a ∧ ρ' m = ρ' a) ∨ (ρ m = ρ b ∧ ρ' m = ρ' b) ∨
        (ρ m = ρ a ∧ ρ' m = ρ' b) := by
  sorry

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
  sorry

theorem c7_tau (ρj ρl ρj' ρl' ωj ωl : ℂ) (hωj : ωj ≠ 0)
    (H : (∀ a1 a2 b1 b2 : ℂ, a1 + a2 = b1 + b2 →
          ρj * a1 + ρl * a2 + ρj' * b1 + ρl' * b2 = 0 → a1 + a2 = 0) ∨
        ∃ k : ℂ, ∀ a1 a2 b1 b2 : ℂ, a1 + a2 = b1 + b2 →
          ρj * a1 + ρl * a2 + ρj' * b1 + ρl' * b2 = 0 →
          ωj * a1 * b2 + ωl * a2 * b1 = k * (a1 + a2) ^ 2) :
    (ρj = ρl → ρj' ≠ ρl' → ωj * (ρj + ρj') + ωl * (ρl + ρl') = 0) ∧
      (ρj ≠ ρl → ρj' = ρl' → ωl * (ρj + ρj') + ωj * (ρl + ρl') = 0) ∧
      (ρj ≠ ρl → ρj' ≠ ρl' → ωj + ωl = 0 ∧ ρj + ρj' = ρl + ρl') := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

noncomputable def dotL {n : ℕ} (κ : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ m, z m * κ m
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' k x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem dotL_apply {n : ℕ} (κ z : Fin n → ℂ) : dotL κ z = ∑ m, z m * κ m := by
  sorry

theorem dotL_single {n : ℕ} (κ : Fin n → ℂ) (a : Fin n) :
    dotL κ (Pi.single a 1) = κ a := by
  sorry

theorem dotL_two {n : ℕ} (κ : Fin n → ℂ) (j l : Fin n) (x1 x2 : ℂ) :
    dotL κ (x1 • (Pi.single j 1 : Fin n → ℂ) + x2 • (Pi.single l 1 : Fin n → ℂ)) =
      x1 * κ j + x2 * κ l := by
  sorry

noncomputable def relM {n : ℕ} (α β : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (dotL α).comp (LinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ)) -
    (dotL β).comp (LinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))

theorem relM_apply {n : ℕ} (α β : Fin n → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    relM α β z = dotL α z.1 - dotL β z.2 := by
  sorry

noncomputable def relP {n : ℕ} (α β : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (dotL α).comp (LinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ)) +
    (dotL β).comp (LinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))

theorem relP_apply {n : ℕ} (α β : Fin n → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    relP α β z = dotL α z.1 + dotL β z.2 := by
  sorry

theorem two_single_eval (j l : Fin 5) (hjl : j ≠ l) (x1 x2 : ℂ) :
    (x1 • (Pi.single j 1 : Fin 5 → ℂ) + x2 • (Pi.single l 1 : Fin 5 → ℂ)) j = x1 ∧
      (x1 • (Pi.single j 1 : Fin 5 → ℂ) + x2 • (Pi.single l 1 : Fin 5 → ℂ)) l = x2 ∧
      ∀ m, m ≠ j → m ≠ l →
        (x1 • (Pi.single j 1 : Fin 5 → ℂ) + x2 • (Pi.single l 1 : Fin 5 → ℂ)) m = 0 := by
  sorry

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
  sorry

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
  sorry

theorem dot_zero_of_row {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (e : Fin 5)
    (hrank : 4 ≤ Module.finrank ℂ (L.map (rowMap e))) (μ : Fin 5 → ℂ)
    (hμL : ∀ t ∈ L, dotL μ (rowMap e t) = 0) (hμ1 : dotL μ 1 = 0) : ∀ m, μ m = 0 := by
  sorry

theorem dotL_comb {n : ℕ} (α β : Fin n → ℂ) (s : ℂ) (z : Fin n → ℂ) :
    dotL (fun m => α m + s * β m) z = dotL α z + s * dotL β z := by
  sorry

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
  sorry

theorem dual_eq_dotL {n : ℕ} (φ : (Fin n → ℂ) →ₗ[ℂ] ℂ) (z : Fin n → ℂ) :
    φ z = dotL (fun i => φ (Pi.single i 1)) z := by
  sorry

theorem fk_annihilator {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5) :
    ∃ κ : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 := by
  sorry

theorem second_relation {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (f1 : (Fin 5 → ℂ) × (Fin 5 → ℂ) →ₗ[ℂ] ℂ)
    (hf1 : ∀ t ∈ L, f1 (rowMap r t, rowMap r' t) = 0)
    (hf1J : f1 ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0)
    (v1 : (Fin 5 → ℂ) × (Fin 5 → ℂ)) (hv1 : f1 v1 ≠ 0) :
    ∃ g : (Fin 5 → ℂ) × (Fin 5 → ℂ) →ₗ[ℂ] ℂ,
      (∀ t ∈ L, g (rowMap r t, rowMap r' t) = 0) ∧
      g ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0 ∧ g v1 = 0 ∧ ∃ x, g x ≠ 0 := by
  sorry

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
  sorry

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

theorem dotD_apply {N : ℕ} (a z : Fin N → ℂ) : dotD a z = ∑ m, z m * a m := by
  sorry

theorem dotD_injective {N : ℕ} : Function.Injective (dotD (N := N)) := by
  sorry

theorem perp_bound {N : ℕ} (A B : Submodule ℂ (Fin N → ℂ))
    (h : ∀ a ∈ A, ∀ b ∈ B, ∑ m, b m * a m = 0) :
    Module.finrank ℂ A + Module.finrank ℂ B ≤ N := by
  sorry

theorem rank_one_bound {N : ℕ} (A B : Submodule ℂ (Fin N → ℂ)) (f : (Fin N → ℂ) →ₗ[ℂ] ℂ)
    (g : (Fin N → ℂ) → ℂ) (h : ∀ a ∈ A, ∀ b ∈ B, ∑ m, b m * a m = f a * g b) :
    Module.finrank ℂ A + Module.finrank ℂ B ≤ N + 1 := by
  sorry

theorem rowsZero_tr {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c1 c2 : Fin n) :
    rowsZero (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))) c1 c2 =
      (colsZero L c1 c2).map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)) := by
  sorry

theorem map_tr_row {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c : Fin n) :
    (L.map (trE n : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ))).map (rowMap c) =
      L.map (colMap c) := by
  sorry

theorem tr_min {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (c c' : Fin 5)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (colsZero L c c') + 7) :
    Module.finrank ℂ (L.map (trE 5 : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ))) =
      Module.finrank ℂ (rowsZero
        (L.map (trE 5 : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ))) c c') + 7 := by
  sorry

theorem c4_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c : Fin 5) (p : Fin 4)
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (colsZero L c (c.succAbove p)) + 7)
    (ha : Module.finrank ℂ (L.map (colMap c)) = 4)
    (ha' : Module.finrank ℂ (L.map (colMap (c.succAbove p))) = 4)
    (x : Fin 5 × Fin 5 → ℂ) (hx : x ∈ colsZero L c (c.succAbove p)) (i0 : Fin 5) (q0 : Fin 4) :
    blk (fun b : Fin 3 => i0.succAbove (q0.succAbove b))
      (fun a : Fin 3 => c.succAbove (p.succAbove a)) x = 0 := by
  sorry

def TypeCl (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) : Prop :=
  ν a / κ a ≠ ν b / κ b ∧ ν' a / κ' a ≠ ν' b / κ' b ∧
    ν a / κ a + ν' a / κ' a = ν b / κ b + ν' b / κ' b ∧
    ∀ m, (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' a / κ' a ∧
        κ' m / κ m = κ' a / κ a) ∨
      (ν m / κ m = ν b / κ b ∧ ν' m / κ' m = ν' b / κ' b ∧
        κ' m / κ m = - (κ' a / κ a)) ∨
      (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b ∧
        ν a / κ a + ν' a / κ' a ≠ 0 ∧ (κ' m / κ m) ^ 2 = - (κ' a / κ a) ^ 2 ∧
        (ν a / κ a + ν' b / κ' b) ^ 2 = - (ν a / κ a + ν' a / κ' a) ^ 2 ∧
        κ' a / κ a * (ν a / κ a + ν' a / κ' a) +
          κ' m / κ m * (ν a / κ a + ν' b / κ' b) = 0)

def MinPairCl (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (π π' : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ)) : Prop :=
  ∃ κ κ' ν ν' : Fin 5 → ℂ,
    (∀ t ∈ L, dotL κ (π t) = 0) ∧ dotL κ 1 = 1 ∧
    (∀ t ∈ L, dotL κ' (π' t) = 0) ∧ dotL κ' 1 = 1 ∧
    (∀ t ∈ L, dotL ν (π t) + dotL ν' (π' t) = 0) ∧
    dotL ν 1 + dotL ν' 1 = 0 ∧
    ((∀ j, κ j ≠ 0) → (∀ j, κ' j ≠ 0) → ∃ a b, TypeCl κ κ' ν ν' a b)

def MinPairNF (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (π π' : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ)) : Prop :=
  ∃ κ κ' ν ν' : Fin 5 → ℂ,
    (∀ t ∈ L, dotL κ (π t) = 0) ∧ dotL κ 1 = 1 ∧
    (∀ t ∈ L, dotL κ' (π' t) = 0) ∧ dotL κ' 1 = 1 ∧
    (∀ t ∈ L, dotL ν (π t) + dotL ν' (π' t) = 0) ∧
    dotL ν 1 + dotL ν' 1 = 0 ∧
    ((∀ j, κ j ≠ 0) → (∀ j, κ' j ≠ 0) → ∃ a b, TypeCl κ κ' ν ν' a b ∧
      ∃ Qa Qb : Finset (Fin 5), (∀ m, m ∈ Qa ↔ ν' m / κ' m = ν' a / κ' a) ∧
        (∀ m, m ∈ Qb ↔ ν m / κ m = ν b / κ b) ∧
        ∀ t ∈ L, ∑ m ∈ Qb, π t m * κ m + ∑ m ∈ Qa, π' t m * κ' m = 0)

theorem c7_final_cl {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (ha : 4 ≤ Module.finrank ℂ (L.map (rowMap r)))
    (ha' : 4 ≤ Module.finrank ℂ (L.map (rowMap r'))) :
    MinPairCl L (rowMap r) (rowMap r') := by
  sorry

theorem c7_final_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c c' : Fin 5)
    (hc : c ≠ c')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (colsZero L c c') + 7)
    (ha : 4 ≤ Module.finrank ℂ (L.map (colMap c)))
    (ha' : 4 ≤ Module.finrank ℂ (L.map (colMap c'))) :
    MinPairCl L (colMap c) (colMap c') := by
  sorry

theorem c7_nf (κ κ' ν ν' : Fin 5 → ℂ) (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0)
    (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b) (Qa Qb : Finset (Fin 5))
    (hQa : ∀ m, m ∈ Qa ↔ ν' m / κ' m = ν' a / κ' a)
    (hQb : ∀ m, m ∈ Qb ↔ ν m / κ m = ν b / κ b)
    (z1 z2 : Fin 5 → ℂ) (h1 : dotL κ z1 = 0) (h2 : dotL κ' z2 = 0)
    (h3 : dotL ν z1 + dotL ν' z2 = 0) :
    ∑ m ∈ Qb, z1 m * κ m + ∑ m ∈ Qa, z2 m * κ' m = 0 := by
  sorry

theorem minPair_nf {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}
    (π π' : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ)) (h : MinPairCl L π π') :
    MinPairNF L π π' := by
  sorry

theorem c7_rows_nf {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (ha : 4 ≤ Module.finrank ℂ (L.map (rowMap r)))
    (ha' : 4 ≤ Module.finrank ℂ (L.map (rowMap r'))) :
    MinPairNF L (rowMap r) (rowMap r') := by
  sorry

theorem c7_cols_nf {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c c' : Fin 5)
    (hc : c ≠ c')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (colsZero L c c') + 7)
    (ha : 4 ≤ Module.finrank ℂ (L.map (colMap c)))
    (ha' : 4 ≤ Module.finrank ℂ (L.map (colMap c'))) :
    MinPairNF L (colMap c) (colMap c') := by
  sorry

theorem zbf_cases {n : ℕ} (hn : n ≠ 0) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {L : Submodule ℂ (Fin n × Fin n → ℂ)} (hL : Lev n L)
    (r c : α ⊕ β ≃ Fin n) :
    (∃ k k' : ℂ, k * k' = (Nat.factorial n : ℂ) ∧ ∀ w ∈ blockSpace L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) =
          k * w.1 ^ Fintype.card α ∧
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) =
          k' * w.1 ^ Fintype.card β) ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧
        ((∀ w ∈ blockSpace L r c,
            blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat n w) = 0) ∨
          ∀ w ∈ blockSpace L r c,
            blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat n w) = 0)) := by
  sorry

theorem t0 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) :
    (∃ k k' : ℂ, k * k' = 120 ∧ ∀ w ∈ blockSpace L r c,
        blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat 5 w) = k * w.1 ^ 3 ∧
        blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat 5 w) = k' * w.1 ^ 2) ∨
      ((∀ w ∈ blockSpace L r c, w.1 = 0) ∧
        ((∀ w ∈ blockSpace L r c,
            blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) (hat 5 w) = 0) ∨
          ∀ w ∈ blockSpace L r c,
            blk (fun b => r (Sum.inr b)) (fun b => c (Sum.inr b)) (hat 5 w) = 0)) := by
  sorry

theorem t2_cubic (t a1 a2 a3 : ℂ) :
    pm (fun p : Fin 3 × Fin 3 => vec3 (vec3 t a1 (-t - a1) p.2) (vec3 t (-a2) (t + a2) p.2)
      (vec3 t (-a3) (t + a3) p.2) p.1) =
      2 * t * (t * a1 + a1 * a2 + a1 * a3 - a2 * a3) := by
  sorry

theorem t2_core (α β1 β2 β3 : ℂ)
    (h : ∀ t a1 a2 a3 : ℂ, α * t + β1 * a1 + β2 * a2 + β3 * a3 = 0 →
      2 * t * (t * a1 + a1 * a2 + a1 * a3 - a2 * a3) = 0) :
    β1 = 0 ∧ β2 = 0 ∧ β3 = 0 := by
  sorry

theorem t2pp_cubic (j t a1 a2 a3 : ℂ) :
    pm (fun p : Fin 3 × Fin 3 => vec3 (vec3 t a1 (-t - a1) p.2) (vec3 t (-a2) (t + a2) p.2)
      (vec3 (-a3) (-(j * (t - a3))) (-t) p.2) p.1) =
      (a2 - a1) * t * (t - j * (t - a3)) - a3 * (t * (a1 + a2) + 2 * a1 * a2) := by
  sorry

theorem t2pp_core (j α β1 β2 β3 : ℂ) (hj : j ≠ 1)
    (h : ∀ t a1 a2 a3 : ℂ, α * t + β1 * a1 + β2 * a2 + β3 * a3 = 0 →
      (a2 - a1) * t * (t - j * (t - a3)) - a3 * (t * (a1 + a2) + 2 * a1 * a2) = 0) :
    False := by
  sorry

theorem t1p_alg (i y a b c c2 c3 : ℂ) (hi : i * i = -1) (hy : 2 * y = -1 + i)
    (h1 : a + b + c = 1) (h2 : c2 * (i * a + b - c) = 1) (h3 : c3 * (-a + b + i * c) = 1)
    (h4 : c + c2 * b = -y) (h5 : a + c3 * b = -y) (h6 : i * (c2 * a + c3 * c) = -y) :
    False := by
  sorry

theorem rowsZeroS_single {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r : Fin n) :
    rowsZeroS L {r} = L ⊓ LinearMap.ker (rowMap r) := by
  sorry

theorem rowsZeroS_single_finrank {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (r : Fin n) :
    Module.finrank ℂ L = Module.finrank ℂ (rowsZeroS L {r}) +
      Module.finrank ℂ (L.map (rowMap r)) := by
  sorry

theorem s2_count (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r1 r2 r3 : Fin 5)
    (h1 : Module.finrank ℂ (rowsZeroS L {r1}) = 5)
    (h2 : Module.finrank ℂ (rowsZeroS L {r2}) = 5)
    (h3 : Module.finrank ℂ (rowsZeroS L {r3}) = 5)
    (h0 : rowsZeroS L {r1, r2, r3} = ⊥)
    (l12 : 2 ≤ Module.finrank ℂ (rowsZeroS L {r1, r2}))
    (l13 : 2 ≤ Module.finrank ℂ (rowsZeroS L {r1, r3}))
    (l23 : 2 ≤ Module.finrank ℂ (rowsZeroS L {r2, r3})) :
    (Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 ∧
        Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 ∧
        Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 ∧
        Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 ∧
        Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 ∧
        Module.finrank ℂ (rowsZeroS L {r1, r3}) = 3 ∧
        Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r2}) = 3 ∧
        Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 ∧
        Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2) := by
  sorry

def ZF (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r : Fin 5) : Prop :=
  4 ≤ Module.finrank ℂ (L.map (rowMap r)) ∧
    ∀ κ : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (rowMap r t) = 0) → dotL κ 1 = 1 → ∀ j, κ j ≠ 0

def PairI (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r r' : Fin 5) : Prop :=
  ∃ κ κ' ν ν' : Fin 5 → ℂ, ∃ a b : Fin 5,
    (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
    (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧
    (∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0) ∧
    dotL ν 1 + dotL ν' 1 = 0 ∧ (∀ j, κ j ≠ 0) ∧ (∀ j, κ' j ≠ 0) ∧ TypeCl κ κ' ν ν' a b ∧
    ∀ m, ¬ (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b)

def PairII (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r r' : Fin 5) : Prop :=
  ∃ κ κ' ν ν' : Fin 5 → ℂ, ∃ a b : Fin 5,
    (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
    (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧
    (∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0) ∧
    dotL ν 1 + dotL ν' 1 = 0 ∧ (∀ j, κ j ≠ 0) ∧ (∀ j, κ' j ≠ 0) ∧ TypeCl κ κ' ν ν' a b ∧
    ∃ m, ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b

theorem pair_I_or_II {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r')
    (hmin : Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7)
    (hz : ZF L r) (hz' : ZF L r') : PairI L r r' ∨ PairII L r r' := by
  sorry

def T1Hyp : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2 → rowsZeroS L {r1, r2, r3} ≠ ⊥

def TripleStmt (P Q : Submodule ℂ (Fin 5 × Fin 5 → ℂ) → Fin 5 → Fin 5 → Prop) : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3 → P L r1 r2 → Q L r1 r3 →
    rowsZeroS L {r1, r2, r3} ≠ ⊥

def T2Hyp : Prop := TripleStmt PairI PairI

def T2ppHyp : Prop := TripleStmt PairI PairII

def R31Hyp : Prop := TripleStmt PairII PairII

theorem set3_swap (r1 r2 r3 : Fin 5) : ({r1, r3, r2} : Finset (Fin 5)) = {r1, r2, r3} := by
  sorry

theorem set3_rot (r1 r2 r3 : Fin 5) : ({r2, r1, r3} : Finset (Fin 5)) = {r1, r2, r3} := by
  sorry

theorem set3_rot2 (r1 r2 r3 : Fin 5) : ({r3, r1, r2} : Finset (Fin 5)) = {r1, r2, r3} := by
  sorry

theorem pair_min {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (h9 : Module.finrank ℂ L = 9)
    (r r' : Fin 5) (x : Module.finrank ℂ (rowsZeroS L {r, r'}) = 2) :
    Module.finrank ℂ L = Module.finrank ℂ (rowsZero L r r') + 7 := by
  sorry

theorem s2_core (hT2 : T2Hyp) (hT2pp : T2ppHyp) {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}
    (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2)
    (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (z1 : ZF L r1) (z2 : ZF L r2) (z3 : ZF L r3)
    (h0 : rowsZeroS L {r1, r2, r3} = ⊥)
    (x12 : Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2)
    (x13 : Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2)
    (x23 : Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3) :
    PairII L r1 r2 ∧ PairII L r1 r3 := by
  sorry

theorem zf_five {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r : Fin 5) (z : ZF L r) :
    Module.finrank ℂ (rowsZeroS L {r}) = 5 := by
  sorry

theorem pair_ge_two {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r r' : Fin 5) (hr : r ≠ r') :
    2 ≤ Module.finrank ℂ (rowsZeroS L {r, r'}) := by
  sorry

theorem s2 (hT1 : T1Hyp) (hT2 : T2Hyp) (hT2pp : T2ppHyp)
    {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (z1 : ZF L r1)
    (z2 : ZF L r2) (z3 : ZF L r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) :
    (Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3 ∧ PairII L r1 r2 ∧ PairII L r1 r3) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r3}) = 3 ∧ PairII L r2 r1 ∧ PairII L r2 r3) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r2}) = 3 ∧ PairII L r3 r1 ∧ PairII L r3 r2) := by
  sorry

theorem s2_star (hT1 : T1Hyp) (hT2 : T2Hyp) (hT2pp : T2ppHyp) (hR31 : R31Hyp)
    {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (z1 : ZF L r1)
    (z2 : ZF L r2) (z3 : ZF L r3) : rowsZeroS L {r1, r2, r3} ≠ ⊥ := by
  sorry

theorem blk_row_scale {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (ρ κ : m → Fin n)
    (d : Fin n → ℂ) (w : Fin n × Fin n → ℂ) :
    blk ρ κ (fun p => d p.1 * w p) = (∏ i, d (ρ i)) * blk ρ κ w := by
  sorry

theorem t1_identity {m : ℕ} {L : Submodule ℂ (Fin (m + 2) × Fin (m + 2) → ℂ)}
    (hL : Lev (m + 2) L) (e : Fin (m + 2))
    (hrank : m + 1 ≤ Module.finrank ℂ (L.map (rowMap e)))
    (S : Finset (Fin (m + 2))) (heS : e ∉ S)
    (x ξ : Fin (m + 2) × Fin (m + 2) → ℂ) (hx : x ∈ L) (hξ : ξ ∈ L)
    (hξe : ∀ j, ξ (e, j) = 0) (hxS : ∀ i, i ∉ S → ∀ j, x (i, j) = 0) (j : Fin (m + 2)) :
    blk e.succAbove j.succAbove (fun p => if p.1 ∈ S then x p else ξ p) = 0 := by
  sorry

noncomputable def comb3 (ν μ κ : Fin 5 → ℂ) : ℂ × ℂ × ℂ →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun w := fun m => w.1 * ν m + w.2.1 * μ m + w.2.2 * κ m
  map_add' x y := by
    funext m
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' k x := by
    funext m
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    ring

theorem comb3_apply (ν μ κ : Fin 5 → ℂ) (w : ℂ × ℂ × ℂ) (m : Fin 5) :
    comb3 ν μ κ w m = w.1 * ν m + w.2.1 * μ m + w.2.2 * κ m := by
  sorry

theorem t2_dep (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r1 r2 r3 : Fin 5)
    (κ ν ν' μ μ' : Fin 5 → ℂ)
    (hκ : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ1 : dotL κ 1 = 1)
    (hν : ∀ t ∈ L, dotL ν (rowMap r1 t) + dotL ν' (rowMap r2 t) = 0)
    (hμ : ∀ t ∈ L, dotL μ (rowMap r1 t) + dotL μ' (rowMap r3 t) = 0)
    (hdim : Module.finrank ℂ (rowsZeroS L {r1, r2, r3}) + 3 ≤
      Module.finrank ℂ (rowsZeroS L {r2, r3})) :
    ∃ α β γ : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ m, α * ν m + β * μ m + γ * κ m = 0 := by
  sorry

theorem t2_partition (κ ν μ : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0) (α β γ : ℂ)
    (hαβ : α ≠ 0 ∨ β ≠ 0) (h : ∀ m, α * ν m + β * μ m + γ * κ m = 0)
    (hν : ∃ a b, ν a / κ a ≠ ν b / κ b) (hμ : ∃ a b, μ a / κ a ≠ μ b / κ b) :
    ∀ m m', ν m / κ m = ν m' / κ m' ↔ μ m / κ m = μ m' / κ m' := by
  sorry

theorem t2_split {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r1 r2 r3 : Fin 5)
    (hrank : 4 ≤ Module.finrank ℂ (L.map (rowMap r1)))
    (hdim : Module.finrank ℂ (rowsZeroS L {r1, r2, r3}) + 3 ≤
      Module.finrank ℂ (rowsZeroS L {r2, r3}))
    (κ ν ν' : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ1 : dotL κ 1 = 1)
    (hνL : ∀ t ∈ L, dotL ν (rowMap r1 t) + dotL ν' (rowMap r2 t) = 0)
    (hνc : ∃ a b, ν a / κ a ≠ ν b / κ b)
    (κ'' μ μ' : Fin 5 → ℂ)
    (hκ''L : ∀ t ∈ L, dotL κ'' (rowMap r1 t) = 0) (hκ''1 : dotL κ'' 1 = 1)
    (hμL : ∀ t ∈ L, dotL μ (rowMap r1 t) + dotL μ' (rowMap r3 t) = 0)
    (hμc : ∃ a b, μ a / κ'' a ≠ μ b / κ'' b) :
    ∀ m m', ν m / κ m = ν m' / κ m' ↔ μ m / κ'' m = μ m' / κ'' m' := by
  sorry

theorem typeCl_nonconst (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b) :
    ∃ a b, ν a / κ a ≠ ν b / κ b := by
  sorry

theorem dotL_mul {n : ℕ} (s : ℂ) (μ z : Fin n → ℂ) :
    dotL (fun m => s * μ m) z = s * dotL μ z := by
  sorry

def ZFc (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (c : Fin 5) : Prop :=
  4 ≤ Module.finrank ℂ (L.map (colMap c)) ∧
    ∀ κ : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (colMap c t) = 0) → dotL κ 1 = 1 → ∀ i, κ i ≠ 0

theorem dot_zero_of_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c : Fin 5)
    (hrank : 4 ≤ Module.finrank ℂ (L.map (colMap c))) (μ : Fin 5 → ℂ)
    (hμL : ∀ t ∈ L, dotL μ (colMap c t) = 0) (hμ1 : dotL μ 1 = 0) : ∀ m, μ m = 0 := by
  sorry

theorem row_rel_zero {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5)
    (hr : ZF L r) (μ : Fin 5 → ℂ) (hμL : ∀ t ∈ L, dotL μ (rowMap r t) = 0) (i : Fin 5)
    (hi : μ i = 0) : ∀ m, μ m = 0 := by
  sorry

theorem col_rel_zero {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c : Fin 5)
    (hc : ZFc L c) (μ : Fin 5 → ℂ) (hμL : ∀ t ∈ L, dotL μ (colMap c t) = 0) (i : Fin 5)
    (hi : μ i = 0) : ∀ m, μ m = 0 := by
  sorry

theorem exists_other (r r' : Fin 5) : ∃ i, i ≠ r ∧ i ≠ r' := by
  sorry

theorem lone_rel (κ κ' ν ν' z1 z2 : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0) (hκ'0 : ∀ m, κ' m ≠ 0)
    (j : Fin 5) (P P' O O' : ℂ) (hP : ν j / κ j = P) (hP' : ν' j / κ' j = P')
    (hO : ∀ m, m ≠ j → ν m / κ m = O ∧ ν' m / κ' m = O') (hsum : P + P' = O + O')
    (hne : P ≠ O) (h1 : dotL κ z1 = 0) (h2 : dotL κ' z2 = 0)
    (h3 : dotL ν z1 + dotL ν' z2 = 0) : z1 j * κ j = z2 j * κ' j := by
  sorry

theorem gen0_typeI {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r') (hcol : ∀ c, ZFc L c) (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5)
    (h1 : ∀ t ∈ L, dotL κ (rowMap r t) = 0) (h3 : ∀ t ∈ L, dotL κ' (rowMap r' t) = 0)
    (h5 : ∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0)
    (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0) (hcl : TypeCl κ κ' ν ν' a b)
    (hI : ∀ m, ¬ (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b)) (j : Fin 5) :
    ∃ l, l ≠ j ∧ ν l / κ l = ν j / κ j := by
  sorry

theorem gen0_pairI {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r') (hcol : ∀ c, ZFc L c) (hp : PairI L r r') :
    ∃ κ κ' ν ν' : Fin 5 → ℂ, ∃ a b : Fin 5,
      (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
      (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧
      (∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0) ∧
      dotL ν 1 + dotL ν' 1 = 0 ∧ (∀ j, κ j ≠ 0) ∧ (∀ j, κ' j ≠ 0) ∧ TypeCl κ κ' ν ν' a b ∧
      (∀ m, ¬ (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b)) ∧
      ∀ j, ∃ l, l ≠ j ∧ ν l / κ l = ν j / κ j := by
  sorry

theorem exists_perm3 (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    ∃ ρ : Equiv.Perm (Fin 5), ρ 0 = r1 ∧ ρ 1 = r2 ∧ ρ 2 = r3 := by
  sorry

noncomputable def blkMap (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) :
    (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 3 × Fin 2 → ℂ) where
  toFun t := fun p => t (r (Sum.inl p.1), c (Sum.inr p.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def blkL (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) :
    Submodule ℂ (Fin 5 × Fin 5 → ℂ) :=
  L ⊓ LinearMap.ker (blkMap r c)

theorem mem_blkL (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) :
    t ∈ blkL L r c ↔ t ∈ L ∧ ∀ a b, t (r (Sum.inl a), c (Sum.inr b)) = 0 := by
  sorry

theorem blkL_finrank (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (blkL L r c) + 6 := by
  sorry

theorem ell_ne_of_small {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h9 : Module.finrank ℂ L = 9) (hs : Module.finrank ℂ (blkL L r c) ≤ 3) :
    ∃ w ∈ blockSpace L r c, w.1 ≠ 0 := by
  sorry

theorem stest_blk {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) (hw : ∃ w ∈ blockSpace L r c, w.1 ≠ 0)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ blkL L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) t = 0 := by
  sorry

theorem hyper_core (H : Submodule ℂ (Fin 4 → ℂ)) (h3 : 3 ≤ Module.finrank ℂ H)
    (cub : (Fin 4 → ℂ) → ℂ)
    (hcore : ∀ α β1 β2 β3 : ℂ, (∀ t a1 a2 a3 : ℂ, α * t + β1 * a1 + β2 * a2 + β3 * a3 = 0 →
      cub ![t, a1, a2, a3] = 0) → β1 = 0 ∧ β2 = 0 ∧ β3 = 0)
    (hcub : Module.finrank ℂ H ≤ 3 → ∀ x ∈ H, cub x = 0) :
    ∀ x : Fin 4 → ℂ, x 0 = 0 → x ∈ H := by
  sorry

theorem t2_alg (k x : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0) (d2 d3 : ℂ) (hd2 : d2 ≠ 0)
    (hd3 : d3 ≠ 0) (hk1 : k 1 0 = d2 * k 0 0 ∧ k 1 1 = -d2 * k 0 1 ∧ k 1 2 = -d2 * k 0 2)
    (hk2 : k 2 0 = d3 * k 0 0 ∧ k 2 1 = -d3 * k 0 1 ∧ k 2 2 = -d3 * k 0 2) (T A1 A2 A3 : ℂ)
    (h0 : ∀ i, k i 0 * x i 0 = T) (h1 : k 0 1 * x 0 1 = A1) (h2 : k 1 1 * x 1 1 = A2)
    (h3 : k 2 1 * x 2 1 = A3) (hs : ∀ i, k i 0 * x i 0 + k i 1 * x i 1 + k i 2 * x i 2 = 0) :
    (d2 * d3 * k 0 0 * k 0 1 * k 0 2) * (Matrix.of x).permanent =
      2 * T * (T * A1 + A1 * A2 + A1 * A3 - A2 * A3) := by
  sorry

noncomputable def lam4 (w : Fin 4 → ℂ) (P : Fin 4 → Fin 5 × Fin 5) :
    (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun t := fun i => w i * t (P i)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lam4_apply (w : Fin 4 → ℂ) (P : Fin 4 → Fin 5 × Fin 5) (t : Fin 5 × Fin 5 → ℂ)
    (i : Fin 4) : lam4 w P t i = w i * t (P i) := by
  sorry

theorem t2_stest {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0) (d2 d3 : ℂ) (hd2 : d2 ≠ 0) (hd3 : d3 ≠ 0)
    (hk1 : k 1 0 = d2 * k 0 0 ∧ k 1 1 = -d2 * k 0 1 ∧ k 1 2 = -d2 * k 0 2)
    (hk2 : k 2 0 = d3 * k 0 0 ∧ k 2 1 = -d3 * k 0 1 ∧ k 2 2 = -d3 * k 0 2)
    (hrel : ∀ t ∈ blkL L r c, ∀ i : Fin 3,
      k i 0 * t (r (Sum.inl i), c (Sum.inl 0)) = k 0 0 * t (r (Sum.inl 0), c (Sum.inl 0)) ∧
      k i 0 * t (r (Sum.inl i), c (Sum.inl 0)) + k i 1 * t (r (Sum.inl i), c (Sum.inl 1)) +
        k i 2 * t (r (Sum.inl i), c (Sum.inl 2)) = 0)
    (a : Fin 3 → ℂ) :
    ∃ t ∈ blkL L r c, ∀ i : Fin 3, t (r (Sum.inl i), c (Sum.inl 0)) = 0 ∧
      k i 1 * t (r (Sum.inl i), c (Sum.inl 1)) = a i ∧
      k i 2 * t (r (Sum.inl i), c (Sum.inl 2)) = - a i := by
  sorry

noncomputable def evalPair (q0 q1 : Fin 5) : Module.Dual ℂ (Fin 5 → ℂ) →ₗ[ℂ] ℂ × ℂ where
  toFun φ := (φ (Pi.single q0 1), φ (Pi.single q1 1))
  map_add' φ ψ := rfl
  map_smul' k φ := rfl

theorem span_classes (R : Submodule ℂ (Fin 5 → ℂ)) (C : Finset (Fin 5)) (q0 q1 : Fin 5)
    (hq0 : q0 ∈ C) (hq1 : q1 ∉ C) (κ : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0)
    (hR : ∀ q s, q ≠ s → (q ∈ C ↔ s ∈ C) →
      (κ q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈ R) :
    3 ≤ Module.finrank ℂ R := by
  sorry

theorem fk_unique {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5)
    (hrank : 4 ≤ Module.finrank ℂ (L.map (rowMap r))) (κ κ' : Fin 5 → ℂ)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0) (hκ1 : dotL κ 1 = 1)
    (hκ'L : ∀ t ∈ L, dotL κ' (rowMap r t) = 0) (hκ'1 : dotL κ' 1 = 1) : κ' = κ := by
  sorry

theorem exists_equiv3 (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    ∃ e : Fin 3 ⊕ Fin 2 ≃ Fin 5, e (Sum.inl 0) = r1 ∧ e (Sum.inl 1) = r2 ∧
      e (Sum.inl 2) = r3 := by
  sorry

theorem sum_supp3 (c : Fin 3 ⊕ Fin 2 ≃ Fin 5) (f : Fin 5 → ℂ)
    (hf : ∀ b, f (c (Sum.inr b)) = 0) :
    ∑ m, f m = f (c (Sum.inl 0)) + f (c (Sum.inl 1)) + f (c (Sum.inl 2)) := by
  sorry

theorem sum_C_supp3 (c : Fin 3 ⊕ Fin 2 ≃ Fin 5) (C : Finset (Fin 5)) (f : Fin 5 → ℂ)
    (hf : ∀ b, f (c (Sum.inr b)) = 0) :
    ∑ m ∈ C, f m = (if c (Sum.inl 0) ∈ C then f (c (Sum.inl 0)) else 0) +
      (if c (Sum.inl 1) ∈ C then f (c (Sum.inl 1)) else 0) +
      (if c (Sum.inl 2) ∈ C then f (c (Sum.inl 2)) else 0) := by
  sorry

theorem typeI_nf {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (κ κ' ν ν' : Fin 5 → ℂ)
    (a b : Fin 5) (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0)
    (hκ'L : ∀ t ∈ L, dotL κ' (rowMap r' t) = 0)
    (hνL : ∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0)
    (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0) (hcl : TypeCl κ κ' ν ν' a b)
    (hI : ∀ m, ¬ (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b))
    (C : Finset (Fin 5)) (hC : ∀ m, m ∈ C ↔ ν m / κ m = ν b / κ b) :
    (∃ f : ℂ, f ≠ 0 ∧ (∀ m, m ∉ C → κ' m = f * κ m) ∧ (∀ m, m ∈ C → κ' m = -f * κ m)) ∧
    (∀ t ∈ L, ∑ m ∈ C, t (r, m) * κ m = ∑ m ∈ C, t (r', m) * κ' m) ∧
    (∀ m, m ∉ C ↔ ν m / κ m = ν a / κ a) := by
  sorry

theorem t2_gen_vec {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) (κ κ2 κ3 : Fin 5 → ℂ)
    (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (C : Finset (Fin 5)) (f2 f3 : ℂ)
    (hf2 : f2 ≠ 0) (hf3 : f3 ≠ 0)
    (hf2a : ∀ m, m ∉ C → κ2 m = f2 * κ m) (hf2b : ∀ m, m ∈ C → κ2 m = -f2 * κ m)
    (hf3a : ∀ m, m ∉ C → κ3 m = f3 * κ m) (hf3b : ∀ m, m ∈ C → κ3 m = -f3 * κ m)
    (hrel2 : ∀ t ∈ L, ∑ m ∈ C, t (r1, m) * κ m = ∑ m ∈ C, t (r2, m) * κ2 m)
    (hrel3 : ∀ t ∈ L, ∑ m ∈ C, t (r1, m) * κ m = ∑ m ∈ C, t (r3, m) * κ3 m)
    (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hcls : (p ∉ C ∧ q ∈ C ∧ s ∈ C) ∨ (p ∈ C ∧ q ∉ C ∧ s ∉ C)) :
    (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈
      (rowsZeroS L {r1, r3}).map (rowMap r2) := by
  sorry

theorem t2_proof : T2Hyp := by
  sorry

theorem s2_noT2 (hT1 : T1Hyp) (hT2pp : T2ppHyp)
    {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (z1 : ZF L r1)
    (z2 : ZF L r2) (z3 : ZF L r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) :
    (Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3 ∧ PairII L r1 r2 ∧ PairII L r1 r3) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r3}) = 3 ∧ PairII L r2 r1 ∧ PairII L r2 r3) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r2}) = 3 ∧ PairII L r3 r1 ∧ PairII L r3 r2) := by
  sorry

theorem s2_star_noT2 (hT1 : T1Hyp) (hT2pp : T2ppHyp) (hR31 : R31Hyp)
    {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (z1 : ZF L r1)
    (z2 : ZF L r2) (z3 : ZF L r3) : rowsZeroS L {r1, r2, r3} ≠ ⊥ := by
  sorry

theorem typeII_nf {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (κ κ' ν ν' : Fin 5 → ℂ)
    (a b : Fin 5) (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0)
    (hκ'L : ∀ t ∈ L, dotL κ' (rowMap r' t) = 0)
    (hνL : ∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0)
    (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0) (hcl : TypeCl κ κ' ν ν' a b)
    (B Q2 : Finset (Fin 5)) (hB : ∀ m, m ∈ B ↔ ν m / κ m = ν b / κ b)
    (hQ2 : ∀ m, m ∈ Q2 ↔ ν' m / κ' m = ν' a / κ' a) :
    (∀ m, m ∈ Q2 → m ∉ B) ∧
    (∀ m, m ∈ Q2 → κ' m = (κ' a / κ a) * κ m) ∧
    (∀ m, m ∈ B → κ' m = -(κ' a / κ a) * κ m) ∧
    (∀ m, m ∉ B → m ∉ Q2 → (κ' m / κ m) ^ 2 = -(κ' a / κ a) ^ 2) ∧
    (∀ t ∈ L, ∑ m ∈ B, t (r, m) * κ m + ∑ m ∈ Q2, t (r', m) * κ' m = 0) := by
  sorry

theorem hyper_top (H : Submodule ℂ (Fin 4 → ℂ)) (h3 : 3 ≤ Module.finrank ℂ H)
    (cub : (Fin 4 → ℂ) → ℂ)
    (hcore : ∀ α β1 β2 β3 : ℂ, (∀ t a1 a2 a3 : ℂ, α * t + β1 * a1 + β2 * a2 + β3 * a3 = 0 →
      cub ![t, a1, a2, a3] = 0) → False)
    (hcub : Module.finrank ℂ H ≤ 3 → ∀ x ∈ H, cub x = 0) :
    ∀ x : Fin 4 → ℂ, x ∈ H := by
  sorry

theorem t2pp_alg (k x : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0) (d2 c j : ℂ) (hd2 : d2 ≠ 0)
    (hc : c ≠ 0) (hj : j * j = -1)
    (hk1 : k 1 0 = d2 * k 0 0 ∧ k 1 1 = -d2 * k 0 1 ∧ k 1 2 = -d2 * k 0 2)
    (hk2 : k 2 0 = -c * k 0 0 ∧ k 2 1 = c * j * k 0 1 ∧ k 2 2 = c * k 0 2) (T A1 A2 A3 : ℂ)
    (h00 : k 0 0 * x 0 0 = T) (h10 : k 1 0 * x 1 0 = T) (h01 : k 0 1 * x 0 1 = A1)
    (h11 : k 1 1 * x 1 1 = A2) (h20 : k 2 0 * x 2 0 = A3) (h22 : k 2 2 * x 2 2 = -T)
    (hs : ∀ i, k i 0 * x i 0 + k i 1 * x i 1 + k i 2 * x i 2 = 0) :
    (d2 * c * k 0 0 * k 0 1 * k 0 2) * (Matrix.of x).permanent =
      (A2 - A1) * T * (T - j * (T - A3)) - A3 * (T * (A1 + A2) + 2 * A1 * A2) := by
  sorry

theorem sum_C_three (B : Finset (Fin 5)) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) (f : Fin 5 → ℂ) (hf : ∀ m, m ≠ p → m ≠ q → m ≠ s → f m = 0) :
    ∑ m ∈ B, f m = (if p ∈ B then f p else 0) + (if q ∈ B then f q else 0) +
      (if s ∈ B then f s else 0) := by
  sorry

theorem loc_rel (κ κ2 κ3 : Fin 5 → ℂ) (B Q2 : Finset (Fin 5)) (r1 r2 r3 : Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hoff : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0)
    (F1 : dotL κ (rowMap r1 t) = 0) (F2 : dotL κ2 (rowMap r2 t) = 0)
    (F3 : dotL κ3 (rowMap r3 t) = 0)
    (rel2 : ∑ m ∈ B, t (r1, m) * κ m = ∑ m ∈ B, t (r2, m) * κ2 m)
    (rel3 : ∑ m ∈ B, t (r1, m) * κ m + ∑ m ∈ Q2, t (r3, m) * κ3 m = 0) :
    t (r1, p) * κ p + t (r1, q) * κ q + t (r1, s) * κ s = 0 ∧
    t (r2, p) * κ2 p + t (r2, q) * κ2 q + t (r2, s) * κ2 s = 0 ∧
    t (r3, p) * κ3 p + t (r3, q) * κ3 q + t (r3, s) * κ3 s = 0 ∧
    (if p ∈ B then t (r1, p) * κ p else 0) + (if q ∈ B then t (r1, q) * κ q else 0) +
        (if s ∈ B then t (r1, s) * κ s else 0) =
      (if p ∈ B then t (r2, p) * κ2 p else 0) + (if q ∈ B then t (r2, q) * κ2 q else 0) +
        (if s ∈ B then t (r2, s) * κ2 s else 0) ∧
    (if p ∈ B then t (r1, p) * κ p else 0) + (if q ∈ B then t (r1, q) * κ q else 0) +
        (if s ∈ B then t (r1, s) * κ s else 0) +
      ((if p ∈ Q2 then t (r3, p) * κ3 p else 0) + (if q ∈ Q2 then t (r3, q) * κ3 q else 0) +
        (if s ∈ Q2 then t (r3, s) * κ3 s else 0)) = 0 := by
  sorry

theorem gen_vec_core {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) (κ κ2 κ3 : Fin 5 → ℂ)
    (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) (d2 d3 : ℂ) (hd2 : d2 ≠ 0)
    (hd3 : d3 ≠ 0) (hk1 : κ2 p = d2 * κ p ∧ κ2 q = -d2 * κ q ∧ κ2 s = -d2 * κ s)
    (hk2 : κ3 p = d3 * κ p ∧ κ3 q = -d3 * κ q ∧ κ3 s = -d3 * κ s)
    (hcs0 : ∀ t ∈ L, (∀ m, m ≠ p → m ≠ q → m ≠ s →
        t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0) →
      t (r2, p) * κ2 p = t (r1, p) * κ p ∧ t (r3, p) * κ3 p = t (r1, p) * κ p) :
    (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈
      (rowsZeroS L {r1, r3}).map (rowMap r2) := by
  sorry

theorem t2pp_stest {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0) (d2 γ j : ℂ) (hd2 : d2 ≠ 0) (hγ : γ ≠ 0)
    (hj : j * j = -1)
    (hk1 : k 1 0 = d2 * k 0 0 ∧ k 1 1 = -d2 * k 0 1 ∧ k 1 2 = -d2 * k 0 2)
    (hk2 : k 2 0 = -γ * k 0 0 ∧ k 2 1 = γ * j * k 0 1 ∧ k 2 2 = γ * k 0 2)
    (hrel : ∀ t ∈ blkL L r c,
      k 1 0 * t (r (Sum.inl 1), c (Sum.inl 0)) = k 0 0 * t (r (Sum.inl 0), c (Sum.inl 0)) ∧
      k 2 2 * t (r (Sum.inl 2), c (Sum.inl 2)) = -(k 0 0 * t (r (Sum.inl 0), c (Sum.inl 0))) ∧
      ∀ i : Fin 3, k i 0 * t (r (Sum.inl i), c (Sum.inl 0)) +
        k i 1 * t (r (Sum.inl i), c (Sum.inl 1)) + k i 2 * t (r (Sum.inl i), c (Sum.inl 2)) = 0) :
    ∃ t ∈ blkL L r c, (∀ j', t (r (Sum.inl 0), c (Sum.inl j')) = 0) ∧
      (∀ j', t (r (Sum.inl 2), c (Sum.inl j')) = 0) ∧
      t (r (Sum.inl 1), c (Sum.inl 0)) = 0 ∧ k 1 1 * t (r (Sum.inl 1), c (Sum.inl 1)) = 1 ∧
      k 1 2 * t (r (Sum.inl 1), c (Sum.inl 2)) = -1 := by
  sorry

theorem gen_vec_A {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) (κ κ2 κ3 : Fin 5 → ℂ)
    (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) (d2 γ j : ℂ) (hd2 : d2 ≠ 0)
    (hγ : γ ≠ 0) (hj : j * j = -1) (hk1 : κ2 p = d2 * κ p ∧ κ2 q = -d2 * κ q ∧ κ2 s = -d2 * κ s)
    (hk2 : κ3 p = -γ * κ p ∧ κ3 q = γ * j * κ q ∧ κ3 s = γ * κ s)
    (hcs0 : ∀ t ∈ L, (∀ m, m ≠ p → m ≠ q → m ≠ s →
        t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0) →
      t (r2, p) * κ2 p = t (r1, p) * κ p ∧ t (r3, s) * κ3 s = -(t (r1, p) * κ p)) :
    (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈
      (rowsZeroS L {r1, r3}).map (rowMap r2) := by
  sorry

theorem t2pp_proof : T2ppHyp := by
  sorry

theorem dotL_single' {n : ℕ} (d : Fin n) (z : Fin n → ℂ) :
    dotL (Pi.single d 1) z = z d := by
  sorry

theorem polyLine_lin {V : Type} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] ℂ) :
    PolyLine (fun v => f v) := by
  sorry

noncomputable def entL (p : Fin 5 × Fin 5) : ℂ × (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] ℂ where
  toFun w := w.1 + w.2 p
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' k x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem entL_apply (p : Fin 5 × Fin 5) (w : ℂ × (Fin 5 × Fin 5 → ℂ)) :
    entL p w = w.1 + w.2 p := by
  sorry

noncomputable def rowHat (i : Fin 5) : ℂ × (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun w := fun j => w.1 + w.2 (i, j)
  map_add' x y := by
    funext j
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' k x := by
    funext j
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem ker_prop {W : Type} [AddCommGroup W] [Module ℂ W] (U : Submodule ℂ W)
    (f g : W →ₗ[ℂ] ℂ) (h : ∀ w ∈ U, f w = 0 → g w = 0) :
    ∃ c0 : ℂ, ∀ w ∈ U, g w = c0 * f w := by
  sorry

theorem gen_lin {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (i i' d : Fin 5)
    (hii : i ≠ i') (hi : 4 ≤ Module.finrank ℂ (L.map (rowMap i))) (hd : ZFc L d)
    (b : Fin 5 → ℂ) (hb : b d = 0)
    (h : ∀ c : ℂ, ∀ t ∈ L, dotL b (fun j => c + t (i, j)) * (c + t (i', d)) +
      (c + t (i, d)) * dotL b (fun j => c + t (i', j)) = 0) :
    ∀ j, b j = 0 := by
  sorry

noncomputable def lam3 (w : Fin 3 → ℂ) (P : Fin 3 → Fin 5 × Fin 5) :
    (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun t := fun l => w l * t (P l)
  map_add' x y := by
    funext l
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lam3_apply (w : Fin 3 → ℂ) (P : Fin 3 → Fin 5 × Fin 5) (t : Fin 5 × Fin 5 → ℂ)
    (l : Fin 3) : lam3 w P t l = w l * t (P l) := by
  sorry

theorem stest_lift3 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3)
    (hM : ∀ t ∈ blkL L r c, ∀ i j, k i j * t (r (Sum.inl i), c (Sum.inl j)) =
      ∑ l, M i j l * (k (pi l) (pj l) * t (r (Sum.inl (pi l)), c (Sum.inl (pj l)))))
    (x0 : Fin 3 → ℂ)
    (hperm : (Matrix.of fun i j => (∑ l, M i j l * x0 l) / k i j).permanent ≠ 0) : False := by
  sorry

theorem t1_iii_local {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (d2 d3 : ℂ) (hd2 : d2 ≠ 0) (hd3 : d3 ≠ 0)
    (hk1 : κs 1 (cc (Sum.inl 0)) = d2 * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = -d2 * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = d2 * κs 0 (cc (Sum.inl 2)))
    (hk2 : κs 2 (cc (Sum.inl 0)) = d3 * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = d3 * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -d3 * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) =
        κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) =
        κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) =
        κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0))) : False := by
  sorry

theorem two_val_eq (r : Fin 5 → ℂ) (f : ℂ) (C : Finset (Fin 5))
    (h1 : ∀ m, m ∉ C → r m = f) (h2 : ∀ m, m ∈ C → r m = -f) (p q : Fin 5)
    (h : q ∈ C ↔ p ∈ C) : r q = r p := by
  sorry

theorem two_val_neg' (r : Fin 5 → ℂ) (f : ℂ) (C : Finset (Fin 5))
    (h1 : ∀ m, m ∉ C → r m = f) (h2 : ∀ m, m ∈ C → r m = -f) (p q : Fin 5)
    (h : q ∈ C ↔ p ∉ C) : r q = -r p := by
  sorry

theorem two_val_neg (r : Fin 5 → ℂ) (f : ℂ) (hf : f ≠ 0) (C : Finset (Fin 5))
    (h1 : ∀ m, m ∉ C → r m = f) (h2 : ∀ m, m ∈ C → r m = -f) (p q : Fin 5)
    (h : r q = -r p) : q ∈ C ↔ p ∉ C := by
  sorry

theorem xor_nonconst (A B Cr : Fin 5 → ℂ) (f2 f3 f23 : ℂ) (hf2 : f2 ≠ 0) (hf23 : f23 ≠ 0)
    (C12 C13 C23 : Finset (Fin 5))
    (hA1 : ∀ m, m ∉ C12 → A m = f2) (hA2 : ∀ m, m ∈ C12 → A m = -f2)
    (hB1 : ∀ m, m ∉ C13 → B m = f3) (hB2 : ∀ m, m ∈ C13 → B m = -f3)
    (hC1 : ∀ m, m ∉ C23 → Cr m = f23) (hC2 : ∀ m, m ∈ C23 → Cr m = -f23)
    (hBCA : ∀ m, B m = Cr m * A m) (u v : Fin 5) (hu : u ∈ C23) (hv : v ∉ C23) :
    ∃ u v, (u ∈ C12 ↔ u ∈ C13) ∧ ¬ (v ∈ C12 ↔ v ∈ C13) := by
  sorry

theorem comb_pqs (X Y : Fin 5 → Prop) (hX1 : ∃ m, X m) (hX2 : ∃ m, ¬ X m) (hY1 : ∃ m, Y m)
    (hY2 : ∃ m, ¬ Y m) (hXY : ∃ u v, (X u ↔ Y u) ∧ ¬ (X v ↔ Y v)) :
    ∃ p q s, (X q ↔ ¬ X p) ∧ (Y q ↔ Y p) ∧ (X s ↔ X p) ∧ (Y s ↔ ¬ Y p) := by
  sorry

theorem pair_local (κa κb : Fin 5 → ℂ) (C : Finset (Fin 5)) (ra rb : Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hoff : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (ra, m) = 0 ∧ t (rb, m) = 0)
    (Fa : dotL κa (rowMap ra t) = 0) (Fb : dotL κb (rowMap rb t) = 0)
    (rel : ∑ m ∈ C, t (ra, m) * κa m = ∑ m ∈ C, t (rb, m) * κb m)
    (hq : q ∈ C ↔ p ∉ C) (hs : s ∈ C ↔ p ∈ C) :
    t (ra, q) * κa q = t (rb, q) * κb q := by
  sorry

set_option maxHeartbeats 2000000 in
theorem t1_III {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (z1 : ZF L r1) (z2 : ZF L r2) (z3 : ZF L r3)
    (hp : PairI L r1 r2) (hq : PairI L r1 r3) (hr : PairI L r2 r3)
    (h0 : rowsZeroS L {r1, r2, r3} = ⊥) : False := by
  sorry

def T1Rest : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2 →
    (PairII L r1 r2 ∨ PairII L r1 r3 ∨ PairII L r2 r3) → rowsZeroS L {r1, r2, r3} ≠ ⊥

theorem t1_of_rest (h : T1Rest) : T1Hyp := by
  sorry

theorem corner_sq {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (hp : PairII L r r') :
    ∃ κ κ' : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
      (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧ (∀ j, κ j ≠ 0) ∧
      (∀ j, κ' j ≠ 0) ∧ ∃ m0 a0 : Fin 5, (κ' m0 / κ m0) ^ 2 = -(κ' a0 / κ a0) ^ 2 := by
  sorry

theorem sq_ratio (u v : Fin 5 → ℂ) (f : ℂ) (C : Finset (Fin 5)) (hv : ∀ m, v m ≠ 0)
    (h1 : ∀ m, m ∉ C → u m = f * v m) (h2 : ∀ m, m ∈ C → u m = -f * v m) (m : Fin 5) :
    (u m / v m) ^ 2 = f ^ 2 := by
  sorry

theorem sq_contra (R : Fin 5 → ℂ) (x : ℂ) (hx : x ≠ 0) (hR : ∀ m, R m ^ 2 = x) (m0 a0 : Fin 5)
    (h : R m0 ^ 2 = -(R a0) ^ 2) : False := by
  sorry

theorem typeI_ratio {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (hp : PairI L r r')
    (κ0 κ0' : Fin 5 → ℂ) (hκ0L : ∀ t ∈ L, dotL κ0 (rowMap r t) = 0) (hκ01 : dotL κ0 1 = 1)
    (hκ0'L : ∀ t ∈ L, dotL κ0' (rowMap r' t) = 0) (hκ0'1 : dotL κ0' 1 = 1)
    (huniq : ∀ κ κ' : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (rowMap r t) = 0) → dotL κ 1 = 1 →
      (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) → dotL κ' 1 = 1 → κ = κ0 ∧ κ' = κ0') :
    ∃ f : ℂ, f ≠ 0 ∧ ∀ m, (κ0' m / κ0 m) ^ 2 = f ^ 2 := by
  sorry

theorem t1_one_II {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r1 r2 r3 : Fin 5)
    (z1 : ZF L r1) (z2 : ZF L r2) (z3 : ZF L r3)
    (hI : (PairI L r1 r2 ∧ PairI L r1 r3 ∧ PairII L r2 r3) ∨
      (PairII L r1 r2 ∧ PairI L r1 r3 ∧ PairI L r2 r3) ∨
      (PairI L r1 r2 ∧ PairII L r1 r3 ∧ PairI L r2 r3)) : False := by
  sorry

def T1Rest2 : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2 →
    ((PairII L r1 r2 ∧ PairII L r1 r3) ∨ (PairII L r1 r2 ∧ PairII L r2 r3) ∨
      (PairII L r1 r3 ∧ PairII L r2 r3)) → rowsZeroS L {r1, r2, r3} ≠ ⊥

theorem t1rest_of_rest2 (h : T1Rest2) : T1Rest := by
  sorry

theorem t1_of_rest2 (h : T1Rest2) : T1Hyp := by
  sorry

theorem corner_unique (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b)
    (m m' : Fin 5) (hm : ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b)
    (hm' : ν m' / κ m' = ν a / κ a ∧ ν' m' / κ' m' = ν' b / κ' b) :
    κ' m / κ m = κ' m' / κ m' := by
  sorry

theorem rule_R (Q1 Q2 Q3 C : Finset (Fin 5)) (hcov : ∀ m, m ∈ Q1 ∨ m ∈ Q2 ∨ m ∈ Q3)
    (h1 : ∃ m, m ∈ Q1) (h2 : ∃ m, m ∈ Q2) (h3 : ∃ m, m ∈ Q3) (hC1 : ∃ m, m ∈ C)
    (hC2 : ∃ m, m ∉ C) :
    ∃ p q s, p ∈ Q1 ∧ q ∈ Q2 ∧ s ∈ Q3 ∧ ¬ ((p ∈ C ↔ q ∈ C) ∧ (q ∈ C ↔ s ∈ C)) := by
  sorry

theorem stest_lift3' {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3)
    (hM : ∀ t ∈ blkL L r c, ∀ i j, k i j * t (r (Sum.inl i), c (Sum.inl j)) =
      ∑ l, M i j l * (k (pi l) (pj l) * t (r (Sum.inl (pi l)), c (Sum.inl (pj l)))))
    (x0 : Fin 3 → ℂ) (y : Fin 3 → Fin 3 → ℂ)
    (hy : ∀ i j, (∑ l, M i j l * x0 l) / k i j = y i j)
    (hperm : (Matrix.of y).permanent ≠ 0) : False := by
  sorry

theorem jsq_ne {j : ℂ} (hj : j * j = -1) : j ≠ 0 := by
  sorry

theorem stest_gen {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (A : Fin 3 → Fin 3 → Fin 3 → ℂ)
    (hrel : ∀ t ∈ blkL L rr cc, ∀ r, ∑ i, ∑ k,
      A r i k * (κs i (cc (Sum.inl k)) * t (rr (Sum.inl i), cc (Sum.inl k))) = 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3) (Lr La : Fin 3 → Fin 3 → Fin 3 → ℂ)
    (hid : ∀ i k (v : Fin 3 → Fin 3 → ℂ), v i k - ∑ l, M i k l * v (pi l) (pj l) =
      ∑ i', Lr i k i' * ∑ k', v i' k' + ∑ r, La i k r * ∑ i', ∑ k', A r i' k' * v i' k')
    (W : Fin 3 → Fin 3 → ℂ) (hW0 : ∀ k, W 0 k = 1) (hW : ∀ i k, W i k ≠ 0)
    (hw1 : ∀ k, κs 1 (cc (Sum.inl k)) = W 1 k * κs 0 (cc (Sum.inl k)))
    (hw2 : ∀ k, κs 2 (cc (Sum.inl k)) = W 2 k * κs 0 (cc (Sum.inl k)))
    (x0 : Fin 3 → ℂ)
    (hperm : (Matrix.of fun i k => (∑ l, M i k l * x0 l) / W i k).permanent ≠ 0) : False := by
  have hrs : ∀ t ∈ blkL L rr cc, ∀ i : Fin 3,
      ∑ k, κs i (cc (Sum.inl k)) * t (rr (Sum.inl i), cc (Sum.inl k)) = 0 := by
    intro t ht i
    obtain ⟨htL, ht0⟩ := (mem_blkL L rr cc t).mp ht
    have e := sum_supp3 cc (fun m => t (rr (Sum.inl i), m) * κs i m)
      (fun b => by simp only [ht0 i b, zero_mul])
    have f := hFK i t htL
    rw [dotL_apply] at f
    simp only [rowMap_apply] at f
    rw [f] at e
    rw [Fin.sum_univ_three]
    linear_combination -e
  refine stest_lift3 hL h9 rr cc h0 (fun i j => κs i (cc (Sum.inl j))) (fun i j => hκs i _) M pi pj
    ?_ x0 ?_
  · intro t ht i k
    have e := hid i k (fun i' k' => κs i' (cc (Sum.inl k')) * t (rr (Sum.inl i'), cc (Sum.inl k')))
    simp only [hrs t ht, hrel t ht, mul_zero, Finset.sum_const_zero, add_zero] at e
    exact sub_eq_zero.mp e
  · show (Matrix.of fun i j => (∑ l, M i j l * x0 l) / κs i (cc (Sum.inl j))).permanent ≠ 0
    have n0 := hκs 0 (cc (Sum.inl 0))
    have n1 := hκs 0 (cc (Sum.inl 1))
    have n2 := hκs 0 (cc (Sum.inl 2))
    have w10 := hW 1 0
    have w11 := hW 1 1
    have w12 := hW 1 2
    have w20 := hW 2 0
    have w21 := hW 2 1
    have w22 := hW 2 2
    have e : (Matrix.of fun i j => (∑ l, M i j l * x0 l) / κs i (cc (Sum.inl j))).permanent *
        (κs 0 (cc (Sum.inl 0)) * κs 0 (cc (Sum.inl 1)) * κs 0 (cc (Sum.inl 2))) =
        (Matrix.of fun i k => (∑ l, M i k l * x0 l) / W i k).permanent := by
      rw [permanent_three, permanent_three]
      simp only [Matrix.of_apply, hw1, hw2, hW0]
      field_simp
      ring
    intro hz
    rw [hz, zero_mul] at e
    exact hperm e.symm

set_option maxHeartbeats 1000000 in
theorem t1p_122_1_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 1], ![0, 0, 0], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![0, 1, 1], ![0, 0, 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (2 * j + 10 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (104 : ℂ) = 0 := by
      linear_combination (-((-10) - 2 * j)) * hP + (2 ^ 2 - ((-10) - 2 * j) * (10)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_122_2_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, (-1)]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_123_0_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) = κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 1, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, (-1), 0], ![(-1), 1, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-2), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-2), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-12) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (144 : ℂ) = 0 := by
      linear_combination (-(12 - 0 * j)) * hP + (0 ^ 2 - (12 - 0 * j) * ((-12))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_132_0_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) = κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]]] ?_
    ![![![(-1), 1, 2], ![0, 0, (-1)], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![(-1), 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 1, (-1)], ![0, 0, 0], ![0, (-1), 1]], ![![0, 0, 1], ![0, 1, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 2], ![0, 0, (-1)], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![(-1), 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_133_1_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]]] ?_
    ![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - (-108) * j)) * hP + ((-108) ^ 2 - (0 - (-108) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_133_2_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, (-1)]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_211_1_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 0, 0], ![1, 1, (-1)]], ![![0, 1, (-1)], ![0, (-1), 1], ![0, 0, 0]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', j * c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', j * c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (2 + 10 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (104 : ℂ) = 0 := by
      linear_combination (-(2 - 10 * j)) * hP + (10 ^ 2 - (2 - 10 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_211_2_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, (-1)]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108)) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_311_1_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]]] ?_
    ![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t1p_311_2_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2))) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, (-1)]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_112_m_131 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, 1], ![0, 0, 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-(0 - 54 * j)) * hP + (54 ^ 2 - (0 - 54 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_112_p_213 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 1, 1]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 0, 0], ![0, 1, 1]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + (-54) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-((-54) - (-54) * j)) * hP + ((-54) ^ 2 - ((-54) - (-54) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_112_p_312 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1]]] ?_
    ![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, (-1)], ![0, 0, 0], ![1, (-1), 1]], ![![0, (-1), 1], ![0, 1, (-1)], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - (-108) * j)) * hP + ((-108) ^ 2 - (0 - (-108) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_112_m_313 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![1, 0, 1], ![0, 0, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, (-1)], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-(0 - 54 * j)) * hP + (54 ^ 2 - (0 - 54 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_113_p_121 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 1, 0], ![1, (-1), 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-(0 - (-54) * j)) * hP + ((-54) ^ 2 - (0 - (-54) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_113_p_212 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 1, 0], ![1, (-1), 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-(0 - (-54) * j)) * hP + ((-54) ^ 2 - (0 - (-54) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_113_m_213 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 1, (-1)], ![1, (-1), 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_113_m_312 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, (-1), 0], ![(-1), 1, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-(0 - 54 * j)) * hP + (54 ^ 2 - (0 - 54 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_121_p_113 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (27 + (-27) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (1458 : ℂ) = 0 := by
      linear_combination (-(27 - (-27) * j)) * hP + ((-27) ^ 2 - (27 - (-27) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_121_m_231 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]]] ?_
    ![![![(-1), 0, 1], ![1, 0, 0], ![0, 0, (-1)]], ![![0, (-1), (-1)], ![0, 0, 1], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 1], ![0, 0, 0], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![0, 1, 1], ![0, 0, 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 1], ![1, 0, 0], ![0, 0, (-1)]], ![![0, (-1), (-1)], ![0, 0, 1], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + 54 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-((-54) - 54 * j)) * hP + (54 ^ 2 - ((-54) - 54 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_121_m_321 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]] ?_
    ![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, (-1)], ![0, 0, 0], ![1, (-1), 1]], ![![0, (-1), 1], ![0, 1, (-1)], ![0, 0, 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_121_p_331 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (27 + (-27) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (1458 : ℂ) = 0 := by
      linear_combination (-(27 - (-27) * j)) * hP + ((-27) ^ 2 - (27 - (-27) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_122_p_223 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![0, 0, 1], ![1, 1, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_122_m_232 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 1]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 1], ![0, 0, 0], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![0, 1, 1], ![0, 0, 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (2 * j + 10 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (104 : ℂ) = 0 := by
      linear_combination (-((-10) - 2 * j)) * hP + (2 ^ 2 - ((-10) - 2 * j) * (10)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_122_m_323 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![1, 0, 1], ![0, 1, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, (-1)], ![0, 0, 0], ![1, (-1), 1]], ![![0, (-1), 1], ![0, 1, (-1)], ![0, 0, 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (2 * j + 10 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (104 : ℂ) = 0 := by
      linear_combination (-((-10) - 2 * j)) * hP + (2 ^ 2 - ((-10) - 2 * j) * (10)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_122_p_332 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 1]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_123_m_233 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 1, 1], ![1, 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![1, (-1), 0], ![(-1), 1, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-2), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-2), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-12) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (144 : ℂ) = 0 := by
      linear_combination (-(12 - 0 * j)) * hP + (0 ^ 2 - (12 - 0 * j) * ((-12))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_123_m_322 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 1]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, (-1), 0], ![(-1), 1, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-2), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-2), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-12) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (144 : ℂ) = 0 := by
      linear_combination (-(12 - 0 * j)) * hP + (0 ^ 2 - (12 - 0 * j) * ((-12))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_131_m_112 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![1, 1, 2] ![1, 2, 1]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (81 * j + (-27) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (7290 : ℂ) = 0 := by
      linear_combination (-(27 - 81 * j)) * hP + (81 ^ 2 - (27 - 81 * j) * ((-27))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_131_m_113 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_131_m_221 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![1, 1, 2] ![1, 2, 1]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (81 * j + (-27) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (7290 : ℂ) = 0 := by
      linear_combination (-(27 - 81 * j)) * hP + (81 ^ 2 - (27 - 81 * j) * ((-27))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_131_p_231 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]]] ?_
    ![![![0, 1, 1], ![0, 0, 0], ![0, (-1), (-1)]], ![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 1, 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 1, 1], ![0, 0, 0], ![0, (-1), (-1)]], ![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-162) * j + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (29160 : ℂ) = 0 := by
      linear_combination (-(54 - (-162) * j)) * hP + ((-162) ^ 2 - (54 - (-162) * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_131_p_321 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]] ?_
    ![![![(-1), 1, 0], ![0, 0, 0], ![1, (-1), 0]], ![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-2), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![0, 0, 0], ![1, (-1), 0]], ![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-2), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-12) * j + 6 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (180 : ℂ) = 0 := by
      linear_combination (-((-6) - (-12) * j)) * hP + ((-12) ^ 2 - ((-6) - (-12) * j) * (6)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_131_m_331 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_132_p_233 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 1, 1], ![1, 0, 0]]] ?_
    ![![![(-1), 1, 2], ![0, 0, (-1)], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![(-1), 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 1, 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 2], ![0, 0, (-1)], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![(-1), 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_132_p_322 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 1]]] ?_
    ![![![(-1), 1, 2], ![0, 0, (-1)], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![(-1), 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 2], ![0, 0, (-1)], ![1, (-1), (-1)]], ![![0, (-1), (-1)], ![(-1), 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_133_m_223 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 1, 0]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_133_p_232 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 1]]] ?_
    ![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - (-108) * j)) * hP + ((-108) ^ 2 - (0 - (-108) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_133_p_323 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 1], ![0, 1, 0]]] ?_
    ![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, (-1)], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![j * c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - (-108) * j)) * hP + ((-108) ^ 2 - (0 - (-108) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_133_m_332 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -j * c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 1]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-j * c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_211_m_223 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 1, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108)) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_211_p_232 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 1]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 0, 0], ![1, 1, (-1)]], ![![0, 1, (-1)], ![0, (-1), 1], ![0, 0, 0]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', j * c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', j * c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (2 + 10 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (104 : ℂ) = 0 := by
      linear_combination (-(2 - 10 * j)) * hP + (10 ^ 2 - (2 - 10 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_211_p_323 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![1, 0, 1], ![0, 1, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 1, 1], ![0, 0, 0], ![0, (-1), (-1)]], ![![0, 0, (-1)], ![0, 1, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 0, 0], ![1, 1, 1]], ![![0, 1, 1], ![0, (-1), (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', j * c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', j * c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (2 + 10 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (104 : ℂ) = 0 := by
      linear_combination (-(2 - 10 * j)) * hP + (10 ^ 2 - (2 - 10 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_211_m_332 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 1]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108)) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_212_m_113 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (27 * j + (-27) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (1458 : ℂ) = 0 := by
      linear_combination (-(27 - 27 * j)) * hP + (27 ^ 2 - (27 - 27 * j) * ((-27))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_212_p_231 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]]] ?_
    ![![![(-1), 0, 1], ![1, 0, 0], ![0, 0, (-1)]], ![![0, (-1), (-1)], ![0, 0, 1], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 0, 0], ![1, 1, (-1)]], ![![0, 1, (-1)], ![0, (-1), 1], ![0, 0, 0]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 1], ![1, 0, 0], ![0, 0, (-1)]], ![![0, (-1), (-1)], ![0, 0, 1], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 * j + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-(54 - 54 * j)) * hP + (54 ^ 2 - (54 - 54 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_212_p_321 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]] ?_
    ![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 1, 1], ![0, 0, 0], ![0, (-1), (-1)]], ![![0, 0, (-1)], ![0, 1, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 0, 0], ![1, 1, 1]], ![![0, 1, 1], ![0, (-1), (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_212_m_331 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 1, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, 0], ![0, (-1), 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (27 * j + (-27) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (1458 : ℂ) = 0 := by
      linear_combination (-(27 - 27 * j)) * hP + (27 ^ 2 - (27 - 27 * j) * ((-27))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_213_m_112 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), (-1)], ![0, 0, 0], ![0, 1, 1]], ![![(-1), 1, 1], ![1, (-1), (-1)], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 * j + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-(54 - 54 * j)) * hP + (54 ^ 2 - (54 - 54 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_213_m_113 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, 1, 1], ![0, (-1), (-1)], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 1, (-1)], ![1, (-1), 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, 1, 1], ![0, (-1), (-1)], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 + 54 * j + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (29160 : ℂ) = 0 := by
      linear_combination (-(162 - 54 * j)) * hP + (54 ^ 2 - (162 - 54 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_213_m_221 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![0, (-1), 1], ![0, 0, 0], ![0, 1, (-1)]], ![![(-1), 1, (-1)], ![1, (-1), 1], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 * j + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-(54 - 54 * j)) * hP + (54 ^ 2 - (54 - 54 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_213_p_321 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]] ?_
    ![![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, (-1), 0], ![0, (-1), (-1)], ![0, 2, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 1], ![0, 1, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, (-1), 0], ![(-1), 1, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, (-1), 0], ![0, (-1), (-1)], ![0, 2, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 + (-270) * j + (-216) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (145800 : ℂ) = 0 := by
      linear_combination (-(270 - (-270) * j)) * hP + ((-270) ^ 2 - (270 - (-270) * j) * ((-216))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_213_m_331 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]] ?_
    ![![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, 1, 1], ![0, (-1), (-1)], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 1, 1], ![1, (-1), 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, 1, 1], ![0, (-1), (-1)], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 + 54 * j + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (29160 : ℂ) = 0 := by
      linear_combination (-(162 - 54 * j)) * hP + (54 ^ 2 - (162 - 54 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_221_p_131 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![(-1), 0, 1], ![0, 0, 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-(54 - 0 * j)) * hP + (0 ^ 2 - (54 - 0 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_221_m_213 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]]] ?_
    ![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 1, 1]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 1, (-1)], ![0, 0, 0], ![0, (-1), 1]], ![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) * j + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-(54 - (-54) * j)) * hP + ((-54) ^ 2 - (54 - (-54) * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_221_m_312 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1]]] ?_
    ![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 1, 1], ![0, 0, 0], ![0, (-1), (-1)]], ![![0, 0, (-1)], ![0, 1, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![(-1), (-1), (-1)], ![0, 0, 0], ![1, 1, 1]], ![![0, 1, 1], ![0, (-1), (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, (-1), 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_221_p_313 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![1, 0, 1], ![0, 0, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![0, 1, 2] ![1, 2, 1]
    ![![![1, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![(-1), 0, (-1)], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-(54 - 0 * j)) * hP + (0 ^ 2 - (54 - 0 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_223_p_122 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 1, 0], ![1, (-1), 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_223_p_133 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![0, 1, 1], ![0, 0, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, 0], ![0, 0, 1], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![1, (-1), 0], ![(-1), 1, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_223_p_211 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 1, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 1, 0], ![1, (-1), 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_223_p_311 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![1, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![1, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 1], ![0, 1, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, (-1), 0], ![(-1), 1, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_231_p_121 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![![1, 0, (-1)], ![0, 0, 1], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![1, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, (-1)], ![0, 0, 1], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_231_p_131 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![![0, (-1), (-1)], ![0, 1, 1], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 1, 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), (-1)], ![0, 1, 1], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_231_p_212 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]]] ?_
    ![![![1, 0, (-1)], ![0, 0, 1], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 1, (-1)], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, (-1)], ![0, 0, 1], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_231_m_213 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]]] ?_
    ![![![1, (-1), (-1)], ![0, 1, 1], ![(-1), 0, 0]], ![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![1, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, (-1), (-1)], ![0, 1, 1], ![(-1), 0, 0]], ![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-162) + 54 * j + (-216) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-(54 - 54 * j)) * hP + (54 ^ 2 - (54 - 54 * j) * ((-216))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_231_m_312 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1]]] ?_
    ![![![(-1), (-1), 0], ![0, 1, 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![(-1), 0, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 1, 1], ![0, 0, (-1)], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![0, 1, 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![(-1), 0, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-20) + 6 * j + (-26) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (72 : ℂ) = 0 := by
      linear_combination (-(6 - 6 * j)) * hP + (6 ^ 2 - (6 - 6 * j) * ((-26))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_231_p_313 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![1, 0, 1], ![0, 0, 0]]] ?_
    ![![![0, (-1), (-1)], ![0, 1, 1], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 1, 1], ![0, 0, (-1)], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), (-1)], ![0, 1, 1], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 + (-54) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-54))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_232_p_122 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]]] ?_
    ![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![1, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - (-108) * j)) * hP + ((-108) ^ 2 - (0 - (-108) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_232_p_133 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![0, 1, 1], ![0, 0, 0]]] ?_
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 1, 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_232_p_211 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]]] ?_
    ![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), (-1), 1], ![0, 1, (-1)], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - (-108) * j)) * hP + ((-108) ^ 2 - (0 - (-108) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_232_p_311 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![1, 0, 1]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]]] ?_
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 1, 1], ![0, 0, (-1)], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), (-1), (-1)], ![0, 1, 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_233_p_123 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]]] ?_
    ![![![0, (-1), (-1)], ![1, 1, 1], ![(-1), 0, 0]], ![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![1, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-2), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), (-1)], ![1, 1, 1], ![(-1), 0, 0]], ![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-2), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-18) * j + (-30) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (1224 : ℂ) = 0 := by
      linear_combination (-(30 - (-18) * j)) * hP + ((-18) ^ 2 - (30 - (-18) * j) * ((-30))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_233_p_132 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 1]]] ?_
    ![![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![(-1), 0, 1], ![0, 0, (-1)], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![1, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, (-1), 0], ![(-1), 1, 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![c', -c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![(-1), 0, 1], ![0, 0, (-1)], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![c', -c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-12) * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (144 : ℂ) = 0 := by
      linear_combination (-(0 - (-12) * j)) * hP + ((-12) ^ 2 - (0 - (-12) * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_311_p_223 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 1, 0]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_311_m_232 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 1]]] ?_
    ![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 0, (-1)], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_311_m_323 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 1], ![0, 1, 0]]] ?_
    ![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 1, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), (-1)], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![0, 1, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_311_p_332 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 1]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_312_p_112 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![1, 1, 2] ![1, 2, 1]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, (-1)], ![(-1), (-1), 1], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + 54 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (54)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_312_p_113 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![![0, 0, (-1)], ![1, 0, 1], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, (-1)], ![1, 0, 1], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 54 * j + 81 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (14580 : ℂ) = 0 := by
      linear_combination (-((-108) - 54 * j)) * hP + (54 ^ 2 - ((-108) - 54 * j) * (81)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_312_p_221 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![1, 1, 2] ![1, 2, 1]
    ![![![0, 0, (-1)], ![1, 0, 1], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![0, 1, 1], ![(-1), (-1), (-1)], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + 54 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (54)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_312_m_231 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]]] ?_
    ![![![0, 0, (-1)], ![0, 1, 2], ![0, (-1), (-1)]], ![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 0, (-1)], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, (-1)], ![0, 1, 2], ![0, (-1), (-1)]], ![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (162 + 270 * j + 432 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (145800 : ℂ) = 0 := by
      linear_combination (-((-270) - 270 * j)) * hP + (270 ^ 2 - ((-270) - 270 * j) * (432)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_312_m_321 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]] ?_
    ![![![0, 0, (-1)], ![(-1), 1, 1], ![1, (-1), 0]], ![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 1, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), (-1)], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, (-1)], ![(-1), 1, 1], ![1, (-1), 0]], ![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 * j + 54 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-((-54) - 54 * j)) * hP + (54 ^ 2 - ((-54) - 54 * j) * (54)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_312_p_331 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]] ?_
    ![![![0, 0, (-1)], ![1, 0, 1], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, (-1)], ![1, 0, 1], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 54 * j + 81 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (14580 : ℂ) = 0 := by
      linear_combination (-((-108) - 54 * j)) * hP + (54 ^ 2 - ((-108) - 54 * j) * (81)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_313_p_112 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![1, 1, 2] ![1, 2, 1]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 0], ![0, (-1), 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + 27 * j + 27 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (7290 : ℂ) = 0 := by
      linear_combination (-((-81) - 27 * j)) * hP + (27 ^ 2 - ((-81) - 27 * j) * (27)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_313_p_113 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 0], ![0, (-1), 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 81 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (81)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_313_p_221 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 1, 0]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]]
    ![1, 1, 2] ![1, 2, 1]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]]
    ![![![(-1), 1, 0], ![0, (-1), 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + 27 * j + 27 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (7290 : ℂ) = 0 := by
      linear_combination (-((-81) - 27 * j)) * hP + (27 ^ 2 - ((-81) - 27 * j) * (27)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_313_m_231 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]]] ?_
    ![![![0, 1, 1], ![0, 0, 0], ![0, (-1), (-1)]], ![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 1, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 1], ![0, (-1), 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 1, 1], ![0, 0, 0], ![0, (-1), (-1)]], ![![(-1), (-1), (-1)], ![0, 1, 1], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (162 + (-54) * j + 324 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (29160 : ℂ) = 0 := by
      linear_combination (-((-162) - (-54) * j)) * hP + ((-54) ^ 2 - ((-162) - (-54) * j) * (324)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_313_m_321 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]] ?_
    ![![![(-1), 1, 0], ![0, 0, 0], ![1, (-1), 0]], ![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, (-1)], ![0, (-1), 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-2), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 1, 0], ![0, 0, 0], ![1, (-1), 0]], ![![0, (-1), 0], ![(-1), 1, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-2), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-4) + 6 * j + 8 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (180 : ℂ) = 0 := by
      linear_combination (-((-12) - 6 * j)) * hP + (6 ^ 2 - ((-12) - 6 * j) * (8)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_313_p_331 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = j * c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]] ?_
    ![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 0], ![0, (-1), 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 0], ![0, 0, 0], ![(-1), 0, 0]], ![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', j * c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 81 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (81)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_321_m_121 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, (-1)], ![(-1), (-1), 1], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + 54 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (54)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_321_m_131 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]]] ?_
    ![![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 27 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-((-54) - 0 * j)) * hP + (0 ^ 2 - ((-54) - 0 * j) * (27)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_321_m_212 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]]] ?_
    ![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![0, 0, (-1)], ![1, 0, 1], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![0, 1, 1], ![(-1), (-1), (-1)], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, 0, 0], ![1, 0, 0], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-54) + 54 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (54)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_321_p_213 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]]] ?_
    ![![![0, (-1), 0], ![1, 1, 0], ![(-1), 0, 0]], ![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), 0], ![1, 1, 0], ![(-1), 0, 0]], ![![(-1), (-1), (-1)], ![1, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (162 + (-54) * j + 216 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (5832 : ℂ) = 0 := by
      linear_combination (-((-54) - (-54) * j)) * hP + ((-54) ^ 2 - ((-54) - (-54) * j) * (216)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_321_m_313 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 1], ![0, 0, 0]]] ?_
    ![![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 1, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), (-1)], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), 0], ![0, 1, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 27 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-((-54) - 0 * j)) * hP + (0 ^ 2 - ((-54) - 0 * j) * (27)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_322_p_123 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]]] ?_
    ![![![0, (-1), (-1)], ![1, 1, 1], ![(-1), 0, 0]], ![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 0], ![1, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-2), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), (-1)], ![1, 1, 1], ![(-1), 0, 0]], ![![(-1), 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-2), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (18 * j + 30 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (1224 : ℂ) = 0 := by
      linear_combination (-((-30) - 18 * j)) * hP + (18 ^ 2 - ((-30) - 18 * j) * (30)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_322_p_132 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 1, 1]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 1]]] ?_
    ![![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![(-1), 0, 1], ![0, 0, (-1)], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![(-1), (-1), 1], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-2)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]], ![![(-1), 0, 1], ![0, 0, (-1)], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-2)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (12 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (144 : ℂ) = 0 := by
      linear_combination (-(0 - 12 * j)) * hP + (12 ^ 2 - (0 - 12 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_323_p_122 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]]] ?_
    ![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, (-1)], ![0, (-1), 1], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_323_p_133 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 1, 1], ![0, 0, 0]]] ?_
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, 1], ![0, (-1), 0], ![1, 0, (-1)]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_323_p_211 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]]] ?_
    ![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![1, 1, 2] ![1, 2, 2]
    ![![![0, 0, (-1)], ![1, 0, 1], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![(-1), 1, 1], ![0, (-1), (-1)], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![1, 0, 1], ![0, 0, (-1)], ![(-1), 0, 0]], ![![(-1), (-1), 0], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(0 - 108 * j)) * hP + (108 ^ 2 - (0 - 108 * j) * 0) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_323_p_311 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]]] ?_
    ![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![1, 2, 2] ![2, 1, 2]
    ![![![0, 1, 0], ![1, 0, 0], ![0, (-1), 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![(-1), 1, (-1)], ![0, (-1), 0], ![1, 0, 1]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), (-1), 0], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', c', -c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_331_m_121 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![1, 1, 0], ![(-1), 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![1, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 27 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-((-54) - 0 * j)) * hP + (0 ^ 2 - ((-54) - 0 * j) * (27)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_331_m_212 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = -j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 1]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![1, 1, 0], ![(-1), 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![1, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', -j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', -j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-27) + 27 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-((-54) - 0 * j)) * hP + (0 ^ 2 - ((-54) - 0 * j) * (27)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_331_p_213 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) + κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![1, 1, 1], ![(-1), 0, 0], ![0, 0, (-1)]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![(-1), (-1), (-1)], ![1, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, (-1), (-1)], ![0, 0, 0], ![0, 1, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (54 + 162 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (162)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_331_p_312 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = j * c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1]]] ?_
    ![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 1], ![1, 1, 0], ![(-1), (-1), (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', j * c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 0], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', j * c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (27 + 81 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (2916 : ℂ) = 0 := by
      linear_combination (-((-54) - 0 * j)) * hP + (0 ^ 2 - ((-54) - 0 * j) * (81)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_332_p_122 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 1]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![1, 1, 0], ![(-1), 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![1, 1, 0], ![0, 0, 0]], ![![0, 0, (-1)], ![0, 0, 1], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_332_p_133 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) + κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 1, 1], ![0, 0, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 1, 0], ![(-1), 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, (-1)], ![1, 1, 0], ![(-1), (-1), 1]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_332_p_211 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]]
    ![0, 1, 2] ![1, 2, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![1, 1, 0], ![(-1), 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![(-1), (-1), 0], ![1, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, (-1)], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, (-1), 1], ![0, 0, (-1)], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = ((-108) * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-(108 - 0 * j)) * hP + (0 ^ 2 - (108 - 0 * j) * ((-108))) * hj
    norm_num at hN

set_option maxHeartbeats 1000000 in
theorem t3p_332_p_311 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (hFK : ∀ i, ∀ t ∈ L, dotL (κs i) (rowMap (rr (Sum.inl i)) t) = 0)
    (c c' j : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0) (hj : j * j = -1)
    (hw1 : κs 1 (cc (Sum.inl 0)) = j * c * κs 0 (cc (Sum.inl 0)) ∧
      κs 1 (cc (Sum.inl 1)) = c * κs 0 (cc (Sum.inl 1)) ∧
      κs 1 (cc (Sum.inl 2)) = -c * κs 0 (cc (Sum.inl 2)))
    (hw2 : κs 2 (cc (Sum.inl 0)) = -c' * κs 0 (cc (Sum.inl 0)) ∧
      κs 2 (cc (Sum.inl 1)) = -c' * κs 0 (cc (Sum.inl 1)) ∧
      κs 2 (cc (Sum.inl 2)) = c' * κs 0 (cc (Sum.inl 2)))
    (hrel : ∀ t ∈ blkL L rr cc,
      κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) + κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) = 0 ∧
      κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) + κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) + κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) = 0 ∧
      κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) = 0) : False := by
  have hj0 := jsq_ne hj
  refine stest_gen hL h9 rr cc h0 κs hκs hFK ![![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]]] ?_
    ![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]]
    ![0, 2, 2] ![1, 1, 2]
    ![![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![1, 1, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]]
    ![![![0, 1, 0], ![0, 0, 0], ![0, (-1), 0]], ![![0, 0, 1], ![1, 1, 0], ![(-1), (-1), (-1)]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]] ?_
    ![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] ?_ ?_ ?_ ?_ ![(-3), (-3), (-3)] ?_
  · intro t ht r
    obtain ⟨E12, E13, E23⟩ := hrel t ht
    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · linear_combination E12
    · linear_combination E13
    · linear_combination E23
  · intro i k v
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl <;> rfl
  · intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |
        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |
        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw1.1
    · exact hw1.2.1
    · exact hw1.2.2
  · intro k
    rcases fin3_cases k with rfl | rfl | rfl
    · exact hw2.1
    · exact hw2.2.1
    · exact hw2.2.2
  · intro hz
    have hP : (Matrix.of fun i k => (∑ l, (![![![(-1), 0, (-1)], ![1, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, (-1)], ![0, 0, 1]], ![![0, (-1), (-1)], ![0, 1, 0], ![0, 0, 1]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * (![(-3), (-3), (-3)] : Fin 3 → ℂ) l) / (![![1, 1, 1], ![j * c, c, -c], ![-c', -c', c']] : Fin 3 → Fin 3 → ℂ) i k).permanent * (j ^ 2 * c * c') = (108 * j ^ 2) := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      ring
    rw [hz, zero_mul] at hP
    have hN : (11664 : ℂ) = 0 := by
      linear_combination (-((-108) - 0 * j)) * hP + (0 ^ 2 - ((-108) - 0 * j) * (108)) * hj
    norm_num at hN

theorem quad_poly_ne (a b c : ℂ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 := by
  intro h0
  have e0 := congrArg (fun p => Polynomial.coeff p 0) h0
  have e1 := congrArg (fun p => Polynomial.coeff p 1) h0
  have e2 := congrArg (fun p => Polynomial.coeff p 2) h0
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_zero] at e0 e1 e2
  norm_num at e0 e1 e2
  rcases h with h | h | h
  · exact h e0
  · exact h e1
  · exact h e2

theorem three_factor_plane (dot : (Fin 3 → ℂ) → (Fin 3 → ℂ) → ℂ)
    (hdot : ∀ l x y (s : ℂ), dot l (x + s • y) = dot l x + s * dot l y)
    (l1 l2 l3 n : Fin 3 → ℂ)
    (h : ∀ x, dot n x = 0 → dot l1 x * dot l2 x * dot l3 x = 0) :
    (∀ x, dot n x = 0 → dot l1 x = 0) ∨ (∀ x, dot n x = 0 → dot l2 x = 0) ∨
      (∀ x, dot n x = 0 → dot l3 x = 0) := by
  by_contra hno
  simp only [not_or, not_forall] at hno
  obtain ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩, ⟨x3, hx3, h3⟩⟩ := hno
  have hpt : ∀ s : ℂ, dot n (x1 + s • (x2 + s • x3)) = 0 := by
    intro s
    rw [hdot, hdot, hx1, hx2, hx3]
    ring
  have hval : ∀ (l : Fin 3 → ℂ) (s : ℂ), dot l (x1 + s • (x2 + s • x3)) =
      Polynomial.eval s (Polynomial.C (dot l x1) + Polynomial.C (dot l x2) * Polynomial.X +
        Polynomial.C (dot l x3) * Polynomial.X ^ 2) := by
    intro l s
    rw [hdot, hdot]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow]
    ring
  have hP : (Polynomial.C (dot l1 x1) + Polynomial.C (dot l1 x2) * Polynomial.X +
        Polynomial.C (dot l1 x3) * Polynomial.X ^ 2) *
      (Polynomial.C (dot l2 x1) + Polynomial.C (dot l2 x2) * Polynomial.X +
        Polynomial.C (dot l2 x3) * Polynomial.X ^ 2) *
      (Polynomial.C (dot l3 x1) + Polynomial.C (dot l3 x2) * Polynomial.X +
        Polynomial.C (dot l3 x3) * Polynomial.X ^ 2) = 0 := by
    apply Polynomial.funext
    intro s
    simp only [Polynomial.eval_mul, Polynomial.eval_zero]
    rw [← hval l1 s, ← hval l2 s, ← hval l3 s]
    exact h _ (hpt s)
  rcases mul_eq_zero.mp hP with hP | hP
  · rcases mul_eq_zero.mp hP with hP | hP
    · exact quad_poly_ne _ _ _ (Or.inl h1) hP
    · exact quad_poly_ne _ _ _ (Or.inr (Or.inl h2)) hP
  · exact quad_poly_ne _ _ _ (Or.inr (Or.inr h3)) hP

noncomputable def cubT (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, T i j k * x i * x j * x k

noncomputable def gradT (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) (m : Fin 3) : ℂ :=
  ∑ j, ∑ k, (T m j k + T j m k + T j k m) * x j * x k

theorem cubT_expand (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ) (h : ℂ) :
    cubT T (p + h • w) = cubT T p + h * (∑ m, gradT T p m * w m) +
      h ^ 2 * (∑ m, gradT T w m * p m) + h ^ 3 * cubT T w := by
  simp only [cubT, gradT, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem cubT_tangent (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ)
    (hw : ∀ h : ℂ, cubT T (p + h • w) = 0) : ∑ m, gradT T p m * w m = 0 := by
  have e0 := hw 0
  have e1 := hw 1
  have e2 := hw (-1)
  have e3 := hw 2
  rw [cubT_expand] at e0 e1 e2 e3
  linear_combination e1 - (1 / 3 : ℂ) * e2 - (1 / 2 : ℂ) * e0 - (1 / 6 : ℂ) * e3

theorem binary_quad_zero (a b c : ℂ) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ s ^ 2 * a + s * t * b + t ^ 2 * c = 0 := by
  by_cases ha : a = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by rw [ha]; ring⟩
  · obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (discrim a b c)
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨z, hz⟩
    exact ⟨x, 1, Or.inr one_ne_zero, by linear_combination hx⟩

theorem cubic_no_plane (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (Aq : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (hcert : ∀ (x : Fin 3 → ℂ) (k : Fin 3),
      x k ^ 4 = ∑ i, (∑ j, ∑ l, Aq k i j l * x j * x l) * gradT T x i)
    (w1 w2 : Fin 3 → ℂ) (hdet : w1 0 * w2 1 - w1 1 * w2 0 ≠ 0)
    (hvan : ∀ s t : ℂ, cubT T (s • w1 + t • w2) = 0) : False := by
  have binq : ∀ s t : ℂ, gradT T (s • w1 + t • w2) 2 = s ^ 2 * gradT T w1 2 +
      s * t * (gradT T (w1 + w2) 2 - gradT T w1 2 - gradT T w2 2) + t ^ 2 * gradT T w2 2 := by
    intro s t
    simp only [gradT, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨s0, t0, hst, hq⟩ := binary_quad_zero (gradT T w1 2)
    (gradT T (w1 + w2) 2 - gradT T w1 2 - gradT T w2 2) (gradT T w2 2)
  have g1 : ∑ m, gradT T (s0 • w1 + t0 • w2) m * w1 m = 0 := by
    apply cubT_tangent
    intro h
    have e : s0 • w1 + t0 • w2 + h • w1 = (s0 + h) • w1 + t0 • w2 := by
      funext m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact hvan _ _
  have g2 : ∑ m, gradT T (s0 • w1 + t0 • w2) m * w2 m = 0 := by
    apply cubT_tangent
    intro h
    have e : s0 • w1 + t0 • w2 + h • w2 = s0 • w1 + (t0 + h) • w2 := by
      funext m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact hvan _ _
  have g3 : gradT T (s0 • w1 + t0 • w2) 2 = 0 := by
    rw [binq]
    linear_combination hq
  rw [Fin.sum_univ_three] at g1 g2
  rw [g3] at g1 g2
  have d0 : gradT T (s0 • w1 + t0 • w2) 0 * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by
    linear_combination w2 1 * g1 - w1 1 * g2
  have d1 : gradT T (s0 • w1 + t0 • w2) 1 * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by
    linear_combination w1 0 * g2 - w2 0 * g1
  have z0 := (mul_eq_zero.mp d0).resolve_right hdet
  have z1 := (mul_eq_zero.mp d1).resolve_right hdet
  have hp : ∀ k, (s0 • w1 + t0 • w2) k = 0 := by
    intro k
    have e := hcert (s0 • w1 + t0 • w2) k
    simp only [Fin.sum_univ_three, z0, z1, g3, mul_zero, add_zero] at e
    exact (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp e
  have p0 := hp 0
  have p1 := hp 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p0 p1
  have es : s0 * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by linear_combination w2 1 * p0 - w2 0 * p1
  have et : t0 * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by linear_combination w1 0 * p1 - w1 1 * p0
  rcases hst with h | h
  · exact h ((mul_eq_zero.mp es).resolve_right hdet)
  · exact h ((mul_eq_zero.mp et).resolve_right hdet)

noncomputable def quadQ (Q : Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) : ℂ := ∑ i, ∑ j, Q i j * x i * x j

noncomputable def gradQ (Q : Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) (k : Fin 3) : ℂ :=
  ∑ j, (Q k j + Q j k) * x j

theorem quadQ_expand (Q : Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ) (h : ℂ) :
    quadQ Q (p + h • w) = quadQ Q p + h * (∑ k, gradQ Q p k * w k) + h ^ 2 * quadQ Q w := by
  simp only [quadQ, gradQ, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem quadQ_tangent (Q : Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ)
    (hw : ∀ h : ℂ, quadQ Q (p + h • w) = 0) : ∑ k, gradQ Q p k * w k = 0 := by
  have e0 := hw 0
  have e1 := hw 1
  have e2 := hw (-1)
  rw [quadQ_expand] at e0 e1 e2
  linear_combination (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * e2

theorem quad_no_plane (Q N : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N i k * gradQ Q x k)
    (w1 w2 : Fin 3 → ℂ) (hdet : w1 0 * w2 1 - w1 1 * w2 0 ≠ 0)
    (hvan : ∀ s t : ℂ, quadQ Q (s • w1 + t • w2) = 0) : False := by
  have tan1 : ∀ s t : ℂ, ∑ k, gradQ Q (s • w1 + t • w2) k * w1 k = 0 := by
    intro s t
    apply quadQ_tangent
    intro h
    have e : s • w1 + t • w2 + h • w1 = (s + h) • w1 + t • w2 := by
      funext m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact hvan _ _
  have tan2 : ∀ s t : ℂ, ∑ k, gradQ Q (s • w1 + t • w2) k * w2 k = 0 := by
    intro s t
    apply quadQ_tangent
    intro h
    have e : s • w1 + t • w2 + h • w2 = s • w1 + (t + h) • w2 := by
      funext m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact hvan _ _
  have lin : ∀ s t : ℂ, ∀ k, gradQ Q (s • w1 + t • w2) k = s * gradQ Q w1 k + t * gradQ Q w2 k := by
    intro s t k
    simp only [gradQ, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have a1 := tan1 1 0
  have a2 := tan2 1 0
  have b1 := tan1 0 1
  have b2 := tan2 0 1
  simp only [lin, Fin.sum_univ_three, one_mul, zero_mul, add_zero, zero_add] at a1 a2 b1 b2
  set a0 := gradQ Q w1 0 with ha0
  set a1' := gradQ Q w1 1 with ha1
  set a2' := gradQ Q w1 2 with ha2
  set b0 := gradQ Q w2 0 with hb0
  set b1' := gradQ Q w2 1 with hb1
  set b2' := gradQ Q w2 2 with hb2
  have v0 : (b2' * a0 - a2' * b0) * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by
    linear_combination (b2' * w2 1) * a1 - (b2' * w1 1) * a2 - (a2' * w2 1) * b1 + (a2' * w1 1) * b2
  have v1 : (b2' * a1' - a2' * b1') * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by
    linear_combination (b2' * w1 0) * a2 - (b2' * w2 0) * a1 - (a2' * w1 0) * b2 + (a2' * w2 0) * b1
  have z0 := (mul_eq_zero.mp v0).resolve_right hdet
  have z1 := (mul_eq_zero.mp v1).resolve_right hdet
  have hv : ∀ i, (b2' • w1 - a2' • w2) i = 0 := by
    intro i
    have e := hN (b2' • w1 - a2' • w2) i
    have g : ∀ k, gradQ Q (b2' • w1 - a2' • w2) k = b2' * gradQ Q w1 k - a2' * gradQ Q w2 k := by
      intro k
      simp only [gradQ, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Fin.sum_univ_three, g, g, g] at e
    rw [e, ← ha0, ← ha1, ← ha2, ← hb0, ← hb1, ← hb2]
    linear_combination N i 0 * z0 + N i 1 * z1
  have p0 := hv 0
  have p1 := hv 1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at p0 p1
  have eb : b2' * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by linear_combination w2 1 * p0 - w2 0 * p1
  have ea : a2' * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by linear_combination w1 1 * p0 - w1 0 * p1
  have hb2z := (mul_eq_zero.mp eb).resolve_right hdet
  have ha2z := (mul_eq_zero.mp ea).resolve_right hdet
  have c0 : a0 * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by
    linear_combination w2 1 * a1 - w1 1 * a2 + (w1 1 * w2 2 - w2 1 * w1 2) * ha2z
  have c1 : a1' * (w1 0 * w2 1 - w1 1 * w2 0) = 0 := by
    linear_combination w1 0 * a2 - w2 0 * a1 + (w2 0 * w1 2 - w1 0 * w2 2) * ha2z
  have za0 := (mul_eq_zero.mp c0).resolve_right hdet
  have za1 := (mul_eq_zero.mp c1).resolve_right hdet
  have hw1 : ∀ i, w1 i = 0 := by
    intro i
    rw [hN w1 i, Fin.sum_univ_three, ← ha0, ← ha1, ← ha2, za0, za1, ha2z]
    ring
  apply hdet
  rw [hw1 0, hw1 1]
  ring

end PEqualNP.Outside.L_gct_210_aux.ZBF

theorem PEqualNP.Outside.L_gct_210 : True := by
  trivial
