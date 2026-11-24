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

theorem typeCl_swap (κ κ' ν ν' : Fin 5 → ℂ) (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0)
    (a b : Fin 5) (h : TypeCl κ κ' ν ν' a b) : TypeCl κ' κ ν' ν b a := by
  sorry

theorem pairI_swap {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (h : PairI L r r') :
    PairI L r' r := by
  sorry

theorem pairII_swap {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (h : PairII L r r') :
    PairII L r' r := by
  sorry

theorem corner_of_not (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b)
    (m : Fin 5) (h1 : ν m / κ m ≠ ν b / κ b) (h2 : ν' m / κ' m ≠ ν' a / κ' a) :
    ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b := by
  sorry

theorem c23_side (κ2 κ3 : Fin 5 → ℂ) (C : Finset (Fin 5)) (f : ℂ)
    (ha : ∀ m, m ∉ C → κ3 m = f * κ2 m) (hb : ∀ m, m ∈ C → κ3 m = -f * κ2 m) (m m' : Fin 5) :
    ((m ∈ C ↔ m' ∈ C) → κ3 m * κ2 m' = κ3 m' * κ2 m) ∧
    ((m ∈ C ↔ m' ∉ C) → κ3 m * κ2 m' = -(κ3 m' * κ2 m)) := by
  sorry

theorem side_cancel (x y A B : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (h : A * x * y = B * x * y) :
    A = B := by
  sorry

theorem typeII_ite (κa κb : Fin 5 → ℂ) (B Q : Finset (Fin 5)) (ra rb : Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hoff : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (ra, m) = 0 ∧ t (rb, m) = 0)
    (rel : ∑ m ∈ B, t (ra, m) * κa m + ∑ m ∈ Q, t (rb, m) * κb m = 0) :
    (if p ∈ B then t (ra, p) * κa p else 0) + (if q ∈ B then t (ra, q) * κa q else 0) +
        (if s ∈ B then t (ra, s) * κa s else 0) +
      ((if p ∈ Q then t (rb, p) * κb p else 0) + (if q ∈ Q then t (rb, q) * κb q else 0) +
        (if s ∈ Q then t (rb, s) * κb s else 0)) = 0 := by
  sorry

theorem s_transfer {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2)
    (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) (κ κ2 κ3 : Fin 5 → ℂ)
    (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) :
    ∃ (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5) (K : Fin 3 → Fin 5 → ℂ),
      rr (Sum.inl 0) = r1 ∧ rr (Sum.inl 1) = r2 ∧ rr (Sum.inl 2) = r3 ∧
      cc (Sum.inl 0) = p ∧ cc (Sum.inl 1) = q ∧ cc (Sum.inl 2) = s ∧
      K 0 = κ ∧ K 1 = κ2 ∧ K 2 = κ3 ∧
      (∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0) ∧
      (∀ i m, K i m ≠ 0) ∧ (∀ i, ∀ t ∈ L, dotL (K i) (rowMap (rr (Sum.inl i)) t) = 0) ∧
      (∀ t ∈ blkL L rr cc, t ∈ L ∧ ∀ m, m ≠ p → m ≠ q → m ≠ s →
        t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0) := by
  sorry

theorem iffA {P Q R : Prop} (h1 : P ↔ Q) (h2 : ¬ (Q ↔ R)) : P ↔ ¬ R := by
  sorry

theorem iffB {P Q : Prop} (h : ¬ (P ↔ Q)) : P ↔ ¬ Q := by
  sorry

theorem iffC {P Q R : Prop} (h1 : ¬ (P ↔ Q)) (h2 : Q ↔ R) : P ↔ ¬ R := by
  sorry

theorem iffD {P Q R : Prop} (h1 : ¬ (P ↔ Q)) (h2 : ¬ (Q ↔ R)) : P ↔ R := by
  sorry

theorem iffE {P R : Prop} (h : P ↔ ¬ R) : R ↔ ¬ P := by
  sorry

def T1Rest3 : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2 →
    (PairII L r1 r2 ∧ PairII L r1 r3 ∧ PairII L r2 r3) → rowsZeroS L {r1, r2, r3} ≠ ⊥

theorem t1rest2_of_rest3 (h : T1Rest3) : T1Rest2 := by
  sorry

theorem t1_of_rest3 (h : T1Rest3) : T1Hyp := by
  sorry

theorem c7_split (κ κ' ν ν' : Fin 5 → ℂ) (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0)
    (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b) (Qa Qb : Finset (Fin 5))
    (hQa : ∀ m, m ∈ Qa ↔ ν' m / κ' m = ν' a / κ' a)
    (hQb : ∀ m, m ∈ Qb ↔ ν m / κ m = ν b / κ b) (z1 z2 : Fin 5 → ℂ) :
    ∑ m, z1 m * ν m = ν a / κ a * ∑ m, z1 m * κ m +
      (ν b / κ b - ν a / κ a) * ∑ m ∈ Qb, z1 m * κ m ∧
    ∑ m, z2 m * ν' m = ν' b / κ' b * ∑ m, z2 m * κ' m +
      (ν' a / κ' a - ν' b / κ' b) * ∑ m ∈ Qa, z2 m * κ' m := by
  sorry

theorem typeII_J (κ κ' ν ν' : Fin 5 → ℂ) (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0)
    (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b) (hκ1 : dotL κ 1 = 1) (hκ'1 : dotL κ' 1 = 1)
    (hν1 : dotL ν 1 + dotL ν' 1 = 0) (m0 : Fin 5)
    (hm0 : ν m0 / κ m0 = ν a / κ a ∧ ν' m0 / κ' m0 = ν' b / κ' b) (Qa Qb : Finset (Fin 5))
    (hQa : ∀ m, m ∈ Qa ↔ ν' m / κ' m = ν' a / κ' a)
    (hQb : ∀ m, m ∈ Qb ↔ ν m / κ m = ν b / κ b) :
    (∑ m ∈ Qb, κ m + ∑ m ∈ Qa, κ' m) * (κ' m0 / κ m0 + κ' a / κ a) = κ' a / κ a := by
  sorry

theorem unit_split {ω c' j : ℂ} (hω : ω ^ 2 = -c' ^ 2) (hj : j * j = -1) :
    ω = j * c' ∨ ω = -j * c' := by
  sorry

theorem stest_affine {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (N : Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3)
    (hM : ∀ w ∈ blockSpace L r c, ∀ i j, k i j * hat 5 w (r (Sum.inl i), c (Sum.inl j)) =
      ∑ l, M i j l * (k (pi l) (pj l) * hat 5 w (r (Sum.inl (pi l)), c (Sum.inl (pj l)))) +
        N i j * w.1)
    (x0 x1 : Fin 3 → ℂ) (y0 y1 : Fin 3 → Fin 3 → ℂ)
    (hy0 : ∀ i j, (∑ l, M i j l * x0 l + N i j) / k i j = y0 i j)
    (hy1 : ∀ i j, (∑ l, M i j l * x1 l + N i j) / k i j = y1 i j)
    (hperm : (Matrix.of y0).permanent ≠ (Matrix.of y1).permanent) : False := by
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

noncomputable def cubT (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, T i j k * x i * x j * x k

noncomputable def gradT (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) (m : Fin 3) : ℂ :=
  ∑ j, ∑ k, (T m j k + T j m k + T j k m) * x j * x k

theorem cubT_expand (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ) (h : ℂ) :
    cubT T (p + h • w) = cubT T p + h * (∑ m, gradT T p m * w m) +
      h ^ 2 * (∑ m, gradT T w m * p m) + h ^ 3 * cubT T w := by
  sorry

theorem cubT_tangent (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ)
    (hw : ∀ h : ℂ, cubT T (p + h • w) = 0) : ∑ m, gradT T p m * w m = 0 := by
  sorry

theorem binary_quad_zero (a b c : ℂ) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ s ^ 2 * a + s * t * b + t ^ 2 * c = 0 := by
  sorry

theorem cubic_no_plane (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (Aq : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (hcert : ∀ (x : Fin 3 → ℂ) (k : Fin 3),
      x k ^ 4 = ∑ i, (∑ j, ∑ l, Aq k i j l * x j * x l) * gradT T x i)
    (w1 w2 : Fin 3 → ℂ) (hdet : w1 0 * w2 1 - w1 1 * w2 0 ≠ 0)
    (hvan : ∀ s t : ℂ, cubT T (s • w1 + t • w2) = 0) : False := by
  sorry

noncomputable def quadQ (Q : Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) : ℂ := ∑ i, ∑ j, Q i j * x i * x j

noncomputable def gradQ (Q : Fin 3 → Fin 3 → ℂ) (x : Fin 3 → ℂ) (k : Fin 3) : ℂ :=
  ∑ j, (Q k j + Q j k) * x j

theorem quadQ_expand (Q : Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ) (h : ℂ) :
    quadQ Q (p + h • w) = quadQ Q p + h * (∑ k, gradQ Q p k * w k) + h ^ 2 * quadQ Q w := by
  sorry

theorem quadQ_tangent (Q : Fin 3 → Fin 3 → ℂ) (p w : Fin 3 → ℂ)
    (hw : ∀ h : ℂ, quadQ Q (p + h • w) = 0) : ∑ k, gradQ Q p k * w k = 0 := by
  sorry

theorem quad_no_plane (Q N : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N i k * gradQ Q x k)
    (w1 w2 : Fin 3 → ℂ) (hdet : w1 0 * w2 1 - w1 1 * w2 0 ≠ 0)
    (hvan : ∀ s t : ℂ, quadQ Q (s • w1 + t • w2) = 0) : False := by
  sorry

theorem ann23_exists {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (h9 : Module.finrank ℂ L = 9)
    (r2 r3 : Fin 5) (hx : Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3)
    (φ1 φ2 : Module.Dual ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ))) :
    ∃ φ : Module.Dual ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)),
      (∀ t ∈ L, φ (rowMap r2 t, rowMap r3 t) = 0) ∧ φ ((1 : Fin 5 → ℂ), (1 : Fin 5 → ℂ)) = 0 ∧
      φ ∉ Submodule.span ℂ {φ1, φ2} := by
  sorry

noncomputable def tauMap (κs : Fin 3 → Fin 5 → ℂ) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5) :
    (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 3 → Fin 3 → ℂ) where
  toFun t := fun i j => κs i (cc (Sum.inl j)) * t (rr (Sum.inl i), cc (Sum.inl j))
  map_add' x y := by
    funext i j
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tauMap_apply (κs : Fin 3 → Fin 5 → ℂ) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) (i j : Fin 3) :
    tauMap κs rr cc t i j = κs i (cc (Sum.inl j)) * t (rr (Sum.inl i), cc (Sum.inl j)) := by
  sorry

theorem stest_vanish {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (H : Submodule ℂ (Fin 3 → Fin 3 → ℂ)) (hH : Module.finrank ℂ H ≤ 3)
    (himg : ∀ t ∈ blkL L rr cc, tauMap κs rr cc t ∈ H) :
    ∀ τ ∈ H, (Matrix.of fun i j => τ i j / κs i (cc (Sum.inl j))).permanent = 0 := by
  sorry

theorem status3 (Q B : Finset (Fin 5)) (hQB : ∀ m, m ∈ Q → m ∉ B) (m : Fin 5) :
    (m ∈ Q ∧ m ∉ B) ∨ (m ∉ Q ∧ m ∈ B) ∨ (m ∉ Q ∧ m ∉ B) := by
  sorry

theorem ratio_eq {x y w k3 k2 k : ℂ} (hk : k ≠ 0) (h1 : k3 = x * k) (h2 : k3 = y * k2)
    (h3 : k2 = w * k) : x = y * w := by
  sorry

theorem stest_glob {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) (κ κ2 κ3 : Fin 5 → ℂ)
    (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) (A : Fin 3 → Fin 3 → Fin 3 → ℂ)
    (hrel : ∀ t ∈ L, (∀ m, m ≠ p → m ≠ q → m ≠ s →
        t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0) → ∀ r, ∑ i, ∑ k,
      A r i k * (![κ, κ2, κ3] i (![p, q, s] k) * t (![r1, r2, r3] i, ![p, q, s] k)) = 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3) (Lr La : Fin 3 → Fin 3 → Fin 3 → ℂ)
    (hid : ∀ i k (v : Fin 3 → Fin 3 → ℂ), v i k - ∑ l, M i k l * v (pi l) (pj l) =
      ∑ i', Lr i k i' * ∑ k', v i' k' + ∑ r, La i k r * ∑ i', ∑ k', A r i' k' * v i' k')
    (W : Fin 3 → Fin 3 → ℂ) (hW0 : ∀ k, W 0 k = 1) (hW : ∀ i k, W i k ≠ 0)
    (hw1 : ∀ k, κ2 (![p, q, s] k) = W 1 k * κ (![p, q, s] k))
    (hw2 : ∀ k, κ3 (![p, q, s] k) = W 2 k * κ (![p, q, s] k))
    (x0 : Fin 3 → ℂ)
    (hperm : (Matrix.of fun i k => (∑ l, M i k l * x0 l) / W i k).permanent ≠ 0) : False := by
  sorry

theorem quad_poly_ne (a b c : ℂ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 := by
  sorry

theorem three_factor_plane (dot : (Fin 3 → ℂ) → (Fin 3 → ℂ) → ℂ)
    (hdot : ∀ l x y (s : ℂ), dot l (x + s • y) = dot l x + s * dot l y)
    (l1 l2 l3 n : Fin 3 → ℂ)
    (h : ∀ x, dot n x = 0 → dot l1 x * dot l2 x * dot l3 x = 0) :
    (∀ x, dot n x = 0 → dot l1 x = 0) ∨ (∀ x, dot n x = 0 → dot l2 x = 0) ∨
      (∀ x, dot n x = 0 → dot l3 x = 0) := by
  sorry

theorem perm_apply_inv' {α : Type} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x := by
  sorry

theorem perm_inv_apply' {α : Type} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := by
  sorry

noncomputable def colPerm (σ : Equiv.Perm (Fin 5)) :
    (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ) where
  toFun t := fun x => t (x.1, σ x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem colPerm_apply (σ : Equiv.Perm (Fin 5)) (t : Fin 5 × Fin 5 → ℂ) (x : Fin 5 × Fin 5) :
    colPerm σ t x = t (x.1, σ x.2) := by
  sorry

theorem colPerm_inv (σ : Equiv.Perm (Fin 5)) (t : Fin 5 × Fin 5 → ℂ) :
    colPerm σ⁻¹ (colPerm σ t) = t := by
  sorry

theorem colPerm_injective (σ : Equiv.Perm (Fin 5)) : Function.Injective (colPerm σ) := by
  sorry

theorem pm_colPerm (σ : Equiv.Perm (Fin 5)) (u : Fin 5 × Fin 5 → ℂ) :
    pm (fun x => u (x.1, σ x.2)) = pm u := by
  sorry

theorem lev_colPerm (σ : Equiv.Perm (Fin 5)) (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (hL : Lev 5 L) :
    Lev 5 (L.map (colPerm σ)) := by
  sorry

theorem finrank_colPerm (σ : Equiv.Perm (Fin 5)) (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) :
    Module.finrank ℂ (L.map (colPerm σ)) = Module.finrank ℂ L := by
  sorry

theorem rowsZeroS_colPerm (σ : Equiv.Perm (Fin 5)) (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (S : Finset (Fin 5)) :
    rowsZeroS (L.map (colPerm σ)) S = (rowsZeroS L S).map (colPerm σ) := by
  sorry

theorem dotL_comp (σ : Equiv.Perm (Fin 5)) (κ v : Fin 5 → ℂ) :
    dotL (fun m => κ (σ m)) (fun m => v (σ m)) = dotL κ v := by
  sorry

theorem rowMap_colPerm (σ : Equiv.Perm (Fin 5)) (r : Fin 5) (t : Fin 5 × Fin 5 → ℂ) :
    rowMap r (colPerm σ t) = fun m => rowMap r t (σ m) := by
  sorry

theorem typeCl_perm (σ : Equiv.Perm (Fin 5)) (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5)
    (h : TypeCl κ κ' ν ν' a b) :
    TypeCl (fun m => κ (σ m)) (fun m => κ' (σ m)) (fun m => ν (σ m)) (fun m => ν' (σ m))
      (σ⁻¹ a) (σ⁻¹ b) := by
  sorry

def PIIBody (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r r' : Fin 5) (κ κ' ν ν' : Fin 5 → ℂ)
    (a b : Fin 5) : Prop :=
  (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
    (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧
    (∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0) ∧
    dotL ν 1 + dotL ν' 1 = 0 ∧ (∀ j, κ j ≠ 0) ∧ (∀ j, κ' j ≠ 0) ∧ TypeCl κ κ' ν ν' a b ∧
    ∃ m, ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b

theorem pairII_iff (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r r' : Fin 5) :
    PairII L r r' ↔ ∃ κ κ' ν ν' : Fin 5 → ℂ, ∃ a b : Fin 5, PIIBody L r r' κ κ' ν ν' a b := by
  sorry

theorem piiBody_perm {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (σ : Equiv.Perm (Fin 5)) (r r' : Fin 5)
    (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (h : PIIBody L r r' κ κ' ν ν' a b) :
    PIIBody (L.map (colPerm σ)) r r' (fun m => κ (σ m)) (fun m => κ' (σ m)) (fun m => ν (σ m))
      (fun m => ν' (σ m)) (σ⁻¹ a) (σ⁻¹ b) := by
  sorry

theorem pairII_perm {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (σ : Equiv.Perm (Fin 5)) (r r' : Fin 5)
    (h : PairII L r r') : PairII (L.map (colPerm σ)) r r' := by
  sorry

theorem pairI_perm {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (σ : Equiv.Perm (Fin 5)) (r r' : Fin 5)
    (h : PairI L r r') : PairI (L.map (colPerm σ)) r r' := by
  sorry

noncomputable def vecPerm (σ : Equiv.Perm (Fin 5)) : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun v := fun m => v (σ m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vecPerm_injective (σ : Equiv.Perm (Fin 5)) : Function.Injective (vecPerm σ) := by
  sorry

theorem zf_perm {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (σ : Equiv.Perm (Fin 5)) (r : Fin 5)
    (h : ZF L r) : ZF (L.map (colPerm σ)) r := by
  sorry

theorem exists_sort_perm (f : Fin 5 → Fin 3) : ∃ σ : Equiv.Perm (Fin 5), Monotone (f ∘ σ) := by
  sorry

theorem single_row_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (j : Fin 5) (κc : Fin 5 → ℂ)
    (hκc : ∀ t ∈ L, dotL κc (colMap j t) = 0) (hκc0 : ∀ i, κc i ≠ 0)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) (a : Fin 5) (hrow : ∀ i, i ≠ a → ∀ m, t (i, m) = 0) :
    t (a, j) = 0 := by
  sorry

theorem no_single_row {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (κc : Fin 5 → Fin 5 → ℂ)
    (hκc : ∀ j, ∀ t ∈ L, dotL (κc j) (colMap j t) = 0) (hκc0 : ∀ j i, κc j i ≠ 0)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) (a : Fin 5) (hrow : ∀ i, i ≠ a → ∀ m, t (i, m) = 0) :
    t = 0 := by
  sorry

theorem fk_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c : Fin 5) :
    ∃ κ : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (colMap c t) = 0) ∧ dotL κ 1 = 1 := by
  sorry

theorem gen_col_ann {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (hc : ∀ c, ZFc L c) :
    ∃ κc : Fin 5 → Fin 5 → ℂ, (∀ j, ∀ t ∈ L, dotL (κc j) (colMap j t) = 0) ∧
      (∀ j, dotL (κc j) 1 = 1) ∧ ∀ j i, κc j i ≠ 0 := by
  sorry

theorem gen_no_single_row {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (hc : ∀ c, ZFc L c)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ L) (a : Fin 5) (hrow : ∀ i, i ≠ a → ∀ m, t (i, m) = 0) :
    t = 0 := by
  sorry

theorem dep3_of_finrank2 {X : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (h : Module.finrank ℂ X = 2)
    (x y z : Fin 5 × Fin 5 → ℂ) (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) :
    ∃ a b c : ℂ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ a • x + b • y + c • z = 0 := by
  sorry

theorem col3 (κ x : Fin 5 → ℂ) (i3 i4 i5 : Fin 5) (h34 : i3 ≠ i4) (h35 : i3 ≠ i5) (h45 : i4 ≠ i5)
    (hoff : ∀ i, i ≠ i3 → i ≠ i4 → i ≠ i5 → x i = 0) (h : dotL κ x = 0) :
    κ i3 * x i3 + κ i4 * x i4 + κ i5 * x i5 = 0 := by
  sorry

theorem gen_tri_param {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (κc : Fin 5 → Fin 5 → ℂ)
    (hκc : ∀ j, ∀ t ∈ L, dotL (κc j) (colMap j t) = 0) (hκc0 : ∀ j i, κc j i ≠ 0)
    (r1 r2 i3 i4 i5 : Fin 5) (hcov : ∀ i, i = r1 ∨ i = r2 ∨ i = i3 ∨ i = i4 ∨ i = i5)
    (h34 : i3 ≠ i4) (h35 : i3 ≠ i5) (h45 : i4 ≠ i5)
    (h2 : Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2)
    (x3 x4 x5 : Fin 5 × Fin 5 → ℂ) (m3 : x3 ∈ rowsZeroS L {r1, r2})
    (m4 : x4 ∈ rowsZeroS L {r1, r2}) (m5 : x5 ∈ rowsZeroS L {r1, r2})
    (n3 : x3 ≠ 0) (n4 : x4 ≠ 0) (n5 : x5 ≠ 0)
    (z3 : ∀ j, x3 (i3, j) = 0) (z4 : ∀ j, x4 (i4, j) = 0) (z5 : ∀ j, x5 (i5, j) = 0) :
    ∀ x ∈ rowsZeroS L {r1, r2}, ∃ c3 c4 c5 : ℂ, c3 + c4 + c5 = 0 ∧ ∀ j,
      κc j i3 * x (i3, j) = c3 * (κc j i4 * x3 (i4, j)) ∧
      κc j i4 * x (i4, j) = c4 * (κc j i4 * x3 (i4, j)) ∧
      κc j i5 * x (i5, j) = c5 * (κc j i4 * x3 (i4, j)) := by
  sorry

def R31Canon : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3 →
    ∀ κ κ' ν ν' : Fin 5 → ℂ, ∀ a b : Fin 5, PIIBody L r1 r2 κ κ' ν ν' a b →
    ∀ f : Fin 5 → Fin 3, (∀ m, f m = 1 ↔ ν' m / κ' m = ν' a / κ' a) →
    (∀ m, f m = 2 ↔ ν m / κ m = ν b / κ b) → Monotone f → PairII L r1 r3 →
    rowsZeroS L {r1, r2, r3} ≠ ⊥

theorem typeCl_disj (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (h : TypeCl κ κ' ν ν' a b) (m : Fin 5)
    (h1 : ν' m / κ' m = ν' a / κ' a) : ¬ (ν m / κ m = ν b / κ b) := by
  sorry

theorem cls_exists (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (h : TypeCl κ κ' ν ν' a b) :
    ∃ f : Fin 5 → Fin 3, (∀ m, f m = 1 ↔ ν' m / κ' m = ν' a / κ' a) ∧
      (∀ m, f m = 2 ↔ ν m / κ m = ν b / κ b) := by
  sorry

theorem r31_of_canon (hC : R31Canon) : R31Hyp := by
  sorry

theorem three_factor_gen {V W : Type} [Add V] [SMul ℂ V] (dot : W → V → ℂ)
    (hdot : ∀ l x y (s : ℂ), dot l (x + s • y) = dot l x + s * dot l y)
    (l1 l2 l3 n : W)
    (h : ∀ x, dot n x = 0 → dot l1 x * dot l2 x * dot l3 x = 0) :
    (∀ x, dot n x = 0 → dot l1 x = 0) ∨ (∀ x, dot n x = 0 → dot l2 x = 0) ∨
      (∀ x, dot n x = 0 → dot l3 x = 0) := by
  sorry

noncomputable def dot4 (l x : Fin 4 → ℂ) : ℂ := ∑ e, l e * x e

theorem dot4_add (l x y : Fin 4 → ℂ) (s : ℂ) : dot4 l (x + s • y) = dot4 l x + s * dot4 l y := by
  sorry

theorem lin_minor (l z : Fin 4 → ℂ) (h : ∀ x, dot4 z x = 0 → dot4 l x = 0) (a b : Fin 4) :
    l a * z b - l b * z a = 0 := by
  sorry

theorem cub3_cases (z : Fin 4 → ℂ) (c : (Fin 4 → ℂ) → ℂ) (l1 l2 l3 : Fin 4 → ℂ) (k : ℂ) (hk : k ≠ 0)
    (hid : ∀ x, c x = k * (dot4 l1 x * dot4 l2 x * dot4 l3 x))
    (h : ∀ x, dot4 z x = 0 → c x = 0) :
    (∀ a b, l1 a * z b - l1 b * z a = 0) ∨ (∀ a b, l2 a * z b - l2 b * z a = 0) ∨
      (∀ a b, l3 a * z b - l3 b * z a = 0) := by
  sorry

theorem sum3_idx (f : Fin 3 → ℂ) (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ m, f m = f a + f b + f c := by
  sorry

theorem cubic_no_plane_idx (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → Fin 3 → (Fin 3 → ℂ) → ℂ)
    (hcert : ∀ (x : Fin 3 → ℂ) (k : Fin 3), x k ^ 4 = ∑ i, Q k i x * gradT T x i)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w1 w2 : Fin 3 → ℂ) (hdet : w1 a * w2 b - w1 b * w2 a ≠ 0)
    (hvan : ∀ s t : ℂ, cubT T (s • w1 + t • w2) = 0) : False := by
  sorry

theorem sec_no_kernel (z : Fin 4 → ℂ) (cf : (Fin 4 → ℂ) → ℂ) (b0 b1 b2 : Fin 4 → ℂ)
    (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → Fin 3 → (Fin 3 → ℂ) → ℂ)
    (hcert : ∀ (x : Fin 3 → ℂ) (k : Fin 3), x k ^ 4 = ∑ i, Q k i x * gradT T x i)
    (hs : ∀ y : Fin 3 → ℂ, cf (fun e => y 0 * b0 e + y 1 * b1 e + y 2 * b2 e) = cubT T y)
    (hv : ∀ x, dot4 z x = 0 → cf x = 0) : False := by
  sorry

theorem cub0_zero (z : Fin 4 → ℂ) (cf : (Fin 4 → ℂ) → ℂ) (b0 b1 b2 : Fin 4 → ℂ)
    (T : Fin 3 → Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → Fin 3 → (Fin 3 → ℂ) → ℂ)
    (hcert : ∀ (x : Fin 3 → ℂ) (k : Fin 3), x k ^ 4 = ∑ i, Q k i x * gradT T x i)
    (hs : ∀ y : Fin 3 → ℂ, cf (fun e => y 0 * b0 e + y 1 * b1 e + y 2 * b2 e) = cubT T y)
    (h : z ≠ 0 → ∀ x, dot4 z x = 0 → cf x = 0) : z = 0 := by
  sorry

theorem qsec_one (z : Fin 4 → ℂ) (q : (Fin 4 → ℂ) → ℂ) (k0 k1 k2 : Fin 4 → ℂ) (Q N : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N i k * gradQ Q x k)
    (hs : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k1 e + y 2 * k2 e) = quadQ Q y)
    (h2 : dot4 z k2 ≠ 0 ∨ (dot4 z k0 = 0 ∧ dot4 z k1 = 0 ∧ dot4 z k2 = 0))
    (hv : ∀ x, dot4 z x = 0 → q x = 0) : False := by
  sorry

theorem qsec_no_kernel (z : Fin 4 → ℂ) (q : (Fin 4 → ℂ) → ℂ) (k0 k1 k2 : Fin 4 → ℂ)
    (Q Q' Q'' N N' N'' : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N i k * gradQ Q x k)
    (hN' : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N' i k * gradQ Q' x k)
    (hN'' : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N'' i k * gradQ Q'' x k)
    (hs : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k1 e + y 2 * k2 e) = quadQ Q y)
    (hs' : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k2 e + y 2 * k1 e) = quadQ Q' y)
    (hs'' : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k2 e + y 1 * k1 e + y 2 * k0 e) = quadQ Q'' y)
    (hv : ∀ x, dot4 z x = 0 → q x = 0) : False := by
  sorry

theorem cub1_cases (z l : Fin 4 → ℂ) (cf q : (Fin 4 → ℂ) → ℂ)
    (hid : ∀ x, cf x = dot4 l x * q x) (Bq : (Fin 4 → ℂ) → (Fin 4 → ℂ) → ℂ)
    (hq : ∀ x y (s : ℂ), q (x + s • y) = q x + s * Bq x y + s ^ 2 * q y)
    (k0 k1 k2 : Fin 4 → ℂ) (Q Q' Q'' N N' N'' : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N i k * gradQ Q x k)
    (hN' : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N' i k * gradQ Q' x k)
    (hN'' : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N'' i k * gradQ Q'' x k)
    (hs : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k1 e + y 2 * k2 e) = quadQ Q y)
    (hs' : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k2 e + y 2 * k1 e) = quadQ Q' y)
    (hs'' : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k2 e + y 1 * k1 e + y 2 * k0 e) = quadQ Q'' y)
    (h : z ≠ 0 → ∀ x, dot4 z x = 0 → cf x = 0) :
    z = 0 ∨ (∀ a b, l a * z b - l b * z a = 0) := by
  sorry

theorem perm3_scale (A B : Matrix (Fin 3) (Fin 3) ℂ) (r c : Fin 3 → ℂ)
    (h : ∀ i k, A i k = r i * c k * B i k) :
    A.permanent = (r 0 * r 1 * r 2) * (c 0 * c 1 * c 2) * B.permanent := by
  sorry

noncomputable def Emap4 (EE : Fin 4 → Fin 3 → Fin 3 → ℂ) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → Fin 3 → ℂ) where
  toFun x := fun i k => ∑ e, x e * EE e i k
  map_add' x y := by
    funext i k
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    funext i k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring

noncomputable def dotMap4 (z : Fin 4 → ℂ) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun x := dot4 z x
  map_add' x y := by
    simp only [dot4, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [dot4, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring

theorem finrank_ker_dot4 (z : Fin 4 → ℂ) (hz : z ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (dotMap4 z)) ≤ 3 := by
  sorry

theorem h0_of_X123 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (r1 r2 r3 : Fin 5) (hr1 : rr (Sum.inl 0) = r1) (hr2 : rr (Sum.inl 1) = r2)
    (hr3 : rr (Sum.inl 2) = r3) (hX : rowsZeroS L {r1, r2, r3} = ⊥) :
    ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0 := by
  sorry

theorem bridge {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (EE PP : Fin 4 → Fin 3 → Fin 3 → ℂ) (z : Fin 4 → ℂ)
    (hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap κs rr cc t i k =
      ∑ e, (∑ i', ∑ k', PP e i' k' * tauMap κs rr cc t i' k') * EE e i k)
    (hzk : ∀ t ∈ blkL L rr cc,
      ∑ e, z e * (∑ i', ∑ k', PP e i' k' * tauMap κs rr cc t i' k') = 0)
    (UU : Fin 3 → Fin 3 → ℂ) (cr : Fin 3 → ℂ)
    (hU : ∀ i k, κs i (cc (Sum.inl k)) * UU i k = cr i * κs 0 (cc (Sum.inl k))) :
    z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * EE e i k) * UU i k).permanent = 0 := by
  sorry

theorem cub3c (z : Fin 4 → ℂ) (c : (Fin 4 → ℂ) → ℂ) (l1 l2 l3 : Fin 4 → ℂ)
    (hid : ∀ x, c x = dot4 l1 x * dot4 l2 x * dot4 l3 x)
    (h : z ≠ 0 → ∀ x, dot4 z x = 0 → c x = 0) :
    (∀ a b, l1 a * z b - l1 b * z a = 0) ∨ (∀ a b, l2 a * z b - l2 b * z a = 0) ∨
      (∀ a b, l3 a * z b - l3 b * z a = 0) := by
  sorry

theorem tau_blk_zero {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ blkL L rr cc) (i : Fin 3) (b : Fin 2) (r m : Fin 5)
    (hr : rr (Sum.inl i) = r) (hm : cc (Sum.inr b) = m) : t (r, m) = 0 := by
  sorry

theorem compl_inr (cc : Fin 3 ⊕ Fin 2 ≃ Fin 5) (p q s : Fin 5) (hp : cc (Sum.inl 0) = p)
    (hq : cc (Sum.inl 1) = q) (hs : cc (Sum.inl 2) = s) (u : Fin 5)
    (hu : u ≠ p ∧ u ≠ q ∧ u ≠ s) : ∃ b, cc (Sum.inr b) = u := by
  sorry

theorem fin5_cases (a : Fin 5) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
  sorry

theorem typeII_weights (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (hκ0 : ∀ m, κ m ≠ 0)
    (hκ'0 : ∀ m, κ' m ≠ 0) (hcl : TypeCl κ κ' ν ν' a b) (m0 : Fin 5)
    (hm0 : ν m0 / κ m0 = ν a / κ a ∧ ν' m0 / κ' m0 = ν' b / κ' b) (f : Fin 5 → Fin 3)
    (hf1 : ∀ m, f m = 1 ↔ ν' m / κ' m = ν' a / κ' a) (hf2 : ∀ m, f m = 2 ↔ ν m / κ m = ν b / κ b) :
    ∃ c j : ℂ, c ≠ 0 ∧ j * j = -1 ∧ (∀ m, f m = 1 → κ' m = 1 * (c * κ m)) ∧
      (∀ m, f m = 2 → κ' m = -1 * (c * κ m)) ∧ (∀ m, f m = 0 → κ' m = j * (c * κ m)) := by
  sorry

theorem jsq_sign {j j' : ℂ} (hj : j * j = -1) (hj' : j' * j' = -1) : j' = j ∨ j' = -j := by
  sorry

noncomputable def pairDual (p q : Fin 5 → ℂ) : Module.Dual ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)) where
  toFun w := ∑ m, (p m * w.1 m + q m * w.2 m)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring

theorem pairDual_apply (p q : Fin 5 → ℂ) (w : (Fin 5 → ℂ) × (Fin 5 → ℂ)) :
    pairDual p q w = ∑ m, (p m * w.1 m + q m * w.2 m) := by
  sorry

theorem pairDual_single1 (p q : Fin 5 → ℂ) (m : Fin 5) :
    pairDual p q (Pi.single m 1, 0) = p m := by
  sorry

theorem pairDual_single2 (p q : Fin 5 → ℂ) (m : Fin 5) :
    pairDual p q (0, Pi.single m 1) = q m := by
  sorry

theorem ann2_dep {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (h9 : Module.finrank ℂ L = 9)
    (r r' : Fin 5) (hx : Module.finrank ℂ (rowsZeroS L {r, r'}) = 2)
    (P Q : Fin 4 → Fin 5 → ℂ)
    (hPQ : ∀ i, ∀ t ∈ L, ∑ m, (P i m * t (r, m) + Q i m * t (r', m)) = 0) :
    ∃ g : Fin 4 → ℂ, (∃ i, g i ≠ 0) ∧ ∀ m, ∑ i, g i * P i m = 0 ∧ ∑ i, g i * Q i m = 0 := by
  sorry

theorem fin4_cases (a : Fin 4) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  sorry

theorem dual_eq_pairDual (φ : Module.Dual ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)))
    (w : (Fin 5 → ℂ) × (Fin 5 → ℂ)) :
    φ w = ∑ m, (φ (Pi.single m 1, 0) * w.1 m + φ (0, Pi.single m 1) * w.2 m) := by
  sorry

theorem e3_final (κ2 κ3 dQ12 dQ13 : Fin 5 → ℂ) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (φ : Module.Dual ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ))) (hφ1 : φ (1, 1) = 0) (b c α sg : ℂ)
    (hp : ∀ m, φ (Pi.single m 1, 0) = (b + c * dQ12 m) * κ2 m)
    (hq : ∀ m, φ (0, Pi.single m 1) = (α + sg * c * dQ13 m) * κ3 m) :
    φ ∈ Submodule.span ℂ {pairDual κ2 (fun m => -κ3 m), pairDual (fun m => dQ12 m * κ2 m) (fun m => sg * dQ13 m * κ3 m - (∑ m, dQ12 m * κ2 m + sg * ∑ m, dQ13 m * κ3 m) * κ3 m)} := by
  sorry

theorem e3_a {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5)
    (hx12 : Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2)
    (κ1 κ2 κ3 : Fin 5 → ℂ) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hκ1 : ∀ m, κ1 m ≠ 0) (hκ2 : ∀ m, κ2 m ≠ 0)
    (hF1 : ∀ t ∈ L, ∑ m, κ1 m * t (r1, m) = 0) (hF2 : ∀ t ∈ L, ∑ m, κ2 m * t (r2, m) = 0)
    (hF3 : ∀ t ∈ L, ∑ m, κ3 m * t (r3, m) = 0)
    (dB12 dQ12 dB13 dQ13 : Fin 5 → ℂ)
    (hG12 : ∀ t ∈ L, ∑ m, (dB12 m * κ1 m * t (r1, m) + dQ12 m * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, (dB13 m * κ1 m * t (r1, m) + dQ13 m * κ3 m * t (r3, m)) = 0)
    (mB mNB mQ mNQ : Fin 5) (h1 : dB12 mB = 1) (h2 : dB12 mNB = 0) (h3 : dQ12 mQ = 1)
    (h4 : dQ12 mNQ = 0) (sg : ℂ)
    (hsg : (sg = -1 ∧ ∀ m, dB13 m = dB12 m) ∨ (sg = 1 ∧ ∀ m, dB13 m = 1 - dB12 m))
    (φ : Module.Dual ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)))
    (hφL : ∀ t ∈ L, φ (rowMap r2 t, rowMap r3 t) = 0) (hφ1 : φ (1, 1) = 0)
    (hφs : φ ∉ Submodule.span ℂ {pairDual κ2 (fun m => -κ3 m), pairDual (fun m => dQ12 m * κ2 m) (fun m => sg * dQ13 m * κ3 m - (∑ m, dQ12 m * κ2 m + sg * ∑ m, dQ13 m * κ3 m) * κ3 m)}) :
    ¬ ∃ α β : ℂ, ∀ m, φ (0, Pi.single m 1) = (α + β * dQ13 m) * κ3 m := by
  sorry

theorem e3_b {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5)
    (hx13 : Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2)
    (κ1 κ2 κ3 : Fin 5 → ℂ) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hκ1 : ∀ m, κ1 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0)
    (hF1 : ∀ t ∈ L, ∑ m, κ1 m * t (r1, m) = 0) (hF2 : ∀ t ∈ L, ∑ m, κ2 m * t (r2, m) = 0)
    (hF3 : ∀ t ∈ L, ∑ m, κ3 m * t (r3, m) = 0)
    (dB12 dQ12 dB13 dQ13 : Fin 5 → ℂ)
    (hG12 : ∀ t ∈ L, ∑ m, (dB12 m * κ1 m * t (r1, m) + dQ12 m * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, (dB13 m * κ1 m * t (r1, m) + dQ13 m * κ3 m * t (r3, m)) = 0)
    (mB mNB mNB3 mQ3 mNQ3 : Fin 5) (h1 : dB12 mB = 1) (h2 : dB12 mNB = 0) (h5 : dB13 mNB3 = 0)
    (h3 : dQ13 mQ3 = 1) (h4 : dQ13 mNQ3 = 0) (sg : ℂ)
    (hsg : (sg = -1 ∧ ∀ m, dB13 m = dB12 m) ∨ (sg = 1 ∧ ∀ m, dB13 m = 1 - dB12 m))
    (φ : Module.Dual ℂ ((Fin 5 → ℂ) × (Fin 5 → ℂ)))
    (hφL : ∀ t ∈ L, φ (rowMap r2 t, rowMap r3 t) = 0) (hφ1 : φ (1, 1) = 0)
    (hφs : φ ∉ Submodule.span ℂ {pairDual κ2 (fun m => -κ3 m), pairDual (fun m => dQ12 m * κ2 m) (fun m => sg * dQ13 m * κ3 m - (∑ m, dQ12 m * κ2 m + sg * ∑ m, dQ13 m * κ3 m) * κ3 m)}) :
    ¬ ∃ b c : ℂ, ∀ m, φ (Pi.single m 1, 0) = (b + c * dQ12 m) * κ2 m := by
  sorry

noncomputable def rhoMap (ρ : Fin 3 → Fin 2 → ℂ) : (Fin 3 × Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ p : Fin 3 × Fin 2, ρ p.1 p.2 * v p
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring

theorem finrank_ker_rho (ρ : Fin 3 → Fin 2 → ℂ) (a0 : Fin 3) (b0 : Fin 2) (hρ : ρ a0 b0 ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (rhoMap ρ)) ≤ 5 := by
  sorry

theorem blk_finrank_rel {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (ρ : Fin 3 → Fin 2 → ℂ) (a0 : Fin 3) (b0 : Fin 2) (hρ : ρ a0 b0 ≠ 0)
    (hrel : ∀ t ∈ L, ∑ a, ∑ b, ρ a b * t (rr (Sum.inl a), cc (Sum.inr b)) = 0) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (blkL L rr cc) + 5 := by
  sorry

theorem blockSpace_finrank_rel {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (ρ : Fin 3 → Fin 2 → ℂ) (a0 : Fin 3) (b0 : Fin 2) (hρ : ρ a0 b0 ≠ 0)
    (hrel : ∀ t ∈ L, ∑ a, ∑ b, ρ a b * t (rr (Sum.inl a), cc (Sum.inr b)) = 0)
    (hJ : ∑ a, ∑ b, ρ a b = 0) :
    Module.finrank ℂ L + 1 ≤ Module.finrank ℂ (blockSpace L rr cc) + 5 := by
  sorry

theorem ell_ne_gen {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) (m : ℕ)
    (hs : Module.finrank ℂ (blkL L r c) ≤ m)
    (hge : m + 1 ≤ Module.finrank ℂ (blockSpace L r c)) :
    ∃ w ∈ blockSpace L r c, w.1 ≠ 0 := by
  sorry

theorem stest_vanish_gen {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (H : Submodule ℂ (Fin 3 → Fin 3 → ℂ)) (m : ℕ) (hH : Module.finrank ℂ H ≤ m)
    (hb : m ≤ Module.finrank ℂ (blkL L rr cc))
    (hw : ∃ w ∈ blockSpace L rr cc, w.1 ≠ 0)
    (himg : ∀ t ∈ blkL L rr cc, tauMap κs rr cc t ∈ H) :
    ∀ τ ∈ H, (Matrix.of fun i j => τ i j / κs i (cc (Sum.inl j))).permanent = 0 := by
  sorry

theorem fk_sum (κ : Fin 5 → ℂ) (r : Fin 5) (t : Fin 5 × Fin 5 → ℂ) :
    dotL κ (rowMap r t) = ∑ m, κ m * t (r, m) := by
  sorry

theorem dot_one_sum (κ : Fin 5 → ℂ) : dotL κ 1 = ∑ m, κ m := by
  sorry

theorem typeII_two_values (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (h : TypeCl κ κ' ν ν' a b) (m : Fin 5) :
    ν m / κ m = ν a / κ a ∨ ν m / κ m = ν b / κ b := by
  sorry

theorem ind_sum (f : Fin 5 → Fin 3) (v : Fin 3) (g : Fin 5 → ℂ) :
    ∑ m ∈ Finset.univ.filter (fun m => f m = v), g m = ∑ m, (if f m = v then (1 : ℂ) else 0) * g m := by
  sorry

theorem typeII_ind {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (κ κ' ν ν' : Fin 5 → ℂ)
    (a b : Fin 5) (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0)
    (hκ'L : ∀ t ∈ L, dotL κ' (rowMap r' t) = 0)
    (hνL : ∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0)
    (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0) (hcl : TypeCl κ κ' ν ν' a b)
    (f : Fin 5 → Fin 3) (hf1 : ∀ m, f m = 1 ↔ ν' m / κ' m = ν' a / κ' a)
    (hf2 : ∀ m, f m = 2 ↔ ν m / κ m = ν b / κ b) :
    ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ m * t (r, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ' m * t (r', m)) = 0 := by
  sorry

theorem e1_of_split (κ κ' ν ν' κ3 μ μ3 : Fin 5 → ℂ) (a b a' b' : Fin 5)
    (hcl : TypeCl κ κ' ν ν' a b) (hcl3 : TypeCl κ κ3 μ μ3 a' b')
    (f f13 : Fin 5 → Fin 3) (hf2 : ∀ m, f m = 2 ↔ ν m / κ m = ν b / κ b)
    (hg2 : ∀ m, f13 m = 2 ↔ μ m / κ m = μ b' / κ b')
    (hsplit : ∀ m m', ν m / κ m = ν m' / κ m' ↔ μ m / κ m = μ m' / κ m') :
    (∀ m, f13 m = 2 ↔ f m = 2) ∨ (∀ m, f13 m = 2 ↔ ¬ f m = 2) := by
  sorry

theorem fin3_zero_of {x : Fin 3} (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  sorry

theorem typeII_K (κ κ' ν ν' : Fin 5 → ℂ) (a b m0 : Fin 5) (hκ0 : ∀ m, κ m ≠ 0)
    (hκ'0 : ∀ m, κ' m ≠ 0) (hcl : TypeCl κ κ' ν ν' a b) (hκ1 : dotL κ 1 = 1) (hκ'1 : dotL κ' 1 = 1)
    (hν1 : dotL ν 1 + dotL ν' 1 = 0)
    (hm0 : ν m0 / κ m0 = ν a / κ a ∧ ν' m0 / κ' m0 = ν' b / κ' b) (f : Fin 5 → Fin 3)
    (hf1 : ∀ m, f m = 1 ↔ ν' m / κ' m = ν' a / κ' a) (hf2 : ∀ m, f m = 2 ↔ ν m / κ m = ν b / κ b)
    (c j : ℂ) (hc : c ≠ 0) (hQ : ∀ m, f m = 1 → κ' m = 1 * (c * κ m))
    (hC : ∀ m, f m = 0 → κ' m = j * (c * κ m)) (fm0 : f m0 = 0) :
    (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ m + (if f m = 1 then (1 : ℂ) else 0) * κ' m)) *
      (1 + j) = 1 := by
  sorry

theorem r31_setup {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (z1 : ZF L r1)
    (d12 : Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2)
    (d13 : Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2)
    (d23 : Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥)
    (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (hb : PIIBody L r1 r2 κ κ' ν ν' a b)
    (f : Fin 5 → Fin 3) (hf1 : ∀ m, f m = 1 ↔ ν' m / κ' m = ν' a / κ' a)
    (hf2 : ∀ m, f m = 2 ↔ ν m / κ m = ν b / κ b) (hP13 : PairII L r1 r3) :
    ∃ (κ3 : Fin 5 → ℂ) (f13 : Fin 5 → Fin 3) (c2 c3 j s : ℂ) (M2 M3 : Fin 5 → ℂ),
      (∀ m, κ3 m ≠ 0) ∧ (∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) ∧ j * j = -1 ∧ (s = 1 ∨ s = -1) ∧
      (∀ m, (f m = 1 → κ' m = 1 * (c2 * κ m)) ∧ (f m = 2 → κ' m = -1 * (c2 * κ m)) ∧
        (f m = 0 → κ' m = j * (c2 * κ m))) ∧
      (∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ m)) ∧
        (f13 m = 0 → κ3 m = s * j * (c3 * κ m))) ∧
      (∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ m * t (r1, m) +
        (if f m = 1 then (1 : ℂ) else 0) * κ' m * t (r2, m)) = 0) ∧
      (∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ m * t (r1, m) +
        (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0) ∧
      ((∀ m, f13 m = 2 ↔ f m = 2) ∨ (∀ m, f13 m = 2 ↔ ¬ f m = 2)) ∧
      (∀ t ∈ L, ∑ m, (M2 m * κ' m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0) ∧
      (¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0)) ∧
      (¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0)) ∧
      (∃ m, f13 m = 0) ∧ (∃ m, f13 m = 1) ∧ (∃ m, f13 m = 2) ∧
      (∑ m, κ m = 1) ∧ (∑ m, κ' m = 1) ∧ (∑ m, κ3 m = 1) ∧
      (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ m + (if f m = 1 then (1 : ℂ) else 0) * κ' m)) *
        (1 + j) = 1 ∧
      (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) *
        (1 + s * j) = 1 ∧
      ∑ m, (M2 m * κ' m + M3 m * κ3 m) = 0 := by
  sorry

theorem canon_vec (v0 v1 v2 v3 v4 : Fin 3) (h01 : v0 ≤ v1) (h12 : v1 ≤ v2) (h23 : v2 ≤ v3) (h34 : v3 ≤ v4)
    (h0 : v0 = 0) (h4 : v4 = 2) (hm : v1 = 1 ∨ v2 = 1 ∨ v3 = 1) :
    (v1 = 0 ∧ v2 = 0 ∧ v3 = 1) ∨ (v1 = 0 ∧ v2 = 1 ∧ v3 = 1) ∨ (v1 = 1 ∧ v2 = 1 ∧ v3 = 1) ∨
      (v1 = 0 ∧ v2 = 1 ∧ v3 = 2) ∨ (v1 = 1 ∧ v2 = 1 ∧ v3 = 2) ∨ (v1 = 1 ∧ v2 = 2 ∧ v3 = 2) := by
  sorry

theorem canon_patterns (f : Fin 5 → Fin 3) (hmono : Monotone f) (h0 : ∃ m, f m = 0)
    (h1 : ∃ m, f m = 1) (h2 : ∃ m, f m = 2) :
    f 0 = 0 ∧ f 4 = 2 ∧
    ((f 1 = 0 ∧ f 2 = 0 ∧ f 3 = 1) ∨ (f 1 = 0 ∧ f 2 = 1 ∧ f 3 = 1) ∨ (f 1 = 1 ∧ f 2 = 1 ∧ f 3 = 1) ∨
      (f 1 = 0 ∧ f 2 = 1 ∧ f 3 = 2) ∨ (f 1 = 1 ∧ f 2 = 1 ∧ f 3 = 2) ∨ (f 1 = 1 ∧ f 2 = 2 ∧ f 3 = 2)) := by
  sorry

theorem f13_cases_00012 (w0 w1 w2 w3 w4 : Fin 3)
    (hE1 : ((w0 = 2 ↔ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ (0 : Fin 3) = 2) ∧ (w2 = 2 ↔ (0 : Fin 3) = 2) ∧ (w3 = 2 ↔ (1 : Fin 3) = 2) ∧ (w4 = 2 ↔ (2 : Fin 3) = 2)) ∨
      ((w0 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w2 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w3 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w4 = 2 ↔ ¬ (2 : Fin 3) = 2)))
    (h0 : (w0 = 0 ∨ w1 = 0 ∨ w2 = 0 ∨ w3 = 0 ∨ w4 = 0)) (h1 : (w0 = 1 ∨ w1 = 1 ∨ w2 = 1 ∨ w3 = 1 ∨ w4 = 1)) (h2 : (w0 = 2 ∨ w1 = 2 ∨ w2 = 2 ∨ w3 = 2 ∨ w4 = 2)) :
    (w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) := by
  sorry

theorem f13_cases_00112 (w0 w1 w2 w3 w4 : Fin 3)
    (hE1 : ((w0 = 2 ↔ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ (0 : Fin 3) = 2) ∧ (w2 = 2 ↔ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ (1 : Fin 3) = 2) ∧ (w4 = 2 ↔ (2 : Fin 3) = 2)) ∨
      ((w0 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w2 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w4 = 2 ↔ ¬ (2 : Fin 3) = 2)))
    (h0 : (w0 = 0 ∨ w1 = 0 ∨ w2 = 0 ∨ w3 = 0 ∨ w4 = 0)) (h1 : (w0 = 1 ∨ w1 = 1 ∨ w2 = 1 ∨ w3 = 1 ∨ w4 = 1)) (h2 : (w0 = 2 ∨ w1 = 2 ∨ w2 = 2 ∨ w3 = 2 ∨ w4 = 2)) :
    (w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) := by
  sorry

theorem f13_cases_01112 (w0 w1 w2 w3 w4 : Fin 3)
    (hE1 : ((w0 = 2 ↔ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ (1 : Fin 3) = 2) ∧ (w2 = 2 ↔ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ (1 : Fin 3) = 2) ∧ (w4 = 2 ↔ (2 : Fin 3) = 2)) ∨
      ((w0 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w2 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w4 = 2 ↔ ¬ (2 : Fin 3) = 2)))
    (h0 : (w0 = 0 ∨ w1 = 0 ∨ w2 = 0 ∨ w3 = 0 ∨ w4 = 0)) (h1 : (w0 = 1 ∨ w1 = 1 ∨ w2 = 1 ∨ w3 = 1 ∨ w4 = 1)) (h2 : (w0 = 2 ∨ w1 = 2 ∨ w2 = 2 ∨ w3 = 2 ∨ w4 = 2)) :
    (w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 2) := by
  sorry

theorem f13_cases_00122 (w0 w1 w2 w3 w4 : Fin 3)
    (hE1 : ((w0 = 2 ↔ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ (0 : Fin 3) = 2) ∧ (w2 = 2 ↔ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ (2 : Fin 3) = 2) ∧ (w4 = 2 ↔ (2 : Fin 3) = 2)) ∨
      ((w0 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w2 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ ¬ (2 : Fin 3) = 2) ∧ (w4 = 2 ↔ ¬ (2 : Fin 3) = 2)))
    (h0 : (w0 = 0 ∨ w1 = 0 ∨ w2 = 0 ∨ w3 = 0 ∨ w4 = 0)) (h1 : (w0 = 1 ∨ w1 = 1 ∨ w2 = 1 ∨ w3 = 1 ∨ w4 = 1)) (h2 : (w0 = 2 ∨ w1 = 2 ∨ w2 = 2 ∨ w3 = 2 ∨ w4 = 2)) :
    (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 2 ∧ w3 = 0 ∧ w4 = 1) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 2 ∧ w3 = 1 ∧ w4 = 0) := by
  sorry

theorem f13_cases_01122 (w0 w1 w2 w3 w4 : Fin 3)
    (hE1 : ((w0 = 2 ↔ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ (1 : Fin 3) = 2) ∧ (w2 = 2 ↔ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ (2 : Fin 3) = 2) ∧ (w4 = 2 ↔ (2 : Fin 3) = 2)) ∨
      ((w0 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w2 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w3 = 2 ↔ ¬ (2 : Fin 3) = 2) ∧ (w4 = 2 ↔ ¬ (2 : Fin 3) = 2)))
    (h0 : (w0 = 0 ∨ w1 = 0 ∨ w2 = 0 ∨ w3 = 0 ∨ w4 = 0)) (h1 : (w0 = 1 ∨ w1 = 1 ∨ w2 = 1 ∨ w3 = 1 ∨ w4 = 1)) (h2 : (w0 = 2 ∨ w1 = 2 ∨ w2 = 2 ∨ w3 = 2 ∨ w4 = 2)) :
    (w0 = 0 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 0 ∧ w1 = 1 ∧ w2 = 1 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 1 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 1 ∧ w2 = 0 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 2 ∧ w3 = 0 ∧ w4 = 1) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 2 ∧ w3 = 1 ∧ w4 = 0) := by
  sorry

theorem f13_cases_01222 (w0 w1 w2 w3 w4 : Fin 3)
    (hE1 : ((w0 = 2 ↔ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ (1 : Fin 3) = 2) ∧ (w2 = 2 ↔ (2 : Fin 3) = 2) ∧ (w3 = 2 ↔ (2 : Fin 3) = 2) ∧ (w4 = 2 ↔ (2 : Fin 3) = 2)) ∨
      ((w0 = 2 ↔ ¬ (0 : Fin 3) = 2) ∧ (w1 = 2 ↔ ¬ (1 : Fin 3) = 2) ∧ (w2 = 2 ↔ ¬ (2 : Fin 3) = 2) ∧ (w3 = 2 ↔ ¬ (2 : Fin 3) = 2) ∧ (w4 = 2 ↔ ¬ (2 : Fin 3) = 2)))
    (h0 : (w0 = 0 ∨ w1 = 0 ∨ w2 = 0 ∨ w3 = 0 ∨ w4 = 0)) (h1 : (w0 = 1 ∨ w1 = 1 ∨ w2 = 1 ∨ w3 = 1 ∨ w4 = 1)) (h2 : (w0 = 2 ∨ w1 = 2 ∨ w2 = 2 ∨ w3 = 2 ∨ w4 = 2)) :
    (w0 = 0 ∧ w1 = 1 ∧ w2 = 2 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 1 ∧ w1 = 0 ∧ w2 = 2 ∧ w3 = 2 ∧ w4 = 2) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 1) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 0) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 0 ∧ w3 = 1 ∧ w4 = 1) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 0) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 1 ∧ w3 = 0 ∧ w4 = 1) ∨
      (w0 = 2 ∧ w1 = 2 ∧ w2 = 1 ∧ w3 = 1 ∧ w4 = 0) := by
  sorry

def R31CfgAll : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → rowsZeroS L {r1, r2, r3} = ⊥ →
    ∀ κ1 κ2 κ3 : Fin 5 → ℂ, (∀ m, κ1 m ≠ 0) → (∀ m, κ2 m ≠ 0) → (∀ m, κ3 m ≠ 0) →
    ∀ c2 c3 j s : ℂ, j * j = -1 → (s = 1 ∨ s = -1) →
    (∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) → (∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0) →
    (∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) →
    ∀ f f13 : Fin 5 → Fin 3, ∀ M2 M3 : Fin 5 → ℂ,
    (∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m))) →
    (∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m))) →
    (∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0) →
    (∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0) →
    (∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0) →
    (¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0)) →
    (¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0)) →
    Monotone f → (∃ m, f m = 0) → (∃ m, f m = 1) → (∃ m, f m = 2) →
    ((∀ m, f13 m = 2 ↔ f m = 2) ∨ (∀ m, f13 m = 2 ↔ ¬ f m = 2)) →
    (∃ m, f13 m = 0) → (∃ m, f13 m = 1) → (∃ m, f13 m = 2) →
    (∑ m, κ1 m = 1) → (∑ m, κ2 m = 1) → (∑ m, κ3 m = 1) →
    (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) *
      (1 + j) = 1 →
    (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) *
      (1 + s * j) = 1 → ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0 → False

theorem r31_canon_of_cfgall (h : R31CfgAll) : R31Canon := by
  sorry

theorem r31_of_cfgall (h : R31CfgAll) : R31Hyp := by
  sorry

noncomputable def dotn {n : ℕ} (l x : Fin n → ℂ) : ℂ := ∑ e, l e * x e

theorem dotn_add {n : ℕ} (l x y : Fin n → ℂ) (s : ℂ) : dotn l (x + s • y) = dotn l x + s * dotn l y := by
  sorry

theorem lin_minor_n {n : ℕ} (l z : Fin n → ℂ) (h : ∀ x, dotn z x = 0 → dotn l x = 0) (a b : Fin n) :
    l a * z b - l b * z a = 0 := by
  sorry

theorem qsec_one_n {n : ℕ} (z : Fin n → ℂ) (q : (Fin n → ℂ) → ℂ) (k0 k1 k2 : Fin n → ℂ)
    (Q N : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N i k * gradQ Q x k)
    (hs : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k1 e + y 2 * k2 e) = quadQ Q y)
    (h2 : dotn z k2 ≠ 0 ∨ (dotn z k0 = 0 ∧ dotn z k1 = 0 ∧ dotn z k2 = 0))
    (hv : ∀ x, dotn z x = 0 → q x = 0) : False := by
  sorry

theorem cub1_cases_n {n : ℕ} (z l : Fin n → ℂ) (cf q : (Fin n → ℂ) → ℂ)
    (hid : ∀ x, cf x = dotn l x * q x) (Bq : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hq : ∀ x y (s : ℂ), q (x + s • y) = q x + s * Bq x y + s ^ 2 * q y)
    (k0 k1 k2 : Fin n → ℂ) (Q Q' Q'' N N' N'' : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N i k * gradQ Q x k)
    (hN' : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N' i k * gradQ Q' x k)
    (hN'' : ∀ (x : Fin 3 → ℂ) (i : Fin 3), x i = ∑ k, N'' i k * gradQ Q'' x k)
    (hs : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k1 e + y 2 * k2 e) = quadQ Q y)
    (hs' : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k0 e + y 1 * k2 e + y 2 * k1 e) = quadQ Q' y)
    (hs'' : ∀ y : Fin 3 → ℂ, q (fun e => y 0 * k2 e + y 1 * k1 e + y 2 * k0 e) = quadQ Q'' y)
    (h : z ≠ 0 → ∀ x, dotn z x = 0 → cf x = 0) :
    z = 0 ∨ (∀ a b, l a * z b - l b * z a = 0) := by
  sorry

noncomputable def Emapn {n : ℕ} (EE : Fin n → Fin 3 → Fin 3 → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin 3 → Fin 3 → ℂ) where
  toFun x := fun i k => ∑ e, x e * EE e i k
  map_add' x y := by
    funext i k
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    funext i k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring

noncomputable def dotMapn {n : ℕ} (z : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun x := dotn z x
  map_add' x y := by
    simp only [dotn, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [dotn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring

theorem finrank_ker_dotn {n : ℕ} (z : Fin n → ℂ) (hz : z ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (dotMapn z)) + 1 ≤ n := by
  sorry

theorem bridge5 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0)
    (κs : Fin 3 → Fin 5 → ℂ) (hκs : ∀ i m, κs i m ≠ 0)
    (EE PP : Fin 5 → Fin 3 → Fin 3 → ℂ) (z : Fin 5 → ℂ)
    (hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap κs rr cc t i k =
      ∑ e, (∑ i', ∑ k', PP e i' k' * tauMap κs rr cc t i' k') * EE e i k)
    (hzk : ∀ t ∈ blkL L rr cc,
      ∑ e, z e * (∑ i', ∑ k', PP e i' k' * tauMap κs rr cc t i' k') = 0)
    (UU : Fin 3 → Fin 3 → ℂ) (cr : Fin 3 → ℂ)
    (hU : ∀ i k, κs i (cc (Sum.inl k)) * UU i k = cr i * κs 0 (cc (Sum.inl k)))
    (ρ : Fin 3 → Fin 2 → ℂ) (a0 : Fin 3) (b0 : Fin 2) (hρ : ρ a0 b0 ≠ 0)
    (hrel : ∀ t ∈ L, ∑ a, ∑ b, ρ a b * t (rr (Sum.inl a), cc (Sum.inr b)) = 0)
    (hJ : ∑ a, ∑ b, ρ a b = 0) :
    z ≠ 0 → ∀ x : Fin 5 → ℂ, dotn z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * EE e i k) * UU i k).permanent = 0 := by
  sorry

theorem exists_equiv5 (p q s u v : Fin 5) (hf : Function.Bijective (![p, q, s, u, v] : Fin 5 → Fin 5)) :
    ∃ e : Fin 3 ⊕ Fin 2 ≃ Fin 5, e (Sum.inl 0) = p ∧ e (Sum.inl 1) = q ∧ e (Sum.inl 2) = s ∧
      e (Sum.inr 0) = u ∧ e (Sum.inr 1) = v := by
  sorry

def R31Surv (P W : Fin 5 → Fin 3) (eps : ℂ) : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → rowsZeroS L {r1, r2, r3} = ⊥ →
    ∀ κ1 κ2 κ3 : Fin 5 → ℂ, (∀ m, κ1 m ≠ 0) → (∀ m, κ2 m ≠ 0) → (∀ m, κ3 m ≠ 0) →
    ∀ c2 c3 j s : ℂ, j * j = -1 →
    (∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) → (∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0) →
    (∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) →
    ∀ f f13 : Fin 5 → Fin 3, ∀ M2 M3 : Fin 5 → ℂ,
    (∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m))) →
    (∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m))) →
    (∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0) →
    (∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0) →
    (∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0) →
    (¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0)) →
    (¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0)) →
    (∀ m, f m = P m) → (∀ m, f13 m = W m) → s = eps →
    (∑ m, κ1 m = 1) → (∑ m, κ2 m = 1) → (∑ m, κ3 m = 1) →
    (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) *
      (1 + j) = 1 →
    (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) *
      (1 + s * j) = 1 → ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0 → False

theorem e3_01222_22001_m_012 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![(-1), (-1), 1 * j]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![(-2), 0, 0, 0] : Fin 4 → ℂ) a * z b - (![(-2), 0, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 1, 0, 0] : Fin 4 → ℂ) a * z b - (![0, 1, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 1, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 1] : Fin 4 → ℂ) b * z a = 0) := by
  sorry

theorem w_01222_22001_m_012 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * (c3 * κ1 0) ∧ κ3 1 = (-1) * (c3 * κ1 1) ∧ κ3 2 = (-1) * j * (c3 * κ1 2) ∧ κ3 3 = (-1) * j * (c3 * κ1 3) ∧ κ3 4 = 1 * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 0 * t (r1, 0) + κ1 1 * t (r1, 1) + κ3 4 * t (r3, 4) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 0 + κ1 1 + κ3 4) * (1 + (-1) * j) = 1) :
    (2 * (M2 0) + (-2) * (M2 2) = 0 ∧ 2 * (M3 0) + (-2) * (M3 1) = 0 ∧ 2 * (M3 0) + (-2) * (M3 2) = 0) ∨
      ((-1) * (M3 0) + 1 * (M3 1) = 0 ∧ (-1) * (M3 0) + 1 * (M3 2) = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 2) = 0 ∧ (-1) * (M3 1) + 1 * (M3 2) = 0) := by
  sorry

theorem e1_01222_22001_m_023 (j : ℂ) (hj : j * j = -1) (z : Fin 5 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 5 → ℂ, dotn z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 5 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, (-1), (-1)], ![(-1), 1 * j, 1 * j]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    z = 0 ∨ (∀ a b, (![1, 0, 0, 0, 0] : Fin 5 → ℂ) a * z b - (![1, 0, 0, 0, 0] : Fin 5 → ℂ) b * z a = 0) := by
  sorry

theorem w_01222_22001_m_023 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * (c3 * κ1 0) ∧ κ3 1 = (-1) * (c3 * κ1 1) ∧ κ3 2 = (-1) * j * (c3 * κ1 2) ∧ κ3 3 = (-1) * j * (c3 * κ1 3) ∧ κ3 4 = 1 * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 0 * t (r1, 0) + κ1 1 * t (r1, 1) + κ3 4 * t (r3, 4) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 0 + κ1 1 + κ3 4) * (1 + (-1) * j) = 1) :
    ((-1) * (M2 0) + 1 * (M2 2) = 0 ∧ (-1) * (M2 0) + 1 * (M2 3) = 0 ∧ (-1) * (M3 0) + 1 * (M3 2) = 0 ∧ (-1) * (M3 0) + 1 * (M3 3) = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 2) = 0 ∧ (-1) * (M2 0) + 1 * (M2 3) = 0 ∧ (-1) * (M3 0) + 1 * (M3 2) = 0 ∧ (-1) * (M3 0) + 1 * (M3 3) = 0) := by
  sorry

theorem cfg_01222_22001_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * (c3 * κ1 0) ∧ κ3 1 = (-1) * (c3 * κ1 1) ∧ κ3 2 = (-1) * j * (c3 * κ1 2) ∧ κ3 3 = (-1) * j * (c3 * κ1 3) ∧ κ3 4 = 1 * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 0 * t (r1, 0) + κ1 1 * t (r1, 1) + κ3 4 * t (r3, 4) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 0 + κ1 1 + κ3 4) * (1 + (-1) * j) = 1)
    (hE3a : ¬ ∃ α β : ℂ, M3 0 = α + β * 0 ∧ M3 1 = α + β * 0 ∧ M3 2 = α + β * 0 ∧ M3 3 = α + β * 0 ∧ M3 4 = α + β * 1)
    (hE3b : ¬ ∃ α β : ℂ, M2 0 = α + β * 0 ∧ M2 1 = α + β * 1 ∧ M2 2 = α + β * 0 ∧ M2 3 = α + β * 0 ∧ M2 4 = α + β * 0) : False := by
  sorry

theorem inst_01222_22001_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))
    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))
    (hf : ∀ m, f m = (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (![2, 2, 0, 0, 1] : Fin 5 → Fin 3) m)
    (hs : s = -1)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) * (1 + j) = 1)
    (hK13 : (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) * (1 + s * j) = 1) : False := by
  sorry

theorem e3_00012_01012_p_013 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, (-1), 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, (-1) * j, 1], ![(-1) * j, 1, 1]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![2 * j, 0, 0, 0] : Fin 4 → ℂ) a * z b - (![2 * j, 0, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 1, 0] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 0, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 0, 1] : Fin 4 → ℂ) b * z a = 0) := by
  sorry

theorem w_00012_01012_p_013 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = j * (c2 * κ1 1) ∧ κ2 2 = j * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = j * (c3 * κ1 2) ∧ κ3 3 = 1 * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) + κ3 3 * t (r3, 3) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 4 + κ2 3) * (1 + j) = 1) (hK13 : (κ1 4 + κ3 1 + κ3 3) * (1 + 1 * j) = 1) :
    ((-2) * (M2 0) * j + 2 * (M2 1) * j = 0 ∧ (-2) * (M3 1) * j + 2 * (M3 3) * j = 0) ∨
      ((-1) * (M3 1) + 1 * (M3 3) = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 1) = 0) := by
  sorry

theorem e1_00012_01012_p_024 (j : ℂ) (hj : j * j = -1) (z : Fin 5 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 5 → ℂ, dotn z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 5 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, (-1) * j, (-1)], ![(-1) * j, (-1) * j, (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    z = 0 ∨ (∀ a b, (![1, 0, 0, 0, 0] : Fin 5 → ℂ) a * z b - (![1, 0, 0, 0, 0] : Fin 5 → ℂ) b * z a = 0) := by
  sorry

theorem w_00012_01012_p_024 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = j * (c2 * κ1 1) ∧ κ2 2 = j * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = j * (c3 * κ1 2) ∧ κ3 3 = 1 * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) + κ3 3 * t (r3, 3) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 4 + κ2 3) * (1 + j) = 1) (hK13 : (κ1 4 + κ3 1 + κ3 3) * (1 + 1 * j) = 1) :
    ((-1) * (M2 0) + 1 * (M2 2) = 0 ∧ (-1) * (M2 0) + 1 * (M2 4) = 0 ∧ (-1) * (M3 0) + 1 * (M3 2) = 0 ∧ (-1) * (M3 0) + 1 * (M3 4) = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 2) = 0 ∧ (-1) * (M2 0) + 1 * (M2 4) = 0 ∧ (-1) * (M3 0) + 1 * (M3 2) = 0 ∧ (-1) * (M3 0) + 1 * (M3 4) = 0) := by
  sorry

theorem cfg_00012_01012_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = j * (c2 * κ1 1) ∧ κ2 2 = j * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = j * (c3 * κ1 2) ∧ κ3 3 = 1 * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) + κ3 3 * t (r3, 3) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 4 + κ2 3) * (1 + j) = 1) (hK13 : (κ1 4 + κ3 1 + κ3 3) * (1 + 1 * j) = 1)
    (hE3a : ¬ ∃ α β : ℂ, M3 0 = α + β * 0 ∧ M3 1 = α + β * 1 ∧ M3 2 = α + β * 0 ∧ M3 3 = α + β * 1 ∧ M3 4 = α + β * 0)
    (hE3b : ¬ ∃ α β : ℂ, M2 0 = α + β * 0 ∧ M2 1 = α + β * 0 ∧ M2 2 = α + β * 0 ∧ M2 3 = α + β * 1 ∧ M2 4 = α + β * 0) : False := by
  sorry

theorem inst_00012_01012_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))
    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))
    (hf : ∀ m, f m = (![0, 0, 0, 1, 2] : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (![0, 1, 0, 1, 2] : Fin 5 → Fin 3) m)
    (hs : s = 1)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) * (1 + j) = 1)
    (hK13 : (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) * (1 + s * j) = 1) : False := by
  sorry

theorem e1_00012_00102_p_014 (j : ℂ) (hj : j * j = -1) (z : Fin 5 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 5 → ℂ, dotn z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 5 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, (-1) * j, (-1)], ![(-1) * j, (-1) * j, (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    z = 0 ∨ (∀ a b, (![1, 0, 0, 0, 0] : Fin 5 → ℂ) a * z b - (![1, 0, 0, 0, 0] : Fin 5 → ℂ) b * z a = 0) := by
  sorry

theorem w_00012_00102_p_014 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = j * (c2 * κ1 1) ∧ κ2 2 = j * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = j * (c3 * κ1 0) ∧ κ3 1 = j * (c3 * κ1 1) ∧ κ3 2 = 1 * (c3 * κ1 2) ∧ κ3 3 = j * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 2 * t (r3, 2) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 4 + κ2 3) * (1 + j) = 1) (hK13 : (κ1 4 + κ3 2) * (1 + 1 * j) = 1) :
    ((-1) * (M2 0) + 1 * (M2 1) = 0 ∧ (-1) * (M2 0) + 1 * (M2 4) = 0 ∧ (-1) * (M3 0) + 1 * (M3 1) = 0 ∧ (-1) * (M3 0) + 1 * (M3 4) = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 1) = 0 ∧ (-1) * (M2 0) + 1 * (M2 4) = 0 ∧ (-1) * (M3 0) + 1 * (M3 1) = 0 ∧ (-1) * (M3 0) + 1 * (M3 4) = 0) := by
  sorry

theorem e3_00012_00102_p_023 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, (-1) * j, 1], ![(-1) * j, 1, (-1) * j]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![0, 0, 0, 2] : Fin 4 → ℂ) a * z b - (![0, 0, 0, 2] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 1, 0] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![1, 1, 0, 0] : Fin 4 → ℂ) a * z b - (![1, 1, 0, 0] : Fin 4 → ℂ) b * z a = 0) := by
  sorry

theorem w_00012_00102_p_023 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = j * (c2 * κ1 1) ∧ κ2 2 = j * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = j * (c3 * κ1 0) ∧ κ3 1 = j * (c3 * κ1 1) ∧ κ3 2 = 1 * (c3 * κ1 2) ∧ κ3 3 = j * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 2 * t (r3, 2) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 4 + κ2 3) * (1 + j) = 1) (hK13 : (κ1 4 + κ3 2) * (1 + 1 * j) = 1) :
    ((-2) * (M2 0) + 2 * (M2 2) = 0) ∨
      ((-1) * (M3 0) + 1 * (M3 3) = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 2) = 0 ∧ (-1) * (M3 0) + 1 * (M3 3) = 0) := by
  sorry

theorem cfg_00012_00102_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = j * (c2 * κ1 1) ∧ κ2 2 = j * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = j * (c3 * κ1 0) ∧ κ3 1 = j * (c3 * κ1 1) ∧ κ3 2 = 1 * (c3 * κ1 2) ∧ κ3 3 = j * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 2 * t (r3, 2) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 4 + κ2 3) * (1 + j) = 1) (hK13 : (κ1 4 + κ3 2) * (1 + 1 * j) = 1)
    (hE3a : ¬ ∃ α β : ℂ, M3 0 = α + β * 0 ∧ M3 1 = α + β * 0 ∧ M3 2 = α + β * 1 ∧ M3 3 = α + β * 0 ∧ M3 4 = α + β * 0)
    (hE3b : ¬ ∃ α β : ℂ, M2 0 = α + β * 0 ∧ M2 1 = α + β * 0 ∧ M2 2 = α + β * 0 ∧ M2 3 = α + β * 1 ∧ M2 4 = α + β * 0) : False := by
  sorry

theorem inst_00012_00102_p {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))
    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))
    (hf : ∀ m, f m = (![0, 0, 0, 1, 2] : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (![0, 0, 1, 0, 2] : Fin 5 → Fin 3) m)
    (hs : s = 1)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) * (1 + j) = 1)
    (hK13 : (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) * (1 + s * j) = 1) : False := by
  sorry

theorem e3_01112_01102_m_013 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, (-1), 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, 1, 1], ![1 * j, 1, 1 * j]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![0, 0, 2 * j, 0] : Fin 4 → ℂ) a * z b - (![0, 0, 2 * j, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 1, 0, 0] : Fin 4 → ℂ) a * z b - (![0, 1, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 0, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 0, 1] : Fin 4 → ℂ) b * z a = 0) := by
  sorry

theorem w_01112_01102_m_013 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = 1 * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = 1 * (c3 * κ1 2) ∧ κ3 3 = (-1) * j * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) + κ2 2 * t (r2, 2) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) + κ3 2 * t (r3, 2) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0) :
    ((-2) * (M3 0) * j + 2 * (M3 3) * j = 0) ∨
      ((-1) * (M2 1) + 1 * (M2 3) = 0 ∧ (-1) * (M3 0) + 1 * (M3 3) = 0) ∨
      ((-1) * (M2 1) + 1 * (M2 3) = 0) := by
  sorry

theorem e3_01112_01102_m_034 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![1 * j, 1 * j, (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![0, 0, 2 * j, 0] : Fin 4 → ℂ) a * z b - (![0, 0, 2 * j, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 1, 0, 0] : Fin 4 → ℂ) a * z b - (![0, 1, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![1, 0, 0, 0] : Fin 4 → ℂ) a * z b - (![1, 0, 0, 0] : Fin 4 → ℂ) b * z a = 0) := by
  sorry

theorem w_01112_01102_m_034 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = 1 * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = 1 * (c3 * κ1 2) ∧ κ3 3 = (-1) * j * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) + κ2 2 * t (r2, 2) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) + κ3 2 * t (r3, 2) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0) :
    ((-2) * (M2 0) * j + 2 * (M2 4) * j = 0 ∧ (-2) * (M3 0) * j + 2 * (M3 4) * j = 0) ∨
      ((-1) * (M3 0) + 1 * (M3 3) = 0 ∧ (-1) * (M3 0) + 1 * (M3 4) = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 4) = 0 ∧ (-1) * (M3 0) + 1 * (M3 3) = 0 ∧ (-1) * (M3 0) + 1 * (M3 4) = 0) := by
  sorry

theorem e1_01112_01102_m_124 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![(-1), 0, 1], ![(-1), 0, 1], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![1, 1, (-1)], ![1, 1, (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    z = 0 ∨ (∀ a b, (![0, 0, 0, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 0, 1] : Fin 4 → ℂ) b * z a = 0) := by
  sorry

theorem w_01112_01102_m_124 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = 1 * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = 1 * (c3 * κ1 2) ∧ κ3 3 = (-1) * j * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) + κ2 2 * t (r2, 2) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) + κ3 2 * t (r3, 2) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0) :
    ((-1) * (M2 1) + 1 * (M2 2) = 0 ∧ (-1) * (M3 1) + 1 * (M3 2) = 0 ∧ (-1) * (M2 1) + 1 * (M2 4) + (-1) * (M3 1) + 1 * (M3 4) = 0) ∨
      ((-1) * (M2 1) + 1 * (M2 2) = 0 ∧ (-1) * (M3 1) + 1 * (M3 2) = 0) := by
  sorry

theorem cfg_01112_01102_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = 1 * (c2 * κ1 2) ∧ κ2 3 = 1 * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = 1 * (c3 * κ1 2) ∧ κ3 3 = (-1) * j * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) + κ2 2 * t (r2, 2) + κ2 3 * t (r2, 3) = 0)
    (hg13 : ∀ t ∈ L, κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) + κ3 2 * t (r3, 2) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, M3 0 = α + β * 0 ∧ M3 1 = α + β * 1 ∧ M3 2 = α + β * 1 ∧ M3 3 = α + β * 0 ∧ M3 4 = α + β * 0)
    (hE3b : ¬ ∃ α β : ℂ, M2 0 = α + β * 0 ∧ M2 1 = α + β * 1 ∧ M2 2 = α + β * 1 ∧ M2 3 = α + β * 1 ∧ M2 4 = α + β * 0) : False := by
  sorry

theorem inst_01112_01102_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))
    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))
    (hf : ∀ m, f m = (![0, 1, 1, 1, 2] : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (![0, 1, 1, 0, 2] : Fin 5 → Fin 3) m)
    (hs : s = -1) : False := by
  sorry

theorem r31_cfgall : R31CfgAll := by
  sorry

theorem r31_hyp_proof : R31Hyp := by
  sorry

theorem hat_zero_off {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (w : ℂ × (Fin 5 × Fin 5 → ℂ)) (hw : w ∈ blockSpace L rr cc) (i : Fin 3) (b : Fin 2) :
    hat 5 w (rr (Sum.inl i), cc (Sum.inr b)) = 0 := by
  rw [hat_apply]
  exact ((mem_blockSpace L rr cc w).mp hw).2 i b

theorem rel_hat1 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (i : Fin 3) (r : Fin 5) (hr : rr (Sum.inl i) = r) (a : Fin 5 → ℂ) (A : ℂ)
    (hrel : ∀ t ∈ L, ∑ m, a m * t (r, m) = 0) (hA : ∑ m, a m = A)
    (w : ℂ × (Fin 5 × Fin 5 → ℂ)) (hw : w ∈ blockSpace L rr cc) :
    ∑ k, a (cc (Sum.inl k)) * hat 5 w (r, cc (Sum.inl k)) = w.1 * A := by
  have hL := ((mem_blockSpace L rr cc w).mp hw).1
  have e1 : ∑ m, a m * hat 5 w (r, m) = w.1 * A := by
    calc ∑ m, a m * hat 5 w (r, m) = ∑ m, w.1 * a m + ∑ m, a m * w.2 (r, m) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun m _ => by rw [hat_apply]; ring)
      _ = w.1 * A := by rw [hrel w.2 hL, add_zero, ← Finset.mul_sum, hA]
  have e2 : ∑ m, a m * hat 5 w (r, m) = ∑ y, a (cc y) * hat 5 w (r, cc y) :=
    (Equiv.sum_comp cc (fun m => a m * hat 5 w (r, m))).symm
  rw [e2, Fintype.sum_sum_type] at e1
  have hz : ∑ b, a (cc (Sum.inr b)) * hat 5 w (r, cc (Sum.inr b)) = 0 :=
    Finset.sum_eq_zero (fun b _ => by rw [← hr, hat_zero_off rr cc w hw i b, mul_zero])
  rw [hz, add_zero] at e1
  exact e1

theorem rel_hat2 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (i i' : Fin 3) (r r' : Fin 5) (hr : rr (Sum.inl i) = r) (hr' : rr (Sum.inl i') = r')
    (a b : Fin 5 → ℂ) (A : ℂ)
    (hrel : ∀ t ∈ L, ∑ m, (a m * t (r, m) + b m * t (r', m)) = 0) (hA : ∑ m, (a m + b m) = A)
    (w : ℂ × (Fin 5 × Fin 5 → ℂ)) (hw : w ∈ blockSpace L rr cc) :
    ∑ k, (a (cc (Sum.inl k)) * hat 5 w (r, cc (Sum.inl k)) +
      b (cc (Sum.inl k)) * hat 5 w (r', cc (Sum.inl k))) = w.1 * A := by
  have hL := ((mem_blockSpace L rr cc w).mp hw).1
  have e1 : ∑ m, (a m * hat 5 w (r, m) + b m * hat 5 w (r', m)) = w.1 * A := by
    calc ∑ m, (a m * hat 5 w (r, m) + b m * hat 5 w (r', m)) =
        ∑ m, w.1 * (a m + b m) + ∑ m, (a m * w.2 (r, m) + b m * w.2 (r', m)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun m _ => by rw [hat_apply, hat_apply]; ring)
      _ = w.1 * A := by rw [hrel w.2 hL, add_zero, ← Finset.mul_sum, hA]
  have e2 : ∑ m, (a m * hat 5 w (r, m) + b m * hat 5 w (r', m)) =
      ∑ y, (a (cc y) * hat 5 w (r, cc y) + b (cc y) * hat 5 w (r', cc y)) :=
    (Equiv.sum_comp cc (fun m => a m * hat 5 w (r, m) + b m * hat 5 w (r', m))).symm
  rw [e2, Fintype.sum_sum_type] at e1
  have hz : ∑ c, (a (cc (Sum.inr c)) * hat 5 w (r, cc (Sum.inr c)) +
      b (cc (Sum.inr c)) * hat 5 w (r', cc (Sum.inr c))) = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      rw [← hr, ← hr', hat_zero_off rr cc w hw i c, hat_zero_off rr cc w hw i' c, mul_zero, mul_zero,
        add_zero])
  rw [hz, add_zero] at e1
  exact e1

theorem stest_const {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (N : Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3)
    (hM : ∀ w ∈ blockSpace L r c, ∀ i j, k i j * hat 5 w (r (Sum.inl i), c (Sum.inl j)) =
      ∑ l, M i j l * (k (pi l) (pj l) * hat 5 w (r (Sum.inl (pi l)), c (Sum.inl (pj l)))) +
        N i j * w.1)
    (x0 x1 : Fin 3 → ℂ) :
    (Matrix.of (fun i j => (∑ l, M i j l * x0 l + N i j) / k i j)).permanent =
      (Matrix.of (fun i j => (∑ l, M i j l * x1 l + N i j) / k i j)).permanent := by
  by_contra hne
  exact stest_affine hL h9 r c h0 k hk M N pi pj hM x0 x1
    (fun i j => (∑ l, M i j l * x0 l + N i j) / k i j) (fun i j => (∑ l, M i j l * x1 l + N i j) / k i j)
    (fun i j => rfl) (fun i j => rfl) hne

theorem perm3_of_eq (y : Fin 3 → Fin 3 → ℂ) (a b c d e f g h i : ℂ)
    (h00 : y 0 0 = a) (h01 : y 0 1 = b) (h02 : y 0 2 = c) (h10 : y 1 0 = d) (h11 : y 1 1 = e)
    (h12 : y 1 2 = f) (h20 : y 2 0 = g) (h21 : y 2 1 = h) (h22 : y 2 2 = i) :
    (Matrix.of y).permanent = a * e * i + a * f * h + b * d * i + b * f * g + c * d * h + c * e * g := by
  rw [permanent_three]
  simp only [Matrix.of_apply, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  ring

theorem stest_const_eval {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (N : Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3)
    (hM : ∀ w ∈ blockSpace L r c, ∀ i j, k i j * hat 5 w (r (Sum.inl i), c (Sum.inl j)) =
      ∑ l, M i j l * (k (pi l) (pj l) * hat 5 w (r (Sum.inl (pi l)), c (Sum.inl (pj l)))) +
        N i j * w.1)
    (x0 x1 : Fin 3 → ℂ) (y0 y1 : Fin 3 → Fin 3 → ℂ)
    (hy0 : ∀ i j, (∑ l, M i j l * x0 l + N i j) / k i j = y0 i j)
    (hy1 : ∀ i j, (∑ l, M i j l * x1 l + N i j) / k i j = y1 i j) :
    y0 0 0 * y0 1 1 * y0 2 2 + y0 0 0 * y0 1 2 * y0 2 1 + y0 0 1 * y0 1 0 * y0 2 2 +
      y0 0 1 * y0 1 2 * y0 2 0 + y0 0 2 * y0 1 0 * y0 2 1 + y0 0 2 * y0 1 1 * y0 2 0 =
    y1 0 0 * y1 1 1 * y1 2 2 + y1 0 0 * y1 1 2 * y1 2 1 + y1 0 1 * y1 1 0 * y1 2 2 +
      y1 0 1 * y1 1 2 * y1 2 0 + y1 0 2 * y1 1 0 * y1 2 1 + y1 0 2 * y1 1 1 * y1 2 0 := by
  have h := stest_const hL h9 r c h0 k hk M N pi pj hM x0 x1
  rw [permanent_three, permanent_three] at h
  simp only [Matrix.of_apply, hy0, hy1] at h
  exact h

theorem blk_zero_mem {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ blkL L rr cc) : ((0 : ℂ), t) ∈ blockSpace L rr cc := by
  obtain ⟨htL, ht0⟩ := (mem_blkL L rr cc t).mp ht
  refine (mem_blockSpace L rr cc _).mpr ⟨htL, fun a b => ?_⟩
  show (0 : ℂ) + t (rr (Sum.inl a), cc (Sum.inr b)) = 0
  rw [zero_add]
  exact ht0 a b

theorem rel_blk1 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (i : Fin 3) (r : Fin 5) (hr : rr (Sum.inl i) = r) (a : Fin 5 → ℂ)
    (hrel : ∀ t ∈ L, ∑ m, a m * t (r, m) = 0) (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ blkL L rr cc) :
    ∑ k, a (cc (Sum.inl k)) * t (r, cc (Sum.inl k)) = 0 := by
  have h := rel_hat1 rr cc i r hr a (∑ m, a m) hrel rfl ((0 : ℂ), t) (blk_zero_mem rr cc t ht)
  simp only [hat_apply, zero_add, zero_mul] at h
  exact h

theorem rel_blk2 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (rr cc : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (i i' : Fin 3) (r r' : Fin 5) (hr : rr (Sum.inl i) = r) (hr' : rr (Sum.inl i') = r')
    (a b : Fin 5 → ℂ) (hrel : ∀ t ∈ L, ∑ m, (a m * t (r, m) + b m * t (r', m)) = 0)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ blkL L rr cc) :
    ∑ k, (a (cc (Sum.inl k)) * t (r, cc (Sum.inl k)) + b (cc (Sum.inl k)) * t (r', cc (Sum.inl k))) = 0 := by
  have h := rel_hat2 rr cc i i' r r' hr hr' a b (∑ m, (a m + b m)) hrel rfl ((0 : ℂ), t)
    (blk_zero_mem rr cc t ht)
  simp only [hat_apply, zero_add, zero_mul] at h
  exact h

set_option maxHeartbeats 4000000 in
theorem e5_01222_01222_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = (-1) * (c3 * κ1 2) ∧ κ3 3 = (-1) * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 2 + κ1 3 + κ1 4 + κ3 1) * (1 + (-1) * j) = 1)
    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0)
    (p0 p1 p2 p3 : ℂ)
    (hm20 : M2 0 = ((-1) * j * p1 + 1 * p0)) (hm21 : M2 1 = ((-1) * j * p1 + 1 * p0 + (-1) * p1 + (-1) * p2 + 1 * p3))
    (hm22 : M2 2 = (1 * p0)) (hm30 : M3 0 = ((-1) * p1 + 1 * p3))
    (hm31 : M3 1 = (1 * p2)) (hm32 : M3 2 = (1 * p3))
    (hq : p1 ≠ 0) : False := by
  obtain ⟨hw20, hw21, hw22, hw23, hw24⟩ := hw2
  obtain ⟨hw30, hw31, hw32, hw33, hw34⟩ := hw3
  have hj0 : j ≠ 0 := by
    rintro rfl
    norm_num at hj
  have hJ : j⁻¹ = -j := (eq_inv_of_mul_eq_one_right (by linear_combination -hj : j * -j = 1)).symm
  have hqi : p1 * p1⁻¹ = 1 := mul_inv_cancel₀ hq
  have hc2 : c2 ≠ 0 := by
    intro h
    apply hκ2 0
    rw [hw20, h]
    ring
  have hc3 : c3 ≠ 0 := by
    intro h
    apply hκ3 0
    rw [hw30, h]
    ring
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2'⟩ := exists_equiv3 0 1 2 (by decide) (by decide) (by decide)
  have h0 := h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX
  have hk : ∀ i jj, (![![κ1 0, κ1 1, κ1 2 * p1], ![κ2 0, κ2 1 * p1, κ2 2 * p1], ![κ3 0 * p1, κ3 1 * p1, κ3 2 * p1]] : Fin 3 → Fin 3 → ℂ) i jj ≠ 0 := by
    intro i jj
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases jj with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first | exact hκ1 _ | exact hκ2 _ | exact hκ3 _ | exact mul_ne_zero (hκ1 _) hq |
        exact mul_ne_zero (hκ2 _) hq | exact mul_ne_zero (hκ3 _) hq
  have hM : ∀ w ∈ blockSpace L rr cc, ∀ i jj, (![![κ1 0, κ1 1, κ1 2 * p1], ![κ2 0, κ2 1 * p1, κ2 2 * p1], ![κ3 0 * p1, κ3 1 * p1, κ3 2 * p1]] : Fin 3 → Fin 3 → ℂ) i jj * hat 5 w (rr (Sum.inl i), cc (Sum.inl jj)) =
      ∑ l, (![![![1, 0, 0], ![0, 1, 0], ![((-1) * p1), ((-1) * p1), 0]], ![![0, 0, 1], ![(1 * p1), (1 * p1), 0], ![((-1) * p1), ((-1) * p1), ((-1) * p1)]], ![![((-1) * j * p1 + (-1) * p1), ((-1) * j * p1 + (-1) * p1), ((-1) * j * p1)], ![(1 * p1), (1 * p1), 0], ![(1 * j * p1), (1 * j * p1), (1 * j * p1)]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i jj l * ((![![κ1 0, κ1 1, κ1 2 * p1], ![κ2 0, κ2 1 * p1, κ2 2 * p1], ![κ3 0 * p1, κ3 1 * p1, κ3 2 * p1]] : Fin 3 → Fin 3 → ℂ) ((![0, 0, 1] : Fin 3 → Fin 3) l) ((![0, 1, 0] : Fin 3 → Fin 3) l) *
        hat 5 w (rr (Sum.inl ((![0, 0, 1] : Fin 3 → Fin 3) l)), cc (Sum.inl ((![0, 1, 0] : Fin 3 → Fin 3) l)))) + (![![0, 0, (1 * p1)], ![0, (((-1) / 2) * j * p1 + ((-1) / 2) * p1), (((1) / 2) * j * p1 + ((3) / 2) * p1)], ![(1 * j * p1 + 1 * j * p2 + (-1) * j * p3 + 1 * p0 + 1 * p3), (((1) / 2) * j * p1 + ((-1) / 2) * p1), (((-3) / 2) * j * p1 + (-1) * j * p2 + 1 * j * p3 + (-1) * p0 + ((3) / 2) * p1 + (-1) * p3)]] : Fin 3 → Fin 3 → ℂ) i jj * w.1 := by
    intro w hw i jj
    have R1 := rel_hat1 rr cc 0 r1 hr1 κ1 1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF1 t ht) hk1 w hw
    have R2 := rel_hat1 rr cc 1 r2 hr2 κ2 1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF2 t ht) hk2 w hw
    have R3 := rel_hat1 rr cc 2 r3 hr3 κ3 1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF3 t ht) hk3 w hw
    have R4 := rel_hat2 rr cc 0 1 r1 r2 hr1 hr2 (![0, 0, κ1 2, κ1 3, κ1 4] : Fin 5 → ℂ) (![0, κ2 1, 0, 0, 0] : Fin 5 → ℂ) ((1 - 1 * j) / 2)
      (fun t ht => by
        simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
        linear_combination hg12 t ht)
      (by
        simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
        linear_combination ((1 - 1 * j) / 2) * hK12 + ((κ1 2 + κ1 3 + κ1 4 + κ2 1) / 2) * hj) w hw
    have R5 := rel_hat2 rr cc 0 2 r1 r3 hr1 hr3 (![0, 0, κ1 2, κ1 3, κ1 4] : Fin 5 → ℂ) (![0, κ3 1, 0, 0, 0] : Fin 5 → ℂ) ((1 - (-1) * j) / 2)
      (fun t ht => by
        simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
        linear_combination hg13 t ht)
      (by
        simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
        linear_combination ((1 - (-1) * j) / 2) * hK13 + ((κ1 2 + κ1 3 + κ1 4 + κ3 1) / 2) * hj) w hw
    have R6 := rel_hat2 rr cc 1 2 r2 r3 hr2 hr3 (fun m => M2 m * κ2 m) (fun m => M3 m * κ3 m) 0 hn hJn w hw
    simp only [Fin.sum_univ_three, hc0, hc1, hc2', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at R1 R2 R3 R4 R5 R6
    rw [hm20, hm21, hm22, hm30, hm31, hm32] at R6
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases jj with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2']
    · ring
    · ring
    · linear_combination ((1 * p1)) * R1
    · ring
    · linear_combination (((-1) * p1)) * R1 + ((1 * p1)) * R4
    · linear_combination ((1 * p1)) * R1 + ((1 * p1)) * R2 + (((-1) * p1)) * R4
    · linear_combination ((1 * j * p1 + 1 * p1)) * R1 + ((1 * p0)) * R2 + ((1 * p3)) * R3 + (((-1) * j * p1 + (-1) * p1 + (-1) * p2 + 1 * p3)) * R4 + ((1 * p2 + (-1) * p3)) * R5 + ((-1)) * R6 + ((((1) / 2) * w.1 * p1)) * hj
    · linear_combination (((-1) * p1)) * R1 + ((1 * p1)) * R5
    · linear_combination (((-1) * j * p1)) * R1 + (((-1) * p0)) * R2 + ((1 * p1 + (-1) * p3)) * R3 + ((1 * j * p1 + 1 * p1 + 1 * p2 + (-1) * p3)) * R4 + (((-1) * p1 + (-1) * p2 + 1 * p3)) * R5 + (1) * R6 + ((((-1) / 2) * w.1 * p1)) * hj
  have hy0 : ∀ i jj, (∑ l, (![![![1, 0, 0], ![0, 1, 0], ![((-1) * p1), ((-1) * p1), 0]], ![![0, 0, 1], ![(1 * p1), (1 * p1), 0], ![((-1) * p1), ((-1) * p1), ((-1) * p1)]], ![![((-1) * j * p1 + (-1) * p1), ((-1) * j * p1 + (-1) * p1), ((-1) * j * p1)], ![(1 * p1), (1 * p1), 0], ![(1 * j * p1), (1 * j * p1), (1 * j * p1)]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i jj l * (![0, 0, 0] : Fin 3 → ℂ) l + (![![0, 0, (1 * p1)], ![0, (((-1) / 2) * j * p1 + ((-1) / 2) * p1), (((1) / 2) * j * p1 + ((3) / 2) * p1)], ![(1 * j * p1 + 1 * j * p2 + (-1) * j * p3 + 1 * p0 + 1 * p3), (((1) / 2) * j * p1 + ((-1) / 2) * p1), (((-3) / 2) * j * p1 + (-1) * j * p2 + 1 * j * p3 + (-1) * p0 + ((3) / 2) * p1 + (-1) * p3)]] : Fin 3 → Fin 3 → ℂ) i jj) /
      (![![κ1 0, κ1 1, κ1 2 * p1], ![κ2 0, κ2 1 * p1, κ2 2 * p1], ![κ3 0 * p1, κ3 1 * p1, κ3 2 * p1]] : Fin 3 → Fin 3 → ℂ) i jj = (![![0, 0, (1 * (κ1 2)⁻¹ * p1⁻¹ * p1)], ![0, (((-1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((-1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((-1) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + ((-3) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1)], ![(1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p1 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p2 + (-1) * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p3 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p0 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p3), (((1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((-1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((3) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p2 + (-1) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p3 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p0 + ((-3) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p3)]] : Fin 3 → Fin 3 → ℂ) i jj := by
    intro i jj
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases jj with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv, mul_inv, hJ, inv_neg, inv_one, hw20, hw21, hw22, hw23, hw24, hw30, hw31, hw32, hw33, hw34] <;> ring
  have hy1 : ∀ i jj, (∑ l, (![![![1, 0, 0], ![0, 1, 0], ![((-1) * p1), ((-1) * p1), 0]], ![![0, 0, 1], ![(1 * p1), (1 * p1), 0], ![((-1) * p1), ((-1) * p1), ((-1) * p1)]], ![![((-1) * j * p1 + (-1) * p1), ((-1) * j * p1 + (-1) * p1), ((-1) * j * p1)], ![(1 * p1), (1 * p1), 0], ![(1 * j * p1), (1 * j * p1), (1 * j * p1)]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) i jj l * (![0, 1, 0] : Fin 3 → ℂ) l + (![![0, 0, (1 * p1)], ![0, (((-1) / 2) * j * p1 + ((-1) / 2) * p1), (((1) / 2) * j * p1 + ((3) / 2) * p1)], ![(1 * j * p1 + 1 * j * p2 + (-1) * j * p3 + 1 * p0 + 1 * p3), (((1) / 2) * j * p1 + ((-1) / 2) * p1), (((-3) / 2) * j * p1 + (-1) * j * p2 + 1 * j * p3 + (-1) * p0 + ((3) / 2) * p1 + (-1) * p3)]] : Fin 3 → Fin 3 → ℂ) i jj) /
      (![![κ1 0, κ1 1, κ1 2 * p1], ![κ2 0, κ2 1 * p1, κ2 2 * p1], ![κ3 0 * p1, κ3 1 * p1, κ3 2 * p1]] : Fin 3 → Fin 3 → ℂ) i jj = (![![0, (1 * (κ1 1)⁻¹), 0], ![0, (((-1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((-1) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + ((-1) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1)], ![(1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p2 + (-1) * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p3 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p0 + (-1) * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p1 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p3), (((1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((1) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p2 + (-1) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p3 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p0 + ((-3) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p3)]] : Fin 3 → Fin 3 → ℂ) i jj := by
    intro i jj
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases jj with rfl | rfl | rfl <;>
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv, mul_inv, hJ, inv_neg, inv_one, hw20, hw21, hw22, hw23, hw24, hw30, hw31, hw32, hw33, hw34] <;> ring
  have hc := stest_const_eval hL h9 rr cc h0 (![![κ1 0, κ1 1, κ1 2 * p1], ![κ2 0, κ2 1 * p1, κ2 2 * p1], ![κ3 0 * p1, κ3 1 * p1, κ3 2 * p1]] : Fin 3 → Fin 3 → ℂ) hk (![![![1, 0, 0], ![0, 1, 0], ![((-1) * p1), ((-1) * p1), 0]], ![![0, 0, 1], ![(1 * p1), (1 * p1), 0], ![((-1) * p1), ((-1) * p1), ((-1) * p1)]], ![![((-1) * j * p1 + (-1) * p1), ((-1) * j * p1 + (-1) * p1), ((-1) * j * p1)], ![(1 * p1), (1 * p1), 0], ![(1 * j * p1), (1 * j * p1), (1 * j * p1)]]] : Fin 3 → Fin 3 → Fin 3 → ℂ) (![![0, 0, (1 * p1)], ![0, (((-1) / 2) * j * p1 + ((-1) / 2) * p1), (((1) / 2) * j * p1 + ((3) / 2) * p1)], ![(1 * j * p1 + 1 * j * p2 + (-1) * j * p3 + 1 * p0 + 1 * p3), (((1) / 2) * j * p1 + ((-1) / 2) * p1), (((-3) / 2) * j * p1 + (-1) * j * p2 + 1 * j * p3 + (-1) * p0 + ((3) / 2) * p1 + (-1) * p3)]] : Fin 3 → Fin 3 → ℂ) (![0, 0, 1] : Fin 3 → Fin 3) (![0, 1, 0] : Fin 3 → Fin 3) hM ![0, 0, 0] ![0, 1, 0] (![![0, 0, (1 * (κ1 2)⁻¹ * p1⁻¹ * p1)], ![0, (((-1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((-1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((-1) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + ((-3) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1)], ![(1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p1 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p2 + (-1) * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p3 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p0 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p3), (((1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((-1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((3) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p2 + (-1) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p3 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p0 + ((-3) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p3)]] : Fin 3 → Fin 3 → ℂ) (![![0, (1 * (κ1 1)⁻¹), 0], ![0, (((-1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((1) / 2) * c2⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((-1) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + ((-1) / 2) * c2⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1)], ![(1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p2 + (-1) * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * j * p3 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p0 + (-1) * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p1 + 1 * c3⁻¹ * (κ1 0)⁻¹ * p1⁻¹ * j * p3), (((1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * j * p1 + ((1) / 2) * c3⁻¹ * (κ1 1)⁻¹ * p1⁻¹ * p1), (((1) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p2 + (-1) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * j * p3 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p0 + ((-3) / 2) * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1 + 1 * c3⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p3)]] : Fin 3 → Fin 3 → ℂ) hy0 hy1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  have key : (-1) * (c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹) = 0 := by
    linear_combination (-1) * hc + ((((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p1 * p1 + ((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p1 * p2 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p1 * p3 + ((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1⁻¹ * p0 * p1 * p1 + ((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1⁻¹ * p1 * p1 * p1 + ((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1⁻¹ * p1 * p1 * p2 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p2 + ((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p3 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p0 * p1 + ((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1 * p1 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1 * p2)) * hj + ((((-1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * j * p0 * p1 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p1 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p2 + (-1) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * j * p1 * p3 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p0 * p1 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1 * p1 + ((1) / 2) * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1⁻¹ * p1 * p2 + 1 * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹ * p1⁻¹ * p1 + 1 * c2⁻¹ * c3⁻¹ * (κ1 0)⁻¹ * (κ1 1)⁻¹ * (κ1 2)⁻¹)) * hqi
  have hd : (-1) ≠ 0 := by
    intro h
    norm_num at h
  exact mul_ne_zero hd (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hc2) (inv_ne_zero hc3))
    (inv_ne_zero (hκ1 0))) (inv_ne_zero (hκ1 1))) (inv_ne_zero (hκ1 2))) key

theorem e3_01222_01222_m_012 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![1, 0, (-1)], ![(-1), 1, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![1 * j, 1, (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![0, 0, (-1) * j + 1, 0] : Fin 4 → ℂ) a * z b - (![0, 0, (-1) * j + 1, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 1 * j, 0, 1] : Fin 4 → ℂ) a * z b - (![0, 1 * j, 0, 1] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![1, 0, (-1), 0] : Fin 4 → ℂ) a * z b - (![1, 0, (-1), 0] : Fin 4 → ℂ) b * z a = 0) := by
  refine cub3c z _ _ _ _ (fun x => ?_) h
  simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (1 * (x 0) * (x 1) * (x 2) + (-1) * (x 1) * (x 2) * (x 2)) * hj

theorem w_01222_01222_m_012 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = (-1) * (c3 * κ1 2) ∧ κ3 3 = (-1) * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 2 + κ1 3 + κ1 4 + κ3 1) * (1 + (-1) * j) = 1) :
    (1 * (M2 0) * j + (-1) * (M2 0) + (-1) * (M2 2) * j + 1 * (M2 2) = 0 ∧ 1 * (M3 0) * j + (-1) * (M3 0) + (-1) * (M3 2) * j + 1 * (M3 2) = 0) ∨
      ((-1) * (M2 0) * j + 1 * (M2 1) * j + (-1) * (M3 0) * j + 1 * (M3 1) * j = 0 ∧ 1 * (M2 0) + (-1) * (M2 2) + (-1) * (M3 0) * j + 1 * (M3 2) * j = 0) ∨
      ((-1) * (M2 0) + 1 * (M2 2) = 0 ∧ (-1) * (M2 0) + 1 * (M2 1) + (-1) * (M3 0) + 1 * (M3 1) = 0 ∧ (-1) * (M3 0) + 1 * (M3 2) = 0) := by
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨hw20, hw21, hw22, hw23, hw24⟩ := hw2
  obtain ⟨hw30, hw31, hw32, hw33, hw34⟩ := hw3
  have rel : ∀ t ∈ blkL L rr cc, 1 * (κ1 0 * t (r1, 0)) + 1 * (κ1 1 * t (r1, 1)) + 1 * (κ1 2 * t (r1, 2)) = 0 ∧ 1 * (κ2 0 * t (r2, 0)) + 1 * (κ2 1 * t (r2, 1)) + 1 * (κ2 2 * t (r2, 2)) = 0 ∧ 1 * (κ3 0 * t (r3, 0)) + 1 * (κ3 1 * t (r3, 1)) + 1 * (κ3 2 * t (r3, 2)) = 0 ∧ 1 * (κ1 2 * t (r1, 2)) + 1 * (κ2 1 * t (r2, 1)) = 0 ∧ 1 * (κ1 2 * t (r1, 2)) + 1 * (κ3 1 * t (r3, 1)) = 0 ∧ 1 * (M2 0) * (κ2 0 * t (r2, 0)) + 1 * (M2 1) * (κ2 1 * t (r2, 1)) + 1 * (M2 2) * (κ2 2 * t (r2, 2)) + 1 * (M3 0) * (κ3 0 * t (r3, 0)) + 1 * (M3 1) * (κ3 1 * t (r3, 1)) + 1 * (M3 2) * (κ3 2 * t (r3, 2)) = 0 := by
    intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    obtain ⟨bu, hbu⟩ := compl_inr cc 0 1 2 hc0 hc1 hc2 3 ⟨by decide, by decide, by decide⟩
    obtain ⟨bv, hbv⟩ := compl_inr cc 0 1 2 hc0 hc1 hc2 4 ⟨by decide, by decide, by decide⟩
    have z0u := tau_blk_zero rr cc t ht 0 bu r1 3 hr1 hbu
    have z0v := tau_blk_zero rr cc t ht 0 bv r1 4 hr1 hbv
    have z1u := tau_blk_zero rr cc t ht 1 bu r2 3 hr2 hbu
    have z1v := tau_blk_zero rr cc t ht 1 bv r2 4 hr2 hbv
    have z2u := tau_blk_zero rr cc t ht 2 bu r3 3 hr3 hbu
    have z2v := tau_blk_zero rr cc t ht 2 bv r3 4 hr3 hbv
    have f1 := hF1 t htL
    have f2 := hF2 t htL
    have f3 := hF3 t htL
    have g1 := hg12 t htL
    have g2 := hg13 t htL
    have nn := hn t htL
    simp only [dotL_apply, rowMap_apply, Fin.sum_univ_five] at f1 f2 f3 nn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination f1 - (1) * κ1 3 * z0u - (1) * κ1 4 * z0v
    · linear_combination f2 - (1) * κ2 3 * z1u - (1) * κ2 4 * z1v
    · linear_combination f3 - (1) * κ3 3 * z2u - (1) * κ3 4 * z2v
    · linear_combination g1 - (1) * κ1 3 * z0u - (1) * κ1 4 * z0v
    · linear_combination g2 - (1) * κ1 3 * z0u - (1) * κ1 4 * z0v
    · linear_combination nn - (1 * (M2 3)) * κ2 3 * z1u - (1 * (M2 4)) * κ2 4 * z1v - (1 * (M3 3)) * κ3 3 * z2u - (1 * (M3 4)) * κ3 4 * z2v
  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =
      ∑ e, (∑ i', ∑ k', (![![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![(-1), 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![0, 0, 0], ![(-1), 0, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *
        (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![1, 0, (-1)], ![(-1), 1, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by
    intro t ht i k
    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    · linear_combination 0
    · linear_combination 0
    · linear_combination (1) * R1
    · linear_combination 0
    · linear_combination ((-1)) * R1 + (1) * R4
    · linear_combination (1) * R1 + (1) * R2 + ((-1)) * R4
    · linear_combination 0
    · linear_combination ((-1)) * R1 + (1) * R5
    · linear_combination (1) * R1 + (1) * R3 + ((-1)) * R5
  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (![0, (-1) * (M2 0) + 1 * (M2 2), (-1) * (M2 0) + 1 * (M2 1) + (-1) * (M3 0) + 1 * (M3 1), (-1) * (M3 0) + 1 * (M3 2)] : Fin 4 → ℂ) e *
      (∑ i', ∑ k', (![![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![(-1), 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![0, 0, 0], ![(-1), 0, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht
    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    linear_combination R6 + (1 * (M2 1) + (-1) * (M2 2) + 1 * (M3 1) + (-1) * (M3 2)) * R1 + ((-1) * (M2 2)) * R2 + ((-1) * (M3 2)) * R3 + ((-1) * (M2 1) + 1 * (M2 2)) * R4 + ((-1) * (M3 1) + 1 * (M3 2)) * R5
  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by
    intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hκ1 m
    · exact hκ2 m
    · exact hκ3 m
  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![1 * j, 1, (-1)]] : Fin 3 → Fin 3 → ℂ) i k =
      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by
    intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hc0, hc1, hc2]
    · ring
    · ring
    · ring
    · linear_combination ((-1) * j) * hw20 + ((-1) * (κ1 0) * c2) * hj
    · linear_combination (1) * hw21
    · linear_combination ((-1)) * hw22
    · linear_combination (1 * j) * hw30 + ((-1) * (κ1 0) * c3) * hj
    · linear_combination (1) * hw31
    · linear_combination ((-1)) * hw32
  have hD := e3_01222_01222_m_012 j hj ![0, (-1) * (M2 0) + 1 * (M2 2), (-1) * (M2 0) + 1 * (M2 1) + (-1) * (M3 0) + 1 * (M3 1), (-1) * (M3 0) + 1 * (M3 2)] (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)
    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)
  rcases hD with h | h | h
  · have q0 := h 2 1
    have q1 := h 2 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inl ⟨by linear_combination q0, by linear_combination q1⟩
  · have q0 := h 1 2
    have q1 := h 1 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr (Or.inl ⟨by linear_combination q0, by linear_combination q1⟩)
  · have q0 := h 0 1
    have q1 := h 0 2
    have q2 := h 0 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1 q2
    exact Or.inr (Or.inr ⟨by linear_combination q0, by linear_combination q1, by linear_combination q2⟩)

theorem e1_01222_01222_m_123 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, (-1), 1], ![0, 0, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 1, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![1, (-1), (-1)], ![1, (-1), (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    z = 0 ∨ (∀ a b, (![0, 0, 1, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 1] : Fin 4 → ℂ) b * z a = 0) := by
  refine cub1_cases z _ _ (fun x => (-2) * (x 0) * (x 1) + 2 * (x 0) * (x 2) + 2 * (x 1) * (x 3)) ?_
    (fun x y => (-2) * (x 0) * (y 1) + 2 * (x 0) * (y 2) + (-2) * (x 1) * (y 0) + 2 * (x 1) * (y 3) + 2 * (x 2) * (y 0) + 2 * (x 3) * (y 1)) ?_ ![1, 0, 0, 0] ![0, 1, 0, 0] ![0, 0, (-1), 1]
    ![![0, (-2), (-2)], ![0, 0, 2], ![0, 0, 0]] ![![0, (-2), (-2)], ![0, 0, 2], ![0, 0, 0]] ![![0, 2, (-2)], ![0, 0, (-2)], ![0, 0, 0]] ![![((-1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((1) / 4)], ![((-1) / 4), ((1) / 4), ((-1) / 4)]] ![![((-1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((1) / 4)], ![((-1) / 4), ((1) / 4), ((-1) / 4)]] ![![((-1) / 4), ((1) / 4), ((-1) / 4)], ![((1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((-1) / 4)]] ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro x
    simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro x y s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj

theorem w_01222_01222_m_123 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = (-1) * (c3 * κ1 2) ∧ κ3 3 = (-1) * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 2 + κ1 3 + κ1 4 + κ3 1) * (1 + (-1) * j) = 1) :
    ((-1) * (M2 2) + 1 * (M2 3) = 0 ∧ (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 2) = 0 ∧ (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 3) = 0) ∨
      ((-1) * (M2 2) + 1 * (M2 3) = 0 ∧ (-1) * (M3 2) + 1 * (M3 3) = 0) := by
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 1 2 3 (by decide) (by decide) (by decide)
  obtain ⟨hw20, hw21, hw22, hw23, hw24⟩ := hw2
  obtain ⟨hw30, hw31, hw32, hw33, hw34⟩ := hw3
  have rel : ∀ t ∈ blkL L rr cc, 1 * (κ1 1 * t (r1, 1)) + 1 * (κ1 2 * t (r1, 2)) + 1 * (κ1 3 * t (r1, 3)) = 0 ∧ 1 * (κ2 1 * t (r2, 1)) + 1 * (κ2 2 * t (r2, 2)) + 1 * (κ2 3 * t (r2, 3)) = 0 ∧ 1 * (κ3 1 * t (r3, 1)) + 1 * (κ3 2 * t (r3, 2)) + 1 * (κ3 3 * t (r3, 3)) = 0 ∧ 1 * (κ1 2 * t (r1, 2)) + 1 * (κ1 3 * t (r1, 3)) + 1 * (κ2 1 * t (r2, 1)) = 0 ∧ 1 * (κ1 2 * t (r1, 2)) + 1 * (κ1 3 * t (r1, 3)) + 1 * (κ3 1 * t (r3, 1)) = 0 ∧ 1 * (M2 1) * (κ2 1 * t (r2, 1)) + 1 * (M2 2) * (κ2 2 * t (r2, 2)) + 1 * (M2 3) * (κ2 3 * t (r2, 3)) + 1 * (M3 1) * (κ3 1 * t (r3, 1)) + 1 * (M3 2) * (κ3 2 * t (r3, 2)) + 1 * (M3 3) * (κ3 3 * t (r3, 3)) = 0 := by
    intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    obtain ⟨bu, hbu⟩ := compl_inr cc 1 2 3 hc0 hc1 hc2 0 ⟨by decide, by decide, by decide⟩
    obtain ⟨bv, hbv⟩ := compl_inr cc 1 2 3 hc0 hc1 hc2 4 ⟨by decide, by decide, by decide⟩
    have z0u := tau_blk_zero rr cc t ht 0 bu r1 0 hr1 hbu
    have z0v := tau_blk_zero rr cc t ht 0 bv r1 4 hr1 hbv
    have z1u := tau_blk_zero rr cc t ht 1 bu r2 0 hr2 hbu
    have z1v := tau_blk_zero rr cc t ht 1 bv r2 4 hr2 hbv
    have z2u := tau_blk_zero rr cc t ht 2 bu r3 0 hr3 hbu
    have z2v := tau_blk_zero rr cc t ht 2 bv r3 4 hr3 hbv
    have f1 := hF1 t htL
    have f2 := hF2 t htL
    have f3 := hF3 t htL
    have g1 := hg12 t htL
    have g2 := hg13 t htL
    have nn := hn t htL
    simp only [dotL_apply, rowMap_apply, Fin.sum_univ_five] at f1 f2 f3 nn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination f1 - (1) * κ1 0 * z0u - (1) * κ1 4 * z0v
    · linear_combination f2 - (1) * κ2 0 * z1u - (1) * κ2 4 * z1v
    · linear_combination f3 - (1) * κ3 0 * z2u - (1) * κ3 4 * z2v
    · linear_combination g1 - (1) * κ1 4 * z0v
    · linear_combination g2 - (1) * κ1 4 * z0v
    · linear_combination nn - (1 * (M2 0)) * κ2 0 * z1u - (1 * (M2 4)) * κ2 4 * z1v - (1 * (M3 0)) * κ3 0 * z2u - (1 * (M3 4)) * κ3 4 * z2v
  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =
      ∑ e, (∑ i', ∑ k', (![![![(-1), (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![0, (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *
        (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, (-1), 1], ![0, 0, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 1, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by
    intro t ht i k
    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    · linear_combination 0
    · linear_combination 0
    · linear_combination (1) * R1
    · linear_combination ((-1)) * R1 + (1) * R4
    · linear_combination 0
    · linear_combination (1) * R1 + (1) * R2 + ((-1)) * R4
    · linear_combination ((-1)) * R1 + (1) * R5
    · linear_combination 0
    · linear_combination (1) * R1 + (1) * R3 + ((-1)) * R5
  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (![0, (-1) * (M2 2) + 1 * (M2 3), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 2), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 3)] : Fin 4 → ℂ) e *
      (∑ i', ∑ k', (![![![(-1), (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![0, (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht
    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    linear_combination R6 + (1 * (M2 1) + (-1) * (M2 3) + 1 * (M3 1) + (-1) * (M3 3)) * R1 + ((-1) * (M2 3)) * R2 + ((-1) * (M3 3)) * R3 + ((-1) * (M2 1) + 1 * (M2 3)) * R4 + ((-1) * (M3 1) + 1 * (M3 3)) * R5
  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by
    intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hκ1 m
    · exact hκ2 m
    · exact hκ3 m
  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (![![1, 1, 1], ![1, (-1), (-1)], ![1, (-1), (-1)]] : Fin 3 → Fin 3 → ℂ) i k =
      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by
    intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hc0, hc1, hc2]
    · ring
    · ring
    · ring
    · linear_combination (1) * hw21
    · linear_combination ((-1)) * hw22
    · linear_combination ((-1)) * hw23
    · linear_combination (1) * hw31
    · linear_combination ((-1)) * hw32
    · linear_combination ((-1)) * hw33
  have hD := e1_01222_01222_m_123 j hj ![0, (-1) * (M2 2) + 1 * (M2 3), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 2), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 3)] (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)
    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)
  rcases hD with h | h
  · have q0 := congrFun h 1
    have q1 := congrFun h 2
    have q2 := congrFun h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1 q2
    exact Or.inl ⟨by linear_combination q0, by linear_combination q1, by linear_combination q2⟩
  · have q0 := h 2 1
    have q1 := h 2 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr ⟨by linear_combination q0, by linear_combination q1⟩

theorem e1_01222_01222_m_124 (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, (-1), 1], ![0, 0, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 1, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![1, (-1), (-1)], ![1, (-1), (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    z = 0 ∨ (∀ a b, (![0, 0, 1, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 1] : Fin 4 → ℂ) b * z a = 0) := by
  refine cub1_cases z _ _ (fun x => (-2) * (x 0) * (x 1) + 2 * (x 0) * (x 2) + 2 * (x 1) * (x 3)) ?_
    (fun x y => (-2) * (x 0) * (y 1) + 2 * (x 0) * (y 2) + (-2) * (x 1) * (y 0) + 2 * (x 1) * (y 3) + 2 * (x 2) * (y 0) + 2 * (x 3) * (y 1)) ?_ ![1, 0, 0, 0] ![0, 1, 0, 0] ![0, 0, (-1), 1]
    ![![0, (-2), (-2)], ![0, 0, 2], ![0, 0, 0]] ![![0, (-2), (-2)], ![0, 0, 2], ![0, 0, 0]] ![![0, 2, (-2)], ![0, 0, (-2)], ![0, 0, 0]] ![![((-1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((1) / 4)], ![((-1) / 4), ((1) / 4), ((-1) / 4)]] ![![((-1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((1) / 4)], ![((-1) / 4), ((1) / 4), ((-1) / 4)]] ![![((-1) / 4), ((1) / 4), ((-1) / 4)], ![((1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((-1) / 4)]] ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro x
    simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro x y s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj

theorem w_01222_01222_m_124 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = (-1) * (c3 * κ1 2) ∧ κ3 3 = (-1) * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 2 + κ1 3 + κ1 4 + κ3 1) * (1 + (-1) * j) = 1) :
    ((-1) * (M2 2) + 1 * (M2 4) = 0 ∧ (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 2) = 0 ∧ (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 4) = 0) ∨
      ((-1) * (M2 2) + 1 * (M2 4) = 0 ∧ (-1) * (M3 2) + 1 * (M3 4) = 0) := by
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 1 2 4 (by decide) (by decide) (by decide)
  obtain ⟨hw20, hw21, hw22, hw23, hw24⟩ := hw2
  obtain ⟨hw30, hw31, hw32, hw33, hw34⟩ := hw3
  have rel : ∀ t ∈ blkL L rr cc, 1 * (κ1 1 * t (r1, 1)) + 1 * (κ1 2 * t (r1, 2)) + 1 * (κ1 4 * t (r1, 4)) = 0 ∧ 1 * (κ2 1 * t (r2, 1)) + 1 * (κ2 2 * t (r2, 2)) + 1 * (κ2 4 * t (r2, 4)) = 0 ∧ 1 * (κ3 1 * t (r3, 1)) + 1 * (κ3 2 * t (r3, 2)) + 1 * (κ3 4 * t (r3, 4)) = 0 ∧ 1 * (κ1 2 * t (r1, 2)) + 1 * (κ1 4 * t (r1, 4)) + 1 * (κ2 1 * t (r2, 1)) = 0 ∧ 1 * (κ1 2 * t (r1, 2)) + 1 * (κ1 4 * t (r1, 4)) + 1 * (κ3 1 * t (r3, 1)) = 0 ∧ 1 * (M2 1) * (κ2 1 * t (r2, 1)) + 1 * (M2 2) * (κ2 2 * t (r2, 2)) + 1 * (M2 4) * (κ2 4 * t (r2, 4)) + 1 * (M3 1) * (κ3 1 * t (r3, 1)) + 1 * (M3 2) * (κ3 2 * t (r3, 2)) + 1 * (M3 4) * (κ3 4 * t (r3, 4)) = 0 := by
    intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    obtain ⟨bu, hbu⟩ := compl_inr cc 1 2 4 hc0 hc1 hc2 0 ⟨by decide, by decide, by decide⟩
    obtain ⟨bv, hbv⟩ := compl_inr cc 1 2 4 hc0 hc1 hc2 3 ⟨by decide, by decide, by decide⟩
    have z0u := tau_blk_zero rr cc t ht 0 bu r1 0 hr1 hbu
    have z0v := tau_blk_zero rr cc t ht 0 bv r1 3 hr1 hbv
    have z1u := tau_blk_zero rr cc t ht 1 bu r2 0 hr2 hbu
    have z1v := tau_blk_zero rr cc t ht 1 bv r2 3 hr2 hbv
    have z2u := tau_blk_zero rr cc t ht 2 bu r3 0 hr3 hbu
    have z2v := tau_blk_zero rr cc t ht 2 bv r3 3 hr3 hbv
    have f1 := hF1 t htL
    have f2 := hF2 t htL
    have f3 := hF3 t htL
    have g1 := hg12 t htL
    have g2 := hg13 t htL
    have nn := hn t htL
    simp only [dotL_apply, rowMap_apply, Fin.sum_univ_five] at f1 f2 f3 nn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination f1 - (1) * κ1 0 * z0u - (1) * κ1 3 * z0v
    · linear_combination f2 - (1) * κ2 0 * z1u - (1) * κ2 3 * z1v
    · linear_combination f3 - (1) * κ3 0 * z2u - (1) * κ3 3 * z2v
    · linear_combination g1 - (1) * κ1 3 * z0v
    · linear_combination g2 - (1) * κ1 3 * z0v
    · linear_combination nn - (1 * (M2 0)) * κ2 0 * z1u - (1 * (M2 3)) * κ2 3 * z1v - (1 * (M3 0)) * κ3 0 * z2u - (1 * (M3 3)) * κ3 3 * z2v
  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =
      ∑ e, (∑ i', ∑ k', (![![![(-1), (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![0, (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *
        (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, (-1), 1], ![0, 0, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 1, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by
    intro t ht i k
    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    · linear_combination 0
    · linear_combination 0
    · linear_combination (1) * R1
    · linear_combination ((-1)) * R1 + (1) * R4
    · linear_combination 0
    · linear_combination (1) * R1 + (1) * R2 + ((-1)) * R4
    · linear_combination ((-1)) * R1 + (1) * R5
    · linear_combination 0
    · linear_combination (1) * R1 + (1) * R3 + ((-1)) * R5
  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (![0, (-1) * (M2 2) + 1 * (M2 4), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 2), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 4)] : Fin 4 → ℂ) e *
      (∑ i', ∑ k', (![![![(-1), (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![0, (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht
    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    linear_combination R6 + (1 * (M2 1) + (-1) * (M2 4) + 1 * (M3 1) + (-1) * (M3 4)) * R1 + ((-1) * (M2 4)) * R2 + ((-1) * (M3 4)) * R3 + ((-1) * (M2 1) + 1 * (M2 4)) * R4 + ((-1) * (M3 1) + 1 * (M3 4)) * R5
  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by
    intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hκ1 m
    · exact hκ2 m
    · exact hκ3 m
  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (![![1, 1, 1], ![1, (-1), (-1)], ![1, (-1), (-1)]] : Fin 3 → Fin 3 → ℂ) i k =
      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by
    intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hc0, hc1, hc2]
    · ring
    · ring
    · ring
    · linear_combination (1) * hw21
    · linear_combination ((-1)) * hw22
    · linear_combination ((-1)) * hw24
    · linear_combination (1) * hw31
    · linear_combination ((-1)) * hw32
    · linear_combination ((-1)) * hw34
  have hD := e1_01222_01222_m_124 j hj ![0, (-1) * (M2 2) + 1 * (M2 4), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 2), (-1) * (M2 1) + 1 * (M2 2) + (-1) * (M3 1) + 1 * (M3 4)] (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)
    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)
  rcases hD with h | h
  · have q0 := congrFun h 1
    have q1 := congrFun h 2
    have q2 := congrFun h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1 q2
    exact Or.inl ⟨by linear_combination q0, by linear_combination q1, by linear_combination q2⟩
  · have q0 := h 2 1
    have q1 := h 2 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr ⟨by linear_combination q0, by linear_combination q1⟩

theorem cfg_01222_01222_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)
    (hw2 : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4))
    (hw3 : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = (-1) * (c3 * κ1 2) ∧ κ3 3 = (-1) * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4))
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)
    (hg12 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0)
    (hg13 : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) = 0)
    (M2 M3 : Fin 5 → ℂ)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1) (hK13 : (κ1 2 + κ1 3 + κ1 4 + κ3 1) * (1 + (-1) * j) = 1)
    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0)
    (hE3a : ¬ ∃ α β : ℂ, M3 0 = α + β * 0 ∧ M3 1 = α + β * 1 ∧ M3 2 = α + β * 0 ∧ M3 3 = α + β * 0 ∧ M3 4 = α + β * 0)
    (hE3b : ¬ ∃ α β : ℂ, M2 0 = α + β * 0 ∧ M2 1 = α + β * 1 ∧ M2 2 = α + β * 0 ∧ M2 3 = α + β * 0 ∧ M2 4 = α + β * 0) : False := by
  have D0 := w_01222_01222_m_012 hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj hw2 hw3 hF1 hF2 hF3 hg12 hg13 M2 M3 hn hk1 hk2 hk3 hK12 hK13
  have D3 := w_01222_01222_m_123 hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj hw2 hw3 hF1 hF2 hF3 hg12 hg13 M2 M3 hn hk1 hk2 hk3 hK12 hK13
  have D4 := w_01222_01222_m_124 hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj hw2 hw3 hF1 hF2 hF3 hg12 hg13 M2 M3 hn hk1 hk2 hk3 hK12 hK13
  rcases D0 with ⟨q1, q2⟩ | ⟨q3, q4⟩ | ⟨q5, q6, q7⟩
  · rcases D3 with ⟨q8, q9, q10⟩ | ⟨q11, q12⟩
    · rcases D4 with ⟨q13, q14, q15⟩ | ⟨q16, q17⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + ((-1)) * q9 + (1) * q10 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + ((-1)) * q9 + (1) * q15 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + ((-1)) * q9 + (1) * q10 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q17 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj⟩
    · rcases D4 with ⟨q18, q19, q20⟩ | ⟨q21, q22⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q12 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + ((-1)) * q19 + (1) * q20 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q12 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q22 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj⟩
  · rcases D3 with ⟨q23, q24, q25⟩ | ⟨q26, q27⟩
    · rcases D4 with ⟨q28, q29, q30⟩ | ⟨q31, q32⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((1) / 2)) * q24 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((-1) / 2)) * q24 + (1) * q25 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((-1) / 2)) * q24 + (1) * q30 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((1) / 2)) * q24 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((-1) / 2)) * q24 + (1) * q25 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((1) / 2)) * q24 + (1) * q32 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj⟩
    · rcases D4 with ⟨q33, q34, q35⟩ | ⟨q36, q37⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((1) / 2)) * q34 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (1) * q27 + (((-1) / 2) * j + ((1) / 2)) * q34 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q3 + (((-1) / 2) * j + ((1) / 2)) * q4 + (((-1) / 2) * j + ((-1) / 2)) * q34 + (1) * q35 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj⟩
      · by_cases hq38 : 1 * (M2 0) * j + (-1) * (M2 2) * j = 0
        · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination ((-1) * j) * q4 + (1) * hq38 + ((-1) * (M3 0) + 1 * (M3 2)) * hj, by linear_combination ((-1) * j) * q4 + (1) * q27 + (1) * hq38 + ((-1) * (M3 0) + 1 * (M3 2)) * hj, by linear_combination ((-1) * j) * q4 + (1) * q37 + (1) * hq38 + ((-1) * (M3 0) + 1 * (M3 2)) * hj⟩
        · exact e5_01222_01222_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj hw2 hw3 hF1 hF2 hF3 hg12 hg13 M2 M3 hn hk1 hk2 hk3 hK12 hK13 hJn (1 * (M2 2)) (1 * (M2 0) * j + (-1) * (M2 2) * j) (1 * (M2 0) + (-1) * (M2 1) + 1 * (M3 0)) (1 * (M2 0) * j + (-1) * (M2 2) * j + 1 * (M3 0)) (by linear_combination 0 + (1 * (M2 0) + (-1) * (M2 2)) * hj) (by linear_combination 0 + (1 * (M2 0) + (-1) * (M2 2)) * hj) (by ring) (by ring) (by linear_combination ((-1) * j) * q3 + ((-1) * (M2 0) + 1 * (M2 1) + (-1) * (M3 0) + 1 * (M3 1)) * hj) (by linear_combination ((-1) * j) * q4 + ((-1) * (M3 0) + 1 * (M3 2)) * hj) hq38
  · rcases D3 with ⟨q39, q40, q41⟩ | ⟨q42, q43⟩
    · rcases D4 with ⟨q44, q45, q46⟩ | ⟨q47, q48⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q7, by linear_combination ((-1)) * q5 + (1) * q6 + (1) * q41, by linear_combination ((-1)) * q5 + (1) * q6 + (1) * q46⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q7, by linear_combination ((-1)) * q5 + (1) * q6 + (1) * q41, by linear_combination (1) * q7 + (1) * q48⟩
    · rcases D4 with ⟨q49, q50, q51⟩ | ⟨q52, q53⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q7, by linear_combination (1) * q7 + (1) * q43, by linear_combination ((-1)) * q5 + (1) * q6 + (1) * q51⟩
      · exact hE3a ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q7, by linear_combination (1) * q7 + (1) * q43, by linear_combination (1) * q7 + (1) * q53⟩

theorem inst_01222_01222_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))
    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))
    (hf : ∀ m, f m = (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) m)
    (hs : s = -1)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) * (1 + j) = 1)
    (hK13 : (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) * (1 + s * j) = 1)
    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0) : False := by
  have fv0 : f 0 = 0 := by rw [hf 0] <;> rfl
  have gv0 : f13 0 = 0 := by rw [hf13 0] <;> rfl
  have fv1 : f 1 = 1 := by rw [hf 1] <;> rfl
  have gv1 : f13 1 = 1 := by rw [hf13 1] <;> rfl
  have fv2 : f 2 = 2 := by rw [hf 2] <;> rfl
  have gv2 : f13 2 = 2 := by rw [hf13 2] <;> rfl
  have fv3 : f 3 = 2 := by rw [hf 3] <;> rfl
  have gv3 : f13 3 = 2 := by rw [hf13 3] <;> rfl
  have fv4 : f 4 = 2 := by rw [hf 4] <;> rfl
  have gv4 : f13 4 = 2 := by rw [hf13 4] <;> rfl
  have ia0 : (if f 0 = 2 then (1 : ℂ) else 0) = 0 := by rw [fv0] <;> rfl
  have ib0 : (if f 0 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv0] <;> rfl
  have ic0 : (if f13 0 = 2 then (1 : ℂ) else 0) = 0 := by rw [gv0] <;> rfl
  have id0 : (if f13 0 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv0] <;> rfl
  have ia1 : (if f 1 = 2 then (1 : ℂ) else 0) = 0 := by rw [fv1] <;> rfl
  have ib1 : (if f 1 = 1 then (1 : ℂ) else 0) = 1 := by rw [fv1] <;> rfl
  have ic1 : (if f13 1 = 2 then (1 : ℂ) else 0) = 0 := by rw [gv1] <;> rfl
  have id1 : (if f13 1 = 1 then (1 : ℂ) else 0) = 1 := by rw [gv1] <;> rfl
  have ia2 : (if f 2 = 2 then (1 : ℂ) else 0) = 1 := by rw [fv2] <;> rfl
  have ib2 : (if f 2 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv2] <;> rfl
  have ic2 : (if f13 2 = 2 then (1 : ℂ) else 0) = 1 := by rw [gv2] <;> rfl
  have id2 : (if f13 2 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv2] <;> rfl
  have ia3 : (if f 3 = 2 then (1 : ℂ) else 0) = 1 := by rw [fv3] <;> rfl
  have ib3 : (if f 3 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv3] <;> rfl
  have ic3 : (if f13 3 = 2 then (1 : ℂ) else 0) = 1 := by rw [gv3] <;> rfl
  have id3 : (if f13 3 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv3] <;> rfl
  have ia4 : (if f 4 = 2 then (1 : ℂ) else 0) = 1 := by rw [fv4] <;> rfl
  have ib4 : (if f 4 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv4] <;> rfl
  have ic4 : (if f13 4 = 2 then (1 : ℂ) else 0) = 1 := by rw [gv4] <;> rfl
  have id4 : (if f13 4 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv4] <;> rfl
  refine cfg_01222_01222_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj ?_ ?_ hF1 hF2 hF3 ?_ ?_ M2 M3 hn hk1 hk2 hk3 ?_ ?_ hJn ?_ ?_
  · exact ⟨by rw [(hw2 0).2.2 fv0] <;> ring, by rw [(hw2 1).1 fv1] <;> ring, by rw [(hw2 2).2.1 fv2] <;> ring, by rw [(hw2 3).2.1 fv3] <;> ring, by rw [(hw2 4).2.1 fv4] <;> ring⟩
  · exact ⟨by rw [(hw3 0).2.2 gv0, hs] <;> ring, by rw [(hw3 1).1 gv1] <;> ring, by rw [(hw3 2).2.1 gv2] <;> ring, by rw [(hw3 3).2.1 gv3] <;> ring, by rw [(hw3 4).2.1 gv4] <;> ring⟩
  · intro t ht
    have e := hG12 t ht
    simp only [Fin.sum_univ_five, ia0, ib0, ia1, ib1, ia2, ib2, ia3, ib3, ia4, ib4] at e
    linear_combination e
  · intro t ht
    have e := hG13 t ht
    simp only [Fin.sum_univ_five, ic0, id0, ic1, id1, ic2, id2, ic3, id3, ic4, id4] at e
    linear_combination e
  · have e := hK12
    simp only [Fin.sum_univ_five, ia0, ib0, ia1, ib1, ia2, ib2, ia3, ib3, ia4, ib4] at e
    linear_combination e
  · have e := hK13
    simp only [Fin.sum_univ_five, hs, ic0, id0, ic1, id1, ic2, id2, ic3, id3, ic4, id4] at e
    linear_combination e
  · rintro ⟨α, β, e0, e1, e2, e3, e4⟩
    refine hE3a ⟨α, β, fun m => ?_⟩
    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl
    · rw [id0]
      exact e0
    · rw [id1]
      exact e1
    · rw [id2]
      exact e2
    · rw [id3]
      exact e3
    · rw [id4]
      exact e4
  · rintro ⟨b0, c0, e0, e1, e2, e3, e4⟩
    refine hE3b ⟨b0, c0, fun m => ?_⟩
    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl
    · rw [ib0]
      exact e0
    · rw [ib1]
      exact e1
    · rw [ib2]
      exact e2
    · rw [ib3]
      exact e3
    · rw [ib4]
      exact e4

theorem surv_01222_01222_m : R31Surv (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) (-1) :=
  fun L hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3 hw2 hw3 hG12 hG13 hn hE3a hE3b hf hf13 hs hk1 hk2 hk3 hK12 hK13 hJn =>
    inst_01222_01222_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3 hw2 hw3 hG12 hG13 hn hE3a hE3b hf hf13 hs hk1 hk2 hk3 hK12 hK13 hJn

theorem pe3_012_220_m (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![(-1), (-1), 1 * j]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![0, (-2), 0, 0] : Fin 4 → ℂ) a * z b - (![0, (-2), 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![1, 0, 0, 0] : Fin 4 → ℂ) a * z b - (![1, 0, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 1, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 1] : Fin 4 → ℂ) b * z a = 0) := by
  refine cub3c z _ _ _ _ (fun x => ?_) h
  simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (1 * (x 0) * (x 1) * (x 3)) * hj

theorem pw_012_220_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (S0 S1 S2 : Fin 5) (hS01 : S0 ≠ S1) (hS02 : S0 ≠ S2) (hS12 : S1 ≠ S2)
    (ha0 : f S0 = 0) (ha1 : f S1 = 1) (ha2 : f S2 = 2) (hb0 : f13 S0 = 2) (hb1 : f13 S1 = 2)
    (hb2 : f13 S2 = 0) (hs : s = -1) :
    (2 * (M3 S0) + (-2) * (M3 S1) = 0 ∧ 2 * (M3 S0) + (-2) * (M3 S2) = 0) ∨
      ((-1) * (M2 S0) + 1 * (M2 S2) = 0 ∧ (-1) * (M3 S0) + 1 * (M3 S1) = 0 ∧ (-1) * (M3 S0) + 1 * (M3 S2) = 0) ∨
      ((-1) * (M2 S0) + 1 * (M2 S2) = 0 ∧ (-1) * (M3 S1) + 1 * (M3 S2) = 0) := by
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 S0 S1 S2 hS01 hS02 hS12
  have hw2_0 : κ2 S0 = j * (c2 * κ1 S0) := by rw [(hw2 S0).2.2 ha0] <;> ring
  have hw2_1 : κ2 S1 = 1 * (c2 * κ1 S1) := by rw [(hw2 S1).1 ha1] <;> ring
  have hw2_2 : κ2 S2 = (-1) * (c2 * κ1 S2) := by rw [(hw2 S2).2.1 ha2] <;> ring
  have hw3_0 : κ3 S0 = (-1) * (c3 * κ1 S0) := by rw [(hw3 S0).2.1 hb0] <;> ring
  have hw3_1 : κ3 S1 = (-1) * (c3 * κ1 S1) := by rw [(hw3 S1).2.1 hb1] <;> ring
  have hw3_2 : κ3 S2 = (-1) * j * (c3 * κ1 S2) := by rw [(hw3 S2).2.2 hb2, hs] <;> ring
  have ia0 : (if f (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc0, ha0] <;> rfl
  have ib0 : (if f (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc0, ha0] <;> rfl
  have ic0 : (if f13 (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc0, hb0] <;> rfl
  have id0 : (if f13 (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc0, hb0] <;> rfl
  have ia1 : (if f (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc1, ha1] <;> rfl
  have ib1 : (if f (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 1 := by rw [hc1, ha1] <;> rfl
  have ic1 : (if f13 (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc1, hb1] <;> rfl
  have id1 : (if f13 (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc1, hb1] <;> rfl
  have ia2 : (if f (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc2, ha2] <;> rfl
  have ib2 : (if f (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc2, ha2] <;> rfl
  have ic2 : (if f13 (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc2, hb2] <;> rfl
  have id2 : (if f13 (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc2, hb2] <;> rfl
  have rel : ∀ t ∈ blkL L rr cc, 1 * (κ1 S0 * t (r1, S0)) + 1 * (κ1 S1 * t (r1, S1)) + 1 * (κ1 S2 * t (r1, S2)) = 0 ∧ 1 * (κ2 S0 * t (r2, S0)) + 1 * (κ2 S1 * t (r2, S1)) + 1 * (κ2 S2 * t (r2, S2)) = 0 ∧ 1 * (κ3 S0 * t (r3, S0)) + 1 * (κ3 S1 * t (r3, S1)) + 1 * (κ3 S2 * t (r3, S2)) = 0 ∧ 1 * (κ1 S2 * t (r1, S2)) + 1 * (κ2 S1 * t (r2, S1)) = 0 ∧ 1 * (κ1 S0 * t (r1, S0)) + 1 * (κ1 S1 * t (r1, S1)) = 0 ∧ 1 * (M2 S0) * (κ2 S0 * t (r2, S0)) + 1 * (M2 S1) * (κ2 S1 * t (r2, S1)) + 1 * (M2 S2) * (κ2 S2 * t (r2, S2)) + 1 * (M3 S0) * (κ3 S0 * t (r3, S0)) + 1 * (M3 S1) * (κ3 S1 * t (r3, S1)) + 1 * (M3 S2) * (κ3 S2 * t (r3, S2)) = 0 := by
    intro t ht
    have e1 := rel_blk1 rr cc 0 r1 hr1 κ1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF1 t ht) t ht
    have e2 := rel_blk1 rr cc 1 r2 hr2 κ2 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF2 t ht) t ht
    have e3 := rel_blk1 rr cc 2 r3 hr3 κ3 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF3 t ht) t ht
    have e4 := rel_blk2 rr cc 0 1 r1 r2 hr1 hr2 (fun m => (if f m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f m = 1 then (1 : ℂ) else 0) * κ2 m) hG12 t ht
    have e5 := rel_blk2 rr cc 0 2 r1 r3 hr1 hr3 (fun m => (if f13 m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m) hG13 t ht
    have e6 := rel_blk2 rr cc 1 2 r2 r3 hr2 hr3 (fun m => M2 m * κ2 m) (fun m => M3 m * κ3 m) hn t ht
    simp only [Fin.sum_univ_three] at e1 e2 e3 e4 e5 e6
    simp only [ia0, ia1, ia2, ib0, ib1, ib2] at e4
    simp only [ic0, ic1, ic2, id0, id1, id2] at e5
    simp only [hc0, hc1, hc2] at e1 e2 e3 e4 e5 e6
    exact ⟨by linear_combination e1, by linear_combination e2, by linear_combination e3, by linear_combination e4,
      by linear_combination e5, by linear_combination e6⟩
  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =
      ∑ e, (∑ i', ∑ k', (![![![(-1), 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *
        (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by
    intro t ht i k
    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    · linear_combination 0
    · linear_combination (1) * R5
    · linear_combination (1) * R1 + ((-1)) * R5
    · linear_combination 0
    · linear_combination ((-1)) * R1 + (1) * R4 + (1) * R5
    · linear_combination (1) * R1 + (1) * R2 + ((-1)) * R4 + ((-1)) * R5
    · linear_combination 0
    · linear_combination 0
    · linear_combination (1) * R3
  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (![0, (-1) * (M2 S0) + 1 * (M2 S2), (-1) * (M3 S0) + 1 * (M3 S1), (-1) * (M3 S0) + 1 * (M3 S2)] : Fin 4 → ℂ) e *
      (∑ i', ∑ k', (![![![(-1), 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht
    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    linear_combination R6 + (1 * (M2 S1) + (-1) * (M2 S2)) * R1 + ((-1) * (M2 S2)) * R2 + ((-1) * (M3 S2)) * R3 + ((-1) * (M2 S1) + 1 * (M2 S2)) * R4 + ((-1) * (M2 S1) + 1 * (M2 S2)) * R5
  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by
    intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hκ1 m
    · exact hκ2 m
    · exact hκ3 m
  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![(-1), (-1), 1 * j]] : Fin 3 → Fin 3 → ℂ) i k =
      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by
    intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hc0, hc1, hc2]
    · ring
    · ring
    · ring
    · linear_combination ((-1) * j) * hw2_0 + ((-1) * (κ1 S0) * c2) * hj
    · linear_combination (1) * hw2_1
    · linear_combination ((-1)) * hw2_2
    · linear_combination ((-1)) * hw3_0
    · linear_combination ((-1)) * hw3_1
    · linear_combination (1 * j) * hw3_2 + ((-1) * (κ1 S2) * c3) * hj
  have hD := pe3_012_220_m j hj ![0, (-1) * (M2 S0) + 1 * (M2 S2), (-1) * (M3 S0) + 1 * (M3 S1), (-1) * (M3 S0) + 1 * (M3 S2)] (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)
    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)
  rcases hD with h | h | h
  · have q0 := h 1 2
    have q1 := h 1 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inl ⟨by linear_combination q0, by linear_combination q1⟩
  · have q0 := h 0 1
    have q1 := h 0 2
    have q2 := h 0 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1 q2
    exact Or.inr (Or.inl ⟨by linear_combination q0, by linear_combination q1, by linear_combination q2⟩)
  · have q0 := h 2 1
    have q1 := h 2 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr (Or.inr ⟨by linear_combination q0, by linear_combination q1⟩)

theorem pe3_022_201_m (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, (-1), (-1)], ![(-1), 1 * j, 1]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![(-2), 0, 0, 0] : Fin 4 → ℂ) a * z b - (![(-2), 0, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 1, 0, 0] : Fin 4 → ℂ) a * z b - (![0, 1, 0, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 0, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 0, 1] : Fin 4 → ℂ) b * z a = 0) := by
  refine cub3c z _ _ _ _ (fun x => ?_) h
  simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (1 * (x 0) * (x 1) * (x 3) + 1 * (x 0) * (x 2) * (x 3)) * hj

theorem pw_022_201_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (S0 S1 S2 : Fin 5) (hS01 : S0 ≠ S1) (hS02 : S0 ≠ S2) (hS12 : S1 ≠ S2)
    (ha0 : f S0 = 0) (ha1 : f S1 = 2) (ha2 : f S2 = 2) (hb0 : f13 S0 = 2) (hb1 : f13 S1 = 0)
    (hb2 : f13 S2 = 1) (hs : s = -1) :
    (2 * (M2 S0) + (-2) * (M2 S1) = 0 ∧ 2 * (M2 S0) + (-2) * (M2 S2) = 0 ∧ 2 * (M3 S0) + (-2) * (M3 S1) = 0) ∨
      ((-1) * (M2 S0) + 1 * (M2 S2) = 0 ∧ (-1) * (M3 S0) + 1 * (M3 S1) = 0) ∨
      ((-1) * (M2 S0) + 1 * (M2 S1) = 0 ∧ (-1) * (M2 S0) + 1 * (M2 S2) = 0) := by
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 S0 S1 S2 hS01 hS02 hS12
  have hw2_0 : κ2 S0 = j * (c2 * κ1 S0) := by rw [(hw2 S0).2.2 ha0] <;> ring
  have hw2_1 : κ2 S1 = (-1) * (c2 * κ1 S1) := by rw [(hw2 S1).2.1 ha1] <;> ring
  have hw2_2 : κ2 S2 = (-1) * (c2 * κ1 S2) := by rw [(hw2 S2).2.1 ha2] <;> ring
  have hw3_0 : κ3 S0 = (-1) * (c3 * κ1 S0) := by rw [(hw3 S0).2.1 hb0] <;> ring
  have hw3_1 : κ3 S1 = (-1) * j * (c3 * κ1 S1) := by rw [(hw3 S1).2.2 hb1, hs] <;> ring
  have hw3_2 : κ3 S2 = 1 * (c3 * κ1 S2) := by rw [(hw3 S2).1 hb2] <;> ring
  have ia0 : (if f (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc0, ha0] <;> rfl
  have ib0 : (if f (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc0, ha0] <;> rfl
  have ic0 : (if f13 (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc0, hb0] <;> rfl
  have id0 : (if f13 (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc0, hb0] <;> rfl
  have ia1 : (if f (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc1, ha1] <;> rfl
  have ib1 : (if f (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc1, ha1] <;> rfl
  have ic1 : (if f13 (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc1, hb1] <;> rfl
  have id1 : (if f13 (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc1, hb1] <;> rfl
  have ia2 : (if f (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc2, ha2] <;> rfl
  have ib2 : (if f (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc2, ha2] <;> rfl
  have ic2 : (if f13 (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc2, hb2] <;> rfl
  have id2 : (if f13 (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 1 := by rw [hc2, hb2] <;> rfl
  have rel : ∀ t ∈ blkL L rr cc, 1 * (κ1 S0 * t (r1, S0)) + 1 * (κ1 S1 * t (r1, S1)) + 1 * (κ1 S2 * t (r1, S2)) = 0 ∧ 1 * (κ2 S0 * t (r2, S0)) + 1 * (κ2 S1 * t (r2, S1)) + 1 * (κ2 S2 * t (r2, S2)) = 0 ∧ 1 * (κ3 S0 * t (r3, S0)) + 1 * (κ3 S1 * t (r3, S1)) + 1 * (κ3 S2 * t (r3, S2)) = 0 ∧ 1 * (κ1 S1 * t (r1, S1)) + 1 * (κ1 S2 * t (r1, S2)) = 0 ∧ 1 * (κ1 S0 * t (r1, S0)) + 1 * (κ3 S2 * t (r3, S2)) = 0 ∧ 1 * (M2 S0) * (κ2 S0 * t (r2, S0)) + 1 * (M2 S1) * (κ2 S1 * t (r2, S1)) + 1 * (M2 S2) * (κ2 S2 * t (r2, S2)) + 1 * (M3 S0) * (κ3 S0 * t (r3, S0)) + 1 * (M3 S1) * (κ3 S1 * t (r3, S1)) + 1 * (M3 S2) * (κ3 S2 * t (r3, S2)) = 0 := by
    intro t ht
    have e1 := rel_blk1 rr cc 0 r1 hr1 κ1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF1 t ht) t ht
    have e2 := rel_blk1 rr cc 1 r2 hr2 κ2 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF2 t ht) t ht
    have e3 := rel_blk1 rr cc 2 r3 hr3 κ3 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF3 t ht) t ht
    have e4 := rel_blk2 rr cc 0 1 r1 r2 hr1 hr2 (fun m => (if f m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f m = 1 then (1 : ℂ) else 0) * κ2 m) hG12 t ht
    have e5 := rel_blk2 rr cc 0 2 r1 r3 hr1 hr3 (fun m => (if f13 m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m) hG13 t ht
    have e6 := rel_blk2 rr cc 1 2 r2 r3 hr2 hr3 (fun m => M2 m * κ2 m) (fun m => M3 m * κ3 m) hn t ht
    simp only [Fin.sum_univ_three] at e1 e2 e3 e4 e5 e6
    simp only [ia0, ia1, ia2, ib0, ib1, ib2] at e4
    simp only [ic0, ic1, ic2, id0, id1, id2] at e5
    simp only [hc0, hc1, hc2] at e1 e2 e3 e4 e5 e6
    exact ⟨by linear_combination e1, by linear_combination e2, by linear_combination e3, by linear_combination e4,
      by linear_combination e5, by linear_combination e6⟩
  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =
      ∑ e, (∑ i', ∑ k', (![![![0, (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *
        (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 1, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by
    intro t ht i k
    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    · linear_combination (1) * R1 + ((-1)) * R4
    · linear_combination 0
    · linear_combination (1) * R4
    · linear_combination 0
    · linear_combination 0
    · linear_combination (1) * R2
    · linear_combination 0
    · linear_combination (1) * R1 + (1) * R3 + ((-1)) * R4 + ((-1)) * R5
    · linear_combination ((-1)) * R1 + (1) * R4 + (1) * R5
  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (![0, (-1) * (M2 S0) + 1 * (M2 S1), (-1) * (M2 S0) + 1 * (M2 S2), (-1) * (M3 S0) + 1 * (M3 S1)] : Fin 4 → ℂ) e *
      (∑ i', ∑ k', (![![![0, (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht
    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    linear_combination R6 + ((-1) * (M3 S1) + 1 * (M3 S2)) * R1 + ((-1) * (M2 S2)) * R2 + ((-1) * (M3 S1)) * R3 + (1 * (M3 S1) + (-1) * (M3 S2)) * R4 + (1 * (M3 S1) + (-1) * (M3 S2)) * R5
  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by
    intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hκ1 m
    · exact hκ2 m
    · exact hκ3 m
  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (![![1, 1, 1], ![(-1) * j, (-1), (-1)], ![(-1), 1 * j, 1]] : Fin 3 → Fin 3 → ℂ) i k =
      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by
    intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hc0, hc1, hc2]
    · ring
    · ring
    · ring
    · linear_combination ((-1) * j) * hw2_0 + ((-1) * (κ1 S0) * c2) * hj
    · linear_combination ((-1)) * hw2_1
    · linear_combination ((-1)) * hw2_2
    · linear_combination ((-1)) * hw3_0
    · linear_combination (1 * j) * hw3_1 + ((-1) * (κ1 S1) * c3) * hj
    · linear_combination (1) * hw3_2
  have hD := pe3_022_201_m j hj ![0, (-1) * (M2 S0) + 1 * (M2 S1), (-1) * (M2 S0) + 1 * (M2 S2), (-1) * (M3 S0) + 1 * (M3 S1)] (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)
    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)
  rcases hD with h | h | h
  · have q0 := h 0 1
    have q1 := h 0 2
    have q2 := h 0 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1 q2
    exact Or.inl ⟨by linear_combination q0, by linear_combination q1, by linear_combination q2⟩
  · have q0 := h 1 2
    have q1 := h 1 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr (Or.inl ⟨by linear_combination q0, by linear_combination q1⟩)
  · have q0 := h 3 1
    have q1 := h 3 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr (Or.inr ⟨by linear_combination q0, by linear_combination q1⟩)

theorem instp_01222_22001_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))
    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))
    (hf : ∀ m, f m = (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (![2, 2, 0, 0, 1] : Fin 5 → Fin 3) m)
    (hs : s = -1) : False := by
  have fv0 : f 0 = 0 := by rw [hf 0] <;> rfl
  have gv0 : f13 0 = 2 := by rw [hf13 0] <;> rfl
  have fv1 : f 1 = 1 := by rw [hf 1] <;> rfl
  have gv1 : f13 1 = 2 := by rw [hf13 1] <;> rfl
  have fv2 : f 2 = 2 := by rw [hf 2] <;> rfl
  have gv2 : f13 2 = 0 := by rw [hf13 2] <;> rfl
  have fv3 : f 3 = 2 := by rw [hf 3] <;> rfl
  have gv3 : f13 3 = 0 := by rw [hf13 3] <;> rfl
  have fv4 : f 4 = 2 := by rw [hf 4] <;> rfl
  have gv4 : f13 4 = 1 := by rw [hf13 4] <;> rfl
  have ib0 : (if f 0 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv0] <;> rfl
  have id0 : (if f13 0 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv0] <;> rfl
  have ib1 : (if f 1 = 1 then (1 : ℂ) else 0) = 1 := by rw [fv1] <;> rfl
  have id1 : (if f13 1 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv1] <;> rfl
  have ib2 : (if f 2 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv2] <;> rfl
  have id2 : (if f13 2 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv2] <;> rfl
  have ib3 : (if f 3 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv3] <;> rfl
  have id3 : (if f13 3 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv3] <;> rfl
  have ib4 : (if f 4 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv4] <;> rfl
  have id4 : (if f13 4 = 1 then (1 : ℂ) else 0) = 1 := by rw [gv4] <;> rfl
  have hE3a' : ¬ ∃ α β : ℂ, M3 0 = α + β * 0 ∧ M3 1 = α + β * 0 ∧ M3 2 = α + β * 0 ∧ M3 3 = α + β * 0 ∧ M3 4 = α + β * 1 := by
    rintro ⟨α, β, e0, e1, e2, e3, e4⟩
    refine hE3a ⟨α, β, fun m => ?_⟩
    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl
    · rw [id0]
      exact e0
    · rw [id1]
      exact e1
    · rw [id2]
      exact e2
    · rw [id3]
      exact e3
    · rw [id4]
      exact e4
  have hE3b' : ¬ ∃ α β : ℂ, M2 0 = α + β * 0 ∧ M2 1 = α + β * 1 ∧ M2 2 = α + β * 0 ∧ M2 3 = α + β * 0 ∧ M2 4 = α + β * 0 := by
    rintro ⟨α, β, e0, e1, e2, e3, e4⟩
    refine hE3b ⟨α, β, fun m => ?_⟩
    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl
    · rw [ib0]
      exact e0
    · rw [ib1]
      exact e1
    · rw [ib2]
      exact e2
    · rw [ib3]
      exact e3
    · rw [ib4]
      exact e4
  have D0 := pw_012_220_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3
    hw2 hw3 hG12 hG13 hn 0 1 2 (by decide) (by decide) (by decide) fv0 fv1 fv2 gv0 gv1 gv2 hs
  have D1 := pw_012_220_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3
    hw2 hw3 hG12 hG13 hn 0 1 3 (by decide) (by decide) (by decide) fv0 fv1 fv3 gv0 gv1 gv3 hs
  have D4 := pw_022_201_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3
    hw2 hw3 hG12 hG13 hn 0 2 4 (by decide) (by decide) (by decide) fv0 fv2 fv4 gv0 gv2 gv4 hs
  rcases D0 with ⟨q1, q2⟩ | ⟨q3, q4, q5⟩ | ⟨q6, q7⟩
  · rcases D1 with ⟨q8, q9⟩ | ⟨q10, q11, q12⟩ | ⟨q13, q14⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (((-1) / 2)) * q1, by linear_combination (((-1) / 2)) * q2, by linear_combination (((-1) / 2)) * q9, by ring⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (((-1) / 2)) * q1, by linear_combination (((-1) / 2)) * q2, by linear_combination (1) * q12, by ring⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (((-1) / 2)) * q1, by linear_combination (((-1) / 2)) * q2, by linear_combination (((-1) / 2)) * q1 + (1) * q14, by ring⟩
  · rcases D1 with ⟨q15, q16⟩ | ⟨q17, q18, q19⟩ | ⟨q20, q21⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (1) * q4, by linear_combination (1) * q5, by linear_combination (((-1) / 2)) * q16, by ring⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (1) * q4, by linear_combination (1) * q5, by linear_combination (1) * q19, by ring⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (1) * q4, by linear_combination (1) * q5, by linear_combination (1) * q4 + (1) * q21, by ring⟩
  · rcases D1 with ⟨q22, q23⟩ | ⟨q24, q25, q26⟩ | ⟨q27, q28⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (((-1) / 2)) * q22, by linear_combination (1) * q7 + (((-1) / 2)) * q22, by linear_combination (((-1) / 2)) * q23, by ring⟩
    · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination (1) * q25, by linear_combination (1) * q7 + (1) * q25, by linear_combination (1) * q26, by ring⟩
    · rcases D4 with ⟨q29, q30, q31⟩ | ⟨q32, q33⟩ | ⟨q34, q35⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination ((-1)) * q7 + (((-1) / 2)) * q31, by linear_combination (((-1) / 2)) * q31, by linear_combination ((-1)) * q7 + (1) * q28 + (((-1) / 2)) * q31, by ring⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 4), by ring, by linear_combination ((-1)) * q7 + (1) * q33, by linear_combination (1) * q33, by linear_combination ((-1)) * q7 + (1) * q28 + (1) * q33, by ring⟩
      · exact hE3b' ⟨1 * (M2 0), (-1) * (M2 0) + 1 * (M2 1), by ring, by ring, by linear_combination (1) * q6, by linear_combination (1) * q27, by linear_combination (1) * q35⟩

theorem pe3_012_012_m (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![1, 0, (-1)], ![(-1), 1, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![1 * j, 1, (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    (∀ a b, (![(-1) * j + 1, 0, 1 * j + (-1), 0] : Fin 4 → ℂ) a * z b - (![(-1) * j + 1, 0, 1 * j + (-1), 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 0, 1, 0] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 0] : Fin 4 → ℂ) b * z a = 0) ∨
      (∀ a b, (![0, 1 * j, 0, 1] : Fin 4 → ℂ) a * z b - (![0, 1 * j, 0, 1] : Fin 4 → ℂ) b * z a = 0) := by
  refine cub3c z _ _ _ _ (fun x => ?_) h
  simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (1 * (x 0) * (x 1) * (x 2) + (-1) * (x 1) * (x 2) * (x 2)) * hj

theorem pw_012_012_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (S0 S1 S2 : Fin 5) (hS01 : S0 ≠ S1) (hS02 : S0 ≠ S2) (hS12 : S1 ≠ S2)
    (ha0 : f S0 = 0) (ha1 : f S1 = 1) (ha2 : f S2 = 2) (hb0 : f13 S0 = 0) (hb1 : f13 S1 = 1)
    (hb2 : f13 S2 = 2) (hs : s = -1) :
    (1 * (M2 S0) * j + (-1) * (M2 S0) + (-1) * (M2 S2) * j + 1 * (M2 S2) = 0 ∧ 1 * (M2 S0) * j + (-1) * (M2 S0) + (-1) * (M2 S1) * j + 1 * (M2 S1) + 1 * (M3 S0) * j + (-1) * (M3 S0) + (-1) * (M3 S1) * j + 1 * (M3 S1) = 0 ∧ 1 * (M3 S0) * j + (-1) * (M3 S0) + (-1) * (M3 S2) * j + 1 * (M3 S2) = 0) ∨
      ((-1) * (M2 S0) + 1 * (M2 S2) = 0 ∧ (-1) * (M3 S0) + 1 * (M3 S2) = 0) ∨
      ((-1) * (M2 S0) * j + 1 * (M2 S1) * j + (-1) * (M3 S0) * j + 1 * (M3 S1) * j = 0 ∧ 1 * (M2 S0) + (-1) * (M2 S2) + (-1) * (M3 S0) * j + 1 * (M3 S2) * j = 0) := by
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 S0 S1 S2 hS01 hS02 hS12
  have hw2_0 : κ2 S0 = j * (c2 * κ1 S0) := by rw [(hw2 S0).2.2 ha0] <;> ring
  have hw2_1 : κ2 S1 = 1 * (c2 * κ1 S1) := by rw [(hw2 S1).1 ha1] <;> ring
  have hw2_2 : κ2 S2 = (-1) * (c2 * κ1 S2) := by rw [(hw2 S2).2.1 ha2] <;> ring
  have hw3_0 : κ3 S0 = (-1) * j * (c3 * κ1 S0) := by rw [(hw3 S0).2.2 hb0, hs] <;> ring
  have hw3_1 : κ3 S1 = 1 * (c3 * κ1 S1) := by rw [(hw3 S1).1 hb1] <;> ring
  have hw3_2 : κ3 S2 = (-1) * (c3 * κ1 S2) := by rw [(hw3 S2).2.1 hb2] <;> ring
  have ia0 : (if f (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc0, ha0] <;> rfl
  have ib0 : (if f (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc0, ha0] <;> rfl
  have ic0 : (if f13 (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc0, hb0] <;> rfl
  have id0 : (if f13 (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc0, hb0] <;> rfl
  have ia1 : (if f (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc1, ha1] <;> rfl
  have ib1 : (if f (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 1 := by rw [hc1, ha1] <;> rfl
  have ic1 : (if f13 (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc1, hb1] <;> rfl
  have id1 : (if f13 (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 1 := by rw [hc1, hb1] <;> rfl
  have ia2 : (if f (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc2, ha2] <;> rfl
  have ib2 : (if f (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc2, ha2] <;> rfl
  have ic2 : (if f13 (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc2, hb2] <;> rfl
  have id2 : (if f13 (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc2, hb2] <;> rfl
  have rel : ∀ t ∈ blkL L rr cc, 1 * (κ1 S0 * t (r1, S0)) + 1 * (κ1 S1 * t (r1, S1)) + 1 * (κ1 S2 * t (r1, S2)) = 0 ∧ 1 * (κ2 S0 * t (r2, S0)) + 1 * (κ2 S1 * t (r2, S1)) + 1 * (κ2 S2 * t (r2, S2)) = 0 ∧ 1 * (κ3 S0 * t (r3, S0)) + 1 * (κ3 S1 * t (r3, S1)) + 1 * (κ3 S2 * t (r3, S2)) = 0 ∧ 1 * (κ1 S2 * t (r1, S2)) + 1 * (κ2 S1 * t (r2, S1)) = 0 ∧ 1 * (κ1 S2 * t (r1, S2)) + 1 * (κ3 S1 * t (r3, S1)) = 0 ∧ 1 * (M2 S0) * (κ2 S0 * t (r2, S0)) + 1 * (M2 S1) * (κ2 S1 * t (r2, S1)) + 1 * (M2 S2) * (κ2 S2 * t (r2, S2)) + 1 * (M3 S0) * (κ3 S0 * t (r3, S0)) + 1 * (M3 S1) * (κ3 S1 * t (r3, S1)) + 1 * (M3 S2) * (κ3 S2 * t (r3, S2)) = 0 := by
    intro t ht
    have e1 := rel_blk1 rr cc 0 r1 hr1 κ1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF1 t ht) t ht
    have e2 := rel_blk1 rr cc 1 r2 hr2 κ2 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF2 t ht) t ht
    have e3 := rel_blk1 rr cc 2 r3 hr3 κ3 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF3 t ht) t ht
    have e4 := rel_blk2 rr cc 0 1 r1 r2 hr1 hr2 (fun m => (if f m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f m = 1 then (1 : ℂ) else 0) * κ2 m) hG12 t ht
    have e5 := rel_blk2 rr cc 0 2 r1 r3 hr1 hr3 (fun m => (if f13 m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m) hG13 t ht
    have e6 := rel_blk2 rr cc 1 2 r2 r3 hr2 hr3 (fun m => M2 m * κ2 m) (fun m => M3 m * κ3 m) hn t ht
    simp only [Fin.sum_univ_three] at e1 e2 e3 e4 e5 e6
    simp only [ia0, ia1, ia2, ib0, ib1, ib2] at e4
    simp only [ic0, ic1, ic2, id0, id1, id2] at e5
    simp only [hc0, hc1, hc2] at e1 e2 e3 e4 e5 e6
    exact ⟨by linear_combination e1, by linear_combination e2, by linear_combination e3, by linear_combination e4,
      by linear_combination e5, by linear_combination e6⟩
  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =
      ∑ e, (∑ i', ∑ k', (![![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![(-1), 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![0, 0, 0], ![(-1), 0, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *
        (![![![(-1), 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![(-1), 0, 1], ![0, 0, 0]], ![![1, 0, (-1)], ![(-1), 1, 0], ![(-1), 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by
    intro t ht i k
    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    · linear_combination 0
    · linear_combination 0
    · linear_combination (1) * R1
    · linear_combination 0
    · linear_combination ((-1)) * R1 + (1) * R4
    · linear_combination (1) * R1 + (1) * R2 + ((-1)) * R4
    · linear_combination 0
    · linear_combination ((-1)) * R1 + (1) * R5
    · linear_combination (1) * R1 + (1) * R3 + ((-1)) * R5
  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (![0, (-1) * (M2 S0) + 1 * (M2 S2), (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S1), (-1) * (M3 S0) + 1 * (M3 S2)] : Fin 4 → ℂ) e *
      (∑ i', ∑ k', (![![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![(-1), 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), (-1), 0], ![0, 0, 0], ![(-1), 0, 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht
    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    linear_combination R6 + (1 * (M2 S1) + (-1) * (M2 S2) + 1 * (M3 S1) + (-1) * (M3 S2)) * R1 + ((-1) * (M2 S2)) * R2 + ((-1) * (M3 S2)) * R3 + ((-1) * (M2 S1) + 1 * (M2 S2)) * R4 + ((-1) * (M3 S1) + 1 * (M3 S2)) * R5
  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by
    intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hκ1 m
    · exact hκ2 m
    · exact hκ3 m
  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (![![1, 1, 1], ![(-1) * j, 1, (-1)], ![1 * j, 1, (-1)]] : Fin 3 → Fin 3 → ℂ) i k =
      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by
    intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hc0, hc1, hc2]
    · ring
    · ring
    · ring
    · linear_combination ((-1) * j) * hw2_0 + ((-1) * (κ1 S0) * c2) * hj
    · linear_combination (1) * hw2_1
    · linear_combination ((-1)) * hw2_2
    · linear_combination (1 * j) * hw3_0 + ((-1) * (κ1 S0) * c3) * hj
    · linear_combination (1) * hw3_1
    · linear_combination ((-1)) * hw3_2
  have hD := pe3_012_012_m j hj ![0, (-1) * (M2 S0) + 1 * (M2 S2), (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S1), (-1) * (M3 S0) + 1 * (M3 S2)] (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)
    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)
  rcases hD with h | h | h
  · have q0 := h 0 1
    have q1 := h 0 2
    have q2 := h 0 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1 q2
    exact Or.inl ⟨by linear_combination q0, by linear_combination q1, by linear_combination q2⟩
  · have q0 := h 2 1
    have q1 := h 2 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr (Or.inl ⟨by linear_combination q0, by linear_combination q1⟩)
  · have q0 := h 1 2
    have q1 := h 1 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr (Or.inr ⟨by linear_combination q0, by linear_combination q1⟩)

theorem pe1_122_122_m (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)
    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →
      (Matrix.of fun i k => (∑ e, x e * (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, (-1), 1], ![0, 0, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 1, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *
        (![![1, 1, 1], ![1, (-1), (-1)], ![1, (-1), (-1)]] : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :
    z = 0 ∨ (∀ a b, (![0, 0, 1, 1] : Fin 4 → ℂ) a * z b - (![0, 0, 1, 1] : Fin 4 → ℂ) b * z a = 0) := by
  refine cub1_cases z _ _ (fun x => (-2) * (x 0) * (x 1) + 2 * (x 0) * (x 2) + 2 * (x 1) * (x 3)) ?_
    (fun x y => (-2) * (x 0) * (y 1) + 2 * (x 0) * (y 2) + (-2) * (x 1) * (y 0) + 2 * (x 1) * (y 3) + 2 * (x 2) * (y 0) + 2 * (x 3) * (y 1)) ?_ ![1, 0, 0, 0] ![0, 1, 0, 0] ![0, 0, (-1), 1]
    ![![0, (-2), (-2)], ![0, 0, 2], ![0, 0, 0]] ![![0, (-2), (-2)], ![0, 0, 2], ![0, 0, 0]] ![![0, 2, (-2)], ![0, 0, (-2)], ![0, 0, 0]] ![![((-1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((1) / 4)], ![((-1) / 4), ((1) / 4), ((-1) / 4)]] ![![((-1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((1) / 4)], ![((-1) / 4), ((1) / 4), ((-1) / 4)]] ![![((-1) / 4), ((1) / 4), ((-1) / 4)], ![((1) / 4), ((-1) / 4), ((-1) / 4)], ![((-1) / 4), ((-1) / 4), ((-1) / 4)]] ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro x
    simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro x y s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro x i
    rcases fin3_cases i with rfl | rfl | rfl
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj
  · intro y
    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (0) * hj

theorem pw_122_122_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (S0 S1 S2 : Fin 5) (hS01 : S0 ≠ S1) (hS02 : S0 ≠ S2) (hS12 : S1 ≠ S2)
    (ha0 : f S0 = 1) (ha1 : f S1 = 2) (ha2 : f S2 = 2) (hb0 : f13 S0 = 1) (hb1 : f13 S1 = 2)
    (hb2 : f13 S2 = 2) (hs : s = -1) :
    ((-1) * (M2 S1) + 1 * (M2 S2) = 0 ∧ (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S1) = 0 ∧ (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S2) = 0) ∨
      ((-1) * (M2 S1) + 1 * (M2 S2) = 0 ∧ (-1) * (M3 S1) + 1 * (M3 S2) = 0) := by
  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 S0 S1 S2 hS01 hS02 hS12
  have hw2_0 : κ2 S0 = 1 * (c2 * κ1 S0) := by rw [(hw2 S0).1 ha0] <;> ring
  have hw2_1 : κ2 S1 = (-1) * (c2 * κ1 S1) := by rw [(hw2 S1).2.1 ha1] <;> ring
  have hw2_2 : κ2 S2 = (-1) * (c2 * κ1 S2) := by rw [(hw2 S2).2.1 ha2] <;> ring
  have hw3_0 : κ3 S0 = 1 * (c3 * κ1 S0) := by rw [(hw3 S0).1 hb0] <;> ring
  have hw3_1 : κ3 S1 = (-1) * (c3 * κ1 S1) := by rw [(hw3 S1).2.1 hb1] <;> ring
  have hw3_2 : κ3 S2 = (-1) * (c3 * κ1 S2) := by rw [(hw3 S2).2.1 hb2] <;> ring
  have ia0 : (if f (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc0, ha0] <;> rfl
  have ib0 : (if f (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 1 := by rw [hc0, ha0] <;> rfl
  have ic0 : (if f13 (cc (Sum.inl 0)) = 2 then (1 : ℂ) else 0) = 0 := by rw [hc0, hb0] <;> rfl
  have id0 : (if f13 (cc (Sum.inl 0)) = 1 then (1 : ℂ) else 0) = 1 := by rw [hc0, hb0] <;> rfl
  have ia1 : (if f (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc1, ha1] <;> rfl
  have ib1 : (if f (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc1, ha1] <;> rfl
  have ic1 : (if f13 (cc (Sum.inl 1)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc1, hb1] <;> rfl
  have id1 : (if f13 (cc (Sum.inl 1)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc1, hb1] <;> rfl
  have ia2 : (if f (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc2, ha2] <;> rfl
  have ib2 : (if f (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc2, ha2] <;> rfl
  have ic2 : (if f13 (cc (Sum.inl 2)) = 2 then (1 : ℂ) else 0) = 1 := by rw [hc2, hb2] <;> rfl
  have id2 : (if f13 (cc (Sum.inl 2)) = 1 then (1 : ℂ) else 0) = 0 := by rw [hc2, hb2] <;> rfl
  have rel : ∀ t ∈ blkL L rr cc, 1 * (κ1 S0 * t (r1, S0)) + 1 * (κ1 S1 * t (r1, S1)) + 1 * (κ1 S2 * t (r1, S2)) = 0 ∧ 1 * (κ2 S0 * t (r2, S0)) + 1 * (κ2 S1 * t (r2, S1)) + 1 * (κ2 S2 * t (r2, S2)) = 0 ∧ 1 * (κ3 S0 * t (r3, S0)) + 1 * (κ3 S1 * t (r3, S1)) + 1 * (κ3 S2 * t (r3, S2)) = 0 ∧ 1 * (κ1 S1 * t (r1, S1)) + 1 * (κ1 S2 * t (r1, S2)) + 1 * (κ2 S0 * t (r2, S0)) = 0 ∧ 1 * (κ1 S1 * t (r1, S1)) + 1 * (κ1 S2 * t (r1, S2)) + 1 * (κ3 S0 * t (r3, S0)) = 0 ∧ 1 * (M2 S0) * (κ2 S0 * t (r2, S0)) + 1 * (M2 S1) * (κ2 S1 * t (r2, S1)) + 1 * (M2 S2) * (κ2 S2 * t (r2, S2)) + 1 * (M3 S0) * (κ3 S0 * t (r3, S0)) + 1 * (M3 S1) * (κ3 S1 * t (r3, S1)) + 1 * (M3 S2) * (κ3 S2 * t (r3, S2)) = 0 := by
    intro t ht
    have e1 := rel_blk1 rr cc 0 r1 hr1 κ1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF1 t ht) t ht
    have e2 := rel_blk1 rr cc 1 r2 hr2 κ2 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF2 t ht) t ht
    have e3 := rel_blk1 rr cc 2 r3 hr3 κ3 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF3 t ht) t ht
    have e4 := rel_blk2 rr cc 0 1 r1 r2 hr1 hr2 (fun m => (if f m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f m = 1 then (1 : ℂ) else 0) * κ2 m) hG12 t ht
    have e5 := rel_blk2 rr cc 0 2 r1 r3 hr1 hr3 (fun m => (if f13 m = 2 then (1 : ℂ) else 0) * κ1 m)
      (fun m => (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m) hG13 t ht
    have e6 := rel_blk2 rr cc 1 2 r2 r3 hr2 hr3 (fun m => M2 m * κ2 m) (fun m => M3 m * κ3 m) hn t ht
    simp only [Fin.sum_univ_three] at e1 e2 e3 e4 e5 e6
    simp only [ia0, ia1, ia2, ib0, ib1, ib2] at e4
    simp only [ic0, ic1, ic2, id0, id1, id2] at e5
    simp only [hc0, hc1, hc2] at e1 e2 e3 e4 e5 e6
    exact ⟨by linear_combination e1, by linear_combination e2, by linear_combination e3, by linear_combination e4,
      by linear_combination e5, by linear_combination e6⟩
  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =
      ∑ e, (∑ i', ∑ k', (![![![(-1), (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![0, (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *
        (![![![0, (-1), 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, (-1), 1], ![0, 0, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 1, 0]], ![![(-1), 1, 0], ![(-1), 1, 0], ![(-1), 0, 1]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by
    intro t ht i k
    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    · linear_combination 0
    · linear_combination 0
    · linear_combination (1) * R1
    · linear_combination ((-1)) * R1 + (1) * R4
    · linear_combination 0
    · linear_combination (1) * R1 + (1) * R2 + ((-1)) * R4
    · linear_combination ((-1)) * R1 + (1) * R5
    · linear_combination 0
    · linear_combination (1) * R1 + (1) * R3 + ((-1)) * R5
  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (![0, (-1) * (M2 S1) + 1 * (M2 S2), (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S1), (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S2)] : Fin 4 → ℂ) e *
      (∑ i', ∑ k', (![![![(-1), (-1), 0], ![0, 0, 0], ![0, 0, 0]], ![![(-1), 0, 0], ![0, (-1), 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![(-1), 0, 0], ![0, 0, 0], ![0, (-1), 0]]] : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht
    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]
    linear_combination R6 + (1 * (M2 S0) + (-1) * (M2 S2) + 1 * (M3 S0) + (-1) * (M3 S2)) * R1 + ((-1) * (M2 S2)) * R2 + ((-1) * (M3 S2)) * R3 + ((-1) * (M2 S0) + 1 * (M2 S2)) * R4 + ((-1) * (M3 S0) + 1 * (M3 S2)) * R5
  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by
    intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · exact hκ1 m
    · exact hκ2 m
    · exact hκ3 m
  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (![![1, 1, 1], ![1, (-1), (-1)], ![1, (-1), (-1)]] : Fin 3 → Fin 3 → ℂ) i k =
      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by
    intro i k
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hc0, hc1, hc2]
    · ring
    · ring
    · ring
    · linear_combination (1) * hw2_0
    · linear_combination ((-1)) * hw2_1
    · linear_combination ((-1)) * hw2_2
    · linear_combination (1) * hw3_0
    · linear_combination ((-1)) * hw3_1
    · linear_combination ((-1)) * hw3_2
  have hD := pe1_122_122_m j hj ![0, (-1) * (M2 S1) + 1 * (M2 S2), (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S1), (-1) * (M2 S0) + 1 * (M2 S1) + (-1) * (M3 S0) + 1 * (M3 S2)] (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)
    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)
  rcases hD with h | h
  · have q0 := congrFun h 1
    have q1 := congrFun h 2
    have q2 := congrFun h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1 q2
    exact Or.inl ⟨by linear_combination q0, by linear_combination q1, by linear_combination q2⟩
  · have q0 := h 2 1
    have q1 := h 2 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at q0 q1
    exact Or.inr ⟨by linear_combination q0, by linear_combination q1⟩

theorem instp_01222_01222_m {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)
    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)
    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)
    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧
      (f m = 0 → κ2 m = j * (c2 * κ1 m)))
    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧
      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))
    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)
    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +
      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)
    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)
    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))
    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))
    (hf : ∀ m, f m = (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) m)
    (hs : s = -1)
    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)
    (hK12 : (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) * (1 + j) = 1)
    (hK13 : (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) * (1 + s * j) = 1)
    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0) : False := by
  have fv0 : f 0 = 0 := by rw [hf 0] <;> rfl
  have gv0 : f13 0 = 0 := by rw [hf13 0] <;> rfl
  have fv1 : f 1 = 1 := by rw [hf 1] <;> rfl
  have gv1 : f13 1 = 1 := by rw [hf13 1] <;> rfl
  have fv2 : f 2 = 2 := by rw [hf 2] <;> rfl
  have gv2 : f13 2 = 2 := by rw [hf13 2] <;> rfl
  have fv3 : f 3 = 2 := by rw [hf 3] <;> rfl
  have gv3 : f13 3 = 2 := by rw [hf13 3] <;> rfl
  have fv4 : f 4 = 2 := by rw [hf 4] <;> rfl
  have gv4 : f13 4 = 2 := by rw [hf13 4] <;> rfl
  have ib0 : (if f 0 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv0] <;> rfl
  have id0 : (if f13 0 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv0] <;> rfl
  have ib1 : (if f 1 = 1 then (1 : ℂ) else 0) = 1 := by rw [fv1] <;> rfl
  have id1 : (if f13 1 = 1 then (1 : ℂ) else 0) = 1 := by rw [gv1] <;> rfl
  have ib2 : (if f 2 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv2] <;> rfl
  have id2 : (if f13 2 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv2] <;> rfl
  have ib3 : (if f 3 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv3] <;> rfl
  have id3 : (if f13 3 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv3] <;> rfl
  have ib4 : (if f 4 = 1 then (1 : ℂ) else 0) = 0 := by rw [fv4] <;> rfl
  have id4 : (if f13 4 = 1 then (1 : ℂ) else 0) = 0 := by rw [gv4] <;> rfl
  have ia0 : (if f 0 = 2 then (1 : ℂ) else 0) = 0 := by rw [fv0] <;> rfl
  have ic0 : (if f13 0 = 2 then (1 : ℂ) else 0) = 0 := by rw [gv0] <;> rfl
  have ia1 : (if f 1 = 2 then (1 : ℂ) else 0) = 0 := by rw [fv1] <;> rfl
  have ic1 : (if f13 1 = 2 then (1 : ℂ) else 0) = 0 := by rw [gv1] <;> rfl
  have ia2 : (if f 2 = 2 then (1 : ℂ) else 0) = 1 := by rw [fv2] <;> rfl
  have ic2 : (if f13 2 = 2 then (1 : ℂ) else 0) = 1 := by rw [gv2] <;> rfl
  have ia3 : (if f 3 = 2 then (1 : ℂ) else 0) = 1 := by rw [fv3] <;> rfl
  have ic3 : (if f13 3 = 2 then (1 : ℂ) else 0) = 1 := by rw [gv3] <;> rfl
  have ia4 : (if f 4 = 2 then (1 : ℂ) else 0) = 1 := by rw [fv4] <;> rfl
  have ic4 : (if f13 4 = 2 then (1 : ℂ) else 0) = 1 := by rw [gv4] <;> rfl
  have hw2x : κ2 0 = j * (c2 * κ1 0) ∧ κ2 1 = 1 * (c2 * κ1 1) ∧ κ2 2 = (-1) * (c2 * κ1 2) ∧ κ2 3 = (-1) * (c2 * κ1 3) ∧ κ2 4 = (-1) * (c2 * κ1 4) :=
    ⟨by rw [(hw2 0).2.2 fv0] <;> ring, by rw [(hw2 1).1 fv1] <;> ring, by rw [(hw2 2).2.1 fv2] <;> ring, by rw [(hw2 3).2.1 fv3] <;> ring, by rw [(hw2 4).2.1 fv4] <;> ring⟩
  have hw3x : κ3 0 = (-1) * j * (c3 * κ1 0) ∧ κ3 1 = 1 * (c3 * κ1 1) ∧ κ3 2 = (-1) * (c3 * κ1 2) ∧ κ3 3 = (-1) * (c3 * κ1 3) ∧ κ3 4 = (-1) * (c3 * κ1 4) :=
    ⟨by rw [(hw3 0).2.2 gv0, hs] <;> ring, by rw [(hw3 1).1 gv1] <;> ring, by rw [(hw3 2).2.1 gv2] <;> ring, by rw [(hw3 3).2.1 gv3] <;> ring, by rw [(hw3 4).2.1 gv4] <;> ring⟩
  have hg12x : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ2 1 * t (r2, 1) = 0 := by
    intro t ht
    have e := hG12 t ht
    simp only [Fin.sum_univ_five, ia0, ib0, ia1, ib1, ia2, ib2, ia3, ib3, ia4, ib4] at e
    linear_combination e
  have hg13x : ∀ t ∈ L, κ1 2 * t (r1, 2) + κ1 3 * t (r1, 3) + κ1 4 * t (r1, 4) + κ3 1 * t (r3, 1) = 0 := by
    intro t ht
    have e := hG13 t ht
    simp only [Fin.sum_univ_five, ic0, id0, ic1, id1, ic2, id2, ic3, id3, ic4, id4] at e
    linear_combination e
  have hK12x : (κ1 2 + κ1 3 + κ1 4 + κ2 1) * (1 + j) = 1 := by
    have e := hK12
    simp only [Fin.sum_univ_five, ia0, ib0, ia1, ib1, ia2, ib2, ia3, ib3, ia4, ib4] at e
    linear_combination e
  have hK13x : (κ1 2 + κ1 3 + κ1 4 + κ3 1) * (1 + (-1) * j) = 1 := by
    have e := hK13
    simp only [Fin.sum_univ_five, hs, ic0, id0, ic1, id1, ic2, id2, ic3, id3, ic4, id4] at e
    linear_combination e
  have hE3a' : ¬ ∃ α β : ℂ, M3 0 = α + β * 0 ∧ M3 1 = α + β * 1 ∧ M3 2 = α + β * 0 ∧ M3 3 = α + β * 0 ∧ M3 4 = α + β * 0 := by
    rintro ⟨α, β, e0, e1, e2, e3, e4⟩
    refine hE3a ⟨α, β, fun m => ?_⟩
    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl
    · rw [id0]
      exact e0
    · rw [id1]
      exact e1
    · rw [id2]
      exact e2
    · rw [id3]
      exact e3
    · rw [id4]
      exact e4
  have hE3b' : ¬ ∃ α β : ℂ, M2 0 = α + β * 0 ∧ M2 1 = α + β * 1 ∧ M2 2 = α + β * 0 ∧ M2 3 = α + β * 0 ∧ M2 4 = α + β * 0 := by
    rintro ⟨α, β, e0, e1, e2, e3, e4⟩
    refine hE3b ⟨α, β, fun m => ?_⟩
    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl
    · rw [ib0]
      exact e0
    · rw [ib1]
      exact e1
    · rw [ib2]
      exact e2
    · rw [ib3]
      exact e3
    · rw [ib4]
      exact e4
  have D0 := pw_012_012_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3
    hw2 hw3 hG12 hG13 hn 0 1 2 (by decide) (by decide) (by decide) fv0 fv1 fv2 gv0 gv1 gv2 hs
  have D3 := pw_122_122_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3
    hw2 hw3 hG12 hG13 hn 1 2 3 (by decide) (by decide) (by decide) fv1 fv2 fv3 gv1 gv2 gv3 hs
  have D4 := pw_122_122_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3
    hw2 hw3 hG12 hG13 hn 1 2 4 (by decide) (by decide) (by decide) fv1 fv2 fv4 gv1 gv2 gv4 hs
  rcases D0 with ⟨q1, q2, q3⟩ | ⟨q4, q5⟩ | ⟨q6, q7⟩
  · rcases D3 with ⟨q8, q9, q10⟩ | ⟨q11, q12⟩
    · rcases D4 with ⟨q13, q14, q15⟩ | ⟨q16, q17⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q1 + (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q10 + (((1) / 2) * (M2 1) + ((-1) / 2) * (M2 2) + ((-1) / 2) * (M3 0) + ((1) / 2) * (M3 1)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q1 + (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q15 + (((1) / 2) * (M2 1) + ((-1) / 2) * (M2 2) + ((-1) / 2) * (M3 0) + ((1) / 2) * (M3 1)) * hj⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q1 + (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q10 + (((1) / 2) * (M2 1) + ((-1) / 2) * (M2 2) + ((-1) / 2) * (M3 0) + ((1) / 2) * (M3 1)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (1) * q17 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj⟩
    · rcases D4 with ⟨q18, q19, q20⟩ | ⟨q21, q22⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (1) * q12 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q1 + (((1) / 2) * j + ((1) / 2)) * q2 + (1) * q20 + (((1) / 2) * (M2 1) + ((-1) / 2) * (M2 2) + ((-1) / 2) * (M3 0) + ((1) / 2) * (M3 1)) * hj⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (1) * q12 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((1) / 2) * j + ((1) / 2)) * q3 + (1) * q22 + (((-1) / 2) * (M3 0) + ((1) / 2) * (M3 2)) * hj⟩
  · rcases D3 with ⟨q23, q24, q25⟩ | ⟨q26, q27⟩
    · rcases D4 with ⟨q28, q29, q30⟩ | ⟨q31, q32⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q5, by linear_combination (1) * q5 + ((-1)) * q24 + (1) * q25, by linear_combination (1) * q5 + ((-1)) * q24 + (1) * q30⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q5, by linear_combination (1) * q5 + ((-1)) * q24 + (1) * q25, by linear_combination (1) * q5 + (1) * q32⟩
    · rcases D4 with ⟨q33, q34, q35⟩ | ⟨q36, q37⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q5, by linear_combination (1) * q5 + (1) * q27, by linear_combination (1) * q5 + ((-1)) * q34 + (1) * q35⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (1) * q5, by linear_combination (1) * q5 + (1) * q27, by linear_combination (1) * q5 + (1) * q37⟩
  · rcases D3 with ⟨q38, q39, q40⟩ | ⟨q41, q42⟩
    · rcases D4 with ⟨q43, q44, q45⟩ | ⟨q46, q47⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((1) / 2)) * q39 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((-1) / 2)) * q39 + (1) * q40 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((-1) / 2)) * q39 + (1) * q45 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((1) / 2)) * q39 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((-1) / 2)) * q39 + (1) * q40 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((1) / 2)) * q39 + (1) * q47 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj⟩
    · rcases D4 with ⟨q48, q49, q50⟩ | ⟨q51, q52⟩
      · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((1) / 2)) * q49 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (1) * q42 + (((-1) / 2) * j + ((1) / 2)) * q49 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj, by linear_combination (((-1) / 2) * j + ((-1) / 2)) * q6 + (((-1) / 2) * j + ((1) / 2)) * q7 + (((-1) / 2) * j + ((-1) / 2)) * q49 + (1) * q50 + (((-1) / 2) * (M2 0) + ((1) / 2) * (M2 1) + (-1) * (M3 0) + ((1) / 2) * (M3 1) + ((1) / 2) * (M3 2)) * hj⟩
      · by_cases hq53 : 1 * (M2 0) * j + (-1) * (M2 2) * j = 0
        · exact hE3a' ⟨1 * (M3 0), (-1) * (M3 0) + 1 * (M3 1), by ring, by ring, by linear_combination ((-1) * j) * q7 + (1) * hq53 + ((-1) * (M3 0) + 1 * (M3 2)) * hj, by linear_combination ((-1) * j) * q7 + (1) * q42 + (1) * hq53 + ((-1) * (M3 0) + 1 * (M3 2)) * hj, by linear_combination ((-1) * j) * q7 + (1) * q52 + (1) * hq53 + ((-1) * (M3 0) + 1 * (M3 2)) * hj⟩
        · exact e5_01222_01222_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj hw2x hw3x hF1 hF2 hF3 hg12x hg13x M2 M3 hn hk1 hk2 hk3 hK12x hK13x hJn (1 * (M2 2)) (1 * (M2 0) * j + (-1) * (M2 2) * j) (1 * (M2 0) + (-1) * (M2 1) + 1 * (M3 0)) (1 * (M2 0) * j + (-1) * (M2 2) * j + 1 * (M3 0)) (by linear_combination 0 + (1 * (M2 0) + (-1) * (M2 2)) * hj) (by linear_combination 0 + (1 * (M2 0) + (-1) * (M2 2)) * hj) (by ring) (by ring) (by linear_combination ((-1) * j) * q6 + ((-1) * (M2 0) + 1 * (M2 1) + (-1) * (M3 0) + 1 * (M3 1)) * hj) (by linear_combination ((-1) * j) * q7 + ((-1) * (M3 0) + 1 * (M3 2)) * hj) hq53

theorem survp_01222_01222_m : R31Surv (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) (![0, 1, 2, 2, 2] : Fin 5 → Fin 3) (-1) :=
  fun L hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3 hw2 hw3 hG12 hG13 hn hE3a hE3b hf hf13 hs hk1 hk2 hk3 hK12 hK13 hJn =>
    instp_01222_01222_m hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3 hw2 hw3 hG12 hG13 hn hE3a hE3b hf hf13 hs hk1 hk2 hk3 hK12 hK13 hJn

end PEqualNP.Outside.L_gct_210_aux.ZBF

theorem PEqualNP.Outside.L_gct_210 : True := by
  trivial
