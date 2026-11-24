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
    comb3 ν μ κ w m = w.1 * ν m + w.2.1 * μ m + w.2.2 * κ m := rfl

theorem t2_dep (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r1 r2 r3 : Fin 5)
    (κ ν ν' μ μ' : Fin 5 → ℂ)
    (hκ : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ1 : dotL κ 1 = 1)
    (hν : ∀ t ∈ L, dotL ν (rowMap r1 t) + dotL ν' (rowMap r2 t) = 0)
    (hμ : ∀ t ∈ L, dotL μ (rowMap r1 t) + dotL μ' (rowMap r3 t) = 0)
    (hdim : Module.finrank ℂ (rowsZeroS L {r1, r2, r3}) + 3 ≤
      Module.finrank ℂ (rowsZeroS L {r2, r3})) :
    ∃ α β γ : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ m, α * ν m + β * μ m + γ * κ m = 0 := by
  obtain ⟨A, hA⟩ : ∃ A : Submodule ℂ (Fin 5 → ℂ), A = (rowsZeroS L {r2, r3}).map (rowMap r1) :=
    ⟨_, rfl⟩
  have hrk := rows_rank L {r2, r3} r1
  rw [← hA] at hrk
  have hA3 : 3 ≤ Module.finrank ℂ A := by
    have e : (insert r1 ({r2, r3} : Finset (Fin 5))) = {r1, r2, r3} := rfl
    rw [e] at hrk
    omega
  have horth : ∀ a ∈ A, ∀ b ∈ LinearMap.range (comb3 ν μ κ), ∑ m, b m * a m = 0 := by
    rw [hA]
    rintro _ ⟨t, ⟨htL, ht0⟩, rfl⟩ b hb
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hb
    have z2 : rowMap r2 t = 0 := funext (ht0 r2 (by simp))
    have z3 : rowMap r3 t = 0 := funext (ht0 r3 (by simp))
    have e1 := hν t htL
    have e2 := hμ t htL
    have e3 := hκ t htL
    rw [z2, map_zero, add_zero] at e1
    rw [z3, map_zero, add_zero] at e2
    rw [dotL_apply] at e1 e2 e3
    calc ∑ m, comb3 ν μ κ w m * rowMap r1 t m
        = w.1 * ∑ m, rowMap r1 t m * ν m + w.2.1 * ∑ m, rowMap r1 t m * μ m +
            w.2.2 * ∑ m, rowMap r1 t m * κ m := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [comb3_apply]
          ring
      _ = 0 := by
          rw [e1, e2, e3]
          ring
  have hp := perp_bound A (LinearMap.range (comb3 ν μ κ)) horth
  have hrn := LinearMap.finrank_range_add_finrank_ker (comb3 ν μ κ)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self] at hrn
  have hker : LinearMap.ker (comb3 ν μ κ) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrn
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hwm : ∀ m, w.1 * ν m + w.2.1 * μ m + w.2.2 * κ m = 0 := fun m => by
    have e := congrFun (LinearMap.mem_ker.mp hw) m
    rw [comb3_apply] at e
    exact e
  refine ⟨w.1, w.2.1, w.2.2, ?_, hwm⟩
  by_contra hc
  push_neg at hc
  obtain ⟨m, hm⟩ : ∃ m, κ m ≠ 0 := by
    by_contra hk
    push_neg at hk
    simp [dotL_apply, hk] at hκ1
  have h2 : w.2.2 = 0 := by
    have e := hwm m
    rw [hc.1, hc.2] at e
    have e' : w.2.2 * κ m = 0 := by linear_combination e
    exact (mul_eq_zero.mp e').resolve_right hm
  exact hw0 (Prod.ext hc.1 (Prod.ext hc.2 h2))

theorem t2_partition (κ ν μ : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0) (α β γ : ℂ)
    (hαβ : α ≠ 0 ∨ β ≠ 0) (h : ∀ m, α * ν m + β * μ m + γ * κ m = 0)
    (hν : ∃ a b, ν a / κ a ≠ ν b / κ b) (hμ : ∃ a b, μ a / κ a ≠ μ b / κ b) :
    ∀ m m', ν m / κ m = ν m' / κ m' ↔ μ m / κ m = μ m' / κ m' := by
  have h' : ∀ m, α * (ν m / κ m) + β * (μ m / κ m) + γ = 0 := by
    intro m
    have e1 : ν m / κ m * κ m = ν m := div_mul_cancel₀ _ (hκ0 m)
    have e2 : μ m / κ m * κ m = μ m := div_mul_cancel₀ _ (hκ0 m)
    have e := h m
    have e3 : κ m * (α * (ν m / κ m) + β * (μ m / κ m) + γ) = 0 := by
      linear_combination e + α * e1 + β * e2
    exact (mul_eq_zero.mp e3).resolve_left (hκ0 m)
  obtain ⟨a, b, hab⟩ := hν
  obtain ⟨c, d, hcd⟩ := hμ
  have hβ : β ≠ 0 := by
    intro hβ
    have hα : α ≠ 0 := hαβ.resolve_right (not_not.mpr hβ)
    apply hab
    have e : α * (ν a / κ a - ν b / κ b) = 0 := by
      linear_combination h' a - h' b - (μ a / κ a - μ b / κ b) * hβ
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hα)
  have hα : α ≠ 0 := by
    intro hα
    apply hcd
    have e : β * (μ c / κ c - μ d / κ d) = 0 := by
      linear_combination h' c - h' d - (ν c / κ c - ν d / κ d) * hα
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hβ)
  intro m m'
  constructor
  · intro hmm
    have e : β * (μ m / κ m - μ m' / κ m') = 0 := by
      linear_combination h' m - h' m' - α * hmm
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hβ)
  · intro hmm
    have e : α * (ν m / κ m - ν m' / κ m') = 0 := by
      linear_combination h' m - h' m' - β * hmm
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hα)

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
  have hkk : ∀ m, κ'' m = κ m := by
    have h := dot_zero_of_row hL r1 hrank (fun m => κ'' m + (-1) * κ m)
      (fun t ht => by rw [dotL_comb, hκ''L t ht, hκL t ht]; ring)
      (by rw [dotL_comb, hκ''1, hκ1]; ring)
    intro m
    have e := h m
    linear_combination e
  have hk : κ'' = κ := funext hkk
  rw [hk] at hμc
  rw [hk]
  obtain ⟨α, β, γ, hαβ, h⟩ := t2_dep L r1 r2 r3 κ ν ν' μ μ' hκL hκ1 hνL hμL hdim
  exact t2_partition κ ν μ hκ0 α β γ hαβ h hνc hμc

theorem typeCl_nonconst (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b) :
    ∃ a b, ν a / κ a ≠ ν b / κ b := ⟨a, b, hcl.1⟩

theorem dotL_mul {n : ℕ} (s : ℂ) (μ z : Fin n → ℂ) :
    dotL (fun m => s * μ m) z = s * dotL μ z := by
  rw [dotL_apply, dotL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

def ZFc (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (c : Fin 5) : Prop :=
  4 ≤ Module.finrank ℂ (L.map (colMap c)) ∧
    ∀ κ : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (colMap c t) = 0) → dotL κ 1 = 1 → ∀ i, κ i ≠ 0

theorem dot_zero_of_col {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c : Fin 5)
    (hrank : 4 ≤ Module.finrank ℂ (L.map (colMap c))) (μ : Fin 5 → ℂ)
    (hμL : ∀ t ∈ L, dotL μ (colMap c t) = 0) (hμ1 : dotL μ 1 = 0) : ∀ m, μ m = 0 := by
  have hT : 4 ≤ Module.finrank ℂ ((L.map
      (trE 5 : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ))).map (rowMap c)) := by
    rw [map_tr_row]
    exact hrank
  refine dot_zero_of_row (lev_tr hL) c hT μ (fun t ht => ?_) hμ1
  obtain ⟨t0, ht0, rfl⟩ := ht
  exact hμL t0 ht0

theorem row_rel_zero {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5)
    (hr : ZF L r) (μ : Fin 5 → ℂ) (hμL : ∀ t ∈ L, dotL μ (rowMap r t) = 0) (i : Fin 5)
    (hi : μ i = 0) : ∀ m, μ m = 0 := by
  by_cases hs : dotL μ 1 = 0
  · exact dot_zero_of_row hL r hr.1 μ hμL hs
  · exfalso
    have h1 : ∀ t ∈ L, dotL (fun m => (dotL μ 1)⁻¹ * μ m) (rowMap r t) = 0 := fun t ht => by
      rw [dotL_mul, hμL t ht, mul_zero]
    have h2 : dotL (fun m => (dotL μ 1)⁻¹ * μ m) 1 = 1 := by
      rw [dotL_mul, inv_mul_cancel₀ hs]
    exact hr.2 _ h1 h2 i (by show (dotL μ 1)⁻¹ * μ i = 0; rw [hi, mul_zero])

theorem col_rel_zero {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (c : Fin 5)
    (hc : ZFc L c) (μ : Fin 5 → ℂ) (hμL : ∀ t ∈ L, dotL μ (colMap c t) = 0) (i : Fin 5)
    (hi : μ i = 0) : ∀ m, μ m = 0 := by
  by_cases hs : dotL μ 1 = 0
  · exact dot_zero_of_col hL c hc.1 μ hμL hs
  · exfalso
    have h1 : ∀ t ∈ L, dotL (fun m => (dotL μ 1)⁻¹ * μ m) (colMap c t) = 0 := fun t ht => by
      rw [dotL_mul, hμL t ht, mul_zero]
    have h2 : dotL (fun m => (dotL μ 1)⁻¹ * μ m) 1 = 1 := by
      rw [dotL_mul, inv_mul_cancel₀ hs]
    exact hc.2 _ h1 h2 i (by show (dotL μ 1)⁻¹ * μ i = 0; rw [hi, mul_zero])

theorem exists_other (r r' : Fin 5) : ∃ i, i ≠ r ∧ i ≠ r' := by
  revert r r'
  decide

theorem lone_rel (κ κ' ν ν' z1 z2 : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0) (hκ'0 : ∀ m, κ' m ≠ 0)
    (j : Fin 5) (P P' O O' : ℂ) (hP : ν j / κ j = P) (hP' : ν' j / κ' j = P')
    (hO : ∀ m, m ≠ j → ν m / κ m = O ∧ ν' m / κ' m = O') (hsum : P + P' = O + O')
    (hne : P ≠ O) (h1 : dotL κ z1 = 0) (h2 : dotL κ' z2 = 0)
    (h3 : dotL ν z1 + dotL ν' z2 = 0) : z1 j * κ j = z2 j * κ' j := by
  have s1 : dotL ν z1 - O * dotL κ z1 = (P - O) * (z1 j * κ j) := by
    rw [dotL_apply, dotL_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single j]
    · have e := div_mul_cancel₀ (ν j) (hκ0 j)
      rw [hP] at e
      rw [← e]
      ring
    · intro m _ hm
      have e := div_mul_cancel₀ (ν m) (hκ0 m)
      rw [(hO m hm).1] at e
      rw [← e]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  have s2 : dotL ν' z2 - O' * dotL κ' z2 = (P' - O') * (z2 j * κ' j) := by
    rw [dotL_apply, dotL_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single j]
    · have e := div_mul_cancel₀ (ν' j) (hκ'0 j)
      rw [hP'] at e
      rw [← e]
      ring
    · intro m _ hm
      have e := div_mul_cancel₀ (ν' m) (hκ'0 m)
      rw [(hO m hm).2] at e
      rw [← e]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h4 : (P - O) * (z1 j * κ j - z2 j * κ' j) = 0 := by
    linear_combination h3 - s1 - s2 - O * h1 - O' * h2 - (z2 j * κ' j) * hsum
  have h5 := (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne)
  linear_combination h5

theorem gen0_typeI {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r') (hcol : ∀ c, ZFc L c) (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5)
    (h1 : ∀ t ∈ L, dotL κ (rowMap r t) = 0) (h3 : ∀ t ∈ L, dotL κ' (rowMap r' t) = 0)
    (h5 : ∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0)
    (hκ0 : ∀ j, κ j ≠ 0) (hκ'0 : ∀ j, κ' j ≠ 0) (hcl : TypeCl κ κ' ν ν' a b)
    (hI : ∀ m, ¬ (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b)) (j : Fin 5) :
    ∃ l, l ≠ j ∧ ν l / κ l = ν j / κ j := by
  by_contra hno
  push_neg at hno
  obtain ⟨hab, hab', hσ, hall⟩ := hcl
  have key : ∀ t ∈ L, t (r, j) * κ j = t (r', j) * κ' j := by
    intro t ht
    rcases hall j with hj | hj | hj
    · refine lone_rel κ κ' ν ν' (rowMap r t) (rowMap r' t) hκ0 hκ'0 j (ν a / κ a)
        (ν' a / κ' a) (ν b / κ b) (ν' b / κ' b) hj.1 hj.2.1 (fun m hm => ?_) hσ hab
        (h1 t ht) (h3 t ht) (h5 t ht)
      rcases hall m with hm' | hm' | hm'
      · exact absurd (hm'.1.trans hj.1.symm) (hno m hm)
      · exact ⟨hm'.1, hm'.2.1⟩
      · exact absurd ⟨hm'.1, hm'.2.1⟩ (hI m)
    · refine lone_rel κ κ' ν ν' (rowMap r t) (rowMap r' t) hκ0 hκ'0 j (ν b / κ b)
        (ν' b / κ' b) (ν a / κ a) (ν' a / κ' a) hj.1 hj.2.1 (fun m hm => ?_) hσ.symm
        (Ne.symm hab) (h1 t ht) (h3 t ht) (h5 t ht)
      rcases hall m with hm' | hm' | hm'
      · exact ⟨hm'.1, hm'.2.1⟩
      · exact absurd (hm'.1.trans hj.1.symm) (hno m hm)
      · exact absurd ⟨hm'.1, hm'.2.1⟩ (hI m)
    · exact absurd ⟨hj.1, hj.2.1⟩ (hI j)
  obtain ⟨i0, hi0, hi0'⟩ := exists_other r r'
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin 5 → ℂ, μ = fun i => κ j * (Pi.single r 1 : Fin 5 → ℂ) i -
      κ' j * (Pi.single r' 1 : Fin 5 → ℂ) i := ⟨_, rfl⟩
  have hdot : ∀ z : Fin 5 → ℂ, dotL μ z = κ j * z r - κ' j * z r' := by
    intro z
    rw [dotL_apply]
    have e1 : ∀ i, z i * μ i = κ j * ((Pi.single r 1 : Fin 5 → ℂ) i * z i) -
        κ' j * ((Pi.single r' 1 : Fin 5 → ℂ) i * z i) := by
      intro i
      simp only [hμ]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_single_mul, sum_single_mul]
  have hμL : ∀ t ∈ L, dotL μ (colMap j t) = 0 := by
    intro t ht
    rw [hdot, colMap_apply, colMap_apply]
    linear_combination key t ht
  have hμi0 : μ i0 = 0 := by
    simp only [hμ, Pi.single_eq_of_ne hi0, Pi.single_eq_of_ne hi0', mul_zero, sub_zero]
  have hz := col_rel_zero hL j (hcol j) μ hμL i0 hμi0 r
  simp only [hμ, Pi.single_eq_same, Pi.single_eq_of_ne hr, mul_one, mul_zero, sub_zero] at hz
  exact hκ0 j hz

theorem gen0_pairI {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r r' : Fin 5)
    (hr : r ≠ r') (hcol : ∀ c, ZFc L c) (hp : PairI L r r') :
    ∃ κ κ' ν ν' : Fin 5 → ℂ, ∃ a b : Fin 5,
      (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
      (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧
      (∀ t ∈ L, dotL ν (rowMap r t) + dotL ν' (rowMap r' t) = 0) ∧
      dotL ν 1 + dotL ν' 1 = 0 ∧ (∀ j, κ j ≠ 0) ∧ (∀ j, κ' j ≠ 0) ∧ TypeCl κ κ' ν ν' a b ∧
      (∀ m, ¬ (ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b)) ∧
      ∀ j, ∃ l, l ≠ j ∧ ν l / κ l = ν j / κ j := by
  obtain ⟨κ, κ', ν, ν', a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  exact ⟨κ, κ', ν, ν', a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    gen0_typeI hL r r' hr hcol κ κ' ν ν' a b h1 h3 h5 h7 h8 h9 h10⟩
theorem exists_perm3 (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    ∃ ρ : Equiv.Perm (Fin 5), ρ 0 = r1 ∧ ρ 1 = r2 ∧ ρ 2 = r3 := by
  obtain ⟨ρ, h0, h1⟩ : ∃ ρ : Equiv.Perm (Fin 5), ρ 0 = r1 ∧ ρ 1 = r2 :=
    exists_perm2 (m := 3) r1 r2 h12
  have hy0 : (0 : Fin 5) ≠ ρ.symm r3 := by
    intro h
    apply h13
    rw [← h0, h, Equiv.apply_symm_apply]
  have hy1 : (1 : Fin 5) ≠ ρ.symm r3 := by
    intro h
    apply h23
    rw [← h1, h, Equiv.apply_symm_apply]
  have h02 : (0 : Fin 5) ≠ 2 := by decide
  have h12' : (1 : Fin 5) ≠ 2 := by decide
  refine ⟨(Equiv.swap 2 (ρ.symm r3)).trans ρ, ?_, ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h02 hy0, h0]
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h12' hy1, h1]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

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
  unfold blkL
  rw [Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b => congrFun h2 (a, b)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun p => h2 p.1 p.2⟩

theorem blkL_finrank (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (blkL L r c) + 6 := by
  have h := rank_nullity L (blkMap r c)
  have h2 := Submodule.finrank_le (L.map (blkMap r c))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at h2
  unfold blkL
  omega

theorem ell_ne_of_small {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h9 : Module.finrank ℂ L = 9) (hs : Module.finrank ℂ (blkL L r c) ≤ 3) :
    ∃ w ∈ blockSpace L r c, w.1 ≠ 0 := by
  by_contra hno
  push_neg at hno
  have hge := blockSpace_finrank_ge L r c
  rw [Fintype.card_fin, Fintype.card_fin, h9] at hge
  have hrn := rank_nullity (blockSpace L r c) (LinearMap.snd ℂ ℂ (Fin 5 × Fin 5 → ℂ))
  have hbot : blockSpace L r c ⊓ LinearMap.ker (LinearMap.snd ℂ ℂ (Fin 5 × Fin 5 → ℂ)) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hk⟩
    replace hk := LinearMap.mem_ker.mp hk
    rw [LinearMap.snd_apply] at hk
    rw [Submodule.mem_bot]
    exact Prod.ext (hno w hw) hk
  have hle : (blockSpace L r c).map (LinearMap.snd ℂ ℂ (Fin 5 × Fin 5 → ℂ)) ≤ blkL L r c := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' := hw
    obtain ⟨hw1, hw2⟩ := hw'
    rw [mem_blkL]
    refine ⟨hw1, fun a b => ?_⟩
    have e := hw2 a b
    rw [hno w hw, zero_add] at e
    exact e
  have h1 := Submodule.finrank_mono hle
  rw [hbot, finrank_bot] at hrn
  omega

theorem stest_blk {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5) (hw : ∃ w ∈ blockSpace L r c, w.1 ≠ 0)
    (t : Fin 5 × Fin 5 → ℂ) (ht : t ∈ blkL L r c) :
    blk (fun a => r (Sum.inl a)) (fun a => c (Sum.inl a)) t = 0 := by
  obtain ⟨w0, hw0, hw01⟩ := hw
  obtain ⟨htL, ht0⟩ := (mem_blkL L r c t).mp ht
  rcases t0 hL r c with ⟨k, k', _, hk⟩ | ⟨h0, _⟩
  · have hmem : ((0 : ℂ), t) ∈ blockSpace L r c := by
      rw [mem_blockSpace]
      refine ⟨htL, fun a b => ?_⟩
      show (0 : ℂ) + t (r (Sum.inl a), c (Sum.inr b)) = 0
      rw [zero_add]
      exact ht0 a b
    have h1 := (hk _ hmem).1
    have e : hat 5 ((0 : ℂ), t) = t := by
      funext p
      show (0 : ℂ) + t p = t p
      ring
    rw [e] at h1
    rw [h1]
    simp
  · exact absurd (h0 w0 hw0) hw01

theorem hyper_core (H : Submodule ℂ (Fin 4 → ℂ)) (h3 : 3 ≤ Module.finrank ℂ H)
    (cub : (Fin 4 → ℂ) → ℂ)
    (hcore : ∀ α β1 β2 β3 : ℂ, (∀ t a1 a2 a3 : ℂ, α * t + β1 * a1 + β2 * a2 + β3 * a3 = 0 →
      cub ![t, a1, a2, a3] = 0) → β1 = 0 ∧ β2 = 0 ∧ β3 = 0)
    (hcub : Module.finrank ℂ H ≤ 3 → ∀ x ∈ H, cub x = 0) :
    ∀ x : Fin 4 → ℂ, x 0 = 0 → x ∈ H := by
  intro x0 hx0
  by_contra hn
  obtain ⟨φ, hφx, hφH⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hHφ : H ≤ LinearMap.ker φ := by
    intro y hy
    have h4 : φ y ∈ H.map φ := ⟨y, hy, rfl⟩
    rw [hφH] at h4
    exact (Submodule.mem_bot ℂ).mp h4
  have hne : LinearMap.ker φ ≠ ⊤ := by
    intro h
    apply hφx
    have h5 : x0 ∈ LinearMap.ker φ := by
      rw [h]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp h5
  have hk3 := Submodule.finrank_lt hne
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hk3
  have hm := Submodule.finrank_mono hHφ
  have hH3 : Module.finrank ℂ H ≤ 3 := by omega
  have hHeq : H = LinearMap.ker φ := Submodule.eq_of_le_of_finrank_le hHφ (by omega)
  have hrep : ∀ y : Fin 4 → ℂ, φ y = φ (Pi.single 0 1) * y 0 + φ (Pi.single 1 1) * y 1 +
      φ (Pi.single 2 1) * y 2 + φ (Pi.single 3 1) * y 3 := by
    intro y
    rw [dual_eq_dotL φ y, dotL_apply, Fin.sum_univ_four]
    ring
  have hb := hcore (φ (Pi.single 0 1)) (φ (Pi.single 1 1)) (φ (Pi.single 2 1))
    (φ (Pi.single 3 1)) (fun t a1 a2 a3 h => by
      apply hcub hH3
      rw [hHeq, LinearMap.mem_ker, hrep]
      exact h)
  apply hφx
  rw [hrep, hb.1, hb.2.1, hb.2.2, hx0]
  ring

theorem t2_alg (k x : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0) (d2 d3 : ℂ) (hd2 : d2 ≠ 0)
    (hd3 : d3 ≠ 0) (hk1 : k 1 0 = d2 * k 0 0 ∧ k 1 1 = -d2 * k 0 1 ∧ k 1 2 = -d2 * k 0 2)
    (hk2 : k 2 0 = d3 * k 0 0 ∧ k 2 1 = -d3 * k 0 1 ∧ k 2 2 = -d3 * k 0 2) (T A1 A2 A3 : ℂ)
    (h0 : ∀ i, k i 0 * x i 0 = T) (h1 : k 0 1 * x 0 1 = A1) (h2 : k 1 1 * x 1 1 = A2)
    (h3 : k 2 1 * x 2 1 = A3) (hs : ∀ i, k i 0 * x i 0 + k i 1 * x i 1 + k i 2 * x i 2 = 0) :
    (d2 * d3 * k 0 0 * k 0 1 * k 0 2) * (Matrix.of x).permanent =
      2 * T * (T * A1 + A1 * A2 + A1 * A3 - A2 * A3) := by
  have q00 : x 0 0 = T / k 0 0 := by
    rw [eq_div_iff (hk 0 0)]
    linear_combination h0 0
  have q01 : x 0 1 = A1 / k 0 1 := by
    rw [eq_div_iff (hk 0 1)]
    linear_combination h1
  have q02 : x 0 2 = (-T - A1) / k 0 2 := by
    rw [eq_div_iff (hk 0 2)]
    linear_combination hs 0 - h0 0 - h1
  have q10 : x 1 0 = T / k 1 0 := by
    rw [eq_div_iff (hk 1 0)]
    linear_combination h0 1
  have q11 : x 1 1 = A2 / k 1 1 := by
    rw [eq_div_iff (hk 1 1)]
    linear_combination h2
  have q12 : x 1 2 = (-T - A2) / k 1 2 := by
    rw [eq_div_iff (hk 1 2)]
    linear_combination hs 1 - h0 1 - h2
  have q20 : x 2 0 = T / k 2 0 := by
    rw [eq_div_iff (hk 2 0)]
    linear_combination h0 2
  have q21 : x 2 1 = A3 / k 2 1 := by
    rw [eq_div_iff (hk 2 1)]
    linear_combination h3
  have q22 : x 2 2 = (-T - A3) / k 2 2 := by
    rw [eq_div_iff (hk 2 2)]
    linear_combination hs 2 - h0 2 - h3
  obtain ⟨a1, a2, a3⟩ := hk1
  obtain ⟨b1, b2, b3⟩ := hk2
  have n0 := hk 0 0
  have n1 := hk 0 1
  have n2 := hk 0 2
  rw [permanent_three]
  simp only [Matrix.of_apply]
  rw [q00, q01, q02, q10, q11, q12, q20, q21, q22, a1, a2, a3, b1, b2, b3]
  field_simp
  ring

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
    (i : Fin 4) : lam4 w P t i = w i * t (P i) := rfl

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
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ), Λ = lam4
      ![k 0 0, k 0 1, k 1 1, k 2 1]
      ![(r (Sum.inl 0), c (Sum.inl 0)), (r (Sum.inl 0), c (Sum.inl 1)),
        (r (Sum.inl 1), c (Sum.inl 1)), (r (Sum.inl 2), c (Sum.inl 1))] := ⟨_, rfl⟩
  have hΛ0 : ∀ t, Λ t 0 = k 0 0 * t (r (Sum.inl 0), c (Sum.inl 0)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hΛ1 : ∀ t, Λ t 1 = k 0 1 * t (r (Sum.inl 0), c (Sum.inl 1)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hΛ2 : ∀ t, Λ t 2 = k 1 1 * t (r (Sum.inl 1), c (Sum.inl 1)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hΛ3 : ∀ t, Λ t 3 = k 2 1 * t (r (Sum.inl 2), c (Sum.inl 1)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hT : ∀ t ∈ blkL L r c, ∀ i : Fin 3, k i 0 * t (r (Sum.inl i), c (Sum.inl 0)) = Λ t 0 :=
    fun t ht i => by
      rw [hΛ0]
      exact (hrel t ht i).1
  obtain ⟨H, hH⟩ : ∃ H : Submodule ℂ (Fin 4 → ℂ), H = (blkL L r c).map Λ := ⟨_, rfl⟩
  have hinj : blkL L r c ⊓ LinearMap.ker Λ = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨ht, hk0⟩
    replace hk0 := LinearMap.mem_ker.mp hk0
    rw [Submodule.mem_bot]
    have z : ∀ i, Λ t i = 0 := fun i => congrFun hk0 i
    apply h0 t ht
    intro i j
    have e0 : k i 0 * t (r (Sum.inl i), c (Sum.inl 0)) = 0 := by rw [hT t ht i, z 0]
    have e1 : k i 1 * t (r (Sum.inl i), c (Sum.inl 1)) = 0 := by
      rcases fin3_cases i with rfl | rfl | rfl
      · rw [← hΛ1 t, z 1]
      · rw [← hΛ2 t, z 2]
      · rw [← hΛ3 t, z 3]
    have e2 : k i 2 * t (r (Sum.inl i), c (Sum.inl 2)) = 0 := by
      have e3 := (hrel t ht i).2
      rw [e0, e1] at e3
      linear_combination e3
    rcases fin3_cases j with rfl | rfl | rfl
    · exact (mul_eq_zero.mp e0).resolve_left (hk i 0)
    · exact (mul_eq_zero.mp e1).resolve_left (hk i 1)
    · exact (mul_eq_zero.mp e2).resolve_left (hk i 2)
  have hrn := rank_nullity (blkL L r c) Λ
  rw [hinj, finrank_bot, zero_add, ← hH] at hrn
  have hb3 := blkL_finrank L r c
  rw [h9] at hb3
  have hH3 : 3 ≤ Module.finrank ℂ H := by omega
  have hcub : Module.finrank ℂ H ≤ 3 → ∀ x ∈ H,
      2 * x 0 * (x 0 * x 1 + x 1 * x 2 + x 1 * x 3 - x 2 * x 3) = 0 := by
    intro hle x hx
    rw [hH] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hw := ell_ne_of_small r c h9 (by omega)
    have hb := stest_blk hL r c hw t ht
    have hb' : (Matrix.of fun i j => t (r (Sum.inl i), c (Sum.inl j))).permanent = 0 := hb
    have halg := t2_alg k (fun i j => t (r (Sum.inl i), c (Sum.inl j))) hk d2 d3 hd2 hd3 hk1 hk2
      (Λ t 0) (Λ t 1) (Λ t 2) (Λ t 3) (fun i => hT t ht i) (hΛ1 t).symm (hΛ2 t).symm
      (hΛ3 t).symm (fun i => (hrel t ht i).2)
    rw [hb', mul_zero] at halg
    linear_combination -halg
  have hall := hyper_core H hH3 (fun x => 2 * x 0 * (x 0 * x 1 + x 1 * x 2 + x 1 * x 3 - x 2 * x 3))
    (fun α β1 β2 β3 h => t2_core α β1 β2 β3 (fun t a1 a2 a3 h' => h t a1 a2 a3 h'))
    hcub
  have hx : (![0, a 0, a 1, a 2] : Fin 4 → ℂ) ∈ (blkL L r c).map Λ := by
    rw [← hH]
    exact hall ![0, a 0, a 1, a 2] rfl
  obtain ⟨t, ht, htx⟩ := hx
  have z0 : Λ t 0 = 0 := congrFun htx 0
  have z1 : Λ t 1 = a 0 := congrFun htx 1
  have z2 : Λ t 2 = a 1 := congrFun htx 2
  have z3 : Λ t 3 = a 2 := congrFun htx 3
  refine ⟨t, ht, fun i => ?_⟩
  have e0 : k i 0 * t (r (Sum.inl i), c (Sum.inl 0)) = 0 := by rw [hT t ht i, z0]
  have e1 : k i 1 * t (r (Sum.inl i), c (Sum.inl 1)) = a i := by
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [← hΛ1 t, z1]
    · rw [← hΛ2 t, z2]
    · rw [← hΛ3 t, z3]
  refine ⟨(mul_eq_zero.mp e0).resolve_left (hk i 0), e1, ?_⟩
  have e3 := (hrel t ht i).2
  rw [e0, e1] at e3
  linear_combination e3

noncomputable def evalPair (q0 q1 : Fin 5) : Module.Dual ℂ (Fin 5 → ℂ) →ₗ[ℂ] ℂ × ℂ where
  toFun φ := (φ (Pi.single q0 1), φ (Pi.single q1 1))
  map_add' φ ψ := rfl
  map_smul' k φ := rfl

theorem span_classes (R : Submodule ℂ (Fin 5 → ℂ)) (C : Finset (Fin 5)) (q0 q1 : Fin 5)
    (hq0 : q0 ∈ C) (hq1 : q1 ∉ C) (κ : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0)
    (hR : ∀ q s, q ≠ s → (q ∈ C ↔ s ∈ C) →
      (κ q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈ R) :
    3 ≤ Module.finrank ℂ R := by
  have hdual := Subspace.finrank_add_finrank_dualAnnihilator_eq R
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdual
  have hrn := rank_nullity R.dualAnnihilator (evalPair q0 q1)
  have hle := Submodule.finrank_le (R.dualAnnihilator.map (evalPair q0 q1))
  rw [Module.finrank_prod, Module.finrank_self] at hle
  have hbot : R.dualAnnihilator ⊓ LinearMap.ker (evalPair q0 q1) = ⊥ := by
    rw [eq_bot_iff]
    rintro φ ⟨hφ, hk⟩
    replace hφ := (Submodule.mem_dualAnnihilator φ).mp hφ
    replace hk := LinearMap.mem_ker.mp hk
    have e0 : φ (Pi.single q0 1) = 0 := congrArg Prod.fst hk
    have e1 : φ (Pi.single q1 1) = 0 := congrArg Prod.snd hk
    have hall : ∀ m, φ (Pi.single m 1) = 0 := by
      intro m
      by_cases hmC : m ∈ C
      · by_cases hm : m = q0
        · rw [hm]
          exact e0
        · have h1 := hφ _ (hR m q0 hm ⟨fun _ => hq0, fun _ => hmC⟩)
          rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, e0, mul_zero,
            sub_zero] at h1
          exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero (hκ0 m))
      · by_cases hm : m = q1
        · rw [hm]
          exact e1
        · have h1 := hφ _ (hR m q1 hm ⟨fun h => absurd h hmC, fun h => absurd h hq1⟩)
          rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, e1, mul_zero,
            sub_zero] at h1
          exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero (hκ0 m))
    rw [Submodule.mem_bot]
    apply LinearMap.ext
    intro z
    rw [dual_eq_dotL φ z, dotL_apply, LinearMap.zero_apply]
    simp [hall]
  rw [hbot, finrank_bot, zero_add] at hrn
  omega
theorem fk_unique {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r : Fin 5)
    (hrank : 4 ≤ Module.finrank ℂ (L.map (rowMap r))) (κ κ' : Fin 5 → ℂ)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r t) = 0) (hκ1 : dotL κ 1 = 1)
    (hκ'L : ∀ t ∈ L, dotL κ' (rowMap r t) = 0) (hκ'1 : dotL κ' 1 = 1) : κ' = κ := by
  have h := dot_zero_of_row hL r hrank (fun m => κ' m + (-1) * κ m)
    (fun t ht => by rw [dotL_comb, hκ'L t ht, hκL t ht]; ring)
    (by rw [dotL_comb, hκ'1, hκ1]; ring)
  funext m
  have e := h m
  linear_combination e

theorem exists_equiv3 (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    ∃ e : Fin 3 ⊕ Fin 2 ≃ Fin 5, e (Sum.inl 0) = r1 ∧ e (Sum.inl 1) = r2 ∧
      e (Sum.inl 2) = r3 := by
  obtain ⟨ρ, h0, h1, h2⟩ := exists_perm3 r1 r2 r3 h12 h13 h23
  refine ⟨(finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5).trans ρ, ?_, ?_, ?_⟩
  · rw [Equiv.trans_apply, finSumFinEquiv_apply_left]
    exact h0
  · rw [Equiv.trans_apply, finSumFinEquiv_apply_left]
    exact h1
  · rw [Equiv.trans_apply, finSumFinEquiv_apply_left]
    exact h2

theorem sum_supp3 (c : Fin 3 ⊕ Fin 2 ≃ Fin 5) (f : Fin 5 → ℂ)
    (hf : ∀ b, f (c (Sum.inr b)) = 0) :
    ∑ m, f m = f (c (Sum.inl 0)) + f (c (Sum.inl 1)) + f (c (Sum.inl 2)) := by
  rw [← Equiv.sum_comp c f, Fintype.sum_sum_type, Fin.sum_univ_three]
  simp [hf]

theorem sum_C_supp3 (c : Fin 3 ⊕ Fin 2 ≃ Fin 5) (C : Finset (Fin 5)) (f : Fin 5 → ℂ)
    (hf : ∀ b, f (c (Sum.inr b)) = 0) :
    ∑ m ∈ C, f m = (if c (Sum.inl 0) ∈ C then f (c (Sum.inl 0)) else 0) +
      (if c (Sum.inl 1) ∈ C then f (c (Sum.inl 1)) else 0) +
      (if c (Sum.inl 2) ∈ C then f (c (Sum.inl 2)) else 0) := by
  have e : ∑ m ∈ C, f m = ∑ m, if m ∈ C then f m else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [e]
  exact sum_supp3 c (fun m => if m ∈ C then f m else 0) (fun b => by simp [hf b])

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
  have hcl0 := hcl
  obtain ⟨hab, hab', hσ, hall⟩ := hcl0
  have hA : ∀ m, m ∉ C → ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' a / κ' a ∧
      κ' m / κ m = κ' a / κ a := by
    intro m hm
    rcases hall m with h | h | h
    · exact h
    · exact absurd ((hC m).mpr h.1) hm
    · exact absurd ⟨h.1, h.2.1⟩ (hI m)
  have hB : ∀ m, m ∈ C → ν m / κ m = ν b / κ b ∧ ν' m / κ' m = ν' b / κ' b ∧
      κ' m / κ m = - (κ' a / κ a) := by
    intro m hm
    rcases hall m with h | h | h
    · exact absurd (h.1.symm.trans ((hC m).mp hm)) hab
    · exact h
    · exact absurd ⟨h.1, h.2.1⟩ (hI m)
  refine ⟨⟨κ' a / κ a, div_ne_zero (hκ'0 a) (hκ0 a), fun m hm => ?_, fun m hm => ?_⟩,
    fun t ht => ?_, fun m => ⟨fun hm => (hA m hm).1,
      fun h hm => hab (h.symm.trans ((hC m).mp hm))⟩⟩
  · have e := (hA m hm).2.2
    rw [div_eq_iff (hκ0 m)] at e
    exact e
  · have e := (hB m hm).2.2
    rw [div_eq_iff (hκ0 m)] at e
    linear_combination e
  · have hnf := c7_nf κ κ' ν ν' hκ0 hκ'0 a b hcl (Finset.univ.filter (fun m => m ∉ C)) C
      (fun m => ⟨fun hm => (hA m (Finset.mem_filter.mp hm).2).2.1,
        fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ m,
          fun hmC => hab' (h.symm.trans (hB m hmC).2.1)⟩⟩)
      hC (rowMap r t) (rowMap r' t) (hκL t ht) (hκ'L t ht) (hνL t ht)
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => m ∈ C)
      (fun m => rowMap r' t m * κ' m)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at hsplit
    have hfk := hκ'L t ht
    rw [dotL_apply] at hfk
    simp only [rowMap_apply] at hnf hsplit hfk
    linear_combination hnf - hsplit - hfk

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
  obtain ⟨rr, hr0, hr1, hr2⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 p q s hpq hps hqs
  obtain ⟨d2, d3, hd2, hd3, hk1, hk2⟩ : ∃ d2 d3 : ℂ, d2 ≠ 0 ∧ d3 ≠ 0 ∧
      (κ2 p = d2 * κ p ∧ κ2 q = -d2 * κ q ∧ κ2 s = -d2 * κ s) ∧
      (κ3 p = d3 * κ p ∧ κ3 q = -d3 * κ q ∧ κ3 s = -d3 * κ s) := by
    rcases hcls with ⟨hp, hq, hs⟩ | ⟨hp, hq, hs⟩
    · exact ⟨f2, f3, hf2, hf3, ⟨hf2a p hp, hf2b q hq, hf2b s hs⟩,
        ⟨hf3a p hp, hf3b q hq, hf3b s hs⟩⟩
    · refine ⟨-f2, -f3, neg_ne_zero.mpr hf2, neg_ne_zero.mpr hf3,
        ⟨hf2b p hp, ?_, ?_⟩, ⟨hf3b p hp, ?_, ?_⟩⟩
      · rw [hf2a q hq]
        ring
      · rw [hf2a s hs]
        ring
      · rw [hf3a q hq]
        ring
      · rw [hf3a s hs]
        ring
  have hv : ∀ t ∈ blkL L rr cc, ∀ b, t (r1, cc (Sum.inr b)) = 0 ∧
      t (r2, cc (Sum.inr b)) = 0 ∧ t (r3, cc (Sum.inr b)) = 0 := by
    intro t ht b
    have h := ((mem_blkL L rr cc t).mp ht).2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr0]
      exact h 0 b
    · rw [← hr1]
      exact h 1 b
    · rw [← hr2]
      exact h 2 b
  have hrs : ∀ t ∈ blkL L rr cc,
      t (r1, p) * κ p + t (r1, q) * κ q + t (r1, s) * κ s = 0 ∧
      t (r2, p) * κ2 p + t (r2, q) * κ2 q + t (r2, s) * κ2 s = 0 ∧
      t (r3, p) * κ3 p + t (r3, q) * κ3 q + t (r3, s) * κ3 s = 0 := by
    intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have e1 := sum_supp3 cc (fun m => t (r1, m) * κ m)
      (fun b => by simp only [(hv t ht b).1, zero_mul])
    have e2 := sum_supp3 cc (fun m => t (r2, m) * κ2 m)
      (fun b => by simp only [(hv t ht b).2.1, zero_mul])
    have e3 := sum_supp3 cc (fun m => t (r3, m) * κ3 m)
      (fun b => by simp only [(hv t ht b).2.2, zero_mul])
    rw [hc0, hc1, hc2] at e1 e2 e3
    refine ⟨?_, ?_, ?_⟩
    · rw [← e1]
      exact hκL t htL
    · rw [← e2]
      exact hκ2L t htL
    · rw [← e3]
      exact hκ3L t htL
  have hcs : ∀ t ∈ blkL L rr cc, t (r2, p) * κ2 p = t (r1, p) * κ p ∧
      t (r3, p) * κ3 p = t (r1, p) * κ p := by
    intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    obtain ⟨R1, R2, R3⟩ := hrs t ht
    have A2 := hrel2 t htL
    have A3 := hrel3 t htL
    rw [sum_C_supp3 cc C (fun m => t (r1, m) * κ m)
        (fun b => by simp only [(hv t ht b).1, zero_mul]),
      sum_C_supp3 cc C (fun m => t (r2, m) * κ2 m)
        (fun b => by simp only [(hv t ht b).2.1, zero_mul]), hc0, hc1, hc2] at A2
    rw [sum_C_supp3 cc C (fun m => t (r1, m) * κ m)
        (fun b => by simp only [(hv t ht b).1, zero_mul]),
      sum_C_supp3 cc C (fun m => t (r3, m) * κ3 m)
        (fun b => by simp only [(hv t ht b).2.2, zero_mul]), hc0, hc1, hc2] at A3
    rcases hcls with ⟨hp, hq, hs⟩ | ⟨hp, hq, hs⟩
    · simp only [hp, hq, hs, ite_true, ite_false, zero_add] at A2 A3
      exact ⟨by linear_combination R2 - R1 + A2, by linear_combination R3 - R1 + A3⟩
    · simp only [hp, hq, hs, ite_true, ite_false, add_zero] at A2 A3
      exact ⟨by linear_combination -A2, by linear_combination -A3⟩
  obtain ⟨K, hK⟩ : ∃ K : Fin 3 → Fin 5 → ℂ, K = ![κ, κ2, κ3] := ⟨_, rfl⟩
  have hK0 : K 0 = κ := by first | (rw [hK]; rfl) | rw [hK]
  have hK1 : K 1 = κ2 := by first | (rw [hK]; rfl) | rw [hK]
  have hK2 : K 2 = κ3 := by first | (rw [hK]; rfl) | rw [hK]
  have hk : ∀ i j, K i (cc (Sum.inl j)) ≠ 0 := by
    intro i j
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0]
      exact hκ0 _
    · rw [hK1]
      exact hκ20 _
    · rw [hK2]
      exact hκ30 _
  have hk1' : K 1 (cc (Sum.inl 0)) = d2 * K 0 (cc (Sum.inl 0)) ∧
      K 1 (cc (Sum.inl 1)) = -d2 * K 0 (cc (Sum.inl 1)) ∧
      K 1 (cc (Sum.inl 2)) = -d2 * K 0 (cc (Sum.inl 2)) := by
    rw [hK0, hK1, hc0, hc1, hc2]
    exact hk1
  have hk2' : K 2 (cc (Sum.inl 0)) = d3 * K 0 (cc (Sum.inl 0)) ∧
      K 2 (cc (Sum.inl 1)) = -d3 * K 0 (cc (Sum.inl 1)) ∧
      K 2 (cc (Sum.inl 2)) = -d3 * K 0 (cc (Sum.inl 2)) := by
    rw [hK0, hK2, hc0, hc1, hc2]
    exact hk2
  have hrel' : ∀ t ∈ blkL L rr cc, ∀ i : Fin 3,
      K i (cc (Sum.inl 0)) * t (rr (Sum.inl i), cc (Sum.inl 0)) =
        K 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) ∧
      K i (cc (Sum.inl 0)) * t (rr (Sum.inl i), cc (Sum.inl 0)) +
        K i (cc (Sum.inl 1)) * t (rr (Sum.inl i), cc (Sum.inl 1)) +
        K i (cc (Sum.inl 2)) * t (rr (Sum.inl i), cc (Sum.inl 2)) = 0 := by
    intro t ht i
    obtain ⟨R1, R2, R3⟩ := hrs t ht
    obtain ⟨C2, C3⟩ := hcs t ht
    rw [hc0, hc1, hc2, hK0, hr0]
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0, hr0]
      exact ⟨rfl, by linear_combination R1⟩
    · rw [hK1, hr1]
      exact ⟨by linear_combination C2, by linear_combination R2⟩
    · rw [hK2, hr2]
      exact ⟨by linear_combination C3, by linear_combination R3⟩
  have h0' : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0 := by
    intro t ht hz
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have hmem : t ∈ rowsZeroS L {r1, r2, r3} := by
      refine ⟨htL, fun r hr m => ?_⟩
      have hri : ∃ i, rr (Sum.inl i) = r := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with h | h | h
        · exact ⟨0, hr0.trans h.symm⟩
        · exact ⟨1, hr1.trans h.symm⟩
        · exact ⟨2, hr2.trans h.symm⟩
      obtain ⟨i, rfl⟩ := hri
      obtain ⟨y, rfl⟩ := cc.surjective m
      rcases y with j | b
      · exact hz i j
      · exact ((mem_blkL L rr cc t).mp ht).2 i b
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨t, ht, hti⟩ := t2_stest hL h9 rr cc h0' (fun i j => K i (cc (Sum.inl j))) hk d2 d3
    hd2 hd3 hk1' hk2' hrel' ![0, 1, 0]
  have htL := ((mem_blkL L rr cc t).mp ht).1
  have hti0 := hti 0
  have hti1 := hti 1
  have hti2 := hti 2
  rw [hK0, hr0, hc0, hc1, hc2] at hti0
  rw [hK1, hr1, hc0, hc1, hc2] at hti1
  rw [hK2, hr2, hc0, hc1, hc2] at hti2
  obtain ⟨u0, u1, u2⟩ := hti0
  obtain ⟨v0, v1, v2⟩ := hti1
  obtain ⟨w0, w1, w2⟩ := hti2
  have u1' : κ q * t (r1, q) = 0 := u1
  have u2' : κ s * t (r1, s) = 0 := by
    have h : κ s * t (r1, s) = -(0 : ℂ) := u2
    rw [h, neg_zero]
  have v1' : κ2 q * t (r2, q) = 1 := v1
  have v2' : κ2 s * t (r2, s) = -1 := v2
  have w1' : κ3 q * t (r3, q) = 0 := w1
  have w2' : κ3 s * t (r3, s) = 0 := by
    have h : κ3 s * t (r3, s) = -(0 : ℂ) := w2
    rw [h, neg_zero]
  have zrow : ∀ m, m ≠ p → m ≠ q → m ≠ s → ∃ b, cc (Sum.inr b) = m := by
    intro m h1 h2 h3
    obtain ⟨y, rfl⟩ := cc.surjective m
    rcases y with j | b
    · rcases fin3_cases j with rfl | rfl | rfl
      · exact absurd hc0 h1
      · exact absurd hc1 h2
      · exact absurd hc2 h3
    · exact ⟨b, rfl⟩
  have hrow13 : ∀ m, t (r1, m) = 0 ∧ t (r3, m) = 0 := by
    intro m
    by_cases hmp : m = p
    · rw [hmp]
      exact ⟨u0, w0⟩
    by_cases hmq : m = q
    · rw [hmq]
      exact ⟨(mul_eq_zero.mp u1').resolve_left (hκ0 q),
        (mul_eq_zero.mp w1').resolve_left (hκ30 q)⟩
    by_cases hms : m = s
    · rw [hms]
      exact ⟨(mul_eq_zero.mp u2').resolve_left (hκ0 s),
        (mul_eq_zero.mp w2').resolve_left (hκ30 s)⟩
    obtain ⟨b, rfl⟩ := zrow m hmp hmq hms
    exact ⟨(hv t ht b).1, (hv t ht b).2.2⟩
  refine ⟨t, ⟨htL, fun r hr j => ?_⟩, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h
    · rw [h]
      exact (hrow13 j).1
    · rw [h]
      exact (hrow13 j).2
  · funext m
    rw [rowMap_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hmp : m = p
    · rw [hmp, v0, Pi.single_eq_of_ne hpq, Pi.single_eq_of_ne hps]
      ring
    by_cases hmq : m = q
    · rw [hmq, Pi.single_eq_same, Pi.single_eq_of_ne hqs]
      have hq0 := hκ20 q
      have e : t (r2, q) = (κ2 q)⁻¹ := by
        field_simp
        linear_combination v1'
      rw [e]
      ring
    by_cases hms : m = s
    · rw [hms, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hqs)]
      have hs0 := hκ20 s
      have e : t (r2, s) = -(κ2 s)⁻¹ := by
        field_simp
        linear_combination v2'
      rw [e]
      ring
    rw [Pi.single_eq_of_ne hmq, Pi.single_eq_of_ne hms]
    obtain ⟨b, rfl⟩ := zrow m hmp hmq hms
    rw [(hv t ht b).2.1]
    ring

theorem t2_proof : T2Hyp := by
  intro L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 hp hq h0
  obtain ⟨κ, κ2, ν, ν', a, b, hκL, hκ1, hκ2L, hκ21, hνL, hν1, hκ0, hκ20, hcl, hI⟩ := hp
  obtain ⟨κ', κ3, μ, μ', a', b', hκ'L, hκ'1, hκ3L, hκ31, hμL, hμ1, hκ'0, hκ30, hcl', hI'⟩ := hq
  have hkk : κ = κ' := (fk_unique hL r1 z1.1 κ κ' hκL hκ1 hκ'L hκ'1).symm
  subst hkk
  have hX0 : Module.finrank ℂ (rowsZeroS L {r1, r2, r3}) = 0 := by
    rw [h0, finrank_bot]
  have hpart := t2_split hL r1 r2 r3 z1.1 (by omega) κ ν ν' hκ0 hκL hκ1 hνL ⟨a, b, hcl.1⟩
    κ μ μ' hκL hκ1 hμL ⟨a', b', hcl'.1⟩
  classical
  obtain ⟨C, hC⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ν m / κ m = ν b / κ b :=
    ⟨Finset.univ.filter (fun m => ν m / κ m = ν b / κ b), fun m => by simp⟩
  obtain ⟨C', hC'⟩ : ∃ C' : Finset (Fin 5), ∀ m, m ∈ C' ↔ μ m / κ m = μ b' / κ b' :=
    ⟨Finset.univ.filter (fun m => μ m / κ m = μ b' / κ b'), fun m => by simp⟩
  obtain ⟨⟨f2, hf2, hf2a, hf2b⟩, hrel2, hCa⟩ :=
    typeI_nf r1 r2 κ κ2 ν ν' a b hκL hκ2L hνL hκ0 hκ20 hcl hI C hC
  obtain ⟨⟨f3, hf3, hf3a, hf3b⟩, hrel3, hC'a⟩ :=
    typeI_nf r1 r3 κ κ3 μ μ' a' b' hκL hκ3L hμL hκ0 hκ30 hcl' hI' C' hC'
  have hCC : (∀ m, m ∈ C' ↔ m ∈ C) ∨ (∀ m, m ∈ C' ↔ m ∉ C) := by
    by_cases hb' : b' ∈ C
    · left
      intro m
      rw [hC', ← hpart m b', hC m]
      have e := (hC b').mp hb'
      exact ⟨fun h => h.trans e, fun h => h.trans e.symm⟩
    · right
      intro m
      rw [hC', ← hpart m b', hCa m]
      have e := (hCa b').mp hb'
      exact ⟨fun h => h.trans e, fun h => h.trans e.symm⟩
  have h3data : (∃ g3 : ℂ, g3 ≠ 0 ∧ (∀ m, m ∉ C → κ3 m = g3 * κ m) ∧
      (∀ m, m ∈ C → κ3 m = -g3 * κ m)) ∧
      (∀ t ∈ L, ∑ m ∈ C, t (r1, m) * κ m = ∑ m ∈ C, t (r3, m) * κ3 m) := by
    rcases hCC with hCC | hCC
    · have e : C' = C := Finset.ext hCC
      rw [e] at hf3a hf3b hrel3
      exact ⟨⟨f3, hf3, hf3a, hf3b⟩, hrel3⟩
    · have e : C' = Cᶜ := Finset.ext fun m => by rw [hCC m, Finset.mem_compl]
      rw [e] at hf3a hf3b hrel3
      refine ⟨⟨-f3, neg_ne_zero.mpr hf3, fun m hm => ?_, fun m hm => ?_⟩, fun t ht => ?_⟩
      · rw [hf3b m (Finset.mem_compl.mpr hm)]
      · rw [hf3a m (fun h => (Finset.mem_compl.mp h) hm)]
        ring
      · have e1 := hrel3 t ht
        have s1 := Finset.sum_compl_add_sum C (fun m => t (r1, m) * κ m)
        have s3 := Finset.sum_compl_add_sum C (fun m => t (r3, m) * κ3 m)
        have f1 := hκL t ht
        have f3' := hκ3L t ht
        rw [dotL_apply] at f1 f3'
        simp only [rowMap_apply] at f1 f3'
        linear_combination -e1 + s1 - s3 + f1 - f3'
  obtain ⟨⟨g3, hg3, hg3a, hg3b⟩, hrel3'⟩ := h3data
  have hbC : b ∈ C := (hC b).mpr rfl
  have haC : a ∉ C := (hCa a).mpr rfl
  have hR := span_classes ((rowsZeroS L {r1, r3}).map (rowMap r2)) C b a hbC haC κ2 hκ20
    (fun q s hqs hiff => by
      by_cases hq : q ∈ C
      · have hs : s ∈ C := hiff.mp hq
        exact t2_gen_vec hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L C
          f2 g3 hf2 hg3 hf2a hf2b hg3a hg3b hrel2 hrel3' a q s
          (fun h => haC (by rw [h]; exact hq)) (fun h => haC (by rw [h]; exact hs)) hqs
          (Or.inl ⟨haC, hq, hs⟩)
      · have hs : s ∉ C := fun h => hq (hiff.mpr h)
        exact t2_gen_vec hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L C
          f2 g3 hf2 hg3 hf2a hf2b hg3a hg3b hrel2 hrel3' b q s
          (fun h => hq (by rw [← h]; exact hbC)) (fun h => hs (by rw [← h]; exact hbC)) hqs
          (Or.inr ⟨hbC, hq, hs⟩))
  have hle := Submodule.finrank_map_le (rowMap r2) (rowsZeroS L {r1, r3})
  omega
theorem s2_noT2 (hT1 : T1Hyp) (hT2pp : T2ppHyp)
    {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (z1 : ZF L r1)
    (z2 : ZF L r2) (z3 : ZF L r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) :
    (Module.finrank ℂ (rowsZeroS L {r2, r3}) = 3 ∧ PairII L r1 r2 ∧ PairII L r1 r3) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r3}) = 3 ∧ PairII L r2 r1 ∧ PairII L r2 r3) ∨
      (Module.finrank ℂ (rowsZeroS L {r1, r2}) = 3 ∧ PairII L r3 r1 ∧ PairII L r3 r2) :=
  s2 hT1 t2_proof hT2pp hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 h0

theorem s2_star_noT2 (hT1 : T1Hyp) (hT2pp : T2ppHyp) (hR31 : R31Hyp)
    {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)
    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) (z1 : ZF L r1)
    (z2 : ZF L r2) (z3 : ZF L r3) : rowsZeroS L {r1, r2, r3} ≠ ⊥ :=
  s2_star hT1 t2_proof hT2pp hR31 hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3

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
  have hcl0 := hcl
  obtain ⟨hab, hab', hσ, hall⟩ := hcl0
  refine ⟨fun m hm hmB => ?_, fun m hm => ?_, fun m hm => ?_, fun m hm hm2 => ?_,
    fun t ht => ?_⟩
  · have h1 := (hQ2 m).mp hm
    have h2 := (hB m).mp hmB
    rcases hall m with h | h | h
    · exact hab (h.1.symm.trans h2)
    · exact hab' (h1.symm.trans h.2.1)
    · exact hab (h.1.symm.trans h2)
  · have h1 := (hQ2 m).mp hm
    rcases hall m with h | h | h
    · have e := h.2.2
      rw [div_eq_iff (hκ0 m)] at e
      exact e
    · exact absurd (h1.symm.trans h.2.1) hab'
    · exact absurd (h1.symm.trans h.2.1) hab'
  · have h2 := (hB m).mp hm
    rcases hall m with h | h | h
    · exact absurd (h.1.symm.trans h2) hab
    · have e := h.2.2
      rw [div_eq_iff (hκ0 m)] at e
      linear_combination e
    · exact absurd (h.1.symm.trans h2) hab
  · rcases hall m with h | h | h
    · exact absurd ((hQ2 m).mpr h.2.1) hm2
    · exact absurd ((hB m).mpr h.1) hm
    · exact h.2.2.2.1
  · have hnf := c7_nf κ κ' ν ν' hκ0 hκ'0 a b hcl Q2 B hQ2 hB (rowMap r t) (rowMap r' t)
      (hκL t ht) (hκ'L t ht) (hνL t ht)
    simp only [rowMap_apply] at hnf
    exact hnf

theorem hyper_top (H : Submodule ℂ (Fin 4 → ℂ)) (h3 : 3 ≤ Module.finrank ℂ H)
    (cub : (Fin 4 → ℂ) → ℂ)
    (hcore : ∀ α β1 β2 β3 : ℂ, (∀ t a1 a2 a3 : ℂ, α * t + β1 * a1 + β2 * a2 + β3 * a3 = 0 →
      cub ![t, a1, a2, a3] = 0) → False)
    (hcub : Module.finrank ℂ H ≤ 3 → ∀ x ∈ H, cub x = 0) :
    ∀ x : Fin 4 → ℂ, x ∈ H := by
  intro x0
  by_contra hn
  obtain ⟨φ, hφx, hφH⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hHφ : H ≤ LinearMap.ker φ := by
    intro y hy
    have h4 : φ y ∈ H.map φ := ⟨y, hy, rfl⟩
    rw [hφH] at h4
    exact (Submodule.mem_bot ℂ).mp h4
  have hne : LinearMap.ker φ ≠ ⊤ := by
    intro h
    apply hφx
    have h5 : x0 ∈ LinearMap.ker φ := by
      rw [h]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp h5
  have hk3 := Submodule.finrank_lt hne
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hk3
  have hm := Submodule.finrank_mono hHφ
  have hH3 : Module.finrank ℂ H ≤ 3 := by omega
  have hHeq : H = LinearMap.ker φ := Submodule.eq_of_le_of_finrank_le hHφ (by omega)
  have hrep : ∀ y : Fin 4 → ℂ, φ y = φ (Pi.single 0 1) * y 0 + φ (Pi.single 1 1) * y 1 +
      φ (Pi.single 2 1) * y 2 + φ (Pi.single 3 1) * y 3 := by
    intro y
    rw [dual_eq_dotL φ y, dotL_apply, Fin.sum_univ_four]
    ring
  exact hcore (φ (Pi.single 0 1)) (φ (Pi.single 1 1)) (φ (Pi.single 2 1))
    (φ (Pi.single 3 1)) (fun t a1 a2 a3 h => by
      apply hcub hH3
      rw [hHeq, LinearMap.mem_ker, hrep]
      exact h)
theorem t2pp_alg (k x : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0) (d2 c j : ℂ) (hd2 : d2 ≠ 0)
    (hc : c ≠ 0) (hj : j * j = -1)
    (hk1 : k 1 0 = d2 * k 0 0 ∧ k 1 1 = -d2 * k 0 1 ∧ k 1 2 = -d2 * k 0 2)
    (hk2 : k 2 0 = -c * k 0 0 ∧ k 2 1 = c * j * k 0 1 ∧ k 2 2 = c * k 0 2) (T A1 A2 A3 : ℂ)
    (h00 : k 0 0 * x 0 0 = T) (h10 : k 1 0 * x 1 0 = T) (h01 : k 0 1 * x 0 1 = A1)
    (h11 : k 1 1 * x 1 1 = A2) (h20 : k 2 0 * x 2 0 = A3) (h22 : k 2 2 * x 2 2 = -T)
    (hs : ∀ i, k i 0 * x i 0 + k i 1 * x i 1 + k i 2 * x i 2 = 0) :
    (d2 * c * k 0 0 * k 0 1 * k 0 2) * (Matrix.of x).permanent =
      (A2 - A1) * T * (T - j * (T - A3)) - A3 * (T * (A1 + A2) + 2 * A1 * A2) := by
  obtain ⟨a1, a2, a3⟩ := hk1
  obtain ⟨b1, b2, b3⟩ := hk2
  have n0 := hk 0 0
  have n1 := hk 0 1
  have n2 := hk 0 2
  have q00 : x 0 0 = T / k 0 0 := by
    rw [eq_div_iff n0]
    linear_combination h00
  have q01 : x 0 1 = A1 / k 0 1 := by
    rw [eq_div_iff n1]
    linear_combination h01
  have q02 : x 0 2 = (-T - A1) / k 0 2 := by
    rw [eq_div_iff n2]
    linear_combination hs 0 - h00 - h01
  have q10 : x 1 0 = T / (d2 * k 0 0) := by
    rw [eq_div_iff (mul_ne_zero hd2 n0)]
    rw [a1] at h10
    linear_combination h10
  have q11 : x 1 1 = A2 / (-d2 * k 0 1) := by
    rw [eq_div_iff (mul_ne_zero (neg_ne_zero.mpr hd2) n1)]
    rw [a2] at h11
    linear_combination h11
  have q12 : x 1 2 = (-T - A2) / (-d2 * k 0 2) := by
    rw [eq_div_iff (mul_ne_zero (neg_ne_zero.mpr hd2) n2)]
    have e := hs 1
    rw [a1, a2, a3] at e
    rw [a1] at h10
    rw [a2] at h11
    linear_combination e - h10 - h11
  have q20 : x 2 0 = A3 / (-c * k 0 0) := by
    rw [eq_div_iff (mul_ne_zero (neg_ne_zero.mpr hc) n0)]
    rw [b1] at h20
    linear_combination h20
  have q22 : x 2 2 = -T / (c * k 0 2) := by
    rw [eq_div_iff (mul_ne_zero hc n2)]
    rw [b3] at h22
    linear_combination h22
  have q21 : x 2 1 = -j * (T - A3) / (c * k 0 1) := by
    rw [eq_div_iff (mul_ne_zero hc n1)]
    have e := hs 2
    rw [b1, b2, b3] at e
    rw [b1] at h20
    rw [b3] at h22
    linear_combination (-j) * (e - h20 - h22) + (c * k 0 1 * x 2 1) * hj
  rw [permanent_three]
  simp only [Matrix.of_apply]
  rw [q00, q01, q02, q10, q11, q12, q20, q21, q22]
  field_simp
  ring
theorem sum_C_three (B : Finset (Fin 5)) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) (f : Fin 5 → ℂ) (hf : ∀ m, m ≠ p → m ≠ q → m ≠ s → f m = 0) :
    ∑ m ∈ B, f m = (if p ∈ B then f p else 0) + (if q ∈ B then f q else 0) +
      (if s ∈ B then f s else 0) := by
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 p q s hpq hps hqs
  have hf' : ∀ b, f (cc (Sum.inr b)) = 0 := by
    intro b
    apply hf
    · intro h
      rw [← hc0] at h
      exact Sum.inr_ne_inl (cc.injective h)
    · intro h
      rw [← hc1] at h
      exact Sum.inr_ne_inl (cc.injective h)
    · intro h
      rw [← hc2] at h
      exact Sum.inr_ne_inl (cc.injective h)
  have e := sum_C_supp3 cc B f hf'
  rw [hc0, hc1, hc2] at e
  exact e

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
  have v1 : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (r1, m) * κ m = 0 := fun m h1 h2 h3 => by
    rw [(hoff m h1 h2 h3).1, zero_mul]
  have v2 : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (r2, m) * κ2 m = 0 := fun m h1 h2 h3 => by
    rw [(hoff m h1 h2 h3).2.1, zero_mul]
  have v3 : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (r3, m) * κ3 m = 0 := fun m h1 h2 h3 => by
    rw [(hoff m h1 h2 h3).2.2, zero_mul]
  have S1 := sum_C_three Finset.univ p q s hpq hps hqs _ v1
  have S2 := sum_C_three Finset.univ p q s hpq hps hqs _ v2
  have S3 := sum_C_three Finset.univ p q s hpq hps hqs _ v3
  simp only [Finset.mem_univ, ite_true] at S1 S2 S3
  rw [dotL_apply] at F1 F2 F3
  simp only [rowMap_apply] at F1 F2 F3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← S1]
    exact F1
  · rw [← S2]
    exact F2
  · rw [← S3]
    exact F3
  · rw [← sum_C_three B p q s hpq hps hqs _ v1, ← sum_C_three B p q s hpq hps hqs _ v2]
    exact rel2
  · rw [← sum_C_three B p q s hpq hps hqs _ v1, ← sum_C_three Q2 p q s hpq hps hqs _ v3]
    exact rel3

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
  obtain ⟨rr, hr0, hr1, hr2⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 p q s hpq hps hqs
  have zrow : ∀ m, m ≠ p → m ≠ q → m ≠ s → ∃ b, cc (Sum.inr b) = m := by
    intro m h1 h2 h3
    obtain ⟨y, rfl⟩ := cc.surjective m
    rcases y with j | b
    · rcases fin3_cases j with rfl | rfl | rfl
      · exact absurd hc0 h1
      · exact absurd hc1 h2
      · exact absurd hc2 h3
    · exact ⟨b, rfl⟩
  have hv : ∀ t ∈ blkL L rr cc, ∀ b, t (r1, cc (Sum.inr b)) = 0 ∧
      t (r2, cc (Sum.inr b)) = 0 ∧ t (r3, cc (Sum.inr b)) = 0 := by
    intro t ht b
    have h := ((mem_blkL L rr cc t).mp ht).2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr0]
      exact h 0 b
    · rw [← hr1]
      exact h 1 b
    · rw [← hr2]
      exact h 2 b
  have hrs : ∀ t ∈ blkL L rr cc,
      t (r1, p) * κ p + t (r1, q) * κ q + t (r1, s) * κ s = 0 ∧
      t (r2, p) * κ2 p + t (r2, q) * κ2 q + t (r2, s) * κ2 s = 0 ∧
      t (r3, p) * κ3 p + t (r3, q) * κ3 q + t (r3, s) * κ3 s = 0 := by
    intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have e1 := sum_supp3 cc (fun m => t (r1, m) * κ m)
      (fun b => by simp only [(hv t ht b).1, zero_mul])
    have e2 := sum_supp3 cc (fun m => t (r2, m) * κ2 m)
      (fun b => by simp only [(hv t ht b).2.1, zero_mul])
    have e3 := sum_supp3 cc (fun m => t (r3, m) * κ3 m)
      (fun b => by simp only [(hv t ht b).2.2, zero_mul])
    rw [hc0, hc1, hc2] at e1 e2 e3
    refine ⟨?_, ?_, ?_⟩
    · rw [← e1]
      exact hκL t htL
    · rw [← e2]
      exact hκ2L t htL
    · rw [← e3]
      exact hκ3L t htL
  have hoff : ∀ t ∈ blkL L rr cc, ∀ m, m ≠ p → m ≠ q → m ≠ s →
      t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0 := by
    intro t ht m h1 h2 h3
    obtain ⟨b, rfl⟩ := zrow m h1 h2 h3
    exact hv t ht b
  have hcs : ∀ t ∈ blkL L rr cc, t (r2, p) * κ2 p = t (r1, p) * κ p ∧
      t (r3, p) * κ3 p = t (r1, p) * κ p :=
    fun t ht => hcs0 t ((mem_blkL L rr cc t).mp ht).1 (hoff t ht)
  obtain ⟨K, hK⟩ : ∃ K : Fin 3 → Fin 5 → ℂ, K = ![κ, κ2, κ3] := ⟨_, rfl⟩
  have hK0 : K 0 = κ := by first | (rw [hK]; rfl) | rw [hK]
  have hK1 : K 1 = κ2 := by first | (rw [hK]; rfl) | rw [hK]
  have hK2 : K 2 = κ3 := by first | (rw [hK]; rfl) | rw [hK]
  have hk : ∀ i j, K i (cc (Sum.inl j)) ≠ 0 := by
    intro i j
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0]
      exact hκ0 _
    · rw [hK1]
      exact hκ20 _
    · rw [hK2]
      exact hκ30 _
  have hk1' : K 1 (cc (Sum.inl 0)) = d2 * K 0 (cc (Sum.inl 0)) ∧
      K 1 (cc (Sum.inl 1)) = -d2 * K 0 (cc (Sum.inl 1)) ∧
      K 1 (cc (Sum.inl 2)) = -d2 * K 0 (cc (Sum.inl 2)) := by
    rw [hK0, hK1, hc0, hc1, hc2]
    exact hk1
  have hk2' : K 2 (cc (Sum.inl 0)) = d3 * K 0 (cc (Sum.inl 0)) ∧
      K 2 (cc (Sum.inl 1)) = -d3 * K 0 (cc (Sum.inl 1)) ∧
      K 2 (cc (Sum.inl 2)) = -d3 * K 0 (cc (Sum.inl 2)) := by
    rw [hK0, hK2, hc0, hc1, hc2]
    exact hk2
  have hrel' : ∀ t ∈ blkL L rr cc, ∀ i : Fin 3,
      K i (cc (Sum.inl 0)) * t (rr (Sum.inl i), cc (Sum.inl 0)) =
        K 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) ∧
      K i (cc (Sum.inl 0)) * t (rr (Sum.inl i), cc (Sum.inl 0)) +
        K i (cc (Sum.inl 1)) * t (rr (Sum.inl i), cc (Sum.inl 1)) +
        K i (cc (Sum.inl 2)) * t (rr (Sum.inl i), cc (Sum.inl 2)) = 0 := by
    intro t ht i
    obtain ⟨R1, R2, R3⟩ := hrs t ht
    obtain ⟨C2, C3⟩ := hcs t ht
    rw [hc0, hc1, hc2, hK0, hr0]
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0, hr0]
      exact ⟨rfl, by linear_combination R1⟩
    · rw [hK1, hr1]
      exact ⟨by linear_combination C2, by linear_combination R2⟩
    · rw [hK2, hr2]
      exact ⟨by linear_combination C3, by linear_combination R3⟩
  have h0' : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0 := by
    intro t ht hz
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have hmem : t ∈ rowsZeroS L {r1, r2, r3} := by
      refine ⟨htL, fun r hr m => ?_⟩
      have hri : ∃ i, rr (Sum.inl i) = r := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with h | h | h
        · exact ⟨0, hr0.trans h.symm⟩
        · exact ⟨1, hr1.trans h.symm⟩
        · exact ⟨2, hr2.trans h.symm⟩
      obtain ⟨i, rfl⟩ := hri
      obtain ⟨y, rfl⟩ := cc.surjective m
      rcases y with j | b
      · exact hz i j
      · exact ((mem_blkL L rr cc t).mp ht).2 i b
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨t, ht, hti⟩ := t2_stest hL h9 rr cc h0' (fun i j => K i (cc (Sum.inl j))) hk d2 d3
    hd2 hd3 hk1' hk2' hrel' ![0, 1, 0]
  have htL := ((mem_blkL L rr cc t).mp ht).1
  have hti0 := hti 0
  have hti1 := hti 1
  have hti2 := hti 2
  rw [hK0, hr0, hc0, hc1, hc2] at hti0
  rw [hK1, hr1, hc0, hc1, hc2] at hti1
  rw [hK2, hr2, hc0, hc1, hc2] at hti2
  obtain ⟨u0, u1, u2⟩ := hti0
  obtain ⟨v0, v1, v2⟩ := hti1
  obtain ⟨w0, w1, w2⟩ := hti2
  have u1' : κ q * t (r1, q) = 0 := u1
  have u2' : κ s * t (r1, s) = 0 := by
    have h : κ s * t (r1, s) = -(0 : ℂ) := u2
    rw [h, neg_zero]
  have v1' : κ2 q * t (r2, q) = 1 := v1
  have v2' : κ2 s * t (r2, s) = -1 := v2
  have w1' : κ3 q * t (r3, q) = 0 := w1
  have w2' : κ3 s * t (r3, s) = 0 := by
    have h : κ3 s * t (r3, s) = -(0 : ℂ) := w2
    rw [h, neg_zero]
  have hrow13 : ∀ m, t (r1, m) = 0 ∧ t (r3, m) = 0 := by
    intro m
    by_cases hmp : m = p
    · rw [hmp]
      exact ⟨u0, w0⟩
    by_cases hmq : m = q
    · rw [hmq]
      exact ⟨(mul_eq_zero.mp u1').resolve_left (hκ0 q),
        (mul_eq_zero.mp w1').resolve_left (hκ30 q)⟩
    by_cases hms : m = s
    · rw [hms]
      exact ⟨(mul_eq_zero.mp u2').resolve_left (hκ0 s),
        (mul_eq_zero.mp w2').resolve_left (hκ30 s)⟩
    obtain ⟨b, rfl⟩ := zrow m hmp hmq hms
    exact ⟨(hv t ht b).1, (hv t ht b).2.2⟩
  refine ⟨t, ⟨htL, fun r hr j => ?_⟩, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h
    · rw [h]
      exact (hrow13 j).1
    · rw [h]
      exact (hrow13 j).2
  · funext m
    rw [rowMap_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hmp : m = p
    · rw [hmp, v0, Pi.single_eq_of_ne hpq, Pi.single_eq_of_ne hps]
      ring
    by_cases hmq : m = q
    · rw [hmq, Pi.single_eq_same, Pi.single_eq_of_ne hqs]
      have hq0 := hκ20 q
      have e : t (r2, q) = (κ2 q)⁻¹ := by
        field_simp
        linear_combination v1'
      rw [e]
      ring
    by_cases hms : m = s
    · rw [hms, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hqs)]
      have hs0 := hκ20 s
      have e : t (r2, s) = -(κ2 s)⁻¹ := by
        field_simp
        linear_combination v2'
      rw [e]
      ring
    rw [Pi.single_eq_of_ne hmq, Pi.single_eq_of_ne hms]
    obtain ⟨b, rfl⟩ := zrow m hmp hmq hms
    rw [(hv t ht b).2.1]
    ring

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
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ), Λ = lam4
      ![k 0 0, k 0 1, k 1 1, k 2 0]
      ![(r (Sum.inl 0), c (Sum.inl 0)), (r (Sum.inl 0), c (Sum.inl 1)),
        (r (Sum.inl 1), c (Sum.inl 1)), (r (Sum.inl 2), c (Sum.inl 0))] := ⟨_, rfl⟩
  have hΛ0 : ∀ t, Λ t 0 = k 0 0 * t (r (Sum.inl 0), c (Sum.inl 0)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hΛ1 : ∀ t, Λ t 1 = k 0 1 * t (r (Sum.inl 0), c (Sum.inl 1)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hΛ2 : ∀ t, Λ t 2 = k 1 1 * t (r (Sum.inl 1), c (Sum.inl 1)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hΛ3 : ∀ t, Λ t 3 = k 2 0 * t (r (Sum.inl 2), c (Sum.inl 0)) := fun t => by
    first
    | (rw [hΛ]; rfl)
    | rw [hΛ]
  have hent : ∀ t ∈ blkL L r c,
      k 0 0 * t (r (Sum.inl 0), c (Sum.inl 0)) = Λ t 0 ∧
      k 0 1 * t (r (Sum.inl 0), c (Sum.inl 1)) = Λ t 1 ∧
      k 0 2 * t (r (Sum.inl 0), c (Sum.inl 2)) = -Λ t 0 - Λ t 1 ∧
      k 1 0 * t (r (Sum.inl 1), c (Sum.inl 0)) = Λ t 0 ∧
      k 1 1 * t (r (Sum.inl 1), c (Sum.inl 1)) = Λ t 2 ∧
      k 1 2 * t (r (Sum.inl 1), c (Sum.inl 2)) = -Λ t 0 - Λ t 2 ∧
      k 2 0 * t (r (Sum.inl 2), c (Sum.inl 0)) = Λ t 3 ∧
      k 2 1 * t (r (Sum.inl 2), c (Sum.inl 1)) = Λ t 0 - Λ t 3 ∧
      k 2 2 * t (r (Sum.inl 2), c (Sum.inl 2)) = -Λ t 0 := by
    intro t ht
    obtain ⟨e10, e22, hs⟩ := hrel t ht
    have s0 := hs 0
    have s1 := hs 1
    have s2 := hs 2
    rw [hΛ0, hΛ1, hΛ2, hΛ3]
    refine ⟨rfl, rfl, ?_, e10, rfl, ?_, rfl, ?_, e22⟩
    · linear_combination s0
    · linear_combination s1 - e10
    · linear_combination s2 - e22
  obtain ⟨H, hH⟩ : ∃ H : Submodule ℂ (Fin 4 → ℂ), H = (blkL L r c).map Λ := ⟨_, rfl⟩
  have hinj : blkL L r c ⊓ LinearMap.ker Λ = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨ht, hk0⟩
    replace hk0 := LinearMap.mem_ker.mp hk0
    rw [Submodule.mem_bot]
    have z : ∀ i, Λ t i = 0 := fun i => congrFun hk0 i
    obtain ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ := hent t ht
    simp only [z 0, z 1, z 2, z 3] at e00 e01 e02 e10 e11 e12 e20 e21 e22
    apply h0 t ht
    intro i j'
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j' with rfl | rfl | rfl
    · exact (mul_eq_zero.mp e00).resolve_left (hk 0 0)
    · exact (mul_eq_zero.mp e01).resolve_left (hk 0 1)
    · exact (mul_eq_zero.mp (e02.trans (by ring))).resolve_left (hk 0 2)
    · exact (mul_eq_zero.mp e10).resolve_left (hk 1 0)
    · exact (mul_eq_zero.mp e11).resolve_left (hk 1 1)
    · exact (mul_eq_zero.mp (e12.trans (by ring))).resolve_left (hk 1 2)
    · exact (mul_eq_zero.mp e20).resolve_left (hk 2 0)
    · exact (mul_eq_zero.mp (e21.trans (by ring))).resolve_left (hk 2 1)
    · exact (mul_eq_zero.mp (e22.trans (by ring))).resolve_left (hk 2 2)
  have hrn := rank_nullity (blkL L r c) Λ
  rw [hinj, finrank_bot, zero_add, ← hH] at hrn
  have hb3 := blkL_finrank L r c
  rw [h9] at hb3
  have hH3 : 3 ≤ Module.finrank ℂ H := by omega
  have hcub : Module.finrank ℂ H ≤ 3 → ∀ x ∈ H,
      (x 2 - x 1) * x 0 * (x 0 - j * (x 0 - x 3)) - x 3 * (x 0 * (x 1 + x 2) + 2 * x 1 * x 2) =
        0 := by
    intro hle x hx
    rw [hH] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hw := ell_ne_of_small r c h9 (by omega)
    have hb := stest_blk hL r c hw t ht
    have hb' : (Matrix.of fun i j => t (r (Sum.inl i), c (Sum.inl j))).permanent = 0 := hb
    obtain ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ := hent t ht
    have halg := t2pp_alg k (fun i j => t (r (Sum.inl i), c (Sum.inl j))) hk d2 γ j hd2 hγ hj
      hk1 hk2 (Λ t 0) (Λ t 1) (Λ t 2) (Λ t 3) e00 e10 e01 e11 e20 e22 ((hrel t ht).2.2)
    rw [hb', mul_zero] at halg
    linear_combination -halg
  have hj1 : j ≠ 1 := by
    intro h
    rw [h] at hj
    norm_num at hj
  have hall := hyper_top H hH3
    (fun x => (x 2 - x 1) * x 0 * (x 0 - j * (x 0 - x 3)) - x 3 * (x 0 * (x 1 + x 2) +
      2 * x 1 * x 2))
    (fun α β1 β2 β3 h => t2pp_core j α β1 β2 β3 hj1 (fun t a1 a2 a3 h' => h t a1 a2 a3 h'))
    hcub
  have hx : (![0, 0, 1, 0] : Fin 4 → ℂ) ∈ (blkL L r c).map Λ := by
    rw [← hH]
    exact hall _
  obtain ⟨t, ht, htx⟩ := hx
  have z0 : Λ t 0 = 0 := congrFun htx 0
  have z1 : Λ t 1 = 0 := congrFun htx 1
  have z2 : Λ t 2 = 1 := congrFun htx 2
  have z3 : Λ t 3 = 0 := congrFun htx 3
  obtain ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ := hent t ht
  simp only [z0, z1, z2, z3] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  refine ⟨t, ht, fun j' => ?_, fun j' => ?_, ?_, e11, by linear_combination e12⟩
  · rcases fin3_cases j' with rfl | rfl | rfl
    · exact (mul_eq_zero.mp e00).resolve_left (hk 0 0)
    · exact (mul_eq_zero.mp e01).resolve_left (hk 0 1)
    · exact (mul_eq_zero.mp (e02.trans (by ring))).resolve_left (hk 0 2)
  · rcases fin3_cases j' with rfl | rfl | rfl
    · exact (mul_eq_zero.mp e20).resolve_left (hk 2 0)
    · exact (mul_eq_zero.mp (e21.trans (by ring))).resolve_left (hk 2 1)
    · exact (mul_eq_zero.mp (e22.trans (by ring))).resolve_left (hk 2 2)
  · exact (mul_eq_zero.mp e10).resolve_left (hk 1 0)

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
  obtain ⟨rr, hr0, hr1, hr2⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 p q s hpq hps hqs
  have zrow : ∀ m, m ≠ p → m ≠ q → m ≠ s → ∃ b, cc (Sum.inr b) = m := by
    intro m h1 h2 h3
    obtain ⟨y, rfl⟩ := cc.surjective m
    rcases y with j | b
    · rcases fin3_cases j with rfl | rfl | rfl
      · exact absurd hc0 h1
      · exact absurd hc1 h2
      · exact absurd hc2 h3
    · exact ⟨b, rfl⟩
  have hv : ∀ t ∈ blkL L rr cc, ∀ b, t (r1, cc (Sum.inr b)) = 0 ∧
      t (r2, cc (Sum.inr b)) = 0 ∧ t (r3, cc (Sum.inr b)) = 0 := by
    intro t ht b
    have h := ((mem_blkL L rr cc t).mp ht).2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr0]
      exact h 0 b
    · rw [← hr1]
      exact h 1 b
    · rw [← hr2]
      exact h 2 b
  have hrs : ∀ t ∈ blkL L rr cc,
      t (r1, p) * κ p + t (r1, q) * κ q + t (r1, s) * κ s = 0 ∧
      t (r2, p) * κ2 p + t (r2, q) * κ2 q + t (r2, s) * κ2 s = 0 ∧
      t (r3, p) * κ3 p + t (r3, q) * κ3 q + t (r3, s) * κ3 s = 0 := by
    intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have e1 := sum_supp3 cc (fun m => t (r1, m) * κ m)
      (fun b => by simp only [(hv t ht b).1, zero_mul])
    have e2 := sum_supp3 cc (fun m => t (r2, m) * κ2 m)
      (fun b => by simp only [(hv t ht b).2.1, zero_mul])
    have e3 := sum_supp3 cc (fun m => t (r3, m) * κ3 m)
      (fun b => by simp only [(hv t ht b).2.2, zero_mul])
    rw [hc0, hc1, hc2] at e1 e2 e3
    refine ⟨?_, ?_, ?_⟩
    · rw [← e1]
      exact hκL t htL
    · rw [← e2]
      exact hκ2L t htL
    · rw [← e3]
      exact hκ3L t htL
  have hoff : ∀ t ∈ blkL L rr cc, ∀ m, m ≠ p → m ≠ q → m ≠ s →
      t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0 := by
    intro t ht m h1 h2 h3
    obtain ⟨b, rfl⟩ := zrow m h1 h2 h3
    exact hv t ht b
  have hcs : ∀ t ∈ blkL L rr cc, t (r2, p) * κ2 p = t (r1, p) * κ p ∧
      t (r3, s) * κ3 s = -(t (r1, p) * κ p) :=
    fun t ht => hcs0 t ((mem_blkL L rr cc t).mp ht).1 (hoff t ht)
  obtain ⟨K, hK⟩ : ∃ K : Fin 3 → Fin 5 → ℂ, K = ![κ, κ2, κ3] := ⟨_, rfl⟩
  have hK0 : K 0 = κ := by first | (rw [hK]; rfl) | rw [hK]
  have hK1 : K 1 = κ2 := by first | (rw [hK]; rfl) | rw [hK]
  have hK2 : K 2 = κ3 := by first | (rw [hK]; rfl) | rw [hK]
  have hk : ∀ i j, K i (cc (Sum.inl j)) ≠ 0 := by
    intro i j
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0]
      exact hκ0 _
    · rw [hK1]
      exact hκ20 _
    · rw [hK2]
      exact hκ30 _
  have hk1' : K 1 (cc (Sum.inl 0)) = d2 * K 0 (cc (Sum.inl 0)) ∧
      K 1 (cc (Sum.inl 1)) = -d2 * K 0 (cc (Sum.inl 1)) ∧
      K 1 (cc (Sum.inl 2)) = -d2 * K 0 (cc (Sum.inl 2)) := by
    rw [hK0, hK1, hc0, hc1, hc2]
    exact hk1
  have hk2' : K 2 (cc (Sum.inl 0)) = -γ * K 0 (cc (Sum.inl 0)) ∧
      K 2 (cc (Sum.inl 1)) = γ * j * K 0 (cc (Sum.inl 1)) ∧
      K 2 (cc (Sum.inl 2)) = γ * K 0 (cc (Sum.inl 2)) := by
    rw [hK0, hK2, hc0, hc1, hc2]
    exact hk2
  have hrel' : ∀ t ∈ blkL L rr cc,
      K 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) =
        K 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) ∧
      K 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) =
        -(K 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) ∧
      ∀ i : Fin 3, K i (cc (Sum.inl 0)) * t (rr (Sum.inl i), cc (Sum.inl 0)) +
        K i (cc (Sum.inl 1)) * t (rr (Sum.inl i), cc (Sum.inl 1)) +
        K i (cc (Sum.inl 2)) * t (rr (Sum.inl i), cc (Sum.inl 2)) = 0 := by
    intro t ht
    obtain ⟨R1, R2, R3⟩ := hrs t ht
    obtain ⟨C2, C3⟩ := hcs t ht
    rw [hc0, hc1, hc2, hK0, hK1, hK2, hr0, hr1, hr2]
    refine ⟨by linear_combination C2, by linear_combination C3, fun i => ?_⟩
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0, hr0]
      linear_combination R1
    · rw [hK1, hr1]
      linear_combination R2
    · rw [hK2, hr2]
      linear_combination R3
  have h0' : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0 := by
    intro t ht hz
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have hmem : t ∈ rowsZeroS L {r1, r2, r3} := by
      refine ⟨htL, fun r hr m => ?_⟩
      have hri : ∃ i, rr (Sum.inl i) = r := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with h | h | h
        · exact ⟨0, hr0.trans h.symm⟩
        · exact ⟨1, hr1.trans h.symm⟩
        · exact ⟨2, hr2.trans h.symm⟩
      obtain ⟨i, rfl⟩ := hri
      obtain ⟨y, rfl⟩ := cc.surjective m
      rcases y with j | b
      · exact hz i j
      · exact ((mem_blkL L rr cc t).mp ht).2 i b
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨t, ht, hA0, hA2, hA10, hA11, hA12⟩ := t2pp_stest hL h9 rr cc h0'
    (fun i j => K i (cc (Sum.inl j))) hk d2 γ j hd2 hγ hj hk1' hk2' hrel'
  have htL := ((mem_blkL L rr cc t).mp ht).1
  have u0 : t (r1, p) = 0 := by rw [← hr0, ← hc0]; exact hA0 0
  have u1 : t (r1, q) = 0 := by rw [← hr0, ← hc1]; exact hA0 1
  have u2 : t (r1, s) = 0 := by rw [← hr0, ← hc2]; exact hA0 2
  have w0 : t (r3, p) = 0 := by rw [← hr2, ← hc0]; exact hA2 0
  have w1 : t (r3, q) = 0 := by rw [← hr2, ← hc1]; exact hA2 1
  have w2 : t (r3, s) = 0 := by rw [← hr2, ← hc2]; exact hA2 2
  have v0 : t (r2, p) = 0 := by rw [← hr1, ← hc0]; exact hA10
  have v1' : κ2 q * t (r2, q) = 1 := by
    have h := hA11
    rw [hK1, hr1, hc1] at h
    exact h
  have v2' : κ2 s * t (r2, s) = -1 := by
    have h := hA12
    rw [hK1, hr1, hc2] at h
    exact h
  have hrow13 : ∀ m, t (r1, m) = 0 ∧ t (r3, m) = 0 := by
    intro m
    by_cases hmp : m = p
    · rw [hmp]
      exact ⟨u0, w0⟩
    by_cases hmq : m = q
    · rw [hmq]
      exact ⟨u1, w1⟩
    by_cases hms : m = s
    · rw [hms]
      exact ⟨u2, w2⟩
    obtain ⟨b, rfl⟩ := zrow m hmp hmq hms
    exact ⟨(hv t ht b).1, (hv t ht b).2.2⟩
  refine ⟨t, ⟨htL, fun r hr j => ?_⟩, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h
    · rw [h]
      exact (hrow13 j).1
    · rw [h]
      exact (hrow13 j).2
  · funext m
    rw [rowMap_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hmp : m = p
    · rw [hmp, v0, Pi.single_eq_of_ne hpq, Pi.single_eq_of_ne hps]
      ring
    by_cases hmq : m = q
    · rw [hmq, Pi.single_eq_same, Pi.single_eq_of_ne hqs]
      have hq0 := hκ20 q
      have e : t (r2, q) = (κ2 q)⁻¹ := by
        field_simp
        linear_combination v1'
      rw [e]
      ring
    by_cases hms : m = s
    · rw [hms, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hqs)]
      have hs0 := hκ20 s
      have e : t (r2, s) = -(κ2 s)⁻¹ := by
        field_simp
        linear_combination v2'
      rw [e]
      ring
    rw [Pi.single_eq_of_ne hmq, Pi.single_eq_of_ne hms]
    obtain ⟨b, rfl⟩ := zrow m hmp hmq hms
    rw [(hv t ht b).2.1]
    ring

theorem t2pp_proof : T2ppHyp := by
  intro L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 hp hq h0
  obtain ⟨κ, κ2, ν, ν', a, b, hκL, hκ1, hκ2L, hκ21, hνL, hν1, hκ0, hκ20, hcl, hI⟩ := hp
  obtain ⟨κ', κ3, μ, μ', a', b', hκ'L, hκ'1, hκ3L, hκ31, hμL, hμ1, hκ'0, hκ30, hcl', hII⟩ := hq
  have hkk : κ = κ' := (fk_unique hL r1 z1.1 κ κ' hκL hκ1 hκ'L hκ'1).symm
  subst hkk
  have hX0 : Module.finrank ℂ (rowsZeroS L {r1, r2, r3}) = 0 := by
    rw [h0, finrank_bot]
  have hpart := t2_split hL r1 r2 r3 z1.1 (by omega) κ ν ν' hκ0 hκL hκ1 hνL ⟨a, b, hcl.1⟩
    κ μ μ' hκL hκ1 hμL ⟨a', b', hcl'.1⟩
  classical
  obtain ⟨C, hC⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ν m / κ m = ν b / κ b :=
    ⟨Finset.univ.filter (fun m => ν m / κ m = ν b / κ b), fun m => by simp⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin 5), ∀ m, m ∈ B ↔ μ m / κ m = μ b' / κ b' :=
    ⟨Finset.univ.filter (fun m => μ m / κ m = μ b' / κ b'), fun m => by simp⟩
  obtain ⟨Q2, hQ2⟩ : ∃ Q2 : Finset (Fin 5), ∀ m, m ∈ Q2 ↔ μ' m / κ3 m = μ' a' / κ3 a' :=
    ⟨Finset.univ.filter (fun m => μ' m / κ3 m = μ' a' / κ3 a'), fun m => by simp⟩
  obtain ⟨⟨f2, hf2, hf2a, hf2b⟩, hrel2, hCa⟩ :=
    typeI_nf r1 r2 κ κ2 ν ν' a b hκL hκ2L hνL hκ0 hκ20 hcl hI C hC
  obtain ⟨hQ2B, hk3Q2, hk3B, hk3Q1, hrel3⟩ :=
    typeII_nf r1 r3 κ κ3 μ μ' a' b' hκL hκ3L hμL hκ0 hκ30 hcl' B Q2 hB hQ2
  have hCC : (∀ m, m ∈ B ↔ m ∈ C) ∨ (∀ m, m ∈ B ↔ m ∉ C) := by
    by_cases hb' : b' ∈ C
    · left
      intro m
      rw [hB, ← hpart m b', hC m]
      have e := (hC b').mp hb'
      exact ⟨fun h => h.trans e, fun h => h.trans e.symm⟩
    · right
      intro m
      rw [hB, ← hpart m b', hCa m]
      have e := (hCa b').mp hb'
      exact ⟨fun h => h.trans e, fun h => h.trans e.symm⟩
  have h2data : ∃ g2 : ℂ, g2 ≠ 0 ∧ (∀ m, m ∉ B → κ2 m = g2 * κ m) ∧
      (∀ m, m ∈ B → κ2 m = -g2 * κ m) ∧
      (∀ t ∈ L, ∑ m ∈ B, t (r1, m) * κ m = ∑ m ∈ B, t (r2, m) * κ2 m) := by
    rcases hCC with hCC | hCC
    · have e : B = C := Finset.ext hCC
      rw [e]
      exact ⟨f2, hf2, hf2a, hf2b, hrel2⟩
    · have e : B = Cᶜ := Finset.ext fun m => by rw [hCC m, Finset.mem_compl]
      rw [e]
      refine ⟨-f2, neg_ne_zero.mpr hf2, fun m hm => ?_, fun m hm => ?_, fun t ht => ?_⟩
      · rw [hf2b m (by simpa using hm)]
      · rw [hf2a m (Finset.mem_compl.mp hm)]
        ring
      · have e1 := hrel2 t ht
        have s1 := Finset.sum_compl_add_sum C (fun m => t (r1, m) * κ m)
        have s2 := Finset.sum_compl_add_sum C (fun m => t (r2, m) * κ2 m)
        have f1 := hκL t ht
        have f2' := hκ2L t ht
        rw [dotL_apply] at f1 f2'
        simp only [rowMap_apply] at f1 f2'
        linear_combination s1 - s2 - e1 + f1 - f2'
  obtain ⟨g2, hg2, hg2a, hg2b, hrel2'⟩ := h2data
  have hc : κ3 a' / κ a' ≠ 0 := div_ne_zero (hκ30 a') (hκ0 a')
  have hb'B : b' ∈ B := (hB b').mpr rfl
  have ha'Q2 : a' ∈ Q2 := (hQ2 a').mpr rfl
  have ha'B : a' ∉ B := hQ2B a' ha'Q2
  have hb'Q : b' ∉ Q2 := fun h => hQ2B b' h hb'B
  have genA : ∀ q s, q ∉ B → q ∉ Q2 → s ∈ Q2 →
      (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈
        (rowsZeroS L {r1, r3}).map (rowMap r2) := by
    intro q s hqB hqQ hsQ
    have hsB : s ∉ B := hQ2B s hsQ
    have hpq : b' ≠ q := fun h => hqB (by rw [← h]; exact hb'B)
    have hps : b' ≠ s := fun h => hsB (by rw [← h]; exact hb'B)
    have hqs : q ≠ s := fun h => hqQ (by rw [h]; exact hsQ)
    have hω := hk3Q1 q hqB hqQ
    have hj : (κ3 q / κ q) / (κ3 a' / κ a') * ((κ3 q / κ q) / (κ3 a' / κ a')) = -1 := by
      have e : (κ3 q / κ q) / (κ3 a' / κ a') * ((κ3 q / κ q) / (κ3 a' / κ a')) =
          (κ3 q / κ q) ^ 2 / (κ3 a' / κ a') ^ 2 := by ring
      rw [e, hω, neg_div, div_self (pow_ne_zero 2 hc)]
    refine gen_vec_A hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L b' q s
      hpq hps hqs (-g2) (κ3 a' / κ a') ((κ3 q / κ q) / (κ3 a' / κ a')) (neg_ne_zero.mpr hg2) hc
      hj ⟨hg2b b' hb'B, ?_, ?_⟩ ⟨hk3B b' hb'B, ?_, hk3Q2 s hsQ⟩ (fun t ht hoff => ?_)
    · rw [hg2a q hqB]
      ring
    · rw [hg2a s hsB]
      ring
    · rw [mul_div_cancel₀ _ hc, div_mul_cancel₀ _ (hκ0 q)]
    · obtain ⟨R1, R2, R3, A2, A3⟩ := loc_rel κ κ2 κ3 B Q2 r1 r2 r3 t b' q s hpq hps hqs hoff
        (hκL t ht) (hκ2L t ht) (hκ3L t ht) (hrel2' t ht) (hrel3 t ht)
      simp only [hb'B, hqB, hsB, hb'Q, hqQ, hsQ, ite_true, ite_false, zero_add, add_zero]
        at A2 A3
      exact ⟨by linear_combination -A2, by linear_combination A3⟩
  have genB : ∀ q s, q ≠ s → q ∈ Q2 → s ∈ Q2 →
      (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈
        (rowsZeroS L {r1, r3}).map (rowMap r2) := by
    intro q s hqs hqQ hsQ
    have hqB : q ∉ B := hQ2B q hqQ
    have hsB : s ∉ B := hQ2B s hsQ
    have hpq : b' ≠ q := fun h => hqB (by rw [← h]; exact hb'B)
    have hps : b' ≠ s := fun h => hsB (by rw [← h]; exact hb'B)
    refine gen_vec_core hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L b' q
      s hpq hps hqs (-g2) (-(κ3 a' / κ a')) (neg_ne_zero.mpr hg2) (neg_ne_zero.mpr hc)
      ⟨hg2b b' hb'B, ?_, ?_⟩ ⟨hk3B b' hb'B, ?_, ?_⟩ (fun t ht hoff => ?_)
    · rw [hg2a q hqB]
      ring
    · rw [hg2a s hsB]
      ring
    · rw [hk3Q2 q hqQ]
      ring
    · rw [hk3Q2 s hsQ]
      ring
    · obtain ⟨R1, R2, R3, A2, A3⟩ := loc_rel κ κ2 κ3 B Q2 r1 r2 r3 t b' q s hpq hps hqs hoff
        (hκL t ht) (hκ2L t ht) (hκ3L t ht) (hrel2' t ht) (hrel3 t ht)
      simp only [hb'B, hqB, hsB, hb'Q, hqQ, hsQ, ite_true, ite_false, zero_add, add_zero]
        at A2 A3
      exact ⟨by linear_combination -A2, by linear_combination R3 - A3⟩
  have genC : ∀ q s, q ≠ s → q ∈ B → s ∈ B →
      (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) - (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) ∈
        (rowsZeroS L {r1, r3}).map (rowMap r2) := by
    intro q s hqs hqB hsB
    have hpq : a' ≠ q := fun h => ha'B (by rw [h]; exact hqB)
    have hps : a' ≠ s := fun h => ha'B (by rw [h]; exact hsB)
    have hqQ : q ∉ Q2 := fun h => hQ2B q h hqB
    have hsQ : s ∉ Q2 := fun h => hQ2B s h hsB
    refine gen_vec_core hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L a' q
      s hpq hps hqs g2 (κ3 a' / κ a') hg2 hc ⟨hg2a a' ha'B, hg2b q hqB, hg2b s hsB⟩
      ⟨hk3Q2 a' ha'Q2, hk3B q hqB, hk3B s hsB⟩ (fun t ht hoff => ?_)
    obtain ⟨R1, R2, R3, A2, A3⟩ := loc_rel κ κ2 κ3 B Q2 r1 r2 r3 t a' q s hpq hps hqs hoff
      (hκL t ht) (hκ2L t ht) (hκ3L t ht) (hrel2' t ht) (hrel3 t ht)
    simp only [ha'B, hqB, hsB, ha'Q2, hqQ, hsQ, ite_true, ite_false, zero_add, add_zero]
      at A2 A3
    exact ⟨by linear_combination R2 - R1 + A2, by linear_combination A3 - R1⟩
  have hR := span_classes ((rowsZeroS L {r1, r3}).map (rowMap r2)) B b' a' hb'B ha'B κ2 hκ20
    (fun q s hqs hiff => by
      by_cases hqB : q ∈ B
      · exact genC q s hqs hqB (hiff.mp hqB)
      · have hsB : s ∉ B := fun h => hqB (hiff.mpr h)
        by_cases hqQ : q ∈ Q2
        · by_cases hsQ : s ∈ Q2
          · exact genB q s hqs hqQ hsQ
          · have h := genA s q hsB hsQ hqQ
            have e : (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) -
                (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) =
                -((κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) -
                  (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ)) := by
              rw [neg_sub]
            rw [e]
            exact Submodule.neg_mem _ h
        · by_cases hsQ : s ∈ Q2
          · exact genA q s hqB hqQ hsQ
          · have h1 := genA q a' hqB hqQ ha'Q2
            have h2 := genA s a' hsB hsQ ha'Q2
            have e : (κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) -
                (κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) =
                ((κ2 q)⁻¹ • (Pi.single q 1 : Fin 5 → ℂ) -
                  (κ2 a')⁻¹ • (Pi.single a' 1 : Fin 5 → ℂ)) -
                ((κ2 s)⁻¹ • (Pi.single s 1 : Fin 5 → ℂ) -
                  (κ2 a')⁻¹ • (Pi.single a' 1 : Fin 5 → ℂ)) := by
              rw [sub_sub_sub_cancel_right]
            rw [e]
            exact Submodule.sub_mem _ h1 h2)
  have hle := Submodule.finrank_map_le (rowMap r2) (rowsZeroS L {r1, r3})
  omega
theorem dotL_single' {n : ℕ} (d : Fin n) (z : Fin n → ℂ) :
    dotL (Pi.single d 1) z = z d := by
  rw [dotL_apply]
  simp [Pi.single_apply]

theorem polyLine_lin {V : Type} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] ℂ) :
    PolyLine (fun v => f v) := by
  intro u v
  refine ⟨Polynomial.C (f u) + Polynomial.C (f v) * Polynomial.X, fun s => ?_⟩
  simp only [map_add, map_smul, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

noncomputable def entL (p : Fin 5 × Fin 5) : ℂ × (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] ℂ where
  toFun w := w.1 + w.2 p
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' k x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem entL_apply (p : Fin 5 × Fin 5) (w : ℂ × (Fin 5 × Fin 5 → ℂ)) :
    entL p w = w.1 + w.2 p := rfl

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
  by_cases hf : ∃ w0 ∈ U, f w0 ≠ 0
  · obtain ⟨w0, hw0, hfw0⟩ := hf
    refine ⟨g w0 / f w0, fun w hw => ?_⟩
    have hv : w - (f w / f w0) • w0 ∈ U := U.sub_mem hw (U.smul_mem _ hw0)
    have hfv : f (w - (f w / f w0) • w0) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfw0, sub_self]
    have hgv := h _ hv hfv
    rw [map_sub, map_smul, smul_eq_mul] at hgv
    linear_combination hgv
  · push_neg at hf
    refine ⟨0, fun w hw => ?_⟩
    rw [h w hw (hf w hw), zero_mul]

theorem gen_lin {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (i i' d : Fin 5)
    (hii : i ≠ i') (hi : 4 ≤ Module.finrank ℂ (L.map (rowMap i))) (hd : ZFc L d)
    (b : Fin 5 → ℂ) (hb : b d = 0)
    (h : ∀ c : ℂ, ∀ t ∈ L, dotL b (fun j => c + t (i, j)) * (c + t (i', d)) +
      (c + t (i, d)) * dotL b (fun j => c + t (i', j)) = 0) :
    ∀ j, b j = 0 := by
  obtain ⟨U, hU⟩ : ∃ U : Submodule ℂ (ℂ × (Fin 5 × Fin 5 → ℂ)),
      U = (⊤ : Submodule ℂ ℂ).prod L := ⟨_, rfl⟩
  have memU : ∀ w : ℂ × (Fin 5 × Fin 5 → ℂ), w ∈ U ↔ w.2 ∈ L := by
    intro w
    rw [hU, Submodule.mem_prod]
    simp
  have h1 : ∀ w ∈ U ⊓ LinearMap.ker (entL (i, d)),
      (dotL b).comp (rowHat i) w * entL (i', d) w = 0 := by
    rintro w ⟨hw, hk⟩
    replace hk := LinearMap.mem_ker.mp hk
    rw [entL_apply] at hk
    have e := h w.1 w.2 ((memU w).mp hw)
    rw [hk, zero_mul, add_zero] at e
    exact e
  rcases ufd_zero (U ⊓ LinearMap.ker (entL (i, d))) (fun w => (dotL b).comp (rowHat i) w)
      (fun w => entL (i', d) w) (polyLine_lin _) (polyLine_lin _) h1 with h2 | h2
  · obtain ⟨c0, hc0⟩ := ker_prop U (entL (i, d)) ((dotL b).comp (rowHat i))
      (fun w hw hk => h2 w ⟨hw, LinearMap.mem_ker.mpr hk⟩)
    have hA : ∀ t ∈ L, dotL (fun j => b j + (-c0) * (Pi.single d 1 : Fin 5 → ℂ) j)
        (rowMap i t) = 0 := by
      intro t ht
      have e := hc0 ((0 : ℂ), t) ((memU _).mpr ht)
      have e1 : (dotL b).comp (rowHat i) ((0 : ℂ), t) = dotL b (rowMap i t) := by
        rw [LinearMap.comp_apply]
        congr 1
        funext j
        show (0 : ℂ) + t (i, j) = t (i, j)
        ring
      have e2 : entL (i, d) ((0 : ℂ), t) = t (i, d) := by
        show (0 : ℂ) + t (i, d) = t (i, d)
        ring
      rw [e1, e2] at e
      rw [dotL_comb, dotL_single', rowMap_apply, e]
      ring
    have hB : dotL (fun j => b j + (-c0) * (Pi.single d 1 : Fin 5 → ℂ) j) 1 = 0 := by
      rw [dotL_comb, dotL_single']
      have e := hc0 ((1 : ℂ), 0) ((memU _).mpr L.zero_mem)
      have e1 : (dotL b).comp (rowHat i) ((1 : ℂ), 0) = dotL b 1 := by
        rw [LinearMap.comp_apply]
        congr 1
        funext j
        show (1 : ℂ) + (0 : Fin 5 × Fin 5 → ℂ) (i, j) = 1
        simp
      have e2 : entL (i, d) ((1 : ℂ), 0) = 1 := by
        show (1 : ℂ) + (0 : Fin 5 × Fin 5 → ℂ) (i, d) = 1
        simp
      rw [e1, e2, mul_one] at e
      rw [e]
      simp
    have hβ := dot_zero_of_row hL i hi _ hA hB
    intro j
    have e := hβ j
    have ed := hβ d
    simp only [Pi.single_eq_same, mul_one] at ed
    have hc : c0 = 0 := by
      rw [hb] at ed
      linear_combination -ed
    rw [hc] at e
    simpa using e
  · obtain ⟨c0, hc0⟩ := ker_prop U (entL (i, d)) (entL (i', d))
      (fun w hw hk => h2 w ⟨hw, LinearMap.mem_ker.mpr hk⟩)
    obtain ⟨i0, hi0, hi0'⟩ := exists_other i i'
    have hμL : ∀ t ∈ L, dotL (fun m => (Pi.single i' 1 : Fin 5 → ℂ) m +
        (-c0) * (Pi.single i 1 : Fin 5 → ℂ) m) (colMap d t) = 0 := by
      intro t ht
      rw [dotL_comb, dotL_single', dotL_single', colMap_apply, colMap_apply]
      have e := hc0 ((0 : ℂ), t) ((memU _).mpr ht)
      have e1 : entL (i', d) ((0 : ℂ), t) = t (i', d) := by
        show (0 : ℂ) + t (i', d) = t (i', d)
        ring
      have e2 : entL (i, d) ((0 : ℂ), t) = t (i, d) := by
        show (0 : ℂ) + t (i, d) = t (i, d)
        ring
      rw [e1, e2] at e
      rw [e]
      ring
    have hz := col_rel_zero hL d hd _ hμL i0 (by simp [Pi.single_apply, hi0, hi0']) i'
    simp [Pi.single_apply, hii.symm] at hz
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
    (l : Fin 3) : lam3 w P t l = w l * t (P l) := rfl

theorem stest_lift3 {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r c : Fin 3 ⊕ Fin 2 ≃ Fin 5)
    (h0 : ∀ t ∈ blkL L r c, (∀ i j, t (r (Sum.inl i), c (Sum.inl j)) = 0) → t = 0)
    (k : Fin 3 → Fin 3 → ℂ) (hk : ∀ i j, k i j ≠ 0)
    (M : Fin 3 → Fin 3 → Fin 3 → ℂ) (pi pj : Fin 3 → Fin 3)
    (hM : ∀ t ∈ blkL L r c, ∀ i j, k i j * t (r (Sum.inl i), c (Sum.inl j)) =
      ∑ l, M i j l * (k (pi l) (pj l) * t (r (Sum.inl (pi l)), c (Sum.inl (pj l)))))
    (x0 : Fin 3 → ℂ)
    (hperm : (Matrix.of fun i j => (∑ l, M i j l * x0 l) / k i j).permanent ≠ 0) : False := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : (Fin 5 × Fin 5 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ),
      Λ = lam3 (fun l => k (pi l) (pj l)) (fun l => (r (Sum.inl (pi l)), c (Sum.inl (pj l)))) :=
    ⟨_, rfl⟩
  have hΛa : ∀ t l, Λ t l = k (pi l) (pj l) * t (r (Sum.inl (pi l)), c (Sum.inl (pj l))) := by
    intro t l
    subst hΛ
    rfl
  have hinj : blkL L r c ⊓ LinearMap.ker Λ = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨ht, hk0⟩
    replace hk0 := LinearMap.mem_ker.mp hk0
    rw [Submodule.mem_bot]
    apply h0 t ht
    intro i j
    have e := hM t ht i j
    have hz : ∀ l, k (pi l) (pj l) * t (r (Sum.inl (pi l)), c (Sum.inl (pj l))) = 0 := by
      intro l
      have e2 := congrFun hk0 l
      rw [hΛa] at e2
      exact e2
    simp only [hz, mul_zero, Finset.sum_const_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (hk i j)
  have hrn := rank_nullity (blkL L r c) Λ
  rw [hinj, finrank_bot, zero_add] at hrn
  have hb3 := blkL_finrank L r c
  rw [h9] at hb3
  have hle := Submodule.finrank_le ((blkL L r c).map Λ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
  have htop : (blkL L r c).map Λ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hx : x0 ∈ (blkL L r c).map Λ := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨t0, ht0, htx⟩ := hx
  have hw := ell_ne_of_small r c h9 (by omega)
  have hb := stest_blk hL r c hw t0 ht0
  apply hperm
  have e : (Matrix.of fun i j => (∑ l, M i j l * x0 l) / k i j) =
      Matrix.of fun i j => t0 (r (Sum.inl i), c (Sum.inl j)) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [div_eq_iff (hk i j), ← htx]
    have e2 := hM t0 ht0 i j
    simp only [hΛa]
    linear_combination -e2
  rw [e]
  exact hb

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
  have hrs : ∀ t ∈ blkL L rr cc, ∀ i : Fin 3,
      κs i (cc (Sum.inl 0)) * t (rr (Sum.inl i), cc (Sum.inl 0)) +
        κs i (cc (Sum.inl 1)) * t (rr (Sum.inl i), cc (Sum.inl 1)) +
        κs i (cc (Sum.inl 2)) * t (rr (Sum.inl i), cc (Sum.inl 2)) = 0 := by
    intro t ht i
    obtain ⟨htL, ht0⟩ := (mem_blkL L rr cc t).mp ht
    have e := sum_supp3 cc (fun m => t (rr (Sum.inl i), m) * κs i m)
      (fun b => by simp only [ht0 i b, zero_mul])
    have f := hFK i t htL
    rw [dotL_apply] at f
    simp only [rowMap_apply] at f
    rw [f] at e
    linear_combination -e
  refine stest_lift3 hL h9 rr cc h0 (fun i j => κs i (cc (Sum.inl j))) (fun i j => hκs i _)
    ![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 0]], ![![0, 0, 1], ![0, 1, 0], ![0, -1, -1]],
      ![![0, 0, 1], ![1, 1, -1], ![-1, -1, 0]]] ![0, 0, 1] ![0, 1, 0] ?_ ![1, 1, 0] ?_
  · intro t ht i j
    have R0 := hrs t ht 0
    have R1 := hrs t ht 1
    have R2 := hrs t ht 2
    obtain ⟨E1, E2, E3⟩ := hrel t ht
    rw [Fin.sum_univ_three]
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl
    · show κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0)) =
        1 * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        0 * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        0 * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      ring
    · show κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1)) =
        0 * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        1 * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        0 * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      ring
    · show κs 0 (cc (Sum.inl 2)) * t (rr (Sum.inl 0), cc (Sum.inl 2)) =
        (-1) * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        (-1) * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        0 * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      linear_combination R0
    · show κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)) =
        0 * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        0 * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        1 * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      ring
    · show κs 1 (cc (Sum.inl 1)) * t (rr (Sum.inl 1), cc (Sum.inl 1)) =
        0 * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        1 * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        0 * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      linear_combination -E1
    · show κs 1 (cc (Sum.inl 2)) * t (rr (Sum.inl 1), cc (Sum.inl 2)) =
        0 * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        (-1) * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        (-1) * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      linear_combination R1 + E1
    · show κs 2 (cc (Sum.inl 0)) * t (rr (Sum.inl 2), cc (Sum.inl 0)) =
        0 * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        0 * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        1 * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      linear_combination -E3
    · show κs 2 (cc (Sum.inl 1)) * t (rr (Sum.inl 2), cc (Sum.inl 1)) =
        1 * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        1 * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        (-1) * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      linear_combination R2 - R0 + E2 + E3
    · show κs 2 (cc (Sum.inl 2)) * t (rr (Sum.inl 2), cc (Sum.inl 2)) =
        (-1) * (κs 0 (cc (Sum.inl 0)) * t (rr (Sum.inl 0), cc (Sum.inl 0))) +
        (-1) * (κs 0 (cc (Sum.inl 1)) * t (rr (Sum.inl 0), cc (Sum.inl 1))) +
        0 * (κs 1 (cc (Sum.inl 0)) * t (rr (Sum.inl 1), cc (Sum.inl 0)))
      linear_combination R0 - E2
  · obtain ⟨a1, a2, a3⟩ := hk1
    obtain ⟨b1, b2, b3⟩ := hk2
    have n0 := hκs 0 (cc (Sum.inl 0))
    have n1 := hκs 0 (cc (Sum.inl 1))
    have n2 := hκs 0 (cc (Sum.inl 2))
    have hval : (Matrix.of fun i j => (∑ l, (![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 0]],
        ![![0, 0, 1], ![0, 1, 0], ![0, -1, -1]], ![![0, 0, 1], ![1, 1, -1], ![-1, -1, 0]]] :
          Fin 3 → Fin 3 → Fin 3 → ℂ) i j l * (![1, 1, 0] : Fin 3 → ℂ) l) /
          κs i (cc (Sum.inl j))).permanent * (d2 * d3 * κs 0 (cc (Sum.inl 0)) *
          κs 0 (cc (Sum.inl 1)) * κs 0 (cc (Sum.inl 2))) = -4 := by
      rw [permanent_three]
      simp only [Matrix.of_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [a1, a2, a3, b1, b2, b3]
      field_simp
      ring
    intro h
    have h' : (Matrix.of fun i j => (∑ l, (![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 0]],
        ![![0, 0, 1], ![0, 1, 0], ![0, -1, -1]], ![![0, 0, 1], ![1, 1, -1], ![-1, -1, 0]]] :
          Fin 3 → Fin 3 → Fin 3 → ℂ) i j l * (![1, 1, 0] : Fin 3 → ℂ) l) /
          κs i (cc (Sum.inl j))).permanent = 0 := h
    rw [h', zero_mul] at hval
    norm_num at hval
theorem two_val_eq (r : Fin 5 → ℂ) (f : ℂ) (C : Finset (Fin 5))
    (h1 : ∀ m, m ∉ C → r m = f) (h2 : ∀ m, m ∈ C → r m = -f) (p q : Fin 5)
    (h : q ∈ C ↔ p ∈ C) : r q = r p := by
  by_cases hp : p ∈ C
  · rw [h2 q (h.mpr hp), h2 p hp]
  · rw [h1 q (fun hq => hp (h.mp hq)), h1 p hp]

theorem two_val_neg' (r : Fin 5 → ℂ) (f : ℂ) (C : Finset (Fin 5))
    (h1 : ∀ m, m ∉ C → r m = f) (h2 : ∀ m, m ∈ C → r m = -f) (p q : Fin 5)
    (h : q ∈ C ↔ p ∉ C) : r q = -r p := by
  by_cases hp : p ∈ C
  · rw [h1 q (fun hq => h.mp hq hp), h2 p hp, neg_neg]
  · rw [h2 q (h.mpr hp), h1 p hp]

theorem two_val_neg (r : Fin 5 → ℂ) (f : ℂ) (hf : f ≠ 0) (C : Finset (Fin 5))
    (h1 : ∀ m, m ∉ C → r m = f) (h2 : ∀ m, m ∈ C → r m = -f) (p q : Fin 5)
    (h : r q = -r p) : q ∈ C ↔ p ∉ C := by
  constructor
  · intro hq hp
    rw [h2 q hq, h2 p hp] at h
    exact hf (by linear_combination (-1 / 2 : ℂ) * h)
  · intro hp
    by_contra hq
    rw [h1 q hq, h1 p hp] at h
    exact hf (by linear_combination (1 / 2 : ℂ) * h)

theorem xor_nonconst (A B Cr : Fin 5 → ℂ) (f2 f3 f23 : ℂ) (hf2 : f2 ≠ 0) (hf23 : f23 ≠ 0)
    (C12 C13 C23 : Finset (Fin 5))
    (hA1 : ∀ m, m ∉ C12 → A m = f2) (hA2 : ∀ m, m ∈ C12 → A m = -f2)
    (hB1 : ∀ m, m ∉ C13 → B m = f3) (hB2 : ∀ m, m ∈ C13 → B m = -f3)
    (hC1 : ∀ m, m ∉ C23 → Cr m = f23) (hC2 : ∀ m, m ∈ C23 → Cr m = -f23)
    (hBCA : ∀ m, B m = Cr m * A m) (u v : Fin 5) (hu : u ∈ C23) (hv : v ∉ C23) :
    ∃ u v, (u ∈ C12 ↔ u ∈ C13) ∧ ¬ (v ∈ C12 ↔ v ∈ C13) := by
  have hCr : Cr u = -Cr v := by rw [hC2 u hu, hC1 v hv]
  have hAv : A v ≠ 0 := by
    by_cases h : v ∈ C12
    · rw [hA2 v h]
      exact neg_ne_zero.mpr hf2
    · rw [hA1 v h]
      exact hf2
  have fin : (Cr u - Cr v) * A v = 0 → False := by
    intro e
    have h3 : Cr v * A v = 0 := by linear_combination (-1 / 2 : ℂ) * e + (A v / 2) * hCr
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rw [hC1 v hv] at h4
      exact hf23 h4
    · exact hAv h4
  have e1 := hBCA u
  have e2 := hBCA v
  by_cases h1 : u ∈ C12 ↔ v ∈ C12 <;> by_cases h2 : u ∈ C13 ↔ v ∈ C13
  · exfalso
    have eA := two_val_eq A f2 C12 hA1 hA2 v u h1
    have eB := two_val_eq B f3 C13 hB1 hB2 v u h2
    exact fin (by linear_combination -e1 + e2 + eB - Cr u * eA)
  · by_cases hu' : u ∈ C12 ↔ u ∈ C13
    · exact ⟨u, v, hu', by tauto⟩
    · exact ⟨v, u, by tauto, hu'⟩
  · by_cases hu' : u ∈ C12 ↔ u ∈ C13
    · exact ⟨u, v, hu', by tauto⟩
    · exact ⟨v, u, by tauto, hu'⟩
  · exfalso
    have eA := two_val_neg' A f2 C12 hA1 hA2 v u (by tauto)
    have eB := two_val_neg' B f3 C13 hB1 hB2 v u (by tauto)
    exact fin (by linear_combination e1 - eB + e2 + Cr u * eA)

theorem comb_pqs (X Y : Fin 5 → Prop) (hX1 : ∃ m, X m) (hX2 : ∃ m, ¬ X m) (hY1 : ∃ m, Y m)
    (hY2 : ∃ m, ¬ Y m) (hXY : ∃ u v, (X u ↔ Y u) ∧ ¬ (X v ↔ Y v)) :
    ∃ p q s, (X q ↔ ¬ X p) ∧ (Y q ↔ Y p) ∧ (X s ↔ X p) ∧ (Y s ↔ ¬ Y p) := by
  classical
  obtain ⟨u, v, hu, hv⟩ := hXY
  by_cases hx : X u ↔ X v
  · obtain ⟨w, hw⟩ : ∃ w, X w ↔ ¬ X u := by
      by_cases h : X u
      · obtain ⟨m, hm⟩ := hX2
        exact ⟨m, by tauto⟩
      · obtain ⟨m, hm⟩ := hX1
        exact ⟨m, by tauto⟩
    by_cases hy : Y w ↔ Y u
    · exact ⟨u, w, v, by tauto⟩
    · exact ⟨v, w, u, by tauto⟩
  · obtain ⟨w, hw⟩ : ∃ w, Y w ↔ ¬ Y u := by
      by_cases h : Y u
      · obtain ⟨m, hm⟩ := hY2
        exact ⟨m, by tauto⟩
      · obtain ⟨m, hm⟩ := hY1
        exact ⟨m, by tauto⟩
    by_cases hw2 : X w ↔ X u
    · exact ⟨u, v, w, by tauto⟩
    · exact ⟨v, u, w, by tauto⟩

theorem pair_local (κa κb : Fin 5 → ℂ) (C : Finset (Fin 5)) (ra rb : Fin 5)
    (t : Fin 5 × Fin 5 → ℂ) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hoff : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (ra, m) = 0 ∧ t (rb, m) = 0)
    (Fa : dotL κa (rowMap ra t) = 0) (Fb : dotL κb (rowMap rb t) = 0)
    (rel : ∑ m ∈ C, t (ra, m) * κa m = ∑ m ∈ C, t (rb, m) * κb m)
    (hq : q ∈ C ↔ p ∉ C) (hs : s ∈ C ↔ p ∈ C) :
    t (ra, q) * κa q = t (rb, q) * κb q := by
  have va : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (ra, m) * κa m = 0 := fun m h1 h2 h3 => by
    rw [(hoff m h1 h2 h3).1, zero_mul]
  have vb : ∀ m, m ≠ p → m ≠ q → m ≠ s → t (rb, m) * κb m = 0 := fun m h1 h2 h3 => by
    rw [(hoff m h1 h2 h3).2, zero_mul]
  have Sa := sum_C_three Finset.univ p q s hpq hps hqs _ va
  have Sb := sum_C_three Finset.univ p q s hpq hps hqs _ vb
  simp only [Finset.mem_univ, ite_true] at Sa Sb
  rw [dotL_apply] at Fa Fb
  simp only [rowMap_apply] at Fa Fb
  rw [Fa] at Sa
  rw [Fb] at Sb
  rw [sum_C_three C p q s hpq hps hqs _ va, sum_C_three C p q s hpq hps hqs _ vb] at rel
  by_cases hp : p ∈ C
  · have hq' : q ∉ C := fun h => hq.mp h hp
    have hs' : s ∈ C := hs.mpr hp
    simp only [hp, hq', hs', ite_true, ite_false, add_zero] at rel
    linear_combination Sb - Sa - rel
  · have hq' : q ∈ C := hq.mpr hp
    have hs' : s ∉ C := fun h => hp (hs.mp h)
    simp only [hp, hq', hs', ite_true, ite_false, zero_add, add_zero] at rel
    exact rel
theorem t1_III {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (z1 : ZF L r1) (z2 : ZF L r2) (z3 : ZF L r3)
    (hp : PairI L r1 r2) (hq : PairI L r1 r3) (hr : PairI L r2 r3)
    (h0 : rowsZeroS L {r1, r2, r3} = ⊥) : False := by
  obtain ⟨κ, κ2, ν, ν', a, b, hκL, hκ1, hκ2L, hκ21, hνL, hν1, hκ0, hκ20, hcl, hI⟩ := hp
  obtain ⟨κ', κ3, μ, μ', a', b', hκ'L, hκ'1, hκ3L, hκ31, hμL, hμ1, hκ'0, hκ30, hcl', hI'⟩ := hq
  obtain ⟨κ2', κ3', ξ, ξ', a'', b'', hκ2'L, hκ2'1, hκ3'L, hκ3'1, hξL, hξ1, hκ2'0, hκ3'0,
    hcl'', hI''⟩ := hr
  have e1 : κ = κ' := (fk_unique hL r1 z1.1 κ κ' hκL hκ1 hκ'L hκ'1).symm
  have e2 : κ2 = κ2' := (fk_unique hL r2 z2.1 κ2 κ2' hκ2L hκ21 hκ2'L hκ2'1).symm
  have e3 : κ3 = κ3' := (fk_unique hL r3 z3.1 κ3 κ3' hκ3L hκ31 hκ3'L hκ3'1).symm
  subst e1
  subst e2
  subst e3
  classical
  obtain ⟨C12, hC12⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ν m / κ m = ν b / κ b :=
    ⟨Finset.univ.filter (fun m => ν m / κ m = ν b / κ b), fun m => by simp⟩
  obtain ⟨C13, hC13⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ μ m / κ m = μ b' / κ b' :=
    ⟨Finset.univ.filter (fun m => μ m / κ m = μ b' / κ b'), fun m => by simp⟩
  obtain ⟨C23, hC23⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ξ m / κ2 m = ξ b'' / κ2 b'' :=
    ⟨Finset.univ.filter (fun m => ξ m / κ2 m = ξ b'' / κ2 b''), fun m => by simp⟩
  obtain ⟨⟨f2, hf2, hf2a, hf2b⟩, hrel12, hC12a⟩ :=
    typeI_nf r1 r2 κ κ2 ν ν' a b hκL hκ2L hνL hκ0 hκ20 hcl hI C12 hC12
  obtain ⟨⟨f3, hf3, hf3a, hf3b⟩, hrel13, hC13a⟩ :=
    typeI_nf r1 r3 κ κ3 μ μ' a' b' hκL hκ3L hμL hκ0 hκ30 hcl' hI' C13 hC13
  obtain ⟨⟨f23, hf23, hf23a, hf23b⟩, hrel23, hC23a⟩ :=
    typeI_nf r2 r3 κ2 κ3 ξ ξ' a'' b'' hκ2L hκ3L hξL hκ20 hκ30 hcl'' hI'' C23 hC23
  have rA1 : ∀ m, m ∉ C12 → κ2 m / κ m = f2 := fun m hm => by
    rw [hf2a m hm, mul_div_assoc, div_self (hκ0 m), mul_one]
  have rA2 : ∀ m, m ∈ C12 → κ2 m / κ m = -f2 := fun m hm => by
    rw [hf2b m hm, mul_div_assoc, div_self (hκ0 m), mul_one]
  have rB1 : ∀ m, m ∉ C13 → κ3 m / κ m = f3 := fun m hm => by
    rw [hf3a m hm, mul_div_assoc, div_self (hκ0 m), mul_one]
  have rB2 : ∀ m, m ∈ C13 → κ3 m / κ m = -f3 := fun m hm => by
    rw [hf3b m hm, mul_div_assoc, div_self (hκ0 m), mul_one]
  have rC1 : ∀ m, m ∉ C23 → κ3 m / κ2 m = f23 := fun m hm => by
    rw [hf23a m hm, mul_div_assoc, div_self (hκ20 m), mul_one]
  have rC2 : ∀ m, m ∈ C23 → κ3 m / κ2 m = -f23 := fun m hm => by
    rw [hf23b m hm, mul_div_assoc, div_self (hκ20 m), mul_one]
  have hBCA : ∀ m, κ3 m / κ m = κ3 m / κ2 m * (κ2 m / κ m) := fun m => by
    rw [div_mul_div_comm, mul_comm (κ3 m) (κ2 m), mul_div_mul_left _ _ (hκ20 m)]
  have hxor := xor_nonconst (fun m => κ2 m / κ m) (fun m => κ3 m / κ m)
    (fun m => κ3 m / κ2 m) f2 f3 f23 hf2 hf23 C12 C13 C23 rA1 rA2 rB1 rB2 rC1 rC2 hBCA b'' a''
    ((hC23 b'').mpr rfl) ((hC23a a'').mpr rfl)
  obtain ⟨p, q, s, hq12, hq13, hs12, hs13⟩ := comb_pqs (fun m => m ∈ C12) (fun m => m ∈ C13)
    ⟨b, (hC12 b).mpr rfl⟩ ⟨a, (hC12a a).mpr rfl⟩ ⟨b', (hC13 b').mpr rfl⟩
    ⟨a', (hC13a a').mpr rfl⟩ hxor
  have hpq : p ≠ q := fun h => by
    rw [h] at hq12
    tauto
  have hps : p ≠ s := fun h => by
    rw [h] at hs13
    tauto
  have hqs : q ≠ s := fun h => by
    rw [h] at hq12
    tauto
  have hAp : κ2 p / κ p ≠ 0 := div_ne_zero (hκ20 p) (hκ0 p)
  have hq23 : q ∈ C23 ↔ p ∉ C23 := by
    have hA_q : κ2 q / κ q = -(κ2 p / κ p) := two_val_neg' _ f2 C12 rA1 rA2 p q hq12
    have hB_q : κ3 q / κ q = κ3 p / κ p := two_val_eq _ f3 C13 rB1 rB2 p q hq13
    have e := hBCA q
    have e' := hBCA p
    rw [hB_q, hA_q, e'] at e
    have e3 : (κ3 q / κ2 q + κ3 p / κ2 p) * (κ2 p / κ p) = 0 := by linear_combination e
    have e4 := (mul_eq_zero.mp e3).resolve_right hAp
    exact two_val_neg _ f23 hf23 C23 rC1 rC2 p q (by linear_combination e4)
  have hs23 : s ∈ C23 ↔ p ∉ C23 := by
    have hA_s : κ2 s / κ s = κ2 p / κ p := two_val_eq _ f2 C12 rA1 rA2 p s hs12
    have hB_s : κ3 s / κ s = -(κ3 p / κ p) := two_val_neg' _ f3 C13 rB1 rB2 p s hs13
    have e := hBCA s
    have e' := hBCA p
    rw [hB_s, hA_s, e'] at e
    have e3 : (κ3 s / κ2 s + κ3 p / κ2 p) * (κ2 p / κ p) = 0 := by linear_combination -e
    have e4 := (mul_eq_zero.mp e3).resolve_right hAp
    exact two_val_neg _ f23 hf23 C23 rC1 rC2 p s (by linear_combination e4)
  obtain ⟨d2, hd2, hk1⟩ : ∃ d2 : ℂ, d2 ≠ 0 ∧
      (κ2 p = d2 * κ p ∧ κ2 q = -d2 * κ q ∧ κ2 s = d2 * κ s) := by
    by_cases hp12 : p ∈ C12
    · exact ⟨-f2, neg_ne_zero.mpr hf2, hf2b p hp12,
        by rw [hf2a q (fun h => hq12.mp h hp12)]; ring, hf2b s (hs12.mpr hp12)⟩
    · exact ⟨f2, hf2, hf2a p hp12, hf2b q (hq12.mpr hp12),
        hf2a s (fun h => hp12 (hs12.mp h))⟩
  obtain ⟨d3, hd3, hk2⟩ : ∃ d3 : ℂ, d3 ≠ 0 ∧
      (κ3 p = d3 * κ p ∧ κ3 q = d3 * κ q ∧ κ3 s = -d3 * κ s) := by
    by_cases hp13 : p ∈ C13
    · exact ⟨-f3, neg_ne_zero.mpr hf3, hf3b p hp13, hf3b q (hq13.mpr hp13),
        by rw [hf3a s (fun h => hs13.mp h hp13)]; ring⟩
    · exact ⟨f3, hf3, hf3a p hp13, hf3a q (fun h => hp13 (hq13.mp h)),
        hf3b s (hs13.mpr hp13)⟩
  obtain ⟨rr, hr0, hr1, hr2⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 p q s hpq hps hqs
  have zrow : ∀ m, m ≠ p → m ≠ q → m ≠ s → ∃ b0, cc (Sum.inr b0) = m := by
    intro m h1 h2 h3
    obtain ⟨y, rfl⟩ := cc.surjective m
    rcases y with j | b0
    · rcases fin3_cases j with rfl | rfl | rfl
      · exact absurd hc0 h1
      · exact absurd hc1 h2
      · exact absurd hc2 h3
    · exact ⟨b0, rfl⟩
  have hoff : ∀ t ∈ blkL L rr cc, ∀ m, m ≠ p → m ≠ q → m ≠ s →
      t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0 := by
    intro t ht m h1 h2 h3
    obtain ⟨b0, rfl⟩ := zrow m h1 h2 h3
    have h := ((mem_blkL L rr cc t).mp ht).2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr0]
      exact h 0 b0
    · rw [← hr1]
      exact h 1 b0
    · rw [← hr2]
      exact h 2 b0
  obtain ⟨K, hK⟩ : ∃ K : Fin 3 → Fin 5 → ℂ, K = ![κ, κ2, κ3] := ⟨_, rfl⟩
  have hK0 : K 0 = κ := by first | (rw [hK]; rfl) | rw [hK]
  have hK1 : K 1 = κ2 := by first | (rw [hK]; rfl) | rw [hK]
  have hK2 : K 2 = κ3 := by first | (rw [hK]; rfl) | rw [hK]
  have h0' : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0 := by
    intro t ht hz
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have hmem : t ∈ rowsZeroS L {r1, r2, r3} := by
      refine ⟨htL, fun r hr m => ?_⟩
      have hri : ∃ i, rr (Sum.inl i) = r := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with h | h | h
        · exact ⟨0, hr0.trans h.symm⟩
        · exact ⟨1, hr1.trans h.symm⟩
        · exact ⟨2, hr2.trans h.symm⟩
      obtain ⟨i, rfl⟩ := hri
      obtain ⟨y, rfl⟩ := cc.surjective m
      rcases y with j | b0
      · exact hz i j
      · exact ((mem_blkL L rr cc t).mp ht).2 i b0
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  refine t1_iii_local hL h9 rr cc h0' K ?_ ?_ d2 d3 hd2 hd3 ?_ ?_ ?_
  · intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0]
      exact hκ0 m
    · rw [hK1]
      exact hκ20 m
    · rw [hK2]
      exact hκ30 m
  · intro i t ht
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0, hr0]
      exact hκL t ht
    · rw [hK1, hr1]
      exact hκ2L t ht
    · rw [hK2, hr2]
      exact hκ3L t ht
  · rw [hK0, hK1, hc0, hc1, hc2]
    exact hk1
  · rw [hK0, hK2, hc0, hc1, hc2]
    exact hk2
  · intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have ho := hoff t ht
    have E1 := pair_local κ κ2 C12 r1 r2 t p q s hpq hps hqs
      (fun m h1 h2 h3 => ⟨(ho m h1 h2 h3).1, (ho m h1 h2 h3).2.1⟩) (hκL t htL) (hκ2L t htL)
      (hrel12 t htL) hq12 hs12
    have E2 := pair_local κ κ3 C13 r1 r3 t p s q hps hpq (Ne.symm hqs)
      (fun m h1 h2 h3 => ⟨(ho m h1 h3 h2).1, (ho m h1 h3 h2).2.2⟩) (hκL t htL) (hκ3L t htL)
      (hrel13 t htL) hs13 hq13
    have E3 := pair_local κ2 κ3 C23 r2 r3 t q p s (Ne.symm hpq) hqs hps
      (fun m h1 h2 h3 => ⟨(ho m h2 h1 h3).2.1, (ho m h2 h1 h3).2.2⟩) (hκ2L t htL) (hκ3L t htL)
      (hrel23 t htL) (by tauto) (by tauto)
    rw [hK0, hK1, hK2, hr0, hr1, hr2, hc0, hc1, hc2]
    exact ⟨by linear_combination E1, by linear_combination E2, by linear_combination E3⟩
def T1Rest : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2 →
    (PairII L r1 r2 ∨ PairII L r1 r3 ∨ PairII L r2 r3) → rowsZeroS L {r1, r2, r3} ≠ ⊥

theorem t1_of_rest (h : T1Rest) : T1Hyp := by
  intro L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 h0
  rcases pair_I_or_II hL r1 r2 h12 (pair_min h9 r1 r2 x12) z1 z2 with p12 | p12
  · rcases pair_I_or_II hL r1 r3 h13 (pair_min h9 r1 r3 x13) z1 z3 with p13 | p13
    · rcases pair_I_or_II hL r2 r3 h23 (pair_min h9 r2 r3 x23) z2 z3 with p23 | p23
      · exact t1_III hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 p12 p13 p23 h0
      · exact h L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 (Or.inr (Or.inr p23)) h0
    · exact h L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 (Or.inr (Or.inl p13)) h0
  · exact h L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 (Or.inl p12) h0
theorem corner_sq {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (hp : PairII L r r') :
    ∃ κ κ' : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (rowMap r t) = 0) ∧ dotL κ 1 = 1 ∧
      (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) ∧ dotL κ' 1 = 1 ∧ (∀ j, κ j ≠ 0) ∧
      (∀ j, κ' j ≠ 0) ∧ ∃ m0 a0 : Fin 5, (κ' m0 / κ m0) ^ 2 = -(κ' a0 / κ a0) ^ 2 := by
  obtain ⟨κ, κ', ν, ν', a, b, h1, h2, h3, h4, h5, h6, h7, h8, hcl, m, hm1, hm2⟩ := hp
  refine ⟨κ, κ', h1, h2, h3, h4, h7, h8, m, a, ?_⟩
  obtain ⟨hab, hab', hσ, hall⟩ := hcl
  rcases hall m with h | h | h
  · exact absurd (hm2.symm.trans h.2.1) (Ne.symm hab')
  · exact absurd (hm1.symm.trans h.1) hab
  · exact h.2.2.2.1

theorem sq_ratio (u v : Fin 5 → ℂ) (f : ℂ) (C : Finset (Fin 5)) (hv : ∀ m, v m ≠ 0)
    (h1 : ∀ m, m ∉ C → u m = f * v m) (h2 : ∀ m, m ∈ C → u m = -f * v m) (m : Fin 5) :
    (u m / v m) ^ 2 = f ^ 2 := by
  by_cases hm : m ∈ C
  · rw [h2 m hm, mul_div_assoc, div_self (hv m), mul_one]
    ring
  · rw [h1 m hm, mul_div_assoc, div_self (hv m), mul_one]

theorem sq_contra (R : Fin 5 → ℂ) (x : ℂ) (hx : x ≠ 0) (hR : ∀ m, R m ^ 2 = x) (m0 a0 : Fin 5)
    (h : R m0 ^ 2 = -(R a0) ^ 2) : False := by
  rw [hR, hR] at h
  exact hx (by linear_combination h / 2)

theorem typeI_ratio {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (r r' : Fin 5) (hp : PairI L r r')
    (κ0 κ0' : Fin 5 → ℂ) (hκ0L : ∀ t ∈ L, dotL κ0 (rowMap r t) = 0) (hκ01 : dotL κ0 1 = 1)
    (hκ0'L : ∀ t ∈ L, dotL κ0' (rowMap r' t) = 0) (hκ0'1 : dotL κ0' 1 = 1)
    (huniq : ∀ κ κ' : Fin 5 → ℂ, (∀ t ∈ L, dotL κ (rowMap r t) = 0) → dotL κ 1 = 1 →
      (∀ t ∈ L, dotL κ' (rowMap r' t) = 0) → dotL κ' 1 = 1 → κ = κ0 ∧ κ' = κ0') :
    ∃ f : ℂ, f ≠ 0 ∧ ∀ m, (κ0' m / κ0 m) ^ 2 = f ^ 2 := by
  classical
  obtain ⟨κ, κ', ν, ν', a, b, h1, h2, h3, h4, h5, h6, h7, h8, hcl, hI⟩ := hp
  obtain ⟨e1, e2⟩ := huniq κ κ' h1 h2 h3 h4
  rw [← e1, ← e2]
  obtain ⟨C, hC⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ν m / κ m = ν b / κ b :=
    ⟨Finset.univ.filter (fun m => ν m / κ m = ν b / κ b), fun m => by simp⟩
  obtain ⟨⟨f, hf, hfa, hfb⟩, _, _⟩ := typeI_nf r r' κ κ' ν ν' a b h1 h3 h5 h7 h8 hcl hI C hC
  exact ⟨f, hf, fun m => sq_ratio κ' κ f C h7 hfa hfb m⟩

theorem t1_one_II {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (r1 r2 r3 : Fin 5)
    (z1 : ZF L r1) (z2 : ZF L r2) (z3 : ZF L r3)
    (hI : (PairI L r1 r2 ∧ PairI L r1 r3 ∧ PairII L r2 r3) ∨
      (PairII L r1 r2 ∧ PairI L r1 r3 ∧ PairI L r2 r3) ∨
      (PairI L r1 r2 ∧ PairII L r1 r3 ∧ PairI L r2 r3)) : False := by
  obtain ⟨κ, hκL, hκ1⟩ := fk_annihilator hL r1
  obtain ⟨κ2, hκ2L, hκ21⟩ := fk_annihilator hL r2
  obtain ⟨κ3, hκ3L, hκ31⟩ := fk_annihilator hL r3
  have u1 : ∀ k, (∀ t ∈ L, dotL k (rowMap r1 t) = 0) → dotL k 1 = 1 → k = κ :=
    fun k hk hk1 => fk_unique hL r1 z1.1 κ k hκL hκ1 hk hk1
  have u2 : ∀ k, (∀ t ∈ L, dotL k (rowMap r2 t) = 0) → dotL k 1 = 1 → k = κ2 :=
    fun k hk hk1 => fk_unique hL r2 z2.1 κ2 k hκ2L hκ21 hk hk1
  have u3 : ∀ k, (∀ t ∈ L, dotL k (rowMap r3 t) = 0) → dotL k 1 = 1 → k = κ3 :=
    fun k hk hk1 => fk_unique hL r3 z3.1 κ3 k hκ3L hκ31 hk hk1
  have n1 : ∀ m, κ m ≠ 0 := z1.2 κ hκL hκ1
  have n2 : ∀ m, κ2 m ≠ 0 := z2.2 κ2 hκ2L hκ21
  have n3 : ∀ m, κ3 m ≠ 0 := z3.2 κ3 hκ3L hκ31
  rcases hI with ⟨p12, p13, p23⟩ | ⟨p12, p13, p23⟩ | ⟨p12, p13, p23⟩
  · obtain ⟨f2, hf2, s2⟩ := typeI_ratio r1 r2 p12 κ κ2 hκL hκ1 hκ2L hκ21
      (fun k k' a b c d => ⟨u1 k a b, u2 k' c d⟩)
    obtain ⟨f3, hf3, s3⟩ := typeI_ratio r1 r3 p13 κ κ3 hκL hκ1 hκ3L hκ31
      (fun k k' a b c d => ⟨u1 k a b, u3 k' c d⟩)
    obtain ⟨k, k', a1, b1, c1, d1, _, _, m0, a0, hsq⟩ := corner_sq r2 r3 p23
    have e1 := u2 k a1 b1
    have e2 := u3 k' c1 d1
    rw [e1, e2] at hsq
    refine sq_contra (fun m => κ3 m / κ2 m) (f3 ^ 2 / f2 ^ 2)
      (div_ne_zero (pow_ne_zero 2 hf3) (pow_ne_zero 2 hf2)) (fun m => ?_) m0 a0 hsq
    have e : κ3 m / κ2 m = (κ3 m / κ m) / (κ2 m / κ m) := by
      rw [div_div_div_cancel_right₀ (n1 m)]
    show (κ3 m / κ2 m) ^ 2 = f3 ^ 2 / f2 ^ 2
    rw [e, div_pow, s3 m, s2 m]
  · obtain ⟨f3, hf3, s3⟩ := typeI_ratio r1 r3 p13 κ κ3 hκL hκ1 hκ3L hκ31
      (fun k k' a b c d => ⟨u1 k a b, u3 k' c d⟩)
    obtain ⟨f23, hf23, s23⟩ := typeI_ratio r2 r3 p23 κ2 κ3 hκ2L hκ21 hκ3L hκ31
      (fun k k' a b c d => ⟨u2 k a b, u3 k' c d⟩)
    obtain ⟨k, k', a1, b1, c1, d1, _, _, m0, a0, hsq⟩ := corner_sq r1 r2 p12
    have e1 := u1 k a1 b1
    have e2 := u2 k' c1 d1
    rw [e1, e2] at hsq
    refine sq_contra (fun m => κ2 m / κ m) (f3 ^ 2 / f23 ^ 2)
      (div_ne_zero (pow_ne_zero 2 hf3) (pow_ne_zero 2 hf23)) (fun m => ?_) m0 a0 hsq
    have e : κ2 m / κ m = (κ3 m / κ m) / (κ3 m / κ2 m) := by
      rw [div_div_div_cancel_left₀ _ _ (n3 m)]
    show (κ2 m / κ m) ^ 2 = f3 ^ 2 / f23 ^ 2
    rw [e, div_pow, s3 m, s23 m]
  · obtain ⟨f2, hf2, s2⟩ := typeI_ratio r1 r2 p12 κ κ2 hκL hκ1 hκ2L hκ21
      (fun k k' a b c d => ⟨u1 k a b, u2 k' c d⟩)
    obtain ⟨f23, hf23, s23⟩ := typeI_ratio r2 r3 p23 κ2 κ3 hκ2L hκ21 hκ3L hκ31
      (fun k k' a b c d => ⟨u2 k a b, u3 k' c d⟩)
    obtain ⟨k, k', a1, b1, c1, d1, _, _, m0, a0, hsq⟩ := corner_sq r1 r3 p13
    have e1 := u1 k a1 b1
    have e2 := u3 k' c1 d1
    rw [e1, e2] at hsq
    refine sq_contra (fun m => κ3 m / κ m) (f23 ^ 2 * f2 ^ 2)
      (mul_ne_zero (pow_ne_zero 2 hf23) (pow_ne_zero 2 hf2)) (fun m => ?_) m0 a0 hsq
    have e : κ3 m / κ m = (κ3 m / κ2 m) * (κ2 m / κ m) := by
      rw [div_mul_div_comm, mul_comm (κ3 m) (κ2 m), mul_div_mul_left _ _ (n2 m)]
    show (κ3 m / κ m) ^ 2 = f23 ^ 2 * f2 ^ 2
    rw [e, mul_pow, s23 m, s2 m]
def T1Rest2 : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
    ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → ZF L r1 → ZF L r2 → ZF L r3 →
    Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
    Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2 →
    ((PairII L r1 r2 ∧ PairII L r1 r3) ∨ (PairII L r1 r2 ∧ PairII L r2 r3) ∨
      (PairII L r1 r3 ∧ PairII L r2 r3)) → rowsZeroS L {r1, r2, r3} ≠ ⊥

theorem t1rest_of_rest2 (h : T1Rest2) : T1Rest := by
  intro L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 _ h0
  have P12 := pair_I_or_II hL r1 r2 h12 (pair_min h9 r1 r2 x12) z1 z2
  have P13 := pair_I_or_II hL r1 r3 h13 (pair_min h9 r1 r3 x13) z1 z3
  have P23 := pair_I_or_II hL r2 r3 h23 (pair_min h9 r2 r3 x23) z2 z3
  rcases P12 with p12 | p12 <;> rcases P13 with p13 | p13 <;> rcases P23 with p23 | p23
  · exact t1_III hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 p12 p13 p23 h0
  · exact t1_one_II hL r1 r2 r3 z1 z2 z3 (Or.inl ⟨p12, p13, p23⟩)
  · exact t1_one_II hL r1 r2 r3 z1 z2 z3 (Or.inr (Or.inr ⟨p12, p13, p23⟩))
  · exact h L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 (Or.inr (Or.inr ⟨p13, p23⟩)) h0
  · exact t1_one_II hL r1 r2 r3 z1 z2 z3 (Or.inr (Or.inl ⟨p12, p13, p23⟩))
  · exact h L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 (Or.inr (Or.inl ⟨p12, p23⟩)) h0
  · exact h L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 (Or.inl ⟨p12, p13⟩) h0
  · exact h L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 (Or.inl ⟨p12, p13⟩) h0

theorem t1_of_rest2 (h : T1Rest2) : T1Hyp := t1_of_rest (t1rest_of_rest2 h)
theorem corner_unique (κ κ' ν ν' : Fin 5 → ℂ) (a b : Fin 5) (hcl : TypeCl κ κ' ν ν' a b)
    (m m' : Fin 5) (hm : ν m / κ m = ν a / κ a ∧ ν' m / κ' m = ν' b / κ' b)
    (hm' : ν m' / κ m' = ν a / κ a ∧ ν' m' / κ' m' = ν' b / κ' b) :
    κ' m / κ m = κ' m' / κ m' := by
  obtain ⟨hab, hab', hσ, hall⟩ := hcl
  have corner : ∀ x, ν x / κ x = ν a / κ a ∧ ν' x / κ' x = ν' b / κ' b →
      ν a / κ a + ν' a / κ' a ≠ 0 ∧
      (ν a / κ a + ν' b / κ' b) ^ 2 = -(ν a / κ a + ν' a / κ' a) ^ 2 ∧
      κ' a / κ a * (ν a / κ a + ν' a / κ' a) +
        κ' x / κ x * (ν a / κ a + ν' b / κ' b) = 0 := by
    intro x hx
    rcases hall x with h | h | h
    · exact absurd (hx.2.symm.trans h.2.1) (Ne.symm hab')
    · exact absurd (hx.1.symm.trans h.1) hab
    · exact ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  obtain ⟨hs, hsq, e1⟩ := corner m hm
  obtain ⟨_, _, e2⟩ := corner m' hm'
  have hc : ν a / κ a + ν' b / κ' b ≠ 0 := by
    intro h0
    rw [h0] at hsq
    apply hs
    have h1 : (ν a / κ a + ν' a / κ' a) ^ 2 = 0 := by linear_combination hsq
    exact (pow_eq_zero_iff two_ne_zero).mp h1
  have e3 : (κ' m / κ m - κ' m' / κ m') * (ν a / κ a + ν' b / κ' b) = 0 := by
    linear_combination e1 - e2
  exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hc)

theorem rule_R (Q1 Q2 Q3 C : Finset (Fin 5)) (hcov : ∀ m, m ∈ Q1 ∨ m ∈ Q2 ∨ m ∈ Q3)
    (h1 : ∃ m, m ∈ Q1) (h2 : ∃ m, m ∈ Q2) (h3 : ∃ m, m ∈ Q3) (hC1 : ∃ m, m ∈ C)
    (hC2 : ∃ m, m ∉ C) :
    ∃ p q s, p ∈ Q1 ∧ q ∈ Q2 ∧ s ∈ Q3 ∧ ¬ ((p ∈ C ↔ q ∈ C) ∧ (q ∈ C ↔ s ∈ C)) := by
  obtain ⟨p0, hp0⟩ := h1
  obtain ⟨q0, hq0⟩ := h2
  obtain ⟨s0, hs0⟩ := h3
  by_cases hsplit : (p0 ∈ C ↔ q0 ∈ C) ∧ (q0 ∈ C ↔ s0 ∈ C)
  · obtain ⟨z, hz⟩ : ∃ z, ¬ (z ∈ C ↔ q0 ∈ C) := by
      by_cases hq : q0 ∈ C
      · obtain ⟨m, hm⟩ := hC2
        exact ⟨m, by tauto⟩
      · obtain ⟨m, hm⟩ := hC1
        exact ⟨m, by tauto⟩
    rcases hcov z with hz1 | hz2 | hz3
    · exact ⟨z, q0, s0, hz1, hq0, hs0, by tauto⟩
    · exact ⟨p0, z, s0, hp0, hz2, hs0, by tauto⟩
    · exact ⟨p0, q0, z, hp0, hq0, hz3, by tauto⟩
  · exact ⟨p0, q0, s0, hp0, hq0, hs0, hsplit⟩

end PEqualNP.Outside.L_gct_210_aux.ZBF

theorem PEqualNP.Outside.L_gct_210 : True := by
  trivial
