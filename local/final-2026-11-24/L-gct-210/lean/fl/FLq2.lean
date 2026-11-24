import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_210_aux.FL

open Finset

noncomputable section

abbrev M55 := Fin 5 × Fin 5 → ℂ

abbrev M45 := Fin 4 × Fin 5 → ℂ

abbrev V4 := Fin 4 → ℂ

theorem sum_emb_perm {n k : ℕ} (σ : Equiv.Perm (Fin k)) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ i : Fin k ↪ Fin n, F (σ.toEmbedding.trans i) = ∑ i : Fin k ↪ Fin n, F i := by
  refine Fintype.sum_bijective (fun i => σ.toEmbedding.trans i)
    ⟨fun i i' h => ?_, fun i => ⟨σ.symm.toEmbedding.trans i, ?_⟩⟩ _ _ (fun i => rfl)
  · refine Function.Embedding.ext fun a => ?_
    have h' := DFunLike.congr_fun h (σ.symm a)
    simpa using h'
  · ext a
    simp

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

theorem rank_nullity {U V : Type} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    [AddCommGroup V] [Module ℂ V] (L : Submodule ℂ U) (f : U →ₗ[ℂ] V) :
    Module.finrank ℂ L = Module.finrank ℂ (L ⊓ LinearMap.ker f : Submodule ℂ U) +
      Module.finrank ℂ (L.map f) := by
  have hrn : Module.finrank ℂ (L.map f) +
      Module.finrank ℂ (L ⊓ LinearMap.ker f : Submodule ℂ U) = Module.finrank ℂ L := by
    rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
      ← (f.submoduleMap L).finrank_range_add_finrank_ker,
      LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]
    simp
  omega

def sumZero (n : ℕ) : Submodule ℂ (Fin n → ℂ) :=
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

theorem fin5 (P : Fin 5 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) :
    ∀ m, P m := by
  intro m
  fin_cases m
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

abbrev T4 := Fin 5 × Fin 5 × Fin 5 × Fin 5

def tup : T4 ≃ (Fin 4 → Fin 5) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun z := (z 0, z 1, z 2, z 3)
  left_inv _ := rfl
  right_inv z := by
    ext i
    fin_cases i <;> rfl

theorem emb4 (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    ∑ e : Fin 4 ↪ Fin 5, F (e 0) (e 1) (e 2) (e 3) = ∑ j, ∑ l, ∑ m, ∑ n,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else F j l m n := by
  classical
  let u (z : Fin 4 → Fin 5) : ℂ := F (z 0) (z 1) (z 2) (z 3)
  have A : ∑ e : Fin 4 ↪ Fin 5, F (e 0) (e 1) (e 2) (e 3) =
      ∑ z : Fin 4 → Fin 5, if Function.Injective z then u z else 0 := by
    let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)
    change (∑ e : Fin 4 ↪ Fin 5, u e) = _
    rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 5 => u e), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) u).symm
  rw [A, ← tup.sum_comp (fun z => if Function.Injective z then u z else 0)]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  let z := tup (a, b, c, d)
  have p : z 0 = a := rfl
  have q : z 1 = b := rfl
  have s : z 2 = c := rfl
  have t : z 3 = d := rfl
  have f : Function.Injective z ↔ ¬(a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) := by
    constructor
    · intro o
      have h (i j : Fin 4) (g : i ≠ j) : z i ≠ z j := fun h => g (o h)
      exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
        (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
          (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
    · intro g i j v
      simp only [not_or] at g
      fin_cases i <;> fin_cases j <;> first | rfl | grind
  change (if Function.Injective z then u z else 0) = _
  by_cases g : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d
  · have k : ¬Function.Injective z := fun h => f.mp h g
    rw [if_neg k, if_pos g]
  · rw [if_pos (f.mpr g), if_neg g]
    rfl

def P4 (a : Fin 5) (N : M45) : ℂ :=
  ∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
    N (0, e 0) * N (1, e 1) * N (2, e 2) * N (3, e 3) else 0

theorem P4_eq (a : Fin 5) (N : M45) : P4 a N = ∑ j, ∑ l, ∑ m, ∑ n,
    if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
      if (j ≠ a ∧ l ≠ a ∧ m ≠ a ∧ n ≠ a) then N (0, j) * N (1, l) * N (2, m) * N (3, n) else 0 :=
  emb4 (fun j l m n => if (j ≠ a ∧ l ≠ a ∧ m ≠ a ∧ n ≠ a) then
    N (0, j) * N (1, l) * N (2, m) * N (3, n) else 0)

def SLev (K : Submodule ℂ M45) : Prop :=
  ∀ Y ∈ K, ∀ a : Fin 5, P4 a (fun p => 1 + Y p) = 24

theorem perm5_row (r : Fin 5) (M : M55) :
    ∑ f : Fin 5 ↪ Fin 5, ∏ i, M (i, f i) =
      ∑ a, M (r, a) * P4 a (fun p => M (r.succAbove p.1, p.2)) := by
  have h1 : ∑ f : Fin 5 ↪ Fin 5, ∏ i, M (i, f i) =
      ∑ g : Fin 5 ↪ Fin 5, ∏ i, M (r.cycleRange.symm i, g i) := by
    refine Eq.trans ?_ (sum_emb_perm r.cycleRange.symm
      (fun g : Fin 5 ↪ Fin 5 => ∏ i, M (r.cycleRange.symm i, g i)))
    refine Finset.sum_congr rfl fun f _ => ?_
    exact (Equiv.prod_comp r.cycleRange.symm (fun j => M (j, f j))).symm
  have h2 : ∀ g : Fin 5 ↪ Fin 5, ∏ i, M (r.cycleRange.symm i, g i) =
      M (r, g 0) * ∏ b : Fin 4, M (r.succAbove b, g b.succ) := by
    intro g
    rw [Fin.prod_univ_succ]
    simp only [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]
  rw [h1]
  refine (Finset.sum_congr rfl (fun g _ => h2 g)).trans ?_
  refine (sum_emb_succ (fun a e => M (r, a) * ∏ b : Fin 4, M (r.succAbove b, e b))).trans ?_
  simp only [P4, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.prod_univ_four]
  by_cases h : ∀ b, e b ≠ a
  · rw [if_pos h, if_pos ⟨h 0, h 1, h 2, h 3⟩]
  · have h' : ¬(e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) := by
      intro hh
      apply h
      intro b
      fin_cases b
      · exact hh.1
      · exact hh.2.1
      · exact hh.2.2.1
      · exact hh.2.2.2
    rw [if_neg h, if_neg h', mul_zero]

def rowMat (r : Fin 5) (w : Fin 5 → ℂ) : M55 := fun p => if p.1 = r then w p.2 else 0

def del (r : Fin 5) : M55 →ₗ[ℂ] M45 :=
  LinearMap.funLeft ℂ ℂ (fun p : Fin 4 × Fin 5 => (r.succAbove p.1, p.2))

def rowP (r : Fin 5) : M55 →ₗ[ℂ] (Fin 5 → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun j : Fin 5 => (r, j))

theorem del_apply (r : Fin 5) (t : M55) (p : Fin 4 × Fin 5) :
    del r t p = t (r.succAbove p.1, p.2) := rfl

theorem rowP_apply (r : Fin 5) (t : M55) (j : Fin 5) : rowP r t j = t (r, j) := rfl

theorem level_row (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → rowMat r w ∈ L)
    (y : M55) (hy : y ∈ L) (w : Fin 5 → ℂ) (hw : ∑ j, w j = 0) (c : ℂ) :
    ∑ a, (1 + c * y (r, a) + w a) * P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) = 120 := by
  have hm : c • y + rowMat r w ∈ L := L.add_mem (L.smul_mem c hy) (hF w hw)
  have h := hL _ hm
  have h2 := perm5_row r (fun p => 1 + (c • y + rowMat r w) p)
  have h3 : ∑ a, (1 + (c • y + rowMat r w) (r, a)) *
      P4 a (fun p => 1 + (c • y + rowMat r w) (r.succAbove p.1, p.2)) = 120 := h2.symm.trans h
  rw [← h3]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • y + rowMat r w) (r.succAbove p.1, p.2)) =
      fun p => 1 + c * y (r.succAbove p.1, p.2) := by
    funext p
    simp [rowMat, Fin.succAbove_ne]
  have e2 : (c • y + rowMat r w) (r, a) = c * y (r, a) + w a := by
    simp [rowMat]
  rw [e1, e2, add_assoc]

theorem propR (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → rowMat r w ∈ L)
    (y : M55) (hy : y ∈ L) :
    (∑ a, y (r, a) = 0) ∧ ∀ a, P4 a (fun p => 1 + y (r.succAbove p.1, p.2)) = 24 := by
  have base : ∀ c : ℂ, ∑ a, (1 + c * y (r, a)) *
      P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) = 120 := by
    intro c
    have h := level_row L hL r hF y hy (fun _ => 0) (by simp) c
    simpa using h
  have eqc : ∀ (c : ℂ) (a b : Fin 5), P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) =
      P4 b (fun p => 1 + c * y (r.succAbove p.1, p.2)) := by
    intro c a b
    have hw : ∑ j : Fin 5, ((if j = a then (1 : ℂ) else 0) - (if j = b then (1 : ℂ) else 0)) = 0 := by
      simp [Finset.sum_sub_distrib]
    have h := level_row L hL r hF y hy
      (fun j => (if j = a then (1 : ℂ) else 0) - (if j = b then (1 : ℂ) else 0)) hw c
    have h3 : ∑ x, (1 + c * y (r, x) + ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0))) *
        P4 x (fun p => 1 + c * y (r.succAbove p.1, p.2)) =
        ∑ x, (1 + c * y (r, x)) * P4 x (fun p => 1 + c * y (r.succAbove p.1, p.2)) +
        (P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) -
          P4 b (fun p => 1 + c * y (r.succAbove p.1, p.2))) := by
      simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hb := base c
    linear_combination h - hb - h3
  have key : ∀ c : ℂ, (5 + c * ∑ a, y (r, a)) *
      P4 0 (fun p => 1 + c * y (r.succAbove p.1, p.2)) = 120 := by
    intro c
    have e5 : (5 : ℂ) + c * ∑ a, y (r, a) = ∑ a : Fin 5, (1 + c * y (r, a)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [← base c, e5, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [eqc c a 0]
  have hρ : ∑ a, y (r, a) = 0 := by
    by_contra hne
    have h := key (-5 / ∑ a, y (r, a))
    have e : (-5 / ∑ a, y (r, a)) * ∑ a, y (r, a) = -5 := by
      field_simp
    rw [e] at h
    norm_num at h
  refine ⟨hρ, fun a => ?_⟩
  have h := key 1
  rw [hρ] at h
  have h1 := eqc 1 a 0
  simp only [one_mul] at h h1
  rw [h1]
  linear_combination (1 / 5 : ℂ) * h

theorem stageA (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → rowMat r w ∈ L) :
    SLev (L.map (del r)) ∧
    SLev ((L ⊓ LinearMap.ker (rowP r)).map (del r)) ∧
    Module.finrank ℂ L ≤
      4 + Module.finrank ℂ ((L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55).map (del r)) := by
  have hS : SLev (L.map (del r)) := by
    intro Y hY a
    obtain ⟨y, hy, rfl⟩ := hY
    exact (propR L hL r hF y hy).2 a
  refine ⟨hS, ?_, ?_⟩
  · intro Y hY a
    exact hS Y (Submodule.map_mono inf_le_left hY) a
  · have h1 := rank_nullity L (rowP r)
    have h2 : L.map (rowP r) ≤ sumZero 5 := by
      rintro v ⟨y, hy, rfl⟩
      rw [mem_sumZero]
      exact (propR L hL r hF y hy).1
    have h3 := (Submodule.finrank_mono h2).trans (finrank_sumZero (n := 5) (by norm_num))
    have h4 := rank_nullity (L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55) (del r)
    have h5 : ((L ⊓ LinearMap.ker (rowP r)) ⊓ LinearMap.ker (del r) : Submodule ℂ M55) = ⊥ := by
      rw [eq_bot_iff]
      rintro t ⟨⟨_, ht1⟩, ht2⟩
      rw [Submodule.mem_bot]
      rw [SetLike.mem_coe, LinearMap.mem_ker] at ht1 ht2
      funext ⟨i, j⟩
      by_cases hi : i = r
      · have := congrFun ht1 j
        rw [rowP_apply] at this
        rw [hi]
        exact this
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hi
        have := congrFun ht2 (k, j)
        rw [del_apply] at this
        rw [← hk]
        exact this
    rw [h5, finrank_bot] at h4
    omega

def tau (z : V4) : ℂ := z 0 + z 1 + z 2 + z 3

def ip (x y : V4) : ℂ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def t3 (x y z : V4) : ℂ := x 0 * y 0 * z 0 + x 1 * y 1 * z 1 + x 2 * y 2 * z 2 + x 3 * y 3 * z 3

def t4 (x y z w : V4) : ℂ :=
  x 0 * y 0 * z 0 * w 0 + x 1 * y 1 * z 1 * w 1 + x 2 * y 2 * z 2 * w 2 + x 3 * y 3 * z 3 * w 3

def br (x y z w : V4) : ℂ :=
  -6 * t4 x y z w + ip x y * ip z w + ip x z * ip y w + ip x w * ip y z

def col (N : M45) (m : Fin 5) : V4 := fun i => N (i, m)

def pc (z1 z2 z3 z4 : V4) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l then 0
    else z1 i * z2 j * z3 k * z4 l

theorem P4_c0 (N : M45) : P4 0 N = pc (col N 1) (col N 2) (col N 3) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem P4_c1 (N : M45) : P4 1 N = pc (col N 0) (col N 2) (col N 3) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem P4_c2 (N : M45) : P4 2 N = pc (col N 0) (col N 1) (col N 3) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem P4_c3 (N : M45) : P4 3 N = pc (col N 0) (col N 1) (col N 2) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem P4_c4 (N : M45) : P4 4 N = pc (col N 0) (col N 1) (col N 2) (col N 3) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem sa0 : (0 : Fin 5).succAbove (0 : Fin 4) = 1 ∧ (0 : Fin 5).succAbove (1 : Fin 4) = 2 ∧
    (0 : Fin 5).succAbove (2 : Fin 4) = 3 ∧ (0 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa1 : (1 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (1 : Fin 5).succAbove (1 : Fin 4) = 2 ∧
    (1 : Fin 5).succAbove (2 : Fin 4) = 3 ∧ (1 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa2 : (2 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (2 : Fin 5).succAbove (1 : Fin 4) = 1 ∧
    (2 : Fin 5).succAbove (2 : Fin 4) = 3 ∧ (2 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa3 : (3 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (3 : Fin 5).succAbove (1 : Fin 4) = 1 ∧
    (3 : Fin 5).succAbove (2 : Fin 4) = 2 ∧ (3 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa4 : (4 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (4 : Fin 5).succAbove (1 : Fin 4) = 1 ∧
    (4 : Fin 5).succAbove (2 : Fin 4) = 2 ∧ (4 : Fin 5).succAbove (3 : Fin 4) = 3 := by decide

theorem P4_cols (m : Fin 5) (N : M45) : P4 m N = pc (col N (m.succAbove 0)) (col N (m.succAbove 1))
    (col N (m.succAbove 2)) (col N (m.succAbove 3)) := by
  revert m
  apply fin5
  · rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2]
    exact P4_c0 N
  · rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2]
    exact P4_c1 N
  · rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2]
    exact P4_c2 N
  · rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2]
    exact P4_c3 N
  · rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2]
    exact P4_c4 N

theorem pc_tau (z1 z2 z3 z4 : V4) : pc z1 z2 z3 z4 =
    tau z1 * tau z2 * tau z3 * tau z4
    - (ip z1 z2 * tau z3 * tau z4 + ip z1 z3 * tau z2 * tau z4 + ip z1 z4 * tau z2 * tau z3
      + ip z2 z3 * tau z1 * tau z4 + ip z2 z4 * tau z1 * tau z3 + ip z3 z4 * tau z1 * tau z2)
    + 2 * (tau z1 * t3 z2 z3 z4 + tau z2 * t3 z1 z3 z4 + tau z3 * t3 z1 z2 z4
      + tau z4 * t3 z1 z2 z3)
    + br z1 z2 z3 z4 := by
  simp (config := {decide := true}) only [pc, tau, ip, t3, t4, br, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem pc_expand (z1 z2 z3 z4 : V4) (c : ℂ) :
    pc (fun i => 1 + c * z1 i) (fun i => 1 + c * z2 i) (fun i => 1 + c * z3 i)
      (fun i => 1 + c * z4 i) =
    24 + c * (6 * (tau z1 + tau z2 + tau z3 + tau z4))
    + c ^ 2 * (2 * (tau z1 * tau z2 + tau z1 * tau z3 + tau z1 * tau z4 + tau z2 * tau z3
        + tau z2 * tau z4 + tau z3 * tau z4)
      - 2 * (ip z1 z2 + ip z1 z3 + ip z1 z4 + ip z2 z3 + ip z2 z4 + ip z3 z4))
    + c ^ 3 * ((tau z1 * tau z2 * tau z3 - tau z1 * ip z2 z3 - tau z2 * ip z1 z3
          - tau z3 * ip z1 z2 + 2 * t3 z1 z2 z3)
        + (tau z1 * tau z2 * tau z4 - tau z1 * ip z2 z4 - tau z2 * ip z1 z4
          - tau z4 * ip z1 z2 + 2 * t3 z1 z2 z4)
        + (tau z1 * tau z3 * tau z4 - tau z1 * ip z3 z4 - tau z3 * ip z1 z4
          - tau z4 * ip z1 z3 + 2 * t3 z1 z3 z4)
        + (tau z2 * tau z3 * tau z4 - tau z2 * ip z3 z4 - tau z3 * ip z2 z4
          - tau z4 * ip z2 z3 + 2 * t3 z2 z3 z4))
    + c ^ 4 * pc z1 z2 z3 z4 := by
  simp (config := {decide := true}) only [pc, tau, ip, t3, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem coeffs (z1 z2 z3 z4 : V4)
    (h : ∀ c : ℂ, pc (fun i => 1 + c * z1 i) (fun i => 1 + c * z2 i) (fun i => 1 + c * z3 i)
      (fun i => 1 + c * z4 i) = 24) :
    tau z1 + tau z2 + tau z3 + tau z4 = 0 ∧
    (2 * (tau z1 * tau z2 + tau z1 * tau z3 + tau z1 * tau z4 + tau z2 * tau z3
        + tau z2 * tau z4 + tau z3 * tau z4)
      - 2 * (ip z1 z2 + ip z1 z3 + ip z1 z4 + ip z2 z3 + ip z2 z4 + ip z3 z4) = 0) ∧
    ((tau z1 * tau z2 * tau z3 - tau z1 * ip z2 z3 - tau z2 * ip z1 z3
          - tau z3 * ip z1 z2 + 2 * t3 z1 z2 z3)
        + (tau z1 * tau z2 * tau z4 - tau z1 * ip z2 z4 - tau z2 * ip z1 z4
          - tau z4 * ip z1 z2 + 2 * t3 z1 z2 z4)
        + (tau z1 * tau z3 * tau z4 - tau z1 * ip z3 z4 - tau z3 * ip z1 z4
          - tau z4 * ip z1 z3 + 2 * t3 z1 z3 z4)
        + (tau z2 * tau z3 * tau z4 - tau z2 * ip z3 z4 - tau z3 * ip z2 z4
          - tau z4 * ip z2 z3 + 2 * t3 z2 z3 z4) = 0) ∧
    pc z1 z2 z3 z4 = 0 := by
  have e1 := h 1
  have e2 := h (-1)
  have e3 := h 2
  have e4 := h (-2)
  rw [pc_expand] at e1 e2 e3 e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 9 : ℂ) * (e1 - e2) - (1 / 72 : ℂ) * (e3 - e4)
  · linear_combination (2 / 3 : ℂ) * (e1 + e2) - (1 / 24 : ℂ) * (e3 + e4)
  · linear_combination (1 / 12 : ℂ) * (e3 - e4) - (1 / 6 : ℂ) * (e1 - e2)
  · linear_combination (1 / 24 : ℂ) * (e3 + e4) - (1 / 6 : ℂ) * (e1 + e2)

theorem coeffs0 (z1 z2 z3 z4 : V4)
    (h : ∀ c : ℂ, pc (fun i => 1 + c * z1 i) (fun i => 1 + c * z2 i) (fun i => 1 + c * z3 i)
      (fun i => 1 + c * z4 i) = 24)
    (h1 : tau z1 = 0) (h2 : tau z2 = 0) (h3 : tau z3 = 0) (h4 : tau z4 = 0) :
    ip z1 z2 + ip z1 z3 + ip z1 z4 + ip z2 z3 + ip z2 z4 + ip z3 z4 = 0 ∧
    t3 z1 z2 z3 + t3 z1 z2 z4 + t3 z1 z3 z4 + t3 z2 z3 z4 = 0 ∧
    br z1 z2 z3 z4 = 0 := by
  obtain ⟨_, a2, a3, a4⟩ := coeffs z1 z2 z3 z4 h
  rw [pc_tau] at a4
  rw [h1, h2, h3, h4] at a2 a3 a4
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 / 2 : ℂ) * a2
  · linear_combination (1 / 2 : ℂ) * a3
  · linear_combination a4

theorem sl_cols (K : Submodule ℂ M45) (hK : SLev K) (Y : M45) (hY : Y ∈ K) (m : Fin 5) (c : ℂ) :
    pc (fun i => 1 + c * col Y (m.succAbove 0) i) (fun i => 1 + c * col Y (m.succAbove 1) i)
      (fun i => 1 + c * col Y (m.succAbove 2) i) (fun i => 1 + c * col Y (m.succAbove 3) i) = 24 := by
  have h := hK (c • Y) (K.smul_mem c hY) m
  rw [P4_cols] at h
  exact h

def rs : M45 →ₗ[ℂ] V4 :=
  LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j)

theorem rs_apply (Y : M45) (i : Fin 4) :
    rs Y i = Y (i, 0) + Y (i, 1) + Y (i, 2) + Y (i, 3) + Y (i, 4) := by
  simp [rs, LinearMap.sum_apply, Fin.sum_univ_five]

theorem C1 (K : Submodule ℂ M45) (hK : SLev K) (Y : M45) (hY : Y ∈ K) :
    ∀ m, tau (col Y m) = 0 := by
  have a0 := (coeffs _ _ _ _ (sl_cols K hK Y hY 0)).1
  have a1 := (coeffs _ _ _ _ (sl_cols K hK Y hY 1)).1
  have a2 := (coeffs _ _ _ _ (sl_cols K hK Y hY 2)).1
  have a3 := (coeffs _ _ _ _ (sl_cols K hK Y hY 3)).1
  have a4 := (coeffs _ _ _ _ (sl_cols K hK Y hY 4)).1
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at a0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at a1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at a2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at a3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at a4
  apply fin5
  · linear_combination (1 / 4 : ℂ) * (a0 + a1 + a2 + a3 + a4) - a0
  · linear_combination (1 / 4 : ℂ) * (a0 + a1 + a2 + a3 + a4) - a1
  · linear_combination (1 / 4 : ℂ) * (a0 + a1 + a2 + a3 + a4) - a2
  · linear_combination (1 / 4 : ℂ) * (a0 + a1 + a2 + a3 + a4) - a3
  · linear_combination (1 / 4 : ℂ) * (a0 + a1 + a2 + a3 + a4) - a4

theorem C34 (K : Submodule ℂ M45) (hK : SLev K) (Y : M45) (hY : Y ∈ K) (m : Fin 5) :
    ip (col Y (m.succAbove 0)) (col Y (m.succAbove 1))
      + ip (col Y (m.succAbove 0)) (col Y (m.succAbove 2))
      + ip (col Y (m.succAbove 0)) (col Y (m.succAbove 3))
      + ip (col Y (m.succAbove 1)) (col Y (m.succAbove 2))
      + ip (col Y (m.succAbove 1)) (col Y (m.succAbove 3))
      + ip (col Y (m.succAbove 2)) (col Y (m.succAbove 3)) = 0 ∧
    t3 (col Y (m.succAbove 0)) (col Y (m.succAbove 1)) (col Y (m.succAbove 2))
      + t3 (col Y (m.succAbove 0)) (col Y (m.succAbove 1)) (col Y (m.succAbove 3))
      + t3 (col Y (m.succAbove 0)) (col Y (m.succAbove 2)) (col Y (m.succAbove 3))
      + t3 (col Y (m.succAbove 1)) (col Y (m.succAbove 2)) (col Y (m.succAbove 3)) = 0 ∧
    br (col Y (m.succAbove 0)) (col Y (m.succAbove 1)) (col Y (m.succAbove 2))
      (col Y (m.succAbove 3)) = 0 :=
  coeffs0 _ _ _ _ (sl_cols K hK Y hY m) (C1 K hK Y hY _) (C1 K hK Y hY _) (C1 K hK Y hY _)
    (C1 K hK Y hY _)

theorem C2 (K : Submodule ℂ M45) (hK : SLev K) (Y : M45) (hY : Y ∈ K) :
    ∀ m, ip (col Y m) (col Y m) = ip (rs Y) (col Y m) := by
  have b0 := (C34 K hK Y hY 0).1
  have b1 := (C34 K hK Y hY 1).1
  have b2 := (C34 K hK Y hY 2).1
  have b3 := (C34 K hK Y hY 3).1
  have b4 := (C34 K hK Y hY 4).1
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at b0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at b1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at b2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at b3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at b4
  simp only [ip, col] at b0 b1 b2 b3 b4
  apply fin5
  · simp only [ip, col, rs_apply]
    linear_combination b0 - (1 / 3 : ℂ) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination b1 - (1 / 3 : ℂ) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination b2 - (1 / 3 : ℂ) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination b3 - (1 / 3 : ℂ) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination b4 - (1 / 3 : ℂ) * (b0 + b1 + b2 + b3 + b4)

theorem C2pol (K : Submodule ℂ M45) (hK : SLev K) (Y Y' : M45) (hY : Y ∈ K) (hY' : Y' ∈ K)
    (m : Fin 5) :
    2 * ip (col Y m) (col Y' m) = ip (rs Y) (col Y' m) + ip (rs Y') (col Y m) := by
  have e1 := C2 K hK Y hY m
  have e2 := C2 K hK Y' hY' m
  have e3 := C2 K hK (Y + Y') (K.add_mem hY hY') m
  rw [map_add] at e3
  simp only [ip, col, Pi.add_apply] at e1 e2 e3 ⊢
  linear_combination e3 - e1 - e2

def colL (m : Fin 5) : M45 →ₗ[ℂ] V4 := LinearMap.funLeft ℂ ℂ (fun i : Fin 4 => (i, m))

theorem colL_apply (m : Fin 5) (Y : M45) : colL m Y = col Y m := rfl

def phi (m : Fin 5) : M45 →ₗ[ℂ] V4 := (2 : ℂ) • colL m - rs

theorem phi_apply (m : Fin 5) (Y : M45) (i : Fin 4) : phi m Y i = 2 * Y (i, m) - rs Y i := rfl

theorem mem_Vs (v : V4) : v ∈ sumZero 4 ↔ tau v = 0 := by
  rw [mem_sumZero, tau, Fin.sum_univ_four]

theorem tau_rs (K : Submodule ℂ M45) (hK : SLev K) (Y : M45) (hY : Y ∈ K) : tau (rs Y) = 0 := by
  have h0 := C1 K hK Y hY 0
  have h1 := C1 K hK Y hY 1
  have h2 := C1 K hK Y hY 2
  have h3 := C1 K hK Y hY 3
  have h4 := C1 K hK Y hY 4
  simp only [tau, col] at h0 h1 h2 h3 h4
  simp only [tau, rs_apply]
  linear_combination h0 + h1 + h2 + h3 + h4

theorem map_rs_le (K : Submodule ℂ M45) (hK : SLev K) : K.map rs ≤ sumZero 4 := by
  rintro _ ⟨Y, hY, rfl⟩
  rw [mem_Vs]
  exact tau_rs K hK Y hY

theorem tau_phi (K : Submodule ℂ M45) (hK : SLev K) (Y : M45) (hY : Y ∈ K) (m : Fin 5) :
    tau (phi m Y) = 0 := by
  have h1 := C1 K hK Y hY m
  have h2 := tau_rs K hK Y hY
  simp only [tau, col] at h1 h2
  simp only [tau, phi_apply]
  linear_combination 2 * h1 - h2

theorem ip_phi (K : Submodule ℂ M45) (hK : SLev K) (Y Y' : M45) (hY : Y ∈ K) (hY' : Y' ∈ K)
    (m : Fin 5) : ip (phi m Y) (phi m Y') = ip (rs Y) (rs Y') := by
  have e := C2pol K hK Y Y' hY hY' m
  simp only [ip, col] at e
  simp only [ip, phi_apply]
  linear_combination 2 * e

theorem ip_col_phi (K : Submodule ℂ M45) (hK : SLev K) (Z Y : M45) (hZ : Z ∈ K) (hY : Y ∈ K)
    (hZ0 : rs Z = 0) (m : Fin 5) : ip (col Z m) (phi m Y) = 0 := by
  have e := C2pol K hK Z Y hZ hY m
  rw [hZ0] at e
  simp only [ip, col, Pi.zero_apply] at e
  simp only [ip, col, phi_apply]
  linear_combination e

theorem nondeg (x : V4) (hx : tau x = 0) (h : ∀ v : V4, tau v = 0 → ip x v = 0) : x = 0 := by
  have a1 : x 0 * 1 + x 1 * (-1) + x 2 * 0 + x 3 * 0 = 0 :=
    h ![1, -1, 0, 0] (by norm_num [tau])
  have a2 : x 0 * 0 + x 1 * 1 + x 2 * (-1) + x 3 * 0 = 0 :=
    h ![0, 1, -1, 0] (by norm_num [tau])
  have a3 : x 0 * 0 + x 1 * 0 + x 2 * 1 + x 3 * (-1) = 0 :=
    h ![0, 0, 1, -1] (by norm_num [tau])
  unfold tau at hx
  funext i
  fin_cases i
  · show x 0 = 0
    linear_combination (1 / 4 : ℂ) * hx + (3 / 4 : ℂ) * a1 + (1 / 2 : ℂ) * a2 + (1 / 4 : ℂ) * a3
  · show x 1 = 0
    linear_combination (1 / 4 : ℂ) * hx - (1 / 4 : ℂ) * a1 + (1 / 2 : ℂ) * a2 + (1 / 4 : ℂ) * a3
  · show x 2 = 0
    linear_combination (1 / 4 : ℂ) * hx - (1 / 4 : ℂ) * a1 - (1 / 2 : ℂ) * a2 + (1 / 4 : ℂ) * a3
  · show x 3 = 0
    linear_combination (1 / 4 : ℂ) * hx - (1 / 4 : ℂ) * a1 - (1 / 2 : ℂ) * a2 - (3 / 4 : ℂ) * a3

theorem Bi (K : Submodule ℂ M45) (hK : SLev K) (hq : Module.finrank ℂ (K.map rs) = 3) :
    (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = ⊥ := by
  have hV3 : Module.finrank ℂ (sumZero 4) ≤ 3 :=
    (finrank_sumZero (n := 4) (by norm_num)).trans (by norm_num)
  have hS : K.map rs ≤ sumZero 4 := map_rs_le K hK
  have hSV : K.map rs = sumZero 4 :=
    Submodule.eq_of_le_of_finrank_le hS (le_trans hV3 (le_of_eq hq.symm))
  have hphi : ∀ m, K.map (phi m) = sumZero 4 := by
    intro m
    have hle : K.map (phi m) ≤ sumZero 4 := by
      rintro _ ⟨Y, hY, rfl⟩
      rw [mem_Vs]
      exact tau_phi K hK Y hY m
    have hker : (K ⊓ LinearMap.ker (phi m) : Submodule ℂ M45) ≤ K ⊓ LinearMap.ker rs := by
      rintro Y ⟨hY, hY0⟩
      refine ⟨hY, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hY0 ⊢
      apply nondeg
      · exact tau_rs K hK Y hY
      · intro v hv
        have hv' : v ∈ K.map rs := by
          rw [hSV, mem_Vs]
          exact hv
        obtain ⟨Y', hY', rfl⟩ := hv'
        rw [← ip_phi K hK Y Y' hY hY' m, hY0]
        simp [ip]
    have r1 := rank_nullity K (phi m)
    have r2 := rank_nullity K rs
    have r3 := Submodule.finrank_mono hker
    have hP3 : 3 ≤ Module.finrank ℂ (K.map (phi m)) := by omega
    exact Submodule.eq_of_le_of_finrank_le hle (le_trans hV3 hP3)
  rw [eq_bot_iff]
  rintro Z ⟨hZ, hZ0⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hZ0
  rw [Submodule.mem_bot]
  have hcol : ∀ m, col Z m = 0 := by
    intro m
    apply nondeg
    · exact C1 K hK Z hZ m
    · intro v hv
      have hv' : v ∈ K.map (phi m) := by
        rw [hphi m, mem_Vs]
        exact hv
      obtain ⟨Y, hY, rfl⟩ := hv'
      exact ip_col_phi K hK Z Y hZ hY hZ0 m
  funext ⟨i, j⟩
  exact congrFun (hcol j) i

def dotDual : V4 →ₗ[ℂ] Module.Dual ℂ V4 :=
  LinearMap.mk₂ ℂ (fun v z => ∑ i, v i * z i)
    (fun a b z => by simp only [Pi.add_apply, add_mul, sum_add_distrib])
    (fun c a z => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum])
    (fun v a b => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c v a => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by ring)

theorem dotDual_apply (v z : V4) : dotDual v z = ∑ i, v i * z i := rfl

theorem dotDual_injective : Function.Injective dotDual := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  funext j
  have h := LinearMap.congr_fun hv (Pi.single j 1)
  rw [dotDual_apply] at h
  simpa [Pi.single_apply] using h

theorem perp_bound (V W : Submodule ℂ V4) (h : ∀ v ∈ V, ∀ z ∈ W, ∑ i, v i * z i = 0) :
    Module.finrank ℂ V + Module.finrank ℂ W ≤ Fintype.card (Fin 4) := by
  have hle : V.map dotDual ≤ W.dualAnnihilator := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h v hv z hz
  have e1 : Module.finrank ℂ (V.map dotDual) = Module.finrank ℂ V :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ dotDual_injective V)).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have e3 := Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card] at e2
  omega

theorem Q1 (W : Submodule ℂ V4) (hτ : ∀ x ∈ W, tau x = 0) (hI : ∀ x ∈ W, ∀ y ∈ W, ip x y = 0) :
    Module.finrank ℂ W ≤ 1 := by
  have hone : (1 : V4) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hinf : W ⊓ Submodule.span ℂ {(1 : V4)} = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx1⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hx1
    obtain ⟨c, rfl⟩ := hx1
    have h := hτ _ hx
    have hc : c = 0 := by
      simp only [tau, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
      linear_combination (1 / 4 : ℂ) * h
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hperp : ∀ v ∈ W, ∀ z ∈ W ⊔ Submodule.span ℂ {(1 : V4)}, ∑ i, v i * z i = 0 := by
    intro v hv z hz
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h1 := hI v hv w hw
    have h2 := hτ v hv
    simp only [ip, tau] at h1 h2
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linear_combination h1 + c * h2
  have hb := perp_bound W (W ⊔ Submodule.span ℂ {(1 : V4)}) hperp
  have hs := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {(1 : V4)})
  rw [hinf, finrank_bot, finrank_span_singleton hone] at hs
  rw [Fintype.card_fin] at hb
  omega

theorem N_iso (K : Submodule ℂ M45) (hK : SLev K) (Z Z' : M45)
    (hZ : Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45))
    (hZ' : Z' ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45)) (m : Fin 5) :
    ip (col Z m) (col Z' m) = 0 := by
  have hz := Submodule.mem_inf.mp hZ
  have hz' := Submodule.mem_inf.mp hZ'
  have e := C2pol K hK Z Z' hz.1 hz'.1 m
  rw [LinearMap.mem_ker.mp hz.2, LinearMap.mem_ker.mp hz'.2] at e
  simp only [ip, col, Pi.zero_apply] at e ⊢
  linear_combination (1 / 2 : ℂ) * e

theorem N_col_dim (K : Submodule ℂ M45) (hK : SLev K) (m : Fin 5) :
    Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colL m)) ≤ 1 := by
  apply Q1
  · rintro _ ⟨Z, hZ, rfl⟩
    exact C1 K hK Z (Submodule.mem_inf.mp hZ).1 m
  · rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
    exact N_iso K hK Z Z' hZ hZ' m

theorem finrank_sup_one (W : Submodule ℂ V4) (hτ : ∀ x ∈ W, tau x = 0) :
    Module.finrank ℂ (W ⊔ Submodule.span ℂ {(1 : V4)} : Submodule ℂ V4) =
      Module.finrank ℂ W + 1 := by
  have hone : (1 : V4) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hinf : W ⊓ Submodule.span ℂ {(1 : V4)} = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx1⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hx1
    obtain ⟨c, rfl⟩ := hx1
    have h := hτ _ hx
    have hc : c = 0 := by
      simp only [tau, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
      linear_combination (1 / 4 : ℂ) * h
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hs := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {(1 : V4)})
  rw [hinf, finrank_bot, finrank_span_singleton hone] at hs
  omega

theorem perp_sup_one (P W : Submodule ℂ V4) (hP : ∀ p ∈ P, tau p = 0)
    (hW : ∀ w ∈ W, tau w = 0) (h : ∀ p ∈ P, ∀ w ∈ W, ip p w = 0) :
    Module.finrank ℂ P + Module.finrank ℂ W + 1 ≤ 4 := by
  have hperp : ∀ v ∈ P, ∀ z ∈ W ⊔ Submodule.span ℂ {(1 : V4)}, ∑ i, v i * z i = 0 := by
    intro v hv z hz
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h1 := h v hv w hw
    have h2 := hP v hv
    simp only [ip, tau] at h1 h2
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linear_combination h1 + c * h2
  have hb := perp_bound P (W ⊔ Submodule.span ℂ {(1 : V4)}) hperp
  have hs := finrank_sup_one W hW
  rw [Fintype.card_fin] at hb
  omega

theorem Bii (K : Submodule ℂ M45) (hK : SLev K) (hq : Module.finrank ℂ (K.map rs) = 2)
    (hN : (K ⊓ LinearMap.ker rs : Submodule ℂ M45) ≠ ⊥) :
    ∃ u ∈ K.map rs, u ≠ 0 ∧ ∀ s ∈ K.map rs, ip u s = 0 := by
  by_contra hcon
  have hnd : ∀ u ∈ K.map rs, (∀ s ∈ K.map rs, ip u s = 0) → u = 0 := by
    intro u hu hs
    by_contra hne
    exact hcon ⟨u, hu, hne, hs⟩
  apply hN
  rw [eq_bot_iff]
  intro Z hZ
  rw [Submodule.mem_bot]
  have hz := Submodule.mem_inf.mp hZ
  have hZ0 : rs Z = 0 := LinearMap.mem_ker.mp hz.2
  have hcol : ∀ m, col Z m = 0 := by
    intro m
    by_contra hzm
    have hker : (K ⊓ LinearMap.ker (phi m) : Submodule ℂ M45) ≤
        ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (colL m) :
          Submodule ℂ M45) := by
      intro Y hY
      have hy := Submodule.mem_inf.mp hY
      have hY0 : phi m Y = 0 := LinearMap.mem_ker.mp hy.2
      have hrs : rs Y = 0 := by
        apply hnd _ (Submodule.mem_map_of_mem hy.1)
        rintro _ ⟨Y', hY', rfl⟩
        rw [← ip_phi K hK Y Y' hy.1 hY' m, hY0]
        simp [ip]
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hy.1, LinearMap.mem_ker.mpr hrs⟩,
        LinearMap.mem_ker.mpr ?_⟩
      funext i
      have h1 := congrFun hY0 i
      rw [phi_apply, hrs] at h1
      simp only [Pi.zero_apply, sub_zero] at h1
      show Y (i, m) = 0
      linear_combination (1 / 2 : ℂ) * h1
    have r1 := rank_nullity K (phi m)
    have r2 := rank_nullity K rs
    have r3 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (colL m)
    have r4 := Submodule.finrank_mono hker
    have r5 : 1 ≤ Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colL m)) := by
      by_contra h0
      have h00 : Module.finrank ℂ
          ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colL m)) = 0 := by omega
      rw [Submodule.finrank_eq_zero] at h00
      have hmem : col Z m ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colL m) :=
        Submodule.mem_map_of_mem hZ
      rw [h00, Submodule.mem_bot] at hmem
      exact hzm hmem
    have hP3 : 3 ≤ Module.finrank ℂ (K.map (phi m)) := by omega
    have h1 : Module.finrank ℂ (Submodule.span ℂ {col Z m}) = 1 := finrank_span_singleton hzm
    have hb := perp_sup_one (K.map (phi m)) (Submodule.span ℂ {col Z m}) ?_ ?_ ?_
    · omega
    · rintro _ ⟨Y, hY, rfl⟩
      exact tau_phi K hK Y hY m
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have ht := C1 K hK Z hz.1 m
      simp only [tau, Pi.smul_apply, smul_eq_mul] at ht ⊢
      linear_combination c * ht
    · rintro _ ⟨Y, hY, rfl⟩ w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have ht := ip_col_phi K hK Z Y hz.1 hY hZ0 m
      simp only [ip, Pi.smul_apply, smul_eq_mul] at ht ⊢
      linear_combination c * ht
  funext ⟨i, j⟩
  exact congrFun (hcol j) i

theorem Q4 (v x : V4) (hv : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hx1 : tau x = 0)
    (hx2 : ip x x = 0) (hvx : ip v x = 0) : ∃ c : ℂ, x = c • v := by
  have hW : Module.finrank ℂ (Submodule.span ℂ {v, x}) ≤ 1 := by
    apply Q1
    · intro a ha
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp ha
      simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv1 hx1 ⊢
      linear_combination s * hv1 + t * hx1
    · intro a ha b hb
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp ha
      obtain ⟨s', t', rfl⟩ := Submodule.mem_span_pair.mp hb
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv2 hx2 hvx ⊢
      linear_combination s * s' * hv2 + t * t' * hx2 + (s * t' + t * s') * hvx
  have hle : Submodule.span ℂ {v} ≤ Submodule.span ℂ {v, x} :=
    Submodule.span_mono (by simp)
  have h1 : Module.finrank ℂ (Submodule.span ℂ {v}) = 1 := finrank_span_singleton hv
  have heq := Submodule.eq_of_le_of_finrank_le hle (le_trans hW (le_of_eq h1.symm))
  have hx : x ∈ Submodule.span ℂ {v} := by
    rw [heq]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c, hc.symm⟩

theorem Biii (K : Submodule ℂ M45) (hK : SLev K) (Yu : M45) (hYu : Yu ∈ K)
    (hu : ip (rs Yu) (rs Yu) = 0) (Z : M45)
    (hZ : Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45))
    (m : Fin 5) (hzm : col Z m ≠ 0) : ∃ c : ℂ, phi m Yu = c • col Z m := by
  have hz := Submodule.mem_inf.mp hZ
  apply Q4 (col Z m) (phi m Yu) hzm (C1 K hK Z hz.1 m) (N_iso K hK Z Z hZ hZ m)
    (tau_phi K hK Yu hYu m)
  · rw [ip_phi K hK Yu Yu hYu hYu m]
    exact hu
  · exact ip_col_phi K hK Z Yu hz.1 hYu (LinearMap.mem_ker.mp hz.2) m

theorem sum_phi (Y : M45) (i : Fin 4) :
    phi 0 Y i + phi 1 Y i + phi 2 Y i + phi 3 Y i + phi 4 Y i = -3 * rs Y i := by
  simp only [phi_apply, rs_apply]
  ring

theorem root4 (a b c d : ℂ) (h1 : a + b + c + d = 0) (h2 : a * a + b * b + c * c + d * d = 0)
    (h3 : a * a * a + b * b * b + c * c * c + d * d * d = 0)
    (h4 : a * a * a * a + b * b * b * b + c * c * c * c + d * d * d * d = 0) : a = 0 := by
  have h : a ^ 4 = 0 := by
    linear_combination
      (a ^ 3 - (a + b + c + d) / 2 * a ^ 2 + (a + b + c + d) ^ 2 / 6 * a
        - (a + b + c + d) ^ 3 / 24) * h1
      + (a ^ 2 / 2 - (a + b + c + d) / 2 * a + (a + b + c + d) ^ 2 / 4
        - (a * a + b * b + c * c + d * d) / 8) * h2
      + (a / 3 - (a + b + c + d) / 3) * h3 + (1 / 4 : ℂ) * h4
  exact (pow_eq_zero_iff (by norm_num)).mp h

theorem iso34 (v : V4) (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0)
    (h4 : t4 v v v v = 0) : v = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4
  funext i
  fin_cases i
  · exact root4 (v 0) (v 1) (v 2) (v 3) h1 h2 h3 h4
  · exact root4 (v 1) (v 0) (v 2) (v 3) (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4)
  · exact root4 (v 2) (v 0) (v 1) (v 3) (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4)
  · exact root4 (v 3) (v 0) (v 1) (v 2) (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4)

def indep (v w : V4) : Prop := ∀ s t : ℂ, s • v + t • w = 0 → s = 0 ∧ t = 0

theorem root4k (a b c d : ℂ) (h1 : a + b + c + d = 0) (h2 : a * a + b * b + c * c + d * d = 0)
    (h3 : a * a * a + b * b * b + c * c * c + d * d * d = 0) :
    a ^ 4 = (a * a * a * a + b * b * b * b + c * c * c * c + d * d * d * d) / 4 := by
  linear_combination
    (a ^ 3 - (a + b + c + d) / 2 * a ^ 2 + (a + b + c + d) ^ 2 / 6 * a
      - (a + b + c + d) ^ 3 / 24) * h1
    + (a ^ 2 / 2 - (a + b + c + d) / 2 * a + (a + b + c + d) ^ 2 / 4
      - (a * a + b * b + c * c + d * d) / 8) * h2
    + (a / 3 - (a + b + c + d) / 3) * h3

theorem pow4_iso (w : V4) (h1 : tau w = 0) (h2 : ip w w = 0) (h3 : t3 w w w = 0) :
    w 0 ^ 4 = t4 w w w w / 4 ∧ w 1 ^ 4 = t4 w w w w / 4 ∧ w 2 ^ 4 = t4 w w w w / 4 ∧
      w 3 ^ 4 = t4 w w w w / 4 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination root4k (w 0) (w 1) (w 2) (w 3) h1 h2 h3
  · linear_combination root4k (w 1) (w 0) (w 2) (w 3) (by linear_combination h1)
      (by linear_combination h2) (by linear_combination h3)
  · linear_combination root4k (w 2) (w 0) (w 1) (w 3) (by linear_combination h1)
      (by linear_combination h2) (by linear_combination h3)
  · linear_combination root4k (w 3) (w 0) (w 1) (w 2) (by linear_combination h1)
      (by linear_combination h2) (by linear_combination h3)

theorem br_w3 (w : V4) (c P : ℂ) (hw2 : ip w w = 0) (p0 : w 0 ^ 4 = P / 4)
    (p1 : w 1 ^ 4 = P / 4) (p2 : w 2 ^ 4 = P / 4) (p3 : w 3 ^ 4 = P / 4) :
    br (c • (fun i => w i ^ 3 : V4)) (c • (fun i => w i ^ 3 : V4)) w w = c ^ 2 * P ^ 2 / 2 := by
  simp only [br, t4, ip, Pi.smul_apply, smul_eq_mul] at hw2 ⊢
  linear_combination (-6 * c ^ 2) * ((w 0 ^ 4 + P / 4) * p0 + (w 1 ^ 4 + P / 4) * p1
      + (w 2 ^ 4 + P / 4) * p2 + (w 3 ^ 4 + P / 4) * p3)
    + 2 * c ^ 2 * (w 0 ^ 4 + w 1 ^ 4 + w 2 ^ 4 + w 3 ^ 4 + P) * (p0 + p1 + p2 + p3)
    + c ^ 2 * (w 0 ^ 6 + w 1 ^ 6 + w 2 ^ 6 + w 3 ^ 6) * hw2

theorem G23core (v w : V4) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hi : indep v w) (h3 : t3 w w w = 0) (h13 : t4 v w w w = 0) :
    br v v w w ≠ 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    have := (hi 0 1 (by rw [h]; simp)).2
    exact one_ne_zero this
  have hv0 : v ≠ 0 := by
    intro h
    have := (hi 1 0 (by rw [h]; simp)).1
    exact one_ne_zero this
  have hP : t4 w w w w ≠ 0 := fun h => hw0 (iso34 w hw1 hw2 h3 h)
  obtain ⟨p0, p1, p2, p3⟩ := pow4_iso w hw1 hw2 h3
  have a1 : tau (fun i => w i ^ 3 : V4) = 0 := by
    simp only [tau, t3] at h3 ⊢
    linear_combination h3
  have a2 : ip (fun i => w i ^ 3 : V4) (fun i => w i ^ 3 : V4) = 0 := by
    simp only [ip] at hw2 ⊢
    linear_combination w 0 ^ 2 * p0 + w 1 ^ 2 * p1 + w 2 ^ 2 * p2 + w 3 ^ 2 * p3
      + t4 w w w w / 4 * hw2
  have a3 : ip (fun i => w i ^ 3 : V4) v = 0 := by
    simp only [ip, t4] at h13 ⊢
    linear_combination h13
  have a4 : (fun i => w i ^ 3 : V4) ≠ 0 := by
    intro h
    apply hP
    have e : t4 w w w w = ip w (fun i => w i ^ 3 : V4) := by
      simp only [t4, ip]
      ring
    rw [e, h]
    simp [ip]
  obtain ⟨c, hc⟩ := Q4 (fun i => w i ^ 3 : V4) v a4 a1 a2 hv1 hv2 a3
  have hc0 : c ≠ 0 := by
    intro h
    apply hv0
    rw [hc, h, zero_smul]
  rw [hc, br_w3 w c (t4 w w w w) hw2 p0 p1 p2 p3]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hP)) two_ne_zero

theorem G23 (v w : V4) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hi : indep v w) (μ ν1 ν2 ν3 : ℂ) (hμ : μ ≠ 0) (h1 : ν1 ≠ 0)
    (h2 : ν2 ≠ 0) (h3 : ν3 ≠ 0)
    (hTa : t3 ((-μ) • v) (ν1 • w) (ν2 • w) + t3 ((-μ) • v) (ν1 • w) (ν3 • w)
      + t3 ((-μ) • v) (ν2 • w) (ν3 • w) + t3 (ν1 • w) (ν2 • w) (ν3 • w) = 0)
    (hTb : t3 (μ • v) (ν1 • w) (ν2 • w) + t3 (μ • v) (ν1 • w) (ν3 • w)
      + t3 (μ • v) (ν2 • w) (ν3 • w) + t3 (ν1 • w) (ν2 • w) (ν3 • w) = 0)
    (hBa : br ((-μ) • v) (ν1 • w) (ν2 • w) (ν3 • w) = 0)
    (hB1 : br (μ • v) ((-μ) • v) (ν2 • w) (ν3 • w) = 0) : False := by
  have hn : ν1 * ν2 * ν3 ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
  have e1 : t3 w w w = 0 := by
    have h : ν1 * ν2 * ν3 * t3 w w w = 0 := by
      simp only [t3, Pi.smul_apply, smul_eq_mul] at hTa hTb ⊢
      linear_combination (1 / 2 : ℂ) * hTa + (1 / 2 : ℂ) * hTb
    exact (mul_eq_zero.mp h).resolve_left hn
  have e2 : t4 v w w w = 0 := by
    have h : μ * (ν1 * ν2 * ν3) * t4 v w w w = 0 := by
      simp only [br, t4, ip, Pi.smul_apply, smul_eq_mul] at hBa hw2 ⊢
      linear_combination (1 / 6 : ℂ) * hBa + (1 / 2 : ℂ) * μ * ν1 * ν2 * ν3
        * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * hw2
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hμ hn)
  have e3 : br v v w w = 0 := by
    have h : μ ^ 2 * (ν2 * ν3) * br v v w w = 0 := by
      simp only [br, t4, ip, Pi.smul_apply, smul_eq_mul] at hB1 ⊢
      linear_combination (-1 : ℂ) * hB1
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero 2 hμ) (mul_ne_zero h2 h3))
  exact G23core v w hv1 hv2 hw1 hw2 hi e1 e2 e3

theorem generic_t {ι : Type} (s : Finset ι) (a b : ι → ℂ) (h : ∀ i ∈ s, a i ≠ 0 ∨ b i ≠ 0) :
    ∃ t : ℂ, ∀ i ∈ s, a i + t * b i ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (s.image (fun i => -a i / b i))
  refine ⟨t, fun i hi h0 => ?_⟩
  by_cases hb : b i = 0
  · rw [hb, mul_zero, add_zero] at h0
    rcases h i hi with h1 | h1
    · exact h1 h0
    · exact h1 hb
  · apply ht
    rw [Finset.mem_image]
    refine ⟨i, hi, ?_⟩
    rw [div_eq_iff hb]
    linear_combination (-1 : ℂ) * h0

theorem generic_pt {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (s : Finset ι)
    (f : ι → P →ₗ[ℂ] ℂ) (h : ∀ i ∈ s, f i ≠ 0) : ∃ x : P, ∀ i ∈ s, f i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨x, hx⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hfj : f j ≠ 0 := h j (Finset.mem_insert_self j s)
    obtain ⟨y, hy⟩ : ∃ y, f j y ≠ 0 := by
      by_contra hcon
      apply hfj
      refine LinearMap.ext fun z => ?_
      by_contra hz
      exact hcon ⟨z, hz⟩
    obtain ⟨t, ht⟩ := generic_t (insert j s) (fun i => f i x) (fun i => f i y) (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact Or.inr hy
      · exact Or.inl (hx i hi'))
    refine ⟨x + t • y, fun i hi => ?_⟩
    rw [map_add, map_smul, smul_eq_mul]
    exact ht i hi

def outer (v : V4) (x : Fin 5 → ℂ) : M45 := fun p => v p.1 * x p.2

theorem A1facts (N : Submodule ℂ M45) (hN : SLev N) (v : V4) (hv2 : ip v v = 0)
    (x : Fin 5 → ℂ) (hZ : outer v x ∈ N) (m : Fin 5) :
    t3 v v v * (x (m.succAbove 0) * x (m.succAbove 1) * x (m.succAbove 2)
      + x (m.succAbove 0) * x (m.succAbove 1) * x (m.succAbove 3)
      + x (m.succAbove 0) * x (m.succAbove 2) * x (m.succAbove 3)
      + x (m.succAbove 1) * x (m.succAbove 2) * x (m.succAbove 3)) = 0 ∧
    t4 v v v v * (x (m.succAbove 0) * x (m.succAbove 1) * x (m.succAbove 2)
      * x (m.succAbove 3)) = 0 := by
  obtain ⟨_, c3, c4⟩ := C34 N hN _ hZ m
  simp only [t3, br, t4, ip, col, outer] at c3 c4 hv2 ⊢
  constructor
  · linear_combination c3
  · linear_combination (-1 / 6 : ℂ) * c4 + (1 / 2 : ℂ) * (x (m.succAbove 0) * x (m.succAbove 1)
      * x (m.succAbove 2) * x (m.succAbove 3)) * (v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3)
      * hv2

def lfN (N : Submodule ℂ M45) (i0 : Fin 4) (j : Fin 5) : ↥N →ₗ[ℂ] ℂ :=
  (LinearMap.proj (i0, j)).comp N.subtype

theorem lfN_apply (N : Submodule ℂ M45) (i0 : Fin 4) (j : Fin 5) (z : ↥N) :
    lfN N i0 j z = (z : M45) (i0, j) := rfl

def psiS (S : Finset (Fin 5)) (i0 : Fin 4) : M45 →ₗ[ℂ] (↥S → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun j : ↥S => (i0, j.1))

theorem psiS_apply (S : Finset (Fin 5)) (i0 : Fin 4) (Z : M45) (j : ↥S) :
    psiS S i0 Z j = Z (i0, j.1) := rfl

theorem A1 (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (v : V4) (hv : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → ℂ, Z = outer v x) : Module.finrank ℂ N ≤ 2 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 5), ∀ j, j ∈ S ↔ lfN N i0 j ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun j => lfN N i0 j ≠ 0), fun j => by simp⟩
  have hnS : ∀ j, j ∉ S → ∀ Z ∈ N, Z (i0, j) = 0 := by
    intro j hj Z hZ
    have h0 : lfN N i0 j = 0 := by
      by_contra h
      exact hj ((hS j).mpr h)
    exact LinearMap.congr_fun h0 ⟨Z, hZ⟩
  obtain ⟨z, hz⟩ := generic_pt S (lfN N i0) (fun j hj => (hS j).mp hj)
  obtain ⟨x, hx⟩ := hform z.1 z.2
  have hZx : outer v x ∈ N := by
    rw [← hx]
    exact z.2
  have hxS : ∀ j, j ∈ S → x j ≠ 0 := by
    intro j hj h0
    apply hz j hj
    rw [lfN_apply, hx]
    simp [outer, h0]
  have hxnS : ∀ j, j ∉ S → x j = 0 := by
    intro j hj
    have h : outer v x (i0, j) = 0 := hnS j hj _ hZx
    simp only [outer] at h
    exact (mul_eq_zero.mp h).resolve_left hi0
  have hker : (N ⊓ LinearMap.ker (psiS S i0) : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz' := Submodule.mem_inf.mp hZ
    obtain ⟨y, hy⟩ := hform Z hz'.1
    have hψ : psiS S i0 Z = 0 := LinearMap.mem_ker.mp hz'.2
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h : Z (i0, j) = 0 := by
        by_cases hj : j ∈ S
        · exact congrFun hψ ⟨j, hj⟩
        · exact hnS j hj Z hz'.1
      rw [hy] at h
      simp only [outer] at h
      exact (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext p
    simp [outer, hy0]
  have r := rank_nullity N (psiS S i0)
  rw [hker, finrank_bot] at r
  have hle : Module.finrank ℂ (N.map (psiS S i0)) ≤ S.card := by
    have h := Submodule.finrank_le (N.map (psiS S i0))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    exact h
  have hsum : ∀ Z ∈ N, ∑ j : ↥S, Z (i0, j.1) = 0 := by
    intro Z hZ
    have h1 : ∑ j : ↥S, Z (i0, j.1) = ∑ j ∈ S, Z (i0, j) :=
      Finset.sum_coe_sort S (fun j => Z (i0, j))
    have h2 : ∑ j ∈ S, Z (i0, j) = ∑ j, Z (i0, j) :=
      Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hnS j hj Z hZ)
    have h3 := congrFun (hrs Z hZ) i0
    rw [rs_apply] at h3
    rw [h1, h2, Fin.sum_univ_five]
    exact h3
  have hlt : S.Nonempty → Module.finrank ℂ (N.map (psiS S i0)) < S.card := by
    rintro ⟨j0, hj0⟩
    have hsub : N.map (psiS S i0) ≤
        LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) := by
      rintro _ ⟨Z, hZ, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      exact hsum Z hZ
    have hne' : LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) ≠ ⊤ := by
      intro h
      have hm : (Pi.single (⟨j0, hj0⟩ : ↥S) (1 : ℂ)) ∈
          LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) :=
        h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sum_apply] at hm
      simp at hm
    have h1 := Submodule.finrank_lt hne'
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    exact lt_of_le_of_lt (Submodule.finrank_mono hsub) h1
  by_cases h4 : t4 v v v v = 0
  · have h3 : t3 v v v ≠ 0 := fun h => hv (iso34 v hv1 hv2 h h4)
    have e0 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 0).1).resolve_left h3
    have e1 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 1).1).resolve_left h3
    have e2 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 2).1).resolve_left h3
    have e3 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 3).1).resolve_left h3
    have e4 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 4).1).resolve_left h3
    rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at e0
    rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at e1
    rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at e2
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at e3
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at e4
    have hs : x 0 + x 1 + x 2 + x 3 + x 4 = 0 := by
      have h := congrFun (hrs _ hZx) i0
      rw [rs_apply] at h
      simp only [outer, Pi.zero_apply] at h
      have h' : v i0 * (x 0 + x 1 + x 2 + x 3 + x 4) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left hi0
    obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2) / 2 :=
      ⟨_, rfl⟩
    have cubic : ∀ j, x j ^ 3 = s * x j := by
      apply fin5
      · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e0
          + (x 0 ^ 2 - x 0 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 0 * hsdef
      · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e1
          + (x 1 ^ 2 - x 1 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 1 * hsdef
      · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e2
          + (x 2 ^ 2 - x 2 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 2 * hsdef
      · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e3
          + (x 3 ^ 2 - x 3 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 3 * hsdef
      · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e4
          + (x 4 ^ 2 - x 4 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 4 * hsdef
    have hsq : ∀ j, x j ^ 2 = if j ∈ S then s else 0 := by
      intro j
      by_cases hj : j ∈ S
      · rw [if_pos hj]
        apply mul_left_cancel₀ (hxS j hj)
        linear_combination cubic j
      · rw [if_neg hj, hxnS j hj]
        ring
    have hsum2 : ∑ j, x j ^ 2 = (S.card : ℂ) * s := by
      rw [Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
    rw [Fin.sum_univ_five] at hsum2
    have hcard : S.card ≤ 2 := by
      rcases S.eq_empty_or_nonempty with h0 | ⟨j, hj⟩
      · rw [h0]
        simp
      · have hs0 : s ≠ 0 := by
          have h := hsq j
          rw [if_pos hj] at h
          rw [← h]
          exact pow_ne_zero 2 (hxS j hj)
        have h2 : ((S.card : ℂ) - 2) * s = 0 := by
          linear_combination (-1 : ℂ) * hsum2 - 2 * hsdef
        have h5 : (S.card : ℂ) = 2 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hs0)
        have h6 : S.card = 2 := by exact_mod_cast h5
        omega
    omega
  · have hprod : ∀ m : Fin 5, ∃ k : Fin 4, m.succAbove k ∉ S := by
      intro m
      have h := (A1facts N hN v hv2 x hZx m).2
      have h' := (mul_eq_zero.mp h).resolve_left h4
      rcases mul_eq_zero.mp h' with h3 | h3
      · rcases mul_eq_zero.mp h3 with h2 | h2
        · rcases mul_eq_zero.mp h2 with h1 | h1
          · exact ⟨0, fun hin => hxS _ hin h1⟩
          · exact ⟨1, fun hin => hxS _ hin h1⟩
        · exact ⟨2, fun hin => hxS _ hin h2⟩
      · exact ⟨3, fun hin => hxS _ hin h3⟩
    obtain ⟨k1, hk1⟩ := hprod 0
    obtain ⟨k2, hk2⟩ := hprod ((0 : Fin 5).succAbove k1)
    have hne12 : ((0 : Fin 5).succAbove k1).succAbove k2 ≠ (0 : Fin 5).succAbove k1 :=
      Fin.succAbove_ne _ _
    have hc : S.card ≤ 3 := by
      have h1 := Finset.card_add_card_compl S
      have h2 : ({(0 : Fin 5).succAbove k1, ((0 : Fin 5).succAbove k1).succAbove k2} :
          Finset (Fin 5)) ⊆ Sᶜ := by
        intro j hj
        rw [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_compl]
        rcases hj with rfl | rfl
        · exact hk1
        · exact hk2
      have h3 := Finset.card_le_card h2
      rw [Finset.card_pair hne12.symm] at h3
      rw [Fintype.card_fin] at h1
      omega
    rcases S.eq_empty_or_nonempty with h0 | h0
    · have hc0 : S.card = 0 := by
        rw [h0]
        exact Finset.card_empty
      omega
    · have := hlt h0
      omega

theorem SLev_mono {N N' : Submodule ℂ M45} (hN : SLev N) (h : N' ≤ N) : SLev N' :=
  fun Y hY a => hN Y (h hY) a

theorem Niso (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (Z Z' : M45)
    (hZ : Z ∈ N) (hZ' : Z' ∈ N) (m : Fin 5) : ip (col Z m) (col Z' m) = 0 := by
  have e := C2pol N hN Z Z' hZ hZ' m
  rw [hrs Z hZ, hrs Z' hZ'] at e
  simp only [ip, Pi.zero_apply] at e ⊢
  linear_combination (1 / 2 : ℂ) * e

theorem Ncol1 (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (m : Fin 5) :
    Module.finrank ℂ (N.map (colL m)) ≤ 1 := by
  apply Q1
  · rintro _ ⟨Z, hZ, rfl⟩
    exact C1 N hN Z hZ m
  · rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
    exact Niso N hN hrs Z Z' hZ hZ' m

theorem peel (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (m : Fin 5) :
    Module.finrank ℂ N ≤
      1 + Module.finrank ℂ (N ⊓ LinearMap.ker (colL m) : Submodule ℂ M45) := by
  have r := rank_nullity N (colL m)
  have h := Ncol1 N hN hrs m
  omega

def efN (N : Submodule ℂ M45) (p : Fin 4 × Fin 5) : ↥N →ₗ[ℂ] ℂ :=
  (LinearMap.proj p).comp N.subtype

theorem maxpt (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) :
    ∃ z ∈ N, ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 4 × Fin 5), ∀ p, p ∈ T ↔ efN N p ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun p => efN N p ≠ 0), fun p => by simp⟩
  obtain ⟨z, hz⟩ := generic_pt T (efN N) (fun p hp => (hT p).mp hp)
  refine ⟨z.1, z.2, fun Z hZ m => ?_⟩
  by_cases h0 : col z.1 m = 0
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    funext i
    have hni : (i, m) ∉ T := by
      intro hin
      apply hz (i, m) hin
      exact congrFun h0 i
    have hf : efN N (i, m) = 0 := by
      by_contra h
      exact hni ((hT (i, m)).mpr h)
    exact LinearMap.congr_fun hf ⟨Z, hZ⟩
  · exact Q4 (col z.1 m) (col Z m) h0 (C1 N hN z.1 z.2 m) (Niso N hN hrs z.1 z.1 z.2 z.2 m)
      (C1 N hN Z hZ m) (Niso N hN hrs Z Z hZ hZ m) (Niso N hN hrs z.1 Z z.2 hZ m)

theorem perm_two {α : Type} [DecidableEq α] (i j a b : α) (c : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm α, σ i = a ∧ σ j = b := by
  have h : Equiv.swap i a b ≠ i := by
    intro e
    simpa [hab] using (congrArg (Equiv.swap i a) e).symm
  exact ⟨Equiv.swap i a * Equiv.swap j (Equiv.swap i a b),
    by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne c h.symm],
    by simp [Equiv.Perm.mul_apply]⟩

theorem perm_three (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  obtain ⟨σ1, h0, h1⟩ := perm_two (0 : Fin 5) 1 a b (by decide) hab
  have hc0 : (0 : Fin 5) ≠ σ1.symm c := by
    intro h
    apply hac
    rw [← h0, h, Equiv.apply_symm_apply]
  have hc1 : (1 : Fin 5) ≠ σ1.symm c := by
    intro h
    apply hbc
    rw [← h1, h, Equiv.apply_symm_apply]
  refine ⟨σ1 * Equiv.swap 2 (σ1.symm c), ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hc0, h0]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hc1, h1]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

theorem sum_cols_perm (σ : Equiv.Perm (Fin 5)) (Z : M45) :
    col Z (σ 0) + col Z (σ 1) + col Z (σ 2) + col Z (σ 3) + col Z (σ 4) = rs Z := by
  have h : ∑ j, col Z (σ j) = ∑ j, col Z j := Equiv.sum_comp σ (fun j => col Z j)
  rw [Fin.sum_univ_five, Fin.sum_univ_five] at h
  rw [h]
  funext i
  simp only [Pi.add_apply, col, rs_apply]

theorem caseA3 (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (z : M45)
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hind : ∀ s1 s2 s3 : ℂ, s1 • col z a + s2 • col z b + s3 • col z c = 0 →
      s1 = 0 ∧ s2 = 0 ∧ s3 = 0) : Module.finrank ℂ N ≤ 2 := by
  obtain ⟨σ, h0, h1, h2⟩ := perm_three a b c hab hac hbc
  have hN1 : SLev (N ⊓ LinearMap.ker (colL (σ 3)) : Submodule ℂ M45) :=
    SLev_mono hN inf_le_left
  have hrs1 : ∀ Z ∈ (N ⊓ LinearMap.ker (colL (σ 3)) : Submodule ℂ M45), rs Z = 0 :=
    fun Z hZ => hrs Z (Submodule.mem_inf.mp hZ).1
  have p1 := peel N hN hrs (σ 3)
  have p2 := peel _ hN1 hrs1 (σ 4)
  have hbot : ((N ⊓ LinearMap.ker (colL (σ 3)) : Submodule ℂ M45) ⊓
      LinearMap.ker (colL (σ 4)) : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz2 := Submodule.mem_inf.mp hZ
    have hz1 := Submodule.mem_inf.mp hz2.1
    have hZN := hz1.1
    have c3 : col Z (σ 3) = 0 := LinearMap.mem_ker.mp hz1.2
    have c4 : col Z (σ 4) = 0 := LinearMap.mem_ker.mp hz2.2
    obtain ⟨s1, e1⟩ := hmax Z hZN a
    obtain ⟨s2, e2⟩ := hmax Z hZN b
    obtain ⟨s3, e3⟩ := hmax Z hZN c
    have hsum := sum_cols_perm σ Z
    rw [h0, h1, h2, c3, c4, hrs Z hZN, e1, e2, e3, add_zero, add_zero] at hsum
    obtain ⟨t1, t2, t3⟩ := hind s1 s2 s3 hsum
    have hcol : ∀ j, col Z (σ j) = 0 := by
      apply fin5
      · rw [h0, e1, t1, zero_smul]
      · rw [h1, e2, t2, zero_smul]
      · rw [h2, e3, t3, zero_smul]
      · exact c3
      · exact c4
    funext ⟨i, m⟩
    have hh := congrFun (hcol (σ.symm m)) i
    rw [Equiv.apply_symm_apply] at hh
    exact hh
  rw [hbot, finrank_bot] at p2
  omega

theorem caseLine (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (z : M45)
    (hz : z ∈ N) (hmax : ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) (m0 : Fin 5)
    (hm0 : col z m0 ≠ 0) (hline : ∀ m, ∃ c : ℂ, col z m = c • col z m0) :
    Module.finrank ℂ N ≤ 2 := by
  have hform : ∀ Z ∈ N, ∃ x : Fin 5 → ℂ, Z = outer (col z m0) x := by
    intro Z hZ
    have h : ∀ m, ∃ d : ℂ, col Z m = d • col z m0 := by
      intro m
      obtain ⟨c, hc⟩ := hmax Z hZ m
      obtain ⟨c', hc'⟩ := hline m
      exact ⟨c * c', by rw [hc, hc', smul_smul]⟩
    choose x hx using h
    refine ⟨x, ?_⟩
    funext ⟨i, m⟩
    have hh := congrFun (hx m) i
    simp only [col, Pi.smul_apply, smul_eq_mul] at hh
    simp only [outer, col]
    rw [hh, mul_comm]
  exact A1 N hN hrs (col z m0) hm0 (C1 N hN z hz m0) (Niso N hN hrs z z hz hz m0) hform

def LemA2 : Prop :=
  ∀ N : Submodule ℂ M45, SLev N → (∀ Z ∈ N, rs Z = 0) → ∀ z ∈ N,
    (∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) → ∀ a b : Fin 5,
    indep (col z a) (col z b) → (∀ m, ∃ s t : ℂ, col z m = s • col z a + t • col z b) →
    Module.finrank ℂ N ≤ 2

theorem LemA_red (H2 : LemA2) (N : Submodule ℂ M45) (hN : SLev N)
    (hrs : ∀ Z ∈ N, rs Z = 0) : Module.finrank ℂ N ≤ 2 := by
  obtain ⟨z, hz, hmax⟩ := maxpt N hN hrs
  by_cases h2 : ∃ a b : Fin 5, indep (col z a) (col z b)
  · obtain ⟨a, b, hab⟩ := h2
    by_cases h3 : ∃ c : Fin 5, ∀ s1 s2 s3 : ℂ,
        s1 • col z a + s2 • col z b + s3 • col z c = 0 → s1 = 0 ∧ s2 = 0 ∧ s3 = 0
    · obtain ⟨c, hc⟩ := h3
      have hne_ab : a ≠ b := by
        intro h
        have h1 := (hab 1 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_ac : a ≠ c := by
        intro h
        have h1 := (hc 1 0 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_bc : b ≠ c := by
        intro h
        have h1 := (hc 0 1 (-1) (by rw [h]; simp)).2.1
        exact one_ne_zero h1
      exact caseA3 N hN hrs z hmax a b c hne_ab hne_ac hne_bc hc
    · apply H2 N hN hrs z hz hmax a b hab
      intro m
      by_contra hcon
      apply h3
      refine ⟨m, fun s1 s2 s3 h => ?_⟩
      have hs3 : s3 = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s1 * s3⁻¹, -s2 * s3⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination s3⁻¹ * hi - col z m i * hinv
      rw [hs3, zero_smul, add_zero] at h
      obtain ⟨t1, t2⟩ := hab s1 s2 h
      exact ⟨t1, t2, hs3⟩
  · by_cases hall : ∀ m, col z m = 0
    · have hbot : N = ⊥ := by
        rw [eq_bot_iff]
        intro Z hZ
        rw [Submodule.mem_bot]
        funext ⟨i, m⟩
        obtain ⟨c, hc⟩ := hmax Z hZ m
        have hh := congrFun hc i
        rw [hall m] at hh
        simpa [col] using hh
      rw [hbot, finrank_bot]
      exact Nat.zero_le 2
    · obtain ⟨m0, hm0⟩ : ∃ m0, col z m0 ≠ 0 := by
        by_contra h
        apply hall
        intro m
        by_contra hm
        exact h ⟨m, hm⟩
      apply caseLine N hN hrs z hz hmax m0 hm0
      intro m
      by_contra hcon
      apply h2
      refine ⟨m0, m, fun s t h => ?_⟩
      have ht : t = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s * t⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination t⁻¹ * hi - col z m i * hinv
      rw [ht, zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right hm0, ht⟩

def cperm (σ : Equiv.Perm (Fin 5)) : M45 →ₗ[ℂ] M45 :=
  LinearMap.funLeft ℂ ℂ (fun p : Fin 4 × Fin 5 => (p.1, σ p.2))

theorem cperm_apply (σ : Equiv.Perm (Fin 5)) (Y : M45) (p : Fin 4 × Fin 5) :
    cperm σ Y p = Y (p.1, σ p.2) := rfl

theorem P4_perm (σ : Equiv.Perm (Fin 5)) (a : Fin 5) (N : M45) :
    P4 a (fun p => N (p.1, σ p.2)) = P4 (σ a) N := by
  have h := (Equiv.embeddingCongr (Equiv.refl (Fin 4)) σ).sum_comp
    (fun e : Fin 4 ↪ Fin 5 => if (e 0 ≠ σ a ∧ e 1 ≠ σ a ∧ e 2 ≠ σ a ∧ e 3 ≠ σ a) then
      N (0, e 0) * N (1, e 1) * N (2, e 2) * N (3, e 3) else 0)
  unfold P4
  rw [← h]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [Equiv.embeddingCongr_apply]

theorem SLev_perm (σ : Equiv.Perm (Fin 5)) (N : Submodule ℂ M45) (hN : SLev N) :
    SLev (N.map (cperm σ)) := by
  intro Y hY a
  obtain ⟨Y0, hY0, rfl⟩ := hY
  have h := P4_perm σ a (fun p => 1 + Y0 p)
  exact h.trans (hN Y0 hY0 (σ a))

theorem pattern23 (N : Submodule ℂ M45) (hN : SLev N) (z : M45) (hz : z ∈ N)
    (σ : Equiv.Perm (Fin 5)) (v w : V4) (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hw1 : tau w = 0) (hw2 : ip w w = 0) (hi : indep v w) (μ ν1 ν2 ν3 : ℂ) (hμ : μ ≠ 0)
    (h1 : ν1 ≠ 0) (h2 : ν2 ≠ 0) (h3 : ν3 ≠ 0) (c0 : col z (σ 0) = μ • v)
    (c1 : col z (σ 1) = (-μ) • v) (c2 : col z (σ 2) = ν1 • w) (c3 : col z (σ 3) = ν2 • w)
    (c4 : col z (σ 4) = ν3 • w) : False := by
  have hNσ := SLev_perm σ N hN
  have hzσ : cperm σ z ∈ N.map (cperm σ) := Submodule.mem_map_of_mem hz
  have k0 := C34 _ hNσ _ hzσ 0
  have k1 := C34 _ hNσ _ hzσ 1
  have k2 := C34 _ hNσ _ hzσ 2
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at k0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at k1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at k2
  have d0 : col (cperm σ z) 0 = μ • v := c0
  have d1 : col (cperm σ z) 1 = (-μ) • v := c1
  have d2 : col (cperm σ z) 2 = ν1 • w := c2
  have d3 : col (cperm σ z) 3 = ν2 • w := c3
  have d4 : col (cperm σ z) 4 = ν3 • w := c4
  rw [d1, d2, d3, d4] at k0
  rw [d0, d2, d3, d4] at k1
  rw [d0, d1, d3, d4] at k2
  exact G23 v w hv1 hv2 hw1 hw2 hi μ ν1 ν2 ν3 hμ h1 h2 h3 k0.2.1 k1.2.1 k0.2.2 k2.2.2

theorem indep_symm {v w : V4} (h : indep v w) : indep w v := fun s t e => by
  have h1 := h t s (by rw [add_comm]; exact e)
  exact ⟨h1.2, h1.1⟩

theorem sum_cols (Z : M45) : ∑ m, col Z m = rs Z := by
  funext i
  rw [Finset.sum_apply, Fin.sum_univ_five, rs_apply]
  rfl

theorem perm_four (a b c d : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c ∧ σ 3 = d := by
  obtain ⟨σ1, h0, h1, h2⟩ := perm_three a b c hab hac hbc
  have hd0 : (0 : Fin 5) ≠ σ1.symm d := by
    intro h
    apply had
    rw [← h0, h, Equiv.apply_symm_apply]
  have hd1 : (1 : Fin 5) ≠ σ1.symm d := by
    intro h
    apply hbd
    rw [← h1, h, Equiv.apply_symm_apply]
  have hd2 : (2 : Fin 5) ≠ σ1.symm d := by
    intro h
    apply hcd
    rw [← h2, h, Equiv.apply_symm_apply]
  refine ⟨σ1 * Equiv.swap 3 (σ1.symm d), ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hd0, h0]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hd1, h1]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hd2, h2]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

def swp : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem swp0 : swp 0 = 2 := by decide

theorem swp1 : swp 1 = 3 := by decide

theorem swp2 : swp 2 = 0 := by decide

theorem swp3 : swp 3 = 1 := by decide

theorem swp4 : swp 4 = 4 := by decide

theorem LemA2_proof : LemA2 := by
  intro N hN hrs z hz hmax a b hab hspan
  have hua1 := C1 N hN z hz a
  have hua2 := Niso N hN hrs z z hz hz a
  have hub1 := C1 N hN z hz b
  have hub2 := Niso N hN hrs z z hz hz b
  choose sc tc hst using hspan
  have hua0 : col z a ≠ 0 := by
    intro h
    have h1 := (hab 1 0 (by rw [h]; simp)).1
    exact one_ne_zero h1
  have hh : ip (col z a) (col z b) ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := Q4 (col z a) (col z b) hua0 hua1 hua2 hub1 hub2 h
    have h1 := (hab c (-1) (by rw [hc]; simp)).2
    norm_num at h1
  have F1 : ∀ m, sc m * tc m = 0 := by
    intro m
    have e := Niso N hN hrs z z hz hz m
    rw [hst m] at e
    have e2 : 2 * (sc m * tc m) * ip (col z a) (col z b) = 0 := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e hua2 hub2 ⊢
      linear_combination e - sc m ^ 2 * hua2 - tc m ^ 2 * hub2
    rcases mul_eq_zero.mp e2 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    · exact absurd h hh
  have F2a : sc a = 1 ∧ tc a = 0 := by
    have e := hst a
    have h := hab (sc a - 1) (tc a) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (-1 : ℂ) * hi)
    exact ⟨sub_eq_zero.mp h.1, h.2⟩
  have F2b : sc b = 0 ∧ tc b = 1 := by
    have e := hst b
    have h := hab (sc b) (tc b - 1) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (-1 : ℂ) * hi)
    exact ⟨h.1, sub_eq_zero.mp h.2⟩
  have F3 : (∑ m, sc m) = 0 ∧ (∑ m, tc m) = 0 := by
    apply hab
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e1 : ∑ m, col z m i = 0 := by
      have h := congrFun (sum_cols z) i
      rw [Finset.sum_apply, hrs z hz] at h
      exact h
    have e2 : ∑ m, col z m i = (∑ m, sc m) * col z a i + (∑ m, tc m) * col z b i := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h := congrFun (hst m) i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    rw [← e2]
    exact e1
  obtain ⟨a', ha'a, hsa'⟩ : ∃ a', a' ≠ a ∧ sc a' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ a → sc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, sc m = sc a :=
      Finset.sum_eq_single a (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ a) h)
    rw [F3.1, F2a.1] at h1
    exact zero_ne_one h1
  obtain ⟨b', hb'b, htb'⟩ : ∃ b', b' ≠ b ∧ tc b' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ b → tc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, tc m = tc b :=
      Finset.sum_eq_single b (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ b) h)
    rw [F3.2, F2b.2] at h1
    exact zero_ne_one h1
  have hta' : tc a' = 0 := (mul_eq_zero.mp (F1 a')).resolve_left hsa'
  have hsb' : sc b' = 0 := (mul_eq_zero.mp (F1 b')).resolve_right htb'
  have hne_ab : a ≠ b := by
    intro h
    apply one_ne_zero (α := ℂ)
    rw [← F2a.1, h, F2b.1]
  have hne_ab' : a ≠ b' := by
    intro h
    apply htb'
    rw [← h, F2a.2]
  have hne_a'b : a' ≠ b := by
    intro h
    apply hsa'
    rw [h, F2b.1]
  have hne_a'b' : a' ≠ b' := by
    intro h
    apply htb'
    rw [← h, hta']
  obtain ⟨σ, h0, h1, h2, h3⟩ := perm_four a a' b b' ha'a.symm hne_ab hne_ab' hne_a'b hne_a'b'
    hb'b.symm
  have hSs : sc a + sc a' + sc b + sc b' + sc (σ 4) = 0 := by
    have h : ∑ j, sc (σ j) = ∑ m, sc m := Equiv.sum_comp σ sc
    rw [Fin.sum_univ_five, F3.1, h0, h1, h2, h3] at h
    exact h
  have hSt : tc a + tc a' + tc b + tc b' + tc (σ 4) = 0 := by
    have h : ∑ j, tc (σ j) = ∑ m, tc m := Equiv.sum_comp σ tc
    rw [Fin.sum_univ_five, F3.2, h0, h1, h2, h3] at h
    exact h
  rw [F2a.1, F2b.1, hsb'] at hSs
  rw [F2a.2, F2b.2, hta'] at hSt
  have za : col z a' = sc a' • col z a := by
    rw [hst a', hta', zero_smul, add_zero]
  have zb : col z b' = tc b' • col z b := by
    rw [hst b', hsb', zero_smul, zero_add]
  by_cases hse : sc (σ 4) = 0
  · by_cases hte : tc (σ 4) = 0
    · have ze : col z (σ 4) = 0 := by
        rw [hst (σ 4), hse, hte, zero_smul, zero_smul, add_zero]
      have hN1 : SLev (N ⊓ LinearMap.ker (colL a) : Submodule ℂ M45) :=
        SLev_mono hN inf_le_left
      have hrs1 : ∀ Z ∈ (N ⊓ LinearMap.ker (colL a) : Submodule ℂ M45), rs Z = 0 :=
        fun Z hZ => hrs Z (Submodule.mem_inf.mp hZ).1
      have p1 := peel N hN hrs a
      have p2 := peel _ hN1 hrs1 b
      have hbot : ((N ⊓ LinearMap.ker (colL a) : Submodule ℂ M45) ⊓
          LinearMap.ker (colL b) : Submodule ℂ M45) = ⊥ := by
        rw [eq_bot_iff]
        intro Z hZ
        rw [Submodule.mem_bot]
        have hz2 := Submodule.mem_inf.mp hZ
        have hz1 := Submodule.mem_inf.mp hz2.1
        have hZN := hz1.1
        have ca : col Z a = 0 := LinearMap.mem_ker.mp hz1.2
        have cb : col Z b = 0 := LinearMap.mem_ker.mp hz2.2
        obtain ⟨k1, e1⟩ := hmax Z hZN a'
        obtain ⟨k2, e2⟩ := hmax Z hZN b'
        obtain ⟨k3, e3⟩ := hmax Z hZN (σ 4)
        rw [za] at e1
        rw [zb] at e2
        rw [ze, smul_zero] at e3
        have hsum := sum_cols_perm σ Z
        rw [h0, h1, h2, h3, hrs Z hZN, ca, cb, e1, e2, e3] at hsum
        have hk := hab (k1 * sc a') (k2 * tc b') (by
          funext i
          have hi := congrFun hsum i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
          linear_combination hi)
        have hk1 : k1 = 0 := (mul_eq_zero.mp hk.1).resolve_right hsa'
        have hk2 : k2 = 0 := (mul_eq_zero.mp hk.2).resolve_right htb'
        have hcol : ∀ j, col Z (σ j) = 0 := by
          apply fin5
          · rw [h0]
            exact ca
          · rw [h1, e1, hk1, zero_smul]
          · rw [h2]
            exact cb
          · rw [h3, e2, hk2, zero_smul]
          · exact e3
        funext ⟨i, m⟩
        have hh2 := congrFun (hcol (σ.symm m)) i
        rw [Equiv.apply_symm_apply] at hh2
        exact hh2
      rw [hbot, finrank_bot] at p2
      omega
    · exfalso
      have hsa'1 : sc a' = -1 := by linear_combination hSs - hse
      have c0 : col z (σ 0) = (1 : ℂ) • col z a := by rw [h0, one_smul]
      have c1 : col z (σ 1) = (-1 : ℂ) • col z a := by rw [h1, za, hsa'1]
      have c2 : col z (σ 2) = (1 : ℂ) • col z b := by rw [h2, one_smul]
      have c3 : col z (σ 3) = tc b' • col z b := by rw [h3, zb]
      have c4 : col z (σ 4) = tc (σ 4) • col z b := by
        rw [hst (σ 4), hse, zero_smul, zero_add]
      exact pattern23 N hN z hz σ (col z a) (col z b) hua1 hua2 hub1 hub2 hab 1 1 (tc b')
        (tc (σ 4)) one_ne_zero one_ne_zero htb' hte c0 c1 c2 c3 c4
  · exfalso
    have hte : tc (σ 4) = 0 := (mul_eq_zero.mp (F1 (σ 4))).resolve_left hse
    have htb'1 : tc b' = -1 := by linear_combination hSt - hte
    have c0 : col z ((σ * swp) 0) =
        (1 : ℂ) • col z b := by
      rw [Equiv.Perm.mul_apply, swp0, h2, one_smul]
    have c1 : col z ((σ * swp) 1) =
        (-1 : ℂ) • col z b := by
      rw [Equiv.Perm.mul_apply, swp1, h3, zb, htb'1]
    have c2 : col z ((σ * swp) 2) =
        (1 : ℂ) • col z a := by
      rw [Equiv.Perm.mul_apply, swp2, h0, one_smul]
    have c3 : col z ((σ * swp) 3) =
        sc a' • col z a := by
      rw [Equiv.Perm.mul_apply, swp3, h1, za]
    have c4 : col z ((σ * swp) 4) =
        sc (σ 4) • col z a := by
      rw [Equiv.Perm.mul_apply, swp4, hst (σ 4), hte, zero_smul, add_zero]
    exact pattern23 N hN z hz (σ * swp) (col z b)
      (col z a) hub1 hub2 hua1 hua2 (indep_symm hab) 1 1 (sc a') (sc (σ 4)) one_ne_zero
      one_ne_zero hsa' hse c0 c1 c2 c3 c4

theorem LemA_proof (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) :
    Module.finrank ℂ N ≤ 2 :=
  LemA_red LemA2_proof N hN hrs

theorem A1b (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (v : V4) (hv : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → ℂ, Z = outer v x) (h3 : t3 v v v ≠ 0) :
    Module.finrank ℂ N ≤ 1 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 5), ∀ j, j ∈ S ↔ lfN N i0 j ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun j => lfN N i0 j ≠ 0), fun j => by simp⟩
  have hnS : ∀ j, j ∉ S → ∀ Z ∈ N, Z (i0, j) = 0 := by
    intro j hj Z hZ
    have h0 : lfN N i0 j = 0 := by
      by_contra h
      exact hj ((hS j).mpr h)
    exact LinearMap.congr_fun h0 ⟨Z, hZ⟩
  obtain ⟨z, hz⟩ := generic_pt S (lfN N i0) (fun j hj => (hS j).mp hj)
  obtain ⟨x, hx⟩ := hform z.1 z.2
  have hZx : outer v x ∈ N := by
    rw [← hx]
    exact z.2
  have hxS : ∀ j, j ∈ S → x j ≠ 0 := by
    intro j hj h0
    apply hz j hj
    rw [lfN_apply, hx]
    simp [outer, h0]
  have hxnS : ∀ j, j ∉ S → x j = 0 := by
    intro j hj
    have h : outer v x (i0, j) = 0 := hnS j hj _ hZx
    simp only [outer] at h
    exact (mul_eq_zero.mp h).resolve_left hi0
  have hker : (N ⊓ LinearMap.ker (psiS S i0) : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz' := Submodule.mem_inf.mp hZ
    obtain ⟨y, hy⟩ := hform Z hz'.1
    have hψ : psiS S i0 Z = 0 := LinearMap.mem_ker.mp hz'.2
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h : Z (i0, j) = 0 := by
        by_cases hj : j ∈ S
        · exact congrFun hψ ⟨j, hj⟩
        · exact hnS j hj Z hz'.1
      rw [hy] at h
      simp only [outer] at h
      exact (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext p
    simp [outer, hy0]
  have r := rank_nullity N (psiS S i0)
  rw [hker, finrank_bot] at r
  have hle : Module.finrank ℂ (N.map (psiS S i0)) ≤ S.card := by
    have h := Submodule.finrank_le (N.map (psiS S i0))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    exact h
  have hsum : ∀ Z ∈ N, ∑ j : ↥S, Z (i0, j.1) = 0 := by
    intro Z hZ
    have h1 : ∑ j : ↥S, Z (i0, j.1) = ∑ j ∈ S, Z (i0, j) :=
      Finset.sum_coe_sort S (fun j => Z (i0, j))
    have h2 : ∑ j ∈ S, Z (i0, j) = ∑ j, Z (i0, j) :=
      Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hnS j hj Z hZ)
    have h3 := congrFun (hrs Z hZ) i0
    rw [rs_apply] at h3
    rw [h1, h2, Fin.sum_univ_five]
    exact h3
  have hlt : S.Nonempty → Module.finrank ℂ (N.map (psiS S i0)) < S.card := by
    rintro ⟨j0, hj0⟩
    have hsub : N.map (psiS S i0) ≤
        LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) := by
      rintro _ ⟨Z, hZ, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      exact hsum Z hZ
    have hne' : LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) ≠ ⊤ := by
      intro h
      have hm : (Pi.single (⟨j0, hj0⟩ : ↥S) (1 : ℂ)) ∈
          LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) :=
        h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sum_apply] at hm
      simp at hm
    have h1 := Submodule.finrank_lt hne'
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    exact lt_of_le_of_lt (Submodule.finrank_mono hsub) h1
  have e0 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 0).1).resolve_left h3
  have e1 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 1).1).resolve_left h3
  have e2 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 2).1).resolve_left h3
  have e3 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 3).1).resolve_left h3
  have e4 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 4).1).resolve_left h3
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at e0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at e1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at e2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at e3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at e4
  have hs : x 0 + x 1 + x 2 + x 3 + x 4 = 0 := by
    have h := congrFun (hrs _ hZx) i0
    rw [rs_apply] at h
    simp only [outer, Pi.zero_apply] at h
    have h' : v i0 * (x 0 + x 1 + x 2 + x 3 + x 4) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left hi0
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2) / 2 :=
    ⟨_, rfl⟩
  have cubic : ∀ j, x j ^ 3 = s * x j := by
    apply fin5
    · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e0
        + (x 0 ^ 2 - x 0 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 0 * hsdef
    · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e1
        + (x 1 ^ 2 - x 1 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 1 * hsdef
    · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e2
        + (x 2 ^ 2 - x 2 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 2 * hsdef
    · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e3
        + (x 3 ^ 2 - x 3 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 3 * hsdef
    · linear_combination (1 / 2 : ℂ) * (e0 + e1 + e2 + e3 + e4) - e4
        + (x 4 ^ 2 - x 4 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 4 * hsdef
  have hsq : ∀ j, x j ^ 2 = if j ∈ S then s else 0 := by
    intro j
    by_cases hj : j ∈ S
    · rw [if_pos hj]
      apply mul_left_cancel₀ (hxS j hj)
      linear_combination cubic j
    · rw [if_neg hj, hxnS j hj]
      ring
  have hsum2 : ∑ j, x j ^ 2 = (S.card : ℂ) * s := by
    rw [Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
  rw [Fin.sum_univ_five] at hsum2
  have hcard : S.card ≤ 2 := by
    rcases S.eq_empty_or_nonempty with h0 | ⟨j, hj⟩
    · rw [h0]
      simp
    · have hs0 : s ≠ 0 := by
        have h := hsq j
        rw [if_pos hj] at h
        rw [← h]
        exact pow_ne_zero 2 (hxS j hj)
      have h2 : ((S.card : ℂ) - 2) * s = 0 := by
        linear_combination (-1 : ℂ) * hsum2 - 2 * hsdef
      have h5 : (S.card : ℂ) = 2 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hs0)
      have h6 : S.card = 2 := by exact_mod_cast h5
      omega
  rcases S.eq_empty_or_nonempty with h0 | h0
  · have hc0 : S.card = 0 := by
      rw [h0]
      exact Finset.card_empty
    omega
  · have hl := hlt h0
    omega


theorem two_line_pattern (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0)
    (z : M45) (hz : z ∈ N) (a b : Fin 5) (hab : indep (col z a) (col z b))
    (hspan : ∀ m, ∃ s t : ℂ, col z m = s • col z a + t • col z b) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = a ∧ σ 2 = b ∧ col z (σ 1) = (-1 : ℂ) • col z a ∧
      col z (σ 3) = (-1 : ℂ) • col z b ∧ col z (σ 4) = 0 := by
  have hua1 := C1 N hN z hz a
  have hua2 := Niso N hN hrs z z hz hz a
  have hub1 := C1 N hN z hz b
  have hub2 := Niso N hN hrs z z hz hz b
  choose sc tc hst using hspan
  have hua0 : col z a ≠ 0 := by
    intro h
    have h1 := (hab 1 0 (by rw [h]; simp)).1
    exact one_ne_zero h1
  have hh : ip (col z a) (col z b) ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := Q4 (col z a) (col z b) hua0 hua1 hua2 hub1 hub2 h
    have h1 := (hab c (-1) (by rw [hc]; simp)).2
    norm_num at h1
  have F1 : ∀ m, sc m * tc m = 0 := by
    intro m
    have e := Niso N hN hrs z z hz hz m
    rw [hst m] at e
    have e2 : 2 * (sc m * tc m) * ip (col z a) (col z b) = 0 := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e hua2 hub2 ⊢
      linear_combination e - sc m ^ 2 * hua2 - tc m ^ 2 * hub2
    rcases mul_eq_zero.mp e2 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    · exact absurd h hh
  have F2a : sc a = 1 ∧ tc a = 0 := by
    have e := hst a
    have h := hab (sc a - 1) (tc a) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (-1 : ℂ) * hi)
    exact ⟨sub_eq_zero.mp h.1, h.2⟩
  have F2b : sc b = 0 ∧ tc b = 1 := by
    have e := hst b
    have h := hab (sc b) (tc b - 1) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (-1 : ℂ) * hi)
    exact ⟨h.1, sub_eq_zero.mp h.2⟩
  have F3 : (∑ m, sc m) = 0 ∧ (∑ m, tc m) = 0 := by
    apply hab
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e1 : ∑ m, col z m i = 0 := by
      have h := congrFun (sum_cols z) i
      rw [Finset.sum_apply, hrs z hz] at h
      exact h
    have e2 : ∑ m, col z m i = (∑ m, sc m) * col z a i + (∑ m, tc m) * col z b i := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h := congrFun (hst m) i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    rw [← e2]
    exact e1
  obtain ⟨a', ha'a, hsa'⟩ : ∃ a', a' ≠ a ∧ sc a' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ a → sc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, sc m = sc a :=
      Finset.sum_eq_single a (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ a) h)
    rw [F3.1, F2a.1] at h1
    exact zero_ne_one h1
  obtain ⟨b', hb'b, htb'⟩ : ∃ b', b' ≠ b ∧ tc b' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ b → tc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, tc m = tc b :=
      Finset.sum_eq_single b (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ b) h)
    rw [F3.2, F2b.2] at h1
    exact zero_ne_one h1
  have hta' : tc a' = 0 := (mul_eq_zero.mp (F1 a')).resolve_left hsa'
  have hsb' : sc b' = 0 := (mul_eq_zero.mp (F1 b')).resolve_right htb'
  have hne_ab : a ≠ b := by
    intro h
    apply one_ne_zero (α := ℂ)
    rw [← F2a.1, h, F2b.1]
  have hne_ab' : a ≠ b' := by
    intro h
    apply htb'
    rw [← h, F2a.2]
  have hne_a'b : a' ≠ b := by
    intro h
    apply hsa'
    rw [h, F2b.1]
  have hne_a'b' : a' ≠ b' := by
    intro h
    apply htb'
    rw [← h, hta']
  obtain ⟨σ, h0, h1, h2, h3⟩ := perm_four a a' b b' ha'a.symm hne_ab hne_ab' hne_a'b hne_a'b'
    hb'b.symm
  have hSs : sc a + sc a' + sc b + sc b' + sc (σ 4) = 0 := by
    have h : ∑ j, sc (σ j) = ∑ m, sc m := Equiv.sum_comp σ sc
    rw [Fin.sum_univ_five, F3.1, h0, h1, h2, h3] at h
    exact h
  have hSt : tc a + tc a' + tc b + tc b' + tc (σ 4) = 0 := by
    have h : ∑ j, tc (σ j) = ∑ m, tc m := Equiv.sum_comp σ tc
    rw [Fin.sum_univ_five, F3.2, h0, h1, h2, h3] at h
    exact h
  rw [F2a.1, F2b.1, hsb'] at hSs
  rw [F2a.2, F2b.2, hta'] at hSt
  have za : col z a' = sc a' • col z a := by
    rw [hst a', hta', zero_smul, add_zero]
  have zb : col z b' = tc b' • col z b := by
    rw [hst b', hsb', zero_smul, zero_add]
  by_cases hse : sc (σ 4) = 0
  · by_cases hte : tc (σ 4) = 0
    · have hsa'1 : sc a' = -1 := by linear_combination hSs - hse
      have htb'1 : tc b' = -1 := by linear_combination hSt - hte
      refine ⟨σ, h0, h2, ?_, ?_, ?_⟩
      · rw [h1, za, hsa'1]
      · rw [h3, zb, htb'1]
      · rw [hst (σ 4), hse, hte, zero_smul, zero_smul, add_zero]
    · exfalso
      have hsa'1 : sc a' = -1 := by linear_combination hSs - hse
      have c0 : col z (σ 0) = (1 : ℂ) • col z a := by rw [h0, one_smul]
      have c1 : col z (σ 1) = (-1 : ℂ) • col z a := by rw [h1, za, hsa'1]
      have c2 : col z (σ 2) = (1 : ℂ) • col z b := by rw [h2, one_smul]
      have c3 : col z (σ 3) = tc b' • col z b := by rw [h3, zb]
      have c4 : col z (σ 4) = tc (σ 4) • col z b := by
        rw [hst (σ 4), hse, zero_smul, zero_add]
      exact pattern23 N hN z hz σ (col z a) (col z b) hua1 hua2 hub1 hub2 hab 1 1 (tc b')
        (tc (σ 4)) one_ne_zero one_ne_zero htb' hte c0 c1 c2 c3 c4
  · exfalso
    have hte : tc (σ 4) = 0 := (mul_eq_zero.mp (F1 (σ 4))).resolve_left hse
    have htb'1 : tc b' = -1 := by linear_combination hSt - hte
    have c0 : col z ((σ * swp) 0) =
        (1 : ℂ) • col z b := by
      rw [Equiv.Perm.mul_apply, swp0, h2, one_smul]
    have c1 : col z ((σ * swp) 1) =
        (-1 : ℂ) • col z b := by
      rw [Equiv.Perm.mul_apply, swp1, h3, zb, htb'1]
    have c2 : col z ((σ * swp) 2) =
        (1 : ℂ) • col z a := by
      rw [Equiv.Perm.mul_apply, swp2, h0, one_smul]
    have c3 : col z ((σ * swp) 3) =
        sc a' • col z a := by
      rw [Equiv.Perm.mul_apply, swp3, h1, za]
    have c4 : col z ((σ * swp) 4) =
        sc (σ 4) • col z a := by
      rw [Equiv.Perm.mul_apply, swp4, hst (σ 4), hte, zero_smul, add_zero]
    exact pattern23 N hN z hz (σ * swp) (col z b)
      (col z a) hub1 hub2 hua1 hua2 (indep_symm hab) 1 1 (sc a') (sc (σ 4)) one_ne_zero
      one_ne_zero hsa' hse c0 c1 c2 c3 c4

theorem typeII_ids (N : Submodule ℂ M45) (hN : SLev N) (z : M45) (hz : z ∈ N)
    (σ : Equiv.Perm (Fin 5)) (v w : V4) (c0 : col z (σ 0) = v)
    (c1 : col z (σ 1) = (-1 : ℂ) • v) (c2 : col z (σ 2) = w)
    (c3 : col z (σ 3) = (-1 : ℂ) • w) (c4 : col z (σ 4) = 0) :
    t3 v w w = 0 ∧ t3 v v w = 0 ∧ br v v w w = 0 := by
  have hNσ := SLev_perm σ N hN
  have hzσ : cperm σ z ∈ N.map (cperm σ) := Submodule.mem_map_of_mem hz
  have k0 := C34 _ hNσ _ hzσ 0
  have k2 := C34 _ hNσ _ hzσ 2
  have k4 := C34 _ hNσ _ hzσ 4
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at k0
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at k2
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at k4
  have d0 : col (cperm σ z) 0 = v := c0
  have d1 : col (cperm σ z) 1 = (-1 : ℂ) • v := c1
  have d2 : col (cperm σ z) 2 = w := c2
  have d3 : col (cperm σ z) 3 = (-1 : ℂ) • w := c3
  have d4 : col (cperm σ z) 4 = 0 := c4
  rw [d1, d2, d3, d4] at k0
  rw [d0, d1, d3, d4] at k2
  rw [d0, d1, d2, d3] at k4
  have a1 := k0.2.1
  have a2 := k2.2.1
  have a3 := k4.2.2
  simp only [t3, br, t4, ip, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a1 a2 a3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination a1
  · linear_combination a2
  · linear_combination a3

theorem A1cols (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (v : V4) (hv : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → ℂ, Z = outer v x) (h4 : t4 v v v v ≠ 0) :
    ∃ j1 j2 : Fin 5, j1 ≠ j2 ∧ ∀ Z ∈ N, col Z j1 = 0 ∧ col Z j2 = 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 5), ∀ j, j ∈ S ↔ lfN N i0 j ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun j => lfN N i0 j ≠ 0), fun j => by simp⟩
  have hnS : ∀ j, j ∉ S → ∀ Z ∈ N, Z (i0, j) = 0 := by
    intro j hj Z hZ
    have h0 : lfN N i0 j = 0 := by
      by_contra h
      exact hj ((hS j).mpr h)
    exact LinearMap.congr_fun h0 ⟨Z, hZ⟩
  obtain ⟨z, hz⟩ := generic_pt S (lfN N i0) (fun j hj => (hS j).mp hj)
  obtain ⟨x, hx⟩ := hform z.1 z.2
  have hZx : outer v x ∈ N := by
    rw [← hx]
    exact z.2
  have hxS : ∀ j, j ∈ S → x j ≠ 0 := by
    intro j hj h0
    apply hz j hj
    rw [lfN_apply, hx]
    simp [outer, h0]
  have hxnS : ∀ j, j ∉ S → x j = 0 := by
    intro j hj
    have h : outer v x (i0, j) = 0 := hnS j hj _ hZx
    simp only [outer] at h
    exact (mul_eq_zero.mp h).resolve_left hi0
  have hker : (N ⊓ LinearMap.ker (psiS S i0) : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz' := Submodule.mem_inf.mp hZ
    obtain ⟨y, hy⟩ := hform Z hz'.1
    have hψ : psiS S i0 Z = 0 := LinearMap.mem_ker.mp hz'.2
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h : Z (i0, j) = 0 := by
        by_cases hj : j ∈ S
        · exact congrFun hψ ⟨j, hj⟩
        · exact hnS j hj Z hz'.1
      rw [hy] at h
      simp only [outer] at h
      exact (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext p
    simp [outer, hy0]
  have r := rank_nullity N (psiS S i0)
  rw [hker, finrank_bot] at r
  have hle : Module.finrank ℂ (N.map (psiS S i0)) ≤ S.card := by
    have h := Submodule.finrank_le (N.map (psiS S i0))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    exact h
  have hsum : ∀ Z ∈ N, ∑ j : ↥S, Z (i0, j.1) = 0 := by
    intro Z hZ
    have h1 : ∑ j : ↥S, Z (i0, j.1) = ∑ j ∈ S, Z (i0, j) :=
      Finset.sum_coe_sort S (fun j => Z (i0, j))
    have h2 : ∑ j ∈ S, Z (i0, j) = ∑ j, Z (i0, j) :=
      Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hnS j hj Z hZ)
    have h3 := congrFun (hrs Z hZ) i0
    rw [rs_apply] at h3
    rw [h1, h2, Fin.sum_univ_five]
    exact h3
  have hlt : S.Nonempty → Module.finrank ℂ (N.map (psiS S i0)) < S.card := by
    rintro ⟨j0, hj0⟩
    have hsub : N.map (psiS S i0) ≤
        LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) := by
      rintro _ ⟨Z, hZ, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      exact hsum Z hZ
    have hne' : LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) ≠ ⊤ := by
      intro h
      have hm : (Pi.single (⟨j0, hj0⟩ : ↥S) (1 : ℂ)) ∈
          LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → ℂ) →ₗ[ℂ] ℂ)) :=
        h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sum_apply] at hm
      simp at hm
    have h1 := Submodule.finrank_lt hne'
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    exact lt_of_le_of_lt (Submodule.finrank_mono hsub) h1
  have hprod : ∀ m : Fin 5, ∃ k : Fin 4, m.succAbove k ∉ S := by
    intro m
    have h := (A1facts N hN v hv2 x hZx m).2
    have h' := (mul_eq_zero.mp h).resolve_left h4
    rcases mul_eq_zero.mp h' with h3 | h3
    · rcases mul_eq_zero.mp h3 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h1 | h1
        · exact ⟨0, fun hin => hxS _ hin h1⟩
        · exact ⟨1, fun hin => hxS _ hin h1⟩
      · exact ⟨2, fun hin => hxS _ hin h2⟩
    · exact ⟨3, fun hin => hxS _ hin h3⟩
  obtain ⟨k1, hk1⟩ := hprod 0
  obtain ⟨k2, hk2⟩ := hprod ((0 : Fin 5).succAbove k1)
  refine ⟨(0 : Fin 5).succAbove k1, ((0 : Fin 5).succAbove k1).succAbove k2,
    (Fin.succAbove_ne _ _).symm, fun Z hZ => ?_⟩
  have hc : ∀ j, j ∉ S → col Z j = 0 := by
    intro j hj
    obtain ⟨y, hy⟩ := hform Z hZ
    have h := hnS j hj Z hZ
    rw [hy] at h
    simp only [outer] at h
    have hyj : y j = 0 := (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext i
    simp [col, outer, hyj]
  exact ⟨hc _ hk1, hc _ hk2⟩

theorem cols_zero (σ : Equiv.Perm (Fin 5)) (Z : M45) (h : ∀ j, col Z (σ j) = 0) : Z = 0 := by
  funext ⟨i, m⟩
  have hh := congrFun (h (σ.symm m)) i
  rw [Equiv.apply_symm_apply] at hh
  exact hh

theorem S6_active (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0)
    (hd : Module.finrank ℂ N = 2) (z : M45)
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hind : ∀ s1 s2 s3 : ℂ, s1 • col z a + s2 • col z b + s3 • col z c = 0 →
      s1 = 0 ∧ s2 = 0 ∧ s3 = 0) : ∀ m, col z m ≠ 0 := by
  intro m hm
  have hma : a ≠ m := by
    intro h
    have h1 := (hind 1 0 0 (by rw [h, hm]; simp)).1
    exact one_ne_zero h1
  have hmb : b ≠ m := by
    intro h
    have h1 := (hind 0 1 0 (by rw [h, hm]; simp)).2.1
    exact one_ne_zero h1
  have hmc : c ≠ m := by
    intro h
    have h1 := (hind 0 0 1 (by rw [h, hm]; simp)).2.2
    exact one_ne_zero h1
  obtain ⟨σ, h0, h1, h2, h3⟩ := perm_four a b c m hab hac hma hbc hmb hmc
  have p := peel N hN hrs (σ 4)
  have hbot : (N ⊓ LinearMap.ker (colL (σ 4)) : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz1 := Submodule.mem_inf.mp hZ
    have hZN := hz1.1
    have c4 : col Z (σ 4) = 0 := LinearMap.mem_ker.mp hz1.2
    obtain ⟨s1, e1⟩ := hmax Z hZN a
    obtain ⟨s2, e2⟩ := hmax Z hZN b
    obtain ⟨s3, e3⟩ := hmax Z hZN c
    obtain ⟨s4, e4⟩ := hmax Z hZN m
    rw [hm, smul_zero] at e4
    have hsum := sum_cols_perm σ Z
    rw [h0, h1, h2, h3, c4, hrs Z hZN, e1, e2, e3, e4, add_zero, add_zero] at hsum
    obtain ⟨u1, u2, u3⟩ := hind s1 s2 s3 hsum
    apply cols_zero σ
    apply fin5
    · rw [h0, e1, u1, zero_smul]
    · rw [h1, e2, u2, zero_smul]
    · rw [h2, e3, u3, zero_smul]
    · rw [h3]
      exact e4
    · exact c4
  rw [hbot, finrank_bot] at p
  omega

theorem SLev_N (K : Submodule ℂ M45) (hK : SLev K) :
    SLev (K ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
  fun Y hY a => hK Y (Submodule.mem_inf.mp hY).1 a

theorem rs_N (K : Submodule ℂ M45) :
    ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), rs Z = 0 :=
  fun _ hZ => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2

theorem col_outer (v : V4) (x : Fin 5 → ℂ) (m : Fin 5) : col (outer v x) m = x m • v := by
  funext i
  simp only [col, outer, Pi.smul_apply, smul_eq_mul]
  ring

def sw02 : Equiv.Perm (Fin 5) := Equiv.swap 0 2

theorem sw02_0 : sw02 0 = 2 := by decide

theorem sw02_3 : sw02 3 = 3 := by decide

theorem sw02_4 : sw02 4 = 4 := by decide

theorem S8_elem (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0)
    (hd : Module.finrank ℂ N = 2) (v : V4) (hv : v ≠ 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → ℂ, Z = outer v x) (σ : Equiv.Perm (Fin 5))
    (h3 : ∀ Z ∈ N, col Z (σ 3) = 0) (h4 : ∀ Z ∈ N, col Z (σ 4) = 0) :
    ∃ W ∈ N, col W (σ 0) = v ∧ col W (σ 1) = (-1 : ℂ) • v ∧ col W (σ 2) = 0 ∧
      col W (σ 3) = 0 ∧ col W (σ 4) = 0 := by
  have p := peel N hN hrs (σ 2)
  have hne : (N ⊓ LinearMap.ker (colL (σ 2)) : Submodule ℂ M45) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at p
    omega
  obtain ⟨W0, hW0, hW0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hW0
  have hWN := hw.1
  have a2 : col W0 (σ 2) = 0 := LinearMap.mem_ker.mp hw.2
  have a3 := h3 W0 hWN
  have a4 := h4 W0 hWN
  obtain ⟨x, hx⟩ := hform W0 hWN
  have b0 : col W0 (σ 0) = x (σ 0) • v := by rw [hx, col_outer]
  have b1 : col W0 (σ 1) = x (σ 1) • v := by rw [hx, col_outer]
  have hsum := sum_cols_perm σ W0
  rw [b0, b1, a2, a3, a4, hrs W0 hWN, add_zero, add_zero, add_zero, ← add_smul] at hsum
  have hx01 : x (σ 0) + x (σ 1) = 0 := (smul_eq_zero.mp hsum).resolve_right hv
  have hx1 : x (σ 1) = -x (σ 0) := by linear_combination hx01
  have hx0 : x (σ 0) ≠ 0 := by
    intro h
    apply hW0ne
    apply cols_zero σ
    apply fin5
    · rw [b0, h, zero_smul]
    · rw [b1, hx1, h, neg_zero, zero_smul]
    · exact a2
    · exact a3
    · exact a4
  refine ⟨(x (σ 0))⁻¹ • W0, N.smul_mem _ hWN, ?_, ?_, ?_, ?_, ?_⟩
  · show (x (σ 0))⁻¹ • col W0 (σ 0) = v
    rw [b0, smul_smul, inv_mul_cancel₀ hx0, one_smul]
  · show (x (σ 0))⁻¹ • col W0 (σ 1) = (-1 : ℂ) • v
    rw [b1, hx1, smul_smul, mul_neg, inv_mul_cancel₀ hx0]
  · show (x (σ 0))⁻¹ • col W0 (σ 2) = 0
    rw [a2, smul_zero]
  · show (x (σ 0))⁻¹ • col W0 (σ 3) = 0
    rw [a3, smul_zero]
  · show (x (σ 0))⁻¹ • col W0 (σ 4) = 0
    rw [a4, smul_zero]

theorem S8_step1 (K : Submodule ℂ M45) (hK : SLev K) (Yu : M45) (hYu : Yu ∈ K)
    (hu : ip (rs Yu) (rs Yu) = 0)
    (hd : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2) (v : V4)
    (hv : v ≠ 0) (hv3 : t3 v v v = 0)
    (hform : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), ∃ x : Fin 5 → ℂ,
      Z = outer v x)
    (σ : Equiv.Perm (Fin 5))
    (h3 : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 3) = 0)
    (h4 : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 4) = 0) :
    t3 v v (rs Yu) = 0 ∧ t3 v v (phi (σ 3) Yu) = 0 ∧ t3 v v (phi (σ 4) Yu) = 0 := by
  have hNs := SLev_N K hK
  have hrsN := rs_N K
  obtain ⟨W, hWN, w0, w1, w2, w3, w4⟩ := S8_elem _ hNs hrsN hd v hv hform σ h3 h4
  have hWK : W ∈ K := (Submodule.mem_inf.mp hWN).1
  have hKσ := SLev_perm σ K hK
  have e0 : ∀ i, W (i, σ 0) = v i := fun i => congrFun w0 i
  have e1 : ∀ i, W (i, σ 1) = -1 * v i := fun i => congrFun w1 i
  have e2 : ∀ i, W (i, σ 2) = 0 := fun i => congrFun w2 i
  have e3 : ∀ i, W (i, σ 3) = 0 := fun i => congrFun w3 i
  have e4 : ∀ i, W (i, σ 4) = 0 := fun i => congrFun w4 i
  have A : t3 v v (col Yu (σ 2)) + t3 v v (col Yu (σ 3)) = 0 := by
    have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 4).2.1
    have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 4).2.1
    have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 4).2.1
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at kp km k0
    simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3, e4]
      at kp km k0
    simp only [t3, col]
    linear_combination (-1 / 2 : ℂ) * (kp + km - 2 * k0)
  have B : t3 v v (col Yu (σ 2)) + t3 v v (col Yu (σ 4)) = 0 := by
    have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 3).2.1
    have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 3).2.1
    have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 3).2.1
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at kp km k0
    simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3, e4]
      at kp km k0
    simp only [t3, col]
    linear_combination (-1 / 2 : ℂ) * (kp + km - 2 * k0)
  have C : t3 v v (col Yu (σ 3)) + t3 v v (col Yu (σ 4)) = 0 := by
    have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 2).2.1
    have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 2).2.1
    have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 2).2.1
    rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at kp km k0
    simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3, e4]
      at kp km k0
    simp only [t3, col]
    linear_combination (-1 / 2 : ℂ) * (kp + km - 2 * k0)
  obtain ⟨W', hW'N, w0', _, _, _, _⟩ := S8_elem _ hNs hrsN hd v hv hform (σ * sw02)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_3]
      exact h3 Z hZ)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_4]
      exact h4 Z hZ)
  rw [Equiv.Perm.mul_apply, sw02_0] at w0'
  have hne2 : col W' (σ 2) ≠ 0 := by
    rw [w0']
    exact hv
  obtain ⟨c, hc⟩ := Biii K hK Yu hYu hu W' hW'N (σ 2) hne2
  rw [w0'] at hc
  have f2 : ∀ i, 2 * Yu (i, σ 2) - rs Yu i = c * v i := fun i => congrFun hc i
  have f20 := f2 0
  have f21 := f2 1
  have f22 := f2 2
  have f23 := f2 3
  simp only [t3, col] at A B C hv3
  refine ⟨?_, ?_, ?_⟩
  · simp only [t3]
    linear_combination A + B - C
      - (v 0 * v 0 * f20 + v 1 * v 1 * f21 + v 2 * v 2 * f22 + v 3 * v 3 * f23) - c * hv3
  · simp only [t3, phi_apply]
    linear_combination (-2 : ℂ) * B + 2 * C
      + (v 0 * v 0 * f20 + v 1 * v 1 * f21 + v 2 * v 2 * f22 + v 3 * v 3 * f23) + c * hv3
  · simp only [t3, phi_apply]
    linear_combination (-2 : ℂ) * A + 2 * C
      + (v 0 * v 0 * f20 + v 1 * v 1 * f21 + v 2 * v 2 * f22 + v 3 * v 3 * f23) + c * hv3

theorem line_form (N : Submodule ℂ M45) (z : M45)
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) (m0 : Fin 5)
    (hline : ∀ m, ∃ c : ℂ, col z m = c • col z m0) :
    ∀ Z ∈ N, ∃ x : Fin 5 → ℂ, Z = outer (col z m0) x := by
  intro Z hZ
  have h : ∀ m, ∃ d : ℂ, col Z m = d • col z m0 := by
    intro m
    obtain ⟨c, hc⟩ := hmax Z hZ m
    obtain ⟨c', hc'⟩ := hline m
    exact ⟨c * c', by rw [hc, hc', smul_smul]⟩
  choose x hx using h
  refine ⟨x, ?_⟩
  funext ⟨i, m⟩
  have hh := congrFun (hx m) i
  simp only [col, Pi.smul_apply, smul_eq_mul] at hh
  simp only [outer, col]
  rw [hh, mul_comm]

theorem tricho (N : Submodule ℂ M45) (z : M45)
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) :
    (∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ s1 s2 s3 : ℂ,
      s1 • col z a + s2 • col z b + s3 • col z c = 0 → s1 = 0 ∧ s2 = 0 ∧ s3 = 0)
    ∨ (∃ a b : Fin 5, indep (col z a) (col z b) ∧
      ∀ m, ∃ s t : ℂ, col z m = s • col z a + t • col z b)
    ∨ (∃ m0 : Fin 5, col z m0 ≠ 0 ∧ ∀ Z ∈ N, ∃ x : Fin 5 → ℂ, Z = outer (col z m0) x)
    ∨ N = ⊥ := by
  by_cases h2 : ∃ a b : Fin 5, indep (col z a) (col z b)
  · obtain ⟨a, b, hab⟩ := h2
    by_cases h3 : ∃ c : Fin 5, ∀ s1 s2 s3 : ℂ,
        s1 • col z a + s2 • col z b + s3 • col z c = 0 → s1 = 0 ∧ s2 = 0 ∧ s3 = 0
    · obtain ⟨c, hc⟩ := h3
      have hne_ab : a ≠ b := by
        intro h
        have h1 := (hab 1 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_ac : a ≠ c := by
        intro h
        have h1 := (hc 1 0 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_bc : b ≠ c := by
        intro h
        have h1 := (hc 0 1 (-1) (by rw [h]; simp)).2.1
        exact one_ne_zero h1
      exact Or.inl ⟨a, b, c, hne_ab, hne_ac, hne_bc, hc⟩
    · refine Or.inr (Or.inl ⟨a, b, hab, ?_⟩)
      intro m
      by_contra hcon
      apply h3
      refine ⟨m, fun s1 s2 s3 h => ?_⟩
      have hs3 : s3 = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s1 * s3⁻¹, -s2 * s3⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination s3⁻¹ * hi - col z m i * hinv
      rw [hs3, zero_smul, add_zero] at h
      obtain ⟨t1, t2⟩ := hab s1 s2 h
      exact ⟨t1, t2, hs3⟩
  · by_cases hall : ∀ m, col z m = 0
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [eq_bot_iff]
      intro Z hZ
      rw [Submodule.mem_bot]
      funext ⟨i, m⟩
      obtain ⟨c, hc⟩ := hmax Z hZ m
      have hh := congrFun hc i
      rw [hall m] at hh
      simpa [col] using hh
    · obtain ⟨m0, hm0⟩ : ∃ m0, col z m0 ≠ 0 := by
        by_contra h
        apply hall
        intro m
        by_contra hm
        exact h ⟨m, hm⟩
      refine Or.inr (Or.inr (Or.inl ⟨m0, hm0, line_form N z hmax m0 ?_⟩))
      intro m
      by_contra hcon
      apply h2
      refine ⟨m0, m, fun s t h => ?_⟩
      have ht : t = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s * t⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination t⁻¹ * hi - col z m i * hinv
      rw [ht, zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right hm0, ht⟩

def HypS6 : Prop :=
  ∀ N : Submodule ℂ M45, SLev N → (∀ Z ∈ N, rs Z = 0) → Module.finrank ℂ N = 2 →
    ∀ z ∈ N, (∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) →
    ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
    (∀ s1 s2 s3 : ℂ, s1 • col z a + s2 • col z b + s3 • col z c = 0 →
      s1 = 0 ∧ s2 = 0 ∧ s3 = 0) → (∀ m, col z m ≠ 0) → False

def HypS7 : Prop :=
  ∀ K : Submodule ℂ M45, SLev K → Module.finrank ℂ (K.map rs) = 2 →
    (∃ u ∈ K.map rs, u ≠ 0 ∧ ∀ s ∈ K.map rs, ip u s = 0) →
    Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2 →
    ∀ z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45),
    (∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), ∀ m, ∃ c : ℂ, col Z m = c • col z m) →
    ∀ σ : Equiv.Perm (Fin 5), indep (col z (σ 0)) (col z (σ 2)) →
    col z (σ 1) = (-1 : ℂ) • col z (σ 0) → col z (σ 3) = (-1 : ℂ) • col z (σ 2) →
    col z (σ 4) = 0 →
    t3 (col z (σ 0)) (col z (σ 2)) (col z (σ 2)) = 0 →
    t3 (col z (σ 0)) (col z (σ 0)) (col z (σ 2)) = 0 →
    br (col z (σ 0)) (col z (σ 0)) (col z (σ 2)) (col z (σ 2)) = 0 → False

def HypS8 : Prop :=
  ∀ K : Submodule ℂ M45, SLev K → Module.finrank ℂ (K.map rs) = 2 →
    Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2 →
    ∀ Yu ∈ K, rs Yu ≠ 0 → (∀ s ∈ K.map rs, ip (rs Yu) s = 0) →
    ∀ v : V4, v ≠ 0 → tau v = 0 → ip v v = 0 → t3 v v v = 0 →
    (∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), ∃ x : Fin 5 → ℂ, Z = outer v x) →
    ∀ σ : Equiv.Perm (Fin 5),
    (∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 3) = 0) →
    (∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 4) = 0) →
    t3 v v (rs Yu) = 0 → t3 v v (phi (σ 3) Yu) = 0 → t3 v v (phi (σ 4) Yu) = 0 → False

theorem No22 (H6 : HypS6) (H7 : HypS7) (H8 : HypS8) (K : Submodule ℂ M45) (hK : SLev K)
    (hq : Module.finrank ℂ (K.map rs) = 2)
    (hd : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2) : False := by
  have hNs := SLev_N K hK
  have hrs := rs_N K
  have hne : (K ⊓ LinearMap.ker rs : Submodule ℂ M45) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hd
    omega
  have hu := Bii K hK hq hne
  obtain ⟨z, hz, hmax⟩ := maxpt _ hNs hrs
  rcases tricho _ z hmax with ⟨a, b, c, hab, hac, hbc, hind⟩ | ⟨a, b, hab, hspan⟩ |
    ⟨m0, hm0, hform⟩ | hbot
  · exact H6 _ hNs hrs hd z hz hmax a b c hab hac hbc hind
      (S6_active _ hNs hrs hd z hmax a b c hab hac hbc hind)
  · obtain ⟨σ, h0, h2, e1, e3, e4⟩ := two_line_pattern _ hNs hrs z hz a b hab hspan
    subst h0
    subst h2
    have ids := typeII_ids _ hNs z hz σ (col z (σ 0)) (col z (σ 2)) rfl e1 rfl e3 e4
    exact H7 K hK hq hu hd z hz hmax σ hab e1 e3 e4 ids.1 ids.2.1 ids.2.2
  · by_cases h3 : t3 (col z m0) (col z m0) (col z m0) = 0
    · have h4 : t4 (col z m0) (col z m0) (col z m0) (col z m0) ≠ 0 := fun h =>
        hm0 (iso34 _ (C1 _ hNs z hz m0) (Niso _ hNs hrs z z hz hz m0) h3 h)
      obtain ⟨j1, j2, hj, hcols⟩ := A1cols _ hNs hrs (col z m0) hm0 (C1 _ hNs z hz m0)
        (Niso _ hNs hrs z z hz hz m0) hform h4
      obtain ⟨σ, s3, s4⟩ := perm_two (3 : Fin 5) 4 j1 j2 (by decide) hj
      obtain ⟨u, huS, hu0, huperp⟩ := hu
      obtain ⟨Yu, hYu, rfl⟩ := huS
      have huu : ip (rs Yu) (rs Yu) = 0 := huperp _ (Submodule.mem_map_of_mem hYu)
      have c3 : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 3) = 0 :=
        fun Z hZ => by
          rw [s3]
          exact (hcols Z hZ).1
      have c4 : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 4) = 0 :=
        fun Z hZ => by
          rw [s4]
          exact (hcols Z hZ).2
      have st := S8_step1 K hK Yu hYu huu hd (col z m0) hm0 h3 hform σ c3 c4
      exact H8 K hK hq hd Yu hYu hu0 huperp (col z m0) hm0 (C1 _ hNs z hz m0)
        (Niso _ hNs hrs z z hz hz m0) h3 hform σ c3 c4 st.1 st.2.1 st.2.2
    · have h1 := A1b _ hNs hrs (col z m0) hm0 (C1 _ hNs z hz m0)
        (Niso _ hNs hrs z z hz hz m0) hform h3
      omega
  · exact hne hbot

theorem SL_of (H6 : HypS6) (H7 : HypS7) (H8 : HypS8)
    (K : Submodule ℂ M45) (hK : SLev K) : Module.finrank ℂ K ≤ 3 := by
  have r := rank_nullity K rs
  have hq := (Submodule.finrank_mono (map_rs_le K hK)).trans (finrank_sumZero (n := 4) (by norm_num))
  have hd := LemA_proof _ (SLev_N K hK) (rs_N K)
  by_cases h3 : Module.finrank ℂ (K.map rs) = 3
  · have hb := Bi K hK h3
    rw [hb, finrank_bot] at r
    omega
  · by_cases h2 : Module.finrank ℂ (K.map rs) = 2 ∧
        Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2
    · exact (No22 H6 H7 H8 K hK h2.1 h2.2).elim
    · omega

theorem FL_of (HSL : ∀ K : Submodule ℂ M45, SLev K → Module.finrank ℂ K ≤ 3)
    (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → rowMat r w ∈ L) :
    Module.finrank ℂ L ≤ 7 := by
  obtain ⟨_, h2, h3⟩ := stageA L hL r hF
  have h4 := HSL _ h2
  omega

theorem S7_elem (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0)
    (hd : Module.finrank ℂ N = 2) (z : M45)
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m) (σ : Equiv.Perm (Fin 5)) (v w : V4)
    (hi : indep v w) (c1 : col z (σ 1) = (-1 : ℂ) • v)
    (c2 : col z (σ 2) = w) (c3 : col z (σ 3) = (-1 : ℂ) • w) (c4 : col z (σ 4) = 0) :
    ∃ W ∈ N, col W (σ 0) = 0 ∧ col W (σ 1) = 0 ∧ col W (σ 2) = w ∧
      col W (σ 3) = (-1 : ℂ) • w := by
  have p := peel N hN hrs (σ 0)
  have hne : (N ⊓ LinearMap.ker (colL (σ 0)) : Submodule ℂ M45) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at p
    omega
  obtain ⟨W0, hW0, hW0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hW0
  have hWN := hw.1
  have a0 : col W0 (σ 0) = 0 := LinearMap.mem_ker.mp hw.2
  obtain ⟨k1, a1⟩ := hmax W0 hWN (σ 1)
  obtain ⟨k2, a2⟩ := hmax W0 hWN (σ 2)
  obtain ⟨k3, a3⟩ := hmax W0 hWN (σ 3)
  obtain ⟨k4, a4⟩ := hmax W0 hWN (σ 4)
  rw [c1] at a1
  rw [c2] at a2
  rw [c3] at a3
  rw [c4, smul_zero] at a4
  have hsum := sum_cols_perm σ W0
  rw [a0, a1, a2, a3, a4, hrs W0 hWN] at hsum
  have hk := hi (-k1) (k2 - k3) (by
    funext i
    have hi' := congrFun hsum i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi' ⊢
    linear_combination hi')
  have hk1 : k1 = 0 := neg_eq_zero.mp hk.1
  have hk3 : k3 = k2 := (sub_eq_zero.mp hk.2).symm
  have hk2 : k2 ≠ 0 := by
    intro h
    apply hW0ne
    apply cols_zero σ
    apply fin5
    · exact a0
    · rw [a1, hk1, zero_smul]
    · rw [a2, h, zero_smul]
    · rw [a3, hk3, h, zero_smul]
    · exact a4
  refine ⟨k2⁻¹ • W0, N.smul_mem _ hWN, ?_, ?_, ?_, ?_⟩
  · show k2⁻¹ • col W0 (σ 0) = 0
    rw [a0, smul_zero]
  · show k2⁻¹ • col W0 (σ 1) = 0
    rw [a1, hk1, zero_smul, smul_zero]
  · show k2⁻¹ • col W0 (σ 2) = w
    rw [a2, smul_smul, inv_mul_cancel₀ hk2, one_smul]
  · show k2⁻¹ • col W0 (σ 3) = (-1 : ℂ) • w
    rw [a3, hk3, smul_smul, inv_mul_cancel₀ hk2, one_smul]

theorem S7_step (K : Submodule ℂ M45) (hK : SLev K) (Yu : M45) (hYu : Yu ∈ K)
    (hu : ip (rs Yu) (rs Yu) = 0)
    (hd : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2) (z : M45)
    (hz : z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45))
    (hmax : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), ∀ m, ∃ c : ℂ,
      col Z m = c • col z m)
    (σ : Equiv.Perm (Fin 5)) (v w : V4) (hi : indep v w) (c0 : col z (σ 0) = v)
    (c1 : col z (σ 1) = (-1 : ℂ) • v) (c2 : col z (σ 2) = w)
    (c3 : col z (σ 3) = (-1 : ℂ) • w) (c4 : col z (σ 4) = 0) (hvww : t3 v w w = 0) :
    t3 (rs Yu) w w = 0 := by
  have hNs := SLev_N K hK
  have hrsN := rs_N K
  obtain ⟨W, hWN, w0, w1, w2, w3⟩ := S7_elem _ hNs hrsN hd z hmax σ v w hi c1 c2 c3 c4
  have hWK : W ∈ K := (Submodule.mem_inf.mp hWN).1
  have hKσ := SLev_perm σ K hK
  have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 4).2.1
  have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 4).2.1
  have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 4).2.1
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at kp km k0
  have e0 : ∀ i, W (i, σ 0) = 0 := fun i => congrFun w0 i
  have e1 : ∀ i, W (i, σ 1) = 0 := fun i => congrFun w1 i
  have e2 : ∀ i, W (i, σ 2) = w i := fun i => congrFun w2 i
  have e3 : ∀ i, W (i, σ 3) = -1 * w i := fun i => congrFun w3 i
  simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3] at kp km k0
  have hc : t3 (col Yu (σ 0)) w w + t3 (col Yu (σ 1)) w w = 0 := by
    simp only [t3, col]
    linear_combination (-1 / 2 : ℂ) * (kp + km - 2 * k0)
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := (hi 1 0 (by rw [h]; simp)).1
    exact one_ne_zero h1
  have hz0 : col z (σ 0) ≠ 0 := by
    rw [c0]
    exact hv0
  have hz1 : col z (σ 1) ≠ 0 := by
    rw [c1]
    intro h
    exact hv0 ((smul_eq_zero.mp h).resolve_left (by norm_num))
  obtain ⟨β0, hβ0⟩ := Biii K hK Yu hYu hu z hz (σ 0) hz0
  obtain ⟨β1, hβ1⟩ := Biii K hK Yu hYu hu z hz (σ 1) hz1
  rw [c0] at hβ0
  rw [c1] at hβ1
  have f0 : ∀ i, 2 * Yu (i, σ 0) - rs Yu i = β0 * v i := fun i => congrFun hβ0 i
  have f1 : ∀ i, 2 * Yu (i, σ 1) - rs Yu i = β1 * (-1 * v i) := fun i => congrFun hβ1 i
  have f00 := f0 0
  have f01 := f0 1
  have f02 := f0 2
  have f03 := f0 3
  have f10 := f1 0
  have f11 := f1 1
  have f12 := f1 2
  have f13 := f1 3
  simp only [t3, col] at hc hvww ⊢
  linear_combination hc
    - (1 / 2 : ℂ) * (w 0 * w 0 * f00 + w 1 * w 1 * f01 + w 2 * w 2 * f02 + w 3 * w 3 * f03)
    - (1 / 2 : ℂ) * (w 0 * w 0 * f10 + w 1 * w 1 * f11 + w 2 * w 2 * f12 + w 3 * w 3 * f13)
    - ((β0 - β1) / 2) * hvww

def HypS7alg : Prop :=
  ∀ v w u : V4, tau v = 0 → ip v v = 0 → tau w = 0 → ip w w = 0 → indep v w →
    t3 v w w = 0 → t3 v v w = 0 → br v v w w = 0 →
    u ≠ 0 → tau u = 0 → ip u u = 0 → t3 u v v = 0 → t3 u w w = 0 → False

theorem HypS7_of (h : HypS7alg) : HypS7 := by
  unfold HypS7
  intro K hK hq hu hd z hz hmax σ hind e1 e3 e4 i1 i2 i3
  obtain ⟨u, huS, hu0, huperp⟩ := hu
  obtain ⟨Yu, hYu, rfl⟩ := huS
  have huu : ip (rs Yu) (rs Yu) = 0 := huperp _ (Submodule.mem_map_of_mem hYu)
  have hzK := (Submodule.mem_inf.mp hz).1
  have s1 := S7_step K hK Yu hYu huu hd z hz hmax σ (col z (σ 0)) (col z (σ 2)) hind rfl e1
    rfl e3 e4 i1
  have s2 := S7_step K hK Yu hYu huu hd z hz hmax (σ * swp) (col z (σ 2)) (col z (σ 0))
    (indep_symm hind)
    (by rw [Equiv.Perm.mul_apply, swp0])
    (by rw [Equiv.Perm.mul_apply, swp1, e3])
    (by rw [Equiv.Perm.mul_apply, swp2])
    (by rw [Equiv.Perm.mul_apply, swp3, e1])
    (by rw [Equiv.Perm.mul_apply, swp4, e4])
    (by
      simp only [t3] at i2 ⊢
      linear_combination i2)
  exact h (col z (σ 0)) (col z (σ 2)) (rs Yu) (C1 K hK z hzK (σ 0))
    (N_iso K hK z z hz hz (σ 0)) (C1 K hK z hzK (σ 2)) (N_iso K hK z z hz hz (σ 2)) hind
    i1 i2 i3 hu0 (tau_rs K hK Yu hYu) huu s2 s1

def HypIIa : Prop :=
  ∀ v w : V4, tau v = 0 → ip v v = 0 → tau w = 0 → ip w w = 0 → indep v w →
    t3 v w w = 0 → t3 v v w = 0 → br v v w w = 0 →
    (∃ c : ℂ, (fun i => v i * v i : V4) = c • w) ∧ (∃ c : ℂ, (fun i => w i * w i : V4) = c • v)

theorem HypS7alg_of (h : HypIIa) : HypS7alg := by
  unfold HypS7alg
  intro v w u hv1 hv2 hw1 hw2 hind i1 i2 i3 hu0 hu1 hu2 j1 j2
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := h v w hv1 hv2 hw1 hw2 hind i1 i2 i3
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := (hind 1 0 (by rw [h0]; simp)).1
    exact one_ne_zero h1
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 := (hind 0 1 (by rw [h0]; simp)).2
    exact one_ne_zero h1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hv0
    funext i
    have hi := congrFun hc i
    rw [h0, zero_smul] at hi
    exact mul_self_eq_zero.mp hi
  have hc0' : c' ≠ 0 := by
    intro h0
    apply hw0
    funext i
    have hi := congrFun hc' i
    rw [h0, zero_smul] at hi
    exact mul_self_eq_zero.mp hi
  have huw : ip u w = 0 := by
    have e : c * ip u w = 0 := by
      have q0 := congrFun hc 0
      have q1 := congrFun hc 1
      have q2 := congrFun hc 2
      have q3 := congrFun hc 3
      simp only [Pi.smul_apply, smul_eq_mul] at q0 q1 q2 q3
      simp only [t3, ip] at j1 ⊢
      linear_combination j1 - u 0 * q0 - u 1 * q1 - u 2 * q2 - u 3 * q3
    exact (mul_eq_zero.mp e).resolve_left hc0
  have huv : ip u v = 0 := by
    have e : c' * ip u v = 0 := by
      have q0 := congrFun hc' 0
      have q1 := congrFun hc' 1
      have q2 := congrFun hc' 2
      have q3 := congrFun hc' 3
      simp only [Pi.smul_apply, smul_eq_mul] at q0 q1 q2 q3
      simp only [t3, ip] at j2 ⊢
      linear_combination j2 - u 0 * q0 - u 1 * q1 - u 2 * q2 - u 3 * q3
    exact (mul_eq_zero.mp e).resolve_left hc0'
  obtain ⟨k, hk⟩ := Q4 u v hu0 hu1 hu2 hv1 hv2 huv
  obtain ⟨k', hk'⟩ := Q4 u w hu0 hu1 hu2 hw1 hw2 huw
  have hkk := hind k' (-k) (by
    rw [hk, hk']
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring)
  apply hw0
  rw [hk', hkk.1, zero_smul]

theorem IIa_tu (t u : ℂ) (htu : t ≠ u)
    (E1 : 2 * u + t + t * u ^ 4 / 4 + t ^ 2 * u ^ 3 / 2 = 0)
    (E2 : 2 * t + u + u * t ^ 4 / 4 + u ^ 2 * t ^ 3 / 2 = 0)
    (B : 8 * (t - u) ^ 4
      - 24 * ((1 + t ^ 4 / 4) * (1 + u ^ 4 / 4) - 2 * t * u * (t ^ 2 + u ^ 2)) = 0) :
    4 + t ^ 4 + 4 * t ^ 3 * u = 0 ∧ t ^ 2 * u ^ 2 = 4 := by
  have hD : (u - t) * (4 + (t + u) ^ 2 * (t * u) + (t * u) ^ 2) = 0 := by
    linear_combination 4 * E1 - 4 * E2
  have h1 : 4 + (t + u) ^ 2 * (t * u) + (t * u) ^ 2 = 0 :=
    (mul_eq_zero.mp hD).resolve_left (sub_ne_zero.mpr (Ne.symm htu))
  have hS : (t + u) * (12 + (t + u) ^ 2 * (t * u) - (t * u) ^ 2) = 0 := by
    linear_combination 4 * E1 + 4 * E2
  rcases mul_eq_zero.mp hS with ha | h2
  · exfalso
    have hu : u = -t := by linear_combination ha
    subst hu
    have h128 : (128 : ℂ) = 0 := by
      linear_combination (-1 : ℂ) * B + (32 - (3 / 2 : ℂ) * (t ^ 4 + 4)) * h1
    norm_num at h128
  · have hb : t ^ 2 * u ^ 2 = 4 := by
      linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2
    refine ⟨?_, hb⟩
    linear_combination (1 / 4 : ℂ) * (t * u) * t ^ 2 * h1
      - ((3 / 4 : ℂ) * (t * u) * t ^ 2 + (1 / 4 : ℂ) * (t ^ 4 + (t * u) ^ 2 + 4)) * hb

def Ps4 (j a0 a1 a2 a3 : ℂ) : V4 :=
  ![a0 + a1 + a2 + a3, a0 + a1 * j - a2 - a3 * j, a0 - a1 + a2 - a3, a0 - a1 * j - a2 + a3 * j]

theorem Ps4_0 (j a0 a1 a2 a3 : ℂ) : Ps4 j a0 a1 a2 a3 0 = a0 + a1 + a2 + a3 := rfl

theorem Ps4_1 (j a0 a1 a2 a3 : ℂ) : Ps4 j a0 a1 a2 a3 1 = a0 + a1 * j - a2 - a3 * j := rfl

theorem Ps4_2 (j a0 a1 a2 a3 : ℂ) : Ps4 j a0 a1 a2 a3 2 = a0 - a1 + a2 - a3 := rfl

theorem Ps4_3 (j a0 a1 a2 a3 : ℂ) : Ps4 j a0 a1 a2 a3 3 = a0 - a1 * j - a2 + a3 * j := rfl

theorem tau_Ps4 (j a0 a1 a2 a3 : ℂ) : tau (Ps4 j a0 a1 a2 a3) = 4 * a0 := by
  simp only [tau, Ps4_0, Ps4_1, Ps4_2, Ps4_3]
  ring

theorem Ps4_mul (j : ℂ) (hj : j * j = -1) (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ) :
    (fun i => Ps4 j a0 a1 a2 a3 i * Ps4 j b0 b1 b2 b3 i : V4) =
      Ps4 j (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) (a0 * b1 + a1 * b0 + a2 * b3 + a3 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3) (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  funext i
  fin_cases i
  · show Ps4 j a0 a1 a2 a3 0 * Ps4 j b0 b1 b2 b3 0 = Ps4 j _ _ _ _ 0
    simp only [Ps4_0]
    ring
  · show Ps4 j a0 a1 a2 a3 1 * Ps4 j b0 b1 b2 b3 1 = Ps4 j _ _ _ _ 1
    simp only [Ps4_1]
    linear_combination (a1 - a3) * (b1 - b3) * hj
  · show Ps4 j a0 a1 a2 a3 2 * Ps4 j b0 b1 b2 b3 2 = Ps4 j _ _ _ _ 2
    simp only [Ps4_2]
    ring
  · show Ps4 j a0 a1 a2 a3 3 * Ps4 j b0 b1 b2 b3 3 = Ps4 j _ _ _ _ 3
    simp only [Ps4_3]
    linear_combination (a1 - a3) * (b1 - b3) * hj

theorem ip_Ps4 (j : ℂ) (hj : j * j = -1) (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ) :
    ip (Ps4 j a0 a1 a2 a3) (Ps4 j b0 b1 b2 b3) =
      4 * (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) := by
  have e : ip (Ps4 j a0 a1 a2 a3) (Ps4 j b0 b1 b2 b3) =
      tau (fun i => Ps4 j a0 a1 a2 a3 i * Ps4 j b0 b1 b2 b3 i : V4) := by
    simp only [ip, tau]
  rw [e, Ps4_mul j hj, tau_Ps4]

theorem Ps4_param (j : ℂ) (hj : j * j = -1) (v : V4) (hv : tau v = 0) :
    v = Ps4 j 0 ((v 0 - j * v 1 - v 2 + j * v 3) / 4) ((v 0 - v 1 + v 2 - v 3) / 4)
      ((v 0 + j * v 1 - v 2 - j * v 3) / 4) := by
  simp only [tau] at hv
  funext i
  fin_cases i
  · show v 0 = Ps4 j _ _ _ _ 0
    simp only [Ps4_0]
    linear_combination (1 / 4 : ℂ) * hv
  · show v 1 = Ps4 j _ _ _ _ 1
    simp only [Ps4_1]
    linear_combination (1 / 4 : ℂ) * hv - ((v 3 - v 1) / 2) * hj
  · show v 2 = Ps4 j _ _ _ _ 2
    simp only [Ps4_2]
    linear_combination (1 / 4 : ℂ) * hv
  · show v 3 = Ps4 j _ _ _ _ 3
    simp only [Ps4_3]
    linear_combination (1 / 4 : ℂ) * hv + ((v 3 - v 1) / 2) * hj

theorem t3_ip_r (x y z : V4) : t3 x y z = ip x (fun i => y i * z i : V4) := by
  simp only [t3, ip]
  ring

theorem t3_ip_l (x y z : V4) : t3 x y z = ip (fun i => x i * y i : V4) z := by
  simp only [t3, ip]

theorem t4_ip (x y z w : V4) :
    t4 x y z w = ip (fun i => x i * y i : V4) (fun i => z i * w i : V4) := by
  simp only [t4, ip]
  ring

theorem IIa_pqr (p1 q1 r1 p2 q2 r2 : ℂ) (iv : 2 * p1 * r1 + q1 ^ 2 = 0)
    (iw : 2 * p2 * r2 + q2 ^ 2 = 0)
    (T1 : 2 * p1 * p2 * q2 + q1 * (p2 ^ 2 + r2 ^ 2) + 2 * r1 * q2 * r2 = 0)
    (T2 : 2 * p2 * p1 * q1 + q2 * (p1 ^ 2 + r1 ^ 2) + 2 * r2 * q1 * r1 = 0)
    (Bq : -24 * (4 * q1 * r1 * p2 * q2 + (p1 ^ 2 + r1 ^ 2) * (p2 ^ 2 + r2 ^ 2)
      + 4 * p1 * q1 * q2 * r2) + 32 * (p1 * r2 + q1 * q2 + r1 * p2) ^ 2 = 0)
    (hnp : ∀ s t : ℂ, s * p1 + t * p2 = 0 → s * q1 + t * q2 = 0 → s * r1 + t * r2 = 0 →
      s = 0 ∧ t = 0) :
    ∃ c : ℂ, 2 * q1 * r1 = c * p2 ∧ p1 ^ 2 + r1 ^ 2 = c * q2 ∧ 2 * p1 * q1 = c * r2 := by
  by_cases hp1 : p1 = 0
  · exfalso
    subst hp1
    have hq1 : q1 = 0 := by
      have h : q1 ^ 2 = 0 := by linear_combination iv
      exact (pow_eq_zero_iff (by norm_num)).mp h
    subst hq1
    have hr1 : r1 ≠ 0 := by
      intro h
      have h1 := (hnp 1 0 (by ring) (by ring) (by rw [h]; ring)).1
      exact one_ne_zero h1
    have hq2 : q2 = 0 := by
      have h : q2 * r1 ^ 2 = 0 := by linear_combination T2
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hr1)
    subst hq2
    have hp2 : p2 ≠ 0 := by
      intro h
      have h1 := (hnp r2 (-r1) (by rw [h]; ring) (by ring) (by ring)).2
      exact hr1 (neg_eq_zero.mp h1)
    have hr2 : r2 = 0 := by
      have h : p2 * r2 = 0 := by linear_combination (1 / 2 : ℂ) * iw
      exact (mul_eq_zero.mp h).resolve_left hp2
    subst hr2
    have hB : r1 ^ 2 * p2 ^ 2 = 0 := by linear_combination (1 / 8 : ℂ) * Bq
    exact mul_ne_zero (pow_ne_zero 2 hr1) (pow_ne_zero 2 hp2) hB
  · by_cases hp2 : p2 = 0
    · exfalso
      subst hp2
      have hq2 : q2 = 0 := by
        have h : q2 ^ 2 = 0 := by linear_combination iw
        exact (pow_eq_zero_iff (by norm_num)).mp h
      subst hq2
      have hr2 : r2 ≠ 0 := by
        intro h
        have h1 := (hnp 0 1 (by ring) (by ring) (by rw [h]; ring)).2
        exact one_ne_zero h1
      have hq1 : q1 = 0 := by
        have h : q1 * r2 ^ 2 = 0 := by linear_combination T1
        exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hr2)
      subst hq1
      have hr1 : r1 = 0 := by
        have h : p1 * r1 = 0 := by linear_combination (1 / 2 : ℂ) * iv
        exact (mul_eq_zero.mp h).resolve_left hp1
      subst hr1
      have hB : p1 ^ 2 * r2 ^ 2 = 0 := by linear_combination (1 / 8 : ℂ) * Bq
      exact mul_ne_zero (pow_ne_zero 2 hp1) (pow_ne_zero 2 hr2) hB
    · obtain ⟨t, ht⟩ : ∃ t : ℂ, q1 = p1 * t :=
        ⟨q1 * p1⁻¹, by linear_combination (-q1) * mul_inv_cancel₀ hp1⟩
      obtain ⟨u, hu⟩ : ∃ u : ℂ, q2 = p2 * u :=
        ⟨q2 * p2⁻¹, by linear_combination (-q2) * mul_inv_cancel₀ hp2⟩
      subst ht
      subst hu
      have hr1 : r1 = -(p1 * t ^ 2) / 2 := by
        have h : p1 * (2 * r1 + p1 * t ^ 2) = 0 := by linear_combination iv
        have h' := (mul_eq_zero.mp h).resolve_left hp1
        linear_combination (1 / 2 : ℂ) * h'
      have hr2 : r2 = -(p2 * u ^ 2) / 2 := by
        have h : p2 * (2 * r2 + p2 * u ^ 2) = 0 := by linear_combination iw
        have h' := (mul_eq_zero.mp h).resolve_left hp2
        linear_combination (1 / 2 : ℂ) * h'
      subst hr1
      subst hr2
      have E1 : 2 * u + t + t * u ^ 4 / 4 + t ^ 2 * u ^ 3 / 2 = 0 := by
        have h : p1 * p2 ^ 2 * (2 * u + t + t * u ^ 4 / 4 + t ^ 2 * u ^ 3 / 2) = 0 := by
          linear_combination T1
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hp1 (pow_ne_zero 2 hp2))
      have E2 : 2 * t + u + u * t ^ 4 / 4 + u ^ 2 * t ^ 3 / 2 = 0 := by
        have h : p1 ^ 2 * p2 * (2 * t + u + u * t ^ 4 / 4 + u ^ 2 * t ^ 3 / 2) = 0 := by
          linear_combination T2
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero 2 hp1) hp2)
      have BB : 8 * (t - u) ^ 4
          - 24 * ((1 + t ^ 4 / 4) * (1 + u ^ 4 / 4) - 2 * t * u * (t ^ 2 + u ^ 2)) = 0 := by
        have h : p1 ^ 2 * p2 ^ 2 * (8 * (t - u) ^ 4
            - 24 * ((1 + t ^ 4 / 4) * (1 + u ^ 4 / 4) - 2 * t * u * (t ^ 2 + u ^ 2))) = 0 := by
          linear_combination Bq
        exact (mul_eq_zero.mp h).resolve_left
          (mul_ne_zero (pow_ne_zero 2 hp1) (pow_ne_zero 2 hp2))
      have htu : t ≠ u := by
        intro h
        subst h
        have h1 := (hnp p2 (-p1) (by ring) (by ring) (by ring)).1
        exact hp2 h1
      obtain ⟨hA, hb⟩ := IIa_tu t u htu E1 E2 BB
      obtain ⟨c, hc⟩ : ∃ c : ℂ, c * p2 = -(p1 ^ 2 * t ^ 3) :=
        ⟨-(p1 ^ 2 * t ^ 3) * p2⁻¹, by
          linear_combination (-(p1 ^ 2 * t ^ 3)) * mul_inv_cancel₀ hp2⟩
      refine ⟨c, ?_, ?_, ?_⟩
      · linear_combination (-1 : ℂ) * hc
      · linear_combination (p1 ^ 2 / 4) * hA - u * hc
      · linear_combination (-(p1 ^ 2 * t) / 2) * hb + (u ^ 2 / 2) * hc

theorem sq_Ps4 (j : ℂ) (hj : j * j = -1) (p1 q1 r1 p2 q2 r2 c : ℂ)
    (iv : 2 * p1 * r1 + q1 ^ 2 = 0) (h1 : 2 * q1 * r1 = c * p2)
    (h2 : p1 ^ 2 + r1 ^ 2 = c * q2) (h3 : 2 * p1 * q1 = c * r2) :
    (fun i => Ps4 j 0 p1 q1 r1 i * Ps4 j 0 p1 q1 r1 i : V4) = c • Ps4 j 0 p2 q2 r2 := by
  rw [Ps4_mul j hj]
  funext i
  fin_cases i
  · show Ps4 j _ _ _ _ 0 = c * Ps4 j 0 p2 q2 r2 0
    simp only [Ps4_0]
    linear_combination iv + h1 + h2 + h3
  · show Ps4 j _ _ _ _ 1 = c * Ps4 j 0 p2 q2 r2 1
    simp only [Ps4_1]
    linear_combination iv + j * h1 - h2 - j * h3
  · show Ps4 j _ _ _ _ 2 = c * Ps4 j 0 p2 q2 r2 2
    simp only [Ps4_2]
    linear_combination iv - h1 + h2 - h3
  · show Ps4 j _ _ _ _ 3 = c * Ps4 j 0 p2 q2 r2 3
    simp only [Ps4_3]
    linear_combination iv - j * h1 - h2 + j * h3

theorem HypIIa_proof : HypIIa := by
  unfold HypIIa
  intro v w hv1 hv2 hw1 hw2 hind i1 i2 i3
  have hj : Complex.I * Complex.I = -1 := Complex.I_mul_I
  obtain ⟨p1, q1, r1, hv⟩ : ∃ p q r : ℂ, v = Ps4 Complex.I 0 p q r :=
    ⟨_, _, _, Ps4_param Complex.I hj v hv1⟩
  obtain ⟨p2, q2, r2, hw⟩ : ∃ p q r : ℂ, w = Ps4 Complex.I 0 p q r :=
    ⟨_, _, _, Ps4_param Complex.I hj w hw1⟩
  subst hv
  subst hw
  have hvv := Ps4_mul Complex.I hj 0 p1 q1 r1 0 p1 q1 r1
  have hww := Ps4_mul Complex.I hj 0 p2 q2 r2 0 p2 q2 r2
  rw [ip_Ps4 Complex.I hj] at hv2 hw2
  rw [t3_ip_r, hww, ip_Ps4 Complex.I hj] at i1
  rw [t3_ip_l, hvv, ip_Ps4 Complex.I hj] at i2
  simp only [br] at i3
  rw [t4_ip, hvv, hww] at i3
  simp only [ip_Ps4 Complex.I hj] at i3
  have iv : 2 * p1 * r1 + q1 ^ 2 = 0 := by linear_combination (1 / 4 : ℂ) * hv2
  have iw : 2 * p2 * r2 + q2 ^ 2 = 0 := by linear_combination (1 / 4 : ℂ) * hw2
  have T1 : 2 * p1 * p2 * q2 + q1 * (p2 ^ 2 + r2 ^ 2) + 2 * r1 * q2 * r2 = 0 := by
    linear_combination (1 / 4 : ℂ) * i1
  have T2 : 2 * p2 * p1 * q1 + q2 * (p1 ^ 2 + r1 ^ 2) + 2 * r2 * q1 * r1 = 0 := by
    linear_combination (1 / 4 : ℂ) * i2
  have Bq : -24 * (4 * q1 * r1 * p2 * q2 + (p1 ^ 2 + r1 ^ 2) * (p2 ^ 2 + r2 ^ 2)
      + 4 * p1 * q1 * q2 * r2) + 32 * (p1 * r2 + q1 * q2 + r1 * p2) ^ 2 = 0 := by
    linear_combination i3 + 8 * (2 * p2 * r2 + q2 ^ 2) * iv
  have hnp : ∀ s t : ℂ, s * p1 + t * p2 = 0 → s * q1 + t * q2 = 0 → s * r1 + t * r2 = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2 h3
    apply hind
    funext i
    fin_cases i
    · show s * Ps4 Complex.I 0 p1 q1 r1 0 + t * Ps4 Complex.I 0 p2 q2 r2 0 = 0
      simp only [Ps4_0]
      linear_combination h1 + h2 + h3
    · show s * Ps4 Complex.I 0 p1 q1 r1 1 + t * Ps4 Complex.I 0 p2 q2 r2 1 = 0
      simp only [Ps4_1]
      linear_combination Complex.I * h1 - h2 - Complex.I * h3
    · show s * Ps4 Complex.I 0 p1 q1 r1 2 + t * Ps4 Complex.I 0 p2 q2 r2 2 = 0
      simp only [Ps4_2]
      linear_combination (-1 : ℂ) * h1 + h2 - h3
    · show s * Ps4 Complex.I 0 p1 q1 r1 3 + t * Ps4 Complex.I 0 p2 q2 r2 3 = 0
      simp only [Ps4_3]
      linear_combination (-Complex.I) * h1 - h2 + Complex.I * h3
  obtain ⟨c, a1, a2, a3⟩ := IIa_pqr p1 q1 r1 p2 q2 r2 iv iw T1 T2 Bq hnp
  obtain ⟨c', b1, b2, b3⟩ := IIa_pqr p2 q2 r2 p1 q1 r1 iw iv (by linear_combination T2)
    (by linear_combination T1) (by linear_combination Bq)
    (fun s t h1 h2 h3 => by
      have h := hnp t s (by linear_combination h1) (by linear_combination h2)
        (by linear_combination h3)
      exact ⟨h.2, h.1⟩)
  exact ⟨⟨c, sq_Ps4 Complex.I hj p1 q1 r1 p2 q2 r2 c iv a1 a2 a3⟩,
    ⟨c', sq_Ps4 Complex.I hj p2 q2 r2 p1 q1 r1 c' iw b1 b2 b3⟩⟩

def Qv (v : V4) (a0 a1 a2 a3 : ℂ) : V4 := fun i => a0 + a1 * v i + a2 * v i ^ 2 + a3 * v i ^ 3

theorem Qv_mul (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ) :
    (fun i => Qv v a0 a1 a2 a3 i * Qv v b0 b1 b2 b3 i : V4) =
      Qv v (a0 * b0 + kap * (a1 * b3 + a2 * b2 + a3 * b1))
        (a0 * b1 + a1 * b0 + kap * (a2 * b3 + a3 * b2))
        (a0 * b2 + a1 * b1 + a2 * b0 + kap * (a3 * b3)) (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  funext i
  simp only [Qv]
  linear_combination ((a1 * b3 + a2 * b2 + a3 * b1) + (a2 * b3 + a3 * b2) * v i
    + a3 * b3 * v i ^ 2) * hk i

theorem tau_Qv (v : V4) (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0)
    (a0 a1 a2 a3 : ℂ) : tau (Qv v a0 a1 a2 a3) = 4 * a0 := by
  simp only [tau, ip, t3] at h1 h2 h3
  simp only [tau, Qv]
  linear_combination a1 * h1 + a2 * h2 + a3 * h3

theorem ip_Qv (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ) :
    ip (Qv v a0 a1 a2 a3) (Qv v b0 b1 b2 b3) =
      4 * (a0 * b0 + kap * (a1 * b3 + a2 * b2 + a3 * b1)) := by
  have e : ip (Qv v a0 a1 a2 a3) (Qv v b0 b1 b2 b3) =
      tau (fun i => Qv v a0 a1 a2 a3 i * Qv v b0 b1 b2 b3 i : V4) := by
    simp only [ip, tau]
  rw [e, Qv_mul v kap hk, tau_Qv v h1 h2 h3]

def Lv (v : V4) : V4 →ₗ[ℂ] V4 where
  toFun a := Qv v (a 0) (a 1) (a 2) (a 3)
  map_add' a b := by
    funext i
    simp only [Qv, Pi.add_apply]
    ring
  map_smul' c a := by
    funext i
    simp only [Qv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem Lv_apply (v a : V4) : Lv v a = Qv v (a 0) (a 1) (a 2) (a 3) := rfl

theorem Qv_inj (v : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0)
    (h2 : ip v v = 0) (h3 : t3 v v v = 0) (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ)
    (h : Qv v a0 a1 a2 a3 = Qv v b0 b1 b2 b3) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have e0 : ip (Qv v a0 a1 a2 a3) (Qv v 1 0 0 0) = ip (Qv v b0 b1 b2 b3) (Qv v 1 0 0 0) := by
    rw [h]
  have e1 : ip (Qv v a0 a1 a2 a3) (Qv v 0 0 0 1) = ip (Qv v b0 b1 b2 b3) (Qv v 0 0 0 1) := by
    rw [h]
  have e2 : ip (Qv v a0 a1 a2 a3) (Qv v 0 0 1 0) = ip (Qv v b0 b1 b2 b3) (Qv v 0 0 1 0) := by
    rw [h]
  have e3 : ip (Qv v a0 a1 a2 a3) (Qv v 0 1 0 0) = ip (Qv v b0 b1 b2 b3) (Qv v 0 1 0 0) := by
    rw [h]
  rw [ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3] at e0 e1 e2 e3
  refine ⟨by linear_combination (1 / 4 : ℂ) * e0, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * e1
  · apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * e2
  · apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * e3

theorem Qv_exists (v : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : V4) :
    ∃ a0 a1 a2 a3 : ℂ, x = Qv v a0 a1 a2 a3 := by
  have hinj : Function.Injective (Lv v) := by
    intro a b hab
    rw [Lv_apply, Lv_apply] at hab
    obtain ⟨q0, q1, q2, q3⟩ := Qv_inj v kap hkap hk h1 h2 h3 _ _ _ _ _ _ _ _ hab
    funext i
    fin_cases i
    · exact q0
    · exact q1
    · exact q2
    · exact q3
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.mp hinj) x
  exact ⟨a 0, a 1, a 2, a 3, ha.symm⟩

theorem Qv_V (v : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : V4) (hx : tau x = 0) :
    ∃ p q r : ℂ, x = Qv v 0 p q r := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := Qv_exists v kap hkap hk h1 h2 h3 x
  rw [tau_Qv v h1 h2 h3] at hx
  have h0 : a0 = 0 := by linear_combination (1 / 4 : ℂ) * hx
  subst h0
  exact ⟨a1, a2, a3, rfl⟩

theorem vperp_coords (v : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : V4) (hx : tau x = 0)
    (hi : ip x x = 0) (ht : t3 v v x = 0) : ∃ p r : ℂ, x = Qv v 0 p 0 r ∧ p * r = 0 := by
  obtain ⟨p, q, r, rfl⟩ := Qv_V v kap hkap hk h1 h2 h3 x hx
  have hvv : (fun i => v i * v i : V4) = Qv v 0 0 1 0 := by
    funext i
    simp only [Qv]
    ring
  rw [t3_ip_l, hvv, ip_Qv v kap hk h1 h2 h3] at ht
  have hq : q = 0 := by
    have h : kap * q = 0 := by linear_combination (1 / 4 : ℂ) * ht
    exact (mul_eq_zero.mp h).resolve_left hkap
  subst hq
  rw [ip_Qv v kap hk h1 h2 h3] at hi
  have hpr : p * r = 0 := by
    have h : kap * (p * r) = 0 := by linear_combination (1 / 8 : ℂ) * hi
    exact (mul_eq_zero.mp h).resolve_left hkap
  exact ⟨p, r, rfl, hpr⟩

theorem vperp1_coords (v : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : V4) (hx : tau x = 0)
    (hi : ip v x = 0) : ∃ p q : ℂ, x = Qv v 0 p q 0 := by
  obtain ⟨p, q, r, rfl⟩ := Qv_V v kap hkap hk h1 h2 h3 x hx
  have hv' : v = Qv v 0 1 0 0 := by
    funext i
    simp only [Qv]
    ring
  have hi' : ip (Qv v 0 1 0 0) (Qv v 0 p q r) = 0 := by
    rw [← hv']
    exact hi
  rw [ip_Qv v kap hk h1 h2 h3] at hi'
  have hr : r = 0 := by
    have h : kap * r = 0 := by linear_combination (1 / 4 : ℂ) * hi'
    exact (mul_eq_zero.mp h).resolve_left hkap
  subst hr
  exact ⟨p, q, rfl⟩

theorem br_13 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (P1 R1 P2 R2 P3 R3 P4 R4 : ℂ) :
    br (Qv v 0 P1 0 R1) (Qv v 0 P2 0 R2) (Qv v 0 P3 0 R3) (Qv v 0 P4 0 R4) =
      -24 * kap * (P1 * P2 * P3 * P4) - 24 * kap ^ 3 * (R1 * R2 * R3 * R4)
      + 8 * kap ^ 2 * (P1 * P2 * R3 * R4 + P1 * P3 * R2 * R4 + P1 * P4 * R2 * R3
        + P2 * P3 * R1 * R4 + P2 * P4 * R1 * R3 + P3 * P4 * R1 * R2) := by
  simp only [br]
  rw [t4_ip, Qv_mul v kap hk, Qv_mul v kap hk]
  simp only [ip_Qv v kap hk h1 h2 h3]
  ring

theorem t3_Qv2 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (P1 k1 P2 k2 P3 k3 : ℂ) :
    t3 (Qv v 0 P1 k1 0) (Qv v 0 P2 k2 0) (Qv v 0 P3 k3 0) =
      4 * kap * (P1 * P2 * k3 + P1 * k2 * P3 + k1 * P2 * P3) := by
  rw [t3_ip_l, Qv_mul v kap hk, ip_Qv v kap hk h1 h2 h3]
  ring

theorem sw02_1 : sw02 1 = 1 := by decide

theorem sw02_2 : sw02 2 = 0 := by decide

theorem S8a (K : Submodule ℂ M45) (hK : SLev K)
    (hd : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2)
    (Yu : M45) (hYu : Yu ∈ K) (hu0 : rs Yu ≠ 0) (huu : ip (rs Yu) (rs Yu) = 0)
    (v : V4) (hv : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (hform : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), ∃ x : Fin 5 → ℂ,
      Z = outer v x)
    (σ : Equiv.Perm (Fin 5))
    (c3 : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 3) = 0)
    (c4 : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), col Z (σ 4) = 0)
    (s1 : t3 v v (rs Yu) = 0) (s2 : t3 v v (phi (σ 3) Yu) = 0)
    (s3 : t3 v v (phi (σ 4) Yu) = 0) :
    ∃ pu : ℂ, pu ≠ 0 ∧ (∀ i, rs Yu i = pu * v i) ∧
      ∀ P0 P1 P2 : ℂ, ∃ R ∈ K, (∀ i, R (i, σ 0) = P0 * v i) ∧ (∀ i, R (i, σ 1) = P1 * v i) ∧
        (∀ i, R (i, σ 2) = P2 * v i) ∧ (∀ i, R (i, σ 3) = 0) ∧ (∀ i, R (i, σ 4) = 0) := by
  have hNs := SLev_N K hK
  have hrsN := rs_N K
  have hut : tau (rs Yu) = 0 := tau_rs K hK Yu hYu
  obtain ⟨pu, ru, hucoord, hpur⟩ := vperp_coords v kap hkap hk hv1 hv2 hv3 (rs Yu) hut huu s1
  have hu_i : ∀ i, rs Yu i = pu * v i + ru * v i ^ 3 := by
    intro i
    have h := congrFun hucoord i
    simp only [Qv] at h
    linear_combination h
  obtain ⟨W01, hW01N, a0, a1, a2, a3, a4⟩ := S8_elem _ hNs hrsN hd v hv hform σ c3 c4
  obtain ⟨W21, hW21N, b0, b1, b2, b3, b4⟩ := S8_elem _ hNs hrsN hd v hv hform (σ * sw02)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_3]
      exact c3 Z hZ)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_4]
      exact c4 Z hZ)
  rw [Equiv.Perm.mul_apply, sw02_0] at b0
  rw [Equiv.Perm.mul_apply, sw02_1] at b1
  rw [Equiv.Perm.mul_apply, sw02_2] at b2
  rw [Equiv.Perm.mul_apply, sw02_3] at b3
  rw [Equiv.Perm.mul_apply, sw02_4] at b4
  have hW01K : W01 ∈ K := (Submodule.mem_inf.mp hW01N).1
  have hW21K : W21 ∈ K := (Submodule.mem_inf.mp hW21N).1
  have wa0 : ∀ i, W01 (i, σ 0) = v i := fun i => congrFun a0 i
  have wa1 : ∀ i, W01 (i, σ 1) = -1 * v i := fun i => congrFun a1 i
  have wa2 : ∀ i, W01 (i, σ 2) = 0 := fun i => congrFun a2 i
  have wa3 : ∀ i, W01 (i, σ 3) = 0 := fun i => congrFun a3 i
  have wa4 : ∀ i, W01 (i, σ 4) = 0 := fun i => congrFun a4 i
  have wb2 : ∀ i, W21 (i, σ 2) = v i := fun i => congrFun b0 i
  have wb1 : ∀ i, W21 (i, σ 1) = -1 * v i := fun i => congrFun b1 i
  have wb0 : ∀ i, W21 (i, σ 0) = 0 := fun i => congrFun b2 i
  have wb3 : ∀ i, W21 (i, σ 3) = 0 := fun i => congrFun b3 i
  have wb4 : ∀ i, W21 (i, σ 4) = 0 := fun i => congrFun b4 i
  have hne0 : col W01 (σ 0) ≠ 0 := by
    rw [a0]
    exact hv
  have hne1 : col W01 (σ 1) ≠ 0 := by
    rw [a1]
    intro h
    exact hv ((smul_eq_zero.mp h).resolve_left (by norm_num))
  have hne2 : col W21 (σ 2) ≠ 0 := by
    rw [b0]
    exact hv
  obtain ⟨be0, hbe0⟩ := Biii K hK Yu hYu huu W01 hW01N (σ 0) hne0
  obtain ⟨be1', hbe1⟩ := Biii K hK Yu hYu huu W01 hW01N (σ 1) hne1
  obtain ⟨be2, hbe2⟩ := Biii K hK Yu hYu huu W21 hW21N (σ 2) hne2
  rw [a0] at hbe0
  rw [a1] at hbe1
  rw [b0] at hbe2
  obtain ⟨be1, hb1d⟩ : ∃ be1 : ℂ, be1 = -be1' := ⟨_, rfl⟩
  have f0 : ∀ i, 2 * Yu (i, σ 0) - rs Yu i = be0 * v i := fun i => congrFun hbe0 i
  have f1 : ∀ i, 2 * Yu (i, σ 1) - rs Yu i = be1 * v i := by
    intro i
    have h : 2 * Yu (i, σ 1) - rs Yu i = be1' * (-1 * v i) := congrFun hbe1 i
    rw [hb1d]
    linear_combination h
  have f2 : ∀ i, 2 * Yu (i, σ 2) - rs Yu i = be2 * v i := fun i => congrFun hbe2 i
  have hb3i : ip (phi (σ 3) Yu) (phi (σ 3) Yu) = 0 := by
    rw [ip_phi K hK Yu Yu hYu hYu (σ 3)]
    exact huu
  have hb4i : ip (phi (σ 4) Yu) (phi (σ 4) Yu) = 0 := by
    rw [ip_phi K hK Yu Yu hYu hYu (σ 4)]
    exact huu
  obtain ⟨pi3, rho3, hb3, hpr3⟩ := vperp_coords v kap hkap hk hv1 hv2 hv3 (phi (σ 3) Yu)
    (tau_phi K hK Yu hYu (σ 3)) hb3i s2
  obtain ⟨pi4, rho4, hb4, hpr4⟩ := vperp_coords v kap hkap hk hv1 hv2 hv3 (phi (σ 4) Yu)
    (tau_phi K hK Yu hYu (σ 4)) hb4i s3
  have f3 : ∀ i, 2 * Yu (i, σ 3) - rs Yu i = pi3 * v i + rho3 * v i ^ 3 := by
    intro i
    have h := congrFun hb3 i
    rw [phi_apply] at h
    simp only [Qv] at h
    linear_combination h
  have f4 : ∀ i, 2 * Yu (i, σ 4) - rs Yu i = pi4 * v i + rho4 * v i ^ 3 := by
    intro i
    have h := congrFun hb4 i
    rw [phi_apply] at h
    simp only [Qv] at h
    linear_combination h
  have hsumphi : ∀ i, (be0 + be1 + be2 + pi3 + pi4) * v i + (rho3 + rho4) * v i ^ 3 =
      -3 * pu * v i + -3 * ru * v i ^ 3 := by
    intro i
    have h := congrFun (sum_cols_perm σ Yu) i
    simp only [Pi.add_apply, col] at h
    linear_combination 2 * h - 3 * hu_i i - f0 i - f1 i - f2 i - f3 i - f4 i
  have hsumco : be0 + be1 + be2 + pi3 + pi4 = -3 * pu ∧ rho3 + rho4 = -3 * ru := by
    have e : Qv v 0 (be0 + be1 + be2 + pi3 + pi4) 0 (rho3 + rho4) =
        Qv v 0 (-3 * pu) 0 (-3 * ru) := by
      funext i
      simp only [Qv]
      linear_combination hsumphi i
    obtain ⟨_, q1, _, q3⟩ := Qv_inj v kap hkap hk hv1 hv2 hv3 _ _ _ _ _ _ _ _ e
    exact ⟨q1, q3⟩
  have hmemY : ∀ t x0 x2 : ℂ, t • Yu + x0 • W01 + x2 • W21 ∈ K := fun t x0 x2 =>
    K.add_mem (K.add_mem (K.smul_mem t hYu) (K.smul_mem x0 hW01K)) (K.smul_mem x2 hW21K)
  have hcol : ∀ t x0 x2 : ℂ,
      col (cperm σ (t • Yu + x0 • W01 + x2 • W21)) 0 =
        Qv v 0 (t * (be0 + pu) / 2 + x0) 0 (t * ru / 2) ∧
      col (cperm σ (t • Yu + x0 • W01 + x2 • W21)) 1 =
        Qv v 0 (t * (be1 + pu) / 2 - x0 - x2) 0 (t * ru / 2) ∧
      col (cperm σ (t • Yu + x0 • W01 + x2 • W21)) 2 =
        Qv v 0 (t * (be2 + pu) / 2 + x2) 0 (t * ru / 2) ∧
      col (cperm σ (t • Yu + x0 • W01 + x2 • W21)) 3 =
        Qv v 0 (t * (pi3 + pu) / 2) 0 (t * (rho3 + ru) / 2) ∧
      col (cperm σ (t • Yu + x0 • W01 + x2 • W21)) 4 =
        Qv v 0 (t * (pi4 + pu) / 2) 0 (t * (rho4 + ru) / 2) := by
    intro t x0 x2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa0, wb0]
      linear_combination (t / 2) * f0 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa1, wb1]
      linear_combination (t / 2) * f1 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa2, wb2]
      linear_combination (t / 2) * f2 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa3, wb3]
      linear_combination (t / 2) * f3 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa4, wb4]
      linear_combination (t / 2) * f4 i + (t / 2) * hu_i i
  have hKσ := SLev_perm σ K hK
  have G4 : ∀ t x0 x2 : ℂ,
      br (Qv v 0 (t * (be0 + pu) / 2 + x0) 0 (t * ru / 2))
        (Qv v 0 (t * (be1 + pu) / 2 - x0 - x2) 0 (t * ru / 2))
        (Qv v 0 (t * (be2 + pu) / 2 + x2) 0 (t * ru / 2))
        (Qv v 0 (t * (pi3 + pu) / 2) 0 (t * (rho3 + ru) / 2)) = 0 := by
    intro t x0 x2
    have h := (C34 _ hKσ _ (Submodule.mem_map_of_mem (hmemY t x0 x2)) 4).2.2
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at h
    obtain ⟨e0, e1, e2, e3, e4⟩ := hcol t x0 x2
    rw [e0, e1, e2, e3] at h
    exact h
  have G3 : ∀ t x0 x2 : ℂ,
      br (Qv v 0 (t * (be0 + pu) / 2 + x0) 0 (t * ru / 2))
        (Qv v 0 (t * (be1 + pu) / 2 - x0 - x2) 0 (t * ru / 2))
        (Qv v 0 (t * (be2 + pu) / 2 + x2) 0 (t * ru / 2))
        (Qv v 0 (t * (pi4 + pu) / 2) 0 (t * (rho4 + ru) / 2)) = 0 := by
    intro t x0 x2
    have h := (C34 _ hKσ _ (Submodule.mem_map_of_mem (hmemY t x0 x2)) 3).2.2
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at h
    obtain ⟨e0, e1, e2, e3, e4⟩ := hcol t x0 x2
    rw [e0, e1, e2, e4] at h
    exact h
  have hp3 : pi3 = -pu := by
    have g1 := G4 1 1 (-2)
    have gm1 := G4 (-1) 1 (-2)
    have g2 := G4 2 1 (-2)
    have gm2 := G4 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap * (pi3 + pu) = 0 := by
      linear_combination (1 / 288 : ℂ) * (8 * (g1 - gm1) - (g2 - gm2))
    have h' := (mul_eq_zero.mp h).resolve_left hkap
    linear_combination h'
  have hp4 : pi4 = -pu := by
    have g1 := G3 1 1 (-2)
    have gm1 := G3 (-1) 1 (-2)
    have g2 := G3 2 1 (-2)
    have gm2 := G3 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap * (pi4 + pu) = 0 := by
      linear_combination (1 / 288 : ℂ) * (8 * (g1 - gm1) - (g2 - gm2))
    have h' := (mul_eq_zero.mp h).resolve_left hkap
    linear_combination h'
  subst hp3
  subst hp4
  have hr3 : ru * (rho3 + ru) = 0 := by
    have g1 := G4 1 1 (-2)
    have gm1 := G4 (-1) 1 (-2)
    have g2 := G4 2 1 (-2)
    have gm2 := G4 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap ^ 2 * (ru * (rho3 + ru)) = 0 := by
      linear_combination (-1 / 144 : ℂ) * (16 * (g1 + gm1) - (g2 + gm2))
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hkap)
  have hr4 : ru * (rho4 + ru) = 0 := by
    have g1 := G3 1 1 (-2)
    have gm1 := G3 (-1) 1 (-2)
    have g2 := G3 2 1 (-2)
    have gm2 := G3 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap ^ 2 * (ru * (rho4 + ru)) = 0 := by
      linear_combination (-1 / 144 : ℂ) * (16 * (g1 + gm1) - (g2 + gm2))
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hkap)
  by_cases hru : ru = 0
  · subst hru
    have hpu : pu ≠ 0 := by
      intro h
      apply hu0
      funext i
      rw [hu_i i, h]
      simp
    have h3r : rho3 = 0 := (mul_eq_zero.mp hpr3).resolve_left (neg_ne_zero.mpr hpu)
    have h4r : rho4 = 0 := (mul_eq_zero.mp hpr4).resolve_left (neg_ne_zero.mpr hpu)
    subst h3r
    subst h4r
    have hbsum : be0 + be1 + be2 = -pu := by linear_combination hsumco.1
    have hinv := mul_inv_cancel₀ hpu
    refine ⟨pu, hpu, fun i => by rw [hu_i i]; ring, ?_⟩
    intro P0 P1 P2
    refine ⟨((P0 + P1 + P2) * pu⁻¹) • Yu
      + (P0 - (P0 + P1 + P2) * pu⁻¹ * ((be0 + pu) / 2)) • W01
      + (P2 - (P0 + P1 + P2) * pu⁻¹ * ((be2 + pu) / 2)) • W21, hmemY _ _ _, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa0, wb0]
      linear_combination ((P0 + P1 + P2) * pu⁻¹ / 2) * f0 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa1, wb1]
      linear_combination ((P0 + P1 + P2) * pu⁻¹ / 2) * f1 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
        + ((P0 + P1 + P2) * pu⁻¹ / 2 * v i) * hbsum + ((P0 + P1 + P2) * v i) * hinv
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa2, wb2]
      linear_combination ((P0 + P1 + P2) * pu⁻¹ / 2) * f2 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa3, wb3]
      linear_combination ((P0 + P1 + P2) * pu⁻¹ / 2) * f3 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa4, wb4]
      linear_combination ((P0 + P1 + P2) * pu⁻¹ / 2) * f4 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
  · exfalso
    have h3' : rho3 + ru = 0 := (mul_eq_zero.mp hr3).resolve_left hru
    have h4' : rho4 + ru = 0 := (mul_eq_zero.mp hr4).resolve_left hru
    apply hru
    linear_combination hsumco.2 - h3' - h4'

theorem S8b (K : Submodule ℂ M45) (hK : SLev K) (hq : Module.finrank ℂ (K.map rs) = 2)
    (Yu : M45) (hYu : Yu ∈ K) (huperp : ∀ s ∈ K.map rs, ip (rs Yu) s = 0)
    (v : V4) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap) (σ : Equiv.Perm (Fin 5))
    (pu : ℂ) (hpu : pu ≠ 0) (hu_i : ∀ i, rs Yu i = pu * v i)
    (hrel : ∀ P0 P1 P2 : ℂ, ∃ R ∈ K, (∀ i, R (i, σ 0) = P0 * v i) ∧
      (∀ i, R (i, σ 1) = P1 * v i) ∧ (∀ i, R (i, σ 2) = P2 * v i) ∧
      (∀ i, R (i, σ 3) = 0) ∧ (∀ i, R (i, σ 4) = 0)) : False := by
  have hv0 : v 0 ≠ 0 := by
    intro h0
    apply hkap
    rw [← hk 0, h0]
    norm_num
  have hu0 : rs Yu ≠ 0 := by
    intro h
    have e := hu_i 0
    rw [h] at e
    exact (mul_ne_zero hpu hv0) e.symm
  obtain ⟨Y4, hY4, hY4n⟩ : ∃ Y4 ∈ K, ∀ c : ℂ, rs Y4 ≠ c • rs Yu := by
    by_contra hcon
    have hall : ∀ Y ∈ K, ∃ c : ℂ, rs Y = c • rs Yu := by
      intro Y hY
      by_contra h
      exact hcon ⟨Y, hY, fun c hc => h ⟨c, hc⟩⟩
    have hle : K.map rs ≤ Submodule.span ℂ {rs Yu} := by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨c, hc⟩ := hall Y hY
      rw [hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0] at h1
    omega
  have hvs : ip v (rs Y4) = 0 := by
    have h := huperp _ (Submodule.mem_map_of_mem hY4)
    simp only [ip] at h ⊢
    have h' : pu * (v 0 * rs Y4 0 + v 1 * rs Y4 1 + v 2 * rs Y4 2 + v 3 * rs Y4 3) = 0 := by
      linear_combination h - rs Y4 0 * hu_i 0 - rs Y4 1 * hu_i 1 - rs Y4 2 * hu_i 2
        - rs Y4 3 * hu_i 3
    exact (mul_eq_zero.mp h').resolve_left hpu
  obtain ⟨Ra, hRa, ra0, ra1, ra2, ra3, ra4⟩ := hrel 1 (-1) 0
  obtain ⟨Rb, hRb, rb0, rb1, rb2, rb3, rb4⟩ := hrel 0 (-1) 1
  obtain ⟨Rc, hRc, rc0, rc1, rc2, rc3, rc4⟩ := hrel 1 0 0
  have hrsRa : rs Ra = 0 := by
    rw [← sum_cols_perm σ Ra]
    funext i
    simp only [Pi.add_apply, col, ra0, ra1, ra2, ra3, ra4, Pi.zero_apply]
    ring
  have hrsRb : rs Rb = 0 := by
    rw [← sum_cols_perm σ Rb]
    funext i
    simp only [Pi.add_apply, col, rb0, rb1, rb2, rb3, rb4, Pi.zero_apply]
    ring
  have hrsRc : ∀ i, rs Rc i = v i := by
    intro i
    have h := congrFun (sum_cols_perm σ Rc) i
    simp only [Pi.add_apply, col, rc0, rc1, rc2, rc3, rc4] at h
    linear_combination (-1 : ℂ) * h
  have hvsU := hvs
  simp only [ip] at hvsU
  have o0 : ip v (col Y4 (σ 0)) = 0 := by
    have e := ip_col_phi K hK Ra Y4 hRa hY4 hrsRa (σ 0)
    simp only [ip, col, phi_apply, ra0] at e
    simp only [ip, col]
    linear_combination (1 / 2 : ℂ) * e + (1 / 2 : ℂ) * hvsU
  have o1 : ip v (col Y4 (σ 1)) = 0 := by
    have e := ip_col_phi K hK Ra Y4 hRa hY4 hrsRa (σ 1)
    simp only [ip, col, phi_apply, ra1] at e
    simp only [ip, col]
    linear_combination (-1 / 2 : ℂ) * e + (1 / 2 : ℂ) * hvsU
  have o2 : ip v (col Y4 (σ 2)) = 0 := by
    have e := ip_col_phi K hK Rb Y4 hRb hY4 hrsRb (σ 2)
    simp only [ip, col, phi_apply, rb2] at e
    simp only [ip, col]
    linear_combination (1 / 2 : ℂ) * e + (1 / 2 : ℂ) * hvsU
  have o3 : ip v (col Y4 (σ 3)) = 0 := by
    have e := C2pol K hK Y4 Rc hY4 hRc (σ 3)
    simp only [ip, col, rc3, hrsRc] at e
    simp only [ip, col]
    linear_combination (-1 : ℂ) * e
  have o4 : ip v (col Y4 (σ 4)) = 0 := by
    have e := C2pol K hK Y4 Rc hY4 hRc (σ 4)
    simp only [ip, col, rc4, hrsRc] at e
    simp only [ip, col]
    linear_combination (-1 : ℂ) * e
  obtain ⟨pe0, ke0, he0⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 0))
    (C1 K hK Y4 hY4 (σ 0)) o0
  obtain ⟨pe1, ke1, he1⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 1))
    (C1 K hK Y4 hY4 (σ 1)) o1
  obtain ⟨pe2, ke2, he2⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 2))
    (C1 K hK Y4 hY4 (σ 2)) o2
  obtain ⟨pe3, ke3, he3⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 3))
    (C1 K hK Y4 hY4 (σ 3)) o3
  obtain ⟨pe4, ke4, he4⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 4))
    (C1 K hK Y4 hY4 (σ 4)) o4
  obtain ⟨ps, qs, hs4⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (rs Y4)
    (tau_rs K hK Y4 hY4) hvs
  have y40 : ∀ i, Y4 (i, σ 0) = pe0 * v i + ke0 * v i ^ 2 := by
    intro i
    have h := congrFun he0 i
    simp only [Qv, col] at h
    linear_combination h
  have y41 : ∀ i, Y4 (i, σ 1) = pe1 * v i + ke1 * v i ^ 2 := by
    intro i
    have h := congrFun he1 i
    simp only [Qv, col] at h
    linear_combination h
  have y42 : ∀ i, Y4 (i, σ 2) = pe2 * v i + ke2 * v i ^ 2 := by
    intro i
    have h := congrFun he2 i
    simp only [Qv, col] at h
    linear_combination h
  have y43 : ∀ i, Y4 (i, σ 3) = pe3 * v i + ke3 * v i ^ 2 := by
    intro i
    have h := congrFun he3 i
    simp only [Qv, col] at h
    linear_combination h
  have y44 : ∀ i, Y4 (i, σ 4) = pe4 * v i + ke4 * v i ^ 2 := by
    intro i
    have h := congrFun he4 i
    simp only [Qv, col] at h
    linear_combination h
  have hksum : ke0 + ke1 + ke2 + ke3 + ke4 = qs := by
    have e : Qv v 0 (pe0 + pe1 + pe2 + pe3 + pe4) (ke0 + ke1 + ke2 + ke3 + ke4) 0 =
        Qv v 0 ps qs 0 := by
      rw [← hs4, ← sum_cols_perm σ Y4, he0, he1, he2, he3, he4]
      funext i
      simp only [Qv, Pi.add_apply]
      ring
    exact (Qv_inj v kap hkap hk hv1 hv2 hv3 _ _ _ _ _ _ _ _ e).2.2.1
  have hqs : qs ≠ 0 := by
    intro h
    apply hY4n (ps * pu⁻¹)
    funext i
    have e := congrFun hs4 i
    simp only [Qv] at e
    rw [e, h]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu_i i]
    have hinv := mul_inv_cancel₀ hpu
    linear_combination (-(ps * v i)) * hinv
  have hc2 : ke3 ^ 2 = qs * ke3 := by
    have e := C2 K hK Y4 hY4 (σ 3)
    rw [he3, hs4, ip_Qv v kap hk hv1 hv2 hv3, ip_Qv v kap hk hv1 hv2 hv3] at e
    apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * e
  have hKσ := SLev_perm σ K hK
  have TT : ∀ P0 P1 P2 : ℂ,
      (t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 pe3 ke3 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe3 ke3 0)
        + t3 (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe3 ke3 0) = 0) ∧
      (t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 pe4 ke4 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe4 ke4 0)
        + t3 (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe4 ke4 0) = 0) := by
    intro P0 P1 P2
    obtain ⟨R, hR, r0, r1, r2, r3, r4⟩ := hrel (P0 - pe0) (P1 - pe1) (P2 - pe2)
    have hmem : cperm σ (Y4 + R) ∈ K.map (cperm σ) :=
      Submodule.mem_map_of_mem (K.add_mem hY4 hR)
    have d0 : col (cperm σ (Y4 + R)) 0 = Qv v 0 P0 ke0 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r0]
      linear_combination y40 i
    have d1 : col (cperm σ (Y4 + R)) 1 = Qv v 0 P1 ke1 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r1]
      linear_combination y41 i
    have d2 : col (cperm σ (Y4 + R)) 2 = Qv v 0 P2 ke2 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r2]
      linear_combination y42 i
    have d3 : col (cperm σ (Y4 + R)) 3 = Qv v 0 pe3 ke3 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r3]
      linear_combination y43 i
    have d4 : col (cperm σ (Y4 + R)) 4 = Qv v 0 pe4 ke4 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r4]
      linear_combination y44 i
    have h4 := (C34 _ hKσ _ hmem 4).2.1
    have h3 := (C34 _ hKσ _ hmem 3).2.1
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2, d0, d1, d2, d3] at h4
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2, d0, d1, d2, d4] at h3
    exact ⟨h4, h3⟩
  have t000 := TT 0 0 0
  have t010 := TT 0 1 0
  have t001 := TT 0 0 1
  have t011 := TT 0 1 1
  have t100 := TT 1 0 0
  have t101 := TT 1 0 1
  have t110 := TT 1 1 0
  simp only [t3_Qv2 v kap hk hv1 hv2 hv3] at t000 t010 t001 t011 t100 t101 t110
  have e03 : ke0 + ke3 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * (t011.1 - t010.1 - t001.1 + t000.1)
  have e13 : ke1 + ke3 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * (t101.1 - t100.1 - t001.1 + t000.1)
  have e23 : ke2 + ke3 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * (t110.1 - t100.1 - t010.1 + t000.1)
  have e04 : ke0 + ke4 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (1 / 4 : ℂ) * (t011.2 - t010.2 - t001.2 + t000.2)
  have hk3 : ke3 = 0 := by
    have h : ke3 ^ 2 = 0 := by
      linear_combination (1 / 2 : ℂ) * hc2 - (ke3 / 2) * hksum + (ke3 / 2) * (e13 + e23 + e04)
    exact (pow_eq_zero_iff (by norm_num)).mp h
  apply hqs
  linear_combination (-1 : ℂ) * hksum + e13 + e23 + e04 - hk3

theorem HypS8_proof : HypS8 := by
  unfold HypS8
  intro K hK hq hd Yu hYu hu0 huperp v hv hv1 hv2 hv3 hform σ c3 c4 s1 s2 s3
  obtain ⟨k0, k1, k2, k3⟩ := pow4_iso v hv1 hv2 hv3
  have hkap : t4 v v v v / 4 ≠ 0 := by
    intro h
    apply hv
    apply iso34 v hv1 hv2 hv3
    linear_combination 4 * h
  have hk : ∀ i, v i ^ 4 = t4 v v v v / 4 := by
    intro i
    fin_cases i
    · exact k0
    · exact k1
    · exact k2
    · exact k3
  have huu : ip (rs Yu) (rs Yu) = 0 := huperp _ (Submodule.mem_map_of_mem hYu)
  obtain ⟨pu, hpu, hu_i, hrel⟩ := S8a K hK hd Yu hYu hu0 huu v hv hv1 hv2 hv3 _ hkap hk hform
    σ c3 c4 s1 s2 s3
  exact S8b K hK hq Yu hYu huperp v hv1 hv2 hv3 _ hkap hk σ pu hpu hu_i hrel


def r3 : Fin 3 → ℂ := ![Complex.I, -1, -Complex.I]

def spv (π : Equiv.Perm (Fin 3)) : V4 := ![1, r3 (π 0), r3 (π 1), r3 (π 2)]

theorem r3_pow (k : Fin 3) : r3 k ^ 4 = 1 := by
  fin_cases k
  · show Complex.I ^ 4 = 1
    linear_combination (Complex.I * Complex.I - 1) * Complex.I_mul_I
  · show (-1 : ℂ) ^ 4 = 1
    norm_num
  · show (-Complex.I) ^ 4 = 1
    linear_combination (Complex.I * Complex.I - 1) * Complex.I_mul_I

theorem r3_inj : Function.Injective r3 := by
  have h1 : Complex.I ≠ -1 := by
    intro h
    have h' := congrArg Complex.im h
    norm_num at h'
  have h2 : Complex.I ≠ -Complex.I := by
    intro h
    have h' := congrArg Complex.im h
    norm_num at h'
  have h3 : (-1 : ℂ) ≠ -Complex.I := by
    intro h
    have h' := congrArg Complex.im h
    norm_num at h'
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h.symm h1
  · rfl
  · exact absurd h h3
  · exact absurd h.symm h2
  · exact absurd h.symm h3
  · rfl

theorem r3_sums (π : Equiv.Perm (Fin 3)) :
    r3 (π 0) + r3 (π 1) + r3 (π 2) = -1 ∧
    r3 (π 0) * r3 (π 0) + r3 (π 1) * r3 (π 1) + r3 (π 2) * r3 (π 2) = -1 ∧
    r3 (π 0) * r3 (π 0) * r3 (π 0) + r3 (π 1) * r3 (π 1) * r3 (π 1)
      + r3 (π 2) * r3 (π 2) * r3 (π 2) = -1 := by
  have h1 : r3 (π 0) + r3 (π 1) + r3 (π 2) = r3 0 + r3 1 + r3 2 := by
    have h := Equiv.sum_comp π r3
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
    exact h
  have h2 : r3 (π 0) * r3 (π 0) + r3 (π 1) * r3 (π 1) + r3 (π 2) * r3 (π 2) =
      r3 0 * r3 0 + r3 1 * r3 1 + r3 2 * r3 2 := by
    have h := Equiv.sum_comp π (fun k => r3 k * r3 k)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
    exact h
  have h3 : r3 (π 0) * r3 (π 0) * r3 (π 0) + r3 (π 1) * r3 (π 1) * r3 (π 1)
      + r3 (π 2) * r3 (π 2) * r3 (π 2) =
      r3 0 * r3 0 * r3 0 + r3 1 * r3 1 * r3 1 + r3 2 * r3 2 * r3 2 := by
    have h := Equiv.sum_comp π (fun k => r3 k * r3 k * r3 k)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
    exact h
  have e0 : r3 0 = Complex.I := rfl
  have e1 : r3 1 = -1 := rfl
  have e2 : r3 2 = -Complex.I := rfl
  rw [e0, e1, e2] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h1
  · linear_combination h2 + 2 * Complex.I_mul_I
  · linear_combination h3

theorem spv_props (π : Equiv.Perm (Fin 3)) :
    tau (spv π) = 0 ∧ ip (spv π) (spv π) = 0 ∧ t3 (spv π) (spv π) (spv π) = 0 ∧
      ∀ i, spv π i ^ 4 = 1 := by
  obtain ⟨h1, h2, h3⟩ := r3_sums π
  have e0 : spv π 0 = 1 := rfl
  have e1 : spv π 1 = r3 (π 0) := rfl
  have e2 : spv π 2 = r3 (π 1) := rfl
  have e3 : spv π 3 = r3 (π 2) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [tau, e0, e1, e2, e3]
    linear_combination h1
  · simp only [ip, e0, e1, e2, e3]
    linear_combination h2
  · simp only [t3, e0, e1, e2, e3]
    linear_combination h3
  · intro i
    fin_cases i
    · show (1 : ℂ) ^ 4 = 1
      norm_num
    · exact r3_pow (π 0)
    · exact r3_pow (π 1)
    · exact r3_pow (π 2)

theorem spv_inj (π π' : Equiv.Perm (Fin 3)) (h0 : r3 (π 0) = r3 (π' 0))
    (h1 : r3 (π 1) = r3 (π' 1)) (h2 : r3 (π 2) = r3 (π' 2)) : π = π' := by
  apply Equiv.ext
  intro k
  fin_cases k
  · exact r3_inj h0
  · exact r3_inj h1
  · exact r3_inj h2

theorem chart (c : Fin 5 → V4) (hc : ∀ m, c m ≠ 0) :
    ∃ v : V4, tau v = 0 ∧ ip v v = 0 ∧ t3 v v v = 0 ∧ (∀ i, v i ^ 4 = 1) ∧
      ∀ m, ∀ k : ℂ, c m ≠ k • v := by
  by_contra hcon
  have hall : ∀ π : Equiv.Perm (Fin 3), ∃ m, ∃ k : ℂ, c m = k • spv π := by
    intro π
    by_contra h
    apply hcon
    obtain ⟨p1, p2, p3, p4⟩ := spv_props π
    exact ⟨spv π, p1, p2, p3, p4, fun m k hk => h ⟨m, k, hk⟩⟩
  choose f g hg using hall
  obtain ⟨π, π', hne, hff⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]; decide)
  have e := hg π
  rw [hff, hg π'] at e
  have q0 := congrFun e 0
  have q1 := congrFun e 1
  have q2 := congrFun e 2
  have q3 := congrFun e 3
  simp only [Pi.smul_apply, smul_eq_mul] at q0 q1 q2 q3
  have a0 : ∀ ρ : Equiv.Perm (Fin 3), spv ρ 0 = 1 := fun ρ => rfl
  have a1 : ∀ ρ : Equiv.Perm (Fin 3), spv ρ 1 = r3 (ρ 0) := fun ρ => rfl
  have a2 : ∀ ρ : Equiv.Perm (Fin 3), spv ρ 2 = r3 (ρ 1) := fun ρ => rfl
  have a3 : ∀ ρ : Equiv.Perm (Fin 3), spv ρ 3 = r3 (ρ 2) := fun ρ => rfl
  rw [a0, a0] at q0
  rw [a1, a1] at q1
  rw [a2, a2] at q2
  rw [a3, a3] at q3
  have hgg : g π' = g π := by linear_combination q0
  have hg0 : g π ≠ 0 := by
    intro h0
    apply hc (f π)
    rw [hg π, h0, zero_smul]
  apply hne
  apply spv_inj
  · apply mul_left_cancel₀ hg0
    linear_combination -q1 + r3 (π' 0) * hgg
  · apply mul_left_cancel₀ hg0
    linear_combination -q2 + r3 (π' 1) * hgg
  · apply mul_left_cancel₀ hg0
    linear_combination -q3 + r3 (π' 2) * hgg

def Uv (v : V4) (θ : ℂ) : V4 := Qv v 0 (-(θ ^ 2) / 2) θ 1

def tt (a b c : ℂ) : ℂ := 4 * (a + b + c) + a * b * c * (a * b + b * c + c * a)

def kk (x y : ℂ) : ℂ := 2 * x + 4 * y + x ^ 2 * y ^ 3 + x * y ^ 4 / 2

def cc (x : ℂ) : ℂ := 12 * x + 3 * x ^ 5

theorem iso_coords (v : V4) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (x : V4) (hx : tau x = 0) (hxx : ip x x = 0)
    (hnp : ∀ k : ℂ, x ≠ k • v) : ∃ θ ζ : ℂ, ζ ≠ 0 ∧ x = ζ • Uv v θ := by
  obtain ⟨p, q, r, rfl⟩ := Qv_V v 1 one_ne_zero hk h1 h2 h3 x hx
  rw [ip_Qv v 1 hk h1 h2 h3] at hxx
  have hr : r ≠ 0 := by
    intro hr
    rw [hr] at hxx
    have hq : q = 0 := by
      have hqq : q * q = 0 := by linear_combination (1 / 4 : ℂ) * hxx
      exact mul_self_eq_zero.mp hqq
    apply hnp p
    funext i
    simp only [Qv, Pi.smul_apply, smul_eq_mul, hr, hq]
    ring
  obtain ⟨θ, hθ⟩ : ∃ θ : ℂ, q = θ * r := ⟨q / r, (div_mul_cancel₀ q hr).symm⟩
  have hp : 2 * p + θ ^ 2 * r = 0 := by
    apply mul_left_cancel₀ hr
    linear_combination (1 / 4 : ℂ) * hxx - (q + θ * r) * hθ
  refine ⟨θ, r, hr, ?_⟩
  funext i
  simp only [Qv, Uv, Pi.smul_apply, smul_eq_mul]
  linear_combination (v i / 2) * hp + (v i ^ 2) * hθ

theorem ip_Uv (v : V4) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (θ : ℂ) : ip (Uv v θ) v = 4 := by
  have hv' : v = Qv v 0 1 0 0 := by
    funext i
    simp only [Qv]
    ring
  have e : ip (Qv v 0 (-(θ ^ 2) / 2) θ 1) (Qv v 0 1 0 0) = 4 := by
    rw [ip_Qv v 1 hk h1 h2 h3]
    ring
  rw [← hv'] at e
  exact e

theorem t3_smul3 (a b c : ℂ) (x y z : V4) : t3 (a • x) (b • y) (c • z) = a * b * c * t3 x y z := by
  simp only [t3, Pi.smul_apply, smul_eq_mul]
  ring

theorem t3_Uv (v : V4) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a b c : ℂ) : t3 (Uv v a) (Uv v b) (Uv v c) = tt a b c := by
  simp only [Uv, tt]
  rw [t3_ip_l, Qv_mul v 1 hk, ip_Qv v 1 hk h1 h2 h3]
  ring

def lamL (v : V4) : M45 →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun Z := fun m => ip (col Z m) v / 4
  map_add' Z Z' := by
    funext m
    simp only [ip, col, Pi.add_apply]
    ring
  map_smul' c Z := by
    funext m
    simp only [ip, col, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lamL_apply (v : V4) (Z : M45) (m : Fin 5) : lamL v Z m = ip (col Z m) v / 4 := rfl

theorem N_coords (N : Submodule ℂ M45) (z : M45)
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : ℂ, col Z m = c • col z m)
    (v : V4) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0)
    (θ ζ : Fin 5 → ℂ) (hz : ∀ m, col z m = ζ m • Uv v (θ m)) (Z : M45) (hZ : Z ∈ N)
    (m : Fin 5) : col Z m = lamL v Z m • Uv v (θ m) := by
  obtain ⟨c, hc⟩ := hmax Z hZ m
  have e : lamL v Z m = c * ζ m := by
    rw [lamL_apply, hc, hz m]
    have h4 := ip_Uv v hk h1 h2 h3 (θ m)
    simp only [ip, Pi.smul_apply, smul_eq_mul] at h4 ⊢
    linear_combination (c * ζ m / 4) * h4
  rw [e, hc, hz m, smul_smul]

def Chart (N : Submodule ℂ M45) (v : V4) (θ : Fin 5 → ℂ) : Prop :=
  (∀ i, v i ^ 4 = 1) ∧ tau v = 0 ∧ ip v v = 0 ∧ t3 v v v = 0 ∧
    ∀ Z ∈ N, ∀ m, col Z m = lamL v Z m • Uv v (θ m)

theorem Uv_sum (v : V4) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (L0 L1 L2 L3 L4 T0 T1 T2 T3 T4 : ℂ)
    (e : L0 • Uv v T0 + L1 • Uv v T1 + L2 • Uv v T2 + L3 • Uv v T3 + L4 • Uv v T4 = 0) :
    (L0 + L1 + L2 + L3 + L4 = 0) ∧ (L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4 = 0) ∧
      (L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2 = 0) := by
  have e' : Qv v 0 (-(L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2) / 2)
      (L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4) (L0 + L1 + L2 + L3 + L4) =
      Qv v 0 0 0 0 := by
    funext i
    have ei := congrFun e i
    simp only [Uv, Qv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ei ⊢
    linear_combination ei
  obtain ⟨_, q1, q2, q3⟩ := Qv_inj v 1 one_ne_zero hk h1 h2 h3 _ _ _ _ _ _ _ _ e'
  exact ⟨q3, q2, by linear_combination (-2 : ℂ) * q1⟩

theorem Lam_rel (N : Submodule ℂ M45) (hrs : ∀ Z ∈ N, rs Z = 0) (v : V4) (θ : Fin 5 → ℂ)
    (hC : Chart N v θ) (Z : M45) (hZ : Z ∈ N) :
    (∑ n, lamL v Z n = 0) ∧ (∑ n, lamL v Z n * θ n = 0) ∧
      (∑ n, lamL v Z n * θ n ^ 2 = 0) := by
  obtain ⟨hk, h1, h2, h3, hcol⟩ := hC
  have e : col Z 0 + col Z 1 + col Z 2 + col Z 3 + col Z 4 = rs Z :=
    sum_cols_perm (Equiv.refl (Fin 5)) Z
  rw [hrs Z hZ, hcol Z hZ 0, hcol Z hZ 1, hcol Z hZ 2, hcol Z hZ 3, hcol Z hZ 4] at e
  rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five]
  exact Uv_sum v hk h1 h2 h3 _ _ _ _ _ _ _ _ _ _ e

theorem star_cert (L0 L1 L2 L3 L4 T0 T1 T2 T3 T4 : ℂ)
    (r0 : L0 + L1 + L2 + L3 + L4 = 0)
    (r1 : L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4 = 0)
    (r2 : L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2 = 0)
    (c0 : L1 * L2 * L3 * tt T1 T2 T3 + L1 * L2 * L4 * tt T1 T2 T4 + L1 * L3 * L4 * tt T1 T3 T4
      + L2 * L3 * L4 * tt T2 T3 T4 = 0)
    (c1 : L0 * L2 * L3 * tt T0 T2 T3 + L0 * L2 * L4 * tt T0 T2 T4 + L0 * L3 * L4 * tt T0 T3 T4
      + L2 * L3 * L4 * tt T2 T3 T4 = 0)
    (c2 : L0 * L1 * L3 * tt T0 T1 T3 + L0 * L1 * L4 * tt T0 T1 T4 + L0 * L3 * L4 * tt T0 T3 T4
      + L1 * L3 * L4 * tt T1 T3 T4 = 0)
    (c3 : L0 * L1 * L2 * tt T0 T1 T2 + L0 * L1 * L4 * tt T0 T1 T4 + L0 * L2 * L4 * tt T0 T2 T4
      + L1 * L2 * L4 * tt T1 T2 T4 = 0)
    (c4 : L0 * L1 * L2 * tt T0 T1 T2 + L0 * L1 * L3 * tt T0 T1 T3 + L0 * L2 * L3 * tt T0 T2 T3
      + L1 * L2 * L3 * tt T1 T2 T3 = 0) :
    L0 * (cc T0 * L0 ^ 2 - (L0 ^ 2 * kk T0 T0 + L1 ^ 2 * kk T0 T1 + L2 ^ 2 * kk T0 T2
      + L3 ^ 2 * kk T0 T3 + L4 ^ 2 * kk T0 T4)) = 0 := by
  simp only [tt] at c0 c1 c2 c3 c4
  simp only [cc, kk]
  linear_combination (1 / 2 : ℂ) * (c0 + c1 + c2 + c3 + c4) - c0
    - L0 * ((2 * T0 * (L0 + L1 + L2 + L3 + L4)
        + 4 * (L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4) - 8 * L0 * T0) * r0
      + (T0 ^ 2 * (L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2)
        - L0 * T0 ^ 4 - 4 * L0) * r1
      + (T0 * (L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2) / 2
        - 2 * L0 * T0 ^ 3) * r2)

theorem Lam_star (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (v : V4)
    (θ : Fin 5 → ℂ) (hC : Chart N v θ) (Z : M45) (hZ : Z ∈ N) (σ : Equiv.Perm (Fin 5)) :
    lamL v Z (σ 0) * (cc (θ (σ 0)) * lamL v Z (σ 0) ^ 2 -
      (lamL v Z (σ 0) ^ 2 * kk (θ (σ 0)) (θ (σ 0)) + lamL v Z (σ 1) ^ 2 * kk (θ (σ 0)) (θ (σ 1))
        + lamL v Z (σ 2) ^ 2 * kk (θ (σ 0)) (θ (σ 2))
        + lamL v Z (σ 3) ^ 2 * kk (θ (σ 0)) (θ (σ 3))
        + lamL v Z (σ 4) ^ 2 * kk (θ (σ 0)) (θ (σ 4)))) = 0 := by
  obtain ⟨hk, h1, h2, h3, hcol⟩ := hC
  have e := sum_cols_perm σ Z
  rw [hrs Z hZ, hcol Z hZ (σ 0), hcol Z hZ (σ 1), hcol Z hZ (σ 2), hcol Z hZ (σ 3),
    hcol Z hZ (σ 4)] at e
  obtain ⟨r0, r1, r2⟩ := Uv_sum v hk h1 h2 h3 _ _ _ _ _ _ _ _ _ _ e
  have hS := SLev_perm σ N hN
  have hY : cperm σ Z ∈ N.map (cperm σ) := Submodule.mem_map_of_mem hZ
  have c0 := (C34 _ hS _ hY 0).2.1
  have c1 := (C34 _ hS _ hY 1).2.1
  have c2 := (C34 _ hS _ hY 2).2.1
  have c3 := (C34 _ hS _ hY 3).2.1
  have c4 := (C34 _ hS _ hY 4).2.1
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at c0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at c1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at c2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at c3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at c4
  have hc : ∀ k, col (cperm σ Z) k = lamL v Z (σ k) • Uv v (θ (σ k)) := fun k =>
    hcol Z hZ (σ k)
  simp only [hc, t3_smul3, t3_Uv v hk h1 h2 h3] at c0 c1 c2 c3 c4
  exact star_cert _ _ _ _ _ _ _ _ _ _ r0 r1 r2 (by linear_combination c0)
    (by linear_combination c1) (by linear_combination c2) (by linear_combination c3)
    (by linear_combination c4)

def Fq (θ : Fin 5 → ℂ) (m : Fin 5) (lam : Fin 5 → ℂ) : ℂ :=
  cc (θ m) * lam m ^ 2 - ∑ n, lam n ^ 2 * kk (θ m) (θ n)

theorem sum5 (σ : Equiv.Perm (Fin 5)) (f : Fin 5 → ℂ) :
    f (σ 0) + f (σ 1) + f (σ 2) + f (σ 3) + f (σ 4) = ∑ n, f n := by
  rw [← Equiv.sum_comp σ f, Fin.sum_univ_five]

theorem Fq_sigma (θ lam : Fin 5 → ℂ) (m : Fin 5) (σ : Equiv.Perm (Fin 5)) :
    Fq θ m lam = cc (θ m) * lam m ^ 2 - (lam (σ 0) ^ 2 * kk (θ m) (θ (σ 0))
      + lam (σ 1) ^ 2 * kk (θ m) (θ (σ 1)) + lam (σ 2) ^ 2 * kk (θ m) (θ (σ 2))
      + lam (σ 3) ^ 2 * kk (θ m) (θ (σ 3)) + lam (σ 4) ^ 2 * kk (θ m) (θ (σ 4))) := by
  have e : lam (σ 0) ^ 2 * kk (θ m) (θ (σ 0))
      + lam (σ 1) ^ 2 * kk (θ m) (θ (σ 1)) + lam (σ 2) ^ 2 * kk (θ m) (θ (σ 2))
      + lam (σ 3) ^ 2 * kk (θ m) (θ (σ 3)) + lam (σ 4) ^ 2 * kk (θ m) (θ (σ 4)) =
      ∑ n, lam n ^ 2 * kk (θ m) (θ n) := sum5 σ (fun n => lam n ^ 2 * kk (θ m) (θ n))
  rw [e]
  rfl

theorem Lam_F (N : Submodule ℂ M45) (hN : SLev N) (hrs : ∀ Z ∈ N, rs Z = 0) (v : V4)
    (θ : Fin 5 → ℂ) (hC : Chart N v θ) (z : M45) (hz : z ∈ N) (hz0 : ∀ m, lamL v z m ≠ 0)
    (Z : M45) (hZ : Z ∈ N) (m : Fin 5) : Fq θ m (lamL v Z) = 0 := by
  have star : ∀ Y ∈ N, lamL v Y m * Fq θ m (lamL v Y) = 0 := by
    intro Y hY
    have h := Lam_star N hN hrs v θ hC Y hY (Equiv.swap 0 m)
    rw [Fq_sigma θ (lamL v Y) m (Equiv.swap 0 m)]
    rw [Equiv.swap_apply_left] at h ⊢
    exact h
  by_cases h0 : lamL v Z m = 0
  · have e1 := star (Z + z) (N.add_mem hZ hz)
    have e2 := star (Z - z) (N.sub_mem hZ hz)
    have e3 := star z hz
    rw [map_add] at e1
    rw [map_sub] at e2
    have n1 : (lamL v Z + lamL v z) m ≠ 0 := by
      rw [Pi.add_apply, h0, zero_add]
      exact hz0 m
    have n2 : (lamL v Z - lamL v z) m ≠ 0 := by
      rw [Pi.sub_apply, h0, zero_sub]
      exact neg_ne_zero.mpr (hz0 m)
    have f1 := (mul_eq_zero.mp e1).resolve_left n1
    have f2 := (mul_eq_zero.mp e2).resolve_left n2
    have f3 := (mul_eq_zero.mp e3).resolve_left (hz0 m)
    have par : Fq θ m (lamL v Z + lamL v z) + Fq θ m (lamL v Z - lamL v z) =
        2 * Fq θ m (lamL v Z) + 2 * Fq θ m (lamL v z) := by
      simp only [Fq, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_five]
      ring
    linear_combination (1 / 2 : ℂ) * (f1 + f2) - f3 - (1 / 2 : ℂ) * par
  · exact (mul_eq_zero.mp (star Z hZ)).resolve_left h0

def AlgCore : Prop := ∀ (θ : Fin 5 → ℂ) (Lam : Submodule ℂ (Fin 5 → ℂ)),
    2 ≤ Module.finrank ℂ Lam →
    (∀ lam ∈ Lam, (∑ n, lam n = 0) ∧ (∑ n, lam n * θ n = 0) ∧ (∑ n, lam n * θ n ^ 2 = 0)) →
    (∀ lam ∈ Lam, ∀ m, Fq θ m lam = 0) →
    (∃ ζ ∈ Lam, ∀ m, ζ m ≠ 0) →
    (∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ θ a ≠ θ b ∧ θ a ≠ θ c ∧ θ b ≠ θ c) → False

theorem HypS6_of (HA : AlgCore) : HypS6 := by
  unfold HypS6
  intro N hN hrs hd z hz hmax a b c hab hac hbc hind hact
  obtain ⟨v, h1, h2, h3, hk, hnp⟩ := chart (fun m => col z m) hact
  have hzc : ∀ m, ∃ θ ζ : ℂ, ζ ≠ 0 ∧ col z m = ζ • Uv v θ := fun m =>
    iso_coords v hk h1 h2 h3 (col z m) (C1 N hN z hz m) (Niso N hN hrs z z hz hz m) (hnp m)
  choose θ ζ hζ hzθ using hzc
  have hcol : ∀ Z ∈ N, ∀ m, col Z m = lamL v Z m • Uv v (θ m) := fun Z hZ m =>
    N_coords N z hmax v hk h1 h2 h3 θ ζ hzθ Z hZ m
  have hC : Chart N v θ := ⟨hk, h1, h2, h3, hcol⟩
  have hz0 : ∀ m, lamL v z m ≠ 0 := by
    intro m h0
    apply hact m
    rw [hcol z hz m, h0, zero_smul]
  have nab : θ a ≠ θ b := by
    intro h
    have e : ζ b • col z a + (-ζ a) • col z b + (0 : ℂ) • col z c = 0 := by
      rw [hzθ a, hzθ b, h]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    exact hζ b (hind _ _ _ e).1
  have nac : θ a ≠ θ c := by
    intro h
    have e : ζ c • col z a + (0 : ℂ) • col z b + (-ζ a) • col z c = 0 := by
      rw [hzθ a, hzθ c, h]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    exact hζ c (hind _ _ _ e).1
  have nbc : θ b ≠ θ c := by
    intro h
    have e : (0 : ℂ) • col z a + ζ c • col z b + (-ζ b) • col z c = 0 := by
      rw [hzθ b, hzθ c, h]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    exact hζ c (hind _ _ _ e).2.1
  have rn := rank_nullity N (lamL v)
  have hker : (N ⊓ LinearMap.ker (lamL v) : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    rintro Z ⟨hZ, hZk⟩
    rw [Submodule.mem_bot]
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hZk
    funext ⟨i, m⟩
    have h := congrFun (hcol Z hZ m) i
    rw [hZk, Pi.zero_apply, zero_smul] at h
    exact h
  rw [hker, finrank_bot] at rn
  apply HA θ (N.map (lamL v))
  · omega
  · rintro lam ⟨Z, hZ, rfl⟩
    exact Lam_rel N hrs v θ hC Z hZ
  · rintro lam ⟨Z, hZ, rfl⟩ m
    exact Lam_F N hN hrs v θ hC z hz hz0 Z hZ m
  · exact ⟨lamL v z, Submodule.mem_map_of_mem hz, hz0⟩
  · exact ⟨a, b, c, hab, hac, hbc, nab, nac, nbc⟩

def Good5 (T L : Fin 5 → ℂ) : Prop :=
  (L 0 + L 1 + L 2 + L 3 + L 4 = 0) ∧
  (L 0 * T 0 + L 1 * T 1 + L 2 * T 2 + L 3 * T 3 + L 4 * T 4 = 0) ∧
  (L 0 * T 0 ^ 2 + L 1 * T 1 ^ 2 + L 2 * T 2 ^ 2 + L 3 * T 3 ^ 2 + L 4 * T 4 ^ 2 = 0) ∧
  ∀ j, cc (T j) * L j ^ 2 - (L 0 ^ 2 * kk (T j) (T 0) + L 1 ^ 2 * kk (T j) (T 1)
    + L 2 ^ 2 * kk (T j) (T 2) + L 3 ^ 2 * kk (T j) (T 3) + L 4 ^ 2 * kk (T j) (T 4)) = 0

theorem singA (Z0 Z1 Z2 Z3 Z4 T0 T1 T2 T3 T4 : ℂ) (r0 : Z0 + Z1 + Z2 + Z3 + Z4 = 0)
    (r1 : Z0 * T0 + Z1 * T1 + Z2 * T2 + Z3 * T3 + Z4 * T4 = 0)
    (r2 : Z0 * T0 ^ 2 + Z1 * T1 ^ 2 + Z2 * T2 ^ 2 + Z3 * T3 ^ 2 + Z4 * T4 ^ 2 = 0)
    (hZ : Z0 ≠ 0) (h1 : T0 ≠ T1) (h2 : T0 ≠ T2) (h3 : T3 = T1 ∨ T3 = T2)
    (h4 : T4 = T1 ∨ T4 = T2) : False := by
  have p3 : (T3 - T1) * (T3 - T2) = 0 := by
    rcases h3 with h | h
    · rw [h]
      ring
    · rw [h]
      ring
  have p4 : (T4 - T1) * (T4 - T2) = 0 := by
    rcases h4 with h | h
    · rw [h]
      ring
    · rw [h]
      ring
  have key : Z0 * ((T0 - T1) * (T0 - T2)) = 0 := by
    linear_combination r2 - (T1 + T2) * r1 + T1 * T2 * r0 - Z3 * p3 - Z4 * p4
  rcases mul_eq_zero.mp key with h | h
  · exact hZ h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact h1 (sub_eq_zero.mp h')
    · exact h2 (sub_eq_zero.mp h')

theorem pairB (La Lb Lm Lx Ly Ta Tb Tm Tx Ty : ℂ) (r0 : La + Lb + Lm + Lx + Ly = 0)
    (r1 : La * Ta + Lb * Tb + Lm * Tm + Lx * Tx + Ly * Ty = 0)
    (r2 : La * Ta ^ 2 + Lb * Tb ^ 2 + Lm * Tm ^ 2 + Lx * Tx ^ 2 + Ly * Ty ^ 2 = 0)
    (hLm : Lm = 0) (hne : ¬(La = 0 ∧ Lb = 0 ∧ Lx = 0 ∧ Ly = 0)) (eab : Ta = Tb)
    (d1 : Tb ≠ Tx) (d2 : Tb ≠ Ty) (d3 : Tx ≠ Ty) (d4 : Tm ≠ Tx) (d5 : Tm ≠ Ty)
    (Fm : cc Tm * Lm ^ 2 - (La ^ 2 * kk Tm Ta + Lb ^ 2 * kk Tm Tb + Lm ^ 2 * kk Tm Tm
      + Lx ^ 2 * kk Tm Tx + Ly ^ 2 * kk Tm Ty) = 0)
    (Fx : cc Tx * Lx ^ 2 - (La ^ 2 * kk Tx Ta + Lb ^ 2 * kk Tx Tb + Lm ^ 2 * kk Tx Tm
      + Lx ^ 2 * kk Tx Tx + Ly ^ 2 * kk Tx Ty) = 0)
    (Fy : cc Ty * Ly ^ 2 - (La ^ 2 * kk Ty Ta + Lb ^ 2 * kk Ty Tb + Lm ^ 2 * kk Ty Tm
      + Lx ^ 2 * kk Ty Tx + Ly ^ 2 * kk Ty Ty) = 0) : False := by
  have kx : Lx * ((Tx - Tb) * (Tx - Ty)) = 0 := by
    linear_combination r2 - (Tb + Ty) * r1 + Tb * Ty * r0 - La * (Ta - Ty) * eab
      - (Tm - Tb) * (Tm - Ty) * hLm
  have ky : Ly * ((Ty - Tb) * (Ty - Tx)) = 0 := by
    linear_combination r2 - (Tb + Tx) * r1 + Tb * Tx * r0 - La * (Ta - Tx) * eab
      - (Tm - Tb) * (Tm - Tx) * hLm
  have hx : Lx = 0 := by
    rcases mul_eq_zero.mp kx with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d1 (sub_eq_zero.mp h').symm).elim
      · exact (d3 (sub_eq_zero.mp h')).elim
  have hy : Ly = 0 := by
    rcases mul_eq_zero.mp ky with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d2 (sub_eq_zero.mp h').symm).elim
      · exact (d3 (sub_eq_zero.mp h').symm).elim
  have hb : Lb = -La := by linear_combination r0 - hLm - hx - hy
  have hLa : La ≠ 0 := by
    intro h
    exact hne ⟨h, by rw [hb, h, neg_zero], hx, hy⟩
  have gm : La ^ 2 * kk Tm Tb = 0 := by
    rw [hLm, hx, hy, hb, eab] at Fm
    linear_combination (-1 / 2 : ℂ) * Fm
  have gx : La ^ 2 * kk Tx Tb = 0 := by
    rw [hLm, hx, hy, hb, eab] at Fx
    linear_combination (-1 / 2 : ℂ) * Fx
  have gy : La ^ 2 * kk Ty Tb = 0 := by
    rw [hLm, hx, hy, hb, eab] at Fy
    linear_combination (-1 / 2 : ℂ) * Fy
  have km := (mul_eq_zero.mp gm).resolve_left (pow_ne_zero 2 hLa)
  have kx' := (mul_eq_zero.mp gx).resolve_left (pow_ne_zero 2 hLa)
  have ky' := (mul_eq_zero.mp gy).resolve_left (pow_ne_zero 2 hLa)
  simp only [kk] at km kx' ky'
  have hA : Tb * (Tb * Tb) * ((Tm - Tx) * (Tm - Ty) * (Tx - Ty)) = 0 := by
    linear_combination (Tx - Ty) * km - (Tm - Ty) * kx' + (Tm - Tx) * ky'
  rcases mul_eq_zero.mp hA with h | h
  · have hs : Tb = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact mul_self_eq_zero.mp h'
    rw [hs] at km kx'
    have h2 : (Tm - Tx) * 2 = 0 := by linear_combination km - kx'
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact d4 (sub_eq_zero.mp h')
    · exact two_ne_zero h'
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact d4 (sub_eq_zero.mp h'')
      · exact d5 (sub_eq_zero.mp h'')
    · exact d3 (sub_eq_zero.mp h')

theorem inj5 (T : Fin 5 → ℂ) (h01 : T 0 ≠ T 1) (h02 : T 0 ≠ T 2) (h03 : T 0 ≠ T 3)
    (h04 : T 0 ≠ T 4) (h12 : T 1 ≠ T 2) (h13 : T 1 ≠ T 3) (h14 : T 1 ≠ T 4) (h23 : T 2 ≠ T 3)
    (h24 : T 2 ≠ T 4) (h34 : T 3 ≠ T 4) : Function.Injective T := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | exact absurd h h01
    | exact absurd h.symm h01
    | exact absurd h h02
    | exact absurd h.symm h02
    | exact absurd h h03
    | exact absurd h.symm h03
    | exact absurd h h04
    | exact absurd h.symm h04
    | exact absurd h h12
    | exact absurd h.symm h12
    | exact absurd h h13
    | exact absurd h.symm h13
    | exact absurd h h14
    | exact absurd h.symm h14
    | exact absurd h h23
    | exact absurd h.symm h23
    | exact absurd h h24
    | exact absurd h.symm h24
    | exact absurd h h34
    | exact absurd h.symm h34

theorem Lam_peel (Lam : Submodule ℂ (Fin 5 → ℂ)) (hfr : 2 ≤ Module.finrank ℂ Lam) (m : Fin 5) :
    ∃ lam ∈ Lam, lam m = 0 ∧ lam ≠ 0 := by
  have rn := rank_nullity Lam (LinearMap.proj m : (Fin 5 → ℂ) →ₗ[ℂ] ℂ)
  have h1 : Module.finrank ℂ (Lam.map (LinearMap.proj m : (Fin 5 → ℂ) →ₗ[ℂ] ℂ)) ≤ 1 := by
    have h := Submodule.finrank_le (Lam.map (LinearMap.proj m : (Fin 5 → ℂ) →ₗ[ℂ] ℂ))
    rw [Module.finrank_self] at h
    exact h
  have hne : (Lam ⊓ LinearMap.ker (LinearMap.proj m : (Fin 5 → ℂ) →ₗ[ℂ] ℂ) :
      Submodule ℂ (Fin 5 → ℂ)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rn
    omega
  obtain ⟨lam, hlam, hne0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hlam
  exact ⟨lam, hw.1, LinearMap.mem_ker.mp hw.2, hne0⟩

theorem core5 (T : Fin 5 → ℂ) (P : (Fin 5 → ℂ) → Prop)
    (hgood : ∀ L, P L → Good5 T L)
    (hpeel : ∀ k : Fin 5, ∃ L, P L ∧ L k = 0 ∧ ¬ (∀ j, L j = 0))
    (hζ : ∃ L, P L ∧ ∀ j, L j ≠ 0)
    (h01 : T 0 ≠ T 1) (h02 : T 0 ≠ T 2) (h12 : T 1 ≠ T 2)
    (hC : Function.Injective T → False) : False := by
  obtain ⟨Z, hPZ, hZ⟩ := hζ
  obtain ⟨z0, z1, z2, _⟩ := hgood Z hPZ
  have tA0 : (T 3 = T 1 ∨ T 3 = T 2) → (T 4 = T 1 ∨ T 4 = T 2) → False := fun h3 h4 =>
    singA (Z 0) (Z 1) (Z 2) (Z 3) (Z 4) (T 0) (T 1) (T 2) (T 3) (T 4) z0 z1 z2 (hZ 0) h01 h02
      h3 h4
  have tA1 : (T 3 = T 0 ∨ T 3 = T 2) → (T 4 = T 0 ∨ T 4 = T 2) → False := fun h3 h4 =>
    singA (Z 1) (Z 0) (Z 2) (Z 3) (Z 4) (T 1) (T 0) (T 2) (T 3) (T 4)
      (by linear_combination z0) (by linear_combination z1) (by linear_combination z2) (hZ 1)
      h01.symm h12 h3 h4
  have tA2 : (T 3 = T 0 ∨ T 3 = T 1) → (T 4 = T 0 ∨ T 4 = T 1) → False := fun h3 h4 =>
    singA (Z 2) (Z 0) (Z 1) (Z 3) (Z 4) (T 2) (T 0) (T 1) (T 3) (T 4)
      (by linear_combination z0) (by linear_combination z1) (by linear_combination z2) (hZ 2)
      h02.symm h12.symm h3 h4
  obtain ⟨A, hPA, hA0, hAnz⟩ := hpeel 0
  obtain ⟨a0, a1, a2, aF⟩ := hgood A hPA
  obtain ⟨B, hPB, hB1, hBnz⟩ := hpeel 1
  obtain ⟨b0, b1, b2, bF⟩ := hgood B hPB
  by_cases m3 : T 3 = T 0 ∨ T 3 = T 1 ∨ T 3 = T 2
  · by_cases m4 : T 4 = T 0 ∨ T 4 = T 1 ∨ T 4 = T 2
    · rcases m3 with e3 | e3 | e3 <;> rcases m4 with e4 | e4 | e4
      · exact tA1 (Or.inl e3) (Or.inl e4)
      · exact tA2 (Or.inl e3) (Or.inr e4)
      · exact tA1 (Or.inl e3) (Or.inr e4)
      · exact tA2 (Or.inr e3) (Or.inl e4)
      · exact tA0 (Or.inl e3) (Or.inl e4)
      · exact tA0 (Or.inl e3) (Or.inr e4)
      · exact tA1 (Or.inr e3) (Or.inl e4)
      · exact tA0 (Or.inr e3) (Or.inl e4)
      · exact tA0 (Or.inr e3) (Or.inr e4)
    · have n40 : T 4 ≠ T 0 := fun h => m4 (Or.inl h)
      have n41 : T 4 ≠ T 1 := fun h => m4 (Or.inr (Or.inl h))
      have n42 : T 4 ≠ T 2 := fun h => m4 (Or.inr (Or.inr h))
      rcases m3 with e3 | e3 | e3
      · exact pairB (B 3) (B 0) (B 1) (B 2) (B 4) (T 3) (T 0) (T 1) (T 2) (T 4)
          (by linear_combination b0) (by linear_combination b1) (by linear_combination b2) hB1
          (fun h => hBnz (fin5 (fun j => B j = 0) h.2.1 hB1 h.2.2.1 h.1 h.2.2.2))
          e3 h02 n40.symm n42.symm h12 n41.symm
          (by linear_combination bF 1) (by linear_combination bF 2) (by linear_combination bF 4)
      · exact pairB (A 3) (A 1) (A 0) (A 2) (A 4) (T 3) (T 1) (T 0) (T 2) (T 4)
          (by linear_combination a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.1 h.2.2.1 h.1 h.2.2.2))
          e3 h12 n41.symm n42.symm h02 n40.symm
          (by linear_combination aF 0) (by linear_combination aF 2) (by linear_combination aF 4)
      · exact pairB (A 3) (A 2) (A 0) (A 1) (A 4) (T 3) (T 2) (T 0) (T 1) (T 4)
          (by linear_combination a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.2.1 h.2.1 h.1 h.2.2.2))
          e3 h12.symm n42.symm n41.symm h01 n40.symm
          (by linear_combination aF 0) (by linear_combination aF 1) (by linear_combination aF 4)
  · have n30 : T 3 ≠ T 0 := fun h => m3 (Or.inl h)
    have n31 : T 3 ≠ T 1 := fun h => m3 (Or.inr (Or.inl h))
    have n32 : T 3 ≠ T 2 := fun h => m3 (Or.inr (Or.inr h))
    by_cases m4 : T 4 = T 0 ∨ T 4 = T 1 ∨ T 4 = T 2
    · rcases m4 with e4 | e4 | e4
      · exact pairB (B 4) (B 0) (B 1) (B 2) (B 3) (T 4) (T 0) (T 1) (T 2) (T 3)
          (by linear_combination b0) (by linear_combination b1) (by linear_combination b2) hB1
          (fun h => hBnz (fin5 (fun j => B j = 0) h.2.1 hB1 h.2.2.1 h.2.2.2 h.1))
          e4 h02 n30.symm n32.symm h12 n31.symm
          (by linear_combination bF 1) (by linear_combination bF 2) (by linear_combination bF 3)
      · exact pairB (A 4) (A 1) (A 0) (A 2) (A 3) (T 4) (T 1) (T 0) (T 2) (T 3)
          (by linear_combination a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.1 h.2.2.1 h.2.2.2 h.1))
          e4 h12 n31.symm n32.symm h02 n30.symm
          (by linear_combination aF 0) (by linear_combination aF 2) (by linear_combination aF 3)
      · exact pairB (A 4) (A 2) (A 0) (A 1) (A 3) (T 4) (T 2) (T 0) (T 1) (T 3)
          (by linear_combination a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.2.1 h.2.1 h.2.2.2 h.1))
          e4 h12.symm n32.symm n31.symm h01 n30.symm
          (by linear_combination aF 0) (by linear_combination aF 1) (by linear_combination aF 3)
    · have n40 : T 4 ≠ T 0 := fun h => m4 (Or.inl h)
      have n41 : T 4 ≠ T 1 := fun h => m4 (Or.inr (Or.inl h))
      have n42 : T 4 ≠ T 2 := fun h => m4 (Or.inr (Or.inr h))
      by_cases e34 : T 3 = T 4
      · exact pairB (A 3) (A 4) (A 0) (A 1) (A 2) (T 3) (T 4) (T 0) (T 1) (T 2)
          (by linear_combination a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.2.1 h.2.2.2 h.1 h.2.1))
          e34 n41 n42 h12 h01 h02
          (by linear_combination aF 0) (by linear_combination aF 1) (by linear_combination aF 2)
      · exact hC (inj5 T h01 h02 n30.symm n40.symm h12 n31.symm n41.symm n32.symm n42.symm e34)

def HypS6C : Prop := ∀ (θ : Fin 5 → ℂ) (Lam : Submodule ℂ (Fin 5 → ℂ)),
    Function.Injective θ → 2 ≤ Module.finrank ℂ Lam →
    (∀ lam ∈ Lam, (∑ n, lam n = 0) ∧ (∑ n, lam n * θ n = 0) ∧ (∑ n, lam n * θ n ^ 2 = 0)) →
    (∀ lam ∈ Lam, ∀ m, Fq θ m lam = 0) → False

theorem AlgCore_of (HC : HypS6C) : AlgCore := by
  unfold AlgCore
  intro θ Lam hfr hrel hF hζ habc
  obtain ⟨a, b, c, hab, hac, hbc, tab, tac, tbc⟩ := habc
  obtain ⟨σ, s0, s1, s2⟩ := perm_three a b c hab hac hbc
  apply core5 (fun k => θ (σ k)) (fun L => ∃ lam ∈ Lam, L = fun k => lam (σ k))
  · rintro L ⟨lam, hlam, rfl⟩
    obtain ⟨R0, R1, R2⟩ := hrel lam hlam
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (sum5 σ lam).trans R0
    · exact (sum5 σ (fun n => lam n * θ n)).trans R1
    · exact (sum5 σ (fun n => lam n * θ n ^ 2)).trans R2
    · intro j
      have h := hF lam hlam (σ j)
      rw [Fq_sigma θ lam (σ j) σ] at h
      exact h
  · intro k
    obtain ⟨lam, hlam, hk0, hne⟩ := Lam_peel Lam hfr (σ k)
    refine ⟨fun j => lam (σ j), ⟨lam, hlam, rfl⟩, hk0, ?_⟩
    intro hall
    apply hne
    funext n
    have h2 : lam (σ (σ.symm n)) = 0 := hall (σ.symm n)
    rw [Equiv.apply_symm_apply] at h2
    exact h2
  · obtain ⟨ζ, hζL, hζ0⟩ := hζ
    exact ⟨fun j => ζ (σ j), ⟨ζ, hζL, rfl⟩, fun j => hζ0 (σ j)⟩
  · show θ (σ 0) ≠ θ (σ 1)
    rw [s0, s1]
    exact tab
  · show θ (σ 0) ≠ θ (σ 2)
    rw [s0, s2]
    exact tac
  · show θ (σ 1) ≠ θ (σ 2)
    rw [s1, s2]
    exact tbc
  · intro hT
    have hθ : Function.Injective θ := by
      intro n n' h
      have h' : (fun k => θ (σ k)) (σ.symm n) = (fun k => θ (σ k)) (σ.symm n') := by
        show θ (σ (σ.symm n)) = θ (σ (σ.symm n'))
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact h
      exact σ.symm.injective (hT h')
    exact HC θ Lam hθ hfr hrel hF

def mom3 (θ : Fin 5 → ℂ) : (Fin 5 → ℂ) →ₗ[ℂ] ℂ where
  toFun lam := lam 0 * θ 0 ^ 3 + lam 1 * θ 1 ^ 3 + lam 2 * θ 2 ^ 3 + lam 3 * θ 3 ^ 3
    + lam 4 * θ 4 ^ 3
  map_add' a b := by
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mom3_apply (θ lam : Fin 5 → ℂ) : mom3 θ lam = lam 0 * θ 0 ^ 3 + lam 1 * θ 1 ^ 3
    + lam 2 * θ 2 ^ 3 + lam 3 * θ 3 ^ 3 + lam 4 * θ 4 ^ 3 := rfl

theorem Lam_ker (Lam : Submodule ℂ (Fin 5 → ℂ)) (hfr : 2 ≤ Module.finrank ℂ Lam)
    (f : (Fin 5 → ℂ) →ₗ[ℂ] ℂ) : ∃ lam ∈ Lam, f lam = 0 ∧ lam ≠ 0 := by
  have rn := rank_nullity Lam f
  have h1 : Module.finrank ℂ (Lam.map f) ≤ 1 := by
    have h := Submodule.finrank_le (Lam.map f)
    rw [Module.finrank_self] at h
    exact h
  have hne : (Lam ⊓ LinearMap.ker f : Submodule ℂ (Fin 5 → ℂ)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rn
    omega
  obtain ⟨lam, hlam, hne0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hlam
  exact ⟨lam, hw.1, LinearMap.mem_ker.mp hw.2, hne0⟩

theorem vdm3 (x0 x1 x2 t0 t1 t2 : ℂ) (h0 : x0 + x1 + x2 = 0)
    (h1 : x0 * t0 + x1 * t1 + x2 * t2 = 0)
    (h2 : x0 * t0 ^ 2 + x1 * t1 ^ 2 + x2 * t2 ^ 2 = 0)
    (d01 : t0 ≠ t1) (d02 : t0 ≠ t2) (d12 : t1 ≠ t2) : x0 = 0 ∧ x1 = 0 ∧ x2 = 0 := by
  have k0 : x0 * ((t0 - t1) * (t0 - t2)) = 0 := by
    linear_combination h2 - (t1 + t2) * h1 + t1 * t2 * h0
  have k1 : x1 * ((t1 - t0) * (t1 - t2)) = 0 := by
    linear_combination h2 - (t0 + t2) * h1 + t0 * t2 * h0
  have k2 : x2 * ((t2 - t0) * (t2 - t1)) = 0 := by
    linear_combination h2 - (t0 + t1) * h1 + t0 * t1 * h0
  refine ⟨?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp k0 with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d01 (sub_eq_zero.mp h')).elim
      · exact (d02 (sub_eq_zero.mp h')).elim
  · rcases mul_eq_zero.mp k1 with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d01 (sub_eq_zero.mp h').symm).elim
      · exact (d12 (sub_eq_zero.mp h')).elim
  · rcases mul_eq_zero.mp k2 with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d02 (sub_eq_zero.mp h').symm).elim
      · exact (d12 (sub_eq_zero.mp h').symm).elim

theorem roots5 (T : Fin 5 → ℂ) (hT : Function.Injective T) (a0 a1 a2 a3 a4 : ℂ)
    (h : ∀ i, a0 + a1 * T i + a2 * T i ^ 2 + a3 * T i ^ 3 + a4 * T i ^ 4 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 := by
  have hz : (![a0, a1, a2, a3, a4] : Fin 5 → ℂ) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hT)
    funext i
    have hi := h i
    show ∑ j : Fin 5, Matrix.vandermonde T i j * (![a0, a1, a2, a3, a4] : Fin 5 → ℂ) j = 0
    rw [Fin.sum_univ_five]
    show T i ^ 0 * a0 + T i ^ 1 * a1 + T i ^ 2 * a2 + T i ^ 3 * a3 + T i ^ 4 * a4 = 0
    linear_combination hi
  exact ⟨congrFun hz 0, congrFun hz 1, congrFun hz 2, congrFun hz 3, congrFun hz 4⟩

theorem moments5 (T : Fin 5 → ℂ) (hT : Function.Injective T) (X : Fin 5 → ℂ)
    (h : ∀ j : Fin 5, ∑ i, X i * T i ^ (j : ℕ) = 0) : X = 0 := by
  apply Matrix.eq_zero_of_vecMul_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hT)
  funext j
  show ∑ i : Fin 5, X i * Matrix.vandermonde T i j = 0
  exact h j

def pw (T W : Fin 5 → ℂ) (j : ℕ) : ℂ :=
  W 0 ^ 2 * T 0 ^ j + W 1 ^ 2 * T 1 ^ j + W 2 ^ 2 * T 2 ^ j + W 3 ^ 2 * T 3 ^ j
    + W 4 ^ 2 * T 4 ^ j

theorem caseC_alg (T W : Fin 5 → ℂ) (hT : Function.Injective T)
    (E1 : ∀ m, Fq T m W = 0) (E3 : ∀ m, Fq T m (fun n => T n * W n) = 0)
    (E12 : ∀ m, Fq T m (W + fun n => T n * W n) = 0) : ∀ n, W n = 0 := by
  have hD : ∀ m, 4 * pw T W 2 + (pw T W 5 / 2 - 2 * pw T W 1) * T m
      + (pw T W 4 / 2 - 2 * pw T W 0) * T m ^ 2 + (-pw T W 3) * T m ^ 3 + 0 * T m ^ 4 = 0 := by
    intro m
    have e1 := E1 m
    have e3 := E3 m
    have e12 := E12 m
    simp only [Fq, Fin.sum_univ_five, Pi.add_apply, cc, kk] at e1 e3 e12
    simp only [pw]
    linear_combination T m * e1 - (1 / 2 : ℂ) * (e12 - e1 - e3)
  have hE : ∀ m, 4 * pw T W 3 + (2 * pw T W 2 + pw T W 6 / 2) * T m
      + (pw T W 5 - 4 * pw T W 1) * T m ^ 2 + (-2 * pw T W 0 - pw T W 4 / 2) * T m ^ 3
      + (-pw T W 3) * T m ^ 4 = 0 := by
    intro m
    have e1 := E1 m
    have e3 := E3 m
    simp only [Fq, Fin.sum_univ_five, cc, kk] at e1 e3
    simp only [pw]
    linear_combination T m ^ 2 * e1 - e3
  obtain ⟨d0, d1, d2, d3, _⟩ := roots5 T hT _ _ _ _ _ hD
  obtain ⟨_, _, _, g3, _⟩ := roots5 T hT _ _ _ _ _ hE
  have q0 : pw T W 0 = 0 := by linear_combination (-1 / 4 : ℂ) * (d2 + g3)
  have q4 : pw T W 4 = 0 := by linear_combination d2 - g3
  have q2 : pw T W 2 = 0 := by linear_combination (1 / 4 : ℂ) * d0
  have q3 : pw T W 3 = 0 := by linear_combination (-1 : ℂ) * d3
  have q1 : pw T W 1 = 0 := by
    have s0 := E1 0
    have s1 := E1 1
    have s2 := E1 2
    have s3 := E1 3
    have s4 := E1 4
    simp only [Fq, Fin.sum_univ_five, cc, kk] at s0 s1 s2 s3 s4
    simp only [pw] at q0 q3 q4 d1 ⊢
    linear_combination (1 / 4 : ℂ) * (s0 + s1 + s2 + s3 + s4) - (3 / 2 : ℂ) * d1
      + ((T 0 + T 1 + T 2 + T 3 + T 4) / 2) * q0
      + ((T 0 ^ 2 + T 1 ^ 2 + T 2 ^ 2 + T 3 ^ 2 + T 4 ^ 2) / 4) * q3
      + ((T 0 + T 1 + T 2 + T 3 + T 4) / 8) * q4
  simp only [pw] at q0 q1 q2 q3 q4
  have m0 : ∑ i : Fin 5, (W i * W i) * T i ^ 0 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination q0
  have m1 : ∑ i : Fin 5, (W i * W i) * T i ^ 1 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination q1
  have m2 : ∑ i : Fin 5, (W i * W i) * T i ^ 2 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination q2
  have m3 : ∑ i : Fin 5, (W i * W i) * T i ^ 3 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination q3
  have m4 : ∑ i : Fin 5, (W i * W i) * T i ^ 4 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination q4
  have hX : (fun n => W n * W n) = 0 :=
    moments5 T hT (fun n => W n * W n)
      (fin5 (fun j : Fin 5 => ∑ i, (fun n => W n * W n) i * T i ^ (j : ℕ) = 0) m0 m1 m2 m3 m4)
  intro n
  have h2 : W n * W n = 0 := congrFun hX n
  exact mul_self_eq_zero.mp h2

theorem HypS6C_proof : HypS6C := by
  unfold HypS6C
  intro θ Lam hθ hfr hrel hF
  have d01 : θ 0 ≠ θ 1 := hθ.ne (by decide)
  have d02 : θ 0 ≠ θ 2 := hθ.ne (by decide)
  have d12 : θ 1 ≠ θ 2 := hθ.ne (by decide)
  obtain ⟨w, hwL, hw3, hwne⟩ := Lam_ker Lam hfr (mom3 θ)
  rw [mom3_apply] at hw3
  obtain ⟨w0, w1, w2⟩ := hrel w hwL
  rw [Fin.sum_univ_five] at w0 w1 w2
  obtain ⟨A, hAL, hA3, hAne⟩ := Lam_peel Lam hfr 3
  obtain ⟨a0, a1, a2⟩ := hrel A hAL
  rw [Fin.sum_univ_five] at a0 a1 a2
  have hA4 : A 4 ≠ 0 := by
    intro h
    obtain ⟨e0, e1, e2⟩ := vdm3 (A 0) (A 1) (A 2) (θ 0) (θ 1) (θ 2)
      (by linear_combination a0 - hA3 - h)
      (by linear_combination a1 - θ 3 * hA3 - θ 4 * h)
      (by linear_combination a2 - θ 3 ^ 2 * hA3 - θ 4 ^ 2 * h) d01 d02 d12
    apply hAne
    funext n
    exact fin5 (fun n => A n = 0) e0 e1 e2 hA3 h n
  obtain ⟨B, hBL, hB4, hBne⟩ := Lam_peel Lam hfr 4
  obtain ⟨b0, b1, b2⟩ := hrel B hBL
  rw [Fin.sum_univ_five] at b0 b1 b2
  have hB3 : B 3 ≠ 0 := by
    intro h
    obtain ⟨e0, e1, e2⟩ := vdm3 (B 0) (B 1) (B 2) (θ 0) (θ 1) (θ 2)
      (by linear_combination b0 - h - hB4)
      (by linear_combination b1 - θ 3 * h - θ 4 * hB4)
      (by linear_combination b2 - θ 3 ^ 2 * h - θ 4 ^ 2 * hB4) d01 d02 d12
    apply hBne
    funext n
    exact fin5 (fun n => B n = 0) e0 e1 e2 h hB4 n
  obtain ⟨cA, hcA⟩ : ∃ c : ℂ, c * A 4 = θ 4 * w 4 :=
    ⟨θ 4 * w 4 / A 4, div_mul_cancel₀ _ hA4⟩
  obtain ⟨cB, hcB⟩ : ∃ c : ℂ, c * B 3 = θ 3 * w 3 :=
    ⟨θ 3 * w 3 / B 3, div_mul_cancel₀ _ hB3⟩
  have hxL : cA • A + cB • B ∈ Lam := Lam.add_mem (Lam.smul_mem cA hAL) (Lam.smul_mem cB hBL)
  obtain ⟨x0, x1, x2⟩ := hrel _ hxL
  rw [Fin.sum_univ_five] at x0 x1 x2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at x0 x1 x2
  obtain ⟨e0, e1, e2⟩ := vdm3 (cA * A 0 + cB * B 0 - θ 0 * w 0)
    (cA * A 1 + cB * B 1 - θ 1 * w 1) (cA * A 2 + cB * B 2 - θ 2 * w 2) (θ 0) (θ 1) (θ 2)
    (by linear_combination x0 - w1 - cA * hA3 - hcB - hcA - cB * hB4)
    (by linear_combination x1 - w2 - θ 3 * (cA * hA3 + hcB) - θ 4 * (hcA + cB * hB4))
    (by linear_combination x2 - hw3 - θ 3 ^ 2 * (cA * hA3 + hcB) - θ 4 ^ 2 * (hcA + cB * hB4))
    d01 d02 d12
  have hxeq : cA • A + cB • B = fun n => θ n * w n := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact fin5 (fun n => cA * A n + cB * B n = θ n * w n)
      (by
        show cA * A 0 + cB * B 0 = θ 0 * w 0
        linear_combination e0)
      (by
        show cA * A 1 + cB * B 1 = θ 1 * w 1
        linear_combination e1)
      (by
        show cA * A 2 + cB * B 2 = θ 2 * w 2
        linear_combination e2)
      (by
        show cA * A 3 + cB * B 3 = θ 3 * w 3
        linear_combination cA * hA3 + hcB)
      (by
        show cA * A 4 + cB * B 4 = θ 4 * w 4
        linear_combination hcA + cB * hB4) n
  have hxL' : (fun n => θ n * w n) ∈ Lam := by
    rw [← hxeq]
    exact hxL
  have hW := caseC_alg θ w hθ (fun m => hF w hwL m) (fun m => hF _ hxL' m)
    (fun m => hF _ (Lam.add_mem hwL hxL') m)
  apply hwne
  funext n
  exact hW n

theorem SL6 (H6 : HypS6) (K : Submodule ℂ M45) (hK : SLev K) : Module.finrank ℂ K ≤ 3 :=
  SL_of H6 (HypS7_of (HypS7alg_of HypIIa_proof)) HypS8_proof K hK

theorem SL6C (HC : HypS6C) (K : Submodule ℂ M45) (hK : SLev K) : Module.finrank ℂ K ≤ 3 :=
  SL6 (HypS6_of (AlgCore_of HC)) K hK

theorem HypS6_proof : HypS6 := HypS6_of (AlgCore_of HypS6C_proof)

theorem LemmaSL (K : Submodule ℂ M45) (hK : SLev K) : Module.finrank ℂ K ≤ 3 :=
  SL6C HypS6C_proof K hK

theorem TheoremFL_row (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → rowMat r w ∈ L) :
    Module.finrank ℂ L ≤ 7 := FL_of LemmaSL L hL r hF

theorem emb_perm_bij : Function.Bijective (fun σ : Equiv.Perm (Fin 5) => σ.toEmbedding) :=
  ⟨fun σ τ h => Equiv.ext fun x => DFunLike.congr_fun h x,
    fun e => ⟨e.equivOfFiniteSelfEmbedding, e.toEmbedding_equivOfFiniteSelfEmbedding⟩⟩

theorem gap_swap5 (t : M55) :
    (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (f i, i))) =
      ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i)) := by
  have h1 : ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (σ i, i)) =
      ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (f i, i)) :=
    Fintype.sum_bijective _ emb_perm_bij (fun σ : Equiv.Perm (Fin 5) => ∏ i, (1 + t (σ i, i)))
      (fun f : Fin 5 ↪ Fin 5 => ∏ i, (1 + t (f i, i))) (fun σ => rfl)
  have h2 : ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (i, σ i)) =
      ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i)) :=
    Fintype.sum_bijective _ emb_perm_bij (fun σ : Equiv.Perm (Fin 5) => ∏ i, (1 + t (i, σ i)))
      (fun f : Fin 5 ↪ Fin 5 => ∏ i, (1 + t (i, f i))) (fun σ => rfl)
  have h3 : ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (i, σ⁻¹ i)) =
      ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (i, σ i)) :=
    Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin 5)))
      (fun σ : Equiv.Perm (Fin 5) => ∏ i, (1 + t (i, σ i)))
  have h4 : ∀ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (σ i, i)) = ∏ i, (1 + t (i, σ⁻¹ i)) := by
    intro σ
    exact Fintype.prod_equiv σ (fun i => 1 + t (σ i, i)) (fun j => 1 + t (j, σ⁻¹ j))
      (fun i => by simp)
  rw [← h1, ← h2, ← h3]
  exact Finset.sum_congr rfl (fun σ _ => h4 σ)

def trE5 : M55 ≃ₗ[ℂ] M55 := LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodComm (Fin 5) (Fin 5))

theorem trE5_apply (t : M55) (i j : Fin 5) : trE5 t (i, j) = t (j, i) := rfl

def colMat (c : Fin 5) (w : Fin 5 → ℂ) : M55 := fun p => if p.2 = c then w p.1 else 0

theorem FL_col_of (HSL : ∀ K : Submodule ℂ M45, SLev K → Module.finrank ℂ K ≤ 3)
    (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (c : Fin 5) (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → colMat c w ∈ L) :
    Module.finrank ℂ L ≤ 7 := by
  have hL' : ∀ t ∈ L.map (trE5 : M55 →ₗ[ℂ] M55),
      (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120 := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := gap_swap5 t
    have h2 : (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + (trE5 t) (i, f i))) =
        ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (f i, i)) := rfl
    exact h2.trans (h1.trans (hL t ht))
  have hF' : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 →
      rowMat c w ∈ L.map (trE5 : M55 →ₗ[ℂ] M55) := by
    intro w hw
    refine ⟨colMat c w, hF w hw, ?_⟩
    funext ⟨i, j⟩
    rfl
  have h := FL_of HSL _ hL' c hF'
  have h2 := LinearEquiv.finrank_map_eq trE5 L
  omega

theorem cor_row (HSL : ∀ K : Submodule ℂ M45, SLev K → Module.finrank ℂ K ≤ 3)
    (L : Submodule ℂ M55) (r : Fin 5)
    (hS : SLev ((L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55).map (del r))) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (L.map (rowP r)) + 3 := by
  have h1 := rank_nullity L (rowP r)
  have h4 := rank_nullity (L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55) (del r)
  have h5 : ((L ⊓ LinearMap.ker (rowP r)) ⊓ LinearMap.ker (del r) : Submodule ℂ M55) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨⟨_, ht1⟩, ht2⟩
    rw [Submodule.mem_bot]
    rw [SetLike.mem_coe, LinearMap.mem_ker] at ht1 ht2
    funext ⟨i, j⟩
    by_cases hi : i = r
    · have := congrFun ht1 j
      rw [rowP_apply] at this
      rw [hi]
      exact this
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hi
      have := congrFun ht2 (k, j)
      rw [del_apply] at this
      rw [← hk]
      exact this
  rw [h5, finrank_bot] at h4
  have h6 := HSL _ hS
  omega

theorem cor_row7 (HSL : ∀ K : Submodule ℂ M45, SLev K → Module.finrank ℂ K ≤ 3)
    (L : Submodule ℂ M55) (r : Fin 5)
    (hS : SLev ((L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55).map (del r)))
    (hrow : ∀ t ∈ L, ∑ j, t (r, j) = 0) : Module.finrank ℂ L ≤ 7 := by
  have h1 := cor_row HSL L r hS
  have h2 : L.map (rowP r) ≤ sumZero 5 := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_sumZero]
    exact hrow y hy
  have h3 := (Submodule.finrank_mono h2).trans (finrank_sumZero (n := 5) (by norm_num))
  omega

theorem TheoremFL_col (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (c : Fin 5) (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → colMat c w ∈ L) :
    Module.finrank ℂ L ≤ 7 := FL_col_of LemmaSL L hL c hF

theorem Cor_row (L : Submodule ℂ M55) (r : Fin 5)
    (hS : SLev ((L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55).map (del r))) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (L.map (rowP r)) + 3 := cor_row LemmaSL L r hS

theorem Cor_row7 (L : Submodule ℂ M55) (r : Fin 5)
    (hS : SLev ((L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55).map (del r)))
    (hrow : ∀ t ∈ L, ∑ j, t (r, j) = 0) : Module.finrank ℂ L ≤ 7 :=
  cor_row7 LemmaSL L r hS hrow

theorem P4_poly (a : Fin 5) (B Y : M45) : ∃ c0 c1 c2 c3 c4 : ℂ, ∀ s : ℂ,
    P4 a (fun p => B p + s * Y p) = c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 + c4 * s ^ 4 := by
  refine ⟨(∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        B (0, e 0) * B (1, e 1) * B (2, e 2) * B (3, e 3) else 0),
    (∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * B (1, e 1) * B (2, e 2) * B (3, e 3)
        + B (0, e 0) * Y (1, e 1) * B (2, e 2) * B (3, e 3)
        + B (0, e 0) * B (1, e 1) * Y (2, e 2) * B (3, e 3)
        + B (0, e 0) * B (1, e 1) * B (2, e 2) * Y (3, e 3) else 0),
    (∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * Y (1, e 1) * B (2, e 2) * B (3, e 3)
        + Y (0, e 0) * B (1, e 1) * Y (2, e 2) * B (3, e 3)
        + Y (0, e 0) * B (1, e 1) * B (2, e 2) * Y (3, e 3)
        + B (0, e 0) * Y (1, e 1) * Y (2, e 2) * B (3, e 3)
        + B (0, e 0) * Y (1, e 1) * B (2, e 2) * Y (3, e 3)
        + B (0, e 0) * B (1, e 1) * Y (2, e 2) * Y (3, e 3) else 0),
    (∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * Y (1, e 1) * Y (2, e 2) * B (3, e 3)
        + Y (0, e 0) * Y (1, e 1) * B (2, e 2) * Y (3, e 3)
        + Y (0, e 0) * B (1, e 1) * Y (2, e 2) * Y (3, e 3)
        + B (0, e 0) * Y (1, e 1) * Y (2, e 2) * Y (3, e 3) else 0),
    (∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * Y (1, e 1) * Y (2, e 2) * Y (3, e 3) else 0), fun s => ?_⟩
  simp only [P4]
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs
  · ring
  · ring

theorem P4_ones (a : Fin 5) : P4 a (fun _ => (1 : ℂ)) = 24 := by
  rw [P4_cols]
  have h := pc_expand (0 : V4) 0 0 0 0
  have e : (fun i : Fin 4 => (1 : ℂ) + 0 * (0 : V4) i) = fun _ => 1 := by
    funext i
    simp
  rw [e] at h
  have h' : pc (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) (fun _ => 1) (fun _ => 1) = 24 := by
    rw [h]
    ring
  exact h'

theorem DS_star (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) (r : Fin 5)
    (hdel : ∀ t ∈ L, ∑ a, P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120)
    (t : M55) (ht : t ∈ L) :
    ∑ a, t (r, a) * P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 0 := by
  have h2 := perm5_row r (fun p => 1 + t p)
  have h3 : ∑ a, (1 + t (r, a)) * P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120 :=
    h2.symm.trans (hL t ht)
  have h4 := hdel t ht
  rw [Fin.sum_univ_five] at h3 h4 ⊢
  linear_combination h3 - h4

theorem DS_i (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) (r : Fin 5)
    (hdel : ∀ t ∈ L, ∑ a, P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120)
    (t : M55) (ht : t ∈ L) (ξ : M55) (hξ : ξ ∈ L) (hξr : ∀ a, ξ (r, a) = 0) :
    ∑ a, t (r, a) * P4 a (fun p => 1 + ξ (r.succAbove p.1, p.2)) = 0 := by
  have hpoly : ∀ a, ∃ c0 c1 c2 c3 c4 : ℂ, ∀ s : ℂ,
      P4 a (fun p => 1 + ξ (r.succAbove p.1, p.2) + s * t (r.succAbove p.1, p.2)) =
        c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 + c4 * s ^ 4 := fun a =>
    P4_poly a (fun p => 1 + ξ (r.succAbove p.1, p.2)) (fun p => t (r.succAbove p.1, p.2))
  choose c0 c1 c2 c3 c4 hc using hpoly
  have hs : ∀ s : ℂ, s ≠ 0 → ∑ a, t (r, a) *
      (c0 a + c1 a * s + c2 a * s ^ 2 + c3 a * s ^ 3 + c4 a * s ^ 4) = 0 := by
    intro s hs0
    have h := DS_star L hL r hdel (s • t + ξ) (L.add_mem (L.smul_mem s ht) hξ)
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (s • t + ξ) (r.succAbove p.1, p.2)) =
        fun p => 1 + ξ (r.succAbove p.1, p.2) + s * t (r.succAbove p.1, p.2) := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1] at h
    have e2 : ∀ a, (s • t + ξ) (r, a) = s * t (r, a) := by
      intro a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hξr a, add_zero]
    simp only [e2, hc] at h
    have h5 : s * ∑ a, t (r, a) *
        (c0 a + c1 a * s + c2 a * s ^ 2 + c3 a * s ^ 3 + c4 a * s ^ 4) = 0 := by
      rw [Finset.mul_sum]
      exact (Finset.sum_congr rfl (fun a _ => by ring)).trans h
    exact (mul_eq_zero.mp h5).resolve_left hs0
  have hpol : ∀ s : ℂ, ∑ a, t (r, a) *
      (c0 a + c1 a * s + c2 a * s ^ 2 + c3 a * s ^ 3 + c4 a * s ^ 4) =
      (∑ a, t (r, a) * c0 a) + (∑ a, t (r, a) * c1 a) * s + (∑ a, t (r, a) * c2 a) * s ^ 2
        + (∑ a, t (r, a) * c3 a) * s ^ 3 + (∑ a, t (r, a) * c4 a) * s ^ 4 := by
    intro s
    simp only [Fin.sum_univ_five]
    ring
  have hinj : Function.Injective (fun i : Fin 5 => ((i : ℕ) : ℂ) + 1) := by
    intro i j h
    have h' : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := add_right_cancel h
    exact Fin.ext (Nat.cast_injective h')
  obtain ⟨hC0, _, _, _, _⟩ := roots5 (fun i : Fin 5 => ((i : ℕ) : ℂ) + 1) hinj
    (∑ a, t (r, a) * c0 a) (∑ a, t (r, a) * c1 a) (∑ a, t (r, a) * c2 a)
    (∑ a, t (r, a) * c3 a) (∑ a, t (r, a) * c4 a)
    (fun i => by
      have h := hs (((i : ℕ) : ℂ) + 1) (Nat.cast_add_one_ne_zero _)
      rw [hpol] at h
      exact h)
  have e0 : ∀ a, P4 a (fun p => 1 + ξ (r.succAbove p.1, p.2)) = c0 a := by
    intro a
    have h := hc a 0
    have e : (fun p : Fin 4 × Fin 5 => 1 + ξ (r.succAbove p.1, p.2)
        + 0 * t (r.succAbove p.1, p.2)) = fun p => 1 + ξ (r.succAbove p.1, p.2) := by
      funext p
      ring
    rw [e] at h
    rw [h]
    ring
  simp only [e0]
  exact hC0

theorem LemmaDS (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) (r : Fin 5)
    (hdel : ∀ t ∈ L, ∑ a, P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120) :
    (∀ t ∈ L, ∑ a, t (r, a) = 0) ∧
    (Module.finrank ℂ (L.map (rowP r)) = 4 →
      SLev ((L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55).map (del r)) ∧
        Module.finrank ℂ L ≤ 7) := by
  have hrow : ∀ t ∈ L, ∑ a, t (r, a) = 0 := by
    intro t ht
    have h := DS_i L hL r hdel t ht 0 L.zero_mem (fun a => rfl)
    have e1 : (fun p : Fin 4 × Fin 5 => (1 : ℂ) + (0 : M55) (r.succAbove p.1, p.2)) =
        fun _ => 1 := by
      funext p
      simp
    rw [e1] at h
    simp only [P4_ones] at h
    rw [← Finset.sum_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (by norm_num)
  refine ⟨hrow, fun h4 => ?_⟩
  have hle : L.map (rowP r) ≤ sumZero 5 := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_sumZero]
    exact hrow y hy
  have heq : L.map (rowP r) = sumZero 5 :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [h4]
      exact finrank_sumZero (n := 5) (by norm_num))
  have hS : SLev ((L ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55).map (del r)) := by
    rintro Y ⟨ξ, hξ, rfl⟩ a
    have hξL := (Submodule.mem_inf.mp hξ).1
    have hξ0 : rowP r ξ = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hξ).2
    have hξr : ∀ b, ξ (r, b) = 0 := fun b => congrFun hξ0 b
    have hg : ∀ b, P4 b (fun p => 1 + ξ (r.succAbove p.1, p.2)) =
        P4 a (fun p => 1 + ξ (r.succAbove p.1, p.2)) := by
      intro b
      have hw : (fun j : Fin 5 => (if j = b then (1 : ℂ) else 0) - (if j = a then (1 : ℂ) else 0))
          ∈ sumZero 5 := by
        rw [mem_sumZero]
        simp [Finset.sum_sub_distrib]
      rw [← heq] at hw
      obtain ⟨t, ht, htw⟩ := hw
      have h := DS_i L hL r hdel t ht ξ hξL hξr
      have e : ∀ j, t (r, j) = (if j = b then (1 : ℂ) else 0) - (if j = a then (1 : ℂ) else 0) :=
        fun j => congrFun htw j
      simp only [e, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      linear_combination h
    have h5 := hdel ξ hξL
    rw [Fin.sum_univ_five, hg 0, hg 1, hg 2, hg 3, hg 4] at h5
    show P4 a (fun p => 1 + ξ (r.succAbove p.1, p.2)) = 24
    linear_combination (1 / 5 : ℂ) * h5
  have h6 := cor_row LemmaSL L r hS
  exact ⟨hS, by omega⟩

def Lev45 (K : Submodule ℂ M45) : Prop := ∀ Y ∈ K, ∑ a, P4 a (fun p => 1 + Y p) = 120

def DefLine (K : Submodule ℂ M45) (m : Fin 5 → ℂ) : Prop :=
  ∀ Y ∈ K, ∃ θ : ℂ, ∀ a, P4 a (fun p => 1 + Y p) = 24 + θ * m a

def defW (K : Submodule ℂ M45) : Submodule ℂ (Fin 5 → ℂ) :=
  { carrier := {w | ∀ Y ∈ K, ∑ a, w a * P4 a (fun p => 1 + Y p) = 0}, add_mem' := (by
      intro w w' hw hw' Y hY
      have h1 := hw Y hY
      have h2 := hw' Y hY
      rw [Fin.sum_univ_five] at h1 h2 ⊢
      simp only [Pi.add_apply]
      linear_combination h1 + h2),
    zero_mem' := (by
      intro Y hY
      simp),
    smul_mem' := (by
      intro c w hw Y hY
      have h1 := hw Y hY
      rw [Fin.sum_univ_five] at h1 ⊢
      simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination c * h1) }

theorem mem_defW (K : Submodule ℂ M45) (w : Fin 5 → ℂ) :
    w ∈ defW K ↔ ∀ Y ∈ K, ∑ a, w a * P4 a (fun p => 1 + Y p) = 0 := Iff.rfl

theorem defW_sum (K : Submodule ℂ M45) (w : Fin 5 → ℂ) (hw : w ∈ defW K) : ∑ a, w a = 0 := by
  have h := (mem_defW K w).mp hw 0 K.zero_mem
  have e1 : (fun p : Fin 4 × Fin 5 => (1 : ℂ) + (0 : M45) p) = fun _ => 1 := by
    funext p
    simp
  rw [e1] at h
  simp only [P4_ones] at h
  rw [← Finset.sum_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (by norm_num)

theorem defW_le (K : Submodule ℂ M45) : defW K ≤ sumZero 5 := by
  intro w hw
  rw [mem_sumZero]
  exact defW_sum K w hw

theorem defW_SLev (K : Submodule ℂ M45) (hK : SLev K) : defW K = sumZero 5 := by
  apply le_antisymm (defW_le K)
  intro w hw
  rw [mem_sumZero] at hw
  refine (mem_defW K w).mpr (fun Y hY => ?_)
  rw [Fin.sum_univ_five] at hw ⊢
  rw [hK Y hY 0, hK Y hY 1, hK Y hY 2, hK Y hY 3, hK Y hY 4]
  linear_combination 24 * hw

def defL (r : Fin 5) (K : Submodule ℂ M45) : Submodule ℂ M55 :=
  K.comap (del r) ⊓ (defW K).comap (rowP r)

theorem defL_level (r : Fin 5) (K : Submodule ℂ M45) (hK : Lev45 K) :
    ∀ t ∈ defL r K, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120 := by
  intro t ht
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp ht
  have hY : del r t ∈ K := h1
  have hw : rowP r t ∈ defW K := h2
  have h4 : (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) =
      ∑ a, (1 + t (r, a)) * P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) :=
    perm5_row r (fun p => 1 + t p)
  rw [h4]
  have h5 : ∑ a, P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120 := hK _ hY
  have h6 : ∑ a, t (r, a) * P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 0 :=
    (mem_defW K _).mp hw _ hY
  rw [Fin.sum_univ_five] at h5 h6 ⊢
  linear_combination h5 + h6

theorem defL_deletable (r : Fin 5) (K : Submodule ℂ M45) (hK : Lev45 K) :
    ∀ t ∈ defL r K, ∑ a, P4 a (fun p => 1 + t (r.succAbove p.1, p.2)) = 120 := by
  intro t ht
  have hY : del r t ∈ K := (Submodule.mem_inf.mp ht).1
  exact hK _ hY

def ins (r : Fin 5) (Y : M45) : M55 :=
  fun p => @Fin.insertNth 4 (fun _ => ℂ) r (0 : ℂ) (fun k => Y (k, p.2)) p.1

theorem del_ins (r : Fin 5) (Y : M45) : del r (ins r Y) = Y := by
  funext ⟨k, j⟩
  show @Fin.insertNth 4 (fun _ => ℂ) r (0 : ℂ) (fun k => Y (k, j)) (r.succAbove k) = Y (k, j)
  rw [Fin.insertNth_apply_succAbove]

theorem rowP_ins (r : Fin 5) (Y : M45) : rowP r (ins r Y) = 0 := by
  funext j
  show @Fin.insertNth 4 (fun _ => ℂ) r (0 : ℂ) (fun k => Y (k, j)) r = 0
  rw [Fin.insertNth_apply_same]

theorem del_rowMat (r : Fin 5) (w : Fin 5 → ℂ) : del r (rowMat r w) = 0 := by
  funext p
  simp [rowMat, del_apply, Fin.succAbove_ne]

theorem rowP_rowMat (r : Fin 5) (w : Fin 5 → ℂ) : rowP r (rowMat r w) = w := by
  funext j
  simp [rowMat, rowP_apply]

theorem del_row_bot (L : Submodule ℂ M55) (r : Fin 5) :
    ((L ⊓ LinearMap.ker (del r)) ⊓ LinearMap.ker (rowP r) : Submodule ℂ M55) = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨⟨_, ht2⟩, ht1⟩
  rw [Submodule.mem_bot]
  rw [SetLike.mem_coe, LinearMap.mem_ker] at ht1 ht2
  funext ⟨i, j⟩
  by_cases hi : i = r
  · have := congrFun ht1 j
    rw [rowP_apply] at this
    rw [hi]
    exact this
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hi
    have := congrFun ht2 (k, j)
    rw [del_apply] at this
    rw [← hk]
    exact this

theorem defL_finrank (r : Fin 5) (K : Submodule ℂ M45) :
    Module.finrank ℂ (defL r K) = Module.finrank ℂ K + Module.finrank ℂ (defW K) := by
  have rn := rank_nullity (defL r K) (del r)
  have rn2 := rank_nullity (defL r K ⊓ LinearMap.ker (del r) : Submodule ℂ M55) (rowP r)
  have h5 := del_row_bot (defL r K) r
  rw [h5, finrank_bot] at rn2
  have e1 : (defL r K).map (del r) = K := by
    apply le_antisymm
    · rintro Y ⟨t, ht, rfl⟩
      exact (Submodule.mem_inf.mp ht).1
    · intro Y hY
      refine ⟨ins r Y, Submodule.mem_inf.mpr ⟨?_, ?_⟩, del_ins r Y⟩
      · show del r (ins r Y) ∈ K
        rw [del_ins]
        exact hY
      · show rowP r (ins r Y) ∈ defW K
        rw [rowP_ins]
        exact (defW K).zero_mem
  have e2 : (defL r K ⊓ LinearMap.ker (del r) : Submodule ℂ M55).map (rowP r) = defW K := by
    apply le_antisymm
    · rintro w ⟨t, ht, rfl⟩
      exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp ht).1).2
    · intro w hw
      refine ⟨rowMat r w, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩,
        rowP_rowMat r w⟩
      · show del r (rowMat r w) ∈ K
        rw [del_rowMat]
        exact K.zero_mem
      · show rowP r (rowMat r w) ∈ defW K
        rw [rowP_rowMat]
        exact hw
      · exact LinearMap.mem_ker.mpr (del_rowMat r w)
  rw [e1] at rn
  rw [e2] at rn2
  omega

theorem defect_conv (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) (r : Fin 5) :
    Module.finrank ℂ L ≤
      Module.finrank ℂ (L.map (del r)) + Module.finrank ℂ (defW (L.map (del r))) := by
  have rn := rank_nullity L (del r)
  have rn2 := rank_nullity (L ⊓ LinearMap.ker (del r) : Submodule ℂ M55) (rowP r)
  have h5 := del_row_bot L r
  rw [h5, finrank_bot] at rn2
  have hle : (L ⊓ LinearMap.ker (del r) : Submodule ℂ M55).map (rowP r) ≤
      defW (L.map (del r)) := by
    rintro w ⟨u, hu, rfl⟩
    refine (mem_defW _ _).mpr ?_
    rintro Y ⟨z, hz, rfl⟩
    obtain ⟨huL, hu0⟩ := Submodule.mem_inf.mp hu
    have hu0' : del r u = 0 := LinearMap.mem_ker.mp hu0
    have hz1 : ∑ a, (1 + z (r, a)) * P4 a (fun p => 1 + z (r.succAbove p.1, p.2)) = 120 :=
      (perm5_row r (fun p => 1 + z p)).symm.trans (hL z hz)
    have hzu : ∑ a, (1 + (z + u) (r, a)) *
        P4 a (fun p => 1 + (z + u) (r.succAbove p.1, p.2)) = 120 :=
      (perm5_row r (fun p => 1 + (z + u) p)).symm.trans (hL _ (L.add_mem hz huL))
    have e : (fun p : Fin 4 × Fin 5 => 1 + (z + u) (r.succAbove p.1, p.2)) =
        fun p => 1 + z (r.succAbove p.1, p.2) := by
      funext p
      have h0 : u (r.succAbove p.1, p.2) = 0 := congrFun hu0' p
      simp only [Pi.add_apply, h0, add_zero]
    rw [e] at hzu
    show ∑ a, u (r, a) * P4 a (fun p => 1 + z (r.succAbove p.1, p.2)) = 0
    rw [Fin.sum_univ_five] at hz1 hzu ⊢
    simp only [Pi.add_apply] at hzu
    linear_combination hzu - hz1
  have h7 := Submodule.finrank_mono hle
  omega

theorem LemmaEQ (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (π : Equiv.Perm (Fin 5)) (j : Fin 5) (hj : m (π j) ≠ m j) :
    SLev (K ⊓ LinearMap.eqLocus (cperm π) LinearMap.id) ∧
      Module.finrank ℂ (K ⊓ LinearMap.eqLocus (cperm π) LinearMap.id : Submodule ℂ M45) ≤ 3 := by
  have hS : SLev (K ⊓ LinearMap.eqLocus (cperm π) LinearMap.id) := by
    intro Y hY a
    obtain ⟨hYK, hfix⟩ := Submodule.mem_inf.mp hY
    have hfix' : cperm π Y = Y := LinearMap.mem_eqLocus.mp hfix
    obtain ⟨θ, hθ⟩ := hdef Y hYK
    have hperm : ∀ b, P4 b (fun p => 1 + Y p) = P4 (π b) (fun p => 1 + Y p) := by
      intro b
      have h : P4 b (fun p => 1 + Y (p.1, π p.2)) = P4 (π b) (fun p => 1 + Y p) :=
        P4_perm π b (fun p => 1 + Y p)
      have e : (fun p : Fin 4 × Fin 5 => 1 + Y (p.1, π p.2)) = fun p => 1 + Y p := by
        funext p
        have h0 : Y (p.1, π p.2) = Y p := congrFun hfix' p
        rw [h0]
      rw [e] at h
      exact h
    have h1 := hθ j
    have h2 := hθ (π j)
    have h3 := hperm j
    have hθ0 : θ = 0 := by
      have h4 : θ * (m (π j) - m j) = 0 := by linear_combination h1 - h2 - h3
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hj)
    rw [hθ a, hθ0]
    ring
  exact ⟨hS, LemmaSL _ hS⟩

theorem LemmaEQ_cols (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (a b : Fin 5) (hab : m a ≠ m b) :
    SLev (K ⊓ LinearMap.ker (colL a - colL b)) ∧
      Module.finrank ℂ K ≤ 3 + Module.finrank ℂ (K.map (colL a - colL b)) := by
  have hle : (K ⊓ LinearMap.ker (colL a - colL b) : Submodule ℂ M45) ≤
      K ⊓ LinearMap.eqLocus (cperm (Equiv.swap a b)) LinearMap.id := by
    intro Y hY
    obtain ⟨hYK, hk⟩ := Submodule.mem_inf.mp hY
    have hk' : (colL a - colL b) Y = 0 := LinearMap.mem_ker.mp hk
    have hcol : ∀ i, Y (i, a) = Y (i, b) := by
      intro i
      have h0 := congrFun hk' i
      simp only [LinearMap.sub_apply, colL_apply, Pi.sub_apply, col, Pi.zero_apply] at h0
      linear_combination h0
    refine Submodule.mem_inf.mpr ⟨hYK, LinearMap.mem_eqLocus.mpr ?_⟩
    funext ⟨i, k⟩
    show Y (i, Equiv.swap a b k) = Y (i, k)
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1]
      exact (hcol i).symm
    · rw [h2]
      exact hcol i
    · rfl
  have h := LemmaEQ K m hdef (Equiv.swap a b) a (by
    rw [Equiv.swap_apply_left]
    exact hab.symm)
  have hS := SLev_mono h.1 hle
  have rn := rank_nullity K (colL a - colL b)
  have h3 := LemmaSL _ hS
  exact ⟨hS, by omega⟩

def repl (i : Fin 4) (u : Fin 5 → ℂ) (N : M45) : M45 := fun p => if p.1 = i then u p.2 else N p

theorem repl_at (i : Fin 4) (u : Fin 5 → ℂ) (N : M45) (j : Fin 5) : repl i u N (i, j) = u j := by
  show (if i = i then u j else N (i, j)) = u j
  rw [if_pos rfl]

theorem repl_ne (i k : Fin 4) (hk : k ≠ i) (u : Fin 5 → ℂ) (N : M45) (j : Fin 5) :
    repl i u N (k, j) = N (k, j) := by
  show (if k = i then u j else N (k, j)) = N (k, j)
  rw [if_neg hk]

theorem P4_prod (a : Fin 5) (M : M45) : P4 a M = ∑ e : Fin 4 ↪ Fin 5,
    if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then ∏ k, M (k, e k) else 0 := by
  unfold P4
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Fin.prod_univ_four]

theorem repl_prod (i : Fin 4) (u : Fin 5 → ℂ) (N : M45) (e : Fin 4 ↪ Fin 5) :
    ∏ k, repl i u N (k, e k) = u (e i) * ∏ k ∈ Finset.univ \ {i}, N (k, e k) := by
  refine (Finset.prod_congr rfl (fun k _ => ?_)).trans
    (Finset.prod_update_of_mem (Finset.mem_univ i) (fun k => N (k, e k)) (u (e i)))
  by_cases h1 : k = i
  · rw [h1, repl_at, Function.update_self]
  · rw [repl_ne i k h1, Function.update_of_ne h1]

theorem P4_repl_add (a : Fin 5) (i : Fin 4) (x y : Fin 5 → ℂ) (N : M45) :
    P4 a (repl i (x + y) N) = P4 a (repl i x N) + P4 a (repl i y N) := by
  rw [P4_prod, P4_prod, P4_prod, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [repl_prod, repl_prod, repl_prod]
  split_ifs
  · simp only [Pi.add_apply]
    ring
  · ring

theorem repl_self (i : Fin 4) (N : M45) : repl i (fun j => N (i, j)) N = N := by
  funext ⟨k, j⟩
  by_cases h : k = i
  · rw [h, repl_at]
  · rw [repl_ne i k h]

def stk (r : Fin 5) (N : M45) (w : Fin 5 → ℂ) : M55 := ins r N + rowMat r w

theorem stk_r (r : Fin 5) (N : M45) (w : Fin 5 → ℂ) (j : Fin 5) : stk r N w (r, j) = w j := by
  have h1 : ins r N (r, j) = 0 := congrFun (rowP_ins r N) j
  have h2 : rowMat r w (r, j) = w j := congrFun (rowP_rowMat r w) j
  show ins r N (r, j) + rowMat r w (r, j) = w j
  rw [h1, h2, zero_add]

theorem stk_s (r : Fin 5) (N : M45) (w : Fin 5 → ℂ) (k : Fin 4) (j : Fin 5) :
    stk r N w (r.succAbove k, j) = N (k, j) := by
  have h1 : ins r N (r.succAbove k, j) = N (k, j) := congrFun (del_ins r N) (k, j)
  have h2 : rowMat r w (r.succAbove k, j) = 0 := congrFun (del_rowMat r w) (k, j)
  show ins r N (r.succAbove k, j) + rowMat r w (r.succAbove k, j) = N (k, j)
  rw [h1, h2, add_zero]

theorem per_stk (r : Fin 5) (N : M45) (w : Fin 5 → ℂ) :
    ∑ f : Fin 5 ↪ Fin 5, ∏ k, stk r N w (k, f k) = ∑ a, w a * P4 a N := by
  have h := perm5_row r (stk r N w)
  have e : (fun p : Fin 4 × Fin 5 => stk r N w (r.succAbove p.1, p.2)) = N := by
    funext p
    exact stk_s r N w p.1 p.2
  rw [e] at h
  rw [h]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [stk_r]

theorem per_rows (σ : Equiv.Perm (Fin 5)) (M : M55) :
    ∑ f : Fin 5 ↪ Fin 5, ∏ k, M (σ k, f k) = ∑ f : Fin 5 ↪ Fin 5, ∏ k, M (k, f k) := by
  refine (Finset.sum_congr rfl (fun f _ => ?_)).trans
    (sum_emb_perm σ⁻¹ (fun f : Fin 5 ↪ Fin 5 => ∏ k, M (k, f k)))
  exact Fintype.prod_equiv σ (fun k => M (σ k, f k))
    (fun k => M (k, (σ⁻¹.toEmbedding.trans f) k)) (fun k => by simp)

theorem P4_sym (r : Fin 5) (i : Fin 4) (w u : Fin 5 → ℂ) (N : M45) :
    ∑ a, w a * P4 a (repl i u N) = ∑ a, u a * P4 a (repl i w N) := by
  rw [← per_stk r (repl i u N) w, ← per_stk r (repl i w N) u,
    ← per_rows (Equiv.swap r (r.succAbove i)) (stk r (repl i u N) w)]
  refine Finset.sum_congr rfl (fun f _ => Finset.prod_congr rfl (fun k _ => ?_))
  have hne : r.succAbove i ≠ r := Fin.succAbove_ne r i
  by_cases hk : k = r
  · rw [hk, Equiv.swap_apply_left, stk_s, stk_r, repl_at]
  · obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hk
    rw [← hk']
    by_cases hi : k' = i
    · rw [hi, Equiv.swap_apply_right, stk_r, stk_s, repl_at]
    · have h1 : r.succAbove k' ≠ r := Fin.succAbove_ne r k'
      have h2 : r.succAbove k' ≠ r.succAbove i := fun h => hi (Fin.succAbove_right_injective h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, stk_s, stk_s, repl_ne i k' hi, repl_ne i k' hi]

def phiRow (i : Fin 4) (m : Fin 5 → ℂ) : M45 →ₗ[ℂ] ℂ where
  toFun Y := m 0 * Y (i, 0) + m 1 * Y (i, 1) + m 2 * Y (i, 2) + m 3 * Y (i, 3) + m 4 * Y (i, 4)
  map_add' Y Y' := by
    simp only [Pi.add_apply]
    ring
  map_smul' c Y := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem phiRow_apply (i : Fin 4) (m : Fin 5 → ℂ) (Y : M45) : phiRow i m Y =
    m 0 * Y (i, 0) + m 1 * Y (i, 1) + m 2 * Y (i, 2) + m 3 * Y (i, 3) + m 4 * Y (i, 4) := rfl

theorem ThmSplit (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hmm : ∑ a, m a * m a ≠ 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K) :
    SLev (K ⊓ LinearMap.ker (phiRow i m)) ∧ Module.finrank ℂ K ≤ 4 := by
  have hS : SLev (K ⊓ LinearMap.ker (phiRow i m)) := by
    intro Y hY a
    obtain ⟨hYK, hYφ⟩ := Submodule.mem_inf.mp hY
    have hφ : m 0 * Y (i, 0) + m 1 * Y (i, 1) + m 2 * Y (i, 2) + m 3 * Y (i, 3)
        + m 4 * Y (i, 4) = 0 := LinearMap.mem_ker.mp hYφ
    obtain ⟨θ, hθ⟩ := hdef Y hYK
    obtain ⟨θ1, hθ1⟩ := hdef _ (K.add_mem hYK hsplit)
    have eN : repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p) = fun p => 1 + Y p :=
      repl_self i (fun p => 1 + Y p)
    have eN1 : (fun p : Fin 4 × Fin 5 =>
        1 + (Y + fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) p) =
        repl i ((fun j => 1 + Y (i, j)) + m) (fun p => 1 + Y p) := by
      funext ⟨k, j⟩
      by_cases h : k = i
      · rw [h, repl_at]
        show 1 + (Y (i, j) + if i = i then m j else 0) = 1 + Y (i, j) + m j
        rw [if_pos rfl]
        ring
      · rw [repl_ne i k h]
        show 1 + (Y (k, j) + if k = i then m j else 0) = 1 + Y (k, j)
        rw [if_neg h]
        ring
    have h0 : ∀ b, P4 b (repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p)) = 24 + θ * m b := by
      intro b
      rw [eN]
      exact hθ b
    have hD : ∀ b, P4 b (repl i m (fun p => 1 + Y p)) = (θ1 - θ) * m b := by
      intro b
      have h1 := hθ1 b
      rw [eN1] at h1
      have hadd := P4_repl_add b i (fun j => 1 + Y (i, j)) m (fun p => 1 + Y p)
      linear_combination h1 - h0 b - hadd
    have hs := P4_sym 0 i m (fun j => 1 + Y (i, j)) (fun p => 1 + Y p)
    rw [Fin.sum_univ_five, Fin.sum_univ_five] at hs
    rw [h0 0, h0 1, h0 2, h0 3, h0 4, hD 0, hD 1, hD 2, hD 3, hD 4] at hs
    rw [Fin.sum_univ_five] at hm hmm
    have hθ0 : θ = 0 := by
      have h4 : θ * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4) = 0 := by
        linear_combination hs + (θ1 - θ - 24) * hm + (θ1 - θ) * hφ
      exact (mul_eq_zero.mp h4).resolve_right hmm
    rw [hθ a, hθ0]
    ring
  refine ⟨hS, ?_⟩
  have rn := rank_nullity K (phiRow i m)
  have h1 : Module.finrank ℂ (K.map (phiRow i m)) ≤ 1 := by
    have h := Submodule.finrank_le (K.map (phiRow i m))
    rw [Module.finrank_self] at h
    exact h
  have h3 := LemmaSL _ hS
  omega

def dotL : (Fin 5 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 5 → ℂ) where
  toFun c :=
    { toFun := fun w => c 0 * w 0 + c 1 * w 1 + c 2 * w 2 + c 3 * w 3 + c 4 * w 4
      map_add' := fun w w' => by
        simp only [Pi.add_apply]
        ring
      map_smul' := fun k w => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' c c' := by
    apply LinearMap.ext
    intro w
    show (c + c') 0 * w 0 + (c + c') 1 * w 1 + (c + c') 2 * w 2 + (c + c') 3 * w 3
      + (c + c') 4 * w 4 = (c 0 * w 0 + c 1 * w 1 + c 2 * w 2 + c 3 * w 3 + c 4 * w 4)
      + (c' 0 * w 0 + c' 1 * w 1 + c' 2 * w 2 + c' 3 * w 3 + c' 4 * w 4)
    simp only [Pi.add_apply]
    ring
  map_smul' k c := by
    apply LinearMap.ext
    intro w
    show (k • c) 0 * w 0 + (k • c) 1 * w 1 + (k • c) 2 * w 2 + (k • c) 3 * w 3
      + (k • c) 4 * w 4 = k * (c 0 * w 0 + c 1 * w 1 + c 2 * w 2 + c 3 * w 3 + c 4 * w 4)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem dotL_apply (c w : Fin 5 → ℂ) :
    dotL c w = c 0 * w 0 + c 1 * w 1 + c 2 * w 2 + c 3 * w 3 + c 4 * w 4 := rfl

theorem dotL_ker : LinearMap.ker dotL = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Submodule.mem_bot]
  have hc' : dotL c = 0 := LinearMap.mem_ker.mp hc
  have t0 : dotL c (fun b => if b = (0 : Fin 5) then 1 else 0) = 0 := by
    rw [hc']
    rfl
  have t1 : dotL c (fun b => if b = (1 : Fin 5) then 1 else 0) = 0 := by
    rw [hc']
    rfl
  have t2 : dotL c (fun b => if b = (2 : Fin 5) then 1 else 0) = 0 := by
    rw [hc']
    rfl
  have t3 : dotL c (fun b => if b = (3 : Fin 5) then 1 else 0) = 0 := by
    rw [hc']
    rfl
  have t4 : dotL c (fun b => if b = (4 : Fin 5) then 1 else 0) = 0 := by
    rw [hc']
    rfl
  rw [dotL_apply] at t0 t1 t2 t3 t4
  simp at t0 t1 t2 t3 t4
  funext a
  exact fin5 (fun a => c a = 0) t0 t1 t2 t3 t4 a

def defC (K : Submodule ℂ M45) : Submodule ℂ (Fin 5 → ℂ) :=
  Submodule.span ℂ {c | ∃ Y ∈ K, c = fun a => P4 a (fun p => 1 + Y p)}

theorem defC_mono {K K' : Submodule ℂ M45} (h : K ≤ K') : defC K ≤ defC K' :=
  Submodule.span_mono (fun _ ⟨Y, hY, hc⟩ => ⟨Y, h hY, hc⟩)

theorem defW_finrank (K : Submodule ℂ M45) :
    Module.finrank ℂ (defW K) + Module.finrank ℂ (defC K) = 5 := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq ((defC K).map dotL)
  have e1 : ((defC K).map dotL).dualCoannihilator = defW K := by
    ext w
    rw [Submodule.mem_dualCoannihilator, mem_defW]
    constructor
    · intro h Y hY
      have h2 := h (dotL (fun a => P4 a (fun p => 1 + Y p)))
        (Submodule.mem_map_of_mem (Submodule.subset_span ⟨Y, hY, rfl⟩))
      rw [dotL_apply] at h2
      rw [Fin.sum_univ_five]
      linear_combination h2
    · intro h φ hφ
      obtain ⟨c, hc, rfl⟩ := hφ
      have hle : defC K ≤ LinearMap.ker (dotL.flip w) := by
        refine Submodule.span_le.mpr ?_
        rintro c ⟨Y, hY, rfl⟩
        refine LinearMap.mem_ker.mpr ?_
        show dotL (fun a => P4 a (fun p => 1 + Y p)) w = 0
        rw [dotL_apply]
        have h3 := h Y hY
        rw [Fin.sum_univ_five] at h3
        linear_combination h3
      exact LinearMap.mem_ker.mp (hle hc)
  rw [e1] at h1
  have h3 := rank_nullity (defC K) dotL
  have hk : (defC K ⊓ LinearMap.ker dotL : Submodule ℂ (Fin 5 → ℂ)) = ⊥ := by
    rw [dotL_ker, inf_bot_eq]
  rw [hk, finrank_bot] at h3
  have h5 : Module.finrank ℂ (Fin 5 → ℂ) = 5 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

theorem defect_conv' (L : Submodule ℂ M55)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) (r : Fin 5) :
    Module.finrank ℂ L + Module.finrank ℂ (defC (L.map (del r))) ≤
      Module.finrank ℂ (L.map (del r)) + 5 := by
  have h1 := defect_conv L hL r
  have h2 := defW_finrank (L.map (del r))
  omega

theorem defL_finrank' (r : Fin 5) (K : Submodule ℂ M45) :
    Module.finrank ℂ (defL r K) + Module.finrank ℂ (defC K) = Module.finrank ℂ K + 5 := by
  have h1 := defL_finrank r K
  have h2 := defW_finrank K
  omega

theorem HyperplaneLemma (e : ℕ)
    (hDI : ∀ K : Submodule ℂ M45, Lev45 K → Module.finrank ℂ (defC K) ≤ e →
      Module.finrank ℂ K ≤ Module.finrank ℂ (defC K) + 2)
    (L' : Submodule ℂ M45) (hL' : Lev45 L') (he : Module.finrank ℂ (defC L') = e + 1)
    (K : Submodule ℂ M45) (hK : K ≤ L') :
    defC K = defC L' ∨ Module.finrank ℂ K ≤ Module.finrank ℂ (defC K) + 2 := by
  have hle := defC_mono hK
  by_cases h : Module.finrank ℂ (defC K) ≤ e
  · exact Or.inr (hDI K (fun Y hY => hL' Y (hK hY)) h)
  · left
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)

theorem HyperplaneCor (e : ℕ)
    (hDI : ∀ K : Submodule ℂ M45, Lev45 K → Module.finrank ℂ (defC K) ≤ e →
      Module.finrank ℂ K ≤ Module.finrank ℂ (defC K) + 2)
    (L' : Submodule ℂ M45) (hL' : Lev45 L') (he : Module.finrank ℂ (defC L') = e + 1)
    (K : Submodule ℂ M45) (hK : K ≤ L') (hdim : e + 3 ≤ Module.finrank ℂ K) :
    defC K = defC L' := by
  have hle := defC_mono hK
  by_cases h : Module.finrank ℂ (defC K) ≤ e
  · have h2 := hDI K (fun Y hY => hL' Y (hK hY)) h
    omega
  · exact Submodule.eq_of_le_of_finrank_le hle (by omega)

theorem LemmaHYP_a (K H : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m) (hH : H ≤ K)
    (h4 : Module.finrank ℂ H = 4) : DefLine H m ∧ ¬ SLev H := by
  refine ⟨fun Y hY => hdef Y (hH hY), fun hS => ?_⟩
  have h := LemmaSL H hS
  omega

def colsumL (j : Fin 5) : M45 →ₗ[ℂ] ℂ where
  toFun Y := ∑ k : Fin 4, Y (k, j)
  map_add' Y Y' := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c Y := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem colsumL_apply (j : Fin 5) (Y : M45) : colsumL j Y = ∑ k : Fin 4, Y (k, j) := rfl

theorem hyp4 (K : Submodule ℂ M45) (hK5 : Module.finrank ℂ K = 5) (ψ : M45 →ₗ[ℂ] ℂ)
    (Z : M45) (hZ : Z ∈ K) (hψ : ψ Z ≠ 0) :
    Module.finrank ℂ (K ⊓ LinearMap.ker ψ : Submodule ℂ M45) = 4 := by
  have rn := rank_nullity K ψ
  have h1 : Module.finrank ℂ (K.map ψ) ≤ 1 := by
    have h := Submodule.finrank_le (K.map ψ)
    rw [Module.finrank_self] at h
    exact h
  have h2 : Module.finrank ℂ (K.map ψ) ≠ 0 := by
    intro h0
    have hb := Submodule.finrank_eq_zero.mp h0
    have hm : ψ Z ∈ K.map ψ := Submodule.mem_map_of_mem hZ
    rw [hb, Submodule.mem_bot] at hm
    exact hψ hm
  omega

theorem LemmaHYP_b (m : Fin 5 → ℂ) (hm0 : m ≠ 0)
    (hdich : ∀ H : Submodule ℂ M45, DefLine H m → Module.finrank ℂ H = 4 →
      ∃ i : Fin 4, (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ H)
    (K : Submodule ℂ M45) (hK : DefLine K m) : Module.finrank ℂ K ≠ 5 := by
  intro hK5
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hm0
  have hj0' : m j0 ≠ 0 := hj0
  have hval : ∀ i : Fin 4,
      colsumL j0 (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) = m j0 := by
    intro i
    rw [colsumL_apply]
    simp
  by_cases hφ : ∃ Z ∈ K, colsumL j0 Z ≠ 0
  · obtain ⟨Z, hZ, hZφ⟩ := hφ
    have h4 := hyp4 K hK5 (colsumL j0) Z hZ hZφ
    obtain ⟨i, hi⟩ := hdich _ (fun Y hY => hK Y (Submodule.mem_inf.mp hY).1) h4
    have h0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hi).2
    rw [hval i] at h0
    exact hj0' h0
  · have hall : ∀ Z ∈ K, colsumL j0 Z = 0 := by
      intro Z hZ
      by_contra hne
      exact hφ ⟨Z, hZ, hne⟩
    have hne : K ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hK5
      omega
    obtain ⟨Z, hZ, hZ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨p0, hp0⟩ := Function.ne_iff.mp hZ0
    have h4 := hyp4 K hK5 (LinearMap.proj p0) Z hZ hp0
    obtain ⟨i, hi⟩ := hdich _ (fun Y hY => hK Y (Submodule.mem_inf.mp hY).1) h4
    have h0 := hall _ (Submodule.mem_inf.mp hi).1
    rw [hval i] at h0
    exact hj0' h0

theorem Vp_sum (i : Fin 4) (y : V4) (hy : tau y = 0) (hyi : y i = 0) :
    y (i.succAbove 0) + y (i.succAbove 1) + y (i.succAbove 2) = 0 := by
  have h := Fin.sum_univ_succAbove y i
  rw [Fin.sum_univ_four, Fin.sum_univ_three] at h
  simp only [tau] at hy
  linear_combination hy - h - hyi

theorem Vp_ext (i : Fin 4) (x y : V4) (hi : x i = y i)
    (h0 : x (i.succAbove 0) = y (i.succAbove 0)) (h1 : x (i.succAbove 1) = y (i.succAbove 1))
    (h2 : x (i.succAbove 2) = y (i.succAbove 2)) : x = y := by
  funext k
  by_cases hk : k = i
  · rw [hk]
    exact hi
  · obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hk
    subst hk'
    fin_cases k'
    · exact h0
    · exact h1
    · exact h2

theorem Vp_zero (i : Fin 4) (y : V4) (hy : tau y = 0) (hyi : y i = 0)
    (h0 : y (i.succAbove 0) = 0) (h1 : y (i.succAbove 1) = 0) : y = 0 := by
  have hs := Vp_sum i y hy hyi
  have h2 : y (i.succAbove 2) = 0 := by linear_combination hs - h0 - h1
  exact Vp_ext i y 0 hyi h0 h1 h2

theorem cramer2 (a b c d e f : ℂ) (hdet : a * d - b * c ≠ 0) :
    ∃ p r : ℂ, e = p * a + r * c ∧ f = p * b + r * d := by
  obtain ⟨p, hp⟩ : ∃ p : ℂ, p * (a * d - b * c) = e * d - f * c :=
    ⟨(e * d - f * c) / (a * d - b * c), div_mul_cancel₀ _ hdet⟩
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r * (a * d - b * c) = a * f - b * e :=
    ⟨(a * f - b * e) / (a * d - b * c), div_mul_cancel₀ _ hdet⟩
  refine ⟨p, r, ?_, ?_⟩
  · apply mul_left_cancel₀ hdet
    linear_combination (-a) * hp - c * hr
  · apply mul_left_cancel₀ hdet
    linear_combination (-b) * hp - d * hr

theorem Vp_span (i : Fin 4) (v w : V4) (hv : tau v = 0) (hvi : v i = 0) (hw : tau w = 0)
    (hwi : w i = 0) (hind : indep v w) (x : V4) (hx : tau x = 0) (hxi : x i = 0) :
    ∃ p r : ℂ, x = p • v + r • w := by
  have comb : ∀ s t : ℂ, tau (s • v + t • w) = 0 ∧ (s • v + t • w) i = 0 := by
    intro s t
    constructor
    · simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv hw ⊢
      linear_combination s * hv + t * hw
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvi, hwi]
      ring
  have hdet : v (i.succAbove 0) * w (i.succAbove 1) - v (i.succAbove 1) * w (i.succAbove 0) ≠ 0 := by
    intro hd
    have r1 : w (i.succAbove 1) • v + (-v (i.succAbove 1)) • w = 0 := by
      apply Vp_zero i _ (comb _ _).1 (comb _ _).2
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination hd
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    have r2 : w (i.succAbove 0) • v + (-v (i.succAbove 0)) • w = 0 := by
      apply Vp_zero i _ (comb _ _).1 (comb _ _).2
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination -hd
    have q1 := hind _ _ r1
    have q2 := hind _ _ r2
    have hv0 : v = 0 := Vp_zero i v hv hvi (neg_eq_zero.mp q2.2) (neg_eq_zero.mp q1.2)
    have q3 := hind 1 0 (by
      rw [hv0]
      simp)
    exact one_ne_zero q3.1
  obtain ⟨p, r, e1, e2⟩ := cramer2 (v (i.succAbove 0)) (v (i.succAbove 1)) (w (i.succAbove 0))
    (w (i.succAbove 1)) (x (i.succAbove 0)) (x (i.succAbove 1)) hdet
  refine ⟨p, r, ?_⟩
  have hd0 : x - (p • v + r • w) = 0 := by
    apply Vp_zero i
    · simp only [tau, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv hw hx ⊢
      linear_combination hx - p * hv - r * hw
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvi, hwi, hxi]
      ring
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e2
  exact sub_eq_zero.mp hd0

theorem Vp_nondeg (i : Fin 4) (u : V4) (hu : tau u = 0) (hui : u i = 0)
    (h : ∀ x : V4, tau x = 0 → x i = 0 → ip u x = 0) : u = 0 := by
  have key : ∀ k : Fin 4, k ≠ i → u k = 0 := by
    intro k hk
    have hx1 : tau (fun a : Fin 4 => (if a = k then (3 : ℂ) else 0) - 1
        + (if a = i then 1 else 0)) = 0 := by
      have e : tau (fun a : Fin 4 => (if a = k then (3 : ℂ) else 0) - 1
          + (if a = i then 1 else 0)) = ∑ a : Fin 4, ((if a = k then (3 : ℂ) else 0) - 1
          + (if a = i then 1 else 0)) := by
        rw [Fin.sum_univ_four]
        rfl
      rw [e]
      norm_num [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hx2 : (fun a : Fin 4 => (if a = k then (3 : ℂ) else 0) - 1
        + (if a = i then 1 else 0)) i = 0 := by
      have hik : ¬ i = k := fun h => hk h.symm
      simp [hik]
    have h0 := h _ hx1 hx2
    have e2 : ip u (fun a : Fin 4 => (if a = k then (3 : ℂ) else 0) - 1
        + (if a = i then 1 else 0)) = ∑ a : Fin 4, u a * ((if a = k then (3 : ℂ) else 0) - 1
        + (if a = i then 1 else 0)) := by
      rw [Fin.sum_univ_four]
      rfl
    rw [e2] at h0
    simp only [mul_add, mul_sub, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h0
    have e3 : ∑ a : Fin 4, u a = 0 := by
      rw [Fin.sum_univ_four]
      exact hu
    rw [e3, hui] at h0
    have h3 : u k * 3 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h3).resolve_right (by norm_num)
  apply Vp_ext i u 0 hui
  · exact key _ (Fin.succAbove_ne i 0)
  · exact key _ (Fin.succAbove_ne i 1)
  · exact key _ (Fin.succAbove_ne i 2)

theorem Vp_t3 (i : Fin 4) (v : V4) (hv : tau v = 0) (hvi : v i = 0) (hvv : ip v v = 0)
    (h3 : t3 v v v = 0) : v = 0 := by
  apply iso34 v hv hvv h3
  have he4 : v 0 * v 1 * v 2 * v 3 = 0 := by
    have h := Finset.prod_eq_zero (Finset.mem_univ i) hvi
    rw [Fin.prod_univ_four] at h
    exact h
  simp only [tau, ip, t3, t4] at hv hvv h3 ⊢
  linear_combination (v 0 + v 1 + v 2 + v 3) * h3
    - (v 0 * v 1 + v 0 * v 2 + v 0 * v 3 + v 1 * v 2 + v 1 * v 3 + v 2 * v 3) * hvv
    + (v 0 * v 1 * v 2 + v 0 * v 1 * v 3 + v 0 * v 2 * v 3 + v 1 * v 2 * v 3) * hv - 4 * he4

theorem rs_row (K : Submodule ℂ M45) (i : Fin 4) (hrow : ∀ Y ∈ K, ∀ j, Y (i, j) = 0)
    (Y : M45) (hY : Y ∈ K) : rs Y i = 0 := by
  rw [rs_apply, hrow Y hY 0, hrow Y hY 1, hrow Y hY 2, hrow Y hY 3, hrow Y hY 4]
  ring

theorem Vp_finrank (i : Fin 4) :
    Module.finrank ℂ (sumZero 4 ⊓ LinearMap.ker (LinearMap.proj i : V4 →ₗ[ℂ] ℂ) :
      Submodule ℂ V4) ≤ 2 := by
  have rn := rank_nullity (sumZero 4) (LinearMap.proj i : V4 →ₗ[ℂ] ℂ)
  have h3 : Module.finrank ℂ (sumZero 4) ≤ 3 :=
    (finrank_sumZero (n := 4) (by norm_num)).trans (by norm_num)
  have hne : Module.finrank ℂ ((sumZero 4).map (LinearMap.proj i : V4 →ₗ[ℂ] ℂ)) ≠ 0 := by
    intro h0
    have hb := Submodule.finrank_eq_zero.mp h0
    have hx : (fun a : Fin 4 => (if a = i then (4 : ℂ) else 0) - 1) ∈ sumZero 4 := by
      rw [mem_sumZero]
      norm_num [Finset.sum_sub_distrib]
    have hm : (LinearMap.proj i : V4 →ₗ[ℂ] ℂ) (fun a : Fin 4 => (if a = i then (4 : ℂ) else 0) - 1)
        ∈ (sumZero 4).map (LinearMap.proj i : V4 →ₗ[ℂ] ℂ) := Submodule.mem_map_of_mem hx
    rw [hb, Submodule.mem_bot] at hm
    norm_num at hm
  have h4 : Module.finrank ℂ (sumZero 4 ⊓ LinearMap.ker (LinearMap.proj i : V4 →ₗ[ℂ] ℂ) :
      Submodule ℂ V4) + Module.finrank ℂ ((sumZero 4).map (LinearMap.proj i : V4 →ₗ[ℂ] ℂ)) ≤ 3 := by
    rw [← rn]
    exact h3
  omega

theorem SL3_rs_le (K : Submodule ℂ M45) (hK : SLev K) (i : Fin 4)
    (hrow : ∀ Y ∈ K, ∀ j, Y (i, j) = 0) :
    K.map rs ≤ (sumZero 4 ⊓ LinearMap.ker (LinearMap.proj i : V4 →ₗ[ℂ] ℂ) : Submodule ℂ V4) := by
  rintro _ ⟨Y, hY, rfl⟩
  refine Submodule.mem_inf.mpr ⟨map_rs_le K hK (Submodule.mem_map_of_mem hY), ?_⟩
  exact LinearMap.mem_ker.mpr (rs_row K i hrow Y hY)

theorem SL3_q2 (K : Submodule ℂ M45) (hK : SLev K) (i : Fin 4)
    (hrow : ∀ Y ∈ K, ∀ j, Y (i, j) = 0) (hq : Module.finrank ℂ (K.map rs) = 2) :
    (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = ⊥ := by
  by_contra hne
  obtain ⟨u, huS, hu0, huperp⟩ := Bii K hK hq hne
  have hle := SL3_rs_le K hK i hrow
  have heq : K.map rs =
      (sumZero 4 ⊓ LinearMap.ker (LinearMap.proj i : V4 →ₗ[ℂ] ℂ) : Submodule ℂ V4) :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [hq]
      exact Vp_finrank i)
  have hu' := Submodule.mem_inf.mp (hle huS)
  have hut : tau u = 0 := (mem_Vs u).mp hu'.1
  have hui : u i = 0 := LinearMap.mem_ker.mp hu'.2
  apply hu0
  apply Vp_nondeg i u hut hui
  intro x hx hxi
  apply huperp
  rw [heq]
  exact Submodule.mem_inf.mpr ⟨(mem_Vs x).mpr hx, LinearMap.mem_ker.mpr hxi⟩

theorem T4col (K : Submodule ℂ M45) (hK : SLev K) (σ : Equiv.Perm (Fin 5)) (Y : M45)
    (hY : Y ∈ K) :
    t3 (col Y (σ 0)) (col Y (σ 1)) (col Y (σ 2)) + t3 (col Y (σ 0)) (col Y (σ 1)) (col Y (σ 3))
      + t3 (col Y (σ 0)) (col Y (σ 2)) (col Y (σ 3))
      + t3 (col Y (σ 1)) (col Y (σ 2)) (col Y (σ 3)) = 0 := by
  have hKσ := SLev_perm σ K hK
  have hYσ : cperm σ Y ∈ K.map (cperm σ) := Submodule.mem_map_of_mem hY
  have k4 := (C34 _ hKσ _ hYσ 4).2.1
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at k4
  exact k4

theorem SL3_two (K : Submodule ℂ M45) (hK : SLev K) (i : Fin 4)
    (hrow : ∀ Y ∈ K, ∀ j, Y (i, j) = 0)
    (hd : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2)
    (z : M45) (hz : z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45))
    (hmax : ∀ Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), ∀ m, ∃ c : ℂ, col Z m = c • col z m)
    (σ : Equiv.Perm (Fin 5)) (v w : V4) (hvw : indep v w) (c0 : col z (σ 0) = v)
    (c1 : col z (σ 1) = (-1 : ℂ) • v) (c2 : col z (σ 2) = w)
    (c3 : col z (σ 3) = (-1 : ℂ) • w) (c4 : col z (σ 4) = 0)
    (id1 : t3 v w w = 0) (id2 : t3 v v w = 0) (Y0 : M45) (hY0 : Y0 ∈ K) : rs Y0 = 0 := by
  have hNs := SLev_N K hK
  have hrs := rs_N K
  have hzK : z ∈ K := (Submodule.mem_inf.mp hz).1
  have hv1 : tau v = 0 := by
    rw [← c0]
    exact C1 K hK z hzK (σ 0)
  have hvi : v i = 0 := by
    rw [← c0]
    exact hrow z hzK (σ 0)
  have hvv : ip v v = 0 := by
    rw [← c0]
    exact Niso _ hNs hrs z z hz hz (σ 0)
  have hw1 : tau w = 0 := by
    rw [← c2]
    exact C1 K hK z hzK (σ 2)
  have hwi : w i = 0 := by
    rw [← c2]
    exact hrow z hzK (σ 2)
  have hww : ip w w = 0 := by
    rw [← c2]
    exact Niso _ hNs hrs z z hz hz (σ 2)
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := (hvw 1 0 (by
      rw [h]
      simp)).1
    exact one_ne_zero h1
  have hw0 : w ≠ 0 := by
    intro h
    have h1 := (hvw 0 1 (by
      rw [h]
      simp)).2
    exact one_ne_zero h1
  have gv : t3 v v v ≠ 0 := fun h => hv0 (Vp_t3 i v hv1 hvi hvv h)
  have gw : t3 w w w ≠ 0 := fun h => hw0 (Vp_t3 i w hw1 hwi hww h)
  have hβ : ip v w ≠ 0 := by
    intro hb
    apply hv0
    apply Vp_nondeg i v hv1 hvi
    intro x hx hxi
    obtain ⟨p, r, rfl⟩ := Vp_span i v w hv1 hvi hw1 hwi hvw x hx hxi
    simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hvv hb ⊢
    linear_combination p * hvv + r * hb
  have keyw : ∀ x : V4, tau x = 0 → x i = 0 → t3 x w w * ip v w = t3 w w w * ip x v := by
    intro x hx hxi
    obtain ⟨p, r, rfl⟩ := Vp_span i v w hv1 hvi hw1 hwi hvw x hx hxi
    simp only [ip, t3, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hvv id1 ⊢
    linear_combination (p * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3)) * id1
      - (p * (w 0 * w 0 * w 0 + w 1 * w 1 * w 1 + w 2 * w 2 * w 2 + w 3 * w 3 * w 3)) * hvv
  have keyv : ∀ x : V4, tau x = 0 → x i = 0 → t3 x v v * ip v w = t3 v v v * ip x w := by
    intro x hx hxi
    obtain ⟨p, r, rfl⟩ := Vp_span i v w hv1 hvi hw1 hwi hvw x hx hxi
    simp only [ip, t3, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hww id2 ⊢
    linear_combination (r * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3)) * id2
      - (r * (v 0 * v 0 * v 0 + v 1 * v 1 * v 1 + v 2 * v 2 * v 2 + v 3 * v 3 * v 3)) * hww
  obtain ⟨W2, hW2, w20, w21, w22, w23⟩ := S7_elem _ hNs hrs hd z hmax σ v w hvw c1 c2 c3 c4
  obtain ⟨W1, hW1, w10, w11, w12, w13⟩ := S7_elem _ hNs hrs hd z hmax (σ * swp) w v
    (indep_symm hvw)
    (by
      rw [Equiv.Perm.mul_apply, swp1]
      exact c3)
    (by
      rw [Equiv.Perm.mul_apply, swp2]
      exact c0)
    (by
      rw [Equiv.Perm.mul_apply, swp3]
      exact c1)
    (by
      rw [Equiv.Perm.mul_apply, swp4]
      exact c4)
  rw [Equiv.Perm.mul_apply, swp0] at w10
  rw [Equiv.Perm.mul_apply, swp1] at w11
  rw [Equiv.Perm.mul_apply, swp2] at w12
  rw [Equiv.Perm.mul_apply, swp3] at w13
  have hW1K : W1 ∈ K := (Submodule.mem_inf.mp hW1).1
  have hW2K : W2 ∈ K := (Submodule.mem_inf.mp hW2).1
  have hyV : ∀ m, tau (col Y0 m) = 0 ∧ col Y0 m i = 0 := fun m =>
    ⟨C1 K hK Y0 hY0 m, hrow Y0 hY0 m⟩
  have cA : ∀ (W : M45) (k : Fin 5), col (Y0 + W) k = col Y0 k + col W k := fun _ _ => rfl
  have cS : ∀ (W : M45) (k : Fin 5), col (Y0 - W) k = col Y0 k - col W k := fun _ _ => rfl
  have A : t3 (col Y0 (σ 0)) w w + t3 (col Y0 (σ 1)) w w = 0 := by
    have tp := T4col K hK σ (Y0 + W2) (K.add_mem hY0 hW2K)
    have tm := T4col K hK σ (Y0 - W2) (K.sub_mem hY0 hW2K)
    have t0 := T4col K hK σ Y0 hY0
    simp only [cA, cS, w20, w21, w22, w23] at tp tm
    simp only [t3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      at tp tm t0 ⊢
    linear_combination (-1 / 2 : ℂ) * (tp + tm - 2 * t0)
  have B : t3 (col Y0 (σ 2)) v v + t3 (col Y0 (σ 3)) v v = 0 := by
    have tp := T4col K hK σ (Y0 + W1) (K.add_mem hY0 hW1K)
    have tm := T4col K hK σ (Y0 - W1) (K.sub_mem hY0 hW1K)
    have t0 := T4col K hK σ Y0 hY0
    simp only [cA, cS, w10, w11, w12, w13] at tp tm
    simp only [t3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      at tp tm t0 ⊢
    linear_combination (-1 / 2 : ℂ) * (tp + tm - 2 * t0)
  have hI : ip (col Y0 (σ 0)) v + ip (col Y0 (σ 1)) v = 0 := by
    have k0 := keyw _ (hyV (σ 0)).1 (hyV (σ 0)).2
    have k1 := keyw _ (hyV (σ 1)).1 (hyV (σ 1)).2
    have h : t3 w w w * (ip (col Y0 (σ 0)) v + ip (col Y0 (σ 1)) v) = 0 := by
      linear_combination (ip v w) * A - k0 - k1
    exact (mul_eq_zero.mp h).resolve_left gw
  have hJ : ip (col Y0 (σ 2)) w + ip (col Y0 (σ 3)) w = 0 := by
    have k0 := keyv _ (hyV (σ 2)).1 (hyV (σ 2)).2
    have k1 := keyv _ (hyV (σ 3)).1 (hyV (σ 3)).2
    have h : t3 v v v * (ip (col Y0 (σ 2)) w + ip (col Y0 (σ 3)) w) = 0 := by
      linear_combination (ip v w) * B - k0 - k1
    exact (mul_eq_zero.mp h).resolve_left gv
  have huv : ip (rs Y0) v = 0 := by
    have x0 := C2pol K hK Y0 W1 hY0 hW1K (σ 0)
    have x1 := C2pol K hK Y0 W1 hY0 hW1K (σ 1)
    rw [w12, hrs W1 hW1] at x0
    rw [w13, hrs W1 hW1] at x1
    simp only [ip, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at x0 x1 hI ⊢
    linear_combination (-1 / 2 : ℂ) * x0 + (1 / 2 : ℂ) * x1 + hI
  have huw : ip (rs Y0) w = 0 := by
    have x0 := C2pol K hK Y0 W2 hY0 hW2K (σ 2)
    have x1 := C2pol K hK Y0 W2 hY0 hW2K (σ 3)
    rw [w22, hrs W2 hW2] at x0
    rw [w23, hrs W2 hW2] at x1
    simp only [ip, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at x0 x1 hJ ⊢
    linear_combination (-1 / 2 : ℂ) * x0 + (1 / 2 : ℂ) * x1 + hJ
  apply Vp_nondeg i (rs Y0) (tau_rs K hK Y0 hY0) (rs_row K i hrow Y0 hY0)
  intro x hx hxi
  obtain ⟨p, r, rfl⟩ := Vp_span i v w hv1 hvi hw1 hwi hvw x hx hxi
  simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at huv huw ⊢
  linear_combination p * huv + r * huw

theorem SL3_d2 (K : Submodule ℂ M45) (hK : SLev K) (i : Fin 4)
    (hrow : ∀ Y ∈ K, ∀ j, Y (i, j) = 0)
    (hd : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2) :
    ∀ Y ∈ K, rs Y = 0 := by
  have hNs := SLev_N K hK
  have hrs := rs_N K
  obtain ⟨z, hz, hmax⟩ := maxpt _ hNs hrs
  have hzK : z ∈ K := (Submodule.mem_inf.mp hz).1
  have hcolV : ∀ m, tau (col z m) = 0 ∧ col z m i = 0 := fun m =>
    ⟨C1 K hK z hzK m, hrow z hzK m⟩
  rcases tricho _ z hmax with ⟨a, b, c, hab, hac, hbc, hind⟩ | ⟨a, b, hab, hspan⟩ |
    ⟨m0, hm0, hform⟩ | hbot
  · exfalso
    by_cases h2 : indep (col z a) (col z b)
    · obtain ⟨p, r, e⟩ := Vp_span i (col z a) (col z b) (hcolV a).1 (hcolV a).2 (hcolV b).1
        (hcolV b).2 h2 (col z c) (hcolV c).1 (hcolV c).2
      have h3 := hind p r (-1) (by
        rw [e]
        funext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        ring)
      exact one_ne_zero (neg_eq_zero.mp h3.2.2)
    · have h2' : ∃ s t : ℂ, s • col z a + t • col z b = 0 ∧ ¬ (s = 0 ∧ t = 0) := by
        by_contra hc
        exact h2 (fun s t e => by
          by_contra hh
          exact hc ⟨s, t, e, hh⟩)
      obtain ⟨s, t, hst, hne⟩ := h2'
      have h3 := hind s t 0 (by
        rw [zero_smul, add_zero]
        exact hst)
      exact hne ⟨h3.1, h3.2.1⟩
  · obtain ⟨σ, h0, h2, e1, e3, e4⟩ := two_line_pattern _ hNs hrs z hz a b hab hspan
    subst h0
    subst h2
    have ids := typeII_ids _ hNs z hz σ (col z (σ 0)) (col z (σ 2)) rfl e1 rfl e3 e4
    intro Y0 hY0
    exact SL3_two K hK i hrow hd z hz hmax σ (col z (σ 0)) (col z (σ 2)) hab rfl e1 rfl e3 e4
      ids.1 ids.2.1 Y0 hY0
  · exfalso
    have hv3 : t3 (col z m0) (col z m0) (col z m0) ≠ 0 := fun h =>
      hm0 (Vp_t3 i _ (hcolV m0).1 (hcolV m0).2 (Niso _ hNs hrs z z hz hz m0) h)
    have h1 := A1b _ hNs hrs (col z m0) hm0 (C1 _ hNs z hz m0)
      (Niso _ hNs hrs z z hz hz m0) hform hv3
    omega
  · exfalso
    rw [hbot, finrank_bot] at hd
    omega

theorem LemmaSL3 (K : Submodule ℂ M45) (hK : SLev K) (i : Fin 4)
    (hrow : ∀ Y ∈ K, ∀ j, Y (i, j) = 0) : Module.finrank ℂ K ≤ 2 := by
  have r := rank_nullity K rs
  have hd := LemA_proof _ (SLev_N K hK) (rs_N K)
  have hq := (Submodule.finrank_mono (SL3_rs_le K hK i hrow)).trans (Vp_finrank i)
  by_cases h2 : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) = 2
  · have h0 := SL3_d2 K hK i hrow h2
    have hb : K.map rs = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨Y, hY, rfl⟩
      rw [Submodule.mem_bot]
      exact h0 Y hY
    rw [hb, finrank_bot] at r
    omega
  · by_cases hq2 : Module.finrank ℂ (K.map rs) = 2
    · have hb := SL3_q2 K hK i hrow hq2
      rw [hb, finrank_bot] at r
      omega
    · omega

def ev (i : Fin 4) (x : ℂ) : V4 := fun k => if k = i then x else 1

theorem pc_ev (i : Fin 4) (x1 x2 x3 x4 : ℂ) :
    pc (ev i x1) (ev i x2) (ev i x3) (ev i x4) = 6 * (x1 + x2 + x3 + x4) := by
  fin_cases i <;>
    simp (config := {decide := true}) only [pc, ev, Fin.sum_univ_four, ite_true, ite_false, add_zero,
      zero_add] <;>
    ring

theorem P4_repl_ones (b : Fin 5) (i : Fin 4) (m : Fin 5 → ℂ) :
    P4 b (repl i m (fun _ => 1)) = 6 * (m (b.succAbove 0) + m (b.succAbove 1)
      + m (b.succAbove 2) + m (b.succAbove 3)) := by
  rw [P4_cols]
  have hc : ∀ j, col (repl i m (fun _ => 1)) j = ev i (m j) := fun j => rfl
  rw [hc, hc, hc, hc]
  exact pc_ev i _ _ _ _

theorem P4_lin (b : Fin 5) (Y : M45) : ∃ A2 A3 A4 : ℂ, ∀ c : ℂ,
    P4 b (fun p => 1 + c * Y p) = 24 + c * (6 * (tau (col Y (b.succAbove 0))
      + tau (col Y (b.succAbove 1)) + tau (col Y (b.succAbove 2))
      + tau (col Y (b.succAbove 3)))) + c ^ 2 * A2 + c ^ 3 * A3 + c ^ 4 * A4 := by
  have h := fun c : ℂ => (P4_cols b (fun p => 1 + c * Y p)).trans
    (pc_expand (col Y (b.succAbove 0)) (col Y (b.succAbove 1)) (col Y (b.succAbove 2))
      (col Y (b.succAbove 3)) c)
  exact ⟨_, _, _, h⟩

theorem inj_succ5 : Function.Injective (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) := by
  intro i j h
  have h' : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := add_right_cancel h
  exact Fin.ext (Nat.cast_injective h')

theorem split_id (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (Y : M45) (hYK : Y ∈ K) (b : Fin 5) :
    (P4 b (fun p => 1 + Y p) - 24) * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4)
      = P4 b (repl i m (fun p => 1 + Y p)) * phiRow i m Y := by
  obtain ⟨θ, hθ⟩ := hdef Y hYK
  obtain ⟨θ1, hθ1⟩ := hdef _ (K.add_mem hYK hsplit)
  have eN : repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p) = fun p => 1 + Y p :=
    repl_self i (fun p => 1 + Y p)
  have eN1 : (fun p : Fin 4 × Fin 5 =>
      1 + (Y + fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) p) =
      repl i ((fun j => 1 + Y (i, j)) + m) (fun p => 1 + Y p) := by
    funext ⟨k, j⟩
    by_cases h : k = i
    · rw [h, repl_at]
      show 1 + (Y (i, j) + if i = i then m j else 0) = 1 + Y (i, j) + m j
      rw [if_pos rfl]
      ring
    · rw [repl_ne i k h]
      show 1 + (Y (k, j) + if k = i then m j else 0) = 1 + Y (k, j)
      rw [if_neg h]
      ring
  have h0 : ∀ b, P4 b (repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p)) = 24 + θ * m b := by
    intro b
    rw [eN]
    exact hθ b
  have hD : ∀ b, P4 b (repl i m (fun p => 1 + Y p)) = (θ1 - θ) * m b := by
    intro b
    have h1 := hθ1 b
    rw [eN1] at h1
    have hadd := P4_repl_add b i (fun j => 1 + Y (i, j)) m (fun p => 1 + Y p)
    linear_combination h1 - h0 b - hadd
  have hs := P4_sym 0 i m (fun j => 1 + Y (i, j)) (fun p => 1 + Y p)
  rw [Fin.sum_univ_five, Fin.sum_univ_five] at hs
  rw [h0 0, h0 1, h0 2, h0 3, h0 4, hD 0, hD 1, hD 2, hD 3, hD 4] at hs
  rw [Fin.sum_univ_five] at hm
  rw [hθ b, hD b, phiRow_apply]
  linear_combination (m b) * hs + (m b * (θ1 - θ - 24)) * hm

theorem split_ker (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hmm : ∑ a, m a * m a ≠ 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (Y : M45) (hY : Y ∈ K) (hcs : ∀ j, ∑ k : Fin 4, Y (k, j) = 0) : phiRow i m Y = 0 := by
  obtain ⟨b0, hb0⟩ : ∃ b, m b ≠ 0 := by
    by_contra hc
    apply hmm
    have hz : ∀ b, m b = 0 := fun b => by
      by_contra hb
      exact hc ⟨b, hb⟩
    simp [hz]
  have htau : ∀ j, tau (col Y j) = 0 := by
    intro j
    have h := hcs j
    rw [Fin.sum_univ_four] at h
    exact h
  obtain ⟨A2, A3, A4, hA⟩ := P4_lin b0 Y
  simp only [htau] at hA
  obtain ⟨d0, d1, d2, d3, d4, hB⟩ := P4_poly b0 (repl i m (fun _ => 1)) (repl i 0 Y)
  have hd0 : d0 = -6 * m b0 := by
    have h := hB 0
    have e : (fun p : Fin 4 × Fin 5 => repl i m (fun _ => 1) p + 0 * repl i 0 Y p) =
        repl i m (fun _ => 1) := by
      funext p
      ring
    rw [e, P4_repl_ones] at h
    have hs := Fin.sum_univ_succAbove m b0
    rw [Fin.sum_univ_four, hm] at hs
    linear_combination (-1 : ℂ) * h - 6 * hs
  have hpoly : ∀ c : ℂ, c ≠ 0 →
      -d0 * phiRow i m Y
        + (A2 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4)
          - d1 * phiRow i m Y) * c
        + (A3 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4)
          - d2 * phiRow i m Y) * c ^ 2
        + (A4 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4)
          - d3 * phiRow i m Y) * c ^ 3
        + (-d4 * phiRow i m Y) * c ^ 4 = 0 := by
    intro c hc
    have h := split_id K m hdef hm i hsplit (c • Y) (K.smul_mem c hY) b0
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • Y) p) = fun p => 1 + c * Y p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
    have e2 : repl i m (fun p => 1 + c * Y p) =
        fun p => repl i m (fun _ => 1) p + c * repl i 0 Y p := by
      funext ⟨k, j⟩
      show repl i m (fun p => 1 + c * Y p) (k, j) =
        repl i m (fun _ => 1) (k, j) + c * repl i 0 Y (k, j)
      by_cases hk : k = i
      · rw [hk, repl_at, repl_at, repl_at]
        simp only [Pi.zero_apply]
        ring
      · rw [repl_ne i k hk, repl_ne i k hk, repl_ne i k hk]
    have e3 : phiRow i m (c • Y) = c * phiRow i m Y := by
      rw [map_smul, smul_eq_mul]
    rw [e1, e2, e3, hA c, hB c] at h
    apply mul_left_cancel₀ hc
    linear_combination h
  have hroots := roots5 (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) inj_succ5
    (-d0 * phiRow i m Y)
    (A2 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4) - d1 * phiRow i m Y)
    (A3 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4) - d2 * phiRow i m Y)
    (A4 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4) - d3 * phiRow i m Y)
    (-d4 * phiRow i m Y) (fun k => hpoly _ (Nat.cast_add_one_ne_zero _))
  have h0 : d0 * phiRow i m Y = 0 := by linear_combination (-1 : ℂ) * hroots.1
  rcases mul_eq_zero.mp h0 with h | h
  · exfalso
    rw [hd0] at h
    have h2 : m b0 = 0 := by linear_combination (-1 / 6 : ℂ) * h
    exact hb0 h2
  · exact h

def csL : M45 →ₗ[ℂ] (Fin 5 → ℂ) := LinearMap.pi (fun j => colsumL j)

theorem ThmSplit_kappa (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hmm : ∑ a, m a * m a ≠ 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K) :
    SLev (K ⊓ LinearMap.ker csL) ∧
      Module.finrank ℂ (K ⊓ LinearMap.ker csL : Submodule ℂ M45) ≤ 3 := by
  have h := (ThmSplit K m hdef hm hmm i hsplit).1
  have hle : (K ⊓ LinearMap.ker csL : Submodule ℂ M45) ≤ K ⊓ LinearMap.ker (phiRow i m) := by
    intro Y hY
    obtain ⟨hYK, hYc⟩ := Submodule.mem_inf.mp hY
    have hc : csL Y = 0 := LinearMap.mem_ker.mp hYc
    refine Submodule.mem_inf.mpr ⟨hYK, LinearMap.mem_ker.mpr ?_⟩
    apply split_ker K m hdef hm hmm i hsplit Y hYK
    intro j
    exact congrFun hc j
  have hS := SLev_mono h hle
  exact ⟨hS, LemmaSL _ hS⟩

def kc1 (a : Fin 5) (B Y : M45) : ℂ :=
  ∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * B (1, e 1) * B (2, e 2) * B (3, e 3)
        + B (0, e 0) * Y (1, e 1) * B (2, e 2) * B (3, e 3)
        + B (0, e 0) * B (1, e 1) * Y (2, e 2) * B (3, e 3)
        + B (0, e 0) * B (1, e 1) * B (2, e 2) * Y (3, e 3) else 0

theorem P4_poly1 (a : Fin 5) (B Y : M45) : ∃ c2 c3 c4 : ℂ, ∀ s : ℂ,
    P4 a (fun p => B p + s * Y p) = P4 a B + kc1 a B Y * s + c2 * s ^ 2 + c3 * s ^ 3
      + c4 * s ^ 4 := by
  refine ⟨(∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * Y (1, e 1) * B (2, e 2) * B (3, e 3)
        + Y (0, e 0) * B (1, e 1) * Y (2, e 2) * B (3, e 3)
        + Y (0, e 0) * B (1, e 1) * B (2, e 2) * Y (3, e 3)
        + B (0, e 0) * Y (1, e 1) * Y (2, e 2) * B (3, e 3)
        + B (0, e 0) * Y (1, e 1) * B (2, e 2) * Y (3, e 3)
        + B (0, e 0) * B (1, e 1) * Y (2, e 2) * Y (3, e 3) else 0),
    (∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * Y (1, e 1) * Y (2, e 2) * B (3, e 3)
        + Y (0, e 0) * Y (1, e 1) * B (2, e 2) * Y (3, e 3)
        + Y (0, e 0) * B (1, e 1) * Y (2, e 2) * Y (3, e 3)
        + B (0, e 0) * Y (1, e 1) * Y (2, e 2) * Y (3, e 3) else 0),
    (∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
        Y (0, e 0) * Y (1, e 1) * Y (2, e 2) * Y (3, e 3) else 0), fun s => ?_⟩
  simp only [P4, kc1]
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs
  · ring
  · ring

theorem kc1_eq (a : Fin 5) (B Y : M45) : kc1 a B Y =
    P4 a (repl 0 (fun j => Y (0, j)) B) + P4 a (repl 1 (fun j => Y (1, j)) B)
      + P4 a (repl 2 (fun j => Y (2, j)) B) + P4 a (repl 3 (fun j => Y (3, j)) B) := by
  simp only [kc1, P4]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [repl_at, repl_ne 0 1 (by decide), repl_ne 0 2 (by decide), repl_ne 0 3 (by decide), repl_ne 1 0 (by decide), repl_ne 1 2 (by decide), repl_ne 1 3 (by decide), repl_ne 2 0 (by decide), repl_ne 2 1 (by decide), repl_ne 2 3 (by decide), repl_ne 3 0 (by decide), repl_ne 3 1 (by decide), repl_ne 3 2 (by decide)]
  split_ifs
  · ring
  · ring

theorem P4_zero_row (a : Fin 5) (N : M45) (i : Fin 4) (h : ∀ j, N (i, j) = 0) : P4 a N = 0 := by
  rw [P4_prod]
  apply Finset.sum_eq_zero
  intro e _
  have hz : ∏ k, N (k, e k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h (e i))
  rw [hz]
  simp

def ev2 (k i : Fin 4) (y x : ℂ) : V4 := fun a => if a = k then y else if a = i then x else 1

theorem pc_ev2_0 (i : Fin 4) (hki : (0 : Fin 4) ≠ i) (y1 y2 y3 y4 x1 x2 x3 x4 : ℂ) :
    pc (ev2 0 i y1 x1) (ev2 0 i y2 x2) (ev2 0 i y3 x3) (ev2 0 i y4 x4) =
      2 * (y1 * (x2 + x3 + x4) + y2 * (x1 + x3 + x4) + y3 * (x1 + x2 + x4)
        + y4 * (x1 + x2 + x3)) := by
  fin_cases i <;>
    first
    | exact absurd rfl hki
    | (simp (config := {decide := true}) only [pc, ev2, Fin.sum_univ_four, ite_true, ite_false, add_zero,
        zero_add] <;> ring)

theorem pc_ev2_1 (i : Fin 4) (hki : (1 : Fin 4) ≠ i) (y1 y2 y3 y4 x1 x2 x3 x4 : ℂ) :
    pc (ev2 1 i y1 x1) (ev2 1 i y2 x2) (ev2 1 i y3 x3) (ev2 1 i y4 x4) =
      2 * (y1 * (x2 + x3 + x4) + y2 * (x1 + x3 + x4) + y3 * (x1 + x2 + x4)
        + y4 * (x1 + x2 + x3)) := by
  fin_cases i <;>
    first
    | exact absurd rfl hki
    | (simp (config := {decide := true}) only [pc, ev2, Fin.sum_univ_four, ite_true, ite_false, add_zero,
        zero_add] <;> ring)

theorem pc_ev2_2 (i : Fin 4) (hki : (2 : Fin 4) ≠ i) (y1 y2 y3 y4 x1 x2 x3 x4 : ℂ) :
    pc (ev2 2 i y1 x1) (ev2 2 i y2 x2) (ev2 2 i y3 x3) (ev2 2 i y4 x4) =
      2 * (y1 * (x2 + x3 + x4) + y2 * (x1 + x3 + x4) + y3 * (x1 + x2 + x4)
        + y4 * (x1 + x2 + x3)) := by
  fin_cases i <;>
    first
    | exact absurd rfl hki
    | (simp (config := {decide := true}) only [pc, ev2, Fin.sum_univ_four, ite_true, ite_false, add_zero,
        zero_add] <;> ring)

theorem pc_ev2_3 (i : Fin 4) (hki : (3 : Fin 4) ≠ i) (y1 y2 y3 y4 x1 x2 x3 x4 : ℂ) :
    pc (ev2 3 i y1 x1) (ev2 3 i y2 x2) (ev2 3 i y3 x3) (ev2 3 i y4 x4) =
      2 * (y1 * (x2 + x3 + x4) + y2 * (x1 + x3 + x4) + y3 * (x1 + x2 + x4)
        + y4 * (x1 + x2 + x3)) := by
  fin_cases i <;>
    first
    | exact absurd rfl hki
    | (simp (config := {decide := true}) only [pc, ev2, Fin.sum_univ_four, ite_true, ite_false, add_zero,
        zero_add] <;> ring)

theorem pc_ev2 (k i : Fin 4) (hki : k ≠ i) (y1 y2 y3 y4 x1 x2 x3 x4 : ℂ) :
    pc (ev2 k i y1 x1) (ev2 k i y2 x2) (ev2 k i y3 x3) (ev2 k i y4 x4) =
      2 * (y1 * (x2 + x3 + x4) + y2 * (x1 + x3 + x4) + y3 * (x1 + x2 + x4)
        + y4 * (x1 + x2 + x3)) := by
  fin_cases k
  · exact pc_ev2_0 i hki y1 y2 y3 y4 x1 x2 x3 x4
  · exact pc_ev2_1 i hki y1 y2 y3 y4 x1 x2 x3 x4
  · exact pc_ev2_2 i hki y1 y2 y3 y4 x1 x2 x3 x4
  · exact pc_ev2_3 i hki y1 y2 y3 y4 x1 x2 x3 x4

theorem P4_repl2 (b : Fin 5) (k i : Fin 4) (hki : k ≠ i) (y m : Fin 5 → ℂ) :
    P4 b (repl k y (repl i m (fun _ => 1))) =
      2 * (y (b.succAbove 0) * (m (b.succAbove 1) + m (b.succAbove 2) + m (b.succAbove 3))
        + y (b.succAbove 1) * (m (b.succAbove 0) + m (b.succAbove 2) + m (b.succAbove 3))
        + y (b.succAbove 2) * (m (b.succAbove 0) + m (b.succAbove 1) + m (b.succAbove 3))
        + y (b.succAbove 3) * (m (b.succAbove 0) + m (b.succAbove 1) + m (b.succAbove 2))) := by
  rw [P4_cols]
  have hc : ∀ j, col (repl k y (repl i m (fun _ => 1))) j = ev2 k i (y j) (m j) := fun j => rfl
  rw [hc, hc, hc, hc]
  exact pc_ev2 k i hki _ _ _ _ _ _ _ _

theorem d1_term (b : Fin 5) (i k : Fin 4) (m : Fin 5 → ℂ) (Y : M45) :
    P4 b (repl k (fun j => repl i 0 Y (k, j)) (repl i m (fun _ => 1))) =
      2 * (repl i 0 Y (k, b.succAbove 0)
          * (m (b.succAbove 1) + m (b.succAbove 2) + m (b.succAbove 3))
        + repl i 0 Y (k, b.succAbove 1)
          * (m (b.succAbove 0) + m (b.succAbove 2) + m (b.succAbove 3))
        + repl i 0 Y (k, b.succAbove 2)
          * (m (b.succAbove 0) + m (b.succAbove 1) + m (b.succAbove 3))
        + repl i 0 Y (k, b.succAbove 3)
          * (m (b.succAbove 0) + m (b.succAbove 1) + m (b.succAbove 2))) := by
  by_cases hk : k = i
  · rw [hk]
    have hz : ∀ j, repl i 0 Y (i, j) = 0 := fun j => repl_at i 0 Y j
    have h0 := P4_zero_row b (repl i (fun j => repl i 0 Y (i, j)) (repl i m (fun _ => 1))) i
      (fun j => by
        rw [repl_at]
        exact hz j)
    rw [h0, hz, hz, hz, hz]
    ring
  · exact P4_repl2 b k i hk (fun j => repl i 0 Y (k, j)) m

theorem kc1_formula (b : Fin 5) (i : Fin 4) (m : Fin 5 → ℂ) (Y : M45) :
    kc1 b (repl i m (fun _ => 1)) (repl i 0 Y) =
      2 * (tau (col (repl i 0 Y) (b.succAbove 0))
          * (m (b.succAbove 1) + m (b.succAbove 2) + m (b.succAbove 3))
        + tau (col (repl i 0 Y) (b.succAbove 1))
          * (m (b.succAbove 0) + m (b.succAbove 2) + m (b.succAbove 3))
        + tau (col (repl i 0 Y) (b.succAbove 2))
          * (m (b.succAbove 0) + m (b.succAbove 1) + m (b.succAbove 3))
        + tau (col (repl i 0 Y) (b.succAbove 3))
          * (m (b.succAbove 0) + m (b.succAbove 1) + m (b.succAbove 2))) := by
  rw [kc1_eq, d1_term b i 0 m Y, d1_term b i 1 m Y, d1_term b i 2 m Y, d1_term b i 3 m Y]
  simp only [tau, col]
  ring

theorem split_eig (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (Y : M45) (hYK : Y ∈ K) :
    ∃ μ : ℂ, ∀ b, P4 b (repl i m (fun p => 1 + Y p)) = μ * m b := by
  obtain ⟨θ, hθ⟩ := hdef Y hYK
  obtain ⟨θ1, hθ1⟩ := hdef _ (K.add_mem hYK hsplit)
  have eN : repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p) = fun p => 1 + Y p :=
    repl_self i (fun p => 1 + Y p)
  have eN1 : (fun p : Fin 4 × Fin 5 =>
      1 + (Y + fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) p) =
      repl i ((fun j => 1 + Y (i, j)) + m) (fun p => 1 + Y p) := by
    funext ⟨k, j⟩
    by_cases h : k = i
    · rw [h, repl_at]
      show 1 + (Y (i, j) + if i = i then m j else 0) = 1 + Y (i, j) + m j
      rw [if_pos rfl]
      ring
    · rw [repl_ne i k h]
      show 1 + (Y (k, j) + if k = i then m j else 0) = 1 + Y (k, j)
      rw [if_neg h]
      ring
  have h0 : ∀ b, P4 b (repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p)) = 24 + θ * m b := by
    intro b
    rw [eN]
    exact hθ b
  refine ⟨θ1 - θ, fun b => ?_⟩
  have h1 := hθ1 b
  rw [eN1] at h1
  have hadd := P4_repl_add b i (fun j => 1 + Y (i, j)) m (fun p => 1 + Y p)
  linear_combination h1 - h0 b - hadd

theorem ncol_lin (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (Y : M45) (hY : Y ∈ K) (b b' : Fin 5) :
    m b' * kc1 b (repl i m (fun _ => 1)) (repl i 0 Y) =
      m b * kc1 b' (repl i m (fun _ => 1)) (repl i 0 Y) := by
  obtain ⟨p2, p3, p4, hp⟩ := P4_poly1 b (repl i m (fun _ => 1)) (repl i 0 Y)
  obtain ⟨q2, q3, q4, hq⟩ := P4_poly1 b' (repl i m (fun _ => 1)) (repl i 0 Y)
  have hall : ∀ c : ℂ,
      (m b' * P4 b (repl i m (fun _ => 1)) - m b * P4 b' (repl i m (fun _ => 1)))
      + (m b' * kc1 b (repl i m (fun _ => 1)) (repl i 0 Y)
          - m b * kc1 b' (repl i m (fun _ => 1)) (repl i 0 Y)) * c
      + (m b' * p2 - m b * q2) * c ^ 2 + (m b' * p3 - m b * q3) * c ^ 3
      + (m b' * p4 - m b * q4) * c ^ 4 = 0 := by
    intro c
    obtain ⟨μ, hμ⟩ := split_eig K m hdef i hsplit (c • Y) (K.smul_mem c hY)
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • Y) p) = fun p => 1 + c * Y p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
    have e2 : repl i m (fun p => 1 + c * Y p) =
        fun p => repl i m (fun _ => 1) p + c * repl i 0 Y p := by
      funext ⟨k, j⟩
      show repl i m (fun p => 1 + c * Y p) (k, j) =
        repl i m (fun _ => 1) (k, j) + c * repl i 0 Y (k, j)
      by_cases hk : k = i
      · rw [hk, repl_at, repl_at, repl_at]
        simp only [Pi.zero_apply]
        ring
      · rw [repl_ne i k hk, repl_ne i k hk, repl_ne i k hk]
    have h1 := hμ b
    have h2 := hμ b'
    rw [e1, e2, hp c] at h1
    rw [e1, e2, hq c] at h2
    linear_combination (m b') * h1 - (m b) * h2
  have hr := roots5 (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) inj_succ5
    (m b' * P4 b (repl i m (fun _ => 1)) - m b * P4 b' (repl i m (fun _ => 1)))
    (m b' * kc1 b (repl i m (fun _ => 1)) (repl i 0 Y)
      - m b * kc1 b' (repl i m (fun _ => 1)) (repl i 0 Y))
    (m b' * p2 - m b * q2) (m b' * p3 - m b * q3) (m b' * p4 - m b * q4) (fun k => hall _)
  linear_combination hr.2.1

theorem tau_repl0 (i : Fin 4) (Y : M45) (b : Fin 5) :
    tau (col Y b) = Y (i, b) + tau (col (repl i 0 Y) b) := by
  have e1 : tau (col Y b) = ∑ k : Fin 4, Y (k, b) := by
    rw [Fin.sum_univ_four]
    rfl
  have e2 : tau (col (repl i 0 Y) b) = ∑ k : Fin 4, (if k = i then (0 : ℂ) else Y (k, b)) := by
    rw [Fin.sum_univ_four]
    rfl
  have e3 : ∑ k : Fin 4, Y (k, b) = ∑ k : Fin 4, ((if k = i then Y (i, b) else 0)
      + (if k = i then (0 : ℂ) else Y (k, b))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : k = i
    · rw [if_pos h, if_pos h, h, add_zero]
    · rw [if_neg h, if_neg h, zero_add]
  rw [e1, e2, e3, Finset.sum_add_distrib]
  simp

theorem NCOL_S_a (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hmm : ∑ a, m a * m a ≠ 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (hm0 : ∀ j, m j ≠ 0) :
    (∀ Y ∈ (K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45), ∀ j, Y (i, j) = 0) ∧
      Module.finrank ℂ K ≤ 3 := by
  have hS := (ThmSplit K m hdef hm hmm i hsplit).1
  have hrow : ∀ Y ∈ (K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45), ∀ j, Y (i, j) = 0 := by
    intro Y hY
    have hYK : Y ∈ K := (Submodule.mem_inf.mp hY).1
    have E0 := kc1_formula 0 i m Y
    have E1 := kc1_formula 1 i m Y
    have E2 := kc1_formula 2 i m Y
    have E3 := kc1_formula 3 i m Y
    have E4 := kc1_formula 4 i m Y
    rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at E0
    rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at E1
    rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at E2
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at E3
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at E4
    have L1 := ncol_lin K m hdef i hsplit Y hYK 1 0
    have L2 := ncol_lin K m hdef i hsplit Y hYK 2 0
    have L3 := ncol_lin K m hdef i hsplit Y hYK 3 0
    have L4 := ncol_lin K m hdef i hsplit Y hYK 4 0
    obtain ⟨c, hc⟩ : ∃ c : Fin 5 → ℂ, ∀ j, tau (col (repl i 0 Y) j) = c j :=
      ⟨fun j => tau (col (repl i 0 Y) j), fun j => rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : Fin 5 → ℂ,
        ∀ b, kc1 b (repl i m (fun _ => 1)) (repl i 0 Y) = D b :=
      ⟨fun b => kc1 b (repl i m (fun _ => 1)) (repl i 0 Y), fun b => rfl⟩
    simp only [hc, hD] at E0 E1 E2 E3 E4 L1 L2 L3 L4
    have hm' := hm
    rw [Fin.sum_univ_five] at hm'
    have hcm : c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4 = 0 := by
      apply mul_left_cancel₀ (hm0 0)
      linear_combination (m 0 * (c 0 + c 1 + c 2 + c 3 + c 4) - D 0 / 6) * hm'
        + (m 0 / 6) * (E0 + E1 + E2 + E3 + E4) - (1 / 6 : ℂ) * (L1 + L2 + L3 + L4)
    have hc1 : c 1 = c 0 := by
      have h : 4 * m 0 * m 1 * (c 1 - c 0) = 0 := by
        linear_combination L1 - m 0 * E1 + m 1 * E0
          - 2 * (m 0 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 1) - m 1 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 0)) * hm' - 2 * (m 1 - m 0) * hcm
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · norm_num at h3
          · exact (hm0 0 h3).elim
        · exact (hm0 1 h'').elim
      · exact sub_eq_zero.mp h'
    have hc2 : c 2 = c 0 := by
      have h : 4 * m 0 * m 2 * (c 2 - c 0) = 0 := by
        linear_combination L2 - m 0 * E2 + m 2 * E0
          - 2 * (m 0 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 2) - m 2 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 0)) * hm' - 2 * (m 2 - m 0) * hcm
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · norm_num at h3
          · exact (hm0 0 h3).elim
        · exact (hm0 2 h'').elim
      · exact sub_eq_zero.mp h'
    have hc3 : c 3 = c 0 := by
      have h : 4 * m 0 * m 3 * (c 3 - c 0) = 0 := by
        linear_combination L3 - m 0 * E3 + m 3 * E0
          - 2 * (m 0 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 3) - m 3 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 0)) * hm' - 2 * (m 3 - m 0) * hcm
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · norm_num at h3
          · exact (hm0 0 h3).elim
        · exact (hm0 3 h'').elim
      · exact sub_eq_zero.mp h'
    have hc4 : c 4 = c 0 := by
      have h : 4 * m 0 * m 4 * (c 4 - c 0) = 0 := by
        linear_combination L4 - m 0 * E4 + m 4 * E0
          - 2 * (m 0 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 4) - m 4 * (c 0 + c 1 + c 2 + c 3 + c 4 - c 0)) * hm' - 2 * (m 4 - m 0) * hcm
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · norm_num at h3
          · exact (hm0 0 h3).elim
        · exact (hm0 4 h'').elim
      · exact sub_eq_zero.mp h'
    have hcb : ∀ b, c b = c 0 := fin5 (fun b => c b = c 0) rfl hc1 hc2 hc3 hc4
    have hC1 := C1 _ hS Y hY
    have hyi : ∀ b, Y (i, b) = -c 0 := by
      intro b
      have h1 := hC1 b
      rw [tau_repl0 i Y b, hc b, hcb b] at h1
      linear_combination h1
    by_cases hα : c 0 = 0
    · intro j
      rw [hyi j, hα, neg_zero]
    · exfalso
      have hY1 : (1 / c 0) • Y ∈ (K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45) :=
        Submodule.smul_mem _ _ hY
      have h24 := hS _ hY1 0
      have hz := P4_zero_row 0 (fun p => 1 + ((1 / c 0) • Y) p) i (fun j => by
        show 1 + (1 / c 0) * Y (i, j) = 0
        rw [hyi j]
        have h1 : 1 / c 0 * c 0 = 1 := one_div_mul_cancel hα
        linear_combination (-1 : ℂ) * h1)
      rw [hz] at h24
      norm_num at h24
  refine ⟨hrow, ?_⟩
  have h3 := LemmaSL3 _ hS i hrow
  have rn := rank_nullity K (phiRow i m)
  have h1 : Module.finrank ℂ (K.map (phiRow i m)) ≤ 1 := by
    have h := Submodule.finrank_le (K.map (phiRow i m))
    rw [Module.finrank_self] at h
    exact h
  omega

theorem ncol_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (Y : M45) (hYK : Y ∈ K) :
    ∃ c D : Fin 5 → ℂ, (∀ j, tau (col (repl i 0 Y) j) = c j) ∧
      (∀ b, D b = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * m b + 4 * c b * m b - 2 * (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4)) ∧
      (∀ b b', m b' * D b = m b * D b') := by
  have E0 := kc1_formula 0 i m Y
  have E1 := kc1_formula 1 i m Y
  have E2 := kc1_formula 2 i m Y
  have E3 := kc1_formula 3 i m Y
  have E4 := kc1_formula 4 i m Y
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at E0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at E1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at E2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at E3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at E4
  obtain ⟨c, hc⟩ : ∃ c : Fin 5 → ℂ, ∀ j, tau (col (repl i 0 Y) j) = c j :=
    ⟨fun j => tau (col (repl i 0 Y) j), fun j => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Fin 5 → ℂ,
      ∀ b, kc1 b (repl i m (fun _ => 1)) (repl i 0 Y) = D b :=
    ⟨fun b => kc1 b (repl i m (fun _ => 1)) (repl i 0 Y), fun b => rfl⟩
  simp only [hc, hD] at E0 E1 E2 E3 E4
  have hm' := hm
  rw [Fin.sum_univ_five] at hm'
  have g0 : D 0 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * m 0 + 4 * c 0 * m 0 - 2 * (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4) := by
    linear_combination E0 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 0) * hm'
  have g1 : D 1 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * m 1 + 4 * c 1 * m 1 - 2 * (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4) := by
    linear_combination E1 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 1) * hm'
  have g2 : D 2 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * m 2 + 4 * c 2 * m 2 - 2 * (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4) := by
    linear_combination E2 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 2) * hm'
  have g3 : D 3 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * m 3 + 4 * c 3 * m 3 - 2 * (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4) := by
    linear_combination E3 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 3) * hm'
  have g4 : D 4 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * m 4 + 4 * c 4 * m 4 - 2 * (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4) := by
    linear_combination E4 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 4) * hm'
  refine ⟨c, D, hc, fin5 (fun b => D b = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * m b + 4 * c b * m b - 2 * (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4)) g0 g1 g2 g3 g4, fun b b' => ?_⟩
  have h := ncol_lin K m hdef i hsplit Y hYK b b'
  rw [hD b, hD b'] at h
  exact h

theorem ncol_b1 (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hmm : ∑ a, m a * m a ≠ 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (Y : M45) (hYK : Y ∈ K) :
    ∃ α : ℂ, ∀ b, m b ≠ 0 → tau (col (repl i 0 Y) b) = α := by
  obtain ⟨c, D, hc, G, L⟩ := ncol_core K m hdef hm i hsplit Y hYK
  obtain ⟨b0, hb0⟩ : ∃ b, m b ≠ 0 := by
    by_contra hcon
    apply hmm
    have hz : ∀ b, m b = 0 := fun b => by
      by_contra hb
      exact hcon ⟨b, hb⟩
    simp [hz]
  have hm' := hm
  rw [Fin.sum_univ_five] at hm'
  have hcm : (c 0 * m 0 + c 1 * m 1 + c 2 * m 2 + c 3 * m 3 + c 4 * m 4) = 0 := by
    apply mul_left_cancel₀ hb0
    linear_combination (-1 / 6 : ℂ) * (L 0 b0 + L 1 b0 + L 2 b0 + L 3 b0 + L 4 b0)
      - (D b0 / 6) * hm' + (m b0 / 6) * (G 0 + G 1 + G 2 + G 3 + G 4)
      - (m b0 * (c 0 + c 1 + c 2 + c 3 + c 4) / 3) * hm'
  refine ⟨c b0, fun b hb => ?_⟩
  rw [hc b]
  have h : 4 * m b * m b0 * (c b - c b0) = 0 := by
    linear_combination L b b0 - m b0 * G b + m b * G b0 + 2 * (m b0 - m b) * hcm
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · norm_num at h3
      · exact (hb h3).elim
    · exact (hb0 h'').elim
  · exact sub_eq_zero.mp h'

theorem P4_zero_row' (a : Fin 5) (N : M45) (i : Fin 4) (h : ∀ j, j ≠ a → N (i, j) = 0) :
    P4 a N = 0 := by
  rw [P4_prod]
  apply Finset.sum_eq_zero
  intro e _
  split_ifs with hcond
  · have hi : e i ≠ a := by
      fin_cases i
      · exact hcond.1
      · exact hcond.2.1
      · exact hcond.2.2.1
      · exact hcond.2.2.2
    exact Finset.prod_eq_zero (Finset.mem_univ i) (h (e i) hi)
  · rfl

theorem NCOL_S_b (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hmm : ∑ a, m a * m a ≠ 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (n : Fin 5) (hn' : ∀ j, j ≠ n → m j ≠ 0) :
    (∀ Y ∈ (K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45), ∀ j, j ≠ n → Y (i, j) = 0) ∧
    SLev ((K ⊓ LinearMap.ker (phiRow i m)) ⊓
      LinearMap.ker (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ)) ∧
    Module.finrank ℂ ((K ⊓ LinearMap.ker (phiRow i m)) ⊓
      LinearMap.ker (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ) : Submodule ℂ M45) ≤ 2 ∧
    (Module.finrank ℂ K = 4 → Module.finrank ℂ ((K ⊓ LinearMap.ker (phiRow i m)) ⊓
      LinearMap.ker (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ) : Submodule ℂ M45) = 2) := by
  have hS := (ThmSplit K m hdef hm hmm i hsplit).1
  have hsup : ∀ Y ∈ (K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45), ∀ j, j ≠ n →
      Y (i, j) = 0 := by
    intro Y hY
    have hYK : Y ∈ K := (Submodule.mem_inf.mp hY).1
    obtain ⟨α, hα⟩ := ncol_b1 K m hdef hm hmm i hsplit Y hYK
    have hC1 := C1 _ hS Y hY
    have hyi : ∀ b, b ≠ n → Y (i, b) = -α := by
      intro b hb
      have h1 := hC1 b
      rw [tau_repl0 i Y b, hα b (hn' b hb)] at h1
      linear_combination h1
    by_cases h0 : α = 0
    · intro j hj
      rw [hyi j hj, h0, neg_zero]
    · exfalso
      have hY1 : (1 / α) • Y ∈ (K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45) :=
        Submodule.smul_mem _ _ hY
      have h24 := hS _ hY1 n
      have hz := P4_zero_row' n (fun p => 1 + ((1 / α) • Y) p) i (fun j hj => by
        show 1 + (1 / α) * Y (i, j) = 0
        rw [hyi j hj]
        have h1 : 1 / α * α = 1 := one_div_mul_cancel h0
        linear_combination (-1 : ℂ) * h1)
      rw [hz] at h24
      norm_num at h24
  have hS2 : SLev ((K ⊓ LinearMap.ker (phiRow i m)) ⊓
      LinearMap.ker (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ)) := SLev_mono hS inf_le_left
  have hrow : ∀ Y ∈ ((K ⊓ LinearMap.ker (phiRow i m)) ⊓
      LinearMap.ker (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ) : Submodule ℂ M45),
      ∀ j, Y (i, j) = 0 := by
    intro Y hY j
    obtain ⟨hY1, hY2⟩ := Submodule.mem_inf.mp hY
    by_cases hj : j = n
    · rw [hj]
      exact LinearMap.mem_ker.mp hY2
    · exact hsup Y hY1 j hj
  have h2 := LemmaSL3 _ hS2 i hrow
  refine ⟨hsup, hS2, h2, fun h4 => ?_⟩
  have rn := rank_nullity K (phiRow i m)
  have h1 : Module.finrank ℂ (K.map (phiRow i m)) ≤ 1 := by
    have h := Submodule.finrank_le (K.map (phiRow i m))
    rw [Module.finrank_self] at h
    exact h
  have rn2 := rank_nullity (K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45)
    (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ)
  have h1' : Module.finrank ℂ ((K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45).map
      (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ)) ≤ 1 := by
    have h := Submodule.finrank_le ((K ⊓ LinearMap.ker (phiRow i m) : Submodule ℂ M45).map
      (LinearMap.proj (i, n) : M45 →ₗ[ℂ] ℂ))
    rw [Module.finrank_self] at h
    exact h
  omega

def rowL (i : Fin 4) : M45 →ₗ[ℂ] (Fin 5 → ℂ) := LinearMap.funLeft ℂ ℂ (fun j : Fin 5 => (i, j))

def fsMap (i : Fin 4) (Cs : Submodule ℂ (Fin 5 → ℂ)) : M45 →ₗ[ℂ] Module.Dual ℂ Cs :=
  (Submodule.dualRestrict Cs).comp (dotL.flip.comp (rowL i))

theorem fsMap_apply (i : Fin 4) (Cs : Submodule ℂ (Fin 5 → ℂ)) (Y : M45) (v : Fin 5 → ℂ)
    (hv : v ∈ Cs) : fsMap i Cs Y ⟨v, hv⟩ =
      v 0 * Y (i, 0) + v 1 * Y (i, 1) + v 2 * Y (i, 2) + v 3 * Y (i, 3) + v 4 * Y (i, 4) := rfl

theorem ThmFS (K : Submodule ℂ M45) (Cs : Submodule ℂ (Fin 5 → ℂ))
    (hdefC : ∀ Y ∈ K, (fun a => P4 a (fun p => 1 + Y p) - 24) ∈ Cs)
    (hC1 : ∀ u ∈ Cs, ∑ a, u a = 0) (i : Fin 4)
    (hsplit : ∀ u ∈ Cs, (fun p : Fin 4 × Fin 5 => if p.1 = i then u p.2 else 0) ∈ K)
    (hnd : ∀ x ∈ Cs, (∀ u ∈ Cs, ∑ a, u a * x a = 0) → x = 0) :
    SLev (K ⊓ LinearMap.ker (fsMap i Cs)) ∧
      Module.finrank ℂ K ≤ 3 + Module.finrank ℂ Cs := by
  have hS : SLev (K ⊓ LinearMap.ker (fsMap i Cs)) := by
    intro Y hY a
    obtain ⟨hYK, hYψ⟩ := Submodule.mem_inf.mp hY
    have hψ : fsMap i Cs Y = 0 := LinearMap.mem_ker.mp hYψ
    have hc := hdefC Y hYK
    have eN : repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p) = fun p => 1 + Y p :=
      repl_self i (fun p => 1 + Y p)
    have key : ∀ u ∈ Cs, ∑ b, u b * (P4 b (fun p => 1 + Y p) - 24) = 0 := by
      intro u hu
      have hE := hdefC _ (K.add_mem hYK (hsplit u hu))
      have eN1 : (fun p : Fin 4 × Fin 5 =>
          1 + (Y + fun p : Fin 4 × Fin 5 => if p.1 = i then u p.2 else 0) p) =
          repl i ((fun j => 1 + Y (i, j)) + u) (fun p => 1 + Y p) := by
        funext ⟨k, j⟩
        by_cases h : k = i
        · rw [h, repl_at]
          show 1 + (Y (i, j) + if i = i then u j else 0) = 1 + Y (i, j) + u j
          rw [if_pos rfl]
          ring
        · rw [repl_ne i k h]
          show 1 + (Y (k, j) + if k = i then u j else 0) = 1 + Y (k, j)
          rw [if_neg h]
          ring
      have hDu : (fun b => P4 b (repl i u (fun p => 1 + Y p))) ∈ Cs := by
        have e : (fun b => P4 b (repl i u (fun p => 1 + Y p))) =
            (fun a => P4 a (fun p : Fin 4 × Fin 5 =>
              1 + (Y + fun p : Fin 4 × Fin 5 => if p.1 = i then u p.2 else 0) p) - 24)
            - (fun a => P4 a (fun p => 1 + Y p) - 24) := by
          funext b
          have hadd := P4_repl_add b i (fun j => 1 + Y (i, j)) u (fun p => 1 + Y p)
          rw [eN] at hadd
          show P4 b (repl i u (fun p => 1 + Y p)) =
            (P4 b (fun p : Fin 4 × Fin 5 =>
              1 + (Y + fun p : Fin 4 × Fin 5 => if p.1 = i then u p.2 else 0) p) - 24)
            - (P4 b (fun p => 1 + Y p) - 24)
          rw [eN1]
          linear_combination (-1 : ℂ) * hadd
        rw [e]
        exact Cs.sub_mem hE hc
      have hs := P4_sym 0 i u (fun j => 1 + Y (i, j)) (fun p => 1 + Y p)
      rw [eN] at hs
      have h1 := hC1 _ hDu
      have h2 := fsMap_apply i Cs Y _ hDu
      rw [hψ] at h2
      have h3 := hC1 u hu
      rw [Fin.sum_univ_five] at h1 h3 hs ⊢
      rw [Fin.sum_univ_five] at hs
      have h2' : P4 0 (repl i u (fun p => 1 + Y p)) * Y (i, 0)
          + P4 1 (repl i u (fun p => 1 + Y p)) * Y (i, 1)
          + P4 2 (repl i u (fun p => 1 + Y p)) * Y (i, 2)
          + P4 3 (repl i u (fun p => 1 + Y p)) * Y (i, 3)
          + P4 4 (repl i u (fun p => 1 + Y p)) * Y (i, 4) = 0 := h2.symm
      linear_combination hs - 24 * h3 + h1 + h2'
    have hz := hnd _ hc key
    have hza := congrFun hz a
    have hza' : P4 a (fun p => 1 + Y p) - 24 = 0 := hza
    linear_combination hza'
  refine ⟨hS, ?_⟩
  have rn := rank_nullity K (fsMap i Cs)
  have h1 : Module.finrank ℂ (K.map (fsMap i Cs)) ≤ Module.finrank ℂ Cs := by
    have h := Submodule.finrank_le (K.map (fsMap i Cs))
    rw [Subspace.dual_finrank_eq] at h
    exact h
  have h3 := LemmaSL _ hS
  omega

def uY (Y : M45) : V4 := fun k => (Y (k, 0) + Y (k, 1)) / 2

def dY (Y : M45) : V4 := fun k => (Y (k, 0) - Y (k, 1)) / 2

def e2 (d : V4) : ℂ := (tau d ^ 2 - ip d d) / 2

def Ed (d : V4) : V4 := fun k => e2 d - tau d * d k + d k ^ 2

theorem TC5_sum (Y : M45) :
    P4 0 (fun p => 1 + Y p) + P4 1 (fun p => 1 + Y p) =
      2 * pc (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 3)) (fun k => 1 + Y (k, 4)) := by
  rw [P4_c0, P4_c1]
  simp (config := {decide := true}) only [pc, col, uY, dY, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  ring

theorem TC5_diff (Y : M45) :
    P4 1 (fun p => 1 + Y p) - P4 0 (fun p => 1 + Y p) =
      2 * pc (dY Y) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 3)) (fun k => 1 + Y (k, 4)) := by
  rw [P4_c0, P4_c1]
  simp (config := {decide := true}) only [pc, col, uY, dY, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  ring

theorem TC5_n2 (Y : M45) :
    P4 2 (fun p => 1 + Y p) = pc (fun k => 1 + uY Y k) (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 3)) (fun k => 1 + Y (k, 4)) - pc (dY Y) (dY Y) (fun k => 1 + Y (k, 3)) (fun k => 1 + Y (k, 4)) := by
  rw [P4_c2]
  simp (config := {decide := true}) only [pc, col, uY, dY, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  ring

theorem TC5_n3 (Y : M45) :
    P4 3 (fun p => 1 + Y p) = pc (fun k => 1 + uY Y k) (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 4)) - pc (dY Y) (dY Y) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 4)) := by
  rw [P4_c3]
  simp (config := {decide := true}) only [pc, col, uY, dY, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  ring

theorem TC5_n4 (Y : M45) :
    P4 4 (fun p => 1 + Y p) = pc (fun k => 1 + uY Y k) (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 3)) - pc (dY Y) (dY Y) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 3)) := by
  rw [P4_c4]
  simp (config := {decide := true}) only [pc, col, uY, dY, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  ring

theorem TC5_dd (d a b : V4) :
    pc d d (fun k => 1 + a k) (fun k => 1 + b k) =
      4 * e2 d + 2 * ip (a + b) (Ed d) + pc d d a b := by
  simp (config := {decide := true}) only [pc, e2, Ed, tau, ip, Pi.add_apply, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

def mTC : Fin 5 → ℂ := fun a => if a = 0 then 1 else if a = 1 then -1 else 0

theorem TC5_normal (K : Submodule ℂ M45) :
    DefLine K mTC ↔ ∀ Y ∈ K,
      pc (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 3)) (fun k => 1 + Y (k, 4)) = 24 ∧
      pc (fun k => 1 + uY Y k) (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 3)) (fun k => 1 + Y (k, 4)) - pc (dY Y) (dY Y) (fun k => 1 + Y (k, 3)) (fun k => 1 + Y (k, 4)) = 24 ∧
      pc (fun k => 1 + uY Y k) (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 4)) - pc (dY Y) (dY Y) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 4)) = 24 ∧
      pc (fun k => 1 + uY Y k) (fun k => 1 + uY Y k) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 3)) - pc (dY Y) (dY Y) (fun k => 1 + Y (k, 2)) (fun k => 1 + Y (k, 3)) = 24 := by
  have m0 : mTC 0 = 1 := by simp [mTC]
  have m1 : mTC 1 = -1 := by simp [mTC]
  have m2 : mTC 2 = 0 := by simp [mTC]
  have m3 : mTC 3 = 0 := by simp [mTC]
  have m4 : mTC 4 = 0 := by simp [mTC]
  constructor
  · intro h Y hY
    obtain ⟨θ, hθ⟩ := h Y hY
    have c0 := hθ 0
    have c1 := hθ 1
    have c2 := hθ 2
    have c3 := hθ 3
    have c4 := hθ 4
    rw [m0] at c0
    rw [m1] at c1
    rw [m2] at c2
    rw [m3] at c3
    rw [m4] at c4
    have t1 := TC5_sum Y
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-1 / 2 : ℂ) * t1 + (1 / 2 : ℂ) * c0 + (1 / 2 : ℂ) * c1
    · rw [← TC5_n2]
      linear_combination c2
    · rw [← TC5_n3]
      linear_combination c3
    · rw [← TC5_n4]
      linear_combination c4
  · intro h Y hY
    obtain ⟨h1, h2, h3, h4⟩ := h Y hY
    refine ⟨P4 0 (fun p => 1 + Y p) - 24, ?_⟩
    apply fin5
    · show P4 0 (fun p => 1 + Y p) = 24 + (P4 0 (fun p => 1 + Y p) - 24) * mTC 0
      rw [m0]
      ring
    · show P4 1 (fun p => 1 + Y p) = 24 + (P4 0 (fun p => 1 + Y p) - 24) * mTC 1
      rw [m1]
      have t1 := TC5_sum Y
      linear_combination t1 + 2 * h1
    · show P4 2 (fun p => 1 + Y p) = 24 + (P4 0 (fun p => 1 + Y p) - 24) * mTC 2
      rw [m2, TC5_n2]
      linear_combination h2
    · show P4 3 (fun p => 1 + Y p) = 24 + (P4 0 (fun p => 1 + Y p) - 24) * mTC 3
      rw [m3, TC5_n3]
      linear_combination h3
    · show P4 4 (fun p => 1 + Y p) = 24 + (P4 0 (fun p => 1 + Y p) - 24) * mTC 4
      rw [m4, TC5_n4]
      linear_combination h4

def qA1 (Y : M45) (b : Fin 5) : ℂ :=
  6 * (tau (col Y (b.succAbove 0)) + tau (col Y (b.succAbove 1)) + tau (col Y (b.succAbove 2)) + tau (col Y (b.succAbove 3)))

def qA2 (Y : M45) (b : Fin 5) : ℂ :=
  2 * (tau (col Y (b.succAbove 0)) * tau (col Y (b.succAbove 1)) + tau (col Y (b.succAbove 0)) * tau (col Y (b.succAbove 2)) + tau (col Y (b.succAbove 0)) * tau (col Y (b.succAbove 3)) + tau (col Y (b.succAbove 1)) * tau (col Y (b.succAbove 2)) + tau (col Y (b.succAbove 1)) * tau (col Y (b.succAbove 3)) + tau (col Y (b.succAbove 2)) * tau (col Y (b.succAbove 3)))
    - 2 * (ip (col Y (b.succAbove 0)) (col Y (b.succAbove 1)) + ip (col Y (b.succAbove 0)) (col Y (b.succAbove 2)) + ip (col Y (b.succAbove 0)) (col Y (b.succAbove 3)) + ip (col Y (b.succAbove 1)) (col Y (b.succAbove 2)) + ip (col Y (b.succAbove 1)) (col Y (b.succAbove 3)) + ip (col Y (b.succAbove 2)) (col Y (b.succAbove 3)))

theorem P4_quad (b : Fin 5) (Y : M45) : ∃ A3 A4 : ℂ, ∀ c : ℂ,
    P4 b (fun p => 1 + c * Y p) = 24 + c * qA1 Y b + c ^ 2 * qA2 Y b + c ^ 3 * A3
      + c ^ 4 * A4 := by
  have h := fun c : ℂ => (P4_cols b (fun p => 1 + c * Y p)).trans
    (pc_expand (col Y (b.succAbove 0)) (col Y (b.succAbove 1)) (col Y (b.succAbove 2))
      (col Y (b.succAbove 3)) c)
  exact ⟨_, _, h⟩

theorem qb_lin (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m) (Y : M45)
    (hY : Y ∈ K) (b b' : Fin 5) :
    m b' * qA1 Y b = m b * qA1 Y b' ∧ m b' * qA2 Y b = m b * qA2 Y b' := by
  obtain ⟨p3, p4, hp⟩ := P4_quad b Y
  obtain ⟨q3, q4, hq⟩ := P4_quad b' Y
  have hall : ∀ c : ℂ, 0 + (m b' * qA1 Y b - m b * qA1 Y b') * c
      + (m b' * qA2 Y b - m b * qA2 Y b') * c ^ 2 + (m b' * p3 - m b * q3) * c ^ 3
      + (m b' * p4 - m b * q4) * c ^ 4 = 0 := by
    intro c
    obtain ⟨θ, hθ⟩ := hdef (c • Y) (K.smul_mem c hY)
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • Y) p) = fun p => 1 + c * Y p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
    have h1 := hθ b
    have h2 := hθ b'
    rw [e1, hp c] at h1
    rw [e1, hq c] at h2
    linear_combination (m b') * h1 - (m b) * h2
  have hr := roots5 (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) inj_succ5 0
    (m b' * qA1 Y b - m b * qA1 Y b') (m b' * qA2 Y b - m b * qA2 Y b')
    (m b' * p3 - m b * q3) (m b' * p4 - m b * q4) (fun k => hall _)
  exact ⟨by linear_combination hr.2.1, by linear_combination hr.2.2.1⟩

theorem qA1_eq (Y : M45) : ∀ b, qA1 Y b = 6 * ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y b)) := by
  apply fin5
  · show qA1 Y 0 = 6 * ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 0))
    simp only [qA1, sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2]
    ring
  · show qA1 Y 1 = 6 * ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 1))
    simp only [qA1, sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2]
    ring
  · show qA1 Y 2 = 6 * ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 2))
    simp only [qA1, sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2]
    ring
  · show qA1 Y 3 = 6 * ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 3))
    simp only [qA1, sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2]
    ring
  · show qA1 Y 4 = 6 * ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 4))
    simp only [qA1, sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2]
    ring

theorem qA2_eq (Y : M45) : ∀ b, qA2 Y b =
    ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y b)) ^ 2 - ((tau (col Y 0) ^ 2 + tau (col Y 1) ^ 2 + tau (col Y 2) ^ 2 + tau (col Y 3) ^ 2 + tau (col Y 4) ^ 2) - tau (col Y b) ^ 2) - ip (rs Y) (rs Y)
      + 2 * ip (rs Y) (col Y b) - 2 * ip (col Y b) (col Y b) + (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2) + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4)) := by
  apply fin5
  · show qA2 Y 0 =
      ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 0)) ^ 2 - ((tau (col Y 0) ^ 2 + tau (col Y 1) ^ 2 + tau (col Y 2) ^ 2 + tau (col Y 3) ^ 2 + tau (col Y 4) ^ 2) - tau (col Y 0) ^ 2) - ip (rs Y) (rs Y)
      + 2 * ip (rs Y) (col Y 0) - 2 * ip (col Y 0) (col Y 0) + (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2) + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4))
    simp only [qA2, sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2, tau, ip, col, rs_apply]
    ring
  · show qA2 Y 1 =
      ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 1)) ^ 2 - ((tau (col Y 0) ^ 2 + tau (col Y 1) ^ 2 + tau (col Y 2) ^ 2 + tau (col Y 3) ^ 2 + tau (col Y 4) ^ 2) - tau (col Y 1) ^ 2) - ip (rs Y) (rs Y)
      + 2 * ip (rs Y) (col Y 1) - 2 * ip (col Y 1) (col Y 1) + (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2) + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4))
    simp only [qA2, sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2, tau, ip, col, rs_apply]
    ring
  · show qA2 Y 2 =
      ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 2)) ^ 2 - ((tau (col Y 0) ^ 2 + tau (col Y 1) ^ 2 + tau (col Y 2) ^ 2 + tau (col Y 3) ^ 2 + tau (col Y 4) ^ 2) - tau (col Y 2) ^ 2) - ip (rs Y) (rs Y)
      + 2 * ip (rs Y) (col Y 2) - 2 * ip (col Y 2) (col Y 2) + (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2) + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4))
    simp only [qA2, sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2, tau, ip, col, rs_apply]
    ring
  · show qA2 Y 3 =
      ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 3)) ^ 2 - ((tau (col Y 0) ^ 2 + tau (col Y 1) ^ 2 + tau (col Y 2) ^ 2 + tau (col Y 3) ^ 2 + tau (col Y 4) ^ 2) - tau (col Y 3) ^ 2) - ip (rs Y) (rs Y)
      + 2 * ip (rs Y) (col Y 3) - 2 * ip (col Y 3) (col Y 3) + (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2) + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4))
    simp only [qA2, sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2, tau, ip, col, rs_apply]
    ring
  · show qA2 Y 4 =
      ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) - tau (col Y 4)) ^ 2 - ((tau (col Y 0) ^ 2 + tau (col Y 1) ^ 2 + tau (col Y 2) ^ 2 + tau (col Y 3) ^ 2 + tau (col Y 4) ^ 2) - tau (col Y 4) ^ 2) - ip (rs Y) (rs Y)
      + 2 * ip (rs Y) (col Y 4) - 2 * ip (col Y 4) (col Y 4) + (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2) + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4))
    simp only [qA2, sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2, tau, ip, col, rs_apply]
    ring

theorem LemmaQB (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (Y : M45) (hY : Y ∈ K) :
    ∃ κ θ2 : ℂ, (∀ j, tau (col Y j) = κ * m j) ∧
      (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2)
        + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4) =
        ip (rs Y) (rs Y) + κ ^ 2 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4)) ∧
      (∀ j, ip (col Y j) (col Y j) - ip (rs Y) (col Y j) - κ ^ 2 * m j ^ 2
        = -(θ2 / 2) * m j) := by
  obtain ⟨b0, hb0⟩ := Function.ne_iff.mp hm0
  have hb0' : m b0 ≠ 0 := hb0
  have hsum0 : ip (rs Y) (col Y 0) + ip (rs Y) (col Y 1) + ip (rs Y) (col Y 2)
      + ip (rs Y) (col Y 3) + ip (rs Y) (col Y 4) = ip (rs Y) (rs Y) := by
    simp only [ip, col, rs_apply]
    ring
  have B1 := qA1_eq Y
  have B2 := qA2_eq Y
  have L := fun b => qb_lin K m hdef Y hY b b0
  obtain ⟨t, ht⟩ : ∃ t : Fin 5 → ℂ, ∀ j, tau (col Y j) = t j :=
    ⟨fun j => tau (col Y j), fun j => rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Fin 5 → ℂ, ∀ j, ip (col Y j) (col Y j) = I j :=
    ⟨fun j => ip (col Y j) (col Y j), fun j => rfl⟩
  obtain ⟨sy, hsy⟩ : ∃ sy : Fin 5 → ℂ, ∀ j, ip (rs Y) (col Y j) = sy j :=
    ⟨fun j => ip (rs Y) (col Y j), fun j => rfl⟩
  obtain ⟨ss, hss⟩ : ∃ ss : ℂ, ip (rs Y) (rs Y) = ss := ⟨ip (rs Y) (rs Y), rfl⟩
  simp only [ht, hI, hsy, hss] at B1 B2 hsum0
  have L1 : ∀ b, m b0 * (6 * ((t 0 + t 1 + t 2 + t 3 + t 4) - t b)) = m b * (6 * ((t 0 + t 1 + t 2 + t 3 + t 4) - t b0)) := by
    intro b
    have h := (L b).1
    rw [B1 b, B1 b0] at h
    exact h
  have L2 : ∀ b, m b0 * (((t 0 + t 1 + t 2 + t 3 + t 4) - t b) ^ 2 - ((t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 + t 4 ^ 2) - t b ^ 2) - ss + 2 * sy b - 2 * I b + (I 0 + I 1 + I 2 + I 3 + I 4)) =
      m b * (((t 0 + t 1 + t 2 + t 3 + t 4) - t b0) ^ 2 - ((t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 + t 4 ^ 2) - t b0 ^ 2) - ss + 2 * sy b0 - 2 * I b0 + (I 0 + I 1 + I 2 + I 3 + I 4)) := by
    intro b
    have h := (L b).2
    rw [B2 b, B2 b0] at h
    exact h
  have hm' := hm
  rw [Fin.sum_univ_five] at hm'
  have hT : (t 0 + t 1 + t 2 + t 3 + t 4) = 0 := by
    apply mul_left_cancel₀ hb0'
    linear_combination (1 / 24 : ℂ) * (L1 0 + L1 1 + L1 2 + L1 3 + L1 4)
      + (1 / 4 : ℂ) * ((t 0 + t 1 + t 2 + t 3 + t 4) - t b0) * hm'
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ * m b0 = t b0 := ⟨t b0 / m b0, div_mul_cancel₀ _ hb0'⟩
  have hτ : ∀ b, t b = κ * m b := by
    intro b
    apply mul_left_cancel₀ hb0'
    linear_combination (m b0 - m b) * hT - (1 / 6 : ℂ) * L1 b - m b * hκ
  obtain ⟨θ2, hθ⟩ : ∃ θ2 : ℂ, θ2 * m b0 = ((t 0 + t 1 + t 2 + t 3 + t 4) - t b0) ^ 2 - ((t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 + t 4 ^ 2) - t b0 ^ 2) - ss + 2 * sy b0 - 2 * I b0 + (I 0 + I 1 + I 2 + I 3 + I 4) :=
    ⟨(((t 0 + t 1 + t 2 + t 3 + t 4) - t b0) ^ 2 - ((t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 + t 4 ^ 2) - t b0 ^ 2) - ss + 2 * sy b0 - 2 * I b0 + (I 0 + I 1 + I 2 + I 3 + I 4)) / m b0, div_mul_cancel₀ _ hb0'⟩
  have R : ∀ b, ((t 0 + t 1 + t 2 + t 3 + t 4) - t b) ^ 2 - ((t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 + t 4 ^ 2) - t b ^ 2) - ss + 2 * sy b - 2 * I b + (I 0 + I 1 + I 2 + I 3 + I 4) = θ2 * m b := by
    intro b
    apply mul_left_cancel₀ hb0'
    linear_combination L2 b - m b * hθ
  have ha : (I 0 + I 1 + I 2 + I 3 + I 4) = ss + κ ^ 2 * (m 0 * m 0 + m 1 * m 1 + m 2 * m 2 + m 3 * m 3 + m 4 * m 4) := by
    linear_combination (1 / 3 : ℂ) * (R 0 + R 1 + R 2 + R 3 + R 4) + (θ2 / 3) * hm'
      - (t 0 + t 1 + t 2 + t 3 + t 4) * hT - (2 / 3 : ℂ) * hsum0 + (t 0 + κ * m 0) * hτ 0 + (t 1 + κ * m 1) * hτ 1 + (t 2 + κ * m 2) * hτ 2 + (t 3 + κ * m 3) * hτ 3 + (t 4 + κ * m 4) * hτ 4
  refine ⟨κ, θ2, fun j => (ht j).trans (hτ j), ?_, fun j => ?_⟩
  · simp only [hI, hss]
    linear_combination ha
  · rw [hI j, hsy j]
    linear_combination (-1 / 2 : ℂ) * R j + (1 / 2 : ℂ) * ((t 0 + t 1 + t 2 + t 3 + t 4) - 2 * t j) * hT
      + (t j + κ * m j) * hτ j - (1 / 2 : ℂ) * ((t 0 + κ * m 0) * hτ 0 + (t 1 + κ * m 1) * hτ 1 + (t 2 + κ * m 2) * hτ 2 + (t 3 + κ * m 3) * hτ 3 + (t 4 + κ * m 4) * hτ 4) + (1 / 2 : ℂ) * ha

theorem Lev45_quad (K : Submodule ℂ M45) (hK : Lev45 K) (Y : M45) (hY : Y ∈ K) :
    (tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4) = 0) ∧
    (ip (col Y 0) (col Y 0) + ip (col Y 1) (col Y 1) + ip (col Y 2) (col Y 2)
      + ip (col Y 3) (col Y 3) + ip (col Y 4) (col Y 4) = ip (rs Y) (rs Y)
      + (tau (col Y 0) ^ 2 + tau (col Y 1) ^ 2 + tau (col Y 2) ^ 2 + tau (col Y 3) ^ 2
        + tau (col Y 4) ^ 2)) := by
  obtain ⟨a3, a4, h0⟩ := P4_quad 0 Y
  obtain ⟨b3, b4, h1⟩ := P4_quad 1 Y
  obtain ⟨c3, c4, h2⟩ := P4_quad 2 Y
  obtain ⟨d3, d4, h3⟩ := P4_quad 3 Y
  obtain ⟨e3, e4, h4⟩ := P4_quad 4 Y
  have hall : ∀ c : ℂ, 0 + (qA1 Y 0 + qA1 Y 1 + qA1 Y 2 + qA1 Y 3 + qA1 Y 4) * c
      + (qA2 Y 0 + qA2 Y 1 + qA2 Y 2 + qA2 Y 3 + qA2 Y 4) * c ^ 2
      + (a3 + b3 + c3 + d3 + e3) * c ^ 3 + (a4 + b4 + c4 + d4 + e4) * c ^ 4 = 0 := by
    intro c
    have h := hK (c • Y) (K.smul_mem c hY)
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • Y) p) = fun p => 1 + c * Y p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [e1, Fin.sum_univ_five, h0 c, h1 c, h2 c, h3 c, h4 c] at h
    linear_combination h
  have hr := roots5 (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) inj_succ5 0
    (qA1 Y 0 + qA1 Y 1 + qA1 Y 2 + qA1 Y 3 + qA1 Y 4)
    (qA2 Y 0 + qA2 Y 1 + qA2 Y 2 + qA2 Y 3 + qA2 Y 4)
    (a3 + b3 + c3 + d3 + e3) (a4 + b4 + c4 + d4 + e4) (fun k => hall _)
  have s1 := hr.2.1
  have s2 := hr.2.2.1
  rw [qA1_eq Y 0, qA1_eq Y 1, qA1_eq Y 2, qA1_eq Y 3, qA1_eq Y 4] at s1
  rw [qA2_eq Y 0, qA2_eq Y 1, qA2_eq Y 2, qA2_eq Y 3, qA2_eq Y 4] at s2
  have hsum0 : ip (rs Y) (col Y 0) + ip (rs Y) (col Y 1) + ip (rs Y) (col Y 2)
      + ip (rs Y) (col Y 3) + ip (rs Y) (col Y 4) = ip (rs Y) (rs Y) := by
    simp only [ip, col, rs_apply]
    ring
  have hT : (tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) = 0 := by
    linear_combination (1 / 24 : ℂ) * s1
  refine ⟨hT, ?_⟩
  linear_combination (1 / 3 : ℂ) * s2 - (tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)) * hT - (2 / 3 : ℂ) * hsum0

def rowE (i : Fin 4) (u : Fin 5 → ℂ) : M45 := fun p => if p.1 = i then u p.2 else 0

theorem one_add_rowE (i : Fin 4) (u : Fin 5 → ℂ) :
    (fun p : Fin 4 × Fin 5 => 1 + rowE i u p) = repl i (fun j => 1 + u j) (fun _ => 1) := by
  funext ⟨k, j⟩
  by_cases h : k = i
  · rw [h, repl_at]
    show 1 + (if i = i then u j else 0) = 1 + u j
    rw [if_pos rfl]
  · rw [repl_ne i k h]
    show 1 + (if k = i then u j else 0) = 1
    rw [if_neg h, add_zero]

theorem one_add_rowE2 (i k : Fin 4) (hik : i ≠ k) (u u' : Fin 5 → ℂ) :
    (fun p : Fin 4 × Fin 5 => 1 + (rowE i u + rowE k u') p) =
      repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1)) := by
  funext ⟨a, j⟩
  by_cases h : a = i
  · rw [h, repl_at]
    show 1 + ((if i = i then u j else 0) + (if i = k then u' j else 0)) = 1 + u j
    rw [if_pos rfl, if_neg hik, add_zero]
  · rw [repl_ne i a h]
    by_cases h2 : a = k
    · rw [h2, repl_at]
      show 1 + ((if k = i then u j else 0) + (if k = k then u' j else 0)) = 1 + u' j
      rw [if_neg (Ne.symm hik), if_pos rfl, zero_add]
    · rw [repl_ne k a h2]
      show 1 + ((if a = i then u j else 0) + (if a = k then u' j else 0)) = 1
      rw [if_neg h, if_neg h2, add_zero, add_zero]

theorem single_row_sum (K : Submodule ℂ M45) (hK : Lev45 K) (i : Fin 4) (u : Fin 5 → ℂ)
    (hE : rowE i u ∈ K) : u 0 + u 1 + u 2 + u 3 + u 4 = 0 := by
  have h := hK _ hE
  rw [one_add_rowE, Fin.sum_univ_five, P4_repl_ones, P4_repl_ones, P4_repl_ones, P4_repl_ones,
    P4_repl_ones] at h
  simp only [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2, sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2, sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2, sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2, sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at h
  linear_combination (1 / 24 : ℂ) * h

theorem single_row_perp (K : Submodule ℂ M45) (hK : Lev45 K) (i k : Fin 4) (hik : i ≠ k)
    (u u' : Fin 5 → ℂ) (hE : rowE i u ∈ K) (hE' : rowE k u' ∈ K) :
    u 0 * u' 0 + u 1 * u' 1 + u 2 * u' 2 + u 3 * u' 3 + u 4 * u' 4 = 0 := by
  have hU := single_row_sum K hK i u hE
  have hU' := single_row_sum K hK k u' hE'
  have h := hK _ (K.add_mem hE hE')
  rw [one_add_rowE2 i k hik, Fin.sum_univ_five, P4_repl2 0 i k hik, P4_repl2 1 i k hik,
    P4_repl2 2 i k hik, P4_repl2 3 i k hik, P4_repl2 4 i k hik] at h
  simp only [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2, sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2, sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2, sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2, sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at h
  linear_combination (-1 / 6 : ℂ) * h + 4 * hU + 4 * hU' + (u 0 + u 1 + u 2 + u 3 + u 4) * hU'

theorem single_row_defC (K : Submodule ℂ M45) (hK : Lev45 K) (i : Fin 4) (u : Fin 5 → ℂ)
    (hE : rowE i u ∈ K) : u ∈ defC K := by
  have hU := single_row_sum K hK i u hE
  have g0 : (fun a => P4 a (fun p : Fin 4 × Fin 5 => 1 + (0 : M45) p)) ∈ defC K :=
    Submodule.subset_span ⟨0, K.zero_mem, rfl⟩
  have gE : (fun a => P4 a (fun p : Fin 4 × Fin 5 => 1 + rowE i u p)) ∈ defC K :=
    Submodule.subset_span ⟨rowE i u, hE, rfl⟩
  have e0 : (fun a => P4 a (fun p : Fin 4 × Fin 5 => 1 + (0 : M45) p)) = fun _ => 24 := by
    funext a
    have e1 : (fun p : Fin 4 × Fin 5 => (1 : ℂ) + (0 : M45) p) = fun _ => 1 := by
      funext p
      simp
    rw [e1, P4_ones]
  have eE : ∀ b, P4 b (fun p : Fin 4 × Fin 5 => 1 + rowE i u p) = 24 - 6 * u b := by
    intro b
    rw [one_add_rowE, P4_repl_ones]
    show 6 * ((1 + u (b.succAbove 0)) + (1 + u (b.succAbove 1)) + (1 + u (b.succAbove 2))
      + (1 + u (b.succAbove 3))) = 24 - 6 * u b
    have hs := Fin.sum_univ_succAbove u b
    rw [Fin.sum_univ_five, Fin.sum_univ_four] at hs
    linear_combination 6 * hU - 6 * hs
  have hu : u = (1 / 6 : ℂ) • ((fun a => P4 a (fun p : Fin 4 × Fin 5 => 1 + (0 : M45) p))
      - (fun a => P4 a (fun p : Fin 4 × Fin 5 => 1 + rowE i u p))) := by
    rw [e0]
    funext b
    show u b = (1 / 6 : ℂ) * (24 - P4 b (fun p : Fin 4 × Fin 5 => 1 + rowE i u p))
    rw [eE b]
    ring
  rw [hu]
  exact (defC K).smul_mem _ ((defC K).sub_mem g0 gE)

theorem single_row_t3 (K : Submodule ℂ M45) (hK : Lev45 K) (i k l : Fin 4) (hik : i ≠ k)
    (hil : i ≠ l) (hkl : k ≠ l) (u u' u'' : Fin 5 → ℂ) (hE : rowE i u ∈ K)
    (hE' : rowE k u' ∈ K) (hE'' : rowE l u'' ∈ K) :
    u 0 * u' 0 * u'' 0 + u 1 * u' 1 * u'' 1 + u 2 * u' 2 * u'' 2 + u 3 * u' 3 * u'' 3
      + u 4 * u' 4 * u'' 4 = 0 := by
  have hU := single_row_sum K hK i u hE
  have hU' := single_row_sum K hK k u' hE'
  have hU'' := single_row_sum K hK l u'' hE''
  have huu'' := single_row_perp K hK i l hil u u'' hE hE''
  have hu'u'' := single_row_perp K hK k l hkl u' u'' hE' hE''
  have hNl : (fun j => (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) (l, j)) = fun _ => 1 := by
    funext j
    rw [repl_ne i l (Ne.symm hil), repl_ne k l (Ne.symm hkl)]
  have eN : repl l (fun _ => 1) (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) = (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) := by
    have h := repl_self l (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1)))
    rw [hNl] at h
    exact h
  have e3 : (fun p : Fin 4 × Fin 5 => 1 + (rowE i u + rowE k u' + rowE l u'') p) =
      repl l ((fun _ => 1) + u'') (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) := by
    funext ⟨a, j⟩
    by_cases h : a = l
    · rw [h, repl_at]
      show 1 + ((if l = i then u j else 0) + (if l = k then u' j else 0)
        + (if l = l then u'' j else 0)) = 1 + u'' j
      rw [if_neg (Ne.symm hil), if_neg (Ne.symm hkl), if_pos rfl, zero_add, zero_add]
    · rw [repl_ne l a h]
      have h2 := congrFun (one_add_rowE2 i k hik u u') (a, j)
      rw [← h2]
      show 1 + ((if a = i then u j else 0) + (if a = k then u' j else 0)
        + (if a = l then u'' j else 0)) = 1 + ((if a = i then u j else 0)
        + (if a = k then u' j else 0))
      rw [if_neg h, add_zero]
  have h3 := hK _ (K.add_mem (K.add_mem hE hE') hE'')
  rw [e3, Fin.sum_univ_five] at h3
  have h2 := hK _ (K.add_mem hE hE')
  rw [one_add_rowE2 i k hik, Fin.sum_univ_five] at h2
  have ha : ∀ b, P4 b (repl l ((fun _ => 1) + u'') (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1)))) =
      P4 b (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) + P4 b (repl l u'' (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1)))) := by
    intro b
    have h := P4_repl_add b l (fun _ => 1) u'' (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1)))
    rw [eN] at h
    exact h
  have hsym := P4_sym 0 l (fun _ => 1) u'' (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1)))
  rw [eN, Fin.sum_univ_five, Fin.sum_univ_five] at hsym
  rw [ha 0, ha 1, ha 2, ha 3, ha 4] at h3
  have hw : u'' 0 * P4 0 (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) + u'' 1 * P4 1 (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) + u'' 2 * P4 2 (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1)))
      + u'' 3 * P4 3 (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) + u'' 4 * P4 4 (repl i (fun j => 1 + u j) (repl k (fun j => 1 + u' j) (fun _ => 1))) = 0 := by
    linear_combination h3 - h2 - hsym
  rw [P4_repl2 0 i k hik, P4_repl2 1 i k hik, P4_repl2 2 i k hik, P4_repl2 3 i k hik,
    P4_repl2 4 i k hik] at hw
  simp only [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2, sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2, sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2, sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2, sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at hw
  linear_combination (1 / 4 : ℂ) * hw
    - (1 / 2 : ℂ) * (12 + 3 * (u 0 + u 1 + u 2 + u 3 + u 4) + 3 * (u' 0 + u' 1 + u' 2 + u' 3 + u' 4) + (u 0 + u 1 + u 2 + u 3 + u 4) * (u' 0 + u' 1 + u' 2 + u' 3 + u' 4) - (u 0 * u' 0 + u 1 * u' 1 + u 2 * u' 2 + u 3 * u' 3 + u 4 * u' 4)) * hU''
    + (3 / 2 : ℂ) * huu'' + (3 / 2 : ℂ) * hu'u'' + (1 / 2 : ℂ) * (u 0 + u 1 + u 2 + u 3 + u 4) * hu'u''
    + (1 / 2 : ℂ) * (u' 0 + u' 1 + u' 2 + u' 3 + u' 4) * huu''

def zrow (i : Fin 4) : M45 →ₗ[ℂ] M45 where
  toFun Y := fun p => if p.1 = i then 0 else Y p
  map_add' Y Y' := by
    funext p
    by_cases h : p.1 = i
    · simp only [Pi.add_apply, if_pos h, add_zero]
    · simp only [Pi.add_apply, if_neg h]
  map_smul' c Y := by
    funext p
    by_cases h : p.1 = i
    · simp only [Pi.smul_apply, if_pos h, smul_zero, RingHom.id_apply]
    · simp only [Pi.smul_apply, if_neg h, RingHom.id_apply]

theorem one_add_zrow (i : Fin 4) (Y : M45) :
    (fun p : Fin 4 × Fin 5 => 1 + zrow i Y p) = repl i (fun _ => 1) (fun p => 1 + Y p) := by
  funext ⟨k, j⟩
  by_cases h : k = i
  · rw [h, repl_at]
    show 1 + (if i = i then (0 : ℂ) else Y (i, j)) = 1
    rw [if_pos rfl, add_zero]
  · rw [repl_ne i k h]
    show 1 + (if k = i then (0 : ℂ) else Y (k, j)) = 1 + Y (k, j)
    rw [if_neg h]

theorem FL45_core (K : Submodule ℂ M45) (hK : Lev45 K) (i : Fin 4)
    (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → rowE i w ∈ K) (Y : M45) (hY : Y ∈ K) :
    (∀ b, P4 b (repl i (fun _ => 1) (fun p => 1 + Y p)) = P4 0 (repl i (fun _ => 1) (fun p => 1 + Y p))) ∧
    (5 + (Y (i, 0) + Y (i, 1) + Y (i, 2) + Y (i, 3) + Y (i, 4))) * P4 0 (repl i (fun _ => 1) (fun p => 1 + Y p)) = 120 := by
  have gen : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 →
      ∑ b, (1 + Y (i, b) + w b) * P4 b (repl i (fun _ => 1) (fun p => 1 + Y p)) = 120 := by
    intro w hw
    have h := hK _ (K.add_mem hY (hF w hw))
    have eN1 : (fun p : Fin 4 × Fin 5 => 1 + (Y + rowE i w) p) =
        repl i (fun j => 1 + Y (i, j) + w j) (fun p => 1 + Y p) := by
      funext ⟨k, j⟩
      by_cases hk : k = i
      · rw [hk, repl_at]
        show 1 + (Y (i, j) + if i = i then w j else 0) = 1 + Y (i, j) + w j
        rw [if_pos rfl]
        ring
      · rw [repl_ne i k hk]
        show 1 + (Y (k, j) + if k = i then w j else 0) = 1 + Y (k, j)
        rw [if_neg hk, add_zero]
    rw [eN1] at h
    have hs := P4_sym 0 i (fun _ => 1) (fun j => 1 + Y (i, j) + w j) (fun p => 1 + Y p)
    rw [Fin.sum_univ_five] at h
    rw [Fin.sum_univ_five, Fin.sum_univ_five] at hs
    rw [Fin.sum_univ_five]
    linear_combination h - hs
  have g0 : ∑ b, (1 + Y (i, b)) * P4 b (repl i (fun _ => 1) (fun p => 1 + Y p)) = 120 := by
    have h := gen (fun _ => 0) (by simp)
    simpa using h
  have heq : ∀ a b, P4 a (repl i (fun _ => 1) (fun p => 1 + Y p)) = P4 b (repl i (fun _ => 1) (fun p => 1 + Y p)) := by
    intro a b
    have hw : ∑ j : Fin 5, ((if j = a then (1 : ℂ) else 0) - (if j = b then (1 : ℂ) else 0)) = 0 := by
      simp [Finset.sum_sub_distrib]
    have h := gen _ hw
    have h3 : ∑ x, (1 + Y (i, x) + ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0))) *
        P4 x (repl i (fun _ => 1) (fun p => 1 + Y p)) =
        ∑ x, (1 + Y (i, x)) * P4 x (repl i (fun _ => 1) (fun p => 1 + Y p)) +
        (P4 a (repl i (fun _ => 1) (fun p => 1 + Y p)) - P4 b (repl i (fun _ => 1) (fun p => 1 + Y p))) := by
      simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linear_combination h - g0 - h3
  refine ⟨fun b => heq b 0, ?_⟩
  rw [Fin.sum_univ_five] at g0
  rw [heq 1 0, heq 2 0, heq 3 0, heq 4 0] at g0
  linear_combination g0

theorem FL45 (K : Submodule ℂ M45) (hK : Lev45 K) (i : Fin 4)
    (hF : ∀ w : Fin 5 → ℂ, ∑ j, w j = 0 → rowE i w ∈ K) : Module.finrank ℂ K ≤ 6 := by
  have hρ : ∀ Y ∈ K, Y (i, 0) + Y (i, 1) + Y (i, 2) + Y (i, 3) + Y (i, 4) = 0 := by
    intro Y hY
    by_contra hne
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c * (Y (i, 0) + Y (i, 1) + Y (i, 2) + Y (i, 3) + Y (i, 4)) = -5 :=
      ⟨-5 / (Y (i, 0) + Y (i, 1) + Y (i, 2) + Y (i, 3) + Y (i, 4)), div_mul_cancel₀ _ hne⟩
    have h := (FL45_core K hK i hF (c • Y) (K.smul_mem c hY)).2
    have e : 5 + ((c • Y) (i, 0) + (c • Y) (i, 1) + (c • Y) (i, 2) + (c • Y) (i, 3)
        + (c • Y) (i, 4)) = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination hc
    rw [e, zero_mul] at h
    norm_num at h
  have hS : SLev (K.map (zrow i)) := by
    rintro _ ⟨Y, hY, rfl⟩ a
    rw [one_add_zrow]
    obtain ⟨h1, h2⟩ := FL45_core K hK i hF Y hY
    rw [hρ Y hY] at h2
    rw [h1 a]
    linear_combination (1 / 5 : ℂ) * h2
  have hrow : ∀ Y ∈ K.map (zrow i), ∀ j, Y (i, j) = 0 := by
    rintro _ ⟨Y, hY, rfl⟩ j
    show (if i = i then (0 : ℂ) else Y (i, j)) = 0
    rw [if_pos rfl]
  have h2 := LemmaSL3 _ hS i hrow
  have rn := rank_nullity K (rowL i)
  have hle : (K ⊓ LinearMap.ker (rowL i) : Submodule ℂ M45) ≤ K.map (zrow i) := by
    intro Y hY
    obtain ⟨hYK, hYr⟩ := Submodule.mem_inf.mp hY
    have hr : rowL i Y = 0 := LinearMap.mem_ker.mp hYr
    refine ⟨Y, hYK, ?_⟩
    funext ⟨k, j⟩
    show (if k = i then (0 : ℂ) else Y (k, j)) = Y (k, j)
    by_cases h : k = i
    · rw [if_pos h, h]
      exact (congrFun hr j).symm
    · rw [if_neg h]
  have h3 := Submodule.finrank_mono hle
  have h4 : K.map (rowL i) ≤ sumZero 5 := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [mem_sumZero, Fin.sum_univ_five]
    exact hρ Y hY
  have h5 := (Submodule.finrank_mono h4).trans (finrank_sumZero (n := 5) (by norm_num))
  omega

theorem Di_mem (K : Submodule ℂ M45) (hK : Lev45 K) (i : Fin 4) (u : Fin 5 → ℂ)
    (hE : rowE i u ∈ K) (Y : M45) (hY : Y ∈ K) :
    (fun b => P4 b (repl i u (fun p => 1 + Y p))) ∈ defC K ∧
      ∑ b, P4 b (repl i u (fun p => 1 + Y p)) = 0 := by
  have eN : repl i (fun j => 1 + Y (i, j)) (fun p => 1 + Y p) = fun p => 1 + Y p :=
    repl_self i (fun p => 1 + Y p)
  have eN1 : (fun p : Fin 4 × Fin 5 => 1 + (Y + rowE i u) p) =
      repl i ((fun j => 1 + Y (i, j)) + u) (fun p => 1 + Y p) := by
    funext ⟨k, j⟩
    by_cases h : k = i
    · rw [h, repl_at]
      show 1 + (Y (i, j) + if i = i then u j else 0) = 1 + Y (i, j) + u j
      rw [if_pos rfl]
      ring
    · rw [repl_ne i k h]
      show 1 + (Y (k, j) + if k = i then u j else 0) = 1 + Y (k, j)
      rw [if_neg h]
      ring
  have hadd : ∀ b, P4 b (repl i u (fun p => 1 + Y p)) =
      P4 b (fun p : Fin 4 × Fin 5 => 1 + (Y + rowE i u) p) - P4 b (fun p => 1 + Y p) := by
    intro b
    have h := P4_repl_add b i (fun j => 1 + Y (i, j)) u (fun p => 1 + Y p)
    rw [eN] at h
    rw [eN1]
    linear_combination (-1 : ℂ) * h
  constructor
  · have g1 : (fun a => P4 a (fun p : Fin 4 × Fin 5 => 1 + (Y + rowE i u) p)) ∈ defC K :=
      Submodule.subset_span ⟨Y + rowE i u, K.add_mem hY hE, rfl⟩
    have g2 : (fun a => P4 a (fun p => 1 + Y p)) ∈ defC K :=
      Submodule.subset_span ⟨Y, hY, rfl⟩
    have e : (fun b => P4 b (repl i u (fun p => 1 + Y p))) =
        (fun a => P4 a (fun p : Fin 4 × Fin 5 => 1 + (Y + rowE i u) p))
        - (fun a => P4 a (fun p => 1 + Y p)) := by
      funext b
      exact hadd b
    rw [e]
    exact (defC K).sub_mem g1 g2
  · have h1 := hK _ (K.add_mem hY hE)
    have h2 := hK Y hY
    rw [Fin.sum_univ_five] at h1 h2 ⊢
    rw [hadd 0, hadd 1, hadd 2, hadd 3, hadd 4]
    linear_combination h1 - h2

theorem R415_F1 (K : Submodule ℂ M45) (hK : Lev45 K) (i : Fin 4) (u : Fin 5 → ℂ)
    (hE : rowE i u ∈ K) (Y : M45) (hY : Y ∈ K) :
    (tau (col (repl i 0 Y) 0) * u 0 + tau (col (repl i 0 Y) 1) * u 1
      + tau (col (repl i 0 Y) 2) * u 2 + tau (col (repl i 0 Y) 3) * u 3
      + tau (col (repl i 0 Y) 4) * u 4 = 0) ∧
    (fun b => tau (col (repl i 0 Y) b) * u b) ∈ defC K := by
  have hU := single_row_sum K hK i u hE
  have hu := single_row_defC K hK i u hE
  have fam : ∀ t : ℂ, (fun b => P4 b (fun p => (repl i u (fun _ => 1)) p + t * (repl i 0 Y) p)) ∈ defC K ∧
      ∑ b, P4 b (fun p => (repl i u (fun _ => 1)) p + t * (repl i 0 Y) p) = 0 := by
    intro t
    have h := Di_mem K hK i u hE (t • Y) (K.smul_mem t hY)
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (t • Y) p) = fun p => 1 + t * Y p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
    have e2 : repl i u (fun p => 1 + t * Y p) =
        fun p => (repl i u (fun _ => 1)) p + t * (repl i 0 Y) p := by
      funext ⟨k, j⟩
      show repl i u (fun p => 1 + t * Y p) (k, j) =
        (repl i u (fun _ => 1)) (k, j) + t * (repl i 0 Y) (k, j)
      by_cases hk : k = i
      · rw [hk, repl_at, repl_at, repl_at]
        simp only [Pi.zero_apply]
        ring
      · rw [repl_ne i k hk, repl_ne i k hk, repl_ne i k hk]
    rw [e1, e2] at h
    exact h
  have hpoly := fun b => P4_poly1 b (repl i u (fun _ => 1)) (repl i 0 Y)
  choose p2 p3 p4 hp using hpoly
  have E0 := kc1_formula 0 i u Y
  have E1 := kc1_formula 1 i u Y
  have E2 := kc1_formula 2 i u Y
  have E3 := kc1_formula 3 i u Y
  have E4 := kc1_formula 4 i u Y
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at E0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at E1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at E2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at E3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at E4
  obtain ⟨c, hc⟩ : ∃ c : Fin 5 → ℂ, ∀ j, tau (col (repl i 0 Y) j) = c j :=
    ⟨fun j => tau (col (repl i 0 Y) j), fun j => rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ k1 : Fin 5 → ℂ, ∀ b, kc1 b (repl i u (fun _ => 1)) (repl i 0 Y) = k1 b :=
    ⟨fun b => kc1 b (repl i u (fun _ => 1)) (repl i 0 Y), fun b => rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q0 : Fin 5 → ℂ, ∀ b, P4 b (repl i u (fun _ => 1)) = q0 b :=
    ⟨fun b => P4 b (repl i u (fun _ => 1)), fun b => rfl⟩
  simp only [hc, hk1] at E0 E1 E2 E3 E4
  simp only [hk1, hq0] at hp
  simp only [hc]
  have hsum : k1 0 + k1 1 + k1 2 + k1 3 + k1 4 = 0 := by
    have hall : ∀ t : ℂ, (q0 0 + q0 1 + q0 2 + q0 3 + q0 4) + (k1 0 + k1 1 + k1 2 + k1 3 + k1 4) * t + (p2 0 + p2 1 + p2 2 + p2 3 + p2 4) * t ^ 2 + (p3 0 + p3 1 + p3 2 + p3 3 + p3 4) * t ^ 3 + (p4 0 + p4 1 + p4 2 + p4 3 + p4 4) * t ^ 4 = 0 := by
      intro t
      have h := (fam t).2
      rw [Fin.sum_univ_five, hp 0 t, hp 1 t, hp 2 t, hp 3 t, hp 4 t] at h
      linear_combination h
    have hr := roots5 (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) inj_succ5 (q0 0 + q0 1 + q0 2 + q0 3 + q0 4) (k1 0 + k1 1 + k1 2 + k1 3 + k1 4) (p2 0 + p2 1 + p2 2 + p2 3 + p2 4) (p3 0 + p3 1 + p3 2 + p3 3 + p3 4) (p4 0 + p4 1 + p4 2 + p4 3 + p4 4)
      (fun k => hall _)
    linear_combination hr.2.1
  have hcu : (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4) = 0 := by
    linear_combination (c 0 + c 1 + c 2 + c 3 + c 4) * hU + (1 / 6 : ℂ) * (E0 + E1 + E2 + E3 + E4) - (1 / 6 : ℂ) * hsum
  have g0 : k1 0 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * u 0 + 4 * c 0 * u 0 - 2 * (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4) := by
    linear_combination E0 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 0) * hU
  have g1 : k1 1 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * u 1 + 4 * c 1 * u 1 - 2 * (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4) := by
    linear_combination E1 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 1) * hU
  have g2 : k1 2 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * u 2 + 4 * c 2 * u 2 - 2 * (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4) := by
    linear_combination E2 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 2) * hU
  have g3 : k1 3 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * u 3 + 4 * c 3 * u 3 - 2 * (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4) := by
    linear_combination E3 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 3) * hU
  have g4 : k1 4 = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * u 4 + 4 * c 4 * u 4 - 2 * (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4) := by
    linear_combination E4 + 2 * ((c 0 + c 1 + c 2 + c 3 + c 4) - c 4) * hU
  have G : ∀ b, k1 b = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * u b + 4 * c b * u b - 2 * (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4) :=
    fin5 (fun b => k1 b = -2 * (c 0 + c 1 + c 2 + c 3 + c 4) * u b + 4 * c b * u b - 2 * (c 0 * u 0 + c 1 * u 1 + c 2 * u 2 + c 3 * u 3 + c 4 * u 4)) g0 g1 g2 g3 g4
  have hk1mem : k1 ∈ defC K := by
    have e : k1 = (1 / 12 : ℂ) • ((-25 : ℂ) • (fun b => P4 b (fun p => (repl i u (fun _ => 1)) p + (0 : ℂ) * (repl i 0 Y) p)) + (48 : ℂ) • (fun b => P4 b (fun p => (repl i u (fun _ => 1)) p + (1 : ℂ) * (repl i 0 Y) p)) - (36 : ℂ) • (fun b => P4 b (fun p => (repl i u (fun _ => 1)) p + (2 : ℂ) * (repl i 0 Y) p))
        + (16 : ℂ) • (fun b => P4 b (fun p => (repl i u (fun _ => 1)) p + (3 : ℂ) * (repl i 0 Y) p)) - (3 : ℂ) • (fun b => P4 b (fun p => (repl i u (fun _ => 1)) p + (4 : ℂ) * (repl i 0 Y) p))) := by
      funext b
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [hp b 0, hp b 1, hp b 2, hp b 3, hp b 4]
      ring
    have m0 := (defC K).smul_mem (-25 : ℂ) (fam 0).1
    have m1 := (defC K).smul_mem (48 : ℂ) (fam 1).1
    have m2 := (defC K).smul_mem (36 : ℂ) (fam 2).1
    have m3 := (defC K).smul_mem (16 : ℂ) (fam 3).1
    have m4 := (defC K).smul_mem (3 : ℂ) (fam 4).1
    rw [e]
    exact (defC K).smul_mem _ ((defC K).sub_mem ((defC K).add_mem ((defC K).sub_mem
      ((defC K).add_mem m0 m1) m2) m3) m4)
  refine ⟨hcu, ?_⟩
  have e : (fun b => c b * u b) = (1 / 4 : ℂ) • (k1 + (2 * (c 0 + c 1 + c 2 + c 3 + c 4)) • u) := by
    funext b
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (-1 / 4 : ℂ) * G b + (1 / 2 : ℂ) * hcu
  rw [e]
  exact (defC K).smul_mem _ ((defC K).add_mem hk1mem ((defC K).smul_mem _ hu))

theorem R415_F2 (K : Submodule ℂ M45) (hK : Lev45 K) (i k : Fin 4) (hik : i ≠ k)
    (u u' : Fin 5 → ℂ) (hE : rowE i u ∈ K) (hE' : rowE k u' ∈ K) :
    (fun b => u' b * u b) ∈ defC K := by
  have h := (R415_F1 K hK i u hE (rowE k u') hE').2
  have e : ∀ b, tau (col (repl i 0 (rowE k u')) b) = u' b := by
    intro b
    have h1 := tau_repl0 i (rowE k u') b
    have h2 : tau (col (rowE k u') b) = ∑ a : Fin 4, (if a = k then u' b else 0) := by
      rw [Fin.sum_univ_four]
      rfl
    have h3 : rowE k u' (i, b) = 0 := by
      show (if i = k then u' b else 0) = 0
      rw [if_neg hik]
    have h4 : ∑ a : Fin 4, (if a = k then u' b else 0) = u' b := by simp
    rw [h2, h3, h4] at h1
    linear_combination (-1 : ℂ) * h1
  simp only [e] at h
  exact h

theorem SLev_Lev45 {K : Submodule ℂ M45} (h : SLev K) : Lev45 K := by
  intro Y hY
  rw [Fin.sum_univ_five, h Y hY 0, h Y hY 1, h Y hY 2, h Y hY 3, h Y hY 4]
  norm_num

theorem DefLine_Lev45 {K : Submodule ℂ M45} {m : Fin 5 → ℂ} (h : DefLine K m)
    (hm : ∑ a, m a = 0) : Lev45 K := by
  intro Y hY
  obtain ⟨θ, hθ⟩ := h Y hY
  rw [Fin.sum_univ_five] at hm ⊢
  rw [hθ 0, hθ 1, hθ 2, hθ 3, hθ 4]
  linear_combination θ * hm

theorem SLev_DefLine {K : Submodule ℂ M45} (h : SLev K) (m : Fin 5 → ℂ) : DefLine K m := by
  intro Y hY
  refine ⟨0, fun a => ?_⟩
  rw [h Y hY a]
  ring

theorem NCOL_S_neutral (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hmm : ∑ a, m a * m a ≠ 0) (i : Fin 4)
    (hsplit : (fun p : Fin 4 × Fin 5 => if p.1 = i then m p.2 else 0) ∈ K)
    (h4 : 4 ≤ Module.finrank ℂ K) : ∃ n, m n = 0 := by
  by_contra hc
  have hm0 : ∀ j, m j ≠ 0 := fun j hj => hc ⟨j, hj⟩
  have h3 := (NCOL_S_a K m hdef hm hmm i hsplit hm0).2
  omega

def zE (z : V4) : M45 := fun p => if p.2 = 0 then z p.1 else if p.2 = 1 then -z p.1 else 0

theorem zE0 (z : V4) (k : Fin 4) : zE z (k, 0) = z k := by simp [zE]

theorem zE1 (z : V4) (k : Fin 4) : zE z (k, 1) = -z k := by simp [zE]

theorem zE3 (z : V4) (k : Fin 4) : zE z (k, 3) = 0 := by simp [zE]

theorem zE4 (z : V4) (k : Fin 4) : zE z (k, 4) = 0 := by simp [zE]

theorem pc_ones : pc (fun _ : Fin 4 => (1 : ℂ)) (fun _ => 1) (fun _ => 1) (fun _ => 1) = 24 := by
  have h1 := P4_ones 0
  rw [P4_c0] at h1
  have hc : ∀ j, col (fun _ : Fin 4 × Fin 5 => (1 : ℂ)) j = fun _ => 1 := fun j => rfl
  rw [hc, hc, hc, hc] at h1
  exact h1

theorem LemmaZ1 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z : V4) (hz : zE z ∈ K) :
    e2 z = 0 := by
  have h := ((TC5_normal K).mp hdef (zE z) hz).2.1
  have eu : (fun k => 1 + uY (zE z) k) = fun _ => (1 : ℂ) := by
    funext k
    simp only [uY, zE0, zE1]
    ring
  have ed : dY (zE z) = z := by
    funext k
    simp only [dY, zE0, zE1]
    ring
  have e3 : (fun k => 1 + zE z (k, 3)) = fun _ => (1 : ℂ) := by
    funext k
    rw [zE3, add_zero]
  have e4 : (fun k => 1 + zE z (k, 4)) = fun _ => (1 : ℂ) := by
    funext k
    rw [zE4, add_zero]
  rw [eu, ed, e3, e4, pc_ones] at h
  have hd := TC5_dd z 0 0
  have e0 : (fun k : Fin 4 => (1 : ℂ) + (0 : V4) k) = fun _ => 1 := by
    funext k
    simp
  have hp0 : pc z z 0 0 = 0 := by
    simp [pc]
  have hi0 : ip ((0 : V4) + 0) (Ed z) = 0 := by
    simp [ip]
  rw [e0, hp0, hi0] at hd
  linear_combination (-1 / 4 : ℂ) * h - (1 / 4 : ℂ) * hd

def sc1F (Y : M45) (x : V4) (n b : Fin 5) : ℂ :=
  4 * tau x * ((tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4))
    - tau (col Y b) - tau (col Y n)) + 4 * (ip x (col Y b) + ip x (col Y n) - ip x (rs Y))

theorem rs_col (Y : M45) (i : Fin 4) :
    rs Y i = col Y 0 i + col Y 1 i + col Y 2 i + col Y 3 i + col Y 4 i := by
  exact rs_apply Y i

set_option maxHeartbeats 2000000 in
theorem sc1_polar (Y : M45) (x : V4) : ∀ n b : Fin 5,
    qA2 (Y + fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) b
      - qA2 (Y - fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) b =
    if b = n then 0 else sc1F Y x n b := by
  apply fin5 <;> apply fin5 <;>
    simp (config := {decide := true}) only [qA2, sc1F, sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2,
      sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2, sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2,
      sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2, sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2,
      tau, ip, col, rs_apply, Pi.add_apply, Pi.sub_apply, ite_true, ite_false] <;> ring

theorem sum_ite_ne5 (F : Fin 5 → ℂ) : ∀ n : Fin 5,
    (if (0 : Fin 5) = n then 0 else F 0) + (if (1 : Fin 5) = n then 0 else F 1)
      + (if (2 : Fin 5) = n then 0 else F 2) + (if (3 : Fin 5) = n then 0 else F 3)
      + (if (4 : Fin 5) = n then 0 else F 4) = F 0 + F 1 + F 2 + F 3 + F 4 - F n := by
  apply fin5 <;> simp (config := {decide := true}) only [ite_true, ite_false] <;> ring

theorem qA2_sum (K : Submodule ℂ M45) (hK : Lev45 K) (W : M45) (hW : W ∈ K) :
    qA2 W 0 + qA2 W 1 + qA2 W 2 + qA2 W 3 + qA2 W 4 = 0 := by
  obtain ⟨a3, a4, h0⟩ := P4_quad 0 W
  obtain ⟨b3, b4, h1⟩ := P4_quad 1 W
  obtain ⟨c3, c4, h2⟩ := P4_quad 2 W
  obtain ⟨d3, d4, h3⟩ := P4_quad 3 W
  obtain ⟨e3, e4, h4⟩ := P4_quad 4 W
  have hall : ∀ c : ℂ, 0 + (qA1 W 0 + qA1 W 1 + qA1 W 2 + qA1 W 3 + qA1 W 4) * c
      + (qA2 W 0 + qA2 W 1 + qA2 W 2 + qA2 W 3 + qA2 W 4) * c ^ 2
      + (a3 + b3 + c3 + d3 + e3) * c ^ 3 + (a4 + b4 + c4 + d4 + e4) * c ^ 4 = 0 := by
    intro c
    have h := hK (c • W) (K.smul_mem c hW)
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • W) p) = fun p => 1 + c * W p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [e1, Fin.sum_univ_five, h0 c, h1 c, h2 c, h3 c, h4 c] at h
    linear_combination h
  have hr := roots5 (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) inj_succ5 0
    (qA1 W 0 + qA1 W 1 + qA1 W 2 + qA1 W 3 + qA1 W 4)
    (qA2 W 0 + qA2 W 1 + qA2 W 2 + qA2 W 3 + qA2 W 4)
    (a3 + b3 + c3 + d3 + e3) (a4 + b4 + c4 + d4 + e4) (fun k => hall _)
  exact hr.2.2.1

theorem qA2_defC (K : Submodule ℂ M45) (W : M45) (hW : W ∈ K) :
    (fun b => qA2 W b) ∈ defC K := by
  choose A3 A4 hA using fun b => P4_quad b W
  have g : ∀ c : ℂ, (fun b => P4 b (fun p => 1 + c * W p)) ∈ defC K := by
    intro c
    have h : (fun a => P4 a (fun p => 1 + (c • W) p)) ∈ defC K :=
      Submodule.subset_span ⟨c • W, K.smul_mem c hW, rfl⟩
    have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • W) p) = fun p => 1 + c * W p := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [e1] at h
    exact h
  have e : (fun b => qA2 W b) = (1 / 24 : ℂ) • ((35 : ℂ) • (fun b => P4 b (fun p => 1 + (0 : ℂ) * W p))
      - (104 : ℂ) • (fun b => P4 b (fun p => 1 + (1 : ℂ) * W p))
      + (114 : ℂ) • (fun b => P4 b (fun p => 1 + (2 : ℂ) * W p))
      - (56 : ℂ) • (fun b => P4 b (fun p => 1 + (3 : ℂ) * W p))
      + (11 : ℂ) • (fun b => P4 b (fun p => 1 + (4 : ℂ) * W p))) := by
    funext b
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [hA b 0, hA b 1, hA b 2, hA b 3, hA b 4]
    ring
  have m0 := (defC K).smul_mem (35 : ℂ) (g 0)
  have m1 := (defC K).smul_mem (104 : ℂ) (g 1)
  have m2 := (defC K).smul_mem (114 : ℂ) (g 2)
  have m3 := (defC K).smul_mem (56 : ℂ) (g 3)
  have m4 := (defC K).smul_mem (11 : ℂ) (g 4)
  rw [e]
  exact (defC K).smul_mem _ ((defC K).add_mem ((defC K).sub_mem ((defC K).add_mem
    ((defC K).sub_mem m0 m1) m2) m3) m4)

theorem SC1 (K : Submodule ℂ M45) (hK : Lev45 K) (n : Fin 5) (x : V4) (hx : tau x = 0)
    (hE : (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) ∈ K) (Y : M45) (hY : Y ∈ K) :
    ip x (rs Y) - ip x (col Y n) = 0 ∧
      (fun b => if b = n then 0 else ip x (col Y b)) ∈ defC K := by
  have hp := K.add_mem hY hE
  have hm := K.sub_mem hY hE
  have sp := qA2_sum K hK _ hp
  have sm := qA2_sum K hK _ hm
  have p0 := sc1_polar Y x n 0
  have p1 := sc1_polar Y x n 1
  have p2 := sc1_polar Y x n 2
  have p3 := sc1_polar Y x n 3
  have p4 := sc1_polar Y x n 4
  have hs := sum_ite_ne5 (sc1F Y x n) n
  have ha : ip x (rs Y) - ip x (col Y n) = 0 := by
    have key : sc1F Y x n 0 + sc1F Y x n 1 + sc1F Y x n 2 + sc1F Y x n 3 + sc1F Y x n 4
        - sc1F Y x n n = 0 := by
      linear_combination sp - sm - p0 - p1 - p2 - p3 - p4 - hs
    simp only [sc1F, ip, rs_col] at key ⊢
    linear_combination (-1 / 12 : ℂ) * key
      + (tau (col Y 0) + tau (col Y 1) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4)
        - tau (col Y n)) * hx
  refine ⟨ha, ?_⟩
  have dp := qA2_defC K _ hp
  have dm := qA2_defC K _ hm
  have e : (fun b => if b = n then 0 else ip x (col Y b)) = (1 / 4 : ℂ) •
      ((fun b => qA2 (Y + fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) b)
        - (fun b => qA2 (Y - fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) b)) := by
    funext b
    have pb := sc1_polar Y x n b
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [pb]
    by_cases h : b = n
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      simp only [sc1F]
      rw [hx]
      linear_combination ha
  rw [e]
  exact (defC K).smul_mem _ ((defC K).sub_mem dp dm)

def QBc (K : Submodule ℂ M45) (m : Fin 5 → ℂ) : Prop :=
  ∀ Y ∈ K, ∃ κ θ2 : ℂ, (∀ j, tau (col Y j) = κ * m j) ∧
    (∀ j, ip (col Y j) (col Y j) - ip (rs Y) (col Y j) - κ ^ 2 * m j ^ 2 = -(θ2 / 2) * m j)

theorem phi_onto (K : Submodule ℂ M45) (hK : SLev K) (hq : Module.finrank ℂ (K.map rs) = 3)
    (m : Fin 5) : K.map rs = sumZero 4 ∧ K.map (phi m) = sumZero 4 := by
  have hV3 : Module.finrank ℂ (sumZero 4) ≤ 3 :=
    (finrank_sumZero (n := 4) (by norm_num)).trans (by norm_num)
  have hS : K.map rs ≤ sumZero 4 := map_rs_le K hK
  have hSV : K.map rs = sumZero 4 :=
    Submodule.eq_of_le_of_finrank_le hS (le_trans hV3 (le_of_eq hq.symm))
  refine ⟨hSV, ?_⟩
  have hle : K.map (phi m) ≤ sumZero 4 := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [mem_Vs]
    exact tau_phi K hK Y hY m
  have hker : (K ⊓ LinearMap.ker (phi m) : Submodule ℂ M45) ≤ K ⊓ LinearMap.ker rs := by
    rintro Y ⟨hY, hY0⟩
    refine ⟨hY, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hY0 ⊢
    apply nondeg
    · exact tau_rs K hK Y hY
    · intro v hv
      have hv' : v ∈ K.map rs := by
        rw [hSV, mem_Vs]
        exact hv
      obtain ⟨Y', hY', rfl⟩ := hv'
      rw [← ip_phi K hK Y Y' hY hY' m, hY0]
      simp [ip]
  have r1 := rank_nullity K (phi m)
  have r2 := rank_nullity K rs
  have r3 := Submodule.finrank_mono hker
  have hP3 : 3 ≤ Module.finrank ℂ (K.map (phi m)) := by omega
  exact Submodule.eq_of_le_of_finrank_le hle (le_trans hV3 hP3)

theorem pol_alg (z y s : V4) (k1 k2 mj th1 th2 : ℂ) (ty : tau y = 0)
    (c1 : tau (z + y) = k1 * mj) (c2 : tau (z - y) = k2 * mj)
    (e1 : ip (z + y) (z + y) - ip s (z + y) - k1 ^ 2 * mj ^ 2 = -(th1 / 2) * mj)
    (e2 : ip (z - y) (z - y) - ip (-s) (z - y) - k2 ^ 2 * mj ^ 2 = -(th2 / 2) * mj) :
    ip z (fun i => 2 * y i - s i) = (-(th1 - th2) / 4) * mj := by
  simp only [ip, tau, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at ty c1 c2 e1 e2 ⊢
  linear_combination (1 / 2 : ℂ) * (e1 - e2)
    - (1 / 2 : ℂ) * ((z 0 + y 0) + (z 1 + y 1) + (z 2 + y 2) + (z 3 + y 3) + k1 * mj) * c1
    + (1 / 2 : ℂ) * ((z 0 - y 0) + (z 1 - y 1) + (z 2 - y 2) + (z 3 - y 3) + k2 * mj) * c2
    + 2 * (z 0 + z 1 + z 2 + z 3) * ty

theorem PS_pol (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (Y : M45) (hY : Y ∈ H) :
    ∃ μ : ℂ, ∀ j, ip (col Z j) (phi j Y) = μ * m j := by
  obtain ⟨κ1, θ1, hc1, hb1⟩ := hQB (Z + Y) (K.add_mem hZ (hHK hY))
  obtain ⟨κ2, θ2, hc2, hb2⟩ := hQB (Z - Y) (K.sub_mem hZ (hHK hY))
  refine ⟨-(θ1 - θ2) / 4, fun j => ?_⟩
  have e1 := hb1 j
  have e2 := hb2 j
  have c1 := hc1 j
  have c2 := hc2 j
  have r1 : rs (Z + Y) = rs Y := by rw [map_add, hZ0, zero_add]
  have r2 : rs (Z - Y) = -rs Y := by rw [map_sub, hZ0, zero_sub]
  have ec1 : col (Z + Y) j = col Z j + col Y j := rfl
  have ec2 : col (Z - Y) j = col Z j - col Y j := rfl
  rw [r1, ec1] at e1
  rw [r2, ec2] at e2
  rw [ec1] at c1
  rw [ec2] at c2
  have hp : phi j Y = fun i => 2 * col Y j i - rs Y i := by
    funext i
    exact phi_apply j Y i
  rw [hp]
  exact pol_alg (col Z j) (col Y j) (rs Y) κ1 κ2 (m j) θ1 θ2 (C1 H hH Y hY j) c1 c2 e1 e2

theorem PS_f (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    ∃ f : V4, tau f = 0 ∧ ∀ Y ∈ H, ∀ j, ip (col Z j) (phi j Y) = m j * ip f (rs Y) := by
  have hSV := (phi_onto H hH hq 0).1
  have hbot := Bi H hH hq
  have hsurj : ∀ σ : V4, tau σ = 0 → ∃ Y ∈ H, rs Y = σ := by
    intro σ hσ
    have h : σ ∈ H.map rs := by
      rw [hSV, mem_Vs]
      exact hσ
    obtain ⟨Y, hY, e⟩ := h
    exact ⟨Y, hY, e⟩
  have hinj : ∀ Y ∈ H, rs Y = 0 → Y = 0 := by
    intro Y hY h0
    have hmem : Y ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
      Submodule.mem_inf.mpr ⟨hY, LinearMap.mem_ker.mpr h0⟩
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨Y1, hY1, e1⟩ := hsurj ![1, 0, 0, -1] (by norm_num [tau])
  obtain ⟨Y2, hY2, e2⟩ := hsurj ![0, 1, 0, -1] (by norm_num [tau])
  obtain ⟨Y3, hY3, e3⟩ := hsurj ![0, 0, 1, -1] (by norm_num [tau])
  obtain ⟨a1, h1⟩ := PS_pol K m hQB H hHK hH Z hZ hZ0 Y1 hY1
  obtain ⟨a2, h2⟩ := PS_pol K m hQB H hHK hH Z hZ hZ0 Y2 hY2
  obtain ⟨a3, h3⟩ := PS_pol K m hQB H hHK hH Z hZ hZ0 Y3 hY3
  have hdec : ∀ Y ∈ H, Y = rs Y 0 • Y1 + rs Y 1 • Y2 + rs Y 2 • Y3 := by
    intro Y hY
    have ht := tau_rs H hH Y hY
    have hmem : Y - (rs Y 0 • Y1 + rs Y 1 • Y2 + rs Y 2 • Y3) ∈ H :=
      H.sub_mem hY (H.add_mem (H.add_mem (H.smul_mem _ hY1) (H.smul_mem _ hY2))
        (H.smul_mem _ hY3))
    have h0 : rs (Y - (rs Y 0 • Y1 + rs Y 1 • Y2 + rs Y 2 • Y3)) = 0 := by
      rw [map_sub, map_add, map_add, map_smul, map_smul, map_smul, e1, e2, e3]
      simp only [tau] at ht
      funext i
      fin_cases i
      · show rs Y 0 - (rs Y 0 * 1 + rs Y 1 * 0 + rs Y 2 * 0) = 0
        ring
      · show rs Y 1 - (rs Y 0 * 0 + rs Y 1 * 1 + rs Y 2 * 0) = 0
        ring
      · show rs Y 2 - (rs Y 0 * 0 + rs Y 1 * 0 + rs Y 2 * 1) = 0
        ring
      · show rs Y 3 - (rs Y 0 * (-1) + rs Y 1 * (-1) + rs Y 2 * (-1)) = 0
        linear_combination ht
    exact sub_eq_zero.mp (hinj _ hmem h0)
  refine ⟨![a1 - (a1 + a2 + a3) / 4, a2 - (a1 + a2 + a3) / 4, a3 - (a1 + a2 + a3) / 4,
    -(a1 + a2 + a3) / 4], ?_, ?_⟩
  · have e : tau ![a1 - (a1 + a2 + a3) / 4, a2 - (a1 + a2 + a3) / 4, a3 - (a1 + a2 + a3) / 4,
        -(a1 + a2 + a3) / 4] = (a1 - (a1 + a2 + a3) / 4) + (a2 - (a1 + a2 + a3) / 4)
          + (a3 - (a1 + a2 + a3) / 4) + (-(a1 + a2 + a3) / 4) := rfl
    rw [e]
    ring
  · intro Y hY j
    have ht := tau_rs H hH Y hY
    have hp : phi j Y = rs Y 0 • phi j Y1 + rs Y 1 • phi j Y2 + rs Y 2 • phi j Y3 := by
      conv_lhs => rw [hdec Y hY]
      rw [map_add, map_add, map_smul, map_smul, map_smul]
    rw [hp]
    have q1 := h1 j
    have q2 := h2 j
    have q3 := h3 j
    have ef : ip ![a1 - (a1 + a2 + a3) / 4, a2 - (a1 + a2 + a3) / 4, a3 - (a1 + a2 + a3) / 4,
        -(a1 + a2 + a3) / 4] (rs Y) = (a1 - (a1 + a2 + a3) / 4) * rs Y 0
          + (a2 - (a1 + a2 + a3) / 4) * rs Y 1 + (a3 - (a1 + a2 + a3) / 4) * rs Y 2
          + (-(a1 + a2 + a3) / 4) * rs Y 3 := rfl
    rw [ef]
    simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at q1 q2 q3 ⊢
    simp only [tau] at ht
    linear_combination rs Y 0 * q1 + rs Y 1 * q2 + rs Y 2 * q3 + (m j * (a1 + a2 + a3) / 4) * ht

theorem PS_nf (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0)
    (κ : ℂ) (hκ : ∀ j, tau (col Z j) = κ * m j) :
    ∃ Yf ∈ H, ∀ j, ∀ i, Z (i, j) = κ * m j / 4 + m j * phi j Yf i := by
  obtain ⟨f, hf, hP⟩ := PS_f K m hQB H hHK hH hq Z hZ hZ0
  have hSV := (phi_onto H hH hq 0).1
  have hmem : f ∈ H.map rs := by
    rw [hSV, mem_Vs]
    exact hf
  obtain ⟨Yf, hYf, ef⟩ := hmem
  refine ⟨Yf, hYf, fun j => ?_⟩
  have hw : (fun i => Z (i, j) - κ * m j / 4 - m j * phi j Yf i) = 0 := by
    apply nondeg
    · have h1 := hκ j
      have h2 := tau_phi H hH Yf hYf j
      simp only [tau, col] at h1 h2 ⊢
      linear_combination h1 - m j * h2
    · intro v hv
      have hv' : v ∈ H.map (phi j) := by
        rw [(phi_onto H hH hq j).2, mem_Vs]
        exact hv
      obtain ⟨Y, hY, rfl⟩ := hv'
      have h1 := hP Y hY j
      have h2 := ip_phi H hH Yf Y hYf hY j
      have h3 := tau_phi H hH Y hY j
      rw [ef] at h2
      simp only [ip, tau, col] at h1 h2 h3 ⊢
      linear_combination h1 - m j * h2 - (κ * m j / 4) * h3
  intro i
  have h := congrFun hw i
  simp only [Pi.zero_apply] at h
  linear_combination h

theorem np3_col (zc g : V4) (κ κ' mj θ ν : ℂ) (hz : ∀ i, zc i = κ * mj / 4 + mj * g i)
    (hb : ip zc zc - ip 0 zc - κ' ^ 2 * mj ^ 2 = -(θ / 2) * mj)
    (hc : tau zc = κ' * mj) (hk : tau zc = κ * mj) (ht : tau g = 0) (hn : ip g g = ν) :
    mj ^ 2 * (ν - 3 * κ ^ 2 / 4) = -(θ / 2) * mj := by
  have e : zc = fun i => κ * mj / 4 + mj * g i := funext hz
  subst e
  simp only [ip, tau, Pi.zero_apply] at hb hc hk ht hn
  linear_combination hb - mj ^ 2 * hn - (κ * mj ^ 2 / 2) * ht
    - (κ * mj + mj * (g 0 + g 1 + g 2 + g 3) + κ' * mj) * hc
    + (κ * mj + mj * (g 0 + g 1 + g 2 + g 3) + κ * mj) * hk

theorem np3_X (m0 m1 m2 m3 m4 X lam : ℂ) (h0 : m0 ≠ 0) (h1 : m1 ≠ 0) (h2 : m2 ≠ 0)
    (hs : m0 + m1 + m2 + m3 + m4 = 0)
    (q0 : m0 ^ 2 * X = lam * m0) (q1 : m1 ^ 2 * X = lam * m1) (q2 : m2 ^ 2 * X = lam * m2)
    (q3 : m3 ^ 2 * X = lam * m3) (q4 : m4 ^ 2 * X = lam * m4) : X = 0 := by
  by_contra hX
  have r0 : m0 * X = lam := mul_left_cancel₀ h0 (by linear_combination q0)
  have r1 : m1 * X = lam := mul_left_cancel₀ h1 (by linear_combination q1)
  have r2 : m2 * X = lam := mul_left_cancel₀ h2 (by linear_combination q2)
  have hl : lam ≠ 0 := by
    rw [← r0]
    exact mul_ne_zero h0 hX
  have s3 : m3 = 0 ∨ m3 * X = lam := by
    have h : m3 * (m3 * X - lam) = 0 := by linear_combination q3
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have s4 : m4 = 0 ∨ m4 * X = lam := by
    have h : m4 * (m4 * X - lam) = 0 := by linear_combination q4
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have hsX : m0 * X + m1 * X + m2 * X + m3 * X + m4 * X = 0 := by linear_combination X * hs
  rcases s3 with h3 | h3 <;> rcases s4 with h4 | h4
  · exact hl (by linear_combination (1 / 3 : ℂ) * (hsX - r0 - r1 - r2 - X * h3 - X * h4))
  · exact hl (by linear_combination (1 / 4 : ℂ) * (hsX - r0 - r1 - r2 - X * h3 - h4))
  · exact hl (by linear_combination (1 / 4 : ℂ) * (hsX - r0 - r1 - r2 - h3 - X * h4))
  · exact hl (by linear_combination (1 / 5 : ℂ) * (hsX - r0 - r1 - r2 - h3 - h4))

theorem np3_alg (al be ga ν x y z : ℂ)
    (E1 : al * ν + be * z + ga * y = 0) (E2 : al * z + be * ν + ga * x = 0)
    (E3 : al * y + be * x + ga * ν = 0) (E4 : 3 * ν + 2 * (x + y + z) = ν) :
    ν * ((al - be - ga) * (al - be + ga) * (al + be - ga)) = 0 := by
  linear_combination (1 / 2 : ℂ) * (2 * al * (al - be - ga) * E1 - 2 * be * (al - be + ga) * E2
    - 2 * ga * (al + be - ga) * E3 + 2 * al * be * ga * E4)

theorem NCOL_P3_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 3) = 0 ∧ Y (i, 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) :
    m 0 * m 1 * m 2 = 0 := by
  by_contra hprod
  have hm0' : m 0 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hm1' : m 1 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hm2' : m 2 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨Yf, hYf, hnf⟩ := PS_nf K m hQB H hHK hH hq Z hZ hZ0 κ hκ
  obtain ⟨κ', θ, hc', hb⟩ := hQB Z hZ
  have Q : ∀ j, m j ^ 2 * (ip (rs Yf) (rs Yf) - 3 * κ ^ 2 / 4) = -(θ / 2) * m j := by
    intro j
    have hbj := hb j
    rw [hZ0] at hbj
    exact np3_col (col Z j) (phi j Yf) κ κ' (m j) θ (ip (rs Yf) (rs Yf)) (fun i => hnf j i)
      hbj (hc' j) (hκ j) (tau_phi H hH Yf hYf j) (ip_phi H hH Yf Yf hYf hYf j)
  have hX := np3_X (m 0) (m 1) (m 2) (m 3) (m 4) (ip (rs Yf) (rs Yf) - 3 * κ ^ 2 / 4)
    (-(θ / 2)) hm0' hm1' hm2' hm' (Q 0) (Q 1) (Q 2) (Q 3) (Q 4)
  have hν : ip (rs Yf) (rs Yf) ≠ 0 := by
    intro h0
    rw [h0] at hX
    apply hκ0
    have h : κ * κ = 0 := by linear_combination (-4 / 3 : ℂ) * hX
    exact mul_self_eq_zero.mp h
  have hg3 : ∀ i, phi 3 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hsupp Yf hYf i).1]
    ring
  have hg4 : ∀ i, phi 4 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hsupp Yf hYf i).2]
    ring
  have hsum : ∀ i, phi 0 Yf i + phi 1 Yf i + phi 2 Yf i = -rs Yf i := by
    intro i
    simp only [phi_apply, rs_apply, (hsupp Yf hYf i).1, (hsupp Yf hYf i).2]
    ring
  have hrel : ∀ i, (m 1 + m 2) * phi 0 Yf i + (m 0 + m 2) * phi 1 Yf i
      + (m 0 + m 1) * phi 2 Yf i = 0 := by
    intro i
    have hrow := congrFun hZ0 i
    rw [rs_apply, hnf 0 i, hnf 1 i, hnf 2 i, hnf 3 i, hnf 4 i] at hrow
    simp only [Pi.zero_apply] at hrow
    linear_combination -hrow + (κ / 4) * hm' + m 3 * hg3 i + m 4 * hg4 i
      + (m 0 + m 1 + m 2) * hsum i - rs Yf i * hm'
  have n0 := ip_phi H hH Yf Yf hYf hYf 0
  have n1 := ip_phi H hH Yf Yf hYf hYf 1
  have n2 := ip_phi H hH Yf Yf hYf hYf 2
  have E1 : (m 1 + m 2) * ip (rs Yf) (rs Yf) + (m 0 + m 2) * ip (phi 0 Yf) (phi 1 Yf)
      + (m 0 + m 1) * ip (phi 0 Yf) (phi 2 Yf) = 0 := by
    simp only [ip] at n0 ⊢
    linear_combination phi 0 Yf 0 * hrel 0 + phi 0 Yf 1 * hrel 1 + phi 0 Yf 2 * hrel 2
      + phi 0 Yf 3 * hrel 3 - (m 1 + m 2) * n0
  have E2 : (m 1 + m 2) * ip (phi 0 Yf) (phi 1 Yf) + (m 0 + m 2) * ip (rs Yf) (rs Yf)
      + (m 0 + m 1) * ip (phi 1 Yf) (phi 2 Yf) = 0 := by
    simp only [ip] at n1 ⊢
    linear_combination phi 1 Yf 0 * hrel 0 + phi 1 Yf 1 * hrel 1 + phi 1 Yf 2 * hrel 2
      + phi 1 Yf 3 * hrel 3 - (m 0 + m 2) * n1
  have E3 : (m 1 + m 2) * ip (phi 0 Yf) (phi 2 Yf) + (m 0 + m 2) * ip (phi 1 Yf) (phi 2 Yf)
      + (m 0 + m 1) * ip (rs Yf) (rs Yf) = 0 := by
    simp only [ip] at n2 ⊢
    linear_combination phi 2 Yf 0 * hrel 0 + phi 2 Yf 1 * hrel 1 + phi 2 Yf 2 * hrel 2
      + phi 2 Yf 3 * hrel 3 - (m 0 + m 1) * n2
  have E4 : 3 * ip (rs Yf) (rs Yf) + 2 * (ip (phi 1 Yf) (phi 2 Yf) + ip (phi 0 Yf) (phi 2 Yf)
      + ip (phi 0 Yf) (phi 1 Yf)) = ip (rs Yf) (rs Yf) := by
    simp only [ip] at n0 n1 n2 ⊢
    linear_combination (phi 0 Yf 0 + phi 1 Yf 0 + phi 2 Yf 0 - rs Yf 0) * hsum 0
      + (phi 0 Yf 1 + phi 1 Yf 1 + phi 2 Yf 1 - rs Yf 1) * hsum 1
      + (phi 0 Yf 2 + phi 1 Yf 2 + phi 2 Yf 2 - rs Yf 2) * hsum 2
      + (phi 0 Yf 3 + phi 1 Yf 3 + phi 2 Yf 3 - rs Yf 3) * hsum 3 - n0 - n1 - n2
  have key := np3_alg (m 1 + m 2) (m 0 + m 2) (m 0 + m 1) (ip (rs Yf) (rs Yf))
    (ip (phi 1 Yf) (phi 2 Yf)) (ip (phi 0 Yf) (phi 2 Yf)) (ip (phi 0 Yf) (phi 1 Yf)) E1 E2 E3 E4
  apply hprod
  have h8 : ip (rs Yf) (rs Yf) * (m 0 * m 1 * m 2) = 0 := by
    linear_combination (-1 / 8 : ℂ) * key
  exact (mul_eq_zero.mp h8).resolve_left hν

theorem sq_prop (m : Fin 5 → ℂ) (hm : ∑ a, m a = 0) (hm0 : m ≠ 0)
    (X lam : ℂ) (h : ∀ j, m j ^ 2 * X = lam * m j) : X = 0 := by
  by_contra hX
  have s : ∀ j, m j = 0 ∨ m j * X = lam := by
    intro j
    have h' : m j * (m j * X - lam) = 0 := by linear_combination h j
    rcases mul_eq_zero.mp h' with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linear_combination h')
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  have hsX : m 0 * X + m 1 * X + m 2 * X + m 3 * X + m 4 * X = 0 := by
    linear_combination X * hm'
  have hl : lam = 0 ∨ ∀ j, m j = 0 := by
    rcases s 0 with h0 | h0 <;> rcases s 1 with h1 | h1 <;> rcases s 2 with h2 | h2 <;>
      rcases s 3 with h3 | h3 <;> rcases s 4 with h4 | h4 <;>
      first
        | exact Or.inr (fin5 _ h0 h1 h2 h3 h4)
        | (simp only [h0, h1, h2, h3, h4, zero_mul, add_zero, zero_add] at hsX
           first
             | exact Or.inl (by linear_combination hsX)
             | exact Or.inl (by linear_combination (1 / 2 : ℂ) * hsX)
             | exact Or.inl (by linear_combination (1 / 3 : ℂ) * hsX)
             | exact Or.inl (by linear_combination (1 / 4 : ℂ) * hsX)
             | exact Or.inl (by linear_combination (1 / 5 : ℂ) * hsX))
  apply hm0
  funext j
  rcases hl with hl | hl
  · rcases s j with hj | hj
    · exact hj
    · rw [hl] at hj
      exact (mul_eq_zero.mp hj).resolve_right hX
  · exact hl j

theorem PS_b_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    ∃ κ : ℂ, (∀ j, tau (col Z j) = κ * m j) ∧ ∃ Yf ∈ H,
      (∀ j, ∀ i, Z (i, j) = κ * m j / 4 + m j * phi j Yf i) ∧
      ip (rs Yf) (rs Yf) = 3 * κ ^ 2 / 4 := by
  obtain ⟨κ, θ, hc, hb⟩ := hQB Z hZ
  obtain ⟨Yf, hYf, hnf⟩ := PS_nf K m hQB H hHK hH hq Z hZ hZ0 κ hc
  refine ⟨κ, hc, Yf, hYf, hnf, ?_⟩
  have Q : ∀ j, m j ^ 2 * (ip (rs Yf) (rs Yf) - 3 * κ ^ 2 / 4) = -(θ / 2) * m j := by
    intro j
    have hbj := hb j
    rw [hZ0] at hbj
    exact np3_col (col Z j) (phi j Yf) κ κ (m j) θ (ip (rs Yf) (rs Yf)) (fun i => hnf j i)
      hbj (hc j) (hc j) (tau_phi H hH Yf hYf j) (ip_phi H hH Yf Yf hYf hYf j)
  have hX := sq_prop m hm hm0 _ _ Q
  linear_combination hX

theorem PS_c_key (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (j0 : Fin 5) (hj0 : m j0 ≠ 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (hc0 : colsumL j0 Z = 0) :
    ip (col Z j0) (col Z j0) = 0 ∧ (col Z j0 = 0 → Z = 0) := by
  have hbot := Bi H hH hq
  obtain ⟨κ, hc, Yf, hYf, hnf, hff⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq Z hZ hZ0
  have hκ : κ = 0 := by
    have h1 := hc j0
    rw [colsumL_apply, Fin.sum_univ_four] at hc0
    simp only [tau, col] at h1
    have h2 : κ * m j0 = 0 := by linear_combination -h1 + hc0
    exact (mul_eq_zero.mp h2).resolve_right hj0
  rw [hκ] at hff hnf
  constructor
  · have hn := ip_phi H hH Yf Yf hYf hYf j0
    have hz : col Z j0 = fun i => m j0 * phi j0 Yf i := by
      funext i
      show Z (i, j0) = m j0 * phi j0 Yf i
      rw [hnf j0 i]
      ring
    rw [hz]
    simp only [ip] at hn hff ⊢
    linear_combination m j0 ^ 2 * hn + m j0 ^ 2 * hff
  · intro hz0
    have hphi : phi j0 Yf = 0 := by
      funext i
      have h := congrFun hz0 i
      have h' : Z (i, j0) = 0 := h
      rw [hnf j0 i] at h'
      have h'' : m j0 * phi j0 Yf i = 0 := by linear_combination h'
      exact (mul_eq_zero.mp h'').resolve_left hj0
    have hrs : rs Yf = 0 := by
      apply nondeg
      · exact tau_rs H hH Yf hYf
      · intro v hv
        have hv' : v ∈ H.map rs := by
          rw [(phi_onto H hH hq 0).1, mem_Vs]
          exact hv
        obtain ⟨Y', hY', rfl⟩ := hv'
        rw [← ip_phi H hH Yf Y' hYf hY' j0, hphi]
        simp [ip]
    have hY0 : Yf = 0 := by
      have hmem : Yf ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
        Submodule.mem_inf.mpr ⟨hYf, LinearMap.mem_ker.mpr hrs⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    funext ⟨i, j⟩
    rw [hnf j i, hY0, map_zero]
    simp

theorem PS_N0_le (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (j0 : Fin 5) (hj0 : m j0 ≠ 0) :
    Module.finrank ℂ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL j0) :
      Submodule ℂ M45) ≤ 1 := by
  have r := rank_nullity ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL j0) :
    Submodule ℂ M45) (colL j0)
  have hb : (((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL j0)) ⊓ LinearMap.ker (colL j0) :
      Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    rintro Z ⟨⟨⟨hZ, hZ0⟩, hc0⟩, hz0⟩
    rw [Submodule.mem_bot]
    exact (PS_c_key K m hQB hm hm0 H hHK hH hq j0 hj0 Z hZ (LinearMap.mem_ker.mp hZ0)
      (LinearMap.mem_ker.mp hc0)).2 (LinearMap.mem_ker.mp hz0)
  have hW : Module.finrank ℂ (((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL j0) :
      Submodule ℂ M45).map (colL j0)) ≤ 1 := by
    apply Q1
    · rintro _ ⟨Z, ⟨⟨hZ, hZ0⟩, hc0⟩, rfl⟩
      have hc := LinearMap.mem_ker.mp hc0
      rw [colsumL_apply, Fin.sum_univ_four] at hc
      rw [colL_apply]
      simp only [tau, col]
      linear_combination hc
    · rintro _ ⟨Z, ⟨⟨hZ, hZ0⟩, hc0⟩, rfl⟩ _ ⟨Z', ⟨⟨hZ', hZ0'⟩, hc0'⟩, rfl⟩
      have a0 := LinearMap.mem_ker.mp hZ0
      have a1 := LinearMap.mem_ker.mp hZ0'
      have b0 := LinearMap.mem_ker.mp hc0
      have b1 := LinearMap.mem_ker.mp hc0'
      have i1 := (PS_c_key K m hQB hm hm0 H hHK hH hq j0 hj0 Z hZ a0 b0).1
      have i2 := (PS_c_key K m hQB hm hm0 H hHK hH hq j0 hj0 Z' hZ' a1 b1).1
      have i3 := (PS_c_key K m hQB hm hm0 H hHK hH hq j0 hj0 (Z + Z') (K.add_mem hZ hZ')
        (by rw [map_add, a0, a1, add_zero]) (by rw [map_add, b0, b1, add_zero])).1
      rw [colL_apply, colL_apply]
      have e : col (Z + Z') j0 = col Z j0 + col Z' j0 := rfl
      rw [e] at i3
      simp only [ip, Pi.add_apply] at i1 i2 i3 ⊢
      linear_combination (1 / 2 : ℂ) * (i3 - i1 - i2)
  rw [hb, finrank_bot] at r
  omega

theorem QB_map_rs (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) : Module.finrank ℂ (K.map rs) ≤ 3 := by
  have hle : K.map rs ≤ sumZero 4 := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [mem_Vs]
    obtain ⟨κ, θ, hc, -⟩ := hQB Y hY
    have hm' := hm
    rw [Fin.sum_univ_five] at hm'
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    have h3 := hc 3
    have h4 := hc 4
    simp only [tau, col] at h0 h1 h2 h3 h4
    simp only [tau, rs_apply]
    linear_combination h0 + h1 + h2 + h3 + h4 + κ * hm'
  exact (Submodule.finrank_mono hle).trans
    ((finrank_sumZero (n := 4) (by norm_num)).trans (by norm_num))

theorem PS_c_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) : Module.finrank ℂ K ≤ 5 := by
  obtain ⟨j0, hj0⟩ : ∃ j0, m j0 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm0 (funext hc)
  have hN0 := PS_N0_le K m hQB hm hm0 H hHK hH hq j0 hj0
  have hN : Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) ≤ 2 := by
    have r := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (colsumL j0)
    have h1 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0)) ≤ 1 := by
      have h := Submodule.finrank_le ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0))
      rw [Module.finrank_self] at h
      exact h
    omega
  have hS := QB_map_rs K m hQB hm
  have r := rank_nullity K rs
  omega

theorem NCOL_P3_two_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) : m 0 * m 1 = 0 := by
  by_contra hprod
  have hm0' : m 0 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hmne : m ≠ 0 := fun h => hm0' (congrFun h 0)
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨κ', hc', Yf, hYf, hnf, hff⟩ := PS_b_core K m hQB hm hmne H hHK hH hq Z hZ hZ0
  have hkk : κ' = κ := by
    have h : κ' * m 0 = κ * m 0 := (hc' 0).symm.trans (hκ 0)
    exact mul_right_cancel₀ hm0' h
  rw [hkk] at hnf hff
  have hν : ip (rs Yf) (rs Yf) ≠ 0 := by
    rw [hff]
    intro h
    apply hκ0
    have h' : κ * κ = 0 := by linear_combination (4 / 3 : ℂ) * h
    exact mul_self_eq_zero.mp h'
  have hg1 : ∀ i, phi 1 Yf i = -phi 0 Yf i := by
    intro i
    simp only [phi_apply, rs_apply, (hsupp Yf hYf i).1, (hsupp Yf hYf i).2.1,
      (hsupp Yf hYf i).2.2]
    ring
  have hg2 : ∀ i, phi 2 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hsupp Yf hYf i).1]
    ring
  have hg3 : ∀ i, phi 3 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hsupp Yf hYf i).2.1]
    ring
  have hg4 : ∀ i, phi 4 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hsupp Yf hYf i).2.2]
    ring
  have hrel : ∀ i, (m 0 - m 1) * phi 0 Yf i + (m 0 + m 1) * rs Yf i = 0 := by
    intro i
    have hrow := congrFun hZ0 i
    rw [rs_apply, hnf 0 i, hnf 1 i, hnf 2 i, hnf 3 i, hnf 4 i] at hrow
    simp only [Pi.zero_apply] at hrow
    linear_combination hrow - (κ / 4) * hm' - m 1 * hg1 i - m 2 * hg2 i - m 3 * hg3 i
      - m 4 * hg4 i + rs Yf i * hm'
  have n0 := ip_phi H hH Yf Yf hYf hYf 0
  have h4 : ip (rs Yf) (rs Yf) * (m 0 * m 1) = 0 := by
    simp only [ip] at n0 ⊢
    linear_combination (1 / 4 : ℂ) * (m 0 - m 1) ^ 2 * n0
      - (1 / 4 : ℂ) * (((m 0 - m 1) * phi 0 Yf 0 - (m 0 + m 1) * rs Yf 0) * hrel 0
        + ((m 0 - m 1) * phi 0 Yf 1 - (m 0 + m 1) * rs Yf 1) * hrel 1
        + ((m 0 - m 1) * phi 0 Yf 2 - (m 0 + m 1) * rs Yf 2) * hrel 2
        + ((m 0 - m 1) * phi 0 Yf 3 - (m 0 + m 1) * rs Yf 3) * hrel 3)
  exact hprod ((mul_eq_zero.mp h4).resolve_left hν)

theorem NCOL_P3_one_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 1) = 0 ∧ Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) : m 0 = 0 := by
  by_contra hm0'
  have hmne : m ≠ 0 := fun h => hm0' (congrFun h 0)
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨κ', hc', Yf, hYf, hnf, hff⟩ := PS_b_core K m hQB hm hmne H hHK hH hq Z hZ hZ0
  have hkk : κ' = κ := by
    have h : κ' * m 0 = κ * m 0 := (hc' 0).symm.trans (hκ 0)
    exact mul_right_cancel₀ hm0' h
  rw [hkk] at hnf hff
  have hs := fun i => hsupp Yf hYf i
  have hg0 : ∀ i, phi 0 Yf i = rs Yf i := by
    intro i
    simp only [phi_apply, rs_apply, (hs i).1, (hs i).2.1, (hs i).2.2.1, (hs i).2.2.2]
    ring
  have hg1 : ∀ i, phi 1 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hs i).1]
    ring
  have hg2 : ∀ i, phi 2 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hs i).2.1]
    ring
  have hg3 : ∀ i, phi 3 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hs i).2.2.1]
    ring
  have hg4 : ∀ i, phi 4 Yf i = -rs Yf i := by
    intro i
    rw [phi_apply, (hs i).2.2.2]
    ring
  have hf : ∀ i, rs Yf i = 0 := by
    intro i
    have hrow := congrFun hZ0 i
    rw [rs_apply, hnf 0 i, hnf 1 i, hnf 2 i, hnf 3 i, hnf 4 i] at hrow
    simp only [Pi.zero_apply] at hrow
    have h2 : (2 * m 0) * rs Yf i = 0 := by
      linear_combination hrow - (κ / 4) * hm' - m 0 * hg0 i - m 1 * hg1 i - m 2 * hg2 i
        - m 3 * hg3 i - m 4 * hg4 i + rs Yf i * hm'
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero hm0')
  have hzero : ip (rs Yf) (rs Yf) = 0 := by
    simp only [ip]
    rw [hf 0, hf 1, hf 2, hf 3]
    ring
  rw [hzero] at hff
  apply hκ0
  have h' : κ * κ = 0 := by linear_combination (-4 / 3 : ℂ) * hff
  exact mul_self_eq_zero.mp h'

theorem phi_colE (n j : Fin 5) (x : V4) (i : Fin 4) :
    phi j (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) i =
      if j = n then x i else -x i := by
  rw [phi_apply, rs_apply]
  fin_cases n <;> fin_cases j <;>
    simp (config := {decide := true}) only [ite_true, ite_false, add_zero, zero_add] <;> ring

theorem rs_colE (n : Fin 5) (x : V4) :
    rs (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) = x := by
  funext i
  rw [rs_apply]
  fin_cases n <;> simp (config := {decide := true}) only [ite_true, ite_false, add_zero, zero_add]

theorem sc_key (m : Fin 5 → ℂ) (hm : ∑ a, m a = 0)
    (H : Submodule ℂ M45) (hH : SLev H) (Z : M45) (hZ0 : rs Z = 0) (κ : ℂ)
    (Yf : M45) (hYf : Yf ∈ H) (hnf : ∀ j, ∀ i, Z (i, j) = κ * m j / 4 + m j * phi j Yf i)
    (n : Fin 5) (x : V4) (hE : (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) ∈ H) :
    m n * ip (rs Yf) x = 0 := by
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  have hR : ∀ i, m 0 * phi 0 Yf i + m 1 * phi 1 Yf i + m 2 * phi 2 Yf i + m 3 * phi 3 Yf i
      + m 4 * phi 4 Yf i = 0 := by
    intro i
    have hrow := congrFun hZ0 i
    rw [rs_apply, hnf 0 i, hnf 1 i, hnf 2 i, hnf 3 i, hnf 4 i] at hrow
    simp only [Pi.zero_apply] at hrow
    linear_combination hrow - (κ / 4) * hm'
  have hiso : ∀ j, ip (phi j Yf) (fun i => if j = n then x i else -x i) = ip (rs Yf) x := by
    intro j
    have h := ip_phi H hH Yf _ hYf hE j
    rw [rs_colE] at h
    have e : phi j (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) =
        fun i => if j = n then x i else -x i := funext (phi_colE n j x)
    rw [e] at h
    exact h
  have R : m 0 * ip (phi 0 Yf) x + m 1 * ip (phi 1 Yf) x + m 2 * ip (phi 2 Yf) x
      + m 3 * ip (phi 3 Yf) x + m 4 * ip (phi 4 Yf) x = 0 := by
    simp only [ip]
    linear_combination x 0 * hR 0 + x 1 * hR 1 + x 2 * hR 2 + x 3 * hR 3
  have e0 := hiso 0
  have e1 := hiso 1
  have e2 := hiso 2
  have e3 := hiso 3
  have e4 := hiso 4
  fin_cases n <;>
    simp (config := {decide := true}) only [ite_true, ite_false] at e0 e1 e2 e3 e4 <;>
    simp only [ip, Pi.neg_apply] at e0 e1 e2 e3 e4 R
  · have key : m 0 * ip (rs Yf) x = 0 := by
      simp only [ip]
      linear_combination (1 / 2 : ℂ) * (R - m 0 * e0 + m 1 * e1 + m 2 * e2 + m 3 * e3 + m 4 * e4
        + (rs Yf 0 * x 0 + rs Yf 1 * x 1 + rs Yf 2 * x 2 + rs Yf 3 * x 3) * hm')
    exact key
  · have key : m 1 * ip (rs Yf) x = 0 := by
      simp only [ip]
      linear_combination (1 / 2 : ℂ) * (R + m 0 * e0 - m 1 * e1 + m 2 * e2 + m 3 * e3 + m 4 * e4
        + (rs Yf 0 * x 0 + rs Yf 1 * x 1 + rs Yf 2 * x 2 + rs Yf 3 * x 3) * hm')
    exact key
  · have key : m 2 * ip (rs Yf) x = 0 := by
      simp only [ip]
      linear_combination (1 / 2 : ℂ) * (R + m 0 * e0 + m 1 * e1 - m 2 * e2 + m 3 * e3 + m 4 * e4
        + (rs Yf 0 * x 0 + rs Yf 1 * x 1 + rs Yf 2 * x 2 + rs Yf 3 * x 3) * hm')
    exact key
  · have key : m 3 * ip (rs Yf) x = 0 := by
      simp only [ip]
      linear_combination (1 / 2 : ℂ) * (R + m 0 * e0 + m 1 * e1 + m 2 * e2 - m 3 * e3 + m 4 * e4
        + (rs Yf 0 * x 0 + rs Yf 1 * x 1 + rs Yf 2 * x 2 + rs Yf 3 * x 3) * hm')
    exact key
  · have key : m 4 * ip (rs Yf) x = 0 := by
      simp only [ip]
      linear_combination (1 / 2 : ℂ) * (R + m 0 * e0 + m 1 * e1 + m 2 * e2 + m 3 * e3 - m 4 * e4
        + (rs Yf 0 * x 0 + rs Yf 1 * x 1 + rs Yf 2 * x 2 + rs Yf 3 * x 3) * hm')
    exact key

theorem NCOL_P_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hspan : ∀ v : V4, tau v = 0 →
      (∀ (n : Fin 5) (x : V4), (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) ∈ H → ip v x = 0) → v = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) :
    ∃ (n : Fin 5) (x : V4), x ≠ 0 ∧ (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) ∈ H ∧ m n = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨j0, hj0'⟩ := Function.ne_iff.mp hm0
  have hj0 : m j0 ≠ 0 := hj0'
  obtain ⟨κ', hc', Yf, hYf, hnf, hff⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq Z hZ hZ0
  have hf : rs Yf = 0 := by
    apply hspan _ (tau_rs H hH Yf hYf)
    intro n x hE
    by_cases hx : x = 0
    · rw [hx]
      simp [ip]
    · have h := sc_key m hm H hH Z hZ0 κ' Yf hYf hnf n x hE
      exact (mul_eq_zero.mp h).resolve_left (hcon n x hx hE)
  have h0 : ip (rs Yf) (rs Yf) = 0 := by
    rw [hf]
    simp [ip]
  rw [h0] at hff
  have hk' : κ' * κ' = 0 := by linear_combination (-4 / 3 : ℂ) * hff
  have hk0 : κ' = 0 := mul_self_eq_zero.mp hk'
  have h1 : κ * m j0 = κ' * m j0 := (hκ j0).symm.trans (hc' j0)
  rw [hk0, zero_mul] at h1
  exact hκ0 ((mul_eq_zero.mp h1).resolve_right hj0)

theorem rowE_rs (i : Fin 4) (m : Fin 5 → ℂ) (hm : ∑ a, m a = 0) : rs (rowE i m) = 0 := by
  funext k
  rw [rs_apply]
  rw [Fin.sum_univ_five] at hm
  by_cases h : k = i
  · simp only [rowE, if_pos h, Pi.zero_apply]
    linear_combination hm
  · simp [rowE, h]

theorem rowE_colsum (i : Fin 4) (u : Fin 5 → ℂ) (j : Fin 5) : colsumL j (rowE i u) = u j := by
  simp [colsumL_apply, rowE]

theorem tau_col_colsum (Y : M45) (j : Fin 5) : tau (col Y j) = colsumL j Y := by
  simp only [colsumL_apply, Fin.sum_univ_four, tau, col]

theorem PR_RED_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hNS : ∀ K' : Submodule ℂ M45, K' ≤ K → Module.finrank ℂ K' = 4 → H ≤ K' →
      (∃ Y ∈ K', ∃ j, tau (col Y j) ≠ 0) → ∃ i : Fin 4, rowE i m ∈ K') :
    Module.finrank ℂ K ≤ 4 := by
  by_contra h5
  push_neg at h5
  obtain ⟨j0, hj0'⟩ := Function.ne_iff.mp hm0
  have hj0 : m j0 ≠ 0 := hj0'
  have hbot := Bi H hH hq
  have hH3 : Module.finrank ℂ H = 3 := by
    have r := rank_nullity H rs
    rw [hbot, finrank_bot] at r
    omega
  have hS := QB_map_rs K m hQB hm
  have hN0 := PS_N0_le K m hQB hm hm0 H hHK hH hq j0 hj0
  have rK := rank_nullity K rs
  have rN := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (colsumL j0)
  have hc1 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0)) ≤ 1 := by
    have h := Submodule.finrank_le ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0))
    rw [Module.finrank_self] at h
    exact h
  have hA : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL j0) : Submodule ℂ M45) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  have hB : ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  obtain ⟨Zs, hZsm, hZs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  obtain ⟨c0, hc0m, hc00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨Z, hZm, hZc⟩ := hc0m
  obtain ⟨⟨hZsK, hZsrs⟩, hZscs⟩ := hZsm
  obtain ⟨hZK, hZrs⟩ := hZm
  have hZsrs' : rs Zs = 0 := LinearMap.mem_ker.mp hZsrs
  have hZscs' : colsumL j0 Zs = 0 := LinearMap.mem_ker.mp hZscs
  have hZrs' : rs Z = 0 := LinearMap.mem_ker.mp hZrs
  obtain ⟨Z1, hZ1K, hZ1rs, hZ1cs⟩ : ∃ Z1 ∈ K, rs Z1 = 0 ∧ colsumL j0 Z1 = m j0 :=
    ⟨(m j0 / c0) • Z, K.smul_mem _ hZK, by rw [map_smul, hZrs', smul_zero],
      by rw [map_smul, hZc, smul_eq_mul, div_mul_cancel₀ _ hc00]⟩
  have key : ∀ t : ℂ, ∃ i : Fin 4, rowE i m = Z1 + t • Zs := by
    intro t
    have hWK : Z1 + t • Zs ∈ K := K.add_mem hZ1K (K.smul_mem t hZsK)
    have hWrs : rs (Z1 + t • Zs) = 0 := by
      rw [map_add, map_smul, hZ1rs, hZsrs', smul_zero, add_zero]
    have hWcs : colsumL j0 (Z1 + t • Zs) = m j0 := by
      rw [map_add, map_smul, hZ1cs, hZscs', smul_zero, add_zero]
    have hW0 : Z1 + t • Zs ≠ 0 := by
      intro h
      rw [h, map_zero] at hWcs
      exact hj0 hWcs.symm
    have hinf : (H ⊓ Submodule.span ℂ {Z1 + t • Zs} : Submodule ℂ M45) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxH, hxS⟩
      rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hxS
      obtain ⟨c, rfl⟩ := hxS
      have hrs0 : rs (c • (Z1 + t • Zs)) = 0 := by rw [map_smul, hWrs, smul_zero]
      have hmem : c • (Z1 + t • Zs) ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
        Submodule.mem_inf.mpr ⟨hxH, LinearMap.mem_ker.mpr hrs0⟩
      rw [hbot] at hmem
      exact hmem
    have hfr : Module.finrank ℂ (H ⊔ Submodule.span ℂ {Z1 + t • Zs} : Submodule ℂ M45) = 4 := by
      have hs := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span ℂ {Z1 + t • Zs})
      rw [hinf, finrank_bot, finrank_span_singleton hW0, hH3] at hs
      omega
    have hle : (H ⊔ Submodule.span ℂ {Z1 + t • Zs} : Submodule ℂ M45) ≤ K :=
      sup_le hHK ((Submodule.span_singleton_le_iff_mem _ _).mpr hWK)
    have hmemW : Z1 + t • Zs ∈ (H ⊔ Submodule.span ℂ {Z1 + t • Zs} : Submodule ℂ M45) :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have hτ : tau (col (Z1 + t • Zs) j0) ≠ 0 := by
      rw [tau_col_colsum, hWcs]
      exact hj0
    obtain ⟨i, hi⟩ := hNS _ hle hfr le_sup_left ⟨Z1 + t • Zs, hmemW, j0, hτ⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hi
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hrsy : rs y = 0 := by
      have h := congrArg rs hyz
      rw [map_add, map_smul, hWrs, smul_zero, add_zero, rowE_rs i m hm] at h
      exact h
    have hy0 : y = 0 := by
      have hmem : y ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
        Submodule.mem_inf.mpr ⟨hy, LinearMap.mem_ker.mpr hrsy⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    have hc1 : c = 1 := by
      have h := congrArg (colsumL j0) hyz
      rw [map_add, map_smul, hWcs, hy0, map_zero, zero_add, smul_eq_mul, rowE_colsum] at h
      exact mul_right_cancel₀ hj0 (h.trans (one_mul _).symm)
    rw [hy0, hc1, one_smul, zero_add] at hyz
    exact ⟨i, hyz.symm⟩
  choose f hf using fun t : Fin 5 => key ((t : ℕ) : ℂ)
  obtain ⟨t, t', htt, hft⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have h1 := hf t
  have h2 := hf t'
  rw [hft] at h1
  have e : Z1 + ((t : ℕ) : ℂ) • Zs = Z1 + ((t' : ℕ) : ℂ) • Zs := h1.symm.trans h2
  have e2 : ((t : ℕ) : ℂ) • Zs = ((t' : ℕ) : ℂ) • Zs := add_left_cancel e
  have e3 : (((t : ℕ) : ℂ) - ((t' : ℕ) : ℂ)) • Zs = 0 := by rw [sub_smul, e2, sub_self]
  rcases smul_eq_zero.mp e3 with h | h
  · apply htt
    have h' : ((t : ℕ) : ℂ) = ((t' : ℕ) : ℂ) := sub_eq_zero.mp h
    exact Fin.val_injective (Nat.cast_injective h')
  · exact hZs0 h

theorem iso_triple (a b c : V4) (ha : a ≠ 0) (h1 : tau a = 0) (h2 : tau b = 0)
    (haa : ip a a = 0) (hbb : ip b b = 0) (hcc : ip c c = 0)
    (hs : ∀ i, a i + b i + c i = 0) : (∃ s : ℂ, b = s • a) ∧ (∃ t : ℂ, c = t • a) := by
  have hab : ip a b = 0 := by
    have s0 := hs 0
    have s1 := hs 1
    have s2 := hs 2
    have s3 := hs 3
    simp only [ip] at haa hbb hcc ⊢
    linear_combination (1 / 2 : ℂ) * (hcc - haa - hbb)
      - (1 / 2 : ℂ) * ((c 0 - a 0 - b 0) * s0 + (c 1 - a 1 - b 1) * s1
        + (c 2 - a 2 - b 2) * s2 + (c 3 - a 3 - b 3) * s3)
  obtain ⟨s, hs'⟩ := Q4 a b ha h1 haa h2 hbb hab
  refine ⟨⟨s, hs'⟩, ⟨-(1 + s), ?_⟩⟩
  funext i
  have h := hs i
  have hb : b i = s * a i := congrFun hs' i
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination h - hb

theorem pc_neutral3 (v : V4) (a b c : ℂ) (h1 : tau v = 0) (h2 : ip v v = 0) :
    pc (fun i => 1 + a * v i) (fun i => 1 + b * v i) (fun i => 1 + c * v i) (fun _ => 1)
      = 24 + 2 * a * b * c * t3 v v v := by
  simp only [tau, ip] at h1 h2
  simp (config := {decide := true}) only [pc, t3, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  linear_combination (6 * (a + b + c) + 2 * (a * b + a * c + b * c) * (v 0 + v 1 + v 2 + v 3)
    + a * b * c * ((v 0 + v 1 + v 2 + v 3) ^ 2
      - 3 * (v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3))) * h1
    - 2 * (a * b + a * c + b * c) * h2

theorem P4_neutral3 (Z : M45) (v : V4) (l0 l1 l2 : ℂ) (h1 : tau v = 0) (h2 : ip v v = 0)
    (hz0 : col Z 0 = l0 • v) (hz1 : col Z 1 = l1 • v) (hz2 : col Z 2 = l2 • v)
    (hz4 : col Z 4 = 0) :
    P4 3 (fun p => 1 + Z p) = 24 + 2 * l0 * l1 * l2 * t3 v v v := by
  rw [P4_c3]
  have c0 : col (fun p : Fin 4 × Fin 5 => 1 + Z p) 0 = fun i => 1 + l0 * v i := by
    funext i
    show 1 + Z (i, 0) = 1 + l0 * v i
    have h := congrFun hz0 i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [show Z (i, 0) = col Z 0 i from rfl, h]
  have c1 : col (fun p : Fin 4 × Fin 5 => 1 + Z p) 1 = fun i => 1 + l1 * v i := by
    funext i
    show 1 + Z (i, 1) = 1 + l1 * v i
    have h := congrFun hz1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [show Z (i, 1) = col Z 1 i from rfl, h]
  have c2 : col (fun p : Fin 4 × Fin 5 => 1 + Z p) 2 = fun i => 1 + l2 * v i := by
    funext i
    show 1 + Z (i, 2) = 1 + l2 * v i
    have h := congrFun hz2 i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [show Z (i, 2) = col Z 2 i from rfl, h]
  have c4 : col (fun p : Fin 4 × Fin 5 => 1 + Z p) 4 = fun _ => 1 := by
    funext i
    show 1 + Z (i, 4) = 1
    have h := congrFun hz4 i
    simp [show Z (i, 4) = col Z 4 i from rfl, h]
  rw [c0, c1, c2, c4]
  exact pc_neutral3 v l0 l1 l2 h1 h2

theorem PR3_step1 (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (h0 : m 0 ≠ 0) (h1 : m 1 ≠ 0) (h2 : m 2 ≠ 0) (h3 : m 3 = 0)
    (h4 : m 4 = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Zs : M45) (hZs : Zs ∈ K) (hZs0 : rs Zs = 0)
    (hcs : colsumL 0 Zs = 0) (hne : Zs ≠ 0) (hneut : P4 3 (fun p => 1 + Zs p) = 24) :
    ∃ v : V4, v ≠ 0 ∧ tau v = 0 ∧ ip v v = 0 ∧ t3 v v v = 0 ∧
      ∃ s t : ℂ, s ≠ 0 ∧ t ≠ 0 ∧ col Zs 0 = v ∧ col Zs 1 = s • v ∧ col Zs 2 = t • v ∧
        col Zs 3 = 0 ∧ col Zs 4 = 0 := by
  have hm0 : m ≠ 0 := fun h => h0 (congrFun h 0)
  obtain ⟨κ, hc, Yf, hYf, hnf, hff⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq Zs hZs hZs0
  have hκ : κ = 0 := by
    have e := hc 0
    rw [tau_col_colsum, hcs] at e
    exact (mul_eq_zero.mp e.symm).resolve_right h0
  have hcs1 : colsumL 1 Zs = 0 := by
    rw [← tau_col_colsum, hc 1, hκ, zero_mul]
  have hcs2 : colsumL 2 Zs = 0 := by
    rw [← tau_col_colsum, hc 2, hκ, zero_mul]
  obtain ⟨i0, hi0⟩ := PS_c_key K m hQB hm hm0 H hHK hH hq 0 h0 Zs hZs hZs0 hcs
  obtain ⟨i1, hi1⟩ := PS_c_key K m hQB hm hm0 H hHK hH hq 1 h1 Zs hZs hZs0 hcs1
  obtain ⟨i2, hi2⟩ := PS_c_key K m hQB hm hm0 H hHK hH hq 2 h2 Zs hZs hZs0 hcs2
  have c3 : col Zs 3 = 0 := by
    funext i
    show Zs (i, 3) = 0
    rw [hnf 3 i, h3]
    ring
  have c4 : col Zs 4 = 0 := by
    funext i
    show Zs (i, 4) = 0
    rw [hnf 4 i, h4]
    ring
  have hv0 : col Zs 0 ≠ 0 := fun h => hne (hi0 h)
  have hv1 : col Zs 1 ≠ 0 := fun h => hne (hi1 h)
  have hv2 : col Zs 2 ≠ 0 := fun h => hne (hi2 h)
  have hsum : ∀ i, col Zs 0 i + col Zs 1 i + col Zs 2 i = 0 := by
    intro i
    have h := congrFun hZs0 i
    rw [rs_apply] at h
    have e3' : Zs (i, 3) = 0 := congrFun c3 i
    have e4' : Zs (i, 4) = 0 := congrFun c4 i
    have h' : Zs (i, 0) + Zs (i, 1) + Zs (i, 2) + Zs (i, 3) + Zs (i, 4) = 0 := h
    show Zs (i, 0) + Zs (i, 1) + Zs (i, 2) = 0
    linear_combination h' - e3' - e4'
  have ht0 : tau (col Zs 0) = 0 := by rw [tau_col_colsum, hcs]
  have ht1 : tau (col Zs 1) = 0 := by rw [tau_col_colsum, hcs1]
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ :=
    iso_triple (col Zs 0) (col Zs 1) (col Zs 2) hv0 ht0 ht1 i0 i1 i2 hsum
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hv1
    rw [hs, zero_smul]
  have ht0' : t ≠ 0 := by
    rintro rfl
    apply hv2
    rw [ht, zero_smul]
  have hP := P4_neutral3 Zs (col Zs 0) 1 s t ht0 i0 (by rw [one_smul]) hs ht c4
  rw [hneut] at hP
  have h3v : t3 (col Zs 0) (col Zs 0) (col Zs 0) = 0 := by
    have hh : (2 * s * t) * t3 (col Zs 0) (col Zs 0) (col Zs 0) = 0 := by
      linear_combination -hP
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero hs0) ht0')
  exact ⟨col Zs 0, hv0, ht0, i0, h3v, s, t, hs0, ht0', rfl, hs, ht, c3, c4⟩

theorem phi_inj (H : Submodule ℂ M45) (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (j : Fin 5) (Y : M45) (hY : Y ∈ H) (h0 : phi j Y = 0) : Y = 0 := by
  have hrs : rs Y = 0 := by
    apply nondeg
    · exact tau_rs H hH Y hY
    · intro v hv
      have hv' : v ∈ H.map rs := by
        rw [(phi_onto H hH hq 0).1, mem_Vs]
        exact hv
      obtain ⟨Y', hY', rfl⟩ := hv'
      rw [← ip_phi H hH Y Y' hY hY' j, h0]
      simp [ip]
  have hmem : Y ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
    Submodule.mem_inf.mpr ⟨hY, LinearMap.mem_ker.mpr hrs⟩
  rw [Bi H hH hq] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

theorem PS_bil (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Z Z' : M45) (hZ : Z ∈ K) (hZ' : Z' ∈ K)
    (hZ0 : rs Z = 0) (hZ0' : rs Z' = 0) :
    ∃ κ κ' : ℂ, ∃ Yf ∈ H, ∃ Yf' ∈ H, (∀ j, tau (col Z j) = κ * m j) ∧
      (∀ j, tau (col Z' j) = κ' * m j) ∧
      (∀ j, ∀ i, Z (i, j) = κ * m j / 4 + m j * phi j Yf i) ∧
      (∀ j, ∀ i, Z' (i, j) = κ' * m j / 4 + m j * phi j Yf' i) ∧
      ip (rs Yf) (rs Yf) = 3 * κ ^ 2 / 4 ∧ ip (rs Yf') (rs Yf') = 3 * κ' ^ 2 / 4 ∧
      ip (rs Yf) (rs Yf') = 3 * κ * κ' / 4 := by
  obtain ⟨j0, hj0'⟩ := Function.ne_iff.mp hm0
  have hj0 : m j0 ≠ 0 := hj0'
  obtain ⟨κ, hc, Yf, hYf, hnf, hff⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq Z hZ hZ0
  obtain ⟨κ', hc', Yf', hYf', hnf', hff'⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq Z' hZ' hZ0'
  obtain ⟨κw, hcw, Yw, hYw, hnfw, hffw⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq (Z + Z')
    (K.add_mem hZ hZ') (by rw [map_add, hZ0, hZ0', add_zero])
  have hkw : κw = κ + κ' := by
    have e : tau (col (Z + Z') j0) = tau (col Z j0) + tau (col Z' j0) := by
      simp only [tau, col, Pi.add_apply]
      ring
    rw [hcw, hc, hc'] at e
    exact mul_right_cancel₀ hj0 (e.trans (add_mul κ κ' (m j0)).symm)
  have hYsum : Yw = Yf + Yf' := by
    have hphi : phi j0 (Yw - (Yf + Yf')) = 0 := by
      funext i
      have e1 := hnfw j0 i
      have e2 := hnf j0 i
      have e3 := hnf' j0 i
      have e4 : (Z + Z') (i, j0) = Z (i, j0) + Z' (i, j0) := rfl
      rw [map_sub, map_add]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
      rw [e4, e2, e3, hkw] at e1
      have h : m j0 * (phi j0 Yw i - (phi j0 Yf i + phi j0 Yf' i)) = 0 := by
        linear_combination -e1
      exact (mul_eq_zero.mp h).resolve_left hj0
    have h := phi_inj H hH hq j0 _ (H.sub_mem hYw (H.add_mem hYf hYf')) hphi
    exact sub_eq_zero.mp h
  rw [hYsum, hkw, map_add] at hffw
  refine ⟨κ, κ', Yf, hYf, Yf', hYf', hc, hc', hnf, hnf', hff, hff', ?_⟩
  simp only [ip, Pi.add_apply] at hffw hff hff' ⊢
  linear_combination (1 / 2 : ℂ) * (hffw - hff - hff')

theorem PR3_step2 (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (h0 : m 0 ≠ 0) (h1 : m 1 ≠ 0) (h2 : m 2 ≠ 0) (h3 : m 3 = 0)
    (h4 : m 4 = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Z Zs : M45) (hZ : Z ∈ K) (hZs : Zs ∈ K)
    (hZ0 : rs Z = 0) (hZs0 : rs Zs = 0) (hcZ : colsumL 0 Z = m 0) (hcs : colsumL 0 Zs = 0)
    (v : V4) (l0 l1 l2 : ℂ) (hl0 : l0 ≠ 0) (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (hv0 : col Zs 0 = l0 • v) (hv1 : col Zs 1 = l1 • v) (hv2 : col Zs 2 = l2 • v)
    (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap) (ht : tau v = 0) (hi : ip v v = 0)
    (h3v : t3 v v v = 0) :
    ∃ β p0 p1 p2 : ℂ, 16 * kap * β ^ 2 = 3 ∧ p0 + p1 + p2 = 0 ∧
      col Z 0 = Qv v (m 0 / 4) p0 (β * m 0) 0 ∧ col Z 1 = Qv v (m 1 / 4) p1 (β * m 1) 0 ∧
      col Z 2 = Qv v (m 2 / 4) p2 (β * m 2) 0 := by
  have hm0 : m ≠ 0 := fun h => h0 (congrFun h 0)
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨κ, κ', Yf, hYf, Yfs, hYfs, hc, hc', hnf, hnfs, hff, hffs, hfs⟩ :=
    PS_bil K m hQB hm hm0 H hHK hH hq Z Zs hZ hZs hZ0 hZs0
  have hκ : κ = 1 := by
    have e := hc 0
    rw [tau_col_colsum, hcZ] at e
    exact mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)
  have hκ' : κ' = 0 := by
    have e := hc' 0
    rw [tau_col_colsum, hcs] at e
    exact (mul_eq_zero.mp e.symm).resolve_right h0
  rw [hκ, hκ'] at hfs
  rw [hκ] at hff hnf
  rw [hκ'] at hnfs
  have colfact : ∀ j : Fin 5, ∀ l : ℂ, m j ≠ 0 → l ≠ 0 → col Zs j = l • v →
      ∃ p q : ℂ, (fun i => m j * phi j Yf i) = Qv v 0 p q 0 ∧ 16 * kap * q ^ 2 = 3 * m j ^ 2 := by
    intro j l hj hl hvj
    have hw_t : tau (fun i => m j * phi j Yf i) = 0 := by
      have h := tau_phi H hH Yf hYf j
      simp only [tau] at h ⊢
      linear_combination m j * h
    have hzs : ∀ i, Zs (i, j) = m j * phi j Yfs i := by
      intro i
      rw [hnfs j i]
      ring
    have hvj' : ∀ i, l * v i = m j * phi j Yfs i := by
      intro i
      have h := congrFun hvj i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      have h' : Zs (i, j) = l * v i := h
      rw [← h', hzs i]
    have hvw : ip v (fun i => m j * phi j Yf i) = 0 := by
      have hiso := ip_phi H hH Yfs Yf hYfs hYf j
      have hfs' : ip (rs Yfs) (rs Yf) = 0 := by
        simp only [ip] at hfs ⊢
        linear_combination hfs
      have key : l * ip v (fun i => m j * phi j Yf i) = 0 := by
        simp only [ip] at hiso hfs' ⊢
        linear_combination (m j * phi j Yf 0) * hvj' 0 + (m j * phi j Yf 1) * hvj' 1
          + (m j * phi j Yf 2) * hvj' 2 + (m j * phi j Yf 3) * hvj' 3
          + m j ^ 2 * hiso + m j ^ 2 * hfs'
      exact (mul_eq_zero.mp key).resolve_left hl
    obtain ⟨p, q, hpq⟩ := vperp1_coords v kap hkap hk ht hi h3v _ hw_t hvw
    have hww : ip (fun i => m j * phi j Yf i) (fun i => m j * phi j Yf i) = 3 * m j ^ 2 / 4 := by
      have hn := ip_phi H hH Yf Yf hYf hYf j
      simp only [ip] at hn hff ⊢
      linear_combination m j ^ 2 * hn + m j ^ 2 * hff
    rw [hpq, ip_Qv v kap hk ht hi h3v] at hww
    exact ⟨p, q, hpq, by linear_combination 4 * hww⟩
  obtain ⟨p0, q0, e0, s0⟩ := colfact 0 l0 h0 hl0 hv0
  obtain ⟨p1, q1, e1, s1⟩ := colfact 1 l1 h1 hl1 hv1
  obtain ⟨p2, q2, e2, s2⟩ := colfact 2 l2 h2 hl2 hv2
  have hsum : Qv v 0 (p0 + p1 + p2) (q0 + q1 + q2) 0 = Qv v 0 0 0 0 := by
    funext i
    have hrow := congrFun hZ0 i
    rw [rs_apply, hnf 0 i, hnf 1 i, hnf 2 i, hnf 3 i, hnf 4 i, h3, h4] at hrow
    have f0 := congrFun e0 i
    have f1 := congrFun e1 i
    have f2 := congrFun e2 i
    simp only [Qv, Pi.zero_apply] at hrow f0 f1 f2 ⊢
    linear_combination hrow - f0 - f1 - f2 - (1 / 4 : ℂ) * hm' + (1 / 4 : ℂ) * h3
      + (1 / 4 : ℂ) * h4
  obtain ⟨-, hP, hQ, -⟩ := Qv_inj v kap hkap hk ht hi h3v _ _ _ _ _ _ _ _ hsum
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, q0 = β * m 0 := ⟨q0 / m 0, (div_mul_cancel₀ q0 h0).symm⟩
  have hβ2 : 16 * kap * β ^ 2 = 3 := by
    rw [hβ] at s0
    apply mul_right_cancel₀ (pow_ne_zero 2 h0)
    linear_combination s0
  have hβ0 : β ≠ 0 := by
    rintro rfl
    norm_num at hβ2
  have h16 : (16 : ℂ) * kap ≠ 0 := mul_ne_zero (by norm_num) hkap
  have hq1 : (q1 - β * m 1) * (q1 + β * m 1) = 0 := by
    have h : 16 * kap * ((q1 - β * m 1) * (q1 + β * m 1)) = 0 := by
      linear_combination s1 - m 1 ^ 2 * hβ2
    exact (mul_eq_zero.mp h).resolve_left h16
  have hq2 : (q2 - β * m 2) * (q2 + β * m 2) = 0 := by
    have h : 16 * kap * ((q2 - β * m 2) * (q2 + β * m 2)) = 0 := by
      linear_combination s2 - m 2 ^ 2 * hβ2
    exact (mul_eq_zero.mp h).resolve_left h16
  have hm3 : m 0 + m 1 + m 2 = 0 := by linear_combination hm' - h3 - h4
  rcases mul_eq_zero.mp hq1 with a1 | a1 <;> rcases mul_eq_zero.mp hq2 with a2 | a2
  · refine ⟨β, p0, p1, p2, hβ2, hP, ?_, ?_, ?_⟩
    · funext i
      show Z (i, 0) = Qv v (m 0 / 4) p0 (β * m 0) 0 i
      have f := congrFun e0 i
      simp only [Qv] at f ⊢
      rw [hnf 0 i]
      linear_combination f + v i ^ 2 * hβ
    · funext i
      show Z (i, 1) = Qv v (m 1 / 4) p1 (β * m 1) 0 i
      have f := congrFun e1 i
      simp only [Qv] at f ⊢
      rw [hnf 1 i]
      linear_combination f + v i ^ 2 * a1
    · funext i
      show Z (i, 2) = Qv v (m 2 / 4) p2 (β * m 2) 0 i
      have f := congrFun e2 i
      simp only [Qv] at f ⊢
      rw [hnf 2 i]
      linear_combination f + v i ^ 2 * a2
  · exfalso
    have h : β * m 2 = 0 := by
      linear_combination (-1 / 2 : ℂ) * (hQ - hβ - a1 - a2 - β * hm3)
    exact (mul_ne_zero hβ0 h2) h
  · exfalso
    have h : β * m 1 = 0 := by
      linear_combination (-1 / 2 : ℂ) * (hQ - hβ - a1 - a2 - β * hm3)
    exact (mul_ne_zero hβ0 h1) h
  · exfalso
    have h : β * m 0 = 0 := by
      linear_combination (1 / 2 : ℂ) * (hQ - hβ - a1 - a2 + β * hm3)
    exact (mul_ne_zero hβ0 h0) h

theorem tau_zero4 : tau (0 : V4) = 0 := by simp [tau]

theorem ip_zero4 (x : V4) : ip x 0 = 0 := by simp [ip]

theorem t3_zero4 (x y : V4) : t3 x y 0 = 0 := by simp [t3]

theorem pc_zero4 (x y z : V4) : pc x y z 0 = 0 := by simp [pc]

theorem pc_Qv3 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (A0 L0 B0 A1 L1 B1 A2 L2 B2 : ℂ) :
    pc (fun i => 1 + Qv v A0 L0 B0 0 i) (fun i => 1 + Qv v A1 L1 B1 0 i)
      (fun i => 1 + Qv v A2 L2 B2 0 i) (fun _ => 1) =
    24 + 6 * (4 * A0 + 4 * A1 + 4 * A2)
      + (2 * (4 * A0 * (4 * A1) + 4 * A0 * (4 * A2) + 4 * A1 * (4 * A2))
        - 2 * (4 * (A0 * A1 + kap * (B0 * B1)) + 4 * (A0 * A2 + kap * (B0 * B2))
          + 4 * (A1 * A2 + kap * (B1 * B2))))
      + (4 * A0 * (4 * A1) * (4 * A2) - 4 * A0 * (4 * (A1 * A2 + kap * (B1 * B2)))
        - 4 * A1 * (4 * (A0 * A2 + kap * (B0 * B2))) - 4 * A2 * (4 * (A0 * A1 + kap * (B0 * B1)))
        + 2 * (4 * (A0 * A1 * A2 + kap * (B0 * B1 * A2 + B0 * A1 * B2 + A0 * B1 * B2
          + B0 * L1 * L2 + L0 * B1 * L2 + L0 * L1 * B2)))) := by
  have e := pc_expand (Qv v A0 L0 B0 0) (Qv v A1 L1 B1 0) (Qv v A2 L2 B2 0) 0 1
  simp only [one_mul, Pi.zero_apply, mul_zero, add_zero, tau_zero4, ip_zero4, t3_zero4,
    pc_zero4] at e
  rw [e]
  simp only [tau_Qv v h1 h2 h3, t3_ip_l, Qv_mul v kap hk, ip_Qv v kap hk h1 h2 h3]
  ring

theorem pr3_alg (p0 p1 l1 m0 m1 : ℂ)
    (hQl : m0 * l1 * (-1 - l1) + m1 * 1 * (-1 - l1) + (-m0 - m1) * 1 * l1 = 0)
    (hB : m0 * (p1 * (-1 - l1) + l1 * (-p0 - p1)) + m1 * (p0 * (-1 - l1) + 1 * (-p0 - p1))
      + (-m0 - m1) * (p0 * l1 + 1 * p1) = 0) :
    (m0 * m1 - (-m0 - m1) ^ 2)
      * (m0 * p1 * (-p0 - p1) + m1 * p0 * (-p0 - p1) + (-m0 - m1) * p0 * p1) ^ 2 = 0 := by
  linear_combination
    ((m0 * m1 - (-m0 - m1) ^ 2) * p0 ^ 2
        * (m0 * p1 * (-p0 - p1) + m1 * p0 * (-p0 - p1) + (-m0 - m1) * p0 * p1)
      + (m0 * m1 - (-m0 - m1) ^ 2) * p0 ^ 2 * (p0 * l1 - p1)
        * (l1 * m0 * p0 + 2 * m0 * p0 + m0 * p1 + 2 * m1 * p0)
      + (m0 * p1 * (-p0 - p1) + m1 * p0 * (-p0 - p1) + (-m0 - m1) * p0 * p1)
        * (l1 * m0 * p0 + 2 * m0 * p0 + m0 * p1 + 2 * m1 * p0) ^ 2) * hQl
    - (1 / 4 : ℂ) * (l1 * m0 * p0 + 2 * m0 * p0 + m0 * p1 + 2 * m1 * p0) ^ 2
      * (m0 * (p1 * (-1 - l1) + l1 * (-p0 - p1)) + m1 * (p0 * (-1 - l1) + 1 * (-p0 - p1))
        + (-m0 - m1) * (p0 * l1 + 1 * p1)) * hB

theorem PR3_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (h0 : m 0 ≠ 0) (h1 : m 1 ≠ 0) (h2 : m 2 ≠ 0) (h3 : m 3 = 0)
    (h4 : m 4 = 0) (hmm : m 0 * m 0 + m 1 * m 1 + m 2 * m 2 ≠ 0)
    (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (hneut : ∀ Y ∈ K, P4 3 (fun p => 1 + Y p) = 24) : Module.finrank ℂ K ≤ 4 := by
  by_contra h5
  push_neg at h5
  have hm0 : m ≠ 0 := fun h => h0 (congrFun h 0)
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  have hm3 : m 0 + m 1 + m 2 = 0 := by linear_combination hm' - h3 - h4
  have hS := QB_map_rs K m hQB hm
  have hN0 := PS_N0_le K m hQB hm hm0 H hHK hH hq 0 h0
  have rK := rank_nullity K rs
  have rN := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (colsumL 0)
  have hcm : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL 0)) ≤ 1 := by
    have h := Submodule.finrank_le ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL 0))
    rw [Module.finrank_self] at h
    exact h
  have hA : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL 0) : Submodule ℂ M45) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  have hB : ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL 0)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  obtain ⟨Zs, hZsm, hZs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  obtain ⟨c0, hc0m, hc00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨Z, hZm, hZc⟩ := hc0m
  obtain ⟨⟨hZsK, hZsrs⟩, hZscs⟩ := hZsm
  obtain ⟨hZK, hZrs⟩ := hZm
  have hZsrs' : rs Zs = 0 := LinearMap.mem_ker.mp hZsrs
  have hZscs' : colsumL 0 Zs = 0 := LinearMap.mem_ker.mp hZscs
  have hZrs' : rs Z = 0 := LinearMap.mem_ker.mp hZrs
  obtain ⟨Z1, hZ1K, hZ1rs, hZ1cs⟩ : ∃ Z1 ∈ K, rs Z1 = 0 ∧ colsumL 0 Z1 = m 0 :=
    ⟨(m 0 / c0) • Z, K.smul_mem _ hZK, by rw [map_smul, hZrs', smul_zero],
      by rw [map_smul, hZc, smul_eq_mul, div_mul_cancel₀ _ hc00]⟩
  obtain ⟨v, hv, ht, hi, h3v, s, t, hs0, ht0, hcol0, hcol1, hcol2, hcol3, hcol4⟩ :=
    PR3_step1 K m hQB hm h0 h1 h2 h3 h4 H hHK hH hq Zs hZsK hZsrs' hZscs' hZs0 (hneut Zs hZsK)
  obtain ⟨q0', q1', q2', q3'⟩ := pow4_iso v ht hi h3v
  have hk : ∀ i, v i ^ 4 = v 0 ^ 4 := by
    intro i
    fin_cases i
    · rfl
    · show v 1 ^ 4 = v 0 ^ 4
      rw [q1', q0']
    · show v 2 ^ 4 = v 0 ^ 4
      rw [q2', q0']
    · show v 3 ^ 4 = v 0 ^ 4
      rw [q3', q0']
  have hkap : v 0 ^ 4 ≠ 0 := by
    intro hz
    apply hv
    funext i
    have h := hk i
    rw [hz] at h
    exact (pow_eq_zero_iff (by norm_num)).mp h
  obtain ⟨β, p0, p1, p2, hβ2, hP, hz0, hz1, hz2⟩ :=
    PR3_step2 K m hQB hm h0 h1 h2 h3 h4 H hHK hH hq Z1 Zs hZ1K hZsK hZ1rs hZsrs' hZ1cs hZscs'
      v 1 s t one_ne_zero hs0 ht0 (by rw [one_smul]; exact hcol0) hcol1 hcol2 (v 0 ^ 4) hkap hk
      ht hi h3v
  have hst : 1 + s + t = 0 := by
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv
    have hrow := congrFun hZsrs' i0
    rw [rs_apply] at hrow
    have e0 : Zs (i0, 0) = v i0 := congrFun hcol0 i0
    have e1 : Zs (i0, 1) = s * v i0 := congrFun hcol1 i0
    have e2 : Zs (i0, 2) = t * v i0 := congrFun hcol2 i0
    have e3 : Zs (i0, 3) = 0 := congrFun hcol3 i0
    have e4 : Zs (i0, 4) = 0 := congrFun hcol4 i0
    have hrow' : Zs (i0, 0) + Zs (i0, 1) + Zs (i0, 2) + Zs (i0, 3) + Zs (i0, 4) = 0 := hrow
    rw [e0, e1, e2, e3, e4] at hrow'
    have h : (1 + s + t) * v i0 = 0 := by linear_combination hrow'
    exact (mul_eq_zero.mp h).resolve_right hi0
  have hZ1c4 : col Z1 4 = 0 := by
    obtain ⟨κ, hc, Yf, hYf, hnf, -⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq Z1 hZ1K hZ1rs
    funext i
    show Z1 (i, 4) = 0
    rw [hnf 4 i, h4]
    ring
  have cubic : ∀ b : ℂ, 8 * v 0 ^ 4 * β * (m 0 * ((p1 + b * s) * (p2 + b * t))
      + m 1 * ((p0 + b * 1) * (p2 + b * t)) + m 2 * ((p0 + b * 1) * (p1 + b * s)))
      - 3 / 4 * (m 0 * m 1 * m 2) = 0 := by
    intro b
    have hY : Z1 + b • Zs ∈ K := K.add_mem hZ1K (K.smul_mem b hZsK)
    have hP4 := hneut _ hY
    rw [P4_c3] at hP4
    have cc0 : col (fun p : Fin 4 × Fin 5 => 1 + (Z1 + b • Zs) p) 0 =
        fun i => 1 + Qv v (m 0 / 4) (p0 + b * 1) (β * m 0) 0 i := by
      funext i
      show 1 + (Z1 (i, 0) + b * Zs (i, 0)) = 1 + Qv v (m 0 / 4) (p0 + b * 1) (β * m 0) 0 i
      have fz : Z1 (i, 0) = Qv v (m 0 / 4) p0 (β * m 0) 0 i := congrFun hz0 i
      have fs : Zs (i, 0) = v i := congrFun hcol0 i
      rw [fz, fs]
      simp only [Qv]
      ring
    have cc1 : col (fun p : Fin 4 × Fin 5 => 1 + (Z1 + b • Zs) p) 1 =
        fun i => 1 + Qv v (m 1 / 4) (p1 + b * s) (β * m 1) 0 i := by
      funext i
      show 1 + (Z1 (i, 1) + b * Zs (i, 1)) = 1 + Qv v (m 1 / 4) (p1 + b * s) (β * m 1) 0 i
      have fz : Z1 (i, 1) = Qv v (m 1 / 4) p1 (β * m 1) 0 i := congrFun hz1 i
      have fs : Zs (i, 1) = s * v i := congrFun hcol1 i
      rw [fz, fs]
      simp only [Qv]
      ring
    have cc2 : col (fun p : Fin 4 × Fin 5 => 1 + (Z1 + b • Zs) p) 2 =
        fun i => 1 + Qv v (m 2 / 4) (p2 + b * t) (β * m 2) 0 i := by
      funext i
      show 1 + (Z1 (i, 2) + b * Zs (i, 2)) = 1 + Qv v (m 2 / 4) (p2 + b * t) (β * m 2) 0 i
      have fz : Z1 (i, 2) = Qv v (m 2 / 4) p2 (β * m 2) 0 i := congrFun hz2 i
      have fs : Zs (i, 2) = t * v i := congrFun hcol2 i
      rw [fz, fs]
      simp only [Qv]
      ring
    have cc4 : col (fun p : Fin 4 × Fin 5 => 1 + (Z1 + b • Zs) p) 4 = fun _ => 1 := by
      funext i
      show 1 + (Z1 (i, 4) + b * Zs (i, 4)) = 1
      have fz : Z1 (i, 4) = 0 := congrFun hZ1c4 i
      have fs : Zs (i, 4) = 0 := congrFun hcol4 i
      rw [fz, fs]
      ring
    rw [cc0, cc1, cc2, cc4, pc_Qv3 v (v 0 ^ 4) hk ht hi h3v] at hP4
    linear_combination hP4
      + ((48 * β ^ 2 * v 0 ^ 4 * m 0 * m 1 + 64 * β ^ 2 * v 0 ^ 4 * m 0
        + 64 * β ^ 2 * v 0 ^ 4 * m 1 - 9 * m 0 * m 1 - 12 * m 0 - 12 * m 1 - 48) / 8) * hm3
      - ((3 * m 0 ^ 2 * m 1 + 4 * m 0 ^ 2 + 3 * m 0 * m 1 ^ 2 + 4 * m 0 * m 1
        + 4 * m 1 ^ 2) / 8) * hβ2
  have E0 := cubic 0
  have E1 := cubic 1
  have Em := cubic (-1)
  have ht' : t = -1 - s := by linear_combination hst
  have hp2 : p2 = -p0 - p1 := by linear_combination hP
  have hm2 : m 2 = -m 0 - m 1 := by linear_combination hm3
  rw [ht', hp2, hm2] at E0 E1 Em
  have hβ0 : β ≠ 0 := by
    rintro rfl
    norm_num at hβ2
  have h16 : 16 * v 0 ^ 4 * β ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hkap) hβ0
  have hQl : m 0 * s * (-1 - s) + m 1 * 1 * (-1 - s) + (-m 0 - m 1) * 1 * s = 0 := by
    have h : (16 * v 0 ^ 4 * β) * (m 0 * s * (-1 - s) + m 1 * 1 * (-1 - s)
        + (-m 0 - m 1) * 1 * s) = 0 := by
      linear_combination E1 + Em - 2 * E0
    exact (mul_eq_zero.mp h).resolve_left h16
  have hBl : m 0 * (p1 * (-1 - s) + s * (-p0 - p1)) + m 1 * (p0 * (-1 - s) + 1 * (-p0 - p1))
      + (-m 0 - m 1) * (p0 * s + 1 * p1) = 0 := by
    have h : (16 * v 0 ^ 4 * β) * (m 0 * (p1 * (-1 - s) + s * (-p0 - p1))
        + m 1 * (p0 * (-1 - s) + 1 * (-p0 - p1)) + (-m 0 - m 1) * (p0 * s + 1 * p1)) = 0 := by
      linear_combination E1 - Em
    exact (mul_eq_zero.mp h).resolve_left h16
  have halg := pr3_alg p0 p1 s (m 0) (m 1) hQl hBl
  have hdet : m 0 * m 1 - (-m 0 - m 1) ^ 2 ≠ 0 := by
    intro h
    apply hmm
    rw [hm2]
    linear_combination -2 * h
  have hQp : m 0 * p1 * (-p0 - p1) + m 1 * p0 * (-p0 - p1) + (-m 0 - m 1) * p0 * p1 = 0 :=
    (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp halg).resolve_left hdet)
  have hfin : m 0 * m 1 * (-m 0 - m 1) = 0 := by
    linear_combination (-4 / 3 : ℂ) * (E0 - 8 * v 0 ^ 4 * β * hQp)
  have h2' : -m 0 - m 1 ≠ 0 := by
    rw [← hm2]
    exact h2
  exact (mul_ne_zero (mul_ne_zero h0 h1) h2') hfin

theorem QBc_of (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) : QBc K m := by
  intro Y hY
  obtain ⟨κ, θ2, h1, -, h3⟩ := LemmaQB K m hdef hm hm0 Y hY
  exact ⟨κ, θ2, h1, h3⟩

theorem ThmPS_a (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    ∃ κ : ℂ, (∀ j, tau (col Z j) = κ * m j) ∧
      ∃ Yf ∈ H, ∀ j, ∀ i, Z (i, j) = κ * m j / 4 + m j * phi j Yf i := by
  have hQB := QBc_of K m hdef hm hm0
  obtain ⟨κ, θ, hc, -⟩ := hQB Z hZ
  exact ⟨κ, hc, PS_nf K m hQB H hHK hH hq Z hZ hZ0 κ hc⟩

theorem NCOL_P3 (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 3) = 0 ∧ Y (i, 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) : m 0 * m 1 * m 2 = 0 := by
  by_cases hm0 : m = 0
  · simp [hm0]
  · exact NCOL_P3_core K m (QBc_of K m hdef hm hm0) hm H hHK hH hq hsupp Z hZ hZ0 κ hκ0 hκ

theorem ThmPS_b (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    ∃ κ : ℂ, (∀ j, tau (col Z j) = κ * m j) ∧ ∃ Yf ∈ H,
      (∀ j, ∀ i, Z (i, j) = κ * m j / 4 + m j * phi j Yf i) ∧
      ip (rs Yf) (rs Yf) = 3 * κ ^ 2 / 4 :=
  PS_b_core K m (QBc_of K m hdef hm hm0) hm hm0 H hHK hH hq Z hZ hZ0

theorem ThmPS_c (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) : Module.finrank ℂ K ≤ 5 :=
  PS_c_core K m (QBc_of K m hdef hm hm0) hm hm0 H hHK hH hq

theorem rs_cperm (σ : Equiv.Perm (Fin 5)) (Y : M45) : rs (cperm σ Y) = rs Y := by
  funext i
  rw [rs_apply, rs_apply]
  have h := Equiv.sum_comp σ (fun j => Y (i, j))
  simp only [Fin.sum_univ_five] at h
  exact h

theorem DefLine_perm (σ : Equiv.Perm (Fin 5)) (K : Submodule ℂ M45) (m : Fin 5 → ℂ)
    (h : DefLine K m) : DefLine (K.map (cperm σ)) (fun a => m (σ a)) := by
  intro Y hY
  obtain ⟨Y0, hY0, rfl⟩ := hY
  obtain ⟨θ, hθ⟩ := h Y0 hY0
  refine ⟨θ, fun a => ?_⟩
  have e := P4_perm σ a (fun p => 1 + Y0 p)
  exact e.trans (hθ (σ a))

theorem NCOL_P3_perm (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (σ : Equiv.Perm (Fin 5))
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, σ 3) = 0 ∧ Y (i, σ 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) : m (σ 0) * m (σ 1) * m (σ 2) = 0 := by
  have hrs : (H.map (cperm σ)).map rs = H.map rs := by
    ext v
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
      exact ⟨Y, hY, (rs_cperm σ Y).symm⟩
    · rintro ⟨Y, hY, rfl⟩
      exact ⟨cperm σ Y, ⟨Y, hY, rfl⟩, rs_cperm σ Y⟩
  have hm' : ∑ a, (fun a => m (σ a)) a = 0 := by
    show ∑ a, m (σ a) = 0
    rw [Equiv.sum_comp σ m]
    exact hm
  have hq' : Module.finrank ℂ ((H.map (cperm σ)).map rs) = 3 := by
    rw [hrs]
    exact hq
  have hsupp' : ∀ Y ∈ H.map (cperm σ), ∀ i, Y (i, 3) = 0 ∧ Y (i, 4) = 0 := by
    rintro _ ⟨Y, hY, rfl⟩ i
    exact hsupp Y hY i
  have hZ0' : rs (cperm σ Z) = 0 := by
    rw [rs_cperm]
    exact hZ0
  exact NCOL_P3 (K.map (cperm σ)) (fun a => m (σ a)) (DefLine_perm σ K m hdef) hm'
    (H.map (cperm σ)) (Submodule.map_mono hHK) (SLev_perm σ H hH) hq' hsupp'
    (cperm σ Z) ⟨Z, hZ, rfl⟩ hZ0' κ hκ0 (fun j => hκ (σ j))

theorem NCOL_P3_two (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) : m 0 * m 1 = 0 := by
  by_cases hm0 : m = 0
  · simp [hm0]
  · exact NCOL_P3_two_core K m (QBc_of K m hdef hm hm0) hm H hHK hH hq hsupp Z hZ hZ0 κ hκ0 hκ

theorem NCOL_P3_one (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 1) = 0 ∧ Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) : m 0 = 0 := by
  by_cases hm0 : m = 0
  · simp [hm0]
  · exact NCOL_P3_one_core K m (QBc_of K m hdef hm hm0) hm H hHK hH hq hsupp Z hZ hZ0 κ hκ0 hκ

theorem NCOL_P3_two_perm (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (σ : Equiv.Perm (Fin 5))
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, σ 2) = 0 ∧ Y (i, σ 3) = 0 ∧ Y (i, σ 4) = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) : m (σ 0) * m (σ 1) = 0 := by
  have hrs : (H.map (cperm σ)).map rs = H.map rs := by
    ext v
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
      exact ⟨Y, hY, (rs_cperm σ Y).symm⟩
    · rintro ⟨Y, hY, rfl⟩
      exact ⟨cperm σ Y, ⟨Y, hY, rfl⟩, rs_cperm σ Y⟩
  have hm' : ∑ a, (fun a => m (σ a)) a = 0 := by
    show ∑ a, m (σ a) = 0
    rw [Equiv.sum_comp σ m]
    exact hm
  have hq' : Module.finrank ℂ ((H.map (cperm σ)).map rs) = 3 := by
    rw [hrs]
    exact hq
  have hsupp' : ∀ Y ∈ H.map (cperm σ), ∀ i, Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0 := by
    rintro _ ⟨Y, hY, rfl⟩ i
    exact hsupp Y hY i
  have hZ0' : rs (cperm σ Z) = 0 := by
    rw [rs_cperm]
    exact hZ0
  exact NCOL_P3_two (K.map (cperm σ)) (fun a => m (σ a)) (DefLine_perm σ K m hdef) hm'
    (H.map (cperm σ)) (Submodule.map_mono hHK) (SLev_perm σ H hH) hq' hsupp'
    (cperm σ Z) ⟨Z, hZ, rfl⟩ hZ0' κ hκ0 (fun j => hκ (σ j))

theorem NCOL_P (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hspan : ∀ v : V4, tau v = 0 →
      (∀ (n : Fin 5) (x : V4), (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) ∈ H → ip v x = 0) → v = 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) (κ : ℂ) (hκ0 : κ ≠ 0)
    (hκ : ∀ j, tau (col Z j) = κ * m j) :
    ∃ (n : Fin 5) (x : V4), x ≠ 0 ∧ (fun p : Fin 4 × Fin 5 => if p.2 = n then x p.1 else 0) ∈ H ∧ m n = 0 :=
  NCOL_P_core K m (QBc_of K m hdef hm hm0) hm hm0 H hHK hH hq hspan Z hZ hZ0 κ hκ0 hκ

def PrincNS4 (m : Fin 5 → ℂ) : Prop :=
  ∀ K' : Submodule ℂ M45, DefLine K' m → Module.finrank ℂ K' = 4 →
    ∀ H : Submodule ℂ M45, H ≤ K' → SLev H → Module.finrank ℂ (H.map rs) = 3 →
    (∃ Y ∈ K', ∃ j, tau (col Y j) ≠ 0) → ∃ i : Fin 4, rowE i m ∈ K'

theorem PR_RED (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (hNS : PrincNS4 m) (H : Submodule ℂ M45) (hHK : H ≤ K)
    (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3) : Module.finrank ℂ K ≤ 4 :=
  PR_RED_core K m (QBc_of K m hdef hm hm0) hm hm0 H hHK hH hq
    (fun K' hK' h4 hHK' hY => hNS K' (fun Y hY' => hdef Y (hK' hY')) h4 H hHK' hH hq hY)

theorem PR3_step1_def (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (h0 : m 0 ≠ 0) (h1 : m 1 ≠ 0) (h2 : m 2 ≠ 0) (h3 : m 3 = 0)
    (h4 : m 4 = 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (Zs : M45) (hZs : Zs ∈ K) (hZs0 : rs Zs = 0)
    (hcs : colsumL 0 Zs = 0) (hne : Zs ≠ 0) :
    ∃ v : V4, v ≠ 0 ∧ tau v = 0 ∧ ip v v = 0 ∧ t3 v v v = 0 ∧
      ∃ s t : ℂ, s ≠ 0 ∧ t ≠ 0 ∧ col Zs 0 = v ∧ col Zs 1 = s • v ∧ col Zs 2 = t • v ∧
        col Zs 3 = 0 ∧ col Zs 4 = 0 := by
  obtain ⟨θ, hθ⟩ := hdef Zs hZs
  have hneut : P4 3 (fun p => 1 + Zs p) = 24 := by
    rw [hθ 3, h3, mul_zero, add_zero]
  exact PR3_step1 K m (QBc_of K m hdef hm (fun h => h0 (congrFun h 0))) hm h0 h1 h2 h3 h4 H hHK
    hH hq Zs hZs hZs0 hcs hne hneut

theorem PR3 (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (h0 : m 0 ≠ 0) (h1 : m 1 ≠ 0) (h2 : m 2 ≠ 0) (h3 : m 3 = 0)
    (h4 : m 4 = 0) (hmm : m 0 * m 0 + m 1 * m 1 + m 2 * m 2 ≠ 0)
    (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3) :
    Module.finrank ℂ K ≤ 4 :=
  PR3_core K m (QBc_of K m hdef hm (fun h => h0 (congrFun h 0))) hm h0 h1 h2 h3 h4 hmm H hHK hH hq
    (fun Y hY => by
      obtain ⟨θ, hθ⟩ := hdef Y hY
      rw [hθ 3, h3, mul_zero, add_zero])

def e2b (d z : V4) : ℂ := (tau d * tau z - ip d z) / 2

def Edb (d z : V4) : V4 := fun k => e2b d z - (tau d * z k + tau z * d k) / 2 + d k * z k

set_option maxHeartbeats 4000000 in
theorem pc_F_expand (d z a b : V4) (c t : ℂ) :
    pc (fun k => c * d k + t * z k) (fun k => c * d k + t * z k) (fun k => 1 + c * a k)
        (fun k => 1 + c * b k)
      - pc (fun k => c * d k) (fun k => c * d k) (fun k => 1 + c * a k) (fun k => 1 + c * b k)
    = 2 * t * c * (4 * e2b d z + 2 * c * ip (a + b) (Edb d z) + c ^ 2 * pc d z a b)
      + t ^ 2 * (4 * e2 z + 2 * c * ip (a + b) (Ed z) + c ^ 2 * pc z z a b) := by
  simp (config := {decide := true}) only [pc, e2, e2b, Ed, Edb, tau, ip, Pi.add_apply,
    Fin.sum_univ_four, ite_true, ite_false, add_zero, zero_add]
  ring

theorem LZ_pair_alg (d z a b : V4)
    (h : ∀ c t : ℂ, pc (fun k => c * d k + t * z k) (fun k => c * d k + t * z k)
        (fun k => 1 + c * a k) (fun k => 1 + c * b k)
      = pc (fun k => c * d k) (fun k => c * d k) (fun k => 1 + c * a k) (fun k => 1 + c * b k)) :
    e2 z = 0 ∧ ip (a + b) (Ed z) = 0 ∧ pc z z a b = 0 ∧ e2b d z = 0 ∧
      ip (a + b) (Edb d z) = 0 ∧ pc d z a b = 0 := by
  have F : ∀ c t : ℂ, 2 * t * c * (4 * e2b d z + 2 * c * ip (a + b) (Edb d z) + c ^ 2 * pc d z a b)
      + t ^ 2 * (4 * e2 z + 2 * c * ip (a + b) (Ed z) + c ^ 2 * pc z z a b) = 0 := by
    intro c t
    rw [← pc_F_expand d z a b c t]
    exact sub_eq_zero.mpr (h c t)
  have f01 := F 0 1
  have f11 := F 1 1
  have f1m := F 1 (-1)
  have fm1 := F (-1) 1
  have fmm := F (-1) (-1)
  have f21 := F 2 1
  have f2m := F 2 (-1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 4 : ℂ) * f01
  · linear_combination (1 / 8 : ℂ) * f11 + (1 / 8 : ℂ) * f1m - (1 / 8 : ℂ) * fm1
      - (1 / 8 : ℂ) * fmm
  · linear_combination (-1 : ℂ) * f01 + (1 / 4 : ℂ) * f11 + (1 / 4 : ℂ) * f1m
      + (1 / 4 : ℂ) * fm1 + (1 / 4 : ℂ) * fmm
  · linear_combination (-1 / 16 : ℂ) * f01 + (3 / 32 : ℂ) * f11 - (1 / 32 : ℂ) * f1m
      - (1 / 96 : ℂ) * fm1 + (1 / 32 : ℂ) * fmm - (1 / 48 : ℂ) * f21
  · linear_combination (1 / 16 : ℂ) * f11 - (1 / 16 : ℂ) * f1m + (1 / 16 : ℂ) * fm1
      - (1 / 16 : ℂ) * fmm
  · linear_combination (1 / 4 : ℂ) * f01 - (1 / 4 : ℂ) * f11 - (1 / 12 : ℂ) * fm1
      + (1 / 12 : ℂ) * f21

theorem LZ_shift (Y : M45) (z : V4) (c t : ℂ) :
    uY (c • Y + t • zE z) = (fun k => c * uY Y k) ∧
    dY (c • Y + t • zE z) = (fun k => c * dY Y k + t * z k) ∧
    (∀ j : Fin 5, j ≠ 0 → j ≠ 1 → ∀ k, (c • Y + t • zE z) (k, j) = c * Y (k, j)) := by
  refine ⟨?_, ?_, ?_⟩
  · funext k
    simp only [uY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zE0, zE1]
    ring
  · funext k
    simp only [dY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zE0, zE1]
    ring
  · intro j hj0 hj1 k
    have hz : zE z (k, j) = 0 := by
      simp [zE, hj0, hj1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz]
    ring

theorem LZ_pair (K : Submodule ℂ M45) (j l : Fin 5) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hl0 : l ≠ 0)
    (hl1 : l ≠ 1)
    (hcl : ∀ W ∈ K, pc (fun k => 1 + uY W k) (fun k => 1 + uY W k) (fun k => 1 + W (k, j))
        (fun k => 1 + W (k, l)) - pc (dY W) (dY W) (fun k => 1 + W (k, j))
        (fun k => 1 + W (k, l)) = 24)
    (z : V4) (hz : zE z ∈ K) (Y : M45) (hY : Y ∈ K) :
    e2 z = 0 ∧ ip (col Y j + col Y l) (Ed z) = 0 ∧ pc z z (col Y j) (col Y l) = 0 ∧
      e2b (dY Y) z = 0 ∧ ip (col Y j + col Y l) (Edb (dY Y) z) = 0 ∧
      pc (dY Y) z (col Y j) (col Y l) = 0 := by
  apply LZ_pair_alg (dY Y) z (col Y j) (col Y l)
  intro c t
  have h1 := hcl _ (K.add_mem (K.smul_mem c hY) (K.smul_mem t hz))
  have h2 := hcl _ (K.add_mem (K.smul_mem c hY) (K.smul_mem 0 hz))
  obtain ⟨u1, d1, c1⟩ := LZ_shift Y z c t
  obtain ⟨u2, d2, c2⟩ := LZ_shift Y z c 0
  simp only [zero_mul, add_zero] at d2
  have ej1 : (fun k => 1 + (c • Y + t • zE z) (k, j)) = fun k => 1 + c * col Y j k := by
    funext k
    show 1 + (c • Y + t • zE z) (k, j) = 1 + c * Y (k, j)
    rw [c1 j hj0 hj1 k]
  have el1 : (fun k => 1 + (c • Y + t • zE z) (k, l)) = fun k => 1 + c * col Y l k := by
    funext k
    show 1 + (c • Y + t • zE z) (k, l) = 1 + c * Y (k, l)
    rw [c1 l hl0 hl1 k]
  have ej2 : (fun k => 1 + (c • Y + (0 : ℂ) • zE z) (k, j)) = fun k => 1 + c * col Y j k := by
    funext k
    show 1 + (c • Y + (0 : ℂ) • zE z) (k, j) = 1 + c * Y (k, j)
    rw [c2 j hj0 hj1 k]
  have el2 : (fun k => 1 + (c • Y + (0 : ℂ) • zE z) (k, l)) = fun k => 1 + c * col Y l k := by
    funext k
    show 1 + (c • Y + (0 : ℂ) • zE z) (k, l) = 1 + c * Y (k, l)
    rw [c2 l hl0 hl1 k]
  rw [u1, d1, ej1, el1] at h1
  rw [u2, d2, ej2, el2] at h2
  linear_combination h2 - h1

theorem LemmaZ (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z : V4) (hz : zE z ∈ K)
    (Y : M45) (hY : Y ∈ K) :
    e2 z = 0 ∧ e2b (dY Y) z = 0 ∧
    ip (col Y 2) (Ed z) = 0 ∧ ip (col Y 3) (Ed z) = 0 ∧ ip (col Y 4) (Ed z) = 0 ∧
    pc z z (col Y 3) (col Y 4) = 0 ∧ pc z z (col Y 2) (col Y 4) = 0 ∧
    pc z z (col Y 2) (col Y 3) = 0 ∧
    ip (col Y 3 + col Y 4) (Edb (dY Y) z) = 0 ∧ ip (col Y 2 + col Y 4) (Edb (dY Y) z) = 0 ∧
    ip (col Y 2 + col Y 3) (Edb (dY Y) z) = 0 ∧
    pc (dY Y) z (col Y 3) (col Y 4) = 0 ∧ pc (dY Y) z (col Y 2) (col Y 4) = 0 ∧
    pc (dY Y) z (col Y 2) (col Y 3) = 0 := by
  have hN := (TC5_normal K).mp hdef
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := LZ_pair K 3 4 (by decide) (by decide) (by decide)
    (by decide) (fun W hW => (hN W hW).2.1) z hz Y hY
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := LZ_pair K 2 4 (by decide) (by decide) (by decide)
    (by decide) (fun W hW => (hN W hW).2.2.1) z hz Y hY
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := LZ_pair K 2 3 (by decide) (by decide) (by decide)
    (by decide) (fun W hW => (hN W hW).2.2.2) z hz Y hY
  have s2 : ip (col Y 2) (Ed z) = 0 := by
    simp only [ip, Pi.add_apply] at a2 b2 g2 ⊢
    linear_combination (1 / 2 : ℂ) * (b2 + g2 - a2)
  have s3 : ip (col Y 3) (Ed z) = 0 := by
    simp only [ip, Pi.add_apply] at a2 b2 g2 ⊢
    linear_combination (1 / 2 : ℂ) * (a2 + g2 - b2)
  have s4 : ip (col Y 4) (Ed z) = 0 := by
    simp only [ip, Pi.add_apply] at a2 b2 g2 ⊢
    linear_combination (1 / 2 : ℂ) * (a2 + b2 - g2)
  exact ⟨a1, a4, s2, s3, s4, a3, b3, g3, a5, b5, g5, a6, b6, g6⟩

theorem zE_add (z z' : V4) : zE (z + z') = zE z + zE z' := by
  funext p
  obtain ⟨k, j⟩ := p
  simp only [zE, Pi.add_apply]
  split_ifs <;> ring

theorem Ed_pol (z z' : V4) : Ed (z + z') = fun k => Ed z k + Ed z' k + 2 * Edb z z' k := by
  funext k
  simp only [Ed, Edb, e2, e2b, tau, ip, Pi.add_apply]
  ring

set_option maxHeartbeats 2000000 in
theorem pc_pol (z z' a b : V4) :
    pc (z + z') (z + z') a b = pc z z a b + pc z' z' a b + 2 * pc z z' a b := by
  simp (config := {decide := true}) only [pc, Pi.add_apply, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  ring

theorem LemmaZ_pol (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z z' : V4) (hz : zE z ∈ K)
    (hz' : zE z' ∈ K) (Y : M45) (hY : Y ∈ K) :
    ip (col Y 2) (Edb z z') = 0 ∧ ip (col Y 3) (Edb z z') = 0 ∧ ip (col Y 4) (Edb z z') = 0 ∧
    pc z z' (col Y 3) (col Y 4) = 0 ∧ pc z z' (col Y 2) (col Y 4) = 0 ∧
    pc z z' (col Y 2) (col Y 3) = 0 := by
  have hzz : zE (z + z') ∈ K := by
    rw [zE_add]
    exact K.add_mem hz hz'
  obtain ⟨-, -, a2, a3, a4, a34, a24, a23, -⟩ := LemmaZ K hdef z hz Y hY
  obtain ⟨-, -, b2, b3, b4, b34, b24, b23, -⟩ := LemmaZ K hdef z' hz' Y hY
  obtain ⟨-, -, c2, c3, c4, c34, c24, c23, -⟩ := LemmaZ K hdef (z + z') hzz Y hY
  rw [Ed_pol] at c2 c3 c4
  rw [pc_pol] at c34 c24 c23
  simp only [ip] at a2 a3 a4 b2 b3 b4 c2 c3 c4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ip]
    linear_combination (1 / 2 : ℂ) * (c2 - a2 - b2)
  · simp only [ip]
    linear_combination (1 / 2 : ℂ) * (c3 - a3 - b3)
  · simp only [ip]
    linear_combination (1 / 2 : ℂ) * (c4 - a4 - b4)
  · linear_combination (1 / 2 : ℂ) * (c34 - a34 - b34)
  · linear_combination (1 / 2 : ℂ) * (c24 - a24 - b24)
  · linear_combination (1 / 2 : ℂ) * (c23 - a23 - b23)

def cE (Y : M45) (n : Fin 5) : M45 := fun p => if p.2 = n then Y (p.1, n) else 0

theorem cE_sum (Y : M45) (m : Fin 5 → ℂ) (i : Fin 4) : ∀ j : Fin 5,
    (m 0 • cE Y 0 + m 1 • cE Y 1 + m 2 • cE Y 2 + m 3 • cE Y 3 + m 4 • cE Y 4) (i, j)
      = m j * Y (i, j) := by
  apply fin5 <;> simp (config := {decide := true}) only [cE, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ite_true, ite_false] <;> ring

theorem P51_rank1 (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3) (hcc : ∀ Y ∈ H, ∀ n : Fin 5, cE Y n ∈ H)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    ∃ κ : ℂ, ∃ Yf ∈ H, ip (rs Yf) (rs Yf) = 3 * κ ^ 2 / 4 ∧
      ∀ i j, Z (i, j) = m j * (κ / 4 - rs Yf i) := by
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨κ, hc, Yf, hYf, hnf, hff⟩ := PS_b_core K m hQB hm hm0 H hHK hH hq Z hZ hZ0
  have hrow : ∀ i, m 0 * Yf (i, 0) + m 1 * Yf (i, 1) + m 2 * Yf (i, 2) + m 3 * Yf (i, 3)
      + m 4 * Yf (i, 4) = 0 := by
    intro i
    have h := congrFun hZ0 i
    rw [rs_apply, hnf 0 i, hnf 1 i, hnf 2 i, hnf 3 i, hnf 4 i] at h
    simp only [phi_apply, Pi.zero_apply] at h
    linear_combination (1 / 2 : ℂ) * h - (κ / 8) * hm' + (1 / 2 : ℂ) * rs Yf i * hm'
  have hWH : (m 0 • cE Yf 0 + m 1 • cE Yf 1 + m 2 • cE Yf 2 + m 3 • cE Yf 3
      + m 4 • cE Yf 4) ∈ H :=
    H.add_mem (H.add_mem (H.add_mem (H.add_mem (H.smul_mem _ (hcc Yf hYf 0))
      (H.smul_mem _ (hcc Yf hYf 1))) (H.smul_mem _ (hcc Yf hYf 2)))
      (H.smul_mem _ (hcc Yf hYf 3))) (H.smul_mem _ (hcc Yf hYf 4))
  have hWrs : rs (m 0 • cE Yf 0 + m 1 • cE Yf 1 + m 2 • cE Yf 2 + m 3 • cE Yf 3
      + m 4 • cE Yf 4) = 0 := by
    funext i
    rw [rs_apply, cE_sum Yf m i 0, cE_sum Yf m i 1, cE_sum Yf m i 2, cE_sum Yf m i 3,
      cE_sum Yf m i 4]
    simp only [Pi.zero_apply]
    linear_combination hrow i
  have hW0 : (m 0 • cE Yf 0 + m 1 • cE Yf 1 + m 2 • cE Yf 2 + m 3 • cE Yf 3
      + m 4 • cE Yf 4) = 0 := by
    have hmem : (m 0 • cE Yf 0 + m 1 • cE Yf 1 + m 2 • cE Yf 2 + m 3 • cE Yf 3
        + m 4 • cE Yf 4) ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
      Submodule.mem_inf.mpr ⟨hWH, LinearMap.mem_ker.mpr hWrs⟩
    rw [Bi H hH hq] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hmy : ∀ i j, m j * Yf (i, j) = 0 := by
    intro i j
    have h := cE_sum Yf m i j
    rw [hW0, Pi.zero_apply] at h
    exact h.symm
  refine ⟨κ, Yf, hYf, hff, fun i j => ?_⟩
  rw [hnf j i, phi_apply]
  linear_combination 2 * hmy i j

def E2v (a : V4) : V4 := fun i => e2 a - a i * (tau a - a i)

def e3v (a : V4) : ℂ := (tau a ^ 3 - 3 * tau a * ip a a + 2 * t3 a a a) / 6

def E3v (a : V4) : V4 := fun i => e3v a - a i * E2v a i

set_option maxHeartbeats 2000000 in
theorem pc_add4 (z1 z2 z3 u x : V4) :
    pc z1 z2 z3 (u + x) = pc z1 z2 z3 u + pc z1 z2 z3 x := by
  simp (config := {decide := true}) only [pc, Pi.add_apply, Fin.sum_univ_four, ite_true,
    ite_false, add_zero, zero_add]
  ring

set_option maxHeartbeats 2000000 in
theorem pc_x4 (a x : V4) (α β γ : ℂ) :
    pc (fun i => 1 + α * a i) (fun i => 1 + β * a i) (fun i => 1 + γ * a i) x =
      6 * tau x + (α + β + γ) * (2 * (tau x * tau a - ip x a))
      + (α * β + α * γ + β * γ) * (2 * ip x (E2v a)) + α * β * γ * (6 * ip x (E3v a)) := by
  simp (config := {decide := true}) only [pc, E2v, E3v, e2, e3v, tau, ip, t3,
    Fin.sum_univ_four, ite_true, ite_false, add_zero, zero_add]
  ring

theorem cubic4 (y0 y1 y2 y3 c0 c1 c2 c3 : ℂ) (h01 : y0 ≠ y1) (h02 : y0 ≠ y2) (h03 : y0 ≠ y3)
    (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3)
    (q0 : c0 + c1 * y0 + c2 * y0 ^ 2 + c3 * y0 ^ 3 = 0)
    (q1 : c0 + c1 * y1 + c2 * y1 ^ 2 + c3 * y1 ^ 3 = 0)
    (q2 : c0 + c1 * y2 + c2 * y2 ^ 2 + c3 * y2 ^ 3 = 0)
    (q3 : c0 + c1 * y3 + c2 * y3 ^ 2 + c3 * y3 ^ 3 = 0) : c3 = 0 ∧ c2 = 0 := by
  have d01 : y1 - y0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
  have d02 : y2 - y0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h02)
  have d03 : y3 - y0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h03)
  have d12 : y2 - y1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have d13 : y3 - y1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  have d23 : y3 - y2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
  have k3 : c3 * ((y1 - y0) * (y2 - y0) * (y3 - y0) * (y2 - y1) * (y3 - y1) * (y3 - y2)) = 0 := by
    linear_combination ((y1 - y2) * (y1 - y3) * (y2 - y3)) * q0
      - ((y0 - y2) * (y0 - y3) * (y2 - y3)) * q1
      + ((y0 - y1) * (y0 - y3) * (y1 - y3)) * q2
      - ((y0 - y1) * (y0 - y2) * (y1 - y2)) * q3
  have c3z : c3 = 0 := by
    rcases mul_eq_zero.mp k3 with h | h
    · exact h
    · exfalso
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero d01 d02) d03) d12)
        d13) d23) h
  have k2 : c2 * ((y1 - y0) * (y2 - y0) * (y2 - y1)) = 0 := by
    linear_combination (-y1 + y2) * q0 + (y0 - y2) * q1 + (-y0 + y1) * q2
      - ((-y1 + y2) * y0 ^ 3 + (y0 - y2) * y1 ^ 3 + (-y0 + y1) * y2 ^ 3) * c3z
  refine ⟨c3z, ?_⟩
  rcases mul_eq_zero.mp k2 with h | h
  · exact h
  · exfalso
    exact (mul_ne_zero (mul_ne_zero d01 d02) d12) h

theorem P51_deriv4 (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hinj : Function.Injective m) (a x : V4) (Z E : M45)
    (hZdef : ∀ i j, Z (i, j) = m j * a i) (hEdef : ∀ i j, E (i, j) = if j = 4 then x i else 0)
    (hZ : Z ∈ K) (hE : E ∈ K) : ip x (E2v a) = 0 ∧ ip x (E3v a) = 0 := by
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨θ1, h1⟩ := hdef (Z + E) (K.add_mem hZ hE)
  obtain ⟨θ0, h0⟩ := hdef Z hZ
  have cA : ∀ k : Fin 5, k ≠ 4 →
      col (fun p : Fin 4 × Fin 5 => 1 + (Z + E) p) k = fun i => 1 + m k * a i := by
    intro k hk
    funext i
    show 1 + (Z (i, k) + E (i, k)) = 1 + m k * a i
    rw [hZdef, hEdef, if_neg hk]
    ring
  have cA4 : col (fun p : Fin 4 × Fin 5 => 1 + (Z + E) p) 4 = (fun i => 1 + m 4 * a i) + x := by
    funext i
    show 1 + (Z (i, 4) + E (i, 4)) = 1 + m 4 * a i + x i
    rw [hZdef, hEdef, if_pos rfl]
    ring
  have cB : ∀ k : Fin 5, col (fun p : Fin 4 × Fin 5 => 1 + Z p) k = fun i => 1 + m k * a i := by
    intro k
    funext i
    show 1 + Z (i, k) = 1 + m k * a i
    rw [hZdef]
  have q0 : 6 * tau x + (m 1 + m 2 + m 3) * (2 * (tau x * tau a - ip x a))
      + (m 1 * m 2 + m 1 * m 3 + m 2 * m 3) * (2 * ip x (E2v a))
      + m 1 * m 2 * m 3 * (6 * ip x (E3v a)) = (θ1 - θ0) * m 0 := by
    have e1 := h1 0
    have e0 := h0 0
    rw [P4_c0, cA 1 (by decide), cA 2 (by decide), cA 3 (by decide), cA4, pc_add4,
      pc_x4 a x (m 1) (m 2) (m 3)] at e1
    rw [P4_c0, cB 1, cB 2, cB 3, cB 4] at e0
    linear_combination e1 - e0
  have q1 : 6 * tau x + (m 0 + m 2 + m 3) * (2 * (tau x * tau a - ip x a))
      + (m 0 * m 2 + m 0 * m 3 + m 2 * m 3) * (2 * ip x (E2v a))
      + m 0 * m 2 * m 3 * (6 * ip x (E3v a)) = (θ1 - θ0) * m 1 := by
    have e1 := h1 1
    have e0 := h0 1
    rw [P4_c1, cA 0 (by decide), cA 2 (by decide), cA 3 (by decide), cA4, pc_add4,
      pc_x4 a x (m 0) (m 2) (m 3)] at e1
    rw [P4_c1, cB 0, cB 2, cB 3, cB 4] at e0
    linear_combination e1 - e0
  have q2 : 6 * tau x + (m 0 + m 1 + m 3) * (2 * (tau x * tau a - ip x a))
      + (m 0 * m 1 + m 0 * m 3 + m 1 * m 3) * (2 * ip x (E2v a))
      + m 0 * m 1 * m 3 * (6 * ip x (E3v a)) = (θ1 - θ0) * m 2 := by
    have e1 := h1 2
    have e0 := h0 2
    rw [P4_c2, cA 0 (by decide), cA 1 (by decide), cA 3 (by decide), cA4, pc_add4,
      pc_x4 a x (m 0) (m 1) (m 3)] at e1
    rw [P4_c2, cB 0, cB 1, cB 3, cB 4] at e0
    linear_combination e1 - e0
  have q3 : 6 * tau x + (m 0 + m 1 + m 2) * (2 * (tau x * tau a - ip x a))
      + (m 0 * m 1 + m 0 * m 2 + m 1 * m 2) * (2 * ip x (E2v a))
      + m 0 * m 1 * m 2 * (6 * ip x (E3v a)) = (θ1 - θ0) * m 3 := by
    have e1 := h1 3
    have e0 := h0 3
    rw [P4_c3, cA 0 (by decide), cA 1 (by decide), cA 2 (by decide), cA4, pc_add4,
      pc_x4 a x (m 0) (m 1) (m 2)] at e1
    rw [P4_c3, cB 0, cB 1, cB 2, cB 4] at e0
    linear_combination e1 - e0
  obtain ⟨c3z, c2z⟩ := cubic4 (m 0) (m 1) (m 2) (m 3)
    (-(m 4) * (2 * (tau x * tau a - ip x a))
      + (m 0 * m 1 + m 0 * m 2 + m 0 * m 3 + m 1 * m 2 + m 1 * m 3 + m 2 * m 3) * (2 * ip x (E2v a))
      + (m 0 * m 1 * m 2 + m 0 * m 1 * m 3 + m 0 * m 2 * m 3 + m 1 * m 2 * m 3) * (6 * ip x (E3v a))
      + 6 * tau x)
    (-(2 * (tau x * tau a - ip x a)) + m 4 * (2 * ip x (E2v a))
      - (m 0 * m 1 + m 0 * m 2 + m 0 * m 3 + m 1 * m 2 + m 1 * m 3 + m 2 * m 3) * (6 * ip x (E3v a))
      - (θ1 - θ0))
    (2 * ip x (E2v a) - m 4 * (6 * ip x (E3v a)))
    (-(6 * ip x (E3v a)))
    (fun h => absurd (hinj h) (by decide)) (fun h => absurd (hinj h) (by decide))
    (fun h => absurd (hinj h) (by decide)) (fun h => absurd (hinj h) (by decide))
    (fun h => absurd (hinj h) (by decide)) (fun h => absurd (hinj h) (by decide))
    (by linear_combination q0 + (-(m 0) ^ 2 * (6 * ip x (E3v a)) + m 0 * (2 * ip x (E2v a))
      - 2 * (tau x * tau a - ip x a)) * hm')
    (by linear_combination q1 + (-(m 1) ^ 2 * (6 * ip x (E3v a)) + m 1 * (2 * ip x (E2v a))
      - 2 * (tau x * tau a - ip x a)) * hm')
    (by linear_combination q2 + (-(m 2) ^ 2 * (6 * ip x (E3v a)) + m 2 * (2 * ip x (E2v a))
      - 2 * (tau x * tau a - ip x a)) * hm')
    (by linear_combination q3 + (-(m 3) ^ 2 * (6 * ip x (E3v a)) + m 3 * (2 * ip x (E2v a))
      - 2 * (tau x * tau a - ip x a)) * hm')
  have h3 : ip x (E3v a) = 0 := by linear_combination (-1 / 6 : ℂ) * c3z
  refine ⟨?_, h3⟩
  linear_combination (1 / 2 : ℂ) * c2z + (3 * m 4) * h3

theorem pair_sq (a b c d : ℂ) (h0 : b * c + b * d + c * d = 0) (h1 : a * c + a * d + c * d = 0)
    (h2 : a * b + a * d + b * d = 0) (h3 : a * b + a * c + b * c = 0) : a * b = 0 := by
  have h : (a * b) ^ 2 = 0 := by
    linear_combination (-a ^ 2 / 3 - a * b / 3) * h0 + (-a * b / 3 - b ^ 2 / 3) * h1
      + (2 * a * b / 3 + a * c / 3 + b * c / 3) * h2 + (a * b / 3) * h3
  exact (pow_eq_zero_iff (by norm_num)).mp h

theorem P51_unit (a : V4) (h2 : ∀ i, E2v a i = E2v a 0) (h3 : ∀ i, E3v a i = E3v a 0) :
    (a 1 = a 0 ∧ a 2 = a 0 ∧ a 3 = a 0) ∨
    (a 0 * a 1 = 0 ∧ a 0 * a 2 = 0 ∧ a 0 * a 3 = 0 ∧ a 1 * a 2 = 0 ∧ a 1 * a 3 = 0
      ∧ a 2 * a 3 = 0) := by
  by_cases hE : E2v a 0 = 0
  · right
    have g0 := hE
    have g1 := (h2 1).trans hE
    have g2 := (h2 2).trans hE
    have g3 := (h2 3).trans hE
    simp only [E2v, e2, tau, ip] at g0 g1 g2 g3
    have f0 : a 1 * a 2 + a 1 * a 3 + a 2 * a 3 = 0 := by linear_combination g0
    have f1 : a 0 * a 2 + a 0 * a 3 + a 2 * a 3 = 0 := by linear_combination g1
    have f2 : a 0 * a 1 + a 0 * a 3 + a 1 * a 3 = 0 := by linear_combination g2
    have f3 : a 0 * a 1 + a 0 * a 2 + a 1 * a 2 = 0 := by linear_combination g3
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact pair_sq (a 0) (a 1) (a 2) (a 3) f0 f1 f2 f3
    · exact pair_sq (a 0) (a 2) (a 1) (a 3) (by linear_combination f0) (by linear_combination f2)
        (by linear_combination f1) (by linear_combination f3)
    · exact pair_sq (a 0) (a 3) (a 1) (a 2) (by linear_combination f0) (by linear_combination f3)
        (by linear_combination f1) (by linear_combination f2)
    · exact pair_sq (a 1) (a 2) (a 0) (a 3) (by linear_combination f1) (by linear_combination f2)
        (by linear_combination f0) (by linear_combination f3)
    · exact pair_sq (a 1) (a 3) (a 0) (a 2) (by linear_combination f1) (by linear_combination f3)
        (by linear_combination f0) (by linear_combination f2)
    · exact pair_sq (a 2) (a 3) (a 0) (a 1) (by linear_combination f2) (by linear_combination f3)
        (by linear_combination f0) (by linear_combination f1)
  · left
    have k : ∀ i, (a i - a 0) * E2v a 0 = 0 := by
      intro i
      have e := h3 i
      have e2' := h2 i
      simp only [E3v] at e
      rw [e2'] at e
      linear_combination -e
    refine ⟨?_, ?_, ?_⟩
    · exact sub_eq_zero.mp ((mul_eq_zero.mp (k 1)).resolve_right hE)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp (k 2)).resolve_right hE)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp (k 3)).resolve_right hE)

theorem P51_deriv (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hinj : Function.Injective m) (a x : V4) (n : Fin 5) (Z E : M45)
    (hZdef : ∀ i j, Z (i, j) = m j * a i) (hEdef : ∀ i j, E (i, j) = if j = n then x i else 0)
    (hZ : Z ∈ K) (hE : E ∈ K) : ip x (E2v a) = 0 ∧ ip x (E3v a) = 0 := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 5), σ = Equiv.swap n 4 := ⟨_, rfl⟩
  have hm' : ∑ a, (fun a => m (σ a)) a = 0 := by
    show ∑ a, m (σ a) = 0
    rw [Equiv.sum_comp σ m]
    exact hm
  have hinj' : Function.Injective (fun a => m (σ a)) := hinj.comp σ.injective
  have hiff : ∀ j, σ j = n ↔ j = 4 := by
    intro j
    rw [hσ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  apply P51_deriv4 (K.map (cperm σ)) (fun a => m (σ a)) (DefLine_perm σ K m hdef) hm' hinj' a x
    (cperm σ Z) (cperm σ E)
  · intro i j
    show Z (i, σ j) = m (σ j) * a i
    exact hZdef i (σ j)
  · intro i j
    show E (i, σ j) = if j = 4 then x i else 0
    rw [hEdef]
    by_cases h : j = 4
    · rw [if_pos ((hiff j).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hiff j).mp h')), if_neg h]
  · exact ⟨Z, hZ, rfl⟩
  · exact ⟨E, hE, rfl⟩

theorem pw_dim (W : Submodule ℂ V4) (hW : ∀ w ∈ W, ∀ i k : Fin 4, i ≠ k → w i * w k = 0) :
    Module.finrank ℂ W ≤ 1 := by
  by_cases hbot : W = ⊥
  · rw [hbot, finrank_bot]
    norm_num
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
  have hi' : w i ≠ 0 := hi
  have hle : W ≤ Submodule.span ℂ {w} := by
    intro w' hw'
    rw [Submodule.mem_span_singleton]
    refine ⟨w' i / w i, ?_⟩
    funext k
    by_cases hk : k = i
    · rw [hk]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ (w' i) hi']
    · have h1 : w i * w k = 0 := hW w hw i k (Ne.symm hk)
      have hwk : w k = 0 := (mul_eq_zero.mp h1).resolve_left hi'
      have h2 : (w + w') i * (w + w') k = 0 := hW _ (W.add_mem hw hw') i k (Ne.symm hk)
      have h3 : w' i * w' k = 0 := hW w' hw' i k (Ne.symm hk)
      simp only [Pi.add_apply, hwk, zero_add] at h2
      have h4 : w i * w' k = 0 := by linear_combination h2 - h3
      have hw'k : w' k = 0 := (mul_eq_zero.mp h4).resolve_left hi'
      simp only [Pi.smul_apply, smul_eq_mul, hwk, hw'k, mul_zero]
  calc Module.finrank ℂ W ≤ Module.finrank ℂ (Submodule.span ℂ {w}) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hw0

theorem P51_key (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (hinj : Function.Injective m) (H : Submodule ℂ M45)
    (hHK : H ≤ K) (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (hcc : ∀ Y ∈ H, ∀ n : Fin 5, cE Y n ∈ H) (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    ∃ a : V4, (∀ i j, Z (i, j) = m j * a i) ∧ ∀ i k : Fin 4, i ≠ k → a i * a k = 0 := by
  have hQB := QBc_of K m hdef hm hm0
  obtain ⟨κ, Yf, hYf, hff, hZf⟩ := P51_rank1 K m hQB hm hm0 H hHK hH hq hcc Z hZ hZ0
  have hSV := (phi_onto H hH hq 0).1
  have hd : ∀ Y ∈ H, ∀ n : Fin 5, ip (col Y n) (E2v (fun i => κ / 4 - rs Yf i)) = 0 ∧
      ip (col Y n) (E3v (fun i => κ / 4 - rs Yf i)) = 0 := by
    intro Y hY n
    exact P51_deriv K m hdef hm hinj (fun i => κ / 4 - rs Yf i) (col Y n) n Z (cE Y n)
      (fun i j => hZf i j) (fun i j => rfl) hZ (hHK (hcc Y hY n))
  have perpV : ∀ v : V4, tau v = 0 → ip v (E2v (fun i => κ / 4 - rs Yf i)) = 0 ∧
      ip v (E3v (fun i => κ / 4 - rs Yf i)) = 0 := by
    intro v hv
    have hmem : v ∈ H.map rs := by
      rw [hSV, mem_Vs]
      exact hv
    obtain ⟨Y, hY, rfl⟩ := hmem
    obtain ⟨d0, e0⟩ := hd Y hY 0
    obtain ⟨d1, e1⟩ := hd Y hY 1
    obtain ⟨d2, e2'⟩ := hd Y hY 2
    obtain ⟨d3, e3⟩ := hd Y hY 3
    obtain ⟨d4, e4⟩ := hd Y hY 4
    simp only [ip, rs_col] at d0 d1 d2 d3 d4 e0 e1 e2' e3 e4 ⊢
    constructor
    · linear_combination d0 + d1 + d2 + d3 + d4
    · linear_combination e0 + e1 + e2' + e3 + e4
  have v1 := perpV ![-1, 1, 0, 0] (by norm_num [tau])
  have v2 := perpV ![-1, 0, 1, 0] (by norm_num [tau])
  have v3 := perpV ![-1, 0, 0, 1] (by norm_num [tau])
  have a1 : (-1) * E2v (fun i => κ / 4 - rs Yf i) 0 + 1 * E2v (fun i => κ / 4 - rs Yf i) 1
      + 0 * E2v (fun i => κ / 4 - rs Yf i) 2 + 0 * E2v (fun i => κ / 4 - rs Yf i) 3 = 0 := v1.1
  have a2 : (-1) * E2v (fun i => κ / 4 - rs Yf i) 0 + 0 * E2v (fun i => κ / 4 - rs Yf i) 1
      + 1 * E2v (fun i => κ / 4 - rs Yf i) 2 + 0 * E2v (fun i => κ / 4 - rs Yf i) 3 = 0 := v2.1
  have a3 : (-1) * E2v (fun i => κ / 4 - rs Yf i) 0 + 0 * E2v (fun i => κ / 4 - rs Yf i) 1
      + 0 * E2v (fun i => κ / 4 - rs Yf i) 2 + 1 * E2v (fun i => κ / 4 - rs Yf i) 3 = 0 := v3.1
  have b1 : (-1) * E3v (fun i => κ / 4 - rs Yf i) 0 + 1 * E3v (fun i => κ / 4 - rs Yf i) 1
      + 0 * E3v (fun i => κ / 4 - rs Yf i) 2 + 0 * E3v (fun i => κ / 4 - rs Yf i) 3 = 0 := v1.2
  have b2 : (-1) * E3v (fun i => κ / 4 - rs Yf i) 0 + 0 * E3v (fun i => κ / 4 - rs Yf i) 1
      + 1 * E3v (fun i => κ / 4 - rs Yf i) 2 + 0 * E3v (fun i => κ / 4 - rs Yf i) 3 = 0 := v2.2
  have b3 : (-1) * E3v (fun i => κ / 4 - rs Yf i) 0 + 0 * E3v (fun i => κ / 4 - rs Yf i) 1
      + 0 * E3v (fun i => κ / 4 - rs Yf i) 2 + 1 * E3v (fun i => κ / 4 - rs Yf i) 3 = 0 := v3.2
  have h2 : ∀ i, E2v (fun i => κ / 4 - rs Yf i) i = E2v (fun i => κ / 4 - rs Yf i) 0 := by
    intro i
    fin_cases i
    · rfl
    · show E2v (fun i => κ / 4 - rs Yf i) 1 = E2v (fun i => κ / 4 - rs Yf i) 0
      linear_combination a1
    · show E2v (fun i => κ / 4 - rs Yf i) 2 = E2v (fun i => κ / 4 - rs Yf i) 0
      linear_combination a2
    · show E2v (fun i => κ / 4 - rs Yf i) 3 = E2v (fun i => κ / 4 - rs Yf i) 0
      linear_combination a3
  have h3 : ∀ i, E3v (fun i => κ / 4 - rs Yf i) i = E3v (fun i => κ / 4 - rs Yf i) 0 := by
    intro i
    fin_cases i
    · rfl
    · show E3v (fun i => κ / 4 - rs Yf i) 1 = E3v (fun i => κ / 4 - rs Yf i) 0
      linear_combination b1
    · show E3v (fun i => κ / 4 - rs Yf i) 2 = E3v (fun i => κ / 4 - rs Yf i) 0
      linear_combination b2
    · show E3v (fun i => κ / 4 - rs Yf i) 3 = E3v (fun i => κ / 4 - rs Yf i) 0
      linear_combination b3
  have hprod : ∀ i k : Fin 4, i ≠ k →
      (κ / 4 - rs Yf i) * (κ / 4 - rs Yf k) = 0 := by
    rcases P51_unit (fun i => κ / 4 - rs Yf i) h2 h3 with hc | hp
    · obtain ⟨c1, c2, c3⟩ := hc
      have ht := tau_rs H hH Yf hYf
      simp only [tau] at ht
      have c1' : κ / 4 - rs Yf 1 = κ / 4 - rs Yf 0 := c1
      have c2' : κ / 4 - rs Yf 2 = κ / 4 - rs Yf 0 := c2
      have c3' : κ / 4 - rs Yf 3 = κ / 4 - rs Yf 0 := c3
      have f1 : rs Yf 1 = rs Yf 0 := by linear_combination -c1'
      have f2 : rs Yf 2 = rs Yf 0 := by linear_combination -c2'
      have f3 : rs Yf 3 = rs Yf 0 := by linear_combination -c3'
      have f0 : rs Yf 0 = 0 := by linear_combination (1 / 4 : ℂ) * ht - (1 / 4 : ℂ) * (f1 + f2 + f3)
      have hz : rs Yf = 0 := by
        funext i
        fin_cases i
        · exact f0
        · exact f1.trans f0
        · exact f2.trans f0
        · exact f3.trans f0
      rw [hz] at hff
      have hk : κ * κ = 0 := by
        simp only [ip, Pi.zero_apply] at hff
        linear_combination (-4 / 3 : ℂ) * hff
      have hk0 : κ = 0 := mul_self_eq_zero.mp hk
      intro i k _
      rw [hz, hk0]
      simp
    · obtain ⟨p01, p02, p03, p12, p13, p23⟩ := hp
      intro i k hik
      fin_cases i <;> fin_cases k
      · exact absurd rfl hik
      · exact p01
      · exact p02
      · exact p03
      · exact (mul_comm _ _).trans p01
      · exact absurd rfl hik
      · exact p12
      · exact p13
      · exact (mul_comm _ _).trans p02
      · exact (mul_comm _ _).trans p12
      · exact absurd rfl hik
      · exact p23
      · exact (mul_comm _ _).trans p03
      · exact (mul_comm _ _).trans p13
      · exact (mul_comm _ _).trans p23
      · exact absurd rfl hik
  exact ⟨fun i => κ / 4 - rs Yf i, hZf, hprod⟩

theorem P51_i (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hinj : Function.Injective m) (H : Submodule ℂ M45) (hHK : H ≤ K)
    (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (hcc : ∀ Y ∈ H, ∀ n : Fin 5, cE Y n ∈ H) : Module.finrank ℂ K ≤ 4 := by
  have hm0 : m ≠ 0 := by
    intro h
    have h01 : m 0 = m 1 := by simp [h]
    exact absurd (hinj h01) (by decide)
  obtain ⟨j0, hj0'⟩ := Function.ne_iff.mp hm0
  have hj0 : m j0 ≠ 0 := hj0'
  have hQB := QBc_of K m hdef hm hm0
  have hS := QB_map_rs K m hQB hm
  have rK := rank_nullity K rs
  have rN := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) ((m j0)⁻¹ • colL j0)
  have hb : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker ((m j0)⁻¹ • colL j0) : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    rintro Z ⟨⟨hZ, hZ0⟩, hZc⟩
    rw [Submodule.mem_bot]
    obtain ⟨a, ha, -⟩ := P51_key K m hdef hm hm0 hinj H hHK hH hq hcc Z hZ
      (LinearMap.mem_ker.mp hZ0)
    have hc := LinearMap.mem_ker.mp hZc
    have hai : ∀ i, a i = 0 := by
      intro i
      have h := congrFun hc i
      simp only [LinearMap.smul_apply, colL_apply, Pi.smul_apply, smul_eq_mul, col,
        Pi.zero_apply] at h
      rw [ha i j0] at h
      have h' : (m j0)⁻¹ * m j0 * a i = 0 := by linear_combination h
      rw [inv_mul_cancel₀ hj0, one_mul] at h'
      exact h'
    funext ⟨i, j⟩
    simp [ha i j, hai i]
  have hW : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map
      ((m j0)⁻¹ • colL j0)) ≤ 1 := by
    apply pw_dim
    rintro _ ⟨Z, ⟨hZ, hZ0⟩, rfl⟩ i k hik
    obtain ⟨a, ha, hp⟩ := P51_key K m hdef hm hm0 hinj H hHK hH hq hcc Z hZ
      (LinearMap.mem_ker.mp hZ0)
    have e : ∀ l, ((m j0)⁻¹ • colL j0) Z l = a l := by
      intro l
      simp only [LinearMap.smul_apply, colL_apply, Pi.smul_apply, smul_eq_mul, col]
      rw [ha l j0, ← mul_assoc, inv_mul_cancel₀ hj0, one_mul]
    rw [e i, e k]
    exact hp i k hik
  rw [hb, finrank_bot] at rN
  omega

theorem two_rel (m : Fin 5 → ℂ) (hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0) (Z Yf : M45) (κ : ℂ)
    (hZ0 : rs Z = 0) (hnf : ∀ j, ∀ i, Z (i, j) = κ * m j / 4 + m j * phi j Yf i)
    (hs : ∀ i, Yf (i, 2) = 0 ∧ Yf (i, 3) = 0 ∧ Yf (i, 4) = 0) (i : Fin 4) :
    (m 0 - m 1) * phi 0 Yf i + (m 0 + m 1) * rs Yf i = 0 := by
  have hg1 : phi 1 Yf i = -phi 0 Yf i := by
    simp only [phi_apply, rs_apply, (hs i).1, (hs i).2.1, (hs i).2.2]
    ring
  have hg2 : phi 2 Yf i = -rs Yf i := by
    rw [phi_apply, (hs i).1]
    ring
  have hg3 : phi 3 Yf i = -rs Yf i := by
    rw [phi_apply, (hs i).2.1]
    ring
  have hg4 : phi 4 Yf i = -rs Yf i := by
    rw [phi_apply, (hs i).2.2]
    ring
  have hrow := congrFun hZ0 i
  rw [rs_apply, hnf 0 i, hnf 1 i, hnf 2 i, hnf 3 i, hnf 4 i] at hrow
  simp only [Pi.zero_apply] at hrow
  linear_combination hrow - (κ / 4) * hm' - m 1 * hg1 - m 2 * hg2 - m 3 * hg3 - m 4 * hg4
    + rs Yf i * hm'

theorem span2_perp (u f g : V4) (hu : tau u = 0) (hf : tau f = 0) (hg : tau g = 0) (hg0 : g ≠ 0)
    (hff : ip f f ≠ 0) (hfg : ip f g = 0) (hgg : ip g g = 0) (huf : ip u f = 0)
    (hug : ip u g = 0) : ∃ c : ℂ, u = c • g := by
  have hW1 : Module.finrank ℂ (Submodule.span ℂ {g}) = 1 := finrank_span_singleton hg0
  have hlt : Submodule.span ℂ {g} < Submodule.span ℂ {f, g} := by
    refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
    intro h
    have hf' : f ∈ Submodule.span ℂ {g} := by
      rw [h]
      exact Submodule.subset_span (by simp)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf'
    apply hff
    rw [← hc]
    simp only [ip, Pi.smul_apply, smul_eq_mul] at hgg ⊢
    linear_combination c ^ 2 * hgg
  have hW2 : 2 ≤ Module.finrank ℂ (Submodule.span ℂ {f, g}) := by
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hperp := perp_sup_one (Submodule.span ℂ {u, g}) (Submodule.span ℂ {f, g})
    (by
      intro p hp
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hp
      simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hu hg ⊢
      linear_combination s * hu + t * hg)
    (by
      intro p hp
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hp
      simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hf hg ⊢
      linear_combination s * hf + t * hg)
    (by
      intro p hp w hw
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hp
      obtain ⟨s', t', rfl⟩ := Submodule.mem_span_pair.mp hw
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at huf hug hfg hgg ⊢
      linear_combination s * s' * huf + s * t' * hug + t * s' * hfg + t * t' * hgg)
  have hP1 : Module.finrank ℂ (Submodule.span ℂ {u, g}) ≤ 1 := by omega
  have hle : Submodule.span ℂ {g} ≤ Submodule.span ℂ {u, g} := Submodule.span_mono (by simp)
  have heq := Submodule.eq_of_le_of_finrank_le hle (le_trans hP1 (le_of_eq hW1.symm))
  have hu' : u ∈ Submodule.span ℂ {g} := by
    rw [heq]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu'
  exact ⟨c, hc.symm⟩

theorem P51_ii_core (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0) (hne : m 0 ≠ m 1)
    (h2 : 2 ≤ Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45)) :
    (∀ Y ∈ H, ∀ i, Y (i, 1) = 0) ∨ (∀ Y ∈ H, ∀ i, Y (i, 0) = 0) := by
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨j0, hj0'⟩ := Function.ne_iff.mp hm0
  have hj0 : m j0 ≠ 0 := hj0'
  have hbot := Bi H hH hq
  have hSV := (phi_onto H hH hq 0).1
  have hN0 := PS_N0_le K m hQB hm hm0 H hHK hH hq j0 hj0
  have rN := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (colsumL j0)
  have hc1 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0)) ≤ 1 := by
    have h := Submodule.finrank_le ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0))
    rw [Module.finrank_self] at h
    exact h
  have hA : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL j0) : Submodule ℂ M45) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  have hB : ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL j0)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  obtain ⟨Zs, hZsm, hZs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  obtain ⟨c0, hc0m, hc00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨Z, hZm, hZc⟩ := hc0m
  obtain ⟨⟨hZsK, hZsrs⟩, hZscs⟩ := hZsm
  obtain ⟨hZK, hZrs⟩ := hZm
  have hZsrs' : rs Zs = 0 := LinearMap.mem_ker.mp hZsrs
  have hZscs' : colsumL j0 Zs = 0 := LinearMap.mem_ker.mp hZscs
  have hZrs' : rs Z = 0 := LinearMap.mem_ker.mp hZrs
  obtain ⟨Z1, hZ1K, hZ1rs, hZ1cs⟩ : ∃ Z1 ∈ K, rs Z1 = 0 ∧ colsumL j0 Z1 = m j0 :=
    ⟨(m j0 / c0) • Z, K.smul_mem _ hZK, by rw [map_smul, hZrs', smul_zero],
      by rw [map_smul, hZc, smul_eq_mul, div_mul_cancel₀ _ hc00]⟩
  obtain ⟨κ, κ', Yf, hYf, Yfs, hYfs, hc, hc', hnf, hnfs, hff, hffs, hfs⟩ :=
    PS_bil K m hQB hm hm0 H hHK hH hq Z1 Zs hZ1K hZsK hZ1rs hZsrs'
  have hκ : κ = 1 := by
    have e := hc j0
    rw [tau_col_colsum, hZ1cs] at e
    exact mul_right_cancel₀ hj0 (e.symm.trans (one_mul _).symm)
  have hκ' : κ' = 0 := by
    have e := hc' j0
    rw [tau_col_colsum, hZscs'] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hj0
  rw [hκ] at hff hnf
  rw [hκ'] at hffs hnfs
  rw [hκ, hκ'] at hfs
  have hfs0 : rs Yfs ≠ 0 := by
    intro h0
    apply hZs0
    have hmem : Yfs ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
      Submodule.mem_inf.mpr ⟨hYfs, LinearMap.mem_ker.mpr h0⟩
    rw [hbot] at hmem
    have hY0 : Yfs = 0 := (Submodule.mem_bot ℂ).mp hmem
    funext ⟨i, j⟩
    rw [hnfs j i, hY0, map_zero]
    simp
  have hd : m 0 - m 1 ≠ 0 := sub_ne_zero.mpr hne
  have hlam : -(m 0 + m 1) / (m 0 - m 1) * (m 0 - m 1) = -(m 0 + m 1) := div_mul_cancel₀ _ hd
  have rel1 := two_rel m hm' Z1 Yf 1 hZ1rs hnf (fun i => hsupp Yf hYf i)
  have rel2 := two_rel m hm' Zs Yfs 0 hZsrs' hnfs (fun i => hsupp Yfs hYfs i)
  have hφf : ∀ i, phi 0 Yf i = -(m 0 + m 1) / (m 0 - m 1) * rs Yf i := by
    intro i
    apply mul_left_cancel₀ hd
    linear_combination rel1 i - rs Yf i * hlam
  have hφs : ∀ i, phi 0 Yfs i = -(m 0 + m 1) / (m 0 - m 1) * rs Yfs i := by
    intro i
    apply mul_left_cancel₀ hd
    linear_combination rel2 i - rs Yfs i * hlam
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℂ, lam = -(m 0 + m 1) / (m 0 - m 1) := ⟨_, rfl⟩
  rw [← hlamdef] at hφf hφs
  have hfpos : ip (rs Yf) (rs Yf) ≠ 0 := by
    rw [hff]
    norm_num
  have hlam2 : lam ^ 2 = 1 := by
    have e := ip_phi H hH Yf Yf hYf hYf 0
    simp only [ip] at e
    rw [hφf 0, hφf 1, hφf 2, hφf 3] at e
    have e' : (lam ^ 2 - 1) * ip (rs Yf) (rs Yf) = 0 := by
      simp only [ip]
      linear_combination e
    exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hfpos)
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    norm_num at hlam2
  have hτf := tau_rs H hH Yf hYf
  have hτs := tau_rs H hH Yfs hYfs
  have hfs' : ip (rs Yf) (rs Yfs) = 0 := by
    rw [hfs]
    ring
  have hss : ip (rs Yfs) (rs Yfs) = 0 := by
    rw [hffs]
    ring
  have inner : ∀ Y ∈ H, ip (rs Y) (rs Yfs) ≠ 0 → ∀ i, phi 0 Y i = lam * rs Y i := by
    intro Y hY hne'
    have e1 := ip_phi H hH Y Yf hY hYf 0
    have e2 := ip_phi H hH Y Yfs hY hYfs 0
    simp only [ip] at e1 e2
    rw [hφf 0, hφf 1, hφf 2, hφf 3] at e1
    rw [hφs 0, hφs 1, hφs 2, hφs 3] at e2
    have huτ : tau (fun i => phi 0 Y i - lam * rs Y i) = 0 := by
      have h1 := tau_phi H hH Y hY 0
      have h2 := tau_rs H hH Y hY
      simp only [tau] at h1 h2 ⊢
      linear_combination h1 - lam * h2
    have huf : ip (fun i => phi 0 Y i - lam * rs Y i) (rs Yf) = 0 := by
      simp only [ip]
      linear_combination lam * e1
        - (phi 0 Y 0 * rs Yf 0 + phi 0 Y 1 * rs Yf 1 + phi 0 Y 2 * rs Yf 2 + phi 0 Y 3 * rs Yf 3)
          * hlam2
    have hus : ip (fun i => phi 0 Y i - lam * rs Y i) (rs Yfs) = 0 := by
      simp only [ip]
      linear_combination lam * e2
        - (phi 0 Y 0 * rs Yfs 0 + phi 0 Y 1 * rs Yfs 1 + phi 0 Y 2 * rs Yfs 2
          + phi 0 Y 3 * rs Yfs 3) * hlam2
    obtain ⟨c, hcu⟩ := span2_perp _ (rs Yf) (rs Yfs) huτ hτf hτs hfs0 hfpos hfs' hss huf hus
    have hu : ∀ i, phi 0 Y i = lam * rs Y i + c * rs Yfs i := by
      intro i
      have h := congrFun hcu i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      linear_combination h
    have e3 := ip_phi H hH Y Y hY hY 0
    have hc0 : 2 * lam * c * ip (rs Y) (rs Yfs) = 0 := by
      simp only [ip] at e3 hss ⊢
      linear_combination e3
        - (phi 0 Y 0 + lam * rs Y 0 + c * rs Yfs 0) * hu 0
        - (phi 0 Y 1 + lam * rs Y 1 + c * rs Yfs 1) * hu 1
        - (phi 0 Y 2 + lam * rs Y 2 + c * rs Yfs 2) * hu 2
        - (phi 0 Y 3 + lam * rs Y 3 + c * rs Yfs 3) * hu 3
        - (rs Y 0 * rs Y 0 + rs Y 1 * rs Y 1 + rs Y 2 * rs Y 2 + rs Y 3 * rs Y 3) * hlam2
        - c ^ 2 * hss
    have hcz : c = 0 := by
      have h : (2 * lam) * c * ip (rs Y) (rs Yfs) = 0 := hc0
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exfalso
          exact (mul_ne_zero two_ne_zero hlam0) h
        · exact h
      · exact absurd h hne'
    intro i
    rw [hu i, hcz]
    ring
  have hex : ∃ Ys ∈ H, ip (rs Ys) (rs Yfs) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hfs0
    apply nondeg
    · exact hτs
    · intro v hv
      have hv' : v ∈ H.map rs := by
        rw [hSV, mem_Vs]
        exact hv
      obtain ⟨Y', hY', rfl⟩ := hv'
      have h := hcon Y' hY'
      simp only [ip] at h ⊢
      linear_combination h
  obtain ⟨Ys, hYs, hYs0⟩ := hex
  have hall : ∀ Y ∈ H, ∀ i, phi 0 Y i = lam * rs Y i := by
    intro Y hY i
    by_cases h0 : ip (rs Y) (rs Yfs) = 0
    · have hsum : ip (rs (Y + Ys)) (rs Yfs) ≠ 0 := by
        rw [map_add]
        simp only [ip, Pi.add_apply] at h0 hYs0 ⊢
        intro h
        apply hYs0
        linear_combination h - h0
      have a1 := inner (Y + Ys) (H.add_mem hY hYs) hsum i
      have a2 := inner Ys hYs hYs0 i
      rw [map_add, map_add] at a1
      simp only [Pi.add_apply] at a1
      linear_combination a1 - a2
    · exact inner Y hY h0 i
  have hl : (lam - 1) * (lam + 1) = 0 := by linear_combination hlam2
  rcases mul_eq_zero.mp hl with h | h
  · left
    intro Y hY i
    have e := hall Y hY i
    have hl1 : lam = 1 := sub_eq_zero.mp h
    rw [hl1, phi_apply, rs_apply, (hsupp Y hY i).1, (hsupp Y hY i).2.1, (hsupp Y hY i).2.2] at e
    linear_combination (-1 / 2 : ℂ) * e
  · right
    intro Y hY i
    have e := hall Y hY i
    have hl1 : lam = -1 := by linear_combination h
    rw [hl1, phi_apply, rs_apply, (hsupp Y hY i).1, (hsupp Y hY i).2.1, (hsupp Y hY i).2.2] at e
    linear_combination (1 / 2 : ℂ) * e

theorem cc_of_single (H : Submodule ℂ M45) (a : Fin 5)
    (h : ∀ Y ∈ H, ∀ i j, j ≠ a → Y (i, j) = 0) : ∀ Y ∈ H, ∀ n : Fin 5, cE Y n ∈ H := by
  intro Y hY n
  by_cases hn : n = a
  · have e : cE Y n = Y := by
      funext p
      obtain ⟨i, j⟩ := p
      show (if j = n then Y (i, n) else 0) = Y (i, j)
      by_cases hj : j = n
      · rw [if_pos hj, hj]
      · rw [if_neg hj]
        exact (h Y hY i j (fun hja => hj (hja.trans hn.symm))).symm
    rw [e]
    exact hY
  · have e : cE Y n = 0 := by
      funext p
      obtain ⟨i, j⟩ := p
      show (if j = n then Y (i, n) else 0) = 0
      by_cases hj : j = n
      · rw [if_pos hj]
        exact h Y hY i n hn
      · rw [if_neg hj]
    rw [e]
    exact H.zero_mem

theorem P51_two (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hinj : Function.Injective m) (H : Submodule ℂ M45) (hHK : H ≤ K)
    (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0) :
    Module.finrank ℂ K ≤ 4 := by
  by_contra h5
  push_neg at h5
  have hm0 : m ≠ 0 := by
    intro h
    have h01 : m 0 = m 1 := by simp [h]
    exact absurd (hinj h01) (by decide)
  have hQB := QBc_of K m hdef hm hm0
  have hS := QB_map_rs K m hQB hm
  have rK := rank_nullity K rs
  have h2 : 2 ≤ Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) := by omega
  have hne : m 0 ≠ m 1 := fun h => absurd (hinj h) (by decide)
  rcases P51_ii_core K m hQB hm hm0 H hHK hH hq hsupp hne h2 with h1 | h0
  · have hcc := cc_of_single H 0 (fun Y hY i j hj => by
      fin_cases j
      · exact absurd rfl hj
      · exact h1 Y hY i
      · exact (hsupp Y hY i).1
      · exact (hsupp Y hY i).2.1
      · exact (hsupp Y hY i).2.2)
    have h4 := P51_i K m hdef hm hinj H hHK hH hq hcc
    omega
  · have hcc := cc_of_single H 1 (fun Y hY i j hj => by
      fin_cases j
      · exact h0 Y hY i
      · exact absurd rfl hj
      · exact (hsupp Y hY i).1
      · exact (hsupp Y hY i).2.1
      · exact (hsupp Y hY i).2.2)
    have h4 := P51_i K m hdef hm hinj H hHK hH hq hcc
    omega

theorem P51_two_perm (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hinj : Function.Injective m) (H : Submodule ℂ M45) (hHK : H ≤ K)
    (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3) (σ : Equiv.Perm (Fin 5))
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, σ 2) = 0 ∧ Y (i, σ 3) = 0 ∧ Y (i, σ 4) = 0) :
    Module.finrank ℂ K ≤ 4 := by
  have hrs : (H.map (cperm σ)).map rs = H.map rs := by
    ext v
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
      exact ⟨Y, hY, (rs_cperm σ Y).symm⟩
    · rintro ⟨Y, hY, rfl⟩
      exact ⟨cperm σ Y, ⟨Y, hY, rfl⟩, rs_cperm σ Y⟩
  have hm' : ∑ a, (fun a => m (σ a)) a = 0 := by
    show ∑ a, m (σ a) = 0
    rw [Equiv.sum_comp σ m]
    exact hm
  have hq' : Module.finrank ℂ ((H.map (cperm σ)).map rs) = 3 := by
    rw [hrs]
    exact hq
  have hsupp' : ∀ Y ∈ H.map (cperm σ), ∀ i, Y (i, 2) = 0 ∧ Y (i, 3) = 0 ∧ Y (i, 4) = 0 := by
    rintro _ ⟨Y, hY, rfl⟩ i
    exact hsupp Y hY i
  have hinj' : Function.Injective (fun a => m (σ a)) := hinj.comp σ.injective
  have h := P51_two (K.map (cperm σ)) (fun a => m (σ a)) (DefLine_perm σ K m hdef) hm' hinj'
    (H.map (cperm σ)) (Submodule.map_mono hHK) (SLev_perm σ H hH) hq' hsupp'
  have hinjc : Function.Injective (cperm σ) := by
    intro Y Y' h
    funext p
    obtain ⟨i, j⟩ := p
    have e := congrFun h (i, σ.symm j)
    simp only [cperm_apply, Equiv.apply_symm_apply] at e
    exact e
  have hfr : Module.finrank ℂ (K.map (cperm σ)) = Module.finrank ℂ K :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (cperm σ) hinjc K)).symm
  omega

theorem rank1_col (H : Submodule ℂ M45) (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (c : Fin 5) (v : V4) (hcol : ∀ Y ∈ H, ∃ a : ℂ, col Y c = a • v) (Y0 : M45) (hY0 : Y0 ∈ H)
    (hne : col Y0 c ≠ 0) :
    ip v v ≠ 0 ∧ ∀ Y ∈ H, col Y c = (ip (rs Y) v / ip v v) • v := by
  have hSV := (phi_onto H hH hq 0).1
  obtain ⟨a0, ha0⟩ := hcol Y0 hY0
  have ha0' : a0 ≠ 0 := by
    rintro rfl
    apply hne
    rw [ha0, zero_smul]
  have hrel : ∀ Y ∈ H, ∀ a : ℂ, col Y c = a • v → a * ip v v = ip (rs Y) v := by
    intro Y hY a ha
    have e1 := C2pol H hH Y Y0 hY hY0 c
    have e2 := C2 H hH Y0 hY0 c
    rw [ha, ha0] at e1
    rw [ha0] at e2
    simp only [ip, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 ha0')
    linear_combination a0 * e1 - a * e2
  have hvv : ip v v ≠ 0 := by
    intro h0
    have hτv : tau v = 0 := by
      have h := C1 H hH Y0 hY0 c
      rw [ha0] at h
      simp only [tau, Pi.smul_apply, smul_eq_mul] at h ⊢
      have h' : a0 * (v 0 + v 1 + v 2 + v 3) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left ha0'
    have hv0 : v = 0 := by
      apply nondeg v hτv
      intro w hw
      have hw' : w ∈ H.map rs := by
        rw [hSV, mem_Vs]
        exact hw
      obtain ⟨Y, hY, rfl⟩ := hw'
      obtain ⟨a, ha⟩ := hcol Y hY
      have h := hrel Y hY a ha
      rw [h0, mul_zero] at h
      simp only [ip] at h ⊢
      linear_combination -h
    apply hne
    rw [ha0, hv0, smul_zero]
  refine ⟨hvv, fun Y hY => ?_⟩
  obtain ⟨a, ha⟩ := hcol Y hY
  have h := hrel Y hY a ha
  rw [ha]
  congr 1
  rw [eq_div_iff hvv]
  exact h

theorem X5_struct (H : Submodule ℂ M45) (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 3) = 0 ∧ Y (i, 4) = 0) (v : V4) (hvv : ip v v ≠ 0)
    (hc2 : ∀ Y ∈ H, col Y 2 = (ip (rs Y) v / ip v v) • v) (Yv : M45) (hYv : Yv ∈ H)
    (hrs : rs Yv = v) : col Yv 0 = 0 ∧ col Yv 1 = 0 ∧ col Yv 2 = v := by
  have hbot := Bi H hH hq
  have h2v : col Yv 2 = v := by
    rw [hc2 Yv hYv, hrs, div_self hvv, one_smul]
  have h01 : ∀ i, Yv (i, 0) + Yv (i, 1) = 0 := by
    intro i
    have h := congrFun hrs i
    rw [rs_apply, (hsupp Yv hYv i).1, (hsupp Yv hYv i).2] at h
    have h2 : Yv (i, 2) = v i := congrFun h2v i
    linear_combination h - h2
  have hn0 := ip_phi H hH Yv Yv hYv hYv 0
  have hn1 := ip_phi H hH Yv Yv hYv hYv 1
  simp only [ip, phi_apply, hrs] at hn0 hn1
  have hww : ip (col Yv 0) (col Yv 0) = 0 := by
    simp only [ip, col]
    linear_combination (1 / 8 : ℂ) * (hn0 + hn1)
      - (1 / 2 : ℂ) * ((Yv (0, 1) - Yv (0, 0) - v 0) * h01 0 + (Yv (1, 1) - Yv (1, 0) - v 1) * h01 1
        + (Yv (2, 1) - Yv (2, 0) - v 2) * h01 2 + (Yv (3, 1) - Yv (3, 0) - v 3) * h01 3)
  have hwv : ip (col Yv 0) v = 0 := by
    simp only [ip, col]
    linear_combination (1 / 8 : ℂ) * (hn1 - hn0)
      - (1 / 2 : ℂ) * ((Yv (0, 1) - Yv (0, 0) - v 0) * h01 0 + (Yv (1, 1) - Yv (1, 0) - v 1) * h01 1
        + (Yv (2, 1) - Yv (2, 0) - v 2) * h01 2 + (Yv (3, 1) - Yv (3, 0) - v 3) * h01 3)
  have orth : ∀ Y ∈ H, ip (rs Y) v = 0 →
      ip (phi 0 Y) (col Yv 0) = 0 ∧ ip (phi 0 Y) v = 0 := by
    intro Y hY hYv0
    have hcY : col Y 2 = 0 := by
      rw [hc2 Y hY, hYv0, zero_div, zero_smul]
    have hφ1 : ∀ i, phi 1 Y i = -phi 0 Y i := by
      intro i
      have h2 : Y (i, 2) = 0 := congrFun hcY i
      simp only [phi_apply, rs_apply, h2, (hsupp Y hY i).1, (hsupp Y hY i).2]
      ring
    have e1 := ip_phi H hH Y Yv hY hYv 0
    have e2 := ip_phi H hH Y Yv hY hYv 1
    rw [hrs, hYv0] at e1
    rw [hrs, hYv0] at e2
    simp only [ip] at e1 e2
    rw [hφ1 0, hφ1 1, hφ1 2, hφ1 3] at e2
    simp only [phi_apply 0 Yv, phi_apply 1 Yv, hrs] at e1 e2
    constructor
    · simp only [ip, col]
      linear_combination (1 / 4 : ℂ) * (e1 + e2)
        + (1 / 2 : ℂ) * (phi 0 Y 0 * h01 0 + phi 0 Y 1 * h01 1 + phi 0 Y 2 * h01 2
          + phi 0 Y 3 * h01 3)
    · simp only [ip]
      linear_combination (1 / 2 : ℂ) * (e2 - e1)
        + (phi 0 Y 0 * h01 0 + phi 0 Y 1 * h01 1 + phi 0 Y 2 * h01 2 + phi 0 Y 3 * h01 3)
  have hy0 : col Yv 0 = 0 := by
    by_contra hne
    have hτv : tau v = 0 := by
      rw [← hrs]
      exact tau_rs H hH Yv hYv
    have hτw : tau (col Yv 0) = 0 := C1 H hH Yv hYv 0
    have hW1 : Module.finrank ℂ (Submodule.span ℂ {col Yv 0}) = 1 := finrank_span_singleton hne
    have hlt : Submodule.span ℂ {col Yv 0} < Submodule.span ℂ {v, col Yv 0} := by
      refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
      intro h
      have hv' : v ∈ Submodule.span ℂ {col Yv 0} := by
        rw [h]
        exact Submodule.subset_span (by simp)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv'
      apply hvv
      rw [← hc]
      simp only [ip, Pi.smul_apply, smul_eq_mul] at hww ⊢
      linear_combination c ^ 2 * hww
    have hW2 : 2 ≤ Module.finrank ℂ (Submodule.span ℂ {v, col Yv 0}) := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hH3 : Module.finrank ℂ H = 3 := by
      have r := rank_nullity H rs
      rw [hbot, finrank_bot] at r
      omega
    have r1 := rank_nullity H ((dotDual v).comp rs)
    have hm1 : Module.finrank ℂ (H.map ((dotDual v).comp rs)) ≤ 1 := by
      have h := Submodule.finrank_le (H.map ((dotDual v).comp rs))
      rw [Module.finrank_self] at h
      exact h
    have r2 := rank_nullity (H ⊓ LinearMap.ker ((dotDual v).comp rs) : Submodule ℂ M45) (phi 0)
    have hb2 : ((H ⊓ LinearMap.ker ((dotDual v).comp rs)) ⊓ LinearMap.ker (phi 0) :
        Submodule ℂ M45) = ⊥ := by
      rw [eq_bot_iff]
      rintro Y ⟨⟨hY, -⟩, hY0⟩
      rw [Submodule.mem_bot]
      exact phi_inj H hH hq 0 Y hY (LinearMap.mem_ker.mp hY0)
    rw [hb2, finrank_bot] at r2
    have hperp := perp_sup_one ((H ⊓ LinearMap.ker ((dotDual v).comp rs) : Submodule ℂ M45).map
      (phi 0)) (Submodule.span ℂ {v, col Yv 0})
      (by
        rintro _ ⟨Y, ⟨hY, -⟩, rfl⟩
        exact tau_phi H hH Y hY 0)
      (by
        intro p hp
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hp
        simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hτv hτw ⊢
        linear_combination s * hτv + t * hτw)
      (by
        rintro _ ⟨Y, ⟨hY, hYk⟩, rfl⟩ w hw
        have hψ : ip (rs Y) v = 0 := by
          have h := LinearMap.mem_ker.mp hYk
          rw [LinearMap.comp_apply, dotDual_apply, Fin.sum_univ_four] at h
          simp only [ip]
          linear_combination h
        obtain ⟨o1, o2⟩ := orth Y hY hψ
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
        simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at o1 o2 ⊢
        linear_combination s * o2 + t * o1)
    omega
  refine ⟨hy0, ?_, h2v⟩
  funext i
  have h := h01 i
  have h0 : Yv (i, 0) = 0 := congrFun hy0 i
  show Yv (i, 1) = 0
  linear_combination h - h0

theorem X5_perp (H : Submodule ℂ M45) (hH : SLev H) (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 3) = 0 ∧ Y (i, 4) = 0) (v : V4) (hvv : ip v v ≠ 0)
    (hc2 : ∀ Y ∈ H, col Y 2 = (ip (rs Y) v / ip v v) • v) (Yv : M45) (hYv : Yv ∈ H)
    (hrs : rs Yv = v) (Y : M45) (hY : Y ∈ H) (hYv0 : ip (rs Y) v = 0) :
    col Y 2 = 0 ∧ (∀ i, phi 1 Y i = -phi 0 Y i) ∧ ip (phi 0 Y) v = 0 := by
  obtain ⟨h0, -, -⟩ := X5_struct H hH hq hsupp v hvv hc2 Yv hYv hrs
  have hcY : col Y 2 = 0 := by
    rw [hc2 Y hY, hYv0, zero_div, zero_smul]
  refine ⟨hcY, fun i => ?_, ?_⟩
  · have h2 : Y (i, 2) = 0 := congrFun hcY i
    simp only [phi_apply, rs_apply, h2, (hsupp Y hY i).1, (hsupp Y hY i).2]
    ring
  · have e1 := ip_phi H hH Y Yv hY hYv 0
    rw [hrs, hYv0] at e1
    have hφv : ∀ i, phi 0 Yv i = -v i := by
      intro i
      have hz : Yv (i, 0) = 0 := congrFun h0 i
      rw [phi_apply, hz, hrs]
      ring
    simp only [ip] at e1 ⊢
    rw [hφv 0, hφv 1, hφv 2, hφv 3] at e1
    linear_combination -e1

def X2c (z1 z2 z3 z4 : V4) : ℂ :=
  2 * (tau z1 * tau z2 + tau z1 * tau z3 + tau z1 * tau z4 + tau z2 * tau z3
      + tau z2 * tau z4 + tau z3 * tau z4)
    - 2 * (ip z1 z2 + ip z1 z3 + ip z1 z4 + ip z2 z3 + ip z2 z4 + ip z3 z4)

def X3c (z1 z2 z3 z4 : V4) : ℂ :=
  (tau z1 * tau z2 * tau z3 - tau z1 * ip z2 z3 - tau z2 * ip z1 z3
      - tau z3 * ip z1 z2 + 2 * t3 z1 z2 z3)
    + (tau z1 * tau z2 * tau z4 - tau z1 * ip z2 z4 - tau z2 * ip z1 z4
      - tau z4 * ip z1 z2 + 2 * t3 z1 z2 z4)
    + (tau z1 * tau z3 * tau z4 - tau z1 * ip z3 z4 - tau z3 * ip z1 z4
      - tau z4 * ip z1 z3 + 2 * t3 z1 z3 z4)
    + (tau z2 * tau z3 * tau z4 - tau z2 * ip z3 z4 - tau z3 * ip z2 z4
      - tau z4 * ip z2 z3 + 2 * t3 z2 z3 z4)

theorem pc_expand2 (z1 z2 z3 z4 : V4) (c : ℂ) :
    pc (fun i => 1 + c * z1 i) (fun i => 1 + c * z2 i) (fun i => 1 + c * z3 i)
      (fun i => 1 + c * z4 i) =
    24 + c * (6 * (tau z1 + tau z2 + tau z3 + tau z4)) + c ^ 2 * X2c z1 z2 z3 z4
      + c ^ 3 * X3c z1 z2 z3 z4 + c ^ 4 * pc z1 z2 z3 z4 := by
  rw [pc_expand]
  simp only [X2c, X3c]

set_option maxHeartbeats 2000000 in
theorem pc_dd_scale (d a b : V4) (c : ℂ) :
    pc (fun k => c * d k) (fun k => c * d k) (fun k => 1 + c * a k) (fun k => 1 + c * b k)
      = c ^ 2 * (4 * e2 d + 2 * c * ip (a + b) (Ed d) + c ^ 2 * pc d d a b) := by
  simp (config := {decide := true}) only [pc, e2, Ed, tau, ip, Pi.add_apply, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem TC5_deg_pair (K : Submodule ℂ M45) (j l : Fin 5)
    (hcl : ∀ W ∈ K, pc (fun k => 1 + uY W k) (fun k => 1 + uY W k) (fun k => 1 + W (k, j))
        (fun k => 1 + W (k, l)) - pc (dY W) (dY W) (fun k => 1 + W (k, j))
        (fun k => 1 + W (k, l)) = 24)
    (Y : M45) (hY : Y ∈ K) :
    tau (uY Y) + tau (uY Y) + tau (col Y j) + tau (col Y l) = 0 ∧
    X2c (uY Y) (uY Y) (col Y j) (col Y l) = 4 * e2 (dY Y) ∧
    X3c (uY Y) (uY Y) (col Y j) (col Y l) = 2 * ip (col Y j + col Y l) (Ed (dY Y)) ∧
    pc (uY Y) (uY Y) (col Y j) (col Y l) = pc (dY Y) (dY Y) (col Y j) (col Y l) := by
  have F : ∀ c : ℂ, 0 + (6 * (tau (uY Y) + tau (uY Y) + tau (col Y j) + tau (col Y l))) * c
      + (X2c (uY Y) (uY Y) (col Y j) (col Y l) - 4 * e2 (dY Y)) * c ^ 2
      + (X3c (uY Y) (uY Y) (col Y j) (col Y l) - 2 * ip (col Y j + col Y l) (Ed (dY Y))) * c ^ 3
      + (pc (uY Y) (uY Y) (col Y j) (col Y l) - pc (dY Y) (dY Y) (col Y j) (col Y l)) * c ^ 4
      = 0 := by
    intro c
    have h := hcl (c • Y) (K.smul_mem c hY)
    have eu : (fun k => 1 + uY (c • Y) k) = fun i => 1 + c * uY Y i := by
      funext k
      simp only [uY, Pi.smul_apply, smul_eq_mul]
      ring
    have ed : dY (c • Y) = fun i => c * dY Y i := by
      funext k
      simp only [dY, Pi.smul_apply, smul_eq_mul]
      ring
    have ej : (fun k => 1 + (c • Y) (k, j)) = fun i => 1 + c * col Y j i := funext fun k => rfl
    have el : (fun k => 1 + (c • Y) (k, l)) = fun i => 1 + c * col Y l i := funext fun k => rfl
    rw [eu, ed, ej, el, pc_expand2 (uY Y) (uY Y) (col Y j) (col Y l) c,
      pc_dd_scale (dY Y) (col Y j) (col Y l) c] at h
    linear_combination h
  have hr := roots5 (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) inj_succ5 0
    (6 * (tau (uY Y) + tau (uY Y) + tau (col Y j) + tau (col Y l)))
    (X2c (uY Y) (uY Y) (col Y j) (col Y l) - 4 * e2 (dY Y))
    (X3c (uY Y) (uY Y) (col Y j) (col Y l) - 2 * ip (col Y j + col Y l) (Ed (dY Y)))
    (pc (uY Y) (uY Y) (col Y j) (col Y l) - pc (dY Y) (dY Y) (col Y j) (col Y l))
    (fun k => F _)
  obtain ⟨-, a1, a2, a3, a4⟩ := hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 6 : ℂ) * a1
  · linear_combination a2
  · linear_combination a3
  · linear_combination a4

theorem TC5_deg_i (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Y : M45) (hY : Y ∈ K) :
    tau (uY Y) + tau (col Y 2) + tau (col Y 3) + tau (col Y 4) = 0 ∧
    X2c (uY Y) (col Y 2) (col Y 3) (col Y 4) = 0 ∧
    X3c (uY Y) (col Y 2) (col Y 3) (col Y 4) = 0 ∧
    pc (uY Y) (col Y 2) (col Y 3) (col Y 4) = 0 := by
  have hall : ∀ c : ℂ, pc (fun i => 1 + c * uY Y i) (fun i => 1 + c * col Y 2 i)
      (fun i => 1 + c * col Y 3 i) (fun i => 1 + c * col Y 4 i) = 24 := by
    intro c
    have h := ((TC5_normal K).mp hdef (c • Y) (K.smul_mem c hY)).1
    have eu : (fun k => 1 + uY (c • Y) k) = fun i => 1 + c * uY Y i := by
      funext k
      simp only [uY, Pi.smul_apply, smul_eq_mul]
      ring
    have e2' : (fun k => 1 + (c • Y) (k, 2)) = fun i => 1 + c * col Y 2 i := funext fun k => rfl
    have e3 : (fun k => 1 + (c • Y) (k, 3)) = fun i => 1 + c * col Y 3 i := funext fun k => rfl
    have e4 : (fun k => 1 + (c • Y) (k, 4)) = fun i => 1 + c * col Y 4 i := funext fun k => rfl
    rw [eu, e2', e3, e4] at h
    exact h
  obtain ⟨b1, b2, b3, b4⟩ := coeffs _ _ _ _ hall
  exact ⟨b1, b2, b3, b4⟩

theorem TC5_degree (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Y : M45) (hY : Y ∈ K) :
    (X2c (uY Y) (uY Y) (col Y 3) (col Y 4) = 4 * e2 (dY Y) ∧
      X2c (uY Y) (uY Y) (col Y 2) (col Y 4) = 4 * e2 (dY Y) ∧
      X2c (uY Y) (uY Y) (col Y 2) (col Y 3) = 4 * e2 (dY Y)) ∧
    (X3c (uY Y) (uY Y) (col Y 3) (col Y 4) = 2 * ip (col Y 3 + col Y 4) (Ed (dY Y)) ∧
      X3c (uY Y) (uY Y) (col Y 2) (col Y 4) = 2 * ip (col Y 2 + col Y 4) (Ed (dY Y)) ∧
      X3c (uY Y) (uY Y) (col Y 2) (col Y 3) = 2 * ip (col Y 2 + col Y 3) (Ed (dY Y))) ∧
    (pc (uY Y) (uY Y) (col Y 3) (col Y 4) = pc (dY Y) (dY Y) (col Y 3) (col Y 4) ∧
      pc (uY Y) (uY Y) (col Y 2) (col Y 4) = pc (dY Y) (dY Y) (col Y 2) (col Y 4) ∧
      pc (uY Y) (uY Y) (col Y 2) (col Y 3) = pc (dY Y) (dY Y) (col Y 2) (col Y 3)) := by
  have hN := (TC5_normal K).mp hdef
  obtain ⟨-, a2, a3, a4⟩ := TC5_deg_pair K 3 4 (fun W hW => (hN W hW).2.1) Y hY
  obtain ⟨-, b2, b3, b4⟩ := TC5_deg_pair K 2 4 (fun W hW => (hN W hW).2.2.1) Y hY
  obtain ⟨-, g2, g3, g4⟩ := TC5_deg_pair K 2 3 (fun W hW => (hN W hW).2.2.2) Y hY
  exact ⟨⟨a2, b2, g2⟩, ⟨a3, b3, g3⟩, ⟨a4, b4, g4⟩⟩

theorem X5_fv (m : Fin 5 → ℂ) (hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0) (hmc : m 2 ≠ 0)
    (H : Submodule ℂ M45) (hH : SLev H)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 3) = 0 ∧ Y (i, 4) = 0) (v : V4) (hvv : ip v v ≠ 0)
    (hc2 : ∀ Y ∈ H, col Y 2 = (ip (rs Y) v / ip v v) • v) (Yv : M45) (hYv : Yv ∈ H)
    (hrs : rs Yv = v) (hy0 : col Yv 0 = 0) (hy1 : col Yv 1 = 0)
    (W YW : M45) (κW : ℂ) (hYW : YW ∈ H) (hW0 : rs W = 0)
    (hnfW : ∀ j, ∀ i, W (i, j) = κW * m j / 4 + m j * phi j YW i) : ip (rs YW) v = 0 := by
  have hrow : ∀ i, m 0 * phi 0 YW i + m 1 * phi 1 YW i + m 2 * phi 2 YW i + m 3 * phi 3 YW i
      + m 4 * phi 4 YW i = 0 := by
    intro i
    have h := congrFun hW0 i
    rw [rs_apply, hnfW 0 i, hnfW 1 i, hnfW 2 i, hnfW 3 i, hnfW 4 i] at h
    simp only [Pi.zero_apply] at h
    linear_combination h - (κW / 4) * hm'
  have hv0 : phi 0 Yv = -v := by
    funext i
    have hz : Yv (i, 0) = 0 := congrFun hy0 i
    rw [phi_apply, hz, hrs]
    simp
  have hv1 : phi 1 Yv = -v := by
    funext i
    have hz : Yv (i, 1) = 0 := congrFun hy1 i
    rw [phi_apply, hz, hrs]
    simp
  have p0 : ip (phi 0 YW) v = -ip (rs YW) v := by
    have e := ip_phi H hH YW Yv hYW hYv 0
    rw [hv0, hrs] at e
    simp only [ip, Pi.neg_apply] at e ⊢
    linear_combination -e
  have p1 : ip (phi 1 YW) v = -ip (rs YW) v := by
    have e := ip_phi H hH YW Yv hYW hYv 1
    rw [hv1, hrs] at e
    simp only [ip, Pi.neg_apply] at e ⊢
    linear_combination -e
  have p2 : ip (phi 2 YW) v = ip (rs YW) v := by
    have hy : ∀ i, YW (i, 2) = (ip (rs YW) v / ip v v) * v i := fun i => congrFun (hc2 YW hYW) i
    have hcd : (ip (rs YW) v / ip v v) * ip v v = ip (rs YW) v := div_mul_cancel₀ _ hvv
    simp only [ip] at hcd
    simp only [ip, phi_apply]
    rw [hy 0, hy 1, hy 2, hy 3]
    simp only [ip]
    linear_combination 2 * hcd
  have p3 : ip (phi 3 YW) v = -ip (rs YW) v := by
    simp only [ip, phi_apply, (hsupp YW hYW 0).1, (hsupp YW hYW 1).1, (hsupp YW hYW 2).1,
      (hsupp YW hYW 3).1]
    ring
  have p4 : ip (phi 4 YW) v = -ip (rs YW) v := by
    simp only [ip, phi_apply, (hsupp YW hYW 0).2, (hsupp YW hYW 1).2, (hsupp YW hYW 2).2,
      (hsupp YW hYW 3).2]
    ring
  have sumrel : m 0 * ip (phi 0 YW) v + m 1 * ip (phi 1 YW) v + m 2 * ip (phi 2 YW) v
      + m 3 * ip (phi 3 YW) v + m 4 * ip (phi 4 YW) v = 0 := by
    simp only [ip]
    linear_combination v 0 * hrow 0 + v 1 * hrow 1 + v 2 * hrow 2 + v 3 * hrow 3
  rw [p0, p1, p2, p3, p4] at sumrel
  have h2 : (2 * m 2) * ip (rs YW) v = 0 := by
    linear_combination sumrel + ip (rs YW) v * hm'
  exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero hmc)

theorem X5_mc (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hQB : QBc K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) (H : Submodule ℂ M45) (hHK : H ≤ K) (hH : SLev H)
    (hq : Module.finrank ℂ (H.map rs) = 3)
    (hsupp : ∀ Y ∈ H, ∀ i, Y (i, 3) = 0 ∧ Y (i, 4) = 0) (v : V4) (hvv : ip v v ≠ 0)
    (hc2 : ∀ Y ∈ H, col Y 2 = (ip (rs Y) v / ip v v) • v) (Yv : M45) (hYv : Yv ∈ H)
    (hrs : rs Yv = v) (h2 : 2 ≤ Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45)) :
    m 2 = 0 := by
  by_contra hmc
  have hm' : m 0 + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [Fin.sum_univ_five] at hm
    exact hm
  obtain ⟨hy0, hy1, -⟩ := X5_struct H hH hq hsupp v hvv hc2 Yv hYv hrs
  have hbot := Bi H hH hq
  have hN0 := PS_N0_le K m hQB hm hm0 H hHK hH hq 2 hmc
  have rN := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (colsumL 2)
  have hc1 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL 2)) ≤ 1 := by
    have h := Submodule.finrank_le ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL 2))
    rw [Module.finrank_self] at h
    exact h
  have hA : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker (colsumL 2) : Submodule ℂ M45) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  have hB : ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colsumL 2)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rN
    omega
  obtain ⟨Zs, hZsm, hZs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  obtain ⟨c0, hc0m, hc00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨Z, hZm, hZc⟩ := hc0m
  obtain ⟨⟨hZsK, hZsrs⟩, hZscs⟩ := hZsm
  obtain ⟨hZK, hZrs⟩ := hZm
  have hZsrs' : rs Zs = 0 := LinearMap.mem_ker.mp hZsrs
  have hZscs' : colsumL 2 Zs = 0 := LinearMap.mem_ker.mp hZscs
  have hZrs' : rs Z = 0 := LinearMap.mem_ker.mp hZrs
  obtain ⟨Z1, hZ1K, hZ1rs, hZ1cs⟩ : ∃ Z1 ∈ K, rs Z1 = 0 ∧ colsumL 2 Z1 = m 2 :=
    ⟨(m 2 / c0) • Z, K.smul_mem _ hZK, by rw [map_smul, hZrs', smul_zero],
      by rw [map_smul, hZc, smul_eq_mul, div_mul_cancel₀ _ hc00]⟩
  obtain ⟨κ, κ', Yf, hYf, Yfs, hYfs, hc, hc', hnf, hnfs, hff, hffs, hfs⟩ :=
    PS_bil K m hQB hm hm0 H hHK hH hq Z1 Zs hZ1K hZsK hZ1rs hZsrs'
  have hκ : κ = 1 := by
    have e := hc 2
    rw [tau_col_colsum, hZ1cs] at e
    exact mul_right_cancel₀ hmc (e.symm.trans (one_mul _).symm)
  have hκ' : κ' = 0 := by
    have e := hc' 2
    rw [tau_col_colsum, hZscs'] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hmc
  rw [hκ] at hff
  rw [hκ'] at hffs hnfs
  rw [hκ, hκ'] at hfs
  have hfs0 : rs Yfs ≠ 0 := by
    intro h0
    apply hZs0
    have hmem : Yfs ∈ (H ⊓ LinearMap.ker rs : Submodule ℂ M45) :=
      Submodule.mem_inf.mpr ⟨hYfs, LinearMap.mem_ker.mpr h0⟩
    rw [hbot] at hmem
    have hY0 : Yfs = 0 := (Submodule.mem_bot ℂ).mp hmem
    funext ⟨i, j⟩
    rw [hnfs j i, hY0, map_zero]
    simp
  have fv1 := X5_fv m hm' hmc H hH hsupp v hvv hc2 Yv hYv hrs hy0 hy1 Z1 Yf κ hYf hZ1rs hnf
  have fv2 := X5_fv m hm' hmc H hH hsupp v hvv hc2 Yv hYv hrs hy0 hy1 Zs Yfs 0 hYfs hZsrs' hnfs
  have hfpos : ip (rs Yf) (rs Yf) ≠ 0 := by
    rw [hff]
    norm_num
  have hfs' : ip (rs Yf) (rs Yfs) = 0 := by
    rw [hfs]
    ring
  have hss : ip (rs Yfs) (rs Yfs) = 0 := by
    rw [hffs]
    ring
  have hτv : tau v = 0 := by
    rw [← hrs]
    exact tau_rs H hH Yv hYv
  have hvf : ip v (rs Yf) = 0 := by
    simp only [ip] at fv1 ⊢
    linear_combination fv1
  have hvs : ip v (rs Yfs) = 0 := by
    simp only [ip] at fv2 ⊢
    linear_combination fv2
  obtain ⟨c, hcv⟩ := span2_perp v (rs Yf) (rs Yfs) hτv (tau_rs H hH Yf hYf) (tau_rs H hH Yfs hYfs)
    hfs0 hfpos hfs' hss hvf hvs
  apply hvv
  rw [hcv]
  simp only [ip, Pi.smul_apply, smul_eq_mul] at hss ⊢
  linear_combination c ^ 2 * hss

theorem LAG_core (a b : V4) (l μ : ℂ) (ha0 : a ≠ 0) (h1 : tau a = 0) (h2 : ip a a = 0)
    (h3 : tau b = 1) (hl : ∀ i, a i * (2 * b i - 1 - 2 * l * a i) = 0)
    (hmu : ∀ i, b i * (b i - 1) = μ * a i ^ 2) : False := by
  simp only [tau, ip] at h1 h2 h3
  have hb : ∀ i, a i ≠ 0 → 2 * b i - 1 - 2 * l * a i = 0 :=
    fun i hi => (mul_eq_zero.mp (hl i)).resolve_left hi
  have hz : ∀ i, a i = 0 → b i * (b i - 1) = 0 := by
    intro i hi
    rw [hmu i, hi]
    ring
  by_cases c0 : a 0 = 0 <;> by_cases c1 : a 1 = 0 <;> by_cases c2 : a 2 = 0 <;>
    by_cases c3 : a 3 = 0
  · apply ha0
    funext i
    fin_cases i
    · exact c0
    · exact c1
    · exact c2
    · exact c3
  · exact c3 (by linear_combination h1 - c0 - c1 - c2)
  · exact c2 (by linear_combination h1 - c0 - c1 - c3)
  · exact c3 ((pow_eq_zero_iff (n := 2) (by norm_num)).mp (by linear_combination (1 / 2 : ℂ) * (h2 - (a 2 - a 3) * h1 - (a 0 - a 2 + a 3) * c0 - (a 1 - a 2 + a 3) * c1)))
  · exact c1 (by linear_combination h1 - c0 - c2 - c3)
  · exact c3 ((pow_eq_zero_iff (n := 2) (by norm_num)).mp (by linear_combination (1 / 2 : ℂ) * (h2 - (a 1 - a 3) * h1 - (a 0 - a 1 + a 3) * c0 - (a 2 - a 1 + a 3) * c2)))
  · exact c2 ((pow_eq_zero_iff (n := 2) (by norm_num)).mp (by linear_combination (1 / 2 : ℂ) * (h2 - (a 1 - a 2) * h1 - (a 0 - a 1 + a 2) * c0 - (a 3 - a 1 + a 2) * c3)))
  · have h : (3 : ℂ) / 4 = 0 := by
      linear_combination hz 0 c0 - (b 0 - 3 / 2) * (h3 - (1 / 2 : ℂ) * (hb 1 c1 + hb 2 c2 + hb 3 c3) - l * h1 + l * c0)
    norm_num at h
  · exact c0 (by linear_combination h1 - c1 - c2 - c3)
  · exact c3 ((pow_eq_zero_iff (n := 2) (by norm_num)).mp (by linear_combination (1 / 2 : ℂ) * (h2 - (a 0 - a 3) * h1 - (a 1 - a 0 + a 3) * c1 - (a 2 - a 0 + a 3) * c2)))
  · exact c2 ((pow_eq_zero_iff (n := 2) (by norm_num)).mp (by linear_combination (1 / 2 : ℂ) * (h2 - (a 0 - a 2) * h1 - (a 1 - a 0 + a 2) * c1 - (a 3 - a 0 + a 2) * c3)))
  · have h : (3 : ℂ) / 4 = 0 := by
      linear_combination hz 1 c1 - (b 1 - 3 / 2) * (h3 - (1 / 2 : ℂ) * (hb 0 c0 + hb 2 c2 + hb 3 c3) - l * h1 + l * c1)
    norm_num at h
  · exact c1 ((pow_eq_zero_iff (n := 2) (by norm_num)).mp (by linear_combination (1 / 2 : ℂ) * (h2 - (a 0 - a 1) * h1 - (a 2 - a 0 + a 1) * c2 - (a 3 - a 0 + a 1) * c3)))
  · have h : (3 : ℂ) / 4 = 0 := by
      linear_combination hz 2 c2 - (b 2 - 3 / 2) * (h3 - (1 / 2 : ℂ) * (hb 0 c0 + hb 1 c1 + hb 3 c3) - l * h1 + l * c2)
    norm_num at h
  · have h : (3 : ℂ) / 4 = 0 := by
      linear_combination hz 3 c3 - (b 3 - 3 / 2) * (h3 - (1 / 2 : ℂ) * (hb 0 c0 + hb 1 c1 + hb 2 c2) - l * h1 + l * c3)
    norm_num at h
  · have h : (1 : ℂ) = 0 := by
      linear_combination h3 - l * h1 - (1 / 2 : ℂ) * (hb 0 c0 + hb 1 c1 + hb 2 c2 + hb 3 c3)
    norm_num at h

theorem tau_Ed (z : V4) : tau (Ed z) = 2 * e2 z := by
  simp only [tau, Ed, e2, ip]
  ring

theorem tau_Edb (z w : V4) : tau (Edb z w) = 2 * e2b z w := by
  simp only [tau, Edb, e2b, ip]
  ring

theorem perp2 (u w : V4) (hu : u ≠ 0) (hw : ∀ c : ℂ, w ≠ c • u) (hτu : tau u = 0)
    (hτw : tau w = 0) (P : Submodule ℂ V4) (hP : ∀ p ∈ P, tau p = 0)
    (hPu : ∀ p ∈ P, ip p u = 0) (hPw : ∀ p ∈ P, ip p w = 0) : Module.finrank ℂ P ≤ 1 := by
  have hW1 : Module.finrank ℂ (Submodule.span ℂ {u}) = 1 := finrank_span_singleton hu
  have hlt : Submodule.span ℂ {u} < Submodule.span ℂ {u, w} := by
    refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
    intro h
    have hw' : w ∈ Submodule.span ℂ {u} := by
      rw [h]
      exact Submodule.subset_span (by simp)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw'
    exact hw c hc.symm
  have hW2 : 2 ≤ Module.finrank ℂ (Submodule.span ℂ {u, w}) := by
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hperp := perp_sup_one P (Submodule.span ℂ {u, w}) hP
    (by
      intro q hq
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hq
      simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hτu hτw ⊢
      linear_combination s * hτu + t * hτw)
    (by
      intro p hp q hq
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hq
      have a := hPu p hp
      have b := hPw p hp
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
      linear_combination s * a + t * b)
  omega

theorem LAG_a (z0 z1 : V4) (hz0 : z0 ≠ 0) (h0 : tau z0 = 0) (h00 : e2 z0 = 0) (h1 : tau z1 = 1)
    (h11 : e2 z1 = 0) (h01 : e2b z0 z1 = 0) (P : Submodule ℂ V4) (hP : ∀ p ∈ P, tau p = 0)
    (hPE : ∀ p ∈ P, ip p (Ed z0) = 0 ∧ ip p (Edb z0 z1) = 0 ∧ ip p (Ed z1) = 0) :
    Module.finrank ℂ P ≤ 1 := by
  have hE0 : ∀ k, Ed z0 k = z0 k ^ 2 := by
    intro k
    simp only [Ed]
    rw [h00, h0]
    ring
  have hE01 : ∀ k, Edb z0 z1 k = z0 k * (z1 k - 1 / 2) := by
    intro k
    simp only [Edb]
    rw [h01, h0, h1]
    ring
  have hE1 : ∀ k, Ed z1 k = z1 k * (z1 k - 1) := by
    intro k
    simp only [Ed]
    rw [h11, h1]
    ring
  have hip : ip z0 z0 = 0 := by
    simp only [e2] at h00
    rw [h0] at h00
    linear_combination -2 * h00
  obtain ⟨i0, hi0'⟩ := Function.ne_iff.mp hz0
  have hi0 : z0 i0 ≠ 0 := hi0'
  have hE0ne : Ed z0 ≠ 0 := by
    intro h
    have e := congrFun h i0
    rw [hE0 i0] at e
    exact hi0 ((pow_eq_zero_iff (by norm_num)).mp e)
  have hτ0 : tau (Ed z0) = 0 := by rw [tau_Ed, h00, mul_zero]
  have hτ01 : tau (Edb z0 z1) = 0 := by rw [tau_Edb, h01, mul_zero]
  have hτ1 : tau (Ed z1) = 0 := by rw [tau_Ed, h11, mul_zero]
  by_cases hA : ∃ c : ℂ, Edb z0 z1 = c • Ed z0
  · obtain ⟨lam, hlam⟩ := hA
    have hB : ∀ c : ℂ, Ed z1 ≠ c • Ed z0 := by
      intro μ hμ
      apply LAG_core z0 z1 lam μ hz0 h0 hip h1
      · intro k
        have e := congrFun hlam k
        simp only [Pi.smul_apply, smul_eq_mul] at e
        rw [hE01 k, hE0 k] at e
        linear_combination 2 * e
      · intro k
        have e := congrFun hμ k
        simp only [Pi.smul_apply, smul_eq_mul] at e
        rw [hE1 k, hE0 k] at e
        exact e
    exact perp2 (Ed z0) (Ed z1) hE0ne hB hτ0 hτ1 P hP (fun p hp => (hPE p hp).1)
      (fun p hp => (hPE p hp).2.2)
  · push_neg at hA
    exact perp2 (Ed z0) (Edb z0 z1) hE0ne hA hτ0 hτ01 P hP (fun p hp => (hPE p hp).1)
      (fun p hp => (hPE p hp).2.1)

theorem LAG_b (n : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, n i ^ 4 = kap) (hn1 : tau n = 0)
    (hn2 : ip n n = 0) (hn3 : t3 n n n = 0) (z0 z1 : V4) (hz0 : z0 ≠ 0) (h0 : tau z0 = 0)
    (h00 : e2 z0 = 0) (h1 : tau z1 = 1) (h11 : e2 z1 = 0) (h01 : e2b z0 z1 = 0) :
    ¬ (ip n (Ed z0) = 0 ∧ ip n (Edb z0 z1) = 0) := by
  rintro ⟨hA, hB⟩
  obtain ⟨p, q, r, hz0q⟩ := Qv_V n kap hkap hk hn1 hn2 hn3 z0 h0
  obtain ⟨a0, a1, a2, a3, hz1q⟩ := Qv_exists n kap hkap hk hn1 hn2 hn3 z1
  have hnq : n = Qv n 0 1 0 0 := by
    funext i
    simp only [Qv]
    ring
  have hipn : ∀ c0 c1 c2 c3 : ℂ,
      ip n (Qv n c0 c1 c2 c3) = 4 * (0 * c0 + kap * (1 * c3 + 0 * c2 + 0 * c1)) := by
    intro c0 c1 c2 c3
    calc ip n (Qv n c0 c1 c2 c3) = ip (Qv n 0 1 0 0) (Qv n c0 c1 c2 c3) := by rw [← hnq]
      _ = 4 * (0 * c0 + kap * (1 * c3 + 0 * c2 + 0 * c1)) :=
        ip_Qv n kap hk hn1 hn2 hn3 0 1 0 0 c0 c1 c2 c3
  have hip0 : ip z0 z0 = 0 := by
    simp only [e2] at h00
    rw [h0] at h00
    linear_combination -2 * h00
  have hip01 : ip z0 z1 = 0 := by
    simp only [e2b] at h01
    rw [h0] at h01
    linear_combination -2 * h01
  have hip11 : ip z1 z1 = 1 := by
    simp only [e2] at h11
    rw [h1] at h11
    linear_combination -2 * h11
  rw [hz0q, ip_Qv n kap hk hn1 hn2 hn3] at hip0
  rw [hz0q, hz1q, ip_Qv n kap hk hn1 hn2 hn3] at hip01
  rw [hz1q, ip_Qv n kap hk hn1 hn2 hn3] at hip11
  rw [hz1q, tau_Qv n hn1 hn2 hn3] at h1
  have hE0 : Ed z0 = fun k => z0 k * z0 k := by
    funext k
    simp only [Ed]
    rw [h00, h0]
    ring
  have hE01 : Edb z0 z1 = fun k => z0 k * Qv n (a0 - 1 / 2) a1 a2 a3 k := by
    funext k
    simp only [Edb]
    rw [h01, h0]
    have h1' : tau z1 = 1 := by
      rw [hz1q, tau_Qv n hn1 hn2 hn3]
      exact h1
    rw [h1', hz1q]
    simp only [Qv]
    ring
  rw [hE0, hz0q, Qv_mul n kap hk, hipn] at hA
  rw [hE01, hz0q, Qv_mul n kap hk, hipn] at hB
  have hpq : p * q = 0 := by
    have h : kap * (p * q) = 0 := by linear_combination (1 / 8 : ℂ) * hA
    exact (mul_eq_zero.mp h).resolve_left hkap
  have ha0 : a0 = 1 / 4 := by linear_combination (1 / 4 : ℂ) * h1
  rcases mul_eq_zero.mp hpq with hp | hq
  · have hq : q = 0 := by
      have h : kap * (q * q) = 0 := by
        rw [hp] at hip0
        linear_combination (1 / 4 : ℂ) * hip0
      exact mul_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hkap)
    have hr : r = 0 := by
      rw [hp, hq, ha0] at hB
      have h : kap * r = 0 := by linear_combination (-1 : ℂ) * hB
      exact (mul_eq_zero.mp h).resolve_left hkap
    apply hz0
    rw [hz0q, hp, hq, hr]
    funext i
    simp [Qv]
  · have hr : p * r = 0 := by
      have h : kap * (p * r) = 0 := by
        rw [hq] at hip0
        linear_combination (1 / 8 : ℂ) * hip0
      exact (mul_eq_zero.mp h).resolve_left hkap
    rcases mul_eq_zero.mp hr with hp | hr0
    · have hr1 : r = 0 := by
        rw [hp, hq, ha0] at hB
        have h : kap * r = 0 := by linear_combination (-1 : ℂ) * hB
        exact (mul_eq_zero.mp h).resolve_left hkap
      apply hz0
      rw [hz0q, hp, hq, hr1]
      funext i
      simp [Qv]
    · have hp0 : p ≠ 0 := by
        intro hp
        apply hz0
        rw [hz0q, hp, hq, hr0]
        funext i
        simp [Qv]
      have ha2 : a2 = 0 := by
        rw [hq, hr0] at hB
        have h : (kap * p) * a2 = 0 := by linear_combination (1 / 4 : ℂ) * hB
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hkap hp0)
      have ha3 : a3 = 0 := by
        rw [hq, hr0] at hip01
        have h : (kap * p) * a3 = 0 := by linear_combination (1 / 4 : ℂ) * hip01
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hkap hp0)
      rw [ha0, ha2, ha3] at hip11
      norm_num at hip11

theorem neutral_pol (K : Submodule ℂ M45) (j : Fin 5)
    (hqb : ∀ Y ∈ K, ip (col Y j) (col Y j) = ip (rs Y) (col Y j)) (Y : M45) (hY : Y ∈ K)
    (Y' : M45) (hY' : Y' ∈ K) :
    2 * ip (col Y j) (col Y' j) = ip (rs Y) (col Y' j) + ip (rs Y') (col Y j) := by
  have e1 := hqb Y hY
  have e2 := hqb Y' hY'
  have e3 := hqb (Y + Y') (K.add_mem hY hY')
  rw [map_add] at e3
  simp only [ip, col, Pi.add_apply] at e1 e2 e3 ⊢
  linear_combination e3 - e1 - e2

theorem neutral_iso (K : Submodule ℂ M45) (j : Fin 5)
    (hqb : ∀ Y ∈ K, ip (col Y j) (col Y j) = ip (rs Y) (col Y j)) (Y : M45) (hY : Y ∈ K)
    (Y' : M45) (hY' : Y' ∈ K) : ip (phi j Y) (phi j Y') = ip (rs Y) (rs Y') := by
  have e := neutral_pol K j hqb Y hY Y' hY'
  simp only [ip, col] at e
  simp only [ip, phi_apply]
  linear_combination 2 * e

theorem neutral_perp (K : Submodule ℂ M45) (j : Fin 5)
    (hqb : ∀ Y ∈ K, ip (col Y j) (col Y j) = ip (rs Y) (col Y j)) (Z : M45) (hZ : Z ∈ K)
    (hZ0 : rs Z = 0) (Y : M45) (hY : Y ∈ K) : ip (col Z j) (phi j Y) = 0 := by
  have e := neutral_pol K j hqb Z hZ Y hY
  rw [hZ0] at e
  simp only [ip, col, Pi.zero_apply] at e
  simp only [ip, col, phi_apply]
  linear_combination e

theorem neutral_zero (K : Submodule ℂ M45) (j : Fin 5)
    (hqb : ∀ Y ∈ K, ip (col Y j) (col Y j) = ip (rs Y) (col Y j))
    (hτj : ∀ Y ∈ K, tau (col Y j) = 0) (hτs : ∀ Y ∈ K, tau (rs Y) = 0)
    (hq : Module.finrank ℂ (K.map rs) = 3) (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    col Z j = 0 := by
  have hV3 : Module.finrank ℂ (sumZero 4) ≤ 3 :=
    (finrank_sumZero (n := 4) (by norm_num)).trans (by norm_num)
  have hS : K.map rs ≤ sumZero 4 := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [mem_Vs]
    exact hτs Y hY
  have hSV : K.map rs = sumZero 4 :=
    Submodule.eq_of_le_of_finrank_le hS (le_trans hV3 (le_of_eq hq.symm))
  have hle : K.map (phi j) ≤ sumZero 4 := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [mem_Vs]
    have h1 := hτj Y hY
    have h2 := hτs Y hY
    simp only [tau, col] at h1 h2
    simp only [tau, phi_apply]
    linear_combination 2 * h1 - h2
  have hker : (K ⊓ LinearMap.ker (phi j) : Submodule ℂ M45) ≤ K ⊓ LinearMap.ker rs := by
    rintro Y ⟨hY, hY0⟩
    refine ⟨hY, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hY0 ⊢
    apply nondeg
    · exact hτs Y hY
    · intro v hv
      have hv' : v ∈ K.map rs := by
        rw [hSV, mem_Vs]
        exact hv
      obtain ⟨Y', hY', rfl⟩ := hv'
      rw [← neutral_iso K j hqb Y hY Y' hY', hY0]
      simp [ip]
  have r1 := rank_nullity K (phi j)
  have r2 := rank_nullity K rs
  have r3 := Submodule.finrank_mono hker
  have hP3 : 3 ≤ Module.finrank ℂ (K.map (phi j)) := by omega
  have hphi : K.map (phi j) = sumZero 4 := Submodule.eq_of_le_of_finrank_le hle (le_trans hV3 hP3)
  apply nondeg
  · exact hτj Z hZ
  · intro v hv
    have hv' : v ∈ K.map (phi j) := by
      rw [hphi, mem_Vs]
      exact hv
    obtain ⟨Y, hY, rfl⟩ := hv'
    exact neutral_perp K j hqb Z hZ hZ0 Y hY

theorem iso_perp_plane (t1 t2 w : V4) (h1 : tau t1 = 0) (h2 : tau t2 = 0) (hw : tau w = 0)
    (hD : ip t1 t1 * ip t2 t2 - ip t1 t2 ^ 2 ≠ 0) (hw1 : ip w t1 = 0) (hw2 : ip w t2 = 0)
    (hww : ip w w = 0) : w = 0 := by
  by_contra hw0
  have hA : Module.finrank ℂ (Submodule.span ℂ {w}) = 1 := finrank_span_singleton hw0
  have hAB : Submodule.span ℂ {w} < Submodule.span ℂ {t2, w} := by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert t2 {w})) ?_
    intro h
    have ht : t2 ∈ Submodule.span ℂ {w} := by
      rw [h]
      exact Submodule.subset_span (Set.mem_insert t2 {w})
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ht
    apply hD
    have e1 : ip t2 t2 = c ^ 2 * ip w w := by
      rw [← hc]
      simp only [ip, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ip t1 t2 = c * ip w t1 := by
      rw [← hc]
      simp only [ip, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2, hww, hw1]
    ring
  have hBC : Submodule.span ℂ {t2, w} < Submodule.span ℂ {t1, t2, w} := by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert t1 {t2, w})) ?_
    intro h
    have ht : t1 ∈ Submodule.span ℂ {t2, w} := by
      rw [h]
      exact Submodule.subset_span (Set.mem_insert t1 {t2, w})
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp ht
    apply hD
    have e1 : ip t1 t1 = a ^ 2 * ip t2 t2 + 2 * a * b * ip w t2 + b ^ 2 * ip w w := by
      rw [← hab]
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ip t1 t2 = a * ip t2 t2 + b * ip w t2 := by
      rw [← hab]
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2, hw2, hww]
    ring
  have hB := Submodule.finrank_lt_finrank_of_lt hAB
  have hC := Submodule.finrank_lt_finrank_of_lt hBC
  have hperp := perp_sup_one (Submodule.span ℂ {w}) (Submodule.span ℂ {t1, t2, w})
    (by
      intro p hp
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
      simp only [tau, Pi.smul_apply, smul_eq_mul] at hw ⊢
      linear_combination c * hw)
    (by
      intro q hq
      obtain ⟨a, q', hq', rfl⟩ := Submodule.mem_span_insert.mp hq
      obtain ⟨b, d, rfl⟩ := Submodule.mem_span_pair.mp hq'
      simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 hw ⊢
      linear_combination a * h1 + b * h2 + d * hw)
    (by
      intro p hp q hq
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
      obtain ⟨a, q', hq', rfl⟩ := Submodule.mem_span_insert.mp hq
      obtain ⟨b, d, rfl⟩ := Submodule.mem_span_pair.mp hq'
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hw1 hw2 hww ⊢
      linear_combination c * a * hw1 + c * b * hw2 + c * d * hww)
  omega

theorem neutral_zero2 (K : Submodule ℂ M45) (j : Fin 5)
    (hqb : ∀ Y ∈ K, ip (col Y j) (col Y j) = ip (rs Y) (col Y j))
    (hτj : ∀ Y ∈ K, tau (col Y j) = 0) (hτs : ∀ Y ∈ K, tau (rs Y) = 0)
    (Y1 : M45) (hY1 : Y1 ∈ K) (Y2 : M45) (hY2 : Y2 ∈ K)
    (hD : ip (rs Y1) (rs Y1) * ip (rs Y2) (rs Y2) - ip (rs Y1) (rs Y2) ^ 2 ≠ 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) : col Z j = 0 := by
  have htp : ∀ Y ∈ K, tau (phi j Y) = 0 := by
    intro Y hY
    have h1 := hτj Y hY
    have h2 := hτs Y hY
    simp only [tau, col] at h1 h2
    simp only [tau, phi_apply]
    linear_combination 2 * h1 - h2
  apply iso_perp_plane (phi j Y1) (phi j Y2) (col Z j) (htp Y1 hY1) (htp Y2 hY2) (hτj Z hZ)
  · rw [neutral_iso K j hqb Y1 hY1 Y1 hY1, neutral_iso K j hqb Y2 hY2 Y2 hY2,
      neutral_iso K j hqb Y1 hY1 Y2 hY2]
    exact hD
  · exact neutral_perp K j hqb Z hZ hZ0 Y1 hY1
  · exact neutral_perp K j hqb Z hZ hZ0 Y2 hY2
  · rw [hqb Z hZ, hZ0]
    simp [ip]

theorem mTC_vals : mTC 0 = 1 ∧ mTC 1 = -1 ∧ mTC 2 = 0 ∧ mTC 3 = 0 ∧ mTC 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [mTC]

theorem mTC_sum : ∑ a, mTC a = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := mTC_vals
  rw [Fin.sum_univ_five]
  linear_combination h0 + h1 + h2 + h3 + h4

theorem mTC_ne : mTC ≠ 0 := by
  intro h
  have e := congrFun h 0
  rw [mTC_vals.1] at e
  norm_num at e

theorem TC5_tau (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Y : M45) (hY : Y ∈ K) :
    tau (uY Y) = 0 ∧ tau (col Y 2) = 0 ∧ tau (col Y 3) = 0 ∧ tau (col Y 4) = 0 ∧
      tau (rs Y) = 0 := by
  obtain ⟨κ, θ, hc, -⟩ := QBc_of K mTC hdef mTC_sum mTC_ne Y hY
  obtain ⟨m0, m1, m2, m3, m4⟩ := mTC_vals
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  rw [m0] at h0
  rw [m1] at h1
  rw [m2, mul_zero] at h2
  rw [m3, mul_zero] at h3
  rw [m4, mul_zero] at h4
  refine ⟨?_, h2, h3, h4, ?_⟩
  · simp only [tau, col] at h0 h1
    simp only [tau, uY]
    linear_combination (1 / 2 : ℂ) * (h0 + h1)
  · simp only [tau, col] at h0 h1 h2 h3 h4
    simp only [tau, rs_apply]
    linear_combination h0 + h1 + h2 + h3 + h4

theorem NB_qbar (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Y : M45) (hY : Y ∈ K) :
    ip (col Y 2) (col Y 2) = ip (rs Y) (col Y 2) ∧ ip (col Y 3) (col Y 3) = ip (rs Y) (col Y 3) ∧
      ip (col Y 4) (col Y 4) = ip (rs Y) (col Y 4) := by
  obtain ⟨tu, t2, t3', t4, -⟩ := TC5_tau K hdef Y hY
  obtain ⟨⟨a34, a24, a23⟩, -, -⟩ := TC5_degree K hdef Y hY
  obtain ⟨-, bI, -, -⟩ := TC5_deg_i K hdef Y hY
  simp only [X2c, tu, t2, t3', t4, mul_zero, zero_mul, add_zero] at a34 a24 a23 bI
  simp only [ip, uY, col, rs_apply] at a34 a24 a23 bI ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 / 3 : ℂ) * a34 + (1 / 6 : ℂ) * a24 + (1 / 6 : ℂ) * a23
      + (1 / 3 : ℂ) * bI
  · linear_combination (1 / 6 : ℂ) * a34 - (1 / 3 : ℂ) * a24 + (1 / 6 : ℂ) * a23
      + (1 / 3 : ℂ) * bI
  · linear_combination (1 / 6 : ℂ) * a34 + (1 / 6 : ℂ) * a24 - (1 / 3 : ℂ) * a23
      + (1 / 3 : ℂ) * bI

theorem NB3 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hq : Module.finrank ℂ (K.map rs) = 3)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    col Z 2 = 0 ∧ col Z 3 = 0 ∧ col Z 4 = 0 ∧ uY Z = 0 := by
  have hτs : ∀ Y ∈ K, tau (rs Y) = 0 := fun Y hY => (TC5_tau K hdef Y hY).2.2.2.2
  have z2 := neutral_zero K 2 (fun Y hY => (NB_qbar K hdef Y hY).1)
    (fun Y hY => (TC5_tau K hdef Y hY).2.1) hτs hq Z hZ hZ0
  have z3 := neutral_zero K 3 (fun Y hY => (NB_qbar K hdef Y hY).2.1)
    (fun Y hY => (TC5_tau K hdef Y hY).2.2.1) hτs hq Z hZ hZ0
  have z4 := neutral_zero K 4 (fun Y hY => (NB_qbar K hdef Y hY).2.2)
    (fun Y hY => (TC5_tau K hdef Y hY).2.2.2.1) hτs hq Z hZ hZ0
  refine ⟨z2, z3, z4, ?_⟩
  funext i
  have h := congrFun hZ0 i
  rw [rs_apply] at h
  have w2 : Z (i, 2) = 0 := congrFun z2 i
  have w3 : Z (i, 3) = 0 := congrFun z3 i
  have w4 : Z (i, 4) = 0 := congrFun z4 i
  have h' : Z (i, 0) + Z (i, 1) + Z (i, 2) + Z (i, 3) + Z (i, 4) = 0 := h
  show (Z (i, 0) + Z (i, 1)) / 2 = 0
  linear_combination (1 / 2 : ℂ) * (h' - w2 - w3 - w4)

theorem NB_plane (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Y1 : M45) (hY1 : Y1 ∈ K)
    (Y2 : M45) (hY2 : Y2 ∈ K)
    (hD : ip (rs Y1) (rs Y1) * ip (rs Y2) (rs Y2) - ip (rs Y1) (rs Y2) ^ 2 ≠ 0)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) :
    col Z 2 = 0 ∧ col Z 3 = 0 ∧ col Z 4 = 0 ∧ uY Z = 0 := by
  have hτs : ∀ Y ∈ K, tau (rs Y) = 0 := fun Y hY => (TC5_tau K hdef Y hY).2.2.2.2
  have z2 := neutral_zero2 K 2 (fun Y hY => (NB_qbar K hdef Y hY).1)
    (fun Y hY => (TC5_tau K hdef Y hY).2.1) hτs Y1 hY1 Y2 hY2 hD Z hZ hZ0
  have z3 := neutral_zero2 K 3 (fun Y hY => (NB_qbar K hdef Y hY).2.1)
    (fun Y hY => (TC5_tau K hdef Y hY).2.2.1) hτs Y1 hY1 Y2 hY2 hD Z hZ hZ0
  have z4 := neutral_zero2 K 4 (fun Y hY => (NB_qbar K hdef Y hY).2.2)
    (fun Y hY => (TC5_tau K hdef Y hY).2.2.2.1) hτs Y1 hY1 Y2 hY2 hD Z hZ hZ0
  refine ⟨z2, z3, z4, ?_⟩
  funext i
  have h := congrFun hZ0 i
  rw [rs_apply] at h
  have w2 : Z (i, 2) = 0 := congrFun z2 i
  have w3 : Z (i, 3) = 0 := congrFun z3 i
  have w4 : Z (i, 4) = 0 := congrFun z4 i
  have h' : Z (i, 0) + Z (i, 1) + Z (i, 2) + Z (i, 3) + Z (i, 4) = 0 := h
  show (Z (i, 0) + Z (i, 1)) / 2 = 0
  linear_combination (1 / 2 : ℂ) * (h' - w2 - w3 - w4)

theorem TC5_qbar1 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Y : M45) (hY : Y ∈ K) :
    ip (uY Y) (uY Y) - ip (rs Y) (uY Y) = 2 * e2 (dY Y) := by
  obtain ⟨tu, t2, t3', t4, -⟩ := TC5_tau K hdef Y hY
  obtain ⟨⟨a34, a24, a23⟩, -, -⟩ := TC5_degree K hdef Y hY
  obtain ⟨-, bI, -, -⟩ := TC5_deg_i K hdef Y hY
  simp only [X2c, tu, t2, t3', t4, mul_zero, zero_mul, add_zero] at a34 a24 a23 bI
  simp only [ip, uY, col, rs_apply] at a34 a24 a23 bI ⊢
  linear_combination (1 / 6 : ℂ) * a34 + (1 / 6 : ℂ) * a24 + (1 / 6 : ℂ) * a23
    - (1 / 6 : ℂ) * bI

theorem zE_smul (c : ℂ) (z : V4) : zE (c • z) = c • zE z := by
  funext p
  obtain ⟨k, j⟩ := p
  simp only [zE, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem dY_zE (z : V4) : dY (zE z) = z := by
  funext k
  simp only [dY, zE0, zE1]
  ring

theorem e2_ip (z : V4) (h : tau z = 0) (h2 : e2 z = 0) : ip z z = 0 := by
  simp only [e2] at h2
  rw [h] at h2
  linear_combination -2 * h2

theorem LAG_line (z0 z1 : V4) (hz0 : z0 ≠ 0) (h0 : tau z0 = 0) (h00 : e2 z0 = 0) (h1 : tau z1 = 1)
    (h11 : e2 z1 = 0) (h01 : e2b z0 z1 = 0) :
    ∃ n : V4, tau n = 0 ∧ ip n (Ed z0) = 0 ∧ ip n (Edb z0 z1) = 0 ∧ ip n (Ed z1) = 0 ∧
      ∀ x : V4, tau x = 0 → ip x (Ed z0) = 0 → ip x (Edb z0 z1) = 0 →
      ip x (Ed z1) = 0 → ∃ c : ℂ, x = c • n := by
  by_cases hex : ∃ x0 : V4, x0 ≠ 0 ∧ tau x0 = 0 ∧ ip x0 (Ed z0) = 0 ∧ ip x0 (Edb z0 z1) = 0 ∧
      ip x0 (Ed z1) = 0
  · obtain ⟨x0, hx0, a1, a2, a3, a4⟩ := hex
    refine ⟨x0, a1, a2, a3, a4, ?_⟩
    intro x b1 b2 b3 b4
    by_contra hne
    push_neg at hne
    have hW1 : Module.finrank ℂ (Submodule.span ℂ {x0}) = 1 := finrank_span_singleton hx0
    have hlt : Submodule.span ℂ {x0} < Submodule.span ℂ {x0, x} := by
      refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
      intro h
      have hx' : x ∈ Submodule.span ℂ {x0} := by
        rw [h]
        exact Submodule.subset_span (by simp)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx'
      exact hne c hc.symm
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    have hle := LAG_a z0 z1 hz0 h0 h00 h1 h11 h01 (Submodule.span ℂ {x0, x})
      (by
        intro p hp
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hp
        simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a1 b1 ⊢
        linear_combination s * a1 + t * b1)
      (by
        intro p hp
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hp
        have e : ∀ q : V4, ip (s • x0 + t • x) q = s * ip x0 q + t * ip x q := by
          intro q
          simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, e, e, a2, a3, a4, b2, b3, b4]
        simp)
    omega
  · push_neg at hex
    refine ⟨0, by simp [tau], by simp [ip], by simp [ip], by simp [ip], ?_⟩
    intro x b1 b2 b3 b4
    refine ⟨0, ?_⟩
    rw [zero_smul]
    by_contra hx
    exact hex x hx b1 b2 b3 b4

theorem zeta_span (z0 z1 d : V4) (hz0 : z0 ≠ 0) (h0 : tau z0 = 0) (h1 : tau z1 = 1)
    (h00 : e2 z0 = 0) (h11 : e2 z1 = 0) (h01 : e2b z0 z1 = 0) (hd0 : e2b d z0 = 0)
    (hd1 : e2b d z1 = 0) : ∃ a b : ℂ, d = a • z0 + b • z1 := by
  have hT0 : tau z0 = z0 0 + z0 1 + z0 2 + z0 3 := rfl
  have hT1 : tau z1 = z1 0 + z1 1 + z1 2 + z1 3 := rfl
  have hTd : tau d = d 0 + d 1 + d 2 + d 3 := rfl
  simp only [e2, e2b, ip] at h00 h11 h01 hd0 hd1
  have hff : ip (fun k => z1 k - 1 / 4) (fun k => z1 k - 1 / 4) = 3 / 4 := by
    simp only [ip]
    linear_combination (-2 : ℂ) * h11 + (tau z1 + 1) * h1 + (1 / 2 : ℂ) * hT1 - (1 / 2 : ℂ) * h1
  obtain ⟨c, hc⟩ := span2_perp (fun k => d k - tau d * z1 k) (fun k => z1 k - 1 / 4) z0
    (by
      show (d 0 - tau d * z1 0) + (d 1 - tau d * z1 1) + (d 2 - tau d * z1 2)
        + (d 3 - tau d * z1 3) = 0
      linear_combination (-1 : ℂ) * hTd + tau d * hT1 - tau d * h1)
    (by
      show (z1 0 - 1 / 4) + (z1 1 - 1 / 4) + (z1 2 - 1 / 4) + (z1 3 - 1 / 4) = 0
      linear_combination h1 - hT1)
    h0 hz0
    (by
      rw [hff]
      norm_num)
    (by
      simp only [ip]
      linear_combination (-2 : ℂ) * h01 + tau z1 * h0 + (1 / 4 : ℂ) * hT0 - (1 / 4 : ℂ) * h0)
    (by
      simp only [ip]
      linear_combination (-2 : ℂ) * h00 + tau z0 * h0)
    (by
      simp only [ip]
      linear_combination (-2 : ℂ) * hd1 + (1 / 4 : ℂ) * hTd + 2 * tau d * h11
        - tau d / 4 * hT1 + tau d * (1 / 4 - tau z1) * h1)
    (by
      simp only [ip]
      linear_combination (-2 : ℂ) * hd0 + 2 * tau d * h01 + tau d * (1 - tau z1) * h0)
  refine ⟨c, tau d, ?_⟩
  funext k
  have e := congrFun hc k
  simp only [Pi.smul_apply, smul_eq_mul] at e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination e

theorem P1_D (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z0 z1 : V4) (hz0K : zE z0 ∈ K)
    (hz1K : zE z1 ∈ K) (hz0 : z0 ≠ 0) (h0 : tau z0 = 0) (h1 : tau z1 = 1) (Y : M45)
    (hY : Y ∈ K) : ∃ a b : ℂ, dY Y = a • z0 + b • z1 := by
  obtain ⟨h00, hd0, -⟩ := LemmaZ K hdef z0 hz0K Y hY
  obtain ⟨h11, hd1, -⟩ := LemmaZ K hdef z1 hz1K Y hY
  obtain ⟨-, h01, -⟩ := LemmaZ K hdef z1 hz1K (zE z0) hz0K
  rw [dY_zE] at h01
  exact zeta_span z0 z1 (dY Y) hz0 h0 h1 h00 h11 h01 hd0 hd1

theorem P1_line (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z0 z1 : V4) (hz0K : zE z0 ∈ K)
    (hz1K : zE z1 ∈ K) (hz0 : z0 ≠ 0) (h0 : tau z0 = 0) (h1 : tau z1 = 1) :
    ∃ n : V4, tau n = 0 ∧ ip n (Ed z0) = 0 ∧ ip n (Edb z0 z1) = 0 ∧
      ∀ Y ∈ K, (∃ c : ℂ, col Y 2 = c • n) ∧ (∃ c : ℂ, col Y 3 = c • n) ∧
      (∃ c : ℂ, col Y 4 = c • n) := by
  obtain ⟨h00, -⟩ := LemmaZ K hdef z0 hz0K (zE z0) hz0K
  obtain ⟨h11, h01, -⟩ := LemmaZ K hdef z1 hz1K (zE z0) hz0K
  rw [dY_zE] at h01
  obtain ⟨n, hn1, hn2, hn3, -, hn⟩ := LAG_line z0 z1 hz0 h0 h00 h1 h11 h01
  refine ⟨n, hn1, hn2, hn3, fun Y hY => ?_⟩
  obtain ⟨-, -, a2, a3, a4, -⟩ := LemmaZ K hdef z0 hz0K Y hY
  obtain ⟨-, -, b2, b3, b4, -⟩ := LemmaZ K hdef z1 hz1K Y hY
  obtain ⟨c2, c3, c4, -⟩ := LemmaZ_pol K hdef z0 z1 hz0K hz1K Y hY
  obtain ⟨-, t2, t3', t4, -⟩ := TC5_tau K hdef Y hY
  exact ⟨hn _ t2 a2 c2 b2, hn _ t3' a3 c3 b3, hn _ t4 a4 c4 b4⟩

theorem P1_nf (K : Submodule ℂ M45) (hdef : DefLine K mTC) (za zb : V4) (ha : zE za ∈ K)
    (hb : zE zb ∈ K) (hind : ∀ a b : ℂ, a • za + b • zb = 0 → a = 0 ∧ b = 0) :
    ∃ z0 z1 : V4, zE z0 ∈ K ∧ zE z1 ∈ K ∧ z0 ≠ 0 ∧ tau z0 = 0 ∧ tau z1 = 1 ∧
      ∃ a b c d : ℂ, za = a • z0 + b • z1 ∧ zb = c • z0 + d • z1 := by
  have hlin : ∀ (x y : V4) (s t : ℂ), zE x ∈ K → zE y ∈ K → zE (s • x + t • y) ∈ K := by
    intro x y s t hx hy
    rw [zE_add, zE_smul, zE_smul]
    exact K.add_mem (K.smul_mem s hx) (K.smul_mem t hy)
  have htau : ∀ (x y : V4) (s t : ℂ), tau (s • x + t • y) = s * tau x + t * tau y := by
    intro x y s t
    simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  by_cases htb : tau zb = 0
  · by_cases hta : tau za = 0
    · exfalso
      obtain ⟨ea, -⟩ := LemmaZ K hdef za ha 0 K.zero_mem
      obtain ⟨eb, -⟩ := LemmaZ K hdef zb hb 0 K.zero_mem
      have hab : zE (za + zb) ∈ K := by
        rw [zE_add]
        exact K.add_mem ha hb
      obtain ⟨eab, -⟩ := LemmaZ K hdef (za + zb) hab 0 K.zero_mem
      have ia := e2_ip za hta ea
      have ib := e2_ip zb htb eb
      have et : tau (za + zb) = 0 := by
        simp only [tau, Pi.add_apply] at hta htb ⊢
        linear_combination hta + htb
      have iab : ip za zb = 0 := by
        simp only [e2] at eab
        rw [et] at eab
        simp only [ip, Pi.add_apply] at eab ia ib ⊢
        linear_combination (-1 : ℂ) * eab - (1 / 2 : ℂ) * ia - (1 / 2 : ℂ) * ib
      have hza0 : za ≠ 0 := by
        intro h
        have := hind 1 0 (by rw [h]; simp)
        exact one_ne_zero this.1
      obtain ⟨c, hc⟩ := Q4 za zb hza0 hta ia htb ib iab
      have := hind c (-1) (by
        rw [hc]
        funext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        ring)
      exact one_ne_zero (neg_eq_zero.mp this.2)
    · have hτ1 : tau ((tau za)⁻¹ • za) = 1 := by
        have e : tau ((tau za)⁻¹ • za) = (tau za)⁻¹ * tau za := by
          simp only [tau, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        exact inv_mul_cancel₀ hta
      refine ⟨zb, (tau za)⁻¹ • za, ?_, ?_, ?_, htb, hτ1, 0, tau za, 1, 0, ?_, ?_⟩
      · exact hb
      · rw [zE_smul]
        exact K.smul_mem _ ha
      · intro h
        have := hind 0 1 (by rw [h]; simp)
        exact one_ne_zero this.2
      · funext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (-(za k)) * mul_inv_cancel₀ hta
      · funext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
  · have hτ1 : tau ((tau zb)⁻¹ • zb) = 1 := by
      have e : tau ((tau zb)⁻¹ • zb) = (tau zb)⁻¹ * tau zb := by
        simp only [tau, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact inv_mul_cancel₀ htb
    refine ⟨1 • za + (-(tau za / tau zb)) • zb, (tau zb)⁻¹ • zb, hlin za zb _ _ ha hb, ?_, ?_, ?_,
      hτ1, 1, tau za, 0, tau zb, ?_, ?_⟩
    · rw [zE_smul]
      exact K.smul_mem _ hb
    · intro h
      have := hind 1 (-(tau za / tau zb)) h
      exact one_ne_zero this.1
    · rw [htau]
      linear_combination (-(tau za)) * inv_mul_cancel₀ htb
    · funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(zb k)) * mul_inv_cancel₀ htb

def uYL : M45 →ₗ[ℂ] V4 where
  toFun Y := uY Y
  map_add' Y Y' := by
    funext k
    simp only [uY, Pi.add_apply]
    ring
  map_smul' c Y := by
    funext k
    simp only [uY, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem uYL_apply (Y : M45) : uYL Y = uY Y := rfl

def dYL : M45 →ₗ[ℂ] V4 where
  toFun Y := dY Y
  map_add' Y Y' := by
    funext k
    simp only [dY, Pi.add_apply]
    ring
  map_smul' c Y := by
    funext k
    simp only [dY, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem dYL_apply (Y : M45) : dYL Y = dY Y := rfl

def mL (n : V4) : M45 →ₗ[ℂ] ℂ where
  toFun Y := ip (rs Y) n
  map_add' Y Y' := by
    simp only [map_add, ip, Pi.add_apply]
    ring
  map_smul' c Y := by
    simp only [map_smul, ip, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mL_apply (n : V4) (Y : M45) : mL n Y = ip (rs Y) n := rfl

theorem uY_dY_zero (Y : M45) (hu : uY Y = 0) (hd : dY Y = 0) (h2 : col Y 2 = 0)
    (h3 : col Y 3 = 0) (h4 : col Y 4 = 0) : Y = 0 := by
  funext p
  obtain ⟨k, j⟩ := p
  have eu := congrFun hu k
  have ed := congrFun hd k
  simp only [uY, dY, Pi.zero_apply] at eu ed
  fin_cases j
  · show Y (k, 0) = 0
    linear_combination eu + ed
  · show Y (k, 1) = 0
    linear_combination eu - ed
  · show Y (k, 2) = 0
    exact congrFun h2 k
  · show Y (k, 3) = 0
    exact congrFun h3 k
  · show Y (k, 4) = 0
    exact congrFun h4 k

theorem P1_L (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (z0 z1 : V4) (hz0K : zE z0 ∈ K) (hz1K : zE z1 ∈ K) (hz0 : z0 ≠ 0) (h0 : tau z0 = 0)
    (h1 : tau z1 = 1) : 3 ≤ Module.finrank ℂ (K ⊓ LinearMap.ker dYL : Submodule ℂ M45) := by
  have hle : K.map dYL ≤ Submodule.span ℂ (Set.range ![z0, z1]) := by
    rintro _ ⟨Y, hY, rfl⟩
    obtain ⟨a, b, hab⟩ := P1_D K hdef z0 z1 hz0K hz1K hz0 h0 h1 Y hY
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![a, b], ?_⟩
    rw [Fin.sum_univ_two, dYL_apply, hab]
    simp
  have h2 := (Submodule.finrank_mono hle).trans (finrank_range_le_card ![z0, z1])
  have r := rank_nullity K dYL
  simp only [Fintype.card_fin] at h2
  omega

theorem P1_Lfacts (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Y : M45) (hYK : Y ∈ K)
    (hd : dY Y = 0) : ip (uY Y) (uY Y) = ip (rs Y) (uY Y) := by
  have e := TC5_qbar1 K hdef Y hYK
  rw [hd] at e
  have e0 : e2 (0 : V4) = 0 := by simp [e2, tau, ip]
  rw [e0, mul_zero, sub_eq_zero] at e
  exact e

theorem iso_image (L : Submodule ℂ M45) (hτ : ∀ Y ∈ L, tau (uY Y) = 0)
    (huu : ∀ Y ∈ L, ip (uY Y) (uY Y) = 0) : Module.finrank ℂ (L.map uYL) ≤ 1 := by
  apply Q1
  · rintro _ ⟨Y, hY, rfl⟩
    exact hτ Y hY
  · rintro _ ⟨Y, hY, rfl⟩ _ ⟨Y', hY', rfl⟩
    have f1 := huu Y hY
    have f2 := huu Y' hY'
    have f3 := huu (Y + Y') (L.add_mem hY hY')
    rw [uYL_apply, uYL_apply]
    have hadd : uY (Y + Y') = fun k => uY Y k + uY Y' k := by
      funext k
      simp only [uY, Pi.add_apply]
      ring
    rw [hadd] at f3
    simp only [ip] at f1 f2 f3 ⊢
    linear_combination (1 / 2 : ℂ) * (f3 - f1 - f2)

theorem P1_van (K : Submodule ℂ M45) (hdef : DefLine K mTC) (L : Submodule ℂ M45)
    (hLK : ∀ Y ∈ L, Y ∈ K ∧ dY Y = 0) (hL3 : 3 ≤ Module.finrank ℂ L)
    (hv : ∀ Y ∈ L, col Y 2 = 0 ∧ col Y 3 = 0 ∧ col Y 4 = 0) : False := by
  have huu : ∀ Y ∈ L, ip (uY Y) (uY Y) = 0 := by
    intro Y hY
    obtain ⟨hYK, hd⟩ := hLK Y hY
    have e := P1_Lfacts K hdef Y hYK hd
    obtain ⟨c2, c3, c4⟩ := hv Y hY
    have hrs : rs Y = fun k => 2 * uY Y k := by
      funext k
      rw [rs_apply]
      have w2 : Y (k, 2) = 0 := congrFun c2 k
      have w3 : Y (k, 3) = 0 := congrFun c3 k
      have w4 : Y (k, 4) = 0 := congrFun c4 k
      simp only [uY]
      rw [w2, w3, w4]
      ring
    rw [hrs] at e
    simp only [ip] at e ⊢
    linear_combination -e
  have hU := iso_image L (fun Y hY => (TC5_tau K hdef Y (hLK Y hY).1).1) huu
  have hker : (L ⊓ LinearMap.ker uYL : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Y hY
    rw [Submodule.mem_bot]
    have hYL := (Submodule.mem_inf.mp hY).1
    have hu : uY Y = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY).2
    obtain ⟨c2, c3, c4⟩ := hv Y hYL
    exact uY_dY_zero Y hu (hLK Y hYL).2 c2 c3 c4
  have r := rank_nullity L uYL
  rw [hker, finrank_bot] at r
  omega

theorem line_quad (x s n : V4) (h : ∃ c : ℂ, x = c • n) (hq : ip x x = ip s x) :
    ip x n * (ip x n - ip s n) = 0 := by
  obtain ⟨c, rfl⟩ := h
  simp only [ip, Pi.smul_apply, smul_eq_mul] at hq ⊢
  linear_combination (n 0 * n 0 + n 1 * n 1 + n 2 * n 2 + n 3 * n 3) * hq

theorem prod_lin (L : Submodule ℂ M45) (f g : M45 → ℂ) (hf : ∀ Y Y', f (Y + Y') = f Y + f Y')
    (hg : ∀ Y Y', g (Y + Y') = g Y + g Y') (h : ∀ Y ∈ L, f Y * g Y = 0) :
    (∀ Y ∈ L, f Y = 0) ∨ (∀ Y ∈ L, g Y = 0) := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨Y1, hY1, h1⟩, ⟨Y2, hY2, h2⟩⟩ := hc
  have e1 : g Y1 = 0 := (mul_eq_zero.mp (h Y1 hY1)).resolve_left h1
  have e2 : f Y2 = 0 := (mul_eq_zero.mp (h Y2 hY2)).resolve_right h2
  have e3 := h (Y1 + Y2) (L.add_mem hY1 hY2)
  rw [hf, hg, e1, e2, zero_add, add_zero] at e3
  exact mul_ne_zero h1 h2 e3

theorem eps_of (L : Submodule ℂ M45) (j : Fin 5) (n : V4)
    (hq : ∀ Y ∈ L, ip (col Y j) n * (ip (col Y j) n - ip (rs Y) n) = 0) :
    ∃ ε : ℂ, (ε = 0 ∨ ε = 1) ∧ ∀ Y ∈ L, ip (col Y j) n = ε * ip (rs Y) n := by
  have hf : ∀ Y Y' : M45, ip (col (Y + Y') j) n = ip (col Y j) n + ip (col Y' j) n := by
    intro Y Y'
    simp only [ip, col, Pi.add_apply]
    ring
  have hg : ∀ Y Y' : M45, ip (col (Y + Y') j) n - ip (rs (Y + Y')) n =
      (ip (col Y j) n - ip (rs Y) n) + (ip (col Y' j) n - ip (rs Y') n) := by
    intro Y Y'
    rw [map_add]
    simp only [ip, col, Pi.add_apply]
    ring
  rcases prod_lin L (fun Y => ip (col Y j) n) (fun Y => ip (col Y j) n - ip (rs Y) n) hf hg hq
    with h | h
  · exact ⟨0, Or.inl rfl, fun Y hY => by linear_combination h Y hY⟩
  · exact ⟨1, Or.inr rfl, fun Y hY => by linear_combination h Y hY⟩

theorem line_exp (Y : M45) (n : V4) (c2 c3 c4 : ℂ) (h2 : col Y 2 = c2 • n)
    (h3 : col Y 3 = c3 • n) (h4 : col Y 4 = c4 • n) :
    ip (col Y 2) n = c2 * ip n n ∧ ip (col Y 3) n = c3 * ip n n ∧
      ip (col Y 4) n = c4 * ip n n ∧
      ip (rs Y) n = 2 * ip (uY Y) n + (c2 + c3 + c4) * ip n n ∧
      ip (rs Y) (uY Y) = 2 * ip (uY Y) (uY Y) + (c2 + c3 + c4) * ip (uY Y) n := by
  have hrs : rs Y = fun k => 2 * uY Y k + c2 * n k + c3 * n k + c4 * n k := by
    funext k
    rw [rs_apply]
    have g2 := congrFun h2 k
    have g3 := congrFun h3 k
    have g4 := congrFun h4 k
    simp only [col, Pi.smul_apply, smul_eq_mul] at g2 g3 g4
    simp only [uY]
    rw [g2, g3, g4]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h2]
    simp only [ip, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [h3]
    simp only [ip, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [h4]
    simp only [ip, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hrs]
    simp only [ip]
    ring
  · rw [hrs]
    simp only [ip]
    ring

theorem P1_rel (K : Submodule ℂ M45) (hdef : DefLine K mTC) (L : Submodule ℂ M45)
    (hLK : ∀ Y ∈ L, Y ∈ K ∧ dY Y = 0) (n : V4)
    (hline : ∀ Y ∈ K, (∃ c : ℂ, col Y 2 = c • n) ∧ (∃ c : ℂ, col Y 3 = c • n) ∧
      (∃ c : ℂ, col Y 4 = c • n))
    (ε2 ε3 ε4 : ℂ) (hl2 : ∀ Y ∈ L, ip (col Y 2) n = ε2 * ip (rs Y) n)
    (hl3 : ∀ Y ∈ L, ip (col Y 3) n = ε3 * ip (rs Y) n)
    (hl4 : ∀ Y ∈ L, ip (col Y 4) n = ε4 * ip (rs Y) n) (Y : M45) (hY : Y ∈ L) :
    (1 - (ε2 + ε3 + ε4)) * ip (rs Y) n = 2 * ip (uY Y) n ∧
      ip n n * ip (uY Y) (uY Y) + (ε2 + ε3 + ε4) * ip (rs Y) n * ip (uY Y) n = 0 := by
  obtain ⟨hYK, hd⟩ := hLK Y hY
  obtain ⟨⟨c2, h2⟩, ⟨c3, h3⟩, ⟨c4, h4⟩⟩ := hline Y hYK
  obtain ⟨A2, A3, A4, B, C⟩ := line_exp Y n c2 c3 c4 h2 h3 h4
  have e := P1_Lfacts K hdef Y hYK hd
  have l2 := hl2 Y hY
  have l3 := hl3 Y hY
  have l4 := hl4 Y hY
  constructor
  · linear_combination B - A2 - A3 - A4 + l2 + l3 + l4
  · linear_combination (-(ip n n)) * e - ip n n * C + ip (uY Y) n * A2 + ip (uY Y) n * A3
      + ip (uY Y) n * A4 - ip (uY Y) n * l2 - ip (uY Y) n * l3 - ip (uY Y) n * l4

theorem P1_aniso (K : Submodule ℂ M45) (hdef : DefLine K mTC) (L : Submodule ℂ M45)
    (hLK : ∀ Y ∈ L, Y ∈ K ∧ dY Y = 0) (hL3 : 3 ≤ Module.finrank ℂ L) (n : V4)
    (htn : tau n = 0) (hN : ip n n ≠ 0)
    (hline : ∀ Y ∈ K, (∃ c : ℂ, col Y 2 = c • n) ∧ (∃ c : ℂ, col Y 3 = c • n) ∧
      (∃ c : ℂ, col Y 4 = c • n)) : False := by
  have hq2 : ∀ Y ∈ L, ip (col Y 2) n * (ip (col Y 2) n - ip (rs Y) n) = 0 := fun Y hY =>
    line_quad (col Y 2) (rs Y) n (hline Y (hLK Y hY).1).1 (NB_qbar K hdef Y (hLK Y hY).1).1
  have hq3 : ∀ Y ∈ L, ip (col Y 3) n * (ip (col Y 3) n - ip (rs Y) n) = 0 := fun Y hY =>
    line_quad (col Y 3) (rs Y) n (hline Y (hLK Y hY).1).2.1 (NB_qbar K hdef Y (hLK Y hY).1).2.1
  have hq4 : ∀ Y ∈ L, ip (col Y 4) n * (ip (col Y 4) n - ip (rs Y) n) = 0 := fun Y hY =>
    line_quad (col Y 4) (rs Y) n (hline Y (hLK Y hY).1).2.2 (NB_qbar K hdef Y (hLK Y hY).1).2.2
  obtain ⟨ε2, he2, hl2⟩ := eps_of L 2 n hq2
  obtain ⟨ε3, he3, hl3⟩ := eps_of L 3 n hq3
  obtain ⟨ε4, he4, hl4⟩ := eps_of L 4 n hq4
  have hrel := P1_rel K hdef L hLK n hline ε2 ε3 ε4 hl2 hl3 hl4
  have hτu : ∀ Y ∈ L, tau (uY Y) = 0 := fun Y hY => (TC5_tau K hdef Y (hLK Y hY).1).1
  have hzero : ∀ Y ∈ L, uY Y = 0 → ip (rs Y) n = 0 → Y = 0 := by
    intro Y hY hu hm
    obtain ⟨hYK, hd⟩ := hLK Y hY
    obtain ⟨⟨c2, h2⟩, ⟨c3, h3⟩, ⟨c4, h4⟩⟩ := hline Y hYK
    obtain ⟨A2, A3, A4, -, -⟩ := line_exp Y n c2 c3 c4 h2 h3 h4
    have z2 : c2 = 0 := by
      have e : c2 * ip n n = 0 := by rw [← A2, hl2 Y hY, hm, mul_zero]
      exact (mul_eq_zero.mp e).resolve_right hN
    have z3 : c3 = 0 := by
      have e : c3 * ip n n = 0 := by rw [← A3, hl3 Y hY, hm, mul_zero]
      exact (mul_eq_zero.mp e).resolve_right hN
    have z4 : c4 = 0 := by
      have e : c4 * ip n n = 0 := by rw [← A4, hl4 Y hY, hm, mul_zero]
      exact (mul_eq_zero.mp e).resolve_right hN
    apply uY_dY_zero Y hu hd
    · rw [h2, z2, zero_smul]
    · rw [h3, z3, zero_smul]
    · rw [h4, z4, zero_smul]
  have r := rank_nullity L uYL
  by_cases hs1 : ε2 + ε3 + ε4 = 1
  · have ha : ∀ Y ∈ L, ip (uY Y) n = 0 := by
      intro Y hY
      linear_combination (-1 / 2 : ℂ) * (hrel Y hY).1 - (1 / 2 : ℂ) * ip (rs Y) n * hs1
    have huu : ∀ Y ∈ L, ip (uY Y) (uY Y) = 0 := by
      intro Y hY
      have e : ip n n * ip (uY Y) (uY Y) = 0 := by
        linear_combination (hrel Y hY).2 - (ε2 + ε3 + ε4) * ip (rs Y) n * ha Y hY
      exact (mul_eq_zero.mp e).resolve_left hN
    have hU := iso_image L hτu huu
    have hb : ((L ⊓ LinearMap.ker uYL) ⊓ LinearMap.ker (mL n) : Submodule ℂ M45) = ⊥ := by
      rw [eq_bot_iff]
      intro Y hY
      rw [Submodule.mem_bot]
      have hY1 := (Submodule.mem_inf.mp hY).1
      have hm : ip (rs Y) n = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY).2
      have hYL := (Submodule.mem_inf.mp hY1).1
      have hu : uY Y = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY1).2
      exact hzero Y hYL hu hm
    have r2 := rank_nullity (L ⊓ LinearMap.ker uYL : Submodule ℂ M45) (mL n)
    rw [hb, finrank_bot] at r2
    have h1 : Module.finrank ℂ ((L ⊓ LinearMap.ker uYL : Submodule ℂ M45).map (mL n)) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    omega
  · have hker : (L ⊓ LinearMap.ker uYL : Submodule ℂ M45) = ⊥ := by
      rw [eq_bot_iff]
      intro Y hY
      rw [Submodule.mem_bot]
      have hYL := (Submodule.mem_inf.mp hY).1
      have hu : uY Y = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY).2
      have R1 := (hrel Y hYL).1
      rw [hu] at R1
      have hm : ip (rs Y) n = 0 := by
        have e : (1 - (ε2 + ε3 + ε4)) * ip (rs Y) n = 0 := by
          rw [R1]
          simp [ip]
        exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr (Ne.symm hs1))
      exact hzero Y hYL hu hm
    rw [hker, finrank_bot] at r
    have hV3 : Module.finrank ℂ (sumZero 4) ≤ 3 :=
      (finrank_sumZero (n := 4) (by norm_num)).trans (by norm_num)
    have hle : L.map uYL ≤ sumZero 4 := by
      rintro _ ⟨Y, hY, rfl⟩
      rw [mem_Vs]
      exact hτu Y hY
    have heq : L.map uYL = sumZero 4 :=
      Submodule.eq_of_le_of_finrank_le hle (hV3.trans (by omega))
    have hn : n ∈ L.map uYL := by
      rw [heq, mem_Vs]
      exact htn
    obtain ⟨Y0, hY0, hu0⟩ := hn
    have hu0' : uY Y0 = n := hu0
    obtain ⟨R1, R2⟩ := hrel Y0 hY0
    rw [hu0'] at R1 R2
    have h : ip n n + (ε2 + ε3 + ε4) * ip (rs Y0) n = 0 := by
      have e : ip n n * (ip n n + (ε2 + ε3 + ε4) * ip (rs Y0) n) = 0 := by
        linear_combination R2
      exact (mul_eq_zero.mp e).resolve_left hN
    have h' : (1 + (ε2 + ε3 + ε4)) * ip n n = 0 := by
      linear_combination (1 - (ε2 + ε3 + ε4)) * h - (ε2 + ε3 + ε4) * R1
    have hs : 1 + (ε2 + ε3 + ε4) = 0 := (mul_eq_zero.mp h').resolve_right hN
    rcases he2 with rfl | rfl <;> rcases he3 with rfl | rfl <;> rcases he4 with rfl | rfl <;>
      norm_num at hs

theorem P1_reduce (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (za zb : V4) (ha : zE za ∈ K) (hb : zE zb ∈ K)
    (hind : ∀ a b : ℂ, a • za + b • zb = 0 → a = 0 ∧ b = 0) :
    ∃ z0 z1 n : V4, zE z0 ∈ K ∧ zE z1 ∈ K ∧ z0 ≠ 0 ∧ tau z0 = 0 ∧ tau z1 = 1 ∧
      tau n = 0 ∧ ip n n = 0 ∧ ip n (Ed z0) = 0 ∧ ip n (Edb z0 z1) = 0 ∧
      (∀ Y ∈ K, (∃ c : ℂ, col Y 2 = c • n) ∧ (∃ c : ℂ, col Y 3 = c • n) ∧
        (∃ c : ℂ, col Y 4 = c • n)) ∧
      ∃ Y ∈ (K ⊓ LinearMap.ker dYL : Submodule ℂ M45),
        ¬ (col Y 2 = 0 ∧ col Y 3 = 0 ∧ col Y 4 = 0) := by
  obtain ⟨z0, z1, hz0K, hz1K, hz0, h0, h1, -⟩ := P1_nf K hdef za zb ha hb hind
  obtain ⟨n, hn1, hn2, hn3, hline⟩ := P1_line K hdef z0 z1 hz0K hz1K hz0 h0 h1
  have hL3 := P1_L K hdef hK5 z0 z1 hz0K hz1K hz0 h0 h1
  have hLK : ∀ Y ∈ (K ⊓ LinearMap.ker dYL : Submodule ℂ M45), Y ∈ K ∧ dY Y = 0 :=
    fun Y hY => ⟨(Submodule.mem_inf.mp hY).1, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY).2⟩
  by_cases hN : ip n n = 0
  · by_cases hv : ∀ Y ∈ (K ⊓ LinearMap.ker dYL : Submodule ℂ M45),
        col Y 2 = 0 ∧ col Y 3 = 0 ∧ col Y 4 = 0
    · exact (P1_van K hdef _ hLK hL3 hv).elim
    · push_neg at hv
      obtain ⟨Y, hY, hY'⟩ := hv
      refine ⟨z0, z1, n, hz0K, hz1K, hz0, h0, h1, hn1, hN, hn2, hn3, hline, Y, hY, ?_⟩
      intro hc
      exact hY' hc.1 hc.2.1 hc.2.2
  · exact (P1_aniso K hdef _ hLK hL3 n hn1 hN hline).elim

theorem chi_pow (n : V4) (h1 : tau n = 0) (h2 : ip n n = 0) (h3 : t3 n n n = 0) :
    ∀ i, n i ^ 4 = -(n 0 * n 1 * n 2 * n 3) := by
  have hp1 : n 0 + n 1 + n 2 + n 3 = 0 := h1
  have hp2 : n 0 * n 0 + n 1 * n 1 + n 2 * n 2 + n 3 * n 3 = 0 := h2
  have hp3 : n 0 * n 0 * n 0 + n 1 * n 1 * n 1 + n 2 * n 2 * n 2 + n 3 * n 3 * n 3 = 0 := h3
  intro i
  fin_cases i
  · show n 0 ^ 4 = -(n 0 * n 1 * n 2 * n 3)
    linear_combination (n 0 ^ 3 - (n 0 + n 1 + n 2 + n 3) * n 0 ^ 2 / 2
      + (n 0 + n 1 + n 2 + n 3) ^ 2 * n 0 / 6
      - (n 0 * n 0 + n 1 * n 1 + n 2 * n 2 + n 3 * n 3) * n 0 / 2) * hp1
      + n 0 ^ 2 / 2 * hp2 + n 0 / 3 * hp3
  · show n 1 ^ 4 = -(n 0 * n 1 * n 2 * n 3)
    linear_combination (n 1 ^ 3 - (n 0 + n 1 + n 2 + n 3) * n 1 ^ 2 / 2
      + (n 0 + n 1 + n 2 + n 3) ^ 2 * n 1 / 6
      - (n 0 * n 0 + n 1 * n 1 + n 2 * n 2 + n 3 * n 3) * n 1 / 2) * hp1
      + n 1 ^ 2 / 2 * hp2 + n 1 / 3 * hp3
  · show n 2 ^ 4 = -(n 0 * n 1 * n 2 * n 3)
    linear_combination (n 2 ^ 3 - (n 0 + n 1 + n 2 + n 3) * n 2 ^ 2 / 2
      + (n 0 + n 1 + n 2 + n 3) ^ 2 * n 2 / 6
      - (n 0 * n 0 + n 1 * n 1 + n 2 * n 2 + n 3 * n 3) * n 2 / 2) * hp1
      + n 2 ^ 2 / 2 * hp2 + n 2 / 3 * hp3
  · show n 3 ^ 4 = -(n 0 * n 1 * n 2 * n 3)
    linear_combination (n 3 ^ 3 - (n 0 + n 1 + n 2 + n 3) * n 3 ^ 2 / 2
      + (n 0 + n 1 + n 2 + n 3) ^ 2 * n 3 / 6
      - (n 0 * n 0 + n 1 * n 1 + n 2 * n 2 + n 3 * n 3) * n 3 / 2) * hp1
      + n 3 ^ 2 / 2 * hp2 + n 3 / 3 * hp3

theorem iso_quad (x s n : V4) (h : ∃ c : ℂ, x = c • n) (hnn : ip n n = 0)
    (hq : ip x x = ip s x) (i0 : Fin 4) : x i0 * ip s n = 0 := by
  obtain ⟨c, rfl⟩ := h
  simp only [ip, Pi.smul_apply, smul_eq_mul] at hq hnn ⊢
  linear_combination (-(n i0)) * hq + n i0 * c ^ 2 * hnn

theorem L_slev (K : Submodule ℂ M45) (hdef : DefLine K mTC) (L : Submodule ℂ M45)
    (hLK : ∀ Y ∈ L, Y ∈ K ∧ dY Y = 0) : SLev L := by
  intro Y hY a
  obtain ⟨hYK, hd⟩ := hLK Y hY
  obtain ⟨θ, hθ⟩ := hdef Y hYK
  have hdiff := TC5_diff Y
  have hpc0 : ∀ b c d : V4, pc 0 b c d = 0 := by
    intro b c d
    simp [pc]
  rw [hd, hpc0, mul_zero, hθ 0, hθ 1] at hdiff
  obtain ⟨m0, m1, -, -, -⟩ := mTC_vals
  rw [m0, m1] at hdiff
  have hθ0 : θ = 0 := by linear_combination (-1 / 2 : ℂ) * hdiff
  rw [hθ a, hθ0, zero_mul, add_zero]

theorem P1_iso (K : Submodule ℂ M45) (hdef : DefLine K mTC) (L : Submodule ℂ M45)
    (hLK : ∀ Y ∈ L, Y ∈ K ∧ dY Y = 0) (hL3 : 3 ≤ Module.finrank ℂ L) (n : V4)
    (htn : tau n = 0) (hnn : ip n n = 0)
    (hline : ∀ Y ∈ K, (∃ c : ℂ, col Y 2 = c • n) ∧ (∃ c : ℂ, col Y 3 = c • n) ∧
      (∃ c : ℂ, col Y 4 = c • n))
    (Y1 : M45) (hY1 : Y1 ∈ L) (hY1' : ¬ (col Y1 2 = 0 ∧ col Y1 3 = 0 ∧ col Y1 4 = 0)) :
    n ≠ 0 ∧ t3 n n n = 0 := by
  have hex : ∃ j : Fin 5, (j = 2 ∨ j = 3 ∨ j = 4) ∧ col Y1 j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hY1' ⟨hc 2 (Or.inl rfl), hc 3 (Or.inr (Or.inl rfl)), hc 4 (Or.inr (Or.inr rfl))⟩
  obtain ⟨j, hj, hcol⟩ := hex
  have hlj : ∀ Y ∈ K, ∃ c : ℂ, col Y j = c • n := by
    intro Y hY
    rcases hj with rfl | rfl | rfl
    · exact (hline Y hY).1
    · exact (hline Y hY).2.1
    · exact (hline Y hY).2.2
  have hqj : ∀ Y ∈ K, ip (col Y j) (col Y j) = ip (rs Y) (col Y j) := by
    intro Y hY
    rcases hj with rfl | rfl | rfl
    · exact (NB_qbar K hdef Y hY).1
    · exact (NB_qbar K hdef Y hY).2.1
    · exact (NB_qbar K hdef Y hY).2.2
  obtain ⟨c1, hc1⟩ := hlj Y1 (hLK Y1 hY1).1
  have hc10 : c1 ≠ 0 := by
    intro h
    apply hcol
    rw [hc1, h, zero_smul]
  have hn0 : n ≠ 0 := by
    intro h
    apply hcol
    rw [hc1, h, smul_zero]
  obtain ⟨i0, hi0'⟩ := Function.ne_iff.mp hn0
  have hi0 : n i0 ≠ 0 := hi0'
  have hm : ∀ Y ∈ L, ip (rs Y) n = 0 := by
    have hprod : ∀ Y ∈ L, Y (i0, j) * ip (rs Y) n = 0 := fun Y hY =>
      iso_quad (col Y j) (rs Y) n (hlj Y (hLK Y hY).1) hnn (hqj Y (hLK Y hY).1) i0
    rcases prod_lin L (fun Y => Y (i0, j)) (fun Y => ip (rs Y) n) (fun Y Y' => rfl)
      (fun Y Y' => by
        simp only [map_add, ip, Pi.add_apply]
        ring) hprod with h | h
    · exfalso
      have e := h Y1 hY1
      have e1 := congrFun hc1 i0
      simp only [col, Pi.smul_apply, smul_eq_mul] at e1
      have e' : Y1 (i0, j) = 0 := e
      rw [e1] at e'
      exact mul_ne_zero hc10 hi0 e'
    · exact h
  have hform : ∀ Y ∈ L, ∃ x : Fin 5 → ℂ, Y = outer n x := by
    intro Y hY
    obtain ⟨hYK, hd⟩ := hLK Y hY
    obtain ⟨⟨c2, h2⟩, ⟨c3, h3⟩, ⟨c4, h4⟩⟩ := hline Y hYK
    obtain ⟨-, -, -, B, C⟩ := line_exp Y n c2 c3 c4 h2 h3 h4
    have e := P1_Lfacts K hdef Y hYK hd
    have hmY := hm Y hY
    have ha : ip (uY Y) n = 0 := by
      linear_combination (1 / 2 : ℂ) * hmY - (1 / 2 : ℂ) * B - (1 / 2 : ℂ) * (c2 + c3 + c4) * hnn
    have huu : ip (uY Y) (uY Y) = 0 := by
      linear_combination (-1 : ℂ) * e - C - (c2 + c3 + c4) * ha
    have hnu : ip n (uY Y) = 0 := by
      simp only [ip] at ha ⊢
      linear_combination ha
    obtain ⟨lam, hlam⟩ := Q4 n (uY Y) hn0 htn hnn (TC5_tau K hdef Y hYK).1 huu hnu
    refine ⟨![lam, lam, c2, c3, c4], ?_⟩
    funext p
    obtain ⟨k, jj⟩ := p
    have eu := congrFun hlam k
    have ed := congrFun hd k
    simp only [uY, dY, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at eu ed
    have g2 := congrFun h2 k
    have g3 := congrFun h3 k
    have g4 := congrFun h4 k
    simp only [col, Pi.smul_apply, smul_eq_mul] at g2 g3 g4
    fin_cases jj
    · show Y (k, 0) = n k * lam
      linear_combination eu + ed
    · show Y (k, 1) = n k * lam
      linear_combination eu - ed
    · show Y (k, 2) = n k * c2
      rw [g2]
      ring
    · show Y (k, 3) = n k * c3
      rw [g3]
      ring
    · show Y (k, 4) = n k * c4
      rw [g4]
      ring
  refine ⟨hn0, ?_⟩
  by_contra h3
  have hS := L_slev K hdef L hLK
  have hle : L.map rs ≤ Submodule.span ℂ {n} := by
    rintro _ ⟨Y, hY, rfl⟩
    obtain ⟨x, rfl⟩ := hform Y hY
    rw [Submodule.mem_span_singleton]
    refine ⟨x 0 + x 1 + x 2 + x 3 + x 4, ?_⟩
    funext k
    rw [rs_apply]
    simp only [outer, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 := (Submodule.finrank_mono hle).trans (le_of_eq (finrank_span_singleton hn0))
  have r := rank_nullity L rs
  have hA := A1b (L ⊓ LinearMap.ker rs : Submodule ℂ M45)
    (fun Y hY a => hS Y (Submodule.mem_inf.mp hY).1 a)
    (fun Y hY => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY).2) n hn0 htn hnn
    (fun Y hY => hform Y (Submodule.mem_inf.mp hY).1) h3
  omega

theorem TC5_P1 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (za zb : V4) (ha : zE za ∈ K) (hb : zE zb ∈ K)
    (hind : ∀ a b : ℂ, a • za + b • zb = 0 → a = 0 ∧ b = 0) : False := by
  obtain ⟨z0, z1, n, hz0K, hz1K, hz0, h0, h1, hn1, hnn, hn2, hn3, hline, Y1, hY1, hY1'⟩ :=
    P1_reduce K hdef hK5 za zb ha hb hind
  have hL3 := P1_L K hdef hK5 z0 z1 hz0K hz1K hz0 h0 h1
  have hLK : ∀ Y ∈ (K ⊓ LinearMap.ker dYL : Submodule ℂ M45), Y ∈ K ∧ dY Y = 0 :=
    fun Y hY => ⟨(Submodule.mem_inf.mp hY).1, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY).2⟩
  obtain ⟨hn0, h3⟩ := P1_iso K hdef _ hLK hL3 n hn1 hnn hline Y1 hY1 hY1'
  have hk := chi_pow n hn1 hnn h3
  have hκ : -(n 0 * n 1 * n 2 * n 3) ≠ 0 := by
    intro h
    apply hn0
    funext i
    have e := hk i
    rw [h] at e
    exact (pow_eq_zero_iff (by norm_num)).mp e
  obtain ⟨h00, -⟩ := LemmaZ K hdef z0 hz0K (zE z0) hz0K
  obtain ⟨h11, h01, -⟩ := LemmaZ K hdef z1 hz1K (zE z0) hz0K
  rw [dY_zE] at h01
  exact LAG_b n _ hκ hk hn1 hnn h3 z0 z1 hz0 h0 h00 h1 h11 h01 ⟨hn2, hn3⟩

theorem two_indep (W : Submodule ℂ V4) (h : 2 ≤ Module.finrank ℂ W) :
    ∃ a ∈ W, ∃ b ∈ W, ∀ s t : ℂ, s • a + t • b = 0 → s = 0 ∧ t = 0 := by
  by_contra hc
  push_neg at hc
  by_cases hW : ∃ w0 ∈ W, w0 ≠ 0
  · obtain ⟨w0, hw0, hne⟩ := hW
    have hle : W ≤ Submodule.span ℂ {w0} := by
      intro w hw
      obtain ⟨s, t, hst, hst'⟩ := hc w0 hw0 w hw
      by_cases ht : t = 0
      · exfalso
        have hs : s ≠ 0 := fun hs => hst' hs ht
        rw [ht, zero_smul, add_zero] at hst
        exact hne ((smul_eq_zero.mp hst).resolve_left hs)
      · rw [Submodule.mem_span_singleton]
        refine ⟨-(s / t), ?_⟩
        funext k
        have e := congrFun hst k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
        linear_combination (-(t⁻¹)) * e + w k * inv_mul_cancel₀ ht
    have h1 := (Submodule.finrank_mono hle).trans (le_of_eq (finrank_span_singleton hne))
    omega
  · push_neg at hW
    have hbot : W = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      exact hW w hw
    rw [hbot, finrank_bot] at h
    omega

theorem zeta_le_one (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (W : Submodule ℂ V4) (hW : ∀ z ∈ W, zE z ∈ K) : Module.finrank ℂ W ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, b, hb, hind⟩ := two_indep W (by omega)
  exact TC5_P1 K hdef hK5 a b (hW a ha) (hW b hb) hind

theorem Z_of_nbar (Z : M45) (h2 : col Z 2 = 0) (h3 : col Z 3 = 0) (h4 : col Z 4 = 0)
    (hu : uY Z = 0) : Z = zE (dY Z) := by
  funext p
  obtain ⟨k, j⟩ := p
  have eu := congrFun hu k
  simp only [uY, Pi.zero_apply] at eu
  fin_cases j
  · show Z (k, 0) = zE (dY Z) (k, 0)
    rw [zE0]
    simp only [dY]
    linear_combination eu
  · show Z (k, 1) = zE (dY Z) (k, 1)
    rw [zE1]
    simp only [dY]
    linear_combination eu
  · show Z (k, 2) = zE (dY Z) (k, 2)
    rw [(by simp [zE] : zE (dY Z) (k, 2) = 0)]
    exact congrFun h2 k
  · show Z (k, 3) = zE (dY Z) (k, 3)
    rw [(by simp [zE] : zE (dY Z) (k, 3) = 0)]
    exact congrFun h3 k
  · show Z (k, 4) = zE (dY Z) (k, 4)
    rw [(by simp [zE] : zE (dY Z) (k, 4) = 0)]
    exact congrFun h4 k

theorem rs_le3 (K : Submodule ℂ M45) (hdef : DefLine K mTC) :
    Module.finrank ℂ (K.map rs) ≤ 3 := by
  have hS : K.map rs ≤ sumZero 4 := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [mem_Vs]
    exact (TC5_tau K hdef Y hY).2.2.2.2
  exact (Submodule.finrank_mono hS).trans
    ((finrank_sumZero (n := 4) (by norm_num)).trans (by norm_num))

theorem no_nbar (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (hall : ∀ Z ∈ K, rs Z = 0 → col Z 2 = 0 ∧ col Z 3 = 0 ∧ col Z 4 = 0 ∧ uY Z = 0) : False := by
  have hW : ∀ z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL, zE z ∈ K := by
    rintro _ ⟨Z, hZ, rfl⟩
    have hZ' := Submodule.mem_inf.mp hZ
    obtain ⟨c2, c3, c4, cu⟩ := hall Z hZ'.1 (LinearMap.mem_ker.mp hZ'.2)
    rw [dYL_apply, ← Z_of_nbar Z c2 c3 c4 cu]
    exact hZ'.1
  have h1 := zeta_le_one K hdef hK5 _ hW
  have hker : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hZ1 := (Submodule.mem_inf.mp hZ).1
    have hd : dY Z = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2
    have hZ' := Submodule.mem_inf.mp hZ1
    obtain ⟨c2, c3, c4, cu⟩ := hall Z hZ'.1 (LinearMap.mem_ker.mp hZ'.2)
    exact uY_dY_zero Z cu hd c2 c3 c4
  have r1 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) dYL
  rw [hker, finrank_bot] at r1
  have r2 := rank_nullity K rs
  have hq := rs_le3 K hdef
  omega

theorem TC5_P2 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K) :
    Module.finrank ℂ (K.map rs) ≤ 2 ∧
      (∀ Y1 ∈ K, ∀ Y2 ∈ K,
        ip (rs Y1) (rs Y1) * ip (rs Y2) (rs Y2) - ip (rs Y1) (rs Y2) ^ 2 = 0) ∧
      3 ≤ Module.finrank ℂ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) ∧
      (∀ W : Submodule ℂ V4, (∀ z ∈ W, zE z ∈ K) → Module.finrank ℂ W ≤ 1) := by
  have hq2 : Module.finrank ℂ (K.map rs) ≤ 2 := by
    by_contra h
    push_neg at h
    have hq : Module.finrank ℂ (K.map rs) = 3 := by
      have := rs_le3 K hdef
      omega
    exact no_nbar K hdef hK5 (fun Z hZ hZ0 => NB3 K hdef hq Z hZ hZ0)
  refine ⟨hq2, ?_, ?_, zeta_le_one K hdef hK5⟩
  · intro Y1 hY1 Y2 hY2
    by_contra hD
    exact no_nbar K hdef hK5 (fun Z hZ hZ0 => NB_plane K hdef Y1 hY1 Y2 hY2 hD Z hZ hZ0)
  · have r2 := rank_nullity K rs
    omega

theorem neut_facts (K : Submodule ℂ M45) (hdef : DefLine K mTC) (j : Fin 5)
    (hj : j = 2 ∨ j = 3 ∨ j = 4) (Y : M45) (hY : Y ∈ K) :
    tau (col Y j) = 0 ∧ ip (col Y j) (col Y j) = ip (rs Y) (col Y j) := by
  rcases hj with rfl | rfl | rfl
  · exact ⟨(TC5_tau K hdef Y hY).2.1, (NB_qbar K hdef Y hY).1⟩
  · exact ⟨(TC5_tau K hdef Y hY).2.2.1, (NB_qbar K hdef Y hY).2.1⟩
  · exact ⟨(TC5_tau K hdef Y hY).2.2.2.1, (NB_qbar K hdef Y hY).2.2⟩

theorem NB_line (K : Submodule ℂ M45) (hdef : DefLine K mTC) (j : Fin 5)
    (hj : j = 2 ∨ j = 3 ∨ j = 4) :
    Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (colL j)) ≤ 1 := by
  have hqb : ∀ Y ∈ K, ip (col Y j) (col Y j) = ip (rs Y) (col Y j) := fun Y hY =>
    (neut_facts K hdef j hj Y hY).2
  apply Q1
  · rintro _ ⟨Z, hZ, rfl⟩
    exact (neut_facts K hdef j hj Z (Submodule.mem_inf.mp hZ).1).1
  · rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
    have h1 := Submodule.mem_inf.mp hZ
    have h2 := Submodule.mem_inf.mp hZ'
    have e := neutral_pol K j hqb Z h1.1 Z' h2.1
    rw [LinearMap.mem_ker.mp h1.2, LinearMap.mem_ker.mp h2.2] at e
    rw [colL_apply, colL_apply]
    simp only [ip, Pi.zero_apply] at e ⊢
    linear_combination (1 / 2 : ℂ) * e

theorem line_of_le_one (W : Submodule ℂ V4) (h : Module.finrank ℂ W ≤ 1) :
    ∃ v : V4, v ∈ W ∧ ∀ w ∈ W, ∃ c : ℂ, w = c • v := by
  by_cases hW : ∃ w0 ∈ W, w0 ≠ 0
  · obtain ⟨w0, hw0, hne⟩ := hW
    refine ⟨w0, hw0, ?_⟩
    intro w hw
    by_contra hc
    push_neg at hc
    have hlt : Submodule.span ℂ {w0} < Submodule.span ℂ {w0, w} := by
      refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
      intro h'
      have hw' : w ∈ Submodule.span ℂ {w0} := by
        rw [h']
        exact Submodule.subset_span (by simp)
      obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp hw'
      exact hc c hc'.symm
    have hle : Submodule.span ℂ {w0, w} ≤ W := by
      rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hw0
      · exact hw
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_mono hle
    have h3 : Module.finrank ℂ (Submodule.span ℂ {w0}) = 1 := finrank_span_singleton hne
    omega
  · push_neg at hW
    refine ⟨0, W.zero_mem, ?_⟩
    intro w hw
    exact ⟨0, by rw [hW w hw, zero_smul]⟩

theorem NB_lines (K : Submodule ℂ M45) (hdef : DefLine K mTC) (j : Fin 5)
    (hj : j = 2 ∨ j = 3 ∨ j = 4) :
    ∃ v : V4, tau v = 0 ∧ ip v v = 0 ∧ ∀ Z ∈ K, rs Z = 0 → ∃ c : ℂ, col Z j = c • v := by
  obtain ⟨v, hv, hall⟩ := line_of_le_one _ (NB_line K hdef j hj)
  obtain ⟨Z0, hZ0, rfl⟩ := Submodule.mem_map.mp hv
  have h0 := Submodule.mem_inf.mp hZ0
  have hrs0 : rs Z0 = 0 := LinearMap.mem_ker.mp h0.2
  obtain ⟨t0, q0⟩ := neut_facts K hdef j hj Z0 h0.1
  refine ⟨colL j Z0, t0, ?_, ?_⟩
  · rw [colL_apply, q0, hrs0]
    simp [ip]
  · intro Z hZ hZ0'
    obtain ⟨c, hc⟩ := hall (colL j Z)
      (Submodule.mem_map.mpr ⟨Z, Submodule.mem_inf.mpr ⟨hZ, LinearMap.mem_ker.mpr hZ0'⟩, rfl⟩)
    exact ⟨c, hc⟩

set_option maxHeartbeats 1000000 in
theorem pc_full (x y z w : V4) :
    pc x y z w = tau x * tau y * tau z * tau w
      - (tau x * tau y * ip z w + tau x * tau z * ip y w + tau x * tau w * ip y z
        + tau y * tau z * ip x w + tau y * tau w * ip x z + tau z * tau w * ip x y)
      + 2 * (tau x * t3 y z w + tau y * t3 x z w + tau z * t3 x y w + tau w * t3 x y z)
      + br x y z w := by
  simp (config := {decide := true}) only [pc, br, tau, ip, t3, t4, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  ring

theorem nbar_tau (a b c : V4) (ha : tau a = 0) (hb : tau b = 0) (hc : tau c = 0) :
    tau (fun k => -(a k + b k + c k) / 2) = 0 := by
  simp only [tau] at ha hb hc ⊢
  linear_combination (-1 / 2 : ℂ) * (ha + hb + hc)

theorem nbar_cubic (a b c : V4) (ha : tau a = 0) (hb : tau b = 0) (hc : tau c = 0) :
    X3c (fun k => -(a k + b k + c k) / 2) a b c =
      -(t3 a a b + t3 a a c + t3 b b a + t3 b b c + t3 c c a + t3 c c b + t3 a b c) := by
  have hu := nbar_tau a b c ha hb hc
  simp only [X3c, hu, ha, hb, hc, zero_mul, mul_zero, sub_zero, zero_sub, zero_add, add_zero]
  simp only [t3]
  ring

theorem nbar_quartic (a b c : V4) (ha : tau a = 0) (hb : tau b = 0) (hc : tau c = 0)
    (haa : ip a a = 0) (hbb : ip b b = 0) (hcc : ip c c = 0) :
    pc (fun k => -(a k + b k + c k) / 2) a b c =
      3 * (t4 a a b c + t4 b b a c + t4 c c a b)
        - (ip a b * ip a c + ip b a * ip b c + ip c a * ip c b) := by
  have hu := nbar_tau a b c ha hb hc
  rw [pc_full, hu, ha, hb, hc]
  simp only [br, t4, ip] at haa hbb hcc ⊢
  linear_combination (-1 / 2 : ℂ) * ((b 0 * c 0 + b 1 * c 1 + b 2 * c 2 + b 3 * c 3) * haa
    + (a 0 * c 0 + a 1 * c 1 + a 2 * c 2 + a 3 * c 3) * hbb
    + (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3) * hcc)

theorem nbar_eqs (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Z : M45) (hZ : Z ∈ K)
    (hZ0 : rs Z = 0) :
    t3 (col Z 2) (col Z 2) (col Z 3) + t3 (col Z 2) (col Z 2) (col Z 4)
      + t3 (col Z 3) (col Z 3) (col Z 2) + t3 (col Z 3) (col Z 3) (col Z 4)
      + t3 (col Z 4) (col Z 4) (col Z 2) + t3 (col Z 4) (col Z 4) (col Z 3)
      + t3 (col Z 2) (col Z 3) (col Z 4) = 0 ∧
    3 * (t4 (col Z 2) (col Z 2) (col Z 3) (col Z 4) + t4 (col Z 3) (col Z 3) (col Z 2) (col Z 4)
        + t4 (col Z 4) (col Z 4) (col Z 2) (col Z 3))
      - (ip (col Z 2) (col Z 3) * ip (col Z 2) (col Z 4)
        + ip (col Z 3) (col Z 2) * ip (col Z 3) (col Z 4)
        + ip (col Z 4) (col Z 2) * ip (col Z 4) (col Z 3)) = 0 := by
  obtain ⟨-, t2, t3', t4', -⟩ := TC5_tau K hdef Z hZ
  obtain ⟨q2, q3, q4⟩ := NB_qbar K hdef Z hZ
  rw [hZ0] at q2 q3 q4
  have i2 : ip (col Z 2) (col Z 2) = 0 := by rw [q2]; simp [ip]
  have i3 : ip (col Z 3) (col Z 3) = 0 := by rw [q3]; simp [ip]
  have i4 : ip (col Z 4) (col Z 4) = 0 := by rw [q4]; simp [ip]
  have hu : uY Z = fun k => -(col Z 2 k + col Z 3 k + col Z 4 k) / 2 := by
    funext k
    have e := congrFun hZ0 k
    rw [rs_apply] at e
    have e' : Z (k, 0) + Z (k, 1) + Z (k, 2) + Z (k, 3) + Z (k, 4) = 0 := e
    simp only [uY, col]
    linear_combination (1 / 2 : ℂ) * e'
  obtain ⟨-, -, b3, b4⟩ := TC5_deg_i K hdef Z hZ
  rw [hu] at b3 b4
  rw [nbar_cubic _ _ _ t2 t3' t4'] at b3
  rw [nbar_quartic _ _ _ t2 t3' t4' i2 i3 i4] at b4
  exact ⟨by linear_combination -b3, b4⟩

theorem pair_E2 (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0) (h4 : ip w w = 0)
    (h5 : t3 v v w = 0) (h6 : t3 v w w = 0) (k : Fin 4) :
    6 * (v k * w k) ^ 2 - 2 * ip v w * (v k * w k) = 6 * (v 0 * w 0) ^ 2 - 2 * ip v w * (v 0 * w 0) := by
  simp only [tau, ip, t3] at h1 h2 h3 h4 h5 h6 ⊢
  fin_cases k
  · rfl
  · show 6 * (v 1 * w 1) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v 1 * w 1) = 6 * (v 0 * w 0) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v 0 * w 0)
    linear_combination (v 0*w 0*w 2/2 + v 0*w 0*w 3/2 - v 0*w 1*w 2/2 - v 0*w 1*w 3/2 - v 0*w 2*w 3 + v 1*w 0*w 2/2 + v 1*w 0*w 3/2 - v 1*w 1*w 2/2 - v 1*w 1*w 3/2 + v 1*w 2*w 3 + v 2*w 0*w 2/2 - v 2*w 0*w 3/2 - v 2*w 1*w 2/2 + v 2*w 1*w 3/2 - v 3*w 0*w 2/2 + v 3*w 0*w 3/2 + v 3*w 1*w 2/2 - v 3*w 1*w 3/2) * h1 + (-v 0^2*w 0 + v 0^2*w 2/2 + v 0^2*w 3/2 - v 0*v 1*w 0 + v 0*v 1*w 1 + v 0*v 2*w 2 + v 0*v 3*w 3 + v 1^2*w 1 - v 1^2*w 2/2 - v 1^2*w 3/2 - v 1*v 2*w 2 - v 1*v 3*w 3 + v 2^2*w 0/2 - v 2^2*w 1/2 + v 3^2*w 0/2 - v 3^2*w 1/2) * h2 + (-w 0^2/2 + w 1^2/2) * h3 + (-v 0^2/2 + v 1^2/2) * h4 + (-w 0 + w 1) * h5 + (-v 0 + v 1) * h6
  · show 6 * (v 2 * w 2) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v 2 * w 2) = 6 * (v 0 * w 0) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v 0 * w 0)
    linear_combination (v 0*w 0*w 1/2 + v 0*w 0*w 3/2 - v 0*w 1*w 2/2 - v 0*w 1*w 3 - v 0*w 2*w 3/2 + v 1*w 0*w 1/2 - v 1*w 0*w 3/2 - v 1*w 1*w 2/2 + v 1*w 2*w 3/2 + v 2*w 0*w 1/2 + v 2*w 0*w 3/2 - v 2*w 1*w 2/2 + v 2*w 1*w 3 - v 2*w 2*w 3/2 - v 3*w 0*w 1/2 + v 3*w 0*w 3/2 + v 3*w 1*w 2/2 - v 3*w 2*w 3/2) * h1 + (-v 0^2*w 0 + v 0^2*w 1/2 + v 0^2*w 3/2 + v 0*v 1*w 1 - v 0*v 2*w 0 + v 0*v 2*w 2 + v 0*v 3*w 3 + v 1^2*w 0/2 - v 1^2*w 2/2 - v 1*v 2*w 1 - v 2^2*w 1/2 + v 2^2*w 2 - v 2^2*w 3/2 - v 2*v 3*w 3 + v 3^2*w 0/2 - v 3^2*w 2/2) * h2 + (-w 0^2/2 + w 2^2/2) * h3 + (-v 0^2/2 + v 2^2/2) * h4 + (-w 0 + w 2) * h5 + (-v 0 + v 2) * h6
  · show 6 * (v 3 * w 3) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v 3 * w 3) = 6 * (v 0 * w 0) ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * (v 0 * w 0)
    linear_combination (v 0*w 0*w 1/2 + v 0*w 0*w 2/2 - v 0*w 1*w 2 - v 0*w 1*w 3/2 - v 0*w 2*w 3/2 + v 1*w 0*w 1/2 - v 1*w 0*w 2/2 - v 1*w 1*w 3/2 + v 1*w 2*w 3/2 - v 2*w 0*w 1/2 + v 2*w 0*w 2/2 + v 2*w 1*w 3/2 - v 2*w 2*w 3/2 + v 3*w 0*w 1/2 + v 3*w 0*w 2/2 + v 3*w 1*w 2 - v 3*w 1*w 3/2 - v 3*w 2*w 3/2) * h1 + (-v 0^2*w 0 + v 0^2*w 1/2 + v 0^2*w 2/2 + v 0*v 1*w 1 + v 0*v 2*w 2 - v 0*v 3*w 0 + v 0*v 3*w 3 + v 1^2*w 0/2 - v 1^2*w 3/2 - v 1*v 3*w 1 + v 2^2*w 0/2 - v 2^2*w 3/2 - v 2*v 3*w 2 - v 3^2*w 1/2 - v 3^2*w 2/2 + v 3^2*w 3) * h2 + (-w 0^2/2 + w 3^2/2) * h3 + (-v 0^2/2 + v 3^2/2) * h4 + (-w 0 + w 3) * h5 + (-v 0 + v 3) * h6

theorem pair_rel (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0) (h4 : ip w w = 0)
    (h5 : t3 v v w = 0) (h6 : t3 v w w = 0) (hg : ip v w ≠ 0) :
    (∀ k, v k * w k = ip v w / 4) ∨
      (∃ k, v k = 0 ∧ w k = 0 ∧ ∀ m, m ≠ k → 3 * (v m * w m) = ip v w) := by
  have E := pair_E2 v w h1 h2 h3 h4 h5 h6
  have F1 : (v 1 * w 1 - v 0 * w 0) * (6 * (v 1 * w 1 + v 0 * w 0) - 2 * ip v w) = 0 := by
    linear_combination E 1
  have F2 : (v 2 * w 2 - v 0 * w 0) * (6 * (v 2 * w 2 + v 0 * w 0) - 2 * ip v w) = 0 := by
    linear_combination E 2
  have F3 : (v 3 * w 3 - v 0 * w 0) * (6 * (v 3 * w 3 + v 0 * w 0) - 2 * ip v w) = 0 := by
    linear_combination E 3
  have hs : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 = ip v w := rfl
  have hv : v 0 + v 1 + v 2 + v 3 = 0 := h1
  have hw : w 0 + w 1 + w 2 + w 3 = 0 := h2
  have sv : v 0 * w 0 * v 0 + v 1 * w 1 * v 1 + v 2 * w 2 * v 2 + v 3 * w 3 * v 3 = 0 := by
    have e : t3 v v w = 0 := h5
    simp only [t3] at e
    linear_combination e
  have sw : v 0 * w 0 * w 0 + v 1 * w 1 * w 1 + v 2 * w 2 * w 2 + v 3 * w 3 * w 3 = 0 := by
    have e : t3 v w w = 0 := h6
    simp only [t3] at e
    linear_combination e
  rcases mul_eq_zero.mp F1 with a1 | a1 <;> rcases mul_eq_zero.mp F2 with a2 | a2 <;>
    rcases mul_eq_zero.mp F3 with a3 | a3
  · left
    have hy0 : v 0 * w 0 = ip v w / 4 := by
      linear_combination (1/4) * hs + (-1/4) * a1 + (-1/4) * a2 + (-1/4) * a3
    intro k
    fin_cases k
    · exact hy0
    · show v 1 * w 1 = ip v w / 4
      linear_combination a1 + hy0
    · show v 2 * w 2 = ip v w / 4
      linear_combination a2 + hy0
    · show v 3 * w 3 = ip v w / 4
      linear_combination a3 + hy0
  · right
    have hy0 : v 0 * w 0 = ip v w / 3 := by
      linear_combination (1/2) * hs + (-1/2) * a1 + (-1/2) * a2 + (-1/12) * a3
    have hyj : v 3 * w 3 = 0 := by
      linear_combination (1/6) * a3 + (-1) * hy0
    refine ⟨3, ?_, ?_, ?_⟩
    · have e : ip v w * v 3 = 0 := by
        linear_combination (-3) * sv + (ip v w) * hv + (3*v 0 + 3*v 1 + 3*v 2) * hy0 + (3*v 1) * a1 + (3*v 2) * a2 + (3*v 3) * hyj
      exact (mul_eq_zero.mp e).resolve_left hg
    · have e : ip v w * w 3 = 0 := by
        linear_combination (-3) * sw + (ip v w) * hw + (3*w 0 + 3*w 1 + 3*w 2) * hy0 + (3*w 1) * a1 + (3*w 2) * a2 + (3*w 3) * hyj
      exact (mul_eq_zero.mp e).resolve_left hg
    · intro m hm
      fin_cases m
      · show 3 * (v 0 * w 0) = ip v w
        linear_combination (3) * hy0
      · show 3 * (v 1 * w 1) = ip v w
        linear_combination (3) * a1 + (3) * hy0
      · show 3 * (v 2 * w 2) = ip v w
        linear_combination (3) * a2 + (3) * hy0
      · exact (hm rfl).elim
  · right
    have hy0 : v 0 * w 0 = ip v w / 3 := by
      linear_combination (1/2) * hs + (-1/2) * a1 + (-1/2) * a3 + (-1/12) * a2
    have hyj : v 2 * w 2 = 0 := by
      linear_combination (1/6) * a2 + (-1) * hy0
    refine ⟨2, ?_, ?_, ?_⟩
    · have e : ip v w * v 2 = 0 := by
        linear_combination (-3) * sv + (ip v w) * hv + (3*v 0 + 3*v 1 + 3*v 3) * hy0 + (3*v 1) * a1 + (3*v 3) * a3 + (3*v 2) * hyj
      exact (mul_eq_zero.mp e).resolve_left hg
    · have e : ip v w * w 2 = 0 := by
        linear_combination (-3) * sw + (ip v w) * hw + (3*w 0 + 3*w 1 + 3*w 3) * hy0 + (3*w 1) * a1 + (3*w 3) * a3 + (3*w 2) * hyj
      exact (mul_eq_zero.mp e).resolve_left hg
    · intro m hm
      fin_cases m
      · show 3 * (v 0 * w 0) = ip v w
        linear_combination (3) * hy0
      · show 3 * (v 1 * w 1) = ip v w
        linear_combination (3) * a1 + (3) * hy0
      · exact (hm rfl).elim
      · show 3 * (v 3 * w 3) = ip v w
        linear_combination (3) * a3 + (3) * hy0
  · exfalso
    apply hg
    linear_combination (3) * a1 + (1/2) * a2 + (1/2) * a3 + (-3) * hs
  · right
    have hy0 : v 0 * w 0 = ip v w / 3 := by
      linear_combination (1/2) * hs + (-1/2) * a2 + (-1/2) * a3 + (-1/12) * a1
    have hyj : v 1 * w 1 = 0 := by
      linear_combination (1/6) * a1 + (-1) * hy0
    refine ⟨1, ?_, ?_, ?_⟩
    · have e : ip v w * v 1 = 0 := by
        linear_combination (-3) * sv + (ip v w) * hv + (3*v 0 + 3*v 2 + 3*v 3) * hy0 + (3*v 2) * a2 + (3*v 3) * a3 + (3*v 1) * hyj
      exact (mul_eq_zero.mp e).resolve_left hg
    · have e : ip v w * w 1 = 0 := by
        linear_combination (-3) * sw + (ip v w) * hw + (3*w 0 + 3*w 2 + 3*w 3) * hy0 + (3*w 2) * a2 + (3*w 3) * a3 + (3*w 1) * hyj
      exact (mul_eq_zero.mp e).resolve_left hg
    · intro m hm
      fin_cases m
      · show 3 * (v 0 * w 0) = ip v w
        linear_combination (3) * hy0
      · exact (hm rfl).elim
      · show 3 * (v 2 * w 2) = ip v w
        linear_combination (3) * a2 + (3) * hy0
      · show 3 * (v 3 * w 3) = ip v w
        linear_combination (3) * a3 + (3) * hy0
  · exfalso
    apply hg
    linear_combination (3) * a2 + (1/2) * a1 + (1/2) * a3 + (-3) * hs
  · exfalso
    apply hg
    linear_combination (3) * a3 + (1/2) * a1 + (1/2) * a2 + (-3) * hs
  · right
    have hy0 : v 0 * w 0 = 0 := by
      linear_combination (-1/2) * hs + (1/12) * a1 + (1/12) * a2 + (1/12) * a3
    refine ⟨0, ?_, ?_, ?_⟩
    · have e : ip v w * v 0 = 0 := by
        linear_combination (-3) * sv + (ip v w) * hv + (3*v 0 - 3*v 1 - 3*v 2 - 3*v 3) * hy0 + (v 1/2) * a1 + (v 2/2) * a2 + (v 3/2) * a3
      exact (mul_eq_zero.mp e).resolve_left hg
    · have e : ip v w * w 0 = 0 := by
        linear_combination (-3) * sw + (ip v w) * hw + (3*w 0 - 3*w 1 - 3*w 2 - 3*w 3) * hy0 + (w 1/2) * a1 + (w 2/2) * a2 + (w 3/2) * a3
      exact (mul_eq_zero.mp e).resolve_left hg
    · intro m hm
      fin_cases m
      · exact (hm rfl).elim
      · show 3 * (v 1 * w 1) = ip v w
        linear_combination (1/2) * a1 + (-3) * hy0
      · show 3 * (v 2 * w 2) = ip v w
        linear_combination (1/2) * a2 + (-3) * hy0
      · show 3 * (v 3 * w 3) = ip v w
        linear_combination (1/2) * a3 + (-3) * hy0

theorem ip_ne_of_line (v w : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hw1 : tau w = 0) (hw2 : ip w w = 0) (hind : ∀ c : ℂ, w ≠ c • v) : ip v w ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := Q4 v w hv0 hv1 hv2 hw1 hw2 h
  exact hind c hc

theorem rel_prop (a b c : V4) (ha1 : tau a = 0) (ha2 : ip a a = 0) (hb1 : tau b = 0)
    (hb2 : ip b b = 0) (hc1 : tau c = 0) (hc2 : ip c c = 0) (r1 : t3 a a b = 0) (r2 : t3 a b b = 0)
    (r3 : t3 a a c = 0) (r4 : t3 a c c = 0) (hab : ip a b ≠ 0) (hac : ip a c ≠ 0) :
    ∀ m, ip a c * b m = ip a b * c m := by
  have Rb := pair_rel a b ha1 hb1 ha2 hb2 r1 r2 hab
  have Rc := pair_rel a c ha1 hc1 ha2 hc2 r3 r4 hac
  rcases Rb with hb | ⟨k, hak, hbk, hb3⟩ <;> rcases Rc with hc | ⟨k', hak', hck', hc3⟩
  · intro m
    have e1 := hb m
    have e2 := hc m
    have ham : a m ≠ 0 := by
      intro h
      rw [h, zero_mul] at e1
      exact hab (by linear_combination (-4 : ℂ) * e1)
    have e : a m * (ip a c * b m - ip a b * c m) = 0 := by
      linear_combination ip a c * e1 - ip a b * e2
    have e' := (mul_eq_zero.mp e).resolve_left ham
    linear_combination e'
  · exfalso
    have e1 := hb k'
    rw [hak', zero_mul] at e1
    exact hab (by linear_combination (-4 : ℂ) * e1)
  · exfalso
    have e2 := hc k
    rw [hak, zero_mul] at e2
    exact hac (by linear_combination (-4 : ℂ) * e2)
  · have hkk : k' = k := by
      by_contra h
      have e := hb3 k' h
      rw [hak', zero_mul, mul_zero] at e
      exact hab e.symm
    rw [hkk] at hck' hc3
    intro m
    by_cases hm : m = k
    · rw [hm, hbk, hck', mul_zero, mul_zero]
    · have e1 := hb3 m hm
      have e2 := hc3 m hm
      have ham : a m ≠ 0 := by
        intro h
        rw [h, zero_mul, mul_zero] at e1
        exact hab e1.symm
      have e : a m * (ip a c * b m - ip a b * c m) = 0 := by
        linear_combination (1 / 3 : ℂ) * (ip a c * e1 - ip a b * e2)
      have e' := (mul_eq_zero.mp e).resolve_left ham
      linear_combination e'

theorem no_triangle (a b c : V4) (ha1 : tau a = 0) (ha2 : ip a a = 0) (hb1 : tau b = 0)
    (hb2 : ip b b = 0) (hc1 : tau c = 0) (hc2 : ip c c = 0) (r1 : t3 a a b = 0) (r2 : t3 a b b = 0)
    (r3 : t3 a a c = 0) (r4 : t3 a c c = 0) (hab : ip a b ≠ 0) (hac : ip a c ≠ 0)
    (hbc : ip b c ≠ 0) : False := by
  have P := rel_prop a b c ha1 ha2 hb1 hb2 hc1 hc2 r1 r2 r3 r4 hab hac
  have p0 := P 0
  have p1 := P 1
  have p2 := P 2
  have p3 := P 3
  have q1 : ip b c = b 0 * c 0 + b 1 * c 1 + b 2 * c 2 + b 3 * c 3 := rfl
  have q2 : b 0 * b 0 + b 1 * b 1 + b 2 * b 2 + b 3 * b 3 = 0 := hb2
  have e : ip a b * ip b c = 0 := by
    linear_combination ip a b * q1 - b 0 * p0 - b 1 * p1 - b 2 * p2 - b 3 * p3 + ip a c * q2
  exact hbc ((mul_eq_zero.mp e).resolve_left hab)

theorem two_equal (v w : V4) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (h3 : t3 v v v = 0) (h21 : t3 v v w = 0) (h12 : t3 v w w = 0)
    (hg : ip v w ≠ 0) (hv0 : v ≠ 0) : 3 * t4 v v w w - ip v w ^ 2 ≠ 0 := by
  rcases pair_rel v w hv1 hw1 hv2 hw2 h21 h12 hg with hA | ⟨k, hvk, -, -⟩
  · have q : t4 v v w w = (v 0 * w 0) ^ 2 + (v 1 * w 1) ^ 2 + (v 2 * w 2) ^ 2 + (v 3 * w 3) ^ 2 := by
      simp only [t4]
      ring
    have e : 3 * t4 v v w w - ip v w ^ 2 = -(ip v w ^ 2 / 4) := by
      rw [q, hA 0, hA 1, hA 2, hA 3]
      ring
    rw [e]
    intro h
    apply hg
    have h' : ip v w ^ 2 = 0 := by linear_combination (-4 : ℂ) * h
    exact (pow_eq_zero_iff (by norm_num)).mp h'
  · exfalso
    apply hv0
    have hk := chi_pow v hv1 hv2 h3
    have hp : v 0 * v 1 * v 2 * v 3 = 0 := by
      have e := hk k
      rw [hvk] at e
      linear_combination e
    funext m
    have e := hk m
    rw [hp, neg_zero] at e
    exact (pow_eq_zero_iff (by norm_num)).mp e

theorem three_equal (v : V4) (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0)
    (h4 : t4 v v v v = 0) : v = 0 := by
  have hk := chi_pow v h1 h2 h3
  have hp : v 0 * v 1 * v 2 * v 3 = 0 := by
    have e : t4 v v v v = v 0 ^ 4 + v 1 ^ 4 + v 2 ^ 4 + v 3 ^ 4 := by
      simp only [t4]
      ring
    rw [e, hk 0, hk 1, hk 2, hk 3] at h4
    linear_combination (-1 / 4 : ℂ) * h4
  funext m
  have e := hk m
  rw [hp, neg_zero] at e
  exact (pow_eq_zero_iff (by norm_num)).mp e

def cubN (a b c : V4) : ℂ :=
  t3 a a b + t3 a a c + t3 b b a + t3 b b c + t3 c c a + t3 c c b + t3 a b c

def quaN (a b c : V4) : ℂ :=
  3 * (t4 a a b c + t4 b b a c + t4 c c a b) - (ip a b * ip a c + ip b a * ip b c + ip c a * ip c b)

def nbarL : M45 →ₗ[ℂ] V4 × (V4 × V4) := (colL 2).prod ((colL 3).prod (colL 4))

theorem nbarL_apply (Z : M45) : nbarL Z = (col Z 2, (col Z 3, col Z 4)) := rfl

theorem cubN_swap (a b c : V4) : cubN a b c = cubN a c b := by
  simp only [cubN, t3]
  ring

theorem cubN_cyc (a b c : V4) : cubN a b c = cubN b c a := by
  simp only [cubN, t3]
  ring

theorem quaN_swap (a b c : V4) : quaN a b c = quaN a c b := by
  simp only [quaN, t4, ip]
  ring

theorem quaN_cyc (a b c : V4) : quaN a b c = quaN b c a := by
  simp only [quaN, t4, ip]
  ring

theorem cub_rels (a b c : V4) (H : ∀ l2 l3 l4 : ℂ, cubN (l2 • a) (l3 • b) (l4 • c) = 0) :
    t3 a a b = 0 ∧ t3 a b b = 0 ∧ t3 a a c = 0 ∧ t3 a c c = 0 ∧ t3 b b c = 0 ∧ t3 b c c = 0 := by
  have e1 := H 1 1 0
  have e2 := H 1 2 0
  have e3 := H 1 0 1
  have e4 := H 1 0 2
  have e5 := H 0 1 1
  have e6 := H 0 1 2
  simp only [cubN, t3, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 e5 e6 ⊢
  exact ⟨by linear_combination 2 * e1 - (1 / 2 : ℂ) * e2,
    by linear_combination (1 / 2 : ℂ) * e2 - e1,
    by linear_combination 2 * e3 - (1 / 2 : ℂ) * e4,
    by linear_combination (1 / 2 : ℂ) * e4 - e3,
    by linear_combination 2 * e5 - (1 / 2 : ℂ) * e6,
    by linear_combination (1 / 2 : ℂ) * e6 - e5⟩

theorem cub_two (v w : V4) (H : ∀ l2 l3 l4 : ℂ, cubN (l2 • v) (l3 • v) (l4 • w) = 0) :
    t3 v v v = 0 ∧ t3 v v w = 0 ∧ t3 v w w = 0 := by
  have e1 := H 1 1 0
  have e2 := H 1 0 1
  have e3 := H 1 0 2
  simp only [cubN, t3, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  exact ⟨by linear_combination (1 / 2 : ℂ) * e1,
    by linear_combination 2 * e2 - (1 / 2 : ℂ) * e3,
    by linear_combination (1 / 2 : ℂ) * e3 - e2⟩

theorem quart_two (v w : V4) (H : ∀ l2 l3 l4 : ℂ, quaN (l2 • v) (l3 • v) (l4 • w) = 0) :
    3 * t4 v v w w - ip v w ^ 2 = 0 := by
  have e1 := H 1 1 1
  have e2 := H 1 1 2
  simp only [quaN, t4, ip, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  linear_combination (1 / 2 : ℂ) * e2 - e1

theorem three_rels (v : V4) (hvv : ip v v = 0)
    (HC : ∀ l2 l3 l4 : ℂ, cubN (l2 • v) (l3 • v) (l4 • v) = 0)
    (HQ : ∀ l2 l3 l4 : ℂ, quaN (l2 • v) (l3 • v) (l4 • v) = 0) :
    t3 v v v = 0 ∧ t4 v v v v = 0 := by
  have e1 := HC 1 1 0
  have e2 := HQ 1 1 1
  simp only [cubN, quaN, t3, t4, ip, Pi.smul_apply, smul_eq_mul] at e1 e2 hvv ⊢
  exact ⟨by linear_combination (1 / 2 : ℂ) * e1,
    by linear_combination (1 / 9 : ℂ) * e2
      + (1 / 3 : ℂ) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) * hvv⟩

theorem fin_le_two (S : Submodule ℂ (V4 × (V4 × V4))) (y z : V4 × (V4 × V4))
    (h : ∀ s ∈ S, ∃ a b : ℂ, s = a • y + b • z) : Module.finrank ℂ S ≤ 2 := by
  have hle : S ≤ Submodule.span ℂ (Set.range ![y, z]) := by
    intro s hs
    obtain ⟨a, b, rfl⟩ := h s hs
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨![a, b], by simp [Fin.sum_univ_two]⟩
  have h2 := (Submodule.finrank_mono hle).trans (finrank_range_le_card ![y, z])
  simpa using h2

theorem smul_mul_eq (a b : ℂ) (x y : V4) (h : y = b • x) : (b * a) • x = a • y := by
  rw [h, smul_smul, mul_comm]

theorem TC5_P3 (K : Submodule ℂ M45) (hdef : DefLine K mTC) :
    Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL) ≤ 2 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨v2, t2, i2, L2⟩ := NB_lines K hdef 2 (Or.inl rfl)
  obtain ⟨v3, t3', i3, L3⟩ := NB_lines K hdef 3 (Or.inr (Or.inl rfl))
  obtain ⟨v4, t4', i4, L4⟩ := NB_lines K hdef 4 (Or.inr (Or.inr rfl))
  have hrep : ∀ s ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL,
      ∃ c2 c3 c4 : ℂ, s = (c2 • v2, (c3 • v3, c4 • v4)) := by
    rintro _ ⟨Z, hZ, rfl⟩
    have h := Submodule.mem_inf.mp hZ
    have h0 : rs Z = 0 := LinearMap.mem_ker.mp h.2
    obtain ⟨c2, e2⟩ := L2 Z h.1 h0
    obtain ⟨c3, e3⟩ := L3 Z h.1 h0
    obtain ⟨c4, e4⟩ := L4 Z h.1 h0
    exact ⟨c2, c3, c4, by rw [nbarL_apply, e2, e3, e4]⟩
  have hv2 : v2 ≠ 0 := by
    intro h
    apply absurd hlt
    push_neg
    apply fin_le_two _ ((0 : V4), (v3, (0 : V4))) ((0 : V4), ((0 : V4), v4))
    intro s hs
    obtain ⟨c2, c3, c4, rfl⟩ := hrep s hs
    refine ⟨c3, c4, ?_⟩
    rw [h]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, zero_add, add_zero]
  have hv3 : v3 ≠ 0 := by
    intro h
    apply absurd hlt
    push_neg
    apply fin_le_two _ (v2, ((0 : V4), (0 : V4))) ((0 : V4), ((0 : V4), v4))
    intro s hs
    obtain ⟨c2, c3, c4, rfl⟩ := hrep s hs
    refine ⟨c2, c4, ?_⟩
    rw [h]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, zero_add, add_zero]
  have hv4 : v4 ≠ 0 := by
    intro h
    apply absurd hlt
    push_neg
    apply fin_le_two _ (v2, ((0 : V4), (0 : V4))) ((0 : V4), (v3, (0 : V4)))
    intro s hs
    obtain ⟨c2, c3, c4, rfl⟩ := hrep s hs
    refine ⟨c2, c3, ?_⟩
    rw [h]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, zero_add, add_zero]
  have hS : (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL =
      Submodule.span ℂ (Set.range ![(v2, ((0 : V4), (0 : V4))), ((0 : V4), (v3, (0 : V4))),
        ((0 : V4), ((0 : V4), v4))]) := by
    apply Submodule.eq_of_le_of_finrank_le
    · intro s hs
      obtain ⟨c2, c3, c4, rfl⟩ := hrep s hs
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![c2, c3, c4], ?_⟩
      simp [Fin.sum_univ_three]
    · have h3 := finrank_range_le_card (R := ℂ) ![(v2, ((0 : V4), (0 : V4))), ((0 : V4), (v3, (0 : V4))),
        ((0 : V4), ((0 : V4), v4))]
      simp only [Fintype.card_fin, Set.finrank] at h3
      omega
  have hreal : ∀ l2 l3 l4 : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l2 • v2 ∧ col Z 3 = l3 • v3 ∧
      col Z 4 = l4 • v4 := by
    intro l2 l3 l4
    have hm : ((l2 • v2, (l3 • v3, l4 • v4)) : V4 × (V4 × V4)) ∈
        (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL := by
      rw [hS, Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![l2, l3, l4], ?_⟩
      simp [Fin.sum_univ_three]
    obtain ⟨Z, hZ, hZe⟩ := Submodule.mem_map.mp hm
    have h := Submodule.mem_inf.mp hZ
    rw [nbarL_apply, Prod.mk.injEq, Prod.mk.injEq] at hZe
    exact ⟨Z, h.1, LinearMap.mem_ker.mp h.2, hZe.1, hZe.2.1, hZe.2.2⟩
  have HC : ∀ l2 l3 l4 : ℂ, cubN (l2 • v2) (l3 • v3) (l4 • v4) = 0 := by
    intro l2 l3 l4
    obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hreal l2 l3 l4
    have e := (nbar_eqs K hdef Z hZ h0).1
    rw [e2, e3, e4] at e
    exact e
  have HQ : ∀ l2 l3 l4 : ℂ, quaN (l2 • v2) (l3 • v3) (l4 • v4) = 0 := by
    intro l2 l3 l4
    obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hreal l2 l3 l4
    have e := (nbar_eqs K hdef Z hZ h0).2
    rw [e2, e3, e4] at e
    exact e
  have hpar : ∀ (x y : V4), x ≠ 0 → y ≠ 0 → tau x = 0 → ip x x = 0 → tau y = 0 →
      ip y y = 0 → ¬ (∃ c : ℂ, y = c • x) → ip x y ≠ 0 := by
    intro x y hx hy tx ix ty iy hn
    apply ip_ne_of_line x y hx tx ix ty iy
    intro c hc
    exact hn ⟨c, hc⟩
  by_cases p23 : ∃ c : ℂ, v3 = c • v2
  · obtain ⟨c, hc⟩ := p23
    have hc0 : c ≠ 0 := by
      intro h
      apply hv3
      rw [hc, h, zero_smul]
    by_cases p24 : ∃ d : ℂ, v4 = d • v2
    · obtain ⟨d, hd⟩ := p24
      have hd0 : d ≠ 0 := by
        intro h
        apply hv4
        rw [hd, h, zero_smul]
      have hu0 : (c * d) • v2 ≠ 0 := by
        intro h
        rcases smul_eq_zero.mp h with h' | h'
        · exact mul_ne_zero hc0 hd0 h'
        · exact hv2 h'
      have hconv : ∀ m2 m3 m4 : ℂ, (c * d * m2) • v2 = m2 • ((c * d) • v2) ∧
          (d * m3) • v3 = m3 • ((c * d) • v2) ∧ (c * m4) • v4 = m4 • ((c * d) • v2) := by
        intro m2 m3 m4
        refine ⟨?_, ?_, ?_⟩
        · rw [smul_smul]
          congr 1
          ring
        · rw [hc, smul_smul, smul_smul]
          congr 1
          ring
        · rw [hd, smul_smul, smul_smul]
          congr 1
          ring
      have HC' : ∀ m2 m3 m4 : ℂ,
          cubN (m2 • ((c * d) • v2)) (m3 • ((c * d) • v2)) (m4 • ((c * d) • v2)) = 0 := by
        intro m2 m3 m4
        obtain ⟨q2, q3, q4⟩ := hconv m2 m3 m4
        have e := HC (c * d * m2) (d * m3) (c * m4)
        rw [q2, q3, q4] at e
        exact e
      have HQ' : ∀ m2 m3 m4 : ℂ,
          quaN (m2 • ((c * d) • v2)) (m3 • ((c * d) • v2)) (m4 • ((c * d) • v2)) = 0 := by
        intro m2 m3 m4
        obtain ⟨q2, q3, q4⟩ := hconv m2 m3 m4
        have e := HQ (c * d * m2) (d * m3) (c * m4)
        rw [q2, q3, q4] at e
        exact e
      have hτu : tau ((c * d) • v2) = 0 := by
        simp only [tau, Pi.smul_apply, smul_eq_mul] at t2 ⊢
        linear_combination (c * d) * t2
      have hiu : ip ((c * d) • v2) ((c * d) • v2) = 0 := by
        simp only [ip, Pi.smul_apply, smul_eq_mul] at i2 ⊢
        linear_combination (c * d) ^ 2 * i2
      obtain ⟨r3, r4⟩ := three_rels _ hiu HC' HQ'
      exact hu0 (three_equal _ hτu hiu r3 r4)
    · have HC' : ∀ m2 m3 m4 : ℂ, cubN (m2 • v3) (m3 • v3) (m4 • v4) = 0 := by
        intro m2 m3 m4
        have e := HC (c * m2) m3 m4
        rw [smul_mul_eq m2 c v2 v3 hc] at e
        exact e
      have HQ' : ∀ m2 m3 m4 : ℂ, quaN (m2 • v3) (m3 • v3) (m4 • v4) = 0 := by
        intro m2 m3 m4
        have e := HQ (c * m2) m3 m4
        rw [smul_mul_eq m2 c v2 v3 hc] at e
        exact e
      have hn : ¬ ∃ e : ℂ, v4 = e • v3 := by
        rintro ⟨e, he⟩
        exact p24 ⟨e * c, by rw [he, hc, smul_smul]⟩
      obtain ⟨r3, r21, r12⟩ := cub_two v3 v4 HC'
      exact two_equal v3 v4 t3' i3 t4' i4 r3 r21 r12 (hpar v3 v4 hv3 hv4 t3' i3 t4' i4 hn) hv3
        (quart_two v3 v4 HQ')
  · by_cases p24 : ∃ d : ℂ, v4 = d • v2
    · obtain ⟨d, hd⟩ := p24
      have HC' : ∀ m2 m3 m4 : ℂ, cubN (m2 • v4) (m3 • v4) (m4 • v3) = 0 := by
        intro m2 m3 m4
        have e := HC (d * m2) m4 m3
        rw [smul_mul_eq m2 d v2 v4 hd, cubN_swap] at e
        exact e
      have HQ' : ∀ m2 m3 m4 : ℂ, quaN (m2 • v4) (m3 • v4) (m4 • v3) = 0 := by
        intro m2 m3 m4
        have e := HQ (d * m2) m4 m3
        rw [smul_mul_eq m2 d v2 v4 hd, quaN_swap] at e
        exact e
      have hn : ¬ ∃ e : ℂ, v3 = e • v4 := by
        rintro ⟨e, he⟩
        exact p23 ⟨e * d, by rw [he, hd, smul_smul]⟩
      obtain ⟨r3, r21, r12⟩ := cub_two v4 v3 HC'
      exact two_equal v4 v3 t4' i4 t3' i3 r3 r21 r12 (hpar v4 v3 hv4 hv3 t4' i4 t3' i3 hn) hv4
        (quart_two v4 v3 HQ')
    · by_cases p34 : ∃ e : ℂ, v4 = e • v3
      · obtain ⟨e, he⟩ := p34
        have HC' : ∀ m2 m3 m4 : ℂ, cubN (m2 • v4) (m3 • v4) (m4 • v2) = 0 := by
          intro m2 m3 m4
          have h := HC m4 (e * m2) m3
          rw [smul_mul_eq m2 e v3 v4 he, cubN_cyc] at h
          exact h
        have HQ' : ∀ m2 m3 m4 : ℂ, quaN (m2 • v4) (m3 • v4) (m4 • v2) = 0 := by
          intro m2 m3 m4
          have h := HQ m4 (e * m2) m3
          rw [smul_mul_eq m2 e v3 v4 he, quaN_cyc] at h
          exact h
        have hn : ¬ ∃ f : ℂ, v2 = f • v4 := by
          rintro ⟨f, hf⟩
          have hf0 : f ≠ 0 := by
            intro h
            apply hv2
            rw [hf, h, zero_smul]
          exact p24 ⟨f⁻¹, by rw [hf, smul_smul, inv_mul_cancel₀ hf0, one_smul]⟩
        obtain ⟨r3, r21, r12⟩ := cub_two v4 v2 HC'
        exact two_equal v4 v2 t4' i4 t2 i2 r3 r21 r12 (hpar v4 v2 hv4 hv2 t4' i4 t2 i2 hn) hv4
          (quart_two v4 v2 HQ')
      · obtain ⟨r1, r2, r3, r4, -, -⟩ := cub_rels v2 v3 v4 HC
        exact no_triangle v2 v3 v4 t2 i2 t3' i3 t4' i4 r1 r2 r3 r4
          (hpar v2 v3 hv2 hv3 t2 i2 t3' i3 p23) (hpar v2 v4 hv2 hv4 t2 i2 t4' i4 p24)
          (hpar v3 v4 hv3 hv4 t3' i3 t4' i4 p34)

theorem nbar_ker (Z : M45) (h0 : rs Z = 0) (h2 : col Z 2 = 0) (h3 : col Z 3 = 0) (h4 : col Z 4 = 0) :
    uY Z = 0 := by
  funext k
  have e := congrFun h0 k
  rw [rs_apply] at e
  have e' : Z (k, 0) + Z (k, 1) + Z (k, 2) + Z (k, 3) + Z (k, 4) = 0 := e
  have w2 : Z (k, 2) = 0 := congrFun h2 k
  have w3 : Z (k, 3) = 0 := congrFun h3 k
  have w4 : Z (k, 4) = 0 := congrFun h4 k
  show (Z (k, 0) + Z (k, 1)) / 2 = 0
  linear_combination (1 / 2 : ℂ) * (e' - w2 - w3 - w4)

theorem TC5_dims (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K) :
    Module.finrank ℂ K = 5 ∧ Module.finrank ℂ (K.map rs) = 2 ∧
      Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL) = 2 ∧
      ∃ z : V4, z ≠ 0 ∧ zE z ∈ K := by
  have hq2 := (TC5_P2 K hdef hK5).1
  have hN2 := TC5_P3 K hdef
  have r1 := rank_nullity K rs
  have r2 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) nbarL
  have hfacts : ∀ Z ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker nbarL : Submodule ℂ M45),
      Z ∈ K ∧ Z = zE (dY Z) := by
    intro Z hZ
    have h1 := Submodule.mem_inf.mp hZ
    have h2 := Submodule.mem_inf.mp h1.1
    have h0 : rs Z = 0 := LinearMap.mem_ker.mp h2.2
    have hn : nbarL Z = 0 := LinearMap.mem_ker.mp h1.2
    rw [nbarL_apply] at hn
    have c2 : col Z 2 = 0 := congrArg Prod.fst hn
    have c3 : col Z 3 = 0 := congrArg (fun p => p.2.1) hn
    have c4 : col Z 4 = 0 := congrArg (fun p => p.2.2) hn
    exact ⟨h2.1, Z_of_nbar Z c2 c3 c4 (nbar_ker Z h0 c2 c3 c4)⟩
  have hW : ∀ z ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker nbarL : Submodule ℂ M45).map dYL,
      zE z ∈ K := by
    rintro _ ⟨Z, hZ, rfl⟩
    obtain ⟨hK, hZe⟩ := hfacts Z hZ
    rw [dYL_apply, ← hZe]
    exact hK
  have h1 := zeta_le_one K hdef hK5 _ hW
  have hker : (((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker nbarL) ⊓ LinearMap.ker dYL :
      Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hZ1 := (Submodule.mem_inf.mp hZ).1
    have hd : dY Z = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2
    obtain ⟨-, hZe⟩ := hfacts Z hZ1
    rw [hZe, hd]
    funext p
    obtain ⟨k, j⟩ := p
    simp [zE]
  have r3 := rank_nullity ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker nbarL : Submodule ℂ M45) dYL
  rw [hker, finrank_bot] at r3
  have hz : 1 ≤ Module.finrank ℂ
      ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker nbarL : Submodule ℂ M45) := by omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  by_contra hc
  push_neg at hc
  have hbot : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker nbarL : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    obtain ⟨hK, hZe⟩ := hfacts Z hZ
    by_cases hd : dY Z = 0
    · rw [hZe, hd]
      funext p
      obtain ⟨k, j⟩ := p
      simp [zE]
    · have hK' : zE (dY Z) ∈ K := by
        rw [← hZe]
        exact hK
      exact (hc (dY Z) hd hK').elim
  rw [hbot, finrank_bot] at hz
  omega

theorem S_radical (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K) :
    ∃ n0 : V4, n0 ≠ 0 ∧ tau n0 = 0 ∧ ip n0 n0 = 0 ∧ n0 ∈ K.map rs ∧
      ∀ s ∈ K.map rs, ip n0 s = 0 := by
  obtain ⟨-, hq, -, -⟩ := TC5_dims K hdef hK5
  have hG := (TC5_P2 K hdef hK5).2.1
  obtain ⟨a, ha, b, hb, hind⟩ := two_indep (K.map rs) (by omega)
  obtain ⟨Y1, hY1, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨Y2, hY2, rfl⟩ := Submodule.mem_map.mp hb
  have hD := hG Y1 hY1 Y2 hY2
  have hτ1 := (TC5_tau K hdef Y1 hY1).2.2.2.2
  have hτ2 := (TC5_tau K hdef Y2 hY2).2.2.2.2
  have ha0 : rs Y1 ≠ 0 := by
    intro h
    have := hind 1 0 (by rw [h]; simp)
    exact one_ne_zero this.1
  have hspan : ∀ s ∈ K.map rs, ∃ x y : ℂ, s = x • rs Y1 + y • rs Y2 := by
    have hlt : Submodule.span ℂ {rs Y1} < Submodule.span ℂ {rs Y1, rs Y2} := by
      refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
      intro h
      have h2 : rs Y2 ∈ Submodule.span ℂ {rs Y1} := by
        rw [h]
        exact Submodule.subset_span (by simp)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
      have := hind c (-1) (by rw [hc]; simp)
      exact one_ne_zero (neg_eq_zero.mp this.2)
    have hle : Submodule.span ℂ {rs Y1, rs Y2} ≤ K.map rs := by
      rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have h1 : Module.finrank ℂ (Submodule.span ℂ {rs Y1}) = 1 := finrank_span_singleton ha0
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro s hs
    rw [← heq] at hs
    obtain ⟨x, y, h⟩ := Submodule.mem_span_pair.mp hs
    exact ⟨x, y, h.symm⟩
  have hperp : ∀ n : V4, ip n (rs Y1) = 0 → ip n (rs Y2) = 0 → ∀ s ∈ K.map rs, ip n s = 0 := by
    intro n h1 h2 s hs
    obtain ⟨x, y, rfl⟩ := hspan s hs
    simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination x * h1 + y * h2
  by_cases hc : ip (rs Y2) (rs Y2) = 0 ∧ ip (rs Y1) (rs Y2) = 0
  · have hb0 : rs Y2 ≠ 0 := by
      intro h
      have := hind 0 1 (by rw [h]; simp)
      exact one_ne_zero this.2
    have p1 : ip (rs Y2) (rs Y1) = 0 := by
      have e := hc.2
      simp only [ip] at e ⊢
      linear_combination e
    exact ⟨rs Y2, hb0, hτ2, hc.1, hb, hperp _ p1 hc.1⟩
  · refine ⟨ip (rs Y2) (rs Y2) • rs Y1 + (-(ip (rs Y1) (rs Y2))) • rs Y2, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨e1, e2⟩ := hind _ _ h
      exact hc ⟨e1, neg_eq_zero.mp e2⟩
    · simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hτ1 hτ2 ⊢
      linear_combination ip (rs Y2) (rs Y2) * hτ1 - ip (rs Y1) (rs Y2) * hτ2
    · have q1 : ip (ip (rs Y2) (rs Y2) • rs Y1 + (-(ip (rs Y1) (rs Y2))) • rs Y2) (rs Y1) = 0 := by
        have e : ip (ip (rs Y2) (rs Y2) • rs Y1 + (-(ip (rs Y1) (rs Y2))) • rs Y2) (rs Y1) =
            ip (rs Y1) (rs Y1) * ip (rs Y2) (rs Y2) - ip (rs Y1) (rs Y2) ^ 2 := by
          simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        exact hD
      have q2 : ip (ip (rs Y2) (rs Y2) • rs Y1 + (-(ip (rs Y1) (rs Y2))) • rs Y2) (rs Y2) = 0 := by
        simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      exact hperp _ q1 q2 _ ((K.map rs).add_mem ((K.map rs).smul_mem _ ha)
        ((K.map rs).smul_mem _ hb))
    · exact (K.map rs).add_mem ((K.map rs).smul_mem _ ha) ((K.map rs).smul_mem _ hb)
    · intro s hs
      have q1 : ip (ip (rs Y2) (rs Y2) • rs Y1 + (-(ip (rs Y1) (rs Y2))) • rs Y2) (rs Y1) = 0 := by
        have e : ip (ip (rs Y2) (rs Y2) • rs Y1 + (-(ip (rs Y1) (rs Y2))) • rs Y2) (rs Y1) =
            ip (rs Y1) (rs Y1) * ip (rs Y2) (rs Y2) - ip (rs Y1) (rs Y2) ^ 2 := by
          simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        exact hD
      have q2 : ip (ip (rs Y2) (rs Y2) • rs Y1 + (-(ip (rs Y1) (rs Y2))) • rs Y2) (rs Y2) = 0 := by
        simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      exact hperp _ q1 q2 s hs

theorem tau_smul (a : ℂ) (x : V4) : tau (a • x) = a * tau x := by
  simp only [tau, Pi.smul_apply, smul_eq_mul]
  ring

theorem rs_zE (z : V4) : rs (zE z) = 0 := by
  funext k
  rw [rs_apply, zE0, zE1]
  simp [zE]

theorem e2_comb (x y : V4) (s t : ℂ) :
    e2 (s • x + t • y) = s ^ 2 * e2 x + 2 * s * t * e2b x y + t ^ 2 * e2 y := by
  simp only [e2, e2b, tau, ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem e2b_comb (x y : V4) (s t a b : ℂ) :
    e2b (s • x + t • y) (a • x + b • y) = s * a * e2 x + (s * b + t * a) * e2b x y + t * b * e2 y := by
  simp only [e2, e2b, tau, ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Ed_comb (x y : V4) (s t : ℂ) :
    Ed (s • x + t • y) = fun k => s ^ 2 * Ed x k + 2 * s * t * Edb x y k + t ^ 2 * Ed y k := by
  funext k
  simp only [Ed, Edb, e2, e2b, tau, ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Edb_comb (x y : V4) (s t a b : ℂ) :
    Edb (s • x + t • y) (a • x + b • y) =
      fun k => s * a * Ed x k + (s * b + t * a) * Edb x y k + t * b * Ed y k := by
  funext k
  simp only [Ed, Edb, e2, e2b, tau, ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem LAG_pair (n : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, n i ^ 4 = kap) (hn1 : tau n = 0)
    (hn2 : ip n n = 0) (hn3 : t3 n n n = 0) (d1 d2 : V4)
    (hind : ∀ s t : ℂ, s • d1 + t • d2 = 0 → s = 0 ∧ t = 0) (q1 : e2 d1 = 0) (q2 : e2 d2 = 0)
    (q12 : e2b d1 d2 = 0) (E1 : ip n (Ed d1) = 0) (E2 : ip n (Ed d2) = 0)
    (E12 : ip n (Edb d1 d2) = 0) : False := by
  have key : ∀ s t a b : ℂ, e2 (s • d1 + t • d2) = 0 ∧ e2 (a • d1 + b • d2) = 0 ∧
      e2b (s • d1 + t • d2) (a • d1 + b • d2) = 0 ∧ ip n (Ed (s • d1 + t • d2)) = 0 ∧
      ip n (Edb (s • d1 + t • d2) (a • d1 + b • d2)) = 0 := by
    intro s t a b
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e2_comb, q1, q2, q12]
      ring
    · rw [e2_comb, q1, q2, q12]
      ring
    · rw [e2b_comb, q1, q2, q12]
      ring
    · rw [Ed_comb]
      simp only [ip] at E1 E2 E12 ⊢
      linear_combination s ^ 2 * E1 + 2 * s * t * E12 + t ^ 2 * E2
    · rw [Edb_comb]
      simp only [ip] at E1 E2 E12 ⊢
      linear_combination s * a * E1 + (s * b + t * a) * E12 + t * b * E2
  have htau : ∀ s t : ℂ, tau (s • d1 + t • d2) = s * tau d1 + t * tau d2 := by
    intro s t
    simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hne : ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → s • d1 + t • d2 ≠ 0 := by
    intro s t h h0
    obtain ⟨e1, e2'⟩ := hind s t h0
    rcases h with h | h
    · exact h e1
    · exact h e2'
  have finish : ∀ s t a b : ℂ, (s ≠ 0 ∨ t ≠ 0) → s * tau d1 + t * tau d2 = 0 →
      a * tau d1 + b * tau d2 = 1 → False := by
    intro s t a b hst h0 h1
    obtain ⟨k1, k2, k3, k4, k5⟩ := key s t a b
    apply LAG_b n kap hkap hk hn1 hn2 hn3 (s • d1 + t • d2) (a • d1 + b • d2) (hne s t hst)
      (by rw [htau]; exact h0) k1 (by rw [htau]; exact h1) k2 k3
    exact ⟨k4, k5⟩
  by_cases ht2 : tau d2 = 0
  · by_cases ht1 : tau d1 = 0
    · have i1 := e2_ip d1 ht1 q1
      have i2 := e2_ip d2 ht2 q2
      have i12 : ip d1 d2 = 0 := by
        simp only [e2b] at q12
        rw [ht1, ht2] at q12
        linear_combination (-2 : ℂ) * q12
      have hd1 : d1 ≠ 0 := by
        have := hne 1 0 (Or.inl one_ne_zero)
        intro h
        apply this
        rw [h]
        simp
      obtain ⟨c, hc⟩ := Q4 d1 d2 hd1 ht1 i1 ht2 i2 i12
      have := hind c (-1) (by
        rw [hc]
        funext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        ring)
      exact one_ne_zero (neg_eq_zero.mp this.2)
    · exact finish 0 1 (tau d1)⁻¹ 0 (Or.inr one_ne_zero) (by rw [ht2]; ring)
        (by rw [inv_mul_cancel₀ ht1]; ring)
  · exact finish 1 (-(tau d1 / tau d2)) 0 (tau d2)⁻¹ (Or.inl one_ne_zero)
      (by linear_combination (-(tau d1)) * inv_mul_cancel₀ ht2)
      (by rw [inv_mul_cancel₀ ht2]; ring)

theorem X3c_line (v : V4) (hv1 : tau v = 0) (hv3 : t3 v v v = 0) (a b c d : ℂ) :
    X3c (a • v) (b • v) (c • v) (d • v) = 0 := by
  simp only [X3c, tau_smul, t3_smul3, hv1, hv3, mul_zero, zero_mul, sub_zero, add_zero]

theorem uY_of_rs (Z : M45) (h0 : rs Z = 0) (v : V4) (c2 c3 c4 : ℂ) (h2 : col Z 2 = c2 • v)
    (h3 : col Z 3 = c3 • v) (h4 : col Z 4 = c4 • v) : uY Z = (-(c2 + c3 + c4) / 2) • v := by
  funext k
  have e := congrFun h0 k
  rw [rs_apply] at e
  have e' : Z (k, 0) + Z (k, 1) + Z (k, 2) + Z (k, 3) + Z (k, 4) = 0 := e
  have g2 := congrFun h2 k
  have g3 := congrFun h3 k
  have g4 := congrFun h4 k
  simp only [col, Pi.smul_apply, smul_eq_mul] at g2 g3 g4
  simp only [uY, Pi.smul_apply, smul_eq_mul]
  linear_combination (1 / 2 : ℂ) * e' - (1 / 2 : ℂ) * (g2 + g3 + g4)

theorem DN_line (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv1 : tau v = 0)
    (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • v) ∧
      (∃ c : ℂ, col Z 4 = c • v))
    (Y0 : M45) (hY0 : Y0 ∈ K) (hv0 : col Y0 2 = v ∨ col Y0 3 = v ∨ col Y0 4 = v)
    (Z : M45) (hZ : Z ∈ K) (hZ0 : rs Z = 0) : e2 (dY Z) = 0 ∧ ip v (Ed (dY Z)) = 0 := by
  obtain ⟨⟨c2, h2⟩, ⟨c3, h3⟩, ⟨c4, h4⟩⟩ := hline Z hZ hZ0
  have hu := uY_of_rs Z hZ0 v c2 c3 c4 h2 h3 h4
  have he : e2 (dY Z) = 0 := by
    have e := TC5_qbar1 K hdef Z hZ
    rw [hu, hZ0] at e
    simp only [ip, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e hv2
    linear_combination (-1 / 2 : ℂ) * e + ((-(c2 + c3 + c4) / 2) ^ 2 / 2) * hv2
  refine ⟨he, ?_⟩
  obtain ⟨-, ⟨b34, b24, b23⟩, -⟩ := TC5_degree K hdef Z hZ
  have x34 : X3c (uY Z) (uY Z) (col Z 3) (col Z 4) = 0 := by
    rw [hu, h3, h4]
    exact X3c_line v hv1 hv3 _ _ _ _
  have x24 : X3c (uY Z) (uY Z) (col Z 2) (col Z 4) = 0 := by
    rw [hu, h2, h4]
    exact X3c_line v hv1 hv3 _ _ _ _
  have x23 : X3c (uY Z) (uY Z) (col Z 2) (col Z 3) = 0 := by
    rw [hu, h2, h3]
    exact X3c_line v hv1 hv3 _ _ _ _
  have G : ∀ (x y : V4) (a b : ℂ), x = a • v → y = b • v →
      ip (x + y) (Ed (dY Z)) = a * ip v (Ed (dY Z)) + b * ip v (Ed (dY Z)) := by
    intro x y a b hx hy
    rw [hx, hy]
    simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have g34 := G _ _ c3 c4 h3 h4
  have g24 := G _ _ c2 c4 h2 h4
  have g23 := G _ _ c2 c3 h2 h3
  have z2 : c2 * ip v (Ed (dY Z)) = 0 := by
    linear_combination (-1 / 4 : ℂ) * (b24 + b23 - b34) + (1 / 4 : ℂ) * (x24 + x23 - x34)
      - (1 / 2 : ℂ) * (g24 + g23 - g34)
  have z3 : c3 * ip v (Ed (dY Z)) = 0 := by
    linear_combination (-1 / 4 : ℂ) * (b34 + b23 - b24) + (1 / 4 : ℂ) * (x34 + x23 - x24)
      - (1 / 2 : ℂ) * (g34 + g23 - g24)
  have z4 : c4 * ip v (Ed (dY Z)) = 0 := by
    linear_combination (-1 / 4 : ℂ) * (b34 + b24 - b23) + (1 / 4 : ℂ) * (x34 + x24 - x23)
      - (1 / 2 : ℂ) * (g34 + g24 - g23)
  by_cases hc : c2 = 0 ∧ c3 = 0 ∧ c4 = 0
  · obtain ⟨e2', e3', e4'⟩ := hc
    have k2 : col Z 2 = 0 := by rw [h2, e2', zero_smul]
    have k3 : col Z 3 = 0 := by rw [h3, e3', zero_smul]
    have k4 : col Z 4 = 0 := by rw [h4, e4', zero_smul]
    have hzK : zE (dY Z) ∈ K := by
      rw [← Z_of_nbar Z k2 k3 k4 (nbar_ker Z hZ0 k2 k3 k4)]
      exact hZ
    obtain ⟨-, -, a2, a3, a4, -⟩ := LemmaZ K hdef (dY Z) hzK Y0 hY0
    rcases hv0 with h | h | h
    · rw [h] at a2
      exact a2
    · rw [h] at a3
      exact a3
    · rw [h] at a4
      exact a4
  · rcases not_and_or.mp hc with h | h
    · exact (mul_eq_zero.mp z2).resolve_left h
    · rcases not_and_or.mp h with h' | h'
      · exact (mul_eq_zero.mp z3).resolve_left h'
      · exact (mul_eq_zero.mp z4).resolve_left h'

theorem zE2c (z : V4) (k : Fin 4) : zE z (k, 2) = 0 := by simp [zE]

theorem chi_t4 (v : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0) :
    -(v 0 * v 1 * v 2 * v 3) ≠ 0 ∧ t4 v v v v ≠ 0 := by
  have hk := chi_pow v hv1 hv2 hv3
  have hκ : -(v 0 * v 1 * v 2 * v 3) ≠ 0 := by
    intro h
    apply hv0
    funext i
    have e := hk i
    rw [h] at e
    exact (pow_eq_zero_iff (by norm_num)).mp e
  refine ⟨hκ, ?_⟩
  intro h
  apply hκ
  have e : t4 v v v v = v 0 ^ 4 + v 1 ^ 4 + v 2 ^ 4 + v 3 ^ 4 := by
    simp only [t4]
    ring
  rw [e, hk 0, hk 1, hk 2, hk 3] at h
  linear_combination (1 / 4 : ℂ) * h

theorem DN_pol (K : Submodule ℂ M45) (v : V4)
    (DN : ∀ Z ∈ K, rs Z = 0 → e2 (dY Z) = 0 ∧ ip v (Ed (dY Z)) = 0)
    (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0) (Z' : M45) (hZ' : Z' ∈ K) (h0' : rs Z' = 0) :
    e2b (dY Z) (dY Z') = 0 ∧ ip v (Edb (dY Z) (dY Z')) = 0 := by
  have hs : Z + Z' ∈ K := K.add_mem hZ hZ'
  have hs0 : rs (Z + Z') = 0 := by rw [map_add, h0, h0', add_zero]
  obtain ⟨a1, b1⟩ := DN Z hZ h0
  obtain ⟨a2, b2⟩ := DN Z' hZ' h0'
  obtain ⟨a3, b3⟩ := DN (Z + Z') hs hs0
  have hd : dY (Z + Z') = dY Z + dY Z' := by
    funext k
    simp only [dY, Pi.add_apply]
    ring
  rw [hd] at a3 b3
  constructor
  · have e : e2 (dY Z + dY Z') = e2 (dY Z) + e2 (dY Z') + 2 * e2b (dY Z) (dY Z') := by
      simp only [e2, e2b, tau, ip, Pi.add_apply]
      ring
    rw [e, a1, a2] at a3
    linear_combination (1 / 2 : ℂ) * a3
  · rw [Ed_pol] at b3
    simp only [ip] at b1 b2 b3 ⊢
    linear_combination (1 / 2 : ℂ) * (b3 - b1 - b2)

theorem DN_on_z (K : Submodule ℂ M45) (v : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (DN : ∀ Z ∈ K, rs Z = 0 → e2 (dY Z) = 0 ∧ ip v (Ed (dY Z)) = 0) (z : V4) (hz0 : z ≠ 0)
    (hzK : zE z ∈ K) (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0) : ∃ μ : ℂ, dY Z = μ • z := by
  by_contra hc
  push_neg at hc
  have hz0' : rs (zE z) = 0 := rs_zE z
  obtain ⟨q2, E2⟩ := DN (zE z) hzK hz0'
  obtain ⟨q12, E12⟩ := DN_pol K v DN Z hZ h0 (zE z) hzK hz0'
  rw [dY_zE] at q2 E2 q12 E12
  apply LAG_pair v kap hkap hk hv1 hv2 hv3 (dY Z) z _ (DN Z hZ h0).1 q2 q12 (DN Z hZ h0).2 E2 E12
  intro s t hst
  by_cases hs : s = 0
  · refine ⟨hs, ?_⟩
    rw [hs, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right hz0
  · exfalso
    apply hc (-(t / s))
    funext k
    have e := congrFun hst k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    linear_combination s⁻¹ * e - dY Z k * inv_mul_cancel₀ hs

theorem N2_form (K : Submodule ℂ M45) (v : V4) (Y : M45) (h0 : rs Y = 0) (hd : dY Y = 0)
    (c2 c3 : ℂ) (h2 : col Y 2 = c2 • v) (h3 : col Y 3 = c3 • v) (h4 : col Y 4 = 0) :
    Y = outer v ![-(c2 + c3) / 2, -(c2 + c3) / 2, c2, c3, 0] := by
  have hu := uY_of_rs Y h0 v c2 c3 0 h2 h3 (by rw [h4, zero_smul])
  funext p
  obtain ⟨k, j⟩ := p
  have eu := congrFun hu k
  have ed := congrFun hd k
  simp only [uY, dY, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at eu ed
  have g2 := congrFun h2 k
  have g3 := congrFun h3 k
  have g4 : Y (k, 4) = 0 := congrFun h4 k
  simp only [col, Pi.smul_apply, smul_eq_mul] at g2 g3
  fin_cases j
  · show Y (k, 0) = v k * (-(c2 + c3) / 2)
    linear_combination eu + ed
  · show Y (k, 1) = v k * (-(c2 + c3) / 2)
    linear_combination eu - ed
  · show Y (k, 2) = v k * c2
    rw [g2]
    ring
  · show Y (k, 3) = v k * c3
    rw [g3]
    ring
  · show Y (k, 4) = v k * 0
    rw [g4]
    ring

theorem P4_Na (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • v) ∧
      col Z 4 = 0)
    (hreal : ∀ l2 l3 : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l2 • v ∧ col Z 3 = l3 • v) : False := by
  have hline' : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • v) ∧
      (∃ c : ℂ, col Z 4 = c • v) := fun Z hZ h0 =>
    ⟨(hline Z hZ h0).1, (hline Z hZ h0).2.1, ⟨0, by rw [(hline Z hZ h0).2.2, zero_smul]⟩⟩
  have hv3 : t3 v v v = 0 := by
    obtain ⟨Z, hZ, h0, e2, e3⟩ := hreal 1 1
    have e4 := (hline Z hZ h0).2.2
    have c := (nbar_eqs K hdef Z hZ h0).1
    rw [e2, e3, e4] at c
    simp only [t3, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at c ⊢
    linear_combination (1 / 2 : ℂ) * c
  have hk := chi_pow v hv1 hv2 hv3
  obtain ⟨hκ, h4⟩ := chi_t4 v hv0 hv1 hv2 hv3
  obtain ⟨Y0, hY0, -, e02, -⟩ := hreal 1 0
  have hY0v : col Y0 2 = v := by rw [e02, one_smul]
  have DN := DN_line K hdef v hv1 hv2 hv3 hline' Y0 hY0 (Or.inl hY0v)
  obtain ⟨-, -, -, z, hz0, hzK⟩ := TC5_dims K hdef hK5
  have hDz := DN_on_z K v _ hκ hk hv1 hv2 hv3 DN z hz0 hzK
  have hN2K : ∀ Y ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45),
      Y ∈ K ∧ dY Y = 0 := by
    intro Y hY
    have h1 := Submodule.mem_inf.mp hY
    exact ⟨(Submodule.mem_inf.mp h1.1).1, LinearMap.mem_ker.mp h1.2⟩
  have hN2rs : ∀ Y ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45), rs Y = 0 := by
    intro Y hY
    exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hY).1).2
  have hS := L_slev K hdef _ hN2K
  have hform : ∀ Y ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45),
      ∃ x : Fin 5 → ℂ, Y = outer v x := by
    intro Y hY
    obtain ⟨hK, hd⟩ := hN2K Y hY
    have h0 := hN2rs Y hY
    obtain ⟨⟨c2, h2⟩, ⟨c3, h3⟩, h4⟩ := hline Y hK h0
    exact ⟨_, N2_form K v Y h0 hd c2 c3 h2 h3 h4⟩
  obtain ⟨j1, j2, hj, hz⟩ := A1cols _ hS hN2rs v hv0 hv1 hv2 hform h4
  have hreal2 : ∀ l2 l3 : ℂ, ∃ Y ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45),
      col Y 0 = (-(l2 + l3) / 2) • v ∧ col Y 1 = (-(l2 + l3) / 2) • v ∧ col Y 2 = l2 • v ∧
      col Y 3 = l3 • v := by
    intro l2 l3
    obtain ⟨Z, hZ, h0, e2, e3⟩ := hreal l2 l3
    have e4 := (hline Z hZ h0).2.2
    obtain ⟨μ, hμ⟩ := hDz Z hZ h0
    have hu := uY_of_rs Z h0 v l2 l3 0 e2 e3 (by rw [e4, zero_smul])
    refine ⟨Z - μ • zE z, ?_, ?_, ?_, ?_, ?_⟩
    · refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨K.sub_mem hZ (K.smul_mem μ hzK), ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, map_sub, map_smul, h0, rs_zE, smul_zero, sub_zero]
      · rw [LinearMap.mem_ker, map_sub, map_smul, dYL_apply, dYL_apply, hμ, dY_zE, sub_self]
    · funext k
      have eu := congrFun hu k
      have ed := congrFun hμ k
      simp only [uY, dY, Pi.smul_apply, smul_eq_mul] at eu ed
      simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE0]
      linear_combination eu + ed
    · funext k
      have eu := congrFun hu k
      have ed := congrFun hμ k
      simp only [uY, dY, Pi.smul_apply, smul_eq_mul] at eu ed
      simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE1]
      linear_combination eu - ed
    · funext k
      have e := congrFun e2 k
      simp only [col, Pi.smul_apply, smul_eq_mul] at e
      simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE2c, mul_zero, sub_zero]
      exact e
    · funext k
      have e := congrFun e3 k
      simp only [col, Pi.smul_apply, smul_eq_mul] at e
      simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE3, mul_zero, sub_zero]
      exact e
  obtain ⟨Ya, hYa, a0, a1, a2, -⟩ := hreal2 1 0
  obtain ⟨Yb, hYb, -, -, -, b3⟩ := hreal2 0 1
  have hsm : ∀ c : ℂ, c ≠ 0 → c • v ≠ 0 := by
    intro c hc h
    rcases smul_eq_zero.mp h with h' | h'
    · exact hc h'
    · exact hv0 h'
  have hnz : ∀ j : Fin 5, (∀ Y ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45),
      col Y j = 0) → j = 4 := by
    intro j hj'
    fin_cases j
    · exfalso
      have e : col Ya 0 = 0 := hj' Ya hYa
      rw [a0] at e
      exact hsm _ (by norm_num) e
    · exfalso
      have e : col Ya 1 = 0 := hj' Ya hYa
      rw [a1] at e
      exact hsm _ (by norm_num) e
    · exfalso
      have e : col Ya 2 = 0 := hj' Ya hYa
      rw [a2] at e
      exact hsm _ (by norm_num) e
    · exfalso
      have e : col Yb 3 = 0 := hj' Yb hYb
      rw [b3] at e
      exact hsm _ (by norm_num) e
    · rfl
  have e1 := hnz j1 (fun Y hY => (hz Y hY).1)
  have e2 := hnz j2 (fun Y hY => (hz Y hY).2)
  exact hj (e1.trans e2.symm)

def Mv (v : V4) : V4 →ₗ[ℂ] V4 where
  toFun d := fun k => v k * d k - (v k * tau d + ip v d) / 2
  map_add' d d' := by
    funext k
    simp only [tau, ip, Pi.add_apply]
    ring
  map_smul' c d := by
    funext k
    simp only [tau, ip, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem Mv_apply (v d : V4) (k : Fin 4) : Mv v d k = v k * d k - (v k * tau d + ip v d) / 2 := rfl

theorem Mv_ip (v : V4) (hv1 : tau v = 0) (d d' : V4) :
    ∑ i, d' i * Mv v d i = ip v (Edb d d') := by
  simp only [Fin.sum_univ_four, Mv_apply, Edb, e2b, tau, ip] at hv1 ⊢
  linear_combination (-(d 0 + d 1 + d 2 + d 3) * (d' 0 + d' 1 + d' 2 + d' 3) / 2
    + (d 0 * d' 0 + d 1 * d' 1 + d 2 * d' 2 + d 3 * d' 3) / 2) * hv1

theorem Mv_inj (v : V4) (hv1 : tau v = 0) (hv : ∀ k, v k ≠ 0) : Function.Injective (Mv v) := by
  intro d d' h
  have h0 : Mv v (d - d') = 0 := by rw [map_sub, h, sub_self]
  set e := d - d' with he
  have hk : ∀ k, v k * e k - (v k * tau e + ip v e) / 2 = 0 := fun k => congrFun h0 k
  have hA : ip v e = 0 := by
    have k0 := hk 0
    have k1 := hk 1
    have k2 := hk 2
    have k3 := hk 3
    have hA' : ip v e = v 0 * e 0 + v 1 * e 1 + v 2 * e 2 + v 3 * e 3 := rfl
    have hv' : v 0 + v 1 + v 2 + v 3 = 0 := hv1
    linear_combination -(k0 + k1 + k2 + k3) - hA' - (tau e / 2) * hv'
  have hc : ∀ k, e k = tau e / 2 := by
    intro k
    have h1 := hk k
    rw [hA] at h1
    have h2 : v k * (e k - tau e / 2) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.mp h2).resolve_left (hv k)
    linear_combination h3
  have hT : tau e = 0 := by
    have hT' : tau e = e 0 + e 1 + e 2 + e 3 := rfl
    linear_combination -hT' - (hc 0 + hc 1 + hc 2 + hc 3)
  have hz : e = 0 := by
    funext k
    rw [hc k, hT]
    simp
  exact sub_eq_zero.mp hz

theorem Fv_nondeg (v : V4) (hv1 : tau v = 0) (hv : ∀ k, v k ≠ 0) (W : Submodule ℂ V4)
    (hW : ∀ d ∈ W, ∀ d' ∈ W, ip v (Edb d d') = 0) : Module.finrank ℂ W ≤ 2 := by
  have hp := perp_bound W (W.map (Mv v)) (by
    rintro d' hd' _ ⟨d, hd, rfl⟩
    rw [Mv_ip v hv1]
    exact hW d hd d' hd')
  have e1 : Module.finrank ℂ (W.map (Mv v)) = Module.finrank ℂ W :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (Mv_inj v hv1 hv) W)).symm
  simp only [Fintype.card_fin] at hp
  omega

theorem three_iso_perp (E a b c : V4) (hE0 : E ≠ 0) (hE : tau E = 0) (ha1 : tau a = 0)
    (ha2 : ip a a = 0) (hb1 : tau b = 0) (hb2 : ip b b = 0) (hc1 : tau c = 0) (hc2 : ip c c = 0)
    (haE : ip a E = 0) (hbE : ip b E = 0) (hcE : ip c E = 0) (ha0 : a ≠ 0)
    (hab : ∀ s : ℂ, b ≠ s • a) (hac : ∀ s : ℂ, c ≠ s • a) (hbc : ∀ s : ℂ, c ≠ s • b) : False := by
  have hg : ip a b ≠ 0 := ip_ne_of_line a b ha0 ha1 ha2 hb1 hb2 hab
  have hb0 : b ≠ 0 := by
    intro h
    exact hab 0 (by rw [h, zero_smul])
  by_cases hin : ∃ α β : ℂ, c = α • a + β • b
  · obtain ⟨α, β, hcab⟩ := hin
    have e : 2 * α * β * ip a b = 0 := by
      rw [hcab] at hc2
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc2 ha2 hb2 ⊢
      linear_combination hc2 - α ^ 2 * ha2 - β ^ 2 * hb2
    rcases mul_eq_zero.mp e with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · norm_num at h''
        · exact hbc β (by rw [hcab, h'', zero_smul, zero_add])
      · exact hac α (by rw [hcab, h', zero_smul, add_zero])
    · exact hg h
  · push_neg at hin
    have hA : Module.finrank ℂ (Submodule.span ℂ {a}) = 1 := finrank_span_singleton ha0
    have hAB : Submodule.span ℂ {a} < Submodule.span ℂ {a, b} := by
      refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
      intro h
      have hb' : b ∈ Submodule.span ℂ {a} := by
        rw [h]
        exact Submodule.subset_span (by simp)
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hb'
      exact hab s hs.symm
    have hBC : Submodule.span ℂ {a, b} < Submodule.span ℂ {c, a, b} := by
      refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert c {a, b})) ?_
      intro h
      have hc' : c ∈ Submodule.span ℂ {a, b} := by
        rw [h]
        exact Submodule.subset_span (Set.mem_insert c {a, b})
      obtain ⟨α, β, hab'⟩ := Submodule.mem_span_pair.mp hc'
      exact hin α β hab'.symm
    have h1 := Submodule.finrank_lt_finrank_of_lt hAB
    have h2 := Submodule.finrank_lt_finrank_of_lt hBC
    have hEs : Module.finrank ℂ (Submodule.span ℂ {E}) = 1 := finrank_span_singleton hE0
    have hperp := perp_sup_one (Submodule.span ℂ {E}) (Submodule.span ℂ {c, a, b})
      (by
        intro p hp
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hp
        simp only [tau, Pi.smul_apply, smul_eq_mul] at hE ⊢
        linear_combination s * hE)
      (by
        intro q hq
        obtain ⟨x, q', hq', rfl⟩ := Submodule.mem_span_insert.mp hq
        obtain ⟨y, t, rfl⟩ := Submodule.mem_span_pair.mp hq'
        simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha1 hb1 hc1 ⊢
        linear_combination x * hc1 + y * ha1 + t * hb1)
      (by
        intro p hp q hq
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hp
        obtain ⟨x, q', hq', rfl⟩ := Submodule.mem_span_insert.mp hq
        obtain ⟨y, t, rfl⟩ := Submodule.mem_span_pair.mp hq'
        simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at haE hbE hcE ⊢
        linear_combination s * x * hcE + s * y * haE + s * t * hbE)
    omega

theorem X3c_two (v w : V4) (hv : tau v = 0) (hw : tau w = 0) (r0 : t3 v v v = 0) (r1 : t3 v v w = 0)
    (r2 : t3 v w w = 0) (c2 c3 : ℂ) :
    X3c (fun k => -(c2 * v k + c3 * w k) / 2) (fun k => -(c2 * v k + c3 * w k) / 2) (c2 • v) 0 = 0 := by
  simp only [X3c, tau, ip, t3, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hv hw r0 r1 r2 ⊢
  linear_combination (-c2^3*v 0^2/2 + c2^3*v 0*v 1/2 + c2^3*v 0*v 2/2 + c2^3*v 0*v 3/2 - c2^3*v 1^2/2 + c2^3*v 1*v 2/2 + c2^3*v 1*v 3/2 - c2^3*v 2^2/2 + c2^3*v 2*v 3/2 - c2^3*v 3^2/2 + c2^2*c3*v 0*w 1 + c2^2*c3*v 0*w 2 + c2^2*c3*v 0*w 3 + c2^2*c3*v 1*w 0 + c2^2*c3*v 1*w 2 + c2^2*c3*v 1*w 3 + c2^2*c3*v 2*w 0 + c2^2*c3*v 2*w 1 + c2^2*c3*v 2*w 3 - c2^2*c3*v 3*w 3 + c2*c3^2*w 0*w 1/2 + c2*c3^2*w 0*w 2/2 + c2*c3^2*w 1*w 2/2 - c2*c3^2*w 3^2/2) * hv + (-c2^2*c3*v 0^2 - c2^2*c3*v 0*v 1 - c2^2*c3*v 0*v 2 - c2^2*c3*v 1^2 - c2^2*c3*v 1*v 2 - c2^2*c3*v 2^2 - c2*c3^2*v 0*w 0/2 + c2*c3^2*v 0*w 3/2 - c2*c3^2*v 1*w 1/2 + c2*c3^2*v 1*w 3/2 - c2*c3^2*v 2*w 2/2 + c2*c3^2*v 2*w 3/2) * hw + (c2^3/2) * r0 + (c2^2*c3) * r1 + (c2*c3^2/2) * r2

theorem uY_of_rs2 (Z : M45) (h0 : rs Z = 0) (v w : V4) (c2 c3 : ℂ) (h2 : col Z 2 = c2 • v)
    (h3 : col Z 3 = c3 • w) (h4 : col Z 4 = 0) : uY Z = fun k => -(c2 * v k + c3 * w k) / 2 := by
  funext k
  have e := congrFun h0 k
  rw [rs_apply] at e
  have e' : Z (k, 0) + Z (k, 1) + Z (k, 2) + Z (k, 3) + Z (k, 4) = 0 := e
  have g2 := congrFun h2 k
  have g3 := congrFun h3 k
  have g4 : Z (k, 4) = 0 := congrFun h4 k
  simp only [col, Pi.smul_apply, smul_eq_mul] at g2 g3
  simp only [uY]
  linear_combination (1 / 2 : ℂ) * e' - (1 / 2 : ℂ) * (g2 + g3 + g4)

theorem qbar_pol (K : Submodule ℂ M45) (hdef : DefLine K mTC) (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0)
    (Z' : M45) (hZ' : Z' ∈ K) (h0' : rs Z' = 0) :
    ip (uY Z) (uY Z') = 2 * e2b (dY Z) (dY Z') := by
  have e1 := TC5_qbar1 K hdef Z hZ
  have e2' := TC5_qbar1 K hdef Z' hZ'
  have e3 := TC5_qbar1 K hdef (Z + Z') (K.add_mem hZ hZ')
  rw [h0] at e1
  rw [h0'] at e2'
  rw [map_add, h0, h0', add_zero] at e3
  simp only [ip, e2, e2b, tau, uY, dY, Pi.add_apply, Pi.zero_apply] at e1 e2' e3 ⊢
  linear_combination (1 / 2 : ℂ) * (e3 - e1 - e2')

theorem Ed_sub (z z' : V4) : Ed (z - z') = fun k => Ed z k + Ed z' k - 2 * Edb z z' k := by
  funext k
  simp only [Ed, Edb, e2, e2b, tau, ip, Pi.sub_apply]
  ring

theorem dY_add (Y Y' : M45) : dY (Y + Y') = dY Y + dY Y' := by
  funext k
  simp only [dY, Pi.add_apply]
  ring

theorem dY_sub (Y Y' : M45) : dY (Y - Y') = dY Y - dY Y' := by
  funext k
  simp only [dY, Pi.sub_apply]
  ring

theorem P4_Nb_chi (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v w : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hvw : ∀ c : ℂ, w ≠ c • v)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • w) ∧
      col Z 4 = 0)
    (hreal : ∀ l2 l3 : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l2 • v ∧ col Z 3 = l3 • w)
    (hchi : ∀ k, v k * w k = ip v w / 4) : False := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  have hvk : ∀ k, v k ≠ 0 := by
    intro k h
    have e := hchi k
    rw [h, zero_mul] at e
    exact hg (by linear_combination (-4 : ℂ) * e)
  have hr : t3 v v w = 0 ∧ t3 v w w = 0 := by
    obtain ⟨Z1, hZ1, h01, a2, a3⟩ := hreal 1 1
    obtain ⟨Z2, hZ2, h02, b2, b3⟩ := hreal 1 2
    have e1 := (nbar_eqs K hdef Z1 hZ1 h01).1
    have e2'' := (nbar_eqs K hdef Z2 hZ2 h02).1
    rw [a2, a3, (hline Z1 hZ1 h01).2.2] at e1
    rw [b2, b3, (hline Z2 hZ2 h02).2.2] at e2''
    simp only [t3, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2'' ⊢
    exact ⟨by linear_combination 2 * e1 - (1 / 2 : ℂ) * e2'',
      by linear_combination (1 / 2 : ℂ) * e2'' - e1⟩
  have hr0 : t3 v v v = 0 := by
    have hw1' : w 0 + w 1 + w 2 + w 3 = 0 := hw1
    have hv1' : v 0 + v 1 + v 2 + v 3 = 0 := hv1
    have he3 : ip v w * (v 0 * v 1 * v 2 + v 0 * v 1 * v 3 + v 0 * v 2 * v 3 + v 1 * v 2 * v 3) = 0 := by
      linear_combination 4 * (v 0 * v 1 * v 2 * v 3) * hw1' - 4 * (v 1 * v 2 * v 3) * hchi 0
        - 4 * (v 0 * v 2 * v 3) * hchi 1 - 4 * (v 0 * v 1 * v 3) * hchi 2
        - 4 * (v 0 * v 1 * v 2) * hchi 3
    have he3' := (mul_eq_zero.mp he3).resolve_left hg
    simp only [t3]
    linear_combination 3 * he3' + ((v 0 + v 1 + v 2 + v 3) ^ 2 - 3 * (v 0 * v 1 + v 0 * v 2
      + v 0 * v 3 + v 1 * v 2 + v 1 * v 3 + v 2 * v 3)) * hv1'
  have hcF : ∀ Z ∈ K, rs Z = 0 → ∀ c : ℂ, col Z 2 = c • v → c * ip v (Ed (dY Z)) = 0 := by
    intro Z hZ h0 c h2
    obtain ⟨-, ⟨c3, h3⟩, h4⟩ := hline Z hZ h0
    have hu := uY_of_rs2 Z h0 v w c c3 h2 h3 h4
    obtain ⟨-, ⟨-, b24, -⟩, -⟩ := TC5_degree K hdef Z hZ
    rw [hu, h2, h4, X3c_two v w hv1 hw1 hr0 hr.1 hr.2] at b24
    have e : ip (c • v + 0) (Ed (dY Z)) = c * ip v (Ed (dY Z)) := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    linear_combination (-1 / 2 : ℂ) * b24 - e
  obtain ⟨Zr, hZr, h0r, r2, r3⟩ := hreal 1 0
  have hFr : ip v (Ed (dY Zr)) = 0 := by
    have e := hcF Zr hZr h0r 1 r2
    linear_combination e
  have hF : ∀ Z ∈ K, rs Z = 0 → ip v (Ed (dY Z)) = 0 := by
    intro Z hZ h0
    obtain ⟨⟨c, h2⟩, -, -⟩ := hline Z hZ h0
    by_cases hc : c = 0
    · have hp := hcF (Z + Zr) (K.add_mem hZ hZr) (by rw [map_add, h0, h0r, add_zero]) 1 (by
        funext k
        have g := congrFun h2 k
        have g' := congrFun r2 k
        simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
        rw [g, g', hc]
        ring)
      have hm := hcF (Z - Zr) (K.sub_mem hZ hZr) (by rw [map_sub, h0, h0r, sub_zero]) (-1) (by
        funext k
        have g := congrFun h2 k
        have g' := congrFun r2 k
        simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
        rw [g, g', hc]
        ring)
      rw [dY_add, Ed_pol] at hp
      rw [dY_sub, Ed_sub] at hm
      simp only [ip] at hp hm hFr ⊢
      linear_combination (1 / 2 : ℂ) * hp - (1 / 2 : ℂ) * hm - hFr
    · exact (mul_eq_zero.mp (hcF Z hZ h0 c h2)).resolve_left hc
  have hB : ∀ d ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL,
      ∀ d' ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL, ip v (Edb d d') = 0 := by
    rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
    have h1 := Submodule.mem_inf.mp hZ
    have h2 := Submodule.mem_inf.mp hZ'
    have h0 : rs Z = 0 := LinearMap.mem_ker.mp h1.2
    have h0' : rs Z' = 0 := LinearMap.mem_ker.mp h2.2
    have f1 := hF Z h1.1 h0
    have f2 := hF Z' h2.1 h0'
    have f3 := hF (Z + Z') (K.add_mem h1.1 h2.1) (by rw [map_add, h0, h0', add_zero])
    rw [dY_add, Ed_pol] at f3
    rw [dYL_apply, dYL_apply]
    simp only [ip] at f1 f2 f3 ⊢
    linear_combination (1 / 2 : ℂ) * (f3 - f1 - f2)
  have hW := Fv_nondeg v hv1 hvk _ hB
  obtain ⟨Za, hZa, h0a, a2, a3⟩ := hreal 1 0
  obtain ⟨Zb, hZb, h0b, b2, b3⟩ := hreal 0 1
  have hua := uY_of_rs2 Za h0a v w 1 0 a2 a3 (hline Za hZa h0a).2.2
  have hub := uY_of_rs2 Zb h0b v w 0 1 b2 b3 (hline Zb hZb h0b).2.2
  have hker : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have h1 := Submodule.mem_inf.mp hZ
    have h2 := Submodule.mem_inf.mp h1.1
    have h0 : rs Z = 0 := LinearMap.mem_ker.mp h2.2
    have hd : dY Z = 0 := LinearMap.mem_ker.mp h1.2
    obtain ⟨⟨c2, e2⟩, ⟨c3, e3⟩, e4⟩ := hline Z h2.1 h0
    have hu := uY_of_rs2 Z h0 v w c2 c3 e2 e3 e4
    have qa := qbar_pol K hdef Z h2.1 h0 Za hZa h0a
    have qb := qbar_pol K hdef Z h2.1 h0 Zb hZb h0b
    rw [hd, hu, hua] at qa
    rw [hd, hub, hu] at qb
    have hc3 : c3 * ip v w = 0 := by
      simp only [ip, e2b, tau, Pi.zero_apply] at qa hv2 ⊢
      linear_combination 4 * qa - c2 * hv2
    have hc2 : c2 * ip v w = 0 := by
      simp only [ip, e2b, tau, Pi.zero_apply] at qb hw2 ⊢
      linear_combination 4 * qb - c3 * hw2
    have z2 := (mul_eq_zero.mp hc2).resolve_right hg
    have z3 := (mul_eq_zero.mp hc3).resolve_right hg
    have k2 : col Z 2 = 0 := by rw [e2, z2, zero_smul]
    have k3 : col Z 3 = 0 := by rw [e3, z3, zero_smul]
    have ku : uY Z = 0 := by
      rw [hu, z2, z3]
      funext k
      simp
    exact uY_dY_zero Z ku hd k2 k3 e4
  have r1 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) dYL
  rw [hker, finrank_bot] at r1
  obtain ⟨hK, hq, -, -⟩ := TC5_dims K hdef hK5
  have r2 := rank_nullity K rs
  omega

theorem X3c_gen2 (v w : V4) (hv : tau v = 0) (hw : tau w = 0) (r1 : t3 v v w = 0) (r2 : t3 v w w = 0)
    (c2 c3 : ℂ) :
    X3c (fun k => -(c2 * v k + c3 * w k) / 2) (fun k => -(c2 * v k + c3 * w k) / 2) (c2 • v) 0 =
      c2 ^ 3 / 2 * t3 v v v := by
  simp only [X3c, tau, ip, t3, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hv hw r1 r2 ⊢
  linear_combination (-c2^3*v 0^2/2 + c2^3*v 0*v 1/2 + c2^3*v 0*v 2/2 + c2^3*v 0*v 3/2 - c2^3*v 1^2/2 + c2^3*v 1*v 2/2 + c2^3*v 1*v 3/2 - c2^3*v 2^2/2 + c2^3*v 2*v 3/2 - c2^3*v 3^2/2 + c2^2*c3*v 0*w 1 + c2^2*c3*v 0*w 2 + c2^2*c3*v 0*w 3 + c2^2*c3*v 1*w 0 + c2^2*c3*v 1*w 2 + c2^2*c3*v 1*w 3 + c2^2*c3*v 2*w 0 + c2^2*c3*v 2*w 1 + c2^2*c3*v 2*w 3 - c2^2*c3*v 3*w 3 + c2*c3^2*w 0*w 1/2 + c2*c3^2*w 0*w 2/2 + c2*c3^2*w 1*w 2/2 - c2*c3^2*w 3^2/2) * hv + (-c2^2*c3*v 0^2 - c2^2*c3*v 0*v 1 - c2^2*c3*v 0*v 2 - c2^2*c3*v 1^2 - c2^2*c3*v 1*v 2 - c2^2*c3*v 2^2 - c2*c3^2*v 0*w 0/2 + c2*c3^2*v 0*w 3/2 - c2*c3^2*v 1*w 1/2 + c2*c3^2*v 1*w 3/2 - c2*c3^2*v 2*w 2/2 + c2*c3^2*v 2*w 3/2) * hw + (c2^2*c3) * r1 + (c2*c3^2/2) * r2

theorem X3c_gen3 (v w : V4) (hv : tau v = 0) (hw : tau w = 0) (r1 : t3 v v w = 0) (r2 : t3 v w w = 0)
    (c2 c3 : ℂ) :
    X3c (fun k => -(c2 * v k + c3 * w k) / 2) (fun k => -(c2 * v k + c3 * w k) / 2) (c3 • w) 0 =
      c3 ^ 3 / 2 * t3 w w w := by
  simp only [X3c, tau, ip, t3, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hv hw r1 r2 ⊢
  linear_combination (c2^2*c3*v 0*w 1/2 + c2^2*c3*v 0*w 2/2 + c2^2*c3*v 0*w 3/2 + c2^2*c3*v 1*w 0/2 + c2^2*c3*v 1*w 2/2 + c2^2*c3*v 1*w 3/2 + c2^2*c3*v 2*w 0/2 + c2^2*c3*v 2*w 1/2 + c2^2*c3*v 2*w 3/2 - c2^2*c3*v 3*w 3/2 + c2*c3^2*w 0*w 1 + c2*c3^2*w 0*w 2 + c2*c3^2*w 1*w 2 - c2*c3^2*w 3^2) * hv + (-c2^2*c3*v 0^2/2 - c2^2*c3*v 0*v 1/2 - c2^2*c3*v 0*v 2/2 - c2^2*c3*v 1^2/2 - c2^2*c3*v 1*v 2/2 - c2^2*c3*v 2^2/2 - c2*c3^2*v 0*w 0 + c2*c3^2*v 0*w 3 - c2*c3^2*v 1*w 1 + c2*c3^2*v 1*w 3 - c2*c3^2*v 2*w 2 + c2*c3^2*v 2*w 3 - c3^3*w 0^2/2 + c3^3*w 0*w 1/2 + c3^3*w 0*w 2/2 + c3^3*w 0*w 3/2 - c3^3*w 1^2/2 + c3^3*w 1*w 2/2 + c3^3*w 1*w 3/2 - c3^3*w 2^2/2 + c3^3*w 2*w 3/2 - c3^3*w 3^2/2) * hw + (c2*c3^2) * r2 + (c2^2*c3/2) * r1

def hvec (k0 : Fin 4) : V4 := fun k => if k = k0 then -1 else 1

theorem hvec_sq (k0 k : Fin 4) : hvec k0 k * hvec k0 k = 1 := by
  simp only [hvec]
  split_ifs <;> norm_num

theorem hvec_ip (k0 : Fin 4) (x : V4) : ip x (hvec k0) = tau x - 2 * x k0 := by
  fin_cases k0
  · show ip x (hvec 0) = tau x - 2 * x 0
    simp (config := {decide := true}) only [ip, tau, hvec, ite_true, ite_false]
    ring
  · show ip x (hvec 1) = tau x - 2 * x 1
    simp (config := {decide := true}) only [ip, tau, hvec, ite_true, ite_false]
    ring
  · show ip x (hvec 2) = tau x - 2 * x 2
    simp (config := {decide := true}) only [ip, tau, hvec, ite_true, ite_false]
    ring
  · show ip x (hvec 3) = tau x - 2 * x 3
    simp (config := {decide := true}) only [ip, tau, hvec, ite_true, ite_false]
    ring

theorem hvec_tau (k0 : Fin 4) : tau (hvec k0) = 2 := by
  fin_cases k0
  · show tau (hvec 0) = 2
    simp (config := {decide := true}) only [tau, hvec, ite_true, ite_false]
    norm_num
  · show tau (hvec 1) = 2
    simp (config := {decide := true}) only [tau, hvec, ite_true, ite_false]
    norm_num
  · show tau (hvec 2) = 2
    simp (config := {decide := true}) only [tau, hvec, ite_true, ite_false]
    norm_num
  · show tau (hvec 3) = 2
    simp (config := {decide := true}) only [tau, hvec, ite_true, ite_false]
    norm_num

theorem tau_single (y : V4) (k0 : Fin 4) (hy : ∀ k, k ≠ k0 → y k = 0) : tau y = y k0 := by
  fin_cases k0
  · show tau y = y 0
    simp only [tau]
    rw [hy 1 (by decide), hy 2 (by decide), hy 3 (by decide)]
    ring
  · show tau y = y 1
    simp only [tau]
    rw [hy 0 (by decide), hy 2 (by decide), hy 3 (by decide)]
    ring
  · show tau y = y 2
    simp only [tau]
    rw [hy 0 (by decide), hy 1 (by decide), hy 3 (by decide)]
    ring
  · show tau y = y 3
    simp only [tau]
    rw [hy 0 (by decide), hy 1 (by decide), hy 2 (by decide)]
    ring

theorem Mv_hvec (v : V4) (hv1 : tau v = 0) (k0 : Fin 4) (hvk0 : v k0 = 0) : Mv v (hvec k0) = 0 := by
  have hip : ip v (hvec k0) = 0 := by
    rw [hvec_ip, hv1, hvk0]
    ring
  funext k
  rw [Mv_apply, hvec_tau, hip]
  by_cases hk : k = k0
  · rw [hk, hvk0]
    simp
  · simp only [hvec, if_neg hk, Pi.zero_apply]
    ring

theorem Mv_ker (v : V4) (k0 : Fin 4) (hvk0 : v k0 = 0) (hvm : ∀ m, m ≠ k0 → v m ≠ 0) (x : V4)
    (hx : Mv v x = 0) : x = (tau x / 2) • hvec k0 := by
  have hk : ∀ k, v k * x k - (v k * tau x + ip v x) / 2 = 0 := fun k => congrFun hx k
  have hA : ip v x = 0 := by
    have e := hk k0
    rw [hvk0] at e
    linear_combination -2 * e
  have hm : ∀ m, m ≠ k0 → x m = tau x / 2 := by
    intro m hm
    have e := hk m
    rw [hA] at e
    have e' : v m * (x m - tau x / 2) = 0 := by linear_combination e
    have e'' := (mul_eq_zero.mp e').resolve_left (hvm m hm)
    linear_combination e''
  have hy := tau_single (fun k => x k - tau x / 2) k0 (fun k hk => by
    show x k - tau x / 2 = 0
    rw [hm k hk]
    ring)
  have hy2 : tau (fun k => x k - tau x / 2) = -tau x := by
    simp only [tau]
    ring
  have hk0 : x k0 = -(tau x / 2) := by
    have e : x k0 - tau x / 2 = -tau x := hy.symm.trans hy2
    linear_combination e
  funext k
  by_cases hk' : k = k0
  · rw [hk', hk0]
    simp [hvec]
  · rw [hm k hk']
    simp [hvec, hk']

theorem Edb_self (x : V4) : Edb x x = Ed x := by
  funext k
  simp only [Ed, Edb, e2, e2b]
  ring

theorem Edb_comm (x y : V4) : Edb x y = Edb y x := by
  funext k
  simp only [Edb, e2b, tau, ip]
  ring

theorem pc_hvec (v w : V4) (hv1 : tau v = 0) (hw1 : tau w = 0) (k0 : Fin 4) (hvk0 : v k0 = 0)
    (hwk0 : w k0 = 0) : pc (hvec k0) (hvec k0) v w = 2 * ip v w := by
  have t3h : t3 (hvec k0) v w = ip v w := by
    have e := hvec_ip k0 (fun k => v k * w k)
    simp only [ip, tau, t3] at e ⊢
    linear_combination e - 2 * w k0 * hvk0
  have t4h : t4 (hvec k0) (hvec k0) v w = ip v w := by
    simp only [t4, ip]
    linear_combination v 0 * w 0 * hvec_sq k0 0 + v 1 * w 1 * hvec_sq k0 1 + v 2 * w 2 * hvec_sq k0 2
      + v 3 * w 3 * hvec_sq k0 3
  have ihh : ip (hvec k0) (hvec k0) = 4 := by
    simp only [ip]
    linear_combination hvec_sq k0 0 + hvec_sq k0 1 + hvec_sq k0 2 + hvec_sq k0 3
  have ihv : ip (hvec k0) v = 0 := by
    have e := hvec_ip k0 v
    rw [hv1, hvk0] at e
    simp only [ip] at e ⊢
    linear_combination e
  have ihw : ip (hvec k0) w = 0 := by
    have e := hvec_ip k0 w
    rw [hw1, hwk0] at e
    simp only [ip] at e ⊢
    linear_combination e
  rw [pc_full, hvec_tau, hv1, hw1]
  simp only [br]
  rw [t3h, t4h, ihh, ihv, ihw]
  ring

theorem dY_inj_two (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4) (hv2 : ip v v = 0)
    (hw2 : ip w w = 0) (hg : ip v w ≠ 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • w) ∧
      col Z 4 = 0)
    (hreal : ∀ l2 l3 : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l2 • v ∧ col Z 3 = l3 • w) :
    ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45) = ⊥ := by
  obtain ⟨Za, hZa, h0a, a2, a3⟩ := hreal 1 0
  obtain ⟨Zb, hZb, h0b, b2, b3⟩ := hreal 0 1
  have hua := uY_of_rs2 Za h0a v w 1 0 a2 a3 (hline Za hZa h0a).2.2
  have hub := uY_of_rs2 Zb h0b v w 0 1 b2 b3 (hline Zb hZb h0b).2.2
  rw [eq_bot_iff]
  intro Z hZ
  rw [Submodule.mem_bot]
  have h1 := Submodule.mem_inf.mp hZ
  have h2 := Submodule.mem_inf.mp h1.1
  have h0 : rs Z = 0 := LinearMap.mem_ker.mp h2.2
  have hd : dY Z = 0 := LinearMap.mem_ker.mp h1.2
  obtain ⟨⟨c2, e2'⟩, ⟨c3, e3'⟩, e4'⟩ := hline Z h2.1 h0
  have hu := uY_of_rs2 Z h0 v w c2 c3 e2' e3' e4'
  have qa := qbar_pol K hdef Z h2.1 h0 Za hZa h0a
  have qb := qbar_pol K hdef Z h2.1 h0 Zb hZb h0b
  rw [hd, hu, hua] at qa
  rw [hd, hub, hu] at qb
  have hc3 : c3 * ip v w = 0 := by
    simp only [ip, e2b, tau, Pi.zero_apply] at qa hv2 ⊢
    linear_combination 4 * qa - c2 * hv2
  have hc2 : c2 * ip v w = 0 := by
    simp only [ip, e2b, tau, Pi.zero_apply] at qb hw2 ⊢
    linear_combination 4 * qb - c3 * hw2
  have z2 := (mul_eq_zero.mp hc2).resolve_right hg
  have z3 := (mul_eq_zero.mp hc3).resolve_right hg
  have k2 : col Z 2 = 0 := by rw [e2', z2, zero_smul]
  have k3 : col Z 3 = 0 := by rw [e3', z3, zero_smul]
  have ku : uY Z = 0 := by
    rw [hu, z2, z3]
    funext k
    simp
  exact uY_dY_zero Z ku hd k2 k3 e4'

theorem P4_Nb_zero (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v w : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hvw : ∀ c : ℂ, w ≠ c • v)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • w) ∧
      col Z 4 = 0)
    (hreal : ∀ l2 l3 : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l2 • v ∧ col Z 3 = l3 • w)
    (k0 : Fin 4) (hvk0 : v k0 = 0) (hwk0 : w k0 = 0)
    (h3m : ∀ m, m ≠ k0 → 3 * (v m * w m) = ip v w) : False := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  have hvm : ∀ m, m ≠ k0 → v m ≠ 0 := by
    intro m hm h
    have e := h3m m hm
    rw [h, zero_mul, mul_zero] at e
    exact hg e.symm
  have hr : t3 v v w = 0 ∧ t3 v w w = 0 := by
    obtain ⟨Z1, hZ1, h01, a2, a3⟩ := hreal 1 1
    obtain ⟨Z2, hZ2, h02, b2, b3⟩ := hreal 1 2
    have e1 := (nbar_eqs K hdef Z1 hZ1 h01).1
    have e2'' := (nbar_eqs K hdef Z2 hZ2 h02).1
    rw [a2, a3, (hline Z1 hZ1 h01).2.2] at e1
    rw [b2, b3, (hline Z2 hZ2 h02).2.2] at e2''
    simp only [t3, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2'' ⊢
    exact ⟨by linear_combination 2 * e1 - (1 / 2 : ℂ) * e2'',
      by linear_combination (1 / 2 : ℂ) * e2'' - e1⟩
  have hτv : t3 v v v ≠ 0 := by
    intro h3
    apply hv0
    have hk := chi_pow v hv1 hv2 h3
    have hp : v 0 * v 1 * v 2 * v 3 = 0 := by
      have e := hk k0
      rw [hvk0] at e
      linear_combination e
    funext m
    have e := hk m
    rw [hp, neg_zero] at e
    exact (pow_eq_zero_iff (by norm_num)).mp e
  have hcF : ∀ Z ∈ K, rs Z = 0 → ∀ c : ℂ, col Z 2 = c • v →
      c * (ip v (Ed (dY Z)) - t3 v v v / 4 * c ^ 2) = 0 := by
    intro Z hZ h0 c h2
    obtain ⟨-, ⟨c3, h3⟩, h4⟩ := hline Z hZ h0
    have hu := uY_of_rs2 Z h0 v w c c3 h2 h3 h4
    obtain ⟨-, ⟨-, b24, -⟩, -⟩ := TC5_degree K hdef Z hZ
    rw [hu, h2, h4, X3c_gen2 v w hv1 hw1 hr.1 hr.2] at b24
    have e : ip (c • v + 0) (Ed (dY Z)) = c * ip v (Ed (dY Z)) := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    linear_combination (-1 / 2 : ℂ) * b24 - e
  obtain ⟨Zr, hZr, h0r, r2, r3⟩ := hreal 1 0
  have hFr : ip v (Ed (dY Zr)) = t3 v v v / 4 := by
    have e := hcF Zr hZr h0r 1 r2
    linear_combination e
  have hF : ∀ Z ∈ K, rs Z = 0 → ∀ c : ℂ, col Z 2 = c • v →
      ip v (Ed (dY Z)) = t3 v v v / 4 * c ^ 2 := by
    intro Z hZ h0 c h2
    by_cases hc : c = 0
    · have hp := hcF (Z + Zr) (K.add_mem hZ hZr) (by rw [map_add, h0, h0r, add_zero]) 1 (by
        funext k
        have g := congrFun h2 k
        have g' := congrFun r2 k
        simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
        rw [g, g', hc]
        ring)
      have hm := hcF (Z - Zr) (K.sub_mem hZ hZr) (by rw [map_sub, h0, h0r, sub_zero]) (-1) (by
        funext k
        have g := congrFun h2 k
        have g' := congrFun r2 k
        simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
        rw [g, g', hc]
        ring)
      rw [dY_add, Ed_pol] at hp
      rw [dY_sub, Ed_sub] at hm
      rw [hc]
      simp only [ip] at hp hm hFr ⊢
      linear_combination (1 / 2 : ℂ) * hp - (1 / 2 : ℂ) * hm - hFr
    · have e := hcF Z hZ h0 c h2
      have e' := (mul_eq_zero.mp e).resolve_left hc
      linear_combination e'
  have hB : ∀ Z ∈ K, rs Z = 0 → ∀ c : ℂ, col Z 2 = c • v → ∀ Z' ∈ K, rs Z' = 0 → ∀ c' : ℂ,
      col Z' 2 = c' • v → ip v (Edb (dY Z) (dY Z')) = t3 v v v / 4 * c * c' := by
    intro Z hZ h0 c h2 Z' hZ' h0' c' h2'
    have f1 := hF Z hZ h0 c h2
    have f2 := hF Z' hZ' h0' c' h2'
    have f3 := hF (Z + Z') (K.add_mem hZ hZ') (by rw [map_add, h0, h0', add_zero]) (c + c') (by
      funext k
      have g := congrFun h2 k
      have g' := congrFun h2' k
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
      rw [g, g']
      ring)
    rw [dY_add, Ed_pol] at f3
    simp only [ip] at f1 f2 f3 ⊢
    linear_combination (1 / 2 : ℂ) * (f3 - f1 - f2)
  have hw0 : w ≠ 0 := by
    intro h
    exact hvw 0 (by rw [h, zero_smul])
  have hτw : t3 w w w ≠ 0 := by
    intro h3
    apply hw0
    have hk := chi_pow w hw1 hw2 h3
    have hp : w 0 * w 1 * w 2 * w 3 = 0 := by
      have e := hk k0
      rw [hwk0] at e
      linear_combination e
    funext m
    have e := hk m
    rw [hp, neg_zero] at e
    exact (pow_eq_zero_iff (by norm_num)).mp e
  have hcG : ∀ Z ∈ K, rs Z = 0 → ∀ c : ℂ, col Z 3 = c • w →
      c * (ip w (Ed (dY Z)) - t3 w w w / 4 * c ^ 2) = 0 := by
    intro Z hZ h0 c h3
    obtain ⟨⟨c2, h2⟩, -, h4⟩ := hline Z hZ h0
    have hu := uY_of_rs2 Z h0 v w c2 c h2 h3 h4
    obtain ⟨-, ⟨b34, -, -⟩, -⟩ := TC5_degree K hdef Z hZ
    rw [hu, h3, h4, X3c_gen3 v w hv1 hw1 hr.1 hr.2] at b34
    have e : ip (c • w + 0) (Ed (dY Z)) = c * ip w (Ed (dY Z)) := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    linear_combination (-1 / 2 : ℂ) * b34 - e
  obtain ⟨Zs, hZs, h0s, s2, s3⟩ := hreal 0 1
  have hGs : ip w (Ed (dY Zs)) = t3 w w w / 4 := by
    have e := hcG Zs hZs h0s 1 s3
    linear_combination e
  have hG : ∀ Z ∈ K, rs Z = 0 → ∀ c : ℂ, col Z 3 = c • w →
      ip w (Ed (dY Z)) = t3 w w w / 4 * c ^ 2 := by
    intro Z hZ h0 c h3
    by_cases hc : c = 0
    · have hp := hcG (Z + Zs) (K.add_mem hZ hZs) (by rw [map_add, h0, h0s, add_zero]) 1 (by
        funext k
        have g := congrFun h3 k
        have g' := congrFun s3 k
        simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
        rw [g, g', hc]
        ring)
      have hm := hcG (Z - Zs) (K.sub_mem hZ hZs) (by rw [map_sub, h0, h0s, sub_zero]) (-1) (by
        funext k
        have g := congrFun h3 k
        have g' := congrFun s3 k
        simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
        rw [g, g', hc]
        ring)
      rw [dY_add, Ed_pol] at hp
      rw [dY_sub, Ed_sub] at hm
      rw [hc]
      simp only [ip] at hp hm hGs ⊢
      linear_combination (1 / 2 : ℂ) * hp - (1 / 2 : ℂ) * hm - hGs
    · have e := hcG Z hZ h0 c h3
      have e' := (mul_eq_zero.mp e).resolve_left hc
      linear_combination e'
  obtain ⟨hK, hq, -, z, hz0, hzK⟩ := TC5_dims K hdef hK5
  have hz0' : rs (zE z) = 0 := rs_zE z
  have hz2 : col (zE z) 2 = (0 : ℂ) • v := by
    funext k
    simp only [col, zE2c, Pi.smul_apply, smul_eq_mul, zero_mul]
  have hradv : ∀ d : V4, ip v (Edb (hvec k0) d) = 0 := by
    intro d
    rw [← Mv_ip v hv1 (hvec k0) d, Mv_hvec v hv1 k0 hvk0]
    simp
  have hradw : ∀ d : V4, ip w (Edb (hvec k0) d) = 0 := by
    intro d
    rw [← Mv_ip w hw1 (hvec k0) d, Mv_hvec w hw1 k0 hwk0]
    simp
  have hker := dY_inj_two K hdef v w hv2 hw2 hg hline hreal
  have r1 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) dYL
  rw [hker, finrank_bot] at r1
  have r2' := rank_nullity K rs
  have hD3 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL) = 3 := by omega
  have hzD : z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL :=
    Submodule.mem_map.mpr ⟨zE z, Submodule.mem_inf.mpr ⟨hzK, LinearMap.mem_ker.mpr hz0'⟩,
      by rw [dYL_apply, dY_zE]⟩
  obtain ⟨Y11, hY11, h011, y2, y3⟩ := hreal 1 1
  by_cases hD : hvec k0 ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL
  · obtain ⟨Zh, hZh, hZhe⟩ := Submodule.mem_map.mp hD
    rw [dYL_apply] at hZhe
    have h1 := Submodule.mem_inf.mp hZh
    have h0h : rs Zh = 0 := LinearMap.mem_ker.mp h1.2
    obtain ⟨⟨c2h, e2h⟩, ⟨c3h, e3h⟩, e4h⟩ := hline Zh h1.1 h0h
    have fv := hF Zh h1.1 h0h c2h e2h
    have fw := hG Zh h1.1 h0h c3h e3h
    rw [hZhe, ← Edb_self, hradv] at fv
    rw [hZhe, ← Edb_self, hradw] at fw
    have z2 : c2h = 0 := by
      have e : t3 v v v * c2h ^ 2 = 0 := by linear_combination -4 * fv
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp ((mul_eq_zero.mp e).resolve_left hτv)
    have z3 : c3h = 0 := by
      have e : t3 w w w * c3h ^ 2 = 0 := by linear_combination -4 * fw
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp ((mul_eq_zero.mp e).resolve_left hτw)
    have k2 : col Zh 2 = 0 := by rw [e2h, z2, zero_smul]
    have k3 : col Zh 3 = 0 := by rw [e3h, z3, zero_smul]
    have hZz := Z_of_nbar Zh k2 k3 e4h (nbar_ker Zh h0h k2 k3 e4h)
    have hhK : zE (hvec k0) ∈ K := by
      rw [← hZhe, ← hZz]
      exact h1.1
    obtain ⟨-, -, -, -, -, -, -, p23, -⟩ := LemmaZ K hdef (hvec k0) hhK Y11 hY11
    rw [y2, y3, one_smul, one_smul, pc_hvec v w hv1 hw1 k0 hvk0 hwk0] at p23
    exact hg (by linear_combination (1 / 2 : ℂ) * p23)
  · have hperp : ∀ b ∈ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL ⊔
        Submodule.span ℂ {hvec k0}), ∑ i, b i * Mv v z i = 0 := by
      intro b hb
      obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp he
      obtain ⟨Zd, hZd, rfl⟩ := Submodule.mem_map.mp hd
      have h1 := Submodule.mem_inf.mp hZd
      have h0d : rs Zd = 0 := LinearMap.mem_ker.mp h1.2
      obtain ⟨⟨cd, ed⟩, -, -⟩ := hline Zd h1.1 h0d
      have bz := hB (zE z) hzK hz0' 0 hz2 Zd h1.1 h0d cd ed
      rw [dY_zE] at bz
      have hsplit : ∑ i, (dYL Zd + t • hvec k0) i * Mv v z i =
          ∑ i, dYL Zd i * Mv v z i + t * ∑ i, hvec k0 i * Mv v z i := by
        simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsplit, Mv_ip v hv1 z, Mv_ip v hv1 z, dYL_apply, bz, Edb_comm, hradv]
      ring
    have hp := perp_bound (Submodule.span ℂ {Mv v z})
      ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL ⊔ Submodule.span ℂ {hvec k0}) (by
        intro a ha b hb
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ha
        have e := hperp b hb
        simp only [Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul] at e ⊢
        linear_combination s * e)
    have hlt : (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL <
        (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL ⊔ Submodule.span ℂ {hvec k0} := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      apply hD
      rw [h]
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    have h4 := Submodule.finrank_lt_finrank_of_lt hlt
    have hy0 : Mv v z = 0 := by
      by_contra hy
      have h1 : Module.finrank ℂ (Submodule.span ℂ {Mv v z}) = 1 := finrank_span_singleton hy
      simp only [Fintype.card_fin] at hp
      omega
    have hzh := Mv_ker v k0 hvk0 hvm z hy0
    have hτz : tau z ≠ 0 := by
      intro h
      apply hz0
      rw [hzh, h]
      simp
    apply hD
    have hT : tau z / 2 ≠ 0 := div_ne_zero hτz two_ne_zero
    have e : hvec k0 = (tau z / 2)⁻¹ • z := by
      calc hvec k0 = (tau z / 2)⁻¹ • ((tau z / 2) • hvec k0) := by
            rw [smul_smul, inv_mul_cancel₀ hT, one_smul]
        _ = (tau z / 2)⁻¹ • z := by rw [← hzh]
    rw [e]
    exact Submodule.smul_mem _ _ hzD

theorem rel_two (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • w) ∧
      col Z 4 = 0)
    (hreal : ∀ l2 l3 : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l2 • v ∧ col Z 3 = l3 • w) :
    t3 v v w = 0 ∧ t3 v w w = 0 := by
  obtain ⟨Z1, hZ1, h01, a2, a3⟩ := hreal 1 1
  obtain ⟨Z2, hZ2, h02, b2, b3⟩ := hreal 1 2
  have e1 := (nbar_eqs K hdef Z1 hZ1 h01).1
  have e2'' := (nbar_eqs K hdef Z2 hZ2 h02).1
  rw [a2, a3, (hline Z1 hZ1 h01).2.2] at e1
  rw [b2, b3, (hline Z2 hZ2 h02).2.2] at e2''
  simp only [t3, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2'' ⊢
  exact ⟨by linear_combination 2 * e1 - (1 / 2 : ℂ) * e2'',
    by linear_combination (1 / 2 : ℂ) * e2'' - e1⟩

theorem P4_k2 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v w : V4) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • w) ∧
      col Z 4 = 0)
    (hreal : ∀ l2 l3 : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l2 • v ∧ col Z 3 = l3 • w) : False := by
  by_cases hpar : ∃ c : ℂ, w = c • v
  · obtain ⟨c, hc⟩ := hpar
    have hc0 : c ≠ 0 := by
      intro h
      apply hw0
      rw [hc, h, zero_smul]
    apply P4_Na K hdef hK5 v hv0 hv1 hv2
    · intro Z hZ h0
      obtain ⟨h2, ⟨c3, h3⟩, h4⟩ := hline Z hZ h0
      exact ⟨h2, ⟨c3 * c, by rw [h3, hc, smul_smul]⟩, h4⟩
    · intro l2 l3
      obtain ⟨Z, hZ, h0, e2, e3⟩ := hreal l2 (l3 / c)
      refine ⟨Z, hZ, h0, e2, ?_⟩
      rw [e3, hc, smul_smul, div_mul_cancel₀ l3 hc0]
  · push_neg at hpar
    have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hpar
    obtain ⟨r1, r2⟩ := rel_two K hdef v w hline hreal
    rcases pair_rel v w hv1 hw1 hv2 hw2 r1 r2 hg with hchi | ⟨k0, hvk0, hwk0, h3m⟩
    · exact P4_Nb_chi K hdef hK5 v w hv0 hv1 hv2 hw1 hw2 hpar hline hreal hchi
    · exact P4_Nb_zero K hdef hK5 v w hv0 hv1 hv2 hw1 hw2 hpar hline hreal k0 hvk0 hwk0 h3m

theorem P4_k2_conf (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v w : V4) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • w) ∧
      col Z 4 = 0) : False := by
  obtain ⟨-, -, hN2, -⟩ := TC5_dims K hdef hK5
  have hS : (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL =
      Submodule.span ℂ (Set.range ![(v, ((0 : V4), (0 : V4))), ((0 : V4), (w, (0 : V4)))]) := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro _ ⟨Z, hZ, rfl⟩
      have h := Submodule.mem_inf.mp hZ
      have h0 : rs Z = 0 := LinearMap.mem_ker.mp h.2
      obtain ⟨⟨c2, e2⟩, ⟨c3, e3⟩, e4⟩ := hline Z h.1 h0
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![c2, c3], ?_⟩
      rw [nbarL_apply, e2, e3, e4]
      simp [Fin.sum_univ_two]
    · have h2 := finrank_range_le_card (R := ℂ) ![(v, ((0 : V4), (0 : V4))), ((0 : V4), (w, (0 : V4)))]
      simp only [Fintype.card_fin, Set.finrank] at h2
      omega
  apply P4_k2 K hdef hK5 v w hv0 hw0 hv1 hv2 hw1 hw2 hline
  intro l2 l3
  have hm : ((l2 • v, (l3 • w, (0 : V4))) : V4 × (V4 × V4)) ∈
      (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL := by
    rw [hS, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![l2, l3], ?_⟩
    simp [Fin.sum_univ_two]
  obtain ⟨Z, hZ, hZe⟩ := Submodule.mem_map.mp hm
  have h := Submodule.mem_inf.mp hZ
  rw [nbarL_apply, Prod.mk.injEq, Prod.mk.injEq] at hZe
  exact ⟨Z, h.1, LinearMap.mem_ker.mp h.2, hZe.1, hZe.2.1⟩

theorem mTC_perm (σ : Equiv.Perm (Fin 5)) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1) :
    (fun a => mTC (σ a)) = mTC := by
  funext a
  by_cases h0 : a = 0
  · rw [h0, hσ0]
  · by_cases h1 : a = 1
    · rw [h1, hσ1]
    · have e0 : σ a ≠ 0 := by
        intro h
        apply h0
        apply σ.injective
        rw [h, hσ0]
      have e1 : σ a ≠ 1 := by
        intro h
        apply h1
        apply σ.injective
        rw [h, hσ1]
      simp only [mTC, if_neg e0, if_neg e1, if_neg h0, if_neg h1]

theorem P4_k2_perm (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (σ : Equiv.Perm (Fin 5)) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1)
    (v w : V4) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z (σ 2) = c • v) ∧ (∃ c : ℂ, col Z (σ 3) = c • w) ∧
      col Z (σ 4) = 0) : False := by
  have hdef' : DefLine (K.map (cperm σ)) mTC := by
    have h := DefLine_perm σ K mTC hdef
    rw [mTC_perm σ hσ0 hσ1] at h
    exact h
  have hinjc : Function.Injective (cperm σ) := by
    intro Y Y' h
    funext p
    obtain ⟨i, j⟩ := p
    have e := congrFun h (i, σ.symm j)
    simp only [cperm_apply, Equiv.apply_symm_apply] at e
    exact e
  have hfr : Module.finrank ℂ (K.map (cperm σ)) = Module.finrank ℂ K :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (cperm σ) hinjc K)).symm
  have hcol : ∀ (Y : M45) (j : Fin 5), col (cperm σ Y) j = col Y (σ j) := by
    intro Y j
    funext i
    rfl
  apply P4_k2_conf (K.map (cperm σ)) hdef' (by omega) v w hv0 hw0 hv1 hv2 hw1 hw2
  rintro _ ⟨Y, hY, rfl⟩ h0
  rw [rs_cperm] at h0
  obtain ⟨⟨c2, e2⟩, ⟨c3, e3⟩, e4⟩ := hline Y hY h0
  exact ⟨⟨c2, by rw [hcol, e2]⟩, ⟨c3, by rw [hcol, e3]⟩, by rw [hcol, e4]⟩

theorem P4_k2_all (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v2 v3 v4 : V4) (t2 : tau v2 = 0) (i2 : ip v2 v2 = 0) (t3' : tau v3 = 0) (i3 : ip v3 v3 = 0)
    (t4' : tau v4 = 0) (i4 : ip v4 v4 = 0)
    (L2 : ∀ Z ∈ K, rs Z = 0 → ∃ c : ℂ, col Z 2 = c • v2)
    (L3 : ∀ Z ∈ K, rs Z = 0 → ∃ c : ℂ, col Z 3 = c • v3)
    (L4 : ∀ Z ∈ K, rs Z = 0 → ∃ c : ℂ, col Z 4 = c • v4)
    (h : (v2 = 0 ∧ v3 ≠ 0 ∧ v4 ≠ 0) ∨ (v2 ≠ 0 ∧ v3 = 0 ∧ v4 ≠ 0) ∨ (v2 ≠ 0 ∧ v3 ≠ 0 ∧ v4 = 0)) :
    False := by
  have zc : ∀ (Z : M45) (j : Fin 5) (u : V4), u = 0 → (∃ c : ℂ, col Z j = c • u) → col Z j = 0 := by
    intro Z j u hu hc
    obtain ⟨c, hc⟩ := hc
    rw [hc, hu, smul_zero]
  rcases h with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
  · apply P4_k2_perm K hdef hK5 (Equiv.swap 2 4) (Equiv.swap_apply_of_ne_of_ne (by decide) (by decide))
      (Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)) v4 v3 h4 h3 t4' i4 t3' i3
    intro Z hZ h0
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 5) ≠ 2) (by decide : (3 : Fin 5) ≠ 4)]
    exact ⟨L4 Z hZ h0, L3 Z hZ h0, zc Z 2 v2 h2 (L2 Z hZ h0)⟩
  · apply P4_k2_perm K hdef hK5 (Equiv.swap 3 4) (Equiv.swap_apply_of_ne_of_ne (by decide) (by decide))
      (Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)) v2 v4 h2 h4 t2 i2 t4' i4
    intro Z hZ h0
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 5) ≠ 3) (by decide : (2 : Fin 5) ≠ 4)]
    exact ⟨L2 Z hZ h0, L4 Z hZ h0, zc Z 3 v3 h3 (L3 Z hZ h0)⟩
  · apply P4_k2_perm K hdef hK5 (Equiv.refl _) rfl rfl v2 v3 h2 h3 t2 i2 t3' i3
    intro Z hZ h0
    exact ⟨L2 Z hZ h0, L3 Z hZ h0, zc Z 4 v4 h4 (L4 Z hZ h0)⟩

theorem P4_c3_Ez (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z : V4) (hzK : zE z ∈ K)
    (hEz : Ed z ≠ 0) (v2 v3 v4 : V4) (t2 : tau v2 = 0) (i2 : ip v2 v2 = 0) (t3' : tau v3 = 0)
    (i3 : ip v3 v3 = 0) (t4' : tau v4 = 0) (i4 : ip v4 v4 = 0) (hv2 : v2 ≠ 0)
    (Y2 : M45) (hY2 : Y2 ∈ K) (e2' : col Y2 2 = v2) (Y3 : M45) (hY3 : Y3 ∈ K) (e3' : col Y3 3 = v3)
    (Y4 : M45) (hY4 : Y4 ∈ K) (e4' : col Y4 4 = v4)
    (p23 : ∀ s : ℂ, v3 ≠ s • v2) (p24 : ∀ s : ℂ, v4 ≠ s • v2) (p34 : ∀ s : ℂ, v4 ≠ s • v3) :
    False := by
  obtain ⟨hq, -, a2, -, -, -⟩ := LemmaZ K hdef z hzK Y2 hY2
  obtain ⟨-, -, -, a3, -, -⟩ := LemmaZ K hdef z hzK Y3 hY3
  obtain ⟨-, -, -, -, a4, -⟩ := LemmaZ K hdef z hzK Y4 hY4
  rw [e2'] at a2
  rw [e3'] at a3
  rw [e4'] at a4
  have hτE : tau (Ed z) = 0 := by rw [tau_Ed, hq, mul_zero]
  exact three_iso_perp (Ed z) v2 v3 v4 hEz hτE t2 i2 t3' i3 t4' i4 a2 a3 a4 hv2 p23 p24 p34

theorem NB_lines' (K : Submodule ℂ M45) (hdef : DefLine K mTC) (j : Fin 5)
    (hj : j = 2 ∨ j = 3 ∨ j = 4) :
    ∃ v : V4, tau v = 0 ∧ ip v v = 0 ∧ (∀ Z ∈ K, rs Z = 0 → ∃ c : ℂ, col Z j = c • v) ∧
      ∃ Z0 ∈ K, rs Z0 = 0 ∧ col Z0 j = v := by
  obtain ⟨v, hv, hall⟩ := line_of_le_one _ (NB_line K hdef j hj)
  obtain ⟨Z0, hZ0, rfl⟩ := Submodule.mem_map.mp hv
  have h0 := Submodule.mem_inf.mp hZ0
  have hrs0 : rs Z0 = 0 := LinearMap.mem_ker.mp h0.2
  obtain ⟨t0, q0⟩ := neut_facts K hdef j hj Z0 h0.1
  refine ⟨colL j Z0, t0, ?_, ?_, Z0, h0.1, hrs0, rfl⟩
  · rw [colL_apply, q0, hrs0]
    simp [ip]
  · intro Z hZ hZ0'
    obtain ⟨c, hc⟩ := hall (colL j Z)
      (Submodule.mem_map.mpr ⟨Z, Submodule.mem_inf.mpr ⟨hZ, LinearMap.mem_ker.mpr hZ0'⟩, rfl⟩)
    exact ⟨c, hc⟩

theorem fin_le_one (S : Submodule ℂ (V4 × (V4 × V4))) (y : V4 × (V4 × V4))
    (h : ∀ s ∈ S, ∃ a : ℂ, s = a • y) : Module.finrank ℂ S ≤ 1 := by
  have hle : S ≤ Submodule.span ℂ {y} := by
    intro s hs
    obtain ⟨a, rfl⟩ := h s hs
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton y))
  by_cases hy : y = 0
  · have hb : Submodule.span ℂ {y} = ⊥ := by
      rw [hy, Submodule.span_singleton_eq_bot]
    have h1 := Submodule.finrank_mono hle
    rw [hb, finrank_bot] at h1
    omega
  · have h1 : Module.finrank ℂ (Submodule.span ℂ {y}) = 1 := finrank_span_singleton hy
    have h2 := Submodule.finrank_mono hle
    omega

theorem P4_k3 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K) :
    ∃ v2 v3 v4 : V4, v2 ≠ 0 ∧ v3 ≠ 0 ∧ v4 ≠ 0 ∧ tau v2 = 0 ∧ ip v2 v2 = 0 ∧ tau v3 = 0 ∧
      ip v3 v3 = 0 ∧ tau v4 = 0 ∧ ip v4 v4 = 0 ∧
      (∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v2) ∧ (∃ c : ℂ, col Z 3 = c • v3) ∧
        (∃ c : ℂ, col Z 4 = c • v4)) ∧
      (∃ Y2 ∈ K, rs Y2 = 0 ∧ col Y2 2 = v2) ∧ (∃ Y3 ∈ K, rs Y3 = 0 ∧ col Y3 3 = v3) ∧
      (∃ Y4 ∈ K, rs Y4 = 0 ∧ col Y4 4 = v4) := by
  obtain ⟨v2, t2, i2, L2, R2⟩ := NB_lines' K hdef 2 (Or.inl rfl)
  obtain ⟨v3, t3', i3, L3, R3⟩ := NB_lines' K hdef 3 (Or.inr (Or.inl rfl))
  obtain ⟨v4, t4', i4, L4, R4⟩ := NB_lines' K hdef 4 (Or.inr (Or.inr rfl))
  obtain ⟨-, -, hN2, -⟩ := TC5_dims K hdef hK5
  have hrep : ∀ s ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map nbarL,
      ∃ c2 c3 c4 : ℂ, s = (c2 • v2, (c3 • v3, c4 • v4)) := by
    rintro _ ⟨Z, hZ, rfl⟩
    have h := Submodule.mem_inf.mp hZ
    have h0 : rs Z = 0 := LinearMap.mem_ker.mp h.2
    obtain ⟨c2, e2⟩ := L2 Z h.1 h0
    obtain ⟨c3, e3⟩ := L3 Z h.1 h0
    obtain ⟨c4, e4⟩ := L4 Z h.1 h0
    exact ⟨c2, c3, c4, by rw [nbarL_apply, e2, e3, e4]⟩
  have two_zero : ∀ y : V4 × (V4 × V4), (∀ c2 c3 c4 : ℂ, ∃ a : ℂ,
      ((c2 • v2, (c3 • v3, c4 • v4)) : V4 × (V4 × V4)) = a • y) → False := by
    intro y hy
    have h1 := fin_le_one _ y (by
      intro s hs
      obtain ⟨c2, c3, c4, rfl⟩ := hrep s hs
      exact hy c2 c3 c4)
    omega
  have hnz : v2 ≠ 0 ∧ v3 ≠ 0 ∧ v4 ≠ 0 := by
    by_cases z2 : v2 = 0 <;> by_cases z3 : v3 = 0 <;> by_cases z4 : v4 = 0
    · exact (two_zero 0 (fun c2 c3 c4 => ⟨0, by rw [z2, z3, z4]; simp⟩)).elim
    · exact (two_zero ((0 : V4), ((0 : V4), v4))
        (fun c2 c3 c4 => ⟨c4, by rw [z2, z3]; simp⟩)).elim
    · exact (two_zero ((0 : V4), (v3, (0 : V4)))
        (fun c2 c3 c4 => ⟨c3, by rw [z2, z4]; simp⟩)).elim
    · exact (P4_k2_all K hdef hK5 v2 v3 v4 t2 i2 t3' i3 t4' i4 L2 L3 L4
        (Or.inl ⟨z2, z3, z4⟩)).elim
    · exact (two_zero (v2, ((0 : V4), (0 : V4)))
        (fun c2 c3 c4 => ⟨c2, by rw [z3, z4]; simp⟩)).elim
    · exact (P4_k2_all K hdef hK5 v2 v3 v4 t2 i2 t3' i3 t4' i4 L2 L3 L4
        (Or.inr (Or.inl ⟨z2, z3, z4⟩))).elim
    · exact (P4_k2_all K hdef hK5 v2 v3 v4 t2 i2 t3' i3 t4' i4 L2 L3 L4
        (Or.inr (Or.inr ⟨z2, z3, z4⟩))).elim
    · exact ⟨z2, z3, z4⟩
  exact ⟨v2, v3, v4, hnz.1, hnz.2.1, hnz.2.2, t2, i2, t3', i3, t4', i4,
    fun Z hZ h0 => ⟨L2 Z hZ h0, L3 Z hZ h0, L4 Z hZ h0⟩, R2, R3, R4⟩

theorem Edb_add_l (a b c : V4) : Edb (a + b) c = fun k => Edb a c k + Edb b c k := by
  funext k
  simp only [Edb, e2b, tau, ip, Pi.add_apply]
  ring

theorem kerEdb (z d : V4) (hz0 : z ≠ 0) (hq : e2 z = 0) (hE : Ed z = 0) (hdz : e2b d z = 0)
    (hED : Edb d z = 0) : d = (tau d / tau z) • z := by
  have hk : ∀ k, z k * (z k - tau z) = 0 := by
    intro k
    have e := congrFun hE k
    simp only [Ed, Pi.zero_apply] at e
    rw [hq] at e
    linear_combination e
  have hτ : tau z ≠ 0 := by
    intro h
    apply hz0
    funext k
    have e := hk k
    rw [h, sub_zero] at e
    exact mul_self_eq_zero.mp e
  funext k
  have e := congrFun hED k
  simp only [Edb, Pi.zero_apply] at e
  rw [hdz] at e
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases mul_eq_zero.mp (hk k) with h | h
  · rw [h] at e ⊢
    have e' : tau z * d k = 0 := by linear_combination -2 * e
    rw [(mul_eq_zero.mp e').resolve_left hτ]
    ring
  · have hzk : z k = tau z := by linear_combination h
    rw [hzk] at e ⊢
    have e' : tau z * (d k - tau d) = 0 := by linear_combination 2 * e
    have e'' := (mul_eq_zero.mp e').resolve_left hτ
    rw [div_mul_cancel₀ _ hτ]
    linear_combination e''

theorem DZ_perp (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z : V4) (hzK : zE z ∈ K) (Y : M45)
    (hY : Y ∈ K) :
    ip (col Y 2) (Edb (dY Y) z) = 0 ∧ ip (col Y 3) (Edb (dY Y) z) = 0 ∧
      ip (col Y 4) (Edb (dY Y) z) = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, q34, q24, q23, -⟩ := LemmaZ K hdef z hzK Y hY
  have hadd : ∀ x y : V4, ip (x + y) (Edb (dY Y) z) = ip x (Edb (dY Y) z) + ip y (Edb (dY Y) z) := by
    intro x y
    simp only [ip, Pi.add_apply]
    ring
  rw [hadd] at q34 q24 q23
  exact ⟨by linear_combination (1 / 2 : ℂ) * (q24 + q23 - q34),
    by linear_combination (1 / 2 : ℂ) * (q34 + q23 - q24),
    by linear_combination (1 / 2 : ℂ) * (q34 + q24 - q23)⟩

theorem perp_line (K : Submodule ℂ M45) (z : V4) (j : Fin 5) (v : V4)
    (hf : ∀ Y ∈ K, ip (col Y j) (Edb (dY Y) z) = 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ c : ℂ, col Z j = c • v)
    (Yj : M45) (hYjK : Yj ∈ K) (hYj : col Yj j = v) (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0) :
    ip v (Edb (dY Z) z) = 0 := by
  obtain ⟨c, hc⟩ := hline Z hZ h0
  have f1 := hf Z hZ
  have f2 := hf Yj hYjK
  have f3 := hf (Z + Yj) (K.add_mem hZ hYjK)
  have hcol : col (Z + Yj) j = col Z j + col Yj j := by
    funext k
    rfl
  rw [hcol, dY_add, Edb_add_l, hc, hYj] at f3
  rw [hc] at f1
  rw [hYj] at f2
  simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at f1 f2 f3 ⊢
  linear_combination f3 - f1 - f2 - c * f2

theorem c3_Qbar (K : Submodule ℂ M45) (hdef : DefLine K mTC) (z : V4) (hz0 : z ≠ 0)
    (hzK : zE z ∈ K) (hEz : Ed z = 0) (v2 v3 v4 : V4) (t2 : tau v2 = 0) (i2 : ip v2 v2 = 0)
    (t3' : tau v3 = 0) (i3 : ip v3 v3 = 0) (t4' : tau v4 = 0) (i4 : ip v4 v4 = 0) (hv2 : v2 ≠ 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v2) ∧ (∃ c : ℂ, col Z 3 = c • v3) ∧
      (∃ c : ℂ, col Z 4 = c • v4))
    (Y2 : M45) (hY2 : Y2 ∈ K) (e2' : col Y2 2 = v2) (Y3 : M45) (hY3 : Y3 ∈ K) (e3' : col Y3 3 = v3)
    (Y4 : M45) (hY4 : Y4 ∈ K) (e4' : col Y4 4 = v4)
    (p23 : ∀ s : ℂ, v3 ≠ s • v2) (p24 : ∀ s : ℂ, v4 ≠ s • v2) (p34 : ∀ s : ℂ, v4 ≠ s • v3)
    (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0) : ip (uY Z) (uY Z) = 0 := by
  have hq : e2 z = 0 := (LemmaZ K hdef z hzK Z hZ).1
  have hdz : e2b (dY Z) z = 0 := (LemmaZ K hdef z hzK Z hZ).2.1
  have a2 := perp_line K z 2 v2 (fun Y hY => (DZ_perp K hdef z hzK Y hY).1)
    (fun Y hY h => (hline Y hY h).1) Y2 hY2 e2' Z hZ h0
  have a3 := perp_line K z 3 v3 (fun Y hY => (DZ_perp K hdef z hzK Y hY).2.1)
    (fun Y hY h => (hline Y hY h).2.1) Y3 hY3 e3' Z hZ h0
  have a4 := perp_line K z 4 v4 (fun Y hY => (DZ_perp K hdef z hzK Y hY).2.2)
    (fun Y hY h => (hline Y hY h).2.2) Y4 hY4 e4' Z hZ h0
  have hED : Edb (dY Z) z = 0 := by
    by_contra hne
    have hτ : tau (Edb (dY Z) z) = 0 := by rw [tau_Edb, hdz, mul_zero]
    exact three_iso_perp (Edb (dY Z) z) v2 v3 v4 hne hτ t2 i2 t3' i3 t4' i4 a2 a3 a4 hv2 p23 p24 p34
  have hd := kerEdb z (dY Z) hz0 hq hEz hdz hED
  have he : e2 (dY Z) = 0 := by
    rw [hd]
    have e := e2_comb z z (tau (dY Z) / tau z) 0
    simp only [zero_smul, add_zero] at e
    rw [e, hq]
    ring
  have e := TC5_qbar1 K hdef Z hZ
  rw [h0, he] at e
  simp only [ip, Pi.zero_apply] at e ⊢
  linear_combination e

theorem uY_of_rs3 (Z : M45) (h0 : rs Z = 0) (v2 v3 v4 : V4) (c2 c3 c4 : ℂ) (h2 : col Z 2 = c2 • v2)
    (h3 : col Z 3 = c3 • v3) (h4 : col Z 4 = c4 • v4) :
    uY Z = fun k => -(c2 * v2 k + c3 * v3 k + c4 * v4 k) / 2 := by
  funext k
  have e := congrFun h0 k
  rw [rs_apply] at e
  have e' : Z (k, 0) + Z (k, 1) + Z (k, 2) + Z (k, 3) + Z (k, 4) = 0 := e
  have g2 := congrFun h2 k
  have g3 := congrFun h3 k
  have g4 := congrFun h4 k
  simp only [col, Pi.smul_apply, smul_eq_mul] at g2 g3 g4
  simp only [uY]
  linear_combination (1 / 2 : ℂ) * e' - (1 / 2 : ℂ) * (g2 + g3 + g4)

theorem indep3 (v2 v3 v4 : V4) (i2 : ip v2 v2 = 0) (i3 : ip v3 v3 = 0) (i4 : ip v4 v4 = 0)
    (g23 : ip v2 v3 ≠ 0) (g24 : ip v2 v4 ≠ 0) (g34 : ip v3 v4 ≠ 0) (α β γ : ℂ)
    (h : ∀ k, α * v2 k + β * v3 k + γ * v4 k = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have e1 : β * ip v2 v3 + γ * ip v2 v4 = 0 := by
    simp only [ip] at i2 ⊢
    linear_combination v2 0 * h0 + v2 1 * h1 + v2 2 * h2 + v2 3 * h3 - α * i2
  have e2 : α * ip v2 v3 + γ * ip v3 v4 = 0 := by
    simp only [ip] at i3 ⊢
    linear_combination v3 0 * h0 + v3 1 * h1 + v3 2 * h2 + v3 3 * h3 - β * i3
  have e3 : α * ip v2 v4 + β * ip v3 v4 = 0 := by
    simp only [ip] at i4 ⊢
    linear_combination v4 0 * h0 + v4 1 * h1 + v4 2 * h2 + v4 3 * h3 - γ * i4
  have hγ : (2 * ip v3 v4 * ip v2 v4) * γ = 0 := by
    linear_combination ip v2 v4 * e2 - ip v2 v3 * e3 + ip v3 v4 * e1
  have hγ0 : γ = 0 :=
    (mul_eq_zero.mp hγ).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero g34) g24)
  have hβ0 : β = 0 := by
    have e : β * ip v2 v3 = 0 := by linear_combination e1 - ip v2 v4 * hγ0
    exact (mul_eq_zero.mp e).resolve_right g23
  have hα0 : α = 0 := by
    have e : α * ip v2 v3 = 0 := by linear_combination e2 - ip v3 v4 * hγ0
    exact (mul_eq_zero.mp e).resolve_right g23
  exact ⟨hα0, hβ0, hγ0⟩

theorem c3_final (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v2 v3 v4 : V4) (i2 : ip v2 v2 = 0) (i3 : ip v3 v3 = 0) (i4 : ip v4 v4 = 0)
    (g23 : ip v2 v3 ≠ 0) (g24 : ip v2 v4 ≠ 0) (g34 : ip v3 v4 ≠ 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v2) ∧ (∃ c : ℂ, col Z 3 = c • v3) ∧
      (∃ c : ℂ, col Z 4 = c • v4))
    (hQ : ∀ Z ∈ K, rs Z = 0 → ip (uY Z) (uY Z) = 0) : False := by
  have hLK : ∀ Y ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45), Y ∈ K ∧ rs Y = 0 :=
    fun Y hY => ⟨(Submodule.mem_inf.mp hY).1, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hY).2⟩
  have hU := iso_image (K ⊓ LinearMap.ker rs : Submodule ℂ M45)
    (fun Y hY => (TC5_tau K hdef Y (hLK Y hY).1).1) (fun Y hY => hQ Y (hLK Y hY).1 (hLK Y hY).2)
  have hcols : ∀ Z ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker uYL : Submodule ℂ M45),
      Z ∈ K ∧ Z = zE (dY Z) := by
    intro Z hZ
    have h1 := Submodule.mem_inf.mp hZ
    obtain ⟨hK, h0⟩ := hLK Z h1.1
    have hu : uY Z = 0 := LinearMap.mem_ker.mp h1.2
    obtain ⟨⟨c2, e2⟩, ⟨c3, e3⟩, ⟨c4, e4⟩⟩ := hline Z hK h0
    have hu3 := uY_of_rs3 Z h0 v2 v3 v4 c2 c3 c4 e2 e3 e4
    rw [hu] at hu3
    obtain ⟨z2, z3, z4⟩ := indep3 v2 v3 v4 i2 i3 i4 g23 g24 g34 c2 c3 c4 (fun k => by
      have e := congrFun hu3 k
      simp only [Pi.zero_apply] at e
      linear_combination 2 * e)
    have k2 : col Z 2 = 0 := by rw [e2, z2, zero_smul]
    have k3 : col Z 3 = 0 := by rw [e3, z3, zero_smul]
    have k4 : col Z 4 = 0 := by rw [e4, z4, zero_smul]
    exact ⟨hK, Z_of_nbar Z k2 k3 k4 hu⟩
  have hW : ∀ z ∈ ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker uYL : Submodule ℂ M45).map dYL,
      zE z ∈ K := by
    rintro _ ⟨Z, hZ, rfl⟩
    obtain ⟨hK, hZe⟩ := hcols Z hZ
    rw [dYL_apply, ← hZe]
    exact hK
  have h1 := zeta_le_one K hdef hK5 _ hW
  have hker : (((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker uYL) ⊓ LinearMap.ker dYL :
      Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hZ1 := (Submodule.mem_inf.mp hZ).1
    have hd : dY Z = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2
    obtain ⟨-, hZe⟩ := hcols Z hZ1
    rw [hZe, hd]
    funext p
    obtain ⟨k, j⟩ := p
    simp [zE]
  have r3 := rank_nullity ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker uYL : Submodule ℂ M45) dYL
  rw [hker, finrank_bot] at r3
  have r2 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) uYL
  obtain ⟨hK, hq, -, -⟩ := TC5_dims K hdef hK5
  have r1 := rank_nullity K rs
  omega

theorem TC5_c3 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v2 v3 v4 : V4) (hv2 : v2 ≠ 0) (hv3 : v3 ≠ 0) (t2 : tau v2 = 0) (i2 : ip v2 v2 = 0)
    (t3' : tau v3 = 0) (i3 : ip v3 v3 = 0) (t4' : tau v4 = 0) (i4 : ip v4 v4 = 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v2) ∧ (∃ c : ℂ, col Z 3 = c • v3) ∧
      (∃ c : ℂ, col Z 4 = c • v4))
    (Y2 : M45) (hY2 : Y2 ∈ K) (e2' : col Y2 2 = v2) (Y3 : M45) (hY3 : Y3 ∈ K) (e3' : col Y3 3 = v3)
    (Y4 : M45) (hY4 : Y4 ∈ K) (e4' : col Y4 4 = v4)
    (p23 : ∀ s : ℂ, v3 ≠ s • v2) (p24 : ∀ s : ℂ, v4 ≠ s • v2) (p34 : ∀ s : ℂ, v4 ≠ s • v3) :
    False := by
  obtain ⟨-, -, -, z, hz0, hzK⟩ := TC5_dims K hdef hK5
  by_cases hEz : Ed z = 0
  · have g23 := ip_ne_of_line v2 v3 hv2 t2 i2 t3' i3 p23
    have g24 := ip_ne_of_line v2 v4 hv2 t2 i2 t4' i4 p24
    have g34 := ip_ne_of_line v3 v4 hv3 t3' i3 t4' i4 p34
    exact c3_final K hdef hK5 v2 v3 v4 i2 i3 i4 g23 g24 g34 hline
      (fun Z hZ h0 => c3_Qbar K hdef z hz0 hzK hEz v2 v3 v4 t2 i2 t3' i3 t4' i4 hv2 hline Y2 hY2 e2'
        Y3 hY3 e3' Y4 hY4 e4' p23 p24 p34 Z hZ h0)
  · exact P4_c3_Ez K hdef z hzK hEz v2 v3 v4 t2 i2 t3' i3 t4' i4 hv2 Y2 hY2 e2' Y3 hY3 e3' Y4 hY4 e4'
      p23 p24 p34

theorem c2_X3c5 (v w : V4) (hv : tau v = 0) (hw : tau w = 0) (l3 l4 b : ℂ) :
    X3c (fun k => -(l3 * v k + l4 * v k + b * w k) / 2) (fun k => -(l3 * v k + l4 * v k + b * w k) / 2) (l3 • v) (l4 • v) =
      2 * ((l3 + l4) * (((l3 + l4) ^ 2 * t3 v v v + 2 * (l3 + l4) * b * t3 v v w + b ^ 2 * t3 v w w) / 4) + 2 * l3 * l4 * (-((l3 + l4) * t3 v v v + b * t3 v v w) / 2)) := by
  simp only [X3c, tau, ip, t3, Pi.smul_apply, smul_eq_mul] at hv hw ⊢
  linear_combination (b^2*l3*w 0*w 1/2 + b^2*l3*w 0*w 2/2 + b^2*l3*w 1*w 2/2 - b^2*l3*w 3^2/2 + b^2*l4*w 0*w 1/2 + b^2*l4*w 0*w 2/2 + b^2*l4*w 1*w 2/2 - b^2*l4*w 3^2/2 + b*l3^2*v 0*w 1 + b*l3^2*v 0*w 2 + b*l3^2*v 0*w 3 + b*l3^2*v 1*w 0 + b*l3^2*v 1*w 2 + b*l3^2*v 1*w 3 + b*l3^2*v 2*w 0 + b*l3^2*v 2*w 1 + b*l3^2*v 2*w 3 - b*l3^2*v 3*w 3 + b*l4^2*v 0*w 1 + b*l4^2*v 0*w 2 + b*l4^2*v 0*w 3 + b*l4^2*v 1*w 0 + b*l4^2*v 1*w 2 + b*l4^2*v 1*w 3 + b*l4^2*v 2*w 0 + b*l4^2*v 2*w 1 + b*l4^2*v 2*w 3 - b*l4^2*v 3*w 3 - l3^3*v 0^2/2 + l3^3*v 0*v 1/2 + l3^3*v 0*v 2/2 + l3^3*v 0*v 3/2 - l3^3*v 1^2/2 + l3^3*v 1*v 2/2 + l3^3*v 1*v 3/2 - l3^3*v 2^2/2 + l3^3*v 2*v 3/2 - l3^3*v 3^2/2 + l3^2*l4*v 0^2/2 - l3^2*l4*v 0*v 1/2 - l3^2*l4*v 0*v 2/2 - l3^2*l4*v 0*v 3/2 + l3^2*l4*v 1^2/2 - l3^2*l4*v 1*v 2/2 - l3^2*l4*v 1*v 3/2 + l3^2*l4*v 2^2/2 - l3^2*l4*v 2*v 3/2 + l3^2*l4*v 3^2/2 + l3*l4^2*v 0^2/2 - l3*l4^2*v 0*v 1/2 - l3*l4^2*v 0*v 2/2 - l3*l4^2*v 0*v 3/2 + l3*l4^2*v 1^2/2 - l3*l4^2*v 1*v 2/2 - l3*l4^2*v 1*v 3/2 + l3*l4^2*v 2^2/2 - l3*l4^2*v 2*v 3/2 + l3*l4^2*v 3^2/2 - l4^3*v 0^2/2 + l4^3*v 0*v 1/2 + l4^3*v 0*v 2/2 + l4^3*v 0*v 3/2 - l4^3*v 1^2/2 + l4^3*v 1*v 2/2 + l4^3*v 1*v 3/2 - l4^3*v 2^2/2 + l4^3*v 2*v 3/2 - l4^3*v 3^2/2) * hv + (-b^2*l3*v 0*w 0/2 + b^2*l3*v 0*w 3/2 - b^2*l3*v 1*w 1/2 + b^2*l3*v 1*w 3/2 - b^2*l3*v 2*w 2/2 + b^2*l3*v 2*w 3/2 - b^2*l4*v 0*w 0/2 + b^2*l4*v 0*w 3/2 - b^2*l4*v 1*w 1/2 + b^2*l4*v 1*w 3/2 - b^2*l4*v 2*w 2/2 + b^2*l4*v 2*w 3/2 - b*l3^2*v 0^2 - b*l3^2*v 0*v 1 - b*l3^2*v 0*v 2 - b*l3^2*v 1^2 - b*l3^2*v 1*v 2 - b*l3^2*v 2^2 - b*l4^2*v 0^2 - b*l4^2*v 0*v 1 - b*l4^2*v 0*v 2 - b*l4^2*v 1^2 - b*l4^2*v 1*v 2 - b*l4^2*v 2^2) * hw

theorem c2_X3c3 (v w : V4) (hv : tau v = 0) (hw : tau w = 0) (l3 l4 b : ℂ) :
    X3c (fun k => -(l3 * v k + l4 * v k + b * w k) / 2) (fun k => -(l3 * v k + l4 * v k + b * w k) / 2) (l4 • v) (b • w) =
      2 * (l4 * (((l3 + l4) ^ 2 * t3 v v v + 2 * (l3 + l4) * b * t3 v v w + b ^ 2 * t3 v w w) / 4) + b * (((l3 + l4) ^ 2 * t3 v v w + 2 * (l3 + l4) * b * t3 v w w + b ^ 2 * t3 w w w) / 4) + 2 * l4 * b * (-((l3 + l4) * t3 v v w + b * t3 v w w) / 2)) := by
  simp only [X3c, tau, ip, t3, Pi.smul_apply, smul_eq_mul] at hv hw ⊢
  linear_combination (b^2*l3*w 0*w 1 + b^2*l3*w 0*w 2 + b^2*l3*w 1*w 2 - b^2*l3*w 3^2 - b^2*l4*w 0*w 1/2 - b^2*l4*w 0*w 2/2 - b^2*l4*w 1*w 2/2 + b^2*l4*w 3^2/2 + b*l3^2*v 0*w 1/2 + b*l3^2*v 0*w 2/2 + b*l3^2*v 0*w 3/2 + b*l3^2*v 1*w 0/2 + b*l3^2*v 1*w 2/2 + b*l3^2*v 1*w 3/2 + b*l3^2*v 2*w 0/2 + b*l3^2*v 2*w 1/2 + b*l3^2*v 2*w 3/2 - b*l3^2*v 3*w 3/2 - b*l4^2*v 0*w 1/2 - b*l4^2*v 0*w 2/2 - b*l4^2*v 0*w 3/2 - b*l4^2*v 1*w 0/2 - b*l4^2*v 1*w 2/2 - b*l4^2*v 1*w 3/2 - b*l4^2*v 2*w 0/2 - b*l4^2*v 2*w 1/2 - b*l4^2*v 2*w 3/2 + b*l4^2*v 3*w 3/2 - l3^2*l4*v 0^2/2 + l3^2*l4*v 0*v 1/2 + l3^2*l4*v 0*v 2/2 + l3^2*l4*v 0*v 3/2 - l3^2*l4*v 1^2/2 + l3^2*l4*v 1*v 2/2 + l3^2*l4*v 1*v 3/2 - l3^2*l4*v 2^2/2 + l3^2*l4*v 2*v 3/2 - l3^2*l4*v 3^2/2 - l3*l4^2*v 0^2 + l3*l4^2*v 0*v 1 + l3*l4^2*v 0*v 2 + l3*l4^2*v 0*v 3 - l3*l4^2*v 1^2 + l3*l4^2*v 1*v 2 + l3*l4^2*v 1*v 3 - l3*l4^2*v 2^2 + l3*l4^2*v 2*v 3 - l3*l4^2*v 3^2 - l4^3*v 0^2/2 + l4^3*v 0*v 1/2 + l4^3*v 0*v 2/2 + l4^3*v 0*v 3/2 - l4^3*v 1^2/2 + l4^3*v 1*v 2/2 + l4^3*v 1*v 3/2 - l4^3*v 2^2/2 + l4^3*v 2*v 3/2 - l4^3*v 3^2/2) * hv + (-b^3*w 0^2/2 + b^3*w 0*w 1/2 + b^3*w 0*w 2/2 + b^3*w 0*w 3/2 - b^3*w 1^2/2 + b^3*w 1*w 2/2 + b^3*w 1*w 3/2 - b^3*w 2^2/2 + b^3*w 2*w 3/2 - b^3*w 3^2/2 - b^2*l3*v 0*w 0 + b^2*l3*v 0*w 3 - b^2*l3*v 1*w 1 + b^2*l3*v 1*w 3 - b^2*l3*v 2*w 2 + b^2*l3*v 2*w 3 + b^2*l4*v 0*w 0/2 - b^2*l4*v 0*w 3/2 + b^2*l4*v 1*w 1/2 - b^2*l4*v 1*w 3/2 + b^2*l4*v 2*w 2/2 - b^2*l4*v 2*w 3/2 - b*l3^2*v 0^2/2 - b*l3^2*v 0*v 1/2 - b*l3^2*v 0*v 2/2 - b*l3^2*v 1^2/2 - b*l3^2*v 1*v 2/2 - b*l3^2*v 2^2/2 + b*l4^2*v 0^2/2 + b*l4^2*v 0*v 1/2 + b*l4^2*v 0*v 2/2 + b*l4^2*v 1^2/2 + b*l4^2*v 1*v 2/2 + b*l4^2*v 2^2/2) * hw

theorem c2_X3c4 (v w : V4) (hv : tau v = 0) (hw : tau w = 0) (l3 l4 b : ℂ) :
    X3c (fun k => -(l3 * v k + l4 * v k + b * w k) / 2) (fun k => -(l3 * v k + l4 * v k + b * w k) / 2) (l3 • v) (b • w) =
      2 * (l3 * (((l3 + l4) ^ 2 * t3 v v v + 2 * (l3 + l4) * b * t3 v v w + b ^ 2 * t3 v w w) / 4) + b * (((l3 + l4) ^ 2 * t3 v v w + 2 * (l3 + l4) * b * t3 v w w + b ^ 2 * t3 w w w) / 4) + 2 * l3 * b * (-((l3 + l4) * t3 v v w + b * t3 v w w) / 2)) := by
  simp only [X3c, tau, ip, t3, Pi.smul_apply, smul_eq_mul] at hv hw ⊢
  linear_combination (-b^2*l3*w 0*w 1/2 - b^2*l3*w 0*w 2/2 - b^2*l3*w 1*w 2/2 + b^2*l3*w 3^2/2 + b^2*l4*w 0*w 1 + b^2*l4*w 0*w 2 + b^2*l4*w 1*w 2 - b^2*l4*w 3^2 - b*l3^2*v 0*w 1/2 - b*l3^2*v 0*w 2/2 - b*l3^2*v 0*w 3/2 - b*l3^2*v 1*w 0/2 - b*l3^2*v 1*w 2/2 - b*l3^2*v 1*w 3/2 - b*l3^2*v 2*w 0/2 - b*l3^2*v 2*w 1/2 - b*l3^2*v 2*w 3/2 + b*l3^2*v 3*w 3/2 + b*l4^2*v 0*w 1/2 + b*l4^2*v 0*w 2/2 + b*l4^2*v 0*w 3/2 + b*l4^2*v 1*w 0/2 + b*l4^2*v 1*w 2/2 + b*l4^2*v 1*w 3/2 + b*l4^2*v 2*w 0/2 + b*l4^2*v 2*w 1/2 + b*l4^2*v 2*w 3/2 - b*l4^2*v 3*w 3/2 - l3^3*v 0^2/2 + l3^3*v 0*v 1/2 + l3^3*v 0*v 2/2 + l3^3*v 0*v 3/2 - l3^3*v 1^2/2 + l3^3*v 1*v 2/2 + l3^3*v 1*v 3/2 - l3^3*v 2^2/2 + l3^3*v 2*v 3/2 - l3^3*v 3^2/2 - l3^2*l4*v 0^2 + l3^2*l4*v 0*v 1 + l3^2*l4*v 0*v 2 + l3^2*l4*v 0*v 3 - l3^2*l4*v 1^2 + l3^2*l4*v 1*v 2 + l3^2*l4*v 1*v 3 - l3^2*l4*v 2^2 + l3^2*l4*v 2*v 3 - l3^2*l4*v 3^2 - l3*l4^2*v 0^2/2 + l3*l4^2*v 0*v 1/2 + l3*l4^2*v 0*v 2/2 + l3*l4^2*v 0*v 3/2 - l3*l4^2*v 1^2/2 + l3*l4^2*v 1*v 2/2 + l3*l4^2*v 1*v 3/2 - l3*l4^2*v 2^2/2 + l3*l4^2*v 2*v 3/2 - l3*l4^2*v 3^2/2) * hv + (-b^3*w 0^2/2 + b^3*w 0*w 1/2 + b^3*w 0*w 2/2 + b^3*w 0*w 3/2 - b^3*w 1^2/2 + b^3*w 1*w 2/2 + b^3*w 1*w 3/2 - b^3*w 2^2/2 + b^3*w 2*w 3/2 - b^3*w 3^2/2 + b^2*l3*v 0*w 0/2 - b^2*l3*v 0*w 3/2 + b^2*l3*v 1*w 1/2 - b^2*l3*v 1*w 3/2 + b^2*l3*v 2*w 2/2 - b^2*l3*v 2*w 3/2 - b^2*l4*v 0*w 0 + b^2*l4*v 0*w 3 - b^2*l4*v 1*w 1 + b^2*l4*v 1*w 3 - b^2*l4*v 2*w 2 + b^2*l4*v 2*w 3 + b*l3^2*v 0^2/2 + b*l3^2*v 0*v 1/2 + b*l3^2*v 0*v 2/2 + b*l3^2*v 1^2/2 + b*l3^2*v 1*v 2/2 + b*l3^2*v 2^2/2 - b*l4^2*v 0^2/2 - b*l4^2*v 0*v 1/2 - b*l4^2*v 0*v 2/2 - b*l4^2*v 1^2/2 - b*l4^2*v 1*v 2/2 - b*l4^2*v 2^2/2) * hw

theorem c2_rels (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4) (hv : tau v = 0)
    (hw : tau w = 0) (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0) (l3 l4 b : ℂ) (h2 : col Z 2 = l3 • v)
    (h3 : col Z 3 = l4 • v) (h4 : col Z 4 = b • w) :
    (l3 + l4) * ip v (Ed (dY Z)) = (l3 + l4) * (((l3 + l4) ^ 2 * t3 v v v + 2 * (l3 + l4) * b * t3 v v w
        + b ^ 2 * t3 v w w) / 4) + 2 * l3 * l4 * (-((l3 + l4) * t3 v v v + b * t3 v v w) / 2) ∧
    l4 * ip v (Ed (dY Z)) + b * ip w (Ed (dY Z)) = l4 * (((l3 + l4) ^ 2 * t3 v v v
        + 2 * (l3 + l4) * b * t3 v v w + b ^ 2 * t3 v w w) / 4) + b * (((l3 + l4) ^ 2 * t3 v v w
        + 2 * (l3 + l4) * b * t3 v w w + b ^ 2 * t3 w w w) / 4)
        + 2 * l4 * b * (-((l3 + l4) * t3 v v w + b * t3 v w w) / 2) ∧
    l3 * ip v (Ed (dY Z)) + b * ip w (Ed (dY Z)) = l3 * (((l3 + l4) ^ 2 * t3 v v v
        + 2 * (l3 + l4) * b * t3 v v w + b ^ 2 * t3 v w w) / 4) + b * (((l3 + l4) ^ 2 * t3 v v w
        + 2 * (l3 + l4) * b * t3 v w w + b ^ 2 * t3 w w w) / 4)
        + 2 * l3 * b * (-((l3 + l4) * t3 v v w + b * t3 v w w) / 2) ∧
    l3 * l4 * ((l3 + l4) * t3 v v v - b * t3 v v w) + (l3 + l4) * b * ((l3 + l4) * t3 v v w
        + b * t3 v w w) = 0 := by
  have hu := uY_of_rs3 Z h0 v v w l3 l4 b h2 h3 h4
  obtain ⟨-, ⟨b34, b24, b23⟩, -⟩ := TC5_degree K hdef Z hZ
  rw [hu, h2, h3, c2_X3c5 v w hv hw] at b23
  rw [hu, h3, h4, c2_X3c3 v w hv hw] at b34
  rw [hu, h2, h4, c2_X3c4 v w hv hw] at b24
  have hadd : ∀ (x y : V4) (p q : ℂ), ip (p • x + q • y) (Ed (dY Z)) =
      p * ip x (Ed (dY Z)) + q * ip y (Ed (dY Z)) := by
    intro x y p q
    simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hadd] at b23 b34 b24
  have c := (nbar_eqs K hdef Z hZ h0).1
  rw [h2, h3, h4] at c
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-1 / 2 : ℂ) * b23
  · linear_combination (-1 / 2 : ℂ) * b34
  · linear_combination (-1 / 2 : ℂ) * b24
  · simp only [t3, Pi.smul_apply, smul_eq_mul] at c ⊢
    linear_combination c

theorem chi_t12 (v : V4) (kap : ℂ) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap) (hv1 : tau v = 0)
    (hv2 : ip v v = 0) (hv3 : t3 v v v = 0) (w : V4) (hw1 : tau w = 0) (hw2 : ip w w = 0)
    (h12 : t3 v w w = 0) : t3 v v w = 0 := by
  obtain ⟨p, q, r, hwq⟩ := Qv_V v kap hkap hk hv1 hv2 hv3 w hw1
  have hvq : v = Qv v 0 1 0 0 := by
    funext i
    simp only [Qv]
    ring
  have hvvq : (fun k => v k * v k : V4) = Qv v 0 0 1 0 := by
    funext i
    simp only [Qv]
    ring
  have hipn : ∀ c0 c1 c2 c3 : ℂ,
      ip v (Qv v c0 c1 c2 c3) = 4 * (0 * c0 + kap * (1 * c3 + 0 * c2 + 0 * c1)) := by
    intro c0 c1 c2 c3
    calc ip v (Qv v c0 c1 c2 c3) = ip (Qv v 0 1 0 0) (Qv v c0 c1 c2 c3) := by rw [← hvq]
      _ = 4 * (0 * c0 + kap * (1 * c3 + 0 * c2 + 0 * c1)) :=
        ip_Qv v kap hk hv1 hv2 hv3 0 1 0 0 c0 c1 c2 c3
  have e12 : t3 v w w = ip v (fun k => w k * w k) := by
    simp only [t3, ip]
    ring
  have e21 : t3 v v w = ip (fun k => v k * v k) w := rfl
  rw [e12, hwq, Qv_mul v kap hk, hipn] at h12
  have iso := hw2
  rw [hwq, ip_Qv v kap hk hv1 hv2 hv3] at iso
  rw [e21, hvvq, hwq, ip_Qv v kap hk hv1 hv2 hv3]
  have hpq : p * q = 0 := by
    have h : kap * (p * q) = 0 := by linear_combination (1 / 8 : ℂ) * h12
    exact (mul_eq_zero.mp h).resolve_left hkap
  rcases mul_eq_zero.mp hpq with hp | hq
  · have hq : q = 0 := by
      have h : kap * (q * q) = 0 := by
        rw [hp] at iso
        linear_combination (1 / 4 : ℂ) * iso
      exact mul_self_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hkap)
    rw [hq]
    ring
  · rw [hq]
    ring

theorem P4_c2i (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v w : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hvw : ∀ c : ℂ, w ≠ c • v) (lam mu : ℂ)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, l3 - l4 = lam * (l3 + l4) + mu * b ∧
      col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w)
    (hreal : ∀ l3 l4 b : ℂ, l3 - l4 = lam * (l3 + l4) + mu * b →
      ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w)
    (hk1 : ¬ (lam = -1 ∧ mu = 0)) (hk2 : ¬ (lam = 1 ∧ mu = 0)) : False := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  have hT3 : t3 v v v = 0 := by
    by_cases hmu : mu = 0
    · by_cases hlam : lam = 0
      · obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hreal (1 / 2) (1 / 2) 0 (by rw [hlam, hmu]; ring)
        obtain ⟨A, D, -, -⟩ := c2_rels K hdef v w hv1 hw1 Z hZ h0 _ _ _ e2 e3 e4
        linear_combination 4 * A - 8 * D
      · obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hreal ((1 + lam) / 2) ((1 - lam) / 2) 0 (by rw [hmu]; ring)
        obtain ⟨A, D, D', -⟩ := c2_rels K hdef v w hv1 hw1 Z hZ h0 _ _ _ e2 e3 e4
        have e : lam * ((1 + lam) * (1 - lam)) * t3 v v v = 0 := by
          linear_combination 4 * lam * A - 4 * (D' - D)
        have h1 : 1 + lam ≠ 0 := by
          intro h
          exact hk1 ⟨by linear_combination h, hmu⟩
        have h2 : 1 - lam ≠ 0 := by
          intro h
          exact hk2 ⟨by linear_combination -h, hmu⟩
        exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero hlam (mul_ne_zero h1 h2))
    · obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hreal (3 / 2) (-1 / 2) ((2 - lam) / mu) (by
        rw [mul_comm mu, div_mul_cancel₀ _ hmu]
        ring)
      obtain ⟨A, D, D', C⟩ := c2_rels K hdef v w hv1 hw1 Z hZ h0 _ _ _ e2 e3 e4
      have e : -3 * t3 v v v = 0 := by
        linear_combination 2 * C + 2 * A - (D' - D)
      linear_combination (-1 / 3 : ℂ) * e
  have hκ := (chi_t4 v hv0 hv1 hv2 hT3).1
  have hk := chi_pow v hv1 hv2 hT3
  have hT12 : t3 v w w = 0 := by
    by_cases hmu : mu = 0
    · obtain ⟨Z1, hZ1, h01, a2, a3, a4⟩ := hreal ((1 + lam) / 2) ((1 - lam) / 2) 1 (by rw [hmu]; ring)
      obtain ⟨-, -, -, C1⟩ := c2_rels K hdef v w hv1 hw1 Z1 hZ1 h01 _ _ _ a2 a3 a4
      obtain ⟨Z2, hZ2, h02, b2, b3, b4⟩ := hreal ((1 + lam) / 2) ((1 - lam) / 2) 2 (by rw [hmu]; ring)
      obtain ⟨-, -, -, C2⟩ := c2_rels K hdef v w hv1 hw1 Z2 hZ2 h02 _ _ _ b2 b3 b4
      rw [hT3] at C1 C2
      linear_combination (1 / 2 : ℂ) * C2 - C1
    · obtain ⟨Z1, hZ1, h01, a2, a3, a4⟩ := hreal (mu / 2) (-mu / 2) 1 (by ring)
      obtain ⟨-, -, -, C1⟩ := c2_rels K hdef v w hv1 hw1 Z1 hZ1 h01 _ _ _ a2 a3 a4
      have h21 : t3 v v w = 0 := by
        have e : mu ^ 2 * t3 v v w = 0 := by linear_combination 4 * C1
        exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero 2 hmu)
      obtain ⟨Z2, hZ2, h02, b2, b3, b4⟩ := hreal ((1 + lam + mu) / 2) ((1 - lam - mu) / 2) 1 (by ring)
      obtain ⟨-, -, -, C2⟩ := c2_rels K hdef v w hv1 hw1 Z2 hZ2 h02 _ _ _ b2 b3 b4
      rw [hT3, h21] at C2
      linear_combination C2
  have hT21 : t3 v v w = 0 := chi_t12 v _ hκ hk hv1 hv2 hT3 w hw1 hw2 hT12
  have hFab : ∀ Z ∈ K, rs Z = 0 → ∀ l3 l4 b : ℂ, col Z 2 = l3 • v → col Z 3 = l4 • v →
      col Z 4 = b • w → (l3 + l4) * ip v (Ed (dY Z)) = 0 ∧ (l3 - l4) * ip v (Ed (dY Z)) = 0 := by
    intro Z hZ h0 l3 l4 b e2 e3 e4
    obtain ⟨A, D, D', -⟩ := c2_rels K hdef v w hv1 hw1 Z hZ h0 _ _ _ e2 e3 e4
    rw [hT3, hT21, hT12] at A D D'
    exact ⟨by linear_combination A, by linear_combination D' - D⟩
  obtain ⟨Zr, hZr, h0r, r2, r3, r4⟩ := hreal ((1 + lam) / 2) ((1 - lam) / 2) 0 (by ring)
  have hFr : ip v (Ed (dY Zr)) = 0 := by
    have e := (hFab Zr hZr h0r _ _ _ r2 r3 r4).1
    linear_combination e
  have hF : ∀ Z ∈ K, rs Z = 0 → ip v (Ed (dY Z)) = 0 := by
    intro Z hZ h0
    obtain ⟨l3, l4, b, -, e2, e3, e4⟩ := hline Z hZ h0
    obtain ⟨fa, fd⟩ := hFab Z hZ h0 l3 l4 b e2 e3 e4
    by_cases ha : l3 + l4 = 0
    · by_cases hd : l3 - l4 = 0
      · have hp := (hFab (Z + Zr) (K.add_mem hZ hZr) (by rw [map_add, h0, h0r, add_zero])
          (l3 + (1 + lam) / 2) (l4 + (1 - lam) / 2) b (by
            funext k
            have g := congrFun e2 k
            have g' := congrFun r2 k
            simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
            rw [g, g']
            ring) (by
            funext k
            have g := congrFun e3 k
            have g' := congrFun r3 k
            simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
            rw [g, g']
            ring) (by
            funext k
            have g := congrFun e4 k
            have g' := congrFun r4 k
            simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
            rw [g, g']
            ring)).1
        have hm := (hFab (Z - Zr) (K.sub_mem hZ hZr) (by rw [map_sub, h0, h0r, sub_zero])
          (l3 - (1 + lam) / 2) (l4 - (1 - lam) / 2) b (by
            funext k
            have g := congrFun e2 k
            have g' := congrFun r2 k
            simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
            rw [g, g']
            ring) (by
            funext k
            have g := congrFun e3 k
            have g' := congrFun r3 k
            simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
            rw [g, g']
            ring) (by
            funext k
            have g := congrFun e4 k
            have g' := congrFun r4 k
            simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at g g' ⊢
            rw [g, g']
            ring)).1
        have hl3 : l3 = 0 := by linear_combination (1 / 2 : ℂ) * ha + (1 / 2 : ℂ) * hd
        have hl4 : l4 = 0 := by linear_combination (1 / 2 : ℂ) * ha - (1 / 2 : ℂ) * hd
        rw [hl3, hl4] at hp hm
        rw [dY_add, Ed_pol] at hp
        rw [dY_sub, Ed_sub] at hm
        simp only [ip] at hp hm hFr ⊢
        linear_combination (1 / 2 : ℂ) * hp - (1 / 2 : ℂ) * hm - hFr
      · exact (mul_eq_zero.mp fd).resolve_left hd
    · exact (mul_eq_zero.mp fa).resolve_left ha
  have hB : ∀ d ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL,
      ∀ d' ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map dYL, ip v (Edb d d') = 0 := by
    rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
    have h1 := Submodule.mem_inf.mp hZ
    have h2 := Submodule.mem_inf.mp hZ'
    have h0 : rs Z = 0 := LinearMap.mem_ker.mp h1.2
    have h0' : rs Z' = 0 := LinearMap.mem_ker.mp h2.2
    have f1 := hF Z h1.1 h0
    have f2 := hF Z' h2.1 h0'
    have f3 := hF (Z + Z') (K.add_mem h1.1 h2.1) (by rw [map_add, h0, h0', add_zero])
    rw [dY_add, Ed_pol] at f3
    rw [dYL_apply, dYL_apply]
    simp only [ip] at f1 f2 f3 ⊢
    linear_combination (1 / 2 : ℂ) * (f3 - f1 - f2)
  have hvk : ∀ k, v k ≠ 0 := by
    intro k h
    apply hκ
    have e := hk k
    rw [h] at e
    linear_combination -e
  have hW := Fv_nondeg v hv1 hvk _ hB
  obtain ⟨Zb, hZb, h0b, b2, b3, b4⟩ := hreal (mu / 2) (-mu / 2) 1 (by ring)
  have hur := uY_of_rs3 Zr h0r v v w _ _ _ r2 r3 r4
  have hub := uY_of_rs3 Zb h0b v v w _ _ _ b2 b3 b4
  have hker : ((K ⊓ LinearMap.ker rs) ⊓ LinearMap.ker dYL : Submodule ℂ M45) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have h1 := Submodule.mem_inf.mp hZ
    have h2 := Submodule.mem_inf.mp h1.1
    have h0 : rs Z = 0 := LinearMap.mem_ker.mp h2.2
    have hd : dY Z = 0 := LinearMap.mem_ker.mp h1.2
    obtain ⟨l3, l4, b, hc, e2, e3, e4⟩ := hline Z h2.1 h0
    have hu := uY_of_rs3 Z h0 v v w l3 l4 b e2 e3 e4
    have qa := qbar_pol K hdef Z h2.1 h0 Zr hZr h0r
    have qb := qbar_pol K hdef Z h2.1 h0 Zb hZb h0b
    rw [hd, hu, hur] at qa
    rw [hd, hu, hub] at qb
    have hb : b * ip v w = 0 := by
      simp only [ip, e2b, tau, Pi.zero_apply] at qa hv2 ⊢
      linear_combination 4 * qa - (l3 + l4) * hv2
    have ha : (l3 + l4) * ip v w = 0 := by
      simp only [ip, e2b, tau, Pi.zero_apply] at qb hw2 ⊢
      linear_combination 4 * qb - b * hw2
    have zb := (mul_eq_zero.mp hb).resolve_right hg
    have za := (mul_eq_zero.mp ha).resolve_right hg
    have zd : l3 - l4 = 0 := by rw [hc, za, zb]; ring
    have hl3 : l3 = 0 := by linear_combination (1 / 2 : ℂ) * za + (1 / 2 : ℂ) * zd
    have hl4 : l4 = 0 := by linear_combination (1 / 2 : ℂ) * za - (1 / 2 : ℂ) * zd
    have k2 : col Z 2 = 0 := by rw [e2, hl3, zero_smul]
    have k3 : col Z 3 = 0 := by rw [e3, hl4, zero_smul]
    have k4 : col Z 4 = 0 := by rw [e4, zb, zero_smul]
    exact uY_dY_zero Z (nbar_ker Z h0 k2 k3 k4) hd k2 k3 k4
  have r1 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) dYL
  rw [hker, finrank_bot] at r1
  obtain ⟨hK, hq, -, -⟩ := TC5_dims K hdef hK5
  have r2 := rank_nullity K rs
  omega

theorem P4_c2ii (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4) (hv0 : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0) (hw2 : ip w w = 0)
    (hvw : ∀ c : ℂ, w ≠ c • v) (c : ℂ) (hc : c ≠ 0)
    (hreal : ∀ l3 l4 b : ℂ, l3 + l4 = c * b →
      ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w) : False := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  obtain ⟨Z1, hZ1, h01, a2, a3, a4⟩ := hreal (3 * c / 2) (-c / 2) 1 (by ring)
  obtain ⟨A1, D1, D1', C1⟩ := c2_rels K hdef v w hv1 hw1 Z1 hZ1 h01 _ _ _ a2 a3 a4
  have hT3 : t3 v v v = 0 := by
    have e : (-3 * c ^ 4) * t3 v v v = 0 := by
      linear_combination 2 * c * C1 + 2 * c * A1 - c * (D1' - D1)
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 4 hc))
  obtain ⟨Z2, hZ2, h02, b2, b3, b4⟩ := hreal (c / 2) (c / 2) 1 (by ring)
  obtain ⟨-, -, -, C2⟩ := c2_rels K hdef v w hv1 hw1 Z2 hZ2 h02 _ _ _ b2 b3 b4
  obtain ⟨Z3, hZ3, h03, d2, d3, d4⟩ := hreal ((c + 2) / 2) ((c - 2) / 2) 1 (by ring)
  obtain ⟨-, -, -, C3⟩ := c2_rels K hdef v w hv1 hw1 Z3 hZ3 h03 _ _ _ d2 d3 d4
  rw [hT3] at C2 C3
  have hT21 : t3 v v w = 0 := by linear_combination C3 - C2
  have hT12 : t3 v w w = 0 := by
    have e : c * t3 v w w = 0 := by
      rw [hT21] at C2
      linear_combination C2
    exact (mul_eq_zero.mp e).resolve_left hc
  have hk := chi_pow v hv1 hv2 hT3
  have hκ := (chi_t4 v hv0 hv1 hv2 hT3).1
  have hvk : ∀ k, v k ≠ 0 := by
    intro k h
    apply hκ
    have e := hk k
    rw [h] at e
    linear_combination -e
  rcases pair_rel v w hv1 hw1 hv2 hw2 hT21 hT12 hg with hchi | ⟨k0, hvk0, -, -⟩
  · have q := (nbar_eqs K hdef Z1 hZ1 h01).2
    rw [a2, a3, a4] at q
    simp only [t4, ip, Pi.smul_apply, smul_eq_mul] at q
    have hv2' := hv2
    simp only [ip] at hv2'
    have e : (3 / 16 : ℂ) * c ^ 2 * ip v w ^ 2 = 0 := by
      linear_combination q - ((-3*c^3*v 0^2/2 + 3*c^3*v 1^2/4 + 3*c^3*v 2^2/4 + 3*c^3*v 3^2/4 + 3*c^2*ip v w/4 - 3*c^2*v 0*w 0/2) * hchi 0 + (3*c^3*v 0^2/4 - 3*c^3*v 1^2/2 + 3*c^3*v 2^2/4 + 3*c^3*v 3^2/4 + 3*c^2*ip v w/8 + 3*c^2*v 0*w 0/2 - 3*c^2*v 1*w 1/2) * hchi 1 + (3*c^3*v 0^2/4 + 3*c^3*v 1^2/4 - 3*c^3*v 2^2/2 + 3*c^3*v 3^2/4 + 3*c^2*v 0*w 0/2 + 3*c^2*v 1*w 1/2 - 3*c^2*v 2*w 2/2) * hchi 2 + (3*c^3*v 0^2/4 + 3*c^3*v 1^2/4 + 3*c^3*v 2^2/4 - 3*c^3*v 3^2/2 - 3*c^2*ip v w/8 + 3*c^2*v 0*w 0/2 + 3*c^2*v 1*w 1/2 + 3*c^2*v 2*w 2/2 - 3*c^2*v 3*w 3/2) * hchi 3 + (3*c^3*ip v w/16) * hv2')
    have e' := (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc))
    exact hg (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e')
  · exact hvk k0 hvk0

def coefL (v w : V4) : M45 →ₗ[ℂ] V4 where
  toFun Z := ![ip (col Z 2) w, ip (col Z 3) w, ip (col Z 4) v, 0]
  map_add' Z Z' := by
    funext k
    fin_cases k <;> simp [ip, col] <;> ring
  map_smul' c Z := by
    funext k
    fin_cases k <;> simp [ip, col] <;> ring

theorem coefL_vals (v w : V4) (Z : M45) (l3 l4 b : ℂ) (h2 : col Z 2 = l3 • v) (h3 : col Z 3 = l4 • v)
    (h4 : col Z 4 = b • w) :
    coefL v w Z = ![l3 * ip v w, l4 * ip v w, b * ip w v, 0] := by
  have e : coefL v w Z = ![ip (col Z 2) w, ip (col Z 3) w, ip (col Z 4) v, 0] := rfl
  rw [e, h2, h3, h4]
  funext k
  fin_cases k <;> simp [ip] <;> ring

theorem c2_plane (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v w : V4) (hg : ip v w ≠ 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w) :
    ∃ Zx ∈ K, rs Zx = 0 ∧ ∃ Zy ∈ K, rs Zy = 0 ∧ ∃ x3 x4 xb y3 y4 yb : ℂ,
      col Zx 2 = x3 • v ∧ col Zx 3 = x4 • v ∧ col Zx 4 = xb • w ∧
      col Zy 2 = y3 • v ∧ col Zy 3 = y4 • v ∧ col Zy 4 = yb • w ∧
      (∀ s t : ℂ, s * x3 + t * y3 = 0 → s * x4 + t * y4 = 0 → s * xb + t * yb = 0 → s = 0 ∧ t = 0) ∧
      ∀ Z ∈ K, rs Z = 0 → ∃ s t : ℂ, col Z 2 = (s * x3 + t * y3) • v ∧ col Z 3 = (s * x4 + t * y4) • v ∧
        col Z 4 = (s * xb + t * yb) • w := by
  have hgw : ip w v ≠ 0 := by
    intro h
    apply hg
    simp only [ip] at h ⊢
    linear_combination h
  obtain ⟨-, -, -, z, hz0, hzK⟩ := TC5_dims K hdef hK5
  obtain ⟨hK, hq, -, -⟩ := TC5_dims K hdef hK5
  have hmemN : ∀ Z, Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) ↔ Z ∈ K ∧ rs Z = 0 := by
    intro Z
    rw [Submodule.mem_inf, LinearMap.mem_ker]
  have hzN : zE z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) := (hmemN _).mpr ⟨hzK, rs_zE z⟩
  have hker1 : 1 ≤ Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL v w) : Submodule ℂ M45) := by
    have hzE : zE z ≠ 0 := by
      intro h
      apply hz0
      funext k
      have e := congrFun h (k, 0)
      rw [zE0] at e
      exact e
    have hmem : zE z ∈ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL v w) : Submodule ℂ M45) := by
      refine Submodule.mem_inf.mpr ⟨hzN, ?_⟩
      rw [LinearMap.mem_ker, coefL_vals v w (zE z) 0 0 0 (by funext k; simp [col, zE2c])
        (by funext k; simp [col, zE3]) (by funext k; simp [col, zE4])]
      funext k
      fin_cases k <;> simp
    have hle : Submodule.span ℂ {zE z} ≤ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL v w) : Submodule ℂ M45) := by
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hmem
    have h1 : Module.finrank ℂ (Submodule.span ℂ {zE z}) = 1 := finrank_span_singleton hzE
    have h2 := Submodule.finrank_mono hle
    omega
  have hker2 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL v w) : Submodule ℂ M45) ≤ 1 := by
    have hW : ∀ y ∈ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL v w) : Submodule ℂ M45).map dYL, zE y ∈ K := by
      rintro _ ⟨Z, hZ, rfl⟩
      have h1 := Submodule.mem_inf.mp hZ
      obtain ⟨hZK, h0⟩ := (hmemN Z).mp h1.1
      obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Z hZK h0
      have hc := LinearMap.mem_ker.mp h1.2
      rw [coefL_vals v w Z l3 l4 b e2 e3 e4] at hc
      have c0 := congrFun hc 0
      have c1 := congrFun hc 1
      have c2 := congrFun hc 2
      simp at c0 c1 c2
      have k2 : col Z 2 = 0 := by rw [e2, c0.resolve_right hg, zero_smul]
      have k3 : col Z 3 = 0 := by rw [e3, c1.resolve_right hg, zero_smul]
      have k4 : col Z 4 = 0 := by rw [e4, c2.resolve_right hgw, zero_smul]
      rw [dYL_apply, ← Z_of_nbar Z k2 k3 k4 (nbar_ker Z h0 k2 k3 k4)]
      exact hZK
    have h1 := zeta_le_one K hdef hK5 _ hW
    have hkerd : (((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL v w)) ⊓ LinearMap.ker dYL : Submodule ℂ M45) = ⊥ := by
      rw [eq_bot_iff]
      intro Z hZ
      rw [Submodule.mem_bot]
      have hZ1 := (Submodule.mem_inf.mp hZ).1
      have hd : dY Z = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2
      have h1' := Submodule.mem_inf.mp hZ1
      obtain ⟨hZK, h0⟩ := (hmemN Z).mp h1'.1
      obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Z hZK h0
      have hc := LinearMap.mem_ker.mp h1'.2
      rw [coefL_vals v w Z l3 l4 b e2 e3 e4] at hc
      have c0 := congrFun hc 0
      have c1 := congrFun hc 1
      have c2 := congrFun hc 2
      simp at c0 c1 c2
      have k2 : col Z 2 = 0 := by rw [e2, c0.resolve_right hg, zero_smul]
      have k3 : col Z 3 = 0 := by rw [e3, c1.resolve_right hg, zero_smul]
      have k4 : col Z 4 = 0 := by rw [e4, c2.resolve_right hgw, zero_smul]
      exact uY_dY_zero Z (nbar_ker Z h0 k2 k3 k4) hd k2 k3 k4
    have r := rank_nullity ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL v w) : Submodule ℂ M45) dYL
    rw [hkerd, finrank_bot] at r
    omega
  have r1 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (coefL v w)
  have r2 := rank_nullity K rs
  have hP2 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL v w)) = 2 := by omega
  obtain ⟨px, hpx, py, hpy, hind⟩ := two_indep ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL v w)) (by omega)
  obtain ⟨Zx, hZx, rfl⟩ := Submodule.mem_map.mp hpx
  obtain ⟨Zy, hZy, rfl⟩ := Submodule.mem_map.mp hpy
  obtain ⟨hZxK, h0x⟩ := (hmemN Zx).mp hZx
  obtain ⟨hZyK, h0y⟩ := (hmemN Zy).mp hZy
  obtain ⟨x3, x4, xb, ex2, ex3, ex4⟩ := hline Zx hZxK h0x
  obtain ⟨y3, y4, yb, ey2, ey3, ey4⟩ := hline Zy hZyK h0y
  have hvx := coefL_vals v w Zx x3 x4 xb ex2 ex3 ex4
  have hvy := coefL_vals v w Zy y3 y4 yb ey2 ey3 ey4
  have hspan : (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL v w) = Submodule.span ℂ {coefL v w Zx, coefL v w Zy} := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact hpx
      · exact hpy
    · have hne : coefL v w Zx ≠ 0 := by
        intro h
        have := hind 1 0 (by rw [h]; simp)
        exact one_ne_zero this.1
      have hlt : Submodule.span ℂ {coefL v w Zx} <
          Submodule.span ℂ {coefL v w Zx, coefL v w Zy} := by
        refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
        intro h
        have hy' : coefL v w Zy ∈ Submodule.span ℂ {coefL v w Zx} := by
          rw [h]
          exact Submodule.subset_span (by simp)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy'
        have := hind c (-1) (by rw [hc]; simp)
        exact one_ne_zero (neg_eq_zero.mp this.2)
      have h1 : Module.finrank ℂ (Submodule.span ℂ {coefL v w Zx}) = 1 := finrank_span_singleton hne
      have h2 := Submodule.finrank_lt_finrank_of_lt hlt
      omega
  refine ⟨Zx, hZxK, h0x, Zy, hZyK, h0y, x3, x4, xb, y3, y4, yb, ex2, ex3, ex4, ey2, ey3, ey4, ?_, ?_⟩
  · intro s t h3 h4 hb
    apply hind s t
    rw [hvx, hvy]
    funext k
    fin_cases k
    · show s * (x3 * ip v w) + t * (y3 * ip v w) = 0
      linear_combination ip v w * h3
    · show s * (x4 * ip v w) + t * (y4 * ip v w) = 0
      linear_combination ip v w * h4
    · show s * (xb * ip w v) + t * (yb * ip w v) = 0
      linear_combination ip w v * hb
    · show s * 0 + t * 0 = 0
      ring
  · intro Z hZ h0
    obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Z hZ h0
    have hmem : coefL v w Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL v w) := Submodule.mem_map.mpr ⟨Z, (hmemN Z).mpr ⟨hZ, h0⟩, rfl⟩
    rw [hspan] at hmem
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hmem
    rw [hvx, hvy, coefL_vals v w Z l3 l4 b e2 e3 e4] at hst
    have c0 := congrFun hst 0
    have c1 := congrFun hst 1
    have c2 := congrFun hst 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at c0 c1 c2
    refine ⟨s, t, ?_, ?_, ?_⟩
    · rw [e2]
      congr 1
      have e : (l3 - (s * x3 + t * y3)) * ip v w = 0 := by linear_combination -c0
      linear_combination (mul_eq_zero.mp e).resolve_right hg
    · rw [e3]
      congr 1
      have e : (l4 - (s * x4 + t * y4)) * ip v w = 0 := by linear_combination -c1
      linear_combination (mul_eq_zero.mp e).resolve_right hg
    · rw [e4]
      congr 1
      have e : (b - (s * xb + t * yb)) * ip w v = 0 := by linear_combination -c2
      linear_combination (mul_eq_zero.mp e).resolve_right hgw

theorem smul_v_inj (v : V4) (hv : v ≠ 0) (a b : ℂ) (h : a • v = b • v) : a = b := by
  by_contra hab
  apply hv
  have e : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hab)

theorem cramer (p q r s' : ℂ) (hD : p * s' - q * r ≠ 0) (α β : ℂ) :
    (α * s' - β * q) / (p * s' - q * r) * p + (p * β - r * α) / (p * s' - q * r) * q = α ∧
      (α * s' - β * q) / (p * s' - q * r) * r + (p * β - r * α) / (p * s' - q * r) * s' = β := by
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring

set_option maxHeartbeats 4000000 in
theorem P4_c2_canon (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v w : V4) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hvw : ∀ c : ℂ, w ≠ c • v)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w)
    (Y2 : M45) (hY2 : Y2 ∈ K) (h0Y2 : rs Y2 = 0) (eY2 : col Y2 2 = v)
    (Y3 : M45) (hY3 : Y3 ∈ K) (h0Y3 : rs Y3 = 0) (κ : ℂ) (hκ : κ ≠ 0) (eY3 : col Y3 3 = κ • v)
    (Y4 : M45) (hY4 : Y4 ∈ K) (h0Y4 : rs Y4 = 0) (eY4 : col Y4 4 = w)
    (Hiii : (∀ l b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l • v ∧ col Z 3 = (-l) • v ∧ col Z 4 = b • w) →
      False) : False := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  obtain ⟨Zx, hZx, h0x, Zy, hZy, h0y, x3, x4, xb, y3, y4, yb, ex2, ex3, ex4, ey2, ey3, ey4, hind,
    hrep⟩ := c2_plane K hdef hK5 v w hg hline
  have hcomb : ∀ s t : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = (s * x3 + t * y3) • v ∧
      col Z 3 = (s * x4 + t * y4) • v ∧ col Z 4 = (s * xb + t * yb) • w := by
    intro s t
    refine ⟨s • Zx + t • Zy, K.add_mem (K.smul_mem s hZx) (K.smul_mem t hZy), ?_, ?_, ?_, ?_⟩
    · rw [map_add, map_smul, map_smul, h0x, h0y, smul_zero, smul_zero, add_zero]
    · funext k
      have g1 := congrFun ex2 k
      have g2 := congrFun ey2 k
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
      rw [g1, g2]
      ring
    · funext k
      have g1 := congrFun ex3 k
      have g2 := congrFun ey3 k
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
      rw [g1, g2]
      ring
    · funext k
      have g1 := congrFun ex4 k
      have g2 := congrFun ey4 k
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
      rw [g1, g2]
      ring
  obtain ⟨s2, t2, f22, f23, f24⟩ := hrep Y2 hY2 h0Y2
  obtain ⟨s3, t3, f32, f33, f34⟩ := hrep Y3 hY3 h0Y3
  obtain ⟨s4, t4, f42, f43, f44⟩ := hrep Y4 hY4 h0Y4
  have c2Y : s2 * x3 + t2 * y3 = 1 := by
    rw [eY2] at f22
    exact (smul_v_inj v hv0 _ _ (by rw [one_smul]; exact f22)).symm
  have c3Y : s3 * x4 + t3 * y4 = κ := by
    rw [eY3] at f33
    exact (smul_v_inj v hv0 _ _ f33).symm
  have c4Y : s4 * xb + t4 * yb = 1 := by
    rw [eY4] at f44
    exact (smul_v_inj w hw0 _ _ (by rw [one_smul]; exact f44)).symm
  by_cases hdet : (x3 + x4) * yb - (y3 + y4) * xb = 0
  · have hbne : ¬ (xb = 0 ∧ yb = 0) := by
      rintro ⟨h1, h2⟩
      rw [h1, h2] at c4Y
      norm_num at c4Y
    obtain ⟨c, hcx, hcy⟩ : ∃ c : ℂ, x3 + x4 = c * xb ∧ y3 + y4 = c * yb := by
      by_cases hxb : xb = 0
      · have hyb : yb ≠ 0 := fun h => hbne ⟨hxb, h⟩
        refine ⟨(y3 + y4) / yb, ?_, ?_⟩
        · rw [hxb] at hdet ⊢
          have e : (x3 + x4) * yb = 0 := by linear_combination hdet
          rw [(mul_eq_zero.mp e).resolve_right hyb]
          ring
        · rw [div_mul_cancel₀ _ hyb]
      · refine ⟨(x3 + x4) / xb, ?_, ?_⟩
        · rw [div_mul_cancel₀ _ hxb]
        · rw [div_mul_eq_mul_div, eq_div_iff hxb]
          linear_combination -hdet
    have hdet' : xb * (y3 - y4) - yb * (x3 - x4) ≠ 0 := by
      intro h
      have := hind yb (-xb) (by linear_combination (1 / 2 : ℂ) * hdet - (1 / 2 : ℂ) * h)
        (by linear_combination (1 / 2 : ℂ) * hdet + (1 / 2 : ℂ) * h) (by ring)
      exact hbne ⟨neg_eq_zero.mp this.2, this.1⟩
    have hrealD : ∀ l3 l4 b : ℂ, l3 + l4 = c * b →
        ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w := by
      intro l3 l4 b hab
      obtain ⟨F1, F2⟩ := cramer xb yb (x3 - x4) (y3 - y4) hdet' b (l3 - l4)
      obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hcomb ((b * (y3 - y4) - (l3 - l4) * yb) / (xb * (y3 - y4) - yb * (x3 - x4)))
        ((xb * (l3 - l4) - (x3 - x4) * b) / (xb * (y3 - y4) - yb * (x3 - x4)))
      refine ⟨Z, hZ, h0, ?_, ?_, ?_⟩
      · rw [e2]
        congr 1
        linear_combination (1 / 2 : ℂ) * F2 + (c / 2) * F1
          + ((b * (y3 - y4) - (l3 - l4) * yb) / (xb * (y3 - y4) - yb * (x3 - x4)) / 2) * hcx
          + ((xb * (l3 - l4) - (x3 - x4) * b) / (xb * (y3 - y4) - yb * (x3 - x4)) / 2) * hcy
          - (1 / 2 : ℂ) * hab
      · rw [e3]
        congr 1
        linear_combination -(1 / 2 : ℂ) * F2 + (c / 2) * F1
          + ((b * (y3 - y4) - (l3 - l4) * yb) / (xb * (y3 - y4) - yb * (x3 - x4)) / 2) * hcx
          + ((xb * (l3 - l4) - (x3 - x4) * b) / (xb * (y3 - y4) - yb * (x3 - x4)) / 2) * hcy
          - (1 / 2 : ℂ) * hab
      · rw [e4, F1]
    by_cases hc0 : c = 0
    · apply Hiii
      intro l b
      exact hrealD l (-l) b (by rw [hc0]; ring)
    · exact P4_c2ii K hdef v w hv0 hv1 hv2 hw1 hw2 hvw c hc0 hrealD
  · have hD : (x3 + x4) * yb - xb * (y3 + y4) ≠ 0 := fun h => hdet (by linear_combination h)
    obtain ⟨Lx, Ly⟩ := cramer (x3 + x4) xb (y3 + y4) yb hD (x3 - x4) (y3 - y4)
    have hline' : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ,
        l3 - l4 = ((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) * (l3 + l4) + ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) * b ∧
        col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w := by
      intro Z hZ h0
      obtain ⟨s, t, e2, e3, e4⟩ := hrep Z hZ h0
      exact ⟨_, _, _, by linear_combination (-s) * Lx - t * Ly, e2, e3, e4⟩
    have hreal' : ∀ l3 l4 b : ℂ, l3 - l4 = ((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) * (l3 + l4) + ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) * b →
        ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w := by
      intro l3 l4 b hcon
      obtain ⟨Fa, Fb⟩ := cramer (x3 + x4) (y3 + y4) xb yb hdet (l3 + l4) b
      obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hcomb (((l3 + l4) * yb - b * (y3 + y4)) / ((x3 + x4) * yb - (y3 + y4) * xb))
        (((x3 + x4) * b - xb * (l3 + l4)) / ((x3 + x4) * yb - (y3 + y4) * xb))
      refine ⟨Z, hZ, h0, ?_, ?_, ?_⟩
      · rw [e2]
        congr 1
        linear_combination (1 / 2 : ℂ) * Fa + (1 / 2 : ℂ) * (((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) * Fa + ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) * Fb
          - ((l3 + l4) * yb - b * (y3 + y4)) / ((x3 + x4) * yb - (y3 + y4) * xb) * Lx - ((x3 + x4) * b - xb * (l3 + l4)) / ((x3 + x4) * yb - (y3 + y4) * xb) * Ly - hcon)
      · rw [e3]
        congr 1
        linear_combination (1 / 2 : ℂ) * Fa - (1 / 2 : ℂ) * (((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) * Fa + ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) * Fb
          - ((l3 + l4) * yb - b * (y3 + y4)) / ((x3 + x4) * yb - (y3 + y4) * xb) * Lx - ((x3 + x4) * b - xb * (l3 + l4)) / ((x3 + x4) * yb - (y3 + y4) * xb) * Ly - hcon)
      · rw [e4, Fb]
    have hk1 : ¬ (((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) = -1 ∧ ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) = 0) := by
      rintro ⟨h1, h2⟩
      have e : (s2 * x3 + t2 * y3) - (s2 * x4 + t2 * y4) = ((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) * ((s2 * x3 + t2 * y3)
          + (s2 * x4 + t2 * y4)) + ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) * (s2 * xb + t2 * yb) := by
        linear_combination (-s2) * Lx - t2 * Ly
      rw [h1, h2] at e
      have e' : (2 : ℂ) = 0 := by linear_combination e - 2 * c2Y
      norm_num at e'
    have hk2 : ¬ (((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) = 1 ∧ ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) = 0) := by
      rintro ⟨h1, h2⟩
      have e : (s3 * x3 + t3 * y3) - (s3 * x4 + t3 * y4) = ((x3 - x4) * yb - (y3 - y4) * xb) / ((x3 + x4) * yb - xb * (y3 + y4)) * ((s3 * x3 + t3 * y3)
          + (s3 * x4 + t3 * y4)) + ((x3 + x4) * (y3 - y4) - (y3 + y4) * (x3 - x4)) / ((x3 + x4) * yb - xb * (y3 + y4)) * (s3 * xb + t3 * yb) := by
        linear_combination (-s3) * Lx - t3 * Ly
      rw [h1, h2] at e
      have e' : -2 * κ = 0 := by linear_combination e + 2 * c3Y
      exact hκ (by linear_combination (-1 / 2 : ℂ) * e')
    exact P4_c2i K hdef hK5 v w hv0 hv1 hv2 hw1 hw2 hvw _ _ hline' hreal' hk1 hk2

def C2iiiHyp : Prop := ∀ K : Submodule ℂ M45, DefLine K mTC → 5 ≤ Module.finrank ℂ K →
  ∀ v w : V4, v ≠ 0 → tau v = 0 → ip v v = 0 → tau w = 0 → ip w w = 0 → (∀ c : ℂ, w ≠ c • v) →
  (∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w) →
  (∀ l b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l • v ∧ col Z 3 = (-l) • v ∧ col Z 4 = b • w) → False

def C1Hyp : Prop := ∀ K : Submodule ℂ M45, DefLine K mTC → 5 ≤ Module.finrank ℂ K →
  ∀ v : V4, v ≠ 0 → tau v = 0 → ip v v = 0 →
  (∀ Z ∈ K, rs Z = 0 → ∃ a b c : ℂ, col Z 2 = a • v ∧ col Z 3 = b • v ∧ col Z 4 = c • v) →
  (∃ Y2 ∈ K, rs Y2 = 0 ∧ col Y2 2 ≠ 0) → (∃ Y3 ∈ K, rs Y3 = 0 ∧ col Y3 3 ≠ 0) →
  (∃ Y4 ∈ K, rs Y4 = 0 ∧ col Y4 4 ≠ 0) → False

theorem P4_c2_perm (H3 : C2iiiHyp) (K : Submodule ℂ M45) (hdef : DefLine K mTC)
    (hK5 : 5 ≤ Module.finrank ℂ K) (σ : Equiv.Perm (Fin 5)) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1)
    (v w : V4) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hvw : ∀ c : ℂ, w ≠ c • v)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z (σ 2) = l3 • v ∧ col Z (σ 3) = l4 • v ∧
      col Z (σ 4) = b • w)
    (Y2 : M45) (hY2 : Y2 ∈ K) (h0Y2 : rs Y2 = 0) (eY2 : col Y2 (σ 2) = v)
    (Y3 : M45) (hY3 : Y3 ∈ K) (h0Y3 : rs Y3 = 0) (κ : ℂ) (hκ : κ ≠ 0) (eY3 : col Y3 (σ 3) = κ • v)
    (Y4 : M45) (hY4 : Y4 ∈ K) (h0Y4 : rs Y4 = 0) (eY4 : col Y4 (σ 4) = w) : False := by
  have hdef' : DefLine (K.map (cperm σ)) mTC := by
    have h := DefLine_perm σ K mTC hdef
    rw [mTC_perm σ hσ0 hσ1] at h
    exact h
  have hinjc : Function.Injective (cperm σ) := by
    intro Y Y' h
    funext p
    obtain ⟨i, j⟩ := p
    have e := congrFun h (i, σ.symm j)
    simp only [cperm_apply, Equiv.apply_symm_apply] at e
    exact e
  have hfr : Module.finrank ℂ (K.map (cperm σ)) = Module.finrank ℂ K :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (cperm σ) hinjc K)).symm
  have hcol : ∀ (Y : M45) (j : Fin 5), col (cperm σ Y) j = col Y (σ j) := by
    intro Y j
    funext i
    rfl
  have hK5' : 5 ≤ Module.finrank ℂ (K.map (cperm σ)) := by omega
  have hline' : ∀ Z ∈ K.map (cperm σ), rs Z = 0 →
      ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w := by
    rintro _ ⟨Y, hY, rfl⟩ h0
    rw [rs_cperm] at h0
    obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Y hY h0
    exact ⟨l3, l4, b, by rw [hcol, e2], by rw [hcol, e3], by rw [hcol, e4]⟩
  have rr2 : rs (cperm σ Y2) = 0 := by rw [rs_cperm]; exact h0Y2
  have rr3 : rs (cperm σ Y3) = 0 := by rw [rs_cperm]; exact h0Y3
  have rr4 : rs (cperm σ Y4) = 0 := by rw [rs_cperm]; exact h0Y4
  have c2 : col (cperm σ Y2) 2 = v := by rw [hcol]; exact eY2
  have c3 : col (cperm σ Y3) 3 = κ • v := by rw [hcol]; exact eY3
  have c4 : col (cperm σ Y4) 4 = w := by rw [hcol]; exact eY4
  exact P4_c2_canon (K.map (cperm σ)) hdef' hK5' v w hv0 hw0 hv1 hv2 hw1 hw2 hvw hline'
    (cperm σ Y2) (Submodule.mem_map_of_mem hY2) rr2 c2
    (cperm σ Y3) (Submodule.mem_map_of_mem hY3) rr3 κ hκ c3
    (cperm σ Y4) (Submodule.mem_map_of_mem hY4) rr4 c4
    (fun h => H3 _ hdef' hK5' v w hv0 hv1 hv2 hw1 hw2 hvw hline' h)

theorem not_par_symm (x y : V4) (hx : x ≠ 0) (h : ∀ s : ℂ, y ≠ s • x) : ∀ s : ℂ, x ≠ s • y := by
  intro s hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs
    exact hx hs
  apply h s⁻¹
  rw [hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]

theorem sne0_left (x : V4) (s : ℂ) (h : s • x ≠ 0) : s ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h
  exact h rfl

theorem TC5_main (H1 : C1Hyp) (H3 : C2iiiHyp) (K : Submodule ℂ M45) (hdef : DefLine K mTC) :
    Module.finrank ℂ K ≤ 4 := by
  by_contra hcon
  have hK5 : 5 ≤ Module.finrank ℂ K := by omega
  obtain ⟨v2, v3, v4, hv2, hv3, hv4, t2, i2, t3', i3, t4', i4, hline, ⟨Y2, hY2, h0Y2, e2⟩,
    ⟨Y3, hY3, h0Y3, e3⟩, ⟨Y4, hY4, h0Y4, e4⟩⟩ := P4_k3 K hdef hK5
  by_cases p32 : ∃ s : ℂ, v3 = s • v2
  · obtain ⟨s, hs⟩ := p32
    have hs0 : s ≠ 0 := sne0_left v2 s (by rw [← hs]; exact hv3)
    by_cases p42 : ∃ t : ℂ, v4 = t • v2
    · obtain ⟨t, ht⟩ := p42
      have hl : ∀ Z ∈ K, rs Z = 0 →
          ∃ a b c : ℂ, col Z 2 = a • v2 ∧ col Z 3 = b • v2 ∧ col Z 4 = c • v2 := by
        intro Z hZ h0
        obtain ⟨⟨a, ea⟩, ⟨b, eb⟩, ⟨c, ec⟩⟩ := hline Z hZ h0
        exact ⟨a, b * s, c * t, ea, by rw [eb, hs, smul_smul], by rw [ec, ht, smul_smul]⟩
      exact H1 K hdef hK5 v2 hv2 t2 i2 hl ⟨Y2, hY2, h0Y2, by rw [e2]; exact hv2⟩
        ⟨Y3, hY3, h0Y3, by rw [e3]; exact hv3⟩ ⟨Y4, hY4, h0Y4, by rw [e4]; exact hv4⟩
    · have hvw : ∀ c : ℂ, v4 ≠ c • v2 := fun c h => p42 ⟨c, h⟩
      have hl : ∀ Z ∈ K, rs Z = 0 →
          ∃ l3 l4 b : ℂ, col Z 2 = l3 • v2 ∧ col Z 3 = l4 • v2 ∧ col Z 4 = b • v4 := by
        intro Z hZ h0
        obtain ⟨⟨a, ea⟩, ⟨b, eb⟩, ⟨c, ec⟩⟩ := hline Z hZ h0
        exact ⟨a, b * s, c, ea, by rw [eb, hs, smul_smul], ec⟩
      have c3 : col Y3 3 = s • v2 := by rw [e3, hs]
      exact P4_c2_canon K hdef hK5 v2 v4 hv2 hv4 t2 i2 t4' i4 hvw hl Y2 hY2 h0Y2 e2 Y3 hY3 h0Y3 s hs0
        c3 Y4 hY4 h0Y4 e4 (fun h => H3 K hdef hK5 v2 v4 hv2 t2 i2 t4' i4 hvw hl h)
  · have n32 : ∀ s : ℂ, v3 ≠ s • v2 := fun s h => p32 ⟨s, h⟩
    by_cases p42 : ∃ t : ℂ, v4 = t • v2
    · obtain ⟨t, ht⟩ := p42
      have ht0 : t ≠ 0 := sne0_left v2 t (by rw [← ht]; exact hv4)
      have s0 : (Equiv.swap (3 : Fin 5) 4) 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      have s1 : (Equiv.swap (3 : Fin 5) 4) 1 = 1 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      have s2 : (Equiv.swap (3 : Fin 5) 4) 2 = 2 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      have s3 : (Equiv.swap (3 : Fin 5) 4) 3 = 4 := Equiv.swap_apply_left 3 4
      have s4 : (Equiv.swap (3 : Fin 5) 4) 4 = 3 := Equiv.swap_apply_right 3 4
      have hl : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z ((Equiv.swap (3 : Fin 5) 4) 2) = l3 • v2 ∧
          col Z ((Equiv.swap (3 : Fin 5) 4) 3) = l4 • v2 ∧ col Z ((Equiv.swap (3 : Fin 5) 4) 4) = b • v3 := by
        intro Z hZ h0
        rw [s2, s3, s4]
        obtain ⟨⟨a, ea⟩, ⟨b, eb⟩, ⟨c, ec⟩⟩ := hline Z hZ h0
        exact ⟨a, c * t, b, ea, by rw [ec, ht, smul_smul], eb⟩
      have c2 : col Y2 ((Equiv.swap (3 : Fin 5) 4) 2) = v2 := by rw [s2]; exact e2
      have c3 : col Y4 ((Equiv.swap (3 : Fin 5) 4) 3) = t • v2 := by rw [s3, e4, ht]
      have c4 : col Y3 ((Equiv.swap (3 : Fin 5) 4) 4) = v3 := by rw [s4]; exact e3
      exact P4_c2_perm H3 K hdef hK5 (Equiv.swap 3 4) s0 s1 v2 v3 hv2 hv3 t2 i2 t3' i3 n32 hl
        Y2 hY2 h0Y2 c2 Y4 hY4 h0Y4 t ht0 c3 Y3 hY3 h0Y3 c4
    · have n42 : ∀ t : ℂ, v4 ≠ t • v2 := fun t h => p42 ⟨t, h⟩
      by_cases p43 : ∃ s : ℂ, v4 = s • v3
      · obtain ⟨s, hs⟩ := p43
        have hs0 : s ≠ 0 := sne0_left v3 s (by rw [← hs]; exact hv4)
        have hv3' : v3 = s⁻¹ • v4 := by rw [hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]
        have s0 : (Equiv.swap (2 : Fin 5) 4) 0 = 0 :=
          Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
        have s1 : (Equiv.swap (2 : Fin 5) 4) 1 = 1 :=
          Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
        have s3 : (Equiv.swap (2 : Fin 5) 4) 3 = 3 :=
          Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
        have s2 : (Equiv.swap (2 : Fin 5) 4) 2 = 4 := Equiv.swap_apply_left 2 4
        have s4 : (Equiv.swap (2 : Fin 5) 4) 4 = 2 := Equiv.swap_apply_right 2 4
        have hvw : ∀ c : ℂ, v2 ≠ c • v4 := not_par_symm v2 v4 hv2 n42
        have hl : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z ((Equiv.swap (2 : Fin 5) 4) 2) = l3 • v4 ∧
            col Z ((Equiv.swap (2 : Fin 5) 4) 3) = l4 • v4 ∧ col Z ((Equiv.swap (2 : Fin 5) 4) 4) = b • v2 := by
          intro Z hZ h0
          rw [s2, s3, s4]
          obtain ⟨⟨a, ea⟩, ⟨b, eb⟩, ⟨c, ec⟩⟩ := hline Z hZ h0
          exact ⟨c, b * s⁻¹, a, ec, by rw [eb, hv3', smul_smul], ea⟩
        have c2 : col Y4 ((Equiv.swap (2 : Fin 5) 4) 2) = v4 := by rw [s2]; exact e4
        have c3 : col Y3 ((Equiv.swap (2 : Fin 5) 4) 3) = s⁻¹ • v4 := by rw [s3, e3, hv3']
        have c4 : col Y2 ((Equiv.swap (2 : Fin 5) 4) 4) = v2 := by rw [s4]; exact e2
        exact P4_c2_perm H3 K hdef hK5 (Equiv.swap 2 4) s0 s1 v4 v2 hv4 hv2 t4' i4 t2 i2 hvw hl
          Y4 hY4 h0Y4 c2 Y3 hY3 h0Y3 s⁻¹ (inv_ne_zero hs0) c3 Y2 hY2 h0Y2 c4
      · have n43 : ∀ s : ℂ, v4 ≠ s • v3 := fun s h => p43 ⟨s, h⟩
        exact TC5_c3 K hdef hK5 v2 v3 v4 hv2 hv3 t2 i2 t3' i3 t4' i4 hline Y2 hY2 e2 Y3 hY3 e3
          Y4 hY4 e4 n32 n42 n43

theorem indep_of_np (v w : V4) (hv0 : v ≠ 0) (hvw : ∀ c : ℂ, w ≠ c • v) : indep v w := by
  intro s t h
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hv0, ht⟩
  · exfalso
    apply hvw (-s / t)
    funext k
    have e := congrFun h k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    rw [div_mul_eq_mul_div, eq_div_iff ht]
    linear_combination e

def sig23p : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem sig23 : sig23p 0 = 2 ∧ sig23p 1 = 3 ∧ sig23p 2 = 0 ∧ sig23p 3 = 1 ∧ sig23p 4 = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sig23p, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 5) ≠ 1)
      (by decide : (0 : Fin 5) ≠ 3), Equiv.swap_apply_left]
  · rw [sig23p, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
      (by decide : (3 : Fin 5) ≠ 0) (by decide : (3 : Fin 5) ≠ 2)]
  · rw [sig23p, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 5) ≠ 1)
      (by decide : (2 : Fin 5) ≠ 3), Equiv.swap_apply_right]
  · rw [sig23p, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne
      (by decide : (1 : Fin 5) ≠ 0) (by decide : (1 : Fin 5) ≠ 2)]
  · rw [sig23p, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide : (4 : Fin 5) ≠ 1)
      (by decide : (4 : Fin 5) ≠ 3), Equiv.swap_apply_of_ne_of_ne (by decide : (4 : Fin 5) ≠ 0)
      (by decide : (4 : Fin 5) ≠ 2)]

theorem c2iii_zeta (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4) (hv0 : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0) (hw2 : ip w w = 0)
    (hvw : ∀ c : ℂ, w ≠ c • v) (z : V4) (hzK : zE z ∈ K)
    (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0) (l b : ℂ) (hl : l ≠ 0) (hb : b ≠ 0)
    (e2 : col Z 2 = l • v) (e3 : col Z 3 = (-l) • v) (e4 : col Z 4 = b • w)
    (c : ℂ) (hd : dY Z = c • z) : False := by
  obtain ⟨Z', hZ'⟩ : ∃ Z' : M45, Z' = Z - c • zE z := ⟨_, rfl⟩
  have hZ'K : Z' ∈ K := by
    rw [hZ']
    exact K.sub_mem hZ (K.smul_mem c hzK)
  have pt : ∀ k : Fin 4, Z' (k, 0) = -(b / 2) * w k ∧ Z' (k, 1) = -(b / 2) * w k ∧
      Z' (k, 2) = l * v k ∧ Z' (k, 3) = -l * v k ∧ Z' (k, 4) = b * w k := by
    intro k
    have R := congrFun h0 k
    rw [rs_apply] at R
    have D := congrFun hd k
    have E2 := congrFun e2 k
    have E3 := congrFun e3 k
    have E4 := congrFun e4 k
    simp only [dY, col, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at R D E2 E3 E4
    rw [hZ']
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE0, zE1, zE2c, zE3, zE4]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination (1 / 2 : ℂ) * R + D - (1 / 2 : ℂ) * (E2 + E3 + E4)
    · linear_combination (1 / 2 : ℂ) * R - D - (1 / 2 : ℂ) * (E2 + E3 + E4)
    · linear_combination E2
    · linear_combination E3
    · linear_combination E4
  have hdY : dY Z' = 0 := by
    funext k
    obtain ⟨p0, p1, -, -, -⟩ := pt k
    simp only [dY, Pi.zero_apply]
    rw [p0, p1]
    ring
  have hLK : ∀ Y ∈ Submodule.span ℂ {Z'}, Y ∈ K ∧ dY Y = 0 := by
    intro Y hY
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hY
    refine ⟨K.smul_mem t hZ'K, ?_⟩
    have e := map_smul dYL t Z'
    rw [dYL_apply, dYL_apply, hdY, smul_zero] at e
    exact e
  have hL := L_slev K hdef _ hLK
  obtain ⟨s0, s1, s2, s3, s4⟩ := sig23
  have hb2 : -(b / 2) ≠ 0 := by
    intro h
    apply hb
    linear_combination -2 * h
  have c0 : col Z' (sig23p 0) = l • v := by
    rw [s0]
    funext k
    simp only [col, Pi.smul_apply, smul_eq_mul]
    exact (pt k).2.2.1
  have c1 : col Z' (sig23p 1) = (-l) • v := by
    rw [s1]
    funext k
    simp only [col, Pi.smul_apply, smul_eq_mul]
    exact (pt k).2.2.2.1
  have c2 : col Z' (sig23p 2) = (-(b / 2)) • w := by
    rw [s2]
    funext k
    simp only [col, Pi.smul_apply, smul_eq_mul]
    exact (pt k).1
  have c3 : col Z' (sig23p 3) = (-(b / 2)) • w := by
    rw [s3]
    funext k
    simp only [col, Pi.smul_apply, smul_eq_mul]
    exact (pt k).2.1
  have c4 : col Z' (sig23p 4) = b • w := by
    rw [s4]
    funext k
    simp only [col, Pi.smul_apply, smul_eq_mul]
    exact (pt k).2.2.2.2
  exact pattern23 _ hL Z' (Submodule.mem_span_singleton_self Z')
    sig23p v w hv1 hv2 hw1 hw2 (indep_of_np v w hv0 hvw)
    l (-(b / 2)) (-(b / 2)) b hl hb2 hb2 hb c0 c1 c2 c3 c4

def C2iiiLagHyp : Prop := ∀ K : Submodule ℂ M45, DefLine K mTC → 5 ≤ Module.finrank ℂ K →
  ∀ v w : V4, v ≠ 0 → tau v = 0 → ip v v = 0 → tau w = 0 → ip w w = 0 → (∀ c : ℂ, w ≠ c • v) →
  (∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w) →
  (∀ l b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l • v ∧ col Z 3 = (-l) • v ∧ col Z 4 = b • w) →
  (∀ z : V4, zE z ∈ K → ∀ Z ∈ K, rs Z = 0 → ∀ l b c : ℂ, l ≠ 0 → b ≠ 0 → col Z 2 = l • v →
    col Z 3 = (-l) • v → col Z 4 = b • w → dY Z ≠ c • z) → False

theorem C2iii_of_lag (H : C2iiiLagHyp) : C2iiiHyp := by
  intro K hdef hK5 v w hv0 hv1 hv2 hw1 hw2 hvw hline hreal
  apply H K hdef hK5 v w hv0 hv1 hv2 hw1 hw2 hvw hline hreal
  intro z hzK Z hZ h0 l b c hl hb e2 e3 e4 hd
  exact c2iii_zeta K hdef v w hv0 hv1 hv2 hw1 hw2 hvw z hzK Z hZ h0 l b hl hb e2 e3 e4 c hd

theorem TC5_main' (H1 : C1Hyp) (H3 : C2iiiLagHyp) (K : Submodule ℂ M45) (hdef : DefLine K mTC) :
    Module.finrank ℂ K ≤ 4 :=
  TC5_main H1 (C2iii_of_lag H3) K hdef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem F1_vprod (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0)
    (h4 : ip w w = 0) (h5 : t3 v v w = 0) (hq : 3 * t4 v v w w = ip v w ^ 2) :
    8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * (v 0 * v 1 * v 2 * v 3) ^ 2) = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4 h5 hq
  linear_combination (-8*v 0^4*v 1^2*v 2^2*v 3^2*w 1^3 - 24*v 0^4*v 1^2*v 2^2*v 3^2*w 1^2*w 2 - 24*v 0^4*v 1^2*v 2^2*v 3^2*w 1^2*w 3 - 24*v 0^4*v 1^2*v 2^2*v 3^2*w 1*w 2^2 - 48*v 0^4*v 1^2*v 2^2*v 3^2*w 1*w 2*w 3 - 24*v 0^4*v 1^2*v 2^2*v 3^2*w 1*w 3^2 - 8*v 0^4*v 1^2*v 2^2*v 3^2*w 2^3 - 24*v 0^4*v 1^2*v 2^2*v 3^2*w 2^2*w 3 - 24*v 0^4*v 1^2*v 2^2*v 3^2*w 2*w 3^2 - 8*v 0^4*v 1^2*v 2^2*v 3^2*w 3^3 + 32*v 0^3*v 1^3*v 2^2*v 3^2*w 1^3 + 72*v 0^3*v 1^3*v 2^2*v 3^2*w 1^2*w 2 + 72*v 0^3*v 1^3*v 2^2*v 3^2*w 1^2*w 3 + 48*v 0^3*v 1^3*v 2^2*v 3^2*w 1*w 2^2 + 96*v 0^3*v 1^3*v 2^2*v 3^2*w 1*w 2*w 3 + 48*v 0^3*v 1^3*v 2^2*v 3^2*w 1*w 3^2 + 8*v 0^3*v 1^3*v 2^2*v 3^2*w 2^3 + 24*v 0^3*v 1^3*v 2^2*v 3^2*w 2^2*w 3 + 24*v 0^3*v 1^3*v 2^2*v 3^2*w 2*w 3^2 + 8*v 0^3*v 1^3*v 2^2*v 3^2*w 3^3 + 8*v 0^3*v 1^2*v 2^3*v 3^2*w 1^3 + 48*v 0^3*v 1^2*v 2^3*v 3^2*w 1^2*w 2 + 24*v 0^3*v 1^2*v 2^3*v 3^2*w 1^2*w 3 + 72*v 0^3*v 1^2*v 2^3*v 3^2*w 1*w 2^2 + 96*v 0^3*v 1^2*v 2^3*v 3^2*w 1*w 2*w 3 + 24*v 0^3*v 1^2*v 2^3*v 3^2*w 1*w 3^2 + 32*v 0^3*v 1^2*v 2^3*v 3^2*w 2^3 + 72*v 0^3*v 1^2*v 2^3*v 3^2*w 2^2*w 3 + 48*v 0^3*v 1^2*v 2^3*v 3^2*w 2*w 3^2 + 8*v 0^3*v 1^2*v 2^3*v 3^2*w 3^3 + 8*v 0^3*v 1^2*v 2^2*v 3^3*w 1^3 + 24*v 0^3*v 1^2*v 2^2*v 3^3*w 1^2*w 2 + 48*v 0^3*v 1^2*v 2^2*v 3^3*w 1^2*w 3 + 24*v 0^3*v 1^2*v 2^2*v 3^3*w 1*w 2^2 + 96*v 0^3*v 1^2*v 2^2*v 3^3*w 1*w 2*w 3 + 72*v 0^3*v 1^2*v 2^2*v 3^3*w 1*w 3^2 + 8*v 0^3*v 1^2*v 2^2*v 3^3*w 2^3 + 48*v 0^3*v 1^2*v 2^2*v 3^3*w 2^2*w 3 + 72*v 0^3*v 1^2*v 2^2*v 3^3*w 2*w 3^2 + 32*v 0^3*v 1^2*v 2^2*v 3^3*w 3^3 - 56*v 0^2*v 1^4*v 2^2*v 3^2*w 1^3 - 96*v 0^2*v 1^4*v 2^2*v 3^2*w 1^2*w 2 - 96*v 0^2*v 1^4*v 2^2*v 3^2*w 1^2*w 3 - 48*v 0^2*v 1^4*v 2^2*v 3^2*w 1*w 2^2 - 96*v 0^2*v 1^4*v 2^2*v 3^2*w 1*w 2*w 3 - 48*v 0^2*v 1^4*v 2^2*v 3^2*w 1*w 3^2 - 8*v 0^2*v 1^4*v 2^2*v 3^2*w 2^3 - 24*v 0^2*v 1^4*v 2^2*v 3^2*w 2^2*w 3 - 24*v 0^2*v 1^4*v 2^2*v 3^2*w 2*w 3^2 - 8*v 0^2*v 1^4*v 2^2*v 3^2*w 3^3 - 40*v 0^2*v 1^3*v 2^3*v 3^2*w 1^3 - 168*v 0^2*v 1^3*v 2^3*v 3^2*w 1^2*w 2 - 96*v 0^2*v 1^3*v 2^3*v 3^2*w 1^2*w 3 - 168*v 0^2*v 1^3*v 2^3*v 3^2*w 1*w 2^2 - 240*v 0^2*v 1^3*v 2^3*v 3^2*w 1*w 2*w 3 - 72*v 0^2*v 1^3*v 2^3*v 3^2*w 1*w 3^2 - 40*v 0^2*v 1^3*v 2^3*v 3^2*w 2^3 - 96*v 0^2*v 1^3*v 2^3*v 3^2*w 2^2*w 3 - 72*v 0^2*v 1^3*v 2^3*v 3^2*w 2*w 3^2 - 16*v 0^2*v 1^3*v 2^3*v 3^2*w 3^3 - 40*v 0^2*v 1^3*v 2^2*v 3^3*w 1^3 - 96*v 0^2*v 1^3*v 2^2*v 3^3*w 1^2*w 2 - 168*v 0^2*v 1^3*v 2^2*v 3^3*w 1^2*w 3 - 72*v 0^2*v 1^3*v 2^2*v 3^3*w 1*w 2^2 - 240*v 0^2*v 1^3*v 2^2*v 3^3*w 1*w 2*w 3 - 168*v 0^2*v 1^3*v 2^2*v 3^3*w 1*w 3^2 - 16*v 0^2*v 1^3*v 2^2*v 3^3*w 2^3 - 72*v 0^2*v 1^3*v 2^2*v 3^3*w 2^2*w 3 - 96*v 0^2*v 1^3*v 2^2*v 3^3*w 2*w 3^2 - 40*v 0^2*v 1^3*v 2^2*v 3^3*w 3^3 - 8*v 0^2*v 1^2*v 2^4*v 3^2*w 1^3 - 48*v 0^2*v 1^2*v 2^4*v 3^2*w 1^2*w 2 - 24*v 0^2*v 1^2*v 2^4*v 3^2*w 1^2*w 3 - 96*v 0^2*v 1^2*v 2^4*v 3^2*w 1*w 2^2 - 96*v 0^2*v 1^2*v 2^4*v 3^2*w 1*w 2*w 3 - 24*v 0^2*v 1^2*v 2^4*v 3^2*w 1*w 3^2 - 56*v 0^2*v 1^2*v 2^4*v 3^2*w 2^3 - 96*v 0^2*v 1^2*v 2^4*v 3^2*w 2^2*w 3 - 48*v 0^2*v 1^2*v 2^4*v 3^2*w 2*w 3^2 - 8*v 0^2*v 1^2*v 2^4*v 3^2*w 3^3 - 16*v 0^2*v 1^2*v 2^3*v 3^3*w 1^3 - 72*v 0^2*v 1^2*v 2^3*v 3^3*w 1^2*w 2 - 72*v 0^2*v 1^2*v 2^3*v 3^3*w 1^2*w 3 - 96*v 0^2*v 1^2*v 2^3*v 3^3*w 1*w 2^2 - 240*v 0^2*v 1^2*v 2^3*v 3^3*w 1*w 2*w 3 - 96*v 0^2*v 1^2*v 2^3*v 3^3*w 1*w 3^2 - 40*v 0^2*v 1^2*v 2^3*v 3^3*w 2^3 - 168*v 0^2*v 1^2*v 2^3*v 3^3*w 2^2*w 3 - 168*v 0^2*v 1^2*v 2^3*v 3^3*w 2*w 3^2 - 40*v 0^2*v 1^2*v 2^3*v 3^3*w 3^3 - 8*v 0^2*v 1^2*v 2^2*v 3^4*w 1^3 - 24*v 0^2*v 1^2*v 2^2*v 3^4*w 1^2*w 2 - 48*v 0^2*v 1^2*v 2^2*v 3^4*w 1^2*w 3 - 24*v 0^2*v 1^2*v 2^2*v 3^4*w 1*w 2^2 - 96*v 0^2*v 1^2*v 2^2*v 3^4*w 1*w 2*w 3 - 96*v 0^2*v 1^2*v 2^2*v 3^4*w 1*w 3^2 - 8*v 0^2*v 1^2*v 2^2*v 3^4*w 2^3 - 48*v 0^2*v 1^2*v 2^2*v 3^4*w 2^2*w 3 - 96*v 0^2*v 1^2*v 2^2*v 3^4*w 2*w 3^2 - 56*v 0^2*v 1^2*v 2^2*v 3^4*w 3^3 + 64*v 0*v 1^5*v 2^2*v 3^2*w 1^3 + 96*v 0*v 1^5*v 2^2*v 3^2*w 1^2*w 2 + 96*v 0*v 1^5*v 2^2*v 3^2*w 1^2*w 3 + 72*v 0*v 1^5*v 2^2*v 3^2*w 1*w 2^2 + 112*v 0*v 1^5*v 2^2*v 3^2*w 1*w 2*w 3 + 72*v 0*v 1^5*v 2^2*v 3^2*w 1*w 3^2 + 20*v 0*v 1^5*v 2^2*v 3^2*w 2^3 + 44*v 0*v 1^5*v 2^2*v 3^2*w 2^2*w 3 + 44*v 0*v 1^5*v 2^2*v 3^2*w 2*w 3^2 + 20*v 0*v 1^5*v 2^2*v 3^2*w 3^3 - 16*v 0*v 1^4*v 2^3*v 3^2*w 1^3 + 288*v 0*v 1^4*v 2^3*v 3^2*w 1^2*w 2 + 192*v 0*v 1^4*v 2^3*v 3^2*w 1^2*w 3 + 276*v 0*v 1^4*v 2^3*v 3^2*w 1*w 2^2 + 488*v 0*v 1^4*v 2^3*v 3^2*w 1*w 2*w 3 + 180*v 0*v 1^4*v 2^3*v 3^2*w 1*w 3^2 + 244*v 0*v 1^4*v 2^3*v 3^2*w 2^3 + 448*v 0*v 1^4*v 2^3*v 3^2*w 2^2*w 3 + 436*v 0*v 1^4*v 2^3*v 3^2*w 2*w 3^2 + 184*v 0*v 1^4*v 2^3*v 3^2*w 3^3 + 96*v 0*v 1^4*v 2^2*v 3^3*w 1^3 + 192*v 0*v 1^4*v 2^2*v 3^3*w 1^2*w 2 + 288*v 0*v 1^4*v 2^2*v 3^3*w 1^2*w 3 + 180*v 0*v 1^4*v 2^2*v 3^3*w 1*w 2^2 + 376*v 0*v 1^4*v 2^2*v 3^3*w 1*w 2*w 3 + 276*v 0*v 1^4*v 2^2*v 3^3*w 1*w 3^2 + 72*v 0*v 1^4*v 2^2*v 3^3*w 2^3 + 212*v 0*v 1^4*v 2^2*v 3^3*w 2^2*w 3 + 224*v 0*v 1^4*v 2^2*v 3^3*w 2*w 3^2 + 132*v 0*v 1^4*v 2^2*v 3^3*w 3^3 + 48*v 0*v 1^3*v 2^4*v 3^2*w 1^3 + 216*v 0*v 1^3*v 2^4*v 3^2*w 1^2*w 2 + 120*v 0*v 1^3*v 2^4*v 3^2*w 1^2*w 3 + 264*v 0*v 1^3*v 2^4*v 3^2*w 1*w 2^2 + 320*v 0*v 1^3*v 2^4*v 3^2*w 1*w 2*w 3 + 120*v 0*v 1^3*v 2^4*v 3^2*w 1*w 3^2 + 192*v 0*v 1^3*v 2^4*v 3^2*w 2^3 + 280*v 0*v 1^3*v 2^4*v 3^2*w 2^2*w 3 + 256*v 0*v 1^3*v 2^4*v 3^2*w 2*w 3^2 + 72*v 0*v 1^3*v 2^4*v 3^2*w 3^3 + 96*v 0*v 1^3*v 2^3*v 3^3*w 1^3 + 336*v 0*v 1^3*v 2^3*v 3^3*w 1^2*w 2 + 336*v 0*v 1^3*v 2^3*v 3^3*w 1^2*w 3 + 384*v 0*v 1^3*v 2^3*v 3^3*w 1*w 2^2 + 704*v 0*v 1^3*v 2^3*v 3^3*w 1*w 2*w 3 + 384*v 0*v 1^3*v 2^3*v 3^3*w 1*w 3^2 + 264*v 0*v 1^3*v 2^3*v 3^3*w 2^3 + 568*v 0*v 1^3*v 2^3*v 3^3*w 2^2*w 3 + 568*v 0*v 1^3*v 2^3*v 3^3*w 2*w 3^2 + 264*v 0*v 1^3*v 2^3*v 3^3*w 3^3 + 48*v 0*v 1^3*v 2^2*v 3^4*w 1^3 + 120*v 0*v 1^3*v 2^2*v 3^4*w 1^2*w 2 + 216*v 0*v 1^3*v 2^2*v 3^4*w 1^2*w 3 + 120*v 0*v 1^3*v 2^2*v 3^4*w 1*w 2^2 + 320*v 0*v 1^3*v 2^2*v 3^4*w 1*w 2*w 3 + 264*v 0*v 1^3*v 2^2*v 3^4*w 1*w 3^2 + 72*v 0*v 1^3*v 2^2*v 3^4*w 2^3 + 256*v 0*v 1^3*v 2^2*v 3^4*w 2^2*w 3 + 280*v 0*v 1^3*v 2^2*v 3^4*w 2*w 3^2 + 192*v 0*v 1^3*v 2^2*v 3^4*w 3^3 + 8*v 0*v 1^2*v 2^5*v 3^2*w 1^3 + 48*v 0*v 1^2*v 2^5*v 3^2*w 1^2*w 2 + 24*v 0*v 1^2*v 2^5*v 3^2*w 1^2*w 3 + 32*v 0*v 1^2*v 2^5*v 3^2*w 1*w 2*w 3 + 16*v 0*v 1^2*v 2^5*v 3^2*w 2^3 + 16*v 0*v 1^2*v 2^5*v 3^2*w 2^2*w 3 + 16*v 0*v 1^2*v 2^5*v 3^2*w 2*w 3^2 + 24*v 0*v 1^2*v 2^4*v 3^3*w 1^3 + 120*v 0*v 1^2*v 2^4*v 3^3*w 1^2*w 2 + 96*v 0*v 1^2*v 2^4*v 3^3*w 1^2*w 3 + 48*v 0*v 1^2*v 2^4*v 3^3*w 1*w 2^2 + 96*v 0*v 1^2*v 2^4*v 3^3*w 1*w 2*w 3 + 48*v 0*v 1^2*v 2^4*v 3^3*w 1*w 3^2 + 96*v 0*v 1^2*v 2^4*v 3^3*w 2^3 + 144*v 0*v 1^2*v 2^4*v 3^3*w 2^2*w 3 + 144*v 0*v 1^2*v 2^4*v 3^3*w 2*w 3^2 + 48*v 0*v 1^2*v 2^4*v 3^3*w 3^3 + 24*v 0*v 1^2*v 2^3*v 3^4*w 1^3 + 96*v 0*v 1^2*v 2^3*v 3^4*w 1^2*w 2 + 120*v 0*v 1^2*v 2^3*v 3^4*w 1^2*w 3 + 48*v 0*v 1^2*v 2^3*v 3^4*w 1*w 2^2 + 96*v 0*v 1^2*v 2^3*v 3^4*w 1*w 2*w 3 + 48*v 0*v 1^2*v 2^3*v 3^4*w 1*w 3^2 + 48*v 0*v 1^2*v 2^3*v 3^4*w 2^3 + 144*v 0*v 1^2*v 2^3*v 3^4*w 2^2*w 3 + 144*v 0*v 1^2*v 2^3*v 3^4*w 2*w 3^2 + 96*v 0*v 1^2*v 2^3*v 3^4*w 3^3 + 8*v 0*v 1^2*v 2^2*v 3^5*w 1^3 + 24*v 0*v 1^2*v 2^2*v 3^5*w 1^2*w 2 + 48*v 0*v 1^2*v 2^2*v 3^5*w 1^2*w 3 + 32*v 0*v 1^2*v 2^2*v 3^5*w 1*w 2*w 3 + 16*v 0*v 1^2*v 2^2*v 3^5*w 2^2*w 3 + 16*v 0*v 1^2*v 2^2*v 3^5*w 2*w 3^2 + 16*v 0*v 1^2*v 2^2*v 3^5*w 3^3 - 72*v 0*v 1*v 2^8*w 1^3 - 180*v 0*v 1*v 2^8*w 1^2*w 2 - 108*v 0*v 1*v 2^8*w 1^2*w 3 - 144*v 0*v 1*v 2^8*w 1*w 2^2 - 180*v 0*v 1*v 2^8*w 1*w 2*w 3 - 72*v 0*v 1*v 2^8*w 1*w 3^2 - 36*v 0*v 1*v 2^8*w 2^3 - 72*v 0*v 1*v 2^8*w 2^2*w 3 - 54*v 0*v 1*v 2^8*w 2*w 3^2 - 18*v 0*v 1*v 2^8*w 3^3 - 72*v 0*v 1*v 2^7*v 3*w 1^3 - 180*v 0*v 1*v 2^7*v 3*w 1^2*w 2 - 216*v 0*v 1*v 2^7*v 3*w 1^2*w 3 - 144*v 0*v 1*v 2^7*v 3*w 1*w 2^2 - 288*v 0*v 1*v 2^7*v 3*w 1*w 2*w 3 - 180*v 0*v 1*v 2^7*v 3*w 1*w 3^2 - 36*v 0*v 1*v 2^7*v 3*w 2^3 - 99*v 0*v 1*v 2^7*v 3*w 2^2*w 3 - 108*v 0*v 1*v 2^7*v 3*w 2*w 3^2 - 45*v 0*v 1*v 2^7*v 3*w 3^3 - 172*v 0*v 1*v 2^6*v 3^2*w 1^3 - 598*v 0*v 1*v 2^6*v 3^2*w 1^2*w 2 - 298*v 0*v 1*v 2^6*v 3^2*w 1^2*w 3 - 476*v 0*v 1*v 2^6*v 3^2*w 1*w 2^2 - 614*v 0*v 1*v 2^6*v 3^2*w 1*w 2*w 3 - 200*v 0*v 1*v 2^6*v 3^2*w 1*w 3^2 - 164*v 0*v 1*v 2^6*v 3^2*w 2^3 - 290*v 0*v 1*v 2^6*v 3^2*w 2^2*w 3 - 227*v 0*v 1*v 2^6*v 3^2*w 2*w 3^2 - 61*v 0*v 1*v 2^6*v 3^2*w 3^3 - 332*v 0*v 1*v 2^5*v 3^3*w 1^3 - 830*v 0*v 1*v 2^5*v 3^3*w 1^2*w 2 - 806*v 0*v 1*v 2^5*v 3^3*w 1^2*w 3 - 640*v 0*v 1*v 2^5*v 3^3*w 1*w 2^2 - 1074*v 0*v 1*v 2^5*v 3^3*w 1*w 2*w 3 - 616*v 0*v 1*v 2^5*v 3^3*w 1*w 3^2 - 262*v 0*v 1*v 2^5*v 3^3*w 2^3 - 545*v 0*v 1*v 2^5*v 3^3*w 2^2*w 3 - 515*v 0*v 1*v 2^5*v 3^3*w 2*w 3^2 - 216*v 0*v 1*v 2^5*v 3^3*w 3^3 - 168*v 0*v 1*v 2^4*v 3^4*w 1^3 - 420*v 0*v 1*v 2^4*v 3^4*w 1^2*w 2 - 444*v 0*v 1*v 2^4*v 3^4*w 1^2*w 3 - 288*v 0*v 1*v 2^4*v 3^4*w 1*w 2^2 - 564*v 0*v 1*v 2^4*v 3^4*w 1*w 2*w 3 - 312*v 0*v 1*v 2^4*v 3^4*w 1*w 3^2 - 168*v 0*v 1*v 2^4*v 3^4*w 2^3 - 396*v 0*v 1*v 2^4*v 3^4*w 2^2*w 3 - 402*v 0*v 1*v 2^4*v 3^4*w 2*w 3^2 - 174*v 0*v 1*v 2^4*v 3^4*w 3^3 - 176*v 0*v 1*v 2^3*v 3^5*w 1^3 - 440*v 0*v 1*v 2^3*v 3^5*w 1^2*w 2 - 572*v 0*v 1*v 2^3*v 3^5*w 1^2*w 3 - 328*v 0*v 1*v 2^3*v 3^5*w 1*w 2^2 - 684*v 0*v 1*v 2^3*v 3^5*w 1*w 2*w 3 - 460*v 0*v 1*v 2^3*v 3^5*w 1*w 3^2 - 144*v 0*v 1*v 2^3*v 3^5*w 2^3 - 365*v 0*v 1*v 2^3*v 3^5*w 2^2*w 3 - 422*v 0*v 1*v 2^3*v 3^5*w 2*w 3^2 - 217*v 0*v 1*v 2^3*v 3^5*w 3^3 - 76*v 0*v 1*v 2^2*v 3^6*w 1^3 - 190*v 0*v 1*v 2^2*v 3^6*w 1^2*w 2 - 322*v 0*v 1*v 2^2*v 3^6*w 1^2*w 3 - 140*v 0*v 1*v 2^2*v 3^6*w 1*w 2^2 - 374*v 0*v 1*v 2^2*v 3^6*w 1*w 2*w 3 - 248*v 0*v 1*v 2^2*v 3^6*w 1*w 3^2 - 46*v 0*v 1*v 2^2*v 3^6*w 2^3 - 164*v 0*v 1*v 2^2*v 3^6*w 2^2*w 3 - 185*v 0*v 1*v 2^2*v 3^6*w 2*w 3^2 - 107*v 0*v 1*v 2^2*v 3^6*w 3^3 - 36*v 0*v 1*v 2*v 3^7*w 1^3 - 90*v 0*v 1*v 2*v 3^7*w 1^2*w 2 - 162*v 0*v 1*v 2*v 3^7*w 1^2*w 3 - 72*v 0*v 1*v 2*v 3^7*w 1*w 2^2 - 198*v 0*v 1*v 2*v 3^7*w 1*w 2*w 3 - 144*v 0*v 1*v 2*v 3^7*w 1*w 3^2 - 18*v 0*v 1*v 2*v 3^7*w 2^3 - 63*v 0*v 1*v 2*v 3^7*w 2^2*w 3 - 81*v 0*v 1*v 2*v 3^7*w 2*w 3^2 - 36*v 0*v 1*v 2*v 3^7*w 3^3 - 36*v 0*v 2^9*w 1^3 - 36*v 0*v 2^9*w 1^2*w 2 - 54*v 0*v 2^9*w 1^2*w 3 + 36*v 0*v 2^9*w 1*w 2^2 - 36*v 0*v 2^9*w 1*w 2*w 3 - 36*v 0*v 2^9*w 1*w 3^2 + 36*v 0*v 2^9*w 2^3 + 18*v 0*v 2^9*w 2^2*w 3 - 9*v 0*v 2^9*w 3^3 - 72*v 0*v 2^8*v 3*w 1^3 - 180*v 0*v 2^8*v 3*w 1^2*w 2 - 216*v 0*v 2^8*v 3*w 1^2*w 3 - 252*v 0*v 2^8*v 3*w 1*w 2^2 - 477*v 0*v 2^8*v 3*w 1*w 2*w 3 - 261*v 0*v 2^8*v 3*w 1*w 3^2 - 144*v 0*v 2^8*v 3*w 2^3 - 324*v 0*v 2^8*v 3*w 2^2*w 3 - 315*v 0*v 2^8*v 3*w 2*w 3^2 - 126*v 0*v 2^8*v 3*w 3^3 - 122*v 0*v 2^7*v 3^2*w 1^3 - 104*v 0*v 2^7*v 3^2*w 1^2*w 2 - 222*v 0*v 2^7*v 3^2*w 1^2*w 3 + 116*v 0*v 2^7*v 3^2*w 1*w 2^2 - 159*v 0*v 2^7*v 3^2*w 1*w 2*w 3 - 156*v 0*v 2^7*v 3^2*w 1*w 3^2 + 14*v 0*v 2^7*v 3^2*w 2^3 - 74*v 0*v 2^7*v 3^2*w 2^2*w 3 - 159*v 0*v 2^7*v 3^2*w 2*w 3^2 - 72*v 0*v 2^7*v 3^2*w 3^3 - 252*v 0*v 2^6*v 3^3*w 1^3 - 364*v 0*v 2^6*v 3^3*w 1^2*w 2 - 482*v 0*v 2^6*v 3^3*w 1^2*w 3 - 254*v 0*v 2^6*v 3^3*w 1*w 2^2 - 737*v 0*v 2^6*v 3^3*w 1*w 2*w 3 - 595*v 0*v 2^6*v 3^3*w 1*w 3^2 - 127*v 0*v 2^6*v 3^3*w 2^3 - 392*v 0*v 2^6*v 3^3*w 2^2*w 3 - 528*v 0*v 2^6*v 3^3*w 2*w 3^2 - 255*v 0*v 2^6*v 3^3*w 3^3 - 250*v 0*v 2^5*v 3^4*w 1^3 - 162*v 0*v 2^5*v 3^4*w 1^2*w 2 - 244*v 0*v 2^5*v 3^4*w 1^2*w 3 - 31*v 0*v 2^5*v 3^4*w 1*w 2*w 3 - 92*v 0*v 2^5*v 3^4*w 1*w 3^2 + 38*v 0*v 2^5*v 3^4*w 2^3 + 118*v 0*v 2^5*v 3^4*w 2^2*w 3 + 72*v 0*v 2^5*v 3^4*w 2*w 3^2 + 75*v 0*v 2^5*v 3^4*w 3^3 - 172*v 0*v 2^4*v 3^5*w 1^3 - 142*v 0*v 2^4*v 3^5*w 1^2*w 2 - 60*v 0*v 2^4*v 3^5*w 1^2*w 3 - 110*v 0*v 2^4*v 3^5*w 1*w 2^2 + 65*v 0*v 2^4*v 3^5*w 1*w 2*w 3 + 99*v 0*v 2^4*v 3^5*w 1*w 3^2 + 27*v 0*v 2^4*v 3^5*w 2^3 + 60*v 0*v 2^4*v 3^5*w 2^2*w 3 + 145*v 0*v 2^4*v 3^5*w 2*w 3^2 + 68*v 0*v 2^4*v 3^5*w 3^3 - 126*v 0*v 2^3*v 3^6*w 1^3 - 224*v 0*v 2^3*v 3^6*w 1^2*w 2 - 106*v 0*v 2^3*v 3^6*w 1^2*w 3 - 274*v 0*v 2^3*v 3^6*w 1*w 2^2 - 209*v 0*v 2^3*v 3^6*w 1*w 2*w 3 + 22*v 0*v 2^3*v 3^6*w 1*w 3^2 - 138*v 0*v 2^3*v 3^6*w 2^3 - 252*v 0*v 2^3*v 3^6*w 2^2*w 3 - 131*v 0*v 2^3*v 3^6*w 2*w 3^2 - 40*v 0*v 2^3*v 3^6*w 3^3 - 56*v 0*v 2^2*v 3^7*w 1^3 - 192*v 0*v 2^2*v 3^7*w 1^2*w 2 - 74*v 0*v 2^2*v 3^7*w 1^2*w 3 - 240*v 0*v 2^2*v 3^7*w 1*w 2^2 - 303*v 0*v 2^2*v 3^7*w 1*w 2*w 3 - 13*v 0*v 2^2*v 3^7*w 1*w 3^2 - 135*v 0*v 2^2*v 3^7*w 2^3 - 300*v 0*v 2^2*v 3^7*w 2^2*w 3 - 230*v 0*v 2^2*v 3^7*w 2*w 3^2 - 79*v 0*v 2^2*v 3^7*w 3^3 - 18*v 0*v 2*v 3^8*w 1^3 - 90*v 0*v 2*v 3^8*w 1^2*w 2 - 54*v 0*v 2*v 3^8*w 1^2*w 3 - 108*v 0*v 2*v 3^8*w 1*w 2^2 - 189*v 0*v 2*v 3^8*w 1*w 2*w 3 - 72*v 0*v 2*v 3^8*w 1*w 3^2 - 72*v 0*v 2*v 3^8*w 2^3 - 162*v 0*v 2*v 3^8*w 2^2*w 3 - 162*v 0*v 2*v 3^8*w 2*w 3^2 - 72*v 0*v 2*v 3^8*w 3^3 - 18*v 0*v 3^9*w 1^2*w 2 - 18*v 0*v 3^9*w 1*w 2^2 - 36*v 0*v 3^9*w 1*w 2*w 3 - 9*v 0*v 3^9*w 2^3 - 18*v 0*v 3^9*w 2^2*w 3 - 18*v 0*v 3^9*w 2*w 3^2 - 64*v 1^6*v 2^2*v 3^2*w 1^3 - 96*v 1^6*v 2^2*v 3^2*w 1^2*w 2 - 96*v 1^6*v 2^2*v 3^2*w 1^2*w 3 - 72*v 1^6*v 2^2*v 3^2*w 1*w 2^2 - 112*v 1^6*v 2^2*v 3^2*w 1*w 2*w 3 - 72*v 1^6*v 2^2*v 3^2*w 1*w 3^2 - 20*v 1^6*v 2^2*v 3^2*w 2^3 - 44*v 1^6*v 2^2*v 3^2*w 2^2*w 3 - 44*v 1^6*v 2^2*v 3^2*w 2*w 3^2 - 20*v 1^6*v 2^2*v 3^2*w 3^3 - 48*v 1^5*v 2^3*v 3^2*w 1^3 - 384*v 1^5*v 2^3*v 3^2*w 1^2*w 2 - 288*v 1^5*v 2^3*v 3^2*w 1^2*w 3 - 348*v 1^5*v 2^3*v 3^2*w 1*w 2^2 - 600*v 1^5*v 2^3*v 3^2*w 1*w 2*w 3 - 252*v 1^5*v 2^3*v 3^2*w 1*w 3^2 - 264*v 1^5*v 2^3*v 3^2*w 2^3 - 492*v 1^5*v 2^3*v 3^2*w 2^2*w 3 - 480*v 1^5*v 2^3*v 3^2*w 2*w 3^2 - 204*v 1^5*v 2^3*v 3^2*w 3^3 - 160*v 1^5*v 2^2*v 3^3*w 1^3 - 288*v 1^5*v 2^2*v 3^3*w 1^2*w 2 - 384*v 1^5*v 2^2*v 3^3*w 1^2*w 3 - 252*v 1^5*v 2^2*v 3^3*w 1*w 2^2 - 488*v 1^5*v 2^2*v 3^3*w 1*w 2*w 3 - 348*v 1^5*v 2^2*v 3^3*w 1*w 3^2 - 92*v 1^5*v 2^2*v 3^3*w 2^3 - 256*v 1^5*v 2^2*v 3^3*w 2^2*w 3 - 268*v 1^5*v 2^2*v 3^3*w 2*w 3^2 - 152*v 1^5*v 2^2*v 3^3*w 3^3 - 32*v 1^4*v 2^4*v 3^2*w 1^3 - 504*v 1^4*v 2^4*v 3^2*w 1^2*w 2 - 312*v 1^4*v 2^4*v 3^2*w 1^2*w 3 - 540*v 1^4*v 2^4*v 3^2*w 1*w 2^2 - 808*v 1^4*v 2^4*v 3^2*w 1*w 2*w 3 - 300*v 1^4*v 2^4*v 3^2*w 1*w 3^2 - 436*v 1^4*v 2^4*v 3^2*w 2^3 - 728*v 1^4*v 2^4*v 3^2*w 2^2*w 3 - 692*v 1^4*v 2^4*v 3^2*w 2*w 3^2 - 256*v 1^4*v 2^4*v 3^2*w 3^3 - 176*v 1^4*v 2^3*v 3^3*w 1^3 - 816*v 1^4*v 2^3*v 3^3*w 1^2*w 2 - 816*v 1^4*v 2^3*v 3^3*w 1^2*w 3 - 840*v 1^4*v 2^3*v 3^3*w 1*w 2^2 - 1568*v 1^4*v 2^3*v 3^3*w 1*w 2*w 3 - 840*v 1^4*v 2^3*v 3^3*w 1*w 3^2 - 580*v 1^4*v 2^3*v 3^3*w 2^3 - 1228*v 1^4*v 2^3*v 3^3*w 2^2*w 3 - 1228*v 1^4*v 2^3*v 3^3*w 2*w 3^2 - 580*v 1^4*v 2^3*v 3^3*w 3^3 - 144*v 1^4*v 2^2*v 3^4*w 1^3 - 312*v 1^4*v 2^2*v 3^4*w 1^2*w 2 - 504*v 1^4*v 2^2*v 3^4*w 1^2*w 3 - 300*v 1^4*v 2^2*v 3^4*w 1*w 2^2 - 696*v 1^4*v 2^2*v 3^4*w 1*w 2*w 3 - 540*v 1^4*v 2^2*v 3^4*w 1*w 3^2 - 144*v 1^4*v 2^2*v 3^4*w 2^3 - 468*v 1^4*v 2^2*v 3^4*w 2^2*w 3 - 504*v 1^4*v 2^2*v 3^4*w 2*w 3^2 - 324*v 1^4*v 2^2*v 3^4*w 3^3 - 56*v 1^3*v 2^5*v 3^2*w 1^3 - 264*v 1^3*v 2^5*v 3^2*w 1^2*w 2 - 144*v 1^3*v 2^5*v 3^2*w 1^2*w 3 - 264*v 1^3*v 2^5*v 3^2*w 1*w 2^2 - 352*v 1^3*v 2^5*v 3^2*w 1*w 2*w 3 - 120*v 1^3*v 2^5*v 3^2*w 1*w 3^2 - 208*v 1^3*v 2^5*v 3^2*w 2^3 - 296*v 1^3*v 2^5*v 3^2*w 2^2*w 3 - 272*v 1^3*v 2^5*v 3^2*w 2*w 3^2 - 72*v 1^3*v 2^5*v 3^2*w 3^3 - 168*v 1^3*v 2^4*v 3^3*w 1^3 - 672*v 1^3*v 2^4*v 3^3*w 1^2*w 2 - 552*v 1^3*v 2^4*v 3^3*w 1^2*w 3 - 696*v 1^3*v 2^4*v 3^3*w 1*w 2^2 - 1120*v 1^3*v 2^4*v 3^3*w 1*w 2*w 3 - 552*v 1^3*v 2^4*v 3^3*w 1*w 3^2 - 552*v 1^3*v 2^4*v 3^3*w 2^3 - 992*v 1^3*v 2^4*v 3^3*w 2^2*w 3 - 968*v 1^3*v 2^4*v 3^3*w 2*w 3^2 - 384*v 1^3*v 2^4*v 3^3*w 3^3 - 168*v 1^3*v 2^3*v 3^4*w 1^3 - 552*v 1^3*v 2^3*v 3^4*w 1^2*w 2 - 672*v 1^3*v 2^3*v 3^4*w 1^2*w 3 - 552*v 1^3*v 2^3*v 3^4*w 1*w 2^2 - 1120*v 1^3*v 2^3*v 3^4*w 1*w 2*w 3 - 696*v 1^3*v 2^3*v 3^4*w 1*w 3^2 - 384*v 1^3*v 2^3*v 3^4*w 2^3 - 968*v 1^3*v 2^3*v 3^4*w 2^2*w 3 - 992*v 1^3*v 2^3*v 3^4*w 2*w 3^2 - 552*v 1^3*v 2^3*v 3^4*w 3^3 - 56*v 1^3*v 2^2*v 3^5*w 1^3 - 144*v 1^3*v 2^2*v 3^5*w 1^2*w 2 - 264*v 1^3*v 2^2*v 3^5*w 1^2*w 3 - 120*v 1^3*v 2^2*v 3^5*w 1*w 2^2 - 352*v 1^3*v 2^2*v 3^5*w 1*w 2*w 3 - 264*v 1^3*v 2^2*v 3^5*w 1*w 3^2 - 72*v 1^3*v 2^2*v 3^5*w 2^3 - 272*v 1^3*v 2^2*v 3^5*w 2^2*w 3 - 296*v 1^3*v 2^2*v 3^5*w 2*w 3^2 - 208*v 1^3*v 2^2*v 3^5*w 3^3 + 72*v 1^2*v 2^8*w 1^2*w 2 + 108*v 1^2*v 2^8*w 1*w 2^2 + 108*v 1^2*v 2^8*w 1*w 2*w 3 + 36*v 1^2*v 2^8*w 1*w 3^2 + 36*v 1^2*v 2^8*w 2^3 + 72*v 1^2*v 2^8*w 2^2*w 3 + 54*v 1^2*v 2^8*w 2*w 3^2 + 18*v 1^2*v 2^8*w 3^3 + 72*v 1^2*v 2^7*v 3*w 1^2*w 2 + 108*v 1^2*v 2^7*v 3*w 1^2*w 3 + 108*v 1^2*v 2^7*v 3*w 1*w 2^2 + 216*v 1^2*v 2^7*v 3*w 1*w 2*w 3 + 144*v 1^2*v 2^7*v 3*w 1*w 3^2 + 36*v 1^2*v 2^7*v 3*w 2^3 + 99*v 1^2*v 2^7*v 3*w 2^2*w 3 + 108*v 1^2*v 2^7*v 3*w 2*w 3^2 + 45*v 1^2*v 2^7*v 3*w 3^3 - 8*v 1^2*v 2^6*v 3^2*w 1^3 + 292*v 1^2*v 2^6*v 3^2*w 1^2*w 2 + 16*v 1^2*v 2^6*v 3^2*w 1^2*w 3 + 390*v 1^2*v 2^6*v 3^2*w 1*w 2^2 + 410*v 1^2*v 2^6*v 3^2*w 1*w 2*w 3 + 114*v 1^2*v 2^6*v 3^2*w 1*w 3^2 + 148*v 1^2*v 2^6*v 3^2*w 2^3 + 274*v 1^2*v 2^6*v 3^2*w 2^2*w 3 + 211*v 1^2*v 2^6*v 3^2*w 2*w 3^2 + 61*v 1^2*v 2^6*v 3^2*w 3^3 - 32*v 1^2*v 2^5*v 3^3*w 1^3 + 164*v 1^2*v 2^5*v 3^3*w 1^2*w 2 + 188*v 1^2*v 2^5*v 3^3*w 1^2*w 3 + 426*v 1^2*v 2^5*v 3^3*w 1*w 2^2 + 614*v 1^2*v 2^5*v 3^3*w 1*w 2*w 3 + 402*v 1^2*v 2^5*v 3^3*w 1*w 3^2 + 150*v 1^2*v 2^5*v 3^3*w 2^3 + 385*v 1^2*v 2^5*v 3^3*w 2^2*w 3 + 355*v 1^2*v 2^5*v 3^3*w 2*w 3^2 + 168*v 1^2*v 2^5*v 3^3*w 3^3 - 48*v 1^2*v 2^4*v 3^4*w 1^3 - 48*v 1^2*v 2^4*v 3^4*w 1^2*w 2 - 24*v 1^2*v 2^4*v 3^4*w 1^2*w 3 + 108*v 1^2*v 2^4*v 3^4*w 1*w 2^2 + 204*v 1^2*v 2^4*v 3^4*w 1*w 2*w 3 + 132*v 1^2*v 2^4*v 3^4*w 1*w 3^2 + 24*v 1^2*v 2^4*v 3^4*w 2^3 + 108*v 1^2*v 2^4*v 3^4*w 2^2*w 3 + 114*v 1^2*v 2^4*v 3^4*w 2*w 3^2 + 30*v 1^2*v 2^4*v 3^4*w 3^3 - 32*v 1^2*v 2^3*v 3^5*w 1^3 + 56*v 1^2*v 2^3*v 3^5*w 1^2*w 2 + 140*v 1^2*v 2^3*v 3^5*w 1^2*w 3 + 192*v 1^2*v 2^3*v 3^5*w 1*w 2^2 + 380*v 1^2*v 2^3*v 3^5*w 1*w 2*w 3 + 324*v 1^2*v 2^3*v 3^5*w 1*w 3^2 + 96*v 1^2*v 2^3*v 3^5*w 2^3 + 205*v 1^2*v 2^3*v 3^5*w 2^2*w 3 + 262*v 1^2*v 2^3*v 3^5*w 2*w 3^2 + 105*v 1^2*v 2^3*v 3^5*w 3^3 - 8*v 1^2*v 2^2*v 3^6*w 1^3 + 52*v 1^2*v 2^2*v 3^6*w 1^2*w 2 + 160*v 1^2*v 2^2*v 3^6*w 1^2*w 3 + 102*v 1^2*v 2^2*v 3^6*w 1*w 2^2 + 266*v 1^2*v 2^2*v 3^6*w 1*w 2*w 3 + 210*v 1^2*v 2^2*v 3^6*w 1*w 3^2 + 46*v 1^2*v 2^2*v 3^6*w 2^3 + 148*v 1^2*v 2^2*v 3^6*w 2^2*w 3 + 169*v 1^2*v 2^2*v 3^6*w 2*w 3^2 + 91*v 1^2*v 2^2*v 3^6*w 3^3 + 36*v 1^2*v 2*v 3^7*w 1^2*w 2 + 108*v 1^2*v 2*v 3^7*w 1^2*w 3 + 54*v 1^2*v 2*v 3^7*w 1*w 2^2 + 162*v 1^2*v 2*v 3^7*w 1*w 2*w 3 + 126*v 1^2*v 2*v 3^7*w 1*w 3^2 + 18*v 1^2*v 2*v 3^7*w 2^3 + 63*v 1^2*v 2*v 3^7*w 2^2*w 3 + 81*v 1^2*v 2*v 3^7*w 2*w 3^2 + 36*v 1^2*v 2*v 3^7*w 3^3 + 72*v 1*v 2^9*w 1^3 + 144*v 1*v 2^9*w 1^2*w 2 + 108*v 1*v 2^9*w 1^2*w 3 + 36*v 1*v 2^9*w 1*w 2^2 + 126*v 1*v 2^9*w 1*w 2*w 3 + 90*v 1*v 2^9*w 1*w 3^2 - 36*v 1*v 2^9*w 2^3 - 18*v 1*v 2^9*w 2^2*w 3 + 18*v 1*v 2^9*w 2*w 3^2 + 27*v 1*v 2^9*w 3^3 + 144*v 1*v 2^8*v 3*w 1^3 + 360*v 1*v 2^8*v 3*w 1^2*w 2 + 306*v 1*v 2^8*v 3*w 1^2*w 3 + 396*v 1*v 2^8*v 3*w 1*w 2^2 + 603*v 1*v 2^8*v 3*w 1*w 2*w 3 + 315*v 1*v 2^8*v 3*w 1*w 3^2 + 180*v 1*v 2^8*v 3*w 2^3 + 387*v 1*v 2^8*v 3*w 2^2*w 3 + 369*v 1*v 2^8*v 3*w 2*w 3^2 + 153*v 1*v 2^8*v 3*w 3^3 + 244*v 1*v 2^7*v 3^2*w 1^3 + 812*v 1*v 2^7*v 3^2*w 1^2*w 2 + 516*v 1*v 2^7*v 3^2*w 1^2*w 3 + 470*v 1*v 2^7*v 3^2*w 1*w 2^2 + 893*v 1*v 2^7*v 3^2*w 1*w 2*w 3 + 402*v 1*v 2^7*v 3^2*w 1*w 3^2 + 100*v 1*v 2^7*v 3^2*w 2^3 + 255*v 1*v 2^7*v 3^2*w 2^2*w 3 + 336*v 1*v 2^7*v 3^2*w 2*w 3^2 + 142*v 1*v 2^7*v 3^2*w 3^3 + 504*v 1*v 2^6*v 3^3*w 1^3 + 1432*v 1*v 2^6*v 3^3*w 1^2*w 2 + 1106*v 1*v 2^6*v 3^3*w 1^2*w 3 + 1096*v 1*v 2^6*v 3^3*w 1*w 2^2 + 1837*v 1*v 2^6*v 3^3*w 1*w 2*w 3 + 1097*v 1*v 2^6*v 3^3*w 1*w 3^2 + 387*v 1*v 2^6*v 3^3*w 2^3 + 809*v 1*v 2^6*v 3^3*w 2^2*w 3 + 932*v 1*v 2^6*v 3^3*w 2*w 3^2 + 446*v 1*v 2^6*v 3^3*w 3^3 + 500*v 1*v 2^5*v 3^4*w 1^3 + 1332*v 1*v 2^5*v 3^4*w 1^2*w 2 + 1168*v 1*v 2^5*v 3^4*w 1^2*w 3 + 1014*v 1*v 2^5*v 3^4*w 1*w 2^2 + 1513*v 1*v 2^5*v 3^4*w 1*w 2*w 3 + 778*v 1*v 2^5*v 3^4*w 1*w 3^2 + 308*v 1*v 2^5*v 3^4*w 2^3 + 489*v 1*v 2^5*v 3^4*w 2^2*w 3 + 429*v 1*v 2^5*v 3^4*w 2*w 3^2 + 149*v 1*v 2^5*v 3^4*w 3^3 + 344*v 1*v 2^4*v 3^5*w 1^3 + 856*v 1*v 2^4*v 3^5*w 1^2*w 2 + 1098*v 1*v 2^4*v 3^5*w 1^2*w 3 + 664*v 1*v 2^4*v 3^5*w 1*w 2^2 + 1231*v 1*v 2^4*v 3^5*w 1*w 2*w 3 + 783*v 1*v 2^4*v 3^5*w 1*w 3^2 + 197*v 1*v 2^4*v 3^5*w 2^3 + 441*v 1*v 2^4*v 3^5*w 2^2*w 3 + 423*v 1*v 2^4*v 3^5*w 2*w 3^2 + 239*v 1*v 2^4*v 3^5*w 3^3 + 252*v 1*v 2^3*v 3^6*w 1^3 + 680*v 1*v 2^3*v 3^6*w 1^2*w 2 + 976*v 1*v 2^3*v 3^6*w 1^2*w 3 + 656*v 1*v 2^3*v 3^6*w 1*w 2^2 + 1195*v 1*v 2^3*v 3^6*w 1*w 2*w 3 + 700*v 1*v 2^3*v 3^6*w 1*w 3^2 + 290*v 1*v 2^3*v 3^6*w 2^3 + 617*v 1*v 2^3*v 3^6*w 2^2*w 3 + 524*v 1*v 2^3*v 3^6*w 2*w 3^2 + 276*v 1*v 2^3*v 3^6*w 3^3 + 112*v 1*v 2^2*v 3^7*w 1^3 + 300*v 1*v 2^2*v 3^7*w 1^2*w 2 + 566*v 1*v 2^2*v 3^7*w 1^2*w 3 + 318*v 1*v 2^2*v 3^7*w 1*w 2^2 + 767*v 1*v 2^2*v 3^7*w 1*w 2*w 3 + 431*v 1*v 2^2*v 3^7*w 1*w 3^2 + 181*v 1*v 2^2*v 3^7*w 2^3 + 453*v 1*v 2^2*v 3^7*w 2^2*w 3 + 402*v 1*v 2^2*v 3^7*w 2*w 3^2 + 184*v 1*v 2^2*v 3^7*w 3^3 + 36*v 1*v 2*v 3^8*w 1^3 + 108*v 1*v 2*v 3^8*w 1^2*w 2 + 180*v 1*v 2*v 3^8*w 1^2*w 3 + 126*v 1*v 2*v 3^8*w 1*w 2^2 + 297*v 1*v 2*v 3^8*w 1*w 2*w 3 + 180*v 1*v 2*v 3^8*w 1*w 3^2 + 90*v 1*v 2*v 3^8*w 2^3 + 207*v 1*v 2*v 3^8*w 2^2*w 3 + 207*v 1*v 2*v 3^8*w 2*w 3^2 + 90*v 1*v 2*v 3^8*w 3^3 + 18*v 1*v 3^9*w 1*w 2*w 3 + 9*v 1*v 3^9*w 2^3 + 18*v 1*v 3^9*w 2^2*w 3 + 18*v 1*v 3^9*w 2*w 3^2 + 36*v 2^10*w 1^3 + 54*v 2^10*w 1^2*w 3 - 36*v 2^10*w 1*w 2^2 - 18*v 2^10*w 1*w 2*w 3 + 36*v 2^10*w 1*w 3^2 - 18*v 2^10*w 2*w 3^2 + 9*v 2^10*w 3^3 + 108*v 2^9*v 3*w 1^3 + 144*v 2^9*v 3*w 1^2*w 2 + 234*v 2^9*v 3*w 1^2*w 3 + 108*v 2^9*v 3*w 1*w 2^2 + 351*v 2^9*v 3*w 1*w 2*w 3 + 243*v 2^9*v 3*w 1*w 3^2 + 72*v 2^9*v 3*w 2^3 + 216*v 2^9*v 3*w 2^2*w 3 + 243*v 2^9*v 3*w 2*w 3^2 + 117*v 2^9*v 3*w 3^3 + 194*v 2^8*v 3^2*w 1^3 + 162*v 2^8*v 3^2*w 1^2*w 2 + 366*v 2^8*v 3^2*w 1^2*w 3 + 238*v 2^8*v 3^2*w 1*w 2^2 + 380*v 2^8*v 3^2*w 1*w 2*w 3 + 255*v 2^8*v 3^2*w 1*w 3^2 + 354*v 2^8*v 3^2*w 2^3 + 560*v 2^8*v 3^2*w 2^2*w 3 + 322*v 2^8*v 3^2*w 2*w 3^2 + 108*v 2^8*v 3^2*w 3^3 + 374*v 2^7*v 3^3*w 1^3 + 216*v 2^7*v 3^3*w 1^2*w 2 + 582*v 2^7*v 3^3*w 1^2*w 3 + 110*v 2^7*v 3^3*w 1*w 2^2 + 690*v 2^7*v 3^3*w 1*w 2*w 3 + 603*v 2^7*v 3^3*w 1*w 3^2 + 337*v 2^7*v 3^3*w 2^3 + 858*v 2^7*v 3^3*w 2^2*w 3 + 829*v 2^7*v 3^3*w 2*w 3^2 + 301*v 2^7*v 3^3*w 3^3 + 502*v 2^6*v 3^4*w 1^3 + 276*v 2^6*v 3^4*w 1^2*w 2 + 474*v 2^6*v 3^4*w 1^2*w 3 + 342*v 2^6*v 3^4*w 1*w 2^2 + 746*v 2^6*v 3^4*w 1*w 2*w 3 + 379*v 2^6*v 3^4*w 1*w 3^2 + 427*v 2^6*v 3^4*w 2^3 + 1092*v 2^6*v 3^4*w 2^2*w 3 + 880*v 2^6*v 3^4*w 2*w 3^2 + 124*v 2^6*v 3^4*w 3^3 + 422*v 2^5*v 3^5*w 1^3 + 132*v 2^5*v 3^5*w 1^2*w 2 + 54*v 2^5*v 3^5*w 1^2*w 3 + 140*v 2^5*v 3^5*w 1*w 2^2 + 244*v 2^5*v 3^5*w 1*w 2*w 3 - v 2^5*v 3^5*w 1*w 3^2 + 137*v 2^5*v 3^5*w 2^3 + 724*v 2^5*v 3^5*w 2^2*w 3 + 739*v 2^5*v 3^5*w 2*w 3^2 + 113*v 2^5*v 3^5*w 3^3 + 298*v 2^4*v 3^6*w 1^3 + 240*v 2^4*v 3^6*w 1^2*w 2 - 6*v 2^4*v 3^6*w 1^2*w 3 + 286*v 2^4*v 3^6*w 1*w 2^2 + 326*v 2^4*v 3^6*w 1*w 2*w 3 + 69*v 2^4*v 3^6*w 1*w 3^2 + 139*v 2^4*v 3^6*w 2^3 + 700*v 2^4*v 3^6*w 2^2*w 3 + 828*v 2^4*v 3^6*w 2*w 3^2 + 334*v 2^4*v 3^6*w 3^3 + 182*v 2^3*v 3^7*w 1^3 + 360*v 2^3*v 3^7*w 1^2*w 2 + 54*v 2^3*v 3^7*w 1^2*w 3 + 378*v 2^3*v 3^7*w 1*w 2^2 + 498*v 2^3*v 3^7*w 1*w 2*w 3 + 143*v 2^3*v 3^7*w 1*w 3^2 + 193*v 2^3*v 3^7*w 2^3 + 640*v 2^3*v 3^7*w 2^2*w 3 + 807*v 2^3*v 3^7*w 2*w 3^2 + 397*v 2^3*v 3^7*w 3^3 + 74*v 2^2*v 3^8*w 1^3 + 264*v 2^2*v 3^8*w 1^2*w 2 + 72*v 2^2*v 3^8*w 1^2*w 3 + 276*v 2^2*v 3^8*w 1*w 2^2 + 356*v 2^2*v 3^8*w 1*w 2*w 3 + 169*v 2^2*v 3^8*w 1*w 3^2 + 153*v 2^2*v 3^8*w 2^3 + 346*v 2^2*v 3^8*w 2^2*w 3 + 470*v 2^2*v 3^8*w 2*w 3^2 + 291*v 2^2*v 3^8*w 3^3 + 18*v 2*v 3^9*w 1^3 + 108*v 2*v 3^9*w 1^2*w 2 + 36*v 2*v 3^9*w 1^2*w 3 + 108*v 2*v 3^9*w 1*w 2^2 + 153*v 2*v 3^9*w 1*w 2*w 3 + 72*v 2*v 3^9*w 1*w 3^2 + 63*v 2*v 3^9*w 2^3 + 108*v 2*v 3^9*w 2^2*w 3 + 144*v 2*v 3^9*w 2*w 3^2 + 90*v 2*v 3^9*w 3^3 + 18*v 3^10*w 1^2*w 2 + 18*v 3^10*w 1*w 2^2 + 18*v 3^10*w 1*w 2*w 3 + 9*v 3^10*w 2^3) * h1 + (8*v 0^5*v 1^2*v 2^2*v 3^2*w 0^2 - 8*v 0^5*v 1^2*v 2^2*v 3^2*w 0*w 1 - 8*v 0^5*v 1^2*v 2^2*v 3^2*w 0*w 2 - 8*v 0^5*v 1^2*v 2^2*v 3^2*w 0*w 3 + 8*v 0^5*v 1^2*v 2^2*v 3^2*w 1^2 + 16*v 0^5*v 1^2*v 2^2*v 3^2*w 1*w 2 + 16*v 0^5*v 1^2*v 2^2*v 3^2*w 1*w 3 + 8*v 0^5*v 1^2*v 2^2*v 3^2*w 2^2 + 16*v 0^5*v 1^2*v 2^2*v 3^2*w 2*w 3 + 8*v 0^5*v 1^2*v 2^2*v 3^2*w 3^2 + 24*v 0^4*v 1^3*v 2^2*v 3^2*w 0*w 1 - 24*v 0^4*v 1^3*v 2^2*v 3^2*w 1^2 - 24*v 0^4*v 1^3*v 2^2*v 3^2*w 1*w 2 - 24*v 0^4*v 1^3*v 2^2*v 3^2*w 1*w 3 + 24*v 0^4*v 1^2*v 2^3*v 3^2*w 0*w 2 - 24*v 0^4*v 1^2*v 2^3*v 3^2*w 1*w 2 - 24*v 0^4*v 1^2*v 2^3*v 3^2*w 2^2 - 24*v 0^4*v 1^2*v 2^3*v 3^2*w 2*w 3 + 24*v 0^4*v 1^2*v 2^2*v 3^3*w 0*w 3 - 24*v 0^4*v 1^2*v 2^2*v 3^3*w 1*w 3 - 24*v 0^4*v 1^2*v 2^2*v 3^3*w 2*w 3 - 24*v 0^4*v 1^2*v 2^2*v 3^3*w 3^2 + 24*v 0^3*v 1^4*v 2^2*v 3^2*w 1^2 + 48*v 0^3*v 1^3*v 2^3*v 3^2*w 1*w 2 + 48*v 0^3*v 1^3*v 2^2*v 3^3*w 1*w 3 + 24*v 0^3*v 1^2*v 2^4*v 3^2*w 2^2 + 48*v 0^3*v 1^2*v 2^3*v 3^3*w 2*w 3 + 24*v 0^3*v 1^2*v 2^2*v 3^4*w 3^2 - 72*v 0^2*v 1*v 2^8*w 0*w 1 - 36*v 0^2*v 1*v 2^8*w 0*w 2 - 36*v 0^2*v 1*v 2^8*w 0*w 3 + 72*v 0^2*v 1*v 2^8*w 1^2 + 108*v 0^2*v 1*v 2^8*w 1*w 2 + 36*v 0^2*v 1*v 2^8*w 1*w 3 + 36*v 0^2*v 1*v 2^8*w 2^2 + 36*v 0^2*v 1*v 2^8*w 2*w 3 - 72*v 0^2*v 1*v 2^7*v 3*w 0*w 1 - 36*v 0^2*v 1*v 2^7*v 3*w 0*w 2 - 36*v 0^2*v 1*v 2^7*v 3*w 0*w 3 + 72*v 0^2*v 1*v 2^7*v 3*w 1^2 + 108*v 0^2*v 1*v 2^7*v 3*w 1*w 2 + 144*v 0^2*v 1*v 2^7*v 3*w 1*w 3 + 36*v 0^2*v 1*v 2^7*v 3*w 2^2 + 90*v 0^2*v 1*v 2^7*v 3*w 2*w 3 + 54*v 0^2*v 1*v 2^7*v 3*w 3^2 - 172*v 0^2*v 1*v 2^6*v 3^2*w 0*w 1 - 86*v 0^2*v 1*v 2^6*v 3^2*w 0*w 2 - 86*v 0^2*v 1*v 2^6*v 3^2*w 0*w 3 + 172*v 0^2*v 1*v 2^6*v 3^2*w 1^2 + 426*v 0^2*v 1*v 2^6*v 3^2*w 1*w 2 + 126*v 0^2*v 1*v 2^6*v 3^2*w 1*w 3 + 170*v 0^2*v 1*v 2^6*v 3^2*w 2^2 + 190*v 0^2*v 1*v 2^6*v 3^2*w 2*w 3 + 20*v 0^2*v 1*v 2^6*v 3^2*w 3^2 - 332*v 0^2*v 1*v 2^5*v 3^3*w 0*w 1 - 166*v 0^2*v 1*v 2^5*v 3^3*w 0*w 2 - 166*v 0^2*v 1*v 2^5*v 3^3*w 0*w 3 + 332*v 0^2*v 1*v 2^5*v 3^3*w 1^2 + 498*v 0^2*v 1*v 2^5*v 3^3*w 1*w 2 + 474*v 0^2*v 1*v 2^5*v 3^3*w 1*w 3 + 166*v 0^2*v 1*v 2^5*v 3^3*w 2^2 + 320*v 0^2*v 1*v 2^5*v 3^3*w 2*w 3 + 154*v 0^2*v 1*v 2^5*v 3^3*w 3^2 - 168*v 0^2*v 1*v 2^4*v 3^4*w 0*w 1 - 84*v 0^2*v 1*v 2^4*v 3^4*w 0*w 2 - 84*v 0^2*v 1*v 2^4*v 3^4*w 0*w 3 + 168*v 0^2*v 1*v 2^4*v 3^4*w 1^2 + 252*v 0^2*v 1*v 2^4*v 3^4*w 1*w 2 + 276*v 0^2*v 1*v 2^4*v 3^4*w 1*w 3 + 84*v 0^2*v 1*v 2^4*v 3^4*w 2^2 + 180*v 0^2*v 1*v 2^4*v 3^4*w 2*w 3 + 96*v 0^2*v 1*v 2^4*v 3^4*w 3^2 - 176*v 0^2*v 1*v 2^3*v 3^5*w 0*w 1 - 88*v 0^2*v 1*v 2^3*v 3^5*w 0*w 2 - 88*v 0^2*v 1*v 2^3*v 3^5*w 0*w 3 + 176*v 0^2*v 1*v 2^3*v 3^5*w 1^2 + 264*v 0^2*v 1*v 2^3*v 3^5*w 1*w 2 + 396*v 0^2*v 1*v 2^3*v 3^5*w 1*w 3 + 88*v 0^2*v 1*v 2^3*v 3^5*w 2^2 + 242*v 0^2*v 1*v 2^3*v 3^5*w 2*w 3 + 154*v 0^2*v 1*v 2^3*v 3^5*w 3^2 - 76*v 0^2*v 1*v 2^2*v 3^6*w 0*w 1 - 38*v 0^2*v 1*v 2^2*v 3^6*w 0*w 2 - 38*v 0^2*v 1*v 2^2*v 3^6*w 0*w 3 + 76*v 0^2*v 1*v 2^2*v 3^6*w 1^2 + 114*v 0^2*v 1*v 2^2*v 3^6*w 1*w 2 + 246*v 0^2*v 1*v 2^2*v 3^6*w 1*w 3 + 38*v 0^2*v 1*v 2^2*v 3^6*w 2^2 + 142*v 0^2*v 1*v 2^2*v 3^6*w 2*w 3 + 104*v 0^2*v 1*v 2^2*v 3^6*w 3^2 - 36*v 0^2*v 1*v 2*v 3^7*w 0*w 1 - 18*v 0^2*v 1*v 2*v 3^7*w 0*w 2 - 18*v 0^2*v 1*v 2*v 3^7*w 0*w 3 + 36*v 0^2*v 1*v 2*v 3^7*w 1^2 + 54*v 0^2*v 1*v 2*v 3^7*w 1*w 2 + 126*v 0^2*v 1*v 2*v 3^7*w 1*w 3 + 18*v 0^2*v 1*v 2*v 3^7*w 2^2 + 72*v 0^2*v 1*v 2*v 3^7*w 2*w 3 + 54*v 0^2*v 1*v 2*v 3^7*w 3^2 - 36*v 0^2*v 2^9*w 0*w 1 + 36*v 0^2*v 2^9*w 0*w 2 - 18*v 0^2*v 2^9*w 0*w 3 + 36*v 0^2*v 2^9*w 1^2 + 18*v 0^2*v 2^9*w 1*w 3 - 36*v 0^2*v 2^9*w 2^2 + 18*v 0^2*v 2^9*w 2*w 3 - 72*v 0^2*v 2^8*v 3*w 0*w 1 - 36*v 0^2*v 2^8*v 3*w 0*w 2 - 90*v 0^2*v 2^8*v 3*w 0*w 3 + 72*v 0^2*v 2^8*v 3*w 1^2 + 108*v 0^2*v 2^8*v 3*w 1*w 2 + 144*v 0^2*v 2^8*v 3*w 1*w 3 + 144*v 0^2*v 2^8*v 3*w 2^2 + 252*v 0^2*v 2^8*v 3*w 2*w 3 + 108*v 0^2*v 2^8*v 3*w 3^2 - 122*v 0^2*v 2^7*v 3^2*w 0*w 1 + 224*v 0^2*v 2^7*v 3^2*w 0*w 2 - 26*v 0^2*v 2^7*v 3^2*w 0*w 3 + 122*v 0^2*v 2^7*v 3^2*w 1^2 - 18*v 0^2*v 2^7*v 3^2*w 1*w 2 + 100*v 0^2*v 2^7*v 3^2*w 1*w 3 - 20*v 0^2*v 2^7*v 3^2*w 2^2 + 180*v 0^2*v 2^7*v 3^2*w 2*w 3 + 44*v 0^2*v 2^7*v 3^2*w 3^2 - 252*v 0^2*v 2^6*v 3^3*w 0*w 1 + 224*v 0^2*v 2^6*v 3^3*w 0*w 2 - 56*v 0^2*v 2^6*v 3^3*w 0*w 3 + 252*v 0^2*v 2^6*v 3^3*w 1^2 + 112*v 0^2*v 2^6*v 3^3*w 1*w 2 + 230*v 0^2*v 2^6*v 3^3*w 1*w 3 + 280*v 0^2*v 2^6*v 3^3*w 2^2 + 636*v 0^2*v 2^6*v 3^3*w 2*w 3 + 374*v 0^2*v 2^6*v 3^3*w 3^2 - 250*v 0^2*v 2^5*v 3^4*w 0*w 1 + 338*v 0^2*v 2^5*v 3^4*w 0*w 2 + 256*v 0^2*v 2^5*v 3^4*w 0*w 3 + 250*v 0^2*v 2^5*v 3^4*w 1^2 - 88*v 0^2*v 2^5*v 3^4*w 1*w 2 - 6*v 0^2*v 2^5*v 3^4*w 1*w 3 + 220*v 0^2*v 2^5*v 3^4*w 2^2 + 450*v 0^2*v 2^5*v 3^4*w 2*w 3 + 206*v 0^2*v 2^5*v 3^4*w 3^2 - 172*v 0^2*v 2^4*v 3^5*w 0*w 1 + 202*v 0^2*v 2^4*v 3^5*w 0*w 2 + 362*v 0^2*v 2^4*v 3^5*w 0*w 3 + 172*v 0^2*v 2^4*v 3^5*w 1^2 - 30*v 0^2*v 2^4*v 3^5*w 1*w 2 - 112*v 0^2*v 2^4*v 3^5*w 1*w 3 + 248*v 0^2*v 2^4*v 3^5*w 2^2 + 402*v 0^2*v 2^4*v 3^5*w 2*w 3 + 184*v 0^2*v 2^4*v 3^5*w 3^2 - 126*v 0^2*v 2^3*v 3^6*w 0*w 1 + 28*v 0^2*v 2^3*v 3^6*w 0*w 2 + 278*v 0^2*v 2^3*v 3^6*w 0*w 3 + 126*v 0^2*v 2^3*v 3^6*w 1^2 + 98*v 0^2*v 2^3*v 3^6*w 1*w 2 - 20*v 0^2*v 2^3*v 3^6*w 1*w 3 + 224*v 0^2*v 2^3*v 3^6*w 2^2 + 372*v 0^2*v 2^3*v 3^6*w 2*w 3 + 160*v 0^2*v 2^3*v 3^6*w 3^2 - 56*v 0^2*v 2^2*v 3^7*w 0*w 1 - 80*v 0^2*v 2^2*v 3^7*w 0*w 2 + 140*v 0^2*v 2^2*v 3^7*w 0*w 3 + 56*v 0^2*v 2^2*v 3^7*w 1^2 + 136*v 0^2*v 2^2*v 3^7*w 1*w 2 + 18*v 0^2*v 2^2*v 3^7*w 1*w 3 + 116*v 0^2*v 2^2*v 3^7*w 2^2 + 252*v 0^2*v 2^2*v 3^7*w 2*w 3 + 82*v 0^2*v 2^2*v 3^7*w 3^2 - 18*v 0^2*v 2*v 3^8*w 0*w 1 - 54*v 0^2*v 2*v 3^8*w 0*w 2 + 18*v 0^2*v 2*v 3^8*w 0*w 3 + 18*v 0^2*v 2*v 3^8*w 1^2 + 72*v 0^2*v 2*v 3^8*w 1*w 2 + 36*v 0^2*v 2*v 3^8*w 1*w 3 + 36*v 0^2*v 2*v 3^8*w 2^2 + 108*v 0^2*v 2*v 3^8*w 2*w 3 + 54*v 0^2*v 2*v 3^8*w 3^2 - 18*v 0^2*v 3^9*w 0*w 2 + 18*v 0^2*v 3^9*w 1*w 2 + 18*v 0^2*v 3^9*w 2*w 3 + 72*v 0*v 1^2*v 2^8*w 1^2 + 36*v 0*v 1^2*v 2^8*w 1*w 2 + 36*v 0*v 1^2*v 2^8*w 1*w 3 + 72*v 0*v 1^2*v 2^7*v 3*w 1^2 + 36*v 0*v 1^2*v 2^7*v 3*w 1*w 2 + 36*v 0*v 1^2*v 2^7*v 3*w 1*w 3 + 172*v 0*v 1^2*v 2^6*v 3^2*w 1^2 + 86*v 0*v 1^2*v 2^6*v 3^2*w 1*w 2 + 86*v 0*v 1^2*v 2^6*v 3^2*w 1*w 3 + 332*v 0*v 1^2*v 2^5*v 3^3*w 1^2 + 166*v 0*v 1^2*v 2^5*v 3^3*w 1*w 2 + 166*v 0*v 1^2*v 2^5*v 3^3*w 1*w 3 + 168*v 0*v 1^2*v 2^4*v 3^4*w 1^2 + 84*v 0*v 1^2*v 2^4*v 3^4*w 1*w 2 + 84*v 0*v 1^2*v 2^4*v 3^4*w 1*w 3 + 176*v 0*v 1^2*v 2^3*v 3^5*w 1^2 + 88*v 0*v 1^2*v 2^3*v 3^5*w 1*w 2 + 88*v 0*v 1^2*v 2^3*v 3^5*w 1*w 3 + 76*v 0*v 1^2*v 2^2*v 3^6*w 1^2 + 38*v 0*v 1^2*v 2^2*v 3^6*w 1*w 2 + 38*v 0*v 1^2*v 2^2*v 3^6*w 1*w 3 + 36*v 0*v 1^2*v 2*v 3^7*w 1^2 + 18*v 0*v 1^2*v 2*v 3^7*w 1*w 2 + 18*v 0*v 1^2*v 2*v 3^7*w 1*w 3 + 36*v 0*v 1*v 2^9*w 1^2 + 36*v 0*v 1*v 2^9*w 1*w 2 + 18*v 0*v 1*v 2^9*w 1*w 3 + 36*v 0*v 1*v 2^9*w 2^2 + 36*v 0*v 1*v 2^9*w 2*w 3 + 72*v 0*v 1*v 2^8*v 3*w 1^2 + 108*v 0*v 1*v 2^8*v 3*w 1*w 2 + 162*v 0*v 1*v 2^8*v 3*w 1*w 3 + 36*v 0*v 1*v 2^8*v 3*w 2^2 + 72*v 0*v 1*v 2^8*v 3*w 2*w 3 + 36*v 0*v 1*v 2^8*v 3*w 3^2 + 122*v 0*v 1*v 2^7*v 3^2*w 1^2 - 52*v 0*v 1*v 2^7*v 3^2*w 1*w 2 + 98*v 0*v 1*v 2^7*v 3^2*w 1*w 3 + 86*v 0*v 1*v 2^7*v 3^2*w 2^2 + 122*v 0*v 1*v 2^7*v 3^2*w 2*w 3 + 36*v 0*v 1*v 2^7*v 3^2*w 3^2 + 252*v 0*v 1*v 2^6*v 3^3*w 1^2 + 108*v 0*v 1*v 2^6*v 3^3*w 1*w 2 + 228*v 0*v 1*v 2^6*v 3^3*w 1*w 3 + 166*v 0*v 1*v 2^6*v 3^3*w 2^2 + 252*v 0*v 1*v 2^6*v 3^3*w 2*w 3 + 86*v 0*v 1*v 2^6*v 3^3*w 3^2 + 250*v 0*v 1*v 2^5*v 3^4*w 1^2 - 170*v 0*v 1*v 2^5*v 3^4*w 1*w 2 + 76*v 0*v 1*v 2^5*v 3^4*w 1*w 3 + 84*v 0*v 1*v 2^5*v 3^4*w 2^2 + 250*v 0*v 1*v 2^5*v 3^4*w 2*w 3 + 166*v 0*v 1*v 2^5*v 3^4*w 3^2 + 172*v 0*v 1*v 2^4*v 3^5*w 1^2 - 26*v 0*v 1*v 2^4*v 3^5*w 1*w 2 - 194*v 0*v 1*v 2^4*v 3^5*w 1*w 3 + 88*v 0*v 1*v 2^4*v 3^5*w 2^2 + 172*v 0*v 1*v 2^4*v 3^5*w 2*w 3 + 84*v 0*v 1*v 2^4*v 3^5*w 3^2 + 126*v 0*v 1*v 2^3*v 3^6*w 1^2 + 48*v 0*v 1*v 2^3*v 3^6*w 1*w 2 - 102*v 0*v 1*v 2^3*v 3^6*w 1*w 3 + 38*v 0*v 1*v 2^3*v 3^6*w 2^2 + 126*v 0*v 1*v 2^3*v 3^6*w 2*w 3 + 88*v 0*v 1*v 2^3*v 3^6*w 3^2 + 56*v 0*v 1*v 2^2*v 3^7*w 1^2 + 116*v 0*v 1*v 2^2*v 3^7*w 1*w 2 - 64*v 0*v 1*v 2^2*v 3^7*w 1*w 3 + 18*v 0*v 1*v 2^2*v 3^7*w 2^2 + 56*v 0*v 1*v 2^2*v 3^7*w 2*w 3 + 38*v 0*v 1*v 2^2*v 3^7*w 3^2 + 18*v 0*v 1*v 2*v 3^8*w 1^2 + 54*v 0*v 1*v 2*v 3^8*w 1*w 2 + 18*v 0*v 1*v 2*v 3^8*w 1*w 3 + 18*v 0*v 1*v 2*v 3^8*w 2*w 3 + 18*v 0*v 1*v 2*v 3^8*w 3^2 + 18*v 0*v 1*v 3^9*w 1*w 2 + 36*v 0*v 2^10*w 1*w 2 - 36*v 0*v 2^10*w 2^2 + 18*v 0*v 2^10*w 2*w 3 + 72*v 0*v 2^9*v 3*w 1*w 2 + 36*v 0*v 2^9*v 3*w 1*w 3 + 36*v 0*v 2^9*v 3*w 2^2 + 54*v 0*v 2^9*v 3*w 2*w 3 + 18*v 0*v 2^9*v 3*w 3^2 + 122*v 0*v 2^8*v 3^2*w 1*w 2 + 72*v 0*v 2^8*v 3^2*w 1*w 3 - 224*v 0*v 2^8*v 3^2*w 2^2 + 62*v 0*v 2^8*v 3^2*w 2*w 3 + 90*v 0*v 2^8*v 3^2*w 3^2 + 252*v 0*v 2^7*v 3^3*w 1*w 2 + 122*v 0*v 2^7*v 3^3*w 1*w 3 - 224*v 0*v 2^7*v 3^3*w 2^2 - 168*v 0*v 2^7*v 3^3*w 2*w 3 + 26*v 0*v 2^7*v 3^3*w 3^2 + 250*v 0*v 2^6*v 3^4*w 1*w 2 + 252*v 0*v 2^6*v 3^4*w 1*w 3 - 338*v 0*v 2^6*v 3^4*w 2^2 - 480*v 0*v 2^6*v 3^4*w 2*w 3 + 56*v 0*v 2^6*v 3^4*w 3^2 + 172*v 0*v 2^5*v 3^5*w 1*w 2 + 250*v 0*v 2^5*v 3^5*w 1*w 3 - 202*v 0*v 2^5*v 3^5*w 2^2 - 700*v 0*v 2^5*v 3^5*w 2*w 3 - 256*v 0*v 2^5*v 3^5*w 3^2 + 126*v 0*v 2^4*v 3^6*w 1*w 2 + 172*v 0*v 2^4*v 3^6*w 1*w 3 - 28*v 0*v 2^4*v 3^6*w 2^2 - 480*v 0*v 2^4*v 3^6*w 2*w 3 - 362*v 0*v 2^4*v 3^6*w 3^2 + 56*v 0*v 2^3*v 3^7*w 1*w 2 + 126*v 0*v 2^3*v 3^7*w 1*w 3 + 80*v 0*v 2^3*v 3^7*w 2^2 - 168*v 0*v 2^3*v 3^7*w 2*w 3 - 278*v 0*v 2^3*v 3^7*w 3^2 + 18*v 0*v 2^2*v 3^8*w 1*w 2 + 56*v 0*v 2^2*v 3^8*w 1*w 3 + 54*v 0*v 2^2*v 3^8*w 2^2 + 62*v 0*v 2^2*v 3^8*w 2*w 3 - 140*v 0*v 2^2*v 3^8*w 3^2 + 18*v 0*v 2*v 3^9*w 1*w 3 + 18*v 0*v 2*v 3^9*w 2^2 + 54*v 0*v 2*v 3^9*w 2*w 3 - 18*v 0*v 2*v 3^9*w 3^2 + 18*v 0*v 3^10*w 2*w 3 - 32*v 1^7*v 2^2*v 3^2*w 0*w 1 - 16*v 1^7*v 2^2*v 3^2*w 0*w 2 - 16*v 1^7*v 2^2*v 3^2*w 0*w 3 + 32*v 1^7*v 2^2*v 3^2*w 1^2 + 48*v 1^7*v 2^2*v 3^2*w 1*w 2 + 48*v 1^7*v 2^2*v 3^2*w 1*w 3 + 16*v 1^7*v 2^2*v 3^2*w 2^2 + 32*v 1^7*v 2^2*v 3^2*w 2*w 3 + 16*v 1^7*v 2^2*v 3^2*w 3^2 - 240*v 1^6*v 2^3*v 3^2*w 0*w 2 - 192*v 1^6*v 2^3*v 3^2*w 0*w 3 + 240*v 1^6*v 2^3*v 3^2*w 1*w 2 + 192*v 1^6*v 2^3*v 3^2*w 1*w 3 + 240*v 1^6*v 2^3*v 3^2*w 2^2 + 432*v 1^6*v 2^3*v 3^2*w 2*w 3 + 192*v 1^6*v 2^3*v 3^2*w 3^2 - 112*v 1^6*v 2^2*v 3^3*w 0*w 1 - 80*v 1^6*v 2^2*v 3^3*w 0*w 2 - 128*v 1^6*v 2^2*v 3^3*w 0*w 3 + 112*v 1^6*v 2^2*v 3^3*w 1^2 + 192*v 1^6*v 2^2*v 3^3*w 1*w 2 + 240*v 1^6*v 2^2*v 3^3*w 1*w 3 + 80*v 1^6*v 2^2*v 3^3*w 2^2 + 208*v 1^6*v 2^2*v 3^3*w 2*w 3 + 128*v 1^6*v 2^2*v 3^3*w 3^2 - 40*v 1^5*v 2^4*v 3^2*w 0*w 1 - 404*v 1^5*v 2^4*v 3^2*w 0*w 2 - 260*v 1^5*v 2^4*v 3^2*w 0*w 3 + 40*v 1^5*v 2^4*v 3^2*w 1^2 + 444*v 1^5*v 2^4*v 3^2*w 1*w 2 + 300*v 1^5*v 2^4*v 3^2*w 1*w 3 + 404*v 1^5*v 2^4*v 3^2*w 2^2 + 664*v 1^5*v 2^4*v 3^2*w 2*w 3 + 260*v 1^5*v 2^4*v 3^2*w 3^2 - 192*v 1^5*v 2^3*v 3^3*w 0*w 1 - 552*v 1^5*v 2^3*v 3^3*w 0*w 2 - 552*v 1^5*v 2^3*v 3^3*w 0*w 3 + 192*v 1^5*v 2^3*v 3^3*w 1^2 + 744*v 1^5*v 2^3*v 3^3*w 1*w 2 + 744*v 1^5*v 2^3*v 3^3*w 1*w 3 + 552*v 1^5*v 2^3*v 3^3*w 2^2 + 1104*v 1^5*v 2^3*v 3^3*w 2*w 3 + 552*v 1^5*v 2^3*v 3^3*w 3^2 - 152*v 1^5*v 2^2*v 3^4*w 0*w 1 - 148*v 1^5*v 2^2*v 3^4*w 0*w 2 - 292*v 1^5*v 2^2*v 3^4*w 0*w 3 + 152*v 1^5*v 2^2*v 3^4*w 1^2 + 300*v 1^5*v 2^2*v 3^4*w 1*w 2 + 444*v 1^5*v 2^2*v 3^4*w 1*w 3 + 148*v 1^5*v 2^2*v 3^4*w 2^2 + 440*v 1^5*v 2^2*v 3^4*w 2*w 3 + 292*v 1^5*v 2^2*v 3^4*w 3^2 + 12*v 1^4*v 2^5*v 3^2*w 0*w 1 - 396*v 1^4*v 2^5*v 3^2*w 0*w 2 - 240*v 1^4*v 2^5*v 3^2*w 0*w 3 - 12*v 1^4*v 2^5*v 3^2*w 1^2 + 384*v 1^4*v 2^5*v 3^2*w 1*w 2 + 228*v 1^4*v 2^5*v 3^2*w 1*w 3 + 396*v 1^4*v 2^5*v 3^2*w 2^2 + 636*v 1^4*v 2^5*v 3^2*w 2*w 3 + 240*v 1^4*v 2^5*v 3^2*w 3^2 - 188*v 1^4*v 2^4*v 3^3*w 0*w 1 - 808*v 1^4*v 2^4*v 3^3*w 0*w 2 - 652*v 1^4*v 2^4*v 3^3*w 0*w 3 + 188*v 1^4*v 2^4*v 3^3*w 1^2 + 996*v 1^4*v 2^4*v 3^3*w 1*w 2 + 840*v 1^4*v 2^4*v 3^3*w 1*w 3 + 808*v 1^4*v 2^4*v 3^3*w 2^2 + 1460*v 1^4*v 2^4*v 3^3*w 2*w 3 + 652*v 1^4*v 2^4*v 3^3*w 3^2 - 188*v 1^4*v 2^3*v 3^4*w 0*w 1 - 652*v 1^4*v 2^3*v 3^4*w 0*w 2 - 808*v 1^4*v 2^3*v 3^4*w 0*w 3 + 188*v 1^4*v 2^3*v 3^4*w 1^2 + 840*v 1^4*v 2^3*v 3^4*w 1*w 2 + 996*v 1^4*v 2^3*v 3^4*w 1*w 3 + 652*v 1^4*v 2^3*v 3^4*w 2^2 + 1460*v 1^4*v 2^3*v 3^4*w 2*w 3 + 808*v 1^4*v 2^3*v 3^4*w 3^2 - 100*v 1^4*v 2^2*v 3^5*w 0*w 1 - 128*v 1^4*v 2^2*v 3^5*w 0*w 2 - 284*v 1^4*v 2^2*v 3^5*w 0*w 3 + 100*v 1^4*v 2^2*v 3^5*w 1^2 + 228*v 1^4*v 2^2*v 3^5*w 1*w 2 + 384*v 1^4*v 2^2*v 3^5*w 1*w 3 + 128*v 1^4*v 2^2*v 3^5*w 2^2 + 412*v 1^4*v 2^2*v 3^5*w 2*w 3 + 284*v 1^4*v 2^2*v 3^5*w 3^2 + 36*v 1^3*v 2^8*w 0*w 1 + 18*v 1^3*v 2^8*w 0*w 2 + 18*v 1^3*v 2^8*w 0*w 3 - 36*v 1^3*v 2^8*w 1^2 - 54*v 1^3*v 2^8*w 1*w 2 - 54*v 1^3*v 2^8*w 1*w 3 - 18*v 1^3*v 2^8*w 2^2 - 36*v 1^3*v 2^8*w 2*w 3 - 18*v 1^3*v 2^8*w 3^2 + 36*v 1^3*v 2^7*v 3*w 0*w 1 + 18*v 1^3*v 2^7*v 3*w 0*w 2 + 18*v 1^3*v 2^7*v 3*w 0*w 3 - 36*v 1^3*v 2^7*v 3*w 1^2 - 54*v 1^3*v 2^7*v 3*w 1*w 2 - 54*v 1^3*v 2^7*v 3*w 1*w 3 - 18*v 1^3*v 2^7*v 3*w 2^2 - 36*v 1^3*v 2^7*v 3*w 2*w 3 - 18*v 1^3*v 2^7*v 3*w 3^2 + 54*v 1^3*v 2^6*v 3^2*w 0*w 1 - 81*v 1^3*v 2^6*v 3^2*w 0*w 2 - 9*v 1^3*v 2^6*v 3^2*w 0*w 3 - 54*v 1^3*v 2^6*v 3^2*w 1^2 + 27*v 1^3*v 2^6*v 3^2*w 1*w 2 - 45*v 1^3*v 2^6*v 3^2*w 1*w 3 + 81*v 1^3*v 2^6*v 3^2*w 2^2 + 90*v 1^3*v 2^6*v 3^2*w 2*w 3 + 9*v 1^3*v 2^6*v 3^2*w 3^2 + 38*v 1^3*v 2^5*v 3^3*w 0*w 1 - 341*v 1^3*v 2^5*v 3^3*w 0*w 2 - 197*v 1^3*v 2^5*v 3^3*w 0*w 3 - 38*v 1^3*v 2^5*v 3^3*w 1^2 + 303*v 1^3*v 2^5*v 3^3*w 1*w 2 + 159*v 1^3*v 2^5*v 3^3*w 1*w 3 + 341*v 1^3*v 2^5*v 3^3*w 2^2 + 538*v 1^3*v 2^5*v 3^3*w 2*w 3 + 197*v 1^3*v 2^5*v 3^3*w 3^2 - 108*v 1^3*v 2^4*v 3^4*w 0*w 1 - 486*v 1^3*v 2^4*v 3^4*w 0*w 2 - 486*v 1^3*v 2^4*v 3^4*w 0*w 3 + 108*v 1^3*v 2^4*v 3^4*w 1^2 + 594*v 1^3*v 2^4*v 3^4*w 1*w 2 + 594*v 1^3*v 2^4*v 3^4*w 1*w 3 + 486*v 1^3*v 2^4*v 3^4*w 2^2 + 972*v 1^3*v 2^4*v 3^4*w 2*w 3 + 486*v 1^3*v 2^4*v 3^4*w 3^2 - 40*v 1^3*v 2^3*v 3^5*w 0*w 1 - 236*v 1^3*v 2^3*v 3^5*w 0*w 2 - 380*v 1^3*v 2^3*v 3^5*w 0*w 3 + 40*v 1^3*v 2^3*v 3^5*w 1^2 + 276*v 1^3*v 2^3*v 3^5*w 1*w 2 + 420*v 1^3*v 2^3*v 3^5*w 1*w 3 + 236*v 1^3*v 2^3*v 3^5*w 2^2 + 616*v 1^3*v 2^3*v 3^5*w 2*w 3 + 380*v 1^3*v 2^3*v 3^5*w 3^2 + 6*v 1^3*v 2^2*v 3^6*w 0*w 1 - 33*v 1^3*v 2^2*v 3^6*w 0*w 2 - 105*v 1^3*v 2^2*v 3^6*w 0*w 3 - 6*v 1^3*v 2^2*v 3^6*w 1^2 + 27*v 1^3*v 2^2*v 3^6*w 1*w 2 + 99*v 1^3*v 2^2*v 3^6*w 1*w 3 + 33*v 1^3*v 2^2*v 3^6*w 2^2 + 138*v 1^3*v 2^2*v 3^6*w 2*w 3 + 105*v 1^3*v 2^2*v 3^6*w 3^2 + 18*v 1^3*v 2*v 3^7*w 0*w 1 + 9*v 1^3*v 2*v 3^7*w 0*w 2 + 9*v 1^3*v 2*v 3^7*w 0*w 3 - 18*v 1^3*v 2*v 3^7*w 1^2 - 27*v 1^3*v 2*v 3^7*w 1*w 2 - 27*v 1^3*v 2*v 3^7*w 1*w 3 - 9*v 1^3*v 2*v 3^7*w 2^2 - 18*v 1^3*v 2*v 3^7*w 2*w 3 - 9*v 1^3*v 2*v 3^7*w 3^2 + 54*v 1^2*v 2^9*w 0*w 1 + 27*v 1^2*v 2^9*w 0*w 3 - 54*v 1^2*v 2^9*w 1^2 - 54*v 1^2*v 2^9*w 1*w 2 - 81*v 1^2*v 2^9*w 1*w 3 - 27*v 1^2*v 2^9*w 2*w 3 - 27*v 1^2*v 2^9*w 3^2 + 108*v 1^2*v 2^8*v 3*w 0*w 1 + 126*v 1^2*v 2^8*v 3*w 0*w 2 + 117*v 1^2*v 2^8*v 3*w 0*w 3 - 108*v 1^2*v 2^8*v 3*w 1^2 - 234*v 1^2*v 2^8*v 3*w 1*w 2 - 225*v 1^2*v 2^8*v 3*w 1*w 3 - 126*v 1^2*v 2^8*v 3*w 2^2 - 243*v 1^2*v 2^8*v 3*w 2*w 3 - 117*v 1^2*v 2^8*v 3*w 3^2 + 179*v 1^2*v 2^7*v 3^2*w 0*w 1 + 169*v 1^2*v 2^7*v 3^2*w 0*w 2 + 142*v 1^2*v 2^7*v 3^2*w 0*w 3 - 179*v 1^2*v 2^7*v 3^2*w 1^2 - 348*v 1^2*v 2^7*v 3^2*w 1*w 2 - 321*v 1^2*v 2^7*v 3^2*w 1*w 3 - 169*v 1^2*v 2^7*v 3^2*w 2^2 - 311*v 1^2*v 2^7*v 3^2*w 2*w 3 - 142*v 1^2*v 2^7*v 3^2*w 3^2 + 358*v 1^2*v 2^6*v 3^3*w 0*w 1 + 266*v 1^2*v 2^6*v 3^3*w 0*w 2 + 278*v 1^2*v 2^6*v 3^3*w 0*w 3 - 358*v 1^2*v 2^6*v 3^3*w 1^2 - 624*v 1^2*v 2^6*v 3^3*w 1*w 2 - 636*v 1^2*v 2^6*v 3^3*w 1*w 3 - 266*v 1^2*v 2^6*v 3^3*w 2^2 - 544*v 1^2*v 2^6*v 3^3*w 2*w 3 - 278*v 1^2*v 2^6*v 3^3*w 3^2 + 335*v 1^2*v 2^5*v 3^4*w 0*w 1 + 136*v 1^2*v 2^5*v 3^4*w 0*w 2 + 37*v 1^2*v 2^5*v 3^4*w 0*w 3 - 335*v 1^2*v 2^5*v 3^4*w 1^2 - 471*v 1^2*v 2^5*v 3^4*w 1*w 2 - 372*v 1^2*v 2^5*v 3^4*w 1*w 3 - 136*v 1^2*v 2^5*v 3^4*w 2^2 - 173*v 1^2*v 2^5*v 3^4*w 2*w 3 - 37*v 1^2*v 2^5*v 3^4*w 3^2 + 218*v 1^2*v 2^4*v 3^5*w 0*w 1 + 25*v 1^2*v 2^4*v 3^5*w 0*w 2 + 85*v 1^2*v 2^4*v 3^5*w 0*w 3 - 218*v 1^2*v 2^4*v 3^5*w 1^2 - 243*v 1^2*v 2^4*v 3^5*w 1*w 2 - 303*v 1^2*v 2^4*v 3^5*w 1*w 3 - 25*v 1^2*v 2^4*v 3^5*w 2^2 - 110*v 1^2*v 2^4*v 3^5*w 2*w 3 - 85*v 1^2*v 2^4*v 3^5*w 3^2 + 169*v 1^2*v 2^3*v 3^6*w 0*w 1 + 173*v 1^2*v 2^3*v 3^6*w 0*w 2 + 176*v 1^2*v 2^3*v 3^6*w 0*w 3 - 169*v 1^2*v 2^3*v 3^6*w 1^2 - 342*v 1^2*v 2^3*v 3^6*w 1*w 2 - 345*v 1^2*v 2^3*v 3^6*w 1*w 3 - 173*v 1^2*v 2^3*v 3^6*w 2^2 - 349*v 1^2*v 2^3*v 3^6*w 2*w 3 - 176*v 1^2*v 2^3*v 3^6*w 3^2 + 80*v 1^2*v 2^2*v 3^7*w 0*w 1 + 136*v 1^2*v 2^2*v 3^7*w 0*w 2 + 178*v 1^2*v 2^2*v 3^7*w 0*w 3 - 80*v 1^2*v 2^2*v 3^7*w 1^2 - 216*v 1^2*v 2^2*v 3^7*w 1*w 2 - 258*v 1^2*v 2^2*v 3^7*w 1*w 3 - 136*v 1^2*v 2^2*v 3^7*w 2^2 - 314*v 1^2*v 2^2*v 3^7*w 2*w 3 - 178*v 1^2*v 2^2*v 3^7*w 3^2 + 27*v 1^2*v 2*v 3^8*w 0*w 1 + 72*v 1^2*v 2*v 3^8*w 0*w 2 + 72*v 1^2*v 2*v 3^8*w 0*w 3 - 27*v 1^2*v 2*v 3^8*w 1^2 - 99*v 1^2*v 2*v 3^8*w 1*w 2 - 99*v 1^2*v 2*v 3^8*w 1*w 3 - 72*v 1^2*v 2*v 3^8*w 2^2 - 144*v 1^2*v 2*v 3^8*w 2*w 3 - 72*v 1^2*v 2*v 3^8*w 3^2 + 9*v 1^2*v 3^9*w 0*w 2 - 9*v 1^2*v 3^9*w 1*w 2 - 9*v 1^2*v 3^9*w 2^2 - 9*v 1^2*v 3^9*w 2*w 3 + 54*v 1*v 2^10*w 0*w 1 + 27*v 1*v 2^10*w 0*w 3 - 54*v 1*v 2^10*w 1^2 - 54*v 1*v 2^10*w 1*w 2 - 81*v 1*v 2^10*w 1*w 3 - 27*v 1*v 2^10*w 2*w 3 - 27*v 1*v 2^10*w 3^2 + 162*v 1*v 2^9*v 3*w 0*w 1 + 126*v 1*v 2^9*v 3*w 0*w 2 + 144*v 1*v 2^9*v 3*w 0*w 3 - 162*v 1*v 2^9*v 3*w 1^2 - 288*v 1*v 2^9*v 3*w 1*w 2 - 306*v 1*v 2^9*v 3*w 1*w 3 - 126*v 1*v 2^9*v 3*w 2^2 - 270*v 1*v 2^9*v 3*w 2*w 3 - 144*v 1*v 2^9*v 3*w 3^2 + 291*v 1*v 2^8*v 3^2*w 0*w 1 + 315*v 1*v 2^8*v 3^2*w 0*w 2 + 267*v 1*v 2^8*v 3^2*w 0*w 3 - 291*v 1*v 2^8*v 3^2*w 1^2 - 606*v 1*v 2^8*v 3^2*w 1*w 2 - 558*v 1*v 2^8*v 3^2*w 1*w 3 - 315*v 1*v 2^8*v 3^2*w 2^2 - 582*v 1*v 2^8*v 3^2*w 2*w 3 - 267*v 1*v 2^8*v 3^2*w 3^2 + 561*v 1*v 2^7*v 3^3*w 0*w 1 + 543*v 1*v 2^7*v 3^3*w 0*w 2 + 480*v 1*v 2^7*v 3^3*w 0*w 3 - 561*v 1*v 2^7*v 3^3*w 1^2 - 1104*v 1*v 2^7*v 3^3*w 1*w 2 - 1041*v 1*v 2^7*v 3^3*w 1*w 3 - 543*v 1*v 2^7*v 3^3*w 2^2 - 1023*v 1*v 2^7*v 3^3*w 2*w 3 - 480*v 1*v 2^7*v 3^3*w 3^2 + 753*v 1*v 2^6*v 3^4*w 0*w 1 + 642*v 1*v 2^6*v 3^4*w 0*w 2 + 495*v 1*v 2^6*v 3^4*w 0*w 3 - 753*v 1*v 2^6*v 3^4*w 1^2 - 1395*v 1*v 2^6*v 3^4*w 1*w 2 - 1248*v 1*v 2^6*v 3^4*w 1*w 3 - 642*v 1*v 2^6*v 3^4*w 2^2 - 1137*v 1*v 2^6*v 3^4*w 2*w 3 - 495*v 1*v 2^6*v 3^4*w 3^2 + 633*v 1*v 2^5*v 3^5*w 0*w 1 + 441*v 1*v 2^5*v 3^5*w 0*w 2 + 402*v 1*v 2^5*v 3^5*w 0*w 3 - 633*v 1*v 2^5*v 3^5*w 1^2 - 1074*v 1*v 2^5*v 3^5*w 1*w 2 - 1035*v 1*v 2^5*v 3^5*w 1*w 3 - 441*v 1*v 2^5*v 3^5*w 2^2 - 843*v 1*v 2^5*v 3^5*w 2*w 3 - 402*v 1*v 2^5*v 3^5*w 3^2 + 447*v 1*v 2^4*v 3^6*w 0*w 1 + 378*v 1*v 2^4*v 3^6*w 0*w 2 + 501*v 1*v 2^4*v 3^6*w 0*w 3 - 447*v 1*v 2^4*v 3^6*w 1^2 - 825*v 1*v 2^4*v 3^6*w 1*w 2 - 948*v 1*v 2^4*v 3^6*w 1*w 3 - 378*v 1*v 2^4*v 3^6*w 2^2 - 879*v 1*v 2^4*v 3^6*w 2*w 3 - 501*v 1*v 2^4*v 3^6*w 3^2 + 273*v 1*v 2^3*v 3^7*w 0*w 1 + 369*v 1*v 2^3*v 3^7*w 0*w 2 + 462*v 1*v 2^3*v 3^7*w 0*w 3 - 273*v 1*v 2^3*v 3^7*w 1^2 - 642*v 1*v 2^3*v 3^7*w 1*w 2 - 735*v 1*v 2^3*v 3^7*w 1*w 3 - 369*v 1*v 2^3*v 3^7*w 2^2 - 831*v 1*v 2^3*v 3^7*w 2*w 3 - 462*v 1*v 2^3*v 3^7*w 3^2 + 111*v 1*v 2^2*v 3^8*w 0*w 1 + 216*v 1*v 2^2*v 3^8*w 0*w 2 + 270*v 1*v 2^2*v 3^8*w 0*w 3 - 111*v 1*v 2^2*v 3^8*w 1^2 - 327*v 1*v 2^2*v 3^8*w 1*w 2 - 381*v 1*v 2^2*v 3^8*w 1*w 3 - 216*v 1*v 2^2*v 3^8*w 2^2 - 486*v 1*v 2^2*v 3^8*w 2*w 3 - 270*v 1*v 2^2*v 3^8*w 3^2 + 27*v 1*v 2*v 3^9*w 0*w 1 + 81*v 1*v 2*v 3^9*w 0*w 2 + 72*v 1*v 2*v 3^9*w 0*w 3 - 27*v 1*v 2*v 3^9*w 1^2 - 108*v 1*v 2*v 3^9*w 1*w 2 - 99*v 1*v 2*v 3^9*w 1*w 3 - 81*v 1*v 2*v 3^9*w 2^2 - 153*v 1*v 2*v 3^9*w 2*w 3 - 72*v 1*v 2*v 3^9*w 3^2 + 9*v 1*v 3^10*w 0*w 2 - 9*v 1*v 3^10*w 1*w 2 - 9*v 1*v 3^10*w 2^2 - 9*v 1*v 3^10*w 2*w 3 + 18*v 2^11*w 0*w 1 - 18*v 2^11*w 0*w 2 + 9*v 2^11*w 0*w 3 - 18*v 2^11*w 1^2 - 27*v 2^11*w 1*w 3 + 18*v 2^11*w 2^2 + 9*v 2^11*w 2*w 3 - 9*v 2^11*w 3^2 + 72*v 2^10*v 3*w 0*w 1 + 72*v 2^10*v 3*w 0*w 3 - 72*v 2^10*v 3*w 1^2 - 72*v 2^10*v 3*w 1*w 2 - 144*v 2^10*v 3*w 1*w 3 - 72*v 2^10*v 3*w 2*w 3 - 72*v 2^10*v 3*w 3^2 + 151*v 2^9*v 3^2*w 0*w 1 + 2*v 2^9*v 3^2*w 0*w 2 + 149*v 2^9*v 3^2*w 0*w 3 - 151*v 2^9*v 3^2*w 1^2 - 153*v 2^9*v 3^2*w 1*w 2 - 300*v 2^9*v 3^2*w 1*w 3 - 2*v 2^9*v 3^2*w 2^2 - 151*v 2^9*v 3^2*w 2*w 3 - 149*v 2^9*v 3^2*w 3^2 + 284*v 2^8*v 3^3*w 0*w 1 - 95*v 2^8*v 3^3*w 0*w 2 + 190*v 2^8*v 3^3*w 0*w 3 - 284*v 2^8*v 3^3*w 1^2 - 189*v 2^8*v 3^3*w 1*w 2 - 474*v 2^8*v 3^3*w 1*w 3 + 95*v 2^8*v 3^3*w 2^2 - 95*v 2^8*v 3^3*w 2*w 3 - 190*v 2^8*v 3^3*w 3^2 + 438*v 2^7*v 3^4*w 0*w 1 - 192*v 2^7*v 3^4*w 0*w 2 + 90*v 2^7*v 3^4*w 0*w 3 - 438*v 2^7*v 3^4*w 1^2 - 246*v 2^7*v 3^4*w 1*w 2 - 528*v 2^7*v 3^4*w 1*w 3 + 192*v 2^7*v 3^4*w 2^2 + 102*v 2^7*v 3^4*w 2*w 3 - 90*v 2^7*v 3^4*w 3^2 + 462*v 2^6*v 3^5*w 0*w 1 - 258*v 2^6*v 3^5*w 0*w 2 - 198*v 2^6*v 3^5*w 0*w 3 - 462*v 2^6*v 3^5*w 1^2 - 204*v 2^6*v 3^5*w 1*w 2 - 264*v 2^6*v 3^5*w 1*w 3 + 258*v 2^6*v 3^5*w 2^2 + 456*v 2^6*v 3^5*w 2*w 3 + 198*v 2^6*v 3^5*w 3^2 + 360*v 2^5*v 3^6*w 0*w 1 - 174*v 2^5*v 3^6*w 0*w 2 - 336*v 2^5*v 3^6*w 0*w 3 - 360*v 2^5*v 3^6*w 1^2 - 186*v 2^5*v 3^6*w 1*w 2 - 24*v 2^5*v 3^6*w 1*w 3 + 174*v 2^5*v 3^6*w 2^2 + 510*v 2^5*v 3^6*w 2*w 3 + 336*v 2^5*v 3^6*w 3^2 + 240*v 2^4*v 3^7*w 0*w 1 + 60*v 2^4*v 3^7*w 0*w 2 - 216*v 2^4*v 3^7*w 0*w 3 - 240*v 2^4*v 3^7*w 1^2 - 300*v 2^4*v 3^7*w 1*w 2 - 24*v 2^4*v 3^7*w 1*w 3 - 60*v 2^4*v 3^7*w 2^2 + 156*v 2^4*v 3^7*w 2*w 3 + 216*v 2^4*v 3^7*w 3^2 + 128*v 2^3*v 3^8*w 0*w 1 + 184*v 2^3*v 3^8*w 0*w 2 - 65*v 2^3*v 3^8*w 0*w 3 - 128*v 2^3*v 3^8*w 1^2 - 312*v 2^3*v 3^8*w 1*w 2 - 63*v 2^3*v 3^8*w 1*w 3 - 184*v 2^3*v 3^8*w 2^2 - 119*v 2^3*v 3^8*w 2*w 3 + 65*v 2^3*v 3^8*w 3^2 + 46*v 2^2*v 3^9*w 0*w 1 + 140*v 2^2*v 3^9*w 0*w 2 + 8*v 2^2*v 3^9*w 0*w 3 - 46*v 2^2*v 3^9*w 1^2 - 186*v 2^2*v 3^9*w 1*w 2 - 54*v 2^2*v 3^9*w 1*w 3 - 140*v 2^2*v 3^9*w 2^2 - 148*v 2^2*v 3^9*w 2*w 3 - 8*v 2^2*v 3^9*w 3^2 + 9*v 2*v 3^10*w 0*w 1 + 54*v 2*v 3^10*w 0*w 2 + 9*v 2*v 3^10*w 0*w 3 - 9*v 2*v 3^10*w 1^2 - 63*v 2*v 3^10*w 1*w 2 - 18*v 2*v 3^10*w 1*w 3 - 54*v 2*v 3^10*w 2^2 - 63*v 2*v 3^10*w 2*w 3 - 9*v 2*v 3^10*w 3^2 + 9*v 3^11*w 0*w 2 - 9*v 3^11*w 1*w 2 - 9*v 3^11*w 2^2 - 9*v 3^11*w 2*w 3) * h2 + (-24*v 1^5*v 2^2*v 3^2*w 1*w 2^2 - 16*v 1^5*v 2^2*v 3^2*w 1*w 2*w 3 - 24*v 1^5*v 2^2*v 3^2*w 1*w 3^2 - 12*v 1^5*v 2^2*v 3^2*w 2^3 - 20*v 1^5*v 2^2*v 3^2*w 2^2*w 3 - 20*v 1^5*v 2^2*v 3^2*w 2*w 3^2 - 12*v 1^5*v 2^2*v 3^2*w 3^3 + 112*v 1^4*v 2^3*v 3^2*w 1^3 - 60*v 1^4*v 2^3*v 3^2*w 1*w 2^2 - 152*v 1^4*v 2^3*v 3^2*w 1*w 2*w 3 - 60*v 1^4*v 2^3*v 3^2*w 1*w 3^2 - 196*v 1^4*v 2^3*v 3^2*w 2^3 - 328*v 1^4*v 2^3*v 3^2*w 2^2*w 3 - 340*v 1^4*v 2^3*v 3^2*w 2*w 3^2 - 160*v 1^4*v 2^3*v 3^2*w 3^3 - 60*v 1^4*v 2^2*v 3^3*w 1*w 2^2 - 40*v 1^4*v 2^2*v 3^3*w 1*w 2*w 3 - 60*v 1^4*v 2^2*v 3^3*w 1*w 3^2 - 48*v 1^4*v 2^2*v 3^3*w 2^3 - 116*v 1^4*v 2^2*v 3^3*w 2^2*w 3 - 104*v 1^4*v 2^2*v 3^3*w 2*w 3^2 - 84*v 1^4*v 2^2*v 3^3*w 3^3 + 24*v 1^3*v 2^4*v 3^2*w 1*w 2^2 + 16*v 1^3*v 2^4*v 3^2*w 1*w 2*w 3 - 24*v 1^3*v 2^4*v 3^2*w 1*w 3^2 - 96*v 1^3*v 2^4*v 3^2*w 2^3 - 88*v 1^3*v 2^4*v 3^2*w 2^2*w 3 - 136*v 1^3*v 2^4*v 3^2*w 2*w 3^2 - 48*v 1^3*v 2^4*v 3^2*w 3^3 - 48*v 1^3*v 2^3*v 3^3*w 1*w 2^2 + 64*v 1^3*v 2^3*v 3^3*w 1*w 2*w 3 - 48*v 1^3*v 2^3*v 3^3*w 1*w 3^2 - 168*v 1^3*v 2^3*v 3^3*w 2^3 - 232*v 1^3*v 2^3*v 3^3*w 2^2*w 3 - 232*v 1^3*v 2^3*v 3^3*w 2*w 3^2 - 168*v 1^3*v 2^3*v 3^3*w 3^3 - 24*v 1^3*v 2^2*v 3^4*w 1*w 2^2 + 16*v 1^3*v 2^2*v 3^4*w 1*w 2*w 3 + 24*v 1^3*v 2^2*v 3^4*w 1*w 3^2 - 48*v 1^3*v 2^2*v 3^4*w 2^3 - 136*v 1^3*v 2^2*v 3^4*w 2^2*w 3 - 88*v 1^3*v 2^2*v 3^4*w 2*w 3^2 - 96*v 1^3*v 2^2*v 3^4*w 3^3 + 96*v 1^2*v 2^5*v 3^2*w 1*w 2^2 + 64*v 1^2*v 2^5*v 3^2*w 1*w 2*w 3 + 24*v 1^2*v 2^5*v 3^2*w 1*w 3^2 + 48*v 1^2*v 2^5*v 3^2*w 2^3 + 80*v 1^2*v 2^5*v 3^2*w 2^2*w 3 + 32*v 1^2*v 2^5*v 3^2*w 2*w 3^2 + 8*v 1^2*v 2^5*v 3^2*w 3^3 + 144*v 1^2*v 2^4*v 3^3*w 1*w 2^2 + 240*v 1^2*v 2^4*v 3^3*w 1*w 2*w 3 + 72*v 1^2*v 2^4*v 3^3*w 1*w 3^2 + 144*v 1^2*v 2^4*v 3^3*w 2^2*w 3 + 72*v 1^2*v 2^4*v 3^3*w 2*w 3^2 + 72*v 1^2*v 2^3*v 3^4*w 1*w 2^2 + 240*v 1^2*v 2^3*v 3^4*w 1*w 2*w 3 + 144*v 1^2*v 2^3*v 3^4*w 1*w 3^2 + 72*v 1^2*v 2^3*v 3^4*w 2^2*w 3 + 144*v 1^2*v 2^3*v 3^4*w 2*w 3^2 + 24*v 1^2*v 2^2*v 3^5*w 1*w 2^2 + 64*v 1^2*v 2^2*v 3^5*w 1*w 2*w 3 + 96*v 1^2*v 2^2*v 3^5*w 1*w 3^2 + 8*v 1^2*v 2^2*v 3^5*w 2^3 + 32*v 1^2*v 2^2*v 3^5*w 2^2*w 3 + 80*v 1^2*v 2^2*v 3^5*w 2*w 3^2 + 48*v 1^2*v 2^2*v 3^5*w 3^3 + 36*v 1*v 2^8*w 1*w 3^2 + 18*v 1*v 2^8*w 2*w 3^2 + 18*v 1*v 2^8*w 3^3 - 54*v 1*v 2^7*v 3*w 1*w 2*w 3 - 18*v 1*v 2^7*v 3*w 1*w 3^2 - 27*v 1*v 2^7*v 3*w 2^2*w 3 - 36*v 1*v 2^7*v 3*w 2*w 3^2 - 9*v 1*v 2^7*v 3*w 3^3 - 120*v 1*v 2^6*v 3^2*w 1*w 2^2 - 128*v 1*v 2^6*v 3^2*w 1*w 2*w 3 + 54*v 1*v 2^6*v 3^2*w 1*w 3^2 - 6*v 1*v 2^6*v 3^2*w 2^3 - 70*v 1*v 2^6*v 3^2*w 2^2*w 3 + 17*v 1*v 2^6*v 3^2*w 2*w 3^2 + 41*v 1*v 2^6*v 3^2*w 3^3 - 24*v 1*v 2^5*v 3^3*w 1*w 2^2 - 218*v 1*v 2^5*v 3^3*w 1*w 2*w 3 - 12*v 1*v 2^5*v 3^3*w 1*w 3^2 + 96*v 1*v 2^5*v 3^3*w 2^3 + 59*v 1*v 2^5*v 3^3*w 2^2*w 3 + 41*v 1*v 2^5*v 3^3*w 2*w 3^2 + 62*v 1*v 2^5*v 3^3*w 3^3 - 48*v 1*v 2^4*v 3^4*w 1*w 2^2 - 144*v 1*v 2^4*v 3^4*w 1*w 2*w 3 - 60*v 1*v 2^4*v 3^4*w 1*w 3^2 + 84*v 1*v 2^4*v 3^4*w 2^3 + 132*v 1*v 2^4*v 3^4*w 2^2*w 3 + 126*v 1*v 2^4*v 3^4*w 2*w 3^2 + 78*v 1*v 2^4*v 3^4*w 3^3 - 24*v 1*v 2^3*v 3^5*w 1*w 2^2 - 218*v 1*v 2^3*v 3^5*w 1*w 2*w 3 - 90*v 1*v 2^3*v 3^5*w 1*w 3^2 + 56*v 1*v 2^3*v 3^5*w 2^3 + 35*v 1*v 2^3*v 3^5*w 2^2*w 3 + 26*v 1*v 2^3*v 3^5*w 2*w 3^2 + 63*v 1*v 2^3*v 3^5*w 3^3 - 12*v 1*v 2^2*v 3^6*w 1*w 2^2 - 128*v 1*v 2^2*v 3^6*w 1*w 2*w 3 - 102*v 1*v 2^2*v 3^6*w 1*w 3^2 + 8*v 1*v 2^2*v 3^6*w 2^3 - 16*v 1*v 2^2*v 3^6*w 2^2*w 3 - 61*v 1*v 2^2*v 3^6*w 2*w 3^2 + 3*v 1*v 2^2*v 3^6*w 3^3 - 54*v 1*v 2*v 3^7*w 1*w 2*w 3 - 36*v 1*v 2*v 3^7*w 1*w 3^2 - 27*v 1*v 2*v 3^7*w 2^2*w 3 - 45*v 1*v 2*v 3^7*w 2*w 3^2 - 18*v 1*v 2*v 3^7*w 3^3 + 18*v 2^9*w 1*w 3^2 - 18*v 2^9*w 2*w 3^2 + 9*v 2^9*w 3^3 - 27*v 2^8*v 3*w 1*w 2*w 3 + 9*v 2^8*v 3*w 1*w 3^2 - 72*v 2^8*v 3*w 2^2*w 3 - 45*v 2^8*v 3*w 2*w 3^2 + 18*v 2^8*v 3*w 3^3 - 78*v 2^7*v 3^2*w 1*w 2^2 - 103*v 2^7*v 3^2*w 1*w 2*w 3 + 12*v 2^7*v 3^2*w 1*w 3^2 + 6*v 2^7*v 3^2*w 2^3 - 86*v 2^7*v 3^2*w 2^2*w 3 - 65*v 2^7*v 3^2*w 2*w 3^2 + 28*v 2^7*v 3^2*w 3^3 - 138*v 2^6*v 3^3*w 1*w 2^2 - 241*v 2^6*v 3^3*w 1*w 2*w 3 - 9*v 2^6*v 3^3*w 1*w 3^2 - 153*v 2^6*v 3^3*w 2^3 - 524*v 2^6*v 3^3*w 2^2*w 3 - 482*v 2^6*v 3^3*w 2*w 3^2 - 119*v 2^6*v 3^3*w 3^3 - 132*v 2^5*v 3^4*w 1*w 2^2 - 325*v 2^5*v 3^4*w 1*w 2*w 3 - 108*v 2^5*v 3^4*w 1*w 3^2 - 258*v 2^5*v 3^4*w 2^3 - 788*v 2^5*v 3^4*w 2^2*w 3 - 728*v 2^5*v 3^4*w 2*w 3^2 - 281*v 2^5*v 3^4*w 3^3 - 108*v 2^4*v 3^5*w 1*w 2^2 - 325*v 2^4*v 3^5*w 1*w 2*w 3 - 171*v 2^4*v 3^5*w 1*w 3^2 - 275*v 2^4*v 3^5*w 2^3 - 710*v 2^4*v 3^5*w 2^2*w 3 - 731*v 2^4*v 3^5*w 2*w 3^2 - 252*v 2^4*v 3^5*w 3^3 - 48*v 2^3*v 3^6*w 1*w 2^2 - 241*v 2^3*v 3^6*w 1*w 2*w 3 - 162*v 2^3*v 3^6*w 1*w 3^2 - 86*v 2^3*v 3^6*w 2^3 - 344*v 2^3*v 3^6*w 2^2*w 3 - 401*v 2^3*v 3^6*w 2*w 3^2 - 120*v 2^3*v 3^6*w 3^3 - 12*v 2^2*v 3^7*w 1*w 2^2 - 103*v 2^2*v 3^7*w 1*w 2*w 3 - 87*v 2^2*v 3^7*w 1*w 3^2 + 19*v 2^2*v 3^7*w 2^3 - 68*v 2^2*v 3^7*w 2^2*w 3 - 104*v 2^2*v 3^7*w 2*w 3^2 - 3*v 2^2*v 3^7*w 3^3 - 27*v 2*v 3^8*w 1*w 2*w 3 - 18*v 2*v 3^8*w 1*w 3^2 + 36*v 2*v 3^8*w 2^3 + 18*v 2*v 3^8*w 2^2*w 3 + 18*v 2*v 3^8*w 3^3 + 9*v 3^9*w 2^3) * h3 + (32*v 1^7*v 2^2*v 3^2*w 1 + 16*v 1^7*v 2^2*v 3^2*w 2 + 16*v 1^7*v 2^2*v 3^2*w 3 + 240*v 1^6*v 2^3*v 3^2*w 2 + 192*v 1^6*v 2^3*v 3^2*w 3 + 112*v 1^6*v 2^2*v 3^3*w 1 + 80*v 1^6*v 2^2*v 3^3*w 2 + 128*v 1^6*v 2^2*v 3^3*w 3 + 40*v 1^5*v 2^4*v 3^2*w 1 + 404*v 1^5*v 2^4*v 3^2*w 2 + 260*v 1^5*v 2^4*v 3^2*w 3 + 192*v 1^5*v 2^3*v 3^3*w 1 + 552*v 1^5*v 2^3*v 3^3*w 2 + 552*v 1^5*v 2^3*v 3^3*w 3 + 152*v 1^5*v 2^2*v 3^4*w 1 + 148*v 1^5*v 2^2*v 3^4*w 2 + 292*v 1^5*v 2^2*v 3^4*w 3 - 12*v 1^4*v 2^5*v 3^2*w 1 + 396*v 1^4*v 2^5*v 3^2*w 2 + 240*v 1^4*v 2^5*v 3^2*w 3 + 188*v 1^4*v 2^4*v 3^3*w 1 + 808*v 1^4*v 2^4*v 3^3*w 2 + 652*v 1^4*v 2^4*v 3^3*w 3 + 188*v 1^4*v 2^3*v 3^4*w 1 + 652*v 1^4*v 2^3*v 3^4*w 2 + 808*v 1^4*v 2^3*v 3^4*w 3 + 100*v 1^4*v 2^2*v 3^5*w 1 + 128*v 1^4*v 2^2*v 3^5*w 2 + 284*v 1^4*v 2^2*v 3^5*w 3 - 36*v 1^3*v 2^8*w 1 - 18*v 1^3*v 2^8*w 2 - 18*v 1^3*v 2^8*w 3 - 36*v 1^3*v 2^7*v 3*w 1 - 18*v 1^3*v 2^7*v 3*w 2 - 18*v 1^3*v 2^7*v 3*w 3 - 54*v 1^3*v 2^6*v 3^2*w 1 + 81*v 1^3*v 2^6*v 3^2*w 2 + 9*v 1^3*v 2^6*v 3^2*w 3 - 38*v 1^3*v 2^5*v 3^3*w 1 + 341*v 1^3*v 2^5*v 3^3*w 2 + 197*v 1^3*v 2^5*v 3^3*w 3 + 108*v 1^3*v 2^4*v 3^4*w 1 + 486*v 1^3*v 2^4*v 3^4*w 2 + 486*v 1^3*v 2^4*v 3^4*w 3 + 40*v 1^3*v 2^3*v 3^5*w 1 + 236*v 1^3*v 2^3*v 3^5*w 2 + 380*v 1^3*v 2^3*v 3^5*w 3 - 6*v 1^3*v 2^2*v 3^6*w 1 + 33*v 1^3*v 2^2*v 3^6*w 2 + 105*v 1^3*v 2^2*v 3^6*w 3 - 18*v 1^3*v 2*v 3^7*w 1 - 9*v 1^3*v 2*v 3^7*w 2 - 9*v 1^3*v 2*v 3^7*w 3 - 54*v 1^2*v 2^9*w 1 - 27*v 1^2*v 2^9*w 3 - 108*v 1^2*v 2^8*v 3*w 1 - 126*v 1^2*v 2^8*v 3*w 2 - 117*v 1^2*v 2^8*v 3*w 3 - 179*v 1^2*v 2^7*v 3^2*w 1 - 169*v 1^2*v 2^7*v 3^2*w 2 - 142*v 1^2*v 2^7*v 3^2*w 3 - 358*v 1^2*v 2^6*v 3^3*w 1 - 266*v 1^2*v 2^6*v 3^3*w 2 - 278*v 1^2*v 2^6*v 3^3*w 3 - 335*v 1^2*v 2^5*v 3^4*w 1 - 136*v 1^2*v 2^5*v 3^4*w 2 - 37*v 1^2*v 2^5*v 3^4*w 3 - 218*v 1^2*v 2^4*v 3^5*w 1 - 25*v 1^2*v 2^4*v 3^5*w 2 - 85*v 1^2*v 2^4*v 3^5*w 3 - 169*v 1^2*v 2^3*v 3^6*w 1 - 173*v 1^2*v 2^3*v 3^6*w 2 - 176*v 1^2*v 2^3*v 3^6*w 3 - 80*v 1^2*v 2^2*v 3^7*w 1 - 136*v 1^2*v 2^2*v 3^7*w 2 - 178*v 1^2*v 2^2*v 3^7*w 3 - 27*v 1^2*v 2*v 3^8*w 1 - 72*v 1^2*v 2*v 3^8*w 2 - 72*v 1^2*v 2*v 3^8*w 3 - 9*v 1^2*v 3^9*w 2 - 54*v 1*v 2^10*w 1 - 27*v 1*v 2^10*w 3 - 162*v 1*v 2^9*v 3*w 1 - 126*v 1*v 2^9*v 3*w 2 - 144*v 1*v 2^9*v 3*w 3 - 291*v 1*v 2^8*v 3^2*w 1 - 315*v 1*v 2^8*v 3^2*w 2 - 267*v 1*v 2^8*v 3^2*w 3 - 561*v 1*v 2^7*v 3^3*w 1 - 543*v 1*v 2^7*v 3^3*w 2 - 480*v 1*v 2^7*v 3^3*w 3 - 753*v 1*v 2^6*v 3^4*w 1 - 642*v 1*v 2^6*v 3^4*w 2 - 495*v 1*v 2^6*v 3^4*w 3 - 633*v 1*v 2^5*v 3^5*w 1 - 441*v 1*v 2^5*v 3^5*w 2 - 402*v 1*v 2^5*v 3^5*w 3 - 447*v 1*v 2^4*v 3^6*w 1 - 378*v 1*v 2^4*v 3^6*w 2 - 501*v 1*v 2^4*v 3^6*w 3 - 273*v 1*v 2^3*v 3^7*w 1 - 369*v 1*v 2^3*v 3^7*w 2 - 462*v 1*v 2^3*v 3^7*w 3 - 111*v 1*v 2^2*v 3^8*w 1 - 216*v 1*v 2^2*v 3^8*w 2 - 270*v 1*v 2^2*v 3^8*w 3 - 27*v 1*v 2*v 3^9*w 1 - 81*v 1*v 2*v 3^9*w 2 - 72*v 1*v 2*v 3^9*w 3 - 9*v 1*v 3^10*w 2 - 18*v 2^11*w 1 + 18*v 2^11*w 2 - 9*v 2^11*w 3 - 72*v 2^10*v 3*w 1 - 72*v 2^10*v 3*w 3 - 151*v 2^9*v 3^2*w 1 - 2*v 2^9*v 3^2*w 2 - 149*v 2^9*v 3^2*w 3 - 284*v 2^8*v 3^3*w 1 + 95*v 2^8*v 3^3*w 2 - 190*v 2^8*v 3^3*w 3 - 438*v 2^7*v 3^4*w 1 + 192*v 2^7*v 3^4*w 2 - 90*v 2^7*v 3^4*w 3 - 462*v 2^6*v 3^5*w 1 + 258*v 2^6*v 3^5*w 2 + 198*v 2^6*v 3^5*w 3 - 360*v 2^5*v 3^6*w 1 + 174*v 2^5*v 3^6*w 2 + 336*v 2^5*v 3^6*w 3 - 240*v 2^4*v 3^7*w 1 - 60*v 2^4*v 3^7*w 2 + 216*v 2^4*v 3^7*w 3 - 128*v 2^3*v 3^8*w 1 - 184*v 2^3*v 3^8*w 2 + 65*v 2^3*v 3^8*w 3 - 46*v 2^2*v 3^9*w 1 - 140*v 2^2*v 3^9*w 2 - 8*v 2^2*v 3^9*w 3 - 9*v 2*v 3^10*w 1 - 54*v 2*v 3^10*w 2 - 9*v 2*v 3^10*w 3 - 9*v 3^11*w 2) * h4 + (72*v 1*v 2^8*w 1*w 3 + 36*v 1*v 2^8*w 2*w 3 + 36*v 1*v 2^8*w 3^2 - 36*v 1*v 2^7*v 3*w 1*w 3 - 18*v 1*v 2^7*v 3*w 2*w 3 - 18*v 1*v 2^7*v 3*w 3^2 - 168*v 1*v 2^6*v 3^2*w 1*w 2 + 132*v 1*v 2^6*v 3^2*w 1*w 3 - 84*v 1*v 2^6*v 3^2*w 2^2 - 18*v 1*v 2^6*v 3^2*w 2*w 3 + 66*v 1*v 2^6*v 3^2*w 3^2 + 24*v 1*v 2^5*v 3^3*w 1*w 3 + 12*v 1*v 2^5*v 3^3*w 2*w 3 + 12*v 1*v 2^5*v 3^3*w 3^2 - 24*v 1*v 2^4*v 3^4*w 1*w 3 - 12*v 1*v 2^4*v 3^4*w 2*w 3 - 12*v 1*v 2^4*v 3^4*w 3^2 - 132*v 1*v 2^3*v 3^5*w 1*w 3 - 66*v 1*v 2^3*v 3^5*w 2*w 3 - 66*v 1*v 2^3*v 3^5*w 3^2 - 132*v 1*v 2^2*v 3^6*w 1*w 3 - 66*v 1*v 2^2*v 3^6*w 2*w 3 - 66*v 1*v 2^2*v 3^6*w 3^2 - 72*v 1*v 2*v 3^7*w 1*w 3 - 36*v 1*v 2*v 3^7*w 2*w 3 - 36*v 1*v 2*v 3^7*w 3^2 + 36*v 2^9*w 1*w 3 - 36*v 2^9*w 2*w 3 + 18*v 2^9*w 3^2 + 18*v 2^8*v 3*w 1*w 3 - 108*v 2^8*v 3*w 2^2 - 126*v 2^8*v 3*w 2*w 3 - 18*v 2^8*v 3*w 3^2 - 84*v 2^7*v 3^2*w 1*w 2 + 48*v 2^7*v 3^2*w 1*w 3 - 204*v 2^7*v 3^2*w 2^2 - 378*v 2^7*v 3^2*w 2*w 3 - 18*v 2^7*v 3^2*w 3^2 - 84*v 2^6*v 3^3*w 1*w 2 + 78*v 2^6*v 3^3*w 1*w 3 - 504*v 2^6*v 3^3*w 2^2 - 804*v 2^6*v 3^3*w 2*w 3 - 318*v 2^6*v 3^3*w 3^2 - 558*v 2^5*v 3^4*w 2^2 - 1044*v 2^5*v 3^4*w 2*w 3 - 462*v 2^5*v 3^4*w 3^2 - 78*v 2^4*v 3^5*w 1*w 3 - 450*v 2^4*v 3^5*w 2^2 - 966*v 2^4*v 3^5*w 2*w 3 - 546*v 2^4*v 3^5*w 3^2 - 132*v 2^3*v 3^6*w 1*w 3 - 252*v 2^3*v 3^6*w 2^2 - 678*v 2^3*v 3^6*w 2*w 3 - 438*v 2^3*v 3^6*w 3^2 - 102*v 2^2*v 3^7*w 1*w 3 - 36*v 2^2*v 3^7*w 2^2 - 312*v 2^2*v 3^7*w 2*w 3 - 222*v 2^2*v 3^7*w 3^2 - 36*v 2*v 3^8*w 1*w 3 + 18*v 2*v 3^8*w 2^2 - 72*v 2*v 3^8*w 2*w 3 - 72*v 2*v 3^8*w 3^2 + 18*v 3^9*w 2^2) * h5 + (36*v 1*v 2^8*w 1 + 18*v 1*v 2^8*w 2 + 18*v 1*v 2^8*w 3 + 36*v 1*v 2^7*v 3*w 1 + 18*v 1*v 2^7*v 3*w 2 + 18*v 1*v 2^7*v 3*w 3 + 86*v 1*v 2^6*v 3^2*w 1 + 43*v 1*v 2^6*v 3^2*w 2 + 43*v 1*v 2^6*v 3^2*w 3 + 166*v 1*v 2^5*v 3^3*w 1 + 83*v 1*v 2^5*v 3^3*w 2 + 83*v 1*v 2^5*v 3^3*w 3 + 84*v 1*v 2^4*v 3^4*w 1 + 42*v 1*v 2^4*v 3^4*w 2 + 42*v 1*v 2^4*v 3^4*w 3 + 88*v 1*v 2^3*v 3^5*w 1 + 44*v 1*v 2^3*v 3^5*w 2 + 44*v 1*v 2^3*v 3^5*w 3 + 38*v 1*v 2^2*v 3^6*w 1 + 19*v 1*v 2^2*v 3^6*w 2 + 19*v 1*v 2^2*v 3^6*w 3 + 18*v 1*v 2*v 3^7*w 1 + 9*v 1*v 2*v 3^7*w 2 + 9*v 1*v 2*v 3^7*w 3 + 18*v 2^9*w 1 - 18*v 2^9*w 2 + 9*v 2^9*w 3 + 36*v 2^8*v 3*w 1 + 18*v 2^8*v 3*w 2 + 45*v 2^8*v 3*w 3 + 61*v 2^7*v 3^2*w 1 - 112*v 2^7*v 3^2*w 2 + 13*v 2^7*v 3^2*w 3 + 126*v 2^6*v 3^3*w 1 - 112*v 2^6*v 3^3*w 2 + 28*v 2^6*v 3^3*w 3 + 125*v 2^5*v 3^4*w 1 - 169*v 2^5*v 3^4*w 2 - 128*v 2^5*v 3^4*w 3 + 86*v 2^4*v 3^5*w 1 - 101*v 2^4*v 3^5*w 2 - 181*v 2^4*v 3^5*w 3 + 63*v 2^3*v 3^6*w 1 - 14*v 2^3*v 3^6*w 2 - 139*v 2^3*v 3^6*w 3 + 28*v 2^2*v 3^7*w 1 + 40*v 2^2*v 3^7*w 2 - 70*v 2^2*v 3^7*w 3 + 9*v 2*v 3^8*w 1 + 27*v 2*v 3^8*w 2 - 9*v 2*v 3^8*w 3 + 9*v 3^9*w 2) * hq

set_option maxRecDepth 20000 in
theorem F1_w0 (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0)
    (h4 : ip w w = 0) (h5 : t3 v v w = 0) (hq : 3 * t4 v v w w = ip v w ^ 2) (hk : v 0 = 0) :
    8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * w 0 ^ 2) = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4 h5 hq
  linear_combination (8*v 1^2*w 1^5 + 16*v 1^2*w 1^4*w 2 + 16*v 1^2*w 1^4*w 3 + 8*v 1^2*w 1^3*w 2^2 + 16*v 1^2*w 1^3*w 2*w 3 + 8*v 1^2*w 1^3*w 3^2 - 8*v 1*v 2*w 1^5 + 8*v 1*v 2*w 1^4*w 2 - 16*v 1*v 2*w 1^4*w 3 + 40*v 1*v 2*w 1^3*w 2^2 + 32*v 1*v 2*w 1^3*w 2*w 3 - 8*v 1*v 2*w 1^3*w 3^2 + 14*v 1*v 2*w 1^2*w 2^3 + 102*v 1*v 2*w 1^2*w 2^2*w 3 + 34*v 1*v 2*w 1^2*w 2*w 3^2 - 22*v 1*v 2*w 1^2*w 3^3 + 8*v 1*v 2*w 1*w 2^4 - 20*v 1*v 2*w 1*w 2^3*w 3 + 8*v 1*v 2*w 1*w 2^2*w 3^2 + 60*v 1*v 2*w 1*w 2*w 3^3 - 8*v 1*v 2*w 1*w 3^4 - 34*v 1*v 2*w 2^5 - 94*v 1*v 2*w 2^4*w 3 - 78*v 1*v 2*w 2^3*w 3^2 - 66*v 1*v 2*w 2^2*w 3^3 + 4*v 1*v 3*w 1^5 - 16*v 1*v 3*w 1^4*w 2 + 8*v 1*v 3*w 1^4*w 3 - 8*v 1*v 3*w 1^3*w 2^2 + 32*v 1*v 3*w 1^3*w 2*w 3 + 40*v 1*v 3*w 1^3*w 3^2 - 22*v 1*v 3*w 1^2*w 2^3 + 34*v 1*v 3*w 1^2*w 2^2*w 3 + 102*v 1*v 3*w 1^2*w 2*w 3^2 + 14*v 1*v 3*w 1^2*w 3^3 + 4*v 1*v 3*w 1*w 2^4 + 96*v 1*v 3*w 1*w 2^3*w 3 + 44*v 1*v 3*w 1*w 2^2*w 3^2 + 16*v 1*v 3*w 1*w 2*w 3^3 + 20*v 1*v 3*w 1*w 3^4 + 12*v 1*v 3*w 2^5 + 24*v 1*v 3*w 2^4*w 3 - 30*v 1*v 3*w 2^3*w 3^2 - 42*v 1*v 3*w 2^2*w 3^3 - 70*v 1*v 3*w 2*w 3^4 - 22*v 1*v 3*w 3^5 + 8*v 2^2*w 1^5 - 8*v 2^2*w 1^4*w 2 + 16*v 2^2*w 1^4*w 3 - 16*v 2^2*w 1^3*w 2^2 - 32*v 2^2*w 1^3*w 2*w 3 + 8*v 2^2*w 1^3*w 3^2 + 34*v 2^2*w 1^2*w 2^3 - 54*v 2^2*w 1^2*w 2^2*w 3 - 34*v 2^2*w 1^2*w 2*w 3^2 + 22*v 2^2*w 1^2*w 3^3 + 16*v 2^2*w 1*w 2^4 + 68*v 2^2*w 1*w 2^3*w 3 + 16*v 2^2*w 1*w 2^2*w 3^2 - 60*v 2^2*w 1*w 2*w 3^3 + 8*v 2^2*w 1*w 3^4 + 34*v 2^2*w 2^5 + 94*v 2^2*w 2^4*w 3 + 78*v 2^2*w 2^3*w 3^2 + 66*v 2^2*w 2^2*w 3^3 + 4*v 2*v 3*w 1^5 + 8*v 2*v 3*w 1^4*w 2 + 8*v 2*v 3*w 1^4*w 3 - 32*v 2*v 3*w 1^3*w 2^2 - 16*v 2*v 3*w 1^3*w 2*w 3 - 32*v 2*v 3*w 1^3*w 3^2 + 8*v 2*v 3*w 1^2*w 2^3 - 40*v 2*v 3*w 1^2*w 2^2*w 3 - 40*v 2*v 3*w 1^2*w 2*w 3^2 + 8*v 2*v 3*w 1^2*w 3^3 - 12*v 2*v 3*w 1*w 2^4 - 28*v 2*v 3*w 1*w 2^3*w 3 + 44*v 2*v 3*w 1*w 2^2*w 3^2 - 28*v 2*v 3*w 1*w 2*w 3^3 - 12*v 2*v 3*w 1*w 3^4 + 22*v 2*v 3*w 2^5 + 70*v 2*v 3*w 2^4*w 3 + 108*v 2*v 3*w 2^3*w 3^2 + 108*v 2*v 3*w 2^2*w 3^3 + 70*v 2*v 3*w 2*w 3^4 + 22*v 2*v 3*w 3^5 - 4*v 3^2*w 1^5 + 16*v 3^2*w 1^4*w 2 - 8*v 3^2*w 1^4*w 3 + 8*v 3^2*w 1^3*w 2^2 - 32*v 3^2*w 1^3*w 2*w 3 - 16*v 3^2*w 1^3*w 3^2 + 22*v 3^2*w 1^2*w 2^3 - 34*v 3^2*w 1^2*w 2^2*w 3 - 54*v 3^2*w 1^2*w 2*w 3^2 + 34*v 3^2*w 1^2*w 3^3 - 4*v 3^2*w 1*w 2^4 - 96*v 3^2*w 1*w 2^3*w 3 - 20*v 3^2*w 1*w 2^2*w 3^2 + 32*v 3^2*w 1*w 2*w 3^3 + 4*v 3^2*w 1*w 3^4 - 12*v 3^2*w 2^5 - 24*v 3^2*w 2^4*w 3 + 30*v 3^2*w 2^3*w 3^2 + 42*v 3^2*w 2^2*w 3^3 + 70*v 3^2*w 2*w 3^4 + 22*v 3^2*w 3^5) * h1 + (8*v 1^3*w 0*w 1^3 - 8*v 1^3*w 1^4 - 8*v 1^3*w 1^3*w 2 - 8*v 1^3*w 1^3*w 3 + 24*v 1^2*v 2*w 0*w 1^2*w 2 - 24*v 1^2*v 2*w 1^3*w 2 - 24*v 1^2*v 2*w 1^2*w 2^2 - 24*v 1^2*v 2*w 1^2*w 2*w 3 + 24*v 1^2*v 3*w 0*w 1^2*w 3 - 24*v 1^2*v 3*w 1^3*w 3 - 24*v 1^2*v 3*w 1^2*w 2*w 3 - 24*v 1^2*v 3*w 1^2*w 3^2 + 24*v 1*v 2^2*w 0*w 1*w 2^2 - 24*v 1*v 2^2*w 1^2*w 2^2 - 24*v 1*v 2^2*w 1*w 2^3 - 24*v 1*v 2^2*w 1*w 2^2*w 3 + 48*v 1*v 2*v 3*w 0*w 1*w 2*w 3 - 48*v 1*v 2*v 3*w 1^2*w 2*w 3 - 48*v 1*v 2*v 3*w 1*w 2^2*w 3 - 48*v 1*v 2*v 3*w 1*w 2*w 3^2 + 24*v 1*v 3^2*w 0*w 1*w 3^2 - 24*v 1*v 3^2*w 1^2*w 3^2 - 24*v 1*v 3^2*w 1*w 2*w 3^2 - 24*v 1*v 3^2*w 1*w 3^3 + 4*v 2^3*w 0*w 1^3 - 8*v 2^3*w 0*w 1^2*w 2 + 4*v 2^3*w 0*w 1^2*w 3 - 4*v 2^3*w 0*w 1*w 2^2 - 16*v 2^3*w 0*w 1*w 2*w 3 - 4*v 2^3*w 0*w 1*w 3^2 + 28*v 2^3*w 0*w 2^3 + 24*v 2^3*w 0*w 2^2*w 3 + 12*v 2^3*w 0*w 2*w 3^2 - 4*v 2^3*w 1^4 + 4*v 2^3*w 1^3*w 2 - 8*v 2^3*w 1^3*w 3 + 12*v 2^3*w 1^2*w 2^2 + 20*v 2^3*w 1^2*w 2*w 3 - 24*v 2^3*w 1*w 2^3 - 4*v 2^3*w 1*w 2^2*w 3 + 8*v 2^3*w 1*w 2*w 3^2 + 4*v 2^3*w 1*w 3^3 - 28*v 2^3*w 2^4 - 52*v 2^3*w 2^3*w 3 - 36*v 2^3*w 2^2*w 3^2 - 12*v 2^3*w 2*w 3^3 + 12*v 2^2*v 3*w 0*w 1^2*w 3 - 24*v 2^2*v 3*w 0*w 1*w 2^2 - 36*v 2^2*v 3*w 0*w 1*w 2*w 3 - 24*v 2^2*v 3*w 0*w 1*w 3^2 + 34*v 2^2*v 3*w 0*w 2^3 + 18*v 2^2*v 3*w 0*w 2^2*w 3 + 38*v 2^2*v 3*w 0*w 2*w 3^2 + 22*v 2^2*v 3*w 0*w 3^3 - 12*v 2^2*v 3*w 1^3*w 3 + 24*v 2^2*v 3*w 1^2*w 2^2 + 24*v 2^2*v 3*w 1^2*w 2*w 3 + 12*v 2^2*v 3*w 1^2*w 3^2 - 10*v 2^2*v 3*w 1*w 2^3 + 42*v 2^2*v 3*w 1*w 2^2*w 3 + 22*v 2^2*v 3*w 1*w 2*w 3^2 + 2*v 2^2*v 3*w 1*w 3^3 - 34*v 2^2*v 3*w 2^4 - 52*v 2^2*v 3*w 2^3*w 3 - 56*v 2^2*v 3*w 2^2*w 3^2 - 60*v 2^2*v 3*w 2*w 3^3 - 22*v 2^2*v 3*w 3^4 + 12*v 2*v 3^2*w 0*w 1^2*w 2 - 24*v 2*v 3^2*w 0*w 1*w 2^2 - 36*v 2*v 3^2*w 0*w 1*w 2*w 3 - 24*v 2*v 3^2*w 0*w 1*w 3^2 + 22*v 2*v 3^2*w 0*w 2^3 + 38*v 2*v 3^2*w 0*w 2^2*w 3 + 18*v 2*v 3^2*w 0*w 2*w 3^2 + 34*v 2*v 3^2*w 0*w 3^3 - 12*v 2*v 3^2*w 1^3*w 2 + 12*v 2*v 3^2*w 1^2*w 2^2 + 24*v 2*v 3^2*w 1^2*w 2*w 3 + 24*v 2*v 3^2*w 1^2*w 3^2 + 2*v 2*v 3^2*w 1*w 2^3 + 22*v 2*v 3^2*w 1*w 2^2*w 3 + 42*v 2*v 3^2*w 1*w 2*w 3^2 - 10*v 2*v 3^2*w 1*w 3^3 - 22*v 2*v 3^2*w 2^4 - 60*v 2*v 3^2*w 2^3*w 3 - 56*v 2*v 3^2*w 2^2*w 3^2 - 52*v 2*v 3^2*w 2*w 3^3 - 34*v 2*v 3^2*w 3^4 - 8*v 3^3*w 0*w 1^3 + 16*v 3^3*w 0*w 1^2*w 2 + 4*v 3^3*w 0*w 1^2*w 3 - 4*v 3^3*w 0*w 1*w 2^2 - 28*v 3^3*w 0*w 1*w 2*w 3 - 4*v 3^3*w 0*w 1*w 3^2 - 12*v 3^3*w 0*w 2^3 + 12*v 3^3*w 0*w 2*w 3^2 + 16*v 3^3*w 0*w 3^3 + 8*v 3^3*w 1^4 - 8*v 3^3*w 1^3*w 2 + 4*v 3^3*w 1^3*w 3 - 12*v 3^3*w 1^2*w 2^2 + 8*v 3^3*w 1^2*w 2*w 3 + 16*v 3^3*w 1*w 2^3 + 32*v 3^3*w 1*w 2^2*w 3 + 20*v 3^3*w 1*w 2*w 3^2 - 12*v 3^3*w 1*w 3^3 + 12*v 3^3*w 2^4 + 12*v 3^3*w 2^3*w 3 - 12*v 3^3*w 2^2*w 3^2 - 28*v 3^3*w 2*w 3^3 - 16*v 3^3*w 3^4) * h2 + (-10*v 2*w 1^2*w 2^3 + 54*v 2*w 1^2*w 2^2*w 3 + 10*v 2*w 1^2*w 2*w 3^2 - 22*v 2*w 1^2*w 3^3 + 12*v 2*w 1*w 2^4 + 104*v 2*w 1*w 2^3*w 3 + 28*v 2*w 1*w 2^2*w 3^2 - 16*v 2*w 1*w 3^4 + 34*v 2*w 2^5 + 94*v 2*w 2^4*w 3 + 78*v 2*w 2^3*w 3^2 + 66*v 2*w 2^2*w 3^3 - 12*v 3*w 1^5 - 22*v 3*w 1^2*w 2^3 + 10*v 3*w 1^2*w 2^2*w 3 + 54*v 3*w 1^2*w 2*w 3^2 - 10*v 3*w 1^2*w 3^3 - 28*v 3*w 1*w 2^4 - 36*v 3*w 1*w 2^3*w 3 - 8*v 3*w 1*w 2^2*w 3^2 + 68*v 3*w 1*w 2*w 3^3 - 12*v 3*w 2^5 - 24*v 3*w 2^4*w 3 + 30*v 3*w 2^3*w 3^2 + 42*v 3*w 2^2*w 3^3 + 70*v 3*w 2*w 3^4 + 22*v 3*w 3^5) * h3 + (-4*v 2^3*w 1^3 + 8*v 2^3*w 1^2*w 2 - 4*v 2^3*w 1^2*w 3 + 4*v 2^3*w 1*w 2^2 + 16*v 2^3*w 1*w 2*w 3 + 4*v 2^3*w 1*w 3^2 - 20*v 2^3*w 2^3 - 24*v 2^3*w 2^2*w 3 - 12*v 2^3*w 2*w 3^2 - 12*v 2^2*v 3*w 1^2*w 3 + 24*v 2^2*v 3*w 1*w 2^2 + 36*v 2^2*v 3*w 1*w 2*w 3 + 24*v 2^2*v 3*w 1*w 3^2 - 34*v 2^2*v 3*w 2^3 + 6*v 2^2*v 3*w 2^2*w 3 - 38*v 2^2*v 3*w 2*w 3^2 - 22*v 2^2*v 3*w 3^3 - 12*v 2*v 3^2*w 1^2*w 2 + 24*v 2*v 3^2*w 1*w 2^2 + 36*v 2*v 3^2*w 1*w 2*w 3 + 24*v 2*v 3^2*w 1*w 3^2 - 22*v 2*v 3^2*w 2^3 - 38*v 2*v 3^2*w 2^2*w 3 + 6*v 2*v 3^2*w 2*w 3^2 - 34*v 2*v 3^2*w 3^3 + 8*v 3^3*w 1^3 - 16*v 3^3*w 1^2*w 2 - 4*v 3^3*w 1^2*w 3 + 4*v 3^3*w 1*w 2^2 + 28*v 3^3*w 1*w 2*w 3 + 4*v 3^3*w 1*w 3^2 + 12*v 3^3*w 2^3 - 12*v 3^3*w 2*w 3^2 - 8*v 3^3*w 3^3) * h4 + (20*v 2*w 1*w 2^3 - 108*v 2*w 1*w 2^2*w 3 - 20*v 2*w 1*w 2*w 3^2 + 44*v 2*w 1*w 3^3 - 20*v 2*w 2^4 - 84*v 2*w 2^3*w 3 - 36*v 2*w 2^2*w 3^2 - 60*v 2*w 2*w 3^3 + 24*v 2*w 3^4 + 44*v 3*w 1*w 2^3 - 20*v 3*w 1*w 2^2*w 3 - 108*v 3*w 1*w 2*w 3^2 + 20*v 3*w 1*w 3^3 + 24*v 3*w 2^4 - 60*v 3*w 2^3*w 3 - 36*v 3*w 2^2*w 3^2 - 84*v 3*w 2*w 3^3 - 20*v 3*w 3^4) * h5 + (8*v 0^2*w 0^5 + 24*v 0*v 1*w 0^4*w 1 + 24*v 0*v 2*w 0^4*w 2 - 20*v 0*v 2*w 0*w 1*w 2^3 + 108*v 0*v 2*w 0*w 1*w 2^2*w 3 + 20*v 0*v 2*w 0*w 1*w 2*w 3^2 - 44*v 0*v 2*w 0*w 1*w 3^3 + 20*v 0*v 2*w 0*w 2^4 + 84*v 0*v 2*w 0*w 2^3*w 3 + 36*v 0*v 2*w 0*w 2^2*w 3^2 + 60*v 0*v 2*w 0*w 2*w 3^3 - 24*v 0*v 2*w 0*w 3^4 + 10*v 0*v 2*w 1^2*w 2^3 - 54*v 0*v 2*w 1^2*w 2^2*w 3 - 10*v 0*v 2*w 1^2*w 2*w 3^2 + 22*v 0*v 2*w 1^2*w 3^3 - 12*v 0*v 2*w 1*w 2^4 - 104*v 0*v 2*w 1*w 2^3*w 3 - 28*v 0*v 2*w 1*w 2^2*w 3^2 + 16*v 0*v 2*w 1*w 3^4 - 34*v 0*v 2*w 2^5 - 94*v 0*v 2*w 2^4*w 3 - 78*v 0*v 2*w 2^3*w 3^2 - 66*v 0*v 2*w 2^2*w 3^3 + 24*v 0*v 3*w 0^4*w 3 - 44*v 0*v 3*w 0*w 1*w 2^3 + 20*v 0*v 3*w 0*w 1*w 2^2*w 3 + 108*v 0*v 3*w 0*w 1*w 2*w 3^2 - 20*v 0*v 3*w 0*w 1*w 3^3 - 24*v 0*v 3*w 0*w 2^4 + 60*v 0*v 3*w 0*w 2^3*w 3 + 36*v 0*v 3*w 0*w 2^2*w 3^2 + 84*v 0*v 3*w 0*w 2*w 3^3 + 20*v 0*v 3*w 0*w 3^4 + 12*v 0*v 3*w 1^5 + 22*v 0*v 3*w 1^2*w 2^3 - 10*v 0*v 3*w 1^2*w 2^2*w 3 - 54*v 0*v 3*w 1^2*w 2*w 3^2 + 10*v 0*v 3*w 1^2*w 3^3 + 28*v 0*v 3*w 1*w 2^4 + 36*v 0*v 3*w 1*w 2^3*w 3 + 8*v 0*v 3*w 1*w 2^2*w 3^2 - 68*v 0*v 3*w 1*w 2*w 3^3 + 12*v 0*v 3*w 2^5 + 24*v 0*v 3*w 2^4*w 3 - 30*v 0*v 3*w 2^3*w 3^2 - 42*v 0*v 3*w 2^2*w 3^3 - 70*v 0*v 3*w 2*w 3^4 - 22*v 0*v 3*w 3^5 + 24*v 1^2*w 0^3*w 1^2 - 8*v 1^2*w 1^5 - 16*v 1^2*w 1^4*w 2 - 16*v 1^2*w 1^4*w 3 - 8*v 1^2*w 1^3*w 2^2 - 16*v 1^2*w 1^3*w 2*w 3 - 8*v 1^2*w 1^3*w 3^2 + 48*v 1*v 2*w 0^3*w 1*w 2 + 8*v 1*v 2*w 1^5 - 8*v 1*v 2*w 1^4*w 2 + 16*v 1*v 2*w 1^4*w 3 - 40*v 1*v 2*w 1^3*w 2^2 - 32*v 1*v 2*w 1^3*w 2*w 3 + 8*v 1*v 2*w 1^3*w 3^2 - 14*v 1*v 2*w 1^2*w 2^3 - 102*v 1*v 2*w 1^2*w 2^2*w 3 - 34*v 1*v 2*w 1^2*w 2*w 3^2 + 22*v 1*v 2*w 1^2*w 3^3 - 8*v 1*v 2*w 1*w 2^4 + 20*v 1*v 2*w 1*w 2^3*w 3 - 8*v 1*v 2*w 1*w 2^2*w 3^2 - 60*v 1*v 2*w 1*w 2*w 3^3 + 8*v 1*v 2*w 1*w 3^4 + 34*v 1*v 2*w 2^5 + 94*v 1*v 2*w 2^4*w 3 + 78*v 1*v 2*w 2^3*w 3^2 + 66*v 1*v 2*w 2^2*w 3^3 + 48*v 1*v 3*w 0^3*w 1*w 3 - 4*v 1*v 3*w 1^5 + 16*v 1*v 3*w 1^4*w 2 - 8*v 1*v 3*w 1^4*w 3 + 8*v 1*v 3*w 1^3*w 2^2 - 32*v 1*v 3*w 1^3*w 2*w 3 - 40*v 1*v 3*w 1^3*w 3^2 + 22*v 1*v 3*w 1^2*w 2^3 - 34*v 1*v 3*w 1^2*w 2^2*w 3 - 102*v 1*v 3*w 1^2*w 2*w 3^2 - 14*v 1*v 3*w 1^2*w 3^3 - 4*v 1*v 3*w 1*w 2^4 - 96*v 1*v 3*w 1*w 2^3*w 3 - 44*v 1*v 3*w 1*w 2^2*w 3^2 - 16*v 1*v 3*w 1*w 2*w 3^3 - 20*v 1*v 3*w 1*w 3^4 - 12*v 1*v 3*w 2^5 - 24*v 1*v 3*w 2^4*w 3 + 30*v 1*v 3*w 2^3*w 3^2 + 42*v 1*v 3*w 2^2*w 3^3 + 70*v 1*v 3*w 2*w 3^4 + 22*v 1*v 3*w 3^5 + 24*v 2^2*w 0^3*w 2^2 - 8*v 2^2*w 1^5 + 8*v 2^2*w 1^4*w 2 - 16*v 2^2*w 1^4*w 3 + 16*v 2^2*w 1^3*w 2^2 + 32*v 2^2*w 1^3*w 2*w 3 - 8*v 2^2*w 1^3*w 3^2 - 34*v 2^2*w 1^2*w 2^3 + 54*v 2^2*w 1^2*w 2^2*w 3 + 34*v 2^2*w 1^2*w 2*w 3^2 - 22*v 2^2*w 1^2*w 3^3 - 16*v 2^2*w 1*w 2^4 - 68*v 2^2*w 1*w 2^3*w 3 - 16*v 2^2*w 1*w 2^2*w 3^2 + 60*v 2^2*w 1*w 2*w 3^3 - 8*v 2^2*w 1*w 3^4 - 34*v 2^2*w 2^5 - 94*v 2^2*w 2^4*w 3 - 78*v 2^2*w 2^3*w 3^2 - 66*v 2^2*w 2^2*w 3^3 + 48*v 2*v 3*w 0^3*w 2*w 3 - 4*v 2*v 3*w 1^5 - 8*v 2*v 3*w 1^4*w 2 - 8*v 2*v 3*w 1^4*w 3 + 32*v 2*v 3*w 1^3*w 2^2 + 16*v 2*v 3*w 1^3*w 2*w 3 + 32*v 2*v 3*w 1^3*w 3^2 - 8*v 2*v 3*w 1^2*w 2^3 + 40*v 2*v 3*w 1^2*w 2^2*w 3 + 40*v 2*v 3*w 1^2*w 2*w 3^2 - 8*v 2*v 3*w 1^2*w 3^3 + 12*v 2*v 3*w 1*w 2^4 + 28*v 2*v 3*w 1*w 2^3*w 3 - 44*v 2*v 3*w 1*w 2^2*w 3^2 + 28*v 2*v 3*w 1*w 2*w 3^3 + 12*v 2*v 3*w 1*w 3^4 - 22*v 2*v 3*w 2^5 - 70*v 2*v 3*w 2^4*w 3 - 108*v 2*v 3*w 2^3*w 3^2 - 108*v 2*v 3*w 2^2*w 3^3 - 70*v 2*v 3*w 2*w 3^4 - 22*v 2*v 3*w 3^5 + 24*v 3^2*w 0^3*w 3^2 + 4*v 3^2*w 1^5 - 16*v 3^2*w 1^4*w 2 + 8*v 3^2*w 1^4*w 3 - 8*v 3^2*w 1^3*w 2^2 + 32*v 3^2*w 1^3*w 2*w 3 + 16*v 3^2*w 1^3*w 3^2 - 22*v 3^2*w 1^2*w 2^3 + 34*v 3^2*w 1^2*w 2^2*w 3 + 54*v 3^2*w 1^2*w 2*w 3^2 - 34*v 3^2*w 1^2*w 3^3 + 4*v 3^2*w 1*w 2^4 + 96*v 3^2*w 1*w 2^3*w 3 + 20*v 3^2*w 1*w 2^2*w 3^2 - 32*v 3^2*w 1*w 2*w 3^3 - 4*v 3^2*w 1*w 3^4 + 12*v 3^2*w 2^5 + 24*v 3^2*w 2^4*w 3 - 30*v 3^2*w 2^3*w 3^2 - 42*v 3^2*w 2^2*w 3^3 - 70*v 3^2*w 2*w 3^4 - 22*v 3^2*w 3^5) * hk

set_option maxRecDepth 20000 in
theorem F1_w1 (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0)
    (h4 : ip w w = 0) (h5 : t3 v v w = 0) (hq : 3 * t4 v v w w = ip v w ^ 2) (hk : v 1 = 0) :
    8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * w 1 ^ 2) = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4 h5 hq
  linear_combination (-8*v 0^2*w 1^5 - 24*v 0^2*w 1^4*w 2 - 24*v 0^2*w 1^4*w 3 - 24*v 0^2*w 1^3*w 2^2 - 48*v 0^2*w 1^3*w 2*w 3 - 24*v 0^2*w 1^3*w 3^2 - 8*v 0^2*w 1^2*w 2^3 - 24*v 0^2*w 1^2*w 2^2*w 3 - 24*v 0^2*w 1^2*w 2*w 3^2 - 8*v 0^2*w 1^2*w 3^3 + 8*v 0*v 2*w 1^5 + 48*v 0*v 2*w 1^4*w 2 + 24*v 0*v 2*w 1^4*w 3 + 72*v 0*v 2*w 1^3*w 2^2 + 96*v 0*v 2*w 1^3*w 2*w 3 + 24*v 0*v 2*w 1^3*w 3^2 + 22*v 0*v 2*w 1^2*w 2^3 + 126*v 0*v 2*w 1^2*w 2^2*w 3 + 58*v 0*v 2*w 1^2*w 2*w 3^2 - 14*v 0*v 2*w 1^2*w 3^3 - 28*v 0*v 2*w 1*w 2^4 + 108*v 0*v 2*w 1*w 2^3*w 3 + 120*v 0*v 2*w 1*w 2^2*w 3^2 - 84*v 0*v 2*w 1*w 2*w 3^3 - 36*v 0*v 2*w 1*w 3^4 - 52*v 0*v 2*w 2^5 - 48*v 0*v 2*w 2^4*w 3 + 42*v 0*v 2*w 2^3*w 3^2 - 82*v 0*v 2*w 2^2*w 3^3 - 86*v 0*v 2*w 2*w 3^4 - 14*v 0*v 2*w 3^5 - 4*v 0*v 3*w 1^5 + 24*v 0*v 3*w 1^4*w 2 + 48*v 0*v 3*w 1^4*w 3 + 24*v 0*v 3*w 1^3*w 2^2 + 96*v 0*v 3*w 1^3*w 2*w 3 + 72*v 0*v 3*w 1^3*w 3^2 - 14*v 0*v 3*w 1^2*w 2^3 + 58*v 0*v 3*w 1^2*w 2^2*w 3 + 126*v 0*v 3*w 1^2*w 2*w 3^2 + 22*v 0*v 3*w 1^2*w 3^3 - 48*v 0*v 3*w 1*w 2^4 - 120*v 0*v 3*w 1*w 2^3*w 3 + 84*v 0*v 3*w 1*w 2^2*w 3^2 + 72*v 0*v 3*w 1*w 2*w 3^3 - 40*v 0*v 3*w 1*w 3^4 - 26*v 0*v 3*w 2^5 - 110*v 0*v 3*w 2^4*w 3 - 118*v 0*v 3*w 2^3*w 3^2 + 6*v 0*v 3*w 2^2*w 3^3 - 72*v 0*v 3*w 2*w 3^4 - 64*v 0*v 3*w 3^5 - 8*v 2^2*w 1^5 - 48*v 2^2*w 1^4*w 2 - 24*v 2^2*w 1^4*w 3 - 96*v 2^2*w 1^3*w 2^2 - 96*v 2^2*w 1^3*w 2*w 3 - 24*v 2^2*w 1^3*w 3^2 - 46*v 2^2*w 1^2*w 2^3 - 150*v 2^2*w 1^2*w 2^2*w 3 - 58*v 2^2*w 1^2*w 2*w 3^2 + 14*v 2^2*w 1^2*w 3^3 + 28*v 2^2*w 1*w 2^4 - 108*v 2^2*w 1*w 2^3*w 3 - 120*v 2^2*w 1*w 2^2*w 3^2 + 84*v 2^2*w 1*w 2*w 3^3 + 36*v 2^2*w 1*w 3^4 + 52*v 2^2*w 2^5 + 48*v 2^2*w 2^4*w 3 - 42*v 2^2*w 2^3*w 3^2 + 82*v 2^2*w 2^2*w 3^3 + 86*v 2^2*w 2*w 3^4 + 14*v 2^2*w 3^5 - 4*v 2*v 3*w 1^5 - 72*v 2*v 3*w 1^4*w 2 - 72*v 2*v 3*w 1^4*w 3 - 96*v 2*v 3*w 1^3*w 2^2 - 240*v 2*v 3*w 1^3*w 2*w 3 - 96*v 2*v 3*w 1^3*w 3^2 - 8*v 2*v 3*w 1^2*w 2^3 - 232*v 2*v 3*w 1^2*w 2^2*w 3 - 232*v 2*v 3*w 1^2*w 2*w 3^2 - 8*v 2*v 3*w 1^2*w 3^3 + 76*v 2*v 3*w 1*w 2^4 + 12*v 2*v 3*w 1*w 2^3*w 3 - 204*v 2*v 3*w 1*w 2^2*w 3^2 + 12*v 2*v 3*w 1*w 2*w 3^3 + 76*v 2*v 3*w 1*w 3^4 + 78*v 2*v 3*w 2^5 + 158*v 2*v 3*w 2^4*w 3 + 76*v 2*v 3*w 2^3*w 3^2 + 76*v 2*v 3*w 2^2*w 3^3 + 158*v 2*v 3*w 2*w 3^4 + 78*v 2*v 3*w 3^5 + 4*v 3^2*w 1^5 - 24*v 3^2*w 1^4*w 2 - 48*v 3^2*w 1^4*w 3 - 24*v 3^2*w 1^3*w 2^2 - 96*v 3^2*w 1^3*w 2*w 3 - 96*v 3^2*w 1^3*w 3^2 + 14*v 3^2*w 1^2*w 2^3 - 58*v 3^2*w 1^2*w 2^2*w 3 - 150*v 3^2*w 1^2*w 2*w 3^2 - 46*v 3^2*w 1^2*w 3^3 + 48*v 3^2*w 1*w 2^4 + 120*v 3^2*w 1*w 2^3*w 3 - 84*v 3^2*w 1*w 2^2*w 3^2 - 72*v 3^2*w 1*w 2*w 3^3 + 40*v 3^2*w 1*w 3^4 + 26*v 3^2*w 2^5 + 110*v 3^2*w 2^4*w 3 + 118*v 3^2*w 2^3*w 3^2 - 6*v 3^2*w 2^2*w 3^3 + 72*v 3^2*w 2*w 3^4 + 64*v 3^2*w 3^5) * h1 + (8*v 0^3*w 0^2*w 1^2 - 8*v 0^3*w 0*w 1^3 - 8*v 0^3*w 0*w 1^2*w 2 - 8*v 0^3*w 0*w 1^2*w 3 + 8*v 0^3*w 1^4 + 16*v 0^3*w 1^3*w 2 + 16*v 0^3*w 1^3*w 3 + 8*v 0^3*w 1^2*w 2^2 + 16*v 0^3*w 1^2*w 2*w 3 + 8*v 0^3*w 1^2*w 3^2 + 24*v 0^2*v 2*w 0*w 1^2*w 2 - 24*v 0^2*v 2*w 1^3*w 2 - 24*v 0^2*v 2*w 1^2*w 2^2 - 24*v 0^2*v 2*w 1^2*w 2*w 3 + 20*v 0^2*v 2*w 1*w 2^3 - 108*v 0^2*v 2*w 1*w 2^2*w 3 - 20*v 0^2*v 2*w 1*w 2*w 3^2 + 44*v 0^2*v 2*w 1*w 3^3 + 40*v 0^2*v 2*w 2^4 - 4*v 0^2*v 2*w 2^3*w 3 - 92*v 0^2*v 2*w 2^2*w 3^2 + 84*v 0^2*v 2*w 2*w 3^3 + 20*v 0^2*v 2*w 3^4 + 24*v 0^2*v 3*w 0*w 1^2*w 3 - 24*v 0^2*v 3*w 1^3*w 3 - 24*v 0^2*v 3*w 1^2*w 2*w 3 - 24*v 0^2*v 3*w 1^2*w 3^2 + 44*v 0^2*v 3*w 1*w 2^3 - 20*v 0^2*v 3*w 1*w 2^2*w 3 - 108*v 0^2*v 3*w 1*w 2*w 3^2 + 20*v 0^2*v 3*w 1*w 3^3 + 20*v 0^2*v 3*w 2^4 + 84*v 0^2*v 3*w 2^3*w 3 - 92*v 0^2*v 3*w 2^2*w 3^2 - 4*v 0^2*v 3*w 2*w 3^3 + 40*v 0^2*v 3*w 3^4 + 24*v 0*v 2^2*w 1^2*w 2^2 + 48*v 0*v 2*v 3*w 1^2*w 2*w 3 + 24*v 0*v 3^2*w 1^2*w 3^2 - 4*v 2^3*w 0*w 1^3 - 20*v 2^3*w 0*w 1^2*w 2 - 8*v 2^3*w 0*w 1^2*w 3 - 24*v 2^3*w 0*w 1*w 2^2 - 16*v 2^3*w 0*w 1*w 2*w 3 + 12*v 2^3*w 0*w 2^3 + 20*v 2^3*w 0*w 2^2*w 3 + 20*v 2^3*w 0*w 2*w 3^2 + 4*v 2^3*w 0*w 3^3 + 4*v 2^3*w 1^4 + 24*v 2^3*w 1^3*w 2 + 12*v 2^3*w 1^3*w 3 + 44*v 2^3*w 1^2*w 2^2 + 44*v 2^3*w 1^2*w 2*w 3 + 8*v 2^3*w 1^2*w 3^2 + 12*v 2^3*w 1*w 2^3 + 20*v 2^3*w 1*w 2^2*w 3 - 4*v 2^3*w 1*w 2*w 3^2 - 4*v 2^3*w 1*w 3^3 - 12*v 2^3*w 2^4 - 32*v 2^3*w 2^3*w 3 - 40*v 2^3*w 2^2*w 3^2 - 24*v 2^3*w 2*w 3^3 - 4*v 2^3*w 3^4 - 60*v 2^2*v 3*w 0*w 1^2*w 2 - 48*v 2^2*v 3*w 0*w 1^2*w 3 - 36*v 2^2*v 3*w 0*w 1*w 2^2 - 60*v 2^2*v 3*w 0*w 1*w 2*w 3 - 12*v 2^2*v 3*w 0*w 1*w 3^2 + 58*v 2^2*v 3*w 0*w 2^3 + 6*v 2^2*v 3*w 0*w 2^2*w 3 + 62*v 2^2*v 3*w 0*w 2*w 3^2 + 58*v 2^2*v 3*w 0*w 3^3 + 60*v 2^2*v 3*w 1^3*w 2 + 48*v 2^2*v 3*w 1^3*w 3 + 96*v 2^2*v 3*w 1^2*w 2^2 + 168*v 2^2*v 3*w 1^2*w 2*w 3 + 60*v 2^2*v 3*w 1^2*w 3^2 - 22*v 2^2*v 3*w 1*w 2^3 + 90*v 2^2*v 3*w 1*w 2^2*w 3 + 10*v 2^2*v 3*w 1*w 2*w 3^2 - 46*v 2^2*v 3*w 1*w 3^3 - 58*v 2^2*v 3*w 2^4 - 64*v 2^2*v 3*w 2^3*w 3 - 68*v 2^2*v 3*w 2^2*w 3^2 - 120*v 2^2*v 3*w 2*w 3^3 - 58*v 2^2*v 3*w 3^4 - 48*v 2*v 3^2*w 0*w 1^2*w 2 - 60*v 2*v 3^2*w 0*w 1^2*w 3 - 12*v 2*v 3^2*w 0*w 1*w 2^2 - 60*v 2*v 3^2*w 0*w 1*w 2*w 3 - 36*v 2*v 3^2*w 0*w 1*w 3^2 + 58*v 2*v 3^2*w 0*w 2^3 + 62*v 2*v 3^2*w 0*w 2^2*w 3 + 6*v 2*v 3^2*w 0*w 2*w 3^2 + 58*v 2*v 3^2*w 0*w 3^3 + 48*v 2*v 3^2*w 1^3*w 2 + 60*v 2*v 3^2*w 1^3*w 3 + 60*v 2*v 3^2*w 1^2*w 2^2 + 168*v 2*v 3^2*w 1^2*w 2*w 3 + 96*v 2*v 3^2*w 1^2*w 3^2 - 46*v 2*v 3^2*w 1*w 2^3 + 10*v 2*v 3^2*w 1*w 2^2*w 3 + 90*v 2*v 3^2*w 1*w 2*w 3^2 - 22*v 2*v 3^2*w 1*w 3^3 - 58*v 2*v 3^2*w 2^4 - 120*v 2*v 3^2*w 2^3*w 3 - 68*v 2*v 3^2*w 2^2*w 3^2 - 64*v 2*v 3^2*w 2*w 3^3 - 58*v 2*v 3^2*w 3^4 + 8*v 3^3*w 0*w 1^3 - 20*v 3^3*w 0*w 1^2*w 2 - 32*v 3^3*w 0*w 1^2*w 3 - 4*v 3^3*w 0*w 1*w 2*w 3 - 24*v 3^3*w 0*w 1*w 3^2 + 16*v 3^3*w 0*w 2^3 + 32*v 3^3*w 0*w 2^2*w 3 + 32*v 3^3*w 0*w 2*w 3^2 + 24*v 3^3*w 0*w 3^3 - 8*v 3^3*w 1^4 + 12*v 3^3*w 1^3*w 2 + 24*v 3^3*w 1^3*w 3 + 20*v 3^3*w 1^2*w 2^2 + 56*v 3^3*w 1^2*w 2*w 3 + 56*v 3^3*w 1^2*w 3^2 - 16*v 3^3*w 1*w 2^3 - 28*v 3^3*w 1*w 2^2*w 3 - 4*v 3^3*w 1*w 2*w 3^2 - 16*v 3^3*w 2^4 - 48*v 3^3*w 2^3*w 3 - 64*v 3^3*w 2^2*w 3^2 - 56*v 3^3*w 2*w 3^3 - 24*v 3^3*w 3^4) * h2 + (-10*v 2*w 1^2*w 2^3 + 54*v 2*w 1^2*w 2^2*w 3 + 10*v 2*w 1^2*w 2*w 3^2 - 22*v 2*w 1^2*w 3^3 - 32*v 2*w 1*w 2^4 - 16*v 2*w 1*w 2^3*w 3 + 100*v 2*w 1*w 2^2*w 3^2 - 24*v 2*w 1*w 2*w 3^3 - 28*v 2*w 1*w 3^4 + 12*v 2*w 2^5 + 12*v 2*w 2^4*w 3 + 54*v 2*w 2^3*w 3^2 + 90*v 2*w 2^2*w 3^3 - 18*v 2*w 2*w 3^4 - 6*v 2*w 3^5 + 12*v 3*w 1^5 - 22*v 3*w 1^2*w 2^3 + 10*v 3*w 1^2*w 2^2*w 3 + 54*v 3*w 1^2*w 2*w 3^2 - 10*v 3*w 1^2*w 3^3 - 16*v 3*w 1*w 2^4 + 12*v 3*w 1*w 2^3*w 3 + 136*v 3*w 1*w 2^2*w 3^2 + 20*v 3*w 1*w 2*w 3^3 - 20*v 3*w 1*w 3^4 + 6*v 3*w 2^5 + 6*v 3*w 2^4*w 3 + 126*v 3*w 2^3*w 3^2 + 90*v 3*w 2^2*w 3^3 + 36*v 3*w 2*w 3^4 + 24*v 3*w 3^5) * h3 + (4*v 2^3*w 1^3 + 20*v 2^3*w 1^2*w 2 + 8*v 2^3*w 1^2*w 3 + 24*v 2^3*w 1*w 2^2 + 16*v 2^3*w 1*w 2*w 3 - 12*v 2^3*w 2^3 - 20*v 2^3*w 2^2*w 3 - 20*v 2^3*w 2*w 3^2 - 4*v 2^3*w 3^3 + 60*v 2^2*v 3*w 1^2*w 2 + 48*v 2^2*v 3*w 1^2*w 3 + 36*v 2^2*v 3*w 1*w 2^2 + 60*v 2^2*v 3*w 1*w 2*w 3 + 12*v 2^2*v 3*w 1*w 3^2 - 58*v 2^2*v 3*w 2^3 - 6*v 2^2*v 3*w 2^2*w 3 - 62*v 2^2*v 3*w 2*w 3^2 - 58*v 2^2*v 3*w 3^3 + 48*v 2*v 3^2*w 1^2*w 2 + 60*v 2*v 3^2*w 1^2*w 3 + 12*v 2*v 3^2*w 1*w 2^2 + 60*v 2*v 3^2*w 1*w 2*w 3 + 36*v 2*v 3^2*w 1*w 3^2 - 58*v 2*v 3^2*w 2^3 - 62*v 2*v 3^2*w 2^2*w 3 - 6*v 2*v 3^2*w 2*w 3^2 - 58*v 2*v 3^2*w 3^3 - 8*v 3^3*w 1^3 + 20*v 3^3*w 1^2*w 2 + 32*v 3^3*w 1^2*w 3 + 4*v 3^3*w 1*w 2*w 3 + 24*v 3^3*w 1*w 3^2 - 16*v 3^3*w 2^3 - 32*v 3^3*w 2^2*w 3 - 32*v 3^3*w 2*w 3^2 - 24*v 3^3*w 3^3) * h4 + (-20*v 2*w 1*w 2^3 + 108*v 2*w 1*w 2^2*w 3 + 20*v 2*w 1*w 2*w 3^2 - 44*v 2*w 1*w 3^3 - 40*v 2*w 2^4 + 4*v 2*w 2^3*w 3 + 92*v 2*w 2^2*w 3^2 - 84*v 2*w 2*w 3^3 - 20*v 2*w 3^4 - 44*v 3*w 1*w 2^3 + 20*v 3*w 1*w 2^2*w 3 + 108*v 3*w 1*w 2*w 3^2 - 20*v 3*w 1*w 3^3 - 20*v 3*w 2^4 - 84*v 3*w 2^3*w 3 + 92*v 3*w 2^2*w 3^2 + 4*v 3*w 2*w 3^3 - 40*v 3*w 3^4) * h5 + (24*v 0^2*w 0^2*w 1^3 + 8*v 0^2*w 1^5 + 24*v 0^2*w 1^4*w 2 + 24*v 0^2*w 1^4*w 3 + 24*v 0^2*w 1^3*w 2^2 + 48*v 0^2*w 1^3*w 2*w 3 + 24*v 0^2*w 1^3*w 3^2 + 8*v 0^2*w 1^2*w 2^3 + 24*v 0^2*w 1^2*w 2^2*w 3 + 24*v 0^2*w 1^2*w 2*w 3^2 + 8*v 0^2*w 1^2*w 3^3 + 24*v 0*v 1*w 0*w 1^4 + 48*v 0*v 2*w 0*w 1^3*w 2 - 8*v 0*v 2*w 1^5 - 48*v 0*v 2*w 1^4*w 2 - 24*v 0*v 2*w 1^4*w 3 - 72*v 0*v 2*w 1^3*w 2^2 - 96*v 0*v 2*w 1^3*w 2*w 3 - 24*v 0*v 2*w 1^3*w 3^2 - 22*v 0*v 2*w 1^2*w 2^3 - 126*v 0*v 2*w 1^2*w 2^2*w 3 - 58*v 0*v 2*w 1^2*w 2*w 3^2 + 14*v 0*v 2*w 1^2*w 3^3 + 28*v 0*v 2*w 1*w 2^4 - 108*v 0*v 2*w 1*w 2^3*w 3 - 120*v 0*v 2*w 1*w 2^2*w 3^2 + 84*v 0*v 2*w 1*w 2*w 3^3 + 36*v 0*v 2*w 1*w 3^4 + 52*v 0*v 2*w 2^5 + 48*v 0*v 2*w 2^4*w 3 - 42*v 0*v 2*w 2^3*w 3^2 + 82*v 0*v 2*w 2^2*w 3^3 + 86*v 0*v 2*w 2*w 3^4 + 14*v 0*v 2*w 3^5 + 48*v 0*v 3*w 0*w 1^3*w 3 + 4*v 0*v 3*w 1^5 - 24*v 0*v 3*w 1^4*w 2 - 48*v 0*v 3*w 1^4*w 3 - 24*v 0*v 3*w 1^3*w 2^2 - 96*v 0*v 3*w 1^3*w 2*w 3 - 72*v 0*v 3*w 1^3*w 3^2 + 14*v 0*v 3*w 1^2*w 2^3 - 58*v 0*v 3*w 1^2*w 2^2*w 3 - 126*v 0*v 3*w 1^2*w 2*w 3^2 - 22*v 0*v 3*w 1^2*w 3^3 + 48*v 0*v 3*w 1*w 2^4 + 120*v 0*v 3*w 1*w 2^3*w 3 - 84*v 0*v 3*w 1*w 2^2*w 3^2 - 72*v 0*v 3*w 1*w 2*w 3^3 + 40*v 0*v 3*w 1*w 3^4 + 26*v 0*v 3*w 2^5 + 110*v 0*v 3*w 2^4*w 3 + 118*v 0*v 3*w 2^3*w 3^2 - 6*v 0*v 3*w 2^2*w 3^3 + 72*v 0*v 3*w 2*w 3^4 + 64*v 0*v 3*w 3^5 + 8*v 1^2*w 1^5 + 24*v 1*v 2*w 1^4*w 2 + 30*v 1*v 2*w 1^2*w 2^3 - 162*v 1*v 2*w 1^2*w 2^2*w 3 - 30*v 1*v 2*w 1^2*w 2*w 3^2 + 66*v 1*v 2*w 1^2*w 3^3 + 72*v 1*v 2*w 1*w 2^4 + 12*v 1*v 2*w 1*w 2^3*w 3 - 192*v 1*v 2*w 1*w 2^2*w 3^2 + 108*v 1*v 2*w 1*w 2*w 3^3 + 48*v 1*v 2*w 1*w 3^4 - 12*v 1*v 2*w 2^5 - 12*v 1*v 2*w 2^4*w 3 - 54*v 1*v 2*w 2^3*w 3^2 - 90*v 1*v 2*w 2^2*w 3^3 + 18*v 1*v 2*w 2*w 3^4 + 6*v 1*v 2*w 3^5 - 12*v 1*v 3*w 1^5 + 24*v 1*v 3*w 1^4*w 3 + 66*v 1*v 3*w 1^2*w 2^3 - 30*v 1*v 3*w 1^2*w 2^2*w 3 - 162*v 1*v 3*w 1^2*w 2*w 3^2 + 30*v 1*v 3*w 1^2*w 3^3 + 36*v 1*v 3*w 1*w 2^4 + 72*v 1*v 3*w 1*w 2^3*w 3 - 228*v 1*v 3*w 1*w 2^2*w 3^2 - 24*v 1*v 3*w 1*w 2*w 3^3 + 60*v 1*v 3*w 1*w 3^4 - 6*v 1*v 3*w 2^5 - 6*v 1*v 3*w 2^4*w 3 - 126*v 1*v 3*w 2^3*w 3^2 - 90*v 1*v 3*w 2^2*w 3^3 - 36*v 1*v 3*w 2*w 3^4 - 24*v 1*v 3*w 3^5 + 8*v 2^2*w 1^5 + 48*v 2^2*w 1^4*w 2 + 24*v 2^2*w 1^4*w 3 + 120*v 2^2*w 1^3*w 2^2 + 96*v 2^2*w 1^3*w 2*w 3 + 24*v 2^2*w 1^3*w 3^2 + 46*v 2^2*w 1^2*w 2^3 + 150*v 2^2*w 1^2*w 2^2*w 3 + 58*v 2^2*w 1^2*w 2*w 3^2 - 14*v 2^2*w 1^2*w 3^3 - 28*v 2^2*w 1*w 2^4 + 108*v 2^2*w 1*w 2^3*w 3 + 120*v 2^2*w 1*w 2^2*w 3^2 - 84*v 2^2*w 1*w 2*w 3^3 - 36*v 2^2*w 1*w 3^4 - 52*v 2^2*w 2^5 - 48*v 2^2*w 2^4*w 3 + 42*v 2^2*w 2^3*w 3^2 - 82*v 2^2*w 2^2*w 3^3 - 86*v 2^2*w 2*w 3^4 - 14*v 2^2*w 3^5 + 4*v 2*v 3*w 1^5 + 72*v 2*v 3*w 1^4*w 2 + 72*v 2*v 3*w 1^4*w 3 + 96*v 2*v 3*w 1^3*w 2^2 + 288*v 2*v 3*w 1^3*w 2*w 3 + 96*v 2*v 3*w 1^3*w 3^2 + 8*v 2*v 3*w 1^2*w 2^3 + 232*v 2*v 3*w 1^2*w 2^2*w 3 + 232*v 2*v 3*w 1^2*w 2*w 3^2 + 8*v 2*v 3*w 1^2*w 3^3 - 76*v 2*v 3*w 1*w 2^4 - 12*v 2*v 3*w 1*w 2^3*w 3 + 204*v 2*v 3*w 1*w 2^2*w 3^2 - 12*v 2*v 3*w 1*w 2*w 3^3 - 76*v 2*v 3*w 1*w 3^4 - 78*v 2*v 3*w 2^5 - 158*v 2*v 3*w 2^4*w 3 - 76*v 2*v 3*w 2^3*w 3^2 - 76*v 2*v 3*w 2^2*w 3^3 - 158*v 2*v 3*w 2*w 3^4 - 78*v 2*v 3*w 3^5 - 4*v 3^2*w 1^5 + 24*v 3^2*w 1^4*w 2 + 48*v 3^2*w 1^4*w 3 + 24*v 3^2*w 1^3*w 2^2 + 96*v 3^2*w 1^3*w 2*w 3 + 120*v 3^2*w 1^3*w 3^2 - 14*v 3^2*w 1^2*w 2^3 + 58*v 3^2*w 1^2*w 2^2*w 3 + 150*v 3^2*w 1^2*w 2*w 3^2 + 46*v 3^2*w 1^2*w 3^3 - 48*v 3^2*w 1*w 2^4 - 120*v 3^2*w 1*w 2^3*w 3 + 84*v 3^2*w 1*w 2^2*w 3^2 + 72*v 3^2*w 1*w 2*w 3^3 - 40*v 3^2*w 1*w 3^4 - 26*v 3^2*w 2^5 - 110*v 3^2*w 2^4*w 3 - 118*v 3^2*w 2^3*w 3^2 + 6*v 3^2*w 2^2*w 3^3 - 72*v 3^2*w 2*w 3^4 - 64*v 3^2*w 3^5) * hk

set_option maxRecDepth 20000 in
theorem F1_w2 (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0)
    (h4 : ip w w = 0) (h5 : t3 v v w = 0) (hq : 3 * t4 v v w w = ip v w ^ 2) (hk : v 2 = 0) :
    8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * w 2 ^ 2) = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4 h5 hq
  linear_combination (-8*v 0^2*w 1^3*w 2^2 - 24*v 0^2*w 1^2*w 2^3 - 24*v 0^2*w 1^2*w 2^2*w 3 - 24*v 0^2*w 1*w 2^4 - 48*v 0^2*w 1*w 2^3*w 3 - 24*v 0^2*w 1*w 2^2*w 3^2 - 8*v 0^2*w 2^5 - 24*v 0^2*w 2^4*w 3 - 24*v 0^2*w 2^3*w 3^2 - 8*v 0^2*w 2^2*w 3^3 + 32*v 0*v 1*w 1^3*w 2^2 + 32*v 0*v 1*w 1^2*w 2^3 - 96*v 0*v 1*w 1^2*w 2^2*w 3 - 216*v 0*v 1*w 1^2*w 2*w 3^2 - 216*v 0*v 1*w 1^2*w 3^3 + 32*v 0*v 1*w 1*w 2^4 - 96*v 0*v 1*w 1*w 2^3*w 3 - 312*v 0*v 1*w 1*w 2^2*w 3^2 - 432*v 0*v 1*w 1*w 2*w 3^3 - 216*v 0*v 1*w 1*w 3^4 + 10*v 0*v 1*w 2^5 - 18*v 0*v 1*w 2^4*w 3 - 104*v 0*v 1*w 2^3*w 3^2 - 184*v 0*v 1*w 2^2*w 3^3 - 162*v 0*v 1*w 2*w 3^4 - 54*v 0*v 1*w 3^5 - 40*v 0*v 3*w 1^3*w 2^2 + 4*v 0*v 3*w 1^2*w 2^3 - 36*v 0*v 3*w 1^2*w 2^2*w 3 - 108*v 0*v 3*w 1^2*w 2*w 3^2 - 108*v 0*v 3*w 1^2*w 3^3 - 18*v 0*v 3*w 1*w 2^4 - 72*v 0*v 3*w 1*w 2^3*w 3 - 360*v 0*v 3*w 1*w 2^2*w 3^2 - 432*v 0*v 3*w 1*w 2*w 3^3 - 270*v 0*v 3*w 1*w 3^4 + 28*v 0*v 3*w 2^5 - 34*v 0*v 3*w 2^4*w 3 - 304*v 0*v 3*w 2^3*w 3^2 - 592*v 0*v 3*w 2^2*w 3^3 - 540*v 0*v 3*w 2*w 3^4 - 270*v 0*v 3*w 3^5 - 56*v 1^2*w 1^3*w 2^2 - 56*v 1^2*w 1^2*w 2^3 + 72*v 1^2*w 1^2*w 2^2*w 3 + 216*v 1^2*w 1^2*w 2*w 3^2 + 216*v 1^2*w 1^2*w 3^3 - 32*v 1^2*w 1*w 2^4 + 96*v 1^2*w 1*w 2^3*w 3 + 312*v 1^2*w 1*w 2^2*w 3^2 + 432*v 1^2*w 1*w 2*w 3^3 + 216*v 1^2*w 1*w 3^4 - 10*v 1^2*w 2^5 + 18*v 1^2*w 2^4*w 3 + 104*v 1^2*w 2^3*w 3^2 + 184*v 1^2*w 2^2*w 3^3 + 162*v 1^2*w 2*w 3^4 + 54*v 1^2*w 3^5 + 8*v 1*v 3*w 1^3*w 2^2 - 36*v 1*v 3*w 1^2*w 2^3 + 84*v 1*v 3*w 1^2*w 2^2*w 3 + 324*v 1*v 3*w 1^2*w 2*w 3^2 + 324*v 1*v 3*w 1^2*w 3^3 - 14*v 1*v 3*w 1*w 2^4 + 120*v 1*v 3*w 1*w 2^3*w 3 + 624*v 1*v 3*w 1*w 2^2*w 3^2 + 864*v 1*v 3*w 1*w 2*w 3^3 + 486*v 1*v 3*w 1*w 3^4 - 38*v 1*v 3*w 2^5 + 52*v 1*v 3*w 2^4*w 3 + 408*v 1*v 3*w 2^3*w 3^2 + 776*v 1*v 3*w 2^2*w 3^3 + 702*v 1*v 3*w 2*w 3^4 + 324*v 1*v 3*w 3^5 + 40*v 3^2*w 1^3*w 2^2 - 4*v 3^2*w 1^2*w 2^3 + 36*v 3^2*w 1^2*w 2^2*w 3 + 108*v 3^2*w 1^2*w 2*w 3^2 + 108*v 3^2*w 1^2*w 3^3 + 18*v 3^2*w 1*w 2^4 + 72*v 3^2*w 1*w 2^3*w 3 + 336*v 3^2*w 1*w 2^2*w 3^2 + 432*v 3^2*w 1*w 2*w 3^3 + 270*v 3^2*w 1*w 3^4 - 28*v 3^2*w 2^5 + 34*v 3^2*w 2^4*w 3 + 280*v 3^2*w 2^3*w 3^2 + 568*v 3^2*w 2^2*w 3^3 + 540*v 3^2*w 2*w 3^4 + 270*v 3^2*w 3^5) * h1 + (8*v 0^3*w 0^2*w 2^2 - 8*v 0^3*w 0*w 1*w 2^2 - 8*v 0^3*w 0*w 2^3 - 8*v 0^3*w 0*w 2^2*w 3 + 8*v 0^3*w 1^2*w 2^2 + 16*v 0^3*w 1*w 2^3 + 16*v 0^3*w 1*w 2^2*w 3 + 8*v 0^3*w 2^4 + 16*v 0^3*w 2^3*w 3 + 8*v 0^3*w 2^2*w 3^2 + 24*v 0^2*v 1*w 0*w 1*w 2^2 - 24*v 0^2*v 1*w 1^2*w 2^2 + 16*v 0^2*v 1*w 1*w 2^3 + 144*v 0^2*v 1*w 1*w 2^2*w 3 + 216*v 0^2*v 1*w 1*w 2*w 3^2 + 216*v 0^2*v 1*w 1*w 3^3 + 20*v 0^2*v 1*w 2^4 + 104*v 0^2*v 1*w 2^3*w 3 + 192*v 0^2*v 1*w 2^2*w 3^2 + 216*v 0^2*v 1*w 2*w 3^3 + 108*v 0^2*v 1*w 3^4 + 24*v 0^2*v 3*w 0*w 2^2*w 3 + 20*v 0^2*v 3*w 1*w 2^3 + 60*v 0^2*v 3*w 1*w 2^2*w 3 + 108*v 0^2*v 3*w 1*w 2*w 3^2 + 108*v 0^2*v 3*w 1*w 3^3 + 44*v 0^2*v 3*w 2^4 + 148*v 0^2*v 3*w 2^3*w 3 + 324*v 0^2*v 3*w 2^2*w 3^2 + 324*v 0^2*v 3*w 2*w 3^3 + 216*v 0^2*v 3*w 3^4 + 24*v 0*v 1^2*w 1^2*w 2^2 + 48*v 0*v 1*v 3*w 1*w 2^2*w 3 + 24*v 0*v 3^2*w 2^2*w 3^2 - 32*v 1^3*w 0*w 1*w 2^2 - 16*v 1^3*w 0*w 2^3 - 16*v 1^3*w 0*w 2^2*w 3 + 32*v 1^3*w 1^2*w 2^2 + 48*v 1^3*w 1*w 2^3 + 48*v 1^3*w 1*w 2^2*w 3 + 16*v 1^3*w 2^4 + 32*v 1^3*w 2^3*w 3 + 16*v 1^3*w 2^2*w 3^2 - 56*v 1^2*v 3*w 0*w 2^3 + 24*v 1^2*v 3*w 0*w 2^2*w 3 + 216*v 1^2*v 3*w 0*w 2*w 3^2 + 216*v 1^2*v 3*w 0*w 3^3 + 56*v 1^2*v 3*w 1*w 2^3 - 24*v 1^2*v 3*w 1*w 2^2*w 3 - 216*v 1^2*v 3*w 1*w 2*w 3^2 - 216*v 1^2*v 3*w 1*w 3^3 + 56*v 1^2*v 3*w 2^4 + 32*v 1^2*v 3*w 2^3*w 3 - 240*v 1^2*v 3*w 2^2*w 3^2 - 432*v 1^2*v 3*w 2*w 3^3 - 216*v 1^2*v 3*w 3^4 + 24*v 1*v 3^2*w 0*w 1*w 2^2 - 44*v 1*v 3^2*w 0*w 2^3 + 36*v 1*v 3^2*w 0*w 2^2*w 3 + 216*v 1*v 3^2*w 0*w 2*w 3^2 + 216*v 1*v 3^2*w 0*w 3^3 - 24*v 1*v 3^2*w 1^2*w 2^2 + 20*v 1*v 3^2*w 1*w 2^3 - 60*v 1*v 3^2*w 1*w 2^2*w 3 - 216*v 1*v 3^2*w 1*w 2*w 3^2 - 216*v 1*v 3^2*w 1*w 3^3 + 44*v 1*v 3^2*w 2^4 + 8*v 1*v 3^2*w 2^3*w 3 - 252*v 1*v 3^2*w 2^2*w 3^2 - 432*v 1*v 3^2*w 2*w 3^3 - 216*v 1*v 3^2*w 3^4 + 44*v 3^3*w 0*w 1*w 2^2 - 46*v 3^3*w 0*w 2^3 - 26*v 3^3*w 0*w 2^2*w 3 + 54*v 3^3*w 0*w 2*w 3^2 + 54*v 3^3*w 0*w 3^3 - 44*v 3^3*w 1^2*w 2^2 + 2*v 3^3*w 1*w 2^3 - 18*v 3^3*w 1*w 2^2*w 3 - 54*v 3^3*w 1*w 2*w 3^2 - 54*v 3^3*w 1*w 3^3 + 46*v 3^3*w 2^4 + 72*v 3^3*w 2^3*w 3 - 28*v 3^3*w 2^2*w 3^2 - 108*v 3^3*w 2*w 3^3 - 54*v 3^3*w 3^4) * h2 + (-44*v 1*w 1*w 2^4 - 120*v 1*w 1*w 2^3*w 3 - 216*v 1*w 1*w 2^2*w 3^2 - 216*v 1*w 1*w 2*w 3^3 - 108*v 1*w 1*w 3^4 - 22*v 1*w 2^5 - 82*v 1*w 2^4*w 3 - 168*v 1*w 2^3*w 3^2 - 216*v 1*w 2^2*w 3^3 - 162*v 1*w 2*w 3^4 - 54*v 1*w 3^5 + 48*v 3*w 1^3*w 2^2 - 22*v 3*w 1*w 2^4 - 108*v 3*w 1*w 2^3*w 3 - 108*v 3*w 1*w 2^2*w 3^2 - 108*v 3*w 1*w 2*w 3^3 - 54*v 3*w 1*w 3^4 - 64*v 3*w 2^5 - 134*v 3*w 2^4*w 3 - 144*v 3*w 2^3*w 3^2 - 48*v 3*w 2^2*w 3^3 + 54*v 3*w 3^5) * h3 + (32*v 1^3*w 1*w 2^2 + 16*v 1^3*w 2^3 + 16*v 1^3*w 2^2*w 3 + 56*v 1^2*v 3*w 2^3 - 24*v 1^2*v 3*w 2^2*w 3 - 216*v 1^2*v 3*w 2*w 3^2 - 216*v 1^2*v 3*w 3^3 - 24*v 1*v 3^2*w 1*w 2^2 + 44*v 1*v 3^2*w 2^3 - 36*v 1*v 3^2*w 2^2*w 3 - 216*v 1*v 3^2*w 2*w 3^2 - 216*v 1*v 3^2*w 3^3 - 44*v 3^3*w 1*w 2^2 + 46*v 3^3*w 2^3 + 26*v 3^3*w 2^2*w 3 - 54*v 3^3*w 2*w 3^2 - 54*v 3^3*w 3^3) * h4 + (-40*v 1*w 1*w 2^3 - 168*v 1*w 1*w 2^2*w 3 - 216*v 1*w 1*w 2*w 3^2 - 216*v 1*w 1*w 3^3 - 20*v 1*w 2^4 - 104*v 1*w 2^3*w 3 - 192*v 1*w 2^2*w 3^2 - 216*v 1*w 2*w 3^3 - 108*v 1*w 3^4 - 20*v 3*w 1*w 2^3 - 84*v 3*w 1*w 2^2*w 3 - 108*v 3*w 1*w 2*w 3^2 - 108*v 3*w 1*w 3^3 - 44*v 3*w 2^4 - 172*v 3*w 2^3*w 3 - 348*v 3*w 2^2*w 3^2 - 324*v 3*w 2*w 3^3 - 216*v 3*w 3^4) * h5 + (24*v 0^2*w 0^2*w 2^3 + 8*v 0^2*w 1^3*w 2^2 + 24*v 0^2*w 1^2*w 2^3 + 24*v 0^2*w 1^2*w 2^2*w 3 + 24*v 0^2*w 1*w 2^4 + 48*v 0^2*w 1*w 2^3*w 3 + 24*v 0^2*w 1*w 2^2*w 3^2 + 8*v 0^2*w 2^5 + 24*v 0^2*w 2^4*w 3 + 24*v 0^2*w 2^3*w 3^2 + 8*v 0^2*w 2^2*w 3^3 + 48*v 0*v 1*w 0*w 1*w 2^3 - 32*v 0*v 1*w 1^3*w 2^2 - 32*v 0*v 1*w 1^2*w 2^3 + 96*v 0*v 1*w 1^2*w 2^2*w 3 + 216*v 0*v 1*w 1^2*w 2*w 3^2 + 216*v 0*v 1*w 1^2*w 3^3 - 32*v 0*v 1*w 1*w 2^4 + 96*v 0*v 1*w 1*w 2^3*w 3 + 312*v 0*v 1*w 1*w 2^2*w 3^2 + 432*v 0*v 1*w 1*w 2*w 3^3 + 216*v 0*v 1*w 1*w 3^4 - 10*v 0*v 1*w 2^5 + 18*v 0*v 1*w 2^4*w 3 + 104*v 0*v 1*w 2^3*w 3^2 + 184*v 0*v 1*w 2^2*w 3^3 + 162*v 0*v 1*w 2*w 3^4 + 54*v 0*v 1*w 3^5 + 24*v 0*v 2*w 0*w 2^4 + 48*v 0*v 3*w 0*w 2^3*w 3 + 40*v 0*v 3*w 1^3*w 2^2 - 4*v 0*v 3*w 1^2*w 2^3 + 36*v 0*v 3*w 1^2*w 2^2*w 3 + 108*v 0*v 3*w 1^2*w 2*w 3^2 + 108*v 0*v 3*w 1^2*w 3^3 + 18*v 0*v 3*w 1*w 2^4 + 72*v 0*v 3*w 1*w 2^3*w 3 + 360*v 0*v 3*w 1*w 2^2*w 3^2 + 432*v 0*v 3*w 1*w 2*w 3^3 + 270*v 0*v 3*w 1*w 3^4 - 28*v 0*v 3*w 2^5 + 34*v 0*v 3*w 2^4*w 3 + 304*v 0*v 3*w 2^3*w 3^2 + 592*v 0*v 3*w 2^2*w 3^3 + 540*v 0*v 3*w 2*w 3^4 + 270*v 0*v 3*w 3^5 + 56*v 1^2*w 1^3*w 2^2 + 80*v 1^2*w 1^2*w 2^3 - 72*v 1^2*w 1^2*w 2^2*w 3 - 216*v 1^2*w 1^2*w 2*w 3^2 - 216*v 1^2*w 1^2*w 3^3 + 32*v 1^2*w 1*w 2^4 - 96*v 1^2*w 1*w 2^3*w 3 - 312*v 1^2*w 1*w 2^2*w 3^2 - 432*v 1^2*w 1*w 2*w 3^3 - 216*v 1^2*w 1*w 3^4 + 10*v 1^2*w 2^5 - 18*v 1^2*w 2^4*w 3 - 104*v 1^2*w 2^3*w 3^2 - 184*v 1^2*w 2^2*w 3^3 - 162*v 1^2*w 2*w 3^4 - 54*v 1^2*w 3^5 + 108*v 1*v 2*w 1*w 2^4 + 288*v 1*v 2*w 1*w 2^3*w 3 + 432*v 1*v 2*w 1*w 2^2*w 3^2 + 432*v 1*v 2*w 1*w 2*w 3^3 + 108*v 1*v 2*w 1*w 3^4 + 42*v 1*v 2*w 2^5 + 186*v 1*v 2*w 2^4*w 3 + 360*v 1*v 2*w 2^3*w 3^2 + 432*v 1*v 2*w 2^2*w 3^3 + 270*v 1*v 2*w 2*w 3^4 + 54*v 1*v 2*w 3^5 - 8*v 1*v 3*w 1^3*w 2^2 + 36*v 1*v 3*w 1^2*w 2^3 - 84*v 1*v 3*w 1^2*w 2^2*w 3 - 324*v 1*v 3*w 1^2*w 2*w 3^2 - 324*v 1*v 3*w 1^2*w 3^3 + 14*v 1*v 3*w 1*w 2^4 - 72*v 1*v 3*w 1*w 2^3*w 3 - 624*v 1*v 3*w 1*w 2^2*w 3^2 - 864*v 1*v 3*w 1*w 2*w 3^3 - 486*v 1*v 3*w 1*w 3^4 + 38*v 1*v 3*w 2^5 - 52*v 1*v 3*w 2^4*w 3 - 408*v 1*v 3*w 2^3*w 3^2 - 776*v 1*v 3*w 2^2*w 3^3 - 702*v 1*v 3*w 2*w 3^4 - 324*v 1*v 3*w 3^5 + 8*v 2^2*w 2^5 - 48*v 2*v 3*w 1^3*w 2^2 + 42*v 2*v 3*w 1*w 2^4 + 192*v 2*v 3*w 1*w 2^3*w 3 + 216*v 2*v 3*w 1*w 2^2*w 3^2 + 216*v 2*v 3*w 1*w 2*w 3^3 + 54*v 2*v 3*w 1*w 3^4 + 108*v 2*v 3*w 2^5 + 330*v 2*v 3*w 2^4*w 3 + 492*v 2*v 3*w 2^3*w 3^2 + 372*v 2*v 3*w 2^2*w 3^3 + 216*v 2*v 3*w 2*w 3^4 - 54*v 2*v 3*w 3^5 - 40*v 3^2*w 1^3*w 2^2 + 4*v 3^2*w 1^2*w 2^3 - 36*v 3^2*w 1^2*w 2^2*w 3 - 108*v 3^2*w 1^2*w 2*w 3^2 - 108*v 3^2*w 1^2*w 3^3 - 18*v 3^2*w 1*w 2^4 - 72*v 3^2*w 1*w 2^3*w 3 - 336*v 3^2*w 1*w 2^2*w 3^2 - 432*v 3^2*w 1*w 2*w 3^3 - 270*v 3^2*w 1*w 3^4 + 28*v 3^2*w 2^5 - 34*v 3^2*w 2^4*w 3 - 256*v 3^2*w 2^3*w 3^2 - 568*v 3^2*w 2^2*w 3^3 - 540*v 3^2*w 2*w 3^4 - 270*v 3^2*w 3^5) * hk

set_option maxRecDepth 20000 in
theorem F1_w3 (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0)
    (h4 : ip w w = 0) (h5 : t3 v v w = 0) (hq : 3 * t4 v v w w = ip v w ^ 2) (hk : v 3 = 0) :
    8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * w 3 ^ 2) = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4 h5 hq
  linear_combination (-8*v 0^2*w 1^3*w 3^2 - 24*v 0^2*w 1^2*w 2*w 3^2 - 24*v 0^2*w 1^2*w 3^3 - 24*v 0^2*w 1*w 2^2*w 3^2 - 48*v 0^2*w 1*w 2*w 3^3 - 24*v 0^2*w 1*w 3^4 - 8*v 0^2*w 2^3*w 3^2 - 24*v 0^2*w 2^2*w 3^3 - 24*v 0^2*w 2*w 3^4 - 8*v 0^2*w 3^5 + 32*v 0*v 1*w 1^3*w 3^2 - 216*v 0*v 1*w 1^2*w 2^3 - 216*v 0*v 1*w 1^2*w 2^2*w 3 - 96*v 0*v 1*w 1^2*w 2*w 3^2 + 32*v 0*v 1*w 1^2*w 3^3 - 216*v 0*v 1*w 1*w 2^4 - 432*v 0*v 1*w 1*w 2^3*w 3 - 312*v 0*v 1*w 1*w 2^2*w 3^2 - 96*v 0*v 1*w 1*w 2*w 3^3 + 32*v 0*v 1*w 1*w 3^4 - 54*v 0*v 1*w 2^5 - 162*v 0*v 1*w 2^4*w 3 - 184*v 0*v 1*w 2^3*w 3^2 - 104*v 0*v 1*w 2^2*w 3^3 - 18*v 0*v 1*w 2*w 3^4 + 10*v 0*v 1*w 3^5 - 40*v 0*v 2*w 1^3*w 3^2 - 108*v 0*v 2*w 1^2*w 2^3 - 108*v 0*v 2*w 1^2*w 2^2*w 3 - 36*v 0*v 2*w 1^2*w 2*w 3^2 + 4*v 0*v 2*w 1^2*w 3^3 - 270*v 0*v 2*w 1*w 2^4 - 432*v 0*v 2*w 1*w 2^3*w 3 - 360*v 0*v 2*w 1*w 2^2*w 3^2 - 72*v 0*v 2*w 1*w 2*w 3^3 - 18*v 0*v 2*w 1*w 3^4 - 270*v 0*v 2*w 2^5 - 540*v 0*v 2*w 2^4*w 3 - 592*v 0*v 2*w 2^3*w 3^2 - 304*v 0*v 2*w 2^2*w 3^3 - 34*v 0*v 2*w 2*w 3^4 + 28*v 0*v 2*w 3^5 - 56*v 1^2*w 1^3*w 3^2 + 216*v 1^2*w 1^2*w 2^3 + 216*v 1^2*w 1^2*w 2^2*w 3 + 72*v 1^2*w 1^2*w 2*w 3^2 - 56*v 1^2*w 1^2*w 3^3 + 216*v 1^2*w 1*w 2^4 + 432*v 1^2*w 1*w 2^3*w 3 + 312*v 1^2*w 1*w 2^2*w 3^2 + 96*v 1^2*w 1*w 2*w 3^3 - 32*v 1^2*w 1*w 3^4 + 54*v 1^2*w 2^5 + 162*v 1^2*w 2^4*w 3 + 184*v 1^2*w 2^3*w 3^2 + 104*v 1^2*w 2^2*w 3^3 + 18*v 1^2*w 2*w 3^4 - 10*v 1^2*w 3^5 + 8*v 1*v 2*w 1^3*w 3^2 + 324*v 1*v 2*w 1^2*w 2^3 + 324*v 1*v 2*w 1^2*w 2^2*w 3 + 84*v 1*v 2*w 1^2*w 2*w 3^2 - 36*v 1*v 2*w 1^2*w 3^3 + 486*v 1*v 2*w 1*w 2^4 + 864*v 1*v 2*w 1*w 2^3*w 3 + 624*v 1*v 2*w 1*w 2^2*w 3^2 + 120*v 1*v 2*w 1*w 2*w 3^3 - 14*v 1*v 2*w 1*w 3^4 + 324*v 1*v 2*w 2^5 + 702*v 1*v 2*w 2^4*w 3 + 776*v 1*v 2*w 2^3*w 3^2 + 408*v 1*v 2*w 2^2*w 3^3 + 52*v 1*v 2*w 2*w 3^4 - 38*v 1*v 2*w 3^5 + 40*v 2^2*w 1^3*w 3^2 + 108*v 2^2*w 1^2*w 2^3 + 108*v 2^2*w 1^2*w 2^2*w 3 + 36*v 2^2*w 1^2*w 2*w 3^2 - 4*v 2^2*w 1^2*w 3^3 + 270*v 2^2*w 1*w 2^4 + 432*v 2^2*w 1*w 2^3*w 3 + 336*v 2^2*w 1*w 2^2*w 3^2 + 72*v 2^2*w 1*w 2*w 3^3 + 18*v 2^2*w 1*w 3^4 + 270*v 2^2*w 2^5 + 540*v 2^2*w 2^4*w 3 + 568*v 2^2*w 2^3*w 3^2 + 280*v 2^2*w 2^2*w 3^3 + 34*v 2^2*w 2*w 3^4 - 28*v 2^2*w 3^5) * h1 + (8*v 0^3*w 0^2*w 3^2 - 8*v 0^3*w 0*w 1*w 3^2 - 8*v 0^3*w 0*w 2*w 3^2 - 8*v 0^3*w 0*w 3^3 + 8*v 0^3*w 1^2*w 3^2 + 16*v 0^3*w 1*w 2*w 3^2 + 16*v 0^3*w 1*w 3^3 + 8*v 0^3*w 2^2*w 3^2 + 16*v 0^3*w 2*w 3^3 + 8*v 0^3*w 3^4 + 24*v 0^2*v 1*w 0*w 1*w 3^2 - 24*v 0^2*v 1*w 1^2*w 3^2 + 216*v 0^2*v 1*w 1*w 2^3 + 216*v 0^2*v 1*w 1*w 2^2*w 3 + 144*v 0^2*v 1*w 1*w 2*w 3^2 + 16*v 0^2*v 1*w 1*w 3^3 + 108*v 0^2*v 1*w 2^4 + 216*v 0^2*v 1*w 2^3*w 3 + 192*v 0^2*v 1*w 2^2*w 3^2 + 104*v 0^2*v 1*w 2*w 3^3 + 20*v 0^2*v 1*w 3^4 + 24*v 0^2*v 2*w 0*w 2*w 3^2 + 108*v 0^2*v 2*w 1*w 2^3 + 108*v 0^2*v 2*w 1*w 2^2*w 3 + 60*v 0^2*v 2*w 1*w 2*w 3^2 + 20*v 0^2*v 2*w 1*w 3^3 + 216*v 0^2*v 2*w 2^4 + 324*v 0^2*v 2*w 2^3*w 3 + 324*v 0^2*v 2*w 2^2*w 3^2 + 148*v 0^2*v 2*w 2*w 3^3 + 44*v 0^2*v 2*w 3^4 + 24*v 0*v 1^2*w 1^2*w 3^2 + 48*v 0*v 1*v 2*w 1*w 2*w 3^2 + 24*v 0*v 2^2*w 2^2*w 3^2 - 32*v 1^3*w 0*w 1*w 3^2 - 16*v 1^3*w 0*w 2*w 3^2 - 16*v 1^3*w 0*w 3^3 + 32*v 1^3*w 1^2*w 3^2 + 48*v 1^3*w 1*w 2*w 3^2 + 48*v 1^3*w 1*w 3^3 + 16*v 1^3*w 2^2*w 3^2 + 32*v 1^3*w 2*w 3^3 + 16*v 1^3*w 3^4 + 216*v 1^2*v 2*w 0*w 2^3 + 216*v 1^2*v 2*w 0*w 2^2*w 3 + 24*v 1^2*v 2*w 0*w 2*w 3^2 - 56*v 1^2*v 2*w 0*w 3^3 - 216*v 1^2*v 2*w 1*w 2^3 - 216*v 1^2*v 2*w 1*w 2^2*w 3 - 24*v 1^2*v 2*w 1*w 2*w 3^2 + 56*v 1^2*v 2*w 1*w 3^3 - 216*v 1^2*v 2*w 2^4 - 432*v 1^2*v 2*w 2^3*w 3 - 240*v 1^2*v 2*w 2^2*w 3^2 + 32*v 1^2*v 2*w 2*w 3^3 + 56*v 1^2*v 2*w 3^4 + 24*v 1*v 2^2*w 0*w 1*w 3^2 + 216*v 1*v 2^2*w 0*w 2^3 + 216*v 1*v 2^2*w 0*w 2^2*w 3 + 36*v 1*v 2^2*w 0*w 2*w 3^2 - 44*v 1*v 2^2*w 0*w 3^3 - 24*v 1*v 2^2*w 1^2*w 3^2 - 216*v 1*v 2^2*w 1*w 2^3 - 216*v 1*v 2^2*w 1*w 2^2*w 3 - 60*v 1*v 2^2*w 1*w 2*w 3^2 + 20*v 1*v 2^2*w 1*w 3^3 - 216*v 1*v 2^2*w 2^4 - 432*v 1*v 2^2*w 2^3*w 3 - 252*v 1*v 2^2*w 2^2*w 3^2 + 8*v 1*v 2^2*w 2*w 3^3 + 44*v 1*v 2^2*w 3^4 + 44*v 2^3*w 0*w 1*w 3^2 + 54*v 2^3*w 0*w 2^3 + 54*v 2^3*w 0*w 2^2*w 3 - 26*v 2^3*w 0*w 2*w 3^2 - 46*v 2^3*w 0*w 3^3 - 44*v 2^3*w 1^2*w 3^2 - 54*v 2^3*w 1*w 2^3 - 54*v 2^3*w 1*w 2^2*w 3 - 18*v 2^3*w 1*w 2*w 3^2 + 2*v 2^3*w 1*w 3^3 - 54*v 2^3*w 2^4 - 108*v 2^3*w 2^3*w 3 - 28*v 2^3*w 2^2*w 3^2 + 72*v 2^3*w 2*w 3^3 + 46*v 2^3*w 3^4) * h2 + (-108*v 1*w 1*w 2^4 - 216*v 1*w 1*w 2^3*w 3 - 216*v 1*w 1*w 2^2*w 3^2 - 120*v 1*w 1*w 2*w 3^3 - 44*v 1*w 1*w 3^4 - 54*v 1*w 2^5 - 162*v 1*w 2^4*w 3 - 216*v 1*w 2^3*w 3^2 - 168*v 1*w 2^2*w 3^3 - 82*v 1*w 2*w 3^4 - 22*v 1*w 3^5 + 48*v 2*w 1^3*w 3^2 - 54*v 2*w 1*w 2^4 - 108*v 2*w 1*w 2^3*w 3 - 108*v 2*w 1*w 2^2*w 3^2 - 108*v 2*w 1*w 2*w 3^3 - 22*v 2*w 1*w 3^4 + 54*v 2*w 2^5 - 48*v 2*w 2^3*w 3^2 - 144*v 2*w 2^2*w 3^3 - 134*v 2*w 2*w 3^4 - 64*v 2*w 3^5) * h3 + (32*v 1^3*w 1*w 3^2 + 16*v 1^3*w 2*w 3^2 + 16*v 1^3*w 3^3 - 216*v 1^2*v 2*w 2^3 - 216*v 1^2*v 2*w 2^2*w 3 - 24*v 1^2*v 2*w 2*w 3^2 + 56*v 1^2*v 2*w 3^3 - 24*v 1*v 2^2*w 1*w 3^2 - 216*v 1*v 2^2*w 2^3 - 216*v 1*v 2^2*w 2^2*w 3 - 36*v 1*v 2^2*w 2*w 3^2 + 44*v 1*v 2^2*w 3^3 - 44*v 2^3*w 1*w 3^2 - 54*v 2^3*w 2^3 - 54*v 2^3*w 2^2*w 3 + 26*v 2^3*w 2*w 3^2 + 46*v 2^3*w 3^3) * h4 + (-216*v 1*w 1*w 2^3 - 216*v 1*w 1*w 2^2*w 3 - 168*v 1*w 1*w 2*w 3^2 - 40*v 1*w 1*w 3^3 - 108*v 1*w 2^4 - 216*v 1*w 2^3*w 3 - 192*v 1*w 2^2*w 3^2 - 104*v 1*w 2*w 3^3 - 20*v 1*w 3^4 - 108*v 2*w 1*w 2^3 - 108*v 2*w 1*w 2^2*w 3 - 84*v 2*w 1*w 2*w 3^2 - 20*v 2*w 1*w 3^3 - 216*v 2*w 2^4 - 324*v 2*w 2^3*w 3 - 348*v 2*w 2^2*w 3^2 - 172*v 2*w 2*w 3^3 - 44*v 2*w 3^4) * h5 + (24*v 0^2*w 0^2*w 3^3 + 8*v 0^2*w 1^3*w 3^2 + 24*v 0^2*w 1^2*w 2*w 3^2 + 24*v 0^2*w 1^2*w 3^3 + 24*v 0^2*w 1*w 2^2*w 3^2 + 48*v 0^2*w 1*w 2*w 3^3 + 24*v 0^2*w 1*w 3^4 + 8*v 0^2*w 2^3*w 3^2 + 24*v 0^2*w 2^2*w 3^3 + 24*v 0^2*w 2*w 3^4 + 8*v 0^2*w 3^5 + 48*v 0*v 1*w 0*w 1*w 3^3 - 32*v 0*v 1*w 1^3*w 3^2 + 216*v 0*v 1*w 1^2*w 2^3 + 216*v 0*v 1*w 1^2*w 2^2*w 3 + 96*v 0*v 1*w 1^2*w 2*w 3^2 - 32*v 0*v 1*w 1^2*w 3^3 + 216*v 0*v 1*w 1*w 2^4 + 432*v 0*v 1*w 1*w 2^3*w 3 + 312*v 0*v 1*w 1*w 2^2*w 3^2 + 96*v 0*v 1*w 1*w 2*w 3^3 - 32*v 0*v 1*w 1*w 3^4 + 54*v 0*v 1*w 2^5 + 162*v 0*v 1*w 2^4*w 3 + 184*v 0*v 1*w 2^3*w 3^2 + 104*v 0*v 1*w 2^2*w 3^3 + 18*v 0*v 1*w 2*w 3^4 - 10*v 0*v 1*w 3^5 + 48*v 0*v 2*w 0*w 2*w 3^3 + 40*v 0*v 2*w 1^3*w 3^2 + 108*v 0*v 2*w 1^2*w 2^3 + 108*v 0*v 2*w 1^2*w 2^2*w 3 + 36*v 0*v 2*w 1^2*w 2*w 3^2 - 4*v 0*v 2*w 1^2*w 3^3 + 270*v 0*v 2*w 1*w 2^4 + 432*v 0*v 2*w 1*w 2^3*w 3 + 360*v 0*v 2*w 1*w 2^2*w 3^2 + 72*v 0*v 2*w 1*w 2*w 3^3 + 18*v 0*v 2*w 1*w 3^4 + 270*v 0*v 2*w 2^5 + 540*v 0*v 2*w 2^4*w 3 + 592*v 0*v 2*w 2^3*w 3^2 + 304*v 0*v 2*w 2^2*w 3^3 + 34*v 0*v 2*w 2*w 3^4 - 28*v 0*v 2*w 3^5 + 24*v 0*v 3*w 0*w 3^4 + 56*v 1^2*w 1^3*w 3^2 - 216*v 1^2*w 1^2*w 2^3 - 216*v 1^2*w 1^2*w 2^2*w 3 - 72*v 1^2*w 1^2*w 2*w 3^2 + 80*v 1^2*w 1^2*w 3^3 - 216*v 1^2*w 1*w 2^4 - 432*v 1^2*w 1*w 2^3*w 3 - 312*v 1^2*w 1*w 2^2*w 3^2 - 96*v 1^2*w 1*w 2*w 3^3 + 32*v 1^2*w 1*w 3^4 - 54*v 1^2*w 2^5 - 162*v 1^2*w 2^4*w 3 - 184*v 1^2*w 2^3*w 3^2 - 104*v 1^2*w 2^2*w 3^3 - 18*v 1^2*w 2*w 3^4 + 10*v 1^2*w 3^5 - 8*v 1*v 2*w 1^3*w 3^2 - 324*v 1*v 2*w 1^2*w 2^3 - 324*v 1*v 2*w 1^2*w 2^2*w 3 - 84*v 1*v 2*w 1^2*w 2*w 3^2 + 36*v 1*v 2*w 1^2*w 3^3 - 486*v 1*v 2*w 1*w 2^4 - 864*v 1*v 2*w 1*w 2^3*w 3 - 624*v 1*v 2*w 1*w 2^2*w 3^2 - 72*v 1*v 2*w 1*w 2*w 3^3 + 14*v 1*v 2*w 1*w 3^4 - 324*v 1*v 2*w 2^5 - 702*v 1*v 2*w 2^4*w 3 - 776*v 1*v 2*w 2^3*w 3^2 - 408*v 1*v 2*w 2^2*w 3^3 - 52*v 1*v 2*w 2*w 3^4 + 38*v 1*v 2*w 3^5 + 108*v 1*v 3*w 1*w 2^4 + 432*v 1*v 3*w 1*w 2^3*w 3 + 432*v 1*v 3*w 1*w 2^2*w 3^2 + 288*v 1*v 3*w 1*w 2*w 3^3 + 108*v 1*v 3*w 1*w 3^4 + 54*v 1*v 3*w 2^5 + 270*v 1*v 3*w 2^4*w 3 + 432*v 1*v 3*w 2^3*w 3^2 + 360*v 1*v 3*w 2^2*w 3^3 + 186*v 1*v 3*w 2*w 3^4 + 42*v 1*v 3*w 3^5 - 40*v 2^2*w 1^3*w 3^2 - 108*v 2^2*w 1^2*w 2^3 - 108*v 2^2*w 1^2*w 2^2*w 3 - 36*v 2^2*w 1^2*w 2*w 3^2 + 4*v 2^2*w 1^2*w 3^3 - 270*v 2^2*w 1*w 2^4 - 432*v 2^2*w 1*w 2^3*w 3 - 336*v 2^2*w 1*w 2^2*w 3^2 - 72*v 2^2*w 1*w 2*w 3^3 - 18*v 2^2*w 1*w 3^4 - 270*v 2^2*w 2^5 - 540*v 2^2*w 2^4*w 3 - 568*v 2^2*w 2^3*w 3^2 - 256*v 2^2*w 2^2*w 3^3 - 34*v 2^2*w 2*w 3^4 + 28*v 2^2*w 3^5 - 48*v 2*v 3*w 1^3*w 3^2 + 54*v 2*v 3*w 1*w 2^4 + 216*v 2*v 3*w 1*w 2^3*w 3 + 216*v 2*v 3*w 1*w 2^2*w 3^2 + 192*v 2*v 3*w 1*w 2*w 3^3 + 42*v 2*v 3*w 1*w 3^4 - 54*v 2*v 3*w 2^5 + 216*v 2*v 3*w 2^4*w 3 + 372*v 2*v 3*w 2^3*w 3^2 + 492*v 2*v 3*w 2^2*w 3^3 + 330*v 2*v 3*w 2*w 3^4 + 108*v 2*v 3*w 3^5 + 8*v 3^2*w 3^5) * hk

theorem F1_zero_row (v w : V4) (h1 : tau v = 0) (h2 : tau w = 0) (h3 : ip v v = 0)
    (h4 : ip w w = 0) (h5 : t3 v v w = 0) (hq : 3 * t4 v v w w = ip v w ^ 2) (hg : ip v w ≠ 0) : ∃ k, v k = 0 ∧ w k = 0 := by
  have hg3 : (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 ≠ 0 := pow_ne_zero 3 hg
  have sq : ∀ x : ℂ, 8 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 3 * x ^ 2) = 0 → x = 0 := by
    intro x hx
    have hx' := (mul_eq_zero.mp hx).resolve_left (by norm_num)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp hx').resolve_left hg3)
  have hP := sq _ (F1_vprod v w h1 h2 h3 h4 h5 hq)
  rcases mul_eq_zero.mp hP with h | e3
  · rcases mul_eq_zero.mp h with h | e2
    · rcases mul_eq_zero.mp h with e0 | e1
      · exact ⟨0, e0, sq _ (F1_w0 v w h1 h2 h3 h4 h5 hq e0)⟩
      · exact ⟨1, e1, sq _ (F1_w1 v w h1 h2 h3 h4 h5 hq e1)⟩
    · exact ⟨2, e2, sq _ (F1_w2 v w h1 h2 h3 h4 h5 hq e2)⟩
  · exact ⟨3, e3, sq _ (F1_w3 v w h1 h2 h3 h4 h5 hq e3)⟩

theorem c2iii_zero_row (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4) (hv0 : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0) (hw2 : ip w w = 0)
    (hvw : ∀ c : ℂ, w ≠ c • v)
    (hreal : ∀ l b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l • v ∧ col Z 3 = (-l) • v ∧ col Z 4 = b • w) :
    t3 v v w = 0 ∧ 3 * t4 v v w w = ip v w ^ 2 ∧ ∃ k, v k = 0 ∧ w k = 0 := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hreal 1 1
  obtain ⟨q1, q2⟩ := nbar_eqs K hdef Z hZ h0
  rw [e2, e3, e4] at q1 q2
  simp only [t3, t4, ip, Pi.smul_apply, smul_eq_mul] at q1 q2
  have h5 : t3 v v w = 0 := by
    simp only [t3]
    linear_combination q1
  have hq : 3 * t4 v v w w = ip v w ^ 2 := by
    simp only [t4, ip]
    linear_combination -q2
  exact ⟨h5, hq, F1_zero_row v w hv1 hw1 hv2 hw2 h5 hq hg⟩

theorem uconst_0 (v w u : V4) (hvk : v 0 = 0) (hwk : w 0 = 0) (h1 : tau v = 0) (h2 : tau w = 0)
    (h3 : ip v v = 0) (h4 : ip w w = 0) (hu1 : ip v u = 0) (hu2 : ip w u = 0) (hu3 : tau u = 0) :
    2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 1 - u 2)) = 0 ∧
      2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 2 - u 3)) = 0 := by
  simp only [tau, ip] at h1 h2 h3 h4 hu1 hu2 hu3
  refine ⟨?_, ?_⟩
  · linear_combination (-5*u 0*v 0*w 3^2 + 2*u 0*v 1*w 2^2 + 4*u 0*v 1*w 2*w 3 + 7*u 0*v 1*w 3^2 - 6*u 0*v 2*w 2^2 - 24*u 0*v 2*w 2*w 3 - 15*u 0*v 2*w 3^2 - 2*u 0*v 3*w 2^2 + 8*u 0*v 3*w 2*w 3 + 9*u 0*v 3*w 3^2 - 6*u 2*v 0*w 3^2 + 4*u 2*v 1*w 2^2 + 8*u 2*v 1*w 2*w 3 + 10*u 2*v 1*w 3^2 - 12*u 2*v 2*w 2^2 - 24*u 2*v 2*w 2*w 3 - 14*u 2*v 2*w 3^2 - 4*u 2*v 3*w 2^2 - 8*u 2*v 3*w 2*w 3 - 8*u 2*v 3*w 3^2 - 9*u 3*v 0*w 3^2 + 2*u 3*v 1*w 2^2 + 4*u 3*v 1*w 2*w 3 + 11*u 3*v 1*w 3^2 - 6*u 3*v 2*w 2^2 - 16*u 3*v 2*w 2*w 3 - 15*u 3*v 2*w 3^2 - 2*u 3*v 3*w 2^2 - 5*u 3*v 3*w 3^2) * hvk + (2*u 0*v 1^2*w 1 - 2*u 0*v 1^2*w 2 - 2*u 0*v 1^2*w 3 + 4*u 0*v 1*v 2*w 2 + 4*u 0*v 1*v 3*w 3 + 4*u 0*v 2^2*w 0 - 4*u 0*v 2^2*w 1 + 4*u 0*v 2^2*w 2 + 20*u 0*v 2^2*w 3 + 16*u 0*v 2*v 3*w 2 + 24*u 0*v 2*v 3*w 3 + 5*u 0*v 3^2*w 0 - 5*u 0*v 3^2*w 1 - 11*u 0*v 3^2*w 2 + u 0*v 3^2*w 3 + 2*u 1*v 0^2*w 0 + 4*u 1*v 0*v 1*w 1 + 4*u 1*v 0*v 2*w 2 + 4*u 1*v 0*v 3*w 3 - 2*u 2*v 0^2*w 0 - 4*u 2*v 0*v 1*w 1 - 4*u 2*v 0*v 2*w 2 - 4*u 2*v 0*v 3*w 3 + 4*u 2*v 1^2*w 1 - 4*u 2*v 1^2*w 2 - 4*u 2*v 1^2*w 3 + 8*u 2*v 1*v 2*w 2 + 8*u 2*v 1*v 3*w 3 + 8*u 2*v 2^2*w 0 - 8*u 2*v 2^2*w 1 + 8*u 2*v 2^2*w 2 + 16*u 2*v 2^2*w 3 + 8*u 2*v 2*v 3*w 2 + 12*u 2*v 2*v 3*w 3 + 10*u 2*v 3^2*w 0 - 10*u 2*v 3^2*w 1 + 2*u 2*v 3^2*w 2 + 8*u 2*v 3^2*w 3 + 2*u 3*v 1^2*w 1 - 2*u 3*v 1^2*w 2 - 2*u 3*v 1^2*w 3 + 4*u 3*v 1*v 2*w 2 + 4*u 3*v 1*v 3*w 3 + 4*u 3*v 2^2*w 0 - 4*u 3*v 2^2*w 1 + 4*u 3*v 2^2*w 2 + 12*u 3*v 2^2*w 3 + 8*u 3*v 2*v 3*w 2 + 12*u 3*v 2*v 3*w 3 + 5*u 3*v 3^2*w 0 - 5*u 3*v 3^2*w 1 - 3*u 3*v 3^2*w 2 + 3*u 3*v 3^2*w 3) * hwk + (-2*u 0*v 1*w 2^2 - 4*u 0*v 1*w 2*w 3 - 7*u 0*v 1*w 3^2 + 6*u 0*v 2*w 2^2 + 16*u 0*v 2*w 2*w 3 + 11*u 0*v 2*w 3^2 + 2*u 0*v 3*w 2^2 + u 0*v 3*w 3^2 - 4*u 2*v 1*w 2^2 - 8*u 2*v 1*w 2*w 3 - 10*u 2*v 1*w 3^2 + 12*u 2*v 2*w 2^2 + 24*u 2*v 2*w 2*w 3 + 14*u 2*v 2*w 3^2 + 4*u 2*v 3*w 2^2 + 8*u 2*v 3*w 2*w 3 + 8*u 2*v 3*w 3^2 - 2*u 3*v 1*w 2^2 - 4*u 3*v 1*w 2*w 3 - 11*u 3*v 1*w 3^2 + 6*u 3*v 2*w 2^2 + 16*u 3*v 2*w 2*w 3 + 15*u 3*v 2*w 3^2 + 2*u 3*v 3*w 2^2 + 5*u 3*v 3*w 3^2) * h1 + (-2*u 0*v 1^2*w 1 + 2*u 0*v 1^2*w 2 + 2*u 0*v 1^2*w 3 - 4*u 0*v 1*v 2*w 2 - 4*u 0*v 1*v 3*w 3 + 4*u 0*v 2^2*w 1 - 4*u 0*v 2^2*w 2 - 12*u 0*v 2^2*w 3 - 8*u 0*v 2*v 3*w 2 - 12*u 0*v 2*v 3*w 3 + 5*u 0*v 3^2*w 1 + 3*u 0*v 3^2*w 2 - 3*u 0*v 3^2*w 3 - 4*u 2*v 1^2*w 1 + 4*u 2*v 1^2*w 2 + 4*u 2*v 1^2*w 3 - 8*u 2*v 1*v 2*w 2 - 8*u 2*v 1*v 3*w 3 + 8*u 2*v 2^2*w 1 - 8*u 2*v 2^2*w 2 - 16*u 2*v 2^2*w 3 - 8*u 2*v 2*v 3*w 2 - 12*u 2*v 2*v 3*w 3 + 10*u 2*v 3^2*w 1 - 2*u 2*v 3^2*w 2 - 8*u 2*v 3^2*w 3 - 2*u 3*v 1^2*w 1 + 2*u 3*v 1^2*w 2 + 2*u 3*v 1^2*w 3 - 4*u 3*v 1*v 2*w 2 - 4*u 3*v 1*v 3*w 3 + 4*u 3*v 2^2*w 1 - 4*u 3*v 2^2*w 2 - 12*u 3*v 2^2*w 3 - 8*u 3*v 2*v 3*w 2 - 12*u 3*v 2*v 3*w 3 + 5*u 3*v 3^2*w 1 + 3*u 3*v 3^2*w 2 - 3*u 3*v 3^2*w 3) * h2 + (5*u 0*w 3^2 + 6*u 2*w 3^2 + 9*u 3*w 3^2) * h3 + (-4*u 0*v 2^2 - 5*u 0*v 3^2 - 8*u 2*v 2^2 - 10*u 2*v 3^2 - 4*u 3*v 2^2 - 5*u 3*v 3^2) * h4 + (8*v 2*w 2*w 3 + 4*v 2*w 3^2 - 8*v 3*w 2*w 3 - 10*v 3*w 3^2) * hu1 + (-8*v 2^2*w 3 - 8*v 2*v 3*w 2 - 12*v 2*v 3*w 3 + 8*v 3^2*w 2 + 2*v 3^2*w 3) * hu2 + (2*v 1^2*w 1^2 + 4*v 1*v 2*w 1*w 2 - 8*v 1*v 2*w 2*w 3 - 4*v 1*v 2*w 3^2 + 4*v 1*v 3*w 1*w 3 + 8*v 1*v 3*w 2*w 3 + 10*v 1*v 3*w 3^2 + 8*v 2^2*w 1*w 3 + 2*v 2^2*w 2^2 + 8*v 2*v 3*w 1*w 2 + 12*v 2*v 3*w 1*w 3 + 4*v 2*v 3*w 2*w 3 - 8*v 3^2*w 1*w 2 - 2*v 3^2*w 1*w 3 + 2*v 3^2*w 3^2) * hu3
  · linear_combination (4*u 0*v 0*w 3^2 - 4*u 0*v 1*w 3^2 + 32*u 0*v 2*w 2*w 3 + 20*u 0*v 2*w 3^2 + 4*u 0*v 3*w 2*w 3 + 3*u 2*v 0*w 3^2 - 2*u 2*v 1*w 2^2 - 4*u 2*v 1*w 2*w 3 - 5*u 2*v 1*w 3^2 + 6*u 2*v 2*w 2^2 + 24*u 2*v 2*w 2*w 3 + 13*u 2*v 2*w 3^2 + 2*u 2*v 3*w 2^2 + 10*u 2*v 3*w 2*w 3 + 7*u 2*v 3*w 3^2 + 9*u 3*v 0*w 3^2 + 2*u 3*v 1*w 2^2 + 4*u 3*v 1*w 2*w 3 - 7*u 3*v 1*w 3^2 - 6*u 3*v 2*w 2^2 + 8*u 3*v 2*w 2*w 3 + 15*u 3*v 2*w 3^2 - 2*u 3*v 3*w 2^2 - 6*u 3*v 3*w 2*w 3 + u 3*v 3*w 3^2) * hvk + (-32*u 0*v 2^2*w 3 + 2*u 0*v 2*v 3*w 0 - 2*u 0*v 2*v 3*w 1 - 6*u 0*v 2*v 3*w 2 - 34*u 0*v 2*v 3*w 3 - 2*u 0*v 3^2*w 0 + 2*u 0*v 3^2*w 1 + 6*u 0*v 3^2*w 2 - 6*u 0*v 3^2*w 3 + 2*u 2*v 0^2*w 0 + 4*u 2*v 0*v 1*w 1 + 4*u 2*v 0*v 2*w 2 + 4*u 2*v 0*v 3*w 3 - 2*u 2*v 1^2*w 1 + 2*u 2*v 1^2*w 2 + 2*u 2*v 1^2*w 3 - 4*u 2*v 1*v 2*w 2 - 4*u 2*v 1*v 3*w 3 - 4*u 2*v 2^2*w 0 + 4*u 2*v 2^2*w 1 - 4*u 2*v 2^2*w 2 - 20*u 2*v 2^2*w 3 - 4*u 2*v 2*v 3*w 2 - 18*u 2*v 2*v 3*w 3 - 5*u 2*v 3^2*w 0 + 5*u 2*v 3^2*w 1 - u 2*v 3^2*w 2 - 7*u 2*v 3^2*w 3 - 2*u 3*v 0^2*w 0 - 4*u 3*v 0*v 1*w 1 - 4*u 3*v 0*v 2*w 2 - 4*u 3*v 0*v 3*w 3 + 2*u 3*v 1^2*w 1 - 2*u 3*v 1^2*w 2 - 2*u 3*v 1^2*w 3 + 4*u 3*v 1*v 2*w 2 + 4*u 3*v 1*v 3*w 3 + 4*u 3*v 2^2*w 0 - 4*u 3*v 2^2*w 1 + 4*u 3*v 2^2*w 2 - 12*u 3*v 2^2*w 3 + 6*u 3*v 2*v 3*w 0 - 6*u 3*v 2*v 3*w 1 + 2*u 3*v 2*v 3*w 2 - 12*u 3*v 2*v 3*w 3 - u 3*v 3^2*w 0 + u 3*v 3^2*w 1 + 3*u 3*v 3^2*w 2 - 3*u 3*v 3^2*w 3) * hwk + (4*u 0*v 1*w 3^2 - 16*u 0*v 2*w 2*w 3 - 12*u 0*v 2*w 3^2 - 2*u 0*v 3*w 2*w 3 - 2*u 0*v 3*w 3^2 + 2*u 2*v 1*w 2^2 + 4*u 2*v 1*w 2*w 3 + 5*u 2*v 1*w 3^2 - 6*u 2*v 2*w 2^2 - 24*u 2*v 2*w 2*w 3 - 13*u 2*v 2*w 3^2 - 2*u 2*v 3*w 2^2 - 10*u 2*v 3*w 2*w 3 - 7*u 2*v 3*w 3^2 - 2*u 3*v 1*w 2^2 - 4*u 3*v 1*w 2*w 3 + 7*u 3*v 1*w 3^2 + 6*u 3*v 2*w 2^2 - 8*u 3*v 2*w 2*w 3 - 15*u 3*v 2*w 3^2 + 2*u 3*v 3*w 2^2 + 6*u 3*v 3*w 2*w 3 - u 3*v 3*w 3^2) * h1 + (16*u 0*v 2^2*w 3 + 2*u 0*v 2*v 3*w 1 + 2*u 0*v 2*v 3*w 2 + 16*u 0*v 2*v 3*w 3 - 2*u 0*v 3^2*w 1 - 2*u 0*v 3^2*w 2 + 4*u 0*v 3^2*w 3 + 2*u 2*v 1^2*w 1 - 2*u 2*v 1^2*w 2 - 2*u 2*v 1^2*w 3 + 4*u 2*v 1*v 2*w 2 + 4*u 2*v 1*v 3*w 3 - 4*u 2*v 2^2*w 1 + 4*u 2*v 2^2*w 2 + 20*u 2*v 2^2*w 3 + 4*u 2*v 2*v 3*w 2 + 18*u 2*v 2*v 3*w 3 - 5*u 2*v 3^2*w 1 + u 2*v 3^2*w 2 + 7*u 2*v 3^2*w 3 - 2*u 3*v 1^2*w 1 + 2*u 3*v 1^2*w 2 + 2*u 3*v 1^2*w 3 - 4*u 3*v 1*v 2*w 2 - 4*u 3*v 1*v 3*w 3 + 4*u 3*v 2^2*w 1 - 4*u 3*v 2^2*w 2 + 12*u 3*v 2^2*w 3 + 6*u 3*v 2*v 3*w 1 - 2*u 3*v 2*v 3*w 2 + 12*u 3*v 2*v 3*w 3 - u 3*v 3^2*w 1 - 3*u 3*v 3^2*w 2 + 3*u 3*v 3^2*w 3) * h2 + (-4*u 0*w 3^2 - 3*u 2*w 3^2 - 9*u 3*w 3^2) * h3 + (-2*u 0*v 2*v 3 + 2*u 0*v 3^2 + 4*u 2*v 2^2 + 5*u 2*v 3^2 - 4*u 3*v 2^2 - 6*u 3*v 2*v 3 + u 3*v 3^2) * h4 + (-16*v 2*w 2*w 3 - 8*v 2*w 3^2 - 2*v 3*w 2*w 3 + 2*v 3*w 3^2) * hu1 + (16*v 2^2*w 3 + 4*v 2*v 3*w 2 + 18*v 2*v 3*w 3 - 4*v 3^2*w 2 + 2*v 3^2*w 3) * hu2 + (16*v 1*v 2*w 2*w 3 + 8*v 1*v 2*w 3^2 + 2*v 1*v 3*w 2*w 3 - 2*v 1*v 3*w 3^2 - 16*v 2^2*w 1*w 3 - 4*v 2*v 3*w 1*w 2 - 18*v 2*v 3*w 1*w 3 + 4*v 3^2*w 1*w 2 - 2*v 3^2*w 1*w 3) * hu3

theorem uconst_1 (v w u : V4) (hvk : v 1 = 0) (hwk : w 1 = 0) (h1 : tau v = 0) (h2 : tau w = 0)
    (h3 : ip v v = 0) (h4 : ip w w = 0) (hu1 : ip v u = 0) (hu2 : ip w u = 0) (hu3 : tau u = 0) :
    2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 0 - u 2)) = 0 ∧
      2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 2 - u 3)) = 0 := by
  simp only [tau, ip] at h1 h2 h3 h4 hu1 hu2 hu3
  refine ⟨?_, ?_⟩
  · linear_combination (2*u 1*v 0*w 2^2 + 4*u 1*v 0*w 2*w 3 + 7*u 1*v 0*w 3^2 - 5*u 1*v 1*w 3^2 - 6*u 1*v 2*w 2^2 - 24*u 1*v 2*w 2*w 3 - 15*u 1*v 2*w 3^2 - 2*u 1*v 3*w 2^2 + 8*u 1*v 3*w 2*w 3 + 9*u 1*v 3*w 3^2 + 4*u 2*v 0*w 2^2 + 8*u 2*v 0*w 2*w 3 + 10*u 2*v 0*w 3^2 - 6*u 2*v 1*w 3^2 - 12*u 2*v 2*w 2^2 - 24*u 2*v 2*w 2*w 3 - 14*u 2*v 2*w 3^2 - 4*u 2*v 3*w 2^2 - 8*u 2*v 3*w 2*w 3 - 8*u 2*v 3*w 3^2 + 2*u 3*v 0*w 2^2 + 4*u 3*v 0*w 2*w 3 + 11*u 3*v 0*w 3^2 - 9*u 3*v 1*w 3^2 - 6*u 3*v 2*w 2^2 - 16*u 3*v 2*w 2*w 3 - 15*u 3*v 2*w 3^2 - 2*u 3*v 3*w 2^2 - 5*u 3*v 3*w 3^2) * hvk + (4*u 0*v 0*v 1*w 0 + 2*u 0*v 1^2*w 1 + 4*u 0*v 1*v 2*w 2 + 4*u 0*v 1*v 3*w 3 + 2*u 1*v 0^2*w 0 - 2*u 1*v 0^2*w 2 - 2*u 1*v 0^2*w 3 + 4*u 1*v 0*v 2*w 2 + 4*u 1*v 0*v 3*w 3 - 4*u 1*v 2^2*w 0 + 4*u 1*v 2^2*w 1 + 4*u 1*v 2^2*w 2 + 20*u 1*v 2^2*w 3 + 16*u 1*v 2*v 3*w 2 + 24*u 1*v 2*v 3*w 3 - 5*u 1*v 3^2*w 0 + 5*u 1*v 3^2*w 1 - 11*u 1*v 3^2*w 2 + u 1*v 3^2*w 3 + 4*u 2*v 0^2*w 0 - 4*u 2*v 0^2*w 2 - 4*u 2*v 0^2*w 3 - 4*u 2*v 0*v 1*w 0 + 8*u 2*v 0*v 2*w 2 + 8*u 2*v 0*v 3*w 3 - 2*u 2*v 1^2*w 1 - 4*u 2*v 1*v 2*w 2 - 4*u 2*v 1*v 3*w 3 - 8*u 2*v 2^2*w 0 + 8*u 2*v 2^2*w 1 + 8*u 2*v 2^2*w 2 + 16*u 2*v 2^2*w 3 + 8*u 2*v 2*v 3*w 2 + 12*u 2*v 2*v 3*w 3 - 10*u 2*v 3^2*w 0 + 10*u 2*v 3^2*w 1 + 2*u 2*v 3^2*w 2 + 8*u 2*v 3^2*w 3 + 2*u 3*v 0^2*w 0 - 2*u 3*v 0^2*w 2 - 2*u 3*v 0^2*w 3 + 4*u 3*v 0*v 2*w 2 + 4*u 3*v 0*v 3*w 3 - 4*u 3*v 2^2*w 0 + 4*u 3*v 2^2*w 1 + 4*u 3*v 2^2*w 2 + 12*u 3*v 2^2*w 3 + 8*u 3*v 2*v 3*w 2 + 12*u 3*v 2*v 3*w 3 - 5*u 3*v 3^2*w 0 + 5*u 3*v 3^2*w 1 - 3*u 3*v 3^2*w 2 + 3*u 3*v 3^2*w 3) * hwk + (-2*u 1*v 0*w 2^2 - 4*u 1*v 0*w 2*w 3 - 7*u 1*v 0*w 3^2 + 6*u 1*v 2*w 2^2 + 16*u 1*v 2*w 2*w 3 + 11*u 1*v 2*w 3^2 + 2*u 1*v 3*w 2^2 + u 1*v 3*w 3^2 - 4*u 2*v 0*w 2^2 - 8*u 2*v 0*w 2*w 3 - 10*u 2*v 0*w 3^2 + 12*u 2*v 2*w 2^2 + 24*u 2*v 2*w 2*w 3 + 14*u 2*v 2*w 3^2 + 4*u 2*v 3*w 2^2 + 8*u 2*v 3*w 2*w 3 + 8*u 2*v 3*w 3^2 - 2*u 3*v 0*w 2^2 - 4*u 3*v 0*w 2*w 3 - 11*u 3*v 0*w 3^2 + 6*u 3*v 2*w 2^2 + 16*u 3*v 2*w 2*w 3 + 15*u 3*v 2*w 3^2 + 2*u 3*v 3*w 2^2 + 5*u 3*v 3*w 3^2) * h1 + (-2*u 1*v 0^2*w 0 + 2*u 1*v 0^2*w 2 + 2*u 1*v 0^2*w 3 - 4*u 1*v 0*v 2*w 2 - 4*u 1*v 0*v 3*w 3 + 4*u 1*v 2^2*w 0 - 4*u 1*v 2^2*w 2 - 12*u 1*v 2^2*w 3 - 8*u 1*v 2*v 3*w 2 - 12*u 1*v 2*v 3*w 3 + 5*u 1*v 3^2*w 0 + 3*u 1*v 3^2*w 2 - 3*u 1*v 3^2*w 3 - 4*u 2*v 0^2*w 0 + 4*u 2*v 0^2*w 2 + 4*u 2*v 0^2*w 3 - 8*u 2*v 0*v 2*w 2 - 8*u 2*v 0*v 3*w 3 + 8*u 2*v 2^2*w 0 - 8*u 2*v 2^2*w 2 - 16*u 2*v 2^2*w 3 - 8*u 2*v 2*v 3*w 2 - 12*u 2*v 2*v 3*w 3 + 10*u 2*v 3^2*w 0 - 2*u 2*v 3^2*w 2 - 8*u 2*v 3^2*w 3 - 2*u 3*v 0^2*w 0 + 2*u 3*v 0^2*w 2 + 2*u 3*v 0^2*w 3 - 4*u 3*v 0*v 2*w 2 - 4*u 3*v 0*v 3*w 3 + 4*u 3*v 2^2*w 0 - 4*u 3*v 2^2*w 2 - 12*u 3*v 2^2*w 3 - 8*u 3*v 2*v 3*w 2 - 12*u 3*v 2*v 3*w 3 + 5*u 3*v 3^2*w 0 + 3*u 3*v 3^2*w 2 - 3*u 3*v 3^2*w 3) * h2 + (5*u 1*w 3^2 + 6*u 2*w 3^2 + 9*u 3*w 3^2) * h3 + (-4*u 1*v 2^2 - 5*u 1*v 3^2 - 8*u 2*v 2^2 - 10*u 2*v 3^2 - 4*u 3*v 2^2 - 5*u 3*v 3^2) * h4 + (8*v 2*w 2*w 3 + 4*v 2*w 3^2 - 8*v 3*w 2*w 3 - 10*v 3*w 3^2) * hu1 + (-8*v 2^2*w 3 - 8*v 2*v 3*w 2 - 12*v 2*v 3*w 3 + 8*v 3^2*w 2 + 2*v 3^2*w 3) * hu2 + (2*v 0^2*w 0^2 + 4*v 0*v 2*w 0*w 2 - 8*v 0*v 2*w 2*w 3 - 4*v 0*v 2*w 3^2 + 4*v 0*v 3*w 0*w 3 + 8*v 0*v 3*w 2*w 3 + 10*v 0*v 3*w 3^2 + 8*v 2^2*w 0*w 3 + 2*v 2^2*w 2^2 + 8*v 2*v 3*w 0*w 2 + 12*v 2*v 3*w 0*w 3 + 4*v 2*v 3*w 2*w 3 - 8*v 3^2*w 0*w 2 - 2*v 3^2*w 0*w 3 + 2*v 3^2*w 3^2) * hu3
  · linear_combination (-4*u 1*v 0*w 3^2 + 4*u 1*v 1*w 3^2 + 32*u 1*v 2*w 2*w 3 + 20*u 1*v 2*w 3^2 + 4*u 1*v 3*w 2*w 3 - 2*u 2*v 0*w 2^2 - 4*u 2*v 0*w 2*w 3 - 5*u 2*v 0*w 3^2 + 3*u 2*v 1*w 3^2 + 6*u 2*v 2*w 2^2 + 24*u 2*v 2*w 2*w 3 + 13*u 2*v 2*w 3^2 + 2*u 2*v 3*w 2^2 + 10*u 2*v 3*w 2*w 3 + 7*u 2*v 3*w 3^2 + 2*u 3*v 0*w 2^2 + 4*u 3*v 0*w 2*w 3 - 7*u 3*v 0*w 3^2 + 9*u 3*v 1*w 3^2 - 6*u 3*v 2*w 2^2 + 8*u 3*v 2*w 2*w 3 + 15*u 3*v 2*w 3^2 - 2*u 3*v 3*w 2^2 - 6*u 3*v 3*w 2*w 3 + u 3*v 3*w 3^2) * hvk + (-32*u 1*v 2^2*w 3 - 2*u 1*v 2*v 3*w 0 + 2*u 1*v 2*v 3*w 1 - 6*u 1*v 2*v 3*w 2 - 34*u 1*v 2*v 3*w 3 + 2*u 1*v 3^2*w 0 - 2*u 1*v 3^2*w 1 + 6*u 1*v 3^2*w 2 - 6*u 1*v 3^2*w 3 - 2*u 2*v 0^2*w 0 + 2*u 2*v 0^2*w 2 + 2*u 2*v 0^2*w 3 + 4*u 2*v 0*v 1*w 0 - 4*u 2*v 0*v 2*w 2 - 4*u 2*v 0*v 3*w 3 + 2*u 2*v 1^2*w 1 + 4*u 2*v 1*v 2*w 2 + 4*u 2*v 1*v 3*w 3 + 4*u 2*v 2^2*w 0 - 4*u 2*v 2^2*w 1 - 4*u 2*v 2^2*w 2 - 20*u 2*v 2^2*w 3 - 4*u 2*v 2*v 3*w 2 - 18*u 2*v 2*v 3*w 3 + 5*u 2*v 3^2*w 0 - 5*u 2*v 3^2*w 1 - u 2*v 3^2*w 2 - 7*u 2*v 3^2*w 3 + 2*u 3*v 0^2*w 0 - 2*u 3*v 0^2*w 2 - 2*u 3*v 0^2*w 3 - 4*u 3*v 0*v 1*w 0 + 4*u 3*v 0*v 2*w 2 + 4*u 3*v 0*v 3*w 3 - 2*u 3*v 1^2*w 1 - 4*u 3*v 1*v 2*w 2 - 4*u 3*v 1*v 3*w 3 - 4*u 3*v 2^2*w 0 + 4*u 3*v 2^2*w 1 + 4*u 3*v 2^2*w 2 - 12*u 3*v 2^2*w 3 - 6*u 3*v 2*v 3*w 0 + 6*u 3*v 2*v 3*w 1 + 2*u 3*v 2*v 3*w 2 - 12*u 3*v 2*v 3*w 3 + u 3*v 3^2*w 0 - u 3*v 3^2*w 1 + 3*u 3*v 3^2*w 2 - 3*u 3*v 3^2*w 3) * hwk + (4*u 1*v 0*w 3^2 - 16*u 1*v 2*w 2*w 3 - 12*u 1*v 2*w 3^2 - 2*u 1*v 3*w 2*w 3 - 2*u 1*v 3*w 3^2 + 2*u 2*v 0*w 2^2 + 4*u 2*v 0*w 2*w 3 + 5*u 2*v 0*w 3^2 - 6*u 2*v 2*w 2^2 - 24*u 2*v 2*w 2*w 3 - 13*u 2*v 2*w 3^2 - 2*u 2*v 3*w 2^2 - 10*u 2*v 3*w 2*w 3 - 7*u 2*v 3*w 3^2 - 2*u 3*v 0*w 2^2 - 4*u 3*v 0*w 2*w 3 + 7*u 3*v 0*w 3^2 + 6*u 3*v 2*w 2^2 - 8*u 3*v 2*w 2*w 3 - 15*u 3*v 2*w 3^2 + 2*u 3*v 3*w 2^2 + 6*u 3*v 3*w 2*w 3 - u 3*v 3*w 3^2) * h1 + (16*u 1*v 2^2*w 3 + 2*u 1*v 2*v 3*w 0 + 2*u 1*v 2*v 3*w 2 + 16*u 1*v 2*v 3*w 3 - 2*u 1*v 3^2*w 0 - 2*u 1*v 3^2*w 2 + 4*u 1*v 3^2*w 3 + 2*u 2*v 0^2*w 0 - 2*u 2*v 0^2*w 2 - 2*u 2*v 0^2*w 3 + 4*u 2*v 0*v 2*w 2 + 4*u 2*v 0*v 3*w 3 - 4*u 2*v 2^2*w 0 + 4*u 2*v 2^2*w 2 + 20*u 2*v 2^2*w 3 + 4*u 2*v 2*v 3*w 2 + 18*u 2*v 2*v 3*w 3 - 5*u 2*v 3^2*w 0 + u 2*v 3^2*w 2 + 7*u 2*v 3^2*w 3 - 2*u 3*v 0^2*w 0 + 2*u 3*v 0^2*w 2 + 2*u 3*v 0^2*w 3 - 4*u 3*v 0*v 2*w 2 - 4*u 3*v 0*v 3*w 3 + 4*u 3*v 2^2*w 0 - 4*u 3*v 2^2*w 2 + 12*u 3*v 2^2*w 3 + 6*u 3*v 2*v 3*w 0 - 2*u 3*v 2*v 3*w 2 + 12*u 3*v 2*v 3*w 3 - u 3*v 3^2*w 0 - 3*u 3*v 3^2*w 2 + 3*u 3*v 3^2*w 3) * h2 + (-4*u 1*w 3^2 - 3*u 2*w 3^2 - 9*u 3*w 3^2) * h3 + (-2*u 1*v 2*v 3 + 2*u 1*v 3^2 + 4*u 2*v 2^2 + 5*u 2*v 3^2 - 4*u 3*v 2^2 - 6*u 3*v 2*v 3 + u 3*v 3^2) * h4 + (-16*v 2*w 2*w 3 - 8*v 2*w 3^2 - 2*v 3*w 2*w 3 + 2*v 3*w 3^2) * hu1 + (16*v 2^2*w 3 + 4*v 2*v 3*w 2 + 18*v 2*v 3*w 3 - 4*v 3^2*w 2 + 2*v 3^2*w 3) * hu2 + (16*v 0*v 2*w 2*w 3 + 8*v 0*v 2*w 3^2 + 2*v 0*v 3*w 2*w 3 - 2*v 0*v 3*w 3^2 - 16*v 2^2*w 0*w 3 - 4*v 2*v 3*w 0*w 2 - 18*v 2*v 3*w 0*w 3 + 4*v 3^2*w 0*w 2 - 2*v 3^2*w 0*w 3) * hu3

theorem uconst_2 (v w u : V4) (hvk : v 2 = 0) (hwk : w 2 = 0) (h1 : tau v = 0) (h2 : tau w = 0)
    (h3 : ip v v = 0) (h4 : ip w w = 0) (hu1 : ip v u = 0) (hu2 : ip w u = 0) (hu3 : tau u = 0) :
    2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 0 - u 1)) = 0 ∧
      2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 1 - u 3)) = 0 := by
  simp only [tau, ip] at h1 h2 h3 h4 hu1 hu2 hu3
  refine ⟨?_, ?_⟩
  · linear_combination (4*u 1*v 0*w 1^2 + 8*u 1*v 0*w 1*w 3 + 10*u 1*v 0*w 3^2 - 12*u 1*v 1*w 1^2 - 24*u 1*v 1*w 1*w 3 - 14*u 1*v 1*w 3^2 - 6*u 1*v 2*w 3^2 - 4*u 1*v 3*w 1^2 - 8*u 1*v 3*w 1*w 3 - 8*u 1*v 3*w 3^2 + 2*u 2*v 0*w 1^2 + 4*u 2*v 0*w 1*w 3 + 7*u 2*v 0*w 3^2 - 6*u 2*v 1*w 1^2 - 24*u 2*v 1*w 1*w 3 - 15*u 2*v 1*w 3^2 - 5*u 2*v 2*w 3^2 - 2*u 2*v 3*w 1^2 + 8*u 2*v 3*w 1*w 3 + 9*u 2*v 3*w 3^2 + 2*u 3*v 0*w 1^2 + 4*u 3*v 0*w 1*w 3 + 11*u 3*v 0*w 3^2 - 6*u 3*v 1*w 1^2 - 16*u 3*v 1*w 1*w 3 - 15*u 3*v 1*w 3^2 - 9*u 3*v 2*w 3^2 - 2*u 3*v 3*w 1^2 - 5*u 3*v 3*w 3^2) * hvk + (4*u 0*v 0*v 2*w 0 + 4*u 0*v 1*v 2*w 1 + 2*u 0*v 2^2*w 2 + 4*u 0*v 2*v 3*w 3 + 4*u 1*v 0^2*w 0 - 4*u 1*v 0^2*w 1 - 4*u 1*v 0^2*w 3 + 8*u 1*v 0*v 1*w 1 - 4*u 1*v 0*v 2*w 0 + 8*u 1*v 0*v 3*w 3 - 8*u 1*v 1^2*w 0 + 8*u 1*v 1^2*w 1 + 8*u 1*v 1^2*w 2 + 16*u 1*v 1^2*w 3 - 4*u 1*v 1*v 2*w 1 + 8*u 1*v 1*v 3*w 1 + 12*u 1*v 1*v 3*w 3 - 2*u 1*v 2^2*w 2 - 4*u 1*v 2*v 3*w 3 - 10*u 1*v 3^2*w 0 + 2*u 1*v 3^2*w 1 + 10*u 1*v 3^2*w 2 + 8*u 1*v 3^2*w 3 + 2*u 2*v 0^2*w 0 - 2*u 2*v 0^2*w 1 - 2*u 2*v 0^2*w 3 + 4*u 2*v 0*v 1*w 1 + 4*u 2*v 0*v 3*w 3 - 4*u 2*v 1^2*w 0 + 4*u 2*v 1^2*w 1 + 4*u 2*v 1^2*w 2 + 20*u 2*v 1^2*w 3 + 16*u 2*v 1*v 3*w 1 + 24*u 2*v 1*v 3*w 3 - 5*u 2*v 3^2*w 0 - 11*u 2*v 3^2*w 1 + 5*u 2*v 3^2*w 2 + u 2*v 3^2*w 3 + 2*u 3*v 0^2*w 0 - 2*u 3*v 0^2*w 1 - 2*u 3*v 0^2*w 3 + 4*u 3*v 0*v 1*w 1 + 4*u 3*v 0*v 3*w 3 - 4*u 3*v 1^2*w 0 + 4*u 3*v 1^2*w 1 + 4*u 3*v 1^2*w 2 + 12*u 3*v 1^2*w 3 + 8*u 3*v 1*v 3*w 1 + 12*u 3*v 1*v 3*w 3 - 5*u 3*v 3^2*w 0 - 3*u 3*v 3^2*w 1 + 5*u 3*v 3^2*w 2 + 3*u 3*v 3^2*w 3) * hwk + (-4*u 1*v 0*w 1^2 - 8*u 1*v 0*w 1*w 3 - 10*u 1*v 0*w 3^2 + 12*u 1*v 1*w 1^2 + 24*u 1*v 1*w 1*w 3 + 14*u 1*v 1*w 3^2 + 4*u 1*v 3*w 1^2 + 8*u 1*v 3*w 1*w 3 + 8*u 1*v 3*w 3^2 - 2*u 2*v 0*w 1^2 - 4*u 2*v 0*w 1*w 3 - 7*u 2*v 0*w 3^2 + 6*u 2*v 1*w 1^2 + 16*u 2*v 1*w 1*w 3 + 11*u 2*v 1*w 3^2 + 2*u 2*v 3*w 1^2 + u 2*v 3*w 3^2 - 2*u 3*v 0*w 1^2 - 4*u 3*v 0*w 1*w 3 - 11*u 3*v 0*w 3^2 + 6*u 3*v 1*w 1^2 + 16*u 3*v 1*w 1*w 3 + 15*u 3*v 1*w 3^2 + 2*u 3*v 3*w 1^2 + 5*u 3*v 3*w 3^2) * h1 + (-4*u 1*v 0^2*w 0 + 4*u 1*v 0^2*w 1 + 4*u 1*v 0^2*w 3 - 8*u 1*v 0*v 1*w 1 - 8*u 1*v 0*v 3*w 3 + 8*u 1*v 1^2*w 0 - 8*u 1*v 1^2*w 1 - 16*u 1*v 1^2*w 3 - 8*u 1*v 1*v 3*w 1 - 12*u 1*v 1*v 3*w 3 + 10*u 1*v 3^2*w 0 - 2*u 1*v 3^2*w 1 - 8*u 1*v 3^2*w 3 - 2*u 2*v 0^2*w 0 + 2*u 2*v 0^2*w 1 + 2*u 2*v 0^2*w 3 - 4*u 2*v 0*v 1*w 1 - 4*u 2*v 0*v 3*w 3 + 4*u 2*v 1^2*w 0 - 4*u 2*v 1^2*w 1 - 12*u 2*v 1^2*w 3 - 8*u 2*v 1*v 3*w 1 - 12*u 2*v 1*v 3*w 3 + 5*u 2*v 3^2*w 0 + 3*u 2*v 3^2*w 1 - 3*u 2*v 3^2*w 3 - 2*u 3*v 0^2*w 0 + 2*u 3*v 0^2*w 1 + 2*u 3*v 0^2*w 3 - 4*u 3*v 0*v 1*w 1 - 4*u 3*v 0*v 3*w 3 + 4*u 3*v 1^2*w 0 - 4*u 3*v 1^2*w 1 - 12*u 3*v 1^2*w 3 - 8*u 3*v 1*v 3*w 1 - 12*u 3*v 1*v 3*w 3 + 5*u 3*v 3^2*w 0 + 3*u 3*v 3^2*w 1 - 3*u 3*v 3^2*w 3) * h2 + (6*u 1*w 3^2 + 5*u 2*w 3^2 + 9*u 3*w 3^2) * h3 + (-8*u 1*v 1^2 - 10*u 1*v 3^2 - 4*u 2*v 1^2 - 5*u 2*v 3^2 - 4*u 3*v 1^2 - 5*u 3*v 3^2) * h4 + (8*v 1*w 1*w 3 + 4*v 1*w 3^2 - 8*v 3*w 1*w 3 - 10*v 3*w 3^2) * hu1 + (-8*v 1^2*w 3 - 8*v 1*v 3*w 1 - 12*v 1*v 3*w 3 + 8*v 3^2*w 1 + 2*v 3^2*w 3) * hu2 + (2*v 0^2*w 0^2 + 4*v 0*v 1*w 0*w 1 - 8*v 0*v 1*w 1*w 3 - 4*v 0*v 1*w 3^2 + 4*v 0*v 3*w 0*w 3 + 8*v 0*v 3*w 1*w 3 + 10*v 0*v 3*w 3^2 + 8*v 1^2*w 0*w 3 + 2*v 1^2*w 1^2 + 8*v 1*v 3*w 0*w 1 + 12*v 1*v 3*w 0*w 3 + 4*v 1*v 3*w 1*w 3 - 8*v 3^2*w 0*w 1 - 2*v 3^2*w 0*w 3 + 2*v 3^2*w 3^2) * hu3
  · linear_combination (-2*u 1*v 0*w 1^2 - 4*u 1*v 0*w 1*w 3 - 5*u 1*v 0*w 3^2 + 6*u 1*v 1*w 1^2 + 24*u 1*v 1*w 1*w 3 + 13*u 1*v 1*w 3^2 + 3*u 1*v 2*w 3^2 + 2*u 1*v 3*w 1^2 + 10*u 1*v 3*w 1*w 3 + 7*u 1*v 3*w 3^2 - 4*u 2*v 0*w 3^2 + 32*u 2*v 1*w 1*w 3 + 20*u 2*v 1*w 3^2 + 4*u 2*v 2*w 3^2 + 4*u 2*v 3*w 1*w 3 + 2*u 3*v 0*w 1^2 + 4*u 3*v 0*w 1*w 3 - 7*u 3*v 0*w 3^2 - 6*u 3*v 1*w 1^2 + 8*u 3*v 1*w 1*w 3 + 15*u 3*v 1*w 3^2 + 9*u 3*v 2*w 3^2 - 2*u 3*v 3*w 1^2 - 6*u 3*v 3*w 1*w 3 + u 3*v 3*w 3^2) * hvk + (-2*u 1*v 0^2*w 0 + 2*u 1*v 0^2*w 1 + 2*u 1*v 0^2*w 3 - 4*u 1*v 0*v 1*w 1 + 4*u 1*v 0*v 2*w 0 - 4*u 1*v 0*v 3*w 3 + 4*u 1*v 1^2*w 0 - 4*u 1*v 1^2*w 1 - 4*u 1*v 1^2*w 2 - 20*u 1*v 1^2*w 3 + 4*u 1*v 1*v 2*w 1 - 4*u 1*v 1*v 3*w 1 - 18*u 1*v 1*v 3*w 3 + 2*u 1*v 2^2*w 2 + 4*u 1*v 2*v 3*w 3 + 5*u 1*v 3^2*w 0 - u 1*v 3^2*w 1 - 5*u 1*v 3^2*w 2 - 7*u 1*v 3^2*w 3 - 32*u 2*v 1^2*w 3 - 2*u 2*v 1*v 3*w 0 - 6*u 2*v 1*v 3*w 1 + 2*u 2*v 1*v 3*w 2 - 34*u 2*v 1*v 3*w 3 + 2*u 2*v 3^2*w 0 + 6*u 2*v 3^2*w 1 - 2*u 2*v 3^2*w 2 - 6*u 2*v 3^2*w 3 + 2*u 3*v 0^2*w 0 - 2*u 3*v 0^2*w 1 - 2*u 3*v 0^2*w 3 + 4*u 3*v 0*v 1*w 1 - 4*u 3*v 0*v 2*w 0 + 4*u 3*v 0*v 3*w 3 - 4*u 3*v 1^2*w 0 + 4*u 3*v 1^2*w 1 + 4*u 3*v 1^2*w 2 - 12*u 3*v 1^2*w 3 - 4*u 3*v 1*v 2*w 1 - 6*u 3*v 1*v 3*w 0 + 2*u 3*v 1*v 3*w 1 + 6*u 3*v 1*v 3*w 2 - 12*u 3*v 1*v 3*w 3 - 2*u 3*v 2^2*w 2 - 4*u 3*v 2*v 3*w 3 + u 3*v 3^2*w 0 + 3*u 3*v 3^2*w 1 - u 3*v 3^2*w 2 - 3*u 3*v 3^2*w 3) * hwk + (2*u 1*v 0*w 1^2 + 4*u 1*v 0*w 1*w 3 + 5*u 1*v 0*w 3^2 - 6*u 1*v 1*w 1^2 - 24*u 1*v 1*w 1*w 3 - 13*u 1*v 1*w 3^2 - 2*u 1*v 3*w 1^2 - 10*u 1*v 3*w 1*w 3 - 7*u 1*v 3*w 3^2 + 4*u 2*v 0*w 3^2 - 16*u 2*v 1*w 1*w 3 - 12*u 2*v 1*w 3^2 - 2*u 2*v 3*w 1*w 3 - 2*u 2*v 3*w 3^2 - 2*u 3*v 0*w 1^2 - 4*u 3*v 0*w 1*w 3 + 7*u 3*v 0*w 3^2 + 6*u 3*v 1*w 1^2 - 8*u 3*v 1*w 1*w 3 - 15*u 3*v 1*w 3^2 + 2*u 3*v 3*w 1^2 + 6*u 3*v 3*w 1*w 3 - u 3*v 3*w 3^2) * h1 + (2*u 1*v 0^2*w 0 - 2*u 1*v 0^2*w 1 - 2*u 1*v 0^2*w 3 + 4*u 1*v 0*v 1*w 1 + 4*u 1*v 0*v 3*w 3 - 4*u 1*v 1^2*w 0 + 4*u 1*v 1^2*w 1 + 20*u 1*v 1^2*w 3 + 4*u 1*v 1*v 3*w 1 + 18*u 1*v 1*v 3*w 3 - 5*u 1*v 3^2*w 0 + u 1*v 3^2*w 1 + 7*u 1*v 3^2*w 3 + 16*u 2*v 1^2*w 3 + 2*u 2*v 1*v 3*w 0 + 2*u 2*v 1*v 3*w 1 + 16*u 2*v 1*v 3*w 3 - 2*u 2*v 3^2*w 0 - 2*u 2*v 3^2*w 1 + 4*u 2*v 3^2*w 3 - 2*u 3*v 0^2*w 0 + 2*u 3*v 0^2*w 1 + 2*u 3*v 0^2*w 3 - 4*u 3*v 0*v 1*w 1 - 4*u 3*v 0*v 3*w 3 + 4*u 3*v 1^2*w 0 - 4*u 3*v 1^2*w 1 + 12*u 3*v 1^2*w 3 + 6*u 3*v 1*v 3*w 0 - 2*u 3*v 1*v 3*w 1 + 12*u 3*v 1*v 3*w 3 - u 3*v 3^2*w 0 - 3*u 3*v 3^2*w 1 + 3*u 3*v 3^2*w 3) * h2 + (-3*u 1*w 3^2 - 4*u 2*w 3^2 - 9*u 3*w 3^2) * h3 + (4*u 1*v 1^2 + 5*u 1*v 3^2 - 2*u 2*v 1*v 3 + 2*u 2*v 3^2 - 4*u 3*v 1^2 - 6*u 3*v 1*v 3 + u 3*v 3^2) * h4 + (-16*v 1*w 1*w 3 - 8*v 1*w 3^2 - 2*v 3*w 1*w 3 + 2*v 3*w 3^2) * hu1 + (16*v 1^2*w 3 + 4*v 1*v 3*w 1 + 18*v 1*v 3*w 3 - 4*v 3^2*w 1 + 2*v 3^2*w 3) * hu2 + (16*v 0*v 1*w 1*w 3 + 8*v 0*v 1*w 3^2 + 2*v 0*v 3*w 1*w 3 - 2*v 0*v 3*w 3^2 - 16*v 1^2*w 0*w 3 - 4*v 1*v 3*w 0*w 1 - 18*v 1*v 3*w 0*w 3 + 4*v 3^2*w 0*w 1 - 2*v 3^2*w 0*w 3) * hu3

theorem uconst_3 (v w u : V4) (hvk : v 3 = 0) (hwk : w 3 = 0) (h1 : tau v = 0) (h2 : tau w = 0)
    (h3 : ip v v = 0) (h4 : ip w w = 0) (hu1 : ip v u = 0) (hu2 : ip w u = 0) (hu3 : tau u = 0) :
    2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 0 - u 1)) = 0 ∧
      2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * (u 1 - u 2)) = 0 := by
  simp only [tau, ip] at h1 h2 h3 h4 hu1 hu2 hu3
  refine ⟨?_, ?_⟩
  · linear_combination (4*u 1*v 0*w 1^2 + 8*u 1*v 0*w 1*w 2 + 10*u 1*v 0*w 2^2 - 12*u 1*v 1*w 1^2 - 24*u 1*v 1*w 1*w 2 - 14*u 1*v 1*w 2^2 - 4*u 1*v 2*w 1^2 - 8*u 1*v 2*w 1*w 2 - 8*u 1*v 2*w 2^2 - 6*u 1*v 3*w 2^2 + 2*u 2*v 0*w 1^2 + 4*u 2*v 0*w 1*w 2 + 11*u 2*v 0*w 2^2 - 6*u 2*v 1*w 1^2 - 16*u 2*v 1*w 1*w 2 - 15*u 2*v 1*w 2^2 - 2*u 2*v 2*w 1^2 - 5*u 2*v 2*w 2^2 - 9*u 2*v 3*w 2^2 + 2*u 3*v 0*w 1^2 + 4*u 3*v 0*w 1*w 2 + 7*u 3*v 0*w 2^2 - 6*u 3*v 1*w 1^2 - 24*u 3*v 1*w 1*w 2 - 15*u 3*v 1*w 2^2 - 2*u 3*v 2*w 1^2 + 8*u 3*v 2*w 1*w 2 + 9*u 3*v 2*w 2^2 - 5*u 3*v 3*w 2^2) * hvk + (4*u 0*v 0*v 3*w 0 + 4*u 0*v 1*v 3*w 1 + 4*u 0*v 2*v 3*w 2 + 2*u 0*v 3^2*w 3 + 4*u 1*v 0^2*w 0 - 4*u 1*v 0^2*w 1 - 4*u 1*v 0^2*w 2 + 8*u 1*v 0*v 1*w 1 + 8*u 1*v 0*v 2*w 2 - 4*u 1*v 0*v 3*w 0 - 8*u 1*v 1^2*w 0 + 8*u 1*v 1^2*w 1 + 16*u 1*v 1^2*w 2 + 8*u 1*v 1^2*w 3 + 8*u 1*v 1*v 2*w 1 + 12*u 1*v 1*v 2*w 2 - 4*u 1*v 1*v 3*w 1 - 10*u 1*v 2^2*w 0 + 2*u 1*v 2^2*w 1 + 8*u 1*v 2^2*w 2 + 10*u 1*v 2^2*w 3 - 4*u 1*v 2*v 3*w 2 - 2*u 1*v 3^2*w 3 + 2*u 2*v 0^2*w 0 - 2*u 2*v 0^2*w 1 - 2*u 2*v 0^2*w 2 + 4*u 2*v 0*v 1*w 1 + 4*u 2*v 0*v 2*w 2 - 4*u 2*v 1^2*w 0 + 4*u 2*v 1^2*w 1 + 12*u 2*v 1^2*w 2 + 4*u 2*v 1^2*w 3 + 8*u 2*v 1*v 2*w 1 + 12*u 2*v 1*v 2*w 2 - 5*u 2*v 2^2*w 0 - 3*u 2*v 2^2*w 1 + 3*u 2*v 2^2*w 2 + 5*u 2*v 2^2*w 3 + 2*u 3*v 0^2*w 0 - 2*u 3*v 0^2*w 1 - 2*u 3*v 0^2*w 2 + 4*u 3*v 0*v 1*w 1 + 4*u 3*v 0*v 2*w 2 - 4*u 3*v 1^2*w 0 + 4*u 3*v 1^2*w 1 + 20*u 3*v 1^2*w 2 + 4*u 3*v 1^2*w 3 + 16*u 3*v 1*v 2*w 1 + 24*u 3*v 1*v 2*w 2 - 5*u 3*v 2^2*w 0 - 11*u 3*v 2^2*w 1 + u 3*v 2^2*w 2 + 5*u 3*v 2^2*w 3) * hwk + (-4*u 1*v 0*w 1^2 - 8*u 1*v 0*w 1*w 2 - 10*u 1*v 0*w 2^2 + 12*u 1*v 1*w 1^2 + 24*u 1*v 1*w 1*w 2 + 14*u 1*v 1*w 2^2 + 4*u 1*v 2*w 1^2 + 8*u 1*v 2*w 1*w 2 + 8*u 1*v 2*w 2^2 - 2*u 2*v 0*w 1^2 - 4*u 2*v 0*w 1*w 2 - 11*u 2*v 0*w 2^2 + 6*u 2*v 1*w 1^2 + 16*u 2*v 1*w 1*w 2 + 15*u 2*v 1*w 2^2 + 2*u 2*v 2*w 1^2 + 5*u 2*v 2*w 2^2 - 2*u 3*v 0*w 1^2 - 4*u 3*v 0*w 1*w 2 - 7*u 3*v 0*w 2^2 + 6*u 3*v 1*w 1^2 + 16*u 3*v 1*w 1*w 2 + 11*u 3*v 1*w 2^2 + 2*u 3*v 2*w 1^2 + u 3*v 2*w 2^2) * h1 + (-4*u 1*v 0^2*w 0 + 4*u 1*v 0^2*w 1 + 4*u 1*v 0^2*w 2 - 8*u 1*v 0*v 1*w 1 - 8*u 1*v 0*v 2*w 2 + 8*u 1*v 1^2*w 0 - 8*u 1*v 1^2*w 1 - 16*u 1*v 1^2*w 2 - 8*u 1*v 1*v 2*w 1 - 12*u 1*v 1*v 2*w 2 + 10*u 1*v 2^2*w 0 - 2*u 1*v 2^2*w 1 - 8*u 1*v 2^2*w 2 - 2*u 2*v 0^2*w 0 + 2*u 2*v 0^2*w 1 + 2*u 2*v 0^2*w 2 - 4*u 2*v 0*v 1*w 1 - 4*u 2*v 0*v 2*w 2 + 4*u 2*v 1^2*w 0 - 4*u 2*v 1^2*w 1 - 12*u 2*v 1^2*w 2 - 8*u 2*v 1*v 2*w 1 - 12*u 2*v 1*v 2*w 2 + 5*u 2*v 2^2*w 0 + 3*u 2*v 2^2*w 1 - 3*u 2*v 2^2*w 2 - 2*u 3*v 0^2*w 0 + 2*u 3*v 0^2*w 1 + 2*u 3*v 0^2*w 2 - 4*u 3*v 0*v 1*w 1 - 4*u 3*v 0*v 2*w 2 + 4*u 3*v 1^2*w 0 - 4*u 3*v 1^2*w 1 - 12*u 3*v 1^2*w 2 - 8*u 3*v 1*v 2*w 1 - 12*u 3*v 1*v 2*w 2 + 5*u 3*v 2^2*w 0 + 3*u 3*v 2^2*w 1 - 3*u 3*v 2^2*w 2) * h2 + (6*u 1*w 2^2 + 9*u 2*w 2^2 + 5*u 3*w 2^2) * h3 + (-8*u 1*v 1^2 - 10*u 1*v 2^2 - 4*u 2*v 1^2 - 5*u 2*v 2^2 - 4*u 3*v 1^2 - 5*u 3*v 2^2) * h4 + (8*v 1*w 1*w 2 + 4*v 1*w 2^2 - 8*v 2*w 1*w 2 - 10*v 2*w 2^2) * hu1 + (-8*v 1^2*w 2 - 8*v 1*v 2*w 1 - 12*v 1*v 2*w 2 + 8*v 2^2*w 1 + 2*v 2^2*w 2) * hu2 + (2*v 0^2*w 0^2 + 4*v 0*v 1*w 0*w 1 - 8*v 0*v 1*w 1*w 2 - 4*v 0*v 1*w 2^2 + 4*v 0*v 2*w 0*w 2 + 8*v 0*v 2*w 1*w 2 + 10*v 0*v 2*w 2^2 + 8*v 1^2*w 0*w 2 + 2*v 1^2*w 1^2 + 8*v 1*v 2*w 0*w 1 + 12*v 1*v 2*w 0*w 2 + 4*v 1*v 2*w 1*w 2 - 8*v 2^2*w 0*w 1 - 2*v 2^2*w 0*w 2 + 2*v 2^2*w 2^2) * hu3
  · linear_combination (-2*u 1*v 0*w 1^2 - 4*u 1*v 0*w 1*w 2 - 5*u 1*v 0*w 2^2 + 6*u 1*v 1*w 1^2 + 24*u 1*v 1*w 1*w 2 + 13*u 1*v 1*w 2^2 + 2*u 1*v 2*w 1^2 + 10*u 1*v 2*w 1*w 2 + 7*u 1*v 2*w 2^2 + 3*u 1*v 3*w 2^2 + 2*u 2*v 0*w 1^2 + 4*u 2*v 0*w 1*w 2 - 7*u 2*v 0*w 2^2 - 6*u 2*v 1*w 1^2 + 8*u 2*v 1*w 1*w 2 + 15*u 2*v 1*w 2^2 - 2*u 2*v 2*w 1^2 - 6*u 2*v 2*w 1*w 2 + u 2*v 2*w 2^2 + 9*u 2*v 3*w 2^2 - 4*u 3*v 0*w 2^2 + 32*u 3*v 1*w 1*w 2 + 20*u 3*v 1*w 2^2 + 4*u 3*v 2*w 1*w 2 + 4*u 3*v 3*w 2^2) * hvk + (-2*u 1*v 0^2*w 0 + 2*u 1*v 0^2*w 1 + 2*u 1*v 0^2*w 2 - 4*u 1*v 0*v 1*w 1 - 4*u 1*v 0*v 2*w 2 + 4*u 1*v 0*v 3*w 0 + 4*u 1*v 1^2*w 0 - 4*u 1*v 1^2*w 1 - 20*u 1*v 1^2*w 2 - 4*u 1*v 1^2*w 3 - 4*u 1*v 1*v 2*w 1 - 18*u 1*v 1*v 2*w 2 + 4*u 1*v 1*v 3*w 1 + 5*u 1*v 2^2*w 0 - u 1*v 2^2*w 1 - 7*u 1*v 2^2*w 2 - 5*u 1*v 2^2*w 3 + 4*u 1*v 2*v 3*w 2 + 2*u 1*v 3^2*w 3 + 2*u 2*v 0^2*w 0 - 2*u 2*v 0^2*w 1 - 2*u 2*v 0^2*w 2 + 4*u 2*v 0*v 1*w 1 + 4*u 2*v 0*v 2*w 2 - 4*u 2*v 0*v 3*w 0 - 4*u 2*v 1^2*w 0 + 4*u 2*v 1^2*w 1 - 12*u 2*v 1^2*w 2 + 4*u 2*v 1^2*w 3 - 6*u 2*v 1*v 2*w 0 + 2*u 2*v 1*v 2*w 1 - 12*u 2*v 1*v 2*w 2 + 6*u 2*v 1*v 2*w 3 - 4*u 2*v 1*v 3*w 1 + u 2*v 2^2*w 0 + 3*u 2*v 2^2*w 1 - 3*u 2*v 2^2*w 2 - u 2*v 2^2*w 3 - 4*u 2*v 2*v 3*w 2 - 2*u 2*v 3^2*w 3 - 32*u 3*v 1^2*w 2 - 2*u 3*v 1*v 2*w 0 - 6*u 3*v 1*v 2*w 1 - 34*u 3*v 1*v 2*w 2 + 2*u 3*v 1*v 2*w 3 + 2*u 3*v 2^2*w 0 + 6*u 3*v 2^2*w 1 - 6*u 3*v 2^2*w 2 - 2*u 3*v 2^2*w 3) * hwk + (2*u 1*v 0*w 1^2 + 4*u 1*v 0*w 1*w 2 + 5*u 1*v 0*w 2^2 - 6*u 1*v 1*w 1^2 - 24*u 1*v 1*w 1*w 2 - 13*u 1*v 1*w 2^2 - 2*u 1*v 2*w 1^2 - 10*u 1*v 2*w 1*w 2 - 7*u 1*v 2*w 2^2 - 2*u 2*v 0*w 1^2 - 4*u 2*v 0*w 1*w 2 + 7*u 2*v 0*w 2^2 + 6*u 2*v 1*w 1^2 - 8*u 2*v 1*w 1*w 2 - 15*u 2*v 1*w 2^2 + 2*u 2*v 2*w 1^2 + 6*u 2*v 2*w 1*w 2 - u 2*v 2*w 2^2 + 4*u 3*v 0*w 2^2 - 16*u 3*v 1*w 1*w 2 - 12*u 3*v 1*w 2^2 - 2*u 3*v 2*w 1*w 2 - 2*u 3*v 2*w 2^2) * h1 + (2*u 1*v 0^2*w 0 - 2*u 1*v 0^2*w 1 - 2*u 1*v 0^2*w 2 + 4*u 1*v 0*v 1*w 1 + 4*u 1*v 0*v 2*w 2 - 4*u 1*v 1^2*w 0 + 4*u 1*v 1^2*w 1 + 20*u 1*v 1^2*w 2 + 4*u 1*v 1*v 2*w 1 + 18*u 1*v 1*v 2*w 2 - 5*u 1*v 2^2*w 0 + u 1*v 2^2*w 1 + 7*u 1*v 2^2*w 2 - 2*u 2*v 0^2*w 0 + 2*u 2*v 0^2*w 1 + 2*u 2*v 0^2*w 2 - 4*u 2*v 0*v 1*w 1 - 4*u 2*v 0*v 2*w 2 + 4*u 2*v 1^2*w 0 - 4*u 2*v 1^2*w 1 + 12*u 2*v 1^2*w 2 + 6*u 2*v 1*v 2*w 0 - 2*u 2*v 1*v 2*w 1 + 12*u 2*v 1*v 2*w 2 - u 2*v 2^2*w 0 - 3*u 2*v 2^2*w 1 + 3*u 2*v 2^2*w 2 + 16*u 3*v 1^2*w 2 + 2*u 3*v 1*v 2*w 0 + 2*u 3*v 1*v 2*w 1 + 16*u 3*v 1*v 2*w 2 - 2*u 3*v 2^2*w 0 - 2*u 3*v 2^2*w 1 + 4*u 3*v 2^2*w 2) * h2 + (-3*u 1*w 2^2 - 9*u 2*w 2^2 - 4*u 3*w 2^2) * h3 + (4*u 1*v 1^2 + 5*u 1*v 2^2 - 4*u 2*v 1^2 - 6*u 2*v 1*v 2 + u 2*v 2^2 - 2*u 3*v 1*v 2 + 2*u 3*v 2^2) * h4 + (-16*v 1*w 1*w 2 - 8*v 1*w 2^2 - 2*v 2*w 1*w 2 + 2*v 2*w 2^2) * hu1 + (16*v 1^2*w 2 + 4*v 1*v 2*w 1 + 18*v 1*v 2*w 2 - 4*v 2^2*w 1 + 2*v 2^2*w 2) * hu2 + (16*v 0*v 1*w 1*w 2 + 8*v 0*v 1*w 2^2 + 2*v 0*v 2*w 1*w 2 - 2*v 0*v 2*w 2^2 - 16*v 1^2*w 0*w 2 - 4*v 1*v 2*w 0*w 1 - 18*v 1*v 2*w 0*w 2 + 4*v 2^2*w 0*w 1 - 2*v 2^2*w 0*w 2) * hu3

theorem F2_scalar (za zb zc zk T lam : ℂ) (ea : za ^ 2 - T * za = lam) (eb : zb ^ 2 - T * zb = lam)
    (ec : zc ^ 2 - T * zc = lam) (ek : zk ^ 2 - T * zk = -3 * lam) (hs : za + zb + zc + zk = T) :
    (za = 0 ∧ zb = 0 ∧ zc = 0 ∧ zk = T) ∨ (za = T ∧ zb = 0 ∧ zc = 0 ∧ zk = 0) ∨
    (za = 0 ∧ zb = T ∧ zc = 0 ∧ zk = 0) ∨ (za = 0 ∧ zb = 0 ∧ zc = T ∧ zk = 0) ∨
    (za = T / 2 ∧ zb = T / 2 ∧ zc = T / 2 ∧ zk = -(T / 2)) := by
  have fab : (za - zb) * (za + zb - T) = 0 := by linear_combination ea - eb
  have fac : (za - zc) * (za + zc - T) = 0 := by linear_combination ea - ec
  rcases mul_eq_zero.mp fab with h1 | h1 <;> rcases mul_eq_zero.mp fac with h2 | h2
  · have hzk : zk = T - 3 * za := by linear_combination hs + h1 + h2
    have e : za * (2 * za - T) = 0 := by
      linear_combination (1 / 6 : ℂ) * ek + (1 / 2 : ℂ) * ea - ((zk + (T - 3 * za) - T) / 6) * hzk
    rcases mul_eq_zero.mp e with e1 | e1
    · exact Or.inl ⟨e1, by linear_combination e1 - h1, by linear_combination e1 - h2,
        by linear_combination hzk - 3 * e1⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linear_combination (1 / 2 : ℂ) * e1,
        by linear_combination (1 / 2 : ℂ) * e1 - h1, by linear_combination (1 / 2 : ℂ) * e1 - h2,
        by linear_combination hzk - (3 / 2 : ℂ) * e1⟩)))
  · have hzk : zk = -za := by linear_combination hs + h1 - h2
    have e : za * (2 * za - T) = 0 := by
      linear_combination (1 / 2 : ℂ) * ek + (3 / 2 : ℂ) * ea - ((zk - za - T) / 2) * hzk
    rcases mul_eq_zero.mp e with e1 | e1
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e1, by linear_combination e1 - h1,
        by linear_combination h2 - e1, by linear_combination hzk - e1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linear_combination (1 / 2 : ℂ) * e1,
        by linear_combination (1 / 2 : ℂ) * e1 - h1, by linear_combination h2 - (1 / 2 : ℂ) * e1,
        by linear_combination hzk - (1 / 2 : ℂ) * e1⟩)))
  · have hzk : zk = -za := by linear_combination hs - h1 + h2
    have e : za * (2 * za - T) = 0 := by
      linear_combination (1 / 2 : ℂ) * ek + (3 / 2 : ℂ) * ea - ((zk - za - T) / 2) * hzk
    rcases mul_eq_zero.mp e with e1 | e1
    · exact Or.inr (Or.inr (Or.inl ⟨e1, by linear_combination h1 - e1,
        by linear_combination e1 - h2, by linear_combination hzk - e1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linear_combination (1 / 2 : ℂ) * e1,
        by linear_combination h1 - (1 / 2 : ℂ) * e1, by linear_combination (1 / 2 : ℂ) * e1 - h2,
        by linear_combination hzk - (1 / 2 : ℂ) * e1⟩)))
  · have hzk : zk = za - T := by linear_combination hs - h1 - h2
    have e : (2 * za - T) * (za - T) = 0 := by
      linear_combination (1 / 2 : ℂ) * ek + (3 / 2 : ℂ) * ea - ((zk + (za - T) - T) / 2) * hzk
    rcases mul_eq_zero.mp e with e1 | e1
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linear_combination (1 / 2 : ℂ) * e1,
        by linear_combination h1 - (1 / 2 : ℂ) * e1, by linear_combination h2 - (1 / 2 : ℂ) * e1,
        by linear_combination hzk + (1 / 2 : ℂ) * e1⟩)))
    · exact Or.inr (Or.inl ⟨by linear_combination e1, by linear_combination h1 - e1,
        by linear_combination h2 - e1, by linear_combination hzk + e1⟩)

theorem pc_smul2 (c : ℂ) (x a b : V4) : pc (c • x) (c • x) a b = c ^ 2 * pc x x a b := by
  simp only [pc, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

theorem c2iii_h (v w : V4) (hv1 : tau v = 0) (hw1 : tau w = 0) (k0 : Fin 4) (hvk : v k0 = 0)
    (hwk : w k0 = 0) (hg : ip v w ≠ 0) (z : V4) (T : ℂ) (hz : z = (T / 2) • hvec k0)
    (hp : pc z z v w = 0) : T = 0 := by
  rw [hz, pc_smul2, pc_hvec v w hv1 hw1 k0 hvk hwk] at hp
  have e : T ^ 2 * ip v w = 0 := by linear_combination 2 * hp
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp e).resolve_right hg)

theorem c2iii_ei (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4) (hv0 : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0) (hw2 : ip w w = 0)
    (hvw : ∀ c : ℂ, w ≠ c • v)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w)
    (z : V4) (hzK : zE z ∈ K) (i j k l : Fin 4)
    (hipc : ∀ x y : V4, ip x y = x i * y i + x j * y j + x k * y k + x l * y l)
    (hzi : z i = tau z) (hzj : z j = 0) (hzk : z k = 0) (hzl : z l = 0) (hT : tau z ≠ 0)
    (Z : M45) (hZ : Z ∈ K) (h0 : rs Z = 0) (c2 : col Z 2 = v) (c3 : col Z 3 = (-1 : ℂ) • v)
    (c4 : col Z 4 = w) (hd : ∀ c : ℂ, dY Z ≠ c • z) : False := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  have hgw : ip w v ≠ 0 := by
    intro h
    apply hg
    simp only [ip] at h ⊢
    linear_combination h
  obtain ⟨he2z, he2b, -, -, -, -, -, -, -, -, -, -, -, -⟩ := LemmaZ K hdef z hzK Z hZ
  obtain ⟨Z', hZ'⟩ : ∃ Z' : M45, Z' = tau z • Z - tau (dY Z) • zE z := ⟨_, rfl⟩
  have hZ'K : Z' ∈ K := by
    rw [hZ']
    exact K.sub_mem (K.smul_mem _ hZ) (K.smul_mem _ hzK)
  have h0' : rs Z' = 0 := by
    rw [hZ', map_sub, map_smul, map_smul, h0, rs_zE, smul_zero, smul_zero, sub_zero]
  have hz0 : dY Z' = tau z • dY Z - tau (dY Z) • z := by
    have e1 := map_sub dYL (tau z • Z) (tau (dY Z) • zE z)
    rw [map_smul, map_smul, dYL_apply, dYL_apply, dYL_apply, dY_zE] at e1
    rw [hZ']
    exact e1
  have hz0ne : dY Z' ≠ 0 := by
    intro h
    apply hd (tau (dY Z) / tau z)
    funext m
    have e := congrFun h m
    rw [hz0] at e
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hT]
    linear_combination e
  have hτ0 : tau (dY Z') = 0 := by
    rw [hz0]
    simp only [tau, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he0 : e2b (dY Z') z = 0 := by
    rw [hz0]
    simp only [e2b, e2, tau, ip, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at he2b he2z ⊢
    linear_combination (z 0 + z 1 + z 2 + z 3) * he2b - (dY Z 0 + dY Z 1 + dY Z 2 + dY Z 3) * he2z
  have hz0i : dY Z' i = 0 := by
    have e : e2b (dY Z') z = (tau (dY Z') * tau z - ip (dY Z') z) / 2 := rfl
    rw [he0, hτ0, hipc, hzj, hzk, hzl, hzi] at e
    have e' : tau z * dY Z' i = 0 := by linear_combination 2 * e
    exact (mul_eq_zero.mp e').resolve_left hT
  have hEdb : ∀ x : V4, ip x (Edb (dY Z') z) = -(tau z / 2) * ip x (dY Z') := by
    intro x
    rw [hipc, hipc]
    simp only [Edb, he0, hτ0]
    rw [hzi, hzj, hzk, hzl, hz0i]
    ring
  have hf2 : ∀ Y ∈ K, ip (col Y 2) (Edb (dY Y) z) = 0 := fun Y hY => (DZ_perp K hdef z hzK Y hY).1
  have hf4 : ∀ Y ∈ K, ip (col Y 4) (Edb (dY Y) z) = 0 :=
    fun Y hY => (DZ_perp K hdef z hzK Y hY).2.2
  have hl2 : ∀ Y ∈ K, rs Y = 0 → ∃ c : ℂ, col Y 2 = c • v := by
    intro Y hY hY0
    obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Y hY hY0
    exact ⟨l3, e2⟩
  have hl4 : ∀ Y ∈ K, rs Y = 0 → ∃ c : ℂ, col Y 4 = c • w := by
    intro Y hY hY0
    obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Y hY hY0
    exact ⟨b, e4⟩
  have pv := perp_line K z 2 v hf2 hl2 Z hZ c2 Z' hZ'K h0'
  have pw := perp_line K z 4 w hf4 hl4 Z hZ c4 Z' hZ'K h0'
  rw [hEdb] at pv pw
  have hc : -(tau z / 2) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hT two_ne_zero)
  have hvz : ip v (dY Z') = 0 := (mul_eq_zero.mp pv).resolve_left hc
  have hwz : ip w (dY Z') = 0 := (mul_eq_zero.mp pw).resolve_left hc
  have huY : ∀ m, uY Z' m = -(tau z / 2) * w m := by
    intro m
    have R := congrFun h0 m
    rw [rs_apply] at R
    have E2 := congrFun c2 m
    have E3 := congrFun c3 m
    have E4 := congrFun c4 m
    simp only [col, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at R E2 E3 E4
    rw [hZ']
    simp only [uY, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE0, zE1]
    linear_combination (tau z / 2) * R - (tau z / 2) * (E2 + E3 + E4)
  have hiso : ip (dY Z') (dY Z') = 0 := by
    have q := qbar_pol K hdef Z' hZ'K h0' Z' hZ'K h0'
    have lhs0 : ip (uY Z') (uY Z') = 0 := by
      simp only [ip]
      rw [huY 0, huY 1, huY 2, huY 3]
      have hw2' := hw2
      simp only [ip] at hw2'
      linear_combination (tau z / 2) ^ 2 * hw2'
    rw [lhs0] at q
    have e : e2b (dY Z') (dY Z') = (tau (dY Z') * tau (dY Z') - ip (dY Z') (dY Z')) / 2 := rfl
    rw [hτ0] at e
    linear_combination q + 2 * e
  have hac : ∀ s : ℂ, dY Z' ≠ s • v := by
    intro s hs
    have e : ip w (dY Z') = s * ip w v := by
      rw [hs]
      simp only [ip, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hwz] at e
    have hs0 : s = 0 := (mul_eq_zero.mp e.symm).resolve_right hgw
    apply hz0ne
    rw [hs, hs0, zero_smul]
  have hbc : ∀ s : ℂ, dY Z' ≠ s • w := by
    intro s hs
    have e : ip v (dY Z') = s * ip v w := by
      rw [hs]
      simp only [ip, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hvz] at e
    have hs0 : s = 0 := (mul_eq_zero.mp e.symm).resolve_right hg
    apply hz0ne
    rw [hs, hs0, zero_smul]
  exact three_iso_perp (dY Z') v w (dY Z') hz0ne hτ0 hv1 hv2 hw1 hw2 hτ0 hiso hvz hwz hiso hv0 hvw
    hac hbc

theorem c2iii_core (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v w : V4) (hv0 : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0) (hw2 : ip w w = 0)
    (hvw : ∀ c : ℂ, w ≠ c • v)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • w)
    (hreal : ∀ l b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = l • v ∧ col Z 3 = (-l) • v ∧ col Z 4 = b • w)
    (hlag : ∀ z : V4, zE z ∈ K → ∀ Z ∈ K, rs Z = 0 → ∀ l b c : ℂ, l ≠ 0 → b ≠ 0 → col Z 2 = l • v →
      col Z 3 = (-l) • v → col Z 4 = b • w → dY Z ≠ c • z)
    (k0 a b c : Fin 4) (hvk : v k0 = 0) (hwk : w k0 = 0)
    (htc : ∀ x : V4, tau x = x a + x b + x c + x k0)
    (hipc : ∀ x y : V4, ip x y = x a * y a + x b * y b + x c * y c + x k0 * y k0)
    (hha : hvec k0 a = 1) (hhb : hvec k0 b = 1) (hhc : hvec k0 c = 1) (hhk : hvec k0 k0 = -1)
    (hcov : ∀ m : Fin 4, m = a ∨ m = b ∨ m = c ∨ m = k0)
    (hU : ∀ u : V4, ip v u = 0 → ip w u = 0 → tau u = 0 → u a = u b ∧ u b = u c)
    (z : V4) (hz0 : z ≠ 0) (hzK : zE z ∈ K) : False := by
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hreal 1 1
  have hd : ∀ c' : ℂ, dY Z ≠ c' • z :=
    fun c' => hlag z hzK Z hZ h0 1 1 c' one_ne_zero one_ne_zero e2 e3 e4
  have c2 : col Z 2 = v := by rw [e2, one_smul]
  have c4 : col Z 4 = w := by rw [e4, one_smul]
  obtain ⟨he2z, -, iE2, -, iE4, -, p24, -⟩ := LemmaZ K hdef z hzK Z hZ
  rw [c2] at iE2
  rw [c4] at iE4
  rw [c2, c4] at p24
  have hτE : tau (Ed z) = 0 := by rw [tau_Ed, he2z, mul_zero]
  obtain ⟨u1, u2⟩ := hU (Ed z) iE2 iE4 hτE
  have hEd : ∀ m, Ed z m = z m ^ 2 - tau z * z m := by
    intro m
    simp only [Ed]
    rw [he2z]
    ring
  have ea : z a ^ 2 - tau z * z a = Ed z a := (hEd a).symm
  have eb : z b ^ 2 - tau z * z b = Ed z a := by rw [← hEd b, u1]
  have ec : z c ^ 2 - tau z * z c = Ed z a := by rw [← hEd c, u1, u2]
  have ek : z k0 ^ 2 - tau z * z k0 = -3 * Ed z a := by
    have t := htc (Ed z)
    rw [hτE, ← u2, ← u1] at t
    rw [← hEd k0]
    linear_combination -t
  have hs : z a + z b + z c + z k0 = tau z := (htc z).symm
  have zero_of : z a = 0 → z b = 0 → z c = 0 → z k0 = 0 → False := by
    intro a0 b0 c0 k00
    apply hz0
    funext m
    rcases hcov m with h | h | h | h
    · rw [h]; exact a0
    · rw [h]; exact b0
    · rw [h]; exact c0
    · rw [h]; exact k00
  have hip1 : ∀ x y : V4, ip x y = x k0 * y k0 + x a * y a + x b * y b + x c * y c := by
    intro x y
    rw [hipc]
    ring
  have hip2 : ∀ x y : V4, ip x y = x b * y b + x a * y a + x c * y c + x k0 * y k0 := by
    intro x y
    rw [hipc]
    ring
  have hip3 : ∀ x y : V4, ip x y = x c * y c + x a * y a + x b * y b + x k0 * y k0 := by
    intro x y
    rw [hipc]
    ring
  rcases F2_scalar (z a) (z b) (z c) (z k0) (tau z) (Ed z a) ea eb ec ek hs with
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · by_cases hT : tau z = 0
    · exact zero_of h1 h2 h3 (by rw [h4, hT])
    · exact c2iii_ei K hdef v w hv0 hv1 hv2 hw1 hw2 hvw hline z hzK k0 a b c hip1 h4 h1 h2 h3 hT
        Z hZ h0 c2 e3 c4 hd
  · by_cases hT : tau z = 0
    · exact zero_of (by rw [h1, hT]) h2 h3 h4
    · exact c2iii_ei K hdef v w hv0 hv1 hv2 hw1 hw2 hvw hline z hzK a b c k0 hipc h1 h2 h3 h4 hT
        Z hZ h0 c2 e3 c4 hd
  · by_cases hT : tau z = 0
    · exact zero_of h1 (by rw [h2, hT]) h3 h4
    · exact c2iii_ei K hdef v w hv0 hv1 hv2 hw1 hw2 hvw hline z hzK b a c k0 hip2 h2 h1 h3 h4 hT
        Z hZ h0 c2 e3 c4 hd
  · by_cases hT : tau z = 0
    · exact zero_of h1 h2 (by rw [h3, hT]) h4
    · exact c2iii_ei K hdef v w hv0 hv1 hv2 hw1 hw2 hvw hline z hzK c a b k0 hip3 h3 h1 h2 h4 hT
        Z hZ h0 c2 e3 c4 hd
  · have hzf : z = (tau z / 2) • hvec k0 := by
      funext m
      simp only [Pi.smul_apply, smul_eq_mul]
      rcases hcov m with h | h | h | h
      · rw [h, hha, h1, mul_one]
      · rw [h, hhb, h2, mul_one]
      · rw [h, hhc, h3, mul_one]
      · rw [h, hhk, h4]
        ring
    have hT := c2iii_h v w hv1 hw1 k0 hvk hwk hg z (tau z) hzf p24
    exact zero_of (by rw [h1, hT]; ring) (by rw [h2, hT]; ring) (by rw [h3, hT]; ring)
      (by rw [h4, hT]; ring)

theorem C2iiiLag_proof : C2iiiLagHyp := by
  intro K hdef hK5 v w hv0 hv1 hv2 hw1 hw2 hvw hline hreal hlag
  have hg : ip v w ≠ 0 := ip_ne_of_line v w hv0 hv1 hv2 hw1 hw2 hvw
  have hg' : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 ≠ 0 := hg
  have cancel : ∀ x : ℂ, 2 * ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) ^ 2 * x) = 0 → x = 0 := by
    intro x hx
    have h1 := (mul_eq_zero.mp hx).resolve_left two_ne_zero
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hg')
  obtain ⟨-, -, k0, hvk, hwk⟩ := c2iii_zero_row K hdef v w hv0 hv1 hv2 hw1 hw2 hvw hreal
  obtain ⟨-, -, -, z, hz0, hzK⟩ := TC5_dims K hdef hK5
  have core := c2iii_core K hdef v w hv0 hv1 hv2 hw1 hw2 hvw hline hreal hlag
  fin_cases k0
  · refine core 0 1 2 3 hvk hwk (fun x => by simp only [tau]; ring) (fun x y => by simp only [ip]; ring)
      (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (fun m => by fin_cases m <;> decide)
      (fun u h1 h2 h3 => ?_) z hz0 hzK
    obtain ⟨e1, e2⟩ := uconst_0 v w u hvk hwk hv1 hw1 hv2 hw2 h1 h2 h3
    exact ⟨sub_eq_zero.mp (cancel _ e1), sub_eq_zero.mp (cancel _ e2)⟩
  · refine core 1 0 2 3 hvk hwk (fun x => by simp only [tau]; ring) (fun x y => by simp only [ip]; ring)
      (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (fun m => by fin_cases m <;> decide)
      (fun u h1 h2 h3 => ?_) z hz0 hzK
    obtain ⟨e1, e2⟩ := uconst_1 v w u hvk hwk hv1 hw1 hv2 hw2 h1 h2 h3
    exact ⟨sub_eq_zero.mp (cancel _ e1), sub_eq_zero.mp (cancel _ e2)⟩
  · refine core 2 0 1 3 hvk hwk (fun x => by simp only [tau]; ring) (fun x y => by simp only [ip]; ring)
      (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (fun m => by fin_cases m <;> decide)
      (fun u h1 h2 h3 => ?_) z hz0 hzK
    obtain ⟨e1, e2⟩ := uconst_2 v w u hvk hwk hv1 hw1 hv2 hw2 h1 h2 h3
    exact ⟨sub_eq_zero.mp (cancel _ e1), sub_eq_zero.mp (cancel _ e2)⟩
  · refine core 3 0 1 2 hvk hwk (fun x => rfl) (fun x y => rfl)
      (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (by simp [hvec]) (fun m => by fin_cases m <;> decide)
      (fun u h1 h2 h3 => ?_) z hz0 hzK
    obtain ⟨e1, e2⟩ := uconst_3 v w u hvk hwk hv1 hw1 hv2 hw2 h1 h2 h3
    exact ⟨sub_eq_zero.mp (cancel _ e1), sub_eq_zero.mp (cancel _ e2)⟩

theorem TC5_of_c1 (H1 : C1Hyp) (K : Submodule ℂ M45) (hdef : DefLine K mTC) :
    Module.finrank ℂ K ≤ 4 :=
  TC5_main' H1 C2iiiLag_proof K hdef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem noline (x3 x4 x5 y3 y4 y5 : ℂ)
    (h1 : (x3 + x4) * (x4 + x5) * (x5 + x3) - x3 * x4 * x5 = 0)
    (h2 : (y3 + y4) * (y4 + y5) * (y5 + y3) - y3 * y4 * y5 = 0)
    (h3 : (x3 + y3 + (x4 + y4)) * (x4 + y4 + (x5 + y5)) * (x5 + y5 + (x3 + y3))
      - (x3 + y3) * (x4 + y4) * (x5 + y5) = 0)
    (h4 : (x3 - y3 + (x4 - y4)) * (x4 - y4 + (x5 - y5)) * (x5 - y5 + (x3 - y3))
      - (x3 - y3) * (x4 - y4) * (x5 - y5) = 0) :
    x3 * y4 - x4 * y3 = 0 ∧ x3 * y5 - x5 * y3 = 0 ∧ x4 * y5 - x5 * y4 = 0 := by
  have e34 : 4 * (x3*y4 - x4*y3) ^ 4 = 0 := by
    linear_combination (-12*x3^3*y4^2 + 56*x3^3*y4*y5 + 64*x3^3*y5^2 - 56*x3^2*x4*y3*y4 - 56*x3^2*x4*y3*y5 - 12*x3^2*x4*y4^2 + 1082*x3^2*x4*y4*y5 - 16198*x3^2*x4*y5^2 - 64*x3^2*x5*y3*y4 - 80*x3^2*x5*y3*y5 + 46*x3^2*x5*y4^2 - 312*x3^2*x5*y4*y5 - 17514*x3^2*x5*y5^2 - 23144*x3^2*y3*y4*y5 - 23144*x3^2*y3*y5^2 + 6*x3^2*y4^3 - 34210*x3^2*y4^2*y5 - 62616*x3^2*y4*y5^2 - 28400*x3^2*y5^3 - 20*x3*x4^2*y3*y4 - 36*x3*x4^2*y3*y5 - 8*x3*x4^2*y4^2 + 920*x3*x4^2*y4*y5 - 18112*x3*x4^2*y5^2 + 722*x3*x4*x5*y3*y4 + 730*x3*x4*x5*y3*y5 + 20*x3*x4*x5*y4^2 - 1512*x3*x4*x5*y4*y5 - 17306*x3*x4*x5*y5^2 + 12*x3*x4*y3*y4^2 - 68346*x3*x4*y3*y4*y5 - 56886*x3*x4*y3*y5^2 + 12*x3*x4*y4^3 - 68402*x3*x4*y4^2*y5 - 67872*x3*x4*y4*y5^2 - 5280*x3*x4*y5^3 + 8*x3*x5^2*y3^2 - 1362*x3*x5^2*y3*y4 - 1326*x3*x5^2*y3*y5 - 46*x3*x5^2*y4^2 - 2142*x3*x5^2*y4*y5 - 18950*x3*x5^2*y5^2 + 29*x3*x5*y3^2*y4 + 29*x3*x5*y3^2*y5 - 45*x3*x5*y3*y4^2 - 68317*x3*x5*y3*y4*y5 - 56771*x3*x5*y3*y5^2 - 18*x3*x5*y4^3 - 11031*x3*x5*y4^2*y5 - 73635*x3*x5*y4*y5^2 - 56800*x3*x5*y5^3 + 23895*x3*y3^2*y4*y5 + 23907*x3*y3^2*y5^2 + 25329*x3*y3*y4^2*y5 - 8661*x3*y3*y4*y5^2 - 9979*x3*y3*y5^3 + 16*x3*y4^4 + 1136*x3*y4^3*y5 + 10961*x3*y4^2*y5^2 + 10727*x3*y4*y5^3 - 16334*x3*y5^4 - 4*x4^3*y3^2 + 76*x4^3*y3*y4 + 72*x4^3*y3*y5 + 36*x4^3*y4^2 + 530*x4^3*y4*y5 + 72*x4^3*y5^2 + 4*x4^2*x5*y3^2 - 474*x4^2*x5*y3*y4 - 462*x4^2*x5*y3*y5 + 80*x4^2*x5*y4^2 + 1092*x4^2*x5*y4*y5 - 17498*x4^2*x5*y5^2 + 30*x4^2*y3*y4^2 - 34106*x4^2*y3*y4*y5 - 28400*x4^2*y3*y5^2 + 24*x4^2*y4^3 - 23176*x4^2*y4^2*y5 - 57312*x4^2*y4*y5^2 - 28400*x4^2*y5^3 + 1432*x4*x5^2*y3*y4 + 1444*x4*x5^2*y3*y5 + 80*x4*x5^2*y4^2 - 156*x4*x5^2*y4*y5 - 17036*x4*x5^2*y5^2 + 10*x4*x5*y3^2*y4 + 10*x4*x5*y3^2*y5 + 78*x4*x5*y3*y4^2 - 10852*x4*x5*y3*y4*y5 - 5184*x4*x5*y3*y5^2 + 12*x4*x5*y4^3 - 68276*x4*x5*y4^2*y5 - 125088*x4*x5*y4*y5^2 - 56800*x4*x5*y5^3 + 60*x4*y3^3*y4 + 60*x4*y3^3*y5 + 151*x4*y3^2*y4^2 - 507*x4*y3^2*y4*y5 - 19422*x4*y3^2*y5^2 + 39*x4*y3*y4^3 + 1125*x4*y3*y4^2*y5 - 33191*x4*y3*y4*y5^2 - 20180*x4*y3*y5^3 - 36*x4*y4^4 - 415*x4*y4^3*y5 + 989*x4*y4^2*y5^2 - 34102*x4*y4*y5^3 - 18248*x4*y5^4 + 4*x5^3*y3^2 + 42*x5^3*y3*y4 + 58*x5^3*y3*y5 + 38*x5^3*y4^2 - 1314*x5^3*y4*y5 - 64*x5^3*y5^2 + 61*x5^2*y3^2*y4 + 61*x5^2*y3^2*y5 + 67*x5^2*y3*y4^2 - 34045*x5^2*y3*y4*y5 - 28315*x5^2*y3*y5^2 + 6*x5^2*y4^3 - 34107*x5^2*y4^2*y5 - 51521*x5^2*y4*y5^2 - 23120*x5^2*y5^3 + 134*x5*y3^3*y4 + 134*x5*y3^3*y5 + 71*x5*y3^2*y4^2 - 234015*x5*y3^2*y4*y5 - 252980*x5*y3^2*y5^2 - 121*x5*y3*y4^3 - 238187*x5*y3*y4^2*y5 - 251817*x5*y3*y4*y5^2 - 270602*x5*y3*y5^3 - 72*x5*y4^4 + 453*x5*y4^3*y5 - 251547*x5*y4^2*y5^2 - 269230*x5*y4*y5^3 + 64*x5*y5^4 + 23722*y3^3*y4*y5 + 23722*y3^3*y5^2 - 11*y3^2*y4^3 - 54916*y3^2*y4^2*y5 - 1230124*y3^2*y4*y5^2 - 1174641*y3^2*y5^3 - 35*y3*y4^4 - 55666*y3*y4^3*y5 - 1299777*y3*y4^2*y5^2 - 1299728*y3*y4*y5^3 - 1175243*y3*y5^4 - 24*y4^5 + 23171*y4^4*y5 - 32532*y4^3*y5^2 - 1230884*y4^2*y5^3 - 1152037*y4*y5^4 + 23120*y5^5) * h1 + (-36*x3^3*x4*y4 - 276*x3^3*x4*y5 + 7*x3^3*x5*y4 - 257*x3^3*x5*y5 - 22855*x3^3*y4*y5 - 22855*x3^3*y5^2 - 36*x3^2*x4^2*y3 - 96*x3^2*x4^2*y4 + 66*x3^2*x4^2*y5 - 36*x3^2*x4*x5*y3 + 910*x3^2*x4*x5*y4 + 3416*x3^2*x4*x5*y5 + 21*x3^2*x4*y4^2 + 873*x3^2*x4*y4*y5 + 797496*x3^2*x4*y5^2 + 12*x3^2*x5^2*y3 - 2194*x3^2*x5^2*y4 + 56*x3^2*x5^2*y5 + 58*x3^2*x5*y3*y4 + 58*x3^2*x5*y3*y5 - 148*x3^2*x5*y4^2 + 13520*x3^2*x5*y4*y5 + 810919*x3^2*x5*y5^2 + 24*x3^2*y3*y4^2 + 47678*x3^2*y3*y4*y5 + 47662*x3^2*y3*y5^2 - 3*x3^2*y4^3 - 685*x3^2*y4^2*y5 - 339938*x3^2*y4*y5^2 - 315429*x3^2*y5^3 - 24*x3*x4^3*y3 - 100*x3*x4^3*y4 + 958*x3*x4^3*y5 + 51*x3*x4^2*x5*y3 - 218*x3*x4^2*x5*y4 - 2238*x3*x4^2*x5*y5 + 42*x3*x4^2*y3*y4 - 26299*x3*x4^2*y3*y5 + 42*x3*x4^2*y4^2 - 12767*x3*x4^2*y4*y5 + 797520*x3*x4^2*y5^2 + 15*x3*x4*x5^2*y3 + 698*x3*x4*x5^2*y4 + 824*x3*x4*x5^2*y5 + 29*x3*x4*x5*y3^2 + 24*x3*x4*x5*y3*y4 - 26308*x3*x4*x5*y3*y5 - 137*x3*x4*x5*y4^2 + 70369*x3*x4*x5*y4*y5 + 854279*x3*x4*x5*y5^2 + 40*x3*x4*y3^2*y4 + 23935*x3*x4*y3^2*y5 - 12*x3*x4*y3*y4^2 - 1924*x3*x4*y3*y4*y5 - 656079*x3*x4*y3*y5^2 - 15*x3*x4*y4^3 - 48886*x3*x4*y4^2*y5 - 653418*x3*x4*y4*y5^2 - 315475*x3*x4*y5^3 - 39*x3*x5^3*y3 - 2094*x3*x5^3*y4 - 517*x3*x5^3*y5 + 29*x3*x5^2*y3^2 + 55*x3*x5^2*y3*y4 - 167*x3*x5^2*y3*y5 - 63*x3*x5^2*y4^2 + 13505*x3*x5^2*y4*y5 + 810344*x3*x5^2*y5^2 + 99*x3*x5*y3^2*y4 + 24002*x3*x5*y3^2*y5 - 221*x3*x5*y3*y4^2 - 494810*x3*x5*y3*y4*y5 - 1101063*x3*x5*y3*y5^2 - 112*x3*x5*y4^3 - 235063*x3*x5*y4^2*y5 - 573221*x3*x5*y4*y5^2 - 912995*x3*x5*y5^3 + 23433*x3*y3^2*y4*y5 + 23433*x3*y3^2*y5^2 - 34*x3*y3*y4^3 - 15979*x3*y3*y4^2*y5 - 688901*x3*y3*y4*y5^2 - 672667*x3*y3*y5^3 - 17*x3*y4^4 - 8134*x3*y4^3*y5 - 367467*x3*y4^2*y5^2 - 367450*x3*y4*y5^3 - 336478*x3*y5^4 + 88*x4^4*y3 + 36*x4^4*y4 + 542*x4^4*y5 - 756*x4^3*x5*y3 - 12*x4^3*x5*y4 + 796*x4^3*x5*y5 + 45*x4^3*y3*y4 - 12962*x4^3*y3*y5 + 24*x4^3*y4^2 - 23161*x4^3*y4*y5 - 36168*x4^3*y5^2 + 1139*x4^2*x5^2*y3 - 102*x4^2*x5^2*y4 + 710*x4^2*x5^2*y5 + 10*x4^2*x5*y3^2 + 122*x4^2*x5*y3*y4 - 13497*x4^2*x5*y3*y5 + 42*x4^2*x5*y4^2 - 12645*x4^2*x5*y4*y5 + 784312*x4^2*x5*y5^2 + 15*x4^2*y3^2*y4 + 46*x4^2*y3^2*y5 - 85*x4^2*y3*y4^2 - 24566*x4^2*y3*y4*y5 - 338764*x4^2*y3*y5^2 - 36*x4^2*y4^3 - 539*x4^2*y4^2*y5 - 24602*x4^2*y4*y5^2 - 339306*x4^2*y5^3 + 1691*x4*x5^3*y3 + 294*x4*x5^3*y4 + 1397*x4*x5^3*y5 + 71*x4*x5^2*y3^2 + 210*x4*x5^2*y3*y4 - 13402*x4*x5^2*y3*y5 - 65*x4*x5^2*y4^2 + 334*x4*x5^2*y4*y5 + 810344*x4*x5^2*y5^2 - 402*x4*x5*y3^2*y4 - 236079*x4*x5*y3^2*y5 + 6*x4*x5*y3*y4^2 - 496752*x4*x5*y3*y4*y5 - 576847*x4*x5*y3*y5^2 - 103*x4*x5*y4^3 - 49534*x4*x5*y4^2*y5 - 1198307*x4*x5*y4*y5^2 - 914909*x4*x5*y5^3 + 4*x4*y3^2*y4^2 - 21144*x4*y3^2*y4*y5 - 349440*x4*y3^2*y5^2 - 37*x4*y3*y4^3 - 29388*x4*y3*y4^2*y5 - 717306*x4*y3*y4*y5^2 - 372646*x4*y3*y5^3 - 24*x4*y4^4 + 23169*x4*y4^3*y5 - 6206*x4*y4^2*y5^2 - 694145*x4*y4*y5^3 - 336478*x4*y5^4 + 715*x5^4*y3 - 657*x5^4*y4 - 64*x5^4*y5 + 61*x5^3*y3^2 + 56*x5^3*y3*y4 + 117*x5^3*y3*y5 - 6*x5^3*y4^2 - 23089*x5^3*y4*y5 - 23120*x5^3*y5^2 - 4*x5^2*y3^3 + 598*x5^2*y3^2*y4 - 235134*x5^2*y3^2*y5 - 785*x5^2*y3*y4^2 - 259941*x5^2*y3*y4*y5 - 810227*x5^2*y3*y5^2 - 124*x5^2*y4^3 - 259869*x5^2*y4^2*y5 - 808855*x5^2*y4*y5^2 + 64*x5^2*y5^3 - 22*x5*y3^2*y4^2 - 8237*x5*y3^2*y4*y5 - 336507*x5*y3^2*y5^2 - 84*x5*y3*y4^3 - 31477*x5*y3*y4^2*y5 - 376086*x5*y3*y4*y5^2 - 673009*x5*y3*y5^3 - 17*x5*y4^4 - 8266*x5*y4^3*y5 - 352904*x5*y4^2*y5^2 - 649803*x5*y4*y5^3 + 23120*x5*y5^4 - 11*y3^2*y4^3 - 24528*y3^2*y4^2*y5 - 363777*y3^2*y4*y5^2 - 339260*y3^2*y5^3 - 11*y3*y4^4 - 24528*y3*y4^3*y5 - 363788*y3*y4^2*y5^2 - 363777*y3*y4*y5^3 - 339260*y3*y5^4 - 11*y4^4*y5 - 24528*y4^3*y5^2 - 363777*y4^2*y5^3 - 339260*y4*y5^4) * h2 + (6*x3^3*y4^2 - 28*x3^3*y4*y5 - 32*x3^3*y5^2 + 28*x3^2*x4*y3*y4 + 28*x3^2*x4*y3*y5 + 6*x3^2*x4*y4^2 - 541*x3^2*x4*y4*y5 + 8099*x3^2*x4*y5^2 + 32*x3^2*x5*y3*y4 + 40*x3^2*x5*y3*y5 - 23*x3^2*x5*y4^2 + 156*x3^2*x5*y4*y5 + 8757*x3^2*x5*y5^2 - 12*x3^2*y3*y4^2 + 11628*x3^2*y3*y4*y5 + 11636*x3^2*y3*y5^2 - 7*x3^2*y4^3 + 17131*x3^2*y4^2*y5 + 31336*x3^2*y4*y5^2 + 14232*x3^2*y5^3 + 10*x3*x4^2*y3*y4 + 18*x3*x4^2*y3*y5 + 4*x3*x4^2*y4^2 - 460*x3*x4^2*y4*y5 + 9056*x3*x4^2*y5^2 - 361*x3*x4*x5*y3*y4 - 365*x3*x4*x5*y3*y5 - 10*x3*x4*x5*y4^2 + 756*x3*x4*x5*y4*y5 + 8653*x3*x4*x5*y5^2 - 20*x3*x4*y3^2*y4 - 20*x3*x4*y3^2*y5 - 16*x3*x4*y3*y4^2 + 34534*x3*x4*y3*y4*y5 + 29196*x3*x4*y3*y5^2 - 12*x3*x4*y4^3 + 34132*x3*x4*y4^2*y5 + 33032*x3*x4*y4*y5^2 + 2708*x3*x4*y5^3 - 4*x3*x5^2*y3^2 + 681*x3*x5^2*y3*y4 + 663*x3*x5^2*y3*y5 + 23*x3*x5^2*y4^2 + 1071*x3*x5^2*y4*y5 + 9475*x3*x5^2*y5^2 - 64*x3*x5*y3^2*y4 - 68*x3*x5*y3^2*y5 + 47*x3*x5*y3*y4^2 + 33136*x3*x5*y3*y4*y5 + 27769*x3*x5*y3*y5^2 + 22*x3*x5*y4^3 + 4796*x3*x5*y4^2*y5 + 35247*x3*x5*y4*y5^2 + 27746*x3*x5*y5^3 - 23664*x3*y3^2*y4*y5 - 23664*x3*y3^2*y5^2 + 6*x3*y3*y4^3 - 46302*x3*y3*y4^2*y5 - 74708*x3*y3*y4*y5^2 - 40492*x3*y3*y5^3 + 3*x3*y4^4 - 17105*x3*y4^3*y5 - 31825*x3*y4^2*y5^2 - 31828*x3*y4*y5^3 - 14200*x3*y5^4 + 2*x4^3*y3^2 - 38*x4^3*y3*y4 - 36*x4^3*y3*y5 - 18*x4^3*y4^2 - 265*x4^3*y4*y5 - 36*x4^3*y5^2 - 2*x4^2*x5*y3^2 + 237*x4^2*x5*y3*y4 + 231*x4^2*x5*y3*y5 - 40*x4^2*x5*y4^2 - 546*x4^2*x5*y4*y5 + 8749*x4^2*x5*y5^2 - 10*x4^2*y3^2*y4 - 10*x4^2*y3^2*y5 + 17*x4^2*y3*y4^2 + 17101*x4^2*y3*y4*y5 + 13965*x4^2*y3*y5^2 + 6*x4^2*y4^3 + 11847*x4^2*y4^2*y5 + 28722*x4^2*y4*y5^2 + 14236*x4^2*y5^3 - 716*x4*x5^2*y3*y4 - 722*x4*x5^2*y3*y5 - 40*x4*x5^2*y4^2 + 78*x4*x5^2*y4*y5 + 8518*x4*x5^2*y5^2 + 156*x4*x5*y3^2*y4 + 156*x4*x5*y3^2*y5 - 125*x4*x5*y3*y4^2 + 5731*x4*x5*y3*y4*y5 + 3520*x4*x5*y3*y5^2 + 32*x4*x5*y4^3 + 34310*x4*x5*y4^2*y5 + 62126*x4*x5*y4*y5^2 + 28703*x4*x5*y5^3 - 5*x4*y3^2*y4^2 - 10605*x4*y3^2*y4*y5 - 7732*x4*y3^2*y5^2 + 10*x4*y3*y4^3 - 27655*x4*y3*y4^2*y5 - 27402*x4*y3*y4*y5^2 + 3871*x4*y3*y5^3 + 12*x4*y4^4 - 11593*x4*y4^3*y5 - 39246*x4*y4^2*y5^2 - 38985*x4*y4*y5^3 - 14200*x4*y5^4 - 2*x5^3*y3^2 - 21*x5^3*y3*y4 - 29*x5^3*y3*y5 - 19*x5^3*y4^2 + 657*x5^3*y4*y5 + 32*x5^3*y5^2 + 2*x5^2*y3^3 - 367*x5^2*y3^2*y4 - 355*x5^2*y3^2*y5 + 316*x5^2*y3*y4^2 + 16768*x5^2*y3*y4*y5 + 13858*x5^2*y3*y5^2 + 16*x5^2*y4^3 + 16763*x5^2*y4^2*y5 + 24775*x5^2*y4*y5^2 + 11528*x5^2*y5^3 + 43*x5*y3^2*y4^2 + 100881*x5*y3^2*y4*y5 + 103706*x5*y3^2*y5^2 + 74*x5*y3*y4^3 + 112490*x5*y3*y4^2*y5 + 81200*x5*y3*y4*y5^2 + 89518*x5*y3*y5^3 + 3*x5*y4^4 - 17007*x5*y4^3*y5 + 69609*x5*y4^2*y5^2 + 77915*x5*y4*y5^3 - 11560*x5*y5^4 + 11*y3^2*y4^3 + 33436*y3^2*y4^2*y5 + 385494*y3^2*y4*y5^2 + 352069*y3^2*y5^3 + 11*y3*y4^4 + 33436*y3*y4^3*y5 + 385505*y3*y4^2*y5^2 + 385494*y3*y4*y5^3 + 352069*y3*y5^4 + 11*y4^4*y5 + 33436*y4^3*y5^2 + 385494*y4^2*y5^3 + 352069*y4*y5^4) * h3 + (6*x3^3*y4^2 - 28*x3^3*y4*y5 - 32*x3^3*y5^2 + 28*x3^2*x4*y3*y4 + 28*x3^2*x4*y3*y5 + 6*x3^2*x4*y4^2 - 541*x3^2*x4*y4*y5 + 8099*x3^2*x4*y5^2 + 32*x3^2*x5*y3*y4 + 40*x3^2*x5*y3*y5 - 23*x3^2*x5*y4^2 + 156*x3^2*x5*y4*y5 + 8757*x3^2*x5*y5^2 + 12*x3^2*y3*y4^2 + 11516*x3^2*y3*y4*y5 + 11508*x3^2*y3*y5^2 + x3^2*y4^3 + 17079*x3^2*y4^2*y5 + 31280*x3^2*y4*y5^2 + 14168*x3^2*y5^3 + 10*x3*x4^2*y3*y4 + 18*x3*x4^2*y3*y5 + 4*x3*x4^2*y4^2 - 460*x3*x4^2*y4*y5 + 9056*x3*x4^2*y5^2 - 361*x3*x4*x5*y3*y4 - 365*x3*x4*x5*y3*y5 - 10*x3*x4*x5*y4^2 + 756*x3*x4*x5*y4*y5 + 8653*x3*x4*x5*y5^2 + 20*x3*x4*y3^2*y4 + 20*x3*x4*y3^2*y5 + 4*x3*x4*y3*y4^2 + 33812*x3*x4*y3*y4*y5 + 27690*x3*x4*y3*y5^2 + 34270*x3*x4*y4^2*y5 + 34840*x3*x4*y4*y5^2 + 2572*x3*x4*y5^3 - 4*x3*x5^2*y3^2 + 681*x3*x5^2*y3*y4 + 663*x3*x5^2*y3*y5 + 23*x3*x5^2*y4^2 + 1071*x3*x5^2*y4*y5 + 9475*x3*x5^2*y5^2 + 35*x3*x5*y3^2*y4 + 39*x3*x5*y3^2*y5 - 2*x3*x5*y3*y4^2 + 35181*x3*x5*y3*y4*y5 + 29002*x3*x5*y3*y5^2 - 4*x3*x5*y4^3 + 6235*x3*x5*y4^2*y5 + 38388*x3*x5*y4*y5^2 + 29054*x3*x5*y5^3 - 231*x3*y3^2*y4*y5 - 231*x3*y3^2*y5^2 - 6*x3*y3*y4^3 + 22407*x3*y3*y4^2*y5 + 50813*x3*y3*y4*y5^2 + 16597*x3*y3*y5^3 - 3*x3*y4^4 + 17105*x3*y4^3*y5 + 7930*x3*y4^2*y5^2 + 7933*x3*y4*y5^3 + 14200*x3*y5^4 + 2*x4^3*y3^2 - 38*x4^3*y3*y4 - 36*x4^3*y3*y5 - 18*x4^3*y4^2 - 265*x4^3*y4*y5 - 36*x4^3*y5^2 - 2*x4^2*x5*y3^2 + 237*x4^2*x5*y3*y4 + 231*x4^2*x5*y3*y5 - 40*x4^2*x5*y4^2 - 546*x4^2*x5*y4*y5 + 8749*x4^2*x5*y5^2 + 10*x4^2*y3^2*y4 + 10*x4^2*y3^2*y5 - 47*x4^2*y3*y4^2 + 17005*x4^2*y3*y4*y5 + 14435*x4^2*y3*y5^2 - 30*x4^2*y4^3 + 11329*x4^2*y4^2*y5 + 28590*x4^2*y4*y5^2 + 14164*x4^2*y5^3 - 716*x4*x5^2*y3*y4 - 722*x4*x5^2*y3*y5 - 40*x4*x5^2*y4^2 + 78*x4*x5^2*y4*y5 + 8518*x4*x5^2*y5^2 - 166*x4*x5*y3^2*y4 - 166*x4*x5*y3^2*y5 + 47*x4*x5*y3*y4^2 + 5121*x4*x5*y3*y4*y5 + 1664*x4*x5*y3*y5^2 - 44*x4*x5*y4^3 + 33966*x4*x5*y4^2*y5 + 62962*x4*x5*y4*y5^2 + 28097*x4*x5*y5^3 + 10*x4*y3^2*y4^2 + 10584*x4*y3^2*y4*y5 + 7706*x4*y3^2*y5^2 - 5*x4*y3*y4^3 + 27634*x4*y3*y4^2*y5 + 27381*x4*y3*y4*y5^2 - 3897*x4*y3*y5^3 - 12*x4*y4^4 + 11598*x4*y4^3*y5 + 39225*x4*y4^2*y5^2 + 38959*x4*y4*y5^3 + 14200*x4*y5^4 - 2*x5^3*y3^2 - 21*x5^3*y3*y4 - 29*x5^3*y3*y5 - 19*x5^3*y4^2 + 657*x5^3*y4*y5 + 32*x5^3*y5^2 - 2*x5^2*y3^3 + 306*x5^2*y3^2*y4 + 294*x5^2*y3^2*y5 - 383*x5^2*y3*y4^2 + 17277*x5^2*y3*y4*y5 + 14457*x5^2*y3*y5^2 - 22*x5^2*y4^3 + 17344*x5^2*y4^2*y5 + 26746*x5^2*y4*y5^2 + 11592*x5^2*y5^3 + 32*x5*y3^2*y4^2 + 134977*x5*y3^2*y4*y5 + 132077*x5*y3^2*y5^2 + x5*y3*y4^3 + 123368*x5*y3*y4^2*y5 + 154658*x5*y3*y4*y5^2 + 146265*x5*y3*y5^3 - 3*x5*y4^4 + 17082*x5*y4^3*y5 + 166249*x5*y4^2*y5^2 + 157868*x5*y4*y5^3 + 11560*x5*y5^4 + 8908*y3^2*y4^2*y5 + 21717*y3^2*y4*y5^2 + 12809*y3^2*y5^3 + 8908*y3*y4^3*y5 + 21717*y3*y4^2*y5^2 + 21717*y3*y4*y5^3 + 12809*y3*y5^4 + 8908*y4^3*y5^2 + 21717*y4^2*y5^3 + 12809*y4*y5^4) * h4
  have e35 : 4 * (x3*y5 - x5*y3) ^ 4 = 0 := by
    linear_combination (-160*x3^3*y4*y5 - 164*x3^3*y5^2 - 292*x3^2*x4*y4*y5 + 14960*x3^2*x4*y5^2 - 80*x3^2*x5*y3*y4 - 96*x3^2*x5*y3*y5 - 2*x3^2*x5*y4^2 + 1606*x3^2*x5*y4*y5 + 16548*x3^2*x5*y5^2 + 12572*x3^2*y3*y4*y5 + 12572*x3^2*y3*y5^2 + 16168*x3^2*y4^2*y5 + 27722*x3^2*y4*y5^2 + 11554*x3^2*y5^3 + 254*x3*x4^2*y4*y5 + 16318*x3*x4^2*y5^2 - 2*x3*x4*x5*y3*y4 - 10*x3*x4*x5*y3*y5 - 4*x3*x4*x5*y4^2 + 3102*x3*x4*x5*y4*y5 + 16472*x3*x4*x5*y5^2 + 32336*x3*x4*y3*y4*y5 + 23108*x3*x4*y3*y5^2 + 32336*x3*x4*y4^2*y5 + 26704*x3*x4*y4*y5^2 - 1018*x3*x4*y5^3 + 8*x3*x5^2*y3^2 + 1750*x3*x5^2*y3*y4 + 1738*x3*x5^2*y3*y5 + 306*x3*x5^2*y4^2 + 3060*x3*x5^2*y4*y5 + 18616*x3*x5^2*y5^2 - 39*x3*x5*y3^2*y4 - 39*x3*x5*y3^2*y5 - 39*x3*x5*y3*y4^2 + 32297*x3*x5*y3*y4*y5 + 23069*x3*x5*y3*y5^2 + 3557*x3*x5*y4^2*y5 + 31279*x3*x5*y4*y5^2 + 23108*x3*x5*y5^3 - 12568*x3*y3^2*y4*y5 - 12556*x3*y3^2*y5^2 - 12674*x3*y3*y4^2*y5 + 19336*x3*y3*y4*y5^2 + 19270*x3*y3*y5^3 - 198*x3*y4^3*y5 + 534*x3*y4^2*y5^2 + 752*x3*y4*y5^3 + 15120*x3*y5^4 + 390*x4^3*y4*y5 - 230*x4^2*x5*y3*y4 - 230*x4^2*x5*y3*y5 - 308*x4^2*x5*y4^2 + 94*x4^2*x5*y4*y5 + 16868*x4^2*x5*y5^2 + 16168*x4^2*y3*y4*y5 + 11554*x4^2*y3*y5^2 + 12572*x4^2*y4^2*y5 + 28740*x4^2*y4*y5^2 + 11554*x4^2*y5^3 + 4*x4*x5^2*y3^2 - 1432*x4*x5^2*y3*y4 - 1432*x4*x5^2*y3*y5 - 4*x4*x5^2*y4^2 + 1762*x4*x5^2*y4*y5 + 17254*x4*x5^2*y5^2 + 3596*x4*x5*y3*y4*y5 - 1018*x4*x5*y3*y5^2 + 32336*x4*x5*y4^2*y5 + 55444*x4*x5*y4*y5^2 + 23108*x4*x5*y5^3 + 580*x4*y3^2*y4*y5 + 19020*x4*y3^2*y5^2 + 290*x4*y3*y4^2*y5 + 33748*x4*y3*y4*y5^2 + 18794*x4*y3*y5^3 - 390*x4*y4^3*y5 + 290*x4*y4^2*y5^2 + 32260*x4*y4*y5^3 + 16482*x4*y5^4 + 2*x5^3*y3*y4 - 10*x5^3*y3*y5 - 2*x5^3*y4^2 + 1434*x5^3*y4*y5 + 68*x5^3*y5^2 + x5^2*y3^2*y4 + x5^2*y3^2*y5 + x5^2*y3*y4^2 + 16169*x5^2*y3*y4*y5 + 11555*x5^2*y3*y5^2 + 16169*x5^2*y4^2*y5 + 24127*x5^2*y4*y5^2 + 12572*x5^2*y5^3 + 318*x5*y3^3*y4 + 318*x5*y3^3*y5 + 517*x5*y3^2*y4^2 + 123463*x5*y3^2*y4*y5 + 141956*x5*y3^2*y5^2 + 505*x5*y3*y4^3 + 127783*x5*y3*y4^2*y5 + 142481*x5*y3*y4*y5^2 + 158276*x5*y3*y5^3 + 308*x5*y4^4 + 237*x5*y4^3*y5 + 141731*x5*y4^2*y5^2 + 156832*x5*y4*y5^3 - 68*x5*y5^4 - 12572*y3^3*y4*y5 - 12572*y3^3*y5^2 + 25909*y3^2*y4^2*y5 + 643448*y3^2*y4*y5^2 + 617539*y3^2*y5^3 + 25909*y3*y4^3*y5 + 681164*y3*y4^2*y5^2 + 681164*y3*y4*y5^3 + 617539*y3*y5^4 - 12572*y4^4*y5 + 13337*y4^3*y5^2 + 643448*y4^2*y5^3 + 604967*y4*y5^4 - 12572*y5^5) * h1 + (480*x3^3*x4*y5 + 39*x3^3*x5*y4 + 495*x3^3*x5*y5 + 12572*x3^3*y4*y5 + 12572*x3^3*y5^2 + 84*x3^2*x4^2*y5 - 2088*x3^2*x4*x5*y5 - 424662*x3^2*x4*y5^2 + 12*x3^2*x5^2*y3 + 2418*x3^2*x5^2*y4 + 816*x3^2*x5^2*y5 - 78*x3^2*x5*y3*y4 - 78*x3^2*x5*y3*y5 - 6241*x3^2*x5*y4*y5 - 430942*x3^2*x5*y5^2 - 24816*x3^2*y3*y4*y5 - 24808*x3^2*y3*y5^2 + 13*x3^2*y4^2*y5 + 172404*x3^2*y4*y5^2 + 159979*x3^2*y5^3 - 8*x3*x4^3*y5 + 39*x3*x4^2*x5*y3 - 162*x3*x4^2*x5*y4 + 1986*x3*x4^2*x5*y5 + 12560*x3*x4^2*y3*y5 + 6280*x3*x4^2*y4*y5 - 424662*x3*x4^2*y5^2 + 39*x3*x4*x5^2*y3 + 912*x3*x4*x5^2*y4 + 522*x3*x4*x5^2*y5 - 39*x3*x4*x5*y3^2 + 12599*x3*x4*x5*y3*y5 + 78*x3*x4*x5*y4^2 - 37677*x3*x4*x5*y4*y5 - 456098*x3*x4*x5*y5^2 - 12568*x3*x4*y3^2*y5 + 24*x3*x4*y3*y4*y5 + 334120*x3*x4*y3*y5^2 + 24616*x3*x4*y4^2*y5 + 331031*x3*x4*y4*y5^2 + 159983*x3*x4*y5^3 - 131*x3*x5^3*y3 + 2194*x3*x5^3*y4 + 1131*x3*x5^3*y5 - 39*x3*x5^2*y3^2 + 41*x3*x5^2*y3*y4 + 2*x3*x5^2*y3*y5 + x3*x5^2*y4^2 - 6240*x3*x5^2*y4*y5 - 430863*x3*x5^2*y5^2 + 199*x3*x5*y3^2*y4 - 12361*x3*x5*y3^2*y5 + 41*x3*x5*y3*y4^2 + 260311*x3*x5*y3*y4*y5 + 569665*x3*x5*y3*y5^2 - 39*x3*x5*y4^3 + 123710*x3*x5*y4^2*y5 + 294964*x3*x5*y4*y5^2 + 468689*x3*x5*y5^3 - 12572*x3*y3^2*y4*y5 - 12572*x3*y3^2*y5^2 + 6922*x3*y3*y4^2*y5 + 357008*x3*y3*y4*y5^2 + 350086*x3*y3*y5^3 + 3461*x3*y4^3*y5 + 191076*x3*y4^2*y5^2 + 191076*x3*y4*y5^3 + 175043*x3*y5^4 + 390*x4^4*y5 - 150*x4^3*x5*y3 - 308*x4^3*x5*y4 - 88*x4^3*x5*y5 + 6280*x4^3*y3*y5 + 12572*x4^3*y4*y5 + 18852*x4^3*y5^2 - 2775*x4^2*x5^2*y3 - 162*x4^2*x5^2*y4 + 180*x4^2*x5^2*y5 + 39*x4^2*x5*y3*y4 + 6319*x4^2*x5*y3*y5 + 6319*x4^2*x5*y4*y5 - 418343*x4^2*x5*y5^2 + 12421*x4^2*y3*y4*y5 + 172777*x4^2*y3*y5^2 - 390*x4^2*y4^2*y5 + 12421*x4^2*y4*y5^2 + 172387*x4^2*y5^3 - 2555*x4*x5^3*y3 - 252*x4*x5^3*y4 - 231*x4*x5^3*y5 + x4*x5^2*y3^2 + 41*x4*x5^2*y3*y4 + 6320*x4*x5^2*y3*y5 + 78*x4*x5^2*y4^2 + 158*x4*x5^2*y4*y5 - 430863*x4*x5^2*y5^2 + 39*x4*x5*y3^2*y4 + 125743*x4*x5*y3^2*y5 + 228*x4*x5*y3*y4^2 + 263866*x4*x5*y3*y4*y5 + 299724*x4*x5*y3*y5^2 + 308*x4*x5*y4^3 + 24774*x4*x5*y4^2*y5 + 619243*x4*x5*y4*y5^2 + 470051*x4*x5*y5^3 + 9741*x4*y3^2*y4*y5 + 181323*x4*y3^2*y5^2 + 13202*x4*y3*y4^2*y5 + 372399*x4*y3*y4*y5^2 + 193895*x4*y3*y5^3 - 12572*x4*y4^3*y5 + 630*x4*y4^2*y5^2 + 359827*x4*y4*y5^3 + 175043*x4*y5^4 - 885*x5^4*y3 + 559*x5^4*y4 + 68*x5^4*y5 + x5^3*y3^2 + 40*x5^3*y3*y4 + 41*x5^3*y3*y5 + 40*x5^3*y4^2 + 12613*x5^3*y4*y5 + 12572*x5^3*y5^2 - 4*x5^2*y3^3 - 924*x5^2*y3^2*y4 + 124788*x5^2*y3^2*y5 + 516*x5^2*y3*y4^2 + 137191*x5^2*y3*y4*y5 + 422848*x5^2*y3*y5^2 - 39*x5^2*y4^3 + 137131*x5^2*y4^2*y5 + 421404*x5^2*y4*y5^2 - 68*x5^2*y5^3 + 39*x5*y3^2*y4^2 + 3539*x5*y3^2*y4*y5 + 175082*x5*y3^2*y5^2 + 39*x5*y3*y4^3 + 16111*x5*y3*y4^2*y5 + 194615*x5*y3*y4*y5^2 + 350125*x5*y3*y5^3 + 3500*x5*y4^3*y5 + 182043*x5*y4^2*y5^2 + 337553*x5*y4*y5^3 - 12572*x5*y5^4 + 12421*y3^2*y4^2*y5 + 184808*y3^2*y4*y5^2 + 172387*y3^2*y5^3 + 12421*y3*y4^3*y5 + 184808*y3*y4^2*y5^2 + 184808*y3*y4*y5^3 + 172387*y3*y5^4 + 12421*y4^3*y5^2 + 184808*y4^2*y5^3 + 172387*y4*y5^4) * h2 + (80*x3^3*y4*y5 + 82*x3^3*y5^2 + 146*x3^2*x4*y4*y5 - 7480*x3^2*x4*y5^2 + 40*x3^2*x5*y3*y4 + 48*x3^2*x5*y3*y5 + x3^2*x5*y4^2 - 803*x3^2*x5*y4*y5 - 8274*x3^2*x5*y5^2 - 6446*x3^2*y3*y4*y5 - 6450*x3^2*y3*y5^2 - 8164*x3^2*y4^2*y5 - 13943*x3^2*y4*y5^2 - 5857*x3^2*y5^3 - 127*x3*x4^2*y4*y5 - 8159*x3*x4^2*y5^2 + x3*x4*x5*y3*y4 + 5*x3*x4*x5*y3*y5 + 2*x3*x4*x5*y4^2 - 1551*x3*x4*x5*y4*y5 - 8236*x3*x4*x5*y5^2 - 16327*x3*x4*y3*y4*y5 - 12511*x3*x4*y3*y5^2 - 16055*x3*x4*y4^2*y5 - 12838*x3*x4*y4*y5^2 + 427*x3*x4*y5^3 - 4*x3*x5^2*y3^2 - 875*x3*x5^2*y3*y4 - 869*x3*x5^2*y3*y5 - 153*x3*x5^2*y4^2 - 1530*x3*x5^2*y4*y5 - 9308*x3*x5^2*y5^2 - 80*x3*x5*y3^2*y4 - 84*x3*x5*y3^2*y5 - 42*x3*x5*y3*y4^2 - 14545*x3*x5*y3*y4*y5 - 10885*x3*x5*y3*y5^2 - x3*x5*y4^3 - 896*x3*x5*y4^2*y5 - 14264*x3*x5*y4*y5^2 - 10680*x3*x5*y5^3 + 12570*x3*y3^2*y4*y5 + 12570*x3*y3^2*y5^2 + 22452*x3*y3*y4^2*y5 + 34006*x3*y3*y4*y5^2 + 17838*x3*y3*y5^3 + 8084*x3*y4^3*y5 + 13859*x3*y4^2*y5^2 + 13859*x3*y4*y5^3 + 5777*x3*y5^4 - 195*x4^3*y4*y5 + 115*x4^2*x5*y3*y4 + 115*x4^2*x5*y3*y5 + 154*x4^2*x5*y4^2 - 47*x4^2*x5*y4*y5 - 8434*x4^2*x5*y5^2 - 8084*x4^2*y3*y4*y5 - 5972*x4^2*y3*y5^2 - 6091*x4^2*y4^2*y5 - 14370*x4^2*y4*y5^2 - 5777*x4^2*y5^3 - 2*x4*x5^2*y3^2 + 716*x4*x5^2*y3*y4 + 716*x4*x5^2*y3*y5 + 2*x4*x5^2*y4^2 - 881*x4*x5^2*y4*y5 - 8627*x4*x5^2*y5^2 - 40*x4*x5*y3^2*y4 - 40*x4*x5*y3^2*y5 - 155*x4*x5*y3*y4^2 - 1878*x4*x5*y3*y4*y5 - 328*x4*x5*y3*y5^2 - 154*x4*x5*y4^3 - 16175*x4*x5*y4^2*y5 - 26893*x4*x5*y4*y5^2 - 11361*x4*x5*y5^3 + 4944*x4*y3^2*y4*y5 + 2637*x4*y3^2*y5^2 + 13028*x4*y3*y4^2*y5 + 10212*x4*y3*y4*y5^2 - 3649*x4*y3*y5^3 + 6286*x4*y4^3*y5 + 19314*x4*y4^2*y5^2 + 16498*x4*y4*y5^3 + 5777*x4*y5^4 - x5^3*y3*y4 + 5*x5^3*y3*y5 + x5^3*y4^2 - 717*x5^3*y4*y5 - 34*x5^3*y5^2 + 2*x5^2*y3^3 + 441*x5^2*y3^2*y4 + 437*x5^2*y3^2*y5 - 279*x5^2*y3*y4^2 - 7679*x5^2*y3*y4*y5 - 5345*x5^2*y3*y5^2 - x5^2*y4^3 - 7649*x5^2*y4^2*y5 - 10909*x5^2*y4*y5^2 - 6252*x5^2*y5^3 + x5*y3^2*y4^2 - 54766*x5*y3^2*y4*y5 - 57074*x5*y3^2*y5^2 + x5*y3*y4^3 - 61052*x5*y3*y4^2*y5 - 47191*x5*y3*y4*y5^2 - 51297*x5*y3*y5^3 + 8085*x5*y4^3*y5 - 40905*x5*y4^2*y5^2 - 45011*x5*y4*y5^3 + 6286*x5*y5^4 - 16025*y3^2*y4^2*y5 - 195517*y3^2*y4*y5^2 - 179492*y3^2*y5^3 - 16025*y3*y4^3*y5 - 195517*y3*y4^2*y5^2 - 195517*y3*y4*y5^3 - 179492*y3*y5^4 - 16025*y4^3*y5^2 - 195517*y4^2*y5^3 - 179492*y4*y5^4) * h3 + (80*x3^3*y4*y5 + 82*x3^3*y5^2 + 146*x3^2*x4*y4*y5 - 7480*x3^2*x4*y5^2 + 40*x3^2*x5*y3*y4 + 48*x3^2*x5*y3*y5 + x3^2*x5*y4^2 - 803*x3^2*x5*y4*y5 - 8274*x3^2*x5*y5^2 - 6126*x3^2*y3*y4*y5 - 6122*x3^2*y3*y5^2 - 8004*x3^2*y4^2*y5 - 13779*x3^2*y4*y5^2 - 5697*x3^2*y5^3 - 127*x3*x4^2*y4*y5 - 8159*x3*x4^2*y5^2 + x3*x4*x5*y3*y4 + 5*x3*x4*x5*y3*y5 + 2*x3*x4*x5*y4^2 - 1551*x3*x4*x5*y4*y5 - 8236*x3*x4*x5*y5^2 - 16009*x3*x4*y3*y4*y5 - 10597*x3*x4*y3*y5^2 - 16281*x3*x4*y4^2*y5 - 13866*x3*x4*y4*y5^2 + 591*x3*x4*y5^3 - 4*x3*x5^2*y3^2 - 875*x3*x5^2*y3*y4 - 869*x3*x5^2*y3*y5 - 153*x3*x5^2*y4^2 - 1530*x3*x5^2*y4*y5 - 9308*x3*x5^2*y5^2 + 119*x3*x5*y3^2*y4 + 123*x3*x5*y3^2*y5 + 81*x3*x5*y3*y4^2 - 17752*x3*x5*y3*y4*y5 - 12184*x3*x5*y3*y5^2 + x3*x5*y4^3 - 2661*x3*x5*y4^2*y5 - 17015*x3*x5*y4*y5^2 - 12428*x3*x5*y5^3 - 2*x3*y3^2*y4*y5 - 2*x3*y3^2*y5^2 - 9884*x3*y3*y4^2*y5 - 21438*x3*y3*y4*y5^2 - 5270*x3*y3*y5^3 - 8084*x3*y4^3*y5 - 1291*x3*y4^2*y5^2 - 1291*x3*y4*y5^3 - 5777*x3*y5^4 - 195*x4^3*y4*y5 + 115*x4^2*x5*y3*y4 + 115*x4^2*x5*y3*y5 + 154*x4^2*x5*y4^2 - 47*x4^2*x5*y4*y5 - 8434*x4^2*x5*y5^2 - 8084*x4^2*y3*y4*y5 - 5582*x4^2*y3*y5^2 - 6481*x4^2*y4^2*y5 - 14370*x4^2*y4*y5^2 - 5777*x4^2*y5^3 - 2*x4*x5^2*y3^2 + 716*x4*x5^2*y3*y4 + 716*x4*x5^2*y3*y5 + 2*x4*x5^2*y4^2 - 881*x4*x5^2*y4*y5 - 8627*x4*x5^2*y5^2 + 40*x4*x5*y3^2*y4 + 40*x4*x5*y3^2*y5 + 155*x4*x5*y3*y4^2 - 1718*x4*x5*y3*y4*y5 + 1346*x4*x5*y3*y5^2 + 154*x4*x5*y4^3 - 16161*x4*x5*y4^2*y5 - 28551*x4*x5*y4*y5^2 - 11747*x4*x5*y5^3 - 4944*x4*y3^2*y4*y5 - 2637*x4*y3^2*y5^2 - 13028*x4*y3*y4^2*y5 - 10212*x4*y3*y4*y5^2 + 3649*x4*y3*y5^3 - 6286*x4*y4^3*y5 - 19314*x4*y4^2*y5^2 - 16498*x4*y4*y5^3 - 5777*x4*y5^4 - x5^3*y3*y4 + 5*x5^3*y3*y5 + x5^3*y4^2 - 717*x5^3*y4*y5 - 34*x5^3*y5^2 - 2*x5^2*y3^3 - 442*x5^2*y3^2*y4 - 438*x5^2*y3^2*y5 + 278*x5^2*y3*y4^2 - 8490*x5^2*y3*y4*y5 - 6210*x5^2*y3*y5^2 + x5^2*y4^3 - 8520*x5^2*y4^2*y5 - 13218*x5^2*y4*y5^2 - 6320*x5^2*y5^3 + 40*x5*y3^2*y4^2 - 70856*x5*y3^2*y4*y5 - 68589*x5*y3^2*y5^2 + 40*x5*y3*y4^3 - 64570*x5*y3*y4^2*y5 - 78431*x5*y3*y4*y5^2 - 74366*x5*y3*y5^3 - 8044*x5*y4^3*y5 - 84717*x5*y4^2*y5^2 - 80652*x5*y4*y5^3 - 6286*x5*y5^4 - 3604*y3^2*y4^2*y5 - 10709*y3^2*y4*y5^2 - 7105*y3^2*y5^3 - 3604*y3*y4^3*y5 - 10709*y3*y4^2*y5^2 - 10709*y3*y4*y5^3 - 7105*y3*y5^4 - 3604*y4^3*y5^2 - 10709*y4^2*y5^3 - 7105*y4*y5^4) * h4
  have e45 : 4 * (x4*y5 - x5*y4) ^ 4 = 0 := by
    linear_combination (-528*x3^2*x4*y5^2 - 2*x3^2*x5*y4^2 - 10*x3^2*x5*y4*y5 - 536*x3^2*x5*y5^2 + 96*x3^2*y4^2*y5 + 366*x3^2*y4*y5^2 + 270*x3^2*y5^3 - 14*x3*x4^2*y4*y5 - 534*x3*x4^2*y5^2 - 2*x3*x4*x5*y3*y4 - 2*x3*x4*x5*y3*y5 - 4*x3*x4*x5*y4^2 - 30*x3*x4*x5*y4*y5 - 544*x3*x4*x5*y5^2 + 192*x3*x4*y3*y4*y5 + 540*x3*x4*y3*y5^2 + 192*x3*x4*y4^2*y5 + 636*x3*x4*y4*y5^2 + 270*x3*x4*y5^3 - 10*x3*x5^2*y3*y4 - 10*x3*x5^2*y3*y5 - 10*x3*x5^2*y4^2 - 20*x3*x5^2*y4*y5 - 548*x3*x5^2*y5^2 + x3*x5*y3^2*y4 + x3*x5*y3^2*y5 + x3*x5*y3*y4^2 + 193*x3*x5*y3*y4*y5 + 541*x3*x5*y3*y5^2 + 97*x3*x5*y4^2*y5 + 463*x3*x5*y4*y5^2 + 540*x3*x5*y5^3 - 2*x3*y3*y4^2*y5 - 1064*x3*y3*y4*y5^2 - 1062*x3*y3*y5^3 + 14*x3*y4^3*y5 - 502*x3*y4^2*y5^2 - 512*x3*y4*y5^3 - 524*x3*y5^4 - 10*x4^3*y4*y5 - 4*x4^3*y5^2 + 10*x4^2*x5*y3*y4 + 10*x4^2*x5*y3*y5 + 12*x4^2*x5*y4^2 - 6*x4^2*x5*y4*y5 - 536*x4^2*x5*y5^2 + 96*x4^2*y3*y4*y5 + 270*x4^2*y3*y5^2 + 96*x4^2*y4*y5^2 + 270*x4^2*y5^3 + 8*x4*x5^2*y3*y4 + 8*x4*x5^2*y3*y5 + 4*x4*x5^2*y4^2 - 14*x4*x5^2*y4*y5 - 538*x4*x5^2*y5^2 + 96*x4*x5*y3*y4*y5 + 270*x4*x5*y3*y5^2 + 192*x4*x5*y4^2*y5 + 732*x4*x5*y4*y5^2 + 540*x4*x5*y5^3 - 4*x4*y3^2*y4*y5 - 540*x4*y3^2*y5^2 - 2*x4*y3*y4^2*y5 - 1084*x4*y3*y4*y5^2 - 538*x4*y3*y5^3 + 10*x4*y4^3*y5 + 10*x4*y4^2*y5^2 - 1064*x4*y4*y5^3 - 534*x4*y5^4 + 2*x5^3*y3*y4 + 2*x5^3*y3*y5 - 2*x5^3*y4^2 - 6*x5^3*y4*y5 + x5^2*y3^2*y4 + x5^2*y3^2*y5 + x5^2*y3*y4^2 + 97*x5^2*y3*y4*y5 + 271*x5^2*y3*y5^2 + 97*x5^2*y4^2*y5 + 271*x5^2*y4*y5^2 - 2*x5*y3^3*y4 - 2*x5*y3^3*y5 - 3*x5*y3^2*y4^2 + 11*x5*y3^2*y4*y5 - 524*x5*y3^2*y5^2 - 15*x5*y3*y4^3 - x5*y3*y4^2*y5 - 539*x5*y3*y4*y5^2 - 1060*x5*y3*y5^3 - 12*x5*y4^4 - 15*x5*y4^3*y5 - 525*x5*y4^2*y5^2 - 1052*x5*y4*y5^3 + 193*y3^2*y4^2*y5 + 182*y3^2*y4*y5^2 - 11*y3^2*y5^3 + 193*y3*y4^3*y5 + 182*y3*y4^2*y5^2 + 182*y3*y4*y5^3 - 11*y3*y5^4 + 193*y4^3*y5^2 + 182*y4^2*y5^3 - 11*y4*y5^4) * h1 + (-x3^3*x5*y4 - x3^3*x5*y5 - 10*x3^2*x5^2*y4 - 12*x3^2*x5^2*y5 + 2*x3^2*x5*y3*y4 + 2*x3^2*x5*y3*y5 - x3^2*x5*y4*y5 + x3^2*y4^2*y5 + 4*x3^2*y4*y5^2 + 3*x3^2*y5^3 - 12*x3*x4^3*y5 - x3*x4^2*x5*y3 - 2*x3*x4^2*x5*y4 - 18*x3*x4^2*x5*y5 - x3*x4*x5^2*y3 - 24*x3*x4*x5^2*y4 - 26*x3*x4*x5^2*y5 + x3*x4*x5*y3^2 - x3*x4*x5*y3*y5 - 2*x3*x4*x5*y4^2 - x3*x4*x5*y4*y5 + 16*x3*x4*y4^2*y5 + 19*x3*x4*y4*y5^2 + 7*x3*x4*y5^3 + x3*x5^3*y3 - 6*x3*x5^3*y4 - 17*x3*x5^3*y5 + x3*x5^2*y3^2 + x3*x5^2*y3*y4 + 2*x3*x5^2*y3*y5 + x3*x5^2*y4^2 - x3*x5^2*y5^2 - x3*x5*y3^2*y4 - x3*x5*y3^2*y5 + x3*x5*y3*y4^2 + 15*x3*x5*y3*y4*y5 + 13*x3*x5*y3*y5^2 + x3*x5*y4^3 + 22*x3*x5*y4^2*y5 + 24*x3*x5*y4*y5^2 + 17*x3*x5*y5^3 + 194*x3*y3*y4^2*y5 - 368*x3*y3*y4*y5^2 - 562*x3*y3*y5^3 + 97*x3*y4^3*y5 - 184*x3*y4^2*y5^2 - 184*x3*y4*y5^3 - 281*x3*y5^4 - 10*x4^4*y5 + 10*x4^3*x5*y3 + 12*x4^3*x5*y4 - 12*x4^3*x5*y5 + 25*x4^2*x5^2*y3 + 10*x4^2*x5^2*y4 - 12*x4^2*x5^2*y5 - x4^2*x5*y3*y4 - x4^2*x5*y3*y5 - x4^2*x5*y4*y5 - x4^2*x5*y5^2 + x4^2*y3*y4*y5 - 3*x4^2*y3*y5^2 + 10*x4^2*y4^2*y5 + 9*x4^2*y4*y5^2 + 3*x4^2*y5^3 + 17*x4*x5^3*y3 - 7*x4*x5^3*y5 + x4*x5^2*y3^2 + x4*x5^2*y3*y4 - 2*x4*x5^2*y4^2 - 2*x4*x5^2*y4*y5 - x4*x5^2*y5^2 - x4*x5*y3^2*y4 - x4*x5*y3^2*y5 - 12*x4*x5*y3*y4^2 - 10*x4*x5*y3*y4*y5 - 4*x4*x5*y3*y5^2 - 12*x4*x5*y4^3 - 2*x4*x5*y4^2*y5 + 15*x4*x5*y4*y5^2 + 7*x4*x5*y5^3 + 97*x4*y3^2*y4*y5 - 281*x4*y3^2*y5^2 + 194*x4*y3*y4^2*y5 - 465*x4*y3*y4*y5^2 - 281*x4*y3*y5^3 + 194*x4*y4^2*y5^2 - 465*x4*y4*y5^3 - 281*x4*y5^4 + 7*x5^4*y3 - x5^4*y4 + x5^3*y3^2 + x5^3*y3*y5 + x5^3*y4*y5 + 4*x5^2*y3^2*y4 + 4*x5^2*y3^2*y5 - x5^2*y3*y4*y5 + 4*x5^2*y3*y5^2 - 3*x5^2*y4^3 + 7*x5^2*y4^2*y5 + 12*x5^2*y4*y5^2 - x5*y3^2*y4^2 + 95*x5*y3^2*y4*y5 - 282*x5*y3^2*y5^2 - x5*y3*y4^3 + 95*x5*y3*y4^2*y5 - 89*x5*y3*y4*y5^2 - 563*x5*y3*y5^3 + 96*x5*y4^3*y5 - 89*x5*y4^2*y5^2 - 563*x5*y4*y5^3 + y3^2*y4^2*y5 + 4*y3^2*y4*y5^2 + 3*y3^2*y5^3 + y3*y4^3*y5 + 4*y3*y4^2*y5^2 + 4*y3*y4*y5^3 + 3*y3*y5^4 + y4^3*y5^2 + 4*y4^2*y5^3 + 3*y4*y5^4) * h2 + (264*x3^2*x4*y5^2 + x3^2*x5*y4^2 + 5*x3^2*x5*y4*y5 + 268*x3^2*x5*y5^2 - 48*x3^2*y4^2*y5 - 183*x3^2*y4*y5^2 - 135*x3^2*y5^3 + 7*x3*x4^2*y4*y5 + 267*x3*x4^2*y5^2 + x3*x4*x5*y3*y4 + x3*x4*x5*y3*y5 + 2*x3*x4*x5*y4^2 + 15*x3*x4*x5*y4*y5 + 272*x3*x4*x5*y5^2 - 95*x3*x4*y3*y4*y5 - 267*x3*x4*y3*y5^2 - 103*x3*x4*y4^2*y5 - 324*x3*x4*y4*y5^2 - 137*x3*x4*y5^3 + 5*x3*x5^2*y3*y4 + 5*x3*x5^2*y3*y5 + 5*x3*x5^2*y4^2 + 10*x3*x5^2*y4*y5 + 274*x3*x5^2*y5^2 - 2*x3*x5*y3*y4^2 - 105*x3*x5*y3*y4*y5 - 275*x3*x5*y3*y5^2 - x3*x5*y4^3 - 60*x3*x5*y4^2*y5 - 242*x3*x5*y4*y5^2 - 276*x3*x5*y5^3 + 96*x3*y3*y4^2*y5 + 366*x3*y3*y4*y5^2 + 270*x3*y3*y5^3 + 48*x3*y4^3*y5 + 183*x3*y4^2*y5^2 + 183*x3*y4*y5^3 + 135*x3*y5^4 + 5*x4^3*y4*y5 + 2*x4^3*y5^2 - 5*x4^2*x5*y3*y4 - 5*x4^2*x5*y3*y5 - 6*x4^2*x5*y4^2 + 3*x4^2*x5*y4*y5 + 268*x4^2*x5*y5^2 - 48*x4^2*y3*y4*y5 - 132*x4^2*y3*y5^2 - 5*x4^2*y4^2*y5 - 52*x4^2*y4*y5^2 - 135*x4^2*y5^3 - 4*x4*x5^2*y3*y4 - 4*x4*x5^2*y3*y5 - 2*x4*x5^2*y4^2 + 7*x4*x5^2*y4*y5 + 269*x4*x5^2*y5^2 + 5*x4*x5*y3*y4^2 - 44*x4*x5*y3*y4*y5 - 132*x4*x5*y3*y5^2 + 6*x4*x5*y4^3 - 95*x4*x5*y4^2*y5 - 371*x4*x5*y4*y5^2 - 271*x4*x5*y5^3 + 48*x4*y3^2*y4*y5 + 135*x4*y3^2*y5^2 + 96*x4*y3*y4^2*y5 + 318*x4*y3*y4*y5^2 + 135*x4*y3*y5^3 + 96*x4*y4^2*y5^2 + 318*x4*y4*y5^3 + 135*x4*y5^4 - x5^3*y3*y4 - x5^3*y3*y5 + x5^3*y4^2 + 3*x5^3*y4*y5 - 3*x5^2*y3^2*y4 - 3*x5^2*y3^2*y5 - x5^2*y3*y4^2 - 49*x5^2*y3*y4*y5 - 137*x5^2*y3*y5^2 + x5^2*y4^3 - 53*x5^2*y4^2*y5 - 141*x5^2*y4*y5^2 + x5*y3^2*y4^2 + 50*x5*y3^2*y4*y5 + 136*x5*y3^2*y5^2 + x5*y3*y4^3 + 50*x5*y3*y4^2*y5 + 233*x5*y3*y4*y5^2 + 271*x5*y3*y5^3 + 49*x5*y4^3*y5 + 233*x5*y4^2*y5^2 + 271*x5*y4*y5^3 - 97*y3^2*y4^2*y5 - 93*y3^2*y4*y5^2 + 4*y3^2*y5^3 - 97*y3*y4^3*y5 - 93*y3*y4^2*y5^2 - 93*y3*y4*y5^3 + 4*y3*y5^4 - 97*y4^3*y5^2 - 93*y4^2*y5^3 + 4*y4*y5^4) * h3 + (264*x3^2*x4*y5^2 + x3^2*x5*y4^2 + 5*x3^2*x5*y4*y5 + 268*x3^2*x5*y5^2 - 48*x3^2*y4^2*y5 - 183*x3^2*y4*y5^2 - 135*x3^2*y5^3 + 7*x3*x4^2*y4*y5 + 267*x3*x4^2*y5^2 + x3*x4*x5*y3*y4 + x3*x4*x5*y3*y5 + 2*x3*x4*x5*y4^2 + 15*x3*x4*x5*y4*y5 + 272*x3*x4*x5*y5^2 - 97*x3*x4*y3*y4*y5 - 273*x3*x4*y3*y5^2 - 89*x3*x4*y4^2*y5 - 312*x3*x4*y4*y5^2 - 133*x3*x4*y5^3 + 5*x3*x5^2*y3*y4 + 5*x3*x5^2*y3*y5 + 5*x3*x5^2*y4^2 + 10*x3*x5^2*y4*y5 + 274*x3*x5^2*y5^2 - x3*x5*y3^2*y4 - x3*x5*y3^2*y5 + x3*x5*y3*y4^2 - 88*x3*x5*y3*y4*y5 - 266*x3*x5*y3*y5^2 + x3*x5*y4^3 - 37*x3*x5*y4^2*y5 - 221*x3*x5*y4*y5^2 - 264*x3*x5*y5^3 - 96*x3*y3*y4^2*y5 - 366*x3*y3*y4*y5^2 - 270*x3*y3*y5^3 - 48*x3*y4^3*y5 - 183*x3*y4^2*y5^2 - 183*x3*y4*y5^3 - 135*x3*y5^4 + 5*x4^3*y4*y5 + 2*x4^3*y5^2 - 5*x4^2*x5*y3*y4 - 5*x4^2*x5*y3*y5 - 6*x4^2*x5*y4^2 + 3*x4^2*x5*y4*y5 + 268*x4^2*x5*y5^2 - 48*x4^2*y3*y4*y5 - 138*x4^2*y3*y5^2 + 5*x4^2*y4^2*y5 - 44*x4^2*y4*y5^2 - 135*x4^2*y5^3 - 4*x4*x5^2*y3*y4 - 4*x4*x5^2*y3*y5 - 2*x4*x5^2*y4^2 + 7*x4*x5^2*y4*y5 + 269*x4*x5^2*y5^2 - 5*x4*x5*y3*y4^2 - 52*x4*x5*y3*y4*y5 - 138*x4*x5*y3*y5^2 - 6*x4*x5*y4^3 - 97*x4*x5*y4^2*y5 - 361*x4*x5*y4*y5^2 - 269*x4*x5*y5^3 - 48*x4*y3^2*y4*y5 - 135*x4*y3^2*y5^2 - 96*x4*y3*y4^2*y5 - 318*x4*y3*y4*y5^2 - 135*x4*y3*y5^3 - 96*x4*y4^2*y5^2 - 318*x4*y4*y5^3 - 135*x4*y5^4 - x5^3*y3*y4 - x5^3*y3*y5 + x5^3*y4^2 + 3*x5^3*y4*y5 + 2*x5^2*y3^2*y4 + 2*x5^2*y3^2*y5 - 48*x5^2*y3*y4*y5 - 134*x5^2*y3*y5^2 - x5^2*y4^3 - 44*x5^2*y4^2*y5 - 130*x5^2*y4*y5^2 - 48*x5*y3^2*y4*y5 - 135*x5*y3^2*y5^2 - 48*x5*y3*y4^2*y5 - 231*x5*y3*y4*y5^2 - 270*x5*y3*y5^3 - 48*x5*y4^3*y5 - 231*x5*y4^2*y5^2 - 270*x5*y4*y5^3 - 96*y3^2*y4^2*y5 - 89*y3^2*y4*y5^2 + 7*y3^2*y5^3 - 96*y3*y4^3*y5 - 89*y3*y4^2*y5^2 - 89*y3*y4*y5^3 + 7*y3*y5^4 - 96*y4^3*y5^2 - 89*y4^2*y5^3 + 7*y4*y5^4) * h4
  have q : ∀ m : ℂ, 4 * m ^ 4 = 0 → m = 0 := by
    intro m hm
    have h := (mul_eq_zero.mp hm).resolve_left (by norm_num)
    exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h
  refine ⟨?_, ?_, ?_⟩
  · have := q _ e34
    linear_combination this
  · have := q _ e35
    linear_combination this
  · have := q _ e45
    linear_combination this

def coefL1 (v u : V4) : M45 →ₗ[ℂ] V4 where
  toFun Z := ![ip (col Z 2) u, ip (col Z 3) u, ip (col Z 4) u, 0]
  map_add' Z Z' := by
    funext k
    fin_cases k <;> simp [ip, col] <;> ring
  map_smul' c Z := by
    funext k
    fin_cases k <;> simp [ip, col] <;> ring

theorem coefL1_vals (v u : V4) (Z : M45) (l3 l4 b : ℂ) (h2 : col Z 2 = l3 • v) (h3 : col Z 3 = l4 • v)
    (h4 : col Z 4 = b • v) :
    coefL1 v u Z = ![l3 * ip v u, l4 * ip v u, b * ip v u, 0] := by
  have e : coefL1 v u Z = ![ip (col Z 2) u, ip (col Z 3) u, ip (col Z 4) u, 0] := rfl
  rw [e, h2, h3, h4]
  funext k
  fin_cases k <;> simp [ip] <;> ring

theorem c1_plane (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v u : V4) (hg : ip v u ≠ 0)
    (hline : ∀ Z ∈ K, rs Z = 0 → ∃ l3 l4 b : ℂ, col Z 2 = l3 • v ∧ col Z 3 = l4 • v ∧ col Z 4 = b • v) :
    ∃ Zx ∈ K, rs Zx = 0 ∧ ∃ Zy ∈ K, rs Zy = 0 ∧ ∃ x3 x4 xb y3 y4 yb : ℂ,
      col Zx 2 = x3 • v ∧ col Zx 3 = x4 • v ∧ col Zx 4 = xb • v ∧
      col Zy 2 = y3 • v ∧ col Zy 3 = y4 • v ∧ col Zy 4 = yb • v ∧
      (∀ s t : ℂ, s * x3 + t * y3 = 0 → s * x4 + t * y4 = 0 → s * xb + t * yb = 0 → s = 0 ∧ t = 0) ∧
      ∀ Z ∈ K, rs Z = 0 → ∃ s t : ℂ, col Z 2 = (s * x3 + t * y3) • v ∧ col Z 3 = (s * x4 + t * y4) • v ∧
        col Z 4 = (s * xb + t * yb) • v := by
  obtain ⟨-, -, -, z, hz0, hzK⟩ := TC5_dims K hdef hK5
  obtain ⟨hK, hq, -, -⟩ := TC5_dims K hdef hK5
  have hmemN : ∀ Z, Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) ↔ Z ∈ K ∧ rs Z = 0 := by
    intro Z
    rw [Submodule.mem_inf, LinearMap.mem_ker]
  have hzN : zE z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45) := (hmemN _).mpr ⟨hzK, rs_zE z⟩
  have hker1 : 1 ≤ Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL1 v u) : Submodule ℂ M45) := by
    have hzE : zE z ≠ 0 := by
      intro h
      apply hz0
      funext k
      have e := congrFun h (k, 0)
      rw [zE0] at e
      exact e
    have hmem : zE z ∈ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL1 v u) : Submodule ℂ M45) := by
      refine Submodule.mem_inf.mpr ⟨hzN, ?_⟩
      rw [LinearMap.mem_ker, coefL1_vals v u (zE z) 0 0 0 (by funext k; simp [col, zE2c])
        (by funext k; simp [col, zE3]) (by funext k; simp [col, zE4])]
      funext k
      fin_cases k <;> simp
    have hle : Submodule.span ℂ {zE z} ≤ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL1 v u) : Submodule ℂ M45) := by
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hmem
    have h1 : Module.finrank ℂ (Submodule.span ℂ {zE z}) = 1 := finrank_span_singleton hzE
    have h2 := Submodule.finrank_mono hle
    omega
  have hker2 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL1 v u) : Submodule ℂ M45) ≤ 1 := by
    have hW : ∀ y ∈ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL1 v u) : Submodule ℂ M45).map dYL, zE y ∈ K := by
      rintro _ ⟨Z, hZ, rfl⟩
      have h1 := Submodule.mem_inf.mp hZ
      obtain ⟨hZK, h0⟩ := (hmemN Z).mp h1.1
      obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Z hZK h0
      have hc := LinearMap.mem_ker.mp h1.2
      rw [coefL1_vals v u Z l3 l4 b e2 e3 e4] at hc
      have c0 := congrFun hc 0
      have c1 := congrFun hc 1
      have c2 := congrFun hc 2
      simp at c0 c1 c2
      have k2 : col Z 2 = 0 := by rw [e2, c0.resolve_right hg, zero_smul]
      have k3 : col Z 3 = 0 := by rw [e3, c1.resolve_right hg, zero_smul]
      have k4 : col Z 4 = 0 := by rw [e4, c2.resolve_right hg, zero_smul]
      rw [dYL_apply, ← Z_of_nbar Z k2 k3 k4 (nbar_ker Z h0 k2 k3 k4)]
      exact hZK
    have h1 := zeta_le_one K hdef hK5 _ hW
    have hkerd : (((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL1 v u)) ⊓ LinearMap.ker dYL : Submodule ℂ M45) = ⊥ := by
      rw [eq_bot_iff]
      intro Z hZ
      rw [Submodule.mem_bot]
      have hZ1 := (Submodule.mem_inf.mp hZ).1
      have hd : dY Z = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2
      have h1' := Submodule.mem_inf.mp hZ1
      obtain ⟨hZK, h0⟩ := (hmemN Z).mp h1'.1
      obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Z hZK h0
      have hc := LinearMap.mem_ker.mp h1'.2
      rw [coefL1_vals v u Z l3 l4 b e2 e3 e4] at hc
      have c0 := congrFun hc 0
      have c1 := congrFun hc 1
      have c2 := congrFun hc 2
      simp at c0 c1 c2
      have k2 : col Z 2 = 0 := by rw [e2, c0.resolve_right hg, zero_smul]
      have k3 : col Z 3 = 0 := by rw [e3, c1.resolve_right hg, zero_smul]
      have k4 : col Z 4 = 0 := by rw [e4, c2.resolve_right hg, zero_smul]
      exact uY_dY_zero Z (nbar_ker Z h0 k2 k3 k4) hd k2 k3 k4
    have r := rank_nullity ((K ⊓ LinearMap.ker rs : Submodule ℂ M45) ⊓ LinearMap.ker (coefL1 v u) : Submodule ℂ M45) dYL
    rw [hkerd, finrank_bot] at r
    omega
  have r1 := rank_nullity (K ⊓ LinearMap.ker rs : Submodule ℂ M45) (coefL1 v u)
  have r2 := rank_nullity K rs
  have hP2 : Module.finrank ℂ ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL1 v u)) = 2 := by omega
  obtain ⟨px, hpx, py, hpy, hind⟩ := two_indep ((K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL1 v u)) (by omega)
  obtain ⟨Zx, hZx, rfl⟩ := Submodule.mem_map.mp hpx
  obtain ⟨Zy, hZy, rfl⟩ := Submodule.mem_map.mp hpy
  obtain ⟨hZxK, h0x⟩ := (hmemN Zx).mp hZx
  obtain ⟨hZyK, h0y⟩ := (hmemN Zy).mp hZy
  obtain ⟨x3, x4, xb, ex2, ex3, ex4⟩ := hline Zx hZxK h0x
  obtain ⟨y3, y4, yb, ey2, ey3, ey4⟩ := hline Zy hZyK h0y
  have hvx := coefL1_vals v u Zx x3 x4 xb ex2 ex3 ex4
  have hvy := coefL1_vals v u Zy y3 y4 yb ey2 ey3 ey4
  have hspan : (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL1 v u) = Submodule.span ℂ {coefL1 v u Zx, coefL1 v u Zy} := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact hpx
      · exact hpy
    · have hne : coefL1 v u Zx ≠ 0 := by
        intro h
        have := hind 1 0 (by rw [h]; simp)
        exact one_ne_zero this.1
      have hlt : Submodule.span ℂ {coefL1 v u Zx} <
          Submodule.span ℂ {coefL1 v u Zx, coefL1 v u Zy} := by
        refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
        intro h
        have hy' : coefL1 v u Zy ∈ Submodule.span ℂ {coefL1 v u Zx} := by
          rw [h]
          exact Submodule.subset_span (by simp)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy'
        have := hind c (-1) (by rw [hc]; simp)
        exact one_ne_zero (neg_eq_zero.mp this.2)
      have h1 : Module.finrank ℂ (Submodule.span ℂ {coefL1 v u Zx}) = 1 := finrank_span_singleton hne
      have h2 := Submodule.finrank_lt_finrank_of_lt hlt
      omega
  refine ⟨Zx, hZxK, h0x, Zy, hZyK, h0y, x3, x4, xb, y3, y4, yb, ex2, ex3, ex4, ey2, ey3, ey4, ?_, ?_⟩
  · intro s t h3 h4 hb
    apply hind s t
    rw [hvx, hvy]
    funext k
    fin_cases k
    · show s * (x3 * ip v u) + t * (y3 * ip v u) = 0
      linear_combination ip v u * h3
    · show s * (x4 * ip v u) + t * (y4 * ip v u) = 0
      linear_combination ip v u * h4
    · show s * (xb * ip v u) + t * (yb * ip v u) = 0
      linear_combination ip v u * hb
    · show s * 0 + t * 0 = 0
      ring
  · intro Z hZ h0
    obtain ⟨l3, l4, b, e2, e3, e4⟩ := hline Z hZ h0
    have hmem : coefL1 v u Z ∈ (K ⊓ LinearMap.ker rs : Submodule ℂ M45).map (coefL1 v u) := Submodule.mem_map.mpr ⟨Z, (hmemN Z).mpr ⟨hZ, h0⟩, rfl⟩
    rw [hspan] at hmem
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hmem
    rw [hvx, hvy, coefL1_vals v u Z l3 l4 b e2 e3 e4] at hst
    have c0 := congrFun hst 0
    have c1 := congrFun hst 1
    have c2 := congrFun hst 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at c0 c1 c2
    refine ⟨s, t, ?_, ?_, ?_⟩
    · rw [e2]
      congr 1
      have e : (l3 - (s * x3 + t * y3)) * ip v u = 0 := by linear_combination -c0
      linear_combination (mul_eq_zero.mp e).resolve_right hg
    · rw [e3]
      congr 1
      have e : (l4 - (s * x4 + t * y4)) * ip v u = 0 := by linear_combination -c1
      linear_combination (mul_eq_zero.mp e).resolve_right hg
    · rw [e4]
      congr 1
      have e : (b - (s * xb + t * yb)) * ip v u = 0 := by linear_combination -c2
      linear_combination (mul_eq_zero.mp e).resolve_right hg

theorem c1_eqs (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv2 : ip v v = 0) (Z : M45)
    (hZ : Z ∈ K) (h0 : rs Z = 0) (a b c : ℂ) (e2 : col Z 2 = a • v) (e3 : col Z 3 = b • v)
    (e4 : col Z 4 = c • v) :
    t3 v v v * ((a + b) * (b + c) * (c + a) - a * b * c) = 0 ∧
      3 * (t4 v v v v * (a * b * c * (a + b + c))) = 0 := by
  obtain ⟨q1, q2⟩ := nbar_eqs K hdef Z hZ h0
  rw [e2, e3, e4] at q1 q2
  have hv2' := hv2
  simp only [t3, t4, ip, Pi.smul_apply, smul_eq_mul] at q1 q2 hv2' ⊢
  constructor
  · linear_combination q1
  · linear_combination q2 + (v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3) * (a * b * c * (a + b + c)) * hv2'

theorem c1_reduce (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hl : ∀ Z ∈ K, rs Z = 0 → ∃ a b c : ℂ, col Z 2 = a • v ∧ col Z 3 = b • v ∧ col Z 4 = c • v)
    (hY2 : ∃ Y ∈ K, rs Y = 0 ∧ col Y 2 ≠ 0) (hY3 : ∃ Y ∈ K, rs Y = 0 ∧ col Y 3 ≠ 0)
    (hY4 : ∃ Y ∈ K, rs Y = 0 ∧ col Y 4 ≠ 0) :
    t3 v v v = 0 ∧
      (∀ Z ∈ K, rs Z = 0 → ∃ a b : ℂ, col Z 2 = a • v ∧ col Z 3 = b • v ∧ col Z 4 = (-(a + b)) • v) ∧
      (∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧ col Z 4 = (-(a + b)) • v) := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have hu : ip v (fun i => if i = k then (1 : ℂ) else 0) = v k := by
    simp only [ip]
    fin_cases k <;> simp
  have hg : ip v (fun i => if i = k then (1 : ℂ) else 0) ≠ 0 := by rw [hu]; exact hk
  obtain ⟨Zx, hZx, h0x, Zy, hZy, h0y, x3, x4, xb, y3, y4, yb, ex2, ex3, ex4, ey2, ey3, ey4, hind,
    hrep⟩ := c1_plane K hdef hK5 v _ hg hl
  have hcomb : ∀ s t : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = (s * x3 + t * y3) • v ∧
      col Z 3 = (s * x4 + t * y4) • v ∧ col Z 4 = (s * xb + t * yb) • v := by
    intro s t
    refine ⟨s • Zx + t • Zy, K.add_mem (K.smul_mem s hZx) (K.smul_mem t hZy), ?_, ?_, ?_, ?_⟩
    · rw [map_add, map_smul, map_smul, h0x, h0y, smul_zero, smul_zero, add_zero]
    · funext m
      have g1 := congrFun ex2 m
      have g2 := congrFun ey2 m
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
      rw [g1, g2]
      ring
    · funext m
      have g1 := congrFun ex3 m
      have g2 := congrFun ey3 m
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
      rw [g1, g2]
      ring
    · funext m
      have g1 := congrFun ex4 m
      have g2 := congrFun ey4 m
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
      rw [g1, g2]
      ring
  have heq : ∀ s t : ℂ, t3 v v v * ((s * x3 + t * y3 + (s * x4 + t * y4)) *
      (s * x4 + t * y4 + (s * xb + t * yb)) * (s * xb + t * yb + (s * x3 + t * y3))
      - (s * x3 + t * y3) * (s * x4 + t * y4) * (s * xb + t * yb)) = 0 ∧
      3 * (t4 v v v v * ((s * x3 + t * y3) * (s * x4 + t * y4) * (s * xb + t * yb) *
        (s * x3 + t * y3 + (s * x4 + t * y4) + (s * xb + t * yb)))) = 0 := by
    intro s t
    obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hcomb s t
    exact c1_eqs K hdef v hv2 Z hZ h0 _ _ _ e2 e3 e4
  have act2 : x3 ≠ 0 ∨ y3 ≠ 0 := by
    obtain ⟨Y, hY, h0, hc⟩ := hY2
    obtain ⟨s, t, f2, -, -⟩ := hrep Y hY h0
    by_contra hcon
    push_neg at hcon
    apply hc
    rw [f2, hcon.1, hcon.2, mul_zero, mul_zero, add_zero, zero_smul]
  have act3 : x4 ≠ 0 ∨ y4 ≠ 0 := by
    obtain ⟨Y, hY, h0, hc⟩ := hY3
    obtain ⟨s, t, -, f3, -⟩ := hrep Y hY h0
    by_contra hcon
    push_neg at hcon
    apply hc
    rw [f3, hcon.1, hcon.2, mul_zero, mul_zero, add_zero, zero_smul]
  have act4 : xb ≠ 0 ∨ yb ≠ 0 := by
    obtain ⟨Y, hY, h0, hc⟩ := hY4
    obtain ⟨s, t, -, -, f4⟩ := hrep Y hY h0
    by_contra hcon
    push_neg at hcon
    apply hc
    rw [f4, hcon.1, hcon.2, mul_zero, mul_zero, add_zero, zero_smul]
  by_cases hT3 : t3 v v v = 0
  · have hT4 : t4 v v v v ≠ 0 := (chi_t4 v hv0 hv1 hv2 hT3).2
    have hsum : x3 + x4 + xb = 0 ∧ y3 + y4 + yb = 0 := by
      by_contra hcon
      have hs : x3 + x4 + xb ≠ 0 ∨ y3 + y4 + yb ≠ 0 := by
        by_contra h'
        push_neg at h'
        exact hcon h'
      have hgen : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
          (![x3, x4, xb, x3 + x4 + xb] : Fin 4 → ℂ) i ≠ 0 ∨ (![y3, y4, yb, y3 + y4 + yb] : Fin 4 → ℂ) i ≠ 0 := by
        intro i _
        fin_cases i
        · exact act2
        · exact act3
        · exact act4
        · exact hs
      obtain ⟨t0, ht0⟩ := generic_t (Finset.univ : Finset (Fin 4)) ![x3, x4, xb, x3 + x4 + xb] ![y3, y4, yb, y3 + y4 + yb] hgen
      have a0 : x3 + t0 * y3 ≠ 0 := ht0 0 (Finset.mem_univ _)
      have a1 : x4 + t0 * y4 ≠ 0 := ht0 1 (Finset.mem_univ _)
      have a2 : xb + t0 * yb ≠ 0 := ht0 2 (Finset.mem_univ _)
      have a3 : x3 + x4 + xb + t0 * (y3 + y4 + yb) ≠ 0 := ht0 3 (Finset.mem_univ _)
      have q := (heq 1 t0).2
      have e : 3 * (t4 v v v v * ((x3 + t0 * y3) * (x4 + t0 * y4) * (xb + t0 * yb) *
          (x3 + x4 + xb + t0 * (y3 + y4 + yb)))) = 0 := by linear_combination q
      have h3 : (3 : ℂ) ≠ 0 := by norm_num
      exact mul_ne_zero h3 (mul_ne_zero hT4 (mul_ne_zero (mul_ne_zero (mul_ne_zero a0 a1) a2) a3)) e
    have hdet : x3 * y4 - y3 * x4 ≠ 0 := by
      intro hd
      by_cases h3 : x3 = 0 ∧ y3 = 0
      · have h' := hind y4 (-x4) (by rw [h3.1, h3.2]; ring) (by ring)
          (by linear_combination y4 * hsum.1 - x4 * hsum.2 - y4 * h3.1 + x4 * h3.2)
        rcases act3 with h | h
        · exact h (by linear_combination -h'.2)
        · exact h h'.1
      · have h' := hind y3 (-x3) (by ring) (by linear_combination -hd)
          (by linear_combination y3 * hsum.1 - x3 * hsum.2 + hd)
        exact h3 ⟨by linear_combination -h'.2, h'.1⟩
    refine ⟨hT3, ?_, ?_⟩
    · intro Z hZ h0
      obtain ⟨s, t, f2, f3, f4⟩ := hrep Z hZ h0
      refine ⟨s * x3 + t * y3, s * x4 + t * y4, f2, f3, ?_⟩
      rw [f4]
      congr 1
      linear_combination s * hsum.1 + t * hsum.2
    · intro a b
      obtain ⟨F1, F2⟩ := cramer x3 y3 x4 y4 hdet a b
      obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hcomb ((a * y4 - b * y3) / (x3 * y4 - y3 * x4))
        ((x3 * b - x4 * a) / (x3 * y4 - y3 * x4))
      refine ⟨Z, hZ, h0, ?_, ?_, ?_⟩
      · rw [e2, F1]
      · rw [e3, F2]
      · rw [e4]
        congr 1
        linear_combination ((a * y4 - b * y3) / (x3 * y4 - y3 * x4)) * hsum.1
          + ((x3 * b - x4 * a) / (x3 * y4 - y3 * x4)) * hsum.2 - F1 - F2
  · exfalso
    have c10 := (mul_eq_zero.mp (heq 1 0).1).resolve_left hT3
    have c01 := (mul_eq_zero.mp (heq 0 1).1).resolve_left hT3
    have c11 := (mul_eq_zero.mp (heq 1 1).1).resolve_left hT3
    have c1m := (mul_eq_zero.mp (heq 1 (-1)).1).resolve_left hT3
    obtain ⟨m34, m35, m45⟩ := noline x3 x4 xb y3 y4 yb (by linear_combination c10)
      (by linear_combination c01) (by linear_combination c11) (by linear_combination c1m)
    by_cases h3 : x3 = 0
    · by_cases h4 : x4 = 0
      · by_cases h5 : xb = 0
        · have := hind 1 0 (by rw [h3]; ring) (by rw [h4]; ring) (by rw [h5]; ring)
          exact one_ne_zero this.1
        · have := hind yb (-xb) (by linear_combination m35) (by linear_combination m45) (by ring)
          exact h5 (by linear_combination -this.2)
      · have := hind y4 (-x4) (by linear_combination m34) (by ring) (by linear_combination -m45)
        exact h4 (by linear_combination -this.2)
    · have := hind y3 (-x3) (by ring) (by linear_combination -m34) (by linear_combination -m35)
      exact h3 (by linear_combination -this.2)

def C1chiHyp : Prop := ∀ K : Submodule ℂ M45, DefLine K mTC → 5 ≤ Module.finrank ℂ K →
  ∀ v : V4, v ≠ 0 → tau v = 0 → ip v v = 0 → t3 v v v = 0 →
  (∀ Z ∈ K, rs Z = 0 → ∃ a b : ℂ, col Z 2 = a • v ∧ col Z 3 = b • v ∧ col Z 4 = (-(a + b)) • v) →
  (∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧ col Z 4 = (-(a + b)) • v) → False

theorem C1_of_chi (H : C1chiHyp) : C1Hyp := by
  intro K hdef hK5 v hv0 hv1 hv2 hl hY2 hY3 hY4
  obtain ⟨hT3, hl', hr'⟩ := c1_reduce K hdef hK5 v hv0 hv1 hv2 hl hY2 hY3 hY4
  exact H K hdef hK5 v hv0 hv1 hv2 hT3 hl' hr'

theorem TC5_of_c1chi (H : C1chiHyp) (K : Submodule ℂ M45) (hdef : DefLine K mTC) :
    Module.finrank ℂ K ≤ 4 :=
  TC5_of_c1 (C1_of_chi H) K hdef

def C1RHyp : Prop := ∀ K : Submodule ℂ M45, DefLine K mTC → 5 ≤ Module.finrank ℂ K →
  ∀ v : V4, v ≠ 0 → tau v = 0 → ip v v = 0 → t3 v v v = 0 →
  (∀ Z ∈ K, rs Z = 0 → ∃ a b : ℂ, col Z 2 = a • v ∧ col Z 3 = b • v ∧ col Z 4 = (-(a + b)) • v) →
  (∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
    col Z 4 = (-(a + b)) • v) →
  ∀ z : V4, z ≠ 0 → zE z ∈ K → (∀ Z ∈ K, rs Z = 0 → ∃ μ : ℂ, dY Z = μ • z) → False

theorem C1chi_of_R (H : C1RHyp) : C1chiHyp := by
  intro K hdef hK5 v hv0 hv1 hv2 hv3 hl hr
  obtain ⟨-, -, -, z, hz0, hzK⟩ := TC5_dims K hdef hK5
  have hline3 : ∀ Z ∈ K, rs Z = 0 → (∃ c : ℂ, col Z 2 = c • v) ∧ (∃ c : ℂ, col Z 3 = c • v) ∧
      (∃ c : ℂ, col Z 4 = c • v) := by
    intro Z hZ h0
    obtain ⟨a, b, e2, e3, e4⟩ := hl Z hZ h0
    exact ⟨⟨a, e2⟩, ⟨b, e3⟩, ⟨-(a + b), e4⟩⟩
  obtain ⟨Y0, hY0, h0Y0, f2, -, -⟩ := hr 1 0
  have hY0v : col Y0 2 = v := by rw [f2, one_smul]
  have DN : ∀ Z ∈ K, rs Z = 0 → e2 (dY Z) = 0 ∧ ip v (Ed (dY Z)) = 0 :=
    fun Z hZ h0 => DN_line K hdef v hv1 hv2 hv3 hline3 Y0 hY0 (Or.inl hY0v) Z hZ h0
  have hk := chi_pow v hv1 hv2 hv3
  have hκ := (chi_t4 v hv0 hv1 hv2 hv3).1
  have hDz : ∀ Z ∈ K, rs Z = 0 → ∃ μ : ℂ, dY Z = μ • z :=
    fun Z hZ h0 => DN_on_z K v _ hκ hk hv1 hv2 hv3 DN z hz0 hzK Z hZ h0
  apply H K hdef hK5 v hv0 hv1 hv2 hv3 hl _ z hz0 hzK hDz
  intro a b
  obtain ⟨Z, hZ, h0, e2, e3, e4⟩ := hr a b
  obtain ⟨μ, hμ⟩ := hDz Z hZ h0
  refine ⟨Z - μ • zE z, K.sub_mem hZ (K.smul_mem μ hzK), ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_smul, h0, rs_zE, smul_zero, sub_zero]
  · have e := map_sub dYL Z (μ • zE z)
    rw [map_smul, dYL_apply, dYL_apply, dYL_apply, dY_zE, hμ, sub_self] at e
    exact e
  · funext m
    have g := congrFun e2 m
    simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE2c] at g ⊢
    rw [g]
    ring
  · funext m
    have g := congrFun e3 m
    simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE3] at g ⊢
    rw [g]
    ring
  · funext m
    have g := congrFun e4 m
    simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zE4] at g ⊢
    rw [g]
    ring

theorem TC5_of_c1R (H : C1RHyp) (K : Submodule ℂ M45) (hdef : DefLine K mTC) :
    Module.finrank ℂ K ≤ 4 :=
  TC5_of_c1chi (C1chi_of_R H) K hdef

theorem exists_iso_rs (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (hact : ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 ≠ 0) :
    ∃ Y0 ∈ K, rs Y0 ≠ 0 ∧ ip (rs Y0) (rs Y0) = 0 := by
  obtain ⟨-, hq, -, -⟩ := TC5_dims K hdef hK5
  obtain ⟨a, ha, b, hb, hind⟩ := two_indep (K.map rs) (by omega)
  obtain ⟨Y1, hY1, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨Y2, hY2, rfl⟩ := Submodule.mem_map.mp hb
  have hD0 : ip (rs Y1) (rs Y1) * ip (rs Y2) (rs Y2) - ip (rs Y1) (rs Y2) ^ 2 = 0 := by
    by_contra hD
    obtain ⟨Z, hZ, h0, hc⟩ := hact
    exact hc (NB_plane K hdef Y1 hY1 Y2 hY2 hD Z hZ h0).1
  by_cases hAB : ip (rs Y1) (rs Y1) = 0 ∧ ip (rs Y1) (rs Y2) = 0
  · refine ⟨Y1, hY1, ?_, hAB.1⟩
    intro h
    have := hind 1 0 (by rw [h]; simp)
    exact one_ne_zero this.1
  · refine ⟨ip (rs Y1) (rs Y2) • Y1 - ip (rs Y1) (rs Y1) • Y2,
      K.sub_mem (K.smul_mem _ hY1) (K.smul_mem _ hY2), ?_, ?_⟩
    · rw [map_sub, map_smul, map_smul]
      intro h
      have := hind (ip (rs Y1) (rs Y2)) (-ip (rs Y1) (rs Y1)) (by rw [neg_smul, ← sub_eq_add_neg]; exact h)
      exact hAB ⟨by linear_combination -this.2, this.1⟩
    · rw [map_sub, map_smul, map_smul]
      have hD0' := hD0
      simp only [ip, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hD0' ⊢
      linear_combination (rs Y1 0 * rs Y1 0 + rs Y1 1 * rs Y1 1 + rs Y1 2 * rs Y1 2 + rs Y1 3 * rs Y1 3) * hD0'

theorem uY_R (Z : M45) (h0 : rs Z = 0) (v : V4) (a b : ℂ) (c2 : col Z 2 = a • v) (c3 : col Z 3 = b • v)
    (c4 : col Z 4 = (-(a + b)) • v) : uY Z = 0 := by
  funext k
  have R := congrFun h0 k
  rw [rs_apply] at R
  have E2 := congrFun c2 k
  have E3 := congrFun c3 k
  have E4 := congrFun c4 k
  simp only [col, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at R E2 E3 E4
  simp only [uY, Pi.zero_apply]
  linear_combination (1 / 2 : ℂ) * R - (1 / 2 : ℂ) * (E2 + E3 + E4)

theorem c1R_ipv (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv1 : tau v = 0)
    (hv2 : ip v v = 0) (Y : M45) (hY : Y ∈ K) (Z : M45) (hZ : Z ∈ K) (hu : uY Z = 0) (a b : ℂ)
    (c2 : col Z 2 = a • v) (c3 : col Z 3 = b • v) (c4 : col Z 4 = (-(a + b)) • v) :
    2 * (a * (ip v (col Y 4) - ip v (col Y 2)) + b * (ip v (col Y 4) - ip v (col Y 3))) = 0 := by
  have e1 := (TC5_deg_i K hdef (Y + Z) (K.add_mem hY hZ)).2.1
  have e2 := (TC5_deg_i K hdef Y hY).2.1
  have hu' : uY (Y + Z) = uY Y := by
    funext k
    have g := congrFun hu k
    simp only [uY, Pi.add_apply, Pi.zero_apply] at g ⊢
    linear_combination g
  have hc : ∀ j, col (Y + Z) j = col Y j + col Z j := fun j => rfl
  rw [hu', hc, hc, hc, c2, c3, c4] at e1
  simp only [X2c, tau, ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 hv1 hv2 ⊢
  linear_combination (-2 * (a ^ 2 + a * b + b ^ 2) * (v 0 + v 1 + v 2 + v 3)
      - 2 * (a * ((col Y 2 0 + col Y 2 1 + col Y 2 2 + col Y 2 3) - (col Y 4 0 + col Y 4 1 + col Y 4 2 + col Y 4 3))
        + b * ((col Y 3 0 + col Y 3 1 + col Y 3 2 + col Y 3 3) - (col Y 4 0 + col Y 4 1 + col Y 4 2 + col Y 4 3)))) * hv1
    + 2 * (a ^ 2 + a * b + b ^ 2) * hv2 - e1 + e2

theorem c1R_cols (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv1 : tau v = 0)
    (hv2 : ip v v = 0)
    (hr : ∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
      col Z 4 = (-(a + b)) • v)
    (Y : M45) (hY : Y ∈ K) : ip v (col Y 2) = ip v (col Y 4) ∧ ip v (col Y 3) = ip v (col Y 4) := by
  obtain ⟨Z1, hZ1, h01, -, a2, a3, a4⟩ := hr 1 0
  obtain ⟨Z2, hZ2, h02, -, b2, b3, b4⟩ := hr 0 1
  have e1 := c1R_ipv K hdef v hv1 hv2 Y hY Z1 hZ1 (uY_R Z1 h01 v 1 0 a2 a3 a4) 1 0 a2 a3 a4
  have e2 := c1R_ipv K hdef v hv1 hv2 Y hY Z2 hZ2 (uY_R Z2 h02 v 0 1 b2 b3 b4) 0 1 b2 b3 b4
  exact ⟨by linear_combination (-1 / 2 : ℂ) * e1, by linear_combination (-1 / 2 : ℂ) * e2⟩

theorem c1R_half (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4)
    (hr : ∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
      col Z 4 = (-(a + b)) • v)
    (Y : M45) (hY : Y ∈ K) :
    2 * ip v (col Y 2) = ip v (rs Y) ∧ 2 * ip v (col Y 3) = ip v (rs Y) ∧
      2 * ip v (col Y 4) = ip v (rs Y) := by
  obtain ⟨Z1, hZ1, h01, -, a2, -, -⟩ := hr 1 0
  obtain ⟨Z2, hZ2, h02, -, -, b3, -⟩ := hr 0 1
  obtain ⟨Z3, hZ3, h03, -, -, -, c4⟩ := hr (-1) 0
  have e2 := neutral_pol K 2 (fun Y hY => (NB_qbar K hdef Y hY).1) Y hY Z1 hZ1
  have e3 := neutral_pol K 3 (fun Y hY => (NB_qbar K hdef Y hY).2.1) Y hY Z2 hZ2
  have e4 := neutral_pol K 4 (fun Y hY => (NB_qbar K hdef Y hY).2.2) Y hY Z3 hZ3
  rw [a2, h01] at e2
  rw [b3, h02] at e3
  rw [c4, h03] at e4
  simp only [ip, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2 e3 e4 ⊢
  exact ⟨by linear_combination e2, by linear_combination e3, by linear_combination e4⟩

set_option maxRecDepth 20000 in
theorem c1R_x3c (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv1 : tau v = 0)
    (hv2 : ip v v = 0) (Y : M45) (hY : Y ∈ K) (Z : M45) (hZ : Z ∈ K) (hu : uY Z = 0) (a b : ℂ)
    (c2 : col Z 2 = a • v) (c3 : col Z 3 = b • v) (c4 : col Z 4 = (-(a + b)) • v) :
    4 * ((a * b + a * (-(a + b)) + b * (-(a + b))) * t3 (uY Y) v v + a * b * t3 v v (col Y 4)
      + a * (-(a + b)) * t3 v v (col Y 3) + b * (-(a + b)) * t3 v v (col Y 2)) = 0 := by
  have e1 := (TC5_deg_i K hdef (Y + Z) (K.add_mem hY hZ)).2.2.1
  have em := (TC5_deg_i K hdef (Y - Z) (K.sub_mem hY hZ)).2.2.1
  have e0 := (TC5_deg_i K hdef Y hY).2.2.1
  have hup : uY (Y + Z) = uY Y := by
    funext k
    have g := congrFun hu k
    simp only [uY, Pi.add_apply, Pi.zero_apply] at g ⊢
    linear_combination g
  have hum : uY (Y - Z) = uY Y := by
    funext k
    have g := congrFun hu k
    simp only [uY, Pi.sub_apply, Pi.zero_apply] at g ⊢
    linear_combination -g
  have hcp : ∀ j, col (Y + Z) j = col Y j + col Z j := fun j => rfl
  have hcm : ∀ j, col (Y - Z) j = col Y j - col Z j := fun j => rfl
  rw [hup, hcp, hcp, hcp, c2, c3, c4] at e1
  rw [hum, hcm, hcm, hcm, c2, c3, c4] at em
  simp only [X3c, tau, ip, t3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 em e0 hv1 hv2 ⊢
  linear_combination e1 + em - 2 * e0 - (2*a^2*col Y 3 0*v 0 - 2*a^2*col Y 3 0*v 1 - 2*a^2*col Y 3 0*v 2 - 2*a^2*col Y 3 0*v 3 - 2*a^2*col Y 3 1*v 0 + 2*a^2*col Y 3 1*v 1 - 2*a^2*col Y 3 1*v 2 - 2*a^2*col Y 3 1*v 3 - 2*a^2*col Y 3 2*v 0 - 2*a^2*col Y 3 2*v 1 + 2*a^2*col Y 3 2*v 2 - 2*a^2*col Y 3 2*v 3 - 2*a^2*col Y 3 3*v 0 - 2*a^2*col Y 3 3*v 1 - 2*a^2*col Y 3 3*v 2 + 2*a^2*col Y 3 3*v 3 + 2*a^2*uY Y 0*v 0 - 2*a^2*uY Y 0*v 1 - 2*a^2*uY Y 0*v 2 - 2*a^2*uY Y 0*v 3 - 2*a^2*uY Y 1*v 0 + 2*a^2*uY Y 1*v 1 - 2*a^2*uY Y 1*v 2 - 2*a^2*uY Y 1*v 3 - 2*a^2*uY Y 2*v 0 - 2*a^2*uY Y 2*v 1 + 2*a^2*uY Y 2*v 2 - 2*a^2*uY Y 2*v 3 - 2*a^2*uY Y 3*v 0 - 2*a^2*uY Y 3*v 1 - 2*a^2*uY Y 3*v 2 + 2*a^2*uY Y 3*v 3 + 2*a*b*col Y 2 0*v 0 - 2*a*b*col Y 2 0*v 1 - 2*a*b*col Y 2 0*v 2 - 2*a*b*col Y 2 0*v 3 - 2*a*b*col Y 2 1*v 0 + 2*a*b*col Y 2 1*v 1 - 2*a*b*col Y 2 1*v 2 - 2*a*b*col Y 2 1*v 3 - 2*a*b*col Y 2 2*v 0 - 2*a*b*col Y 2 2*v 1 + 2*a*b*col Y 2 2*v 2 - 2*a*b*col Y 2 2*v 3 - 2*a*b*col Y 2 3*v 0 - 2*a*b*col Y 2 3*v 1 - 2*a*b*col Y 2 3*v 2 + 2*a*b*col Y 2 3*v 3 + 2*a*b*col Y 3 0*v 0 - 2*a*b*col Y 3 0*v 1 - 2*a*b*col Y 3 0*v 2 - 2*a*b*col Y 3 0*v 3 - 2*a*b*col Y 3 1*v 0 + 2*a*b*col Y 3 1*v 1 - 2*a*b*col Y 3 1*v 2 - 2*a*b*col Y 3 1*v 3 - 2*a*b*col Y 3 2*v 0 - 2*a*b*col Y 3 2*v 1 + 2*a*b*col Y 3 2*v 2 - 2*a*b*col Y 3 2*v 3 - 2*a*b*col Y 3 3*v 0 - 2*a*b*col Y 3 3*v 1 - 2*a*b*col Y 3 3*v 2 + 2*a*b*col Y 3 3*v 3 - 2*a*b*col Y 4 0*v 0 + 2*a*b*col Y 4 0*v 1 + 2*a*b*col Y 4 0*v 2 + 2*a*b*col Y 4 0*v 3 + 2*a*b*col Y 4 1*v 0 - 2*a*b*col Y 4 1*v 1 + 2*a*b*col Y 4 1*v 2 + 2*a*b*col Y 4 1*v 3 + 2*a*b*col Y 4 2*v 0 + 2*a*b*col Y 4 2*v 1 - 2*a*b*col Y 4 2*v 2 + 2*a*b*col Y 4 2*v 3 + 2*a*b*col Y 4 3*v 0 + 2*a*b*col Y 4 3*v 1 + 2*a*b*col Y 4 3*v 2 - 2*a*b*col Y 4 3*v 3 + 2*a*b*uY Y 0*v 0 - 2*a*b*uY Y 0*v 1 - 2*a*b*uY Y 0*v 2 - 2*a*b*uY Y 0*v 3 - 2*a*b*uY Y 1*v 0 + 2*a*b*uY Y 1*v 1 - 2*a*b*uY Y 1*v 2 - 2*a*b*uY Y 1*v 3 - 2*a*b*uY Y 2*v 0 - 2*a*b*uY Y 2*v 1 + 2*a*b*uY Y 2*v 2 - 2*a*b*uY Y 2*v 3 - 2*a*b*uY Y 3*v 0 - 2*a*b*uY Y 3*v 1 - 2*a*b*uY Y 3*v 2 + 2*a*b*uY Y 3*v 3 + 2*b^2*col Y 2 0*v 0 - 2*b^2*col Y 2 0*v 1 - 2*b^2*col Y 2 0*v 2 - 2*b^2*col Y 2 0*v 3 - 2*b^2*col Y 2 1*v 0 + 2*b^2*col Y 2 1*v 1 - 2*b^2*col Y 2 1*v 2 - 2*b^2*col Y 2 1*v 3 - 2*b^2*col Y 2 2*v 0 - 2*b^2*col Y 2 2*v 1 + 2*b^2*col Y 2 2*v 2 - 2*b^2*col Y 2 2*v 3 - 2*b^2*col Y 2 3*v 0 - 2*b^2*col Y 2 3*v 1 - 2*b^2*col Y 2 3*v 2 + 2*b^2*col Y 2 3*v 3 + 2*b^2*uY Y 0*v 0 - 2*b^2*uY Y 0*v 1 - 2*b^2*uY Y 0*v 2 - 2*b^2*uY Y 0*v 3 - 2*b^2*uY Y 1*v 0 + 2*b^2*uY Y 1*v 1 - 2*b^2*uY Y 1*v 2 - 2*b^2*uY Y 1*v 3 - 2*b^2*uY Y 2*v 0 - 2*b^2*uY Y 2*v 1 + 2*b^2*uY Y 2*v 2 - 2*b^2*uY Y 2*v 3 - 2*b^2*uY Y 3*v 0 - 2*b^2*uY Y 3*v 1 - 2*b^2*uY Y 3*v 2 + 2*b^2*uY Y 3*v 3) * hv1 - (2*a^2*col Y 3 0 + 2*a^2*col Y 3 1 + 2*a^2*col Y 3 2 + 2*a^2*col Y 3 3 + 2*a^2*uY Y 0 + 2*a^2*uY Y 1 + 2*a^2*uY Y 2 + 2*a^2*uY Y 3 + 2*a*b*col Y 2 0 + 2*a*b*col Y 2 1 + 2*a*b*col Y 2 2 + 2*a*b*col Y 2 3 + 2*a*b*col Y 3 0 + 2*a*b*col Y 3 1 + 2*a*b*col Y 3 2 + 2*a*b*col Y 3 3 - 2*a*b*col Y 4 0 - 2*a*b*col Y 4 1 - 2*a*b*col Y 4 2 - 2*a*b*col Y 4 3 + 2*a*b*uY Y 0 + 2*a*b*uY Y 1 + 2*a*b*uY Y 2 + 2*a*b*uY Y 3 + 2*b^2*col Y 2 0 + 2*b^2*col Y 2 1 + 2*b^2*col Y 2 2 + 2*b^2*col Y 2 3 + 2*b^2*uY Y 0 + 2*b^2*uY Y 1 + 2*b^2*uY Y 2 + 2*b^2*uY Y 3) * hv2

theorem c1R_b (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0)
    (hv2 : ip v v = 0) (Y0 : M45) (hY0 : Y0 ∈ K) (hiso : ip (rs Y0) (rs Y0) = 0) (j : Fin 5)
    (hq : ip (col Y0 j) (col Y0 j) = ip (rs Y0) (col Y0 j)) (ht : tau (col Y0 j) = 0)
    (hh : 2 * ip v (col Y0 j) = ip v (rs Y0)) :
    ∃ β : ℂ, ∀ k, 2 * col Y0 j k = rs Y0 k + β * v k := by
  have htn := (TC5_tau K hdef Y0 hY0).2.2.2.2
  obtain ⟨β, hβ⟩ := Q4 v ((2 : ℂ) • col Y0 j - rs Y0) hv0 hv1 hv2
    (by
      simp only [tau, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ht htn ⊢
      linear_combination 2 * ht - htn)
    (by
      simp only [ip, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hq hiso ⊢
      linear_combination 4 * hq + hiso)
    (by
      simp only [ip, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hh ⊢
      linear_combination hh)
  refine ⟨β, fun k => ?_⟩
  have g := congrFun hβ k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at g
  linear_combination g

theorem c1R_v2n (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0)
    (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (hr : ∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
      col Z 4 = (-(a + b)) • v)
    (Y0 : M45) (hY0 : Y0 ∈ K) (hiso : ip (rs Y0) (rs Y0) = 0) : t3 v v (rs Y0) = 0 := by
  obtain ⟨h2, h3, h4⟩ := c1R_half K hdef v hr Y0 hY0
  obtain ⟨q2, q3, q4⟩ := NB_qbar K hdef Y0 hY0
  obtain ⟨-, t2, t3', t4', -⟩ := TC5_tau K hdef Y0 hY0
  obtain ⟨β2, hp⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 2 q2 t2 h2
  obtain ⟨β3, hq⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 3 q3 t3' h3
  obtain ⟨β4, hs⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 4 q4 t4' h4
  have hu : ∀ k, 2 * uY Y0 k = rs Y0 k - col Y0 2 k - col Y0 3 k - col Y0 4 k := by
    intro k
    simp only [uY, col, rs_apply]
    ring
  obtain ⟨Z, hZ, h0, -, c2, c3, c4⟩ := hr 1 1
  have e := c1R_x3c K hdef v hv1 hv2 Y0 hY0 Z hZ (uY_R Z h0 v 1 1 c2 c3 c4) 1 1 c2 c3 c4
  have hv3' := hv3
  simp only [t3] at e hv3' ⊢
  have key : 3 * (v 0 * v 0 * rs Y0 0 + v 1 * v 1 * rs Y0 1 + v 2 * v 2 * rs Y0 2 + v 3 * v 3 * rs Y0 3) = 0 := by
    linear_combination -e + (-β2 - β3 + 5 * β4) * hv3'
      - (v 0 ^ 2 * (6 * hu 0 + hp 0 + hq 0 - 5 * hs 0) + v 1 ^ 2 * (6 * hu 1 + hp 1 + hq 1 - 5 * hs 1)
        + v 2 ^ 2 * (6 * hu 2 + hp 2 + hq 2 - 5 * hs 2) + v 3 ^ 2 * (6 * hu 3 + hp 3 + hq 3 - 5 * hs 3))
  have h3n : (3 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp key).resolve_left h3n

set_option maxRecDepth 20000 in
theorem pc_Qv13 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a1 a3 b1 b3 c1 c3 d1 d3 : ℂ) :
    pc (Qv v 0 a1 0 a3) (Qv v 0 b1 0 b3) (Qv v 0 c1 0 c3) (Qv v 0 d1 0 d3) = -24*a1*b1*c1*d1*kap + 8*a1*b1*c3*d3*kap^2 + 8*a1*b3*c1*d3*kap^2 + 8*a1*b3*c3*d1*kap^2 + 8*a3*b1*c1*d3*kap^2 + 8*a3*b1*c3*d1*kap^2 + 8*a3*b3*c1*d1*kap^2 - 24*a3*b3*c3*d3*kap^3 := by
  rw [pc_full, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3]
  simp only [br]
  rw [ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3,
    ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3]
  have h2' := h2
  simp only [ip] at h2'
  simp only [t4, Qv]
  linear_combination -((6*a1*b1*c1*d1 + 6*a1*b1*c1*d3*v 0^2 + 6*a1*b1*c3*d1*v 0^2 + 6*a1*b1*c3*d3*kap + 6*a1*b1*c3*d3*v 0^4 + 6*a1*b3*c1*d1*v 0^2 + 6*a1*b3*c1*d3*kap + 6*a1*b3*c1*d3*v 0^4 + 6*a1*b3*c3*d1*kap + 6*a1*b3*c3*d1*v 0^4 + 6*a1*b3*c3*d3*kap*v 0^2 + 6*a1*b3*c3*d3*v 0^6 + 6*a3*b1*c1*d1*v 0^2 + 6*a3*b1*c1*d3*kap + 6*a3*b1*c1*d3*v 0^4 + 6*a3*b1*c3*d1*kap + 6*a3*b1*c3*d1*v 0^4 + 6*a3*b1*c3*d3*kap*v 0^2 + 6*a3*b1*c3*d3*v 0^6 + 6*a3*b3*c1*d1*kap + 6*a3*b3*c1*d1*v 0^4 + 6*a3*b3*c1*d3*kap*v 0^2 + 6*a3*b3*c1*d3*v 0^6 + 6*a3*b3*c3*d1*kap*v 0^2 + 6*a3*b3*c3*d1*v 0^6 + 6*a3*b3*c3*d3*kap^2 + 6*a3*b3*c3*d3*kap*v 0^4 + 6*a3*b3*c3*d3*v 0^8) * hk 0 + (6*a1*b1*c1*d1 + 6*a1*b1*c1*d3*v 1^2 + 6*a1*b1*c3*d1*v 1^2 + 6*a1*b1*c3*d3*kap + 6*a1*b1*c3*d3*v 1^4 + 6*a1*b3*c1*d1*v 1^2 + 6*a1*b3*c1*d3*kap + 6*a1*b3*c1*d3*v 1^4 + 6*a1*b3*c3*d1*kap + 6*a1*b3*c3*d1*v 1^4 + 6*a1*b3*c3*d3*kap*v 1^2 + 6*a1*b3*c3*d3*v 1^6 + 6*a3*b1*c1*d1*v 1^2 + 6*a3*b1*c1*d3*kap + 6*a3*b1*c1*d3*v 1^4 + 6*a3*b1*c3*d1*kap + 6*a3*b1*c3*d1*v 1^4 + 6*a3*b1*c3*d3*kap*v 1^2 + 6*a3*b1*c3*d3*v 1^6 + 6*a3*b3*c1*d1*kap + 6*a3*b3*c1*d1*v 1^4 + 6*a3*b3*c1*d3*kap*v 1^2 + 6*a3*b3*c1*d3*v 1^6 + 6*a3*b3*c3*d1*kap*v 1^2 + 6*a3*b3*c3*d1*v 1^6 + 6*a3*b3*c3*d3*kap^2 + 6*a3*b3*c3*d3*kap*v 1^4 + 6*a3*b3*c3*d3*v 1^8) * hk 1 + (6*a1*b1*c1*d1 + 6*a1*b1*c1*d3*v 2^2 + 6*a1*b1*c3*d1*v 2^2 + 6*a1*b1*c3*d3*kap + 6*a1*b1*c3*d3*v 2^4 + 6*a1*b3*c1*d1*v 2^2 + 6*a1*b3*c1*d3*kap + 6*a1*b3*c1*d3*v 2^4 + 6*a1*b3*c3*d1*kap + 6*a1*b3*c3*d1*v 2^4 + 6*a1*b3*c3*d3*kap*v 2^2 + 6*a1*b3*c3*d3*v 2^6 + 6*a3*b1*c1*d1*v 2^2 + 6*a3*b1*c1*d3*kap + 6*a3*b1*c1*d3*v 2^4 + 6*a3*b1*c3*d1*kap + 6*a3*b1*c3*d1*v 2^4 + 6*a3*b1*c3*d3*kap*v 2^2 + 6*a3*b1*c3*d3*v 2^6 + 6*a3*b3*c1*d1*kap + 6*a3*b3*c1*d1*v 2^4 + 6*a3*b3*c1*d3*kap*v 2^2 + 6*a3*b3*c1*d3*v 2^6 + 6*a3*b3*c3*d1*kap*v 2^2 + 6*a3*b3*c3*d1*v 2^6 + 6*a3*b3*c3*d3*kap^2 + 6*a3*b3*c3*d3*kap*v 2^4 + 6*a3*b3*c3*d3*v 2^8) * hk 2 + (6*a1*b1*c1*d1 + 6*a1*b1*c1*d3*v 3^2 + 6*a1*b1*c3*d1*v 3^2 + 6*a1*b1*c3*d3*kap + 6*a1*b1*c3*d3*v 3^4 + 6*a1*b3*c1*d1*v 3^2 + 6*a1*b3*c1*d3*kap + 6*a1*b3*c1*d3*v 3^4 + 6*a1*b3*c3*d1*kap + 6*a1*b3*c3*d1*v 3^4 + 6*a1*b3*c3*d3*kap*v 3^2 + 6*a1*b3*c3*d3*v 3^6 + 6*a3*b1*c1*d1*v 3^2 + 6*a3*b1*c1*d3*kap + 6*a3*b1*c1*d3*v 3^4 + 6*a3*b1*c3*d1*kap + 6*a3*b1*c3*d1*v 3^4 + 6*a3*b1*c3*d3*kap*v 3^2 + 6*a3*b1*c3*d3*v 3^6 + 6*a3*b3*c1*d1*kap + 6*a3*b3*c1*d1*v 3^4 + 6*a3*b3*c1*d3*kap*v 3^2 + 6*a3*b3*c1*d3*v 3^6 + 6*a3*b3*c3*d1*kap*v 3^2 + 6*a3*b3*c3*d1*v 3^6 + 6*a3*b3*c3*d3*kap^2 + 6*a3*b3*c3*d3*kap*v 3^4 + 6*a3*b3*c3*d3*v 3^8) * hk 3) - (6*a1*b1*c1*d3*kap + 6*a1*b1*c3*d1*kap + 6*a1*b3*c1*d1*kap + 6*a1*b3*c3*d3*kap^2 + 6*a3*b1*c1*d1*kap + 6*a3*b1*c3*d3*kap^2 + 6*a3*b3*c1*d3*kap^2 + 6*a3*b3*c3*d1*kap^2) * h2'

theorem c1R_case_v3 (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv0 : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (hr : ∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
      col Z 4 = (-(a + b)) • v)
    (Y0 : M45) (hY0 : Y0 ∈ K) (hiso : ip (rs Y0) (rs Y0) = 0) (r : ℂ)
    (hn : rs Y0 = Qv v 0 0 0 r) : r = 0 := by
  have hk := chi_pow v hv1 hv2 hv3
  have hκ := (chi_t4 v hv0 hv1 hv2 hv3).1
  obtain ⟨h2, h3, h4⟩ := c1R_half K hdef v hr Y0 hY0
  obtain ⟨q2, q3, q4⟩ := NB_qbar K hdef Y0 hY0
  obtain ⟨-, t2, t3', t4', -⟩ := TC5_tau K hdef Y0 hY0
  obtain ⟨β2, hp⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 2 q2 t2 h2
  obtain ⟨β3, hq⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 3 q3 t3' h3
  obtain ⟨β4, hs⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 4 q4 t4' h4
  have hcol : ∀ (j : Fin 5) (β : ℂ), (∀ k, 2 * col Y0 j k = rs Y0 k + β * v k) →
      col Y0 j = Qv v 0 (β / 2) 0 (r / 2) := by
    intro j β h
    funext k
    have g := h k
    rw [hn] at g
    simp only [Qv] at g ⊢
    linear_combination (1 / 2 : ℂ) * g
  have c2Y := hcol 2 β2 hp
  have c3Y := hcol 3 β3 hq
  have c4Y := hcol 4 β4 hs
  have huY : uY Y0 = Qv v 0 (-(β2 + β3 + β4) / 4) 0 (-r / 4) := by
    funext k
    have g2 := congrFun c2Y k
    have g3 := congrFun c3Y k
    have g4 := congrFun c4Y k
    have hu : 2 * uY Y0 k = rs Y0 k - col Y0 2 k - col Y0 3 k - col Y0 4 k := by
      simp only [uY, col, rs_apply]
      ring
    rw [hn] at hu
    simp only [Qv] at g2 g3 g4 hu ⊢
    linear_combination (1 / 2 : ℂ) * hu - (1 / 2 : ℂ) * (g2 + g3 + g4)
  have key : ∀ s a b : ℂ, pc (Qv v 0 (-(β2 + β3 + β4) / 4) 0 (-r / 4)) (Qv v 0 (β2 / 2 + s * a) 0 (r / 2))
      (Qv v 0 (β3 / 2 + s * b) 0 (r / 2)) (Qv v 0 (β4 / 2 + s * (-(a + b))) 0 (r / 2)) = 0 := by
    intro s a b
    obtain ⟨Z, hZ, h0, -, z2, z3, z4⟩ := hr a b
    have hu0 := uY_R Z h0 v a b z2 z3 z4
    have e := (TC5_deg_i K hdef (Y0 + s • Z) (K.add_mem hY0 (K.smul_mem s hZ))).2.2.2
    have eu : uY (Y0 + s • Z) = uY Y0 := by
      funext k
      have g := congrFun hu0 k
      simp only [uY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at g ⊢
      linear_combination s * g
    have ec : ∀ (j : Fin 5) (β l : ℂ), col Y0 j = Qv v 0 (β / 2) 0 (r / 2) → col Z j = l • v →
        col (Y0 + s • Z) j = Qv v 0 (β / 2 + s * l) 0 (r / 2) := by
      intro j β l g1 g2
      funext k
      have f1 := congrFun g1 k
      have f2 := congrFun g2 k
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv] at f1 f2 ⊢
      rw [f1, f2]
      ring
    rw [eu, huY, ec 2 β2 a c2Y z2, ec 3 β3 b c3Y z3, ec 4 β4 (-(a + b)) c4Y z4] at e
    exact e
  have e20 := key 2 1 1
  have e10 := key 1 1 1
  have em0 := key (-1) 1 1
  have e00 := key 0 1 1
  have f10 := key 1 1 0
  have fm0 := key (-1) 1 0
  rw [pc_Qv13 v _ hk hv1 hv2 hv3] at e20 e10 em0 e00 f10 fm0
  have hS : 72 * (-(v 0 * v 1 * v 2 * v 3) * (β2 + β3 + β4)) = 0 := by
    linear_combination -(e20 - 3 * e10 - em0 + 3 * e00)
  have hS' : β2 + β3 + β4 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hS).resolve_left (by norm_num))).resolve_left hκ
  have hR : 2 * ((-(v 0 * v 1 * v 2 * v 3)) ^ 2 * r ^ 2) = 0 := by
    linear_combination f10 + fm0 - 2 * e00 + 6 * (-(v 0 * v 1 * v 2 * v 3)) * β3 * hS'
  have hR' := (mul_eq_zero.mp ((mul_eq_zero.mp hR).resolve_left two_ne_zero)).resolve_left
    (pow_ne_zero 2 hκ)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hR'

theorem c1R_case_v_u (K : Submodule ℂ M45) (hdef : DefLine K mTC) (v : V4) (hv0 : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (hr : ∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
      col Z 4 = (-(a + b)) • v)
    (Y0 : M45) (hY0 : Y0 ∈ K) (hiso : ip (rs Y0) (rs Y0) = 0) (p : ℂ)
    (hn : rs Y0 = Qv v 0 p 0 0) :
    uY Y0 = 0 ∧ ∃ c2 c3 c4 : ℂ, col Y0 2 = c2 • v ∧ col Y0 3 = c3 • v ∧ col Y0 4 = c4 • v ∧
      c2 + c3 + c4 = p := by
  have hk := chi_pow v hv1 hv2 hv3
  have hκ := (chi_t4 v hv0 hv1 hv2 hv3).1
  obtain ⟨h2, h3, h4⟩ := c1R_half K hdef v hr Y0 hY0
  obtain ⟨q2, q3, q4⟩ := NB_qbar K hdef Y0 hY0
  obtain ⟨-, t2, t3', t4', -⟩ := TC5_tau K hdef Y0 hY0
  obtain ⟨β2, hp⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 2 q2 t2 h2
  obtain ⟨β3, hq⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 3 q3 t3' h3
  obtain ⟨β4, hs⟩ := c1R_b K hdef v hv0 hv1 hv2 Y0 hY0 hiso 4 q4 t4' h4
  have hcol : ∀ (j : Fin 5) (β : ℂ), (∀ k, 2 * col Y0 j k = rs Y0 k + β * v k) →
      col Y0 j = Qv v 0 ((p + β) / 2) 0 0 := by
    intro j β h
    funext k
    have g := h k
    rw [hn] at g
    simp only [Qv] at g ⊢
    linear_combination (1 / 2 : ℂ) * g
  have c2Y := hcol 2 β2 hp
  have c3Y := hcol 3 β3 hq
  have c4Y := hcol 4 β4 hs
  have huY : uY Y0 = Qv v 0 (-(p + (β2 + β3 + β4)) / 4) 0 0 := by
    funext k
    have g2 := congrFun c2Y k
    have g3 := congrFun c3Y k
    have g4 := congrFun c4Y k
    have hu : 2 * uY Y0 k = rs Y0 k - col Y0 2 k - col Y0 3 k - col Y0 4 k := by
      simp only [uY, col, rs_apply]
      ring
    rw [hn] at hu
    simp only [Qv] at g2 g3 g4 hu ⊢
    linear_combination (1 / 2 : ℂ) * hu - (1 / 2 : ℂ) * (g2 + g3 + g4)
  have key : ∀ s a b : ℂ, pc (Qv v 0 (-(p + (β2 + β3 + β4)) / 4) 0 0)
      (Qv v 0 ((p + β2) / 2 + s * a) 0 0) (Qv v 0 ((p + β3) / 2 + s * b) 0 0)
      (Qv v 0 ((p + β4) / 2 + s * (-(a + b))) 0 0) = 0 := by
    intro s a b
    obtain ⟨Z, hZ, h0, -, z2, z3, z4⟩ := hr a b
    have hu0 := uY_R Z h0 v a b z2 z3 z4
    have e := (TC5_deg_i K hdef (Y0 + s • Z) (K.add_mem hY0 (K.smul_mem s hZ))).2.2.2
    have eu : uY (Y0 + s • Z) = uY Y0 := by
      funext k
      have g := congrFun hu0 k
      simp only [uY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at g ⊢
      linear_combination s * g
    have ec : ∀ (j : Fin 5) (c l : ℂ), col Y0 j = Qv v 0 c 0 0 → col Z j = l • v →
        col (Y0 + s • Z) j = Qv v 0 (c + s * l) 0 0 := by
      intro j c l g1 g2
      funext k
      have f1 := congrFun g1 k
      have f2 := congrFun g2 k
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv] at f1 f2 ⊢
      rw [f1, f2]
      ring
    rw [eu, huY, ec 2 _ a c2Y z2, ec 3 _ b c3Y z3, ec 4 _ (-(a + b)) c4Y z4] at e
    exact e
  have e20 := key 2 1 1
  have e10 := key 1 1 1
  have em0 := key (-1) 1 1
  have e00 := key 0 1 1
  rw [pc_Qv13 v _ hk hv1 hv2 hv3] at e20 e10 em0 e00
  have hS : 72 * (-(v 0 * v 1 * v 2 * v 3) * (p + (β2 + β3 + β4))) = 0 := by
    linear_combination -(e20 - 3 * e10 - em0 + 3 * e00)
  have hS' : p + (β2 + β3 + β4) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hS).resolve_left (by norm_num))).resolve_left hκ
  refine ⟨?_, (p + β2) / 2, (p + β3) / 2, (p + β4) / 2, ?_, ?_, ?_, ?_⟩
  · rw [huY]
    funext k
    simp only [Qv, Pi.zero_apply]
    rw [hS']
    ring
  · rw [c2Y]
    funext k
    simp only [Qv, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [c3Y]
    funext k
    simp only [Qv, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [c4Y]
    funext k
    simp only [Qv, Pi.smul_apply, smul_eq_mul]
    ring
  · linear_combination (1 / 2 : ℂ) * hS'

set_option maxRecDepth 20000 in
theorem pc_Qv12 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a1 a2 b1 b2 c1 c2 d1 d2 : ℂ) :
    pc (Qv v 0 a1 a2 0) (Qv v 0 b1 b2 0) (Qv v 0 c1 c2 0) (Qv v 0 d1 d2 0) = -24*a1*b1*c1*d1*kap + 24*a2*b2*c2*d2*kap^2 := by
  rw [pc_full, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3]
  simp only [br]
  rw [ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3,
    ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3]
  have h1' := h1
  have h2' := h2
  have h3' := h3
  simp only [tau, ip, t3] at h1' h2' h3'
  simp only [t4, Qv]
  linear_combination -((6*a1*b1*c1*d1 + 6*a1*b1*c1*d2*v 0 + 6*a1*b1*c2*d1*v 0 + 6*a1*b1*c2*d2*v 0^2 + 6*a1*b2*c1*d1*v 0 + 6*a1*b2*c1*d2*v 0^2 + 6*a1*b2*c2*d1*v 0^2 + 6*a1*b2*c2*d2*v 0^3 + 6*a2*b1*c1*d1*v 0 + 6*a2*b1*c1*d2*v 0^2 + 6*a2*b1*c2*d1*v 0^2 + 6*a2*b1*c2*d2*v 0^3 + 6*a2*b2*c1*d1*v 0^2 + 6*a2*b2*c1*d2*v 0^3 + 6*a2*b2*c2*d1*v 0^3 + 6*a2*b2*c2*d2*kap + 6*a2*b2*c2*d2*v 0^4) * hk 0 + (6*a1*b1*c1*d1 + 6*a1*b1*c1*d2*v 1 + 6*a1*b1*c2*d1*v 1 + 6*a1*b1*c2*d2*v 1^2 + 6*a1*b2*c1*d1*v 1 + 6*a1*b2*c1*d2*v 1^2 + 6*a1*b2*c2*d1*v 1^2 + 6*a1*b2*c2*d2*v 1^3 + 6*a2*b1*c1*d1*v 1 + 6*a2*b1*c1*d2*v 1^2 + 6*a2*b1*c2*d1*v 1^2 + 6*a2*b1*c2*d2*v 1^3 + 6*a2*b2*c1*d1*v 1^2 + 6*a2*b2*c1*d2*v 1^3 + 6*a2*b2*c2*d1*v 1^3 + 6*a2*b2*c2*d2*kap + 6*a2*b2*c2*d2*v 1^4) * hk 1 + (6*a1*b1*c1*d1 + 6*a1*b1*c1*d2*v 2 + 6*a1*b1*c2*d1*v 2 + 6*a1*b1*c2*d2*v 2^2 + 6*a1*b2*c1*d1*v 2 + 6*a1*b2*c1*d2*v 2^2 + 6*a1*b2*c2*d1*v 2^2 + 6*a1*b2*c2*d2*v 2^3 + 6*a2*b1*c1*d1*v 2 + 6*a2*b1*c1*d2*v 2^2 + 6*a2*b1*c2*d1*v 2^2 + 6*a2*b1*c2*d2*v 2^3 + 6*a2*b2*c1*d1*v 2^2 + 6*a2*b2*c1*d2*v 2^3 + 6*a2*b2*c2*d1*v 2^3 + 6*a2*b2*c2*d2*kap + 6*a2*b2*c2*d2*v 2^4) * hk 2 + (6*a1*b1*c1*d1 + 6*a1*b1*c1*d2*v 3 + 6*a1*b1*c2*d1*v 3 + 6*a1*b1*c2*d2*v 3^2 + 6*a1*b2*c1*d1*v 3 + 6*a1*b2*c1*d2*v 3^2 + 6*a1*b2*c2*d1*v 3^2 + 6*a1*b2*c2*d2*v 3^3 + 6*a2*b1*c1*d1*v 3 + 6*a2*b1*c1*d2*v 3^2 + 6*a2*b1*c2*d1*v 3^2 + 6*a2*b1*c2*d2*v 3^3 + 6*a2*b2*c1*d1*v 3^2 + 6*a2*b2*c1*d2*v 3^3 + 6*a2*b2*c2*d1*v 3^3 + 6*a2*b2*c2*d2*kap + 6*a2*b2*c2*d2*v 3^4) * hk 3) - ((6*a1*b1*c1*d2*kap + 6*a1*b1*c2*d1*kap + 6*a1*b2*c1*d1*kap + 6*a2*b1*c1*d1*kap) * h1' + (6*a1*b1*c2*d2*kap + 6*a1*b2*c1*d2*kap + 6*a1*b2*c2*d1*kap + 6*a2*b1*c1*d2*kap + 6*a2*b1*c2*d1*kap + 6*a2*b2*c1*d1*kap) * h2' + (6*a1*b2*c2*d2*kap + 6*a2*b1*c2*d2*kap + 6*a2*b2*c1*d2*kap + 6*a2*b2*c2*d1*kap) * h3')

set_option maxRecDepth 20000 in
theorem x3c_Qv12 (v : V4) (kap : ℂ) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a1 a2 b1 b2 c1 c2 d1 d2 : ℂ) :
    X3c (Qv v 0 a1 a2 0) (Qv v 0 b1 b2 0) (Qv v 0 c1 c2 0) (Qv v 0 d1 d2 0) = 8*a1*b1*c2*kap + 8*a1*b1*d2*kap + 8*a1*b2*c1*kap + 8*a1*b2*d1*kap + 8*a1*c1*d2*kap + 8*a1*c2*d1*kap + 8*a2*b1*c1*kap + 8*a2*b1*d1*kap + 8*a2*c1*d1*kap + 8*b1*c1*d2*kap + 8*b1*c2*d1*kap + 8*b2*c1*d1*kap := by
  simp only [X3c]
  rw [tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3, tau_Qv v h1 h2 h3]
  have h1' := h1
  have h2' := h2
  have h3' := h3
  simp only [tau, ip, t3] at h1' h2' h3'
  simp only [ip, t3, Qv]
  linear_combination (2*a1*b1*c2 + 2*a1*b1*d2 + 2*a1*b2*c1 + 2*a1*b2*c2*v 0 + 2*a1*b2*d1 + 2*a1*b2*d2*v 0 + 2*a1*c1*d2 + 2*a1*c2*d1 + 2*a1*c2*d2*v 0 + 2*a2*b1*c1 + 2*a2*b1*c2*v 0 + 2*a2*b1*d1 + 2*a2*b1*d2*v 0 + 2*a2*b2*c1*v 0 + 2*a2*b2*c2*v 0^2 + 2*a2*b2*d1*v 0 + 2*a2*b2*d2*v 0^2 + 2*a2*c1*d1 + 2*a2*c1*d2*v 0 + 2*a2*c2*d1*v 0 + 2*a2*c2*d2*v 0^2 + 2*b1*c1*d2 + 2*b1*c2*d1 + 2*b1*c2*d2*v 0 + 2*b2*c1*d1 + 2*b2*c1*d2*v 0 + 2*b2*c2*d1*v 0 + 2*b2*c2*d2*v 0^2) * hk 0 + (2*a1*b1*c2 + 2*a1*b1*d2 + 2*a1*b2*c1 + 2*a1*b2*c2*v 1 + 2*a1*b2*d1 + 2*a1*b2*d2*v 1 + 2*a1*c1*d2 + 2*a1*c2*d1 + 2*a1*c2*d2*v 1 + 2*a2*b1*c1 + 2*a2*b1*c2*v 1 + 2*a2*b1*d1 + 2*a2*b1*d2*v 1 + 2*a2*b2*c1*v 1 + 2*a2*b2*c2*v 1^2 + 2*a2*b2*d1*v 1 + 2*a2*b2*d2*v 1^2 + 2*a2*c1*d1 + 2*a2*c1*d2*v 1 + 2*a2*c2*d1*v 1 + 2*a2*c2*d2*v 1^2 + 2*b1*c1*d2 + 2*b1*c2*d1 + 2*b1*c2*d2*v 1 + 2*b2*c1*d1 + 2*b2*c1*d2*v 1 + 2*b2*c2*d1*v 1 + 2*b2*c2*d2*v 1^2) * hk 1 + (2*a1*b1*c2 + 2*a1*b1*d2 + 2*a1*b2*c1 + 2*a1*b2*c2*v 2 + 2*a1*b2*d1 + 2*a1*b2*d2*v 2 + 2*a1*c1*d2 + 2*a1*c2*d1 + 2*a1*c2*d2*v 2 + 2*a2*b1*c1 + 2*a2*b1*c2*v 2 + 2*a2*b1*d1 + 2*a2*b1*d2*v 2 + 2*a2*b2*c1*v 2 + 2*a2*b2*c2*v 2^2 + 2*a2*b2*d1*v 2 + 2*a2*b2*d2*v 2^2 + 2*a2*c1*d1 + 2*a2*c1*d2*v 2 + 2*a2*c2*d1*v 2 + 2*a2*c2*d2*v 2^2 + 2*b1*c1*d2 + 2*b1*c2*d1 + 2*b1*c2*d2*v 2 + 2*b2*c1*d1 + 2*b2*c1*d2*v 2 + 2*b2*c2*d1*v 2 + 2*b2*c2*d2*v 2^2) * hk 2 + (2*a1*b1*c2 + 2*a1*b1*d2 + 2*a1*b2*c1 + 2*a1*b2*c2*v 3 + 2*a1*b2*d1 + 2*a1*b2*d2*v 3 + 2*a1*c1*d2 + 2*a1*c2*d1 + 2*a1*c2*d2*v 3 + 2*a2*b1*c1 + 2*a2*b1*c2*v 3 + 2*a2*b1*d1 + 2*a2*b1*d2*v 3 + 2*a2*b2*c1*v 3 + 2*a2*b2*c2*v 3^2 + 2*a2*b2*d1*v 3 + 2*a2*b2*d2*v 3^2 + 2*a2*c1*d1 + 2*a2*c1*d2*v 3 + 2*a2*c2*d1*v 3 + 2*a2*c2*d2*v 3^2 + 2*b1*c1*d2 + 2*b1*c2*d1 + 2*b1*c2*d2*v 3 + 2*b2*c1*d1 + 2*b2*c1*d2*v 3 + 2*b2*c2*d1*v 3 + 2*b2*c2*d2*v 3^2) * hk 3 + (2*a1*b2*c2*kap + 2*a1*b2*d2*kap + 2*a1*c2*d2*kap + 2*a2*b1*c2*kap + 2*a2*b1*d2*kap + 2*a2*b2*c1*kap + 2*a2*b2*d1*kap + 2*a2*c1*d2*kap + 2*a2*c2*d1*kap + 2*b1*c2*d2*kap + 2*b2*c1*d2*kap + 2*b2*c2*d1*kap) * h1' + (2*a2*b2*c2*kap + 2*a2*b2*d2*kap + 2*a2*c2*d2*kap + 2*b2*c2*d2*kap) * h2' + (2*a1*b1*c1 + 2*a1*b1*d1 + 2*a1*c1*d1 + 2*b1*c1*d1) * h3'

theorem exists_rad_rs (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (hact : ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 ≠ 0) :
    ∃ Y0 ∈ K, rs Y0 ≠ 0 ∧ ∀ Y ∈ K, ip (rs Y0) (rs Y) = 0 := by
  obtain ⟨-, hq, -, -⟩ := TC5_dims K hdef hK5
  obtain ⟨a, ha, b, hb, hind⟩ := two_indep (K.map rs) (by omega)
  have hspan : K.map rs = Submodule.span ℂ {a, b} := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · have hne : a ≠ 0 := by
        intro h
        have := hind 1 0 (by rw [h]; simp)
        exact one_ne_zero this.1
      have hlt : Submodule.span ℂ {a} < Submodule.span ℂ {a, b} := by
        refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
        intro h
        have hy' : b ∈ Submodule.span ℂ {a} := by
          rw [h]
          exact Submodule.subset_span (by simp)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy'
        have := hind c (-1) (by rw [hc]; simp)
        exact one_ne_zero (neg_eq_zero.mp this.2)
      have h1 : Module.finrank ℂ (Submodule.span ℂ {a}) = 1 := finrank_span_singleton hne
      have h2 := Submodule.finrank_lt_finrank_of_lt hlt
      omega
  obtain ⟨Y1, hY1, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨Y2, hY2, rfl⟩ := Submodule.mem_map.mp hb
  have hrad : ∀ n0 : V4, ip n0 (rs Y1) = 0 → ip n0 (rs Y2) = 0 → ∀ Y ∈ K, ip n0 (rs Y) = 0 := by
    intro n0 h1 h2 Y hY
    have hm : rs Y ∈ K.map rs := Submodule.mem_map_of_mem hY
    rw [hspan] at hm
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hm
    rw [← hst]
    simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination s * h1 + t * h2
  have hD0 : ip (rs Y1) (rs Y1) * ip (rs Y2) (rs Y2) - ip (rs Y1) (rs Y2) ^ 2 = 0 := by
    by_contra hD
    obtain ⟨Z, hZ, h0, hc⟩ := hact
    exact hc (NB_plane K hdef Y1 hY1 Y2 hY2 hD Z hZ h0).1
  by_cases hAB : ip (rs Y1) (rs Y1) = 0 ∧ ip (rs Y1) (rs Y2) = 0
  · refine ⟨Y1, hY1, ?_, hrad _ hAB.1 hAB.2⟩
    intro h
    have := hind 1 0 (by rw [h]; simp)
    exact one_ne_zero this.1
  · refine ⟨ip (rs Y1) (rs Y2) • Y1 - ip (rs Y1) (rs Y1) • Y2,
      K.sub_mem (K.smul_mem _ hY1) (K.smul_mem _ hY2), ?_, ?_⟩
    · rw [map_sub, map_smul, map_smul]
      intro h
      have := hind (ip (rs Y1) (rs Y2)) (-ip (rs Y1) (rs Y1)) (by rw [neg_smul, ← sub_eq_add_neg]; exact h)
      exact hAB ⟨by linear_combination -this.2, this.1⟩
    · rw [map_sub, map_smul, map_smul]
      apply hrad
      · simp only [ip, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · have hD0' := hD0
        simp only [ip, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hD0' ⊢
        linear_combination -hD0'

theorem c1R_W (K : Submodule ℂ M45) (v : V4)
    (hr : ∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
      col Z 4 = (-(a + b)) • v)
    (Y0 : M45) (hY0 : Y0 ∈ K) (p : ℂ) (hp0 : p ≠ 0) (hu0 : uY Y0 = 0) (c2 c3 c4 : ℂ)
    (e2 : col Y0 2 = c2 • v) (e3 : col Y0 3 = c3 • v) (e4 : col Y0 4 = c4 • v)
    (hc : c2 + c3 + c4 = p) (x2 x3 x4 : ℂ) :
    ∃ W ∈ K, uY W = 0 ∧ col W 2 = x2 • v ∧ col W 3 = x3 • v ∧ col W 4 = x4 • v := by
  obtain ⟨Z, hZ, h0, -, z2, z3, z4⟩ := hr (x2 - (x2 + x3 + x4) / p * c2) (x3 - (x2 + x3 + x4) / p * c3)
  have hs : (x2 + x3 + x4) / p * p = x2 + x3 + x4 := div_mul_cancel₀ _ hp0
  refine ⟨((x2 + x3 + x4) / p) • Y0 + Z, K.add_mem (K.smul_mem _ hY0) hZ, ?_, ?_, ?_, ?_⟩
  · have hz := uY_R Z h0 v _ _ z2 z3 z4
    funext k
    have g1 := congrFun hu0 k
    have g2 := congrFun hz k
    simp only [uY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at g1 g2 ⊢
    linear_combination (x2 + x3 + x4) / p * g1 + g2
  · funext k
    have g1 := congrFun e2 k
    have g2 := congrFun z2 k
    simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
    rw [g1, g2]
    ring
  · funext k
    have g1 := congrFun e3 k
    have g2 := congrFun z3 k
    simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
    rw [g1, g2]
    ring
  · funext k
    have g1 := congrFun e4 k
    have g2 := congrFun z4 k
    simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at g1 g2 ⊢
    rw [g1, g2]
    linear_combination (v k) * ((x2 + x3 + x4) / p) * hc + v k * hs

theorem c1R_case_v_final (K : Submodule ℂ M45) (hdef : DefLine K mTC) (hK5 : 5 ≤ Module.finrank ℂ K)
    (v : V4) (hv0 : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (hr : ∀ a b : ℂ, ∃ Z ∈ K, rs Z = 0 ∧ dY Z = 0 ∧ col Z 2 = a • v ∧ col Z 3 = b • v ∧
      col Z 4 = (-(a + b)) • v)
    (Y0 : M45) (hY0 : Y0 ∈ K) (p : ℂ) (hp0 : p ≠ 0) (hn : rs Y0 = Qv v 0 p 0 0)
    (hrad : ∀ Y ∈ K, ip (rs Y0) (rs Y) = 0) (hu0 : uY Y0 = 0) (c2 c3 c4 : ℂ)
    (e2 : col Y0 2 = c2 • v) (e3 : col Y0 3 = c3 • v) (e4 : col Y0 4 = c4 • v)
    (hc : c2 + c3 + c4 = p) : False := by
  have hk := chi_pow v hv1 hv2 hv3
  have hκ := (chi_t4 v hv0 hv1 hv2 hv3).1
  obtain ⟨-, hq, -, -⟩ := TC5_dims K hdef hK5
  obtain ⟨Y4, hY4, hY4n⟩ : ∃ Y4 ∈ K, ∀ c : ℂ, rs Y4 ≠ c • v := by
    by_contra hcon
    push_neg at hcon
    have hle : K.map rs ≤ Submodule.span ℂ {v} := by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨c, hc'⟩ := hcon Y hY
      rw [hc']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank ℂ (Submodule.span ℂ {v}) = 1 := finrank_span_singleton hv0
    omega
  obtain ⟨tu, t2, t3', t4', tn⟩ := TC5_tau K hdef Y4 hY4
  have hvn : ip v (rs Y4) = 0 := by
    have e := hrad Y4 hY4
    rw [hn] at e
    have e' : ip (Qv v 0 p 0 0) (rs Y4) = p * ip v (rs Y4) := by
      simp only [ip, Qv]
      ring
    rw [e'] at e
    exact (mul_eq_zero.mp e).resolve_left hp0
  obtain ⟨π, q, hn4⟩ := vperp1_coords v _ hκ hk hv1 hv2 hv3 (rs Y4) tn hvn
  have hq0 : q ≠ 0 := by
    intro h
    apply hY4n π
    rw [hn4, h]
    funext k
    simp only [Qv, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨h2', h3', h4'⟩ := c1R_half K hdef v hr Y4 hY4
  rw [hvn] at h2' h3' h4'
  have hz2 : ip v (col Y4 2) = 0 := by linear_combination (1 / 2 : ℂ) * h2'
  have hz3 : ip v (col Y4 3) = 0 := by linear_combination (1 / 2 : ℂ) * h3'
  have hz4 : ip v (col Y4 4) = 0 := by linear_combination (1 / 2 : ℂ) * h4'
  have hu4 : ∀ k, 2 * uY Y4 k = rs Y4 k - col Y4 2 k - col Y4 3 k - col Y4 4 k := by
    intro k
    simp only [uY, col, rs_apply]
    ring
  have hzu : ip v (uY Y4) = 0 := by
    have hvn' := hvn
    have hz2' := hz2
    have hz3' := hz3
    have hz4' := hz4
    simp only [ip] at hvn' hz2' hz3' hz4' ⊢
    linear_combination (1 / 2 : ℂ) * (v 0 * hu4 0 + v 1 * hu4 1 + v 2 * hu4 2 + v 3 * hu4 3)
      + (1 / 2 : ℂ) * hvn' - (1 / 2 : ℂ) * (hz2' + hz3' + hz4')
  obtain ⟨π2, κ2, f2⟩ := vperp1_coords v _ hκ hk hv1 hv2 hv3 (col Y4 2) t2 hz2
  obtain ⟨π3, κ3, f3⟩ := vperp1_coords v _ hκ hk hv1 hv2 hv3 (col Y4 3) t3' hz3
  obtain ⟨π4, κ4, f4⟩ := vperp1_coords v _ hκ hk hv1 hv2 hv3 (col Y4 4) t4' hz4
  obtain ⟨πu, κu, fu⟩ := vperp1_coords v _ hκ hk hv1 hv2 hv3 (uY Y4) tu hzu
  have hsumκ : 2 * κu + κ2 + κ3 + κ4 = q := by
    have hv2q : ip (Qv v 0 0 1 0) (Qv v 0 (2 * πu) (2 * κu) 0) =
        ip (Qv v 0 0 1 0) (Qv v 0 (π - π2 - π3 - π4) (q - κ2 - κ3 - κ4) 0) := by
      congr 1
      funext k
      have g := hu4 k
      rw [fu, hn4, f2, f3, f4] at g
      simp only [Qv] at g ⊢
      linear_combination g
    rw [ip_Qv v _ hk hv1 hv2 hv3, ip_Qv v _ hk hv1 hv2 hv3] at hv2q
    have e : -(v 0 * v 1 * v 2 * v 3) * (2 * κu + κ2 + κ3 + κ4 - q) = 0 := by
      linear_combination (1 / 4 : ℂ) * hv2q
    have e' := (mul_eq_zero.mp e).resolve_left hκ
    linear_combination e'
  have hX : ∀ x2 x3 x4 : ℂ, X3c (Qv v 0 πu κu 0) (Qv v 0 (π2 + x2) κ2 0) (Qv v 0 (π3 + x3) κ3 0)
      (Qv v 0 (π4 + x4) κ4 0) = 0 ∧ pc (Qv v 0 πu κu 0) (Qv v 0 (π2 + x2) κ2 0) (Qv v 0 (π3 + x3) κ3 0)
      (Qv v 0 (π4 + x4) κ4 0) = 0 := by
    intro x2 x3 x4
    obtain ⟨W, hW, huW, w2, w3, w4⟩ := c1R_W K v hr Y0 hY0 p hp0 hu0 c2 c3 c4 e2 e3 e4 hc x2 x3 x4
    obtain ⟨-, -, eX, eP⟩ := TC5_deg_i K hdef (Y4 + W) (K.add_mem hY4 hW)
    have eu : uY (Y4 + W) = Qv v 0 πu κu 0 := by
      rw [← fu]
      funext k
      have g := congrFun huW k
      simp only [uY, Pi.add_apply, Pi.zero_apply] at g ⊢
      linear_combination g
    have ec : ∀ (j : Fin 5) (πj κj xj : ℂ), col Y4 j = Qv v 0 πj κj 0 → col W j = xj • v →
        col (Y4 + W) j = Qv v 0 (πj + xj) κj 0 := by
      intro j πj κj xj g1 g2
      funext k
      have h1 := congrFun g1 k
      have h2 := congrFun g2 k
      simp only [col, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv] at h1 h2 ⊢
      rw [h1, h2]
      ring
    rw [eu, ec 2 π2 κ2 x2 f2 w2, ec 3 π3 κ3 x3 f3 w3, ec 4 π4 κ4 x4 f4 w4] at eX eP
    exact ⟨eX, eP⟩
  have X0 := (hX 0 0 0).1
  have X2 := (hX 1 0 0).1
  have X3 := (hX 0 1 0).1
  have X4 := (hX 0 0 1).1
  have X23 := (hX 1 1 0).1
  have X24 := (hX 1 0 1).1
  have X34 := (hX 0 1 1).1
  rw [x3c_Qv12 v _ hk hv1 hv2 hv3] at X0 X2 X3 X4 X23 X24 X34
  have a4 : κu + κ4 = 0 := by
    have e : 8 * (-(v 0 * v 1 * v 2 * v 3)) * (κu + κ4) = 0 := by linear_combination X23 - X2 - X3 + X0
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by norm_num) hκ)
  have a3 : κu + κ3 = 0 := by
    have e : 8 * (-(v 0 * v 1 * v 2 * v 3)) * (κu + κ3) = 0 := by linear_combination X24 - X2 - X4 + X0
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by norm_num) hκ)
  have a2 : κu + κ2 = 0 := by
    have e : 8 * (-(v 0 * v 1 * v 2 * v 3)) * (κu + κ2) = 0 := by linear_combination X34 - X3 - X4 + X0
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (by norm_num) hκ)
  have hκu : κu = -q := by linear_combination -hsumκ + a2 + a3 + a4
  have P := (hX (-π2) (-π3) (-π4)).2
  rw [pc_Qv12 v _ hk hv1 hv2 hv3] at P
  have hfin : 24 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * q ^ 4 = 0 := by
    linear_combination -P + (24 * κ3 * κ4 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * κu) * a2 + (-24 * κ4 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * κu ^ 2) * a3
      + (24 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * κu ^ 3) * a4
      + (-24 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * κu ^ 3 + 24 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * κu ^ 2 * q - 24 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * κu * q ^ 2
        + 24 * (-(v 0 * v 1 * v 2 * v 3)) ^ 2 * q ^ 3) * hκu
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hκ)) (pow_ne_zero 4 hq0) hfin

theorem C1R_proof : C1RHyp := by
  intro K hdef hK5 v hv0 hv1 hv2 hv3 hl hr z hz0 hzK hDz
  have hk := chi_pow v hv1 hv2 hv3
  have hκ := (chi_t4 v hv0 hv1 hv2 hv3).1
  have hact : ∃ Z ∈ K, rs Z = 0 ∧ col Z 2 ≠ 0 := by
    obtain ⟨Z, hZ, h0, -, c2, -, -⟩ := hr 1 0
    refine ⟨Z, hZ, h0, ?_⟩
    rw [c2, one_smul]
    exact hv0
  obtain ⟨Y0, hY0, hn0, hrad⟩ := exists_rad_rs K hdef hK5 hact
  have hiso : ip (rs Y0) (rs Y0) = 0 := hrad Y0 hY0
  have hτ := (TC5_tau K hdef Y0 hY0).2.2.2.2
  have h3n := c1R_v2n K hdef v hv0 hv1 hv2 hv3 hr Y0 hY0 hiso
  obtain ⟨p, r, hpr, hpr0⟩ := vperp_coords v _ hκ hk hv1 hv2 hv3 (rs Y0) hτ hiso h3n
  rcases mul_eq_zero.mp hpr0 with hp | hr0
  · have hn : rs Y0 = Qv v 0 0 0 r := by rw [hpr, hp]
    have hrz := c1R_case_v3 K hdef v hv0 hv1 hv2 hv3 hr Y0 hY0 hiso r hn
    apply hn0
    rw [hn, hrz]
    funext k
    simp only [Qv, Pi.zero_apply]
    ring
  · have hn : rs Y0 = Qv v 0 p 0 0 := by rw [hpr, hr0]
    have hp0 : p ≠ 0 := by
      intro h
      apply hn0
      rw [hn, h]
      funext k
      simp only [Qv, Pi.zero_apply]
      ring
    obtain ⟨hu0, c2, c3, c4, e2, e3, e4, hc⟩ :=
      c1R_case_v_u K hdef v hv0 hv1 hv2 hv3 hr Y0 hY0 hiso p hn
    exact c1R_case_v_final K hdef hK5 v hv0 hv1 hv2 hv3 hr Y0 hY0 p hp0 hn hrad hu0 c2 c3 c4 e2 e3 e4 hc

theorem TC5_final (K : Submodule ℂ M45) (hdef : DefLine K mTC) : Module.finrank ℂ K ≤ 4 :=
  TC5_of_c1R C1R_proof K hdef

end

end PEqualNP.Outside.L_gct_210_aux.FL

theorem PEqualNP.Outside.L_gct_210 :
    (∀ K : Submodule ℂ (Fin 4 × Fin 5 → ℂ), PEqualNP.Outside.L_gct_210_aux.FL.SLev K →
      Module.finrank ℂ K ≤ 3) ∧
    (∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      ∀ r : Fin 5,
      (∀ w : Fin 5 → ℂ, ∑ j, w j = 0 →
        (fun p : Fin 5 × Fin 5 => if p.1 = r then w p.2 else 0) ∈ L) →
      Module.finrank ℂ L ≤ 7) ∧
    (∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      ∀ c : Fin 5,
      (∀ w : Fin 5 → ℂ, ∑ j, w j = 0 →
        (fun p : Fin 5 × Fin 5 => if p.2 = c then w p.1 else 0) ∈ L) →
      Module.finrank ℂ L ≤ 7) :=
  ⟨PEqualNP.Outside.L_gct_210_aux.FL.LemmaSL,
    fun L hL r hF => PEqualNP.Outside.L_gct_210_aux.FL.FL_of (PEqualNP.Outside.L_gct_210_aux.FL.LemmaSL) L hL r hF,
    fun L hL c hF => PEqualNP.Outside.L_gct_210_aux.FL.FL_col_of (PEqualNP.Outside.L_gct_210_aux.FL.LemmaSL) L hL c hF⟩
