import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Gct.FL210

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

def defW (K : Submodule ℂ M45) : Submodule ℂ (Fin 5 → ℂ) where
  carrier := {w | ∀ Y ∈ K, ∑ a, w a * P4 a (fun p => 1 + Y p) = 0}
  add_mem' := by
    intro w w' hw hw' Y hY
    have h1 := hw Y hY
    have h2 := hw' Y hY
    rw [Fin.sum_univ_five] at h1 h2 ⊢
    simp only [Pi.add_apply]
    linear_combination h1 + h2
  zero_mem' := by
    intro Y hY
    simp
  smul_mem' := by
    intro c w hw Y hY
    have h1 := hw Y hY
    rw [Fin.sum_univ_five] at h1 ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * h1

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

end

end PEqualNP.Gct.FL210

theorem PEqualNP.Outside.L_gct_210_fl :
    (∀ K : Submodule ℂ (Fin 4 × Fin 5 → ℂ), PEqualNP.Gct.FL210.SLev K →
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
  ⟨PEqualNP.Gct.FL210.LemmaSL,
    fun L hL r hF => PEqualNP.Gct.FL210.FL_of (PEqualNP.Gct.FL210.LemmaSL) L hL r hF,
    fun L hL c hF => PEqualNP.Gct.FL210.FL_col_of (PEqualNP.Gct.FL210.LemmaSL) L hL c hF⟩
