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


def DefLine (K : Submodule ℂ M45) (m : Fin 5 → ℂ) : Prop :=
  ∀ Y ∈ K, ∃ θ : ℂ, ∀ a, P4 a (fun p => 1 + Y p) = 24 + θ * m a



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

def zE (z : V4) : M45 := fun p => if p.2 = 0 then z p.1 else if p.2 = 1 then -z p.1 else 0

theorem zE0 (z : V4) (k : Fin 4) : zE z (k, 0) = z k := by simp [zE]

theorem zE1 (z : V4) (k : Fin 4) : zE z (k, 1) = -z k := by simp [zE]

theorem zE3 (z : V4) (k : Fin 4) : zE z (k, 3) = 0 := by simp [zE]

theorem zE4 (z : V4) (k : Fin 4) : zE z (k, 4) = 0 := by simp [zE]

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

end

end PEqualNP.Outside.L_gct_210_aux.FL
