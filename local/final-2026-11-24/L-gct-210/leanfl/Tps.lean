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
    rw [phi_apply]
    rfl
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
      · simp
      · simp
      · simp
      · simp
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

end

end PEqualNP.Outside.L_gct_210_aux.FL
