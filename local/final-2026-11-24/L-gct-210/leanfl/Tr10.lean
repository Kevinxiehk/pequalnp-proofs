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

def colL (m : Fin 5) : M45 →ₗ[ℂ] V4 := LinearMap.funLeft ℂ ℂ (fun i : Fin 4 => (i, m))

theorem colL_apply (m : Fin 5) (Y : M45) : colL m Y = col Y m := rfl

def phi (m : Fin 5) : M45 →ₗ[ℂ] V4 := (2 : ℂ) • colL m - rs

theorem phi_apply (m : Fin 5) (Y : M45) (i : Fin 4) : phi m Y i = 2 * Y (i, m) - rs Y i := rfl

theorem mem_Vs (v : V4) : v ∈ sumZero 4 ↔ tau v = 0 := by
  rw [mem_sumZero, tau, Fin.sum_univ_four]

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


def r3 : Fin 3 → ℂ := ![Complex.I, -1, -Complex.I]

theorem t3_smul3 (a b c : ℂ) (x y z : V4) : t3 (a • x) (b • y) (c • z) = a * b * c * t3 x y z := by
  simp only [t3, Pi.smul_apply, smul_eq_mul]
  ring

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

def DefLine (K : Submodule ℂ M45) (m : Fin 5 → ℂ) : Prop :=
  ∀ Y ∈ K, ∃ θ : ℂ, ∀ a, P4 a (fun p => 1 + Y p) = 24 + θ * m a

theorem inj_succ5 : Function.Injective (fun k : Fin 5 => ((k : ℕ) : ℂ) + 1) := by
  intro i j h
  have h' : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := add_right_cancel h
  exact Fin.ext (Nat.cast_injective h')


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

def zE (z : V4) : M45 := fun p => if p.2 = 0 then z p.1 else if p.2 = 1 then -z p.1 else 0

theorem zE0 (z : V4) (k : Fin 4) : zE z (k, 0) = z k := by simp [zE]

theorem zE1 (z : V4) (k : Fin 4) : zE z (k, 1) = -z k := by simp [zE]

theorem zE3 (z : V4) (k : Fin 4) : zE z (k, 3) = 0 := by simp [zE]


def QBc (K : Submodule ℂ M45) (m : Fin 5 → ℂ) : Prop :=
  ∀ Y ∈ K, ∃ κ θ2 : ℂ, (∀ j, tau (col Y j) = κ * m j) ∧
    (∀ j, ip (col Y j) (col Y j) - ip (rs Y) (col Y j) - κ ^ 2 * m j ^ 2 = -(θ2 / 2) * m j)


theorem QBc_of (K : Submodule ℂ M45) (m : Fin 5 → ℂ) (hdef : DefLine K m)
    (hm : ∑ a, m a = 0) (hm0 : m ≠ 0) : QBc K m := by
  intro Y hY
  obtain ⟨κ, θ2, h1, -, h3⟩ := LemmaQB K m hdef hm hm0 Y hY
  exact ⟨κ, θ2, h1, h3⟩


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

end

end PEqualNP.Outside.L_gct_210_aux.FL
