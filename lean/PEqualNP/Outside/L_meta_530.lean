import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_530_aux

open PEqualNP.MetaComplexity

abbrev Good {n : ℕ} (X Y : Finset (Fin n → Bool)) (k : ℕ) (A B : Fin k → Finset (Fin n → Bool))
    (t : Fin k → Fin n) : Prop :=
  (∀ i, A i ⊆ X ∧ B i ⊆ Y) ∧ (∀ i, ∀ x ∈ A i, x (t i) = true) ∧
    (∀ i, ∀ y ∈ B i, y (t i) = false) ∧ ∀ x ∈ X, ∀ y ∈ Y, ∃! i, x ∈ A i ∧ y ∈ B i

lemma glue {n k1 k2 : ℕ} {X Y X1 Y1 X2 Y2 : Finset (Fin n → Bool)}
    {A1 B1 : Fin k1 → Finset (Fin n → Bool)} {t1 : Fin k1 → Fin n}
    {A2 B2 : Fin k2 → Finset (Fin n → Bool)} {t2 : Fin k2 → Fin n}
    (g1 : Good X1 Y1 k1 A1 B1 t1) (g2 : Good X2 Y2 k2 A2 B2 t2)
    (hX1 : X1 ⊆ X) (hX2 : X2 ⊆ X) (hY1 : Y1 ⊆ Y) (hY2 : Y2 ⊆ Y)
    (hcov : ∀ x ∈ X, ∀ y ∈ Y, (x ∈ X1 ∧ y ∈ Y1) ∨ (x ∈ X2 ∧ y ∈ Y2))
    (hdisj : ∀ x ∈ X, ∀ y ∈ Y, ¬ ((x ∈ X1 ∧ y ∈ Y1) ∧ (x ∈ X2 ∧ y ∈ Y2))) :
    Good X Y (k1 + k2) (Fin.append A1 A2) (Fin.append B1 B2) (Fin.append t1 t2) := by
  obtain ⟨s1, la1, lb1, u1⟩ := g1
  obtain ⟨s2, la2, lb2, u2⟩ := g2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j =>
      simp only [Fin.append_left]
      exact ⟨(s1 j).1.trans hX1, (s1 j).2.trans hY1⟩
    | right j =>
      simp only [Fin.append_right]
      exact ⟨(s2 j).1.trans hX2, (s2 j).2.trans hY2⟩
  · intro i
    induction i using Fin.addCases with
    | left j =>
      simp only [Fin.append_left]
      exact la1 j
    | right j =>
      simp only [Fin.append_right]
      exact la2 j
  · intro i
    induction i using Fin.addCases with
    | left j =>
      simp only [Fin.append_left]
      exact lb1 j
    | right j =>
      simp only [Fin.append_right]
      exact lb2 j
  · intro x hx y hy
    rcases hcov x hx y hy with ⟨hx1, hy1⟩ | ⟨hx2, hy2⟩
    · obtain ⟨j, hj, hju⟩ := u1 x hx1 y hy1
      refine ⟨Fin.castAdd k2 j, ?_, ?_⟩
      · simp only [Fin.append_left]
        exact hj
      · intro i hi
        revert hi
        induction i using Fin.addCases with
        | left j' =>
          intro hi
          simp only [Fin.append_left] at hi
          rw [hju j' hi]
        | right j' =>
          intro hi
          simp only [Fin.append_right] at hi
          exact absurd ⟨⟨hx1, hy1⟩, ⟨(s2 j').1 hi.1, (s2 j').2 hi.2⟩⟩ (hdisj x hx y hy)
    · obtain ⟨j, hj, hju⟩ := u2 x hx2 y hy2
      refine ⟨Fin.natAdd k1 j, ?_, ?_⟩
      · simp only [Fin.append_right]
        exact hj
      · intro i hi
        revert hi
        induction i using Fin.addCases with
        | left j' =>
          intro hi
          simp only [Fin.append_left] at hi
          exact absurd ⟨⟨(s1 j').1 hi.1, (s1 j').2 hi.2⟩, ⟨hx2, hy2⟩⟩ (hdisj x hx y hy)
        | right j' =>
          intro hi
          simp only [Fin.append_right] at hi
          rw [hju j' hi]

lemma main {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n) :
    PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ →
    ∀ X Y : Finset (Fin n → Bool), (∀ x ∈ X, φ.eval x = true) → (∀ y ∈ Y, φ.eval y = false) →
      ∃ (k : ℕ) (A B : Fin k → Finset (Fin n → Bool)) (t : Fin k → Fin n),
        k ≤ φ.leaves ∧ Good X Y k A B t := by
  induction φ with
  | lit i c =>
    intro hpos X Y hX hY
    have hc : c = true := hpos
    subst hc
    refine ⟨1, fun _ => X, fun _ => Y, fun _ => i, le_refl _, ?_, ?_, ?_, ?_⟩
    · intro _
      exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
    · intro _ x hx
      have := hX x hx
      simpa [DMFormula.eval] using this
    · intro _ y hy
      have := hY y hy
      simpa [DMFormula.eval] using this
    · intro x hx y hy
      exact ⟨0, ⟨hx, hy⟩, fun j _ => Subsingleton.elim j 0⟩
  | and φ ψ ihφ ihψ =>
    intro hpos X Y hX hY
    obtain ⟨hp1, hp2⟩ := hpos
    have hXφ : ∀ x ∈ X, φ.eval x = true := by
      intro x hx
      have := hX x hx
      simp only [DMFormula.eval, Bool.and_eq_true] at this
      exact this.1
    have hXψ : ∀ x ∈ X, ψ.eval x = true := by
      intro x hx
      have := hX x hx
      simp only [DMFormula.eval, Bool.and_eq_true] at this
      exact this.2
    obtain ⟨k1, A1, B1, t1, hk1, g1⟩ :=
      ihφ hp1 X (Y.filter (fun y => φ.eval y = false)) hXφ
        (fun y hy => (Finset.mem_filter.1 hy).2)
    obtain ⟨k2, A2, B2, t2, hk2, g2⟩ :=
      ihψ hp2 X (Y.filter (fun y => φ.eval y = true)) hXψ (by
        intro y hy
        obtain ⟨hy, h1⟩ := Finset.mem_filter.1 hy
        have := hY y hy
        simp only [DMFormula.eval, h1, Bool.true_and] at this
        exact this)
    refine ⟨k1 + k2, _, _, _, ?_, glue g1 g2 (Finset.Subset.refl _) (Finset.Subset.refl _)
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) ?_ ?_⟩
    · simp only [DMFormula.leaves]
      omega
    · intro x hx y hy
      cases h : φ.eval y
      · exact Or.inl ⟨hx, Finset.mem_filter.2 ⟨hy, h⟩⟩
      · exact Or.inr ⟨hx, Finset.mem_filter.2 ⟨hy, h⟩⟩
    · rintro x - y - ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
      rw [Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact Bool.false_ne_true h2.2
  | or φ ψ ihφ ihψ =>
    intro hpos X Y hX hY
    obtain ⟨hp1, hp2⟩ := hpos
    have hYφ : ∀ y ∈ Y, φ.eval y = false := by
      intro y hy
      have := hY y hy
      simp only [DMFormula.eval, Bool.or_eq_false_iff] at this
      exact this.1
    have hYψ : ∀ y ∈ Y, ψ.eval y = false := by
      intro y hy
      have := hY y hy
      simp only [DMFormula.eval, Bool.or_eq_false_iff] at this
      exact this.2
    obtain ⟨k1, A1, B1, t1, hk1, g1⟩ :=
      ihφ hp1 (X.filter (fun x => φ.eval x = true)) Y
        (fun x hx => (Finset.mem_filter.1 hx).2) hYφ
    obtain ⟨k2, A2, B2, t2, hk2, g2⟩ :=
      ihψ hp2 (X.filter (fun x => φ.eval x = false)) Y (by
        intro x hx
        obtain ⟨hx, h1⟩ := Finset.mem_filter.1 hx
        have := hX x hx
        simp only [DMFormula.eval, h1, Bool.false_or] at this
        exact this) hYψ
    refine ⟨k1 + k2, _, _, _, ?_, glue g1 g2 (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (Finset.Subset.refl _) (Finset.Subset.refl _) ?_ ?_⟩
    · simp only [DMFormula.leaves]
      omega
    · intro x hx y hy
      cases h : φ.eval x
      · exact Or.inr ⟨Finset.mem_filter.2 ⟨hx, h⟩, hy⟩
      · exact Or.inl ⟨Finset.mem_filter.2 ⟨hx, h⟩, hy⟩
    · rintro x - y - ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
      rw [Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact Bool.false_ne_true h2.2.symm

end PEqualNP.Outside.L_meta_530_aux

theorem PEqualNP.Outside.L_meta_530 : ∀ (n : ℕ) (φ : PEqualNP.MetaComplexity.DMFormula n), PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ → ∀ (X Y : Finset (Fin n → Bool)), (∀ x ∈ X, φ.eval x = true) → (∀ y ∈ Y, φ.eval y = false) → ∃ (k : ℕ) (A B : Fin k → Finset (Fin n → Bool)) (t : Fin k → Fin n), k ≤ φ.leaves ∧ (∀ i : Fin k, ∀ x ∈ A i, x (t i) = true) ∧ (∀ i : Fin k, ∀ y ∈ B i, y (t i) = false) ∧ ∀ x ∈ X, ∀ y ∈ Y, ∃! i : Fin k, x ∈ A i ∧ y ∈ B i := by
  intro n φ hpos X Y hX hY
  obtain ⟨k, A, B, t, hk, -, ha, hb, hu⟩ :=
    PEqualNP.Outside.L_meta_530_aux.main φ hpos X Y hX hY
  exact ⟨k, A, B, t, hk, ha, hb, hu⟩
