import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3533

/-- A straight-line program over the base list `B`: every entry is the bitwise AND or OR of two
values taken from `B` or from earlier entries. -/
def Valid (B p : List ℕ) : Prop :=
  ∀ i : Fin p.length, ∃ a ∈ B ++ List.take (↑i) p, ∃ b ∈ B ++ List.take (↑i) p,
    p.get i = a &&& b ∨ p.get i = a ||| b

theorem valid_prefix (B y : List ℕ) (a : ℕ) (h : Valid B (y ++ [a])) : Valid B y := by
  intro i
  have hi : (i : ℕ) < (y ++ [a]).length := by simp only [List.length_append, List.length_singleton]; omega
  obtain ⟨c, hc, d, hd, hcd⟩ := h ⟨i, hi⟩
  have ht : List.take (i : ℕ) (y ++ [a]) = List.take i y :=
    List.take_append_of_le_length (le_of_lt i.isLt)
  have hg : (y ++ [a]).get ⟨i, hi⟩ = y.get i := by
    simp only [List.get_eq_getElem]
    exact List.getElem_append_left i.isLt
  rw [ht] at hc hd
  rw [hg] at hcd
  exact ⟨c, hc, d, hd, hcd⟩

theorem valid_last (B y : List ℕ) (a : ℕ) (h : Valid B (y ++ [a])) :
    ∃ c ∈ B ++ y, ∃ d ∈ B ++ y, a = c &&& d ∨ a = c ||| d := by
  have hi : y.length < (y ++ [a]).length := by simp
  obtain ⟨c, hc, d, hd, hcd⟩ := h ⟨y.length, hi⟩
  have ht : List.take y.length (y ++ [a]) = y := by simp
  have hg : (y ++ [a]).get ⟨y.length, hi⟩ = a := by simp
  rw [ht] at hc hd
  rw [hg] at hcd
  exact ⟨c, hc, d, hd, hcd⟩

theorem valid_snoc (B x : List ℕ) (a : ℕ) (h : Valid B x)
    (ha : ∃ c ∈ B ++ x, ∃ d ∈ B ++ x, a = c &&& d ∨ a = c ||| d) : Valid B (x ++ [a]) := by
  intro i
  obtain ⟨iv, hiv⟩ := i
  by_cases hi : iv < x.length
  · obtain ⟨c, hc, d, hd, hcd⟩ := h ⟨iv, hi⟩
    have ht : List.take iv (x ++ [a]) = List.take iv x := List.take_append_of_le_length (le_of_lt hi)
    have hg : (x ++ [a]).get ⟨iv, hiv⟩ = x.get ⟨iv, hi⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_append_left hi
    simp only [Fin.val_mk]
    rw [ht, hg]
    exact ⟨c, hc, d, hd, hcd⟩
  · have hi' : iv = x.length := by simp at hiv; omega
    subst hi'
    have ht : List.take x.length (x ++ [a]) = x := by simp
    have hg : (x ++ [a]).get ⟨x.length, hiv⟩ = a := by simp
    simp only [Fin.val_mk]
    rw [ht, hg]
    exact ha

/-- Keep the first occurrence of each new value: the result is a program with no repeats and no
base values that still produces every value of the original. -/
theorem key (B : List ℕ) : ∀ p : List ℕ, Valid B p → ∃ q : List ℕ, Valid B q ∧ q.Nodup ∧
    (∀ v ∈ q, v ∉ B) ∧ q.length ≤ p.length ∧ ∀ v ∈ p, v ∈ B ∨ v ∈ q := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], fun i => i.elim0, List.nodup_nil, by simp, by simp, by simp⟩
  | append_singleton y a ih =>
    intro hv
    obtain ⟨q, hq, hqn, hqB, hql, hcov⟩ := ih (valid_prefix B y a hv)
    obtain ⟨c, hc, d, hd, hcd⟩ := valid_last B y a hv
    have lift : ∀ w ∈ B ++ y, w ∈ B ++ q := by
      intro w hw
      rcases List.mem_append.1 hw with h | h
      · exact List.mem_append_left _ h
      · rcases hcov w h with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ h'
    by_cases ha : a ∈ B ∨ a ∈ q
    · refine ⟨q, hq, hqn, hqB, by simp; omega, ?_⟩
      intro v hv'
      rcases List.mem_append.1 hv' with h | h
      · exact hcov v h
      · simp at h; subst h; exact ha
    · push_neg at ha
      refine ⟨q ++ [a], valid_snoc B q a hq ⟨c, lift c hc, d, lift d hd, hcd⟩, ?_, ?_, by simp; omega, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hqn, List.nodup_singleton a, ?_⟩
        intro u hu w hw
        simp at hw
        subst hw
        intro e
        exact ha.2 (e ▸ hu)
      · intro v hv'
        rcases List.mem_append.1 hv' with h | h
        · exact hqB v h
        · simp at h; subst h; exact ha.1
      · intro v hv'
        rcases List.mem_append.1 hv' with h | h
        · rcases hcov v h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_append_left _ h')
        · simp at h; subst h; exact Or.inr (by simp)

end PEqualNP.Outside.L_meta_3533

open PEqualNP.Outside.L_meta_3533 in
theorem PEqualNP.Outside.L_meta_3533 : ∀ (x1 x2 : List ℕ), ∀ x3 ∉ x1, x3 ∈ x2 → (∀ (x6 : Fin x2.length), ∃ x7 ∈ x1 ++ List.take (↑x6) x2, ∃ x8 ∈ x1 ++ List.take (↑x6) x2, x2.get x6 = x7 &&& x8 ∨ x2.get x6 = x7 ||| x8) → ∃ (x7 : List ℕ), x7.length ≤ x2.length ∧ x7.Nodup ∧ (∀ x8 ∈ x7, x8 ∉ x1) ∧ x3 ∈ x7 ∧ ∀ (x8 : Fin x7.length), ∃ x9 ∈ x1 ++ List.take (↑x8) x7, ∃ x10 ∈ x1 ++ List.take (↑x8) x7, x7.get x8 = x9 &&& x10 ∨ x7.get x8 = x9 ||| x10 := by
  intro x1 x2 x3 hx3 hx3' hv
  obtain ⟨q, hq, hqn, hqB, hql, hcov⟩ := key x1 x2 hv
  refine ⟨q, hql, hqn, hqB, ?_, hq⟩
  rcases hcov x3 hx3' with h | h
  · exact absurd h hx3
  · exact h
