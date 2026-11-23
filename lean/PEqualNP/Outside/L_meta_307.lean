import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_307 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ c : ℕ, (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔ (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  intro V G0 N num G' h1 h2 h3 c
  classical
  have hW : {u : V | ∃ v, G0.Adj u v}.Finite := by
    apply Set.Finite.of_finite_image (f := num)
    · apply (Set.finite_Iio N).subset
      rintro _ ⟨u, ⟨v, huv⟩, rfl⟩
      exact h1 u v huv
    · rintro u ⟨v, huv⟩ w ⟨z, hwz⟩ e
      exact h2 u v w z huv hwz e
  constructor
  · intro H S' hS'
    let S : Finset V := hW.toFinset.filter (fun u => ∃ a ∈ S', a.val = num u)
    have hcov : ∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S := by
      intro u v huv
      have hadj : G'.Adj ⟨num u, h1 u v huv⟩ ⟨num v, h1 v u huv.symm⟩ :=
        (h3 _ _).2 ⟨u, v, huv, rfl, rfl⟩
      rcases hS' _ _ hadj with ha | hb
      · left
        simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact ⟨⟨v, huv⟩, _, ha, rfl⟩
      · right
        simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact ⟨⟨u, huv.symm⟩, _, hb, rfl⟩
    have hle : S.card ≤ S'.card := by
      have hinj : Set.InjOn num (S : Set V) := by
        intro u hu w hw e
        simp only [Finset.mem_coe, S, Finset.mem_filter, Set.Finite.mem_toFinset,
          Set.mem_ofPred_eq] at hu hw
        obtain ⟨⟨v, huv⟩, _⟩ := hu
        obtain ⟨⟨z, hwz⟩, _⟩ := hw
        exact h2 u v w z huv hwz e
      rw [← Finset.card_image_of_injOn hinj]
      calc (S.image num).card ≤ (S'.image Fin.val).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_image] at hx ⊢
            obtain ⟨u, hu, rfl⟩ := hx
            simp only [S, Finset.mem_filter] at hu
            obtain ⟨_, a, ha, e⟩ := hu
            exact ⟨a, ha, e⟩
        _ ≤ S'.card := Finset.card_image_le
    exact le_trans (H S hcov) hle
  · intro H S hS
    let S' : Finset (Fin N) :=
      Finset.univ.filter (fun a => ∃ u ∈ S, (∃ v, G0.Adj u v) ∧ num u = a.val)
    have hcov : ∀ a b, G'.Adj a b → a ∈ S' ∨ b ∈ S' := by
      intro a b hab
      obtain ⟨u, v, huv, ha, hb⟩ := (h3 a b).1 hab
      rcases hS u v huv with hu | hv
      · left
        simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, hu, ⟨v, huv⟩, ha⟩
      · right
        simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨v, hv, ⟨u, huv.symm⟩, hb⟩
    have hle : S'.card ≤ S.card := by
      rw [← Finset.card_image_of_injective S' Fin.val_injective]
      calc (S'.image Fin.val).card ≤ (S.image num).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_image] at hx ⊢
            obtain ⟨a, ha, rfl⟩ := hx
            simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at ha
            obtain ⟨u, hu, _, e⟩ := ha
            exact ⟨u, hu, e⟩
        _ ≤ S.card := Finset.card_image_le
    exact le_trans (H S' hcov) hle
