import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_366_aux

lemma card_bound (s : Set (Fin 5 × Fin 5 → ZMod 2)) (p : Fin 5 → Fin 5 × Fin 5 → ZMod 2)
    (hp : ∀ i, p i ∈ s) (hinj : Function.Injective p) :
    3 ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) s) := by
  let f : Fin 5 → vectorSpan (ZMod 2) s := fun i =>
    ⟨p i -ᵥ p 0, vsub_mem_vectorSpan (ZMod 2) (hp i) (hp 0)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg Subtype.val hij
    simp only [f, vsub_eq_sub, sub_left_inj] at h
    exact hinj h
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (vectorSpan (ZMod 2) s) =
      2 ^ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) s) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := vectorSpan (ZMod 2) s), Nat.card_zmod]
  have h3 : Nat.card (Fin 5) = 5 := by simp
  rw [h2, h3] at h1
  generalize Module.finrank (ZMod 2) (vectorSpan (ZMod 2) s) = r at h1 ⊢
  by_contra hr
  have hr2 : r ≤ 2 := by omega
  interval_cases r <;> norm_num at h1

lemma key {E : List (Fin 5 × Fin 5)} {O : Finset (Fin 5) → Finset (Fin 5 × Fin 5)}
    {A B : Finset (Fin 5)}
    (hA : (∀ d ∈ O A, d ∈ E ∨ (d.2, d.1) ∈ E) ∧
      (∀ e ∈ E, (e ∈ O A ∨ (e.2, e.1) ∈ O A) ∧ ¬ (e ∈ O A ∧ (e.2, e.1) ∈ O A)) ∧
      (∀ d ∈ O A, d.2 ∉ A))
    (hB : (∀ d ∈ O B, d ∈ E ∨ (d.2, d.1) ∈ E) ∧
      (∀ e ∈ E, (e ∈ O B ∨ (e.2, e.1) ∈ O B) ∧ ¬ (e ∈ O B ∧ (e.2, e.1) ∈ O B)) ∧
      (∀ d ∈ O B, d.2 ∉ B))
    {a b : Fin 5} (ha : a ∈ A) (hb : b ∈ B) (hab : (a, b) ∈ E ∨ (b, a) ∈ E) :
    (fun d : Fin 5 × Fin 5 => if d ∈ O A then (1 : ZMod 2) else 0) ≠
      (fun d : Fin 5 × Fin 5 => if d ∈ O B then (1 : ZMod 2) else 0) := by
  intro h
  have h1 : (a, b) ∉ O B := fun hm => hB.2.2 _ hm hb
  have h2 : (b, a) ∉ O A := fun hm => hA.2.2 _ hm ha
  have h3 : (a, b) ∈ O A := by
    rcases hab with he | he
    · rcases (hA.2.1 _ he).1 with h | h
      · exact h
      · exact absurd h h2
    · rcases (hA.2.1 _ he).1 with h | h
      · exact absurd h h2
      · exact h
  have h4 := congrFun h (a, b)
  simp only [h1, h3, ite_true, ite_false] at h4
  exact one_ne_zero h4

end PEqualNP.Outside.L_meta_366_aux

theorem PEqualNP.Outside.L_meta_366 : ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] → ∀ O : Finset (Fin 5) → Finset (Fin 5 × Fin 5), (∀ J : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 5 × Fin 5 → ZMod 2 | ∃ J : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro E hE O hO
  have hvc : PEqualNP.MetaComplexity.SingleLevel.vc E ≤ 3 := by
    subst hE
    apply Nat.sInf_le
    exact ⟨{0, 2, 4}, by decide, rfl⟩
  refine le_trans hvc ?_
  let J : Fin 5 → Finset (Fin 5) := ![{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}]
  have hind : ∀ i, ∀ f ∈ E, ¬ (f.1 ∈ J i ∧ f.2 ∈ J i) := by
    subst hE
    decide
  let W : Fin 5 → Fin 5 → Fin 5 × Fin 5 :=
    ![![(0, 0), (2, 3), (0, 1), (0, 1), (0, 4)],
      ![(3, 2), (0, 0), (0, 1), (0, 1), (0, 4)],
      ![(1, 0), (1, 0), (0, 0), (3, 4), (1, 2)],
      ![(1, 0), (1, 0), (4, 3), (0, 0), (1, 2)],
      ![(4, 0), (2, 3), (2, 1), (2, 1), (0, 0)]]
  have sep : ∀ i j : Fin 5, i ≠ j →
      (W i j).1 ∈ J i ∧ (W i j).2 ∈ J j ∧
        (((W i j).1, (W i j).2) ∈ E ∨ ((W i j).2, (W i j).1) ∈ E) := by
    subst hE
    decide
  refine PEqualNP.Outside.L_meta_366_aux.card_bound _
    (fun i d => if d ∈ O (J i) then (1 : ZMod 2) else 0) (fun i => ⟨J i, hind i, rfl⟩) ?_
  intro i j hij
  by_contra hne
  obtain ⟨ha, hb, hab⟩ := sep i j hne
  exact PEqualNP.Outside.L_meta_366_aux.key (hO _ (hind i)) (hO _ (hind j)) ha hb hab hij
