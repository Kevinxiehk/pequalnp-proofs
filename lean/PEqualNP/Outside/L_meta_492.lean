import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_492_aux

lemma decode (m K u v p z : ℕ) (hK : 0 < K) (hv : v < m) (hp1 : 1 ≤ p) (hp2 : p ≤ K)
    (hz : z + 1 = m + K * (u * m + v) + p) :
    m ≤ z ∧ (z - m) / K = u * m + v ∧ (z - m) % K = p - 1 ∧
      (u * m + v) / m = u ∧ (u * m + v) % m = v := by
  have hm : 0 < m := by omega
  have hmz : m ≤ z := by
    generalize K * (u * m + v) = T at hz
    omega
  have h1 : (z - m) / K = u * m + v ∧ (z - m) % K = p - 1 := by
    rw [Nat.div_mod_unique hK]
    constructor
    · generalize K * (u * m + v) = T at hz ⊢
      omega
    · omega
  have h2 : (u * m + v) / m = u ∧ (u * m + v) % m = v := by
    rw [Nat.div_mod_unique hm]
    exact ⟨by ring, hv⟩
  exact ⟨hmz, h1.1, h1.2, h2.1, h2.2⟩

abbrev Pos (m k u v p z : ℕ) : Prop :=
  (p = 0 ∧ z = u) ∨ (p = 2 * k + 1 ∧ z = v) ∨
    (1 ≤ p ∧ p ≤ 2 * k ∧ z + 1 = m + 2 * k * (u * m + v) + p)

def gpot (m k xv z : ℕ) : ℕ :=
  if z = xv then 0
  else if z < m then 2 * k + 1
  else if (z - m) / (2 * k) / m = xv then (z - m) % (2 * k) + 1
  else if (z - m) / (2 * k) % m = xv then 2 * k + 1 - ((z - m) % (2 * k) + 1)
  else 2 * k + 1

lemma g_path {m k xv u v p z : ℕ} (hk : 1 ≤ k) (hxv : xv < m) (hu : u < m) (hv : v < m)
    (huv : u < v)
    (hQ : (p = 0 ∧ z = u) ∨ (p = 2 * k + 1 ∧ z = v) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ z + 1 = m + 2 * k * (u * m + v) + p)) :
    gpot m k xv z = if u = xv then p else if v = xv then 2 * k + 1 - p else 2 * k + 1 := by
  rcases hQ with ⟨hp, hz⟩ | ⟨hp, hz⟩ | ⟨hp1, hp2, hz⟩
  · subst hp hz
    unfold gpot
    split_ifs <;> omega
  · subst hp hz
    unfold gpot
    split_ifs <;> omega
  · obtain ⟨hmz, hb, hr, hbu, hbv⟩ := decode m (2 * k) u v p z (by omega) hv hp1 hp2 hz
    unfold gpot
    rw [hb, hr, hbu, hbv]
    split_ifs <;> omega

end PEqualNP.Outside.L_meta_492_aux

open PEqualNP.Outside.L_meta_492_aux in
theorem PEqualNP.Outside.L_meta_492 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ u v : Fin (m + 2 * k * m * m), u ≠ v → 3 ≤ (S.neighborSet u).ncard → 3 ≤ (S.neighborSet v).ncard → ∀ p : S.Walk u v, 2 * k + 1 ≤ p.length := by
  intro k m H hk S hS x y hxy hx3 hy3 w
  have adj_pos : ∀ a b : Fin (m + 2 * k * m * m), S.Adj a b → ∃ u v : Fin m, u < v ∧
      ∃ p : ℕ, p ≤ 2 * k ∧
        ((Pos m k u.val v.val p a.val ∧ Pos m k u.val v.val (p + 1) b.val) ∨
          (Pos m k u.val v.val p b.val ∧ Pos m k u.val v.val (p + 1) a.val)) := by
    have key : ∀ a b : Fin (m + 2 * k * m * m), (∃ u v : Fin m, u < v ∧ H.Adj u v ∧
        ∃ i : Fin (2 * k), a.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
          ((i.val = 0 ∧ b.val = u.val) ∨
            (i.val + 1 < 2 * k ∧ b.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
            (i.val + 1 = 2 * k ∧ b.val = v.val))) →
        ∃ u v : Fin m, u < v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
          ((Pos m k u.val v.val p a.val ∧ Pos m k u.val v.val (p + 1) b.val) ∨
            (Pos m k u.val v.val p b.val ∧ Pos m k u.val v.val (p + 1) a.val)) := by
      rintro a b ⟨u, v, huv, -, i, ha, hb⟩
      have hi := i.isLt
      refine ⟨u, v, huv, ?_⟩
      unfold Pos
      generalize 2 * k * (u.val * m + v.val) = T at ha hb ⊢
      rcases hb with ⟨h0, hb⟩ | ⟨h1, hb⟩ | ⟨h2, hb⟩
      · exact ⟨0, by omega, Or.inr ⟨Or.inl ⟨rfl, hb⟩,
          Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)⟩⟩
      · exact ⟨i.val + 1, by omega, Or.inl ⟨Or.inr (Or.inr ⟨by omega, by omega, by omega⟩),
          Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)⟩⟩
      · exact ⟨i.val + 1, by omega, Or.inl ⟨Or.inr (Or.inr ⟨by omega, by omega, by omega⟩),
          Or.inr (Or.inl ⟨by omega, hb⟩)⟩⟩
    intro a b hab
    rw [hS, SimpleGraph.fromRel_adj] at hab
    rcases hab with ⟨-, hR | hR⟩
    · exact key a b hR
    · obtain ⟨u, v, huv, p, hp, h⟩ := key b a hR
      exact ⟨u, v, huv, p, hp, h.symm⟩
  have deg : ∀ z : Fin (m + 2 * k * m * m), m ≤ z.val → (S.neighborSet z).ncard ≤ 2 := by
    intro z hmz
    have hsub : S.neighborSet z ⊆
        {w | w.val = if (z.val - m) % (2 * k) = 0 then (z.val - m) / (2 * k) / m
          else z.val - 1} ∪
        {w | w.val = if (z.val - m) % (2 * k) + 1 = 2 * k then (z.val - m) / (2 * k) % m
          else z.val + 1} := by
      intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      obtain ⟨u, v, huv, p, hp, h⟩ := adj_pos z w hw
      have hu := u.isLt
      have hv := v.isLt
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      rcases h with ⟨hz, hw'⟩ | ⟨hw', hz⟩
      · unfold Pos at hz hw'
        rcases hz with ⟨-, hz⟩ | ⟨hp', -⟩ | ⟨hp1, hp2, hz⟩
        · omega
        · omega
        · obtain ⟨-, hb, hr, -, hbv⟩ :=
            decode m (2 * k) u.val v.val p z.val (by omega) hv hp1 hp2 hz
          right
          rw [hr, hb, hbv]
          rcases hw' with ⟨h0, -⟩ | ⟨h1, hw'⟩ | ⟨-, h2, hw'⟩
          · omega
          · rw [if_pos (by omega)]
            exact hw'
          · rw [if_neg (by omega)]
            generalize 2 * k * (u.val * m + v.val) = T at hz hw'
            omega
      · unfold Pos at hz hw'
        rcases hz with ⟨h0, -⟩ | ⟨hp', hz⟩ | ⟨hp1, hp2, hz⟩
        · omega
        · omega
        · obtain ⟨-, hb, hr, hbu, -⟩ :=
            decode m (2 * k) u.val v.val (p + 1) z.val (by omega) hv hp1 hp2 hz
          left
          rw [hr, hb, hbu]
          rcases hw' with ⟨h0, hw'⟩ | ⟨h1, -⟩ | ⟨h1, -, hw'⟩
          · rw [if_pos (by omega)]
            exact hw'
          · omega
          · rw [if_neg (by omega)]
            generalize 2 * k * (u.val * m + v.val) = T at hz hw'
            omega
    have hone : ∀ c : ℕ, ({w | w.val = c} : Set (Fin (m + 2 * k * m * m))).ncard ≤ 1 := by
      intro c
      rw [Set.ncard_le_one]
      intro a ha b hb
      simp only [Set.mem_ofPred_eq] at ha hb
      exact Fin.ext (ha.trans hb.symm)
    calc (S.neighborSet z).ncard ≤ _ := Set.ncard_le_ncard hsub
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add (hone _) (hone _)
  have orig : ∀ z : Fin (m + 2 * k * m * m), 3 ≤ (S.neighborSet z).ncard → z.val < m := by
    intro z hz
    by_contra hzm
    have := deg z (by omega)
    omega
  have hxm := orig x hx3
  have hym := orig y hy3
  have lip : ∀ a b : Fin (m + 2 * k * m * m), S.Adj a b →
      gpot m k x.val b.val ≤ gpot m k x.val a.val + 1 := by
    intro a b hab
    obtain ⟨u, v, huv, p, hp, h⟩ := adj_pos a b hab
    have huv' : u.val < v.val := huv
    rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · unfold Pos at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
    · unfold Pos at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
  have hwalk : ∀ (a b : Fin (m + 2 * k * m * m)) (q : S.Walk a b),
      gpot m k x.val b.val ≤ gpot m k x.val a.val + q.length := by
    intro a b q
    induction q with
    | nil => simp
    | cons hadj q ih =>
      rw [SimpleGraph.Walk.length_cons]
      have := lip _ _ hadj
      omega
  have hgx : gpot m k x.val x.val = 0 := by
    unfold gpot
    simp
  have hgy : gpot m k x.val y.val = 2 * k + 1 := by
    have hne : y.val ≠ x.val := fun h => hxy (Fin.ext h).symm
    unfold gpot
    rw [if_neg hne, if_pos hym]
  have := hwalk x y w
  omega
