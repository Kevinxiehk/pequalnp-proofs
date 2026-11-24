import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3795

open PEqualNP.CircuitLowerBounds

/-- One step of the line-degree fold. -/
def stp (d : List ℕ) (g : Gate) : List ℕ := d ++ [g.lineDegree d]

theorem foldl_ext (gs : List Gate) (d : List ℕ) : ∃ e, gs.foldl stp d = d ++ e := by
  induction gs generalizing d with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨e, he⟩ := ih (stp d g)
    refine ⟨[g.lineDegree d] ++ e, ?_⟩
    rw [List.foldl_cons, he, stp, List.append_assoc]

theorem foldl_len (gs : List Gate) (d : List ℕ) :
    (gs.foldl stp d).length = d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stp]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_app_lt (l l' : List ℕ) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem main (C : Circuit) (x2 : ℕ) (hx2 : x2 < 14)
    (hg : ∀ (x4 : ℕ) (x5 : Gate), C.gates[x4]? = some x5 →
      (x5.op = GateOp.and ∨ x5.op = GateOp.or) ∧
      ∃ (x7 x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 ≠ x8 ∧ x7 < 14 + x4 ∧ x8 < 14 + x4)
    (hnd : (List.filter (fun (x5 : ℕ) => decide (14 ≤ x5))
      (C.output :: List.flatMap Gate.inputs C.gates)).Nodup)
    (hc : List.count x2 (List.flatMap Gate.inputs C.gates) ≤ 1) :
    HasLineDegree 14 {x2} C 1 := by
  set gs := C.gates with hgs
  set init : List ℕ := (List.range 14).map fun i => if i ∈ ({x2} : Finset ℕ) then 1 else 0
    with hinit
  have hD : C.lineDegrees 14 {x2} = gs.foldl stp init := rfl
  set D := gs.foldl stp init with hDdef
  set F : ℕ → List ℕ := fun k => (gs.take k).foldl stp init with hF
  set R : ℕ → List ℕ := fun k => (gs.take k).flatMap Gate.inputs with hR
  have hinitlen : init.length = 14 := by simp [hinit]
  have hFlen : ∀ k, k ≤ gs.length → (F k).length = 14 + k := by
    intro k hk
    simp only [hF, foldl_len, hinitlen, List.length_take]
    omega
  have hDF : ∀ k, ∃ e, D = F k ++ e := by
    intro k
    obtain ⟨e, he⟩ := foldl_ext (gs.drop k) (F k)
    refine ⟨e, ?_⟩
    rw [← he, hF, hDdef]
    simp only
    rw [← List.foldl_append, List.take_append_drop]
  have hDget : ∀ k w, k ≤ gs.length → w < 14 + k → D.getD w 0 = (F k).getD w 0 := by
    intro k w hk hw
    obtain ⟨e, he⟩ := hDF k
    rw [he, getD_app_lt _ _ _ (by rw [hFlen k hk]; exact hw)]
  have hFsucc : ∀ k (hk : k < gs.length), F (k+1) = F k ++ [gs[k].lineDegree (F k)] := by
    intro k hk
    simp only [hF]
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
    rfl
  have hRsucc : ∀ k (hk : k < gs.length), R (k+1) = R k ++ gs[k].inputs := by
    intro k hk
    simp only [hR]
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
    simp
  have hD0 : ∀ w, w < 14 → D.getD w 0 = if w = x2 then 1 else 0 := by
    intro w hw
    rw [hDget 0 w (Nat.zero_le _) (by omega)]
    simp [hF, hinit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
  have hsplit : ∀ k (hk : k < gs.length), gs.flatMap Gate.inputs =
      R k ++ gs[k].inputs ++ (gs.drop (k+1)).flatMap Gate.inputs := by
    intro k hk
    have e1 : gs = gs.take k ++ gs[k] :: gs.drop (k+1) := by
      rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have e2 := congrArg (List.flatMap Gate.inputs) e1
    rw [List.flatMap_append, List.flatMap_cons] at e2
    simp only [hR]
    rw [List.append_assoc]
    exact e2
  have hRR : ∀ k (hk : k < gs.length) w, w ∈ gs[k].inputs → w ∈ R k → D.getD w 0 = 0 := by
    intro k hk w hw1 hw2
    have hcnt : 2 ≤ List.count w (gs.flatMap Gate.inputs) := by
      rw [hsplit k hk, List.count_append, List.count_append]
      have h1 := List.count_pos_iff.mpr hw2
      have h2 := List.count_pos_iff.mpr hw1
      omega
    by_cases hw14 : 14 ≤ w
    · exfalso
      have h1 := List.nodup_iff_count_le_one.mp hnd w
      have hsub : List.Sublist ((gs.flatMap Gate.inputs).filter (fun (x5 : ℕ) => decide (14 ≤ x5)))
          ((C.output :: gs.flatMap Gate.inputs).filter (fun (x5 : ℕ) => decide (14 ≤ x5))) :=
        (List.sublist_cons_self _ _).filter _
      have h2 := hsub.count_le w
      rw [List.count_filter (by simpa using hw14)] at h2
      omega
    · push_neg at hw14
      rw [hD0 w hw14]
      by_cases hwx : w = x2
      · subst hwx; omega
      · simp [hwx]
  have hQ : ∀ k, k ≤ gs.length →
      (∀ w, w < 14 + k → D.getD w 0 ≤ 1) ∧
      (∀ u v, u < 14 + k → v < 14 + k → u ∉ R k → v ∉ R k →
        0 < D.getD u 0 → 0 < D.getD v 0 → u = v) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun w hw => ?_, fun u v hu hv _ _ hpu hpv => ?_⟩
      · rw [hD0 w (by omega)]; split_ifs <;> omega
      · rw [hD0 u (by omega)] at hpu
        rw [hD0 v (by omega)] at hpv
        split_ifs at hpu hpv with h1 h2 <;> omega
    | succ k ih =>
      intro hk
      have hk' : k < gs.length := by omega
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨hop, a, b, hin, hab, ha, hb⟩ := hg k gs[k] (List.getElem?_eq_getElem hk')
      have hRk : R (k+1) = R k ++ [a, b] := by rw [hRsucc k hk', hin]
      have hFa : (F k).getD a 0 = D.getD a 0 := (hDget k a (by omega) ha).symm
      have hFb : (F k).getD b 0 = D.getD b 0 := (hDget k b (by omega) hb).symm
      have hnew : D.getD (14 + k) 0 = gs[k].lineDegree (F k) := by
        rw [hDget (k+1) (14+k) hk (by omega), hFsucc k hk',
          List.getD_append_right _ _ _ _ (by rw [hFlen k (by omega)])]
        simp [hFlen k (by omega)]
      have hval : (gs[k].op = GateOp.and → D.getD (14 + k) 0 = D.getD a 0 + D.getD b 0) ∧
          (gs[k].op = GateOp.or → D.getD (14 + k) 0 = max (D.getD a 0) (D.getD b 0)) := by
        rw [hnew]
        unfold Gate.lineDegree
        rw [hin]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [if_pos h]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          rw [hFa, hFb]
          omega
        · rw [if_neg (by rw [h]; exact fun e => GateOp.noConfusion e)]
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [hFa, hFb]
          omega
      have hpos : 0 < D.getD (14 + k) 0 → 0 < D.getD a 0 ∨ 0 < D.getD b 0 := by
        intro h
        rcases hop with h1 | h1
        · rw [hval.1 h1] at h; omega
        · rw [hval.2 h1] at h; omega
      have hRa : a ∈ R k → D.getD a 0 = 0 := hRR k hk' a (by rw [hin]; simp)
      have hRb : b ∈ R k → D.getD b 0 = 0 := hRR k hk' b (by rw [hin]; simp)
      have hle : D.getD (14 + k) 0 ≤ 1 := by
        have h1 := ih1 a (by omega)
        have h2 := ih1 b (by omega)
        rcases hop with hh | hh
        · rw [hval.1 hh]
          by_contra hcon
          have pa : 0 < D.getD a 0 := by omega
          have pb : 0 < D.getD b 0 := by omega
          have na : a ∉ R k := fun hm => by have := hRa hm; omega
          have nb : b ∉ R k := fun hm => by have := hRb hm; omega
          exact hab (ih2 a b ha hb na nb pa pb)
        · rw [hval.2 hh]; omega
      refine ⟨fun w hw => ?_, fun u v hu hv hu' hv' hpu hpv => ?_⟩
      · by_cases hwk : w < 14 + k
        · exact ih1 w hwk
        · have : w = 14 + k := by omega
          rw [this]; exact hle
      · rw [hRk] at hu' hv'
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hu' hv'
        obtain ⟨hu1, hu2, hu3⟩ := hu'
        obtain ⟨hv1, hv2, hv3⟩ := hv'
        by_cases huk : u < 14 + k <;> by_cases hvk : v < 14 + k
        · exact ih2 u v huk hvk hu1 hv1 hpu hpv
        · have hv14 : v = 14 + k := by omega
          rw [hv14] at hpv
          rcases hpos hpv with pa | pb
          · have na : a ∉ R k := fun hm => by have := hRa hm; omega
            exact absurd (ih2 u a huk ha hu1 na hpu pa) hu2
          · have nb : b ∉ R k := fun hm => by have := hRb hm; omega
            exact absurd (ih2 u b huk hb hu1 nb hpu pb) hu3
        · have hu14 : u = 14 + k := by omega
          rw [hu14] at hpu
          rcases hpos hpu with pa | pb
          · have na : a ∉ R k := fun hm => by have := hRa hm; omega
            exact absurd (ih2 v a hvk ha hv1 na hpv pa) hv2
          · have nb : b ∉ R k := fun hm => by have := hRb hm; omega
            exact absurd (ih2 v b hvk hb hv1 nb hpv pb) hv3
        · omega
  show (C.lineDegrees 14 {x2}).getD C.output 0 ≤ 1
  rw [hD]
  by_cases ho : C.output < 14 + gs.length
  · exact (hQ gs.length le_rfl).1 C.output ho
  · rw [List.getD_eq_default]
    · omega
    · rw [foldl_len, hinitlen]; omega

end PEqualNP.Outside.L_meta_3795

open PEqualNP.Outside.L_meta_3795 in
theorem PEqualNP.Outside.L_meta_3795 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x2 < (14 : ℕ), (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 ≠ x8 ∧ x7 < (14 : ℕ) + x4 ∧ x8 < (14 : ℕ) + x4) → (List.filter (fun (x5 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x5)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup → List.count x2 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ≤ (1 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {x2} x1 (1 : ℕ) := by
  intro x1 x2 hx2 hg hnd hc
  exact main x1 x2 hx2 hg hnd hc
