import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25481_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-! ## Wire values (copied from `PEqualNP.Outside.L_meta_5520`) -/

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

/-! ## The inputs `oneEach` -/

lemma oneEach_length {n m : ℕ} (u : Fin n) (c : Fin m) :
    (PEqualNP.Represents.oneEach u c).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

lemma oneEach_row {n m : ℕ} (u : Fin n) (c : Fin m) {i : ℕ} (hi : i < n) :
    (PEqualNP.Represents.oneEach u c).getD i false = decide (i = u.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
  simp [hi, Fin.ext_iff]

lemma oneEach_col {n m : ℕ} (u v : Fin n) (c : Fin m) {i : ℕ} (hi : n ≤ i) :
    (PEqualNP.Represents.oneEach u c).getD i false =
      (PEqualNP.Represents.oneEach v c).getD i false := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simpa using hi), List.getElem?_append_right (by simpa using hi)]
  simp

/-! ## Safe wires -/

/-- One operand step that avoids `O` at both ends. -/
def R (N O : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a ≠ O ∧ b ≠ O ∧ ∃ j : Fin C.gates.length, b = N + j.val ∧ a ∈ (gateAt C j.val).inputs

/-- Every safe wire (the wire `O`, or a wire other than `u` not reached from `u` by an
`O`-avoiding operand path) is on at `y` when it is on at `x`. -/
theorem safe_mono {N : ℕ} {C : Circuit} (hM : Monotone2 C) {x y : List Bool}
    (hx : x.length = N) (hy : y.length = N) (u O : ℕ)
    (hO : val C y O = true)
    (hin : ∀ i, i < N → i ≠ u → x.getD i false = true → y.getD i false = true) :
    ∀ w, (w = O ∨ (w ≠ u ∧ ¬ Relation.TransGen (R N O C) u w)) →
      val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hs hw
    by_cases hwO : w = O
    · subst hwO; exact hO
    obtain ⟨hwu, hnt⟩ := hs.resolve_left hwO
    by_cases h1 : w < N
    · rw [val_input hx h1] at hw; rw [val_input hy h1]; exact hin w h1 hwu hw
    · by_cases h2 : N + C.gates.length ≤ w
      · rw [val_ge hx h2] at hw; exact absurd hw (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [val_gate hx hj] at hw
        rw [val_gate hy hj]
        have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq hj]; exact List.getElem_mem hj
        have hop := (hM _ hg).1
        have hstep : ∀ i ∈ (gateAt C j).inputs,
            (if i < N + j then val C x i else false) = true →
            (if i < N + j then val C y i else false) = true := by
          intro i hiin hi
          by_cases hlt : i < N + j
          · rw [if_pos hlt] at hi ⊢
            apply ih i hlt _ hi
            by_cases hiO : i = O
            · exact Or.inl hiO
            · right
              have hR : R N O C i (N + j) := ⟨hiO, hwO, ⟨j, hj⟩, rfl, hiin⟩
              refine ⟨?_, ?_⟩
              · rintro rfl
                exact hnt (Relation.TransGen.single hR)
              · intro ht
                exact hnt (Relation.TransGen.tail ht hR)
          · rw [if_neg hlt] at hi; exact absurd hi (by simp)
        rcases hop with h | h
        · rw [h] at hw ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hw ⊢
          rintro b ⟨i, hi, rfl⟩
          exact hstep i hi (hw _ ⟨i, hi, rfl⟩)
        · have h' : (gateAt C j).op = GateOp.or := h
          rw [h'] at hw ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hw ⊢
          obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hw
          exact ⟨_, ⟨i, hi, rfl⟩, hstep i hi hb⟩

end PEqualNP.Outside.L_meta_25481_aux

theorem PEqualNP.Outside.L_meta_25481 :
  ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (u v : Fin n) (O : ℕ),
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
    PEqualNP.Represents.Represents G C →
    u ≠ v →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
    C.output ≠ u.val →
    O < n + m + C.gates.length →
    (∀ c : Fin m, (C.wires (PEqualNP.Represents.oneEach v c)).getD O false = true) →
    (¬ Relation.TransGen
      (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
        ∃ j : Fin C.gates.length, b = n + m + j.val ∧
          a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs)
      u.val C.output) →
    ∀ c : Fin m, G u c = true → G v c = true := by
  intro n m G C u v O hM _hRB hRep _huv _hread hout _hOlt hOn hsafe c hGu
  have key := PEqualNP.Outside.L_meta_25481_aux.safe_mono (N := n + m) hM
    (PEqualNP.Outside.L_meta_25481_aux.oneEach_length u c)
    (PEqualNP.Outside.L_meta_25481_aux.oneEach_length v c) u.val O (hOn c) (by
      intro i hi hne h
      by_cases hin : i < n
      · rw [PEqualNP.Outside.L_meta_25481_aux.oneEach_row u c hin] at h
        exact absurd (of_decide_eq_true h) hne
      · rw [PEqualNP.Outside.L_meta_25481_aux.oneEach_col u v c (Nat.le_of_not_lt hin)] at h
        exact h) C.output (by
      by_cases ho : C.output = O
      · exact Or.inl ho
      · exact Or.inr ⟨hout, hsafe⟩)
  rw [← hRep v c]
  rw [← hRep u c] at hGu
  exact key hGu
