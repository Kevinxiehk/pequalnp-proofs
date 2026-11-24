import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- One evaluation step. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- Evaluation of a gate list from a starting wire list. -/
def wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wf C.gates x := rfl

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (step w g) := rfl

theorem wf_append (gs gs' : List Gate) (w : List Bool) :
    wf (gs ++ gs') w = wf gs' (wf gs w) := by
  simp [wf, List.foldl_append]

theorem length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem length_wf (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    rw [wf_cons, ih, length_step]
    simp; omega

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  rw [List.getD_append _ _ _ _ h]

theorem getD_step_eq (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem getD_wf_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [wf_cons, ih _ _ (by rw [length_step]; omega), getD_step_lt _ _ _ h]

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  simp

/-- A gate with its inputs relabelled by `m`. -/
def rel (m : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map m⟩

/-- Relabelling the wires: inputs below `n0` go below `c`, gate wires shift from `n0` to `c`. -/
theorem relabel (m : ℕ → ℕ) (n0 c : ℕ) (hm1 : ∀ i, i < n0 → m i < c)
    (hm2 : ∀ i, n0 ≤ i → m i = c + (i - n0)) (gs : List Gate) :
    ∀ (k : ℕ) (V W : List Bool), V.length = n0 + k → W.length = c + k →
      (∀ i, V.getD i false = W.getD (m i) false) →
      ∀ i, (wf gs V).getD i false = (wf (gs.map (rel m)) W).getD (m i) false := by
  induction gs with
  | nil => intro k V W _ _ hVW i; exact hVW i
  | cons g gs ih =>
    intro k V W hV hW hVW
    rw [List.map_cons]
    intro i
    rw [wf_cons, wf_cons]
    apply ih (k + 1)
    · rw [length_step, hV]; omega
    · rw [length_step, hW]; omega
    · intro i'
      by_cases hlt : i' < V.length
      · have hmlt : m i' < W.length := by
          by_cases h0 : i' < n0
          · have := hm1 i' h0; omega
          · have := hm2 i' (by omega); omega
        rw [getD_step_lt _ _ _ hlt, hVW i', getD_step_lt _ _ _ hmlt]
      · by_cases heq : i' = V.length
        · subst heq
          have hm : m V.length = W.length := by rw [hm2 _ (by omega)]; omega
          rw [hm, getD_step_eq, getD_step_eq]
          simp only [rel, List.map_map]
          congr 1
          apply List.map_congr_left
          intro j _
          exact hVW j
        · have hm : W.length + 1 ≤ m i' := by rw [hm2 _ (by omega)]; omega
          rw [getD_ge _ _ (by rw [length_step]; omega), getD_ge _ _ (by rw [length_step]; omega)]

/-- gateAt on an appended list, left part. -/
theorem gateAt_append_left (gs gs' : List Gate) (j : ℕ) (h : j < gs.length) :
    gateAt ⟨gs ++ gs', 0⟩ j = gateAt ⟨gs, 0⟩ j := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gateAt_out (C : Circuit) (o : ℕ) (j : ℕ) : gateAt ⟨C.gates, o⟩ j = gateAt C j := rfl

/-- Adding one edge `(a, b)` costs two gates: an AND of the two inputs and an OR into the output. -/
theorem add_edge (n : ℕ) (D : Circuit) (a b : ℕ) (ha : a < n) (hb : b < n)
    (hD : PEqualNP.TopForm.IsAO2 n D) (ho : D.output < n + D.size) :
    PEqualNP.TopForm.IsAO2 n ⟨D.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + D.size]⟩], n + D.size + 1⟩ ∧
    (⟨D.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + D.size]⟩], n + D.size + 1⟩ : Circuit).size = D.size + 2 ∧
    n + D.size + 1 < n + (D.size + 2) ∧
    ∀ x : List Bool, x.length = n →
      (⟨D.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + D.size]⟩], n + D.size + 1⟩ : Circuit).eval x
        = (D.eval x || (x.getD a false && x.getD b false)) := by
  obtain ⟨hao, hrb, h2⟩ := hD
  refine ⟨⟨?_, ?_, ?_⟩, ?_, by omega, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hao g hg
    · simp at hg; rcases hg with rfl | rfl <;> simp
  · intro j hj i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hjl : j < D.gates.length
    · have : gateAt ⟨D.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + D.size]⟩], n + D.size + 1⟩ j
          = gateAt D j := by
        simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hjl]
      rw [this] at hi
      exact hrb j hjl i hi
    · have hsz : D.size = D.gates.length := rfl
      by_cases hj0 : j = D.gates.length
      · subst hj0
        simp [gateAt, List.getD_eq_getElem?_getD] at hi
        omega
      · have hj1 : j = D.gates.length + 1 := by omega
        subst hj1
        simp [gateAt, List.getD_eq_getElem?_getD] at hi
        rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h2 g hg
    · simp at hg; rcases hg with rfl | rfl <;> simp
  · simp [Circuit.size]
  · intro x hx
    have hsz : D.size = D.gates.length := rfl
    simp only [Circuit.eval]
    rw [wires_eq, wires_eq, wf_append]
    have hWl : (wf D.gates x).length = n + D.size := by rw [length_wf, hx, hsz]
    generalize hW : wf D.gates x = W at hWl ⊢
    have hWa : W.getD a false = x.getD a false := by
      rw [← hW]; exact getD_wf_lt _ _ _ (by rw [hx]; exact ha)
    have hWb : W.getD b false = x.getD b false := by
      rw [← hW]; exact getD_wf_lt _ _ _ (by rw [hx]; exact hb)
    have h2 : wf [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + D.size]⟩] W
        = step (step W ⟨GateOp.and, [a, b]⟩) ⟨GateOp.or, [D.output, n + D.size]⟩ := rfl
    rw [h2]
    have h1 : (step W ⟨GateOp.and, [a, b]⟩).length = n + D.size + 1 := by rw [length_step, hWl]
    rw [← h1, getD_step_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id]
    rw [getD_step_lt _ _ _ (by rw [hWl]; exact ho), ← hWl, getD_step_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id,
      hWa, hWb]

end PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_3264 in
theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro x1 x2 x3 C hne hC hf
  dsimp only
  have hsz : C.size = C.gates.length := rfl
  -- the output wire exists: otherwise the circuit is constantly false
  have hout : C.output < (x1 + x2) + C.size := by
    by_contra hge
    push_neg at hge
    obtain ⟨⟨p, l⟩, hpl⟩ := hne
    have h := hf (fun _ => true)
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval] at h
    rw [getD_ge _ _ (by rw [wires_eq, length_wf]; simp only [List.length_ofFn]; omega)] at h
    have h2 : ∃ (a : Fin x1) (b : Fin x2), (a, b) ∈ x3 ∧ True ∧ True := ⟨p, l, hpl, trivial, trivial⟩
    rw [decide_eq_true h2] at h
    exact Bool.false_ne_true h
  -- the relabelled circuit on the doubled inputs
  let m : ℕ → ℕ := fun i => if i < x1 then i else if i < x1 + x2 then (x1 + x2) + i
    else (x1 + x2) + (x1 + x2) + (i - (x1 + x2))
  have hm1 : ∀ i, i < x1 + x2 → m i < (x1 + x2) + (x1 + x2) := by
    intro i hi; simp only [m]; split_ifs <;> omega
  have hm2 : ∀ i, x1 + x2 ≤ i → m i = (x1 + x2) + (x1 + x2) + (i - (x1 + x2)) := by
    intro i hi; simp only [m]; split_ifs <;> omega
  obtain ⟨hao, hrb, h2⟩ := hC
  have base : ∃ D : Circuit, PEqualNP.TopForm.IsAO2 ((x1 + x2) + (x1 + x2)) D ∧ D.size ≤ C.size ∧
      D.output < (x1 + x2) + (x1 + x2) + D.size ∧
      ∀ z : Fin ((x1 + x2) + (x1 + x2)) → Bool, D.eval (List.ofFn z) = decide (∃ (a b : Fin (x1 + x2)),
        (a, b) ∈ Finset.image (fun (y : Fin x1 × Fin x2) => (Fin.castAdd x2 y.1, Fin.natAdd x1 y.2)) x3 ∧
        z (Fin.castAdd (x1 + x2) a) = true ∧ z (Fin.natAdd (x1 + x2) b) = true) := by
    refine ⟨⟨C.gates.map (rel m), m C.output⟩, ⟨?_, ?_, ?_⟩, by simp [Circuit.size], ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact hao g0 hg0
    · intro j hj i hi
      simp only [List.length_map] at hj
      have hga : gateAt ⟨C.gates.map (rel m), m C.output⟩ j = rel m (gateAt C j) := by
        simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
          Option.map_some, Option.getD_some]
      rw [hga] at hi
      simp only [rel, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have := hrb j hj i0 hi0
      simp only [m]; split_ifs <;> omega
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      simpa [rel] using h2 g0 hg0
    · simp only [Circuit.size, List.length_map] at hout ⊢
      by_cases ho : C.output < x1 + x2
      · have := hm1 _ ho; omega
      · rw [hm2 _ (by omega)]; omega
    · intro z
      let y : Fin (x1 + x2) → Bool := fun i => (List.ofFn z).getD (m i) false
      have hrel := relabel m (x1 + x2) ((x1 + x2) + (x1 + x2)) hm1 hm2 C.gates 0 (List.ofFn y) (List.ofFn z)
        (by simp) (by simp) (by
          intro i
          by_cases hi : i < x1 + x2
          · rw [getD_ofFn _ _ hi]
          · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; rw [hm2 _ (by omega)]; omega)]) C.output
      simp only [Circuit.eval]
      rw [wires_eq, ← hrel]
      have hfy := hf y
      simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval] at hfy
      rw [wires_eq] at hfy
      rw [hfy]
      apply decide_eq_decide.2
      have hy1 : ∀ p : Fin x1, y (Fin.castAdd x2 p) = z (Fin.castAdd (x1 + x2) (Fin.castAdd x2 p)) := by
        intro p
        have hp := p.isLt
        show (List.ofFn z).getD (m p) false = _
        have hmp : m p = p := by simp only [m]; rw [if_pos hp]
        rw [hmp, getD_ofFn _ _ (by omega)]
        rfl
      have hy2 : ∀ l : Fin x2, y (Fin.natAdd x1 l) = z (Fin.natAdd (x1 + x2) (Fin.natAdd x1 l)) := by
        intro l
        have hl := l.isLt
        show (List.ofFn z).getD (m (x1 + l)) false = _
        have hml : m (x1 + l) = (x1 + x2) + (x1 + l) := by
          simp only [m]; rw [if_neg (by omega), if_pos (by omega)]
        rw [hml, getD_ofFn _ _ (by omega)]
        rfl
      constructor
      · rintro ⟨p, l, hpl, h1, h3⟩
        exact ⟨_, _, Finset.mem_image_of_mem _ hpl, by rw [← hy1]; exact h1, by rw [← hy2]; exact h3⟩
      · rintro ⟨a, b, hab, h1, h3⟩
        obtain ⟨⟨p, l⟩, hpl, he⟩ := Finset.mem_image.1 hab
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨p, l, hpl, by rw [hy1]; exact h1, by rw [hy2]; exact h3⟩
  have key : ∀ s : Finset (Fin (x1 + x2) × Fin (x1 + x2)), ∃ D : Circuit,
      PEqualNP.TopForm.IsAO2 ((x1 + x2) + (x1 + x2)) D ∧ D.size ≤ C.size + 2 * s.card ∧
      D.output < (x1 + x2) + (x1 + x2) + D.size ∧
      ∀ z : Fin ((x1 + x2) + (x1 + x2)) → Bool, D.eval (List.ofFn z) = decide (∃ (a b : Fin (x1 + x2)),
        (a, b) ∈ Finset.image (fun (y : Fin x1 × Fin x2) => (Fin.castAdd x2 y.1, Fin.natAdd x1 y.2)) x3 ∪ s ∧
        z (Fin.castAdd (x1 + x2) a) = true ∧ z (Fin.natAdd (x1 + x2) b) = true) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨D, hD, hDs, hDo, hDf⟩ := base
      refine ⟨D, hD, by simpa using hDs, hDo, ?_⟩
      intro z
      rw [Finset.union_empty]
      exact hDf z
    | insert e s hes ih =>
      obtain ⟨D, hD, hDs, hDo, hDf⟩ := ih
      have ha : (e.1 : ℕ) < (x1 + x2) + (x1 + x2) := by have := e.1.isLt; omega
      have hb : (x1 + x2) + (e.2 : ℕ) < (x1 + x2) + (x1 + x2) := by have := e.2.isLt; omega
      obtain ⟨hD', hsz', hout', heval⟩ := add_edge ((x1 + x2) + (x1 + x2)) D e.1 ((x1 + x2) + e.2) ha hb hD hDo
      refine ⟨_, hD', ?_, ?_, ?_⟩
      · rw [hsz', Finset.card_insert_of_notMem hes]; omega
      · rw [hsz']; exact hout'
      · intro z
        rw [heval (List.ofFn z) (by simp), hDf z, getD_ofFn _ _ ha, getD_ofFn _ _ hb]
        rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, Bool.and_eq_true]
        constructor
        · rintro (⟨a', b', hab, h1, h3⟩ | ⟨h1, h3⟩)
          · rcases Finset.mem_union.1 hab with hab | hab
            · exact ⟨a', b', Finset.mem_union.2 (Or.inl hab), h1, h3⟩
            · exact ⟨a', b', Finset.mem_union.2 (Or.inr (Finset.mem_insert_of_mem hab)), h1, h3⟩
          · exact ⟨e.1, e.2, Finset.mem_union.2 (Or.inr (Finset.mem_insert_self _ _)), h1, h3⟩
        · rintro ⟨a', b', hab, h1, h3⟩
          rcases Finset.mem_union.1 hab with hab | hab
          · exact Or.inl ⟨a', b', Finset.mem_union.2 (Or.inl hab), h1, h3⟩
          · rcases Finset.mem_insert.1 hab with he | hab
            · subst he
              exact Or.inr ⟨h1, h3⟩
            · exact Or.inl ⟨a', b', Finset.mem_union.2 (Or.inr hab), h1, h3⟩
  intro s
  obtain ⟨D, hD, hDs, _, hDf⟩ := key s
  exact ⟨D, hD, hDs, fun z => hDf z⟩
