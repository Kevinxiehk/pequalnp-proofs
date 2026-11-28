import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1188_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

/-! ## Running the gates (copied from L_meta_7730) -/

def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [value w g]) w

lemma run_ext (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [value w g])
    exact ⟨value w g :: t, by
      change run gs (w ++ [value w g]) = _
      rw [ht, List.append_assoc]
      rfl, by simp [hl]⟩

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_ext gs w
  rw [ht, List.length_append, hl]

lemma run_before (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_take (gs : List Gate) (w : List Bool) {j i : ℕ}
    (hj : j ≤ gs.length) (hi : i < w.length + j) :
    (run (gs.take j) w).getD i false = (run gs w).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_before _ _ _ (by simpa [run_length, List.length_take, min_eq_left hj])).symm

lemma gateAt_eq (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj

lemma split_gate (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) = C.gates := by
  rw [gateAt_eq C hj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]

lemma value_take (C : Circuit) {n j : ℕ} (xs : List Bool) (hx : xs.length = n)
    (hj : j ≤ C.gates.length) (g : Gate) (hb : ∀ i ∈ g.inputs, i < n + j) :
    value (run (C.gates.take j) xs) g = value (C.wires xs) g := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_take _ _ hj (by rw [hx]; exact hb i hi)

lemma wire_gate (C : Circuit) {n j : ℕ} (xs : List Bool) (hx : xs.length = n)
    (hr : ReadsBack n C) (hj : j < C.gates.length) :
    (C.wires xs).getD (n + j) false = value (C.wires xs) (gateAt C j) := by
  let w := run (C.gates.take j) xs
  let b := value w (gateAt C j)
  have hl : w.length = n + j := by
    simp [w, run_length, hx, List.length_take, min_eq_left (Nat.le_of_lt hj)]
  have he : C.wires xs = run (C.gates.drop (j + 1)) (w ++ [b]) := by
    change run C.gates xs = _
    conv_lhs => rw [← split_gate C hj, run_append]
    rfl
  calc
    _ = (w ++ [b]).getD (n + j) false := by
      rw [he, run_before _ _ _ (by simp [hl])]
    _ = b := by rw [← hl]; simp
    _ = _ := value_take C xs hx hj.le _ (hr j hj)

/-! ## Wire values on an input function -/

def W (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x ++ [false, true])).getD i false

lemma W_lt (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n + 2) :
    W C x i = (List.ofFn x ++ [false, true]).getD i false := by
  unfold W
  exact run_before C.gates _ i (by simpa using hi)

@[simp] lemma W_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    W C x v.val = x v := by
  rw [W_lt C x v.val (by omega), List.getD_append _ _ _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp)]
  simp

lemma W_n (C : Circuit) {n : ℕ} (x : Fin n → Bool) : W C x n = false := by
  rw [W_lt C x n (by omega), List.getD_append_right _ _ _ _ (by simp), List.length_ofFn,
    Nat.sub_self]
  rfl

lemma W_n1 (C : Circuit) {n : ℕ} (x : Fin n → Bool) : W C x (n + 1) = true := by
  rw [W_lt C x (n + 1) (by omega), List.getD_append_right _ _ _ _ (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left]
  rfl

lemma W_gate (C : Circuit) {n j : ℕ} (hr : ReadsBack (n + 2) C) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    W C x (n + 2 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C x)) := by
  unfold W
  rw [wire_gate C _ (by simp) hr hj]
  rfl

lemma W_gate_at (C : Circuit) {n : ℕ} (hr : ReadsBack (n + 2) C) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool) (m : ℕ) (hm : m = n + 2 + j) :
    W C x m = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C x)) := by
  subst hm
  exact W_gate C hr hj x

/-! ## Four-point value vectors -/

def enc (b0 b1 b2 b3 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0)

lemma enc_and (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    enc (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) = enc a0 a1 a2 a3 &&& enc b0 b1 b2 b3 := by
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

lemma enc_or (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    enc (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) = enc a0 a1 a2 a3 ||| enc b0 b1 b2 b3 := by
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

lemma enc_not (a0 a1 a2 a3 : Bool) :
    enc (!a0) (!a1) (!a2) (!a3) = enc a0 a1 a2 a3 ^^^ 15 := by
  revert a0 a1 a2 a3
  decide

lemma enc_lt (a0 a1 a2 a3 : Bool) : enc a0 a1 a2 a3 < 16 := by
  revert a0 a1 a2 a3
  decide

def V (C : Circuit) {n : ℕ} (x0 x1 x2 x3 : Fin n → Bool) (i : ℕ) : ℕ :=
  enc (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i)

lemma V_gate (C : Circuit) {n : ℕ} (hf : FanInTwo C) (hr : ReadsBack (n + 2) C) {j : ℕ}
    (hj : j < C.gates.length) (x0 x1 x2 x3 : Fin n → Bool) (M : ℕ → Prop)
    (hM : ∀ i < n + 2 + j, M (V C x0 x1 x2 x3 i)) :
    ((gateAt C j).op = GateOp.not →
      V C x0 x1 x2 x3 (n + 2 + j) = 15 ∨
        ∃ u, M u ∧ u < 16 ∧ V C x0 x1 x2 x3 (n + 2 + j) = u ^^^ 15) ∧
    ((gateAt C j).op ≠ GateOp.not →
      V C x0 x1 x2 x3 (n + 2 + j) = 0 ∨ V C x0 x1 x2 x3 (n + 2 + j) = 15 ∨
        ∃ u w, M u ∧ M w ∧ u < 16 ∧ w < 16 ∧
          (V C x0 x1 x2 x3 (n + 2 + j) = u &&& w ∨ V C x0 x1 x2 x3 (n + 2 + j) = u ||| w)) := by
  have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C hj]; exact List.getElem_mem _
  have hfg := hf _ hg
  have hin : ∀ i ∈ (gateAt C j).inputs, i < n + 2 + j := hr j hj
  have hV : V C x0 x1 x2 x3 (n + 2 + j) =
      enc ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x0)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x1)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x2)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x3))) := by
    simp only [V, W_gate C hr hj]
  rw [hV]
  generalize gateAt C j = g at hfg hin ⊢
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hfg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hVi : ∀ i ∈ ins, M (V C x0 x1 x2 x3 i) := fun i hi => hM i (hin i hi)
  rcases ins with _ | ⟨i, _ | ⟨i', _ | ⟨i'', rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨fun h => (by cases h), fun _ => Or.inr (Or.inl rfl)⟩
    · exact ⟨fun h => (by cases h), fun _ => Or.inl rfl⟩
    · exact ⟨fun _ => Or.inl rfl, fun h => absurd rfl h⟩
  · have hi := hVi i (by simp)
    have hlt := enc_lt (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i)
    rcases hop with rfl | rfl | rfl
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi, hlt, hlt, Or.inl ?_⟩)⟩
      rw [Nat.and_self]
      simp [GateOp.eval, V]
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi, hlt, hlt, Or.inr ?_⟩)⟩
      rw [Nat.or_self]
      simp [GateOp.eval, V]
    · refine ⟨fun _ => Or.inr ⟨_, hi, hlt, ?_⟩, fun h => absurd rfl h⟩
      rw [V, ← enc_not]
      simp [GateOp.eval]
  · have hi := hVi i (by simp)
    have hi' := hVi i' (by simp)
    have hlt := enc_lt (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i)
    have hlt' := enc_lt (W C x0 i') (W C x1 i') (W C x2 i') (W C x3 i')
    rcases hop with rfl | rfl | rfl
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi', hlt, hlt', Or.inl ?_⟩)⟩
      rw [V, V, ← enc_and]
      simp [GateOp.eval]
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi', hlt, hlt', Or.inr ?_⟩)⟩
      rw [V, V, ← enc_or]
      simp [GateOp.eval]
    · refine ⟨fun _ => Or.inr ⟨_, hi, hlt, ?_⟩, fun h => absurd rfl h⟩
      rw [V, ← enc_not]
      simp [GateOp.eval]
  · exfalso
    simp only [List.length_cons] at hlen
    omega

/-! ## NOT counts of gate lists -/

lemma nc_append_not (l : List Gate) (g : Gate) (h : g.op = GateOp.not) :
    notCount ⟨l ++ [g], 0⟩ = notCount ⟨l, 0⟩ + 1 := by
  simp [notCount, List.filter_append, h]

lemma nc_append_ne (l : List Gate) (g : Gate) (h : g.op ≠ GateOp.not) :
    notCount ⟨l ++ [g], 0⟩ = notCount ⟨l, 0⟩ := by
  simp [notCount, List.filter_append, h]

lemma nc_cons_not (l : List Gate) (g : Gate) (h : g.op = GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ + 1 := by
  simp [notCount, h]

lemma nc_cons_ne (l : List Gate) (g : Gate) (h : g.op ≠ GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ := by
  simp [notCount, h]

lemma nc_sublist {l₁ l₂ : List Gate} (h : l₁.Sublist l₂) :
    notCount ⟨l₁, 0⟩ ≤ notCount ⟨l₂, 0⟩ := by
  unfold notCount
  exact (h.filter _).length_le

lemma nc_le_length (C : Circuit) : notCount C ≤ C.gates.length := by
  unfold notCount
  exact List.length_filter_le _ _

lemma take_succ_gate (C : Circuit) {k : ℕ} (hk : k < C.gates.length) :
    C.gates.take (k + 1) = C.gates.take k ++ [gateAt C k] := by
  rw [gateAt_eq C hk, List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

/-! ## Bounded search over sets of value vectors -/

def mem (S v : ℕ) : Bool := S.testBit v

def ins (S v : ℕ) : ℕ := S ||| 2 ^ v

lemma mem_ins (S v u : ℕ) : mem (ins S v) u = (mem S u || decide (v = u)) := by
  simp [mem, ins, Nat.testBit_two_pow]

def goal (S : ℕ) : Bool := mem S 6 && mem S 12

def okAO (S v : ℕ) : Bool :=
  v == 0 || v == 15 || (List.range 16).any (fun u => mem S u &&
    (List.range 16).any (fun w => mem S w && (u &&& w == v || u ||| w == v)))

def okN (S v : ℕ) : Bool :=
  v == 15 || (List.range 16).any (fun u => mem S u && u ^^^ 15 == v)

def search : ℕ → ℕ → ℕ → Bool
  | 0, _, S => goal S
  | k + 1, 0, S => goal S || (List.range 16).any (fun v =>
      !mem S v && okAO S v && search k 0 (ins S v))
  | k + 1, r + 1, S => goal S || (List.range 16).any (fun v =>
      !mem S v && ((okAO S v && search k (r + 1) (ins S v)) ||
        (okN S v && search k r (ins S v))))

lemma search_goal {k r S : ℕ} (h : goal S = true) : search k r S = true := by
  cases k with
  | zero => simpa [search] using h
  | succ k => cases r <;> simp [search, h]

lemma search_sz (k S : ℕ) : search (k + 1) 0 S = (goal S || (List.range 16).any (fun v =>
      !mem S v && okAO S v && search k 0 (ins S v))) := rfl

lemma search_ss (k r S : ℕ) : search (k + 1) (r + 1) S = (goal S || (List.range 16).any (fun v =>
      !mem S v && ((okAO S v && search k (r + 1) (ins S v)) ||
        (okN S v && search k r (ins S v))))) := rfl

lemma search_mono_k (k : ℕ) : ∀ r S, search k r S = true → search (k + 1) r S = true := by
  induction k with
  | zero =>
    intro r S h
    exact search_goal (by simpa [search] using h)
  | succ k ih =>
    intro r S h
    cases r with
    | zero =>
      rw [search_sz] at h ⊢
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with h | ⟨v, hv, hb⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hb.1, ih _ _ hb.2⟩
    | succ r =>
      rw [search_ss] at h ⊢
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with h | ⟨v, hv, hm, ⟨ho, hs⟩ | ⟨ho, hs⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hm, Or.inl ⟨ho, ih _ _ hs⟩⟩
      · exact Or.inr ⟨v, hv, hm, Or.inr ⟨ho, ih _ _ hs⟩⟩

lemma search_mono_r (k : ℕ) : ∀ r S, search k r S = true → search k (r + 1) S = true := by
  induction k with
  | zero =>
    intro r S h
    simpa [search] using h
  | succ k ih =>
    intro r S h
    cases r with
    | zero =>
      rw [search_sz] at h
      rw [search_ss]
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with h | ⟨v, hv, ⟨hm, ho⟩, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hm, Or.inl ⟨ho, ih _ _ hs⟩⟩
    | succ r =>
      rw [search_ss] at h
      rw [search_ss]
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with h | ⟨v, hv, hm, ⟨ho, hs⟩ | ⟨ho, hs⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hm, Or.inl ⟨ho, ih _ _ hs⟩⟩
      · exact Or.inr ⟨v, hv, hm, Or.inr ⟨ho, ih _ _ hs⟩⟩

lemma search_mono {k k' r r' S : ℕ} (hk : k ≤ k') (hr : r ≤ r') (h : search k r S = true) :
    search k' r' S = true := by
  have h1 : search k r' S = true := by
    induction hr with
    | refl => exact h
    | step _ ih => exact search_mono_r _ _ _ ih
  induction hk with
  | refl => exact h1
  | step _ ih => exact search_mono_k _ _ _ ih

lemma search_step_ao {k r S v : ℕ} (hv : v < 16) (hm : mem S v = false)
    (ho : okAO S v = true) (h : search k r (ins S v) = true) : search (k + 1) r S = true := by
  cases r with
  | zero =>
    rw [search_sz, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨v, List.mem_range.2 hv, by simp [hm, ho, h]⟩
  | succ r =>
    rw [search_ss, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨v, List.mem_range.2 hv, by simp [hm, ho, h]⟩

lemma search_step_n {k r S v : ℕ} (hv : v < 16) (hm : mem S v = false)
    (ho : okN S v = true) (h : search k r (ins S v) = true) :
    search (k + 1) (r + 1) S = true := by
  rw [search_ss, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨v, List.mem_range.2 hv, by simp [hm, ho, h]⟩

lemma search_sound (C : Circuit) {n : ℕ} (hf : FanInTwo C) (hr : ReadsBack (n + 2) C)
    (x0 x1 x2 x3 : Fin n → Bool) (p q : ℕ) (hp : p < n + 2 + C.gates.length)
    (hq : q < n + 2 + C.gates.length) (hP : V C x0 x1 x2 x3 p = 6)
    (hQ : V C x0 x1 x2 x3 q = 12) :
    ∀ d j, j + d = C.gates.length → ∀ S,
      (∀ i < n + 2 + j, mem S (V C x0 x1 x2 x3 i) = true) →
        search d (notCount ⟨C.gates.drop j, 0⟩) S = true := by
  intro d
  induction d with
  | zero =>
    intro j hj S hS
    have h6 := hS p (by omega)
    have h12 := hS q (by omega)
    rw [hP] at h6
    rw [hQ] at h12
    exact search_goal (by simp [goal, h6, h12])
  | succ d ih =>
    intro j hj S hS
    have hjl : j < C.gates.length := by omega
    have hdrop : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [gateAt_eq C hjl]
      exact List.drop_eq_getElem_cons hjl
    rw [hdrop]
    have hvlt : V C x0 x1 x2 x3 (n + 2 + j) < 16 := enc_lt _ _ _ _
    have hgate := V_gate C hf hr hjl x0 x1 x2 x3 (fun u => mem S u = true) hS
    by_cases hm : mem S (V C x0 x1 x2 x3 (n + 2 + j)) = true
    · have h1 := ih (j + 1) (by omega) S (fun i hi => by
        rcases (show i < n + 2 + j ∨ i = n + 2 + j by omega) with h | h
        · exact hS i h
        · rw [h]; exact hm)
      by_cases hn : (gateAt C j).op = GateOp.not
      · rw [nc_cons_not _ _ hn]
        exact search_mono (Nat.le_succ d) (Nat.le_succ _) h1
      · rw [nc_cons_ne _ _ hn]
        exact search_mono (Nat.le_succ d) le_rfl h1
    · have hmS : mem S (V C x0 x1 x2 x3 (n + 2 + j)) = false := by simpa using hm
      have h1 := ih (j + 1) (by omega) (ins S (V C x0 x1 x2 x3 (n + 2 + j))) (fun i hi => by
        rw [mem_ins]
        rcases (show i < n + 2 + j ∨ i = n + 2 + j by omega) with h | h
        · simp [hS i h]
        · simp [h])
      by_cases hn : (gateAt C j).op = GateOp.not
      · rw [nc_cons_not _ _ hn]
        refine search_step_n hvlt hmS ?_ h1
        rcases hgate.1 hn with h | ⟨u, hu, hu16, h⟩
        · simp [okN, h]
        · simp only [okN, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
            beq_iff_eq]
          exact Or.inr ⟨u, hu16, hu, h.symm⟩
      · rw [nc_cons_ne _ _ hn]
        refine search_step_ao hvlt hmS ?_ h1
        rcases hgate.2 hn with h | h | ⟨u, w, hu, hw, hu16, hw16, h | h⟩
        · simp [okAO, h]
        · simp [okAO, h]
        · simp only [okAO, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
            beq_iff_eq]
          exact Or.inr ⟨u, hu16, hu, w, hw16, hw, Or.inl h.symm⟩
        · simp only [okAO, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
            beq_iff_eq]
          exact Or.inr ⟨u, hu16, hu, w, hw16, hw, Or.inr h.symm⟩

lemma chk3 : search 3 3 43137 = false := by decide +kernel

lemma chk4 : search 4 1 43137 = false := by decide +kernel

/-! ## Inputs fixed outside the three vertices -/

def inp {n : ℕ} (a b c : Fin n) (pa pb pc : Bool) : Fin n → Bool :=
  fun v => if v = a then pa else if v = b then pb else if v = c then pc else true

lemma inp_a {n : ℕ} (a b c : Fin n) (pa pb pc : Bool) : inp a b c pa pb pc a = pa := by
  simp [inp]

lemma inp_b {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (pa pb pc : Bool) :
    inp a b c pa pb pc b = pb := by
  simp [inp, hab.symm]

lemma inp_c {n : ℕ} {a b c : Fin n} (hbc : b ≠ c) (hac : a ≠ c) (pa pb pc : Bool) :
    inp a b c pa pb pc c = pc := by
  simp [inp, hac.symm, hbc.symm]

lemma inp_other {n : ℕ} {a b c v : Fin n} (h1 : v ≠ a) (h2 : v ≠ b) (h3 : v ≠ c)
    (pa pb pc : Bool) : inp a b c pa pb pc v = true := by
  simp [inp, h1, h2, h3]

lemma inp_cover {n : ℕ} {G : Finset (Fin n × Fin n)} {a b c : Fin n}
    (hG : ∀ e ∈ G, e.1 < e.2) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (pa pb pc : Bool)
    (h1 : (pa || pb) = true) (h2 : (pb || pc) = true)
    (h3 : ((a, c) ∈ G ∨ (c, a) ∈ G) → (pa || pc) = true) :
    ∀ e ∈ G, inp a b c pa pb pc e.1 = true ∨ inp a b c pa pb pc e.2 = true := by
  rintro ⟨u, v⟩ he
  have hne : u ≠ v := ne_of_lt (hG _ he)
  simp only
  by_cases hu : u = a ∨ u = b ∨ u = c
  swap
  · simp only [not_or] at hu
    exact Or.inl (inp_other hu.1 hu.2.1 hu.2.2 _ _ _)
  by_cases hv : v = a ∨ v = b ∨ v = c
  swap
  · simp only [not_or] at hv
    exact Or.inr (inp_other hv.1 hv.2.1 hv.2.2 _ _ _)
  have ia := inp_a a b c pa pb pc
  have ib := inp_b (c := c) hab pa pb pc
  have ic := inp_c hbc hac pa pb pc
  rw [Bool.or_eq_true] at h1 h2
  simp only [Bool.or_eq_true] at h3
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | (simp only [ia, ib, ic]; tauto)

lemma V_base (C : Circuit) {n : ℕ} {a b c : Fin n}
    (pa0 pa1 pa2 pa3 pb0 pb1 pb2 pb3 pc0 pc1 pc2 pc3 : Bool)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (i : ℕ) (hi : i < n + 2) :
    V C (inp a b c pa0 pb0 pc0) (inp a b c pa1 pb1 pc1) (inp a b c pa2 pb2 pc2)
        (inp a b c pa3 pb3 pc3) i ∈
      [0, 15, enc pa0 pa1 pa2 pa3, enc pb0 pb1 pb2 pb3, enc pc0 pc1 pc2 pc3] := by
  rcases (show i < n ∨ i = n ∨ i = n + 1 by omega) with h | h | h
  · obtain ⟨v, rfl⟩ : ∃ v : Fin n, v.val = i := ⟨⟨i, h⟩, rfl⟩
    simp only [V, W_input]
    by_cases ha : v = a
    · subst ha
      simp [inp_a]
    by_cases hb : v = b
    · subst hb
      simp [inp_b hab]
    by_cases hc : v = c
    · subst hc
      simp [inp_c hbc hac]
    · simp only [inp_other ha hb hc]
      rw [show enc true true true true = 15 from rfl]
      simp
  · subst h
    simp only [V, W_n]
    rw [show enc false false false false = 0 from rfl]
    simp
  · subst h
    simp only [V, W_n1]
    rw [show enc true true true true = 15 from rfl]
    simp

lemma V_target (C : Circuit) {n : ℕ} {G : Finset (Fin n × Fin n)} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (p q : ℕ)
    (hPQ : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      W C x p = xor (x a) (x b) ∧ W C x q = xor (x b) (x c))
    (pa0 pa1 pa2 pa3 pb0 pb1 pb2 pb3 pc0 pc1 pc2 pc3 : Bool)
    (c0 : ∀ e ∈ G, inp a b c pa0 pb0 pc0 e.1 = true ∨ inp a b c pa0 pb0 pc0 e.2 = true)
    (c1 : ∀ e ∈ G, inp a b c pa1 pb1 pc1 e.1 = true ∨ inp a b c pa1 pb1 pc1 e.2 = true)
    (c2 : ∀ e ∈ G, inp a b c pa2 pb2 pc2 e.1 = true ∨ inp a b c pa2 pb2 pc2 e.2 = true)
    (c3 : ∀ e ∈ G, inp a b c pa3 pb3 pc3 e.1 = true ∨ inp a b c pa3 pb3 pc3 e.2 = true) :
    V C (inp a b c pa0 pb0 pc0) (inp a b c pa1 pb1 pc1) (inp a b c pa2 pb2 pc2)
        (inp a b c pa3 pb3 pc3) p =
      enc (xor pa0 pb0) (xor pa1 pb1) (xor pa2 pb2) (xor pa3 pb3) ∧
    V C (inp a b c pa0 pb0 pc0) (inp a b c pa1 pb1 pc1) (inp a b c pa2 pb2 pc2)
        (inp a b c pa3 pb3 pc3) q =
      enc (xor pb0 pc0) (xor pb1 pc1) (xor pb2 pc2) (xor pb3 pc3) := by
  constructor
  · simp only [V, (hPQ _ c0).1, (hPQ _ c1).1, (hPQ _ c2).1, (hPQ _ c3).1, inp_a, inp_b hab]
  · simp only [V, (hPQ _ c0).2, (hPQ _ c1).2, (hPQ _ c2).2, (hPQ _ c3).2, inp_b hab,
      inp_c hbc hac]

/-! ## Closed sets of vectors and circuits with at most one NOT -/

abbrev closed (T : List ℕ) : Prop := ∀ u ∈ T, ∀ w ∈ T, u &&& w ∈ T ∧ u ||| w ∈ T

lemma one_not_inv (C : Circuit) {n : ℕ} (hf : FanInTwo C) (hr : ReadsBack (n + 2) C)
    (x0 x1 x2 x3 : Fin n → Bool) (T1 : List ℕ) (Tm : ℕ → List ℕ)
    (hT1 : closed T1) (h0 : 0 ∈ T1) (h15 : 15 ∈ T1)
    (hbase : ∀ i < n + 2, V C x0 x1 x2 x3 i ∈ T1)
    (hTm : ∀ u ∈ T1, closed (Tm u) ∧ (∀ v ∈ T1, v ∈ Tm u) ∧ u ^^^ 15 ∈ Tm u)
    (hnot : notCount C ≤ 1) :
    (∀ i < n + 2 + C.gates.length, V C x0 x1 x2 x3 i ∈ T1) ∨
      (1 ≤ notCount C ∧ ∃ u ∈ T1, ∀ i < n + 2 + C.gates.length, V C x0 x1 x2 x3 i ∈ Tm u) := by
  have step : ∀ T : List ℕ, closed T → 0 ∈ T → 15 ∈ T → ∀ k (hk : k < C.gates.length),
      (gateAt C k).op ≠ GateOp.not → (∀ i < n + 2 + k, V C x0 x1 x2 x3 i ∈ T) →
      ∀ i < n + 2 + (k + 1), V C x0 x1 x2 x3 i ∈ T := by
    intro T hT hT0 hT15 k hk hn hall i hi
    rcases (show i < n + 2 + k ∨ i = n + 2 + k by omega) with h | h
    · exact hall i h
    · subst h
      rcases (V_gate C hf hr hk x0 x1 x2 x3 (· ∈ T) hall).2 hn with
        h | h | ⟨u, w, hu, hw, -, -, h | h⟩
      · rw [h]; exact hT0
      · rw [h]; exact hT15
      · rw [h]; exact (hT u hu w hw).1
      · rw [h]; exact (hT u hu w hw).2
  have key : ∀ k, k ≤ C.gates.length →
      (notCount ⟨C.gates.take k, 0⟩ = 0 ∧ ∀ i < n + 2 + k, V C x0 x1 x2 x3 i ∈ T1) ∨
      (1 ≤ notCount ⟨C.gates.take k, 0⟩ ∧
        ∃ u ∈ T1, ∀ i < n + 2 + k, V C x0 x1 x2 x3 i ∈ Tm u) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact Or.inl ⟨by simp [notCount], fun i hi => hbase i (by omega)⟩
    | succ k ih =>
      intro hk
      have hk' : k < C.gates.length := by omega
      have hle : notCount ⟨C.gates.take (k + 1), 0⟩ ≤ 1 :=
        le_trans (nc_sublist (List.take_sublist _ _)) hnot
      rw [take_succ_gate C hk'] at hle ⊢
      by_cases hn : (gateAt C k).op = GateOp.not
      · rw [nc_append_not _ _ hn] at hle ⊢
        rcases ih hk'.le with ⟨_, hall⟩ | ⟨h1, -⟩
        · right
          refine ⟨by omega, ?_⟩
          have hg := (V_gate C hf hr hk' x0 x1 x2 x3 (· ∈ T1) hall).1 hn
          obtain ⟨u, hu, hv⟩ : ∃ u ∈ T1, V C x0 x1 x2 x3 (n + 2 + k) = u ^^^ 15 := by
            rcases hg with h | ⟨u, hu, -, h⟩
            · exact ⟨0, h0, h.trans (by decide)⟩
            · exact ⟨u, hu, h⟩
          refine ⟨u, hu, fun i hi => ?_⟩
          rcases (show i < n + 2 + k ∨ i = n + 2 + k by omega) with h | h
          · exact (hTm u hu).2.1 _ (hall i h)
          · rw [h, hv]; exact (hTm u hu).2.2
        · omega
      · rw [nc_append_ne _ _ hn] at hle ⊢
        rcases ih hk'.le with ⟨h0', hall⟩ | ⟨h1, u, hu, hall⟩
        · exact Or.inl ⟨h0', step T1 hT1 h0 h15 k hk' hn hall⟩
        · exact Or.inr ⟨h1, u, hu, step (Tm u) (hTm u hu).1 ((hTm u hu).2.1 0 h0)
            ((hTm u hu).2.1 15 h15) k hk' hn hall⟩
  rcases key C.gates.length le_rfl with ⟨-, h⟩ | ⟨h1, h⟩
  · exact Or.inl h
  · rw [List.take_length] at h1
    exact Or.inr ⟨h1, h⟩

def Tm (u : ℕ) : List ℕ :=
  if u = 12 then [0, 2, 3, 12, 14, 15] else if u = 14 then [0, 1, 12, 13, 14, 15]
  else [0, 12, 14, 15]

/-! ## The four lower bounds -/

section lower

variable {n : ℕ} {G : Finset (Fin n × Fin n)} {a b c : Fin n}

lemma lowA (hG : ∀ e ∈ G, e.1 < e.2) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack (n + 2) C) (p q : ℕ)
    (hp : p < n + 2 + C.gates.length)
    (hPQ : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      W C x p = xor (x a) (x b) ∧ W C x q = xor (x b) (x c))
    (h0 : notCount C = 0) : False := by
  have c0 := inp_cover hG hab hbc hac true true true rfl rfl (fun _ => rfl)
  have c1 := inp_cover hG hab hbc hac false true true rfl rfl (fun _ => rfl)
  have c2 := inp_cover hG hab hbc hac true false true rfl rfl (fun _ => rfl)
  have c3 := inp_cover hG hab hbc hac true true false rfl rfl (fun _ => rfl)
  have ht := (V_target C hab hbc hac p q hPQ true false true true true true false true
    true true true false c0 c1 c2 c3).1
  have hP6 : V C (inp a b c true true true) (inp a b c false true true)
      (inp a b c true false true) (inp a b c true true false) p = 6 := ht.trans (by decide)
  have hsub : ∀ z ∈ [0, 15, enc true false true true, enc true true false true,
      enc true true true false], z ∈ [0, 1, 3, 5, 7, 9, 11, 13, 15] := by decide
  rcases one_not_inv C hf hr (inp a b c true true true) (inp a b c false true true)
      (inp a b c true false true) (inp a b c true true false) [0, 1, 3, 5, 7, 9, 11, 13, 15]
      (fun _ => List.range 16) (by decide) (by decide) (by decide)
      (fun i hi => hsub _ (V_base C true false true true true true false true true true true
        false hab hbc hac i hi)) (by decide) (by omega) with h | ⟨h1, -⟩
  · have := h p hp
    rw [hP6] at this
    exact absurd this (by decide)
  · omega

lemma lowB (hG : ∀ e ∈ G, e.1 < e.2) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack (n + 2) C) (p q : ℕ)
    (hp : p < n + 2 + C.gates.length) (hq : q < n + 2 + C.gates.length)
    (hPQ : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      W C x p = xor (x a) (x b) ∧ W C x q = xor (x b) (x c))
    (hnac : ¬((a, c) ∈ G ∨ (c, a) ∈ G)) (hnot : notCount C ≤ 1) : False := by
  have c0 := inp_cover hG hab hbc hac false true false rfl rfl (fun h => absurd h hnac)
  have c1 := inp_cover hG hab hbc hac true true false rfl rfl (fun _ => rfl)
  have c2 := inp_cover hG hab hbc hac true true true rfl rfl (fun _ => rfl)
  have ht := V_target C hab hbc hac p q hPQ false true true true true true true true
    false false true true c0 c1 c2 c2
  have hP1 : V C (inp a b c false true false) (inp a b c true true false)
      (inp a b c true true true) (inp a b c true true true) p = 1 := ht.1.trans (by decide)
  have hQ3 : V C (inp a b c false true false) (inp a b c true true false)
      (inp a b c true true true) (inp a b c true true true) q = 3 := ht.2.trans (by decide)
  have hsub : ∀ z ∈ [0, 15, enc false true true true, enc true true true true,
      enc false false true true], z ∈ [0, 12, 14, 15] := by decide
  have hTm : ∀ u ∈ [0, 12, 14, 15], closed (Tm u) ∧ (∀ v ∈ [0, 12, 14, 15], v ∈ Tm u) ∧
      u ^^^ 15 ∈ Tm u := by decide
  have hTm' : ∀ u ∈ [0, 12, 14, 15], ¬(1 ∈ Tm u ∧ 3 ∈ Tm u) := by decide
  rcases one_not_inv C hf hr (inp a b c false true false) (inp a b c true true false)
      (inp a b c true true true) (inp a b c true true true) [0, 12, 14, 15] Tm
      (by decide) (by decide) (by decide)
      (fun i hi => hsub _ (V_base C false true true true true true true true false false true
        true hab hbc hac i hi)) hTm hnot with h | ⟨-, u, hu, h⟩
  · have h1 := h p hp
    have h3 := h q hq
    rw [hP1] at h1
    rw [hQ3] at h3
    exact absurd h1 (by decide)
  · have h1 := h p hp
    have h3 := h q hq
    rw [hP1] at h1
    rw [hQ3] at h3
    exact hTm' u hu ⟨h1, h3⟩

lemma lowCD (hG : ∀ e ∈ G, e.1 < e.2) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack (n + 2) C) (p q : ℕ)
    (hp : p < n + 2 + C.gates.length) (hq : q < n + 2 + C.gates.length)
    (hPQ : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      W C x p = xor (x a) (x b) ∧ W C x q = xor (x b) (x c)) :
    search C.gates.length (notCount C) 43137 = true := by
  have c0 := inp_cover hG hab hbc hac true true true rfl rfl (fun _ => rfl)
  have c1 := inp_cover hG hab hbc hac false true true rfl rfl (fun _ => rfl)
  have c2 := inp_cover hG hab hbc hac true false true rfl rfl (fun _ => rfl)
  have c3 := inp_cover hG hab hbc hac true true false rfl rfl (fun _ => rfl)
  have ht := V_target C hab hbc hac p q hPQ true false true true true true false true
    true true true false c0 c1 c2 c3
  have hP6 : V C (inp a b c true true true) (inp a b c false true true)
      (inp a b c true false true) (inp a b c true true false) p = 6 := ht.1.trans (by decide)
  have hQ12 : V C (inp a b c true true true) (inp a b c false true true)
      (inp a b c true false true) (inp a b c true true false) q = 12 := ht.2.trans (by decide)
  have hsub : ∀ z ∈ [0, 15, enc true false true true, enc true true false true,
      enc true true true false], mem 43137 z = true := by decide
  have h := search_sound C hf hr _ _ _ _ p q hp hq hP6 hQ12 C.gates.length 0 (by simp) 43137
    (fun i hi => hsub _ (V_base C true false true true true true false true true true true
      false hab hbc hac i (by omega)))
  rw [List.drop_zero] at h
  exact h

end lower

/-! ## The two explicit circuits -/

def circ1 (n : ℕ) (a b c : Fin n) : Circuit :=
  ⟨[⟨GateOp.and, [a.val, b.val]⟩, ⟨GateOp.not, [n + 2]⟩, ⟨GateOp.and, [b.val, c.val]⟩,
    ⟨GateOp.not, [n + 4]⟩], n + 3⟩

def circ2 (n : ℕ) (a b c : Fin n) : Circuit :=
  ⟨[⟨GateOp.and, [a.val, b.val]⟩, ⟨GateOp.and, [n + 2, c.val]⟩, ⟨GateOp.not, [n + 3]⟩,
    ⟨GateOp.and, [n + 4, c.val]⟩, ⟨GateOp.and, [n + 4, a.val]⟩], n + 5⟩

lemma circ1_fan (n : ℕ) (a b c : Fin n) : FanInTwo (circ1 n a b c) := by
  intro g hg
  simp [circ1] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

lemma circ2_fan (n : ℕ) (a b c : Fin n) : FanInTwo (circ2 n a b c) := by
  intro g hg
  simp [circ2] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

lemma circ1_reads (n : ℕ) (a b c : Fin n) : ReadsBack (n + 2) (circ1 n a b c) := by
  intro j hj i hi
  have := a.isLt
  have := b.isLt
  have := c.isLt
  simp only [circ1, List.length_cons, List.length_nil] at hj
  interval_cases j <;> simp [gateAt, circ1] at hi <;> omega

lemma circ2_reads (n : ℕ) (a b c : Fin n) : ReadsBack (n + 2) (circ2 n a b c) := by
  intro j hj i hi
  have := a.isLt
  have := b.isLt
  have := c.isLt
  simp only [circ2, List.length_cons, List.length_nil] at hj
  interval_cases j <;> simp [gateAt, circ2] at hi <;> omega

lemma circ1_not (n : ℕ) (a b c : Fin n) : notCount (circ1 n a b c) = 2 := by
  simp [notCount, circ1]

lemma circ2_not (n : ℕ) (a b c : Fin n) : notCount (circ2 n a b c) = 1 := by
  simp [notCount, circ2]

lemma circ1_eval (n : ℕ) (a b c : Fin n) (x : Fin n → Bool) (h1 : x a = true ∨ x b = true)
    (h2 : x b = true ∨ x c = true) :
    W (circ1 n a b c) x (n + 3) = xor (x a) (x b) ∧
      W (circ1 n a b c) x (n + 5) = xor (x b) (x c) := by
  have hr := circ1_reads n a b c
  have g0 : gateAt (circ1 n a b c) 0 = ⟨GateOp.and, [a.val, b.val]⟩ := rfl
  have g1 : gateAt (circ1 n a b c) 1 = ⟨GateOp.not, [n + 2]⟩ := rfl
  have g2 : gateAt (circ1 n a b c) 2 = ⟨GateOp.and, [b.val, c.val]⟩ := rfl
  have g3 : gateAt (circ1 n a b c) 3 = ⟨GateOp.not, [n + 4]⟩ := rfl
  have e0 : W (circ1 n a b c) x (n + 2) = (x a && x b) := by
    rw [W_gate_at _ hr 0 (by simp [circ1]) x (n + 2) (by omega), g0]
    simp [GateOp.eval]
  have e1 : W (circ1 n a b c) x (n + 3) = !(x a && x b) := by
    rw [W_gate_at _ hr 1 (by simp [circ1]) x (n + 3) (by omega), g1]
    simp [GateOp.eval, e0]
  have e2 : W (circ1 n a b c) x (n + 4) = (x b && x c) := by
    rw [W_gate_at _ hr 2 (by simp [circ1]) x (n + 4) (by omega), g2]
    simp [GateOp.eval]
  have e3 : W (circ1 n a b c) x (n + 5) = !(x b && x c) := by
    rw [W_gate_at _ hr 3 (by simp [circ1]) x (n + 5) (by omega), g3]
    simp [GateOp.eval, e2]
  rw [e1, e3]
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp_all

lemma circ2_eval (n : ℕ) (a b c : Fin n) (x : Fin n → Bool) (h1 : x a = true ∨ x b = true)
    (h2 : x b = true ∨ x c = true) (h3 : x a = true ∨ x c = true) :
    W (circ2 n a b c) x (n + 5) = xor (x a) (x b) ∧
      W (circ2 n a b c) x (n + 6) = xor (x b) (x c) := by
  have hr := circ2_reads n a b c
  have g0 : gateAt (circ2 n a b c) 0 = ⟨GateOp.and, [a.val, b.val]⟩ := rfl
  have g1 : gateAt (circ2 n a b c) 1 = ⟨GateOp.and, [n + 2, c.val]⟩ := rfl
  have g2 : gateAt (circ2 n a b c) 2 = ⟨GateOp.not, [n + 3]⟩ := rfl
  have g3 : gateAt (circ2 n a b c) 3 = ⟨GateOp.and, [n + 4, c.val]⟩ := rfl
  have g4 : gateAt (circ2 n a b c) 4 = ⟨GateOp.and, [n + 4, a.val]⟩ := rfl
  have e0 : W (circ2 n a b c) x (n + 2) = (x a && x b) := by
    rw [W_gate_at _ hr 0 (by simp [circ2]) x (n + 2) (by omega), g0]
    simp [GateOp.eval]
  have e1 : W (circ2 n a b c) x (n + 3) = (x a && x b && x c) := by
    rw [W_gate_at _ hr 1 (by simp [circ2]) x (n + 3) (by omega), g1]
    simp [GateOp.eval, e0]
  have e2 : W (circ2 n a b c) x (n + 4) = !(x a && x b && x c) := by
    rw [W_gate_at _ hr 2 (by simp [circ2]) x (n + 4) (by omega), g2]
    simp [GateOp.eval, e1]
  have e3 : W (circ2 n a b c) x (n + 5) = (!(x a && x b && x c) && x c) := by
    rw [W_gate_at _ hr 3 (by simp [circ2]) x (n + 5) (by omega), g3]
    simp [GateOp.eval, e2]
  have e4 : W (circ2 n a b c) x (n + 6) = (!(x a && x b && x c) && x a) := by
    rw [W_gate_at _ hr 4 (by simp [circ2]) x (n + 6) (by omega), g4]
    simp [GateOp.eval, e2]
  rw [e3, e4]
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp_all

end PEqualNP.Outside.L_lib_1188_aux

theorem PEqualNP.Outside.L_lib_1188 : ∀ n : Nat, ∀ (G : Finset (Fin n × Fin n)) (a b c : Fin n),
  (∀ e ∈ G, e.1 < e.2) → a ≠ b → b ≠ c → a ≠ c →
  let adjacent := fun u v : Fin n => (u,v) ∈ G ∨ (v,u) ∈ G
  adjacent a b → adjacent b c → ∀ s r : Nat,
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output = p.val ∧ C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1=true ∨ x e.2=true) →
        let w := C.wires (List.ofFn x ++ [false,true])
        w.getD p.val false = xor (x a) (x b) ∧ w.getD q.val false = xor (x b) (x c)) ↔
    (4 ≤ s ∧ 2 ≤ r) ∨ (adjacent a c ∧ 5 ≤ s ∧ 1 ≤ r) := by
  intro n G a b c hG hab hbc hac
  dsimp only
  intro hadjab hadjbc s r
  constructor
  · rintro ⟨C, p, q, hf, hr, -, hs, hnc, hPQ⟩
    have hp : p.val < n + 2 + C.gates.length := p.isLt
    have hq : q.val < n + 2 + C.gates.length := q.isLt
    have hsz : C.size = C.gates.length := rfl
    have hPQ' : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        PEqualNP.Outside.L_lib_1188_aux.W C x p.val = xor (x a) (x b) ∧
          PEqualNP.Outside.L_lib_1188_aux.W C x q.val = xor (x b) (x c) := hPQ
    have hA : PEqualNP.NotBracket.notCount C ≠ 0 := fun h =>
      PEqualNP.Outside.L_lib_1188_aux.lowA hG hab hbc hac C hf hr p.val q.val hp hPQ' h
    have hsearch := PEqualNP.Outside.L_lib_1188_aux.lowCD hG hab hbc hac C hf hr p.val q.val
      hp hq hPQ'
    have hle := PEqualNP.Outside.L_lib_1188_aux.nc_le_length C
    have hC4 : 4 ≤ C.gates.length := by
      by_contra hlt
      have h3 := PEqualNP.Outside.L_lib_1188_aux.search_mono (k' := 3) (r' := 3)
        (by omega) (by omega) hsearch
      rw [PEqualNP.Outside.L_lib_1188_aux.chk3] at h3
      cases h3
    by_cases h2 : 2 ≤ PEqualNP.NotBracket.notCount C
    · left
      constructor <;> omega
    · right
      refine ⟨?_, ?_, by omega⟩
      · by_contra hnac
        exact PEqualNP.Outside.L_lib_1188_aux.lowB hG hab hbc hac C hf hr p.val q.val hp hq
          hPQ' hnac (by omega)
      · by_contra h5
        have h4 := PEqualNP.Outside.L_lib_1188_aux.search_mono (k' := 4) (r' := 1)
          (by omega) (by omega) hsearch
        rw [PEqualNP.Outside.L_lib_1188_aux.chk4] at h4
        cases h4
  · have cab : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        x a = true ∨ x b = true := by
      intro x hx
      rcases hadjab with h | h
      · exact hx _ h
      · exact (hx _ h).symm
    have cbc : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        x b = true ∨ x c = true := by
      intro x hx
      rcases hadjbc with h | h
      · exact hx _ h
      · exact (hx _ h).symm
    rintro (⟨hs, hr⟩ | ⟨hac', hs, hr⟩)
    · refine ⟨PEqualNP.Outside.L_lib_1188_aux.circ1 n a b c,
        ⟨n + 3, by show n + 3 < n + 2 + 4; omega⟩, ⟨n + 5, by show n + 5 < n + 2 + 4; omega⟩,
        PEqualNP.Outside.L_lib_1188_aux.circ1_fan n a b c,
        PEqualNP.Outside.L_lib_1188_aux.circ1_reads n a b c, rfl,
        by show 4 ≤ s; omega,
        by rw [PEqualNP.Outside.L_lib_1188_aux.circ1_not]; omega, ?_⟩
      intro x hx
      exact PEqualNP.Outside.L_lib_1188_aux.circ1_eval n a b c x (cab x hx) (cbc x hx)
    · have cac : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
          x a = true ∨ x c = true := by
        intro x hx
        rcases hac' with h | h
        · exact hx _ h
        · exact (hx _ h).symm
      refine ⟨PEqualNP.Outside.L_lib_1188_aux.circ2 n a b c,
        ⟨n + 5, by show n + 5 < n + 2 + 5; omega⟩, ⟨n + 6, by show n + 6 < n + 2 + 5; omega⟩,
        PEqualNP.Outside.L_lib_1188_aux.circ2_fan n a b c,
        PEqualNP.Outside.L_lib_1188_aux.circ2_reads n a b c, rfl,
        by show 5 ≤ s; omega,
        by rw [PEqualNP.Outside.L_lib_1188_aux.circ2_not]; omega, ?_⟩
      intro x hx
      exact PEqualNP.Outside.L_lib_1188_aux.circ2_eval n a b c x (cab x hx) (cbc x hx) (cac x hx)
