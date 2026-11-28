import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49930_aux

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

/-! ## Five-point value vectors -/

def enc (b0 b1 b2 b3 b4 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0) +
    (if b4 then 16 else 0)

lemma enc_and (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) :
    enc (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) =
      enc a0 a1 a2 a3 a4 &&& enc b0 b1 b2 b3 b4 := by
  revert a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  decide +kernel

lemma enc_or (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) :
    enc (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) =
      enc a0 a1 a2 a3 a4 ||| enc b0 b1 b2 b3 b4 := by
  revert a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  decide +kernel

lemma enc_not (a0 a1 a2 a3 a4 : Bool) :
    enc (!a0) (!a1) (!a2) (!a3) (!a4) = enc a0 a1 a2 a3 a4 ^^^ 31 := by
  revert a0 a1 a2 a3 a4
  decide +kernel

lemma enc_lt (a0 a1 a2 a3 a4 : Bool) : enc a0 a1 a2 a3 a4 < 32 := by
  revert a0 a1 a2 a3 a4
  decide +kernel

def V (C : Circuit) {n : ℕ} (x0 x1 x2 x3 x4 : Fin n → Bool) (i : ℕ) : ℕ :=
  enc (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i) (W C x4 i)

lemma V_gate (C : Circuit) {n : ℕ} (hf : FanInTwo C) (hr : ReadsBack (n + 2) C) {j : ℕ}
    (hj : j < C.gates.length) (x0 x1 x2 x3 x4 : Fin n → Bool) (M : ℕ → Prop)
    (hM : ∀ i < n + 2 + j, M (V C x0 x1 x2 x3 x4 i)) :
    ((gateAt C j).op = GateOp.not →
      V C x0 x1 x2 x3 x4 (n + 2 + j) = 31 ∨
        ∃ u, M u ∧ u < 32 ∧ V C x0 x1 x2 x3 x4 (n + 2 + j) = u ^^^ 31) ∧
    ((gateAt C j).op ≠ GateOp.not →
      V C x0 x1 x2 x3 x4 (n + 2 + j) = 0 ∨ V C x0 x1 x2 x3 x4 (n + 2 + j) = 31 ∨
        ∃ u w, M u ∧ M w ∧ u < 32 ∧ w < 32 ∧
          (V C x0 x1 x2 x3 x4 (n + 2 + j) = u &&& w ∨
            V C x0 x1 x2 x3 x4 (n + 2 + j) = u ||| w)) := by
  have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C hj]; exact List.getElem_mem _
  have hfg := hf _ hg
  have hin : ∀ i ∈ (gateAt C j).inputs, i < n + 2 + j := hr j hj
  have hV : V C x0 x1 x2 x3 x4 (n + 2 + j) =
      enc ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x0)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x1)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x2)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x3)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x4))) := by
    simp only [V, W_gate C hr hj]
  rw [hV]
  generalize gateAt C j = g at hfg hin ⊢
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hfg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hVi : ∀ i ∈ ins, M (V C x0 x1 x2 x3 x4 i) := fun i hi => hM i (hin i hi)
  rcases ins with _ | ⟨i, _ | ⟨i', _ | ⟨i'', rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨fun h => (by cases h), fun _ => Or.inr (Or.inl rfl)⟩
    · exact ⟨fun h => (by cases h), fun _ => Or.inl rfl⟩
    · exact ⟨fun _ => Or.inl rfl, fun h => absurd rfl h⟩
  · have hi := hVi i (by simp)
    have hlt := enc_lt (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i) (W C x4 i)
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
    have hlt := enc_lt (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i) (W C x4 i)
    have hlt' := enc_lt (W C x0 i') (W C x1 i') (W C x2 i') (W C x3 i') (W C x4 i')
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

lemma nc_cons_not (l : List Gate) (g : Gate) (h : g.op = GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ + 1 := by
  simp [notCount, h]

lemma nc_cons_ne (l : List Gate) (g : Gate) (h : g.op ≠ GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ := by
  simp [notCount, h]

/-! ## Bounded search over sets of value vectors -/

def mem (S v : ℕ) : Bool := S.testBit v

def ins (S v : ℕ) : ℕ := S ||| 2 ^ v

lemma mem_ins (S v u : ℕ) : mem (ins S v) u = (mem S u || decide (v = u)) := by
  simp [mem, ins, Nat.testBit_two_pow]

def goal (S : ℕ) : Bool := mem S 4 && mem S 22 && mem S 29

/-- How many of the three target vectors are still absent from `S`. -/
def miss (S : ℕ) : ℕ := (!mem S 4).toNat + (!mem S 22).toNat + (!mem S 29).toNat

lemma miss_goal {S : ℕ} (h : goal S = true) : miss S = 0 := by
  simp only [goal, Bool.and_eq_true] at h
  simp [miss, h.1.1, h.1.2, h.2]

lemma miss_ins (S v : ℕ) : miss S ≤ miss (ins S v) + 1 := by
  simp only [miss, mem_ins]
  cases mem S 4 <;> cases mem S 22 <;> cases mem S 29 <;>
    by_cases h6 : v = 4 <;> by_cases h18 : v = 22 <;> by_cases h26 : v = 29 <;>
      simp_all

def okAO (S v : ℕ) : Bool :=
  v == 0 || v == 31 || (List.range 32).any (fun u => mem S u &&
    (List.range 32).any (fun w => mem S w && (u &&& w == v || u ||| w == v)))

def okN (S v : ℕ) : Bool :=
  v == 31 || (List.range 32).any (fun u => mem S u && u ^^^ 31 == v)

def search : ℕ → ℕ → ℕ → Bool
  | 0, _, S => goal S
  | k + 1, 0, S => goal S || (List.range 32).any (fun v =>
      !mem S v && decide (miss (ins S v) ≤ k) && okAO S v && search k 0 (ins S v))
  | k + 1, r + 1, S => goal S || (List.range 32).any (fun v =>
      !mem S v && decide (miss (ins S v) ≤ k) && ((okAO S v && search k (r + 1) (ins S v)) ||
        (okN S v && search k r (ins S v))))

lemma search_goal {k r S : ℕ} (h : goal S = true) : search k r S = true := by
  cases k with
  | zero => simpa [search] using h
  | succ k => cases r <;> simp [search, h]

lemma search_sz (k S : ℕ) : search (k + 1) 0 S = (goal S || (List.range 32).any (fun v =>
      !mem S v && decide (miss (ins S v) ≤ k) && okAO S v && search k 0 (ins S v))) := rfl

lemma search_ss (k r S : ℕ) : search (k + 1) (r + 1) S = (goal S || (List.range 32).any (fun v =>
      !mem S v && decide (miss (ins S v) ≤ k) && ((okAO S v && search k (r + 1) (ins S v)) ||
        (okN S v && search k r (ins S v))))) := rfl

lemma search_miss (k r S : ℕ) (h : search k r S = true) : miss S ≤ k := by
  cases k with
  | zero =>
    have hg : goal S = true := by simpa [search] using h
    rw [miss_goal hg]
  | succ k =>
    cases r with
    | zero =>
      rw [search_sz] at h
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨v, -, ⟨⟨-, hk⟩, -⟩, -⟩
      · rw [miss_goal h]; omega
      · have := miss_ins S v
        omega
    | succ r =>
      rw [search_ss] at h
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨v, -, ⟨-, hk⟩, -⟩
      · rw [miss_goal h]; omega
      · have := miss_ins S v
        omega

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
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | ⟨v, hv, ⟨⟨hm, hk⟩, ho⟩, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, ⟨⟨hm, by omega⟩, ho⟩, ih _ _ hs⟩
    | succ r =>
      rw [search_ss] at h ⊢
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | ⟨v, hv, ⟨hm, hk⟩, ⟨ho, hs⟩ | ⟨ho, hs⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, ⟨hm, by omega⟩, Or.inl ⟨ho, ih _ _ hs⟩⟩
      · exact Or.inr ⟨v, hv, ⟨hm, by omega⟩, Or.inr ⟨ho, ih _ _ hs⟩⟩

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
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | ⟨v, hv, ⟨⟨hm, hk⟩, ho⟩, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, ⟨hm, hk⟩, Or.inl ⟨ho, ih _ _ hs⟩⟩
    | succ r =>
      rw [search_ss] at h
      rw [search_ss]
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with h | ⟨v, hv, ⟨hm, hk⟩, ⟨ho, hs⟩ | ⟨ho, hs⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, ⟨hm, hk⟩, Or.inl ⟨ho, ih _ _ hs⟩⟩
      · exact Or.inr ⟨v, hv, ⟨hm, hk⟩, Or.inr ⟨ho, ih _ _ hs⟩⟩

lemma search_mono {k k' r r' S : ℕ} (hk : k ≤ k') (hr : r ≤ r') (h : search k r S = true) :
    search k' r' S = true := by
  have h1 : search k r' S = true := by
    induction hr with
    | refl => exact h
    | step _ ih => exact search_mono_r _ _ _ ih
  induction hk with
  | refl => exact h1
  | step _ ih => exact search_mono_k _ _ _ ih

lemma search_step_ao {k r S v : ℕ} (hv : v < 32) (hm : mem S v = false)
    (ho : okAO S v = true) (h : search k r (ins S v) = true) : search (k + 1) r S = true := by
  have hk := search_miss k r _ h
  cases r with
  | zero =>
    rw [search_sz, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨v, List.mem_range.2 hv, by simp [hm, ho, h, hk]⟩
  | succ r =>
    rw [search_ss, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨v, List.mem_range.2 hv, by simp [hm, ho, h, hk]⟩

lemma search_step_n {k r S v : ℕ} (hv : v < 32) (hm : mem S v = false)
    (ho : okN S v = true) (h : search k r (ins S v) = true) :
    search (k + 1) (r + 1) S = true := by
  have hk := search_miss k r _ h
  rw [search_ss, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨v, List.mem_range.2 hv, by simp [hm, ho, h, hk]⟩

lemma search_sound (C : Circuit) {n : ℕ} (hf : FanInTwo C) (hr : ReadsBack (n + 2) C)
    (x0 x1 x2 x3 x4 : Fin n → Bool) (p q s : ℕ) (hp : p < n + 2 + C.gates.length)
    (hq : q < n + 2 + C.gates.length) (hs : s < n + 2 + C.gates.length)
    (hP : V C x0 x1 x2 x3 x4 p = 4) (hQ : V C x0 x1 x2 x3 x4 q = 22)
    (hS' : V C x0 x1 x2 x3 x4 s = 29) :
    ∀ d j, j + d = C.gates.length → ∀ S,
      (∀ i < n + 2 + j, mem S (V C x0 x1 x2 x3 x4 i) = true) →
        search d (notCount ⟨C.gates.drop j, 0⟩) S = true := by
  intro d
  induction d with
  | zero =>
    intro j hj S hS
    have h6 := hS p (by omega)
    have h18 := hS q (by omega)
    have h26 := hS s (by omega)
    rw [hP] at h6
    rw [hQ] at h18
    rw [hS'] at h26
    exact search_goal (by simp [goal, h6, h18, h26])
  | succ d ih =>
    intro j hj S hS
    have hjl : j < C.gates.length := by omega
    have hdrop : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [gateAt_eq C hjl]
      exact List.drop_eq_getElem_cons hjl
    rw [hdrop]
    have hvlt : V C x0 x1 x2 x3 x4 (n + 2 + j) < 32 := enc_lt _ _ _ _ _
    have hgate := V_gate C hf hr hjl x0 x1 x2 x3 x4 (fun u => mem S u = true) hS
    by_cases hm : mem S (V C x0 x1 x2 x3 x4 (n + 2 + j)) = true
    · have h1 := ih (j + 1) (by omega) S (fun i hi => by
        rcases (show i < n + 2 + j ∨ i = n + 2 + j by omega) with h | h
        · exact hS i h
        · rw [h]; exact hm)
      by_cases hn : (gateAt C j).op = GateOp.not
      · rw [nc_cons_not _ _ hn]
        exact search_mono (Nat.le_succ d) (Nat.le_succ _) h1
      · rw [nc_cons_ne _ _ hn]
        exact search_mono (Nat.le_succ d) le_rfl h1
    · have hmS : mem S (V C x0 x1 x2 x3 x4 (n + 2 + j)) = false := by simpa using hm
      have h1 := ih (j + 1) (by omega) (ins S (V C x0 x1 x2 x3 x4 (n + 2 + j))) (fun i hi => by
        rw [mem_ins]
        rcases (show i < n + 2 + j ∨ i = n + 2 + j by omega) with h | h
        · simp [hS i h]
        · simp [h])
      by_cases hn : (gateAt C j).op = GateOp.not
      · rw [nc_cons_not _ _ hn]
        refine search_step_n hvlt hmS ?_ h1
        rcases hgate.1 hn with h | ⟨u, hu, hu32, h⟩
        · simp [okN, h]
        · simp only [okN, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
            beq_iff_eq]
          exact Or.inr ⟨u, hu32, hu, h.symm⟩
      · rw [nc_cons_ne _ _ hn]
        refine search_step_ao hvlt hmS ?_ h1
        rcases hgate.2 hn with h | h | ⟨u, w, hu, hw, hu32, hw32, h | h⟩
        · simp [okAO, h]
        · simp [okAO, h]
        · simp only [okAO, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
            beq_iff_eq]
          exact Or.inr ⟨u, hu32, hu, w, hw32, hw, Or.inl h.symm⟩
        · simp only [okAO, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
            beq_iff_eq]
          exact Or.inr ⟨u, hu32, hu, w, hw32, hw, Or.inr h.symm⟩

/-- No 5 gates with at most two NOTs reach all three targets from the chain inputs. -/
lemma chk : search 5 2 3506503681 = false := by decide +kernel

/-! ## The chain inputs -/

def xf (t : ℕ) : Fin 4 → Bool := fun i => decide (i.val < t)

lemma V_base (C : Circuit) (i : ℕ) (hi : i < 4 + 2) :
    mem 3506503681 (V C (xf 0) (xf 1) (xf 2) (xf 3) (xf 4) i) = true := by
  rcases (show i < 4 ∨ i = 4 ∨ i = 4 + 1 by omega) with h | h | h
  · obtain ⟨v, rfl⟩ : ∃ v : Fin 4, v.val = i := ⟨⟨i, h⟩, rfl⟩
    simp only [V, W_input]
    fin_cases v <;> decide
  · subst h
    simp only [V, W_n]
    decide
  · subst h
    simp only [V, W_n1]
    decide

lemma V_tgt (C : Circuit) (i m : ℕ)
    (h : ∀ t : Fin 5, W C (xf t.val) i = m.testBit t.val) :
    V C (xf 0) (xf 1) (xf 2) (xf 3) (xf 4) i =
      enc (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3) (m.testBit 4) := by
  have e0 : W C (xf 0) i = m.testBit 0 := h ⟨0, by decide⟩
  have e1 : W C (xf 1) i = m.testBit 1 := h ⟨1, by decide⟩
  have e2 : W C (xf 2) i = m.testBit 2 := h ⟨2, by decide⟩
  have e3 : W C (xf 3) i = m.testBit 3 := h ⟨3, by decide⟩
  have e4 : W C (xf 4) i = m.testBit 4 := h ⟨4, by decide⟩
  simp only [V, e0, e1, e2, e3, e4]

end PEqualNP.Outside.L_meta_49930_aux

theorem PEqualNP.Outside.L_meta_49930 :
¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (22 : Nat).testBit t.val ∧
    w.getD r.val false = (29 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, s, hf, hrb, hn, hsz, h⟩
  have hP : ∀ t : Fin 5, PEqualNP.Outside.L_meta_49930_aux.W D
      (PEqualNP.Outside.L_meta_49930_aux.xf t.val) p.val = (4 : ℕ).testBit t.val := by
    intro t
    obtain ⟨a, -, -⟩ := h t
    exact a
  have hQ : ∀ t : Fin 5, PEqualNP.Outside.L_meta_49930_aux.W D
      (PEqualNP.Outside.L_meta_49930_aux.xf t.val) q.val = (22 : ℕ).testBit t.val := by
    intro t
    obtain ⟨-, a, -⟩ := h t
    exact a
  have hS : ∀ t : Fin 5, PEqualNP.Outside.L_meta_49930_aux.W D
      (PEqualNP.Outside.L_meta_49930_aux.xf t.val) s.val = (29 : ℕ).testBit t.val := by
    intro t
    obtain ⟨-, -, a⟩ := h t
    exact a
  have h6 : PEqualNP.Outside.L_meta_49930_aux.V D (PEqualNP.Outside.L_meta_49930_aux.xf 0)
      (PEqualNP.Outside.L_meta_49930_aux.xf 1) (PEqualNP.Outside.L_meta_49930_aux.xf 2)
      (PEqualNP.Outside.L_meta_49930_aux.xf 3) (PEqualNP.Outside.L_meta_49930_aux.xf 4) p.val = 4 :=
    (PEqualNP.Outside.L_meta_49930_aux.V_tgt D p.val 4 hP).trans (by decide)
  have h18 : PEqualNP.Outside.L_meta_49930_aux.V D (PEqualNP.Outside.L_meta_49930_aux.xf 0)
      (PEqualNP.Outside.L_meta_49930_aux.xf 1) (PEqualNP.Outside.L_meta_49930_aux.xf 2)
      (PEqualNP.Outside.L_meta_49930_aux.xf 3) (PEqualNP.Outside.L_meta_49930_aux.xf 4) q.val = 22 :=
    (PEqualNP.Outside.L_meta_49930_aux.V_tgt D q.val 22 hQ).trans (by decide)
  have h26 : PEqualNP.Outside.L_meta_49930_aux.V D (PEqualNP.Outside.L_meta_49930_aux.xf 0)
      (PEqualNP.Outside.L_meta_49930_aux.xf 1) (PEqualNP.Outside.L_meta_49930_aux.xf 2)
      (PEqualNP.Outside.L_meta_49930_aux.xf 3) (PEqualNP.Outside.L_meta_49930_aux.xf 4) s.val = 29 :=
    (PEqualNP.Outside.L_meta_49930_aux.V_tgt D s.val 29 hS).trans (by decide)
  have hlen : D.size = D.gates.length := rfl
  have hp : p.val < 4 + 2 + D.gates.length := by have := p.isLt; omega
  have hq : q.val < 4 + 2 + D.gates.length := by have := q.isLt; omega
  have hs : s.val < 4 + 2 + D.gates.length := by have := s.isLt; omega
  have hsearch := PEqualNP.Outside.L_meta_49930_aux.search_sound D hf hrb _ _ _ _ _
    p.val q.val s.val hp hq hs h6 h18 h26 D.gates.length 0 (by simp) 3506503681
    (fun i hi => PEqualNP.Outside.L_meta_49930_aux.V_base D i hi)
  rw [List.drop_zero] at hsearch
  have h52 := PEqualNP.Outside.L_meta_49930_aux.search_mono (k' := 5) (r' := 2)
    (by omega) hn hsearch
  rw [PEqualNP.Outside.L_meta_49930_aux.chk] at h52
  cases h52
