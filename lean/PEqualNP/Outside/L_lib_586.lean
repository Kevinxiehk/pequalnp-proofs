import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_586_aux

open PEqualNP.CircuitLowerBounds

/-! ## Wires as a fold -/

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wires (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x = step (wires gs x) g := by
  simp [wires]

theorem wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih => rw [wires_snoc, step]; simp [ih, Nat.add_assoc]

theorem wire_before (gs : List Gate) (g : Gate) (x : List Bool) {i : ℕ}
    (h : i < x.length + gs.length) :
    (wires (gs ++ [g]) x).getD i false = (wires gs x).getD i false := by
  rw [wires_snoc, step]
  have h' : i < (wires gs x).length := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h']

theorem wire_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
  rw [wires_snoc, step, ← wires_length]
  simp [List.getD_eq_getElem?_getD]

theorem wire_outside (gs : List Gate) (x : List Bool) {i : ℕ}
    (h : x.length + gs.length ≤ i) : (wires gs x).getD i false = false := by
  have h' : (wires gs x).length ≤ i := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h']

theorem wires_prefix (dg ng : List Gate) (x : List Bool) {j : ℕ}
    (h : j < x.length + dg.length) :
    (wires (dg ++ ng) x).getD j false = (wires dg x).getD j false := by
  induction ng using List.reverseRecOn with
  | nil => simp
  | append_singleton ng g ih =>
    rw [← List.append_assoc, wire_before _ _ _ (by simp; omega), ih]

theorem getD_snoc_lt {α : Type} (l : List α) (a d : α) {m : ℕ} (h : m < l.length) :
    (l ++ [a]).getD m d = l.getD m d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) {m : ℕ} (h : l.length ≤ m) : l.getD m d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_ofFn {α : Type} {n : ℕ} (F : Fin n → α) (d : α) (m : ℕ) :
    (List.ofFn F).getD m d = if h : m < n then F ⟨m, h⟩ else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem len_one {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  match l, h with
  | [a], _ => exact ⟨a, rfl⟩

/-! ## Symbolic records -/

inductive SV
  | cst (b : Bool)
  | lv (j : ℕ)
  deriving DecidableEq

def SV.ev : SV → List Bool → Bool
  | .cst b, _ => b
  | .lv j, w => w.getD j false

def SV.isC : SV → Bool
  | .cst _ => true
  | .lv _ => false

theorem lv_ne_cst (j : ℕ) (b : Bool) : (SV.lv j = SV.cst b) ↔ False :=
  ⟨fun h => SV.noConfusion h, False.elim⟩

structure Rec where
  sv : SV
  A : Finset ℕ
  cost : Bool
  al : Bool

def dR : Rec := ⟨.cst false, ∅, false, false⟩

def stat (rs : List Rec) (i : ℕ) : SV := (rs.getD i dR).sv

def AA (rs : List Rec) (i : ℕ) : Finset ℕ := (rs.getD i dR).A

def lvs (rs : List Rec) (ins : List ℕ) : List ℕ :=
  ins.filterMap (fun i => match stat rs i with | .lv j => some j | .cst _ => none)

def cA (rs : List Rec) (ins : List ℕ) : Finset ℕ :=
  ((ins.filter (fun i => (stat rs i).isC)).toFinset).biUnion (AA rs)

def aoNew (op : GateOp) (z : Bool) (k : ℕ) (rs : List Rec) (dg : List Gate) (ins : List ℕ) :
    Rec × List Gate :=
  if ins.any (fun i => decide (stat rs i = .cst z)) then (⟨.cst z, cA rs ins, true, false⟩, [])
  else if (lvs rs ins).length = 0 then (⟨.cst (!z), cA rs ins, true, false⟩, [])
  else if (lvs rs ins).length = 1 then
    (⟨.lv ((lvs rs ins).headD 0), cA rs ins, false, true⟩, [])
  else (⟨.lv (k + dg.length), ∅, false, false⟩, [⟨op, lvs rs ins⟩])

def notNew (k : ℕ) (rs : List Rec) (dg : List Gate) (ins : List ℕ) : Rec × List Gate :=
  match ins with
  | [] => (⟨.cst true, ∅, false, false⟩, [])
  | a :: _ =>
    match stat rs a with
    | .cst b => (⟨.cst (!b), AA rs a, false, false⟩, [])
    | .lv j => (⟨.lv (k + dg.length), ∅, false, false⟩, [⟨.not, [j]⟩])

def newR (k : ℕ) (rs : List Rec) (dg : List Gate) (g : Gate) : Rec × List Gate :=
  match g.op with
  | .and => aoNew .and false k rs dg g.inputs
  | .or => aoNew .or true k rs dg g.inputs
  | .not => notNew k rs dg g.inputs
  | _ => (dR, [])

def stp (k : ℕ) (st : List Rec × List Gate) (g : Gate) : List Rec × List Gate :=
  (st.1 ++ [(newR k st.1 st.2 g).1], st.2 ++ (newR k st.1 st.2 g).2)

def run (k : ℕ) (init : List Rec) (gs : List Gate) : List Rec × List Gate :=
  gs.foldl (stp k) (init, [])

theorem run_snoc (k : ℕ) (init : List Rec) (gs : List Gate) (g : Gate) :
    run k init (gs ++ [g]) = stp k (run k init gs) g := by
  simp [run]

def opNot : GateOp → Bool
  | .and => false
  | .or => false
  | .not => true
  | .mod _ => false
  | .maj => false

def isNot (g : Gate) : Bool := opNot g.op

def nN (gs : List Gate) : ℕ := (gs.filter isNot).length

theorem nN_nil : nN [] = 0 := rfl
theorem nN_not (l : List ℕ) : nN [⟨.not, l⟩] = 1 := rfl
theorem nN_and (l : List ℕ) : nN [⟨.and, l⟩] = 0 := rfl
theorem nN_or (l : List ℕ) : nN [⟨.or, l⟩] = 0 := rfl

abbrev ok (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def operands (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def UU (rs : List Rec) : Finset ℕ :=
  ((Finset.range rs.length).filter (fun m => (rs.getD m dR).al = true)).biUnion (AA rs)

/-! ## Basic facts -/

theorem stat_snoc_lt (rs : List Rec) (r : Rec) {m : ℕ} (h : m < rs.length) :
    stat (rs ++ [r]) m = stat rs m := by
  unfold stat; rw [getD_snoc_lt _ _ _ h]

theorem stat_snoc_eq (rs : List Rec) (r : Rec) : stat (rs ++ [r]) rs.length = r.sv := by
  unfold stat; rw [getD_snoc_eq]

theorem stat_ge (rs : List Rec) {m : ℕ} (h : rs.length ≤ m) : stat rs m = .cst false := by
  unfold stat; rw [getD_ge _ _ h]; rfl

theorem AA_snoc_lt (rs : List Rec) (r : Rec) {m : ℕ} (h : m < rs.length) :
    AA (rs ++ [r]) m = AA rs m := by
  unfold AA; rw [getD_snoc_lt _ _ _ h]

theorem AA_snoc_eq (rs : List Rec) (r : Rec) : AA (rs ++ [r]) rs.length = r.A := by
  unfold AA; rw [getD_snoc_eq]

theorem AA_ge (rs : List Rec) {m : ℕ} (h : rs.length ≤ m) : AA rs m = ∅ := by
  unfold AA; rw [getD_ge _ _ h]; rfl

theorem and_eval (l : List Bool) : GateOp.eval .and l = if false ∈ l then false else !false := by
  show l.all id = _
  induction l with
  | nil => rfl
  | cons a t ih => cases a <;> simp [List.all_cons, ih]

theorem or_eval (l : List Bool) : GateOp.eval .or l = if true ∈ l then true else !true := by
  show l.any id = _
  induction l with
  | nil => rfl
  | cons a t ih => cases a <;> simp [List.any_cons, ih]

theorem lvs_bound (rs : List Rec) (B : ℕ) (hb : ∀ m j, stat rs m = .lv j → j < B)
    (ins : List ℕ) : ∀ j ∈ lvs rs ins, j < B := by
  intro j hj
  simp only [lvs, List.mem_filterMap] at hj
  obtain ⟨i, _, hi⟩ := hj
  revert hi
  cases h : stat rs i with
  | cst b => simp
  | lv j' => simp only [Option.some.injEq]; intro e; subst e; exact hb i _ h

theorem len_split (rs : List Rec) (ins : List ℕ) :
    (ins.filter (fun i => (stat rs i).isC)).length + (lvs rs ins).length = ins.length := by
  induction ins with
  | nil => simp [lvs]
  | cons a t ih =>
    cases h : stat rs a with
    | cst b =>
      have e1 : (a :: t).filter (fun i => (stat rs i).isC) =
          a :: t.filter (fun i => (stat rs i).isC) := by simp [List.filter_cons, h, SV.isC]
      have e2 : lvs rs (a :: t) = lvs rs t := by simp [lvs, h]
      rw [e1, e2, List.length_cons, List.length_cons]; omega
    | lv j =>
      have e1 : (a :: t).filter (fun i => (stat rs i).isC) =
          t.filter (fun i => (stat rs i).isC) := by simp [List.filter_cons, h, SV.isC]
      have e2 : lvs rs (a :: t) = j :: lvs rs t := by simp [lvs, h]
      rw [e1, e2, List.length_cons, List.length_cons]; omega

theorem mem_ev (rs : List Rec) (w : List Bool) (z : Bool) (ins : List ℕ) :
    z ∈ ins.map (fun i => (stat rs i).ev w) ↔
      (∃ i ∈ ins, stat rs i = .cst z) ∨ z ∈ (lvs rs ins).map (fun j => w.getD j false) := by
  induction ins with
  | nil => simp [lvs]
  | cons a t ih =>
    have e1 : (a :: t).map (fun i => (stat rs i).ev w) =
        (stat rs a).ev w :: t.map (fun i => (stat rs i).ev w) := rfl
    have e3 : (∃ i ∈ a :: t, stat rs i = .cst z) ↔
        stat rs a = .cst z ∨ ∃ i ∈ t, stat rs i = .cst z := by
      constructor
      · rintro ⟨i, hi, hs⟩
        rcases List.mem_cons.1 hi with rfl | hi
        · exact Or.inl hs
        · exact Or.inr ⟨i, hi, hs⟩
      · rintro (hs | ⟨i, hi, hs⟩)
        · exact ⟨a, by simp, hs⟩
        · exact ⟨i, List.mem_cons_of_mem _ hi, hs⟩
    rw [e1, List.mem_cons, ih, e3]
    cases h : stat rs a with
    | cst b =>
      have e2 : lvs rs (a :: t) = lvs rs t := by simp [lvs, h]
      rw [e2]
      simp only [SV.ev, SV.cst.injEq]
      cases b <;> cases z <;> simp
    | lv j =>
      have e2 : lvs rs (a :: t) = j :: lvs rs t := by simp [lvs, h]
      rw [e2]
      simp only [SV.ev, List.map_cons, List.mem_cons, lv_ne_cst, false_or]
      exact or_left_comm

theorem ev_ext (s : SV) (dg ng : List Gate) (y : List Bool)
    (hs : ∀ j, s = .lv j → j < y.length + dg.length) :
    s.ev (wires (dg ++ ng) y) = s.ev (wires dg y) := by
  cases s with
  | cst b => rfl
  | lv j => exact wires_prefix dg ng y (hs j rfl)

/-! ## The new record: bounds -/

theorem aoNew_bound (op : GateOp) (z : Bool) (k : ℕ) (rs : List Rec) (dg : List Gate)
    (ins : List ℕ) (hb : ∀ m j, stat rs m = .lv j → j < k + dg.length) :
    ∀ j, (aoNew op z k rs dg ins).1.sv = .lv j →
      j < k + (dg ++ (aoNew op z k rs dg ins).2).length := by
  intro j hj
  unfold aoNew at hj ⊢
  by_cases h1 : (ins.any fun i => decide (stat rs i = SV.cst z)) = true
  · rw [if_pos h1] at hj; simp at hj
  · rw [if_neg h1] at hj ⊢
    by_cases h2 : (lvs rs ins).length = 0
    · rw [if_pos h2] at hj; simp at hj
    · rw [if_neg h2] at hj ⊢
      by_cases h3 : (lvs rs ins).length = 1
      · rw [if_pos h3] at hj ⊢
        obtain ⟨a, ha⟩ := len_one h3
        simp only [ha, List.headD_cons, SV.lv.injEq] at hj
        subst hj
        have := lvs_bound rs _ hb ins a (by rw [ha]; simp)
        simp; omega
      · rw [if_neg h3] at hj ⊢
        simp only [SV.lv.injEq] at hj
        subst hj; simp

theorem notNew_bound (k : ℕ) (rs : List Rec) (dg : List Gate) (ins : List ℕ) :
    ∀ j, (notNew k rs dg ins).1.sv = .lv j →
      j < k + (dg ++ (notNew k rs dg ins).2).length := by
  intro j hj
  rcases ins with _ | ⟨a, t⟩
  · simp [notNew] at hj
  · cases h : stat rs a with
    | cst b => simp [notNew, h] at hj
    | lv j' => simp [notNew, h] at hj ⊢; omega

theorem newR_bound (k : ℕ) (rs : List Rec) (dg : List Gate) (g : Gate)
    (hb : ∀ m j, stat rs m = .lv j → j < k + dg.length) :
    ∀ j, (newR k rs dg g).1.sv = .lv j → j < k + (dg ++ (newR k rs dg g).2).length := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and => exact aoNew_bound _ _ _ _ _ _ hb
  | or => exact aoNew_bound _ _ _ _ _ _ hb
  | not => exact notNew_bound _ _ _ _
  | mod m => intro j hj; simp [newR, dR] at hj
  | maj => intro j hj; simp [newR, dR] at hj

/-! ## The new record: values -/

theorem aoNew_ev (op : GateOp) (z : Bool)
    (hop : ∀ l : List Bool, op.eval l = if z ∈ l then z else !z)
    (k : ℕ) (rs : List Rec) (dg : List Gate) (ins : List ℕ) (y : List Bool) (hy : y.length = k)
    (hb : ∀ m j, stat rs m = .lv j → j < k + dg.length) :
    (aoNew op z k rs dg ins).1.sv.ev (wires (dg ++ (aoNew op z k rs dg ins).2) y) =
      op.eval (ins.map fun i => (stat rs i).ev (wires dg y)) := by
  have hm := mem_ev rs (wires dg y) z ins
  rw [hop]
  unfold aoNew
  by_cases h1 : (ins.any fun i => decide (stat rs i = SV.cst z)) = true
  · rw [if_pos h1]
    have hz : z ∈ ins.map (fun i => (stat rs i).ev (wires dg y)) := by
      rw [hm]; left; simpa using h1
    rw [if_pos hz]; rfl
  · rw [if_neg h1]
    have h1' : ¬ ∃ i ∈ ins, stat rs i = .cst z := by simpa using h1
    by_cases h2 : (lvs rs ins).length = 0
    · rw [if_pos h2]
      have hz : z ∉ ins.map (fun i => (stat rs i).ev (wires dg y)) := by
        rw [hm, List.length_eq_zero_iff.1 h2]; simpa using h1'
      rw [if_neg hz]; rfl
    · rw [if_neg h2]
      by_cases h3 : (lvs rs ins).length = 1
      · rw [if_pos h3]
        obtain ⟨j, hj⟩ := len_one h3
        have hiff : z ∈ ins.map (fun i => (stat rs i).ev (wires dg y)) ↔
            z = (wires dg y).getD j false := by
          rw [hm, hj]
          simp only [List.map_cons, List.map_nil, List.mem_singleton]
          exact ⟨fun h => h.resolve_left h1', Or.inr⟩
        show (wires (dg ++ []) y).getD ((lvs rs ins).headD 0) false = _
        rw [hj, List.append_nil, List.headD_cons]
        by_cases hz : z ∈ ins.map (fun i => (stat rs i).ev (wires dg y))
        · rw [if_pos hz]; exact (hiff.1 hz).symm
        · rw [if_neg hz]
          have : ¬ z = (wires dg y).getD j false := fun h => hz (hiff.2 h)
          revert this
          cases (wires dg y).getD j false <;> cases z <;> simp
      · rw [if_neg h3]
        have hiff : z ∈ ins.map (fun i => (stat rs i).ev (wires dg y)) ↔
            z ∈ (lvs rs ins).map (fun j => (wires dg y).getD j false) := by
          rw [hm]
          exact ⟨fun h => h.resolve_left h1', Or.inr⟩
        show (wires (dg ++ [⟨op, lvs rs ins⟩]) y).getD (k + dg.length) false = _
        rw [← hy, wire_last]
        simp only []
        rw [hop]
        by_cases hz : z ∈ (lvs rs ins).map (fun j => (wires dg y).getD j false)
        · rw [if_pos hz, if_pos (hiff.2 hz)]
        · rw [if_neg hz, if_neg (fun h => hz (hiff.1 h))]

theorem notNew_ev (k : ℕ) (rs : List Rec) (dg : List Gate) (ins : List ℕ) (y : List Bool)
    (hy : y.length = k) :
    (notNew k rs dg ins).1.sv.ev (wires (dg ++ (notNew k rs dg ins).2) y) =
      GateOp.not.eval (ins.map fun i => (stat rs i).ev (wires dg y)) := by
  rcases ins with _ | ⟨a, t⟩
  · rfl
  · cases h : stat rs a with
    | cst b => simp [notNew, h, SV.ev, GateOp.eval]
    | lv j =>
      simp only [notNew, h]
      show (wires (dg ++ [⟨.not, [j]⟩]) y).getD (k + dg.length) false = _
      rw [← hy, wire_last]
      simp [GateOp.eval, h, SV.ev]

theorem newR_ev (k : ℕ) (rs : List Rec) (dg : List Gate) (g : Gate) (hg : ok g)
    (y : List Bool) (hy : y.length = k)
    (hb : ∀ m j, stat rs m = .lv j → j < k + dg.length) :
    (newR k rs dg g).1.sv.ev (wires (dg ++ (newR k rs dg g).2) y) =
      g.op.eval (g.inputs.map fun i => (stat rs i).ev (wires dg y)) := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and => exact aoNew_ev .and false and_eval k rs dg ins y hy hb
  | or => exact aoNew_ev .or true or_eval k rs dg ins y hy hb
  | not => exact notNew_ev k rs dg ins y hy
  | mod m => exact absurd hg.1 (by simp)
  | maj => exact absurd hg.1 (by simp)

/-! ## The new record: emitted gates and counts -/

theorem newR_fan (k : ℕ) (rs : List Rec) (dg : List Gate) (g : Gate) (hg : ok g) :
    ∀ g' ∈ (newR k rs dg g).2, ok g' := by
  have hlen := len_split rs g.inputs
  rcases g with ⟨op, ins⟩
  obtain ⟨_, hl⟩ := hg
  simp only at hl hlen
  cases op with
  | and =>
    intro g' hg'
    simp only [newR, aoNew] at hg'
    split_ifs at hg' <;> simp at hg'
    subst hg'; exact ⟨by simp, by simp; omega⟩
  | or =>
    intro g' hg'
    simp only [newR, aoNew] at hg'
    split_ifs at hg' <;> simp at hg'
    subst hg'; exact ⟨by simp, by simp; omega⟩
  | not =>
    intro g' hg'
    rcases ins with _ | ⟨a, t⟩
    · simp [newR, notNew] at hg'
    · cases h : stat rs a with
      | cst b => simp [newR, notNew, h] at hg'
      | lv j => simp [newR, notNew, h] at hg'; subst hg'; exact ⟨by simp, by simp⟩
  | mod m => intro g' hg'; simp [newR] at hg'
  | maj => intro g' hg'; simp [newR] at hg'

theorem aoNew_count (op : GateOp) (z : Bool) (k : ℕ) (rs : List Rec) (dg : List Gate)
    (ins : List ℕ) (hop : nN [⟨op, lvs rs ins⟩] = 0) (hop2 : nN [⟨op, ins⟩] = 0) :
    (aoNew op z k rs dg ins).2.length + (if (aoNew op z k rs dg ins).1.cost then 1 else 0) +
        (if (aoNew op z k rs dg ins).1.al then 1 else 0) + nN [⟨op, ins⟩] ≤
        1 + nN (aoNew op z k rs dg ins).2 ∧
      nN (aoNew op z k rs dg ins).2 ≤ nN [⟨op, ins⟩] := by
  rw [hop2]
  unfold aoNew
  by_cases h1 : (ins.any fun i => decide (stat rs i = SV.cst z)) = true
  · rw [if_pos h1]; simp [nN_nil]
  · rw [if_neg h1]
    by_cases h2 : (lvs rs ins).length = 0
    · rw [if_pos h2]; simp [nN_nil]
    · rw [if_neg h2]
      by_cases h3 : (lvs rs ins).length = 1
      · rw [if_pos h3]; simp [nN_nil]
      · rw [if_neg h3]; simp [hop]

theorem newR_count (k : ℕ) (rs : List Rec) (dg : List Gate) (g : Gate) (hg : ok g) :
    (newR k rs dg g).2.length + (if (newR k rs dg g).1.cost then 1 else 0) +
        (if (newR k rs dg g).1.al then 1 else 0) + nN [g] ≤ 1 + nN (newR k rs dg g).2 ∧
      nN (newR k rs dg g).2 ≤ nN [g] := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and => exact aoNew_count _ _ _ _ _ _ (nN_and _) (nN_and _)
  | or => exact aoNew_count _ _ _ _ _ _ (nN_or _) (nN_or _)
  | not =>
    rcases ins with _ | ⟨a, t⟩
    · simp [newR, notNew, nN_nil, nN_not]
    · cases h : stat rs a with
      | cst b => simp [newR, notNew, h, nN_nil, nN_not]
      | lv j => simp [newR, notNew, h, nN_nil, nN_not]
  | mod m => exact absurd hg.1 (by simp)
  | maj => exact absurd hg.1 (by simp)

/-! ## The new record: accounting sets -/

theorem cA_sub (rs : List Rec) (ins : List ℕ) :
    cA rs ins ⊆ (((ins.filter (fun i => (stat rs i).isC)).toFinset).filter
      (fun a => a < rs.length)).biUnion (AA rs) := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
  refine Finset.mem_biUnion.2 ⟨i, Finset.mem_filter.2 ⟨hi, ?_⟩, hxi⟩
  by_contra hc
  rw [AA_ge rs (by omega)] at hxi
  simp at hxi

theorem cA_card (rs : List Rec) (ins : List ℕ) :
    (((ins.filter (fun i => (stat rs i).isC)).toFinset).filter
      (fun a => a < rs.length)).card ≤ (ins.filter (fun i => (stat rs i).isC)).length :=
  (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)

theorem aoNew_A (op : GateOp) (z : Bool) (k : ℕ) (rs : List Rec) (dg : List Gate)
    (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ P L : Finset ℕ, (∀ a ∈ P, a < rs.length) ∧
      (aoNew op z k rs dg ins).1.A ⊆ L ∪ P.biUnion (AA rs) ∧
      L.card + P.card ≤ 1 + (if (aoNew op z k rs dg ins).1.cost then 1 else 0) := by
  have hlen := len_split rs ins
  have hP : ∀ a ∈ (((ins.filter (fun i => (stat rs i).isC)).toFinset).filter
      (fun a => a < rs.length)), a < rs.length := fun a ha => (Finset.mem_filter.1 ha).2
  have hc := cA_card rs ins
  have hs : cA rs ins ⊆ ∅ ∪ (((ins.filter (fun i => (stat rs i).isC)).toFinset).filter
      (fun a => a < rs.length)).biUnion (AA rs) := by
    rw [Finset.empty_union]; exact cA_sub rs ins
  unfold aoNew
  by_cases h1 : (ins.any fun i => decide (stat rs i = SV.cst z)) = true
  · rw [if_pos h1]
    exact ⟨_, ∅, hP, hs, by rw [Finset.card_empty, zero_add]; show _ ≤ 1 + 1; omega⟩
  · rw [if_neg h1]
    by_cases h2 : (lvs rs ins).length = 0
    · rw [if_pos h2]
      exact ⟨_, ∅, hP, hs, by rw [Finset.card_empty, zero_add]; show _ ≤ 1 + 1; omega⟩
    · rw [if_neg h2]
      by_cases h3 : (lvs rs ins).length = 1
      · rw [if_pos h3]
        exact ⟨_, ∅, hP, hs, by rw [Finset.card_empty, zero_add]; show _ ≤ 1 + 0; omega⟩
      · rw [if_neg h3]
        exact ⟨∅, ∅, by simp, by simp, by simp⟩

theorem newR_A (k : ℕ) (rs : List Rec) (dg : List Gate) (g : Gate) (hg : ok g) :
    ∃ P L : Finset ℕ, (∀ a ∈ P, a < rs.length) ∧
      (newR k rs dg g).1.A ⊆ L ∪ P.biUnion (AA rs) ∧
      L.card + P.card ≤ 1 + (if (newR k rs dg g).1.cost then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨_, hl⟩ := hg
  simp only at hl
  cases op with
  | and => exact aoNew_A _ _ _ _ _ _ hl
  | or => exact aoNew_A _ _ _ _ _ _ hl
  | not =>
    rcases ins with _ | ⟨a, t⟩
    · exact ⟨∅, ∅, by simp, by simp [newR, notNew], by simp⟩
    · cases h : stat rs a with
      | cst b =>
        simp only [newR, notNew, h]
        refine ⟨({a} : Finset ℕ).filter (fun a => a < rs.length), ∅, fun x hx =>
          (Finset.mem_filter.1 hx).2, ?_, ?_⟩
        · intro x hx
          by_cases ha : a < rs.length
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, by simp [ha], hx⟩)
          · rw [AA_ge rs (by omega)] at hx; simp at hx
        · simp only [Finset.card_empty, zero_add]
          exact (Finset.card_filter_le _ _).trans (by simp)
      | lv j =>
        simp only [newR, notNew, h]
        exact ⟨∅, ∅, by simp, by simp, by simp⟩
  | mod m => exact ⟨∅, ∅, by simp, by simp [newR, dR], by simp⟩
  | maj => exact ⟨∅, ∅, by simp, by simp [newR, dR], by simp⟩

theorem newR_ops (k : ℕ) (rs : List Rec) (dg : List Gate) (g : Gate) (hg : ok g) :
    ∀ a ∈ operands g, (stat rs a).isC = true →
      ((newR k rs dg g).1.sv.isC = true ∨ (newR k rs dg g).1.al = true) ∧
        AA rs a ⊆ (newR k rs dg g).1.A := by
  have hlen := len_split rs g.inputs
  rcases g with ⟨op, ins⟩
  obtain ⟨_, hl⟩ := hg
  simp only at hl hlen
  have hsub : ∀ a ∈ ins, (stat rs a).isC = true → AA rs a ⊆ cA rs ins := by
    intro a ha hc x hx
    exact Finset.mem_biUnion.2 ⟨a, by simp [ha, hc], hx⟩
  cases op with
  | and =>
    intro a ha hc
    simp only [operands] at ha
    simp only [newR, aoNew]
    split_ifs with h1 h2 h3
    · exact ⟨by simp [SV.isC], hsub a ha hc⟩
    · exact ⟨by simp [SV.isC], hsub a ha hc⟩
    · exact ⟨by simp, hsub a ha hc⟩
    · exfalso
      have : (ins.filter (fun i => (stat rs i).isC)).length = 0 := by omega
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at this
      exact this a ha hc
  | or =>
    intro a ha hc
    simp only [operands] at ha
    simp only [newR, aoNew]
    split_ifs with h1 h2 h3
    · exact ⟨by simp [SV.isC], hsub a ha hc⟩
    · exact ⟨by simp [SV.isC], hsub a ha hc⟩
    · exact ⟨by simp, hsub a ha hc⟩
    · exfalso
      have : (ins.filter (fun i => (stat rs i).isC)).length = 0 := by omega
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at this
      exact this a ha hc
  | not =>
    intro a' ha hc
    rcases ins with _ | ⟨a, t⟩
    · simp [operands] at ha
    · simp [operands] at ha
      subst ha
      cases h : stat rs a' with
      | cst b => simp only [newR, notNew, h]; exact ⟨by simp [SV.isC], le_refl _⟩
      | lv j => rw [h] at hc; simp [SV.isC] at hc
  | mod m => exact absurd ‹_ ∨ _› (by simp)
  | maj => exact absurd ‹_ ∨ _› (by simp)

theorem eval_congr (g : Gate) (hg : ok g) (f f' : ℕ → Bool)
    (h : ∀ a ∈ operands g, f a = f' a) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, _⟩ := hg
  simp only at hop
  rcases hop with hop | hop | hop
  · subst hop
    rw [List.map_congr_left (fun a ha => h a (by simpa [operands] using ha))]
  · subst hop
    rw [List.map_congr_left (fun a ha => h a (by simpa [operands] using ha))]
  · subst hop
    rcases ins with _ | ⟨a, t⟩
    · rfl
    · have := h a (by simp [operands])
      simp [GateOp.eval, this]

/-! ## Invariants of the run -/

theorem inv_len (k : ℕ) (I : List Rec) (gs : List Gate) :
    (run k I gs).1.length = I.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [stp, ih, Nat.add_assoc]

theorem inv_bound (k : ℕ) (I : List Rec) (hI : ∀ m j, stat I m = .lv j → j < k)
    (gs : List Gate) :
    ∀ m j, stat (run k I gs).1 m = .lv j → j < k + (run k I gs).2.length := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hI
  | append_singleton gs g ih =>
    rw [run_snoc]
    generalize run k I gs = st at ih ⊢
    obtain ⟨R, G⟩ := st
    show ∀ m j, stat (R ++ [(newR k R G g).1]) m = .lv j → j < k + (G ++ (newR k R G g).2).length
    dsimp only at ih
    intro m j hm
    by_cases hlt : m < R.length
    · rw [stat_snoc_lt _ _ hlt] at hm
      have := ih m j hm; simp; omega
    · by_cases heq : m = R.length
      · subst heq; rw [stat_snoc_eq] at hm
        exact newR_bound k R G g ih j hm
      · rw [stat_ge _ (by simp; omega)] at hm
        exact absurd hm.symm (by simp [lv_ne_cst])

theorem inv_ev (k : ℕ) (I : List Rec) (hI : ∀ m j, stat I m = .lv j → j < k) (y x : List Bool)
    (hy : y.length = k) (hx : x.length = I.length)
    (hIx : ∀ m, (stat I m).ev y = x.getD m false) (gs : List Gate) (hok : ∀ g ∈ gs, ok g) :
    ∀ m, (stat (run k I gs).1 m).ev (wires (run k I gs).2 y) = (wires gs x).getD m false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run, wires] using hIx
  | append_singleton gs g ih =>
    have hok' : ∀ g ∈ gs, ok g := fun g' hg' => hok g' (by simp [hg'])
    have hg : ok g := hok g (by simp)
    have ih := ih hok'
    have hb := inv_bound k I hI gs
    have hlen := inv_len k I gs
    rw [run_snoc]
    generalize run k I gs = st at ih hb hlen ⊢
    obtain ⟨R, G⟩ := st
    show ∀ m, (stat (R ++ [(newR k R G g).1]) m).ev (wires (G ++ (newR k R G g).2) y) =
      (wires (gs ++ [g]) x).getD m false
    dsimp only at ih hb hlen
    intro m
    by_cases hlt : m < R.length
    · rw [stat_snoc_lt _ _ hlt, ev_ext _ _ _ _ (fun j hj => by have := hb m j hj; omega), ih m,
        wire_before _ _ _ (by omega)]
    · by_cases heq : m = R.length
      · subst heq
        rw [stat_snoc_eq, newR_ev k R G g hg y hy hb, hlen, ← hx, wire_last]
        congr 1
        apply List.map_congr_left
        intro i _
        exact ih i
      · rw [stat_ge _ (by simp; omega), wire_outside _ _ (by simp; omega)]; rfl

theorem inv_fan (k : ℕ) (I : List Rec) (gs : List Gate) (hok : ∀ g ∈ gs, ok g) :
    ∀ g ∈ (run k I gs).2, ok g := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    have hok' : ∀ g ∈ gs, ok g := fun g' hg' => hok g' (by simp [hg'])
    have hg : ok g := hok g (by simp)
    have ih := ih hok'
    rw [run_snoc]
    generalize run k I gs = st at ih ⊢
    obtain ⟨R, G⟩ := st
    show ∀ g' ∈ G ++ (newR k R G g).2, ok g'
    dsimp only at ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact ih g' h
    · exact newR_fan k R G g hg g' h

theorem inv_count (k : ℕ) (I : List Rec) (hI : ∀ r ∈ I, r.cost = false ∧ r.al = false)
    (gs : List Gate) (hok : ∀ g ∈ gs, ok g) :
    (run k I gs).2.length + ((run k I gs).1.filter (fun r => r.cost)).length +
        ((run k I gs).1.filter (fun r => r.al)).length + nN gs ≤
        gs.length + nN (run k I gs).2 ∧ nN (run k I gs).2 ≤ nN gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    have h1 : I.filter (fun r => r.cost) = [] :=
      List.filter_eq_nil_iff.2 (fun r hr => by simp [(hI r hr).1])
    have h2 : I.filter (fun r => r.al) = [] :=
      List.filter_eq_nil_iff.2 (fun r hr => by simp [(hI r hr).2])
    simp [run, h1, h2, nN]
  | append_singleton gs g ih =>
    have hok' : ∀ g ∈ gs, ok g := fun g' hg' => hok g' (by simp [hg'])
    have hg : ok g := hok g (by simp)
    have ih := ih hok'
    rw [run_snoc]
    generalize run k I gs = st at ih ⊢
    obtain ⟨R, G⟩ := st
    dsimp only at ih
    show (G ++ (newR k R G g).2).length + ((R ++ [(newR k R G g).1]).filter (fun r => r.cost)).length +
        ((R ++ [(newR k R G g).1]).filter (fun r => r.al)).length + nN (gs ++ [g]) ≤
        (gs ++ [g]).length + nN (G ++ (newR k R G g).2) ∧ nN (G ++ (newR k R G g).2) ≤ nN (gs ++ [g])
    have hc := newR_count k R G g hg
    have e1 : ∀ l1 l2 : List Gate, nN (l1 ++ l2) = nN l1 + nN l2 := by
      intro l1 l2; simp [nN, List.filter_append]
    rw [e1, e1]
    simp only [List.length_append, List.filter_append, List.length_singleton]
    have e2 : ∀ (p : Rec → Bool) (r : Rec), ([r].filter p).length = if p r then 1 else 0 := by
      intro p r; by_cases h : p r <;> simp [h]
    rw [e2, e2]
    omega

theorem inv_A (k : ℕ) (I : List Rec)
    (hI : ∀ m < I.length, ∃ P L : Finset ℕ, (∀ a ∈ P, a < m) ∧ AA I m ⊆ L ∪ P.biUnion (AA I) ∧
      L.card + P.card ≤ 1 + (if (I.getD m dR).cost then 1 else 0))
    (gs : List Gate) (hok : ∀ g ∈ gs, ok g) :
    ∀ m < (run k I gs).1.length, ∃ P L : Finset ℕ, (∀ a ∈ P, a < m) ∧
      AA (run k I gs).1 m ⊆ L ∪ P.biUnion (AA (run k I gs).1) ∧
      L.card + P.card ≤ 1 + (if ((run k I gs).1.getD m dR).cost then 1 else 0) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hI
  | append_singleton gs g ih =>
    have hok' : ∀ g ∈ gs, ok g := fun g' hg' => hok g' (by simp [hg'])
    have hg : ok g := hok g (by simp)
    have ih := ih hok'
    rw [run_snoc]
    generalize run k I gs = st at ih ⊢
    obtain ⟨R, G⟩ := st
    dsimp only at ih
    show ∀ m < (R ++ [(newR k R G g).1]).length, ∃ P L : Finset ℕ, (∀ a ∈ P, a < m) ∧
      AA (R ++ [(newR k R G g).1]) m ⊆ L ∪ P.biUnion (AA (R ++ [(newR k R G g).1])) ∧
      L.card + P.card ≤ 1 + (if ((R ++ [(newR k R G g).1]).getD m dR).cost then 1 else 0)
    intro m hm
    simp only [List.length_append, List.length_singleton] at hm
    by_cases hlt : m < R.length
    · obtain ⟨P, L, hP, hA, hc⟩ := ih m hlt
      refine ⟨P, L, hP, ?_, ?_⟩
      · rw [AA_snoc_lt _ _ hlt]
        have : P.biUnion (AA (R ++ [(newR k R G g).1])) = P.biUnion (AA R) := by
          apply Finset.biUnion_congr rfl
          intro a ha; exact AA_snoc_lt _ _ (by have := hP a ha; omega)
        rw [this]; exact hA
      · rw [getD_snoc_lt _ _ _ hlt]; exact hc
    · have heq : m = R.length := by omega
      subst heq
      obtain ⟨P, L, hP, hA, hc⟩ := newR_A k R G g hg
      refine ⟨P, L, hP, ?_, ?_⟩
      · rw [AA_snoc_eq]
        have : P.biUnion (AA (R ++ [(newR k R G g).1])) = P.biUnion (AA R) := by
          apply Finset.biUnion_congr rfl
          intro a ha; exact AA_snoc_lt _ _ (hP a ha)
        rw [this]; exact hA
      · rw [getD_snoc_eq]; exact hc

theorem UU_mono (rs : List Rec) (r : Rec) : UU rs ⊆ UU (rs ++ [r]) := by
  intro x hx
  obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
  have hlt := Finset.mem_range.1 hm1
  refine Finset.mem_biUnion.2 ⟨m, Finset.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
  · simp; omega
  · rw [getD_snoc_lt _ _ _ hlt]; exact hm2
  · rw [AA_snoc_lt _ _ hlt]; exact hxm

theorem UU_new (rs : List Rec) (r : Rec) (h : r.al = true) : r.A ⊆ UU (rs ++ [r]) := by
  intro x hx
  refine Finset.mem_biUnion.2 ⟨rs.length, Finset.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
  · simp
  · rw [getD_snoc_eq]; exact h
  · rw [AA_snoc_eq]; exact hx

theorem inv_indep (k : ℕ) (I : List Rec) (i : ℕ) (hIi : (stat I i).isC = true ∧ i ∈ AA I i)
    (x x' : List Bool) (hx : x.length = I.length) (hx' : x'.length = I.length)
    (hxx : ∀ m, m ≠ i → x.getD m false = x'.getD m false)
    (gs : List Gate) (hok : ∀ g ∈ gs, ok g) :
    ∀ m, i ∉ UU (run k I gs).1 → ((stat (run k I gs).1 m).isC = true →
      i ∉ AA (run k I gs).1 m) → (wires gs x).getD m false = (wires gs x').getD m false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro m _ hm
    by_cases hmi : m = i
    · subst hmi
      exact absurd hIi.2 (hm hIi.1)
    · simpa [wires] using hxx m hmi
  | append_singleton gs g ih =>
    have hok' : ∀ g ∈ gs, ok g := fun g' hg' => hok g' (by simp [hg'])
    have hg : ok g := hok g (by simp)
    have ih := ih hok'
    have hlen := inv_len k I gs
    rw [run_snoc]
    generalize run k I gs = st at ih hlen ⊢
    obtain ⟨R, G⟩ := st
    dsimp only at ih hlen
    show ∀ m, i ∉ UU (R ++ [(newR k R G g).1]) →
      ((stat (R ++ [(newR k R G g).1]) m).isC = true → i ∉ AA (R ++ [(newR k R G g).1]) m) →
      (wires (gs ++ [g]) x).getD m false = (wires (gs ++ [g]) x').getD m false
    intro m hU hm
    have hU' : i ∉ UU R := fun h => hU (UU_mono R _ h)
    by_cases hlt : m < R.length
    · rw [stat_snoc_lt _ _ hlt, AA_snoc_lt _ _ hlt] at hm
      rw [wire_before _ _ _ (by omega), wire_before _ _ _ (by omega)]
      exact ih m hU' hm
    · by_cases heq : m = R.length
      · subst heq
        rw [stat_snoc_eq, AA_snoc_eq] at hm
        have e1 : R.length = x.length + gs.length := by omega
        have e2 : R.length = x'.length + gs.length := by omega
        rw [e1, wire_last, ← e1, e2, wire_last]
        apply eval_congr g hg
        intro a ha
        apply ih a hU'
        intro hca hia
        obtain ⟨hor, hsub⟩ := newR_ops k R G g hg a ha hca
        rcases hor with hc | hc
        · exact hm hc (hsub hia)
        · exact hU (UU_new R _ hc (hsub hia))
      · rw [wire_outside _ _ (by simp; omega), wire_outside _ _ (by simp; omega)]

/-! ## Counting -/

theorem setLemma (A : ℕ → Finset ℕ) (c : ℕ → Bool) (T : ℕ)
    (h : ∀ m < T, ∃ P L : Finset ℕ, (∀ a ∈ P, a < m) ∧ A m ⊆ L ∪ P.biUnion A ∧
      L.card + P.card ≤ 1 + (if c m = true then 1 else 0)) :
    ∀ M ≤ T, ∀ Q : Finset ℕ, (∀ q ∈ Q, q < M) →
      (Q.biUnion A).card ≤ ((Finset.range M).filter (fun m => c m = true)).card + Q.card := by
  intro M
  induction M with
  | zero =>
    intro _ Q hQ
    have : Q = ∅ := Finset.eq_empty_of_forall_notMem
      (fun q hq => absurd (hQ q hq) (Nat.not_lt_zero _))
    simp [this]
  | succ M ih =>
    intro hM Q hQ
    have hcnt : ((Finset.range (M+1)).filter (fun m => c m = true)).card =
        ((Finset.range M).filter (fun m => c m = true)).card + (if c M = true then 1 else 0) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hc
      · rw [Finset.card_insert_of_notMem (by simp)]
      · simp
    by_cases hMQ : M ∈ Q
    · obtain ⟨P, L, hP, hA, hcard⟩ := h M (by omega)
      have hQ' : ∀ q ∈ Q.erase M ∪ P, q < M := by
        intro q hq
        rcases Finset.mem_union.1 hq with hq | hq
        · have h1 := Finset.mem_erase.1 hq; have := hQ q h1.2; omega
        · exact hP q hq
      have h1 := ih (by omega) (Q.erase M ∪ P) hQ'
      have hsub : Q.biUnion A ⊆ L ∪ (Q.erase M ∪ P).biUnion A := by
        intro x hx
        obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.1 hx
        by_cases hqM : q = M
        · subst hqM
          rcases Finset.mem_union.1 (hA hxq) with h' | h'
          · exact Finset.mem_union_left _ h'
          · obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 h'
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨p, Finset.mem_union_right _ hp, hxp⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.2
            ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hqM, hq⟩), hxq⟩)
      have h2 := Finset.card_le_card hsub
      have h3 := Finset.card_union_le L ((Q.erase M ∪ P).biUnion A)
      have h4 := Finset.card_union_le (Q.erase M) P
      have h5 : (Q.erase M).card + 1 = Q.card := Finset.card_erase_add_one hMQ
      omega
    · have hQ' : ∀ q ∈ Q, q < M := by
        intro q hq; have := hQ q hq; have : q ≠ M := fun e => hMQ (e ▸ hq); omega
      have := ih (by omega) Q hQ'
      omega

theorem card_range_filter (p : Rec → Bool) (rs : List Rec) :
    ((Finset.range rs.length).filter (fun m => p (rs.getD m dR) = true)).card =
      (rs.filter p).length := by
  induction rs using List.reverseRecOn with
  | nil => simp
  | append_singleton rs r ih =>
    rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert,
      List.filter_append]
    have hc : ((Finset.range rs.length).filter (fun m => p ((rs ++ [r]).getD m dR) = true)) =
        ((Finset.range rs.length).filter (fun m => p (rs.getD m dR) = true)) := by
      apply Finset.filter_congr; intro m hm; rw [getD_snoc_lt _ _ _ (Finset.mem_range.1 hm)]
    rw [hc, getD_snoc_eq]
    by_cases h : p r = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]; simp [h]
    · rw [if_neg h, ih]; simp [h]

/-! ## The initial records -/

noncomputable def initR (n k : ℕ) (wire : Fin k → Fin n) (fixed : Fin n → Bool) : List Rec :=
  List.ofFn (fun i : Fin n => if h : ∃ j, wire j = i then
    (⟨.lv (Classical.choose h).val, ∅, false, false⟩ : Rec)
    else ⟨.cst (fixed i), {i.val}, false, false⟩)

/-! ## Main -/

theorem main (n k : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (wire : Fin k → Fin n) (fixed : Fin n → Bool) (hinj : Function.Injective wire)
    (plug : (Fin k → Bool) → Fin n → Bool)
    (hplug : ∀ y i, plug y i = if i ∈ Finset.univ.image wire then
      decide (∃ j, wire j = i ∧ y j = true) else fixed i)
    (hne : ∃ x y : Fin k → Bool, C.eval (List.ofFn (plug x)) ≠ C.eval (List.ofFn (plug y))) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size - nN D.gates + ((Finset.univ : Finset (Fin n)).filter (fun i =>
        ∃ x : Fin n → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
          C.eval (List.ofFn (Function.update x i true)))).card
        ≤ C.size - nN C.gates + k ∧
      nN D.gates ≤ nN C.gates ∧
      ∀ y : Fin k → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (plug y)) := by
  have hok : ∀ g ∈ C.gates, ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  obtain ⟨I, hIdef⟩ : ∃ I, I = initR n k wire fixed := ⟨_, rfl⟩
  have hIlen : I.length = n := by rw [hIdef]; simp [initR]
  have hIget : ∀ m, I.getD m dR = if h : m < n then
      (if h' : ∃ j, wire j = ⟨m, h⟩ then
        (⟨.lv (Classical.choose h').val, ∅, false, false⟩ : Rec)
        else ⟨.cst (fixed ⟨m, h⟩), {m}, false, false⟩) else dR := by
    intro m; rw [hIdef]; unfold initR; rw [getD_ofFn]
  have hIb : ∀ m j, stat I m = .lv j → j < k := by
    intro m j hm
    unfold stat at hm
    rw [hIget] at hm
    split_ifs at hm with h1 h2
    · simp only [SV.lv.injEq] at hm; subst hm; exact (Classical.choose h2).isLt
    all_goals simp [dR] at hm
  have hIev : ∀ y : Fin k → Bool, ∀ m, (stat I m).ev (List.ofFn y) =
      (List.ofFn (plug y)).getD m false := by
    intro y m
    unfold stat
    rw [hIget, getD_ofFn]
    by_cases h1 : m < n
    · rw [dif_pos h1, dif_pos h1, hplug]
      by_cases h2 : ∃ j, wire j = ⟨m, h1⟩
      · rw [dif_pos h2]
        have hmem : (⟨m, h1⟩ : Fin n) ∈ Finset.univ.image wire := by simpa using h2
        rw [if_pos hmem]
        have hc := Classical.choose_spec h2
        show (List.ofFn y).getD (Classical.choose h2).val false = _
        rw [getD_ofFn, dif_pos (Classical.choose h2).isLt]
        cases hy : y (Classical.choose h2)
        · symm; rw [decide_eq_false_iff_not]
          rintro ⟨j, hj, hyj⟩
          have := hinj (hj.trans hc.symm)
          subst this
          simp [hy] at hyj
        · symm; rw [decide_eq_true_iff]
          exact ⟨_, hc, hy⟩
      · rw [dif_neg h2]
        have hmem : (⟨m, h1⟩ : Fin n) ∉ Finset.univ.image wire := by simpa using h2
        rw [if_neg hmem]; rfl
    · rw [dif_neg h1, dif_neg h1]; rfl
  have hIcnt : ∀ r ∈ I, r.cost = false ∧ r.al = false := by
    intro r hr
    rw [hIdef] at hr
    simp only [initR, List.mem_ofFn] at hr
    obtain ⟨i, hi⟩ := hr
    subst hi
    split_ifs <;> simp
  have hIA : ∀ m < I.length, ∃ P L : Finset ℕ, (∀ a ∈ P, a < m) ∧ AA I m ⊆ L ∪ P.biUnion (AA I) ∧
      L.card + P.card ≤ 1 + (if (I.getD m dR).cost then 1 else 0) := by
    intro m hm
    refine ⟨∅, AA I m, by simp, by simp, ?_⟩
    have : (AA I m).card ≤ 1 := by
      unfold AA; rw [hIget]
      split_ifs <;> simp [dR]
    rw [Finset.card_empty, add_zero]; omega
  -- the run
  have hb := inv_bound k I hIb C.gates
  have hev : ∀ y : Fin k → Bool, ∀ m,
      (stat (run k I C.gates).1 m).ev (wires (run k I C.gates).2 (List.ofFn y)) =
        (wires C.gates (List.ofFn (plug y))).getD m false := by
    intro y
    exact inv_ev k I hIb (List.ofFn y) (List.ofFn (plug y)) (by simp) (by simp [hIlen])
      (hIev y) C.gates hok
  have hfan := inv_fan k I C.gates hok
  have hcount := inv_count k I hIcnt C.gates hok
  have hA := inv_A k I hIA C.gates hok
  set R := (run k I C.gates).1 with hR
  set G := (run k I C.gates).2 with hG
  have hRlen : R.length = n + C.gates.length := by rw [hR, inv_len, hIlen]
  have hCeval : ∀ x : List Bool, C.eval x = (wires C.gates x).getD C.output false :=
    fun x => rfl
  -- the output is live
  cases hs : stat R C.output with
  | cst b =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hne
    have h1 := hev x C.output
    have h2 := hev y C.output
    rw [hs] at h1 h2
    simp only [SV.ev] at h1 h2
    rw [hCeval, hCeval, ← h1, ← h2] at hxy
    exact hxy rfl
  | lv j =>
    refine ⟨⟨G, j⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h | h | h <;> simp [h]
    · -- the counting
      have hU : (UU R).card ≤ (R.filter (fun r => r.cost)).length +
          (R.filter (fun r => r.al)).length := by
        have hc1 : ((Finset.range R.length).filter (fun m => (R.getD m dR).cost = true)).card =
            (R.filter (fun r => r.cost)).length := card_range_filter (fun r => r.cost) R
        have hc2 : ((Finset.range R.length).filter (fun m => (R.getD m dR).al = true)).card =
            (R.filter (fun r => r.al)).length := card_range_filter (fun r => r.al) R
        have hsl : (((Finset.range R.length).filter
            (fun m => (R.getD m dR).al = true)).biUnion (AA R)).card ≤
            ((Finset.range R.length).filter (fun m => (R.getD m dR).cost = true)).card +
            ((Finset.range R.length).filter (fun m => (R.getD m dR).al = true)).card :=
          setLemma (AA R) (fun m => (R.getD m dR).cost) R.length hA R.length le_rfl _
            (fun q hq => Finset.mem_range.1 (Finset.mem_filter.1 hq).1)
        unfold UU
        omega
      have hE : ((Finset.univ : Finset (Fin n)).filter (fun i =>
          ∃ x : Fin n → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
            C.eval (List.ofFn (Function.update x i true)))).card ≤ k + (UU R).card := by
        have hsub : ((Finset.univ : Finset (Fin n)).filter (fun i =>
            ∃ x : Fin n → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
              C.eval (List.ofFn (Function.update x i true)))) ⊆
            Finset.univ.image wire ∪ (Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ UU R)) := by
          intro i hi
          obtain ⟨x, hx⟩ := (Finset.mem_filter.1 hi).2
          by_contra hcon
          rw [Finset.mem_union, not_or] at hcon
          obtain ⟨hc1, hc2⟩ := hcon
          have hnw : ¬ ∃ j, wire j = i := by simpa using hc1
          have hiU : (i : ℕ) ∉ UU R := by simpa using hc2
          have hIi : (stat I i).isC = true ∧ (i : ℕ) ∈ AA I i := by
            unfold stat AA
            rw [hIget, dif_pos i.isLt, dif_neg (by simpa using hnw)]
            simp [SV.isC]
          have key := inv_indep k I i hIi (List.ofFn (Function.update x i false))
            (List.ofFn (Function.update x i true)) (by simp [hIlen]) (by simp [hIlen])
            (by
              intro m hm
              rw [getD_ofFn, getD_ofFn]
              split_ifs with h
              · have : (⟨m, h⟩ : Fin n) ≠ i := fun e => hm (by rw [← e])
                simp [Function.update_of_ne this]
              · rfl)
            C.gates hok C.output hiU (by rw [← hR, hs]; simp [SV.isC])
          rw [hCeval, hCeval] at hx
          exact hx key
        refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
        have h1 : (Finset.univ.image wire).card ≤ k :=
          Finset.card_image_le.trans (by simp)
        have h2 : (Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ UU R)).card ≤ (UU R).card :=
          Finset.card_le_card_of_injOn (fun i => (i : ℕ))
            (fun a ha => (Finset.mem_filter.1 ha).2) (fun a _ b _ h => Fin.ext h)
        omega
      have hn1 : nN G ≤ G.length := List.length_filter_le _ _
      have hn2 : nN C.gates ≤ C.gates.length := List.length_filter_le _ _
      show G.length - nN G + _ ≤ C.gates.length - nN C.gates + k
      omega
    · exact hcount.2
    · intro y
      have := hev y C.output
      rw [hs] at this
      rw [hCeval, ← this]
      rfl

end PEqualNP.Outside.L_lib_586_aux

theorem PEqualNP.Outside.L_lib_586 : ∀ (n k : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C →
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  let f := fun (x : Fin n → Bool) => C.eval (List.ofFn x)
  let e := ((Finset.univ : Finset (Fin n)).filter (fun i =>
    ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))).card
  ∀ (wire : Fin k → Fin n) (fixed : Fin n → Bool), Function.Injective wire →
    let plug := fun (y : Fin k → Bool) (i : Fin n) =>
      if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ y j = true) else fixed i
    (∃ x y : Fin k → Bool, f (plug x) ≠ f (plug y)) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      binary D + e ≤ binary C + k ∧ inv D ≤ inv C ∧
      ∀ y : Fin k → Bool, D.eval (List.ofFn y) = f (plug y) := by
  intro n k C hC inv binary f e wire fixed hinj plug hne
  obtain ⟨D, hD, h1, h2, h3⟩ :=
    PEqualNP.Outside.L_lib_586_aux.main n k C hC wire fixed hinj plug (fun _ _ => rfl) hne
  have hinv : ∀ G : PEqualNP.CircuitLowerBounds.Circuit,
      inv G = PEqualNP.Outside.L_lib_586_aux.nN G.gates := by
    intro G
    show (G.gates.filter _).length = (G.gates.filter _).length
    congr 1
    apply List.filter_congr
    intro g _
    by_cases hp : g.op = PEqualNP.CircuitLowerBounds.GateOp.not
    · rw [@decide_eq_true _ (Classical.propDecidable _) hp]
      simp [PEqualNP.Outside.L_lib_586_aux.isNot, PEqualNP.Outside.L_lib_586_aux.opNot, hp]
    · rw [@decide_eq_false _ (Classical.propDecidable _) hp]
      cases h : g.op <;>
        simp_all [PEqualNP.Outside.L_lib_586_aux.isNot, PEqualNP.Outside.L_lib_586_aux.opNot]
  refine ⟨D, hD, ?_, ?_, h3⟩
  · show D.size - inv D + e ≤ C.size - inv C + k
    rw [hinv D, hinv C]
    exact h1
  · rw [hinv D, hinv C]
    exact h2
