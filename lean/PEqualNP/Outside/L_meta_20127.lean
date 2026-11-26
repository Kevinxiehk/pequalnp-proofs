import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20127_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 32 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [16, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [20, 4]⟩, ⟨.or, [21, 6]⟩, ⟨.or, [16, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [24, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [26, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [28, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [30, 14]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [22, 29]⟩, ⟨.and, [17, 31]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [25, 33]⟩, ⟨.and, [18, 27]⟩, ⟨.and, [23, 32]⟩, ⟨.and, [19, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩, ⟨.or, [46, 41]⟩], 47⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16816131623650294815 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20127_aux

theorem PEqualNP.Outside.L_meta_20127 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16816131623650294815 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20127_aux.main
