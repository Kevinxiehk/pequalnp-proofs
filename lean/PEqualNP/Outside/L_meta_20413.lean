import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20413_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 6 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 11]⟩], 12⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (379 : ℕ).testBit (4 * u.val + v.val)) 6 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20413_aux

theorem PEqualNP.Outside.L_meta_20413 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (379 : ℕ).testBit (4 * u.val + v.val)) 6 :=
  PEqualNP.Outside.L_meta_20413_aux.main
