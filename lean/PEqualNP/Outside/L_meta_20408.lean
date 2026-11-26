import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20408_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 4 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [8, 9]⟩], 10⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (319 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20408_aux

theorem PEqualNP.Outside.L_meta_20408 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (319 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  PEqualNP.Outside.L_meta_20408_aux.main
