import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25664_aux

open PEqualNP.CircuitLowerBounds

/-! ## Part A: abstract programs over label coordinates -/

abbrev Lab (t : ℕ) := Fin t → Bool × Bool

def pi2 (α β : Bool × Bool) : Bool := (xor α.1 β.1) && (xor α.2 β.2)

def sh {t : ℕ} (p : Bool) (c x : Lab t) : Lab t :=
  fun i => (xor (x i).1 (p && (c i).1), xor (x i).2 (p && (c i).2))

def AbsCls : (t : ℕ) → (Lab t → Lab t → Bool) → Prop
  | 0, _ => True
  | t+1, F => ∃ (e : Bool) (c : Lab t) (K : Lab t → Lab t → Bool), AbsCls t K ∧
      ∀ a b, F a b = xor (e && pi2 (a 0) (b 0))
        (K (sh (pi2 (a 0) (b 0)) c (Fin.tail a)) (Fin.tail b))

def chi (b : Bool) : ℤ := if b then -1 else 1

def RowHad {t : ℕ} (F : Lab t → Lab t → Bool) : Prop :=
  ∀ a a' : Lab t, a ≠ a' → ∑ b, chi (xor (F a b) (F a' b)) = 0

def Closed3 {t : ℕ} (F : Lab t → Lab t → Bool) : Prop :=
  ∀ a1 a2 a3 : Lab t, ∃ (a4 : Lab t) (c : Bool), ∀ b,
    xor (xor (xor (F a1 b) (F a2 b)) (F a3 b)) (F a4 b) = c

def T {t : ℕ} (K : Lab t → Lab t → Bool) (x y : Lab t) : ℤ :=
  ∑ b, chi (xor (K x b) (K y b))

lemma sh_false {t : ℕ} (c x : Lab t) : sh false c x = x := by
  funext i; simp [sh]

lemma sh_sh {t : ℕ} (c x : Lab t) : sh true c (sh true c x) = x := by
  funext i; simp [sh, Bool.xor_assoc]

lemma chi_xor (a b : Bool) : chi (xor a b) = chi a * chi b := by
  cases a <;> cases b <;> simp [chi]

lemma chi_not (b : Bool) : chi (!b) = - chi b := by
  cases b <;> simp [chi]

lemma sum_lab_succ {t : ℕ} (f : Lab (t+1) → ℤ) :
    ∑ b, f b = ∑ b0 : Bool × Bool, ∑ b' : Lab t, f (Fin.cons b0 b') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool × Bool)) _ _ (fun _ => rfl)).symm

lemma card_lab (t : ℕ) : Fintype.card (Lab t) = 4 ^ t := by
  simp [Lab, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool]

lemma T_self {t : ℕ} (K : Lab t → Lab t → Bool) (x : Lab t) : T K x x = 4 ^ t := by
  have : ∀ b : Lab t, chi (xor (K x b) (K x b)) = 1 := by intro b; simp [chi]
  simp only [T, this, Finset.sum_const, Finset.card_univ, card_lab, nsmul_eq_mul, mul_one]
  push_cast; ring

lemma T_comm {t : ℕ} (K : Lab t → Lab t → Bool) (x y : Lab t) : T K x y = T K y x := by
  unfold T; congr 1; funext b; rw [Bool.xor_comm]

lemma pi2_sum (α1 α2 α3 β : Bool × Bool) :
    xor (xor (xor (pi2 α1 β) (pi2 α2 β)) (pi2 α3 β))
      (pi2 (xor (xor α1.1 α2.1) α3.1, xor (xor α1.2 α2.2) α3.2) β) =
    xor (xor (xor (α1.1 && α1.2) (α2.1 && α2.2)) (α3.1 && α3.2))
      ((xor (xor α1.1 α2.1) α3.1) && (xor (xor α1.2 α2.2) α3.2)) := by
  obtain ⟨a, b⟩ := α1; obtain ⟨c, d⟩ := α2; obtain ⟨e, f⟩ := α3; obtain ⟨g, h⟩ := β
  simp only [pi2]
  revert a b c d e f g h; decide

lemma xor_rearr (p1 p2 p3 p4 k1 k2 k3 k4 : Bool) :
    xor (xor (xor (xor p1 k1) (xor p2 k2)) (xor p3 k3)) (xor p4 k4) =
    xor (xor (xor (xor k1 k2) k3) k4) (xor (xor (xor p1 p2) p3) p4) := by
  revert p1 p2 p3 p4 k1 k2 k3 k4; decide

theorem had_closed : ∀ (t : ℕ) (F : Lab t → Lab t → Bool), AbsCls t F → RowHad F → Closed3 F
  | 0, F, _, _ => by
    intro a1 a2 a3
    let b0 : Lab 0 := fun i => i.elim0
    refine ⟨a1, xor (xor (xor (F a1 b0) (F a2 b0)) (F a3 b0)) (F a1 b0), fun b => ?_⟩
    have : b = b0 := funext fun i => i.elim0
    rw [this]
  | t+1, F, hF, hH => by
    obtain ⟨e, c, K, hK, hFK⟩ := hF
    have inner : ∀ (α α' : Bool × Bool) (x x' : Lab t) (b0 : Bool × Bool),
        ∑ b' : Lab t, chi (xor (F (Fin.cons α x) (Fin.cons b0 b')) (F (Fin.cons α' x') (Fin.cons b0 b')))
        = chi (xor (e && pi2 α b0) (e && pi2 α' b0)) *
            T K (sh (pi2 α b0) c x) (sh (pi2 α' b0) c x') := by
      intro α α' x x' b0
      rw [T, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b' _
      rw [hFK, hFK]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [← chi_xor]
      congr 1
      generalize (e && pi2 α b0) = p; generalize (e && pi2 α' b0) = q
      generalize K (sh (pi2 α b0) c x) b' = r; generalize K (sh (pi2 α' b0) c x') b' = w
      revert p q r w; decide
    have hdiag : ∀ x y : Lab t, x ≠ y → 3 * T K x y + T K (sh true c x) (sh true c y) = 0 := by
      intro x y hxy
      have hne : (Fin.cons (false, false) x : Lab (t+1)) ≠ Fin.cons (false, false) y := by
        intro h; apply hxy
        have := congrArg (fun z : Lab (t+1) => Fin.tail z) h
        simpa using this
      have h1 := hH _ _ hne
      rw [sum_lab_succ] at h1
      simp only [inner] at h1
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, pi2, Bool.xor_self, chi,
        Bool.xor_true, Bool.xor_false, Bool.not_false, Bool.not_true, Bool.and_true,
        Bool.and_false, Bool.and_self, sh_false, Bool.false_eq_true, ↓reduceIte, one_mul] at h1
      linarith
    have hKH : RowHad K := by
      intro x y hxy
      have h1 := hdiag x y hxy
      have hne' : sh true c x ≠ sh true c y := by
        intro h; apply hxy; rw [← sh_sh c x, h, sh_sh]
      have h2 := hdiag _ _ hne'
      rw [sh_sh, sh_sh] at h2
      show T K x y = 0
      linarith
    have hoff : ∀ x : Lab t,
        2 * 4 ^ t + chi e * (T K x (sh true c x) + T K (sh true c x) x) = 0 := by
      intro x
      have hne : (Fin.cons (false, false) x : Lab (t+1)) ≠ Fin.cons (true, false) x := by
        intro h; have := congrFun h 0; simp at this
      have h1 := hH _ _ hne
      rw [sum_lab_succ] at h1
      simp only [inner] at h1
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, pi2, Bool.xor_self,
        Bool.xor_true, Bool.xor_false, Bool.true_xor, Bool.false_xor, Bool.not_false,
        Bool.not_true, Bool.and_true, Bool.and_false, Bool.and_self, sh_false, T_self] at h1
      have hc0 : chi false = 1 := rfl
      rw [hc0] at h1
      linarith
    have hc : ∀ x : Lab t, sh true c x = x := by
      intro x
      by_contra hne
      have h1 := hoff x
      have e1 : T K x (sh true c x) = 0 := hKH _ _ (Ne.symm hne)
      have e2 : T K (sh true c x) x = 0 := hKH _ _ hne
      rw [e1, e2] at h1
      have : (0 : ℤ) < 4 ^ t := by positivity
      linarith
    have hsh : ∀ (p : Bool) (x : Lab t), sh p c x = x := by
      intro p x; cases p
      · exact sh_false c x
      · exact hc x
    have he : e = true := by
      have h1 := hoff (fun _ => (false, false))
      rw [hc, T_self] at h1
      have : (0 : ℤ) < 4 ^ t := by positivity
      cases e
      · simp [chi] at h1; linarith
      · rfl
    have IH := had_closed t K hK hKH
    intro a1 a2 a3
    obtain ⟨x4, cK, hx4⟩ := IH (Fin.tail a1) (Fin.tail a2) (Fin.tail a3)
    let α4 : Bool × Bool := (xor (xor (a1 0).1 (a2 0).1) (a3 0).1, xor (xor (a1 0).2 (a2 0).2) (a3 0).2)
    refine ⟨Fin.cons α4 x4, xor cK (xor (xor (xor ((a1 0).1 && (a1 0).2) ((a2 0).1 && (a2 0).2))
      ((a3 0).1 && (a3 0).2)) (α4.1 && α4.2)), fun b => ?_⟩
    rw [hFK, hFK, hFK, hFK]
    simp only [Fin.cons_zero, Fin.tail_cons, hsh, he, Bool.true_and]
    rw [xor_rearr, hx4 (Fin.tail b)]
    congr 1
    exact pi2_sum (a1 0) (a2 0) (a3 0) (b 0)

/-! ## Part B: extraction of the abstract program from a circuit -/

def nl (g : Gate) : Bool := (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
    (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma gate_aff (g : Gate) (hl : g.inputs.length ≤ 2) :
    ∃ (k0 k1 k2 : Bool) (i j : ℕ), ∀ W : ℕ → Bool,
      g.op.eval (g.inputs.map W) =
        xor (xor (xor k0 (k1 && W i)) (k2 && W j)) (nl g && (W i && W j)) := by
  rcases g with ⟨op, ins⟩
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · exact ⟨op.eval [], false, false, 0, 0, fun W => by simp [nl]⟩
  · refine ⟨op.eval [false], xor (op.eval [false]) (op.eval [true]), false, i, i, fun W => ?_⟩
    simp only [nl, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
    cases W i <;> simp
  · refine ⟨op.eval [false,false], xor (op.eval [false,false]) (op.eval [true,false]),
      xor (op.eval [false,false]) (op.eval [false,true]), i, j, fun W => ?_⟩
    simp only [nl, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
    have h22 : ((0 + 1 + 1 : ℕ) == 2) = true := rfl
    rw [h22, Bool.true_and]
    cases W i <;> cases W j <;>
    · generalize op.eval [false, false] = a
      generalize op.eval [false, true] = b
      generalize op.eval [true, false] = c
      generalize op.eval [true, true] = d
      revert a b c d; decide
  · simp at hl

def Z4 {R : Type} (Aw : R → ℕ → Bool) (r1 r2 r3 r4 : R) : Prop :=
  ∀ w, xor (xor (xor (Aw r1 w) (Aw r2 w)) (Aw r3 w)) (Aw r4 w) = false

def AffL {R : Type} {t : ℕ} (Aw : R → ℕ → Bool) (ℓ : R → Lab t) : Prop :=
  ∀ r1 r2 r3 r4, Z4 Aw r1 r2 r3 r4 → ∀ i,
    xor (xor (xor (ℓ r1 i).1 (ℓ r2 i).1) (ℓ r3 i).1) (ℓ r4 i).1 = false ∧
    xor (xor (xor (ℓ r1 i).2 (ℓ r2 i).2) (ℓ r3 i).2) (ℓ r4 i).2 = false

def AffB {R : Type} (Aw : R → ℕ → Bool) (A : R → Bool) : Prop :=
  ∀ r1 r2 r3 r4, Z4 Aw r1 r2 r3 r4 → xor (xor (xor (A r1) (A r2)) (A r3)) (A r4) = false

lemma getD_snoc (l : List Bool) (y : Bool) (w : ℕ) :
    (l ++ [y]).getD w false = if w = l.length then y else l.getD w false := by
  rcases lt_trichotomy w l.length with h | h | h
  · rw [if_neg h.ne, List.getD_append _ _ _ _ h]
  · subst h; rw [if_pos rfl, List.getD_append_right _ _ _ _ le_rfl]; simp
  · rw [if_neg h.ne', List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma aff_z4 (k0 k1 k2 a1 a2 a3 a4 b1 b2 b3 b4 : Bool)
    (ha : xor (xor (xor a1 a2) a3) a4 = false) (hb : xor (xor (xor b1 b2) b3) b4 = false) :
    xor (xor (xor (xor (xor k0 (k1 && a1)) (k2 && b1)) (xor (xor k0 (k1 && a2)) (k2 && b2)))
      (xor (xor k0 (k1 && a3)) (k2 && b3))) (xor (xor k0 (k1 && a4)) (k2 && b4)) = false := by
  have ha' : a4 = xor (xor a1 a2) a3 := by
    revert ha; cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> decide
  have hb' : b4 = xor (xor b1 b2) b3 := by
    revert hb; cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide
  subst ha' hb'
  revert k0 k1 k2 a1 a2 a3 b1 b2 b3; decide

lemma bid1 (k0 k1 k2 a b a' b' : Bool) :
    xor (xor k0 (k1 && xor a a')) (k2 && xor b b') =
      xor (xor (xor k0 (k1 && a)) (k2 && b)) (xor (k1 && a') (k2 && b')) := by
  revert k0 k1 k2 a b a' b'; decide

lemma bid2 (k0 k1 k2 a b a' b' : Bool) :
    xor (xor (xor k0 (k1 && xor a a')) (k2 && xor b b')) (xor a a' && xor b b') =
      xor (xor (xor (xor k0 (k1 && a)) (k2 && b)) (xor a a' && xor b b'))
        (xor (k1 && a') (k2 && b')) := by
  revert k0 k1 k2 a b a' b'; decide

lemma bid3 (a p d b f : Bool) :
    xor (xor (xor a (p && d)) b) f = xor (xor a b) (xor (d && p) f) := by
  revert a p d b f; decide

lemma xor4_eq (x1 x2 x3 x4 : Bool) (h : xor (xor (xor x1 x2) x3) x4 = false) :
    x1 = xor x2 (xor x3 x4) := by
  revert h; cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> decide

theorem extract {C : Type} (out : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ (t : ℕ), gs.countP nl = t →
    ∀ (R : Type) (L : ℕ) (x : R → C → List Bool) (Aw : R → ℕ → Bool) (Bw : C → ℕ → Bool),
    (∀ r c, (x r c).length = L) → (∀ r c w, (x r c).getD w false = xor (Aw r w) (Bw c w)) →
    ∃ (ℓ : R → Lab t) (m : C → Lab t) (F : Lab t → Lab t → Bool) (A : R → Bool) (B : C → Bool),
      AbsCls t F ∧
      (∀ r c, (gs.foldl stepW (x r c)).getD out false = xor (xor (A r) (B c)) (F (ℓ r) (m c))) ∧
      AffL Aw ℓ ∧ AffB Aw A
  | [], _, t, ht, R, L, x, Aw, Bw, _, hx => by
    simp at ht; subst ht
    refine ⟨fun _ i => i.elim0, fun _ i => i.elim0, fun _ _ => false, fun r => Aw r out,
      fun c => Bw c out, trivial, ?_, ?_, ?_⟩
    · intro r c; simp only [List.foldl_nil, Bool.xor_false]; exact hx r c out
    · intro r1 r2 r3 r4 _ i; exact i.elim0
    · intro r1 r2 r3 r4 hz; exact hz out
  | g :: gs, hfan, t, ht, R, L, x, Aw, Bw, hlen, hx => by
    obtain ⟨k0, k1, k2, i, j, hg⟩ := gate_aff g (hfan g (by simp))
    have hfan' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    rw [List.countP_cons] at ht
    cases hng : nl g
    · -- an affine gate
      rw [hng] at ht
      simp only [Bool.false_eq_true, if_false, add_zero] at ht
      let Aw' : R → ℕ → Bool := fun r w =>
        if w = L then xor (xor k0 (k1 && Aw r i)) (k2 && Aw r j) else Aw r w
      let Bw' : C → ℕ → Bool := fun c w =>
        if w = L then xor (k1 && Bw c i) (k2 && Bw c j) else Bw c w
      have hlen' : ∀ r c, (stepW (x r c) g).length = L + 1 := by
        intro r c; simp [stepW, hlen]
      have hx' : ∀ r c w, (stepW (x r c) g).getD w false = xor (Aw' r w) (Bw' c w) := by
        intro r c w
        simp only [stepW]
        rw [getD_snoc, hlen r c]
        by_cases hw : w = L
        · simp only [hw, if_true, Aw', Bw']
          rw [hg]
          simp only [hng, Bool.false_and, Bool.xor_false, hx]
          exact bid1 _ _ _ _ _ _ _
        · simp only [hw, if_false, Aw', Bw']; exact hx r c w
      obtain ⟨ℓ, m, F, A, B, hF, hout, hℓ, hA⟩ :=
        extract out gs hfan' t ht R (L+1) (fun r c => stepW (x r c) g) Aw' Bw' hlen' hx'
      have hz' : ∀ r1 r2 r3 r4, Z4 Aw r1 r2 r3 r4 → Z4 Aw' r1 r2 r3 r4 := by
        intro r1 r2 r3 r4 hz w
        simp only [Aw']
        by_cases hw : w = L
        · simp only [hw, if_true]
          exact aff_z4 _ _ _ _ _ _ _ _ _ _ _ (hz i) (hz j)
        · simp only [hw, if_false]; exact hz w
      refine ⟨ℓ, m, F, A, B, hF, fun r c => ?_, fun r1 r2 r3 r4 hz => hℓ _ _ _ _ (hz' _ _ _ _ hz),
        fun r1 r2 r3 r4 hz => hA _ _ _ _ (hz' _ _ _ _ hz)⟩
      rw [List.foldl_cons]; exact hout r c
    · -- a nonlinear gate
      rw [hng] at ht
      simp only [if_true] at ht
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨gs.countP nl, by omega⟩
      have ht' : gs.countP nl = t' := by omega
      let Aw' : R × Bool → ℕ → Bool := fun rp w =>
        if w = L then xor (xor (xor k0 (k1 && Aw rp.1 i)) (k2 && Aw rp.1 j)) rp.2 else Aw rp.1 w
      let Bw' : C → ℕ → Bool := fun c w =>
        if w = L then xor (k1 && Bw c i) (k2 && Bw c j) else Bw c w
      let x' : R × Bool → C → List Bool := fun rp c => x rp.1 c ++ [xor (Aw' rp L) (Bw' c L)]
      have hlen' : ∀ rp c, (x' rp c).length = L + 1 := by
        intro rp c; simp [x', hlen]
      have hx' : ∀ rp c w, (x' rp c).getD w false = xor (Aw' rp w) (Bw' c w) := by
        intro rp c w
        simp only [x']
        rw [getD_snoc, hlen]
        by_cases hw : w = L
        · subst hw; simp
        · simp only [hw, if_false, Aw', Bw']; exact hx rp.1 c w
      obtain ⟨ℓ', m', F', A', B', hF', hout', hℓ', hA'⟩ :=
        extract out gs hfan' t' ht' (R × Bool) (L+1) x' Aw' Bw' hlen' hx'
      let π : R → C → Bool := fun r c => (x r c).getD i false && (x r c).getD j false
      have hstep : ∀ r c, stepW (x r c) g = x' (r, π r c) c := by
        intro r c
        simp only [stepW, x']
        congr 2
        rw [hg]
        simp only [hng, Bool.true_and, Aw', Bw', if_true, π, hx]
        exact bid2 _ _ _ _ _ _ _
      have hzL : ∀ r r0 : R, Z4 Aw' (r, true) (r, false) (r0, true) (r0, false) := by
        intro r r0 w
        simp only [Aw']
        by_cases hw : w = L
        · simp only [hw, if_true]
          generalize xor (xor k0 (k1 && Aw r i)) (k2 && Aw r j) = a
          generalize xor (xor k0 (k1 && Aw r0 i)) (k2 && Aw r0 j) = b
          revert a b; decide
        · simp only [hw, if_false]
          generalize Aw r w = a; generalize Aw r0 w = b
          revert a b; decide
      obtain ⟨csh, d, hsh, hd⟩ : ∃ (csh : Lab t') (d : Bool),
          (∀ r p, ℓ' (r, p) = sh p csh (ℓ' (r, false))) ∧
          (∀ r p, A' (r, p) = xor (A' (r, false)) (p && d)) := by
        rcases isEmpty_or_nonempty R with hR | ⟨⟨r0⟩⟩
        · exact ⟨fun _ => (false, false), false, fun r => (IsEmpty.false r).elim,
            fun r => (IsEmpty.false r).elim⟩
        · refine ⟨fun k => (xor (ℓ' (r0, true) k).1 (ℓ' (r0, false) k).1,
            xor (ℓ' (r0, true) k).2 (ℓ' (r0, false) k).2),
            xor (A' (r0, true)) (A' (r0, false)), ?_, ?_⟩
          · intro r p; cases p
            · exact (sh_false _ _).symm
            · funext k
              obtain ⟨h1, h2⟩ := hℓ' _ _ _ _ (hzL r r0) k
              simp only [sh, Bool.true_and]
              ext
              · exact xor4_eq _ _ _ _ h1
              · exact xor4_eq _ _ _ _ h2
          · intro r p; cases p
            · simp
            · have h1 := hA' _ _ _ _ (hzL r r0)
              simp only [Bool.true_and]
              exact xor4_eq _ _ _ _ h1
      have hz' : ∀ r1 r2 r3 r4, Z4 Aw r1 r2 r3 r4 →
          Z4 Aw' (r1, false) (r2, false) (r3, false) (r4, false) := by
        intro r1 r2 r3 r4 hz w
        simp only [Aw']
        by_cases hw : w = L
        · simp only [hw, if_true, Bool.xor_false]
          exact aff_z4 _ _ _ _ _ _ _ _ _ _ _ (hz i) (hz j)
        · simp only [hw, if_false]; exact hz w
      refine ⟨fun r => Fin.cons (Aw r i, Aw r j) (ℓ' (r, false)),
        fun c => Fin.cons (Bw c i, Bw c j) (m' c),
        fun a b => xor (d && pi2 (a 0) (b 0)) (F' (sh (pi2 (a 0) (b 0)) csh (Fin.tail a)) (Fin.tail b)),
        fun r => A' (r, false), B', ⟨d, csh, F', hF', fun a b => rfl⟩, ?_, ?_, ?_⟩
      · intro r c
        rw [List.foldl_cons, hstep, hout', hsh, hd]
        simp only [Fin.cons_zero, Fin.tail_cons]
        have hπ : pi2 (Aw r i, Aw r j) (Bw c i, Bw c j) = π r c := by
          simp only [pi2, π, hx]
        rw [hπ]
        exact bid3 _ _ _ _ _
      · intro r1 r2 r3 r4 hz k
        refine Fin.cases ?_ (fun k' => ?_) k
        · simp only [Fin.cons_zero]; exact ⟨hz i, hz j⟩
        · simp only [Fin.cons_succ]
          exact hℓ' _ _ _ _ (hz' _ _ _ _ hz) k'
      · intro r1 r2 r3 r4 hz
        exact hA' _ _ _ _ (hz' _ _ _ _ hz)

/-! ## Part D: the switched inner product -/

def dotp (k u v : ℕ) : Bool :=
  ((Finset.univ : Finset (Fin k)).filter (fun i => u.testBit i.val && v.testBit i.val)).card % 2 == 1

def Gf (s : ℕ) (u v : Fin (2 ^ (2 * s))) : Bool :=
  xor (dotp (2 * s) u.val v.val)
    ((u.val.testBit 0 && u.val.testBit 1) && (v.val.testBit 2 && v.val.testBit 3))

lemma parity_flip (k : ℕ) (p q : Fin k → Bool) (j : Fin k) (h : ∀ i, i ≠ j → p i = q i) :
    (((Finset.univ : Finset (Fin k)).filter (fun i => q i = true)).card % 2 == 1) =
    xor (((Finset.univ : Finset (Fin k)).filter (fun i => p i = true)).card % 2 == 1)
      (xor (p j) (q j)) := by
  rw [Finset.card_filter, Finset.card_filter,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hs : ∑ x ∈ Finset.univ.erase j, (if p x = true then 1 else 0) =
      ∑ x ∈ Finset.univ.erase j, (if q x = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i (Finset.ne_of_mem_erase hi)]
  rw [hs]
  generalize ∑ x ∈ Finset.univ.erase j, (if q x = true then 1 else 0) = X
  cases hp : p j <;> cases hq : q j <;> rcases Nat.mod_two_eq_zero_or_one X with hX | hX <;>
    simp [Nat.add_mod, hX]

lemma testBit_flip (v j i : ℕ) : (v ^^^ 2 ^ j).testBit i = xor (v.testBit i) (decide (j = i)) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

lemma dot_flip (k u v j : ℕ) (hj : j < k) :
    dotp k u (v ^^^ 2 ^ j) = xor (dotp k u v) (u.testBit j) := by
  have key := parity_flip k (fun i => u.testBit i.val && v.testBit i.val)
    (fun i => u.testBit i.val && (v ^^^ 2 ^ j).testBit i.val) ⟨j, hj⟩ (by
      intro i hi
      simp only [testBit_flip]
      have : decide (j = i.val) = false := by
        simp only [decide_eq_false_iff_not]; intro h; exact hi (Fin.ext h.symm)
      rw [this, Bool.xor_false])
  beta_reduce at key
  unfold dotp
  rw [key]
  congr 1
  simp only [testBit_flip, decide_true]
  cases u.testBit j <;> cases v.testBit j <;> rfl

def flipP (k j : ℕ) (hj : j < k) : Equiv.Perm (Fin (2 ^ k)) where
  toFun v := ⟨v.val ^^^ 2 ^ j, Nat.xor_lt_two_pow v.isLt (Nat.pow_lt_pow_right (by norm_num) hj)⟩
  invFun v := ⟨v.val ^^^ 2 ^ j, Nat.xor_lt_two_pow v.isLt (Nat.pow_lt_pow_right (by norm_num) hj)⟩
  left_inv v := by ext; simp [Nat.xor_assoc]
  right_inv v := by ext; simp [Nat.xor_assoc]

lemma flipP_val (k j : ℕ) (hj : j < k) (v : Fin (2 ^ k)) :
    (flipP k j hj v).val = v.val ^^^ 2 ^ j := rfl

lemma sum_anti {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → ℤ) (h : ∀ v, f (σ v) = - f v) :
    ∑ v, f v = 0 := by
  have h1 : ∑ v, f (σ v) = ∑ v, f v := Equiv.sum_comp σ f
  simp only [h, Finset.sum_neg_distrib] at h1
  linarith

lemma testBit_high {k : ℕ} (u : Fin (2 ^ k)) {i : ℕ} (hi : k ≤ i) : u.val.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by norm_num) hi))

lemma bool_row (S S' V V' D D' b b' : Bool) (hb : b ≠ b') (hV : S ≠ S' → V' = V) :
    xor (xor (xor D b) (S && V')) (xor (xor D' b') (S' && V')) =
      !(xor (xor D (S && V)) (xor D' (S' && V))) := by
  revert hb hV; revert S S' V V' D D' b b'; decide

lemma row_bal (s : ℕ) (hs : 2 ≤ s) (u u' : Fin (2 ^ (2 * s))) (hne : u ≠ u') :
    ∑ v, chi (xor (Gf s u v) (Gf s u' v)) = 0 := by
  obtain ⟨j, hj, hbit, hsw⟩ : ∃ j, j < 2 * s ∧ u.val.testBit j ≠ u'.val.testBit j ∧
      ((u.val.testBit 0 && u.val.testBit 1) ≠ (u'.val.testBit 0 && u'.val.testBit 1) → j < 2) := by
    by_cases hsw : (u.val.testBit 0 && u.val.testBit 1) = (u'.val.testBit 0 && u'.val.testBit 1)
    · obtain ⟨j, hj⟩ : ∃ j, u.val.testBit j ≠ u'.val.testBit j := by
        by_contra hc; push_neg at hc; exact hne (Fin.ext (Nat.eq_of_testBit_eq hc))
      have hjk : j < 2 * s := by
        by_contra hjk; push_neg at hjk
        exact hj (by rw [testBit_high u hjk, testBit_high u' hjk])
      exact ⟨j, hjk, hj, fun h => absurd hsw h⟩
    · by_cases h0 : u.val.testBit 0 = u'.val.testBit 0
      · refine ⟨1, by omega, ?_, fun _ => by omega⟩
        intro h1; apply hsw; rw [h0, h1]
      · exact ⟨0, by omega, h0, fun _ => by omega⟩
  apply sum_anti (flipP (2 * s) j hj)
  intro v
  rw [← chi_not]
  congr 1
  simp only [Gf, flipP_val, dot_flip _ _ _ _ hj, testBit_flip]
  apply bool_row _ _ _ _ _ _ _ _ hbit
  intro h
  have hj2 := hsw h
  have e2 : decide (j = 2) = false := by simp only [decide_eq_false_iff_not]; omega
  have e3 : decide (j = 3) = false := by simp only [decide_eq_false_iff_not]; omega
  rw [e2, e3, Bool.xor_false, Bool.xor_false]

lemma dot_zero_left (k v : ℕ) : dotp k 0 v = false := by simp [dotp]

lemma dot_zero_right (k u : ℕ) : dotp k u 0 = false := by simp [dotp]

lemma dot_unit_right (k u j : ℕ) (hj : j < k) : dotp k u (2 ^ j) = u.testBit j := by
  have key := parity_flip k (fun _ => false)
    (fun i => u.testBit i.val && (2 ^ j).testBit i.val) ⟨j, hj⟩ (by
      intro i hi
      simp only [Nat.testBit_two_pow]
      have : decide (j = i.val) = false := by
        simp only [decide_eq_false_iff_not]; intro h; exact hi (Fin.ext h.symm)
      rw [this, Bool.and_false])
  beta_reduce at key
  unfold dotp
  rw [key]
  simp [Nat.testBit_two_pow]

lemma dot_unit_left (k v j : ℕ) (hj : j < k) : dotp k (2 ^ j) v = v.testBit j := by
  have key := parity_flip k (fun _ => false)
    (fun i => (2 ^ j).testBit i.val && v.testBit i.val) ⟨j, hj⟩ (by
      intro i hi
      simp only [Nat.testBit_two_pow]
      have : decide (j = i.val) = false := by
        simp only [decide_eq_false_iff_not]; intro h; exact hi (Fin.ext h.symm)
      rw [this, Bool.false_and])
  beta_reduce at key
  unfold dotp
  rw [key]
  simp [Nat.testBit_two_pow]

def zeroF (s : ℕ) : Fin (2 ^ (2 * s)) := ⟨0, by positivity⟩

def unitF (s j : ℕ) (hj : j < 2 * s) : Fin (2 ^ (2 * s)) :=
  ⟨2 ^ j, Nat.pow_lt_pow_right (by norm_num) hj⟩

lemma Gf_zero_left (s : ℕ) (v : Fin (2 ^ (2 * s))) : Gf s (zeroF s) v = false := by
  simp [Gf, zeroF, dot_zero_left]

lemma Gf_zero_right (s : ℕ) (u : Fin (2 ^ (2 * s))) : Gf s u (zeroF s) = false := by
  simp [Gf, zeroF, dot_zero_right]

lemma Gf_unit_left (s j : ℕ) (hj : j < 2 * s) (v : Fin (2 ^ (2 * s))) :
    Gf s (unitF s j hj) v = v.val.testBit j := by
  simp only [Gf, unitF, dot_unit_left _ _ _ hj, Nat.testBit_two_pow]
  have : (decide (j = 0) && decide (j = 1)) = false := by
    by_cases h : j = 0 <;> simp [h]
  rw [this, Bool.false_and, Bool.xor_false]

lemma Gf_unit_right (s j : ℕ) (hj : j < 2 * s) (u : Fin (2 ^ (2 * s))) :
    Gf s u (unitF s j hj) = u.val.testBit j := by
  simp only [Gf, unitF, dot_unit_right _ _ _ hj, Nat.testBit_two_pow]
  have : (decide (j = 2) && decide (j = 3)) = false := by
    by_cases h : j = 2 <;> simp [h]
  rw [this, Bool.and_false, Bool.xor_false]

lemma testBit12 (i : ℕ) : Nat.testBit 12 i = xor (decide (2 = i)) (decide (3 = i)) := by
  have : (12 : ℕ) = 2 ^ 2 ^^^ 2 ^ 3 := by decide
  rw [this, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]

lemma not_closed (s : ℕ) (hs : 2 ≤ s) : ¬ ∃ (u4 : Fin (2 ^ (2 * s))) (c : Bool), ∀ v,
    xor (xor (xor (Gf s (zeroF s) v) (Gf s (unitF s 0 (by omega)) v)) (Gf s (unitF s 1 (by omega)) v))
      (Gf s u4 v) = c := by
  rintro ⟨u4, c, h⟩
  have hc : c = false := by
    have := h (zeroF s)
    simp only [Gf_zero_right, Bool.xor_false] at this
    exact this.symm
  have hbits : ∀ i, i < 2 * s → u4.val.testBit i = xor (decide (0 = i)) (decide (1 = i)) := by
    intro i hi
    have := h (unitF s i hi)
    rw [Gf_zero_left, Gf_unit_right, Gf_unit_right, Gf_unit_right, hc] at this
    simp only [unitF, Nat.testBit_two_pow, Bool.false_xor] at this
    generalize u4.val.testBit i = z at this ⊢
    generalize decide (0 = i) = p at this ⊢
    generalize decide (1 = i) = q at this ⊢
    revert this; revert z p q; decide
  have h12 : (12 : ℕ) < 2 ^ (2 * s) := by
    calc (12 : ℕ) < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := h ⟨12, h12⟩
  rw [Gf_zero_left, Gf_unit_left, Gf_unit_left, hc] at this
  have hdot : dotp (2 * s) u4.val 12 = false := by
    unfold dotp
    have : (Finset.univ.filter (fun i : Fin (2 * s) => u4.val.testBit i.val && Nat.testBit 12 i.val)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro i _
      rw [testBit12, hbits i.val i.isLt]
      generalize i.val = n
      by_cases h2 : n = 2
      · subst h2; decide
      · by_cases h3 : n = 3
        · subst h3; decide
        · have a1 : decide (2 = n) = false := by simp only [decide_eq_false_iff_not]; omega
          have a2 : decide (3 = n) = false := by simp only [decide_eq_false_iff_not]; omega
          rw [a1, a2]; simp
    rw [this]; rfl
  simp only [Gf, hdot, testBit12, hbits 0 (by omega), hbits 1 (by omega)] at this
  revert this; decide

/-! ## Part E: the upper bound construction -/

def xr : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | n+1, f => xor (xr n f) (f n)

lemma xr_congr (n : ℕ) (f g : ℕ → Bool) (h : ∀ i < n, f i = g i) : xr n f = xr n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xr]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]

lemma bx4 (a b c d : Bool) : xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  revert a b c d; decide

lemma xr_xor (n : ℕ) (f g : ℕ → Bool) :
    xr n (fun i => xor (f i) (g i)) = xor (xr n f) (xr n g) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xr, ih]; exact bx4 _ _ _ _

lemma xr_delta (M a : ℕ) (c : ℕ → Bool) :
    xr M (fun w => c w && decide (w = a)) = (decide (a < M) && c a) := by
  induction M with
  | zero => simp [xr]
  | succ M ih =>
    simp only [xr, ih]
    by_cases h : M = a
    · subst h; simp
    · have h1 : decide (a < M + 1) = decide (a < M) := by
        simp only [decide_eq_decide]; omega
      rw [h1]; simp [h]

lemma xr_pairs (n : ℕ) (f : ℕ → Bool) :
    xr n (fun i => xor (f (2 * i)) (f (2 * i + 1))) = xr (2 * n) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [xr, ih]
    rw [Bool.xor_assoc]

lemma xr_card (k : ℕ) (p : ℕ → Bool) :
    xr k p = (((Finset.univ : Finset (Fin k)).filter (fun i => p i.val = true)).card % 2 == 1) := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if p i = true then 1 else 0) k]
  induction k with
  | zero => simp [xr]
  | succ k ih =>
    rw [Finset.sum_range_succ, xr, ih]
    generalize (∑ x ∈ Finset.range k, if p x = true then 1 else 0) = X
    cases hp : p k <;> rcases Nat.mod_two_eq_zero_or_one X with h | h <;> simp [Nat.add_mod, h]

lemma ip_pairs (s : ℕ) (a b : ℕ → Bool) :
    xor (xor (xr s (fun i => a (2 * i) && a (2 * i + 1))) (xr s (fun i => b (2 * i) && b (2 * i + 1))))
      (xr s (fun i => (xor (a (2 * i)) (b (2 * i + 1))) && (xor (a (2 * i + 1)) (b (2 * i))))) =
    xr (2 * s) (fun i => a i && b i) := by
  rw [← xr_xor, ← xr_xor, ← xr_pairs]
  apply xr_congr; intro i _
  generalize a (2 * i) = p; generalize a (2 * i + 1) = p'
  generalize b (2 * i) = q; generalize b (2 * i + 1) = q'
  revert p p' q q'; decide

-- general circuit evaluation lemmas
lemma foldl_len (gs : List Gate) (ys : List Bool) :
    (gs.foldl stepW ys).length = ys.length + gs.length := by
  induction gs generalizing ys with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; ring

lemma foldl_pre (gs : List Gate) (ys : List Bool) (w : ℕ) (hw : w < ys.length) :
    (gs.foldl stepW ys).getD w false = ys.getD w false := by
  induction gs generalizing ys with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp only [stepW]; rw [getD_snoc, if_neg (by omega)]

lemma foldl_snoc_val (gs : List Gate) (g : Gate) (ys : List Bool) :
    ((gs ++ [g]).foldl stepW ys).getD (ys.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stepW ys).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [stepW]; rw [getD_snoc, if_pos (by rw [foldl_len])]

lemma mod2_eval (a b : Bool) : (GateOp.mod 2).eval [a, b] = !(xor a b) := by
  cases a <;> cases b <;> rfl

lemma not_eval (a : Bool) : GateOp.not.eval [a] = !a := rfl

lemma and_eval (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma or_eval1 (a : Bool) : GateOp.or.eval [a] = a := by
  cases a <;> rfl

def cstG (b : Bool) : Gate := ⟨if b then GateOp.and else GateOp.or, []⟩

def lbG (c : ℕ → Bool) (base w : ℕ) : Gate :=
  if c w then ⟨GateOp.mod 2, [base + w, w]⟩ else ⟨GateOp.not, [base + w]⟩

def lb (M : ℕ) (c : ℕ → Bool) (base : ℕ) : ℕ → List Gate
  | 0 => [cstG (M % 2 == 1)]
  | m+1 => lb M c base m ++ [lbG c base m]

lemma lb_len (M : ℕ) (c : ℕ → Bool) (base : ℕ) : ∀ m, (lb M c base m).length = m + 1
  | 0 => rfl
  | m+1 => by simp [lb, lb_len M c base m]

lemma par_succ (m : ℕ) : ((m + 1) % 2 == 1) = !(m % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [Nat.add_mod, h]

lemma lb_val (M : ℕ) (c : ℕ → Bool) (base : ℕ) (y : List Bool) (hy : y.length = base)
    (hM : M ≤ base) : ∀ m, m ≤ M → ((lb M c base m).foldl stepW y).getD (base + m) false =
      xor (xor (M % 2 == 1) (xr m (fun w => c w && y.getD w false))) (m % 2 == 1)
  | 0, _ => by
    simp only [lb, List.foldl_cons, List.foldl_nil, stepW, add_zero]
    rw [getD_snoc, if_pos hy.symm]
    simp only [cstG, xr, Bool.xor_false]
    cases (M % 2 == 1) <;> rfl
  | m+1, hm => by
    have hprev := lb_val M c base y hy hM m (by omega)
    simp only [lb]
    rw [show base + (m + 1) = y.length + (lb M c base m).length by rw [lb_len]; omega]
    rw [foldl_snoc_val]
    have hm' : ((lb M c base m).foldl stepW y).getD m false = y.getD m false :=
      foldl_pre _ _ _ (by omega)
    simp only [lbG]
    rw [par_succ]
    split_ifs with hcm
    · simp only [List.map_cons, List.map_nil, mod2_eval, hprev, hm', xr, hcm, Bool.true_and]
      generalize (M % 2 == 1) = a; generalize xr m (fun w => c w && y.getD w false) = b
      generalize (m % 2 == 1) = d; generalize y.getD m false = e
      revert a b d e; decide
    · simp only [List.map_cons, List.map_nil, not_eval, hprev, xr, hcm, Bool.false_and,
        Bool.xor_false]
      generalize (M % 2 == 1) = a; generalize xr m (fun w => c w && y.getD w false) = b
      generalize (m % 2 == 1) = d
      revert a b d; decide

lemma lb_out (M : ℕ) (c : ℕ → Bool) (base : ℕ) (y : List Bool) (hy : y.length = base)
    (hM : M ≤ base) : ((lb M c base M).foldl stepW y).getD (base + M) false =
      xr M (fun w => c w && y.getD w false) := by
  rw [lb_val M c base y hy hM M le_rfl]
  generalize (M % 2 == 1) = a; generalize xr M (fun w => c w && y.getD w false) = b
  revert a b; decide

def allB (n2 : ℕ) (cf : ℕ → ℕ → Bool) : ℕ → List Gate
  | 0 => []
  | n+1 => allB n2 cf n ++ lb n2 (cf n) (n2 + n * (n2 + 1)) n2

lemma allB_len (n2 : ℕ) (cf : ℕ → ℕ → Bool) : ∀ n, (allB n2 cf n).length = n * (n2 + 1)
  | 0 => by simp [allB]
  | n+1 => by simp only [allB, List.length_append, allB_len n2 cf n, lb_len]; ring

lemma allB_val (n2 : ℕ) (cf : ℕ → ℕ → Bool) (x : List Bool) (hx : x.length = n2) :
    ∀ n, ∀ j < n, ((allB n2 cf n).foldl stepW x).getD (n2 + j * (n2 + 1) + n2) false =
      xr n2 (fun w => cf j w && x.getD w false)
  | 0, j, hj => absurd hj (Nat.not_lt_zero _)
  | n+1, j, hj => by
    simp only [allB]
    rw [List.foldl_append]
    have hlen : ((allB n2 cf n).foldl stepW x).length = n2 + n * (n2 + 1) := by
      rw [foldl_len, allB_len, hx]
    by_cases hjn : j < n
    · rw [foldl_pre _ _ _ (by rw [hlen]; nlinarith)]
      exact allB_val n2 cf x hx n j hjn
    · have hj' : j = n := by omega
      subst hj'
      rw [lb_out _ _ _ _ hlen (by omega)]
      apply xr_congr
      intro w hw
      rw [foldl_pre _ _ _ (by rw [hx]; exact hw)]

def andG (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩
def modG (a b : ℕ) : Gate := ⟨GateOp.mod 2, [a, b]⟩
def notG (a : ℕ) : Gate := ⟨GateOp.not, [a]⟩
def cpyG (a : ℕ) : Gate := ⟨GateOp.or, [a]⟩

def stg (P0 oL : ℕ) (oX oY : ℕ → ℕ) : ℕ → List Gate
  | 0 => [cpyG oL]
  | n+1 => ((stg P0 oL oX oY n ++ [andG (oX n) (oY n)]) ++
      [modG (P0 + 3 * n) (P0 + 3 * n + 1)]) ++ [notG (P0 + 3 * n + 2)]

lemma stg_len (P0 oL : ℕ) (oX oY : ℕ → ℕ) : ∀ n, (stg P0 oL oX oY n).length = 3 * n + 1
  | 0 => rfl
  | n+1 => by
    simp only [stg, List.length_append, stg_len P0 oL oX oY n, List.length_singleton]; omega

lemma stg_val (P0 oL : ℕ) (oX oY : ℕ → ℕ) (y : List Bool) (hy : y.length = P0) (hL : oL < P0) :
    ∀ n, (∀ i < n, oX i < P0 ∧ oY i < P0) →
      ((stg P0 oL oX oY n).foldl stepW y).getD (P0 + 3 * n) false =
        xor (y.getD oL false) (xr n (fun i => y.getD (oX i) false && y.getD (oY i) false))
  | 0, _ => by
    simp only [stg, cpyG, List.foldl_cons, List.foldl_nil, stepW, List.map_cons, List.map_nil,
      or_eval1, mul_zero, add_zero, xr, Bool.xor_false]
    rw [getD_snoc, if_pos hy.symm]
  | n+1, hXY => by
    have hprev := stg_val P0 oL oX oY y hy hL n (fun i hi => hXY i (by omega))
    have hlen0 : ((stg P0 oL oX oY n).foldl stepW y).length = P0 + 3 * n + 1 := by
      rw [foldl_len, stg_len]; omega
    simp only [stg]
    rw [show P0 + 3 * (n + 1) = y.length + ((stg P0 oL oX oY n ++ [andG (oX n) (oY n)]) ++
      [modG (P0 + 3 * n) (P0 + 3 * n + 1)]).length by
        simp only [List.length_append, stg_len, List.length_singleton]; omega]
    rw [foldl_snoc_val]
    simp only [notG, List.map_cons, List.map_nil, not_eval]
    rw [show P0 + 3 * n + 2 = y.length + (stg P0 oL oX oY n ++ [andG (oX n) (oY n)]).length by
        simp only [List.length_append, stg_len, List.length_singleton]; omega]
    rw [foldl_snoc_val]
    simp only [modG, List.map_cons, List.map_nil, mod2_eval]
    rw [List.foldl_append, foldl_pre [andG (oX n) (oY n)] _ (P0 + 3 * n) (by rw [hlen0]; omega)]
    rw [← List.foldl_append]
    rw [show P0 + 3 * n + 1 = y.length + (stg P0 oL oX oY n).length by rw [stg_len]; omega]
    rw [foldl_snoc_val]
    simp only [andG, List.map_cons, List.map_nil, and_eval]
    have hX := (hXY n (by omega)).1
    have hY := (hXY n (by omega)).2
    rw [foldl_pre _ _ (oX n) (by rw [hy]; exact hX), foldl_pre _ _ (oY n) (by rw [hy]; exact hY)]
    rw [hprev]
    simp only [xr]
    generalize y.getD oL false = a
    generalize xr n (fun i => y.getD (oX i) false && y.getD (oY i) false) = b
    generalize y.getD (oX n) false = c; generalize y.getD (oY n) false = d
    revert a b c d; decide

/-! ## Part C: the lower bound -/

lemma oneEach_len (N : ℕ) (u v : Fin N) : (PEqualNP.Represents.oneEach u v).length = N + N := by
  simp [PEqualNP.Represents.oneEach]

lemma oneEach_getD (N : ℕ) (u v : Fin N) (w : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD w false =
      xor (decide (w = u.val)) (decide (w = N + v.val)) := by
  unfold PEqualNP.Represents.oneEach
  by_cases h1 : w < N
  · rw [List.getD_append _ _ _ _ (by simp; exact h1), List.getD_eq_getElem _ _ (by simp; exact h1),
      List.getElem_ofFn]
    have : decide (w = N + v.val) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [this, Bool.xor_false]
    simp only [decide_eq_decide, Fin.ext_iff]
  · by_cases h2 : w < N + N
    · rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      have : decide (w = u.val) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [this, Bool.false_xor]
      simp only [decide_eq_decide, Fin.ext_iff, List.length_ofFn]
      constructor <;> intro h <;> omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : decide (w = u.val) = false := by simp only [decide_eq_false_iff_not]; omega
      have h4 : decide (w = N + v.val) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [h3, h4]; rfl

lemma bc1 (a1 a2 b f : Bool) : xor (xor (xor a1 b) f) (xor (xor a2 b) f) = xor a1 a2 := by
  revert a1 a2 b f; decide

lemma bc2 (a b1 b2 f : Bool) : xor (xor (xor a b1) f) (xor (xor a b2) f) = xor b1 b2 := by
  revert a b1 b2 f; decide

lemma bc3 (a1 a2 b f1 f2 : Bool) :
    xor f1 f2 = xor (xor a1 a2) (xor (xor (xor a1 b) f1) (xor (xor a2 b) f2)) := by
  revert a1 a2 b f1 f2; decide

lemma bc4 (a1 a2 a3 a4 b f1 f2 f3 f4 : Bool) :
    xor (xor (xor (xor (xor a1 b) f1) (xor (xor a2 b) f2)) (xor (xor a3 b) f3)) (xor (xor a4 b) f4) =
      xor (xor (xor (xor f1 f2) f3) f4) (xor (xor (xor a1 a2) a3) a4) := by
  revert a1 a2 a3 a4 b f1 f2 f3 f4; decide

theorem lower (s : ℕ) (hs : 2 ≤ s) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrep : PEqualNP.Represents.Represents (Gf s) C) :
    s + 1 ≤ C.gates.countP nl := by
  obtain ⟨ℓ, m, F, A, B, hF, hout, -, -⟩ := extract C.output C.gates hfan _ rfl
    (Fin (2 ^ (2 * s))) (2 ^ (2 * s) + 2 ^ (2 * s))
    (fun u v => PEqualNP.Represents.oneEach u v) (fun u w => decide (w = u.val))
    (fun v w => decide (w = 2 ^ (2 * s) + v.val))
    (fun u v => oneEach_len _ u v) (fun u v w => oneEach_getD _ u v w)
  have hG : ∀ u v, Gf s u v = xor (xor (A u) (B v)) (F (ℓ u) (m v)) := by
    intro u v; rw [← hrep u v]; exact hout u v
  have hpos : (0 : ℤ) < 2 ^ (2 * s) := by positivity
  have hℓ : Function.Injective ℓ := by
    intro u u' h
    by_contra hne
    have hb := row_bal s hs u u' hne
    have hconst : ∀ v, xor (Gf s u v) (Gf s u' v) = xor (A u) (A u') := by
      intro v; rw [hG, hG, h]; exact bc1 _ _ _ _
    simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
    generalize xor (A u) (A u') = z at hb
    cases z <;> simp [chi] at hb <;> push_cast at hb <;> linarith
  have hm : Function.Injective m := by
    intro v v' h
    by_contra hne
    have hc : ∀ u, xor (Gf s u v) (Gf s u v') = xor (B v) (B v') := by
      intro u; rw [hG, hG, h]; exact bc2 _ _ _ _
    obtain ⟨j, hj⟩ : ∃ j, v.val.testBit j ≠ v'.val.testBit j := by
      by_contra hc'; push_neg at hc'; exact hne (Fin.ext (Nat.eq_of_testBit_eq hc'))
    have hjk : j < 2 * s := by
      by_contra hjk; push_neg at hjk
      exact hj (by rw [testBit_high v hjk, testBit_high v' hjk])
    have h0 := hc (zeroF s)
    have h1 := hc (unitF s j hjk)
    rw [Gf_zero_left, Gf_zero_left] at h0
    rw [Gf_unit_left, Gf_unit_left, ← h0] at h1
    apply hj
    revert h1
    generalize v.val.testBit j = p; generalize v'.val.testBit j = q
    revert p q; decide
  have hcard := Fintype.card_le_of_injective ℓ hℓ
  rw [Fintype.card_fin, card_lab] at hcard
  have h4 : (2 : ℕ) ^ (2 * s) = 4 ^ s := by rw [pow_mul]; norm_num
  rw [h4] at hcard
  have hst : s ≤ C.gates.countP nl := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  by_contra hlt
  have ht : C.gates.countP nl = s := by omega
  have hcardeq : Fintype.card (Fin (2 ^ (2 * s))) = Fintype.card (Lab (C.gates.countP nl)) := by
    rw [Fintype.card_fin, card_lab, ht, h4]
  have hℓb : Function.Bijective ℓ :=
    (Fintype.bijective_iff_injective_and_card ℓ).mpr ⟨hℓ, hcardeq⟩
  have hmb : Function.Bijective m :=
    (Fintype.bijective_iff_injective_and_card m).mpr ⟨hm, hcardeq⟩
  have hRH : RowHad F := by
    intro a a' hne
    obtain ⟨u, rfl⟩ := hℓb.2 a
    obtain ⟨u', rfl⟩ := hℓb.2 a'
    have hne' : u ≠ u' := fun h => hne (by rw [h])
    rw [← Fintype.sum_bijective m hmb (fun v => chi (xor (F (ℓ u) (m v)) (F (ℓ u') (m v))))
      (fun b => chi (xor (F (ℓ u) b) (F (ℓ u') b))) (fun _ => rfl)]
    have : ∀ v, chi (xor (F (ℓ u) (m v)) (F (ℓ u') (m v))) =
        chi (xor (A u) (A u')) * chi (xor (Gf s u v) (Gf s u' v)) := by
      intro v; rw [← chi_xor, hG u v, hG u' v]; congr 1; exact bc3 _ _ _ _ _
    simp only [this, ← Finset.mul_sum, row_bal s hs u u' hne', mul_zero]
  have hcl := had_closed _ F hF hRH
  obtain ⟨a4, c, h4c⟩ := hcl (ℓ (zeroF s)) (ℓ (unitF s 0 (by omega))) (ℓ (unitF s 1 (by omega)))
  obtain ⟨u4, rfl⟩ := hℓb.2 a4
  apply not_closed s hs
  refine ⟨u4, xor c (xor (xor (xor (A (zeroF s)) (A (unitF s 0 (by omega))))
    (A (unitF s 1 (by omega)))) (A u4)), fun v => ?_⟩
  rw [hG (zeroF s) v, hG (unitF s 0 (by omega)) v, hG (unitF s 1 (by omega)) v, hG u4 v,
    ← h4c (m v)]
  exact bc4 _ _ _ _ _ _ _ _ _

/-! ## Part F: correctness of the upper bound circuit -/

def lfU (s j w : ℕ) : Bool :=
  if j < 2 * s then w.testBit j
  else if j = 2 * s then (w.testBit 0 && w.testBit 1)
  else if j = 2 * s + 1 then false
  else xr s (fun i => w.testBit (2 * i) && w.testBit (2 * i + 1))

def partner (j : ℕ) : ℕ := if j % 2 = 0 then j + 1 else j - 1

def lfV (s j w : ℕ) : Bool :=
  if j < 2 * s then w.testBit (partner j)
  else if j = 2 * s then false
  else if j = 2 * s + 1 then (w.testBit 2 && w.testBit 3)
  else xr s (fun i => w.testBit (2 * i) && w.testBit (2 * i + 1))

def lf (s N j w : ℕ) : Bool := if w < N then lfU s j w else lfV s j (w - N)

def oW (n2 j : ℕ) : ℕ := n2 + j * (n2 + 1) + n2

def upC (s : ℕ) : Circuit :=
  ⟨allB (2 ^ (2 * s) + 2 ^ (2 * s)) (lf s (2 ^ (2 * s))) (2 * s + 3) ++
    stg ((2 ^ (2 * s) + 2 ^ (2 * s)) + (2 * s + 3) * ((2 ^ (2 * s) + 2 ^ (2 * s)) + 1))
      (oW (2 ^ (2 * s) + 2 ^ (2 * s)) (2 * s + 2))
      (fun i => oW (2 ^ (2 * s) + 2 ^ (2 * s)) (2 * i))
      (fun i => oW (2 ^ (2 * s) + 2 ^ (2 * s)) (2 * i + 1)) (s + 1),
   (2 ^ (2 * s) + 2 ^ (2 * s)) + (2 * s + 3) * ((2 ^ (2 * s) + 2 ^ (2 * s)) + 1) + 3 * (s + 1)⟩

lemma onehot_xr (s N j : ℕ) (u v : Fin N) :
    xr (N + N) (fun w => lf s N j w && (PEqualNP.Represents.oneEach u v).getD w false) =
      xor (lfU s j u.val) (lfV s j v.val) := by
  simp only [oneEach_getD, Bool.and_xor_distrib_left]
  rw [xr_xor, xr_delta, xr_delta]
  have h1 : decide (u.val < N + N) = true := by simp only [decide_eq_true_eq]; omega
  have h2 : decide (N + v.val < N + N) = true := by simp only [decide_eq_true_eq]; omega
  rw [h1, h2, Bool.true_and, Bool.true_and]
  have h3 : ¬ (N + v.val < N) := by omega
  simp only [lf, if_pos u.isLt, if_neg h3, Nat.add_sub_cancel_left]

def RBL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma RBL_nil (n : ℕ) : RBL n [] := by intro j hj; simp at hj

lemma RBL_append (n : ℕ) (gs gs' : List Gate) (h1 : RBL n gs) (h2 : RBL (n + gs.length) gs') :
    RBL n (gs ++ gs') := by
  intro j hj i hi
  by_cases hjl : j < gs.length
  · rw [List.getD_append _ _ _ _ hjl] at hi; exact h1 j hjl i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    have := h2 (j - gs.length) (by simp only [List.length_append] at hj; omega) i hi
    omega

lemma RBL_single (n : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < n) : RBL n [g] := by
  intro j hj i hi
  simp only [List.length_singleton] at hj
  have : j = 0 := by omega
  subst this
  simp only [List.getD_cons_zero] at hi
  have := h i hi; omega

lemma lb_RBL (M : ℕ) (c : ℕ → Bool) (base : ℕ) : ∀ m, RBL base (lb M c base m)
  | 0 => RBL_single _ _ (by simp [cstG])
  | m+1 => by
    simp only [lb]
    apply RBL_append _ _ _ (lb_RBL M c base m)
    apply RBL_single
    rw [lb_len]
    intro i hi
    simp only [lbG] at hi
    split_ifs at hi <;> simp at hi <;> omega

lemma allB_RBL (n2 : ℕ) (cf : ℕ → ℕ → Bool) : ∀ n, RBL n2 (allB n2 cf n)
  | 0 => RBL_nil _
  | n+1 => by
    simp only [allB]
    apply RBL_append _ _ _ (allB_RBL n2 cf n)
    rw [allB_len]; exact lb_RBL _ _ _ _

lemma stg_RBL (P0 oL : ℕ) (oX oY : ℕ → ℕ) (hL : oL < P0) :
    ∀ n, (∀ i < n, oX i < P0 ∧ oY i < P0) → RBL P0 (stg P0 oL oX oY n)
  | 0, _ => RBL_single _ _ (by simp [cpyG]; exact hL)
  | n+1, hXY => by
    simp only [stg]
    have hX := (hXY n (by omega)).1
    have hY := (hXY n (by omega)).2
    refine RBL_append _ _ _ (RBL_append _ _ _ (RBL_append _ _ _
      (stg_RBL P0 oL oX oY hL n (fun i hi => hXY i (by omega))) ?_) ?_) ?_
    · apply RBL_single
      simp only [andG, List.mem_cons, List.mem_nil_iff, or_false]
      rintro i (rfl | rfl) <;> omega
    · apply RBL_single
      simp only [modG, List.length_append, stg_len, List.length_singleton, List.mem_cons,
        List.mem_nil_iff, or_false]
      rintro i (rfl | rfl) <;> omega
    · apply RBL_single
      simp only [notG, List.length_append, stg_len, List.length_singleton, List.mem_cons,
        List.mem_nil_iff, or_false]
      rintro i rfl; omega

lemma lb_fan (M : ℕ) (c : ℕ → Bool) (base : ℕ) :
    ∀ m, ∀ g ∈ lb M c base m, g.inputs.length ≤ 2 ∧ nl g = false
  | 0 => by
    intro g hg
    simp only [lb, List.mem_singleton] at hg
    subst hg; exact ⟨by simp [cstG], rfl⟩
  | m+1 => by
    intro g hg
    simp only [lb, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact lb_fan M c base m g hg
    · subst hg; unfold lbG; split_ifs
      · exact ⟨by simp, rfl⟩
      · exact ⟨by simp, rfl⟩

lemma allB_fan (n2 : ℕ) (cf : ℕ → ℕ → Bool) :
    ∀ n, ∀ g ∈ allB n2 cf n, g.inputs.length ≤ 2 ∧ nl g = false
  | 0 => by intro g hg; simp [allB] at hg
  | n+1 => by
    intro g hg
    simp only [allB, List.mem_append] at hg
    rcases hg with hg | hg
    · exact allB_fan n2 cf n g hg
    · exact lb_fan _ _ _ _ g hg

lemma stg_fan (P0 oL : ℕ) (oX oY : ℕ → ℕ) :
    ∀ n, (∀ g ∈ stg P0 oL oX oY n, g.inputs.length ≤ 2) ∧ (stg P0 oL oX oY n).countP nl = n
  | 0 => by
    refine ⟨?_, ?_⟩
    · intro g hg; simp only [stg, List.mem_singleton] at hg; subst hg; simp [cpyG]
    · rfl
  | n+1 => by
    obtain ⟨h1, h2⟩ := stg_fan P0 oL oX oY n
    refine ⟨?_, ?_⟩
    · intro g hg
      simp only [stg, List.mem_append, List.mem_singleton] at hg
      rcases hg with ((hg | rfl) | rfl) | rfl
      · exact h1 g hg
      · simp [andG]
      · simp [modG]
      · simp [notG]
    · have e1 : nl (andG (oX n) (oY n)) = true := rfl
      have e2 : nl (modG (P0 + 3 * n) (P0 + 3 * n + 1)) = false := rfl
      have e3 : nl (notG (P0 + 3 * n + 2)) = false := rfl
      simp only [stg, List.countP_append, h2, List.countP_cons, List.countP_nil, e1, e2, e3]
      simp

lemma xr_succ (n : ℕ) (f : ℕ → Bool) : xr (n + 1) f = xor (xr n f) (f n) := rfl

lemma dotp_xr (k u v : ℕ) : dotp k u v = xr k (fun i => u.testBit i && v.testBit i) := by
  rw [xr_card]; rfl

theorem upper (s : ℕ) (hs : 2 ≤ s) :
    (∀ g ∈ (upC s).gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 ^ (2 * s) + 2 ^ (2 * s)) (upC s) ∧
    PEqualNP.Represents.Represents (Gf s) (upC s) ∧
    (upC s).gates.countP nl = s + 1 := by
  have hoW : ∀ j, j < 2 * s + 3 → oW (2 ^ (2 * s) + 2 ^ (2 * s)) j <
      (2 ^ (2 * s) + 2 ^ (2 * s)) + (2 * s + 3) * ((2 ^ (2 * s) + 2 ^ (2 * s)) + 1) := by
    intro j hj
    simp only [oW]
    have : j * (2 ^ (2 * s) + 2 ^ (2 * s) + 1) + (2 ^ (2 * s) + 2 ^ (2 * s) + 1) ≤
        (2 * s + 3) * (2 ^ (2 * s) + 2 ^ (2 * s) + 1) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    omega
  have hXY : ∀ i < s + 1, oW (2 ^ (2 * s) + 2 ^ (2 * s)) (2 * i) <
      (2 ^ (2 * s) + 2 ^ (2 * s)) + (2 * s + 3) * ((2 ^ (2 * s) + 2 ^ (2 * s)) + 1) ∧
      oW (2 ^ (2 * s) + 2 ^ (2 * s)) (2 * i + 1) <
      (2 ^ (2 * s) + 2 ^ (2 * s)) + (2 * s + 3) * ((2 ^ (2 * s) + 2 ^ (2 * s)) + 1) :=
    fun i hi => ⟨hoW _ (by omega), hoW _ (by omega)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [upC, List.mem_append] at hg
    rcases hg with hg | hg
    · exact (allB_fan _ _ _ g hg).1
    · exact (stg_fan _ _ _ _ _).1 g hg
  · intro j hj i hi
    exact RBL_append (2 ^ (2 * s) + 2 ^ (2 * s)) _ _ (allB_RBL _ (lf s (2 ^ (2 * s))) (2 * s + 3))
      (by rw [allB_len]; exact stg_RBL _ _ _ _ (hoW _ (by omega)) (s + 1) hXY) j hj i hi
  · intro u v
    show ((upC s).gates.foldl stepW (PEqualNP.Represents.oneEach u v)).getD (upC s).output false
      = Gf s u v
    simp only [upC]
    rw [List.foldl_append]
    have hx : (PEqualNP.Represents.oneEach u v).length = 2 ^ (2 * s) + 2 ^ (2 * s) :=
      oneEach_len _ u v
    have hY : ((allB (2 ^ (2 * s) + 2 ^ (2 * s)) (lf s (2 ^ (2 * s))) (2 * s + 3)).foldl stepW
        (PEqualNP.Represents.oneEach u v)).length =
        (2 ^ (2 * s) + 2 ^ (2 * s)) + (2 * s + 3) * ((2 ^ (2 * s) + 2 ^ (2 * s)) + 1) := by
      rw [foldl_len, allB_len, hx]
    rw [stg_val _ _ _ _ _ hY (hoW (2 * s + 2) (by omega)) (s + 1) hXY]
    have hblk : ∀ j < 2 * s + 3,
        ((allB (2 ^ (2 * s) + 2 ^ (2 * s)) (lf s (2 ^ (2 * s))) (2 * s + 3)).foldl stepW
          (PEqualNP.Represents.oneEach u v)).getD (oW (2 ^ (2 * s) + 2 ^ (2 * s)) j) false =
        xor (lfU s j u.val) (lfV s j v.val) := by
      intro j hj
      rw [oW, allB_val _ (lf s (2 ^ (2 * s))) _ hx (2 * s + 3) j hj, onehot_xr]
    have e1 : ∀ i < s, lfU s (2 * i) u.val = u.val.testBit (2 * i) := by
      intro i hi; simp only [lfU, if_pos (show 2 * i < 2 * s by omega)]
    have e2 : ∀ i < s, lfV s (2 * i) v.val = v.val.testBit (2 * i + 1) := by
      intro i hi
      simp only [lfV, partner, if_pos (show 2 * i < 2 * s by omega),
        if_pos (show 2 * i % 2 = 0 by omega)]
    have e3 : ∀ i < s, lfU s (2 * i + 1) u.val = u.val.testBit (2 * i + 1) := by
      intro i hi; simp only [lfU, if_pos (show 2 * i + 1 < 2 * s by omega)]
    have e4 : ∀ i < s, lfV s (2 * i + 1) v.val = v.val.testBit (2 * i) := by
      intro i hi
      simp only [lfV, partner, if_pos (show 2 * i + 1 < 2 * s by omega),
        if_neg (show ¬ ((2 * i + 1) % 2 = 0) by omega), Nat.add_sub_cancel]
    have f1 : lfU s (2 * s + 2) u.val =
        xr s (fun i => u.val.testBit (2 * i) && u.val.testBit (2 * i + 1)) := by
      simp only [lfU, if_neg (show ¬ (2 * s + 2 < 2 * s) by omega),
        if_neg (show ¬ (2 * s + 2 = 2 * s) by omega), if_neg (show ¬ (2 * s + 2 = 2 * s + 1) by omega)]
    have f2 : lfV s (2 * s + 2) v.val =
        xr s (fun i => v.val.testBit (2 * i) && v.val.testBit (2 * i + 1)) := by
      simp only [lfV, if_neg (show ¬ (2 * s + 2 < 2 * s) by omega),
        if_neg (show ¬ (2 * s + 2 = 2 * s) by omega), if_neg (show ¬ (2 * s + 2 = 2 * s + 1) by omega)]
    have f3 : lfU s (2 * s) u.val = (u.val.testBit 0 && u.val.testBit 1) := by
      simp only [lfU, if_neg (show ¬ (2 * s < 2 * s) by omega), if_true]
    have f4 : lfV s (2 * s) v.val = false := by
      simp only [lfV, if_neg (show ¬ (2 * s < 2 * s) by omega), if_true]
    have f5 : lfU s (2 * s + 1) u.val = false := by
      simp only [lfU, if_neg (show ¬ (2 * s + 1 < 2 * s) by omega),
        if_neg (show ¬ (2 * s + 1 = 2 * s) by omega), if_true]
    have f6 : lfV s (2 * s + 1) v.val = (v.val.testBit 2 && v.val.testBit 3) := by
      simp only [lfV, if_neg (show ¬ (2 * s + 1 < 2 * s) by omega),
        if_neg (show ¬ (2 * s + 1 = 2 * s) by omega), if_true]
    have hX : xr (s + 1) (fun i =>
        ((allB (2 ^ (2 * s) + 2 ^ (2 * s)) (lf s (2 ^ (2 * s))) (2 * s + 3)).foldl stepW
          (PEqualNP.Represents.oneEach u v)).getD (oW (2 ^ (2 * s) + 2 ^ (2 * s)) (2 * i)) false &&
        ((allB (2 ^ (2 * s) + 2 ^ (2 * s)) (lf s (2 ^ (2 * s))) (2 * s + 3)).foldl stepW
          (PEqualNP.Represents.oneEach u v)).getD (oW (2 ^ (2 * s) + 2 ^ (2 * s)) (2 * i + 1)) false)
        = xor (xr s (fun i => xor (u.val.testBit (2 * i)) (v.val.testBit (2 * i + 1)) &&
            xor (u.val.testBit (2 * i + 1)) (v.val.testBit (2 * i))))
          ((u.val.testBit 0 && u.val.testBit 1) && (v.val.testBit 2 && v.val.testBit 3)) := by
      rw [xr_succ]
      congr 1
      · apply xr_congr
        intro i hi
        rw [hblk (2 * i) (by omega), hblk (2 * i + 1) (by omega), e1 i hi, e2 i hi, e3 i hi, e4 i hi]
      · rw [hblk (2 * s) (by omega), hblk (2 * s + 1) (by omega), f3, f4, f5, f6, Bool.xor_false,
          Bool.false_xor]
    rw [hX, hblk (2 * s + 2) (by omega), f1, f2, ← Bool.xor_assoc,
      ip_pairs s u.val.testBit v.val.testBit]
    simp only [Gf, dotp_xr]
  · simp only [upC, List.countP_append, (stg_fan _ _ _ _ _).2]
    have : (allB (2 ^ (2 * s) + 2 ^ (2 * s)) (lf s (2 ^ (2 * s))) (2 * s + 3)).countP nl = 0 := by
      rw [List.countP_eq_zero]
      intro g hg
      simp [(allB_fan _ _ _ g hg).2]
    rw [this, zero_add]

end PEqualNP.Outside.L_meta_25664_aux

theorem PEqualNP.Outside.L_meta_25664 : ∀ s : ℕ, 2 ≤ s →
  let k := 2 * s
  let N := 2 ^ k
  let G := fun (u v : Fin N) =>
    let parity := ((Finset.univ : Finset (Fin k)).filter (fun i =>
      u.val.testBit i.val && v.val.testBit i.val)).card % 2 == 1
    xor parity ((u.val.testBit 0 && u.val.testBit 1) &&
      (v.val.testBit 2 && v.val.testBit 3))
  let represents := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C ∧
    PEqualNP.Represents.Represents G C
  let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) => C.gates.countP (fun g =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
  (∀ C, represents C → s + 1 ≤ cost C) ∧ ∃ C, represents C ∧ cost C = s + 1 := by
  intro s hs
  refine ⟨fun C hC => ?_, ⟨PEqualNP.Outside.L_meta_25664_aux.upC s, ?_, ?_⟩⟩
  · obtain ⟨h1, _, h3⟩ := hC
    exact PEqualNP.Outside.L_meta_25664_aux.lower s hs C h1 h3
  · obtain ⟨h1, h2, h3, _⟩ := PEqualNP.Outside.L_meta_25664_aux.upper s hs
    exact ⟨h1, h2, h3⟩
  · exact (PEqualNP.Outside.L_meta_25664_aux.upper s hs).2.2.2
