import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41629_aux

def ixf (k : ℕ) (hk : 0 < k) (i : ℕ) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

def addf (k : ℕ) (u v : Fin k → Bool) (i : Fin k) : Bool := xor (u i) (v i)

def mixf (k : ℕ) (hk : 0 < k) (d : ℕ) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x (ixf k hk (i.val+k-d % k))) (xor (x i) (x (ixf k hk (i.val+d))))

def rotf (k : ℕ) (hk : 0 < k) (a : ℕ) (x : Fin k → Bool) (i : Fin k) : Bool :=
  x (ixf k hk (i.val+k-a % k))

def chif (k : ℕ) (hk : 0 < k) (r : Fin k → Bool) (i : Fin k) : Bool :=
  xor (r i) (!(r (ixf k hk (i.val+1))) && r (ixf k hk (i.val+2)))

def rowf (k : ℕ) (hk : 0 < k) (name x : Fin k → Bool) : Fin k → Bool :=
  addf k (chif k hk (mixf k hk 1 (addf k name (rotf k hk 1 x)))) x

def tgt (k : ℕ) (i : Fin k) : Bool :=
  if k = 2 then decide (i.val = 1) else decide (1 + (k-1) % 3 ≤ i.val)

def PairB (k : ℕ) (hk : 0 < k) : Prop :=
  ∃ v : Fin k → Bool, (∀ i : Fin k, mixf k hk 1 v i = tgt k i) ∧
    ∀ u : Fin k → Bool, Function.Injective (fun x : Fin k → Bool => (rowf k hk u x, rowf k hk (addf k u v) x))

def win (G : ℕ → Bool) (n : ℕ) : Bool := xor (G n) (xor (G (n+1)) (G (n+2)))

def rowR (R : ℕ → Bool) (n : ℕ) : Bool := xor (R n) (!(R (n+1)) && R (n+2))

def gfun (p q b c : Bool) : Bool := xor c (xor (p && c) (xor (b && q) (b && c)))

def Gf (k : ℕ) (hk : 0 < k) (name x : Fin k → Bool) (j : ℕ) : Bool :=
  xor (name (ixf k hk (j + (k-1)))) (x (ixf k hk (j + (k-1) + (k-1))))

/-! Boolean identities -/

theorem gff (p q : Bool) : gfun p q false false = false := by cases p <;> cases q <;> rfl
theorem gtf (p q : Bool) : gfun p q true false = q := by cases p <;> cases q <;> rfl
theorem gft (p q : Bool) : gfun p q false true = !p := by cases p <;> cases q <;> rfl
theorem gtt (p q : Bool) : gfun p q true true = xor p q := by cases p <;> cases q <;> rfl

theorem bool1 : ∀ a a' p q p' q' n0 n1 n2 : Bool,
    xor (xor a (!p && q)) (xor a' (!p' && q')) =
      xor (xor (xor a n0) (!(xor p n1) && xor q n2)) (xor (xor a' n0) (!(xor p' n1) && xor q' n2)) →
    (n1 && xor q q') = (xor p p' && n2) := by decide

theorem bool2 : ∀ a a' p q p' q' f : Bool,
    xor (xor a (!p && q)) (xor a' (!p' && q')) = f →
    f = xor (xor a a') (gfun p q (xor p p') (xor q q')) := by decide

theorem bool3 : ∀ A A' X X' U : Bool, xor A X = xor A' X' → xor A A' = xor (xor U X) (xor U X') := by
  decide

theorem bool_winshift : ∀ a b c d : Bool, xor b (xor c d) = xor a (xor b c) → d = a := by decide

theorem bool_winxor : ∀ a b c d e f : Bool,
    xor (xor a (xor b c)) (xor d (xor e f)) = xor (xor a d) (xor (xor b e) (xor c f)) := by decide

theorem bool_winxor' : ∀ a b c d e f : Bool,
    xor (xor a d) (xor (xor b e) (xor c f)) = xor (xor a (xor b c)) (xor d (xor e f)) := by decide

theorem bool_x3 : ∀ a b c : Bool, xor (xor a b) c = xor (xor a c) b := by decide

theorem bool_eq : ∀ a b : Bool, xor a b = false → a = b := by decide

theorem bool_cancel : ∀ a b c : Bool, xor a b = xor a c → b = c := by decide

theorem bool_ne : ∀ b : Bool, b ≠ !b := by decide

/-! Sequences indexed by naturals -/

theorem win_shift (P : ℕ → Bool) (j : ℕ) (h : win P (j+1) = win P j) : P (j+3) = P j :=
  bool_winshift (P j) (P (j+1)) (P (j+2)) (P (j+3)) h

theorem win_per (P : ℕ → Bool) (k : ℕ) (hP : ∀ n, P (n+k) = P n) (n : ℕ) :
    win P (n+k) = win P n := by
  unfold win
  rw [hP n, show n + k + 1 = (n+1) + k by omega, hP, show n + k + 2 = (n+2) + k by omega, hP]

theorem win_xor (P Q : ℕ → Bool) (n : ℕ) :
    win (fun j => xor (P j) (Q j)) n = xor (win P n) (win Q n) :=
  bool_winxor' (P n) (P (n+1)) (P (n+2)) (Q n) (Q (n+1)) (Q (n+2))

theorem per_mod (P : ℕ → Bool) (k : ℕ) (hP : ∀ n, P (n+k) = P n) (n : ℕ) : P n = P (n % k) := by
  have key : ∀ t a, P (a + k * t) = P a := by
    intro t
    induction t with
    | zero => intro a; simp
    | succ t ih => intro a; rw [Nat.mul_succ, ← Nat.add_assoc, hP, ih]
  conv_lhs => rw [← Nat.mod_add_div n k]
  exact key _ _

theorem prop3 (P : ℕ → Bool) (a b : ℕ) (h : ∀ j, a ≤ j → j + 3 ≤ b → P (j+3) = P j) :
    ∀ t s, a ≤ s → s + 3 * t ≤ b → P (s + 3 * t) = P s := by
  intro t
  induction t with
  | zero => intro s _ _; simp
  | succ t ih =>
    intro s hs hb
    rw [show s + 3 * (t+1) = (s + 3*t) + 3 by ring, h _ (by omega) (by omega), ih s hs (by omega)]

/-! Small widths -/

theorem h1pos : 0 < 1 := by norm_num
theorem h2pos : 0 < 2 := by norm_num
theorem h3pos : 0 < 3 := by norm_num

theorem k1dec : ∀ a : Bool, ∀ i : Fin 1,
    rowf 1 h1pos (fun _ => a) (fun _ => false) i = rowf 1 h1pos (fun _ => a) (fun _ => true) i := by
  decide

theorem k3dec : ∀ a b c : Bool, ∀ i : Fin 3,
    rowf 3 h3pos (fun i : Fin 3 => if i.val = 0 then a else if i.val = 1 then b else c) (fun _ => false) i =
      rowf 3 h3pos (fun i : Fin 3 => if i.val = 0 then a else if i.val = 1 then b else c)
        (fun _ => true) i := by
  decide

theorem k2dec : ∀ a b c d e f : Bool,
    (∀ i : Fin 2, rowf 2 h2pos (fun i : Fin 2 => if i.val = 0 then a else b)
        (fun i : Fin 2 => if i.val = 0 then c else d) i =
      rowf 2 h2pos (fun i : Fin 2 => if i.val = 0 then a else b)
        (fun i : Fin 2 => if i.val = 0 then e else f) i) →
    (∀ i : Fin 2, rowf 2 h2pos (addf 2 (fun i : Fin 2 => if i.val = 0 then a else b)
          (fun i : Fin 2 => decide (i.val = 1)))
        (fun i : Fin 2 => if i.val = 0 then c else d) i =
      rowf 2 h2pos (addf 2 (fun i : Fin 2 => if i.val = 0 then a else b)
          (fun i : Fin 2 => decide (i.val = 1)))
        (fun i : Fin 2 => if i.val = 0 then e else f) i) →
    c = e ∧ d = f := by
  decide

theorem k2mix : ∀ i : Fin 2, mixf 2 h2pos 1 (fun i : Fin 2 => decide (i.val = 1)) i = tgt 2 i := by
  decide

/-! The cyclic argument on sequences indexed by naturals -/

theorem bl_b1 : ∀ a b c d : Bool, d = a → xor a (xor b c) = false → xor b (xor c d) = false := by
  decide

theorem bl_m1 : ∀ a b r : Bool, a = xor true r → b = xor true (!r) → a = b → False := by decide

theorem bl_m2 : ∀ a b c : Bool, a = c → xor a (xor b c) = false → b = xor true false → False := by
  decide

theorem bl3 : ∀ a b c : Bool, xor a (xor b c) = false → b = true → c = false → a = true := by decide

theorem bl4 : ∀ a b c : Bool, xor a (xor b c) = false → a = false → b = true → c = true := by decide

theorem bl5 : ∀ a b c : Bool, xor a (xor b c) = true → a = true → b = true → c = true := by decide

theorem bl6 : ∀ f b1 b2 b3 r2 r3 : Bool, f = xor b1 (gfun r2 r3 b2 b3) → b1 = false → b2 = false →
    b3 = true → f = true → r2 = false := by decide

theorem bl7 : ∀ f b2 b3 b4 r3 r4 : Bool, f = xor b2 (gfun r3 r4 b3 b4) → b2 = false → b3 = true →
    b4 = true → f = true → xor r3 r4 = true := by decide

theorem bl8 : ∀ f b0 b1 b2 r1 r2 : Bool, f = xor b0 (gfun r1 r2 b1 b2) → b0 = true → b1 = true →
    b2 = true → f = true → r2 = r1 := by decide

theorem bl9 : ∀ f b0 b1 b2 r1 r2 : Bool, f = xor b0 (gfun r1 r2 b1 b2) → b0 = true → b1 = true →
    b2 = false → f = true → r2 = false := by decide

theorem bl10 : ∀ g0 g1 g2 g3 g4 g5 g6 : Bool, g4 = g1 → g6 = g0 → xor g0 (xor g1 g2) = false →
    xor g2 (xor g3 g4) = false → xor (xor g3 (xor g4 g5)) (xor g4 (xor g5 g6)) = true → False := by
  decide

theorem core2 (k : ℕ) (hk4 : 4 ≤ k) (F B R G N : ℕ → Bool)
    (hF : ∀ n, F (n + k) = F n) (hB : ∀ n, B (n + k) = B n) (hR : ∀ n, R (n + k) = R n)
    (hG : ∀ n, G (n + k) = G n)
    (hN : ∀ n, N n = decide (1 + (k-1) % 3 ≤ n % k))
    (hBF : ∀ n, B n = win F n) (hRG : ∀ n, R n = win G n)
    (S1 : ∀ n, (N (n+1) && B (n+2)) = (B (n+1) && N (n+2)))
    (H : ∀ n, F (n+2) = xor (B n) (gfun (R (n+1)) (R (n+2)) (B (n+1)) (B (n+2)))) :
    ∀ n, F n = false := by
  obtain ⟨m, hm⟩ : ∃ m, m = 1 + (k-1) % 3 := ⟨_, rfl⟩
  rw [← hm] at hN
  have hNlt : ∀ j, j < k → N j = decide (m ≤ j) := fun j hj => by rw [hN, Nat.mod_eq_of_lt hj]
  have hNt : ∀ j, m ≤ j → j < k → N j = true := fun j h1 h2 => by
    rw [hNlt j h2]; exact decide_eq_true h1
  have hNf : ∀ j, j < m → N j = false := fun j h1 => by
    rw [hNlt j (by omega)]; exact decide_eq_false (by omega)
  have hNk : N k = false := by rw [hN, Nat.mod_self]; exact decide_eq_false (by omega)
  have hkm : m + 3 ≤ k := by omega
  have hBk : B k = false := by
    have := S1 (k-2)
    rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = k by omega, hNk,
      hNt (k-1) (by omega) (by omega)] at this
    simp only [Bool.true_and, Bool.and_false] at this
    exact this
  have hB0 : B 0 = false := by
    have := hB 0
    rw [Nat.zero_add, hBk] at this
    exact this.symm
  have hrun : ∀ j, m ≤ j → j + 1 < k → B (j+1) = B j := by
    intro j hj hj2
    have := S1 (j - 1)
    rw [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega, hNt j hj (by omega),
      hNt (j+1) (by omega) hj2] at this
    simp only [Bool.true_and, Bool.and_true] at this
    exact this
  have hconst : ∀ j, m ≤ j → j < k → B j = B m := by
    intro j hj hjk
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [hrun j hj (by omega), ih (by omega)]
  have hFrun : ∀ j, m ≤ j → j + 3 ≤ k → F (j+3) = F j := by
    intro j hj hjk
    apply win_shift
    rw [← hBF, ← hBF]
    exact hrun j hj (by omega)
  have hBm1 : 2 ≤ m → B (m-1) = false := by
    intro h2
    have := S1 (m-2)
    rw [show m - 2 + 1 = m - 1 by omega, show m - 2 + 2 = m by omega, hNf (m-1) (by omega),
      hNt m le_rfl (by omega)] at this
    simp only [Bool.false_and, Bool.and_true] at this
    exact this.symm
  have hF0 : F k = F 0 := by have := hF 0; rwa [Nat.zero_add] at this
  have e0 : win F 0 = false := by rw [← hBF 0]; exact hB0
  have hB1 : m = 3 → B 1 = false := by
    intro h3
    have hF03 : F k = F 3 := by
      have := prop3 F m k hFrun ((k-3)/3) 3 (by omega) (by omega)
      rwa [show 3 + 3 * ((k-3)/3) = k by omega] at this
    have hF30 : F 3 = F 0 := by rw [← hF03, hF0]
    rw [hBF 1]
    exact bl_b1 (F 0) (F 1) (F 2) (F 3) hF30 e0
  have hBz : ∀ j, j < m → B j = false := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact hB0
    · rcases (show m = 2 ∨ m = 3 by omega) with h | h
      · have := hBm1 (by omega); rwa [show m - 1 = 1 by omega] at this
      · exact hB1 h
    · have := hBm1 (by omega); rwa [show m - 1 = 2 by omega] at this
  cases hc : B m with
  | false =>
    have hBall : ∀ n, B n = false := by
      intro n
      rw [per_mod B k hB n]
      have hlt : n % k < k := Nat.mod_lt _ (by omega)
      rcases Nat.lt_or_ge (n % k) m with h | h
      · exact hBz _ h
      · rw [hconst _ h hlt, hc]
    have hF2 : ∀ n, F (n+2) = false := by
      intro n; rw [H n, hBall, hBall, hBall, gff]; rfl
    intro n
    rw [← hF n, show n + k = (n + k - 2) + 2 by omega]
    exact hF2 _
  | true =>
    exfalso
    have hBone : ∀ j, m ≤ j → j < k → B j = true := fun j h1 h2 => by rw [hconst j h1 h2, hc]
    rcases (show m = 1 ∨ m = 2 ∨ m = 3 by omega) with h1 | h2 | h3
    · -- one zero
      have hF01 : F k = F 1 := by
        have := prop3 F m k hFrun ((k-1)/3) 1 (by omega) (by omega)
        rwa [show 1 + 3 * ((k-1)/3) = k by omega] at this
      have a1 := H (k-2)
      rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = k by omega,
        hBone (k-2) (by omega) (by omega), hBone (k-1) (by omega) (by omega), hBk, gtf] at a1
      have a2 := H (k-1)
      rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = 1 + k by omega, hB 1,
        hBone 1 (by omega) (by omega), hBk, hBone (k-1) (by omega) (by omega), gft, hF 1] at a2
      exact bl_m1 (F k) (F 1) (R k) a1 a2 hF01
    · -- two zeros
      have hF02 : F k = F 2 := by
        have := prop3 F m k hFrun ((k-2)/3) 2 (by omega) (by omega)
        rwa [show 2 + 3 * ((k-2)/3) = k by omega] at this
      have a2 := H (k-1)
      rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = 1 + k by omega, hB 1, hBz 1 (by omega),
        hBk, hBone (k-1) (by omega) (by omega), gff, hF 1] at a2
      exact bl_m2 (F 0) (F 1) (F 2) (by rw [← hF0, hF02]) e0 a2
    · -- three zeros
      have hF03 : F k = F 3 := by
        have := prop3 F m k hFrun ((k-3)/3) 3 (by omega) (by omega)
        rwa [show 3 + 3 * ((k-3)/3) = k by omega] at this
      have hF30 : F 3 = F 0 := by rw [← hF03, hF0]
      have a1 := H (k-1)
      rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = 1 + k by omega, hB 1, hBz 1 (by omega),
        hBk, hBone (k-1) (by omega) (by omega), gff, hF 1] at a1
      have a2 := H k
      rw [show k + 1 = 1 + k by omega, show k + 2 = 2 + k by omega, hB 1, hB 2,
        hBz 1 (by omega), hBz 2 (by omega), hBk, gff, hF 2] at a2
      have hF1 : F 1 = true := by rw [a1]; rfl
      have hF2 : F 2 = false := by rw [a2]; rfl
      have e2 : win F 2 = false := by rw [← hBF 2]; exact hBz 2 (by omega)
      have e3 : win F 3 = true := by rw [← hBF 3]; exact hBone 3 (by omega) (by omega)
      have hF0t : F 0 = true := bl3 (F 0) (F 1) (F 2) e0 hF1 hF2
      have hF3t : F 3 = true := by rw [hF30]; exact hF0t
      have hF4t : F 4 = true := bl4 (F 2) (F 3) (F 4) e2 hF2 hF3t
      have hF5t : F 5 = true := bl5 (F 3) (F 4) (F 5) e3 hF3t hF4t
      have hFtrue : ∀ j, 3 ≤ j → j ≤ k → F j = true := by
        intro j hj hjk
        have := prop3 F m k hFrun ((j-3)/3) (3 + (j-3) % 3) (by omega) (by omega)
        rw [show 3 + (j-3) % 3 + 3 * ((j-3)/3) = j by omega] at this
        rw [this]
        rcases (show (j-3) % 3 = 0 ∨ (j-3) % 3 = 1 ∨ (j-3) % 3 = 2 by omega) with h | h | h <;>
          rw [h]
        · exact hF3t
        · exact hF4t
        · exact hF5t
      have hR2 : R 2 = false :=
        bl6 (F 3) (B 1) (B 2) (B 3) (R 2) (R 3) (H 1) (hBz 1 (by omega)) (hBz 2 (by omega))
          (hBone 3 (by omega) (by omega)) hF3t
      have hR34 : xor (R 3) (R 4) = true :=
        bl7 (F 4) (B 2) (B 3) (B 4) (R 3) (R 4) (H 2) (hBz 2 (by omega))
          (hBone 3 (by omega) (by omega)) (hBone 4 (by omega) (by omega)) hF4t
      have hmid : ∀ n, 3 ≤ n → n + 3 ≤ k → R (n+2) = R (n+1) := by
        intro n hn hnk
        exact bl8 (F (n+2)) (B n) (B (n+1)) (B (n+2)) (R (n+1)) (R (n+2)) (H n)
          (hBone n (by omega) (by omega)) (hBone (n+1) (by omega) (by omega))
          (hBone (n+2) (by omega) (by omega)) (hFtrue (n+2) (by omega) (by omega))
      have hGrun : ∀ j, 4 ≤ j → j + 3 ≤ k + 1 → G (j+3) = G j := by
        intro j hj hjk
        apply win_shift
        rw [← hRG, ← hRG]
        have := hmid (j-1) (by omega) (by omega)
        rwa [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega] at this
      have b3 := H (k-2)
      rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = k by omega] at b3
      have hRk : R k = false :=
        bl9 (F k) (B (k-2)) (B (k-1)) (B k) (R (k-1)) (R k) b3 (hBone (k-2) (by omega) (by omega))
          (hBone (k-1) (by omega) (by omega)) hBk (by rw [hF03]; exact hF3t)
      have hR0 : R 0 = false := by
        have := hR 0
        rw [Nat.zero_add, hRk] at this
        exact this.symm
      have hG41 : G 4 = G 1 := by
        have := prop3 G 4 (k+1) hGrun ((k-3)/3) 4 le_rfl (by omega)
        rw [show 4 + 3 * ((k-3)/3) = 1 + k by omega, hG 1] at this
        exact this.symm
      have hG60 : G 6 = G 0 := by
        have := prop3 G 4 (k+1) hGrun ((k-6)/3) 6 (by omega) (by omega)
        rw [show 6 + 3 * ((k-6)/3) = 0 + k by omega, hG 0] at this
        exact this.symm
      have w0 : win G 0 = false := by rw [← hRG 0]; exact hR0
      have w2 : win G 2 = false := by rw [← hRG 2]; exact hR2
      have w34 : xor (win G 3) (win G 4) = true := by rw [← hRG 3, ← hRG 4]; exact hR34
      exact bl10 (G 0) (G 1) (G 2) (G 3) (G 4) (G 5) (G 6) hG41 hG60 w0 w2 w34

theorem core_outer (k : ℕ) (hk4 : 4 ≤ k) (G G' N : ℕ → Bool)
    (hG : ∀ n, G (n + k) = G n) (hG' : ∀ n, G' (n + k) = G' n)
    (hN : ∀ n, N n = decide (1 + (k-1) % 3 ≤ n % k))
    (h1 : ∀ n, xor (rowR (win G) n) (rowR (win G') n) = xor (G (n+2)) (G' (n+2)))
    (h2 : ∀ n, xor (rowR (fun j => xor (win G j) (N j)) n) (rowR (fun j => xor (win G' j) (N j)) n) =
      xor (G (n+2)) (G' (n+2))) :
    ∀ n, G n = G' n := by
  have key := core2 k hk4 (fun n => xor (G n) (G' n)) (fun n => xor (win G n) (win G' n)) (win G) G N
    (fun n => by show xor (G (n+k)) (G' (n+k)) = xor (G n) (G' n); rw [hG, hG'])
    (fun n => by
      show xor (win G (n+k)) (win G' (n+k)) = xor (win G n) (win G' n)
      rw [win_per G k hG, win_per G' k hG'])
    (win_per G k hG) hG hN
    (fun n => bool_winxor (G n) (G (n+1)) (G (n+2)) (G' n) (G' (n+1)) (G' (n+2)))
    (fun n => rfl)
    (fun n => bool1 (win G n) (win G' n) (win G (n+1)) (win G (n+2)) (win G' (n+1)) (win G' (n+2))
      (N n) (N (n+1)) (N (n+2)) ((h1 n).trans (h2 n).symm))
    (fun n => bool2 (win G n) (win G' n) (win G (n+1)) (win G (n+2)) (win G' (n+1)) (win G' (n+2))
      _ (h1 n))
  intro n
  exact bool_eq _ _ (key n)

/-! Index arithmetic for the cyclic words -/

theorem ix_add (k : ℕ) (hk : 0 < k) (n j : ℕ) : ixf k hk ((ixf k hk n).val + j) = ixf k hk (n + j) :=
  Fin.ext (Nat.mod_add_mod n k j)

theorem ix_eq (k : ℕ) (hk : 0 < k) (a b : ℕ) (h : a % k = b % k) : ixf k hk a = ixf k hk b :=
  Fin.ext h

theorem ix_pred (k : ℕ) (hk : 0 < k) (h2 : 2 ≤ k) (n : ℕ) :
    ixf k hk ((ixf k hk n).val + k - 1 % k) = ixf k hk (n + (k-1)) := by
  rw [Nat.mod_eq_of_lt (show 1 < k by omega)]
  rw [show (ixf k hk n).val + k - 1 = (ixf k hk n).val + (k-1) by omega]
  exact ix_add k hk n (k-1)

theorem ix_fin (k : ℕ) (hk : 0 < k) (i : Fin k) : ixf k hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem mixwin (k : ℕ) (hk : 0 < k) (h2 : 2 ≤ k) (z : Fin k → Bool) (n : ℕ) :
    mixf k hk 1 z (ixf k hk n) = win (fun j => z (ixf k hk (j + (k-1)))) n := by
  simp only [mixf, win]
  rw [ix_pred k hk h2, ix_add,
    ix_eq k hk (n + 1 + (k-1)) n (by rw [show n + 1 + (k-1) = n + k by omega, Nat.add_mod_right]),
    ix_eq k hk (n + 2 + (k-1)) (n+1) (by rw [show n + 2 + (k-1) = n + 1 + k by omega, Nat.add_mod_right])]

theorem Gf_eq (k : ℕ) (hk : 0 < k) (h2 : 2 ≤ k) (name x : Fin k → Bool) :
    (fun j => addf k name (rotf k hk 1 x) (ixf k hk (j + (k-1)))) = Gf k hk name x := by
  funext j
  simp only [addf, rotf, Gf]
  rw [ix_pred k hk h2]

theorem mixG (k : ℕ) (hk : 0 < k) (h2 : 2 ≤ k) (name x : Fin k → Bool) (n : ℕ) :
    mixf k hk 1 (addf k name (rotf k hk 1 x)) (ixf k hk n) = win (Gf k hk name x) n := by
  rw [mixwin k hk h2, Gf_eq k hk h2]

theorem row_at (k : ℕ) (hk : 0 < k) (h2 : 2 ≤ k) (name x : Fin k → Bool) (n : ℕ) :
    rowf k hk name x (ixf k hk n) = xor (rowR (win (Gf k hk name x)) n) (x (ixf k hk n)) := by
  show xor (xor (mixf k hk 1 (addf k name (rotf k hk 1 x)) (ixf k hk n))
    (!(mixf k hk 1 (addf k name (rotf k hk 1 x)) (ixf k hk ((ixf k hk n).val + 1))) &&
      mixf k hk 1 (addf k name (rotf k hk 1 x)) (ixf k hk ((ixf k hk n).val + 2)))) (x (ixf k hk n)) = _
  rw [ix_add, ix_add, mixG k hk h2, mixG k hk h2, mixG k hk h2]
  rfl

theorem Gf_per (k : ℕ) (hk : 0 < k) (name x : Fin k → Bool) (n : ℕ) :
    Gf k hk name x (n + k) = Gf k hk name x n := by
  simp only [Gf]
  rw [ix_eq k hk (n + k + (k-1)) (n + (k-1))
      (by rw [show n + k + (k-1) = n + (k-1) + k by omega, Nat.add_mod_right]),
    ix_eq k hk (n + k + (k-1) + (k-1)) (n + (k-1) + (k-1))
      (by rw [show n + k + (k-1) + (k-1) = n + (k-1) + (k-1) + k by omega, Nat.add_mod_right])]

theorem Gf_add (k : ℕ) (hk : 0 < k) (u v x : Fin k → Bool) (j : ℕ) :
    Gf k hk (addf k u v) x j = xor (Gf k hk u x j) (v (ixf k hk (j + (k-1)))) :=
  bool_x3 (u (ixf k hk (j + (k-1)))) (v (ixf k hk (j + (k-1)))) (x (ixf k hk (j + (k-1) + (k-1))))

/-! The pair of names at widths four and up -/

theorem dx (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S]
    (h1 : P → ¬Q ∧ ¬R ∧ S) (h2 : Q → ¬P ∧ ¬R ∧ S) (h3 : R → ¬P ∧ ¬Q ∧ S)
    (h4 : ¬P → ¬Q → ¬R → ¬S) :
    xor (decide P) (xor (decide Q) (decide R)) = decide S := by
  by_cases hP : P
  · obtain ⟨hQ, hR, hS⟩ := h1 hP; simp [hP, hQ, hR, hS]
  · by_cases hQ : Q
    · obtain ⟨-, hR, hS⟩ := h2 hQ; simp [hP, hQ, hR, hS]
    · by_cases hR : R
      · obtain ⟨-, -, hS⟩ := h3 hR; simp [hP, hQ, hR, hS]
      · have hS := h4 hP hQ hR; simp [hP, hQ, hR, hS]

theorem mixv (k : ℕ) (hk : 0 < k) (hk4 : 4 ≤ k) (i : Fin k) :
    mixf k hk 1 (fun i : Fin k => decide (1 + (k-1) % 3 + 1 ≤ i.val ∧
      (i.val - (1 + (k-1) % 3 + 1)) % 3 = 0)) i = decide (1 + (k-1) % 3 ≤ i.val) := by
  obtain ⟨j, hj⟩ := i
  simp only [mixf, ixf]
  rw [Nat.mod_eq_of_lt (show 1 < k by omega)]
  have ha : (j + k - 1) % k = if j = 0 then k - 1 else j - 1 := by
    split_ifs with h
    · subst h; rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    · rw [show j + k - 1 = (j - 1) + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
  have hb : (j + 1) % k = if j + 1 = k then 0 else j + 1 := by
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  simp only [ha, hb]
  split_ifs with h1 h2 h2 <;> apply dx <;> omega

theorem pairB4 (k : ℕ) (hk : 0 < k) (hk4 : 4 ≤ k) : PairB k hk := by
  have h2k : 2 ≤ k := by omega
  obtain ⟨v, hv⟩ : ∃ v : Fin k → Bool, ∀ i, mixf k hk 1 v i = decide (1 + (k-1) % 3 ≤ i.val) :=
    ⟨_, mixv k hk hk4⟩
  have hk2 : ¬ k = 2 := by omega
  refine ⟨v, fun i => by rw [hv i]; simp [tgt, hk2], ?_⟩
  intro u x x' h
  have e1 : rowf k hk u x = rowf k hk u x' := congrArg Prod.fst h
  have e2 : rowf k hk (addf k u v) x = rowf k hk (addf k u v) x' := congrArg Prod.snd h
  have hw : ∀ y : Fin k → Bool, win (Gf k hk (addf k u v) y) =
      fun j => xor (win (Gf k hk u y) j) (mixf k hk 1 v (ixf k hk j)) := by
    intro y; funext j
    show win (Gf k hk (addf k u v) y) j = xor (win (Gf k hk u y) j) (mixf k hk 1 v (ixf k hk j))
    rw [mixwin k hk h2k, ← win_xor]
    congr 1
    funext t
    exact Gf_add k hk u v y t
  have hx2 : ∀ (y : Fin k → Bool) (n : ℕ),
      Gf k hk u y (n+2) = xor (u (ixf k hk (n+2+(k-1)))) (y (ixf k hk n)) := by
    intro y n
    simp only [Gf]
    rw [ix_eq k hk (n+2+(k-1)+(k-1)) n
      (by rw [show n+2+(k-1)+(k-1) = n + k + k by omega, Nat.add_mod_right, Nat.add_mod_right])]
  have key := core_outer k hk4 (Gf k hk u x) (Gf k hk u x') (fun n => mixf k hk 1 v (ixf k hk n))
    (Gf_per k hk u x) (Gf_per k hk u x') (fun n => hv (ixf k hk n))
    (fun n => by
      have := congrFun e1 (ixf k hk n)
      rw [row_at k hk h2k, row_at k hk h2k] at this
      rw [hx2, hx2]
      exact bool3 _ _ _ _ _ this)
    (fun n => by
      have := congrFun e2 (ixf k hk n)
      rw [row_at k hk h2k, row_at k hk h2k, hw, hw] at this
      rw [hx2, hx2]
      exact bool3 _ _ _ _ _ this)
  funext i
  have := key (i.val + 2)
  have hi : ixf k hk (i.val + 2 + (k-1) + (k-1)) = i := by
    rw [ix_eq k hk _ i.val (by rw [show i.val + 2 + (k-1) + (k-1) = i.val + k + k by omega,
      Nat.add_mod_right, Nat.add_mod_right]), ix_fin]
  simp only [Gf, hi] at this
  exact bool_cancel _ _ _ this

theorem fin1_eta (f : Fin 1 → Bool) : (fun _ : Fin 1 => f 0) = f := by
  funext i; fin_cases i; rfl

theorem fin2_eta (f : Fin 2 → Bool) : (fun i : Fin 2 => if i.val = 0 then f 0 else f 1) = f := by
  funext i; fin_cases i <;> rfl

theorem fin3_eta (f : Fin 3 → Bool) :
    (fun i : Fin 3 => if i.val = 0 then f 0 else if i.val = 1 then f 1 else f 2) = f := by
  funext i; fin_cases i <;> rfl

theorem pairB2 : PairB 2 h2pos := by
  refine ⟨fun i => decide (i.val = 1), k2mix, ?_⟩
  intro u x x' h
  have e1 : rowf 2 h2pos u x = rowf 2 h2pos u x' := congrArg Prod.fst h
  have e2 : rowf 2 h2pos (addf 2 u (fun i => decide (i.val = 1))) x =
      rowf 2 h2pos (addf 2 u (fun i => decide (i.val = 1))) x' := congrArg Prod.snd h
  rw [← fin2_eta u, ← fin2_eta x, ← fin2_eta x'] at e1 e2
  have := k2dec (u 0) (u 1) (x 0) (x 1) (x' 0) (x' 1) (congrFun e1) (congrFun e2)
  rw [← fin2_eta x, ← fin2_eta x', this.1, this.2]

theorem k1coll (n : Fin 1 → Bool) : rowf 1 h1pos n (fun _ => false) = rowf 1 h1pos n (fun _ => true) := by
  funext i
  have := k1dec (n 0) i
  rwa [fin1_eta n] at this

theorem k3coll (n : Fin 3 → Bool) : rowf 3 h3pos n (fun _ => false) = rowf 3 h3pos n (fun _ => true) := by
  funext i
  have := k3dec (n 0) (n 1) (n 2) i
  rwa [fin3_eta n] at this

/-! The count of names -/

theorem one_name (k : ℕ) (hk : 0 < k) (n : Fin k → Bool) :
    ∃ x x' : Fin k → Bool, x ≠ x' ∧ rowf k hk n x = rowf k hk n x' := by
  let x : Fin k → Bool := fun i => n (ixf k hk (i.val + 1))
  have hrot : ∀ i, rotf k hk 1 x i = n i := by
    intro i
    show n (ixf k hk ((ixf k hk (i.val + k - 1 % k)).val + 1)) = n i
    rw [ix_add]
    congr 1
    rcases Nat.lt_or_ge k 2 with h | h
    · apply Fin.ext
      have h1 := (ixf k hk (i.val + k - 1 % k + 1)).isLt
      have h2 := i.isLt
      omega
    · rw [ix_eq k hk _ i.val (by rw [Nat.mod_eq_of_lt (show 1 < k by omega),
        show i.val + k - 1 + 1 = i.val + k by omega, Nat.add_mod_right]), ix_fin]
  have hrot' : ∀ i, rotf k hk 1 (fun i => !(x i)) i = !(n i) := by
    intro i
    show (!(x (ixf k hk (i.val + k - 1 % k)))) = !(n i)
    rw [show x (ixf k hk (i.val + k - 1 % k)) = rotf k hk 1 x i from rfl, hrot]
  have hA : addf k n (rotf k hk 1 x) = fun _ => false := by
    funext i; simp only [addf, hrot]; cases n i <;> rfl
  have hB : addf k n (rotf k hk 1 (fun i => !(x i))) = fun _ => true := by
    funext i; simp only [addf, hrot']; cases n i <;> rfl
  refine ⟨x, fun i => !(x i), fun h => ?_, ?_⟩
  · exact bool_ne _ (congrFun h ⟨0, hk⟩)
  · funext i
    show xor (chif k hk (mixf k hk 1 (addf k n (rotf k hk 1 x))) i) (x i) =
      xor (chif k hk (mixf k hk 1 (addf k n (rotf k hk 1 (fun i => !(x i))))) i) (!(x i))
    rw [hA, hB]
    show xor false (x i) = xor true (!(x i))
    cases x i <;> rfl

theorem fwd (k : ℕ) (hk : 0 < k) (q : ℕ) (names : Fin q → Fin k → Bool)
    (hinj : Function.Injective (fun x : Fin k → Bool => fun j : Fin q => rowf k hk (names j) x)) :
    k ≠ 1 ∧ k ≠ 3 ∧ 2 ≤ q := by
  have hne : (fun _ : Fin k => false) ≠ (fun _ : Fin k => true) := by
    intro h; exact Bool.false_ne_true (congrFun h ⟨0, hk⟩)
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply hne; apply hinj; funext j; exact k1coll (names j)
  · rintro rfl
    apply hne; apply hinj; funext j; exact k3coll (names j)
  · by_contra hq
    have hq2 : q < 2 := by omega
    interval_cases q
    · apply hne; apply hinj; funext j; exact j.elim0
    · obtain ⟨x, x', hxx, hrow⟩ := one_name k hk (names 0)
      apply hxx; apply hinj; funext j
      rw [Subsingleton.elim j 0]
      exact hrow

theorem bwd (k : ℕ) (hk : 0 < k) (q : ℕ) (hq : k ≠ 1 ∧ k ≠ 3 ∧ 2 ≤ q)
    (hB : (k = 2 ∨ 4 ≤ k) → PairB k hk) :
    ∃ names : Fin q → Fin k → Bool,
      Function.Injective (fun x : Fin k → Bool => fun j : Fin q => rowf k hk (names j) x) := by
  obtain ⟨v, -, hv⟩ := hB (by omega)
  refine ⟨fun j => if j.val = 0 then (fun _ => false) else addf k (fun _ => false) v, ?_⟩
  intro x x' h
  have e0 : rowf k hk (fun _ => false) x = rowf k hk (fun _ => false) x' := congrFun h ⟨0, by omega⟩
  have e1 : rowf k hk (addf k (fun _ => false) v) x = rowf k hk (addf k (fun _ => false) v) x' :=
    congrFun h ⟨1, by omega⟩
  exact hv (fun _ => false) (Prod.ext e0 e1)

theorem main_aux (k : ℕ) (hk : 0 < k) :
    (∀ q : ℕ, (∃ names : Fin q → Fin k → Bool,
      Function.Injective (fun x : Fin k → Bool => fun j : Fin q => rowf k hk (names j) x)) ↔
        k ≠ 1 ∧ k ≠ 3 ∧ 2 ≤ q) ∧ ((k = 2 ∨ 4 ≤ k) → PairB k hk) := by
  have partB : (k = 2 ∨ 4 ≤ k) → PairB k hk := by
    rintro (rfl | h4)
    · exact pairB2
    · exact pairB4 k hk h4
  exact ⟨fun q => ⟨fun ⟨names, hinj⟩ => fwd k hk q names hinj, fun hq => bwd k hk q hq partB⟩, partB⟩

end PEqualNP.Outside.L_meta_41629_aux

theorem PEqualNP.Outside.L_meta_41629 : ∀ (k : Nat) (hk : 0 < k),
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
  let mix := fun (d : Nat) (x : W) (i : Fin k) =>
    xor (x (ix (i.val+k-d % k))) (xor (x i) (x (ix (i.val+d))))
  let rot := fun (a : Nat) (x : W) (i : Fin k) => x (ix (i.val+k-a % k))
  let chi := fun (r : W) (i : Fin k) => xor (r i) (!(r (ix (i.val+1))) && r (ix (i.val+2)))
  let row := fun (name x : W) => add (chi (mix 1 (add name (rot 1 x)))) x
  let m := 1 + (k-1) % 3
  (∀ q : Nat, (∃ names : Fin q → W, Function.Injective (fun x : W => fun j : Fin q => row (names j) x)) ↔
    k ≠ 1 ∧ k ≠ 3 ∧ 2 ≤ q) ∧
  ((k = 2 ∨ 4 ≤ k) → ∃ v : W,
    (∀ i : Fin k, mix 1 v i = (if k = 2 then decide (i.val = 1) else decide (m ≤ i.val))) ∧
    ∀ u : W, Function.Injective (fun x : W => (row u x, row (add u v) x))) := by
  intro k hk
  exact PEqualNP.Outside.L_meta_41629_aux.main_aux k hk
