import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25541_aux

def rot (k s word : Nat) : Nat := ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def state (k uv : Nat) (c : Nat → Nat) (rounds key : Nat) : Nat :=
  (List.range rounds).foldl (fun prev tick =>
      step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^ rot k (2 * tick) key ^^^
        c (tick + 1)) (rot k 1 key ^^^ uv)

def injected (k : Nat) (c : Nat → Nat) (round key pos : Nat) : Bool :=
  xor ((rot k (2 * (round - 1)) key).testBit (pos % k)) ((c round).testBit (pos % k))

def bit (k uv : Nat) (c : Nat → Nat) (round key pos : Nat) : Bool :=
  (state k uv c round key).testBit (pos % k)

def guard (k uv : Nat) (c : Nat → Nat) (round key stop : Nat) : Bool :=
  xor (xor (bit k uv c round key (stop - 2)) (bit k uv c round key (stop - 1)))
    (bit k uv c round key stop)

def branch (k uv : Nat) (c : Nat → Nat) (t edge subject : Nat) : Nat :=
  let hit := guard k uv c (t - 1) subject edge
  let mid := edge - 3 + hit.toNat
  let next := guard k uv c t subject mid
  if hit then
    let near := bit k uv c t subject (edge - 2) ==
      xor (injected k c t subject (edge - 1)) (injected k c t subject edge)
    let far := bit k uv c t subject (edge - 3) == injected k c t subject edge
    2 + near.toNat + 2 * far.toNat + 4 * next.toNat
  else next.toNat

def gain (v : Nat) : Nat :=
  if v < 2 then v else 1 + (v - 2) / 4 + (if v = 9 then 1 else 0)

def trace (k uv : Nat) (c : Nat → Nat) (q len keyWord : Nat) : Nat × Nat :=
  (List.range len).foldl (fun (acc : Nat × Nat) j =>
      let v := branch k uv c (5 + 2 * j) acc.1 keyWord
      (acc.1 - 6 + gain v, acc.2 + v * 10 ^ j)) (q - 13, 0)

def pack (v bits : Nat) : Nat :=
  ((bits % 2) <<< 5) ||| (if v < 2 then (bits / 2) % 2 else
      (((bits / 2) % 2) <<< 3) ||| (((bits / 4) % 2) <<< 2) ||| (((bits / 8) % 2) <<< 1))


def B (k w i : Nat) : Bool := w.testBit (i % k)

def f (k w : Nat) : Nat := step k (w ^^^ rot k 1 w ^^^ rot k (k - 1) w)

theorem B_xor (k a b i : Nat) : B k (a ^^^ b) i = xor (B k a i) (B k b i) := by
  simp [B, Nat.testBit_xor]

theorem B_period (k w i : Nat) : B k w (i + k) = B k w i := by
  simp [B, Nat.add_mod_right]

theorem testBit_ge (w k i : Nat) (hw : w < 2 ^ k) (hi : k ≤ i) : w.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hi))

theorem rot_lt (k s w : Nat) : rot k s w < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)

theorem B_rot_add (k s w i : Nat) (hk : 0 < k) (hw : w < 2 ^ k) :
    B k (rot k s w) (i + s) = B k w i := by
  unfold B rot
  have ha : i % k < k := Nat.mod_lt _ hk
  have hr : s % k < k := Nat.mod_lt _ hk
  have hj : (i + s) % k < k := Nat.mod_lt _ hk
  have key : (i + s) % k = if i % k + s % k < k then i % k + s % k else i % k + s % k - k := by
    rw [Nat.add_mod]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hj, decide_true, Bool.true_and]
  split_ifs at key with h
  · have h1 : (i + s) % k ≥ s % k := by omega
    have h2 : (i + s) % k - s % k = i % k := by omega
    have h3 : k ≤ k - s % k + (i + s) % k := by omega
    rw [testBit_ge w k _ hw h3]
    simp [h1, h2]
  · have h1 : ¬ ((i + s) % k ≥ s % k) := by omega
    have h2 : k - s % k + (i + s) % k = i % k := by omega
    simp [h1, h2]

theorem B_rot (k s w i : Nat) (hk : 0 < k) (hw : w < 2 ^ k) (h : s ≤ i) :
    B k (rot k s w) i = B k w (i - s) := by
  have := B_rot_add k s w (i - s) hk hw
  rwa [Nat.sub_add_cancel h] at this

theorem foldl_or_testBit (F : Nat → Bool) (n j : Nat) :
    ((List.range n).foldl (fun acc i => acc ||| ((F i).toNat <<< i)) 0).testBit j =
      (decide (j < n) && F j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy j n with h | h | h
    · have : ¬ (j ≥ n) := by omega
      simp [h, this, show j < n + 1 by omega]
    · subst h
      cases F j <;> simp
    · have h1 : ¬ j < n := by omega
      have h2 : ¬ j < n + 1 := by omega
      have h3 : j - n ≠ 0 := by omega
      cases hF : F n
      · simp [h1, h2]
      · have h4 : Nat.testBit 1 (j - n) = false := testBit_ge 1 1 (j - n) (by norm_num) (by omega)
        simp [h1, h2, h4]

theorem step_testBit (k w j : Nat) :
    (step k w).testBit j = (decide (j < k) &&
      xor (w.testBit j) (!(w.testBit ((j + 1) % k)) && w.testBit ((j + 2) % k))) := by
  unfold step
  exact foldl_or_testBit (fun j => xor (w.testBit j)
    (!(w.testBit ((j + 1) % k)) && w.testBit ((j + 2) % k))) k j

theorem step_lt (k w : Nat) : step k w < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [step_testBit]
  simp [show ¬ i < k by omega]

theorem f_lt (k w : Nat) : f k w < 2 ^ k := step_lt _ _

theorem B_step (k w i : Nat) (hk : 0 < k) :
    B k (step k w) i = xor (B k w i) (!(B k w (i + 1)) && B k w (i + 2)) := by
  unfold B
  rw [step_testBit]
  have h1 : (i % k + 1) % k = (i + 1) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : (i % k + 2) % k = (i + 2) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  simp [Nat.mod_lt _ hk, h1, h2]

theorem B_theta (k w i : Nat) (hk : 0 < k) (hw : w < 2 ^ k) :
    B k (w ^^^ rot k 1 w ^^^ rot k (k - 1) w) (i + 1) =
      xor (xor (B k w i) (B k w (i + 1))) (B k w (i + 2)) := by
  rw [B_xor, B_xor, B_rot k 1 w (i + 1) hk hw (by omega)]
  rw [← B_period k (rot k (k - 1) w) (i + 1), B_rot k (k - 1) w _ hk hw (by omega)]
  have : i + 1 + k - (k - 1) = i + 2 := by omega
  rw [this, Nat.add_sub_cancel]
  cases B k w i <;> cases B k w (i + 1) <;> cases B k w (i + 2) <;> rfl

theorem B_f (k w : Nat) (hk : 0 < k) (hw : w < 2 ^ k) {i0 i1 i2 i3 i4 : Nat}
    (h1 : i1 = i0 + 1) (h2 : i2 = i0 + 2) (h3 : i3 = i0 + 3) (h4 : i4 = i0 + 4) :
    B k (f k w) i1 =
      xor (xor (xor (B k w i0) (B k w i1)) (B k w i2))
        (!(xor (xor (B k w i1) (B k w i2)) (B k w i3)) &&
          xor (xor (B k w i2) (B k w i3)) (B k w i4)) := by
  subst h1 h2 h3 h4
  unfold f
  rw [B_step _ _ _ hk, B_theta _ _ _ hk hw, show i0 + 1 + 1 = (i0 + 1) + 1 by rfl,
    B_theta _ _ _ hk hw, show i0 + 1 + 2 = (i0 + 2) + 1 by omega, B_theta _ _ _ hk hw]


theorem state_zero (k uv : Nat) (c : Nat → Nat) (key : Nat) :
    state k uv c 0 key = rot k 1 key ^^^ uv := by
  simp [state]

theorem state_succ (k uv : Nat) (c : Nat → Nat) (n key : Nat) :
    state k uv c (n + 1) key = f k (state k uv c n key) ^^^ rot k (2 * n) key ^^^ c (n + 1) := by
  simp only [state, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, f]

theorem state_lt (k uv : Nat) (c : Nat → Nat) (n key : Nat) (huv : uv < 2 ^ k)
    (hc : ∀ n, c n < 2 ^ k) : state k uv c n key < 2 ^ k := by
  cases n with
  | zero => rw [state_zero]; exact Nat.xor_lt_two_pow (rot_lt _ _ _) huv
  | succ n =>
    rw [state_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (f_lt _ _) (rot_lt _ _ _)) (hc _)

theorem B_state_succ (k uv : Nat) (c : Nat → Nat) (n key i : Nat) :
    B k (state k uv c (n + 1) key) i =
      xor (B k (f k (state k uv c n key)) i) (injected k c (n + 1) key i) := by
  rw [state_succ, B_xor, B_xor]
  unfold injected
  rw [Nat.add_sub_cancel]
  unfold B
  cases (f k (state k uv c n key)).testBit (i % k) <;>
    cases (rot k (2 * n) key).testBit (i % k) <;> cases (c (n + 1)).testBit (i % k) <;> rfl

theorem injected_eq (k : Nat) (c : Nat → Nat) (n key i : Nat) (hk : 0 < k) (hK : key < 2 ^ k)
    (h : 2 * n ≤ i) :
    injected k c (n + 1) key i = xor (B k key (i - 2 * n)) (B k (c (n + 1)) i) := by
  unfold injected
  rw [Nat.add_sub_cancel]
  have := B_rot k (2 * n) key i hk hK h
  unfold B at this ⊢
  rw [this]

def Agree (k A A' a c : Nat) : Prop := ∀ i, a ≤ i → i ≤ c → B k A i = B k A' i

theorem agree_f (k A A' a c : Nat) (hk : 0 < k) (hA : A < 2 ^ k) (hA' : A' < 2 ^ k)
    (h : Agree k A A' a c) (ha : 1 ≤ a) (i : Nat) (h1 : a + 1 ≤ i) (h2 : i + 3 ≤ c) :
    B k (f k A) i = B k (f k A') i := by
  rw [B_f k A hk hA (i0 := i - 1) (i1 := i) (i2 := i + 1) (i3 := i + 2) (i4 := i + 3)
      (by omega) (by omega) (by omega) (by omega),
    B_f k A' hk hA' (i0 := i - 1) (i1 := i) (i2 := i + 1) (i3 := i + 2) (i4 := i + 3)
      (by omega) (by omega) (by omega) (by omega)]
  rw [h (i - 1) (by omega) (by omega), h i (by omega) (by omega), h (i + 1) (by omega) (by omega),
    h (i + 2) (by omega) (by omega), h (i + 3) (by omega) (by omega)]

theorem agree_f_gate (k A A' a c : Nat) (hk : 0 < k) (hA : A < 2 ^ k) (hA' : A' < 2 ^ k)
    (h : Agree k A A' a c) (ha : a + 3 ≤ c)
    (hg : xor (xor (B k A (c - 2)) (B k A (c - 1))) (B k A c) = true) :
    B k (f k A) (c - 2) = B k (f k A') (c - 2) := by
  rw [B_f k A hk hA (i0 := c - 3) (i1 := c - 2) (i2 := c - 1) (i3 := c) (i4 := c + 1)
      (by omega) (by omega) (by omega) (by omega),
    B_f k A' hk hA' (i0 := c - 3) (i1 := c - 2) (i2 := c - 1) (i3 := c) (i4 := c + 1)
      (by omega) (by omega) (by omega) (by omega)]
  rw [← h (c - 3) (by omega) (by omega), ← h (c - 2) (by omega) (by omega),
    ← h (c - 1) (by omega) (by omega), ← h c (by omega) (by omega)]
  simp [hg]

theorem v9 (k uv : Nat) (c : Nat → Nat) (n key x : Nat) (hk : 0 < k) (huv : uv < 2 ^ k)
    (hc : ∀ n, c n < 2 ^ k) (hx : 4 ≤ x)
    (hhit : xor (xor (B k (state k uv c n key) (x - 2)) (B k (state k uv c n key) (x - 1)))
      (B k (state k uv c n key) x) = true)
    (hnear : (B k (state k uv c (n + 1) key) (x - 2) ==
      xor (injected k c (n + 1) key (x - 1)) (injected k c (n + 1) key x)) = true)
    (hfar : (B k (state k uv c (n + 1) key) (x - 3) == injected k c (n + 1) key x) = true) :
    B k (f k (state k uv c (n + 1) key)) (x - 3) =
      xor (xor (B k (state k uv c (n + 1) key) (x - 4)) (B k (state k uv c (n + 1) key) (x - 3)))
        (B k (state k uv c (n + 1) key) (x - 2)) := by
  have hP := state_lt k uv c n key huv hc
  have hS := state_lt k uv c (n + 1) key huv hc
  have eS1 := B_state_succ k uv c n key (x - 1)
  have eS0 := B_state_succ k uv c n key x
  have eP1 := B_f k (state k uv c n key) hk hP (i0 := x - 2) (i1 := x - 1) (i2 := x)
    (i3 := x + 1) (i4 := x + 2) (by omega) (by omega) (by omega) (by omega)
  have eP0 := B_f k (state k uv c n key) hk hP (i0 := x - 1) (i1 := x) (i2 := x + 1)
    (i3 := x + 2) (i4 := x + 3) (by omega) (by omega) (by omega) (by omega)
  rw [B_f k (state k uv c (n + 1) key) hk hS (i0 := x - 4) (i1 := x - 3) (i2 := x - 2)
    (i3 := x - 1) (i4 := x) (by omega) (by omega) (by omega) (by omega)]
  rw [eS1, eS0, eP1, eP0]
  rw [eS1, eS0, eP1, eP0] at *
  revert hhit hnear hfar
  generalize B k (state k uv c n key) (x - 2) = p2
  generalize B k (state k uv c n key) (x - 1) = p1
  generalize B k (state k uv c n key) x = p0
  generalize B k (state k uv c n key) (x + 1) = q1
  generalize B k (state k uv c n key) (x + 2) = q2
  generalize B k (state k uv c n key) (x + 3) = q3
  generalize B k (state k uv c (n + 1) key) (x - 2) = s2
  generalize B k (state k uv c (n + 1) key) (x - 3) = s3
  generalize B k (state k uv c (n + 1) key) (x - 4) = s4
  generalize injected k c (n + 1) key (x - 1) = r1
  generalize injected k c (n + 1) key x = r0
  revert p2 p1 p0 q1 q2 q3 s2 s3 s4 r1 r0
  decide


def vk (k base lo m : Nat) : Nat := base ^^^ rot k (lo + k - 1) m

def AgreeAbove (b m m' : Nat) : Prop := ∀ c, b < c → m.testBit c = m'.testBit c

theorem vk_zero (k base lo : Nat) : vk k base lo 0 = base := by
  simp [vk, rot]

theorem vk_lt (k base lo m : Nat) (hb : base < 2 ^ k) : vk k base lo m < 2 ^ k :=
  Nat.xor_lt_two_pow hb (rot_lt _ _ _)

theorem B_key (k base lo m i : Nat) (hk : 0 < k) (hm : m < 2 ^ k) (h1 : lo ≤ i + 1)
    (h2 : i + 2 ≤ lo + k) : B k (vk k base lo m) i = xor (B k base i) (m.testBit (i + 1 - lo)) := by
  unfold vk
  rw [B_xor, ← B_period k (rot k (lo + k - 1) m) i, B_rot _ _ _ _ hk hm (by omega)]
  have : i + k - (lo + k - 1) = i + 1 - lo := by omega
  rw [this]
  unfold B
  rw [Nat.mod_eq_of_lt (show i + 1 - lo < k by omega)]

theorem key_agree (k base lo m m' b i : Nat) (hk : 0 < k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k)
    (hab : AgreeAbove b m m') (h1 : lo + b ≤ i) (h2 : i + 2 ≤ lo + k) :
    B k (vk k base lo m) i = B k (vk k base lo m') i := by
  rw [B_key k base lo m i hk hm (by omega) h2, B_key k base lo m' i hk hm' (by omega) h2,
    hab _ (by omega)]

theorem point_succ (k uv : Nat) (c : Nat → Nat) (n K K' i : Nat) (hk : 0 < k)
    (hK : K < 2 ^ k) (hK' : K' < 2 ^ k) (hi : 2 * n ≤ i)
    (hf : B k (f k (state k uv c n K)) i = B k (f k (state k uv c n K')) i)
    (hkey : B k K (i - 2 * n) = B k K' (i - 2 * n)) :
    B k (state k uv c (n + 1) K) i = B k (state k uv c (n + 1) K') i := by
  rw [B_state_succ, B_state_succ, injected_eq k c n K i hk hK hi,
    injected_eq k c n K' i hk hK' hi, hf, hkey]

theorem agree_round (k uv : Nat) (c : Nat → Nat) (base lo b m m' n a cc a' c' : Nat)
    (hk : 0 < k) (huv : uv < 2 ^ k) (hc : ∀ n, c n < 2 ^ k) (hb : base < 2 ^ k)
    (hm : m < 2 ^ k) (hm' : m' < 2 ^ k) (hab : AgreeAbove b m m')
    (h : Agree k (state k uv c n (vk k base lo m)) (state k uv c n (vk k base lo m')) a cc)
    (ha : 1 ≤ a) (h1 : a + 1 ≤ a') (h2 : c' + 3 ≤ cc) (h3 : lo + b + 2 * n ≤ a')
    (h4 : c' + 2 ≤ lo + k + 2 * n) :
    Agree k (state k uv c (n + 1) (vk k base lo m)) (state k uv c (n + 1) (vk k base lo m')) a' c' := by
  intro i hi1 hi2
  apply point_succ k uv c n _ _ i hk (vk_lt _ _ _ _ hb) (vk_lt _ _ _ _ hb) (by omega)
  · exact agree_f k _ _ a cc hk (state_lt _ _ _ _ _ huv hc) (state_lt _ _ _ _ _ huv hc) h ha i
      (by omega) (by omega)
  · exact key_agree k base lo m m' b _ hk hm hm' hab (by omega) (by omega)

theorem agree_zero (k uv : Nat) (c : Nat → Nat) (base lo b m m' : Nat)
    (hk : 0 < k) (hb : base < 2 ^ k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k)
    (hab : AgreeAbove b m m') :
    Agree k (state k uv c 0 (vk k base lo m)) (state k uv c 0 (vk k base lo m'))
      (lo + b + 1) (lo + k - 1) := by
  intro i hi1 hi2
  rw [state_zero, state_zero, B_xor, B_xor, B_rot k 1 _ i hk (vk_lt _ _ _ _ hb) (by omega),
    B_rot k 1 _ i hk (vk_lt _ _ _ _ hb) (by omega),
    key_agree k base lo m m' b (i - 1) hk hm hm' hab (by omega) (by omega)]


theorem bit_eq (k uv : Nat) (c : Nat → Nat) (r key pos : Nat) :
    bit k uv c r key pos = B k (state k uv c r key) pos := rfl

theorem guard_eq (k uv : Nat) (c : Nat → Nat) (r key stop : Nat) :
    guard k uv c r key stop = xor (xor (B k (state k uv c r key) (stop - 2))
      (B k (state k uv c r key) (stop - 1))) (B k (state k uv c r key) stop) := rfl

theorem agreeAbove5 (m : Nat) (hm : m < 64) : AgreeAbove 5 m 0 := by
  intro c hc
  rw [Nat.zero_testBit]
  exact testBit_ge m 6 c (by simpa using hm) (by omega)

theorem agree_mono {k A A' a cc a' c' : Nat} (h : Agree k A A' a cc) (h1 : a ≤ a') (h2 : c' ≤ cc) :
    Agree k A A' a' c' := fun i hi1 hi2 => h i (by omega) (by omega)

theorem agree_from_f (k uv : Nat) (c : Nat → Nat) (base lo b m m' r a' c' : Nat)
    (hk : 0 < k) (hb : base < 2 ^ k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k)
    (hab : AgreeAbove b m m') (h3 : lo + b + 2 * r ≤ a') (h4 : c' + 2 ≤ lo + k + 2 * r)
    (hfa : ∀ i, a' ≤ i → i ≤ c' → B k (f k (state k uv c r (vk k base lo m))) i =
      B k (f k (state k uv c r (vk k base lo m'))) i) :
    Agree k (state k uv c (r + 1) (vk k base lo m)) (state k uv c (r + 1) (vk k base lo m'))
      a' c' := by
  intro i hi1 hi2
  exact point_succ k uv c r _ _ i hk (vk_lt _ _ _ _ hb) (vk_lt _ _ _ _ hb) (by omega)
    (hfa i hi1 hi2) (key_agree k base lo m m' b _ hk hm hm' hab (by omega) (by omega))

theorem trace_zero (k uv : Nat) (c : Nat → Nat) (q kw : Nat) :
    trace k uv c q 0 kw = (q - 13, 0) := by
  simp [trace]

theorem trace_succ (k uv : Nat) (c : Nat → Nat) (q j kw : Nat) :
    trace k uv c q (j + 1) kw =
      ((trace k uv c q j kw).1 - 6 + gain (branch k uv c (5 + 2 * j) (trace k uv c q j kw).1 kw),
       (trace k uv c q j kw).2 + branch k uv c (5 + 2 * j) (trace k uv c q j kw).1 kw * 10 ^ j) := by
  simp only [trace, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem branch_miss (k uv : Nat) (c : Nat → Nat) (r e K : Nat)
    (h : guard k uv c r K e = false) :
    branch k uv c (r + 1) e K = (guard k uv c (r + 1) K (e - 3)).toNat := by
  simp [branch, h]

theorem branch_hit (k uv : Nat) (c : Nat → Nat) (r e K : Nat) (he : 3 ≤ e)
    (h : guard k uv c r K e = true) :
    branch k uv c (r + 1) e K =
      2 + (B k (state k uv c (r + 1) K) (e - 2) ==
          xor (injected k c (r + 1) K (e - 1)) (injected k c (r + 1) K e)).toNat +
        2 * (B k (state k uv c (r + 1) K) (e - 3) == injected k c (r + 1) K e).toNat +
        4 * (guard k uv c (r + 1) K (e - 2)).toNat := by
  simp only [branch, Nat.add_sub_cancel, h, ite_true, Bool.toNat_true]
  rw [show e - 3 + 1 = e - 2 by omega]
  rfl

theorem gain_toNat (b : Bool) : gain b.toNat = b.toNat := by cases b <;> rfl

theorem gain_hit (a b c : Bool) :
    gain (2 + a.toNat + 2 * b.toNat + 4 * c.toNat) = 1 + c.toNat + (a && b && c).toNat := by
  cases a <;> cases b <;> cases c <;> rfl

theorem gain_branch_le (k uv : Nat) (c : Nat → Nat) (r e K : Nat) (he : 3 ≤ e) :
    gain (branch k uv c (r + 1) e K) ≤ 3 := by
  cases h : guard k uv c r K e
  · rw [branch_miss k uv c r e K h, gain_toNat]
    cases guard k uv c (r + 1) K (e - 3) <;> simp
  · rw [branch_hit k uv c r e K he h, gain_hit]
    cases (B k (state k uv c (r + 1) K) (e - 2) ==
          xor (injected k c (r + 1) K (e - 1)) (injected k c (r + 1) K e)) <;>
      cases (B k (state k uv c (r + 1) K) (e - 3) == injected k c (r + 1) K e) <;>
      cases guard k uv c (r + 1) K (e - 2) <;> simp

theorem gain_le_one_of_miss (k uv : Nat) (c : Nat → Nat) (r e K : Nat)
    (h : guard k uv c r K e = false) : gain (branch k uv c (r + 1) e K) ≤ 1 := by
  rw [branch_miss k uv c r e K h, gain_toNat]
  cases guard k uv c (r + 1) K (e - 3) <;> simp


theorem step_inv (k uv : Nat) (c : Nat → Nat) (base lo q j : Nat) (hk : 0 < k)
    (h64 : 64 ≤ 2 ^ k) (huv : uv < 2 ^ k) (hc : ∀ n, c n < 2 ^ k) (hb : base < 2 ^ k)
    (he1 : lo + 19 + 4 * j ≤ (trace k uv c q j base).1)
    (he2 : (trace k uv c q j base).1 + 13 ≤ lo + k)
    (htr : ∀ m, m < 64 → trace k uv c q j (vk k base lo m) = trace k uv c q j base)
    (hw : ∀ m m' b, m < 64 → m' < 64 → b ≤ 5 → AgreeAbove b m m' →
      Agree k (state k uv c (4 + 2 * j) (vk k base lo m))
        (state k uv c (4 + 2 * j) (vk k base lo m'))
        (lo + b + 6 + 4 * j) (trace k uv c q j base).1) :
    (∀ m, m < 64 → trace k uv c q (j + 1) (vk k base lo m) = trace k uv c q (j + 1) base) ∧
    (∀ m m' b, m < 64 → m' < 64 → b ≤ 5 → AgreeAbove b m m' →
      Agree k (state k uv c (4 + 2 * j + 1) (vk k base lo m))
        (state k uv c (4 + 2 * j + 1) (vk k base lo m'))
        (lo + b + 8 + 4 * j) ((trace k uv c q (j + 1) base).1 + 1) ∧
      Agree k (state k uv c (4 + 2 * j + 1 + 1) (vk k base lo m))
        (state k uv c (4 + 2 * j + 1 + 1) (vk k base lo m'))
        (lo + b + 10 + 4 * j) (trace k uv c q (j + 1) base).1) := by
  have htr2 : ∀ m, m < 64 → trace k uv c q (j + 1) (vk k base lo m) =
      ((trace k uv c q j base).1 - 6 +
        gain (branch k uv c (4 + 2 * j + 1) (trace k uv c q j base).1 (vk k base lo m)),
       (trace k uv c q j base).2 +
        branch k uv c (4 + 2 * j + 1) (trace k uv c q j base).1 (vk k base lo m) * 10 ^ j) := by
    intro m hm
    rw [trace_succ, htr m hm, show 5 + 2 * j = 4 + 2 * j + 1 by omega]
  have htr3 : trace k uv c q (j + 1) base =
      ((trace k uv c q j base).1 - 6 +
        gain (branch k uv c (4 + 2 * j + 1) (trace k uv c q j base).1 base),
       (trace k uv c q j base).2 +
        branch k uv c (4 + 2 * j + 1) (trace k uv c q j base).1 base * 10 ^ j) := by
    rw [trace_succ, show 5 + 2 * j = 4 + 2 * j + 1 by omega]
  rw [htr3]
  clear htr3
  generalize (trace k uv c q j base).1 = e at *
  generalize (trace k uv c q j base).2 = e2 at *
  have hm64 : ∀ m, m < 64 → m < 2 ^ k := fun m hm => lt_of_lt_of_le hm h64
  have hSlt : ∀ r K, state k uv c r K < 2 ^ k := fun r K => state_lt k uv c r K huv hc
  have hvk0 := vk_zero k base lo
  have h0 : (0 : Nat) < 2 ^ k := Nat.two_pow_pos k
  -- window for round 5 + 2j
  have W5 : ∀ m m' b, m < 64 → m' < 64 → b ≤ 5 → AgreeAbove b m m' →
      Agree k (state k uv c (4 + 2 * j + 1) (vk k base lo m))
        (state k uv c (4 + 2 * j + 1) (vk k base lo m'))
        (lo + b + 8 + 4 * j) (e - 3 + (guard k uv c (4 + 2 * j) base e).toNat) := by
    intro m m' b hm hm' hb5 hab
    have hW := hw m m' b hm hm' hb5 hab
    apply agree_from_f k uv c base lo b m m' (4 + 2 * j) _ _ hk hb (hm64 m hm) (hm64 m' hm')
      hab (by omega) (by cases guard k uv c (4 + 2 * j) base e <;> simp <;> omega)
    intro i hi1 hi2
    by_cases hi : i + 3 ≤ e
    · exact agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hW (by omega) i (by omega) hi
    · have hhit : guard k uv c (4 + 2 * j) base e = true := by
        cases h : guard k uv c (4 + 2 * j) base e
        · rw [h] at hi2; simp at hi2 <;> omega
        · rfl
      have hi' : i = e - 2 := by rw [hhit] at hi2; simp at hi2 <;> omega
      rw [hi']
      apply agree_f_gate k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hW (by omega)
      have hW0 := hw m 0 5 hm (by norm_num) le_rfl (agreeAbove5 m hm)
      rw [hvk0] at hW0
      rw [hW0 (e - 2) (by omega) (by omega), hW0 (e - 1) (by omega) (by omega),
        hW0 e (by omega) le_rfl]
      exact hhit
  have hreadS : ∀ m, m < 64 → ∀ i, lo + 13 + 4 * j ≤ i →
      i ≤ e - 3 + (guard k uv c (4 + 2 * j) base e).toNat →
      B k (state k uv c (4 + 2 * j + 1) (vk k base lo m)) i =
        B k (state k uv c (4 + 2 * j + 1) base) i := by
    intro m hm i h1 h2
    have := W5 m 0 5 hm (by norm_num) le_rfl (agreeAbove5 m hm)
    rw [hvk0] at this
    exact this i (by omega) h2
  have hhitm : ∀ m, m < 64 →
      guard k uv c (4 + 2 * j) (vk k base lo m) e = guard k uv c (4 + 2 * j) base e := by
    intro m hm
    have hW0 := hw m 0 5 hm (by norm_num) le_rfl (agreeAbove5 m hm)
    rw [hvk0] at hW0
    simp only [guard_eq]
    rw [hW0 (e - 2) (by omega) (by omega), hW0 (e - 1) (by omega) (by omega),
      hW0 e (by omega) le_rfl]
  have hinj : ∀ m, m < 64 → ∀ i, e - 1 ≤ i → i ≤ e →
      injected k c (4 + 2 * j + 1) (vk k base lo m) i =
        injected k c (4 + 2 * j + 1) base i := by
    intro m hm i h1 h2
    rw [injected_eq k c (4 + 2 * j) _ i hk (vk_lt _ _ _ _ hb) (by omega),
      injected_eq k c (4 + 2 * j) _ i hk hb (by omega)]
    rw [key_agree k base lo m 0 5 _ hk (hm64 m hm) h0 (agreeAbove5 m hm) (by omega) (by omega),
      hvk0]
  have hbr : ∀ m, m < 64 → branch k uv c (4 + 2 * j + 1) e (vk k base lo m) =
      branch k uv c (4 + 2 * j + 1) e base := by
    intro m hm
    have hh := hhitm m hm
    cases hB : guard k uv c (4 + 2 * j) base e
    · rw [hB] at hh
      rw [branch_miss k uv c _ e _ hh, branch_miss k uv c _ e _ hB]
      simp only [guard_eq]
      rw [hreadS m hm (e - 3 - 2) (by omega) (by simp [hB] <;> omega),
        hreadS m hm (e - 3 - 1) (by omega) (by simp [hB] <;> omega),
        hreadS m hm (e - 3) (by omega) (by simp [hB])]
    · rw [hB] at hh
      rw [branch_hit k uv c _ e _ (by omega) hh, branch_hit k uv c _ e _ (by omega) hB]
      simp only [guard_eq]
      rw [hreadS m hm (e - 2) (by omega) (by simp [hB] <;> omega),
        hreadS m hm (e - 3) (by omega) (by simp [hB] <;> omega),
        hreadS m hm (e - 2 - 2) (by omega) (by simp [hB] <;> omega),
        hreadS m hm (e - 2 - 1) (by omega) (by simp [hB] <;> omega),
        hinj m hm (e - 1) le_rfl (by omega), hinj m hm e (by omega) le_rfl]
  refine ⟨fun m hm => by rw [htr2 m hm, hbr m hm], ?_⟩
  intro m m' b hm hm' hb5 hab
  have hW5 := W5 m m' b hm hm' hb5 hab
  dsimp only
  generalize hE' : e - 6 + gain (branch k uv c (4 + 2 * j + 1) e base) = e'
  cases hB : guard k uv c (4 + 2 * j) base e
  · -- miss
    rw [hB] at hW5
    simp only [Bool.toNat_false, Nat.add_zero] at hW5
    rw [branch_miss k uv c _ e _ hB, gain_toNat] at hE'
    have hle : (guard k uv c (4 + 2 * j + 1) base (e - 3)).toNat ≤ 1 := by
      cases guard k uv c (4 + 2 * j + 1) base (e - 3) <;> simp
    refine ⟨agree_mono hW5 le_rfl (by omega), ?_⟩
    apply agree_from_f k uv c base lo b m m' (4 + 2 * j + 1) _ _ hk hb (hm64 m hm) (hm64 m' hm')
      hab (by omega) (by omega)
    intro i hi1 hi2
    by_cases hi : i + 3 ≤ e - 3
    · exact agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hW5 (by omega) i (by omega) hi
    · have hnx : guard k uv c (4 + 2 * j + 1) base (e - 3) = true := by
        cases h : guard k uv c (4 + 2 * j + 1) base (e - 3)
        · rw [h] at hE'; simp at hE' <;> omega
        · rfl
      have hi' : i = e - 3 - 2 := by rw [hnx] at hE'; simp at hE' <;> omega
      rw [hi']
      apply agree_f_gate k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hW5 (by omega)
      rw [guard_eq] at hnx
      rw [hreadS m hm (e - 3 - 2) (by omega) (by simp [hB] <;> omega),
        hreadS m hm (e - 3 - 1) (by omega) (by simp [hB] <;> omega),
        hreadS m hm (e - 3) (by omega) (by simp [hB])]
      exact hnx
  · -- hit
    rw [hB] at hW5
    simp only [Bool.toNat_true] at hW5
    have hW5' : Agree k (state k uv c (4 + 2 * j + 1) (vk k base lo m))
        (state k uv c (4 + 2 * j + 1) (vk k base lo m')) (lo + b + 8 + 4 * j) (e - 2) :=
      agree_mono hW5 le_rfl (by omega)
    rw [branch_hit k uv c _ e _ (by omega) hB, gain_hit] at hE'
    generalize hnr : (B k (state k uv c (4 + 2 * j + 1) base) (e - 2) ==
      xor (injected k c (4 + 2 * j + 1) base (e - 1)) (injected k c (4 + 2 * j + 1) base e)) = nr
      at hE'
    generalize hfr : (B k (state k uv c (4 + 2 * j + 1) base) (e - 3) ==
      injected k c (4 + 2 * j + 1) base e) = fr at hE'
    generalize hnx : guard k uv c (4 + 2 * j + 1) base (e - 2) = nx at hE'
    have hle : nx.toNat + (nr && fr && nx).toNat ≤ 2 := by
      cases nx <;> cases nr <;> cases fr <;> simp
    refine ⟨agree_mono hW5' le_rfl (by omega), ?_⟩
    apply agree_from_f k uv c base lo b m m' (4 + 2 * j + 1) _ _ hk hb (hm64 m hm) (hm64 m' hm')
      hab (by omega) (by omega)
    intro i hi1 hi2
    by_cases hi : i + 3 ≤ e - 2
    · exact agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hW5' (by omega) i (by omega) hi
    · have hnxt : nx = true := by
        cases nx
        · simp at hE' <;> omega
        · rfl
      subst hnxt
      by_cases hi4 : i = e - 2 - 2
      · rw [hi4]
        apply agree_f_gate k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hW5' (by omega)
        rw [guard_eq] at hnx
        rw [hreadS m hm (e - 2 - 2) (by omega) (by simp [hB] <;> omega),
          hreadS m hm (e - 2 - 1) (by omega) (by simp [hB] <;> omega),
          hreadS m hm (e - 2) (by omega) (by simp [hB] <;> omega)]
        exact hnx
      · have hi3 : i = e - 3 := by omega
        have hall : nr = true ∧ fr = true := by
          cases nr <;> cases fr <;> simp at hE' ⊢ <;> omega
        rw [hall.1] at hnr
        rw [hall.2] at hfr
        have hv9 : ∀ m₀, m₀ < 64 → B k (f k (state k uv c (4 + 2 * j + 1) (vk k base lo m₀))) (e - 3) =
            xor (xor (B k (state k uv c (4 + 2 * j + 1) (vk k base lo m₀)) (e - 4))
              (B k (state k uv c (4 + 2 * j + 1) (vk k base lo m₀)) (e - 3)))
              (B k (state k uv c (4 + 2 * j + 1) (vk k base lo m₀)) (e - 2)) := by
          intro m₀ hm₀
          apply v9 k uv c (4 + 2 * j) (vk k base lo m₀) e hk huv hc (by omega)
          · have := hhitm m₀ hm₀
            rw [hB, guard_eq] at this
            exact this
          · rw [hreadS m₀ hm₀ (e - 2) (by omega) (by simp [hB] <;> omega),
              hinj m₀ hm₀ (e - 1) le_rfl (by omega), hinj m₀ hm₀ e (by omega) le_rfl]
            exact hnr
          · rw [hreadS m₀ hm₀ (e - 3) (by omega) (by simp [hB] <;> omega),
              hinj m₀ hm₀ e (by omega) le_rfl]
            exact hfr
        rw [hi3, hv9 m hm, hv9 m' hm', hW5' (e - 4) (by omega) (by omega),
          hW5' (e - 3) (by omega) (by omega), hW5' (e - 2) (by omega) le_rfl]


theorem pk_facts2 : ∀ y : Fin 16, pack 2 y.val < 64 ∧
    (pack 2 y.val).testBit 5 = decide (y.val % 2 = 1) ∧ (pack 2 y.val).testBit 4 = false ∧
    (pack 2 y.val).testBit 3 = decide (y.val / 2 % 2 = 1) ∧
    (pack 2 y.val).testBit 2 = decide (y.val / 4 % 2 = 1) ∧
    (pack 2 y.val).testBit 1 = decide (y.val / 8 % 2 = 1) ∧ (pack 2 y.val).testBit 0 = false := by
  decide

theorem pk_facts0 : ∀ y : Fin 4, pack 0 y.val < 64 ∧
    (pack 0 y.val).testBit 5 = decide (y.val % 2 = 1) ∧ (pack 0 y.val).testBit 4 = false ∧
    (pack 0 y.val).testBit 3 = false ∧ (pack 0 y.val).testBit 2 = false ∧
    (pack 0 y.val).testBit 1 = false ∧ (pack 0 y.val).testBit 0 = decide (y.val / 2 % 2 = 1) := by
  decide

theorem agreeAbove_of (b m m' : Nat) (hm : m < 64) (hm' : m' < 64)
    (h : ∀ i, b < i → i ≤ 5 → m.testBit i = m'.testBit i) : AgreeAbove b m m' := by
  intro i hi
  by_cases h6 : i ≤ 5
  · exact h i hi h6
  · rw [testBit_ge m 6 i (by simpa using hm) (by omega),
      testBit_ge m' 6 i (by simpa using hm') (by omega)]

theorem xor_eq_false (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

theorem bool_nat (v : Nat) (hv : v < 2) (b : Bool) : decide (v = 1) = b ↔ v = b.toNat := by
  cases b <;> simp <;> omega

theorem xor_cancel (a b c : Bool) (h : xor a b = c) : xor a c = b := by
  subst h; cases a <;> cases b <;> rfl

theorem tn_inj (n f x n' f' x' : Bool)
    (h : 2 + n.toNat + 2 * f.toNat + 4 * x.toNat = 2 + n'.toNat + 2 * f'.toNat + 4 * x'.toNat) :
    n = n' ∧ f = f' ∧ x = x' := by
  revert h
  cases n <;> cases f <;> cases x <;> cases n' <;> cases f' <;> cases x' <;> decide

theorem solve_lo (hitF nxM : Nat → Bool) (brF : Nat → Nat) (h0 : Bool) (l : Nat) (hl : l < 2)
    (hbr : ∀ m, m < 64 → hitF m = false → brF m = (nxM m).toNat)
    (hbr2 : ∀ m, m < 64 → hitF m = true → 2 ≤ brF m)
    (hH : ∀ m, m < 64 → hitF m = xor h0 (m.testBit 5))
    (hM : ∀ m m', m < 64 → m' < 64 → AgreeAbove 0 m m' →
      nxM m = xor (nxM m') (xor (m.testBit 0) (m'.testBit 0))) :
    ∃! y : Fin 4, brF (pack 0 y.val) = l := by
  have hy0 : h0.toNat < 4 := by cases h0 <;> decide
  obtain ⟨lt0, a5, a4, a3, a2, a1, a0⟩ := pk_facts0 ⟨h0.toNat, hy0⟩
  simp only at lt0 a5 a4 a3 a2 a1 a0
  have a0' : (pack 0 h0.toNat).testBit 0 = false := by rw [a0]; cases h0 <;> simp
  generalize hr : nxM (pack 0 h0.toNat) = r
  have key : ∀ y : Fin 4, brF (pack 0 y.val) = l ↔
      (y.val % 2 = h0.toNat ∧ y.val / 2 % 2 = (xor r (decide (l = 1))).toNat) := by
    intro y
    obtain ⟨lt, b5, b4, b3, b2, b1, b0⟩ := pk_facts0 y
    have hy := y.isLt
    have hag : y.val % 2 = h0.toNat → AgreeAbove 0 (pack 0 y.val) (pack 0 h0.toNat) := by
      intro h5
      apply agreeAbove_of 0 _ _ lt lt0
      intro i hi1 hi2
      interval_cases i
      · rw [b1, a1]
      · rw [b2, a2]
      · rw [b3, a3]
      · rw [b4, a4]
      · rw [b5, a5, h5]
        cases h0 <;> rfl
    have hM' : y.val % 2 = h0.toNat →
        nxM (pack 0 y.val) = xor r (decide (y.val / 2 % 2 = 1)) := by
      intro h5
      rw [hM _ _ lt lt0 (hag h5), hr, b0, a0']
      cases r <;> cases decide (y.val / 2 % 2 = 1) <;> rfl
    have hhit : hitF (pack 0 y.val) = false ↔ y.val % 2 = h0.toNat := by
      rw [hH _ lt, b5, xor_eq_false, eq_comm, bool_nat _ (by omega)]
    constructor
    · intro hb
      have hmiss : hitF (pack 0 y.val) = false := by
        cases h : hitF (pack 0 y.val)
        · rfl
        · have := hbr2 _ lt h; omega
      have h5 := hhit.1 hmiss
      refine ⟨h5, ?_⟩
      rw [hbr _ lt hmiss, hM' h5] at hb
      have hyl : y.val / 2 % 2 < 2 := by omega
      revert hb
      generalize y.val / 2 % 2 = w at hyl ⊢
      cases r <;> rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;>
        rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl <;> simp
    · rintro ⟨h5, h1⟩
      rw [hbr _ lt (hhit.2 h5), hM' h5]
      revert h1
      have hyl : y.val / 2 % 2 < 2 := by omega
      generalize y.val / 2 % 2 = w at hyl ⊢
      cases r <;> rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;>
        rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl <;> simp
  generalize hbb : xor r (decide (l = 1)) = bb at key
  have hc : h0.toNat + 2 * bb.toNat < 4 := by cases h0 <;> cases bb <;> decide
  refine ⟨⟨_, hc⟩, (key _).2 ?_, fun y hy => ?_⟩
  · simp only
    constructor
    · cases h0 <;> cases bb <;> decide
    · cases h0 <;> cases bb <;> decide
  · have := (key y).1 hy
    apply Fin.ext
    simp only
    have := y.isLt
    omega

theorem solve_hi (hitF nearF farF nxH : Nat → Bool) (brF : Nat → Nat) (h0 : Bool) (l : Nat)
    (hl1 : 2 ≤ l) (hl2 : l < 10)
    (hbr : ∀ m, m < 64 → hitF m = true →
      brF m = 2 + (nearF m).toNat + 2 * (farF m).toNat + 4 * (nxH m).toNat)
    (hbr2 : ∀ m, m < 64 → hitF m = false → brF m < 2)
    (hH : ∀ m, m < 64 → hitF m = xor h0 (m.testBit 5))
    (hN : ∀ m m', m < 64 → m' < 64 → hitF m = true → hitF m' = true → AgreeAbove 3 m m' →
      nearF m = xor (nearF m') (xor (m.testBit 3) (m'.testBit 3)))
    (hF : ∀ m m', m < 64 → m' < 64 → hitF m = true → hitF m' = true → AgreeAbove 2 m m' →
      farF m = xor (farF m') (xor (m.testBit 2) (m'.testBit 2)))
    (hX : ∀ m m', m < 64 → m' < 64 → hitF m = true → hitF m' = true → AgreeAbove 1 m m' →
      nxH m = xor (nxH m') (xor (m.testBit 1) (m'.testBit 1))) :
    ∃! y : Fin 16, brF (pack 2 y.val) = l := by
  have hfact : ∀ y : Nat, y < 16 → pack 2 y < 64 ∧ (pack 2 y).testBit 5 = decide (y % 2 = 1) ∧
      (pack 2 y).testBit 4 = false ∧ (pack 2 y).testBit 3 = decide (y / 2 % 2 = 1) ∧
      (pack 2 y).testBit 2 = decide (y / 4 % 2 = 1) ∧
      (pack 2 y).testBit 1 = decide (y / 8 % 2 = 1) ∧ (pack 2 y).testBit 0 = false :=
    fun y hy => pk_facts2 ⟨y, hy⟩
  have hhit : ∀ y, y < 16 → (hitF (pack 2 y) = true ↔ y % 2 = (!h0).toNat) := by
    intro y hy
    obtain ⟨lt, b5, -⟩ := hfact y hy
    rw [hH _ lt, b5]
    cases h0 <;> simp <;> omega
  generalize ha : (!h0).toNat = a at hhit
  have ha2 : a < 2 := by rw [← ha]; cases h0 <;> decide
  have hNy : ∀ y, y < 16 → y % 2 = a →
      nearF (pack 2 y) = xor (nearF (pack 2 a)) (decide (y / 2 % 2 = 1)) := by
    intro y hy h5
    obtain ⟨lt, b5, b4, b3, b2, b1, b0⟩ := hfact y hy
    obtain ⟨lt', c5, c4, c3, c2, c1, c0⟩ := hfact a (by omega)
    rw [hN _ _ lt lt' ((hhit y hy).2 h5) ((hhit a (by omega)).2 (by omega)) ?_, b3, c3]
    · have : a / 2 % 2 = 0 := by omega
      rw [this]
      cases nearF (pack 2 a) <;> cases decide (y / 2 % 2 = 1) <;> rfl
    · apply agreeAbove_of 3 _ _ lt lt'
      intro i hi1 hi2
      interval_cases i
      · rw [b4, c4]
      · rw [b5, c5, h5, show a % 2 = a by omega]
  generalize hb1 : xor (nearF (pack 2 a)) (decide ((l - 2) % 2 = 1)) = b1
  have hy1 : a + 2 * b1.toNat < 4 := by cases b1 <;> simp <;> omega
  have hFy : ∀ y, y < 16 → y % 4 = a + 2 * b1.toNat →
      farF (pack 2 y) = xor (farF (pack 2 (a + 2 * b1.toNat))) (decide (y / 4 % 2 = 1)) := by
    intro y hy h5
    obtain ⟨lt, b5, b4, b3, b2, b1', b0⟩ := hfact y hy
    obtain ⟨lt', c5, c4, c3, c2, c1, c0⟩ := hfact (a + 2 * b1.toNat) (by omega)
    rw [hF _ _ lt lt' ((hhit y hy).2 (by omega)) ((hhit _ (by omega)).2 (by omega)) ?_, b2, c2]
    · have : (a + 2 * b1.toNat) / 4 % 2 = 0 := by omega
      rw [this]
      cases farF (pack 2 (a + 2 * b1.toNat)) <;> cases decide (y / 4 % 2 = 1) <;> rfl
    · apply agreeAbove_of 2 _ _ lt lt'
      intro i hi1 hi2
      interval_cases i
      · rw [b3, c3, show y / 2 % 2 = (a + 2 * b1.toNat) / 2 % 2 by omega]
      · rw [b4, c4]
      · rw [b5, c5, show y % 2 = (a + 2 * b1.toNat) % 2 by omega]
  generalize hb2 : xor (farF (pack 2 (a + 2 * b1.toNat))) (decide ((l - 2) / 2 % 2 = 1)) = b2
  have hy2 : a + 2 * b1.toNat + 4 * b2.toNat < 8 := by cases b1 <;> cases b2 <;> simp <;> omega
  have hXy : ∀ y, y < 16 → y % 8 = a + 2 * b1.toNat + 4 * b2.toNat →
      nxH (pack 2 y) = xor (nxH (pack 2 (a + 2 * b1.toNat + 4 * b2.toNat)))
        (decide (y / 8 % 2 = 1)) := by
    intro y hy h5
    obtain ⟨lt, b5, b4, b3, b2', b1', b0⟩ := hfact y hy
    obtain ⟨lt', c5, c4, c3, c2, c1, c0⟩ := hfact (a + 2 * b1.toNat + 4 * b2.toNat) (by omega)
    rw [hX _ _ lt lt' ((hhit y hy).2 (by omega)) ((hhit _ (by omega)).2 (by omega)) ?_, b1', c1]
    · have : (a + 2 * b1.toNat + 4 * b2.toNat) / 8 % 2 = 0 := by omega
      rw [this]
      cases nxH (pack 2 (a + 2 * b1.toNat + 4 * b2.toNat)) <;> cases decide (y / 8 % 2 = 1) <;> rfl
    · apply agreeAbove_of 1 _ _ lt lt'
      intro i hi1 hi2
      interval_cases i
      · rw [b2', c2, show y / 4 % 2 = (a + 2 * b1.toNat + 4 * b2.toNat) / 4 % 2 by omega]
      · rw [b3, c3, show y / 2 % 2 = (a + 2 * b1.toNat + 4 * b2.toNat) / 2 % 2 by omega]
      · rw [b4, c4]
      · rw [b5, c5, show y % 2 = (a + 2 * b1.toNat + 4 * b2.toNat) % 2 by omega]
  generalize hb3 : xor (nxH (pack 2 (a + 2 * b1.toNat + 4 * b2.toNat)))
    (decide ((l - 2) / 4 % 2 = 1)) = b3
  have hl : l = 2 + (decide ((l - 2) % 2 = 1)).toNat + 2 * (decide ((l - 2) / 2 % 2 = 1)).toNat +
      4 * (decide ((l - 2) / 4 % 2 = 1)).toNat := by
    interval_cases l <;> decide
  have hy3 : a + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat < 16 := by
    cases b1 <;> cases b2 <;> cases b3 <;> simp <;> omega
  have hdec : ∀ (v : Nat) (b : Bool), v < 2 → (decide (v = 1) = b ↔ v = b.toNat) :=
    fun v b hv => bool_nat v hv b
  refine ⟨⟨_, hy3⟩, ?_, fun y hy => ?_⟩
  · simp only
    set Y := a + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat with hY
    have e1 : Y % 2 = a := by cases b1 <;> cases b2 <;> cases b3 <;> simp [hY] <;> omega
    have e2 : Y / 2 % 2 = b1.toNat := by cases b1 <;> cases b2 <;> cases b3 <;> simp [hY] <;> omega
    have e3 : Y / 4 % 2 = b2.toNat := by cases b1 <;> cases b2 <;> cases b3 <;> simp [hY] <;> omega
    have e4 : Y / 8 % 2 = b3.toNat := by cases b1 <;> cases b2 <;> cases b3 <;> simp [hY] <;> omega
    have e12 : Y % 4 = a + 2 * b1.toNat := by cases b1 <;> cases b2 <;> cases b3 <;> simp [hY] <;> omega
    have e123 : Y % 8 = a + 2 * b1.toNat + 4 * b2.toNat := by
      cases b1 <;> cases b2 <;> cases b3 <;> simp [hY] <;> omega
    rw [hbr _ (hfact Y hy3).1 ((hhit Y hy3).2 e1), hNy Y hy3 e1, hFy Y hy3 e12, hXy Y hy3 e123]
    rw [(hdec _ _ (by omega)).2 e2, (hdec _ _ (by omega)).2 e3, (hdec _ _ (by omega)).2 e4]
    rw [xor_cancel _ _ _ hb1, xor_cancel _ _ _ hb2, xor_cancel _ _ _ hb3]
    exact hl.symm
  · obtain ⟨y, hy16⟩ := y
    simp only at hy
    have hhy : hitF (pack 2 y) = true := by
      cases h : hitF (pack 2 y)
      · have := hbr2 _ (hfact y hy16).1 h; omega
      · rfl
    have e1 := (hhit y hy16).1 hhy
    rw [hbr _ (hfact y hy16).1 hhy] at hy
    rw [hl] at hy
    obtain ⟨hn, hf, hx⟩ := tn_inj _ _ _ _ _ _ hy
    rw [hNy y hy16 e1] at hn
    have e2 : y / 2 % 2 = b1.toNat := by
      rw [← hdec _ _ (by omega), ← hb1, ← hn]
      cases nearF (pack 2 a) <;> cases decide (y / 2 % 2 = 1) <;> rfl
    rw [hFy y hy16 (by cases b1 <;> simp at e2 ⊢ <;> omega)] at hf
    have e3 : y / 4 % 2 = b2.toNat := by
      rw [← hdec _ _ (by omega), ← hb2, ← hf]
      cases farF (pack 2 (a + 2 * b1.toNat)) <;> cases decide (y / 4 % 2 = 1) <;> rfl
    rw [hXy y hy16 (by cases b1 <;> cases b2 <;> simp at e2 e3 ⊢ <;> omega)] at hx
    have e4 : y / 8 % 2 = b3.toNat := by
      rw [← hdec _ _ (by omega), ← hb3, ← hx]
      cases nxH (pack 2 (a + 2 * b1.toNat + 4 * b2.toNat)) <;> cases decide (y / 8 % 2 = 1) <;> rfl
    apply Fin.ext
    simp only
    omega


theorem pivot_diff (k uv : Nat) (c : Nat → Nat) (base lo r m m' i bb : Nat) (hk : 0 < k)
    (hb : base < 2 ^ k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k) (hi : 2 * r ≤ i)
    (hpos : i - 2 * r + 1 = lo + bb) (hpos2 : i - 2 * r + 2 ≤ lo + k)
    (hf : B k (f k (state k uv c r (vk k base lo m))) i =
      B k (f k (state k uv c r (vk k base lo m'))) i) :
    B k (state k uv c (r + 1) (vk k base lo m)) i =
      xor (B k (state k uv c (r + 1) (vk k base lo m')) i) (xor (m.testBit bb) (m'.testBit bb)) := by
  rw [B_state_succ, B_state_succ, injected_eq k c r _ i hk (vk_lt _ _ _ _ hb) hi,
    injected_eq k c r _ i hk (vk_lt _ _ _ _ hb) hi, B_key k base lo m _ hk hm (by omega) hpos2,
    B_key k base lo m' _ hk hm' (by omega) hpos2, hf, show i - 2 * r + 1 - lo = bb by omega]
  cases B k (f k (state k uv c r (vk k base lo m'))) i <;> cases B k base (i - 2 * r) <;>
    cases m.testBit bb <;> cases m'.testBit bb <;> cases B k (c (r + 1)) i <;> rfl

theorem point_key (k uv : Nat) (c : Nat → Nat) (base lo b r m m' i : Nat) (hk : 0 < k)
    (hb : base < 2 ^ k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k) (hab : AgreeAbove b m m')
    (hi : 2 * r ≤ i) (hpos : lo + b ≤ i - 2 * r) (hpos2 : i - 2 * r + 2 ≤ lo + k)
    (hf : B k (f k (state k uv c r (vk k base lo m))) i =
      B k (f k (state k uv c r (vk k base lo m'))) i) :
    B k (state k uv c (r + 1) (vk k base lo m)) i = B k (state k uv c (r + 1) (vk k base lo m')) i :=
  point_succ k uv c r _ _ i hk (vk_lt _ _ _ _ hb) (vk_lt _ _ _ _ hb) hi hf
    (key_agree k base lo m m' b _ hk hm hm' hab hpos hpos2)

theorem final_facts (k uv : Nat) (c : Nat → Nat) (base lo n x : Nat) (hk : 0 < k)
    (h64 : 64 ≤ 2 ^ k) (huv : uv < 2 ^ k) (hc : ∀ n, c n < 2 ^ k) (hb : base < 2 ^ k)
    (hlo : 1 ≤ lo) (hx : x = lo + 2 * n + 6) (hkx : 8 ≤ k) (hn : 2 ≤ n)
    (WA : ∀ m m' b, m < 64 → m' < 64 → b ≤ 5 → AgreeAbove b m m' →
      Agree k (state k uv c n (vk k base lo m)) (state k uv c n (vk k base lo m'))
        (lo + b + 2 * n - 2) (x + 1))
    (WB : ∀ m m' b, m < 64 → m' < 64 → b ≤ 5 → AgreeAbove b m m' →
      Agree k (state k uv c (n + 1) (vk k base lo m)) (state k uv c (n + 1) (vk k base lo m'))
        (lo + b + 2 * n) x) :
    ∀ label : Fin 10, ∃! assignment : Fin (2 ^ (if label.val < 2 then 2 else 4)),
      branch k uv c (n + 1 + 1) x (vk k base lo (pack label.val assignment.val)) = label.val := by
  have hm64 : ∀ m, m < 64 → m < 2 ^ k := fun m hm => lt_of_lt_of_le hm h64
  have hSlt : ∀ r K, state k uv c r K < 2 ^ k := fun r K => state_lt k uv c r K huv hc
  -- hit relation
  have hH : ∀ m, m < 64 → guard k uv c (n + 1) (vk k base lo m) x =
      xor (guard k uv c (n + 1) (vk k base lo 0) x) (m.testBit 5) := by
    intro m hm
    have hA := WA m 0 5 hm (by norm_num) le_rfl (agreeAbove5 m hm)
    have hB := WB m 0 5 hm (by norm_num) le_rfl (agreeAbove5 m hm)
    simp only [guard_eq]
    rw [hB (x - 1) (by omega) (by omega), hB x (by omega) le_rfl,
      pivot_diff k uv c base lo n m 0 (x - 2) 5 hk hb (hm64 m hm) (by positivity) (by omega)
        (by omega) (by omega)
        (agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hA (by omega) (x - 2) (by omega) (by omega)),
      Nat.zero_testBit]
    cases B k (state k uv c (n + 1) (vk k base lo 0)) (x - 2) <;>
      cases B k (state k uv c (n + 1) (vk k base lo 0)) (x - 1) <;>
      cases B k (state k uv c (n + 1) (vk k base lo 0)) x <;> cases m.testBit 5 <;> rfl
  -- miss next relation
  have hM : ∀ m m', m < 64 → m' < 64 → AgreeAbove 0 m m' →
      guard k uv c (n + 1 + 1) (vk k base lo m) (x - 3) =
        xor (guard k uv c (n + 1 + 1) (vk k base lo m') (x - 3))
          (xor (m.testBit 0) (m'.testBit 0)) := by
    intro m m' hm hm' hab
    have hB := WB m m' 0 hm hm' (by norm_num) hab
    simp only [guard_eq]
    rw [show x - 3 - 2 = x - 5 by omega, show x - 3 - 1 = x - 4 by omega]
    rw [pivot_diff k uv c base lo (n + 1) m m' (x - 5) 0 hk hb (hm64 m hm) (hm64 m' hm')
        (by omega) (by omega) (by omega)
        (agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) (x - 5) (by omega) (by omega)),
      point_key k uv c base lo 0 (n + 1) m m' (x - 4) hk hb (hm64 m hm) (hm64 m' hm') hab
        (by omega) (by omega) (by omega)
        (agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) (x - 4) (by omega) (by omega)),
      point_key k uv c base lo 0 (n + 1) m m' (x - 3) hk hb (hm64 m hm) (hm64 m' hm') hab
        (by omega) (by omega) (by omega)
        (agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) (x - 3) (by omega) (by omega))]
    cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 5) <;>
      cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 4) <;>
      cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 3) <;>
      cases m.testBit 0 <;> cases m'.testBit 0 <;> rfl
  -- injected agreement
  have hinj : ∀ m m' b, m < 64 → m' < 64 → AgreeAbove b m m' → ∀ i, x - 1 ≤ i → i ≤ x →
      lo + b + 2 * n + 2 ≤ i →
      injected k c (n + 1 + 1) (vk k base lo m) i = injected k c (n + 1 + 1) (vk k base lo m') i := by
    intro m m' b hm hm' hab i h1 h2 h3
    rw [injected_eq k c (n + 1) _ i hk (vk_lt _ _ _ _ hb) (by omega),
      injected_eq k c (n + 1) _ i hk (vk_lt _ _ _ _ hb) (by omega),
      key_agree k base lo m m' b _ hk (hm64 m hm) (hm64 m' hm') hab (by omega) (by omega)]
  -- near relation
  have hN : ∀ m m', m < 64 → m' < 64 → guard k uv c (n + 1) (vk k base lo m) x = true →
      guard k uv c (n + 1) (vk k base lo m') x = true → AgreeAbove 3 m m' →
      (B k (state k uv c (n + 1 + 1) (vk k base lo m)) (x - 2) ==
        xor (injected k c (n + 1 + 1) (vk k base lo m) (x - 1))
          (injected k c (n + 1 + 1) (vk k base lo m) x)) =
      xor (B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 2) ==
        xor (injected k c (n + 1 + 1) (vk k base lo m') (x - 1))
          (injected k c (n + 1 + 1) (vk k base lo m') x)) (xor (m.testBit 3) (m'.testBit 3)) := by
    intro m m' hm hm' hh hh' hab
    have hB := WB m m' 3 hm hm' (by norm_num) hab
    rw [guard_eq] at hh
    rw [pivot_diff k uv c base lo (n + 1) m m' (x - 2) 3 hk hb (hm64 m hm) (hm64 m' hm')
        (by omega) (by omega) (by omega)
        (agree_f_gate k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) hh),
      hinj m m' 3 hm hm' hab (x - 1) le_rfl (by omega) (by omega),
      hinj m m' 3 hm hm' hab x (by omega) le_rfl (by omega)]
    cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 2) <;>
      cases injected k c (n + 1 + 1) (vk k base lo m') (x - 1) <;>
      cases injected k c (n + 1 + 1) (vk k base lo m') x <;>
      cases m.testBit 3 <;> cases m'.testBit 3 <;> rfl
  -- far relation
  have hF : ∀ m m', m < 64 → m' < 64 → guard k uv c (n + 1) (vk k base lo m) x = true →
      guard k uv c (n + 1) (vk k base lo m') x = true → AgreeAbove 2 m m' →
      (B k (state k uv c (n + 1 + 1) (vk k base lo m)) (x - 3) ==
        injected k c (n + 1 + 1) (vk k base lo m) x) =
      xor (B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 3) ==
        injected k c (n + 1 + 1) (vk k base lo m') x) (xor (m.testBit 2) (m'.testBit 2)) := by
    intro m m' hm hm' _ _ hab
    have hB := WB m m' 2 hm hm' (by norm_num) hab
    rw [pivot_diff k uv c base lo (n + 1) m m' (x - 3) 2 hk hb (hm64 m hm) (hm64 m' hm')
        (by omega) (by omega) (by omega)
        (agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) (x - 3) (by omega) (by omega)),
      hinj m m' 2 hm hm' hab x (by omega) le_rfl (by omega)]
    cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 3) <;>
      cases injected k c (n + 1 + 1) (vk k base lo m') x <;>
      cases m.testBit 2 <;> cases m'.testBit 2 <;> rfl
  -- hit next relation
  have hX : ∀ m m', m < 64 → m' < 64 → guard k uv c (n + 1) (vk k base lo m) x = true →
      guard k uv c (n + 1) (vk k base lo m') x = true → AgreeAbove 1 m m' →
      guard k uv c (n + 1 + 1) (vk k base lo m) (x - 2) =
        xor (guard k uv c (n + 1 + 1) (vk k base lo m') (x - 2))
          (xor (m.testBit 1) (m'.testBit 1)) := by
    intro m m' hm hm' hh _ hab
    have hB := WB m m' 1 hm hm' (by norm_num) hab
    rw [guard_eq] at hh
    simp only [guard_eq]
    rw [show x - 2 - 2 = x - 4 by omega, show x - 2 - 1 = x - 3 by omega]
    rw [pivot_diff k uv c base lo (n + 1) m m' (x - 4) 1 hk hb (hm64 m hm) (hm64 m' hm')
        (by omega) (by omega) (by omega)
        (agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) (x - 4) (by omega) (by omega)),
      point_key k uv c base lo 1 (n + 1) m m' (x - 3) hk hb (hm64 m hm) (hm64 m' hm') hab
        (by omega) (by omega) (by omega)
        (agree_f k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) (x - 3) (by omega) (by omega)),
      point_key k uv c base lo 1 (n + 1) m m' (x - 2) hk hb (hm64 m hm) (hm64 m' hm') hab
        (by omega) (by omega) (by omega)
        (agree_f_gate k _ _ _ _ hk (hSlt _ _) (hSlt _ _) hB (by omega) hh)]
    cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 4) <;>
      cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 3) <;>
      cases B k (state k uv c (n + 1 + 1) (vk k base lo m')) (x - 2) <;>
      cases m.testBit 1 <;> cases m'.testBit 1 <;> rfl
  intro label
  obtain ⟨l, hl10⟩ := label
  simp only
  by_cases hl : l < 2
  · have e4 : (2 ^ (if l < 2 then 2 else 4)) = 4 := by simp [hl]
    rw [e4]
    have hpk : ∀ y, pack l y = pack 0 y := by intro y; simp [pack, hl]
    simp only [hpk]
    exact solve_lo (fun m => guard k uv c (n + 1) (vk k base lo m) x)
      (fun m => guard k uv c (n + 1 + 1) (vk k base lo m) (x - 3))
      (fun m => branch k uv c (n + 1 + 1) x (vk k base lo m))
      (guard k uv c (n + 1) (vk k base lo 0) x) l hl
      (fun m _ h => branch_miss k uv c (n + 1) x _ h)
      (fun m _ h => by rw [branch_hit k uv c (n + 1) x _ (by omega) h]; omega)
      hH hM
  · have e16 : (2 ^ (if l < 2 then 2 else 4)) = 16 := by simp [hl]
    rw [e16]
    have hpk : ∀ y, pack l y = pack 2 y := by intro y; simp [pack, hl]
    simp only [hpk]
    exact solve_hi (fun m => guard k uv c (n + 1) (vk k base lo m) x)
      (fun m => (B k (state k uv c (n + 1 + 1) (vk k base lo m)) (x - 2) ==
        xor (injected k c (n + 1 + 1) (vk k base lo m) (x - 1))
          (injected k c (n + 1 + 1) (vk k base lo m) x)))
      (fun m => (B k (state k uv c (n + 1 + 1) (vk k base lo m)) (x - 3) ==
        injected k c (n + 1 + 1) (vk k base lo m) x))
      (fun m => guard k uv c (n + 1 + 1) (vk k base lo m) (x - 2))
      (fun m => branch k uv c (n + 1 + 1) x (vk k base lo m))
      (guard k uv c (n + 1) (vk k base lo 0) x) l (by omega) hl10
      (fun m _ h => branch_hit k uv c (n + 1) x _ (by omega) h)
      (fun m _ h => by
        rw [branch_miss k uv c (n + 1) x _ h]
        cases guard k uv c (n + 1 + 1) (vk k base lo m) (x - 3) <;> simp)
      hH hN hF hX


theorem edge_succ (k uv : Nat) (c : Nat → Nat) (q j base : Nat)
    (h6 : 6 ≤ (trace k uv c q j base).1) :
    (trace k uv c q (j + 1) base).1 + 3 ≤ (trace k uv c q j base).1 ∧
    (trace k uv c q j base).1 ≤ (trace k uv c q (j + 1) base).1 + 6 := by
  rw [trace_succ, show 5 + 2 * j = 4 + 2 * j + 1 by omega]
  have := gain_branch_le k uv c (4 + 2 * j) (trace k uv c q j base).1 base (by omega)
  simp only
  omega

theorem edges (k uv : Nat) (c : Nat → Nat) (q p base : Nat) (hq : 19 + 6 * p ≤ q) :
    ∀ j, j ≤ p → q - 13 ≤ (trace k uv c q j base).1 + 6 * j ∧
      (trace k uv c q j base).1 + 3 * j ≤ q - 13 := by
  intro j
  induction j with
  | zero => intro _; simp [trace_zero]
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have := edge_succ k uv c q j base (by omega)
    omega

theorem edges_mono (k uv : Nat) (c : Nat → Nat) (q p base : Nat) (hq : 19 + 6 * p ≤ q) :
    ∀ d j, j + d ≤ p → (trace k uv c q (j + d) base).1 + 3 * d ≤ (trace k uv c q j base).1 := by
  intro d
  induction d with
  | zero => intro j _; simp
  | succ d ih =>
    intro j hjd
    have h1 := ih j (by omega)
    have h2 := (edges k uv c q p base hq (j + d) (by omega)).1
    have h3 := edge_succ k uv c q (j + d) base (by omega)
    rw [show j + (d + 1) = j + d + 1 by omega]
    omega

def Inv (k uv : Nat) (c : Nat → Nat) (base lo q j : Nat) : Prop :=
  (∀ m, m < 64 → trace k uv c q j (vk k base lo m) = trace k uv c q j base) ∧
  ∀ m m' b, m < 64 → m' < 64 → b ≤ 5 → AgreeAbove b m m' →
    Agree k (state k uv c (3 + 2 * j) (vk k base lo m)) (state k uv c (3 + 2 * j) (vk k base lo m'))
      (lo + b + 4 + 4 * j) ((trace k uv c q j base).1 + 1) ∧
    Agree k (state k uv c (4 + 2 * j) (vk k base lo m)) (state k uv c (4 + 2 * j) (vk k base lo m'))
      (lo + b + 6 + 4 * j) (trace k uv c q j base).1

theorem inv_zero (k uv : Nat) (c : Nat → Nat) (base lo q : Nat) (hk : 13 ≤ k)
    (h64 : 64 ≤ 2 ^ k) (huv : uv < 2 ^ k) (hc : ∀ n, c n < 2 ^ k) (hb : base < 2 ^ k)
    (hq : q ≤ lo + k) (hq13 : 13 ≤ q) : Inv k uv c base lo q 0 := by
  refine ⟨fun m _ => by simp [trace_zero], ?_⟩
  intro m m' b hm hm' hb5 hab
  have hm1 := lt_of_lt_of_le hm h64
  have hm1' := lt_of_lt_of_le hm' h64
  have hk0 : 0 < k := by omega
  have A0 := agree_zero k uv c base lo b m m' hk0 hb hm1 hm1' hab
  have A1 := agree_round k uv c base lo b m m' 0 _ _ (lo + b + 2) (lo + k - 4) hk0 huv hc hb hm1
    hm1' hab A0 (by omega) (by omega) (by omega) (by omega) (by omega)
  have A2 := agree_round k uv c base lo b m m' 1 _ _ (lo + b + 3) (lo + k - 7) hk0 huv hc hb hm1
    hm1' hab A1 (by omega) (by omega) (by omega) (by omega) (by omega)
  have A3 := agree_round k uv c base lo b m m' 2 _ _ (lo + b + 4) (lo + k - 10) hk0 huv hc hb hm1
    hm1' hab A2 (by omega) (by omega) (by omega) (by omega) (by omega)
  have A4 := agree_round k uv c base lo b m m' 3 _ _ (lo + b + 6) (lo + k - 13) hk0 huv hc hb hm1
    hm1' hab A3 (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [trace_zero]
  exact ⟨agree_mono A3 (by omega) (by omega), agree_mono A4 (by omega) (by omega)⟩

theorem inv_succ (k uv : Nat) (c : Nat → Nat) (base lo q j : Nat) (hk0 : 0 < k)
    (h64 : 64 ≤ 2 ^ k) (huv : uv < 2 ^ k) (hc : ∀ n, c n < 2 ^ k) (hb : base < 2 ^ k)
    (he1 : lo + 19 + 4 * j ≤ (trace k uv c q j base).1)
    (he2 : (trace k uv c q j base).1 + 13 ≤ lo + k)
    (h : Inv k uv c base lo q j) : Inv k uv c base lo q (j + 1) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨g1, g2⟩ := step_inv k uv c base lo q j hk0 h64 huv hc hb he1 he2 h1
    (fun m m' b hm hm' hb5 hab => (h2 m m' b hm hm' hb5 hab).2)
  refine ⟨g1, ?_⟩
  intro m m' b hm hm' hb5 hab
  obtain ⟨a1, a2⟩ := g2 m m' b hm hm' hb5 hab
  rw [show 3 + 2 * (j + 1) = 4 + 2 * j + 1 by omega,
    show 4 + 2 * (j + 1) = 4 + 2 * j + 1 + 1 by omega,
    show lo + b + 4 + 4 * (j + 1) = lo + b + 8 + 4 * j by omega,
    show lo + b + 6 + 4 * (j + 1) = lo + b + 10 + 4 * j by omega]
  exact ⟨a1, a2⟩

theorem main' (k p anchorv uv basev : Nat) (c : Nat → Nat) (q lo : Nat) (hk : 6 ≤ k)
    (huv : uv < 2 ^ k) (hb : basev < 2 ^ k) (hc : ∀ n, c n < 2 ^ k)
    (hqdef : q = anchorv + (10 * p + 30) * k)
    (hlodef : lo = (trace k uv c q p basev).1 - (2 * (5 + 2 * p) + 2))
    (hq : q ≤ lo + k) :
    (∀ mask : Fin 64, trace k uv c q p (vk k basev lo mask.val) = trace k uv c q p basev) ∧
    ∀ label : Fin 10, ∃! assignment : Fin (2 ^ (if label.val < 2 then 2 else 4)),
      branch k uv c (5 + 2 * p) (trace k uv c q p basev).1
        (vk k basev lo (pack label.val assignment.val)) = label.val := by
  have hk0 : 0 < k := by omega
  have h64 : 64 ≤ 2 ^ k := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqk : (10 * p + 30) * 6 ≤ (10 * p + 30) * k := Nat.mul_le_mul_left _ hk
  have hq19 : 19 + 6 * p ≤ q := by rw [hqdef]; omega
  have hE := edges k uv c q p basev hq19
  have hmono := edges_mono k uv c q p basev hq19
  have hxp := hE p le_rfl
  have hqbig : 180 + 60 * p ≤ q := by rw [hqdef]; omega
  have hx12 : 12 + 4 * p ≤ (trace k uv c q p basev).1 := by omega
  have hlo1 : 1 ≤ lo := by omega
  have hxlo : (trace k uv c q p basev).1 = lo + 12 + 4 * p := by omega
  have hk25 : 25 + 7 * p ≤ k := by omega
  have hInv : ∀ j, j ≤ p → Inv k uv c basev lo q j := by
    intro j
    induction j with
    | zero => intro _; exact inv_zero k uv c basev lo q (by omega) h64 huv hc hb hq (by omega)
    | succ j ih =>
      intro hj
      have hm := hmono (p - j) j (by omega)
      rw [show j + (p - j) = p by omega] at hm
      have hEj := hE j (by omega)
      exact inv_succ k uv c basev lo q j hk0 h64 huv hc hb (by omega) (by omega) (ih (by omega))
  obtain ⟨hI1, hI2⟩ := hInv p le_rfl
  refine ⟨fun mask => hI1 mask.val mask.isLt, ?_⟩
  have hfin := final_facts k uv c basev lo (3 + 2 * p) (trace k uv c q p basev).1 hk0 h64 huv hc
    hb hlo1 (by omega) (by omega) (by omega)
    (fun m m' b hm hm' hb5 hab => by
      have := (hI2 m m' b hm hm' hb5 hab).1
      rw [show lo + b + 2 * (3 + 2 * p) - 2 = lo + b + 4 + 4 * p by omega]
      exact this)
    (fun m m' b hm hm' hb5 hab => by
      have := (hI2 m m' b hm hm' hb5 hab).2
      rw [show 3 + 2 * p + 1 = 4 + 2 * p by omega,
        show lo + b + 2 * (3 + 2 * p) = lo + b + 6 + 4 * p by omega]
      exact this)
  rw [show 3 + 2 * p + 1 + 1 = 5 + 2 * p by omega] at hfin
  exact hfin

theorem main (k p : Nat) (hk : 6 ≤ k) (anchor : Fin k) (u base : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) :
    let c := fun n => (constant n).val
    let q := anchor.val + (10 * p + 30) * k
    let prev := trace k u.val c q p base.val
    let t := 5 + 2 * p
    let lo := prev.1 - (2 * t + 2)
    let vary := fun mask : Nat => base.val ^^^ rot k (lo + k - 1) mask
    q ≤ lo + k →
      (∀ mask : Fin 64, trace k u.val c q p (vary mask.val) = prev) ∧
      ∀ label : Fin 10, ∃! assignment : Fin (2 ^ (if label.val < 2 then 2 else 4)),
        branch k u.val c t prev.1 (vary (pack label.val assignment.val)) = label.val := by
  intro c q prev t lo vary hq
  exact main' k p anchor.val u.val base.val c q lo hk u.isLt base.isLt
    (fun n => (constant n).isLt) rfl rfl hq

end PEqualNP.Outside.L_meta_25541_aux

theorem PEqualNP.Outside.L_meta_25541 : ∀ (k p : Nat), 6 ≤ k → ∀ (anchor : Fin k) (u base : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let state := fun (rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ u.val)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (round key pos : Nat) => (state round key).testBit (pos % k)
  let guard := fun (round key stop : Nat) =>
    xor (xor (bit round key (stop - 2)) (bit round key (stop - 1))) (bit round key stop)
  let branch := fun (t edge subject : Nat) =>
    let hit := guard (t - 1) subject edge
    let mid := edge - 3 + hit.toNat
    let next := guard t subject mid
    if hit then
      let near := bit t subject (edge - 2) ==
        xor (injected t subject (edge - 1)) (injected t subject edge)
      let far := bit t subject (edge - 3) == injected t subject edge
      2 + near.toNat + 2 * far.toNat + 4 * next.toNat
    else next.toNat
  let gain := fun (v : Nat) =>
    if v < 2 then v else 1 + (v - 2) / 4 + (if v = 9 then 1 else 0)
  let q := anchor.val + (10 * p + 30) * k
  let trace := fun (len keyWord : Nat) =>
    (List.range len).foldl (fun (acc : Nat × Nat) j =>
      let v := branch (5 + 2 * j) acc.1 keyWord
      (acc.1 - 6 + gain v, acc.2 + v * 10 ^ j)) (q - 13, 0)
  let prev := trace p base.val
  let t := 5 + 2 * p
  let lo := prev.1 - (2 * t + 2)
  let vary := fun (mask : Nat) => base.val ^^^ rot (lo + k - 1) mask
  let pack := fun (v bits : Nat) =>
    ((bits % 2) <<< 5) ||| (if v < 2 then (bits / 2) % 2 else
      (((bits / 2) % 2) <<< 3) ||| (((bits / 4) % 2) <<< 2) ||| (((bits / 8) % 2) <<< 1))
  q ≤ lo + k →
    (∀ mask : Fin 64, trace p (vary mask.val) = prev) ∧
    ∀ label : Fin 10, ∃! assignment : Fin (2 ^ (if label.val < 2 then 2 else 4)),
      branch t prev.1 (vary (pack label.val assignment.val)) = label.val :=
  fun k p hk anchor u base constant =>
    PEqualNP.Outside.L_meta_25541_aux.main k p hk anchor u base constant
