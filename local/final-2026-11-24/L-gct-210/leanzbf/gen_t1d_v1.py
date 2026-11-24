# Generator part 2: global wrappers t1pw_* for the core pattern lemmas t1p_*, and the dispatch theorem t1_IIi.
import itertools
pats = []
for lab in itertools.product((1, 2, 3), repeat=3):
    for x in range(3):
        for sg in (1, -1):
            I = complex(0, 1)
            w2 = [I, 1, -1]
            w3 = [sg * I if l == 1 else (1 if l == 2 else -1) for l in lab]
            rat = [w3[k] / w2[k] for k in range(3)]
            sgn = [(-1 if k == x else 1) for k in range(3)]
            th = rat[0] / sgn[0]
            if all(abs(rat[k] - th * sgn[k]) < 1e-12 for k in range(3)):
                pats.append((lab, x, sg))
patset = set(pats)
def pname(lab, x, sg): return f'{"".join(map(str, lab))}_{x}_{"p" if sg == 1 else "m"}'
COL = ['p', 'q', 's']
def W(l, sg, m):
    if l == 2: return f'c\' * κ {m}'
    if l == 3: return f'-c\' * κ {m}'
    return f'j * c\' * κ {m}' if sg == 1 else f'-j * c\' * κ {m}'
def R13g(lab):
    t = [f't (r1, {COL[k]}) * κ {COL[k]}' for k in range(3) if lab[k] == 3]
    t += [f't (r3, {COL[k]}) * κ3 {COL[k]}' for k in range(3) if lab[k] == 2]
    return ' + '.join(t)
out = []
for (lab, x, sg) in pats:
    n = pname(lab, x, sg)
    X = COL[x]
    L = []
    L.append(f'theorem t1pw_{n} {{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}} (hL : Lev 5 L)')
    L.append('    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)')
    L.append('    (h23 : r2 ≠ r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) (κ κ2 κ3 : Fin 5 → ℂ)')
    L.append('    (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)')
    L.append('    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)')
    L.append('    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (p q s : Fin 5) (hpq : p ≠ q) (hps : p ≠ s)')
    L.append('    (hqs : q ≠ s) (c c\' j : ℂ) (hc : c ≠ 0) (hc\' : c\' ≠ 0) (hj : j * j = -1)')
    L.append('    (hw1 : κ2 p = j * c * κ p ∧ κ2 q = c * κ q ∧ κ2 s = -c * κ s)')
    L.append(f'    (hw2 : κ3 p = {W(lab[0], sg, "p")} ∧ κ3 q = {W(lab[1], sg, "q")} ∧ κ3 s = {W(lab[2], sg, "s")})')
    L.append('    (hrel : ∀ t ∈ L, (∀ m, m ≠ p → m ≠ q → m ≠ s →')
    L.append('        t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0) →')
    L.append(f'      t (r1, s) * κ s + t (r2, q) * κ2 q = 0 ∧ {R13g(lab)} = 0 ∧')
    L.append(f'      t (r2, {X}) * κ2 {X} = t (r3, {X}) * κ3 {X}) : False := by')
    L.append('''  obtain ⟨rr, hr0, hr1, hr2⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23
  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 p q s hpq hps hqs
  have zrow : ∀ m, m ≠ p → m ≠ q → m ≠ s → ∃ b0, cc (Sum.inr b0) = m := by
    intro m h1 h2 h3
    obtain ⟨y, rfl⟩ := cc.surjective m
    rcases y with i | b0
    · rcases fin3_cases i with rfl | rfl | rfl
      · exact absurd hc0 h1
      · exact absurd hc1 h2
      · exact absurd hc2 h3
    · exact ⟨b0, rfl⟩
  have hoff : ∀ t ∈ blkL L rr cc, ∀ m, m ≠ p → m ≠ q → m ≠ s →
      t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0 := by
    intro t ht m h1 h2 h3
    obtain ⟨b0, rfl⟩ := zrow m h1 h2 h3
    have h := ((mem_blkL L rr cc t).mp ht).2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr0]
      exact h 0 b0
    · rw [← hr1]
      exact h 1 b0
    · rw [← hr2]
      exact h 2 b0
  obtain ⟨K, hK⟩ : ∃ K : Fin 3 → Fin 5 → ℂ, K = ![κ, κ2, κ3] := ⟨_, rfl⟩
  have hK0 : K 0 = κ := by first | (rw [hK]; rfl) | rw [hK]
  have hK1 : K 1 = κ2 := by first | (rw [hK]; rfl) | rw [hK]
  have hK2 : K 2 = κ3 := by first | (rw [hK]; rfl) | rw [hK]
  have h0' : ∀ t ∈ blkL L rr cc, (∀ i j, t (rr (Sum.inl i), cc (Sum.inl j)) = 0) → t = 0 := by
    intro t ht hz
    have htL := ((mem_blkL L rr cc t).mp ht).1
    have hmem : t ∈ rowsZeroS L {r1, r2, r3} := by
      refine ⟨htL, fun r hr m => ?_⟩
      have hri : ∃ i, rr (Sum.inl i) = r := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with h | h | h
        · exact ⟨0, hr0.trans h.symm⟩
        · exact ⟨1, hr1.trans h.symm⟩
        · exact ⟨2, hr2.trans h.symm⟩
      obtain ⟨i, rfl⟩ := hri
      obtain ⟨y, rfl⟩ := cc.surjective m
      rcases y with i' | b0
      · exact hz i i'
      · exact ((mem_blkL L rr cc t).mp ht).2 i b0
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem''')
    L.append(f'  refine t1p_{n} hL h9 rr cc h0\' K ?_ ?_ c c\' j hc hc\' hj ?_ ?_ ?_')
    L.append('''  · intro i m
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0]
      exact hκ0 m
    · rw [hK1]
      exact hκ20 m
    · rw [hK2]
      exact hκ30 m
  · intro i t ht
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [hK0, hr0]
      exact hκL t ht
    · rw [hK1, hr1]
      exact hκ2L t ht
    · rw [hK2, hr2]
      exact hκ3L t ht
  · simp only [hK0, hK1, hc0, hc1, hc2]
    exact hw1
  · simp only [hK0, hK2, hc0, hc1, hc2]
    exact hw2
  · intro t ht
    have htL := ((mem_blkL L rr cc t).mp ht).1
    obtain ⟨E1, E2, E3⟩ := hrel t htL (hoff t ht)
    simp only [hK0, hK1, hK2, hr0, hr1, hr2, hc0, hc1, hc2]
    exact ⟨by linear_combination E1, by linear_combination E2, by linear_combination E3⟩''')
    out.append('\n'.join(L))
# ---------------- dispatch ----------------
D = []
D.append('''theorem t1_IIi {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (z1 : ZF L r1) (z2 : ZF L r2) (z3 : ZF L r3)
    (hp : PairII L r1 r2) (hq : PairII L r1 r3) (hr : PairI L r2 r3)
    (h0 : rowsZeroS L {r1, r2, r3} = ⊥) : False := by
  obtain ⟨κ, κ2, ν, ν', a, b, hκL, hκ1, hκ2L, hκ21, hνL, hν1, hκ0, hκ20, hcl, m0, hm01, hm02⟩ := hp
  obtain ⟨κ', κ3, μ, μ', a', b', hκ'L, hκ'1, hκ3L, hκ31, hμL, hμ1, hκ'0, hκ30, hcl', m1, hm11,
    hm12⟩ := hq
  obtain ⟨κ2', κ3', ξ, ξ', a'', b'', hκ2'L, hκ2'1, hκ3'L, hκ3'1, hξL, hξ1, hκ2'0, hκ3'0,
    hcl'', hI''⟩ := hr
  have e1 : κ = κ' := (fk_unique hL r1 z1.1 κ κ' hκL hκ1 hκ'L hκ'1).symm
  have e2 : κ2 = κ2' := (fk_unique hL r2 z2.1 κ2 κ2' hκ2L hκ21 hκ2'L hκ2'1).symm
  have e3 : κ3 = κ3' := (fk_unique hL r3 z3.1 κ3 κ3' hκ3L hκ31 hκ3'L hκ3'1).symm
  subst κ'
  subst κ2'
  subst κ3'
  classical
  obtain ⟨B12, hB12⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ν m / κ m = ν b / κ b :=
    ⟨Finset.univ.filter (fun m => ν m / κ m = ν b / κ b), fun m => by simp⟩
  obtain ⟨Q12, hQ12⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ν' m / κ2 m = ν' a / κ2 a :=
    ⟨Finset.univ.filter (fun m => ν' m / κ2 m = ν' a / κ2 a), fun m => by simp⟩
  obtain ⟨B13, hB13⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ μ m / κ m = μ b' / κ b' :=
    ⟨Finset.univ.filter (fun m => μ m / κ m = μ b' / κ b'), fun m => by simp⟩
  obtain ⟨Q13, hQ13⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ μ' m / κ3 m = μ' a' / κ3 a' :=
    ⟨Finset.univ.filter (fun m => μ' m / κ3 m = μ' a' / κ3 a'), fun m => by simp⟩
  obtain ⟨C23, hC23⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ξ m / κ2 m = ξ b'' / κ2 b'' :=
    ⟨Finset.univ.filter (fun m => ξ m / κ2 m = ξ b'' / κ2 b''), fun m => by simp⟩
  obtain ⟨hQB12, w12Q, w12B, sq12, rel12⟩ :=
    typeII_nf r1 r2 κ κ2 ν ν' a b hκL hκ2L hνL hκ0 hκ20 hcl B12 Q12 hB12 hQ12
  obtain ⟨hQB13, w13Q, w13B, sq13, rel13⟩ :=
    typeII_nf r1 r3 κ κ3 μ μ' a' b' hκL hκ3L hμL hκ0 hκ30 hcl' B13 Q13 hB13 hQ13
  obtain ⟨⟨f23, hf23, hf23a, hf23b⟩, rel23, hC23a⟩ :=
    typeI_nf r2 r3 κ2 κ3 ξ ξ' a'' b'' hκ2L hκ3L hξL hκ20 hκ30 hcl'' hI'' C23 hC23
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = κ2 a / κ a := ⟨_, rfl⟩
  obtain ⟨c', hc'def⟩ : ∃ c' : ℂ, c' = κ3 a' / κ a' := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (hκ20 a) (hκ0 a)
  have hc' : c' ≠ 0 := by
    rw [hc'def]
    exact div_ne_zero (hκ30 a') (hκ0 a')
  rw [← hcdef] at w12Q w12B sq12
  rw [← hc'def] at w13Q w13B sq13
  have corner13 : ∀ m, m ∉ B13 → m ∉ Q13 → μ m / κ m = μ a' / κ a' ∧
      μ' m / κ3 m = μ' b' / κ3 b' := fun m h1 h2 =>
    corner_of_not κ κ3 μ μ' a' b' hcl' m (fun h => h1 ((hB13 m).mpr h))
      (fun h => h2 ((hQ13 m).mpr h))
  have hm1B : m1 ∉ B13 := fun h => hcl'.1 (hm11.symm.trans ((hB13 m1).mp h))
  have hm1Q : m1 ∉ Q13 := fun h => hcl'.2.1 (((hQ13 m1).mp h).symm.trans hm12)
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℂ, ω = κ3 m1 / κ m1 := ⟨_, rfl⟩
  have hω : ω ^ 2 = -c' ^ 2 := by
    rw [hωdef]
    exact sq13 m1 hm1B hm1Q
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω
    have e : c' ^ 2 = 0 := by linear_combination hω
    exact hc' ((pow_eq_zero_iff two_ne_zero).mp e)
  have hκ3corner : ∀ m, m ∉ B13 → m ∉ Q13 → κ3 m = ω * κ m := fun m h1 h2 => by
    have e := corner_unique κ κ3 μ μ' a' b' hcl' m m1 (corner13 m h1 h2) ⟨hm11, hm12⟩
    rw [hωdef, ← e, div_mul_cancel₀ _ (hκ0 m)]
  obtain ⟨Q1, hQ1⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ m ∉ B12 ∧ m ∉ Q12 :=
    ⟨Finset.univ.filter (fun m => m ∉ B12 ∧ m ∉ Q12), fun m => by simp⟩
  have hm0B : m0 ∉ B12 := fun h => hcl.1 (hm01.symm.trans ((hB12 m0).mp h))
  have hm0Q : m0 ∉ Q12 := fun h => hcl.2.1 (((hQ12 m0).mp h).symm.trans hm02)
  have hcov : ∀ m, m ∈ Q1 ∨ m ∈ Q12 ∨ m ∈ B12 := by
    intro m
    by_cases h1 : m ∈ Q12
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : m ∈ B12
      · exact Or.inr (Or.inr h2)
      · exact Or.inl ((hQ1 m).mpr ⟨h2, h1⟩)
  obtain ⟨p, q, s, hpQ1, hqQ, hsB, hsplit⟩ := rule_R Q1 Q12 B12 C23 hcov
    ⟨m0, (hQ1 m0).mpr ⟨hm0B, hm0Q⟩⟩ ⟨a, (hQ12 a).mpr rfl⟩ ⟨b, (hB12 b).mpr rfl⟩
    ⟨b'', (hC23 b'').mpr rfl⟩ ⟨a'', (hC23a a'').mpr rfl⟩
  have hpB : p ∉ B12 := ((hQ1 p).mp hpQ1).1
  have hpQ : p ∉ Q12 := ((hQ1 p).mp hpQ1).2
  have hqB : q ∉ B12 := hQB12 q hqQ
  have hsQ : s ∉ Q12 := fun h => hQB12 s h hsB
  have hpq : p ≠ q := fun h => hpQ (by rw [h]; exact hqQ)
  have hps : p ≠ s := fun h => hpB (by rw [h]; exact hsB)
  have hqs : q ≠ s := fun h => hqB (by rw [h]; exact hsB)
  obtain ⟨j, hjdef⟩ : ∃ j : ℂ, j = κ2 p / κ p / c := ⟨_, rfl⟩
  have hj : j * j = -1 := by
    have e := sq12 p hpB hpQ
    have e2 : κ2 p / κ p / c * (κ2 p / κ p / c) = (κ2 p / κ p) ^ 2 / c ^ 2 := by ring
    rw [hjdef, e2, e, neg_div, div_self (pow_ne_zero 2 hc)]
  have hw1 : κ2 p = j * c * κ p ∧ κ2 q = c * κ q ∧ κ2 s = -c * κ s := by
    refine ⟨?_, w12Q q hqQ, w12B s hsB⟩
    rw [hjdef, div_mul_cancel₀ _ hc, div_mul_cancel₀ _ (hκ0 p)]
  have hloc : ∀ t ∈ L, (∀ m, m ≠ p → m ≠ q → m ≠ s →
      t (r1, m) = 0 ∧ t (r2, m) = 0 ∧ t (r3, m) = 0) →
      t (r1, s) * κ s + t (r2, q) * κ2 q = 0 ∧
      (if p ∈ B13 then t (r1, p) * κ p else 0) + (if q ∈ B13 then t (r1, q) * κ q else 0) +
        (if s ∈ B13 then t (r1, s) * κ s else 0) +
      ((if p ∈ Q13 then t (r3, p) * κ3 p else 0) + (if q ∈ Q13 then t (r3, q) * κ3 q else 0) +
        (if s ∈ Q13 then t (r3, s) * κ3 s else 0)) = 0 := by
    intro t ht ho
    have A := typeII_ite κ κ2 B12 Q12 r1 r2 t p q s hpq hps hqs
      (fun m h1 h2 h3 => ⟨(ho m h1 h2 h3).1, (ho m h1 h2 h3).2.1⟩) (rel12 t ht)
    have B := typeII_ite κ κ3 B13 Q13 r1 r3 t p q s hpq hps hqs
      (fun m h1 h2 h3 => ⟨(ho m h1 h2 h3).1, (ho m h1 h2 h3).2.2⟩) (rel13 t ht)
    simp only [hpB, hqB, hsB, hpQ, hqQ, hsQ, ite_true, ite_false, zero_add, add_zero] at A
    exact ⟨by linear_combination A, B⟩
  have side := c23_side κ2 κ3 C23 f23 hf23a hf23b''')
def ind(lines, k): return [(' ' * k + l) if l else l for l in lines]
def eps_text(e): return '1' if e == 1 else '(-1)'
def U(st): return {'Q': 'c\'', 'B': '(-c\')', 'C': 'ω'}[st]
def alpha(st): return {'Q': 1, 'B': -1}[st]
def labof(st): return {'Q': 2, 'B': 3, 'C': 1}[st]
def leaf(x, sts, eps):
    # eps: dict pair -> (sign, proof-term-of-side-relation-hyp-name)
    L = []
    for k, m in enumerate(COL):
        st = sts[k]
        if st == 'Q': L.append(f'have V{m} : κ3 {m} = c\' * κ {m} := w13Q {m} h{m}Q3')
        elif st == 'B': L.append(f'have V{m} : κ3 {m} = -c\' * κ {m} := w13B {m} h{m}B3')
        else: L.append(f'have V{m} : κ3 {m} = ω * κ {m} := hκ3corner {m} h{m}B3 h{m}Q3')
    # side equations
    def sideeq(m1_, m2_, name, A, B, k2):
        e, hyp = eps[(m1_, m2_)]
        part = '.1' if e == 1 else '.2'
        out = [f'have S{name} := (side {m1_} {m2_}){part} {hyp}',
               f'rw [V{m1_}, V{m2_}, {k2[m2_]}, {k2[m1_]}] at S{name}',
               f'have E{name} := side_cancel (κ {m1_}) (κ {m2_}) ({A}) ({eps_text(e)} * ({B})) (hκ0 {m1_}) (hκ0 {m2_})',
               f'  (by linear_combination S{name})']
        return out
    k2 = {'p': 'hw1.1', 'q': 'hw1.2.1', 's': 'hw1.2.2'}
    v = {'p': '(j * c)', 'q': 'c', 's': '(-c)'}
    stp, stq, sts_ = sts
    L += sideeq('p', 'q', 'pq', f'{U(stp)} * {v["q"]}', f'{U(stq)} * {v["p"]}', k2)
    L += sideeq('p', 's', 'ps', f'{U(stp)} * {v["s"]}', f'{U(sts_)} * {v["p"]}', k2)
    L += sideeq('q', 's', 'qs', f'{U(stq)} * {v["s"]}', f'{U(sts_)} * {v["q"]}', k2)
    epq, eps_, eqs = eps[('p', 'q')][0], eps[('p', 's')][0], eps[('q', 's')][0]
    if stq != 'C' and sts_ != 'C':
        aq, as_ = alpha(stq), alpha(sts_)
        if aq + eqs * as_ != 0:
            s2 = (aq + eqs * as_) // 2
            L += [f'have e1 : (2 : ℂ) * (c * c\') = 0 := by linear_combination ({-s2}) * Eqs',
                  'simp [hc, hc\'] at e1']
            return L
        if stp != 'C':
            ap = alpha(stp)
            k = epq * ap * aq
            L += [f'have e1 : (c * c\') * (j - ({k})) = 0 := by linear_combination ({-epq * aq}) * Epq',
                  'have e2 := (mul_eq_zero.mp e1).resolve_left (mul_ne_zero hc hc\')',
                  f'have e3 : j = {k} := by linear_combination e2',
                  'rw [e3] at hj',
                  'norm_num at hj']
            return L
        sg = epq * aq
        L += [f'have e1 : c * (ω - ({sg}) * j * c\') = 0 := by linear_combination Epq',
              'have e2 := (mul_eq_zero.mp e1).resolve_left hc',
              f'have hωv : ω = ({sg}) * j * c\' := by linear_combination e2']
        lab = (1, labof(stq), labof(sts_))
    elif (stq == 'C') != (sts_ == 'C'):
        if stq == 'C':
            k = eqs * alpha(sts_)
            L += [f'have e1 : c * (ω + ({k}) * c\') = 0 := by linear_combination (-1) * Eqs']
        else:
            k = eqs * alpha(stq)
            L += [f'have e1 : c * (ω + ({k}) * c\') = 0 := by linear_combination ({-eqs}) * Eqs']
        L += ['have e2 := (mul_eq_zero.mp e1).resolve_left hc',
              f'have e3 : c\' ^ 2 = 0 := by linear_combination (1 / 2 : ℂ) * hω - (1 / 2 : ℂ) * (ω - ({k}) * c\') * e2',
              'exact hc\' ((pow_eq_zero_iff two_ne_zero).mp e3)']
        return L
    else:
        if eqs == 1:
            L += ['have e1 : (2 : ℂ) * (ω * c) = 0 := by linear_combination (-1) * Eqs',
                  'simp [hω0, hc] at e1']
            return L
        if stp == 'C':
            L += [f'have e1 : (ω * c) * (j - ({epq})) = 0 := by linear_combination ({-epq}) * Epq',
                  'have e2 := (mul_eq_zero.mp e1).resolve_left (mul_ne_zero hω0 hc)',
                  f'have e3 : j = {epq} := by linear_combination e2',
                  'rw [e3] at hj',
                  'norm_num at hj']
            return L
        ap = alpha(stp)
        sg = -epq * ap
        L += [f'have e1 : c * (({ap}) * c\' - ({epq}) * ω * j) = 0 := by linear_combination Epq',
              'have e2 := (mul_eq_zero.mp e1).resolve_left hc',
              f'have hωv : ω = ({sg}) * j * c\' := by linear_combination (({epq}) * j) * e2 + ω * hj']
        lab = (labof(stp), 1, 1)
    assert (lab, x, sg) in patset, (lab, x, sg)
    n = pname(lab, x, sg)
    # hw2 pieces
    hw2 = []
    for k, m in enumerate(COL):
        if sts[k] == 'C':
            hw2.append(f'(by rw [V{m}, hωv]; ring)')
        else:
            hw2.append(f'V{m}')
    # R23 via pair_local: singleton X, others y z
    X = COL[x]
    oth = [m for m in COL if m != X]
    y, z = oth[0], oth[1]
    neq = {('p', 'q'): 'hpq', ('p', 's'): 'hps', ('q', 's'): 'hqs'}
    def ne(u, w):
        return neq[(u, w)] if (u, w) in neq else f'(Ne.symm {neq[(w, u)]})'
    L += [f'refine t1pw_{n} hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L p q s',
          f'  hpq hps hqs c c\' j hc hc\' hj hw1 ⟨{hw2[0]}, {hw2[1]}, {hw2[2]}⟩ (fun t ht ho => ?_)',
          'obtain ⟨R12, R13⟩ := hloc t ht ho',
          f'simp only [hpB3, hqB3, hsB3, hpQ3, hqQ3, hsQ3, ite_true, ite_false, zero_add, add_zero] at R13',
          f'have R23 := pair_local κ2 κ3 C23 r2 r3 t {y} {X} {z} {ne(y, X)} {ne(y, z)} {ne(X, z)}',
          '  (fun m h1 h2 h3 => ⟨(ho m ' + ' '.join({'p': 'h', 'q': 'h', 's': 'h'}[w] + str([y, X, z].index(w) + 1) for w in COL) + ').2.1,',
          '    (ho m ' + ' '.join('h' + str([y, X, z].index(w) + 1) for w in COL) + ').2.2⟩)',
          f'  (hκ2L t ht) (hκ3L t ht) (rel23 t ht) (by tauto) (by tauto)',
          'exact ⟨R12, by linear_combination R13, R23⟩']
    return L
def status_tree(x, eps):
    L = []
    def rec(k, sts):
        if k == 3:
            return leaf(x, sts, eps)
        m = COL[k]
        out = [f'by_cases h{m}Q3 : {m} ∈ Q13']
        sub = rec(k + 1, sts + ['Q'])
        out += ['· ' + sub[0]] + ['  ' + l for l in sub[1:]]
        out += [f'· have h{m}B3 : {m} ∉ B13 := hQB13 {m} h{m}Q3', f'  by_cases h{m}B3 : {m} ∈ B13']
        # careful: the have above is wrong when not in Q; fix below
        return out
    return rec(0, [])
# rewrite status tree properly
def tree(x, eps):
    def rec(k, sts):
        if k == 3:
            return leaf(x, sts, eps)
        m = COL[k]
        out = [f'by_cases h{m}Q3 : {m} ∈ Q13']
        subQ = rec(k + 1, sts + ['Q'])
        out += ['· have h{0}B3 : {0} ∉ B13 := hQB13 {0} h{0}Q3'.format(m)] + ['  ' + l for l in subQ]
        out += [f'· by_cases h{m}B3 : {m} ∈ B13']
        subB = rec(k + 1, sts + ['B'])
        out += ['  · ' + subB[0]] + ['    ' + l for l in subB[1:]]
        subC = rec(k + 1, sts + ['C'])
        out += ['  · ' + subC[0]] + ['    ' + l for l in subC[1:]]
        return out
    return rec(0, [])
# x cases
D2 = []
D2.append('by_cases hx1 : p ∈ C23 ↔ q ∈ C23')
# case x = s: p~q same, q!~s, p!~s
eps_s = {('p', 'q'): (1, 'hx1'), ('p', 's'): (-1, '(by tauto)'), ('q', 's'): (-1, '(by tauto)')}
D2.append('· have hx2 : ¬ (q ∈ C23 ↔ s ∈ C23) := fun h => hsplit ⟨hx1, h⟩')
D2 += ['  ' + l for l in tree(2, eps_s)]
D2.append('· by_cases hx2 : q ∈ C23 ↔ s ∈ C23')
eps_p = {('p', 'q'): (-1, '(by tauto)'), ('p', 's'): (-1, '(by tauto)'), ('q', 's'): (1, 'hx2')}
t = tree(0, eps_p)
D2 += ['  · ' + t[0]] + ['    ' + l for l in t[1:]]
eps_q = {('p', 'q'): (-1, '(by tauto)'), ('p', 's'): (1, '(by tauto)'), ('q', 's'): (-1, '(by tauto)')}
t = tree(1, eps_q)
D2 += ['  · ' + t[0]] + ['    ' + l for l in t[1:]]
D.append('\n'.join(ind(D2, 2)))
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_4.txt', 'w', encoding='utf-8').write('\n\n' + '\n\n'.join(out) + '\n\n' + '\n'.join(D) + '\n')
print(len(out), 'wrappers; dispatch lines', sum(x.count('\n') + 1 for x in D))
