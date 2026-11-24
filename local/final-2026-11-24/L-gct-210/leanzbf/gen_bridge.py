# Generator: the two F1 bridges orient1_noT0, orient2_noT0 -> lean/zbf/r7_3.txt (certificates checked in cert_chk.py)
HEAD = '''set_option maxHeartbeats 8000000 in
theorem orient{n}_noT0 {{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}} (r1 r2 r3 : Fin 5)
    (κ κ2 κ3 : Fin 5 → ℂ) (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (hκ1 : dotL κ 1 = 1) (hκ21 : dotL κ2 1 = 1)
    (hκ31 : dotL κ3 1 = 1) (ν ν' μ μ' ξ ξ' : Fin 5 → ℂ) (a b a' b' a'' b'' : Fin 5)
    (hνL : ∀ t ∈ L, dotL ν (rowMap r1 t) + dotL ν' (rowMap r2 t) = 0)
    (hν1 : dotL ν 1 + dotL ν' 1 = 0)
    (hμL : ∀ t ∈ L, dotL μ (rowMap r1 t) + dotL μ' (rowMap r3 t) = 0)
    (hμ1 : dotL μ 1 + dotL μ' 1 = 0)
    (hξL : ∀ t ∈ L, dotL ξ (rowMap r2 t) + dotL ξ' (rowMap r3 t) = 0)
    (hξ1 : dotL ξ 1 + dotL ξ' 1 = 0)
    (hcl : TypeCl κ κ2 ν ν' a b) (hcl' : TypeCl κ κ3 μ μ' a' b')
    (hcl'' : TypeCl κ2 κ3 ξ ξ' a'' b'')
    (m0 : Fin 5) (hm01 : ν m0 / κ m0 = ν a / κ a) (hm02 : ν' m0 / κ2 m0 = ν' b / κ2 b)
    (m1 : Fin 5) (hm11 : μ m1 / κ m1 = μ a' / κ a') (hm12 : μ' m1 / κ3 m1 = μ' b' / κ3 b')
    (m2 : Fin 5) (hm21 : ξ m2 / κ2 m2 = ξ a'' / κ2 a'') (hm22 : ξ' m2 / κ3 m2 = ξ' b'' / κ3 b'')
    (B12 Q12 B13 Q13 B23 Q23 : Finset (Fin 5))
    (hB12 : ∀ m, m ∈ B12 ↔ ν m / κ m = ν b / κ b)
    (hQ12 : ∀ m, m ∈ Q12 ↔ ν' m / κ2 m = ν' a / κ2 a)
    (hB13 : ∀ m, m ∈ B13 ↔ μ m / κ m = μ b' / κ b')
    (hQ13 : ∀ m, m ∈ Q13 ↔ μ' m / κ3 m = μ' a' / κ3 a')
    (hB23 : ∀ m, m ∈ B23 ↔ ξ m / κ2 m = ξ b'' / κ2 b'')
    (hQ23 : ∀ m, m ∈ Q23 ↔ ξ' m / κ3 m = ξ' a'' / κ3 a'')
    (hO : Orient{n} Q12 B12 Q13 B13 Q23 B23)
    (hno : ¬ ∃ m, m ∉ Q12 ∧ m ∉ B12 ∧ m ∉ Q13 ∧ m ∉ B13 ∧ m ∉ Q23 ∧ m ∉ B23) : False := by
  obtain ⟨hQB12, w12Q, w12B, sq12, -⟩ :=
    typeII_nf r1 r2 κ κ2 ν ν' a b hκL hκ2L hνL hκ0 hκ20 hcl B12 Q12 hB12 hQ12
  obtain ⟨hQB13, w13Q, w13B, sq13, -⟩ :=
    typeII_nf r1 r3 κ κ3 μ μ' a' b' hκL hκ3L hμL hκ0 hκ30 hcl' B13 Q13 hB13 hQ13
  obtain ⟨hQB23, w23Q, w23B, sq23, -⟩ :=
    typeII_nf r2 r3 κ2 κ3 ξ ξ' a'' b'' hκ2L hκ3L hξL hκ20 hκ30 hcl'' B23 Q23 hB23 hQ23
'''
COMMON = '''  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = κ2 a / κ a := ⟨_, rfl⟩
  obtain ⟨c', hc'def⟩ : ∃ c' : ℂ, c' = κ3 a' / κ a' := ⟨_, rfl⟩
  obtain ⟨c'', hc''def⟩ : ∃ c'' : ℂ, c'' = κ3 a'' / κ2 a'' := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (hκ20 a) (hκ0 a)
  have hc' : c' ≠ 0 := by
    rw [hc'def]
    exact div_ne_zero (hκ30 a') (hκ0 a')
  have hc'' : c'' ≠ 0 := by
    rw [hc''def]
    exact div_ne_zero (hκ30 a'') (hκ20 a'')
  rw [← hcdef] at w12Q w12B sq12
  rw [← hc'def] at w13Q w13B sq13
  rw [← hc''def] at w23Q w23B sq23
  have hm0B : m0 ∉ B12 := fun h => hcl.1 (hm01.symm.trans ((hB12 m0).mp h))
  have hm0Q : m0 ∉ Q12 := fun h => hcl.2.1 (((hQ12 m0).mp h).symm.trans hm02)
  obtain ⟨cJ, hcJdef⟩ : ∃ cJ : ℂ, cJ = κ2 m0 / κ m0 := ⟨_, rfl⟩
  have corner12 : ∀ m, m ∉ B12 → m ∉ Q12 → κ2 m = cJ * κ m := fun m h1 h2 => by
    have e := corner_unique κ κ2 ν ν' a b hcl m m0
      (corner_of_not κ κ2 ν ν' a b hcl m (fun h => h1 ((hB12 m).mpr h))
        (fun h => h2 ((hQ12 m).mpr h))) ⟨hm01, hm02⟩
    rw [hcJdef, ← e, div_mul_cancel₀ _ (hκ0 m)]
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℂ, ω = κ3 m1 / κ m1 := ⟨_, rfl⟩
  have corner13 : ∀ m, m ∉ B13 → m ∉ Q13 → κ3 m = ω * κ m := fun m h1 h2 => by
    have e := corner_unique κ κ3 μ μ' a' b' hcl' m m1
      (corner_of_not κ κ3 μ μ' a' b' hcl' m (fun h => h1 ((hB13 m).mpr h))
        (fun h => h2 ((hQ13 m).mpr h))) ⟨hm11, hm12⟩
    rw [hωdef, ← e, div_mul_cancel₀ _ (hκ0 m)]
  obtain ⟨ω2, hω2def⟩ : ∃ ω2 : ℂ, ω2 = κ3 m2 / κ2 m2 := ⟨_, rfl⟩
  have corner23 : ∀ m, m ∉ B23 → m ∉ Q23 → κ3 m = ω2 * κ2 m := fun m h1 h2 => by
    have e := corner_unique κ2 κ3 ξ ξ' a'' b'' hcl'' m m2
      (corner_of_not κ2 κ3 ξ ξ' a'' b'' hcl'' m (fun h => h1 ((hB23 m).mpr h))
        (fun h => h2 ((hQ23 m).mpr h))) ⟨hm21, hm22⟩
    rw [hω2def, ← e, div_mul_cancel₀ _ (hκ20 m)]
  obtain ⟨j, hjdef⟩ : ∃ j : ℂ, j = cJ / c := ⟨_, rfl⟩
  have hcJ : cJ = j * c := by rw [hjdef, div_mul_cancel₀ _ hc]
  have hj : j * j = -1 := by
    have e := sq12 m0 hm0B hm0Q
    rw [← hcJdef] at e
    have e2 : (j * j + 1) * c ^ 2 = 0 := by linear_combination e - (cJ + j * c) * hcJ
    have e3 := (mul_eq_zero.mp e2).resolve_right (pow_ne_zero 2 hc)
    linear_combination e3
'''
# per orientation data
O = {
 1: dict(T=['(m ∉ Q12 ∧ m ∉ B12 ∧ m ∈ Q13 ∧ m ∉ B13 ∧ m ∈ Q23 ∧ m ∉ B23)',
            '(m ∈ Q12 ∧ m ∉ B12 ∧ m ∉ Q13 ∧ m ∉ B13 ∧ m ∉ Q23 ∧ m ∈ B23)',
            '(m ∉ Q12 ∧ m ∈ B12 ∧ m ∉ Q13 ∧ m ∈ B13 ∧ m ∉ Q23 ∧ m ∉ B23)'],
         P=('Q13', 'Q12', 'B12')),
 2: dict(T=['(m ∉ Q12 ∧ m ∉ B12 ∧ m ∉ Q13 ∧ m ∈ B13 ∧ m ∉ Q23 ∧ m ∈ B23)',
            '(m ∈ Q12 ∧ m ∉ B12 ∧ m ∈ Q13 ∧ m ∉ B13 ∧ m ∉ Q23 ∧ m ∉ B23)',
            '(m ∉ Q12 ∧ m ∈ B12 ∧ m ∉ Q13 ∧ m ∉ B13 ∧ m ∈ Q23 ∧ m ∉ B23)'],
         P=('B13', 'Q12', 'B12')),
}
# literal index (1-based) of each set in the 6-literal conjunction
IDX = {'Q12': 1, 'B12': 2, 'Q13': 3, 'B13': 4, 'Q23': 5, 'B23': 6}
def lit(h, s):
    i = IDX[s]
    return h + '.2' * (i - 1) + ('.1' if i < 6 else '')
def sign_of(T, s):  # whether literal for set s in type text T is positive
    return f'm ∈ {s}' in T
def type_block(n):
    T = O[n]['T']
    L = ['  have hT : ∀ m, ' + T[0] + ' ∨', '      ' + T[1] + ' ∨', '      ' + T[2] + ' := by',
         '    intro m', '    rcases hO m with h | h | h | h', '    · exact absurd ⟨m, h⟩ hno',
         '    · exact Or.inl h', '    · exact Or.inr (Or.inl h)', '    · exact Or.inr (Or.inr h)']
    return L
def type_lits(n, k, v):
    return O[n]['T'][k].replace('m ', v + ' ').replace('(m', '(' + v)
def get_type(n, v, k, memfact, memset):
    # obtain all six literals of point v known to be of type k (index), using memfact : v ∈ memset to exclude others
    T = O[n]['T']
    names = [f'h{v}{i}' for i in range(1, 7)]
    L = [f'  obtain ⟨{", ".join(names)}⟩ : {type_lits(n, k, v)[1:-1]} := by', f'    rcases hT {v} with h | h | h']
    for kk in range(3):
        if kk == k:
            L.append('    · exact h')
        else:
            assert not sign_of(T[kk], memset)
            L.append(f'    · exact absurd {memfact} {lit("h", memset)}')
    return L
def sets_eq(n, X, Y):
    T = O[n]['T']
    L = [f'  have e{X}_{Y} : {X} = {Y} := by', '    ext m', '    rcases hT m with h | h | h']
    for k in range(3):
        sx, sy = sign_of(T[k], X), sign_of(T[k], Y)
        assert sx == sy, (n, X, Y, k)
        f = 'iff_of_true' if sx else 'iff_of_false'
        L.append(f'    · exact {f} {lit("h", X)} {lit("h", Y)}')
    return L
def part_block(n):
    S1, S2, S3 = O[n]['P']
    T = O[n]['T']
    L = [f'  have hpart : ∀ m, (m ∈ {S1} ∧ m ∉ {S2} ∧ m ∉ {S3}) ∨ (m ∉ {S1} ∧ m ∈ {S2} ∧ m ∉ {S3}) ∨',
         f'      (m ∉ {S1} ∧ m ∉ {S2} ∧ m ∈ {S3}) := by', '    intro m', '    rcases hT m with h | h | h']
    pref = ['Or.inl', 'Or.inr (Or.inl', 'Or.inr (Or.inr']
    for k in range(3):
        for s, pos in zip((S1, S2, S3), [k == 0, k == 1, k == 2]):
            assert sign_of(T[k], s) == pos, (n, k, s)
        body = f'⟨{lit("h", S1)}, {lit("h", S2)}, {lit("h", S3)}⟩'
        L.append(f'    · exact {pref[k]} {body}' + ('' if k == 0 else ')'))
    return L
def scale_fact(n, name, S, f, k_text, hyp_lines):
    L = [f'  have {name} : ∑ m ∈ {S}, {f} m = {k_text} * A{O[n]["P"].index(S) + 1} := by',
         f'    rw [hA{O[n]["P"].index(S) + 1}]',
         f'    exact sum_scale {S} {f} κ ({k_text}) (fun m hm => by']
    L += ['      ' + x for x in hyp_lines]
    L[-1] = L[-1] + ')'
    return L
def by_type(n, S, results):
    # results[k] = tactic text for type k given h (literals) and hm : m ∈ S ; for types where m ∉ S use absurd
    T = O[n]['T']
    L = ['rcases hT m with h | h | h']
    for k in range(3):
        if sign_of(T[k], S):
            L.append(f'· exact {results[k]}')
        else:
            L.append(f'· exact absurd hm {lit("h", S)}')
    return L
def gen(n):
    T = O[n]['T']
    L = [HEAD.format(n=n)] + type_block(n) + [COMMON.rstrip('\n')]
    S1, S2, S3 = O[n]['P']
    if n == 1:
        L += ['  have ha\'Q : a\' ∈ Q13 := (hQ13 a\').mpr rfl'] + get_type(1, "a'", 0, "ha'Q", 'Q13')
        L += ["  have R1 : c' = c'' * cJ := mul_right_cancel₀ (hκ0 a')",
              "    (by linear_combination -(w13Q a' ha'Q) + w23Q a' ha'5 + c'' * corner12 a' ha'2 ha'1)"]
        L += ['  have haQ : a ∈ Q12 := (hQ12 a).mpr rfl'] + get_type(1, 'a', 1, 'haQ', 'Q12')
        L += ["  have R2 : ω = -c'' * c := mul_right_cancel₀ (hκ0 a)",
              "    (by linear_combination -(corner13 a ha4 ha3) + w23B a ha6 + (-c'') * w12Q a haQ)"]
        L += ['  have hbB : b ∈ B12 := (hB12 b).mpr rfl'] + get_type(1, 'b', 2, 'hbB', 'B12')
        L += ["  have R3 : -c' = ω2 * (-c) := mul_right_cancel₀ (hκ0 b)",
              "    (by linear_combination -(w13B b hb4) + corner23 b hb6 hb5 + ω2 * w12B b hbB)"]
        L += ["  have hω : ω = j * c' := by linear_combination R2 - j * R1 - c'' * j * hcJ - c'' * c * hj",
              "  have hω2 : ω2 = j * c'' := by",
              "    have e : (ω2 - j * c'') * c = 0 := by linear_combination R3 + R1 + c'' * hcJ",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hc)"]
    else:
        L += ["  have hb'B : b' ∈ B13 := (hB13 b').mpr rfl"] + get_type(2, "b'", 0, "hb'B", 'B13')
        L += ["  have R1 : -c' = -c'' * cJ := mul_right_cancel₀ (hκ0 b')",
              "    (by linear_combination -(w13B b' hb'B) + w23B b' hb'6 + (-c'') * corner12 b' hb'2 hb'1)"]
        L += ['  have haQ : a ∈ Q12 := (hQ12 a).mpr rfl'] + get_type(2, 'a', 1, 'haQ', 'Q12')
        L += ["  have R2 : c' = ω2 * c := mul_right_cancel₀ (hκ0 a)",
              "    (by linear_combination -(w13Q a ha3) + corner23 a ha6 ha5 + ω2 * w12Q a haQ)"]
        L += ['  have hbB : b ∈ B12 := (hB12 b).mpr rfl'] + get_type(2, 'b', 2, 'hbB', 'B12')
        L += ["  have R3 : ω = c'' * (-c) := mul_right_cancel₀ (hκ0 b)",
              "    (by linear_combination -(corner13 b hb4 hb3) + w23Q b hb5 + c'' * w12B b hbB)"]
        L += ["  have hω : ω = j * c' := by linear_combination R3 + j * R1 - c'' * j * hcJ - c'' * c * hj",
              "  have hω2 : ω2 = j * c'' := by",
              "    have e : (ω2 - j * c'') * c = 0 := by linear_combination -R2 - R1 + c'' * hcJ",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hc)"]
    L += part_block(n)
    L += [f'  obtain ⟨A1, hA1⟩ : ∃ A : ℂ, A = ∑ m ∈ {S1}, κ m := ⟨_, rfl⟩',
          f'  obtain ⟨A2, hA2⟩ : ∃ A : ℂ, A = ∑ m ∈ {S2}, κ m := ⟨_, rfl⟩',
          f'  obtain ⟨A3, hA3⟩ : ∃ A : ℂ, A = ∑ m ∈ {S3}, κ m := ⟨_, rfl⟩',
          '  have S0 := sum_one_eq κ hκ1',
          f'  rw [sum_three_parts {S1} {S2} {S3} κ hpart, ← hA1, ← hA2, ← hA3] at S0',
          '  have S2 := sum_one_eq κ2 hκ21',
          f'  rw [sum_three_parts {S1} {S2} {S3} κ2 hpart] at S2',
          '  have S3 := sum_one_eq κ3 hκ31',
          f'  rw [sum_three_parts {S1} {S2} {S3} κ3 hpart] at S3']
    # kappa2 parts: T1 corner12, T2 Q12 (c), T3 B12 (-c)
    def k2res(k):
        if k == 0: return f'corner12 m {lit("h", "B12")} {lit("h", "Q12")}'
        if k == 1: return 'w12Q m hm'
        return 'w12B m hm'
    P1 = scale_fact(n, 'P1', S1, 'κ2', 'cJ', by_type(n, S1, {0: k2res(0)}))
    P2 = scale_fact(n, 'P2', S2, 'κ2', 'c', by_type(n, S2, {1: 'w12Q m hm'}))
    P3 = scale_fact(n, 'P3', S3, 'κ2', '-c', by_type(n, S3, {2: 'w12B m hm'}))
    L += P1 + P2 + P3 + ['  rw [P1, P2, P3] at S2']
    if n == 1:
        P4 = scale_fact(n, 'P4', 'Q13', 'κ3', "c'", by_type(n, 'Q13', {0: 'w13Q m hm'}))
        P5 = scale_fact(n, 'P5', 'Q12', 'κ3', 'ω', by_type(n, 'Q12', {1: f'corner13 m {lit("h", "B13")} {lit("h", "Q13")}'}))
        P6 = scale_fact(n, 'P6', 'B12', 'κ3', "-c'", by_type(n, 'B12', {2: f'w13B m {lit("h", "B13")}'}))
    else:
        P4 = scale_fact(n, 'P4', 'B13', 'κ3', "-c'", by_type(n, 'B13', {0: 'w13B m hm'}))
        P5 = scale_fact(n, 'P5', 'Q12', 'κ3', "c'", by_type(n, 'Q12', {1: f'w13Q m {lit("h", "Q13")}'}))
        P6 = scale_fact(n, 'P6', 'B12', 'κ3', 'ω', by_type(n, 'B12', {2: f'corner13 m {lit("h", "B13")} {lit("h", "Q13")}'}))
    L += P4 + P5 + P6 + ['  rw [P4, P5, P6] at S3']
    L += ['  have E1 : A1 + A2 + A3 = 1 := S0',
          '  have E2 : c * (j * A1 + A2 - A3) = 1 := by linear_combination S2 - A1 * hcJ']
    if n == 1:
        L += ["  have E3 : c' * (A1 + j * A2 - A3) = 1 := by linear_combination S3 - A2 * hω"]
    else:
        L += ["  have E3 : c' * (-A1 + A2 + j * A3) = 1 := by linear_combination S3 - A3 * hω"]
    L += ['  have J12 := typeII_J κ κ2 ν ν\' hκ0 hκ20 a b hcl hκ1 hκ21 hν1 m0 ⟨hm01, hm02⟩ Q12 B12 hQ12 hB12',
          '  rw [← hcJdef, ← hcdef, P2, ← hA3] at J12',
          '  have E4 : (A3 + c * A2) * (1 + j) = 1 := by',
          '    have e : c * ((A3 + c * A2) * (1 + j) - 1) = 0 := by linear_combination J12 - (A3 + c * A2) * hcJ',
          '    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc)',
          "  have J13 := typeII_J κ κ3 μ μ' hκ0 hκ30 a' b' hcl' hκ1 hκ31 hμ1 m1 ⟨hm11, hm12⟩ Q13 B13 hQ13 hB13",
          "  have J23 := typeII_J κ2 κ3 ξ ξ' hκ20 hκ30 a'' b'' hcl'' hκ21 hκ31 hξ1 m2 ⟨hm21, hm22⟩ Q23 B23 hQ23 hB23"]
    if n == 1:
        L += sets_eq(1, 'B13', 'B12') + sets_eq(1, 'Q23', 'Q13') + sets_eq(1, 'B23', 'Q12')
        L += ["  rw [← hωdef, ← hc'def, P4, eB13_B12, ← hA3] at J13",
              "  have E5 : (A3 + c' * A1) * (1 + j) = 1 := by",
              "    have e : c' * ((A3 + c' * A1) * (1 + j) - 1) = 0 := by linear_combination J13 - (A3 + c' * A1) * hω",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc')",
              "  rw [← hω2def, ← hc''def, eB23_Q12, eQ23_Q13, P2, P4] at J23",
              "  have E6 : (c * A2 + c' * A1) * (1 + j) = 1 := by",
              "    have e : c'' * ((c * A2 + c' * A1) * (1 + j) - 1) = 0 := by",
              "      linear_combination J23 - (c * A2 + c' * A1) * hω2",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc'')",
              "  exact f1_alg j c c' A1 A2 A3 hj hc E1 E2 E3 E4 E5 E6"]
    else:
        L += sets_eq(2, 'Q13', 'Q12') + sets_eq(2, 'B23', 'B13') + sets_eq(2, 'Q23', 'B12')
        L += ["  rw [← hωdef, ← hc'def, eQ13_Q12, P5, ← hA1] at J13",
              "  have E5 : (A1 + c' * A2) * (1 + j) = 1 := by",
              "    have e : c' * ((A1 + c' * A2) * (1 + j) - 1) = 0 := by linear_combination J13 - (A1 + c' * A2) * hω",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc')",
              "  rw [← hω2def, ← hc''def, eB23_B13, eQ23_B12, P1, P6] at J23",
              "  have E6 : j * (c * A1 + c' * A3) * (1 + j) = 1 := by",
              "    have e : c'' * (j * (c * A1 + c' * A3) * (1 + j) - 1) = 0 := by",
              "      linear_combination J23 - (ω2 + c'') * A1 * hcJ - (ω2 + c'') * A3 * hω -",
              "        (j * c * A1 + j * c' * A3) * hω2",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc'')",
              "  exact f1_alg2 j c c' A1 A2 A3 hj E1 E2 E3 E4 E5 E6"]
    return '\n'.join(L)
text = '\n\n' + gen(1) + '\n\n' + gen(2) + '\n'
open('/home/kevxhk/work/L-gct-210/lean/zbf/r7_3.txt', 'w', encoding='utf-8').write(text)
print('lines', text.count('\n'))
