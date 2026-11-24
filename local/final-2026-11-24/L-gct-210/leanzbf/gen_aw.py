# Generator: wrappers a3w_o1, a3w_o2 (T3F2 context -> affine cores a3p_o1 / a3p_o2) + t3f2_proof + t1_proof -> r7_7.txt
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/gen_bridge.py', encoding='utf-8').read().split('text = ')[0])
T0L = '(m ∉ Q12 ∧ m ∉ B12 ∧ m ∉ Q13 ∧ m ∉ B13 ∧ m ∉ Q23 ∧ m ∉ B23)'
O4 = {1: [T0L] + O[1]['T'], 2: [T0L] + O[2]['T']}
def get_type4(n, v, k, memfact, memset):
    T = O4[n]
    names = [f'h{v}{i}' for i in range(1, 7)]
    tl = T[k].replace('m ', v + ' ').replace('(m', '(' + v)[1:-1]
    L = [f'  obtain ⟨{", ".join(names)}⟩ : {tl} := by', f'    rcases hO {v} with h | h | h | h']
    for kk in range(4):
        if kk == k: L.append('    · exact h')
        else:
            assert f'm ∈ {memset}' not in T[kk]
            L.append(f'    · exact absurd {memfact} {lit("h", memset)}')
    return L
HEADW = HEAD.replace('theorem orient{n}_noT0 {{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}} (r1 r2 r3 : Fin 5)',
    'theorem a3w_o{n} {{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)}} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)\n'
    '    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)\n'
    '    (h0 : rowsZeroS L {{r1, r2, r3}} = ⊥)')
HEADW = HEADW.replace('    (hno : ¬ ∃ m, m ∉ Q12 ∧ m ∉ B12 ∧ m ∉ Q13 ∧ m ∉ B13 ∧ m ∉ Q23 ∧ m ∉ B23) : False := by\n', '{extra}')
HEADW = HEADW.replace('obtain ⟨hQB12, w12Q, w12B, sq12, -⟩', 'obtain ⟨hQB12, w12Q, w12B, sq12, rel12⟩')
HEADW = HEADW.replace('obtain ⟨hQB13, w13Q, w13B, sq13, -⟩', 'obtain ⟨hQB13, w13Q, w13B, sq13, rel13⟩')
HEADW = HEADW.replace('obtain ⟨hQB23, w23Q, w23B, sq23, -⟩', 'obtain ⟨hQB23, w23Q, w23B, sq23, rel23⟩')
assert '{extra}' in HEADW and 'rel23⟩' in HEADW
def facts(vs): return ', '.join(f'h{v}{i}' for v in vs for i in range(1, 7))
def wrapper(n):
    if n == 1:
        extra = '    : False := by\n'
    else:
        extra = '    (hT0 : ∃ m, m ∉ Q12 ∧ m ∉ B12 ∧ m ∉ Q13 ∧ m ∉ B13 ∧ m ∉ Q23 ∧ m ∉ B23) : False := by\n'
    L = [HEADW.format(n=n, extra=extra).rstrip('\n'), COMMON.rstrip('\n')]
    if n == 1:
        L += ["  have ha'Q : a' ∈ Q13 := (hQ13 a').mpr rfl"] + get_type4(1, "a'", 1, "ha'Q", 'Q13')
        L += ["  have R1 : c' = c'' * cJ := mul_right_cancel₀ (hκ0 a')",
              "    (by linear_combination -(w13Q a' ha'Q) + w23Q a' ha'5 + c'' * corner12 a' ha'2 ha'1)"]
        L += ['  have haQ : a ∈ Q12 := (hQ12 a).mpr rfl'] + get_type4(1, 'a', 2, 'haQ', 'Q12')
        L += ["  have R2 : ω = -c'' * c := mul_right_cancel₀ (hκ0 a)",
              "    (by linear_combination -(corner13 a ha4 ha3) + w23B a ha6 + (-c'') * w12Q a haQ)"]
        L += ['  have hbB : b ∈ B12 := (hB12 b).mpr rfl'] + get_type4(1, 'b', 3, 'hbB', 'B12')
        L += ["  have R3 : -c' = ω2 * (-c) := mul_right_cancel₀ (hκ0 b)",
              "    (by linear_combination -(w13B b hb4) + corner23 b hb6 hb5 + ω2 * w12B b hbB)"]
        L += ["  have hω : ω = j * c' := by linear_combination R2 - j * R1 - c'' * j * hcJ - c'' * c * hj",
              "  have hω2 : ω2 = j * c'' := by",
              "    have e : (ω2 - j * c'') * c = 0 := by linear_combination R3 + R1 + c'' * hcJ",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hc)"]
        P, PV = "a'", "ha'"
        dist = ["  have hpq : a' ≠ a := fun h => ha3 (by rw [← h]; exact ha'Q)",
                "  have hps : a' ≠ b := fun h => ha'2 (by rw [h]; exact hbB)",
                "  have hqs : a ≠ b := fun h => hb1 (by rw [← h]; exact haQ)"]
        hw1p = "by rw [corner12 a' ha'2 ha'1, hcJ]"
        hw2 = "⟨w13Q a' ha'Q, by rw [corner13 a ha4 ha3, hω], w13B b hb4⟩"
        cols = ["a'", 'a', 'b']
        core = 'a3p_o1'
    else:
        L += ["  have hb'B : b' ∈ B13 := (hB13 b').mpr rfl"] + get_type4(2, "b'", 1, "hb'B", 'B13')
        L += ["  have R1 : -c' = -c'' * cJ := mul_right_cancel₀ (hκ0 b')",
              "    (by linear_combination -(w13B b' hb'B) + w23B b' hb'6 + (-c'') * corner12 b' hb'2 hb'1)"]
        L += ['  have haQ : a ∈ Q12 := (hQ12 a).mpr rfl'] + get_type4(2, 'a', 2, 'haQ', 'Q12')
        L += ["  have R2 : c' = ω2 * c := mul_right_cancel₀ (hκ0 a)",
              "    (by linear_combination -(w13Q a ha3) + corner23 a ha6 ha5 + ω2 * w12Q a haQ)"]
        L += ['  have hbB : b ∈ B12 := (hB12 b).mpr rfl'] + get_type4(2, 'b', 3, 'hbB', 'B12')
        L += ["  have R3 : ω = c'' * (-c) := mul_right_cancel₀ (hκ0 b)",
              "    (by linear_combination -(corner13 b hb4 hb3) + w23Q b hb5 + c'' * w12B b hbB)"]
        L += ["  have hω : ω = j * c' := by linear_combination R3 + j * R1 - c'' * j * hcJ - c'' * c * hj",
              "  have hω2 : ω2 = j * c'' := by",
              "    have e : (ω2 - j * c'') * c = 0 := by linear_combination -R2 - R1 + c'' * hcJ",
              "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hc)",
              "  obtain ⟨t0, ht01, ht02, ht03, ht04, ht05, ht06⟩ := hT0"]
        dist = ["  have hpq : t0 ≠ a := fun h => ht01 (by rw [h]; exact haQ)",
                "  have hps : t0 ≠ b := fun h => ht02 (by rw [h]; exact hbB)",
                "  have hqs : a ≠ b := fun h => hb1 (by rw [← h]; exact haQ)"]
        hw1p = "by rw [corner12 t0 ht02 ht01, hcJ]"
        hw2 = "⟨by rw [corner13 t0 ht04 ht03, hω], w13Q a ha3, by rw [corner13 b hb4 hb3, hω]⟩"
        cols = ['t0', 'a', 'b']
        core = 'a3p_o2'
    L += ["  have J12 := typeII_J κ κ2 ν ν' hκ0 hκ20 a b hcl hκ1 hκ21 hν1 m0 ⟨hm01, hm02⟩ Q12 B12 hQ12 hB12",
          "  rw [← hcJdef, ← hcdef] at J12",
          "  have K12 : ∑ m ∈ B12, κ m + ∑ m ∈ Q12, κ2 m = (1 - j) / 2 := by",
          "    apply ksum_half _ j hj",
          "    have e : c * ((∑ m ∈ B12, κ m + ∑ m ∈ Q12, κ2 m) * (1 + j) - 1) = 0 := by",
          "      linear_combination J12 - (∑ m ∈ B12, κ m + ∑ m ∈ Q12, κ2 m) * hcJ",
          "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc)",
          "  have J13 := typeII_J κ κ3 μ μ' hκ0 hκ30 a' b' hcl' hκ1 hκ31 hμ1 m1 ⟨hm11, hm12⟩ Q13 B13 hQ13 hB13",
          "  rw [← hωdef, ← hc'def] at J13",
          "  have K13 : ∑ m ∈ B13, κ m + ∑ m ∈ Q13, κ3 m = (1 - j) / 2 := by",
          "    apply ksum_half _ j hj",
          "    have e : c' * ((∑ m ∈ B13, κ m + ∑ m ∈ Q13, κ3 m) * (1 + j) - 1) = 0 := by",
          "      linear_combination J13 - (∑ m ∈ B13, κ m + ∑ m ∈ Q13, κ3 m) * hω",
          "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc')",
          "  have J23 := typeII_J κ2 κ3 ξ ξ' hκ20 hκ30 a'' b'' hcl'' hκ21 hκ31 hξ1 m2 ⟨hm21, hm22⟩ Q23 B23 hQ23 hB23",
          "  rw [← hω2def, ← hc''def] at J23",
          "  have K23 : ∑ m ∈ B23, κ2 m + ∑ m ∈ Q23, κ3 m = (1 - j) / 2 := by",
          "    apply ksum_half _ j hj",
          "    have e : c'' * ((∑ m ∈ B23, κ2 m + ∑ m ∈ Q23, κ3 m) * (1 + j) - 1) = 0 := by",
          "      linear_combination J23 - (∑ m ∈ B23, κ2 m + ∑ m ∈ Q23, κ3 m) * hω2",
          "    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc'')"]
    L += dist
    p, q, s = cols
    L += ['  obtain ⟨rr, cc, K, hr0, hr1, hr2, hc0, hc1, hc2, hK0, hK1, hK2, h0\', hKn, hFK, -, hKs, hbs⟩ :=',
          f'    s_transfer_aff r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L hκ1 hκ21 hκ31 {p} {q} {s}',
          '      hpq hps hqs',
          f"  refine {core} hL h9 rr cc h0' K hKn hFK hKs c c' j hc hc' hj ?_ ?_ ?_",
          '  · simp only [hK0, hK1, hc0, hc1, hc2]',
          f'    exact ⟨{hw1p}, w12Q a haQ, w12B b hbB⟩',
          '  · simp only [hK0, hK2, hc0, hc1, hc2]',
          f'    exact {hw2}',
          '  · intro w hw',
          '    obtain ⟨hwL, hoffw⟩ := hbs w hw',
          '    have A12 := typeII_aff κ κ2 B12 Q12 r1 r2 rel12 w hwL',
          '    have A13 := typeII_aff κ κ3 B13 Q13 r1 r3 rel13 w hwL',
          '    have A23 := typeII_aff κ2 κ3 B23 Q23 r2 r3 rel23 w hwL',
          '    rw [K12] at A12',
          '    rw [K13] at A13',
          '    rw [K23] at A23',
          f'    have L12 := typeII_ite_aff κ κ2 B12 Q12 r1 r2 (hat 5 w) {p} {q} {s} hpq hps hqs',
          '      (fun m h1 h2 h3 => ⟨(hoffw m h1 h2 h3).1, (hoffw m h1 h2 h3).2.1⟩) _ A12',
          f'    have L13 := typeII_ite_aff κ κ3 B13 Q13 r1 r3 (hat 5 w) {p} {q} {s} hpq hps hqs',
          '      (fun m h1 h2 h3 => ⟨(hoffw m h1 h2 h3).1, (hoffw m h1 h2 h3).2.2⟩) _ A13',
          f'    have L23 := typeII_ite_aff κ2 κ3 B23 Q23 r2 r3 (hat 5 w) {p} {q} {s} hpq hps hqs',
          '      (fun m h1 h2 h3 => ⟨(hoffw m h1 h2 h3).2.1, (hoffw m h1 h2 h3).2.2⟩) _ A23']
    fl = facts(["a'", 'a', 'b']) if n == 1 else ', '.join([f'ht0{i}' for i in range(1, 7)] + [f'h{v}{i}' for v in ('a', 'b') for i in range(1, 7)])
    L += [f'    simp only [{fl}, ite_true, ite_false, zero_add, add_zero] at L12 L13 L23',
          '    simp only [hK0, hK1, hK2, hr0, hr1, hr2, hc0, hc1, hc2]',
          '    exact ⟨by linear_combination L12, by linear_combination L13, by linear_combination L23⟩']
    return '\n'.join(L)
ARGS = ("hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L hκ1 hκ21 hκ31 ν ν' μ μ' ξ ξ'\n"
        "        a b a' b' a'' b'' hνL hν1 hμL hμ1 hξL hξ1 hcl hcl' hcl'' m0 hm01 hm02 m1 hm11 hm12 m2 hm21 hm22\n"
        "        B12 Q12 B13 Q13 B23 Q23 hB12 hQ12 hB13 hQ13 hB23 hQ23 hO")
FIN = '''theorem t3f2_proof : T3F2 := by
  intro L hL h9 r1 r2 r3 h12 h13 h23 h0 z1 z2 z3 x12 x13 x23 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L
    hκ3L hκ1 hκ21 hκ31 ν ν' μ μ' ξ ξ' a b a' b' a'' b'' hνL hν1 hμL hμ1 hξL hξ1 hcl hcl' hcl'' e12 e13 e23
    B12 Q12 B13 Q13 B23 Q23 hB12 hQ12 hB13 hQ13 hB23 hQ23 hO hT0
  obtain ⟨m0, hm01, hm02⟩ := e12
  obtain ⟨m1, hm11, hm12⟩ := e13
  obtain ⟨m2, hm21, hm22⟩ := e23
  rcases hO with hO | hO
  · exact a3w_o1 ''' + ARGS + '''
  · exact a3w_o2 ''' + ARGS + ''' hT0

theorem t1_proof : T1Hyp := t1_of_t3f2 t3f2_proof'''
text = '\n\n' + wrapper(1) + '\n\n' + wrapper(2) + '\n\n' + FIN + '\n'
open('/home/kevxhk/work/L-gct-210/lean/zbf/r7_7.txt', 'w', encoding='utf-8').write(text)
print('lines', text.count('\n'))
