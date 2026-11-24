# Generator: (II,II,II) top-level dispatch t3_trans -> lean/zbf/r6_9.txt.
# Statement: for all-Type-II data (shared FK annihilators) and a pair-12 transversal p (corner), q (Q2^12), s (B12 = Q3^12),
# the local pattern of (p, q, s) w.r.t. pairs 13 and 23 is one of the consistent NON-passing patterns (disjunction).
# Inconsistent leaves: unit_split for the corner ratios, then a ratio certificate; passing leaves: s_transfer + t3p_* lemma.
import itertools, ast, random
GEN = {}
for line in open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t3p.log'):
    if line.startswith('(('):
        lab, x, sg, name = ast.literal_eval(line.strip()); GEN[(lab, x, sg)] = name
PASS = {(l, x) for (l, x, s) in GEN}
COL = ['p', 'q', 's']
LAB = {'Q': 2, 'B': 3, 'C': 1}
I = 1j
def consistent_any(st13, st23, pts):
    for s1 in (1, -1):
        for s2 in (1, -1):
            if consistent(st13, st23, pts, s1, s2): return True
    return False
def zval(st, sg):  # value in Z4 exponent of j (sign -1 = j^2) for a status with corner sign sg: Q -> 1, B -> -1, C -> sg*j
    return {'Q': 0, 'B': 2, 'C': (1 if sg == 1 else 3)}[st]
WZ = {'p': 1, 'q': 0, 's': 2}
def kval(m, st13, st23, s1, s2):
    return (zval(st13[m], s1) - zval(st23[m], s2) - WZ[m]) % 4
def consistent(st13, st23, pts, s1, s2):
    ks = {kval(m, st13, st23, s1, s2) for m in pts}
    return len(ks) == 1
# non-passing consistent patterns (full p, q, s)
NP = []
for t13 in itertools.product('QBC', repeat=3):
    for t23 in itertools.product('QBC', repeat=3):
        st13 = dict(zip(COL, t13)); st23 = dict(zip(COL, t23))
        if not consistent_any(st13, st23, COL): continue
        l13 = tuple(LAB[a] for a in t13); l23 = tuple(LAB[a] for a in t23)
        if (l13, l23) in PASS: continue
        NP.append((t13, t23))
def atom(m, pair, st):
    S = {'13': ('Q13', 'B13'), '23': ('Q23', 'B23')}[pair]
    if st == 'Q': return f'{m} ∈ {S[0]}'
    if st == 'B': return f'{m} ∈ {S[1]}'
    return f'({m} ∉ {S[0]} ∧ {m} ∉ {S[1]})'
def aproof(m, pair, st):
    suf = '3' if pair == '13' else '23'
    if st == 'Q': return f'h{m}Q{suf}'
    if st == 'B': return f'h{m}B{suf}'
    return f'⟨h{m}Q{suf}, h{m}B{suf}⟩'
def disj_text():
    parts = []
    for (t13, t23) in NP:
        at = []
        for k, m in enumerate(COL):
            at.append(atom(m, '13', t13[k])); at.append(atom(m, '23', t23[k]))
        parts.append('(' + ' ∧ '.join(at) + ')')
    return parts
def disj_proof(t13, t23):
    i = NP.index((t13, t23)); n = len(NP)
    pr = []
    for k, m in enumerate(COL):
        pr.append(aproof(m, '13', t13[k])); pr.append(aproof(m, '23', t23[k]))
    core = '⟨' + ', '.join(pr) + '⟩'
    if i < n - 1: core = f'Or.inl {core}'
    for _ in range(i): core = f'Or.inr ({core})'
    return core
# ---------- texts ----------
X13T = {'Q': "c'", 'B': "-c'", 'C': 'ω'}
X23T = {'Q': "c''", 'B': "-c''", 'C': 'ω2'}
WT = {'p': '(j * c)', 'q': 'c', 's': '(-c)'}
HW1 = {'p': 'hw1.1', 'q': 'hw1.2.1', 's': 'hw1.2.2'}
def vlines(m, a13, a23):
    L = []
    if a13 == 'Q': L.append(f"have V{m}3 : κ3 {m} = c' * κ {m} := w13Q {m} h{m}Q3")
    elif a13 == 'B': L.append(f"have V{m}3 : κ3 {m} = -c' * κ {m} := w13B {m} h{m}B3")
    else: L.append(f'have V{m}3 : κ3 {m} = ω * κ {m} := hκ3corner {m} h{m}B3 h{m}Q3')
    if a23 == 'Q': L.append(f"have V{m}23 : κ3 {m} = c'' * κ2 {m} := w23Q {m} h{m}Q23")
    elif a23 == 'B': L.append(f"have V{m}23 : κ3 {m} = -c'' * κ2 {m} := w23B {m} h{m}B23")
    else: L.append(f'have V{m}23 : κ3 {m} = ω2 * κ2 {m} := hκ3corner2 {m} h{m}B23 h{m}Q23')
    x13, x23 = X13T[a13], X23T[a23]
    L.append(f'have F{m} : {x13} = {x23} * {WT[m]} := mul_right_cancel₀ (hκ0 {m})')
    L.append(f'  (by linear_combination -V{m}3 + V{m}23 + ({x23}) * {HW1[m]})')
    return L
# value model for certificate checks: side values as functions
def side_vals(m, a13, a23, s1, s2):
    # returns (alpha, e) for A = alpha j^e c' and (beta, f, wb, wf) for B = beta j^f c'' * (wb j^wf c)
    A = {'Q': (1, 0), 'B': (-1, 0), 'C': (s1, 1)}[a13]
    B = {'Q': (1, 0), 'B': (-1, 0), 'C': (s2, 1)}[a23]
    W = {'p': (1, 1), 'q': (1, 0), 's': (-1, 0)}[m]
    return A, B, W
def xtext_after(st, pair, sg):
    if pair == '13':
        return {'Q': "c'", 'B': "-c'", 'C': ("j * c'" if sg == 1 else "-j * c'")}[st]
    return {'Q': "c''", 'B': "-c''", 'C': ("j * c''" if sg == 1 else "-j * c''")}[st]
def polyred(coefs):  # dict power -> int, reduce mod j^2 + 1 -> (P, Q)
    P = Q = 0
    for d, v in coefs.items():
        r = d % 4
        if r == 0: P += v
        elif r == 1: Q += v
        elif r == 2: P -= v
        else: Q -= v
    return P, Q
def pmul(a, b):
    out = {}
    for i, x in a.items():
        for k, y in b.items(): out[i + k] = out.get(i + k, 0) + x * y
    return {k: v for k, v in out.items() if v != 0}
def pdiv_j2p1(num):  # exact division by j^2 + 1, returns quotient dict
    num = dict(num); q = {}
    while num:
        d = max(num)
        v = num[d]
        if d < 2: raise ValueError('not divisible')
        q[d - 2] = q.get(d - 2, 0) + v
        num[d] -= v; num[d - 2] = num.get(d - 2, 0) - v
        num = {k: x for k, x in num.items() if x != 0}
    return q
def ptext(pl):
    if not pl: return '0'
    terms = []
    for d in sorted(pl):
        v = pl[d]
        mon = '1' if d == 0 else ('j' if d == 1 else f'j ^ {d}')
        terms.append(f'({v}) * {mon}')
    return ' + '.join(terms)
def cert(m, mp, st13, st23, s1, s2):
    A, B, W = side_vals(m, st13[m], st23[m], s1, s2)
    Ap, Bp, Wp = side_vals(mp, st13[mp], st23[mp], s1, s2)
    # A_m * B_m' - A_m' * B_m divided by c' c'' c
    t1 = A[0] * Bp[0] * Wp[0]; d1 = A[1] + Bp[1] + Wp[1]
    t2 = Ap[0] * B[0] * W[0]; d2 = Ap[1] + B[1] + W[1]
    R = {}
    R[d1] = R.get(d1, 0) + t1; R[d2] = R.get(d2, 0) - t2
    R = {k: v for k, v in R.items() if v != 0}
    P, Q = polyred(R)
    assert (P, Q) != (0, 0)
    N = P * P + Q * Q
    lhs = pmul({0: P, 1: -Q}, R)
    lhs[0] = lhs.get(0, 0) - N
    lhs = {k: v for k, v in lhs.items() if v != 0}
    S = pdiv_j2p1(lhs) if lhs else {}
    Bm = f'({xtext_after(st23[m], "23", s2)}) * {WT[m]}'
    Bmp = f'({xtext_after(st23[mp], "23", s2)}) * {WT[mp]}'
    co = f'(({P}) - ({Q}) * j)'
    line = (f"have e : ({N} : ℂ) * (c' * c'' * c) = 0 := by\n"
            f"  linear_combination ({co} * ({Bmp})) * F{m} - ({co} * ({Bm})) * F{mp} - (c' * c'' * c * ({ptext(S)})) * hj")
    # numeric self-check of the identity (j generic)
    for _ in range(3):
        jv, cv, c1, c2 = (complex(random.uniform(-2, 2), random.uniform(-2, 2)) for _ in range(4))
        def val(side, mm, sg13, sg23):
            a, b, w = side_vals(mm, st13[mm], st23[mm], sg13, sg23)
            Av = a[0] * jv ** a[1] * c1
            Bv = b[0] * jv ** b[1] * c2 * (w[0] * jv ** w[1] * cv)
            return Av, Bv
        Am_, Bm_ = val(0, m, s1, s2); Ap_, Bp_ = val(0, mp, s1, s2)
        cov = P - Q * jv
        Sv = sum(v * jv ** d for d, v in S.items())
        goal = N * c1 * c2 * cv
        comb = cov * Bp_ * (Am_ - Bm_) - cov * Bm_ * (Ap_ - Bp_) - c1 * c2 * cv * Sv * (jv * jv + 1)
        assert abs(goal - comb) < 1e-8 * (1 + abs(goal)), (m, mp, st13, st23, s1, s2)
    return line.split('\n') + ["simp [hc, hc', hc''] at e"]
def leaf(st13, st23, pts):
    u13 = any(st13[m] == 'C' for m in pts)
    u23 = any(st23[m] == 'C' for m in pts)
    def branch(s1, s2):
        L = []
        r13 = [f'F{m}' for m in pts if st13[m] == 'C']
        r23 = [f'F{m}' for m in pts if st23[m] == 'C']
        if r13: L.append(f'rw [hu1] at {" ".join(r13)}')
        if r23: L.append(f'rw [hu2] at {" ".join(r23)}')
        if not consistent(st13, st23, pts, s1, s2):
            ks = {m: kval(m, st13, st23, s1, s2) for m in pts}
            pr = None
            for m, mp in itertools.combinations(pts, 2):
                if ks[m] != ks[mp]: pr = (m, mp); break
            L += cert(pr[0], pr[1], st13, st23, s1, s2)
            return L
        assert len(pts) == 3
        t13 = tuple(st13[m] for m in COL); t23 = tuple(st23[m] for m in COL)
        l13 = tuple(LAB[a] for a in t13); l23 = tuple(LAB[a] for a in t23)
        sg = s1 if u13 else 1
        key = (l13, l23, sg)
        if key not in GEN and not u13: key = (l13, l23, -1)
        if key in GEN:
            name = GEN[key]
            hw2 = []
            for m in COL:
                hw2.append(f'(by rw [V{m}3, hu1])' if st13[m] == 'C' else f'V{m}3')
            hs = ' '.join(f'h{m}{x}' for m in COL for x in ('B3', 'Q3', 'B23', 'Q23'))
            hs = ', '.join(f'h{m}{x}' for m in COL for x in ('B3', 'Q3', 'B23', 'Q23'))
            L += ['exfalso',
                  'obtain ⟨rr, cc, K, hr0, hr1, hr2, hc0, hc1, hc2, hK0, hK1, hK2, h0\', hKn, hFK, hblk⟩ :=',
                  '  s_transfer r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L p q s hpq hps hqs',
                  f"refine {name} hL h9 rr cc h0' K hKn hFK c c' j hc hc' hj ?_ ?_ ?_",
                  '· simp only [hK0, hK1, hc0, hc1, hc2]',
                  '  exact hw1',
                  '· simp only [hK0, hK2, hc0, hc1, hc2]',
                  f'  exact ⟨{hw2[0]}, {hw2[1]}, {hw2[2]}⟩',
                  '· intro t ht',
                  '  obtain ⟨htL, ho⟩ := hblk t ht',
                  '  obtain ⟨R12, R13, R23⟩ := hloc t htL ho',
                  f'  simp only [{hs}, ite_true, ite_false, zero_add, add_zero] at R13 R23',
                  '  simp only [hK0, hK1, hK2, hr0, hr1, hr2, hc0, hc1, hc2]',
                  '  exact ⟨by linear_combination R12, by linear_combination R13, by linear_combination R23⟩']
            return L
        assert (t13, t23) in NP, (t13, t23)
        L.append(f'exact {disj_proof(t13, t23)}')
        return L
    s1s = (1, -1) if u13 else (1,)
    s2s = (1, -1) if u23 else (1,)
    def nest2(s1):
        if not u23: return branch(s1, 1)
        out = ['rcases unit_split hω2 hj with hu2 | hu2']
        for s2 in (1, -1):
            b = branch(s1, s2)
            out += ['· ' + b[0]] + ['  ' + l for l in b[1:]]
        return out
    if not u13: return nest2(1)
    out = ['rcases unit_split hω hj with hu1 | hu1']
    for s1 in (1, -1):
        b = nest2(s1)
        out += ['· ' + b[0]] + ['  ' + l for l in b[1:]]
    return out
STATS = {'leaves': 0}
def status_split(m, pair, cont):
    # returns lines: case split on the status of m in pair, cont(st) gives the sub-lines
    suf = '3' if pair == '13' else '23'
    QS, BS = ('Q13', 'B13') if pair == '13' else ('Q23', 'B23')
    hQB = 'hQB13' if pair == '13' else 'hQB23'
    out = [f'by_cases h{m}Q{suf} : {m} ∈ {QS}']
    sq = cont('Q')
    out += [f'· have h{m}B{suf} : {m} ∉ {BS} := {hQB} {m} h{m}Q{suf}'] + ['  ' + l for l in sq]
    out += [f'· by_cases h{m}B{suf} : {m} ∈ {BS}']
    sb = cont('B'); sc = cont('C')
    out += ['  · ' + sb[0]] + ['    ' + l for l in sb[1:]]
    out += ['  · ' + sc[0]] + ['    ' + l for l in sc[1:]]
    return out
ORDER = ['q', 's', 'p']
def tree(k, st13, st23):
    if k == 3:
        STATS['leaves'] += 1
        return leaf(st13, st23, COL)
    m = ORDER[k]
    def c13(a13):
        def c23(a23):
            n13 = dict(st13); n13[m] = a13
            n23 = dict(st23); n23[m] = a23
            L = vlines(m, a13, a23)
            known = ORDER[:k + 1]
            if k == 1 and not consistent_any(n13, n23, known):
                STATS['leaves'] += 1
                return L + leaf(n13, n23, known)
            return L + tree(k + 1, n13, n23)
        return status_split(m, '23', c23)
    return status_split(m, '13', c13)
HEAD = '''set_option maxHeartbeats 50000000 in
theorem t3_trans {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L)
    (h9 : Module.finrank ℂ L = 9) (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3)
    (h23 : r2 ≠ r3) (h0 : rowsZeroS L {r1, r2, r3} = ⊥) (κ κ2 κ3 : Fin 5 → ℂ)
    (hκ0 : ∀ m, κ m ≠ 0) (hκ20 : ∀ m, κ2 m ≠ 0) (hκ30 : ∀ m, κ3 m ≠ 0)
    (hκL : ∀ t ∈ L, dotL κ (rowMap r1 t) = 0) (hκ2L : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)
    (hκ3L : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (ν ν' μ μ' ξ ξ' : Fin 5 → ℂ)
    (a b a' b' a'' b'' : Fin 5)
    (hνL : ∀ t ∈ L, dotL ν (rowMap r1 t) + dotL ν' (rowMap r2 t) = 0)
    (hμL : ∀ t ∈ L, dotL μ (rowMap r1 t) + dotL μ' (rowMap r3 t) = 0)
    (hξL : ∀ t ∈ L, dotL ξ (rowMap r2 t) + dotL ξ' (rowMap r3 t) = 0)
    (hcl : TypeCl κ κ2 ν ν' a b) (hcl' : TypeCl κ κ3 μ μ' a' b')
    (hcl'' : TypeCl κ2 κ3 ξ ξ' a'' b'')
    (m1 : Fin 5) (hm11 : μ m1 / κ m1 = μ a' / κ a') (hm12 : μ' m1 / κ3 m1 = μ' b' / κ3 b')
    (m2 : Fin 5) (hm21 : ξ m2 / κ2 m2 = ξ a'' / κ2 a'') (hm22 : ξ' m2 / κ3 m2 = ξ' b'' / κ3 b'')
    (B12 Q12 B13 Q13 B23 Q23 : Finset (Fin 5))
    (hB12 : ∀ m, m ∈ B12 ↔ ν m / κ m = ν b / κ b)
    (hQ12 : ∀ m, m ∈ Q12 ↔ ν' m / κ2 m = ν' a / κ2 a)
    (hB13 : ∀ m, m ∈ B13 ↔ μ m / κ m = μ b' / κ b')
    (hQ13 : ∀ m, m ∈ Q13 ↔ μ' m / κ3 m = μ' a' / κ3 a')
    (hB23 : ∀ m, m ∈ B23 ↔ ξ m / κ2 m = ξ b'' / κ2 b'')
    (hQ23 : ∀ m, m ∈ Q23 ↔ ξ' m / κ3 m = ξ' a'' / κ3 a'')
    (p q s : Fin 5) (hpB : p ∉ B12) (hpQ : p ∉ Q12) (hqQ : q ∈ Q12) (hsB : s ∈ B12) :
'''
PRE = '''  obtain ⟨hQB12, w12Q, w12B, sq12, rel12⟩ :=
    typeII_nf r1 r2 κ κ2 ν ν' a b hκL hκ2L hνL hκ0 hκ20 hcl B12 Q12 hB12 hQ12
  obtain ⟨hQB13, w13Q, w13B, sq13, rel13⟩ :=
    typeII_nf r1 r3 κ κ3 μ μ' a' b' hκL hκ3L hμL hκ0 hκ30 hcl' B13 Q13 hB13 hQ13
  obtain ⟨hQB23, w23Q, w23B, sq23, rel23⟩ :=
    typeII_nf r2 r3 κ2 κ3 ξ ξ' a'' b'' hκ2L hκ3L hξL hκ20 hκ30 hcl'' B23 Q23 hB23 hQ23
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = κ2 a / κ a := ⟨_, rfl⟩
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
  have hm1B : m1 ∉ B13 := fun h => hcl'.1 (hm11.symm.trans ((hB13 m1).mp h))
  have hm1Q : m1 ∉ Q13 := fun h => hcl'.2.1 (((hQ13 m1).mp h).symm.trans hm12)
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℂ, ω = κ3 m1 / κ m1 := ⟨_, rfl⟩
  have hω : ω ^ 2 = -c' ^ 2 := by
    rw [hωdef]
    exact sq13 m1 hm1B hm1Q
  have hκ3corner : ∀ m, m ∉ B13 → m ∉ Q13 → κ3 m = ω * κ m := fun m h1 h2 => by
    have e := corner_unique κ κ3 μ μ' a' b' hcl' m m1
      (corner_of_not κ κ3 μ μ' a' b' hcl' m (fun h => h1 ((hB13 m).mpr h))
        (fun h => h2 ((hQ13 m).mpr h))) ⟨hm11, hm12⟩
    rw [hωdef, ← e, div_mul_cancel₀ _ (hκ0 m)]
  have hm2B : m2 ∉ B23 := fun h => hcl''.1 (hm21.symm.trans ((hB23 m2).mp h))
  have hm2Q : m2 ∉ Q23 := fun h => hcl''.2.1 (((hQ23 m2).mp h).symm.trans hm22)
  obtain ⟨ω2, hω2def⟩ : ∃ ω2 : ℂ, ω2 = κ3 m2 / κ2 m2 := ⟨_, rfl⟩
  have hω2 : ω2 ^ 2 = -c'' ^ 2 := by
    rw [hω2def]
    exact sq23 m2 hm2B hm2Q
  have hκ3corner2 : ∀ m, m ∉ B23 → m ∉ Q23 → κ3 m = ω2 * κ2 m := fun m h1 h2 => by
    have e := corner_unique κ2 κ3 ξ ξ' a'' b'' hcl'' m m2
      (corner_of_not κ2 κ3 ξ ξ' a'' b'' hcl'' m (fun h => h1 ((hB23 m).mpr h))
        (fun h => h2 ((hQ23 m).mpr h))) ⟨hm21, hm22⟩
    rw [hω2def, ← e, div_mul_cancel₀ _ (hκ20 m)]
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
        (if s ∈ Q13 then t (r3, s) * κ3 s else 0)) = 0 ∧
      (if p ∈ B23 then t (r2, p) * κ2 p else 0) + (if q ∈ B23 then t (r2, q) * κ2 q else 0) +
        (if s ∈ B23 then t (r2, s) * κ2 s else 0) +
      ((if p ∈ Q23 then t (r3, p) * κ3 p else 0) + (if q ∈ Q23 then t (r3, q) * κ3 q else 0) +
        (if s ∈ Q23 then t (r3, s) * κ3 s else 0)) = 0 := by
    intro t ht ho
    have A := typeII_ite κ κ2 B12 Q12 r1 r2 t p q s hpq hps hqs
      (fun m h1 h2 h3 => ⟨(ho m h1 h2 h3).1, (ho m h1 h2 h3).2.1⟩) (rel12 t ht)
    have B := typeII_ite κ κ3 B13 Q13 r1 r3 t p q s hpq hps hqs
      (fun m h1 h2 h3 => ⟨(ho m h1 h2 h3).1, (ho m h1 h2 h3).2.2⟩) (rel13 t ht)
    have C := typeII_ite κ2 κ3 B23 Q23 r2 r3 t p q s hpq hps hqs
      (fun m h1 h2 h3 => ⟨(ho m h1 h2 h3).2.1, (ho m h1 h2 h3).2.2⟩) (rel23 t ht)
    simp only [hpB, hqB, hsB, hpQ, hqQ, hsQ, ite_true, ite_false, zero_add, add_zero] at A
    exact ⟨by linear_combination A, B, C⟩
'''
def ind(lines, n):
    return [' ' * n + l for l in lines]
body = tree(0, {}, {})
parts = disj_text()
concl = '    ' + ' ∨\n    '.join(parts) + ' := by'
text = HEAD + concl + '\n' + PRE + '\n'.join(ind(body, 2)) + '\n'
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_9.txt', 'w', encoding='utf-8').write('\n' + text)
print('NP patterns', len(NP), 'leaves', STATS['leaves'], 'lines', text.count('\n'), 'bytes', len(text.encode()))
# ---------- T3Rest and the reduction T3Rest -> T1Rest3 ----------
R = []
R.append('''def T3Rest : Prop :=
  ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), Lev 5 L → Module.finrank ℂ L = 9 →
  ∀ r1 r2 r3 : Fin 5, r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → rowsZeroS L {r1, r2, r3} = ⊥ →
  ZF L r1 → ZF L r2 → ZF L r3 →
  Module.finrank ℂ (rowsZeroS L {r1, r2}) = 2 →
  Module.finrank ℂ (rowsZeroS L {r1, r3}) = 2 →
  Module.finrank ℂ (rowsZeroS L {r2, r3}) = 2 →
  ∀ κ κ2 κ3 : Fin 5 → ℂ, (∀ m, κ m ≠ 0) → (∀ m, κ2 m ≠ 0) → (∀ m, κ3 m ≠ 0) →
  (∀ t ∈ L, dotL κ (rowMap r1 t) = 0) → (∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0) →
  (∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) → dotL κ 1 = 1 → dotL κ2 1 = 1 → dotL κ3 1 = 1 →
  ∀ ν ν' μ μ' ξ ξ' : Fin 5 → ℂ, ∀ a b a' b' a'' b'' : Fin 5,
  (∀ t ∈ L, dotL ν (rowMap r1 t) + dotL ν' (rowMap r2 t) = 0) → dotL ν 1 + dotL ν' 1 = 0 →
  (∀ t ∈ L, dotL μ (rowMap r1 t) + dotL μ' (rowMap r3 t) = 0) → dotL μ 1 + dotL μ' 1 = 0 →
  (∀ t ∈ L, dotL ξ (rowMap r2 t) + dotL ξ' (rowMap r3 t) = 0) → dotL ξ 1 + dotL ξ' 1 = 0 →
  TypeCl κ κ2 ν ν' a b → TypeCl κ κ3 μ μ' a' b' → TypeCl κ2 κ3 ξ ξ' a'' b'' →
  (∃ m, ν m / κ m = ν a / κ a ∧ ν' m / κ2 m = ν' b / κ2 b) →
  (∃ m, μ m / κ m = μ a' / κ a' ∧ μ' m / κ3 m = μ' b' / κ3 b') →
  (∃ m, ξ m / κ2 m = ξ a'' / κ2 a'' ∧ ξ' m / κ3 m = ξ' b'' / κ3 b'') →
  ∀ B12 Q12 B13 Q13 B23 Q23 : Finset (Fin 5),
  (∀ m, m ∈ B12 ↔ ν m / κ m = ν b / κ b) → (∀ m, m ∈ Q12 ↔ ν' m / κ2 m = ν' a / κ2 a) →
  (∀ m, m ∈ B13 ↔ μ m / κ m = μ b' / κ b') → (∀ m, m ∈ Q13 ↔ μ' m / κ3 m = μ' a' / κ3 a') →
  (∀ m, m ∈ B23 ↔ ξ m / κ2 m = ξ b'' / κ2 b'') → (∀ m, m ∈ Q23 ↔ ξ' m / κ3 m = ξ' a'' / κ3 a'') →
  (∀ p q s : Fin 5, p ∉ B12 → p ∉ Q12 → q ∈ Q12 → s ∈ B12 →
''' + '    ' + ' ∨\n    '.join(parts) + ') → False')
R.append('''theorem t1rest3_of_t3rest (h : T3Rest) : T1Rest3 := by
  intro L hL h9 r1 r2 r3 h12 h13 h23 z1 z2 z3 x12 x13 x23 hII h0
  obtain ⟨hp, hq, hr⟩ := hII
  obtain ⟨κ, κ2, ν, ν', a, b, hκL, hκ1, hκ2L, hκ21, hνL, hν1, hκ0, hκ20, hcl, m0, hm01, hm02⟩ := hp
  obtain ⟨κ', κ3, μ, μ', a', b', hκ'L, hκ'1, hκ3L, hκ31, hμL, hμ1, hκ'0, hκ30, hcl', m1, hm11,
    hm12⟩ := hq
  obtain ⟨κ2', κ3', ξ, ξ', a'', b'', hκ2'L, hκ2'1, hκ3'L, hκ3'1, hξL, hξ1, hκ2'0, hκ3'0, hcl'',
    m2, hm21, hm22⟩ := hr
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
  obtain ⟨B23, hB23⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ξ m / κ2 m = ξ b'' / κ2 b'' :=
    ⟨Finset.univ.filter (fun m => ξ m / κ2 m = ξ b'' / κ2 b''), fun m => by simp⟩
  obtain ⟨Q23, hQ23⟩ : ∃ C : Finset (Fin 5), ∀ m, m ∈ C ↔ ξ' m / κ3 m = ξ' a'' / κ3 a'' :=
    ⟨Finset.univ.filter (fun m => ξ' m / κ3 m = ξ' a'' / κ3 a''), fun m => by simp⟩
  exact h L hL h9 r1 r2 r3 h12 h13 h23 h0 z1 z2 z3 x12 x13 x23 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L
    hκ3L hκ1 hκ21 hκ31 ν ν' μ μ' ξ ξ' a b a' b' a'' b'' hνL hν1 hμL hμ1 hξL hξ1 hcl hcl' hcl''
    ⟨m0, hm01, hm02⟩ ⟨m1, hm11, hm12⟩ ⟨m2, hm21, hm22⟩ B12 Q12 B13 Q13 B23 Q23 hB12 hQ12 hB13
    hQ13 hB23 hQ23 (fun p q s hpB hpQ hqQ hsB => t3_trans hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3
      hκ0 hκ20 hκ30 hκL hκ2L hκ3L ν ν' μ μ' ξ ξ' a b a' b' a'' b'' hνL hμL hξL hcl hcl' hcl''
      m1 hm11 hm12 m2 hm21 hm22 B12 Q12 B13 Q13 B23 Q23 hB12 hQ12 hB13 hQ13 hB23 hQ23 p q s hpB hpQ
      hqQ hsB)

theorem t1_of_t3rest (h : T3Rest) : T1Hyp := t1_of_rest3 (t1rest3_of_t3rest h)''')
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_9.txt', 'a', encoding='utf-8').write('\n' + '\n\n'.join(R) + '\n')
print('appended T3Rest, t1rest3_of_t3rest, t1_of_t3rest')
# ---------- T3Rest2: also the row order (r1, r3, r2); its configurations are exactly F1 + F2 (t1_iii8.py) ----------
def subst_sets(s):
    for a, b in (('Q13', '@1'), ('B13', '@2'), ('Q23', '@3'), ('B23', '@4')):
        s = s.replace(a, b)
    for a, b in (('@1', 'Q12'), ('@2', 'B12'), ('@3', 'B23'), ('@4', 'Q23')):
        s = s.replace(a, b)
    return s
parts2 = [subst_sets(x) for x in parts]
R2 = []
t3r = R[0]
i0 = t3r.index('  (∀ p q s : Fin 5, p ∉ B12')
head = t3r[:i0].replace('def T3Rest : Prop :=', 'def T3Rest2 : Prop :=')
hall1 = ('  (∀ p q s : Fin 5, p ∉ B12 → p ∉ Q12 → q ∈ Q12 → s ∈ B12 →\n    ' + ' ∨\n    '.join(parts) + ') →\n')
hall2 = ('  (∀ p q s : Fin 5, p ∉ B13 → p ∉ Q13 → q ∈ Q13 → s ∈ B13 →\n    ' + ' ∨\n    '.join(parts2) + ') → False')
R2.append(head + hall1 + hall2)
R2.append('''theorem t3rest_of_t3rest2 (h : T3Rest2) : T3Rest := by
  intro L hL h9 r1 r2 r3 h12 h13 h23 h0 z1 z2 z3 x12 x13 x23 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L
    hκ1 hκ21 hκ31 ν ν' μ μ' ξ ξ' a b a' b' a'' b'' hνL hν1 hμL hμ1 hξL hξ1 hcl hcl' hcl'' e12 e13 e23
    B12 Q12 B13 Q13 B23 Q23 hB12 hQ12 hB13 hQ13 hB23 hQ23 hall
  obtain ⟨m0, hm01, hm02⟩ := e12
  obtain ⟨m2, hm21, hm22⟩ := e23
  have h0' : rowsZeroS L {r1, r3, r2} = ⊥ := by
    rw [set3_swap]
    exact h0
  have hξL' : ∀ t ∈ L, dotL ξ' (rowMap r3 t) + dotL ξ (rowMap r2 t) = 0 := fun t ht => by
    linear_combination hξL t ht
  exact h L hL h9 r1 r2 r3 h12 h13 h23 h0 z1 z2 z3 x12 x13 x23 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L
    hκ3L hκ1 hκ21 hκ31 ν ν' μ μ' ξ ξ' a b a' b' a'' b'' hνL hν1 hμL hμ1 hξL hξ1 hcl hcl' hcl''
    ⟨m0, hm01, hm02⟩ e13 ⟨m2, hm21, hm22⟩ B12 Q12 B13 Q13 B23 Q23 hB12 hQ12 hB13 hQ13 hB23 hQ23
    hall (fun p q s hpB hpQ hqQ hsB => t3_trans hL h9 r1 r3 r2 h13 h12 (Ne.symm h23) h0' κ κ3 κ2
      hκ0 hκ30 hκ20 hκL hκ3L hκ2L μ μ' ν ν' ξ' ξ a' b' a b b'' a'' hμL hνL hξL' hcl' hcl
      (typeCl_swap κ2 κ3 ξ ξ' hκ20 hκ30 a'' b'' hcl'') m0 hm01 hm02 m2 hm22 hm21 B13 Q13 B12 Q12
      Q23 B23 hB13 hQ13 hB12 hQ12 hQ23 hB23 p q s hpB hpQ hqQ hsB)

theorem t1_of_t3rest2 (h : T3Rest2) : T1Hyp := t1_of_t3rest (t3rest_of_t3rest2 h)''')
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_9.txt', 'a', encoding='utf-8').write('\n' + '\n\n'.join(R2) + '\n')
print('appended T3Rest2, t3rest_of_t3rest2, t1_of_t3rest2')
