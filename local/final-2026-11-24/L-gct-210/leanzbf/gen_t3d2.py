# Generator: compact (II,II,II) dispatch t3_trans (same statement) -> lean/zbf/r6_9b.txt
# - status splits via status3 (one rcases per point and pair), F_m via ratio_eq (one line per point)
# - compact certificates, passing leaves call stest_glob directly with the pattern data (no t3p_* lemmas needed)
import itertools, random
from fractions import Fraction as Fr
SRC = open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t3d.py', encoding='utf-8').read()
exec(SRC.split("HEAD = '''")[0])          # NP, consistency, aproof/disj_proof, side_vals, polyred, pmul, pdiv_j2p1 ...
exec("HEAD = '''" + SRC.split("HEAD = '''")[1].split("def ind(lines, n):")[0])   # HEAD, PRE strings
SL = open('/home/kevxhk/work/L-gct-210/leanzbf/gen_slim.py', encoding='utf-8').read().split('def body(')[0]
SLNS = {}
exec(SL, SLNS)   # fmt, nullsolve, solve_rows, padd/pmul/pred/pdivq/ptext over Fractions (own namespace)
fmtF = SLNS['fmt']
def cpoly(d):  # compact polynomial in j from dict power -> number
    terms = []
    for k in sorted(d):
        v = Fr(d[k])
        if v == 0: continue
        mon = '' if k == 0 else ('j' if k == 1 else f'j ^ {k}')
        if mon == '': terms.append(fmtF(v))
        elif v == 1: terms.append(mon)
        elif v == -1: terms.append(f'(-{mon})')
        else: terms.append(f'{fmtF(v)} * {mon}')
    return '(' + ' + '.join(terms) + ')' if terms else '0'
X13T = {'Q': "c'", 'B': "-c'", 'C': 'ω'}
X23T = {'Q': "c''", 'B': "-c''", 'C': 'ω2'}
WT = {'p': '(j * c)', 'q': 'c', 's': '(-c)'}
HW1 = {'p': 'hw1.1', 'q': 'hw1.2.1', 's': 'hw1.2.2'}
def v13(m, a):
    return {'Q': f'(w13Q {m} h{m}Q3)', 'B': f'(w13B {m} h{m}B3)', 'C': f'(hκ3corner {m} h{m}B3 h{m}Q3)'}[a]
def v23(m, a):
    return {'Q': f'(w23Q {m} h{m}Q23)', 'B': f'(w23B {m} h{m}B23)', 'C': f'(hκ3corner2 {m} h{m}B23 h{m}Q23)'}[a]
def vlines2(m, a13, a23):
    return [f'have F{m} := ratio_eq (hκ0 {m}) {v13(m, a13)} {v23(m, a23)} {HW1[m]}']
def cert2(m, mp, st13, st23, s1, s2):
    A, B, W = side_vals(m, st13[m], st23[m], s1, s2)
    Ap, Bp, Wp = side_vals(mp, st13[mp], st23[mp], s1, s2)
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
    # coefficient of F_m: (P - Q j) * B_m' = (P - Q j) * (Bp0 j^Bp1) * (Wp0 j^Wp1) * c'' * c
    c1 = pmul({0: P, 1: -Q}, {Bp[1] + Wp[1]: Bp[0] * Wp[0]})
    c2 = pmul({0: P, 1: -Q}, {B[1] + W[1]: B[0] * W[0]})
    parts = [f'{cpoly(c1)} * c\'\' * c * F{m}', f'{cpoly(c2)} * c\'\' * c * F{mp}']
    line = f"linear_combination {parts[0]} - {parts[1]}"
    if S: line += f" - {cpoly(S)} * c' * c'' * c * hj"
    # numeric self-check (j generic)
    for _ in range(3):
        jv, cv, a1, a2 = (complex(random.uniform(-2, 2), random.uniform(-2, 2)) for _ in range(4))
        def val(mm):
            a, b, w = side_vals(mm, st13[mm], st23[mm], s1, s2)
            return a[0] * jv ** a[1] * a1, b[0] * jv ** b[1] * a2 * (w[0] * jv ** w[1] * cv)
        Am_, Bm_ = val(m); Ap_, Bp_ = val(mp)
        ev = lambda d: sum(complex(v) * jv ** k for k, v in d.items())
        comb = ev(c1) * a2 * cv * (Am_ - Bm_) - ev(c2) * a2 * cv * (Ap_ - Bp_) - (ev(S) if S else 0) * a1 * a2 * cv * (jv * jv + 1)
        goal = N * a1 * a2 * cv
        assert abs(goal - comb) < 1e-8 * (1 + abs(goal)), (m, mp)
    return [f"have e : ({N} : ℂ) * (c' * c'' * c) = 0 := by", '  ' + line, "simp [hc, hc', hc''] at e"]
SIMPV = 'Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons'
SIMPC = 'Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons'
def glob_leaf(lab, sg, lab23, st13):
    padd, pmulF, pred, pdivq, ptext = SLNS['padd'], SLNS['pmul'], SLNS['pred'], SLNS['pdivq'], SLNS['ptext']
    nullsolve, solve_rows = SLNS['nullsolve'], SLNS['solve_rows']
    rels = []
    for i in range(3): rels.append([Fr(1) if v // 3 == i else Fr(0) for v in range(9)])
    Am = [[[Fr(0)] * 3 for _ in range(3)] for _ in range(3)]
    Am[0][0][2] += 1; Am[0][1][1] += 1
    for k in range(3):
        if lab[k] == 3: Am[1][0][k] += 1
        if lab[k] == 2: Am[1][2][k] += 1
        if lab23[k] == 3: Am[2][1][k] += 1
        if lab23[k] == 2: Am[2][2][k] += 1
    for r in range(3): rels.append([Am[r][v // 3][v % 3] for v in range(9)])
    free, M = nullsolve(rels)
    assert len(free) == 3
    lam = {}
    for e in range(9):
        rhs = [Fr(0)] * 9; rhs[e] += 1
        for l in range(3): rhs[free[l]] -= M[e][l]
        lam[e] = solve_rows(rels, rhs)
    w1 = [(1, 1), (1, 0), (-1, 0)]
    w2 = [((sg, 1) if l == 1 else ((1, 0) if l == 2 else (-1, 0))) for l in lab]
    def wtext(i, k):
        if i == 0: return '1'
        s_, p_ = (w1 if i == 1 else w2)[k]
        base = 'c' if i == 1 else "c'"
        if p_ == 1: return f'j * {base}' if s_ == 1 else f'-j * {base}'
        return base if s_ == 1 else f'-{base}'
    def P2_of(x0):
        sv = [sum((M[e][l] * x0[l] for l in range(3)), Fr(0)) for e in range(9)]
        P = {}
        for perm in itertools.permutations(range(3)):
            num = sv[perm[0]] * sv[3 + perm[1]] * sv[6 + perm[2]]
            if num == 0: continue
            (s1_, p1), (s2_, p2) = w1[perm[1]], w2[perm[2]]
            P = padd(P, {2 - p1 - p2: num * s1_ * s2_})
        return P
    found = None
    for x0 in itertools.product(range(-3, 4), repeat=3):
        P = P2_of(x0)
        a, b = pred(P)
        if a != 0 or b != 0: found = (x0, P, a, b); break
    x0, P, a, b = found
    Q = pdivq(padd(P, {0: -a, 1: -b}))
    lit3 = lambda f: '![' + ', '.join('![' + ', '.join('![' + ', '.join(fmtF(f(i, k, l)) for l in range(3)) + ']' for k in range(3)) + ']' for i in range(3)) + ']'
    Alit = lit3(lambda r, i, k: Am[r][i][k])
    Mlit = lit3(lambda i, k, l: M[3 * i + k][l])
    Lr = lit3(lambda i, k, ip: lam[3 * i + k][ip])
    La = lit3(lambda i, k, r: lam[3 * i + k][3 + r])
    pil = '![' + ', '.join(str(f // 3) for f in free) + ']'
    pjl = '![' + ', '.join(str(f % 3) for f in free) + ']'
    Wlit = '![' + ', '.join('![' + ', '.join(wtext(i, k) for k in range(3)) + ']' for i in range(3)) + ']'
    x0l = '![' + ', '.join(fmtF(v) for v in x0) + ']'
    X = f'(Matrix.of fun i k => (∑ l, ({Mlit} : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * ({x0l} : Fin 3 → ℂ) l) / ({Wlit} : Fin 3 → Fin 3 → ℂ) i k)'
    ab = f'({fmtF(a)} - {fmtF(b)} * j)'
    hs = ', '.join(f'h{m}{x}' for m in COL for x in ('B3', 'Q3', 'B23', 'Q23'))
    hw2 = []
    for k, m in enumerate(COL):
        if st13[m] == 'Q': hw2.append(f'· exact w13Q {m} h{m}Q3')
        elif st13[m] == 'B': hw2.append(f'· exact w13B {m} h{m}B3')
        else:
            wt = "j * c'" if sg == 1 else "-j * c'"
            hw2.append(f"· show κ3 {m} = {wt} * κ {m}")
            hw2.append(f'  rw [hκ3corner {m} h{m}B3 h{m}Q3, hu1]')
    L = ['exfalso',
         'have hj0 := jsq_ne hj',
         'refine stest_glob hL h9 r1 r2 r3 h12 h13 h23 h0 κ κ2 κ3 hκ0 hκ20 hκ30 hκL hκ2L hκ3L p q s hpq hps hqs',
         f'  {Alit} ?_',
         f'  {Mlit}',
         f'  {pil} {pjl}',
         f'  {Lr}',
         f'  {La} ?_',
         f'  {Wlit} ?_ ?_ ?_ ?_ {x0l} ?_',
         '· intro t ht ho r',
         '  obtain ⟨R12, R13, R23⟩ := hloc t ht ho',
         f'  simp only [{hs}, ite_true, ite_false, zero_add, add_zero] at R13 R23',
         f'  rcases fin3_cases r with rfl | rfl | rfl <;> simp only [{SIMPV}]',
         '  · linear_combination R12', '  · linear_combination R13', '  · linear_combination R23',
         '· intro i k v',
         '  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>',
         f'    simp only [{SIMPV}] <;> ring',
         '· intro k',
         '  rcases fin3_cases k with rfl | rfl | rfl <;> rfl',
         '· intro i k',
         '  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>',
         f'    simp only [{SIMPC}] <;>',
         "    first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |",
         "      exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |",
         "      exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'",
         '· intro k',
         '  rcases fin3_cases k with rfl | rfl | rfl',
         '  · exact hw1.1', '  · exact hw1.2.1', '  · exact hw1.2.2',
         '· intro k',
         '  rcases fin3_cases k with rfl | rfl | rfl']
    L += ['  ' + x for x in hw2]
    L += ['· intro hz',
          f"  have hP : {X}.permanent * (j ^ 2 * c * c') = {ptext(P)} := by",
          '    rw [permanent_three]',
          f'    simp only [Matrix.of_apply, {SIMPV}]',
          '    field_simp',
          '    ring',
          '  rw [hz, zero_mul] at hP',
          f'  have hN : ({fmtF(a * a + b * b)} : ℂ) = 0 := by',
          f'    linear_combination (-{ab}) * hP + ({fmtF(b)} ^ 2 - {ab} * {ptext(Q)}) * hj',
          '  norm_num at hN']
    return L
def leaf2(st13, st23, pts):
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
            pr = next((m, mp) for m, mp in itertools.combinations(pts, 2) if ks[m] != ks[mp])
            L += cert2(pr[0], pr[1], st13, st23, s1, s2)
            return L
        t13 = tuple(st13[m] for m in COL); t23 = tuple(st23[m] for m in COL)
        l13 = tuple(LAB[a] for a in t13); l23 = tuple(LAB[a] for a in t23)
        sg = s1 if u13 else 1
        key = (l13, l23, sg)
        if key not in GEN and not u13: key = (l13, l23, -1)
        if key in GEN:
            L += glob_leaf(l13, key[2], l23, st13)
            return L
        assert (t13, t23) in NP
        L.append(f'exact {disj_proof(t13, t23)}')
        return L
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
def status_split2(m, pair, cont):
    suf = '3' if pair == '13' else '23'
    QS, BS = ('Q13', 'B13') if pair == '13' else ('Q23', 'B23')
    hQB = 'hQB13' if pair == '13' else 'hQB23'
    pat = f'⟨h{m}Q{suf}, h{m}B{suf}⟩'
    out = [f'rcases status3 {QS} {BS} {hQB} {m} with {pat} | {pat} | {pat}']
    for st in ('Q', 'B', 'C'):
        sub = cont(st)
        out += ['· ' + sub[0]] + ['  ' + l for l in sub[1:]]
    return out
STATS2 = {'leaves': 0}
def tree2(k, st13, st23):
    if k == 3:
        STATS2['leaves'] += 1
        return leaf2(st13, st23, COL)
    m = ORDER[k]
    p13 = f'⟨h{m}Q3, h{m}B3⟩'; p23 = f'⟨h{m}Q23, h{m}B23⟩'
    out = [f'rcases And.intro (status3 Q13 B13 hQB13 {m}) (status3 Q23 B23 hQB23 {m}) with',
           f'  ⟨{p13} | {p13} | {p13}, {p23} | {p23} | {p23}⟩']
    for a13 in ('Q', 'B', 'C'):
        for a23 in ('Q', 'B', 'C'):
            n13 = dict(st13); n13[m] = a13
            n23 = dict(st23); n23[m] = a23
            L = vlines2(m, a13, a23)
            known = ORDER[:k + 1]
            if k == 1 and not consistent_any(n13, n23, known):
                STATS2['leaves'] += 1
                L = L + leaf2(n13, n23, known)
            else:
                L = L + tree2(k + 1, n13, n23)
            out += ['· ' + L[0]] + ['  ' + x for x in L[1:]]
    return out
body2 = tree2(0, {}, {})
concl = '    ' + ' ∨\n    '.join(disj_text()) + ' := by'
text = HEAD + concl + '\n' + PRE + '\n'.join('  ' + x for x in body2) + '\n'
old = open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_9.txt', encoding='utf-8').read()
rest = old[old.index('\ndef T3Rest : Prop :='):]
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_9b.txt', 'w', encoding='utf-8').write('\n' + text + rest)
print('leaves', STATS2['leaves'], 't3_trans lines', text.count('\n'), 'bytes', len(text.encode()), 'total file', len(('\n' + text + rest).encode()))
