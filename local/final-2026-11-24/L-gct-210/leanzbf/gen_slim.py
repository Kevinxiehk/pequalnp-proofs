# Generator: slim instances of the S-test core lemmas through the generic lemma stest_gen (r8_1).
# Keeps the exact headers (names, signatures) of the existing t1p_* (r6_1) and t3p_* (r6_7) lemmas; replaces the bodies.
# Output: lean/zbf/r6_1g.txt (t1p) and lean/zbf/r6_7g.txt (t3p).
import itertools, re
from fractions import Fraction as Fr
exec(open('/home/kevxhk/work/L-gct-210/leanzbf/gen_t1p.py', encoding='utf-8').read().split('lemmas = []; index = []')[0])
def padd(a, b):
    out = dict(a)
    for k, v in b.items(): out[k] = out.get(k, Fr(0)) + v
    return {k: v for k, v in out.items() if v != 0}
def pmul(a, b):
    out = {}
    for i, x in a.items():
        for k, y in b.items(): out[i + k] = out.get(i + k, Fr(0)) + x * y
    return {k: v for k, v in out.items() if v != 0}
def pred(a):
    A = Fr(0); B = Fr(0)
    for d, v in a.items():
        r = d % 4
        if r == 0: A += v
        elif r == 1: B += v
        elif r == 2: A -= v
        else: B -= v
    return A, B
def pdivq(a):
    num = dict(a); q = {}
    while num and max(num) >= 2:
        d = max(num); v = num[d]
        q[d - 2] = q.get(d - 2, Fr(0)) + v
        num[d] = num[d] - v; num[d - 2] = num.get(d - 2, Fr(0)) - v
        num = {k: x for k, x in num.items() if x != 0}
    return {k: v for k, v in q.items() if v != 0}
def ptext(a):
    if not a: return '0'
    parts = []
    for d in sorted(a):
        mon = '' if d == 0 else (' * j' if d == 1 else f' * j ^ {d}')
        parts.append(f'{fmt(a[d])}{mon}')
    return '(' + ' + '.join(parts) + ')'
SIMPV = 'Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons'
SIMPC = 'Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons'
def body(lab, sg, rel23):
    # rel23: list of (i, k, coef) entries of the third pair relation
    rels = []
    for i in range(3): rels.append([Fr(1) if v // 3 == i else Fr(0) for v in range(9)])
    A = [[[Fr(0)] * 3 for _ in range(3)] for _ in range(3)]
    A[0][0][2] += 1; A[0][1][1] += 1
    for k in range(3):
        if lab[k] == 3: A[1][0][k] += 1
        if lab[k] == 2: A[1][2][k] += 1
    for (i, k, cf) in rel23: A[2][i][k] += cf
    for r in range(3): rels.append([A[r][v // 3][v % 3] for v in range(9)])
    free, M = nullsolve(rels)
    assert len(free) == 3
    lam = {}
    for e in range(9):
        rhs = [Fr(0)] * 9; rhs[e] += 1
        for l in range(3): rhs[free[l]] -= M[e][l]
        lam[e] = solve_rows(rels, rhs)
    # weights: (coefficient sign, j-power) for rows 1, 2
    w1 = [(1, 1), (1, 0), (-1, 0)]
    w2 = [((sg, 1) if l == 1 else ((1, 0) if l == 2 else (-1, 0))) for l in lab]
    def wtext(i, k):
        if i == 0: return '1'
        s, p = (w1 if i == 1 else w2)[k]
        base = 'c' if i == 1 else "c'"
        if p == 1: return f'j * {base}' if s == 1 else f'-j * {base}'
        return base if s == 1 else f'-{base}'
    def P2_of(x0):
        s = [sum((M[e][l] * x0[l] for l in range(3)), Fr(0)) for e in range(9)]
        P = {}
        for perm in itertools.permutations(range(3)):
            num = s[0 * 3 + perm[0]] * s[3 + perm[1]] * s[6 + perm[2]]
            if num == 0: continue
            (s1, p1), (s2, p2) = w1[perm[1]], w2[perm[2]]
            P = padd(P, {2 - p1 - p2: num * s1 * s2})
        return P
    found = None
    for x0 in itertools.product(range(-3, 4), repeat=3):
        P = P2_of(x0)
        a, b = pred(P)
        if a != 0 or b != 0: found = (x0, P, a, b); break
    assert found
    x0, P, a, b = found
    Q = pdivq(padd(P, {0: -a, 1: -b}))
    Alit = '![' + ', '.join('![' + ', '.join('![' + ', '.join(fmt(A[r][i][k]) for k in range(3)) + ']' for i in range(3)) + ']' for r in range(3)) + ']'
    Mlit = '![' + ', '.join('![' + ', '.join('![' + ', '.join(fmt(M[3 * i + k][l]) for l in range(3)) + ']' for k in range(3)) + ']' for i in range(3)) + ']'
    Lr = '![' + ', '.join('![' + ', '.join('![' + ', '.join(fmt(lam[3 * i + k][ip]) for ip in range(3)) + ']' for k in range(3)) + ']' for i in range(3)) + ']'
    La = '![' + ', '.join('![' + ', '.join('![' + ', '.join(fmt(lam[3 * i + k][3 + r]) for r in range(3)) + ']' for k in range(3)) + ']' for i in range(3)) + ']'
    pil = '![' + ', '.join(str(f // 3) for f in free) + ']'
    pjl = '![' + ', '.join(str(f % 3) for f in free) + ']'
    Wlit = '![' + ', '.join('![' + ', '.join(wtext(i, k) for k in range(3)) + ']' for i in range(3)) + ']'
    x0l = '![' + ', '.join(fmt(v) for v in x0) + ']'
    X = f'(Matrix.of fun i k => (∑ l, ({Mlit} : Fin 3 → Fin 3 → Fin 3 → ℂ) i k l * ({x0l} : Fin 3 → ℂ) l) / ({Wlit} : Fin 3 → Fin 3 → ℂ) i k)'
    ab = f'({fmt(a)} - {fmt(b)} * j)'
    L = ['  have hj0 := jsq_ne hj',
         f'  refine stest_gen hL h9 rr cc h0 κs hκs hFK {Alit} ?_',
         f'    {Mlit}',
         f'    {pil} {pjl}',
         f'    {Lr}',
         f'    {La} ?_',
         f'    {Wlit} ?_ ?_ ?_ ?_ {x0l} ?_',
         '  · intro t ht r',
         '    obtain ⟨E12, E13, E23⟩ := hrel t ht',
         f'    rcases fin3_cases r with rfl | rfl | rfl <;> simp only [{SIMPV}]',
         '    · linear_combination E12', '    · linear_combination E13', '    · linear_combination E23',
         '  · intro i k v',
         '    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>',
         f'      simp only [{SIMPV}] <;> ring',
         '  · intro k',
         '    rcases fin3_cases k with rfl | rfl | rfl <;> rfl',
         '  · intro i k',
         '    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>',
         f'      simp only [{SIMPC}] <;>',
         "      first | exact one_ne_zero | exact hc | exact hc' | exact neg_ne_zero.mpr hc |",
         "        exact neg_ne_zero.mpr hc' | exact mul_ne_zero hj0 hc | exact mul_ne_zero hj0 hc' |",
         "        exact mul_ne_zero (neg_ne_zero.mpr hj0) hc'",
         '  · intro k',
         '    rcases fin3_cases k with rfl | rfl | rfl',
         '    · exact hw1.1', '    · exact hw1.2.1', '    · exact hw1.2.2',
         '  · intro k',
         '    rcases fin3_cases k with rfl | rfl | rfl',
         '    · exact hw2.1', '    · exact hw2.2.1', '    · exact hw2.2.2',
         '  · intro hz',
         f"    have hP : {X}.permanent * (j ^ 2 * c * c') = {ptext(P)} := by",
         '      rw [permanent_three]',
         f'      simp only [Matrix.of_apply, {SIMPV}]',
         '      field_simp',
         '      ring',
         '    rw [hz, zero_mul] at hP',
         f'    have hN : ({fmt(a * a + b * b)} : ℂ) = 0 := by',
         f'      linear_combination (-{ab}) * hP + ({fmt(b)} ^ 2 - {ab} * {ptext(Q)}) * hj',
         '    norm_num at hN']
    return '\n'.join(L)
def headers(path):
    t = open(path, encoding='utf-8').read()
    blocks = [b for b in t.split('\n\n') if b.strip()]
    out = []
    for b in blocks:
        lines = b.split('\n')
        k = next(i for i, l in enumerate(lines) if l.rstrip().endswith(':= by'))
        hdr = '\n'.join(lines[:k + 1])
        m = re.search(r'theorem (t[13]p_[0-9a-z_]+) ', hdr)
        out.append((m.group(1), hdr))
    return out
res1 = []
for name, hdr in headers('/home/kevxhk/work/L-gct-210/lean/zbf/r6_1.txt'):
    mm = re.match(r't1p_(\d{3})_(\d)_([pm])$', name)
    lab = tuple(int(ch) for ch in mm.group(1)); x = int(mm.group(2)); sg = 1 if mm.group(3) == 'p' else -1
    rel23 = [(1, x, Fr(1)), (2, x, Fr(-1))]
    res1.append(hdr + '\n' + body(lab, sg, rel23))
res7 = []
for name, hdr in headers('/home/kevxhk/work/L-gct-210/lean/zbf/r6_7.txt'):
    mm = re.match(r't3p_(\d{3})_([pm])_(\d{3})$', name)
    lab = tuple(int(ch) for ch in mm.group(1)); sg = 1 if mm.group(2) == 'p' else -1
    lab23 = tuple(int(ch) for ch in mm.group(3))
    rel23 = [(1, k, Fr(1)) for k in range(3) if lab23[k] == 3] + [(2, k, Fr(1)) for k in range(3) if lab23[k] == 2]
    res7.append(hdr + '\n' + body(lab, sg, rel23))
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_1g.txt', 'w', encoding='utf-8').write('\n\n' + '\n\n'.join(res1) + '\n')
open('/home/kevxhk/work/L-gct-210/lean/zbf/r6_7g.txt', 'w', encoding='utf-8').write('\n\n' + '\n\n'.join(res7) + '\n')
print('t1p', len(res1), 't3p', len(res7))
