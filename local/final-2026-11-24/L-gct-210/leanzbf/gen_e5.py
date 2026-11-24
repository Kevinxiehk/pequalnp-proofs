# gen_e5.py s12 s13 eps S F x0 x1 OUT : the (E5) lemma e5_<tag> for one R3-1 survivor (Lean text).
#   S = column triple (e.g. 034), F = three free cells of the [123;S] block as indices 3*i+k (e.g. 013),
#   x0, x1 = two points of {0,1}^3 (values of the free v-cells, lambda = 1), from e5_search.py.
# Statement: configuration context (as the cfg wrappers, with hk1..hK13) + hJn + parameters p (p_K = the pivot det)
#   + the six values M2/M3 on S as linear forms in p + (hq : p_K <> 0)  ->  False.
# Proof: stest_const_eval (cube condition: the hat-block permanent is constant on the lambda = 1 slice) at x0, x1;
#   the dependent cells are solved from the six relations (rows, K12, K13, n**) with pivot p_K (hM certificates);
#   perm(x1) - perm(x0) = delta * c2^-1 c3^-1 prod kappa1(S)^-1 with delta a nonzero constant (Groebner certificate
#   modulo j^2 + 1 and p_K * p_K^-1 = 1).
import sys, itertools
import sympy as sp
sys.path.insert(0, '/home/kevxhk/work/L-gct-210/leanzbf')
from gen_e3 import lean_num, red, j

I = sp.I
s12 = tuple(int(c) for c in sys.argv[1]); s13 = tuple(int(c) for c in sys.argv[2]); eps = int(sys.argv[3])
S = tuple(int(c) for c in sys.argv[4]); F = tuple(int(c) for c in sys.argv[5])
X0 = tuple(int(c) for c in sys.argv[6]); X1 = tuple(int(c) for c in sys.argv[7]); OUT = sys.argv[8]
tag = '%s_%s_%s' % (sys.argv[1], sys.argv[2], 'p' if eps == 1 else 'm')
Sc = [m for m in range(5) if m not in S]
txt = open('/home/kevxhk/work/L-gct-210/leanzbf/surv_families.txt').read()
blk = txt.split('== %s %s %d' % (sys.argv[1], sys.argv[2], eps))[1].split('==')[0]
fam = [sp.sympify(l.strip()) for l in blk.splitlines() if l.strip().startswith('[')]
n = len(fam)
P = list(sp.symbols('p0:%d' % n))
B12 = [m for m in range(5) if s12[m] == 2]; Q12 = [m for m in range(5) if s12[m] == 1]
B13 = [m for m in range(5) if s13[m] == 2]; Q13 = [m for m in range(5) if s13[m] == 1]


def toj(e):
    return sp.expand(sp.expand(sp.sympify(e)).subs(I, j))


def toI(e):
    return sp.expand(sp.sympify(e).subs(j, I))


def rj(e):
    return sp.expand(red(sp.expand(e))[1])


# weights W (kappa_i(S_k) = W * c_i * kappa1(S_k)) and U = 1/W, as Q(j) expressions
def W(i, m):
    if i == 0:
        return sp.Integer(1)
    s = s12 if i == 1 else s13
    return {1: sp.Integer(1), 2: sp.Integer(-1), 0: (j if (i == 1 or eps == 1) else -j)}[s[m]]


def U(i, m):
    w = W(i, m)
    return {1: sp.Integer(1), -1: sp.Integer(-1)}.get(w, -w if w in (j, -j) else None) if w in (1, -1, j, -j) else None


# family with I -> work over Q(I) for linear algebra; reparametrise so that the pivot det becomes p_K
Mv = [sp.expand(sum(P[i] * fam[i][c] for i in range(n))) for c in range(10)]
V = [[sp.Symbol('v%d%d' % (i, k)) for k in range(3)] for i in range(3)]
flat = [V[i][k] for i in range(3) for k in range(3)]
lam = sp.Symbol('lam')


def rels(M2, M3, jj):
    K12 = (1 - jj) / 2; K13 = (1 - eps * jj) / 2
    r = [sum(V[i]) - lam for i in range(3)]
    r.append(sum(V[0][k] for k in range(3) if S[k] in B12) + sum(V[1][k] for k in range(3) if S[k] in Q12) - lam * K12)
    r.append(sum(V[0][k] for k in range(3) if S[k] in B13) + sum(V[2][k] for k in range(3) if S[k] in Q13) - lam * K13)
    r.append(sum(M2[S[k]] * V[1][k] + M3[S[k]] * V[2][k] for k in range(3)))
    return [sp.expand(x) for x in r]


D = [c for c in range(9) if c not in F]
relI = rels(Mv[:5], Mv[5:], I)
AD = sp.Matrix([[r.coeff(flat[c]) for c in D] for r in relI])
det = sp.expand(AD.det())
co = [det.coeff(p) for p in P]
assert sp.expand(det - sum(c * p for c, p in zip(co, P))) == 0, det
K = min((i for i in range(n) if co[i] != 0), key=lambda i: (0 if co[i] in (1, -1) else 1, i))
# new parameters: P' with P'[K] = det; old P[K] = (P'[K] - sum_{i != K} co_i P'[i]) / co_K
sub = {P[K]: (P[K] - sum(co[i] * P[i] for i in range(n) if i != K)) / co[K]}
Mn = [sp.expand(m.subs(sub, simultaneous=True)) for m in Mv]
q = P[K]
relI = rels(Mn[:5], Mn[5:], I)
AD = sp.Matrix([[r.coeff(flat[c]) for c in D] for r in relI])
AF = sp.Matrix([[r.coeff(flat[c]) for c in F] for r in relI])
bb = sp.Matrix([-r.coeff(lam) for r in relI])
detn = sp.expand(AD.det())
assert sp.expand(detn - q) == 0, detn
adj = AD.adjugate().applyfunc(sp.expand)
Mdep = (-adj * AF).applyfunc(sp.expand)      # det * v_D = Mdep * v_F + Ndep * lam
Ndep = (adj * bb).applyfunc(sp.expand)
# check
vF = sp.Matrix([flat[c] for c in F])
for a, c in enumerate(D):
    lhs = q * flat[c] - (Mdep[a, :] * vF)[0] - Ndep[a] * lam
    comb = sum(adj[a, r] * relI[r] for r in range(6))
    assert sp.expand(lhs - comb) == 0
# Lean symbols
pi_ = [F[l] // 3 for l in range(3)]; pj_ = [F[l] % 3 for l in range(3)]
RN = ['r1', 'r2', 'r3']; KN = ['κ1', 'κ2', 'κ3']; CN = ['1', 'c2', 'c3']
Ci = [None, sp.Symbol('Ci2'), sp.Symbol('Ci3')]
Ki = [sp.Symbol('Ki%d' % k) for k in range(3)]
Qi = sp.Symbol('Qi')
NM = {lam: 'w.1', j: 'j', Qi: '%s⁻¹' % ('p%d' % K), Ci[1]: 'c2⁻¹', Ci[2]: 'c3⁻¹'}
for k in range(3):
    NM[Ki[k]] = '(κ1 %d)⁻¹' % S[k]
for i in range(n):
    NM[P[i]] = 'p%d' % i
for i in range(3):
    for k in range(3):
        NM[V[i][k]] = '(%s %d * hat 5 w (%s, %d))' % (KN[i], S[k], RN[i], S[k])


def lp(e):
    e = sp.expand(e)
    if e == 0:
        return '0'
    gens = sorted(e.free_symbols, key=lambda s: s.name)
    if not gens:
        return lean_num(sp.Rational(e))
    Pl = sp.Poly(e, *gens)
    terms = []
    for mon, c in Pl.terms():
        fac = []
        for v, kk in zip(gens, mon):
            fac += [NM[v]] * kk
        s = lean_num(c)
        if fac:
            s = s + ' * ' + ' * '.join(fac)
        terms.append(s)
    return '(' + ' + '.join(terms) + ')'


def jform(e):
    # Q(I) number or polynomial -> Q(j), reduced mod j^2+1
    return rj(toj(e))


# per-cell data (Lean M i j l, N i j, k i j)
Mc = [[[sp.Integer(0)] * 3 for _ in range(3)] for _ in range(3)]
Nc = [[sp.Integer(0)] * 3 for _ in range(3)]
for l in range(3):
    Mc[pi_[l]][pj_[l]][l] = sp.Integer(1)
for a, c in enumerate(D):
    i, k = c // 3, c % 3
    for l in range(3):
        Mc[i][k][l] = jform(Mdep[a, l])
    Nc[i][k] = jform(Ndep[a])
dep = [[(3 * i + k) in D for k in range(3)] for i in range(3)]
klit = '![' + ', '.join('![' + ', '.join(('%s %d * p%d' % (KN[i], S[k], K)) if dep[i][k] else ('%s %d' % (KN[i], S[k]))
                                        for k in range(3)) + ']' for i in range(3)) + ']'
Mlit = '![' + ', '.join('![' + ', '.join('![' + ', '.join(lp(Mc[i][k][l]) for l in range(3)) + ']' for k in range(3)) + ']'
                        for i in range(3)) + ']'
Nlit = '![' + ', '.join('![' + ', '.join(lp(Nc[i][k]) for k in range(3)) + ']' for i in range(3)) + ']'
pilit = '![' + ', '.join(str(x) for x in pi_) + ']'; pjlit = '![' + ', '.join(str(x) for x in pj_) + ']'
x0lit = '![' + ', '.join(str(x) for x in X0) + ']'; x1lit = '![' + ', '.join(str(x) for x in X1) + ']'


# entries y_ik = num * U * Ci * Ki * (Qi if dep)
def entries(Xv):
    Y = [[None] * 3 for _ in range(3)]
    for i in range(3):
        for k in range(3):
            num = sum(Mc[i][k][l] * Xv[l] for l in range(3)) + Nc[i][k]
            e = num * U(i, S[k]) * Ki[k] * (Ci[i] if i > 0 else 1) * (Qi if dep[i][k] else 1)
            Y[i][k] = sp.expand(e)
    return Y


Y0 = entries(X0); Y1 = entries(X1)


def perm(Y):
    return sp.expand(sum(Y[0][s[0]] * Y[1][s[1]] * Y[2][s[2]] for s in itertools.permutations(range(3))))


P0 = perm(Y0); P1 = perm(Y1)
G = Ci[1] * Ci[2] * Ki[0] * Ki[1] * Ki[2]
# delta: P1 - P0 = delta * G mod (j^2+1, q*Qi-1)
gens = [Qi, j] + [p for p in P] + [Ci[1], Ci[2]] + Ki
diff = sp.expand(P1 - P0)
_, rem = sp.reduced(diff, [j ** 2 + 1, q * Qi - 1], *gens, order='lex')
rem = sp.expand(rem)
delta = sp.expand(sp.cancel(rem / G))
assert not (delta.free_symbols - {j}), delta
dre = delta.coeff(j, 0); dim = delta.coeff(j, 1)
assert sp.expand(delta - dre - dim * j) == 0 and (dre != 0 or dim != 0)
T = sp.expand(delta * G + P0 - P1)
(e1, e2), rem2 = sp.reduced(T, [j ** 2 + 1, q * Qi - 1], *gens, order='lex')
assert sp.expand(rem2) == 0
# --- Lean text
ctx = ('{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)\n'
       '    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)\n'
       '    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)\n'
       '    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)\n')
wt = lambda w: {1: '1', -1: '(-1)'}[w] if w in (1, -1) else ('j' if w == j else '(-1) * j')
hw2 = ' ∧ '.join('κ2 %d = %s * (c2 * κ1 %d)' % (m, wt(W(1, m)), m) for m in range(5))
hw3 = ' ∧ '.join('κ3 %d = %s * (c3 * κ1 %d)' % (m, wt(W(2, m)), m) for m in range(5))
g12 = ' + '.join(['κ1 %d * t (r1, %d)' % (m, m) for m in B12] + ['κ2 %d * t (r2, %d)' % (m, m) for m in Q12]) + ' = 0'
g13 = ' + '.join(['κ1 %d * t (r1, %d)' % (m, m) for m in B13] + ['κ3 %d * t (r3, %d)' % (m, m) for m in Q13]) + ' = 0'
EPSL = '1' if eps == 1 else '(-1)'
K12txt = ' + '.join(['κ1 %d' % m for m in B12] + ['κ2 %d' % m for m in Q12])
K13txt = ' + '.join(['κ1 %d' % m for m in B13] + ['κ3 %d' % m for m in Q13])
ctx += ('    (hw2 : %s)\n    (hw3 : %s)\n' % (hw2, hw3) +
        '    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)\n'
        '    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)\n'
        '    (hg12 : ∀ t ∈ L, %s)\n    (hg13 : ∀ t ∈ L, %s)\n' % (g12, g13) +
        '    (M2 M3 : Fin 5 → ℂ)\n'
        '    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)\n'
        '    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)\n'
        '    (hK12 : (%s) * (1 + j) = 1) (hK13 : (%s) * (1 + %s * j) = 1)\n' % (K12txt, K13txt, EPSL) +
        '    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0)')
NMp = dict(NM)
mlines = []
mnames = []
for half, nm in ((0, 'M2'), (1, 'M3')):
    for k in range(3):
        e = jform(Mn[5 * half + S[k]])
        mnames.append('hm%s%d' % (nm[1], S[k]))
        mlines.append('(hm%s%d : %s %d = %s)' % (nm[1], S[k], nm, S[k], lp(e)))
L = []
L.append('set_option maxHeartbeats 4000000 in')
L.append('theorem e5_%s %s\n    (%s : ℂ)\n    %s\n    (hq : p%d ≠ 0) : False := by' % (
    tag, ctx, ' '.join('p%d' % i for i in range(n)), '\n    '.join(' '.join(mlines[a:a + 2]) for a in range(0, 6, 2)), K))
CV = ('Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, '
      'Matrix.head_cons, Matrix.tail_cons')
L.append('  obtain ⟨hw20, hw21, hw22, hw23, hw24⟩ := hw2')
L.append('  obtain ⟨hw30, hw31, hw32, hw33, hw34⟩ := hw3')
L.append('  have hj0 : j ≠ 0 := by')
L.append('    rintro rfl')
L.append('    norm_num at hj')
L.append('  have hJ : j⁻¹ = -j := (eq_inv_of_mul_eq_one_right (by linear_combination -hj : j * -j = 1)).symm')
L.append('  have hqi : p%d * p%d⁻¹ = 1 := mul_inv_cancel₀ hq' % (K, K))
L.append('  have hc2 : c2 ≠ 0 := by')
L.append('    intro h')
L.append('    apply hκ2 0')
L.append('    rw [hw20, h]')
L.append('    ring')
L.append('  have hc3 : c3 ≠ 0 := by')
L.append('    intro h')
L.append('    apply hκ3 0')
L.append('    rw [hw30, h]')
L.append('    ring')
L.append('  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23')
L.append("  obtain ⟨cc, hc0, hc1, hc2'⟩ := exists_equiv3 %d %d %d (by decide) (by decide) (by decide)" % S)
L.append('  have h0 := h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX')
L.append('  have hk : ∀ i jj, (%s : Fin 3 → Fin 3 → ℂ) i jj ≠ 0 := by' % klit)
L.append('    intro i jj')
L.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases jj with rfl | rfl | rfl <;>')
L.append('      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>')
L.append('      first | exact hκ1 _ | exact hκ2 _ | exact hκ3 _ | exact mul_ne_zero (hκ1 _) hq |')
L.append('        exact mul_ne_zero (hκ2 _) hq | exact mul_ne_zero (hκ3 _) hq')
# relations on blockSpace
aB12 = '![' + ', '.join(('κ1 %d' % m) if m in B12 else '0' for m in range(5)) + ']'
bQ12 = '![' + ', '.join(('κ2 %d' % m) if m in Q12 else '0' for m in range(5)) + ']'
aB13 = '![' + ', '.join(('κ1 %d' % m) if m in B13 else '0' for m in range(5)) + ']'
bQ13 = '![' + ', '.join(('κ3 %d' % m) if m in Q13 else '0' for m in range(5)) + ']'
L.append('  have hM : ∀ w ∈ blockSpace L rr cc, ∀ i jj, (%s : Fin 3 → Fin 3 → ℂ) i jj * hat 5 w (rr (Sum.inl i), cc (Sum.inl jj)) =' % klit)
L.append('      ∑ l, (%s : Fin 3 → Fin 3 → Fin 3 → ℂ) i jj l * ((%s : Fin 3 → Fin 3 → ℂ) ((%s : Fin 3 → Fin 3) l) ((%s : Fin 3 → Fin 3) l) *' % (Mlit, klit, pilit, pjlit))
L.append('        hat 5 w (rr (Sum.inl ((%s : Fin 3 → Fin 3) l)), cc (Sum.inl ((%s : Fin 3 → Fin 3) l)))) + (%s : Fin 3 → Fin 3 → ℂ) i jj * w.1 := by' % (pilit, pjlit, Nlit))
L.append('    intro w hw i jj')
L.append('    have R1 := rel_hat1 rr cc 0 r1 hr1 κ1 1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF1 t ht) hk1 w hw')
L.append('    have R2 := rel_hat1 rr cc 1 r2 hr2 κ2 1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF2 t ht) hk2 w hw')
L.append('    have R3 := rel_hat1 rr cc 2 r3 hr3 κ3 1 (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF3 t ht) hk3 w hw')
for nm, a, b, ii, rp, hg, hK, Kt, EP in (('R4', aB12, bQ12, 1, 'r2', 'hg12', 'hK12', K12txt, '1'), ('R5', aB13, bQ13, 2, 'r3', 'hg13', 'hK13', K13txt, EPSL)):
    L.append('    have %s := rel_hat2 rr cc 0 %d r1 %s hr1 hr%d (%s : Fin 5 → ℂ) (%s : Fin 5 → ℂ) ((1 - %s * j) / 2)' % (nm, ii, rp, ii + 1, a, b, EP))
    L.append('      (fun t ht => by')
    L.append('        simp only [Fin.sum_univ_five, %s]' % CV)
    L.append('        linear_combination %s t ht)' % hg)
    L.append('      (by')
    L.append('        simp only [Fin.sum_univ_five, %s]' % CV)
    L.append('        linear_combination ((1 - %s * j) / 2) * %s + ((%s) / 2) * hj) w hw' % (EP, hK, Kt))
L.append('    have R6 := rel_hat2 rr cc 1 2 r2 r3 hr2 hr3 (fun m => M2 m * κ2 m) (fun m => M3 m * κ3 m) 0 hn hJn w hw')
L.append('    simp only [Fin.sum_univ_three, hc0, hc1, hc2\', %s] at R1 R2 R3 R4 R5 R6' % CV)
L.append('    rw [%s] at R6' % ', '.join(mnames))
L.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases jj with rfl | rfl | rfl <;>')
L.append('      simp only [Fin.sum_univ_three, %s, hr1, hr2, hr3, hc0, hc1, hc2\']' % CV)
# relations in sympy with j (Lean semantics): R_r : lhs = rhs, residual lhs - rhs
relJ = rels([jform(m) for m in Mn[:5]], [jform(m) for m in Mn[5:]], j)
for i in range(3):
    for k in range(3):
        c = 3 * i + k
        if not dep[i][k]:
            L.append('    · ring')
            continue
        a = D.index(c)
        coef = [jform(adj[a, r]) for r in range(6)]
        goal = sp.expand(q * flat[c] - sum(Mc[i][k][l] * flat[F[l]] for l in range(3)) - Nc[i][k] * lam)
        comb = sp.expand(sum(coef[r] * relJ[r] for r in range(6)))
        qq, rr_ = red(sp.expand(goal - comb))
        assert sp.expand(rr_) == 0
        parts = ['(%s) * R%d' % (lp(coef[r]), r + 1) for r in range(6) if coef[r] != 0]
        if sp.expand(qq) != 0:
            parts.append('(%s) * hj' % lp(qq))
        L.append('    · linear_combination ' + ' + '.join(parts))


def ylit(Y):
    return '![' + ', '.join('![' + ', '.join(lp(Y[i][k]) for k in range(3)) + ']' for i in range(3)) + ']'


simpY = ('Fin.sum_univ_three, %s, div_eq_mul_inv, mul_inv, hJ, inv_neg, inv_one, '
         'hw20, hw21, hw22, hw23, hw24, hw30, hw31, hw32, hw33, hw34' % CV)
for nm, Y, xl in (('hy0', Y0, x0lit), ('hy1', Y1, x1lit)):
    L.append('  have %s : ∀ i jj, (∑ l, (%s : Fin 3 → Fin 3 → Fin 3 → ℂ) i jj l * (%s : Fin 3 → ℂ) l + (%s : Fin 3 → Fin 3 → ℂ) i jj) /' % (nm, Mlit, xl, Nlit))
    L.append('      (%s : Fin 3 → Fin 3 → ℂ) i jj = (%s : Fin 3 → Fin 3 → ℂ) i jj := by' % (klit, ylit(Y)))
    L.append('    intro i jj')
    L.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases jj with rfl | rfl | rfl <;>')
    L.append('      simp only [%s] <;> ring' % simpY)
L.append("  have hc := stest_const_eval hL h9 rr cc h0 (%s : Fin 3 → Fin 3 → ℂ) hk (%s : Fin 3 → Fin 3 → Fin 3 → ℂ) (%s : Fin 3 → Fin 3 → ℂ) (%s : Fin 3 → Fin 3) (%s : Fin 3 → Fin 3) hM %s %s (%s : Fin 3 → Fin 3 → ℂ) (%s : Fin 3 → Fin 3 → ℂ) hy0 hy1" % (klit, Mlit, Nlit, pilit, pjlit, x0lit, x1lit, ylit(Y0), ylit(Y1)))
L.append('  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc')
Gtxt = 'c2⁻¹ * c3⁻¹ * (κ1 %d)⁻¹ * (κ1 %d)⁻¹ * (κ1 %d)⁻¹' % S
dtxt = lp(delta)
L.append('  have key : %s * (%s) = 0 := by' % (dtxt, Gtxt))
parts = ['(-1) * hc']
if sp.expand(e1) != 0:
    parts.append('(%s) * hj' % lp(e1))
if sp.expand(e2) != 0:
    parts.append('(%s) * hqi' % lp(e2))
L.append('    linear_combination ' + ' + '.join(parts))
L.append('  have hd : (%s : ℂ) ≠ 0 := by' % dtxt)
L.append('    intro h')
if dim == 0:
    L.append('    norm_num at h')
else:
    L.append('    have h2 : (%s : ℂ) = 0 := by' % lean_num(dre ** 2 + dim ** 2))
    L.append('      linear_combination (%s - %s * j) * h + %s * hj' % (lean_num(dre), lean_num(dim), lean_num(dim ** 2)))
    L.append('    norm_num at h2')
L.append('  exact mul_ne_zero hd (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hc2) (inv_ne_zero hc3))')
L.append('    (inv_ne_zero (hκ1 %d))) (inv_ne_zero (hκ1 %d))) (inv_ne_zero (hκ1 %d))) key' % S)
open(OUT, 'w').write('\n' + '\n'.join(L) + '\n')
print(tag, 'S', S, 'F', F, 'pivot p%d' % K, 'delta', delta, 'lines', len(L), 'bytes', len('\n'.join(L)))
