# gen_e1n.py: per-(configuration, S) 1-factor completeness lemmas for d = 5 (dotn, cub1_cases_n) from r3_export_p*.txt; Lean core cub1_cases.
# Data: the factor l, q = c / l, its polar Bq, a basis k0,k1,k2 of ker l, and for the three orderings (k0,k1,k2),
# (k0,k2,k1), (k2,k1,k0) the ternary matrix Q of q and N = (Q + Q^T)^-1. i -> abstract j; identities mod j^2 + 1.
import sys, ast, glob, itertools
import sympy as sp
sys.path.insert(0, '/home/kevxhk/work/L-gct-210/leanzbf')
from gen_e3 import gq, lean_num, red, X, j
from gen_e0 import lean_polyv, Y

I = sp.I
X = sp.symbols('x0:5')
XN = ['(x 0)', '(x 1)', '(x 2)', '(x 3)', '(x 4)']
YN = ['(y 0)', '(y 1)', '(y 2)', '(y 3)', '(y 4)']
Yv = sp.symbols('w0:5')


def tag(r):
    return 'e1_%s_%s_%s_%s' % (''.join(map(str, r['s12'])), ''.join(map(str, r['s13'])),
                               'p' if r['eps'] == 1 else 'm', ''.join(map(str, r['S'])))


def toI(e):
    return sp.expand(e.subs(j, I))


def toj(e):
    e = sp.expand(e)
    return sp.expand(sp.re(e) + sp.im(e) * j) if e.is_number else sp.expand(e.subs(I, j))


def vec(v):
    return '![' + ', '.join(lean_polyv(sp.sympify(a), [], []) for a in v) + ']'


def mat(M):
    return '![' + ', '.join('![' + ', '.join(lean_polyv(sp.sympify(M[a][b]), [], []) for b in range(3)) + ']' for a in range(3)) + ']'


def gen(r):
    E = [[gq(v) for v in e] for e in r['E']]
    u = [[gq(v) for v in row] for row in r['u']]
    T = [[sp.expand(sum(X[e] * E[e][3 * i + k] for e in range(5)) * u[i][k]) for k in range(3)] for i in range(3)]
    perm = (T[0][0] * T[1][1] * T[2][2] + T[0][0] * T[1][2] * T[2][1] + T[0][1] * T[1][0] * T[2][2] +
            T[0][1] * T[1][2] * T[2][0] + T[0][2] * T[1][0] * T[2][1] + T[0][2] * T[1][1] * T[2][0])
    l = [gq(v) for v in r['facs'][0]]
    lI = [toI(a) for a in l]
    cI = toI(perm)
    linI = sum(lI[e] * X[e] for e in range(5))
    qI, rem = sp.div(sp.Poly(cI, *X, domain='QQ_I'), sp.Poly(linI, *X, domain='QQ_I'))
    if not rem.is_zero:
        return None
    qI = qI.as_expr()
    q = toj(qI)
    lj = [toj(a) for a in lI]
    # polar form
    Bq = sp.expand(q.subs({X[e]: X[e] + sp.Symbol('s') * Yv[e] for e in range(5)}, simultaneous=True))
    Bq = sp.expand(sp.Poly(Bq, sp.Symbol('s')).coeff_monomial(sp.Symbol('s')))
    # kernel basis of l over Q(i)
    M = sp.Matrix([lI])
    ns = M.nullspace()
    if len(ns) != 4:
        return None
    kall = [[sp.nsimplify(sp.expand(v[e])) for e in range(5)] for v in ns]
    ks = None
    pool = list(kall)
    for a_, b_ in itertools.combinations(range(4), 2):
        pool.append([sp.expand(x + y) for x, y in zip(kall[a_], kall[b_])])
        pool.append([sp.expand(x - y) for x, y in zip(kall[a_], kall[b_])])
    for tri in itertools.combinations(range(len(pool)), 3):
        cand = [pool[i] for i in tri]
        if sp.Matrix(cand).rank() < 3:
            continue
        sub0 = {X[e]: sum(Y[i] * cand[i][e] for i in range(3)) for e in range(5)}
        qy0 = sp.Poly(sp.expand(qI.subs(sub0, simultaneous=True)), *Y)
        Q0 = [[0] * 3 for _ in range(3)]
        for mon, c in qy0.terms():
            idx = sorted([i for i in range(3) for _ in range(mon[i])])
            Q0[idx[0]][idx[1]] = sp.expand(c)
        if sp.expand(sp.Matrix(3, 3, lambda a, b: Q0[a][b] + Q0[b][a]).det()) != 0:
            ks = cand
            break
    if ks is None:
        return None
    orders = [(0, 1, 2), (0, 2, 1), (2, 1, 0)]
    Qs, Ns = [], []
    for o in orders:
        kk = [ks[o[0]], ks[o[1]], ks[o[2]]]
        sub = {X[e]: sum(Y[i] * kk[i][e] for i in range(3)) for e in range(5)}
        qy = sp.Poly(sp.expand(qI.subs(sub, simultaneous=True)), *Y)
        Q = [[0] * 3 for _ in range(3)]
        for mon, c in qy.terms():
            idx = sorted([i for i in range(3) for _ in range(mon[i])])
            Q[idx[0]][idx[1]] = sp.expand(c)
        S = sp.Matrix(3, 3, lambda a, b: Q[a][b] + Q[b][a])
        if sp.expand(S.det()) == 0:
            return None
        Ninv = S.inv()
        Qs.append([[toj(Q[a][b]) for b in range(3)] for a in range(3)])
        Ns.append([[toj(sp.nsimplify(sp.expand(Ninv[a, b]))) for b in range(3)] for a in range(3)])
    ksj = [[toj(sp.sympify(a)) for a in v] for v in ks]
    # certificates
    lin = sum(lj[e] * X[e] for e in range(5))
    Pid, R = red(sp.expand(perm - lin * q))
    if sp.expand(R) != 0:
        return None
    Ph = []
    for oi, o in enumerate(orders):
        Q, N = Qs[oi], Ns[oi]
        grad = [sum((Q[k][b] + Q[b][k]) * Y[b] for b in range(3)) for k in range(3)]
        for i in range(3):
            P, R = red(sp.expand(Y[i] - sum(N[i][k] * grad[k] for k in range(3))))
            if sp.expand(R) != 0:
                return None
            Ph.append(P)
        kk = [ksj[o[0]], ksj[o[1]], ksj[o[2]]]
        sub = {X[e]: sum(Y[i] * kk[i][e] for i in range(3)) for e in range(5)}
        quadQ = sum(Q[a][b] * Y[a] * Y[b] for a in range(3) for b in range(3))
        P, R = red(sp.expand(q.subs(sub, simultaneous=True) - quadQ))
        if sp.expand(R) != 0:
            return None
        Ph.append(P)
    nm = tag(r)
    Tl = ', '.join('![' + ', '.join(lean_polyv(T[i][k], list(X), XN) for k in range(3)) + ']' for i in range(3))
    s = []
    s.append('theorem %s (j : ℂ) (hj : j * j = -1) (z : Fin 5 → ℂ)' % nm)
    s.append('    (h : z ≠ 0 → ∀ x : Fin 5 → ℂ, dotn z x = 0 →')
    s.append('      (Matrix.of ![%s]).permanent = 0) :' % Tl)
    s.append('    z = 0 ∨ (∀ a b, (%s : Fin 5 → ℂ) a * z b - (%s : Fin 5 → ℂ) b * z a = 0) := by' % (vec(lj), vec(lj)))
    s.append('  refine cub1_cases_n z _ _ (fun x => %s) ?_' % lean_polyv(q, list(X), XN))
    s.append('    (fun x y => %s) ?_ %s %s %s' % (lean_polyv(Bq, list(X) + list(Yv), XN + YN), vec(ksj[0]), vec(ksj[1]), vec(ksj[2])))
    s.append('    %s %s %s %s %s %s ?_ ?_ ?_ ?_ ?_ ?_ h' % (mat(Qs[0]), mat(Qs[1]), mat(Qs[2]), mat(Ns[0]), mat(Ns[1]), mat(Ns[2])))
    s.append('  · intro x')
    s.append('    simp only [permanent_three, dotn, Fin.sum_univ_five, Matrix.of_apply, Matrix.cons_val_zero,')
    s.append('      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]')
    s.append('    linear_combination (%s) * hj' % lean_polyv(Pid, list(X), XN))
    s.append('  · intro x y s')
    s.append('    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]')
    s.append('    ring')
    for oi in range(3):
        s.append('  · intro x i')
        s.append('    rcases fin3_cases i with rfl | rfl | rfl')
        for i in range(3):
            s.append('    · simp only [gradQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,')
            s.append('        Matrix.head_cons, Matrix.tail_cons]')
            s.append('      linear_combination (%s) * hj' % lean_polyv(Ph[4 * oi + i], list(Y), ['(x 0)', '(x 1)', '(x 2)']))
    for oi in range(3):
        s.append('  · intro y')
        s.append('    simp only [quadQ, Fin.sum_univ_three, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,')
        s.append('      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]')
        s.append('    linear_combination (%s) * hj' % lean_polyv(Ph[4 * oi + 3], list(Y), ['(y 0)', '(y 1)', '(y 2)']))
    return '\n'.join(s) + '\n'


if __name__ == '__main__':
    files = sorted(glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_export_p*.txt'))
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 9
    out = []
    cnt = bad = tot = 0
    for f in files:
        for line in open(f):
            if not line.strip():
                continue
            r = ast.literal_eval(line)
            if r['typ'] != 1 or r['d'] != 5:
                continue
            tot += 1
            if cnt >= limit:
                continue
            g = gen(r)
            if g is None:
                bad += 1
                continue
            out.append(g)
            cnt += 1
    open('/tmp/e1n_test.txt', 'w', encoding='utf-8').write('\n' + '\n'.join(out))
    print('1-factor d=4 rows', tot, 'generated', cnt, 'failures', bad, 'bytes', sum(len(x.encode()) for x in out))
