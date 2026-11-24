# gen_e0.py: per-(configuration, S) 0-factor completeness lemmas (d = 4) from r3_export_p*.txt.
# Certificate: a coordinate section b (3 vectors of C^4) on which the plane cubic g = c|b is smooth, with an explicit
# Jacobian certificate y_k^4 = sum_m Q_km(y) d_m g(y) (quadrics Q_km over Q(i), solved exactly). Lean side: cub0_zero.
# The unit i is replaced by an abstract j (j * j = -1); identities closed by linear_combination P * hj.
import sys, ast, glob, itertools
from fractions import Fraction as Fr
import sympy as sp
sys.path.insert(0, '/home/kevxhk/work/L-gct-210/leanzbf')
from gen_e3 import gq, lean_num, red, X, j

Y = sp.symbols('y0:3')


def lean_polyv(e, vars_, names):
    e = sp.expand(e)
    if e == 0:
        return '0'
    P = sp.Poly(e, *vars_, j)
    terms = []
    for mon, c in P.terms():
        fac = []
        for v, k in zip(list(vars_) + [j], mon):
            nm = names[vars_.index(v)] if v in vars_ else 'j'
            fac += [nm] * k
        s = lean_num(c)
        if fac:
            s = s + ' * ' + ' * '.join(fac)
        terms.append(s)
    return ' + '.join(terms)


def to_qi(e):
    # e: polynomial in j of degree <= 1 after reduction; return (re, im) rationals
    q, r = red(e)
    r = sp.expand(r)
    a = r.subs(j, 0)
    b = sp.expand((r - a) / j) if r != a else 0
    return sp.Rational(a), sp.Rational(b)


class G:
    __slots__ = ('a', 'b')

    def __init__(s, a=0, b=0):
        s.a = Fr(a); s.b = Fr(b)

    def __add__(s, o): return G(s.a + o.a, s.b + o.b)

    def __sub__(s, o): return G(s.a - o.a, s.b - o.b)

    def __mul__(s, o): return G(s.a * o.a - s.b * o.b, s.a * o.b + s.b * o.a)

    def inv(s):
        d = s.a * s.a + s.b * s.b
        return G(s.a / d, -s.b / d)

    def z(s): return s.a == 0 and s.b == 0


def solve(M, rhs):
    # one solution of M v = rhs over Q(i) (M: list of rows of G), or None
    n = len(M[0])
    A = [row[:] + [r] for row, r in zip(M, rhs)]
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if not A[i][c].z()), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        iv = A[r][c].inv()
        A[r] = [x * iv for x in A[r]]
        for i in range(len(A)):
            if i != r and not A[i][c].z():
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    for i in range(r, len(A)):
        if not A[i][n].z():
            return None
    v = [G() for _ in range(n)]
    for i, c in enumerate(piv):
        v[c] = A[i][n]
    return v


def sgq(e):
    a, b = to_qi(e)
    return G(Fr(int(a.p), int(a.q)), Fr(int(b.p), int(b.q)))


def gexpr(g):
    return sp.Rational(g.a.numerator, g.a.denominator) + sp.Rational(g.b.numerator, g.b.denominator) * j


mon2 = [m for m in itertools.product(range(3), repeat=3) if sum(m) == 2]
mon4 = [m for m in itertools.product(range(5), repeat=3) if sum(m) == 4]


def ymon(m):
    return Y[0] ** m[0] * Y[1] ** m[1] * Y[2] ** m[2]


def tag(r):
    return 'e0_%s_%s_%s_%s' % (''.join(map(str, r['s12'])), ''.join(map(str, r['s13'])),
                               'p' if r['eps'] == 1 else 'm', ''.join(map(str, r['S'])))


def gen(r):
    E = [[gq(v) for v in e] for e in r['E']]
    u = [[gq(v) for v in row] for row in r['u']]
    T = [[sp.expand(sum(X[e] * E[e][3 * i + k] for e in range(4)) * u[i][k]) for k in range(3)] for i in range(3)]
    perm = (T[0][0] * T[1][1] * T[2][2] + T[0][0] * T[1][2] * T[2][1] + T[0][1] * T[1][0] * T[2][2] +
            T[0][1] * T[1][2] * T[2][0] + T[0][2] * T[1][0] * T[2][1] + T[0][2] * T[1][1] * T[2][0])
    basis = [[1 if a == i else 0 for a in range(4)] for i in range(4)]
    secs = [[basis[i] for i in trip] for trip in itertools.combinations(range(4), 3)]
    vecs = [list(v) for v in itertools.product((-1, 0, 1), repeat=4) if any(v) and next(x for x in v if x) == 1]
    vecs.sort(key=lambda v: sum(abs(x) for x in v))
    extra = []
    for t3 in itertools.combinations(range(len(vecs)), 3):
        bb = [vecs[i] for i in t3]
        if sp.Matrix(bb).rank() == 3:
            extra.append(bb)
        if len(extra) >= MAXSEC:
            break
    dense = [[[1, 1, 0, 2], [0, 1, 1, -1], [1, 0, 2, 1]], [[1, 1, 1, 0], [1, -1, 0, 1], [0, 1, -1, 1]],
             [[1, 1, 0, 1], [0, 1, 1, 1], [1, 0, 1, -1]], [[1, 2, 0, 1], [0, 1, 2, -1], [1, -1, 1, 2]],
             [[2, 1, 1, 0], [1, 0, 1, 2], [0, 1, -1, 1]], [[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1]]]
    secs += dense + extra
    best = None
    for b in secs:
        sub = {X[a]: sum(Y[i] * b[i][a] for i in range(3)) for a in range(4)}
        g = sp.expand(perm.subs(sub, simultaneous=True))
        g = red(g)[1]
        Pg = sp.Poly(g, *Y)
        TT = [[[0] * 3 for _ in range(3)] for _ in range(3)]
        for mon, c in Pg.terms():
            idx = sorted([i for i in range(3) for _ in range(mon[i])])
            TT[idx[0]][idx[1]][idx[2]] = sp.expand(c)
        grads = [sp.expand(sp.diff(g, Y[m])) for m in range(3)]
        Qs = []
        ok = True
        for k in range(3):
            cols = []
            for m in range(3):
                for q in mon2:
                    pr = sp.Poly(sp.expand(ymon(q) * grads[m]), *Y)
                    d = {mm: c for mm, c in pr.terms()}
                    cols.append([sgq(d.get(m4, 0)) for m4 in mon4])
            M = [[cols[c][rr] for c in range(len(cols))] for rr in range(len(mon4))]
            rhs = [G(1) if m4 == tuple(4 if a == k else 0 for a in range(3)) else G(0) for m4 in mon4]
            v = solve(M, rhs)
            if v is None:
                ok = False
                break
            Qk = []
            for m in range(3):
                Qk.append(sp.expand(sum(gexpr(v[6 * m + qi]) * ymon(q) for qi, q in enumerate(mon2))))
            Qs.append(Qk)
        if not ok:
            continue
        # Lean text
        nm = tag(r)
        Tl = ', '.join('![' + ', '.join(lean_polyv(T[i][k], list(X), ['(x 0)', '(x 1)', '(x 2)', '(x 3)']) for k in range(3)) + ']' for i in range(3))
        Bl = ['![' + ', '.join(str(v) for v in bb) + ']' for bb in b]
        Ql = '![' + ', '.join('![' + ', '.join(lean_polyv(Qs[k][m], list(Y), ['(x 0)', '(x 1)', '(x 2)']) for m in range(3)) + ']' for k in range(3)) + ']'
        # certificates P
        Ps = []
        for k in range(3):
            gT = [sum((TT[m][a][c] + TT[a][m][c] + TT[a][c][m]) * Y[a] * Y[c] for a in range(3) for c in range(3)) for m in range(3)]
            diff = sp.expand(Y[k] ** 4 - sum(Qs[k][m] * gT[m] for m in range(3)))
            P, R = red(diff)
            if sp.expand(R) != 0:
                return None
            Ps.append(P.subs({Y[0]: sp.Symbol('X0'), Y[1]: sp.Symbol('X1'), Y[2]: sp.Symbol('X2')}))
        cubTT = sum(TT[a][bq][c] * Y[a] * Y[bq] * Y[c] for a in range(3) for bq in range(3) for c in range(3))
        Psec, R = red(sp.expand(perm.subs(sub, simultaneous=True) - cubTT))
        if sp.expand(R) != 0:
            return None
        Xn = sp.symbols('X0:3')
        s = []
        s.append('theorem %s (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)' % nm)
        s.append('    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →')
        s.append('      (Matrix.of ![%s]).permanent = 0) : z = 0 := by' % Tl)
        s.append('  refine cub0_zero z _ %s %s %s' % (Bl[0], Bl[1], Bl[2]))
        s.append('    %s (fun k i x => %s k i) ?_ ?_ h' % (TTl_const(TT), Ql))
        s.append('  · intro x k')
        s.append('    rcases fin3_cases k with rfl | rfl | rfl')
        for k in range(3):
            s.append('    · simp only [gradT, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,')
            s.append('        Matrix.head_cons, Matrix.tail_cons]')
            s.append('      linear_combination (%s) * hj' % lean_polyv(Ps[k], list(Xn), ['(x 0)', '(x 1)', '(x 2)']))
        s.append('  · intro y')
        s.append('    simp only [permanent_three, cubT, Fin.sum_univ_three, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,')
        s.append('      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]')
        s.append('    linear_combination (%s) * hj' % lean_polyv(Psec, list(Y), ['(y 0)', '(y 1)', '(y 2)']))
        txt = '\n'.join(s) + '\n'
        if best is None or len(txt) < len(best):
            best = txt
        TRIES[0] += 1
        if TRIES[0] >= KEEP:
            break
    TRIES[0] = 0
    return best


TRIES = [0]
MAXSEC = 40
KEEP = 1


def TTl_const(TT):
    return '![' + ', '.join('![' + ', '.join('![' + ', '.join(lean_polyv(TT[a][b][c], list(Y), ['y0', 'y1', 'y2']) for c in range(3)) + ']' for b in range(3)) + ']' for a in range(3)) + ']'


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
            if r['typ'] != 0 or r['d'] != 4:
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
    open('/home/kevxhk/work/L-gct-210/lean/zbf/r10_7.txt', 'w', encoding='utf-8').write('\n' + '\n'.join(out))
    print('0-factor d=4 rows', tot, 'generated', cnt, 'failures', bad, 'bytes', sum(len(x.encode()) for x in out))
