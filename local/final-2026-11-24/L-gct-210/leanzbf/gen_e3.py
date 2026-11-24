# gen_e3.py: per-(configuration, S) 3-factor completeness lemmas (d = 4) from r3_export_p*.txt (exact r3_exact data).
# The Gaussian unit i of verify2's data is replaced by an abstract j with j * j = -1 (covers eps_2 = +-1 at once);
# the identity perm(T(x)) = l1'(x) l2(x) l3(x) (l1' = k l1) holds modulo j^2 + 1, closed by linear_combination P * hj.
import sys, ast, glob
from fractions import Fraction as Fr
import sympy as sp

j = sp.Symbol('j')
X = sp.symbols('x0:4')


def gq(p):
    return sp.Rational(Fr(p[0]).numerator, Fr(p[0]).denominator) + sp.Rational(Fr(p[1]).numerator, Fr(p[1]).denominator) * j


def lean_num(q):
    q = sp.Rational(q)
    if q.q == 1:
        return '(%d)' % q.p if q.p < 0 else '%d' % q.p
    return '((%d) / %d)' % (q.p, q.q)


def lean_poly(e):
    # e: sympy polynomial expression in x0..x3, j with rational coefficients
    e = sp.expand(e)
    if e == 0:
        return '0'
    P = sp.Poly(e, *X, j)
    terms = []
    for mon, c in P.terms():
        fac = []
        for v, k in zip(list(X) + [j], mon):
            nm = ('x %d' % X.index(v)) if v in X else 'j'
            if nm.startswith('x'):
                nm = '(' + nm + ')'
            fac += [nm] * k
        s = lean_num(c)
        if fac:
            s = s + ' * ' + ' * '.join(fac)
        terms.append(s)
    return ' + '.join(terms)


def red(e):
    # reduce modulo j^2 + 1
    q, r = sp.div(sp.Poly(sp.expand(e), j), sp.Poly(j**2 + 1, j))
    return q.as_expr(), r.as_expr()


def tag(r):
    return 'e3_%s_%s_%s_%s' % (''.join(map(str, r['s12'])), ''.join(map(str, r['s13'])),
                               'p' if r['eps'] == 1 else 'm', ''.join(map(str, r['S'])))


def gen(r):
    E = [[gq(v) for v in e] for e in r['E']]
    u = [[gq(v) for v in row] for row in r['u']]
    T = [[sp.expand(sum(X[e] * E[e][3 * i + k] for e in range(4)) * u[i][k]) for k in range(3)] for i in range(3)]
    k0 = gq(r['k'])
    facs = [[gq(v) for v in f] for f in r['facs']]
    facs[0] = [sp.expand(k0 * v) for v in facs[0]]
    # reduce l1' entries mod j^2+1
    facs = [[red(v)[1] for v in f] for f in facs]
    lin = [sum(f[e] * X[e] for e in range(4)) for f in facs]
    perm = (T[0][0] * T[1][1] * T[2][2] + T[0][0] * T[1][2] * T[2][1] + T[0][1] * T[1][0] * T[2][2] +
            T[0][1] * T[1][2] * T[2][0] + T[0][2] * T[1][0] * T[2][1] + T[0][2] * T[1][1] * T[2][0])
    diff = sp.expand(perm - lin[0] * lin[1] * lin[2])
    P, R = red(diff)
    if sp.expand(R) != 0:
        return None
    Tl = ', '.join('![' + ', '.join(lean_poly(T[i][k]) for k in range(3)) + ']' for i in range(3))
    Ls = ['![' + ', '.join(lean_poly(v) for v in f) + ']' for f in facs]
    nm = tag(r)
    s = []
    s.append('theorem %s (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)' % nm)
    s.append('    (h : ∀ x : Fin 4 → ℂ, dot4 z x = 0 →')
    s.append('      (Matrix.of ![%s]).permanent = 0) :' % Tl)
    s.append('    (∀ a b, (%s : Fin 4 → ℂ) a * z b - (%s : Fin 4 → ℂ) b * z a = 0) ∨' % (Ls[0], Ls[0]))
    s.append('      (∀ a b, (%s : Fin 4 → ℂ) a * z b - (%s : Fin 4 → ℂ) b * z a = 0) ∨' % (Ls[1], Ls[1]))
    s.append('      (∀ a b, (%s : Fin 4 → ℂ) a * z b - (%s : Fin 4 → ℂ) b * z a = 0) := by' % (Ls[2], Ls[2]))
    s.append('  refine cub3_cases z _ _ _ _ 1 one_ne_zero (fun x => ?_) h')
    s.append('  simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,')
    s.append('    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]')
    s.append('  linear_combination (%s) * hj' % lean_poly(P))
    return '\n'.join(s) + '\n'


if __name__ == '__main__':
    files = sorted(glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_export_p*.txt'))
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 9
    out = []
    cnt = 0
    bad = 0
    tot = 0
    for f in files:
        for line in open(f):
            if not line.strip():
                continue
            r = ast.literal_eval(line)
            if r['typ'] != 3 or r['d'] != 4:
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
    open('/home/kevxhk/work/L-gct-210/lean/zbf/r10_5.txt', 'w', encoding='utf-8').write('\n' + '\n'.join(out))
    print('3-factor d=4 rows', tot, 'generated', cnt, 'identity failures', bad,
          'bytes', sum(len(x.encode()) for x in out))
