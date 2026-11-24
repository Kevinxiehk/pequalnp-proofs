# gen_cfg.py: ONE R3-1 configuration end to end (Lean text): per kept column triple S an E-lemma (3-factor, d = 4) and a
# wrapper (context -> disjunction of explicit linear equations in the n** coordinates M2, M3), then the DFS lemma
# (context + the two (E3) hypotheses -> False). Data: r3_export_p*.txt (exact r3_exact data); i -> abstract j.
# Usage: python3 -I gen_cfg.py "<s12>" "<s13>" <eps> OUTFILE      e.g. 01222 22001 -1
import sys, ast, glob, itertools
import sympy as sp
sys.path.insert(0, '/home/kevxhk/work/L-gct-210/leanzbf')
from gen_e3 import gq, lean_num, red, X, j

I = sp.I
A = sp.symbols('a0:5')   # M2
B = sp.symbols('b0:5')   # M3
MV = list(A) + list(B)
VS = [[sp.Symbol('v%d%d' % (i, m)) for m in range(5)] for i in range(3)]
KN = ['κ1', 'κ2', 'κ3']
RN = ['r1', 'r2', 'r3']


def vname(i, m):
    return '(%s %d * t (%s, %d))' % (KN[i], m, RN[i], m)


def names_map():
    d = {}
    for m in range(5):
        d[A[m]] = '(M2 %d)' % m
        d[B[m]] = '(M3 %d)' % m
        for i in range(3):
            d[VS[i][m]] = vname(i, m)
    for e in range(4):
        d[X[e]] = '(x %d)' % e
    d[j] = 'j'
    return d


NM = names_map()


def lp(e):
    e = sp.expand(e)
    if e == 0:
        return '0'
    gens = sorted(e.free_symbols, key=lambda s: s.name)
    if not gens:
        return lean_num(sp.Rational(e))
    P = sp.Poly(e, *gens)
    terms = []
    for mon, c in P.terms():
        fac = []
        for v, k in zip(gens, mon):
            fac += [NM[v]] * k
        s = lean_num(c)
        if fac:
            s = s + ' * ' + ' * '.join(fac)
        terms.append(s)
    return ' + '.join(terms)


def toI(e):
    return sp.expand(sp.sympify(e).subs(j, I))


def toj(e):
    e = sp.expand(sp.sympify(e))
    return sp.expand(e.subs(I, j))


def redj(e):
    return sp.expand(red(sp.expand(e))[1])


def quot(e):
    q, r = red(sp.expand(e))
    assert sp.expand(r) == 0, r
    return sp.expand(q)


def hjt(P):
    return '' if sp.expand(P) == 0 else ' + (%s) * hj' % lp(P)


def solve_comb(rows, target):
    # rows: list of linear forms (sympy, Q(j)) in variables; target linear form; find lambda (Q(i)) with sum lam*rows = target
    vars_ = sorted(set().union(*[sp.sympify(r).free_symbols for r in rows + [target]]) - {j}, key=lambda s: s.name)
    if not vars_:
        return [0] * len(rows)
    M = sp.Matrix([[toI(sp.expand(r).coeff(v)) for v in vars_] for r in rows]).T
    tv = sp.Matrix([toI(sp.expand(target).coeff(v)) for v in vars_])
    sol, params = M.gauss_jordan_solve(tv)
    sol = sol.subs({p: 0 for p in params})
    return [toj(sp.nsimplify(sp.expand(x))) for x in sol]


def main():
    s12 = tuple(int(c) for c in sys.argv[1]); s13 = tuple(int(c) for c in sys.argv[2]); eps = int(sys.argv[3])
    out = sys.argv[4]
    rows = []
    for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_export_p*.txt')):
        for line in open(f):
            if line.strip():
                r = ast.literal_eval(line)
                if r['s12'] == s12 and r['s13'] == s13 and r['eps'] == eps:
                    rows.append(r)
    assert rows, 'config not found'
    B12 = [m for m in range(5) if s12[m] == 2]; Q12 = [m for m in range(5) if s12[m] == 1]
    B13 = [m for m in range(5) if s13[m] == 2]; Q13 = [m for m in range(5) if s13[m] == 1]
    tag = '%s_%s_%s' % (sys.argv[1], sys.argv[2], 'p' if eps == 1 else 'm')
    # per-S data
    data = []
    for r in rows:
        if r['typ'] not in (0, 1, 3) or r['d'] != 4:
            continue
        S = r['S']
        E = [[toj(toI(gq(v))) for v in e] for e in r['E']]
        u = [[toj(toI(gq(v))) for v in row] for row in r['u']]
        facs = [[toj(toI(gq(v))) for v in f] for f in r['facs']]
        if r['typ'] == 3:
            k0 = toj(toI(gq(r['k'])))
            facs[0] = [redj(k0 * v) for v in facs[0]]
        z = [redj(sum(A[S[k]] * E[e][3 + k] + B[S[k]] * E[e][6 + k] for k in range(3))) for e in range(4)]
        data.append(dict(S=S, E=E, u=u, facs=facs, z=z, typ=r['typ'], row=r))
    # branch equations (Lean semantics: 3-factor -> z proportional to l_i; 1-factor -> z = 0 or z ~ l; 0-factor -> z = 0)
    for dd in data:
        brs = []
        if dd['typ'] in (0, 1):
            brs.append([(None, e, dd['z'][e], dd['z'][e]) for e in range(4) if sp.expand(dd['z'][e]) != 0])
        for l in dd['facs']:
            a0 = next(a for a in range(4) if l[a] != 0)
            eqs = []
            for b in range(4):
                if b != a0:
                    raw = sp.expand(l[a0] * dd['z'][b] - l[b] * dd['z'][a0])
                    if redj(raw) != 0:
                        eqs.append((a0, b, raw, redj(raw)))
            brs.append(eqs)
        dd['brs'] = brs

    def lin_rows(eqs):
        return [toI(e) for e in eqs]

    def null(eqs):
        if not eqs:
            return [sp.Matrix([1 if i == k else 0 for i in range(10)]) for k in range(10)]
        Mx = sp.Matrix([[sp.expand(e).coeff(v) for v in MV] for e in lin_rows(eqs)])
        return Mx.nullspace()

    def inspan(vecs, base):
        Bm = sp.Matrix(base).T
        r0 = Bm.rank()
        return all(sp.Matrix.hstack(Bm, v).rank() == r0 for v in vecs)

    def adm_info(eqs):
        V = null(eqs)
        if not V:
            return 'zero'
        one = [1] * 5
        q13 = [1 if m in Q13 else 0 for m in range(5)]
        q12 = [1 if m in Q12 else 0 for m in range(5)]
        if inspan([sp.Matrix(list(v[5:10])) for v in V], [one, q13]):
            return 'm3'
        if inspan([sp.Matrix(list(v[0:5])) for v in V], [one, q12]):
            return 'm2'
        return None

    def run(order):
        # returns tree or None if some leaf survives
        def node(idx, eqs):
            a = adm_info(eqs)
            if a is not None:
                return ('leaf', a, eqs)
            if idx == len(order):
                return None
            dd = data[order[idx]]
            subs = []
            for br in dd['brs']:
                t = node(idx + 1, eqs + [e[3] for e in br])
                if t is None:
                    return None
                subs.append(t)
            return ('node', order[idx], subs)
        return node(0, [])


    def run_surv(order):
        leaves = []
        def node(idx, eqs):
            a = adm_info(eqs)
            if a is not None:
                return
            if idx == len(order):
                leaves.append(eqs); return
            dd = data[order[idx]]
            for br in dd['brs']:
                node(idx + 1, eqs + [e[3] for e in br])
        node(0, [])
        return leaves
    allidx = list(range(len(data)))
    lv = run_surv(allidx)
    print('triples', len(data), 'surviving leaves', len(lv))
    dims = []
    for eqs in lv:
        V = null(eqs)
        dims.append(len(V))
    print('leaf dims', sorted(set(dims)), 'max', max(dims) if dims else None)
    # greedy: smallest subset whose surviving leaves all have dim <= the max-dim family and are contained in the union family
    import itertools as _it
    Vmax = None
    for eqs in lv:
        V = null(eqs)
        if len(V) == max(dims):
            Vmax = V; break
    print('family basis (M2 | M3):')
    for v in Vmax:
        print('   ', [sp.nsimplify(x) for x in v])

main()
