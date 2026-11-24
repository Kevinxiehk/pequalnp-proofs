# gen_surv.py: survivor version of gen_cfg5.py (DFS whose surviving leaves are closed by the (E5) lemma e5_<tag>).
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
        if not ((r['typ'] in (0, 1, 3) and r['d'] == 4) or (r['typ'] == 1 and r['d'] == 5)):
            continue
        S = r['S']
        E = [[toj(toI(gq(v))) for v in e] for e in r['E']]
        u = [[toj(toI(gq(v))) for v in row] for row in r['u']]
        facs = [[toj(toI(gq(v))) for v in f] for f in r['facs']]
        if r['typ'] == 3:
            k0 = toj(toI(gq(r['k'])))
            facs[0] = [redj(k0 * v) for v in facs[0]]
        D = r['d']
        z = [redj(sum(A[S[k]] * E[e][3 + k] + B[S[k]] * E[e][6 + k] for k in range(3))) for e in range(D)]
        data.append(dict(S=S, E=E, u=u, facs=facs, z=z, typ=r['typ'], row=r, d=D))
    # branch equations (Lean semantics: 3-factor -> z proportional to l_i; 1-factor -> z = 0 or z ~ l; 0-factor -> z = 0)
    for dd in data:
        brs = []
        if dd['typ'] in (0, 1):
            brs.append([(None, e, dd['z'][e], dd['z'][e]) for e in range(dd['d']) if sp.expand(dd['z'][e]) != 0])
        for l in dd['facs']:
            a0 = next(a for a in range(dd['d']) if l[a] != 0)
            eqs = []
            for b in range(dd['d']):
                if b != a0:
                    raw = sp.expand(l[a0] * dd['z'][b] - l[b] * dd['z'][a0])
                    if redj(raw) != 0:
                        eqs.append((a0, b, raw, redj(raw)))
            brs.append(eqs)
        dd['brs'] = brs

    def lin_rows(eqs):
        return [toI(e) for e in eqs]

    import re as _re
    _txt = open('/home/kevxhk/work/L-gct-210/leanzbf/surv_families.txt').read()
    _blk = _txt.split('== %s %s %d' % (sys.argv[1], sys.argv[2], eps))[1].split('==')[0]
    fam = [sp.sympify(l.strip()) for l in _blk.splitlines() if l.strip().startswith('[')]
    nf = len(fam)
    Vmax = sp.Matrix([[fam[i][c] for i in range(nf)] for c in range(10)])
    _lg = open('/home/kevxhk/work/L-gct-210/leanzbf/e5_search_all.log').read() + open('/home/kevxhk/work/L-gct-210/leanzbf/e5s_01222_01222_m.log').read()
    _key = '%s %s %d' % (sys.argv[1], sys.argv[2], eps)
    if _key == '01222 01222 -1':
        _sb = open('/home/kevxhk/work/L-gct-210/leanzbf/e5s_01222_01222_m.log').read()
    else:
        _sb = open('/home/kevxhk/work/L-gct-210/leanzbf/e5_search_all.log').read().split('== ' + _key)[1].split('==')[0]
    _m = _re.search(r'S \((\d), (\d), (\d)\) F \((\d), (\d), (\d)\)', _sb)
    S5 = tuple(int(_m.group(i)) for i in (1, 2, 3)); F5 = tuple(int(_m.group(i)) for i in (4, 5, 6))
    PP = list(sp.symbols('p0:%d' % nf))
    Mv5 = [sp.expand(sum(PP[i] * fam[i][c] for i in range(nf))) for c in range(10)]
    VV = [[sp.Symbol('vv%d%d' % (i, k)) for k in range(3)] for i in range(3)]
    flat5 = [VV[i][k] for i in range(3) for k in range(3)]
    D5 = [c for c in range(9) if c not in F5]
    r6 = sp.expand(sum(Mv5[S5[k]] * VV[1][k] + Mv5[5 + S5[k]] * VV[2][k] for k in range(3)))
    r15 = [sum(VV[i]) for i in range(3)]
    r15.append(sum(VV[0][k] for k in range(3) if S5[k] in B12) + sum(VV[1][k] for k in range(3) if S5[k] in Q12))
    r15.append(sum(VV[0][k] for k in range(3) if S5[k] in B13) + sum(VV[2][k] for k in range(3) if S5[k] in Q13))
    AD5 = sp.Matrix([[sp.expand(r).coeff(flat5[c]) for c in D5] for r in r15 + [r6]])
    det5 = sp.expand(AD5.det())
    co5 = [det5.coeff(p) for p in PP]
    K5 = min((i for i in range(nf) if co5[i] != 0), key=lambda i: (0 if co5[i] in (1, -1) else 1, i))
    sub5 = {PP[K5]: (PP[K5] - sum(co5[i] * PP[i] for i in range(nf) if i != K5)) / co5[K5]}
    Mn5 = [sp.expand(m.subs(sub5, simultaneous=True)) for m in Mv5]
    famp = sp.Matrix([[Mn5[c].coeff(PP[i]) for i in range(nf)] for c in range(10)])
    # left inverse: pick nf independent rows
    Rsel = []
    for c in range(10):
        if sp.Matrix([list(famp.row(x)) for x in Rsel + [c]]).rank() == len(Rsel) + 1:
            Rsel.append(c)
        if len(Rsel) == nf:
            break
    finv = sp.Matrix([list(famp.row(x)) for x in Rsel]).inv()
    pforms = [toj(sp.expand(sum(finv[i, r] * MV[Rsel[r]] for r in range(nf)))) for i in range(nf)]

    def contained(eqs):
        V = null(eqs)
        r0 = Vmax.rank()
        return all(sp.Matrix.hstack(Vmax, v).rank() == r0 for v in V)

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
                return ('e5', eqs) if contained(eqs) else None
            dd = data[order[idx]]
            subs = []
            for br in dd['brs']:
                t = node(idx + 1, eqs + [e[3] for e in br])
                if t is None:
                    return None
                subs.append(t)
            return ('node', order[idx], subs)
        return node(0, [])

    assert run(list(range(len(data)))) is not None, 'not killed with all triples'
    def costf(dd):
        if dd.get('d', 4) == 5:
            return 4
        return {3: 1, 1: 3, 0: 7}[dd['typ']]
    best = None
    for ksz in range(1, len(data) + 1):
        for sub in itertools.combinations(range(len(data)), ksz):
            c = sum(costf(data[i]) for i in sub)
            if best is not None and c >= best[0]:
                continue
            if run(list(sub)) is not None:
                best = (c, list(sub))
        if best is not None:
            break
    order = best[1]
    tree = run(order)
    print('kept S:', [data[i]['S'] for i in order])
    L = []
    # E-lemmas and wrappers
    ctx_bind = ('{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)\n'
                '    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)\n'
                '    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)\n'
                '    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j : ℂ) (hj : j * j = -1)\n')
    w2 = [j if s12[m] == 0 else (1 if s12[m] == 1 else -1) for m in range(5)]
    w3 = [eps * j if s13[m] == 0 else (1 if s13[m] == 1 else -1) for m in range(5)]
    wt = lambda w: {1: '1', -1: '(-1)'}.get(w, None) if not isinstance(w, sp.Basic) or w.is_number else ('j' if w == j else '(-1) * j')
    hw2 = ' ∧ '.join('κ2 %d = %s * (c2 * κ1 %d)' % (m, wt(w2[m]), m) for m in range(5))
    hw3 = ' ∧ '.join('κ3 %d = %s * (c3 * κ1 %d)' % (m, wt(w3[m]), m) for m in range(5))
    g12 = ' + '.join(['κ1 %d * t (r1, %d)' % (m, m) for m in B12] + ['κ2 %d * t (r2, %d)' % (m, m) for m in Q12]) + ' = 0'
    g13 = ' + '.join(['κ1 %d * t (r1, %d)' % (m, m) for m in B13] + ['κ3 %d * t (r3, %d)' % (m, m) for m in Q13]) + ' = 0'
    ctx_bind += ('    (hw2 : %s)\n    (hw3 : %s)\n' % (hw2, hw3) +
                 '    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)\n'
                 '    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0)\n'
                 '    (hg12 : ∀ t ∈ L, %s)\n    (hg13 : ∀ t ∈ L, %s)\n' % (g12, g13) +
                 '    (M2 M3 : Fin 5 → ℂ)\n'
                 '    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)')
    ctx_args = 'hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj hw2 hw3 hF1 hF2 hF3 hg12 hg13 M2 M3 hn'
    need5 = True
    EPSL = '1' if eps == 1 else '(-1)'
    K12txt = ' + '.join(['κ1 %d' % m for m in B12] + ['κ2 %d' % m for m in Q12])
    K13txt = ' + '.join(['κ1 %d' % m for m in B13] + ['κ3 %d' % m for m in Q13])
    if need5:
        ctx_bind += ('\n    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)\n'
                     '    (hK12 : (%s) * (1 + j) = 1) (hK13 : (%s) * (1 + %s * j) = 1)' % (K12txt, K13txt, EPSL))
        ctx_args += ' hk1 hk2 hk3 hK12 hK13'
    for idx in order:
        dd = data[idx]
        S = dd['S']; E = dd['E']; u = dd['u']; facs = dd['facs']; z = dd['z']
        Sc = [m for m in range(5) if m not in S]
        st = ''.join(map(str, S))
        D = dd['d']
        EEl = '![' + ', '.join('![' + ', '.join('![' + ', '.join(lp(E[e][3 * i + k]) for k in range(3)) + ']' for i in range(3)) + ']' for e in range(D)) + ']'
        UUl = '![' + ', '.join('![' + ', '.join(lp(u[i][k]) for k in range(3)) + ']' for i in range(3)) + ']'
        Ls = ['![' + ', '.join(lp(v) for v in f) + ']' for f in facs]
        # E-lemma
        if dd['typ'] == 3:
            T = [[sp.expand(sum(X[e] * E[e][3 * i + k] for e in range(4)) * u[i][k]) for k in range(3)] for i in range(3)]
            perm = (T[0][0] * T[1][1] * T[2][2] + T[0][0] * T[1][2] * T[2][1] + T[0][1] * T[1][0] * T[2][2] +
                    T[0][1] * T[1][2] * T[2][0] + T[0][2] * T[1][0] * T[2][1] + T[0][2] * T[1][1] * T[2][0])
            lin = [sum(f[e] * X[e] for e in range(4)) for f in facs]
            P = quot(perm - lin[0] * lin[1] * lin[2])
        else:
            P = 0
        en = 'e%d_%s_%s' % (dd['typ'], tag, st)
        hEU = ('      (Matrix.of fun i k => (∑ e, x e * (%s : Fin %d → Fin 3 → Fin 3 → ℂ) e i k) *\n'
               '        (%s : Fin 3 → Fin 3 → ℂ) i k).permanent = 0)' % (EEl, D, UUl))
        if dd['typ'] in (0, 1):
            import gen_e0, gen_e1, gen_e1n
            if D == 5:
                txt = gen_e1n.gen(dd['row'])
            else:
                txt = (gen_e1.gen(dd['row']) if dd['typ'] == 1 else gen_e0.gen(dd['row']))
            assert txt is not None, 'certificate generation failed'
            ls_ = txt.split('\n')
            assert ls_[2].startswith('      (Matrix.of ![')
            suffix = ls_[2][ls_[2].index(').permanent = 0)') + len(').permanent = 0)'):]
            ls_[2] = hEU + suffix
            txt = '\n'.join(ls_)
            txt = txt.replace('Matrix.of_apply, Matrix.cons_val_zero,', 'Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,')
            L.append(txt)
        if dd['typ'] == 3:
          L.append('theorem %s (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)\n'
                   '    (h : z ≠ 0 → ∀ x : Fin 4 → ℂ, dot4 z x = 0 →\n'
                   '      (Matrix.of fun i k => (∑ e, x e * (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *\n'
                   '        (%s : Fin 3 → Fin 3 → ℂ) i k).permanent = 0) :\n' % (en, EEl, UUl) +
                   '    (∀ a b, (%s : Fin 4 → ℂ) a * z b - (%s : Fin 4 → ℂ) b * z a = 0) ∨\n' % (Ls[0], Ls[0]) +
                   '      (∀ a b, (%s : Fin 4 → ℂ) a * z b - (%s : Fin 4 → ℂ) b * z a = 0) ∨\n' % (Ls[1], Ls[1]) +
                   '      (∀ a b, (%s : Fin 4 → ℂ) a * z b - (%s : Fin 4 → ℂ) b * z a = 0) := by\n' % (Ls[2], Ls[2]) +
                   '  refine cub3c z _ _ _ _ (fun x => ?_) h\n'
                   '  simp only [permanent_three, dot4, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,\n'
                   '    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]\n'
                   '  linear_combination (%s) * hj\n' % lp(P))
        # lifting data: 4 positions with invertible E-submatrix
        pos = None
        for cand in itertools.combinations(range(9), D):
            Msub = sp.Matrix([[toI(E[e][c]) for e in range(D)] for c in cand])
            if Msub.det() != 0:
                pos = cand; inv = Msub.inv(); break
        PPv = [[0] * 9 for _ in range(D)]
        for e in range(D):
            for fi, c in enumerate(pos):
                PPv[e][c] = toj(sp.nsimplify(sp.expand(inv[e, fi])))
        PPl = '![' + ', '.join('![' + ', '.join('![' + ', '.join(lp(PPv[e][3 * i + k]) for k in range(3)) + ']' for i in range(3)) + ']' for e in range(D)) + ']'
        tau = [[VS[i][S[k]] for k in range(3)] for i in range(3)]
        # restricted relations (in V on S)
        R = [sum(tau[i][k] for k in range(3)) for i in range(3)]
        R.append(sum(tau[0][k] for k in range(3) if S[k] in B12) + sum(tau[1][k] for k in range(3) if S[k] in Q12))
        R.append(sum(tau[0][k] for k in range(3) if S[k] in B13) + sum(tau[2][k] for k in range(3) if S[k] in Q13))
        RN6 = sum(A[S[k]] * tau[1][k] + B[S[k]] * tau[2][k] for k in range(3))
        Pt = [sum(PPv[e][3 * i + k] * tau[i][k] for i in range(3) for k in range(3)) for e in range(D)]
        # hlift certificates
        lift = []
        for i in range(3):
            for k in range(3):
                target = sp.expand(tau[i][k] - sum(Pt[e] * E[e][3 * i + k] for e in range(D)))
                lam = solve_comb([redj(x) for x in R], redj(target))
                rest = sp.expand(target - sum(lam[r] * R[r] for r in range(5)))
                lift.append((lam, quot(rest)))
        # hzk certificate: target = sum z_e Pt_e ; = RN6 - sum_pos N_pos (tau - E P tau)_pos
        target = sp.expand(sum(z[e] * Pt[e] for e in range(D)))
        coefN = {}
        lamz = [0] * 5
        for i in range(3):
            for k in range(3):
                cN = sp.expand(RN6).coeff(tau[i][k])
                if cN != 0:
                    lam, _ = lift[3 * i + k]
                    for r in range(5):
                        lamz[r] = sp.expand(lamz[r] - cN * lam[r])
        rest = sp.expand(target - RN6 - sum(lamz[r] * R[r] for r in range(5)))
        Pz = quot(rest)
        # hU certificates: kappa_s i (S_k) * u_ik = cr_i * kappa1 (S_k)
        wv = [[1] * 5, w2, w3]
        # Lean text of wrapper
        brs = dd['brs']
        brl = []
        for eqs in brs:
            brl.append('(' + ' ∧ '.join('%s = 0' % lp(e[3]) for e in eqs) + ')')
        wn = 'w_%s_%s' % (tag, st)
        s = []
        s.append('theorem %s %s :' % (wn, ctx_bind))
        s.append('    ' + ' ∨\n      '.join(brl) + ' := by')
        s.append('  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23')
        if D == 5:
            s.append('  obtain ⟨cc, hc0, hc1, hc2, hc3, hc4⟩ := exists_equiv5 %d %d %d %d %d (by decide)' % (S + tuple(Sc)))
        else:
            s.append('  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 %d %d %d (by decide) (by decide) (by decide)' % S)
        s.append('  obtain ⟨hw20, hw21, hw22, hw23, hw24⟩ := hw2')
        s.append('  obtain ⟨hw30, hw31, hw32, hw33, hw34⟩ := hw3')
        s.append('  have rel : ∀ t ∈ blkL L rr cc, %s := by' % ' ∧ '.join('%s = 0' % lp(x) for x in R + [RN6]))
        s.append('    intro t ht')
        s.append('    have htL := ((mem_blkL L rr cc t).mp ht).1')
        if D == 5:
            for i in range(3):
                for nmz, b, m, hcn in (('u', 0, Sc[0], 'hc3'), ('v', 1, Sc[1], 'hc4')):
                    s.append('    have z%d%s := tau_blk_zero rr cc t ht %d %d %s %d hr%d %s' % (i, nmz, i, b, RN[i], m, i + 1, hcn))
        else:
            s.append('    obtain ⟨bu, hbu⟩ := compl_inr cc %d %d %d hc0 hc1 hc2 %d ⟨by decide, by decide, by decide⟩' % (S + (Sc[0],)))
            s.append('    obtain ⟨bv, hbv⟩ := compl_inr cc %d %d %d hc0 hc1 hc2 %d ⟨by decide, by decide, by decide⟩' % (S + (Sc[1],)))
            for i in range(3):
                for nmz, b, m in (('u', 'bu', Sc[0]), ('v', 'bv', Sc[1])):
                    s.append('    have z%d%s := tau_blk_zero rr cc t ht %d %s %s %d hr%d %s' % (i, nmz, i, b, RN[i], m, i + 1, 'hbu' if nmz == 'u' else 'hbv'))
        s.append('    have f1 := hF1 t htL')
        s.append('    have f2 := hF2 t htL')
        s.append('    have f3 := hF3 t htL')
        s.append('    have g1 := hg12 t htL')
        s.append('    have g2 := hg13 t htL')
        s.append('    have nn := hn t htL')
        s.append('    simp only [dotL_apply, rowMap_apply, Fin.sum_univ_five] at f1 f2 f3 nn')
        # full relations in V: F_i full = sum_m V_im ; zero terms at Sc
        full = [sum(VS[i][m] for m in range(5)) for i in range(3)]
        fullN = sum(A[m] * VS[1][m] + B[m] * VS[2][m] for m in range(5))
        zt = {(i, m): '%s * z%d%s' % ('κ%d %d' % (i + 1, m), i, 'u' if m == Sc[0] else 'v') for i in range(3) for m in Sc}

        def zcomb(expr_full):
            # expr_full - restricted = sum over Sc terms; return Lean text of sum coeff * kappa * z
            parts = []
            for (i, m), txt in zt.items():
                c = sp.expand(expr_full).coeff(VS[i][m])
                if c != 0:
                    parts.append('(%s) * %s' % (lp(c), txt))
            return parts
        restr_full = [(R[0], full[0], 'f1'), (R[1], full[1], 'f2'), (R[2], full[2], 'f3')]
        g12full = sum(VS[0][m] for m in B12) + sum(VS[1][m] for m in Q12)
        g13full = sum(VS[0][m] for m in B13) + sum(VS[2][m] for m in Q13)
        restr_full += [(R[3], g12full, 'g1'), (R[4], g13full, 'g2'), (RN6, fullN, 'nn')]
        s.append('    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩')
        for rr_, ff, hn_ in restr_full:
            parts = zcomb(ff)
            s.append('    · linear_combination %s' % ' - '.join([hn_] + parts))
        # hlift
        s.append('  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =')
        s.append('      ∑ e, (∑ i\', ∑ k\', (%s : Fin %d → Fin 3 → Fin 3 → ℂ) e i\' k\' * tauMap ![κ1, κ2, κ3] rr cc t i\' k\') *' % (PPl, D))
        s.append('        (%s : Fin %d → Fin 3 → Fin 3 → ℂ) e i k := by' % (EEl, D))
        s.append('    intro t ht i k')
        s.append('    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht')
        s.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>')
        s.append('      simp only [tauMap_apply, %s, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,' % ('Fin.sum_univ_five, Matrix.cons_val_four' if D == 5 else 'Fin.sum_univ_four'))
        s.append('        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]')
        for (lam, Pq) in lift:
            parts = ['(%s) * R%d' % (lp(lam[r]), r + 1) for r in range(5) if lam[r] != 0]
            s.append('    · linear_combination %s%s' % (' + '.join(parts) if parts else '0', hjt(Pq)))
        # hzk
        zl = '![' + ', '.join(lp(x) for x in z) + ']'
        s.append('  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (%s : Fin %d → ℂ) e *' % (zl, D))
        s.append('      (∑ i\', ∑ k\', (%s : Fin %d → Fin 3 → Fin 3 → ℂ) e i\' k\' * tauMap ![κ1, κ2, κ3] rr cc t i\' k\') = 0 := by' % (PPl, D))
        s.append('    intro t ht')
        s.append('    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht')
        s.append('    simp only [tauMap_apply, %s, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,' % ('Fin.sum_univ_five, Matrix.cons_val_four' if D == 5 else 'Fin.sum_univ_four'))
        s.append('      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]')
        parts = ['R6'] + ['(%s) * R%d' % (lp(lamz[r]), r + 1) for r in range(5) if lamz[r] != 0]
        s.append('    linear_combination %s%s' % (' + '.join(parts), hjt(Pz)))
        # hkappa, hU
        s.append('  have hκs : ∀ i m, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i m ≠ 0 := by')
        s.append('    intro i m')
        s.append('    rcases fin3_cases i with rfl | rfl | rfl')
        s.append('    · exact hκ1 m')
        s.append('    · exact hκ2 m')
        s.append('    · exact hκ3 m')
        s.append('  have hU : ∀ i k, (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) i (cc (Sum.inl k)) * (%s : Fin 3 → Fin 3 → ℂ) i k =' % UUl)
        s.append('      (![1, c2, c3] : Fin 3 → ℂ) i * (![κ1, κ2, κ3] : Fin 3 → Fin 5 → ℂ) 0 (cc (Sum.inl k)) := by')
        s.append('    intro i k')
        s.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>')
        s.append('      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,')
        s.append('        Matrix.tail_cons, hc0, hc1, hc2]')
        kap = [[sp.Symbol('K%d_%d' % (i, m)) for m in range(5)] for i in range(3)]
        NM.update({kap[i][m]: '(κ%d %d)' % (i + 1, m) for i in range(3) for m in range(5)})
        cS = [1, sp.Symbol('c2'), sp.Symbol('c3')]
        NM.update({cS[1]: 'c2', cS[2]: 'c3'})
        for i in range(3):
            for k in range(3):
                m = S[k]
                if i == 0:
                    s.append('    · ring')
                    continue
                # goal: kap_i m * u_ik = c_i * kap_0 m ; hyp: kap_i m = w * (c_i * kap_0 m)
                goal = kap[i][m] * u[i][k] - cS[i] * kap[0][m]
                hyp = kap[i][m] - wv[i][m] * (cS[i] * kap[0][m])
                rest = sp.expand(goal - u[i][k] * hyp)
                Pq = quot(rest)
                s.append('    · linear_combination (%s) * hw%d%d%s' % (lp(u[i][k]), i + 1, m, hjt(Pq)))
        CVS = 'Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons'
        if D == 5:
            CVS += ', Matrix.cons_val_four'
            # rho: combination of the five relations with zero restriction to S
            Rm = sp.Matrix([[sp.expand(x).coeff(tau[i][k]) for i in range(3) for k in range(3)] for x in R])
            nsr = Rm.T.nullspace()
            assert len(nsr) == 1, 'rho nullspace'
            cvec = [sp.nsimplify(v) for v in nsr[0]]
            Cfull = sp.expand(sum(cvec[r] * ff for r, ff in enumerate([full[0], full[1], full[2], g12full, g13full])))
            coef = [[sp.expand(Cfull.coeff(VS[a][Sc[b]])) for b in range(2)] for a in range(3)]
            for a in range(3):
                for k in range(3):
                    assert sp.expand(Cfull.coeff(VS[a][S[k]])) == 0
            rhol = '![' + ', '.join('![' + ', '.join('(%s) * κ%d %d' % (lp(coef[a][b]), a + 1, Sc[b]) for b in range(2)) + ']' for a in range(3)) + ']'
            a0, b0 = next((a, b) for a in range(3) for b in range(2) if coef[a][b] != 0)
            s.append('  have hρ : (%s : Fin 3 → Fin 2 → ℂ) %d %d ≠ 0 := by' % (rhol, a0, b0))
            s.append('    simp only [%s]' % CVS)
            s.append('    exact mul_ne_zero (by norm_num) (hκ%d %d)' % (a0 + 1, Sc[b0]))
            s.append('  have hrel : ∀ t ∈ L, ∑ a, ∑ b, (%s : Fin 3 → Fin 2 → ℂ) a b * t (rr (Sum.inl a), cc (Sum.inr b)) = 0 := by' % rhol)
            s.append('    intro t ht')
            s.append('    have f1 := hF1 t ht')
            s.append('    have f2 := hF2 t ht')
            s.append('    have f3 := hF3 t ht')
            s.append('    have g1 := hg12 t ht')
            s.append('    have g2 := hg13 t ht')
            s.append('    simp only [dotL_apply, rowMap_apply, Fin.sum_univ_five] at f1 f2 f3')
            s.append('    simp only [Fin.sum_univ_three, Fin.sum_univ_two, %s, hr1, hr2, hr3, hc3, hc4]' % CVS)
            parts = ['(%s) * %s' % (lp(cvec[r]), hn_) for r, hn_ in enumerate(['f1', 'f2', 'f3', 'g1', 'g2']) if cvec[r] != 0]
            s.append('    linear_combination %s' % ' + '.join(parts))
            # hJ
            Ksym = [[sp.Symbol('K%d_%d' % (i, m)) for m in range(5)] for i in range(3)]
            NM.update({Ksym[i][m]: '(κ%d %d)' % (i + 1, m) for i in range(3) for m in range(5)})
            target = sp.expand(sum(coef[a][b] * Ksym[a][Sc[b]] for a in range(3) for b in range(2)))
            hk = [sum(Ksym[i][m] for m in range(5)) - 1 for i in range(3)]
            K12 = sum(Ksym[0][m] for m in B12) + sum(Ksym[1][m] for m in Q12)
            K13 = sum(Ksym[0][m] for m in B13) + sum(Ksym[2][m] for m in Q13)
            hK12 = K12 * (1 + j) - 1
            hK13 = K13 * (1 + eps * j) - 1
            ck = [cvec[0], cvec[1], cvec[2], sp.expand(cvec[3] * (1 - j) / 2), sp.expand(cvec[4] * (1 - eps * j) / 2)]
            rest = sp.expand(target - sum(ck[r] * h_ for r, h_ in enumerate(hk + [hK12, hK13])))
            PJ = quot(rest)
            s.append('  have hJ : ∑ a, ∑ b, (%s : Fin 3 → Fin 2 → ℂ) a b = 0 := by' % rhol)
            s.append('    simp only [Fin.sum_univ_three, Fin.sum_univ_two, %s]' % CVS)
            s.append('    have e1 := hk1')
            s.append('    have e2 := hk2')
            s.append('    have e3 := hk3')
            s.append('    simp only [Fin.sum_univ_five] at e1 e2 e3')
            parts = ['(%s) * %s' % (lp(ck[r]), nm_) for r, nm_ in enumerate(['e1', 'e2', 'e3', 'hK12', 'hK13']) if sp.expand(ck[r]) != 0]
            s.append('    linear_combination %s%s' % (' + '.join(parts) if parts else '0', hjt(PJ)))
            s.append('  have hD := %s j hj %s (bridge5 hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)' % (en, zl))
            s.append('    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU _ %d %d hρ hrel hJ)' % (a0, b0))
        else:
            s.append('  have hD := %s j hj %s (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)' % (en, zl))
            s.append('    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)')
        nb = len(brs)
        if nb == 1:
            s.append('  have h := hD')
        else:
            s.append('  rcases hD with ' + ' | '.join(['h'] * nb))
        for bi, eqs in enumerate(brs):
            if nb == 1:
                prefix, close = '', ''
            elif nb == 2:
                prefix, close = ['Or.inl', 'Or.inr'][bi], ''
            else:
                prefix = ['Or.inl', 'Or.inr (Or.inl', 'Or.inr (Or.inr'][bi]
                close = ['', ')', ')'][bi]
            items = []
            haves = []
            for qi, (a0, b, raw, rd) in enumerate(eqs):
                if a0 is None:
                    haves.append('have q%d := congrFun h %d' % (qi, b))
                    items.append('by linear_combination q%d' % qi)
                else:
                    Pq = quot(rd - raw)
                    haves.append('have q%d := h %d %d' % (qi, a0, b))
                    items.append('by linear_combination q%d%s' % (qi, hjt(Pq)))
            qn = ' '.join('q%d' % qi for qi in range(len(eqs)))
            pre = '  ' if nb == 1 else '    '
            lines = haves + ['simp only [%s, Pi.zero_apply] at %s' % (CVS, qn), 'exact %s %s%s' % (prefix, ('(%s)' % items[0]) if len(items) == 1 else ('⟨%s⟩' % ', '.join(items)), close)]
            if nb == 1:
                s += ['  ' + x for x in lines]
            else:
                s.append('  · ' + lines[0])
                s += ['    ' + x for x in lines[1:]]
        L.append('\n'.join(s) + '\n')
    # DFS lemma
    one = [1] * 5
    q13 = [1 if m in Q13 else 0 for m in range(5)]
    q12 = [1 if m in Q12 else 0 for m in range(5)]
    e3a = '¬ ∃ α β : ℂ, ' + ' ∧ '.join('M3 %d = α + β * %d' % (m, q13[m]) for m in range(5))
    e3b = '¬ ∃ α β : ℂ, ' + ' ∧ '.join('M2 %d = α + β * %d' % (m, q12[m]) for m in range(5))
    s = ['theorem cfg_%s %s\n    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0)\n    (hE3a : %s)\n    (hE3b : %s) : False := by' % (tag, ctx_bind, e3a, e3b)]
    for idx in order:
        s.append('  have D%d := w_%s_%s %s' % (idx, tag, ''.join(map(str, data[idx]['S'])), ctx_args))
    cnt = [0]

    def emit(t, hyps):
        if t[0] == 'e5':
            piv = pforms[K5]
            cnt[0] += 1
            hq = 'hq%d' % cnt[0]
            kind = adm_info(t[1] + [redj(piv)])
            assert kind is not None, 'pivot = 0 not (E3)-inadmissible'
            l0 = emit(('leaf', kind, None), hyps + [(hq, redj(piv))])
            items = []
            for half in (0, 1):
                for k in range(3):
                    c = 5 * half + S5[k]
                    target = sp.expand(MV[c] - sum(pforms[i] * toj(famp[c, i]) for i in range(nf)))
                    if target == 0:
                        items.append('(by ring)')
                        continue
                    lam = solve_comb([h[1] for h in hyps], redj(target))
                    rest = sp.expand(target - sum(lam[i] * hyps[i][1] for i in range(len(hyps))))
                    Pq = quot(rest)
                    parts = ['(%s) * %s' % (lp(lam[i]), hyps[i][0]) for i in range(len(hyps)) if lam[i] != 0]
                    items.append('(by linear_combination %s%s)' % (' + '.join(parts) if parts else '0', hjt(Pq)))
            out_ = ['by_cases %s : %s = 0' % (hq, lp(piv)), '· ' + l0[0]] + ['  ' + x for x in l0[1:]]
            out_.append('· exact e5_%s %s hJn %s %s %s' % (tag, ctx_args, ' '.join('(%s)' % lp(pf) for pf in pforms), ' '.join(items), hq))
            return out_
        if t[0] == 'leaf':
            kind, eqs = t[1], t[2]
            if kind in ('m3', 'zero'):
                Mv, qv, hname = B, q13, 'hE3a'
            else:
                Mv, qv, hname = A, q12, 'hE3b'
            ma = next(m for m in range(5) if qv[m] == 0)
            mq = next(m for m in range(5) if qv[m] == 1)
            alpha = Mv[ma]; beta = Mv[mq] - Mv[ma]
            items = []
            for m in range(5):
                target = sp.expand(Mv[m] - alpha - beta * qv[m])
                if target == 0:
                    items.append('by ring')
                    continue
                lam = solve_comb([h[1] for h in hyps], target)
                rest = sp.expand(target - sum(lam[i] * hyps[i][1] for i in range(len(hyps))))
                Pq = quot(rest)
                parts = ['(%s) * %s' % (lp(lam[i]), hyps[i][0]) for i in range(len(hyps)) if lam[i] != 0]
                items.append('by linear_combination %s%s' % (' + '.join(parts) if parts else '0', hjt(Pq)))
            return ['exact %s ⟨%s, %s, %s⟩' % (hname, lp(alpha), lp(beta), ', '.join(items))]
        _, idx, subs = t
        dd = data[idx]
        pats = []
        names = []
        for bi, eqs in enumerate(dd['brs']):
            nm = []
            for e in eqs:
                cnt[0] += 1
                nm.append('q%d' % cnt[0])
            names.append(nm)
            pats.append('⟨' + ', '.join(nm) + '⟩')
        lines = ['rcases D%d with %s' % (idx, ' | '.join(pats))]
        for bi, sub in enumerate(subs):
            newh = hyps + [(names[bi][q], dd['brs'][bi][q][3]) for q in range(len(names[bi]))]
            sl = emit(sub, newh)
            lines.append('· ' + sl[0])
            lines += ['  ' + x for x in sl[1:]]
        return lines
    s += ['  ' + x for x in emit(tree, [])]
    L.append('\n'.join(s) + '\n')
    # inst lemma: setup outputs (generic f, f13, s) + concrete values -> False via cfg lemma
    fl = '![' + ', '.join(str(x) for x in s12) + ']'
    f13l = '![' + ', '.join(str(x) for x in s13) + ']'
    si = ['theorem inst_%s {L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)' % tag,
          '    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)',
          '    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)',
          '    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)',
          '    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)',
          '    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)',
          '    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧',
          '      (f m = 0 → κ2 m = j * (c2 * κ1 m)))',
          '    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧',
          '      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))',
          '    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +',
          '      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)',
          '    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +',
          '      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)',
          '    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)',
          '    (hE3a : ¬ ∃ α β : ℂ, ∀ m, M3 m = α + β * (if f13 m = 1 then (1 : ℂ) else 0))',
          '    (hE3b : ¬ ∃ b c : ℂ, ∀ m, M2 m = b + c * (if f m = 1 then (1 : ℂ) else 0))',
          '    (hf : ∀ m, f m = (%s : Fin 5 → Fin 3) m) (hf13 : ∀ m, f13 m = (%s : Fin 5 → Fin 3) m)' % (fl, f13l),
          '    (hs : s = %s)%s : False := by' % ('1' if eps == 1 else '-1', ('\n    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)\n'
           '    (hK12 : (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) * (1 + j) = 1)\n'
           '    (hK13 : (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) * (1 + s * j) = 1)\n'
           '    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0)') if need5 else '')]
    # value facts
    for m in range(5):
        si.append('  have fv%d : f %d = %d := by rw [hf %d] <;> rfl' % (m, m, s12[m], m))
        si.append('  have gv%d : f13 %d = %d := by rw [hf13 %d] <;> rfl' % (m, m, s13[m], m))
    for m in range(5):
        for nm, fv, v in (('a', 'fv', 2), ('b', 'fv', 1), ('c', 'gv', 2), ('d', 'gv', 1)):
            fn = 'f' if fv == 'fv' else 'f13'
            val = (s12 if fv == 'fv' else s13)[m]
            si.append('  have i%s%d : (if %s %d = %d then (1 : ℂ) else 0) = %d := by rw [%s%d] <;> rfl' % (nm, m, fn, m, v, 1 if val == v else 0, fv, m))
    si.append('  refine cfg_%s hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj ?_ ?_ hF1 hF2 hF3 ?_ ?_ M2 M3 hn%s ?_ ?_' % (tag, ' hk1 hk2 hk3 ?_ ?_ hJn' if need5 else ''))
    # hw2
    def wcomp(row, m):
        cell = (s12 if row == 2 else s13)[m]
        comp = {1: '.1', 2: '.2.1', 0: '.2.2'}[cell]
        return '(hw%d %d)%s %s' % (row, m, comp, ('fv%d' if row == 2 else 'gv%d') % m)
    for row in (2, 3):
        parts = []
        for m in range(5):
            parts.append('by rw [%s%s] <;> ring' % (wcomp(row, m), ', hs' if (row == 3 and s13[m] == 0) else ''))
        si.append('  · exact ⟨%s⟩' % ', '.join(parts))
    si.append('  · intro t ht')
    si.append('    have e := hG12 t ht')
    si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ia%d, ib%d' % (m, m) for m in range(5)))
    si.append('    linear_combination e')
    si.append('  · intro t ht')
    si.append('    have e := hG13 t ht')
    si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ic%d, id%d' % (m, m) for m in range(5)))
    si.append('    linear_combination e')
    if need5:
        si.append('  · have e := hK12')
        si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ia%d, ib%d' % (m, m) for m in range(5)))
        si.append('    linear_combination e')
        si.append('  · have e := hK13')
        si.append('    simp only [Fin.sum_univ_five, hs, %s] at e' % ', '.join('ic%d, id%d' % (m, m) for m in range(5)))
        si.append('    linear_combination e')
    si.append('  · rintro ⟨α, β, e0, e1, e2, e3, e4⟩')
    si.append('    refine hE3a ⟨α, β, fun m => ?_⟩')
    si.append('    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl')
    for m in range(5):
        si.append('    · rw [id%d]' % m)
        si.append('      exact e%d' % m)
    si.append('  · rintro ⟨b0, c0, e0, e1, e2, e3, e4⟩')
    si.append('    refine hE3b ⟨b0, c0, fun m => ?_⟩')
    si.append('    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl')
    for m in range(5):
        si.append('    · rw [ib%d]' % m)
        si.append('      exact e%d' % m)
    L.append('\n'.join(si) + '\n')
    args = ('L hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3 hw2 hw3 hG12 hG13 hn '
            'hE3a hE3b hf hf13 hs hk1 hk2 hk3 hK12 hK13 hJn')
    L.append('theorem surv_%s : R31Surv (%s : Fin 5 → Fin 3) (%s : Fin 5 → Fin 3) (%s) :=\n  fun %s =>\n    inst_%s %s\n' % (
        tag, fl, f13l, '1' if eps == 1 else '-1', args, tag, args.split(' ', 1)[1]))
    open(out, 'w', encoding='utf-8').write('\n' + '\n'.join(L))
    print('written', out, sum(len(x.encode()) for x in L), 'bytes')


main()
