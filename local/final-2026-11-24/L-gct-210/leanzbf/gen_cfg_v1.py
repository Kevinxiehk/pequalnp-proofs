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
            brs.append([(None, e, dd['z'][e], dd['z'][e]) for e in range(4)])
        for l in dd['facs']:
            a0 = next(a for a in range(4) if l[a] != 0)
            eqs = []
            for b in range(4):
                if b != a0:
                    raw = sp.expand(l[a0] * dd['z'][b] - l[b] * dd['z'][a0])
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

    order = list(range(len(data)))
    assert run(order) is not None, 'not killed with all d = 4 triples'
    for i in sorted(order, key=lambda i: {0: 0, 1: 1, 3: 2}[data[i]['typ']]):
        trial = [x for x in order if x != i]
        if run(trial) is not None:
            order = trial
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
    for idx in order:
        dd = data[idx]
        S = dd['S']; E = dd['E']; u = dd['u']; facs = dd['facs']; z = dd['z']
        Sc = [m for m in range(5) if m not in S]
        st = ''.join(map(str, S))
        EEl = '![' + ', '.join('![' + ', '.join('![' + ', '.join(lp(E[e][3 * i + k]) for k in range(3)) + ']' for i in range(3)) + ']' for e in range(4)) + ']'
        UUl = '![' + ', '.join('![' + ', '.join(lp(u[i][k]) for k in range(3)) + ']' for i in range(3)) + ']'
        Ls = ['![' + ', '.join(lp(v) for v in f) + ']' for f in facs]
        # E-lemma
        T = [[sp.expand(sum(X[e] * E[e][3 * i + k] for e in range(4)) * u[i][k]) for k in range(3)] for i in range(3)]
        perm = (T[0][0] * T[1][1] * T[2][2] + T[0][0] * T[1][2] * T[2][1] + T[0][1] * T[1][0] * T[2][2] +
                T[0][1] * T[1][2] * T[2][0] + T[0][2] * T[1][0] * T[2][1] + T[0][2] * T[1][1] * T[2][0])
        lin = [sum(f[e] * X[e] for e in range(4)) for f in facs]
        P = quot(perm - lin[0] * lin[1] * lin[2]) if dd['typ'] == 3 else 0
        en = 'e%d_%s_%s' % (dd['typ'], tag, st)
        hEU = ('      (Matrix.of fun i k => (∑ e, x e * (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k) *\n'
               '        (%s : Fin 3 → Fin 3 → ℂ) i k).permanent = 0)' % (EEl, UUl))
        if dd['typ'] in (0, 1):
            import gen_e0, gen_e1
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
        for cand in itertools.combinations(range(9), 4):
            Msub = sp.Matrix([[toI(E[e][c]) for e in range(4)] for c in cand])
            if Msub.det() != 0:
                pos = cand; inv = Msub.inv(); break
        PPv = [[0] * 9 for _ in range(4)]
        for e in range(4):
            for fi, c in enumerate(pos):
                PPv[e][c] = toj(sp.nsimplify(sp.expand(inv[e, fi])))
        PPl = '![' + ', '.join('![' + ', '.join('![' + ', '.join(lp(PPv[e][3 * i + k]) for k in range(3)) + ']' for i in range(3)) + ']' for e in range(4)) + ']'
        tau = [[VS[i][S[k]] for k in range(3)] for i in range(3)]
        # restricted relations (in V on S)
        R = [sum(tau[i][k] for k in range(3)) for i in range(3)]
        R.append(sum(tau[0][k] for k in range(3) if S[k] in B12) + sum(tau[1][k] for k in range(3) if S[k] in Q12))
        R.append(sum(tau[0][k] for k in range(3) if S[k] in B13) + sum(tau[2][k] for k in range(3) if S[k] in Q13))
        RN6 = sum(A[S[k]] * tau[1][k] + B[S[k]] * tau[2][k] for k in range(3))
        Pt = [sum(PPv[e][3 * i + k] * tau[i][k] for i in range(3) for k in range(3)) for e in range(4)]
        # hlift certificates
        lift = []
        for i in range(3):
            for k in range(3):
                target = sp.expand(tau[i][k] - sum(Pt[e] * E[e][3 * i + k] for e in range(4)))
                lam = solve_comb([redj(x) for x in R], redj(target))
                rest = sp.expand(target - sum(lam[r] * R[r] for r in range(5)))
                lift.append((lam, quot(rest)))
        # hzk certificate: target = sum z_e Pt_e ; = RN6 - sum_pos N_pos (tau - E P tau)_pos
        target = sp.expand(sum(z[e] * Pt[e] for e in range(4)))
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
        s.append('  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 %d %d %d (by decide) (by decide) (by decide)' % S)
        s.append('  obtain ⟨hw20, hw21, hw22, hw23, hw24⟩ := hw2')
        s.append('  obtain ⟨hw30, hw31, hw32, hw33, hw34⟩ := hw3')
        s.append('  have rel : ∀ t ∈ blkL L rr cc, %s := by' % ' ∧ '.join('%s = 0' % lp(x) for x in R + [RN6]))
        s.append('    intro t ht')
        s.append('    have htL := ((mem_blkL L rr cc t).mp ht).1')
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
        s.append('      ∑ e, (∑ i\', ∑ k\', (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i\' k\' * tauMap ![κ1, κ2, κ3] rr cc t i\' k\') *' % PPl)
        s.append('        (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by' % EEl)
        s.append('    intro t ht i k')
        s.append('    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht')
        s.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>')
        s.append('      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,')
        s.append('        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]')
        for (lam, Pq) in lift:
            parts = ['(%s) * R%d' % (lp(lam[r]), r + 1) for r in range(5) if lam[r] != 0] + ['(%s) * hj' % lp(Pq)]
            s.append('    · linear_combination %s' % ' + '.join(parts))
        # hzk
        zl = '![' + ', '.join(lp(x) for x in z) + ']'
        s.append('  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (%s : Fin 4 → ℂ) e *' % zl)
        s.append('      (∑ i\', ∑ k\', (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i\' k\' * tauMap ![κ1, κ2, κ3] rr cc t i\' k\') = 0 := by' % PPl)
        s.append('    intro t ht')
        s.append('    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht')
        s.append('    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,')
        s.append('      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hr1, hr2, hr3, hc0, hc1, hc2]')
        parts = ['R6'] + ['(%s) * R%d' % (lp(lamz[r]), r + 1) for r in range(5) if lamz[r] != 0] + ['(%s) * hj' % lp(Pz)]
        s.append('    linear_combination %s' % ' + '.join(parts))
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
                s.append('    · linear_combination (%s) * hw%d%d + (%s) * hj' % (lp(u[i][k]), i + 1, m, lp(Pq)))
        s.append('  have hD := %s j hj %s (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)' % (en, zl))
        s.append('    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)')
        CVS = 'Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons'
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
            for (a0, b, raw, rd) in eqs:
                if a0 is None:
                    items.append('by have q := congrFun h %d; simp only [%s, Pi.zero_apply] at q; linear_combination q' % (b, CVS))
                else:
                    Pq = quot(rd - raw)
                    items.append('by have q := h %d %d; simp only [%s] at q; linear_combination q + (%s) * hj' % (a0, b, CVS, lp(Pq)))
            if nb == 1:
                s.append('  exact ⟨%s⟩' % ', '.join(items))
            else:
                s.append('  · exact %s ⟨%s⟩%s' % (prefix, ', '.join(items), close))
        L.append('\n'.join(s) + '\n')
    # DFS lemma
    one = [1] * 5
    q13 = [1 if m in Q13 else 0 for m in range(5)]
    q12 = [1 if m in Q12 else 0 for m in range(5)]
    e3a = '¬ ∃ α β : ℂ, ' + ' ∧ '.join('M3 %d = α + β * %d' % (m, q13[m]) for m in range(5))
    e3b = '¬ ∃ α β : ℂ, ' + ' ∧ '.join('M2 %d = α + β * %d' % (m, q12[m]) for m in range(5))
    s = ['theorem cfg_%s %s\n    (hE3a : %s)\n    (hE3b : %s) : False := by' % (tag, ctx_bind, e3a, e3b)]
    for idx in order:
        s.append('  have D%d := w_%s_%s %s' % (idx, tag, ''.join(map(str, data[idx]['S'])), ctx_args))
    cnt = [0]

    def emit(t, hyps):
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
                parts = ['(%s) * %s' % (lp(lam[i]), hyps[i][0]) for i in range(len(hyps)) if lam[i] != 0] + ['(%s) * hj' % lp(Pq)]
                items.append('by linear_combination %s' % ' + '.join(parts))
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
          '    (hs : s = %s) : False := by' % ('1' if eps == 1 else '-1')]
    # value facts
    for m in range(5):
        si.append('  have fv%d : f %d = %d := by rw [hf %d] <;> rfl' % (m, m, s12[m], m))
        si.append('  have gv%d : f13 %d = %d := by rw [hf13 %d] <;> rfl' % (m, m, s13[m], m))
    for m in range(5):
        for nm, fv, v in (('a', 'fv', 2), ('b', 'fv', 1), ('c', 'gv', 2), ('d', 'gv', 1)):
            fn = 'f' if fv == 'fv' else 'f13'
            val = (s12 if fv == 'fv' else s13)[m]
            si.append('  have i%s%d : (if %s %d = %d then (1 : ℂ) else 0) = %d := by rw [%s%d] <;> rfl' % (nm, m, fn, m, v, 1 if val == v else 0, fv, m))
    si.append('  refine cfg_%s hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj ?_ ?_ hF1 hF2 hF3 ?_ ?_ M2 M3 hn ?_ ?_' % tag)
    # hw2
    def wcomp(row, m):
        cell = (s12 if row == 2 else s13)[m]
        comp = {1: '.1', 2: '.2.1', 0: '.2.2'}[cell]
        return '(hw%d %d)%s %s' % (row, m, comp, ('fv%d' if row == 2 else 'gv%d') % m)
    for row in (2, 3):
        parts = []
        for m in range(5):
            parts.append('by rw [%s]%s <;> ring' % (wcomp(row, m), ', hs' if (row == 3 and s13[m] == 0) else ''))
        si.append('  · exact ⟨%s⟩' % ', '.join(parts))
    si.append('  · intro t ht')
    si.append('    have e := hG12 t ht')
    si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ia%d, ib%d' % (m, m) for m in range(5)))
    si.append('    linear_combination e')
    si.append('  · intro t ht')
    si.append('    have e := hG13 t ht')
    si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ic%d, id%d' % (m, m) for m in range(5)))
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
    open(out, 'w', encoding='utf-8').write('\n' + '\n'.join(L))
    print('written', out, sum(len(x.encode()) for x in L), 'bytes')


main()
