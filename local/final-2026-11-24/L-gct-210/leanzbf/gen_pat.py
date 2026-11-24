# gen_pat.py OUT [PATTERNS...] : pattern wrappers (bundling). For each d = 4 local pattern (f|S, f13|S, eps) of
# leanzbf/patterns.txt: the E-lemma pe<typ>_<pat> (from the representative instance) and the wrapper pw_<pat>, generic in
# the columns S0 S1 S2 (Lean variables) and stated in the inst-form context (generic f, f13, s, hw2, hw3, hG12, hG13).
# Conclusion: the branch disjunction in M2 S_k, M3 S_k. Pattern name: <f|S>_<f13|S>_<p|m>, e.g. 001_010_m.
import sys, ast, glob, itertools, re
import sympy as sp
sys.path.insert(0, '/home/kevxhk/work/L-gct-210/leanzbf')
_src = open('/home/kevxhk/work/L-gct-210/leanzbf/gen_cfg5.py').read()
exec(_src[:_src.index('\ndef main():')])          # helpers: lp, toI, toj, redj, quot, hjt, solve_comb, A, B, VS, NM ...
from gen_e3 import gq, X, j

OUT = sys.argv[1]
want = set(sys.argv[2:])
rows = [ast.literal_eval(l) for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_export_p*.txt'))
        for l in open(f) if l.strip()]
pats = []
for line in open('/home/kevxhk/work/L-gct-210/leanzbf/patterns.txt'):
    if line.startswith('#'):
        continue
    w = line.split()
    a, b, eps, d, typ = w[0], w[1], int(w[2]), int(w[3][2:]), int(w[4][4:])
    inst = w[6:]
    pats.append((a, b, eps, d, typ, inst))
# Lean names for the generic columns: VS[i][k] -> kappa_i S_k * t (r_i, S_k); A[k] -> M2 S_k; B[k] -> M3 S_k
for k in range(3):
    NM[A[k]] = '(M2 S%d)' % k
    NM[B[k]] = '(M3 S%d)' % k
    for i in range(3):
        NM[VS[i][k]] = '(κ%d S%d * t (r%d, S%d))' % (i + 1, k, i + 1, k)
CV = 'Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons'
CTX = ('{L : Submodule ℂ (Fin 5 × Fin 5 → ℂ)} (hL : Lev 5 L) (h9 : Module.finrank ℂ L = 9)\n'
       '    (r1 r2 r3 : Fin 5) (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)\n'
       '    (hX : rowsZeroS L {r1, r2, r3} = ⊥) (κ1 κ2 κ3 : Fin 5 → ℂ) (hκ1 : ∀ m, κ1 m ≠ 0)\n'
       '    (hκ2 : ∀ m, κ2 m ≠ 0) (hκ3 : ∀ m, κ3 m ≠ 0) (c2 c3 j s : ℂ) (hj : j * j = -1)\n'
       '    (hF1 : ∀ t ∈ L, dotL κ1 (rowMap r1 t) = 0) (hF2 : ∀ t ∈ L, dotL κ2 (rowMap r2 t) = 0)\n'
       '    (hF3 : ∀ t ∈ L, dotL κ3 (rowMap r3 t) = 0) (f f13 : Fin 5 → Fin 3) (M2 M3 : Fin 5 → ℂ)\n'
       '    (hw2 : ∀ m, (f m = 1 → κ2 m = 1 * (c2 * κ1 m)) ∧ (f m = 2 → κ2 m = -1 * (c2 * κ1 m)) ∧\n'
       '      (f m = 0 → κ2 m = j * (c2 * κ1 m)))\n'
       '    (hw3 : ∀ m, (f13 m = 1 → κ3 m = 1 * (c3 * κ1 m)) ∧ (f13 m = 2 → κ3 m = -1 * (c3 * κ1 m)) ∧\n'
       '      (f13 m = 0 → κ3 m = s * j * (c3 * κ1 m)))\n'
       '    (hG12 : ∀ t ∈ L, ∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +\n'
       '      (if f m = 1 then (1 : ℂ) else 0) * κ2 m * t (r2, m)) = 0)\n'
       '    (hG13 : ∀ t ∈ L, ∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m * t (r1, m) +\n'
       '      (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m * t (r3, m)) = 0)\n'
       '    (hn : ∀ t ∈ L, ∑ m, (M2 m * κ2 m * t (r2, m) + M3 m * κ3 m * t (r3, m)) = 0)\n'
       '    (S0 S1 S2 : Fin 5) (hS01 : S0 ≠ S1) (hS02 : S0 ≠ S2) (hS12 : S1 ≠ S2)')
out = []
nmade = 0
for (pa, pb, eps, d, typ, inst) in pats:
    ptag = '%s_%s_%s' % (pa, pb, 'p' if eps == 1 else 'm')
    if d != 4 or (want and ptag not in want):
        continue
    rtag, rS = inst[0].split(':')
    s12 = tuple(int(c) for c in rtag[:5]); s13 = tuple(int(c) for c in rtag[6:11])
    S = tuple(int(c) for c in rS)
    r = next(x for x in rows if x['s12'] == s12 and x['s13'] == s13 and x['eps'] == eps and tuple(x['S']) == S)
    assert r['typ'] == typ and r['d'] == 4
    fa = [int(c) for c in pa]; fb = [int(c) for c in pb]
    assert [s12[m] for m in S] == fa and [s13[m] for m in S] == fb
    E = [[toj(toI(gq(v))) for v in e] for e in r['E']]
    u = [[toj(toI(gq(v))) for v in row] for row in r['u']]
    facs = [[toj(toI(gq(v))) for v in f_] for f_ in r['facs']]
    if typ == 3:
        k0 = toj(toI(gq(r['k'])))
        facs[0] = [redj(k0 * v) for v in facs[0]]
    D = 4
    z = [redj(sum(A[k] * E[e][3 + k] + B[k] * E[e][6 + k] for k in range(3))) for e in range(D)]
    brs = []
    if typ in (0, 1):
        brs.append([(None, e, z[e], z[e]) for e in range(D) if sp.expand(z[e]) != 0])
    for l in facs:
        a0 = next(a for a in range(D) if l[a] != 0)
        eqs = []
        for b in range(D):
            if b != a0:
                raw = sp.expand(l[a0] * z[b] - l[b] * z[a0])
                if redj(raw) != 0:
                    eqs.append((a0, b, raw, redj(raw)))
        brs.append(eqs)
    EEl = '![' + ', '.join('![' + ', '.join('![' + ', '.join(lp(E[e][3 * i + k]) for k in range(3)) + ']' for i in range(3)) + ']' for e in range(D)) + ']'
    UUl = '![' + ', '.join('![' + ', '.join(lp(u[i][k]) for k in range(3)) + ']' for i in range(3)) + ']'
    Ls = ['![' + ', '.join(lp(v) for v in f_) + ']' for f_ in facs]
    en = 'pe%d_%s' % (typ, ptag)
    # E-lemma (renamed from the representative)
    if typ == 3:
        T = [[sp.expand(sum(X[e] * E[e][3 * i + k] for e in range(4)) * u[i][k]) for k in range(3)] for i in range(3)]
        perm = (T[0][0] * T[1][1] * T[2][2] + T[0][0] * T[1][2] * T[2][1] + T[0][1] * T[1][0] * T[2][2] +
                T[0][1] * T[1][2] * T[2][0] + T[0][2] * T[1][0] * T[2][1] + T[0][2] * T[1][1] * T[2][0])
        lin = [sum(f_[e] * X[e] for e in range(4)) for f_ in facs]
        P = quot(perm - lin[0] * lin[1] * lin[2])
        out.append('theorem %s (j : ℂ) (hj : j * j = -1) (z : Fin 4 → ℂ)\n'
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
    else:
        import gen_e0, gen_e1
        txt = gen_e1.gen(r) if typ == 1 else gen_e0.gen(r)
        assert txt is not None
        ls_ = txt.split('\n')
        assert ls_[2].startswith('      (Matrix.of ![')
        suffix = ls_[2][ls_[2].index(').permanent = 0)') + len(').permanent = 0)'):]
        ls_[2] = ('      (Matrix.of fun i k => (∑ e, x e * (%s : Fin %d → Fin 3 → Fin 3 → ℂ) e i k) *\n'
                  '        (%s : Fin 3 → Fin 3 → ℂ) i k).permanent = 0)' % (EEl, D, UUl)) + suffix
        txt = '\n'.join(ls_)
        txt = txt.replace('Matrix.of_apply, Matrix.cons_val_zero,', 'Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,')
        txt = re.sub(r'^(\s*)theorem \S+', r'\1theorem ' + en, txt, count=1, flags=re.M)
        out.append(txt.strip('\n') + '\n')
    # lifting data
    for cand in itertools.combinations(range(9), D):
        Msub = sp.Matrix([[toI(E[e][c]) for e in range(D)] for c in cand])
        if Msub.det() != 0:
            pos = cand; inv = Msub.inv(); break
    PPv = [[0] * 9 for _ in range(D)]
    for e in range(D):
        for fi, c in enumerate(pos):
            PPv[e][c] = toj(sp.nsimplify(sp.expand(inv[e, fi])))
    PPl = '![' + ', '.join('![' + ', '.join('![' + ', '.join(lp(PPv[e][3 * i + k]) for k in range(3)) + ']' for i in range(3)) + ']' for e in range(D)) + ']'
    tau = [[VS[i][k] for k in range(3)] for i in range(3)]
    R = [sum(tau[i][k] for k in range(3)) for i in range(3)]
    R.append(sum(tau[0][k] for k in range(3) if fa[k] == 2) + sum(tau[1][k] for k in range(3) if fa[k] == 1))
    R.append(sum(tau[0][k] for k in range(3) if fb[k] == 2) + sum(tau[2][k] for k in range(3) if fb[k] == 1))
    RN6 = sum(A[k] * tau[1][k] + B[k] * tau[2][k] for k in range(3))
    Pt = [sum(PPv[e][3 * i + k] * tau[i][k] for i in range(3) for k in range(3)) for e in range(D)]
    lift = []
    for i in range(3):
        for k in range(3):
            target = sp.expand(tau[i][k] - sum(Pt[e] * E[e][3 * i + k] for e in range(D)))
            lam = solve_comb([redj(x) for x in R], redj(target))
            rest = sp.expand(target - sum(lam[q] * R[q] for q in range(5)))
            lift.append((lam, quot(rest)))
    target = sp.expand(sum(z[e] * Pt[e] for e in range(D)))
    lamz = [0] * 5
    for i in range(3):
        for k in range(3):
            cN = sp.expand(RN6).coeff(tau[i][k])
            if cN != 0:
                lam, _ = lift[3 * i + k]
                for q in range(5):
                    lamz[q] = sp.expand(lamz[q] - cN * lam[q])
    rest = sp.expand(target - RN6 - sum(lamz[q] * R[q] for q in range(5)))
    Pz = quot(rest)
    # --- wrapper text
    brl = ['(' + ' ∧ '.join('%s = 0' % lp(e[3]) for e in eqs) + ')' for eqs in brs]
    EPS = '1' if eps == 1 else '-1'
    s = []
    s.append('theorem pw_%s %s\n    (ha0 : f S0 = %d) (ha1 : f S1 = %d) (ha2 : f S2 = %d) (hb0 : f13 S0 = %d) (hb1 : f13 S1 = %d)\n'
             '    (hb2 : f13 S2 = %d) (hs : s = %s) :' % (ptag, CTX, fa[0], fa[1], fa[2], fb[0], fb[1], fb[2], EPS))
    s.append('    ' + ' ∨\n      '.join(brl) + ' := by')
    s.append('  obtain ⟨rr, hr1, hr2, hr3⟩ := exists_equiv3 r1 r2 r3 h12 h13 h23')
    s.append('  obtain ⟨cc, hc0, hc1, hc2⟩ := exists_equiv3 S0 S1 S2 hS01 hS02 hS12')
    comp = {1: '.1', 2: '.2.1', 0: '.2.2'}
    wtx = {1: '1', 2: '(-1)', 0: 'j'}
    for k in range(3):
        s.append('  have hw2_%d : κ2 S%d = %s * (c2 * κ1 S%d) := by rw [(hw2 S%d)%s ha%d] <;> ring' % (k, k, wtx[fa[k]], k, k, comp[fa[k]], k))
    for k in range(3):
        w3t = {1: '1', 2: '(-1)', 0: ('j' if eps == 1 else '(-1) * j')}[fb[k]]
        s.append('  have hw3_%d : κ3 S%d = %s * (c3 * κ1 S%d) := by rw [(hw3 S%d)%s hb%d%s] <;> ring' % (
            k, k, w3t, k, k, comp[fb[k]], k, ', hs' if fb[k] == 0 else ''))
    for k in range(3):
        for nm, fn, v, val in (('ia', 'f', 2, fa[k]), ('ib', 'f', 1, fa[k]), ('ic', 'f13', 2, fb[k]), ('id', 'f13', 1, fb[k])):
            s.append('  have %s%d : (if %s (cc (Sum.inl %d)) = %d then (1 : ℂ) else 0) = %d := by rw [hc%d, h%s%d] <;> rfl' % (
                nm, k, fn, k, v, 1 if val == v else 0, k, 'a' if fn == 'f' else 'b', k))
    s.append('  have rel : ∀ t ∈ blkL L rr cc, %s := by' % ' ∧ '.join('%s = 0' % lp(x) for x in R + [RN6]))
    s.append('    intro t ht')
    for i in range(3):
        s.append('    have e%d := rel_blk1 rr cc %d r%d hr%d κ%d (fun t ht => by simpa only [dotL_apply, rowMap_apply, mul_comm] using hF%d t ht) t ht' % (i + 1, i, i + 1, i + 1, i + 1, i + 1))
    s.append('    have e4 := rel_blk2 rr cc 0 1 r1 r2 hr1 hr2 (fun m => (if f m = 2 then (1 : ℂ) else 0) * κ1 m)')
    s.append('      (fun m => (if f m = 1 then (1 : ℂ) else 0) * κ2 m) hG12 t ht')
    s.append('    have e5 := rel_blk2 rr cc 0 2 r1 r3 hr1 hr3 (fun m => (if f13 m = 2 then (1 : ℂ) else 0) * κ1 m)')
    s.append('      (fun m => (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m) hG13 t ht')
    s.append('    have e6 := rel_blk2 rr cc 1 2 r2 r3 hr2 hr3 (fun m => M2 m * κ2 m) (fun m => M3 m * κ3 m) hn t ht')
    s.append('    simp only [Fin.sum_univ_three] at e1 e2 e3 e4 e5 e6')
    s.append('    simp only [ia0, ia1, ia2, ib0, ib1, ib2] at e4')
    s.append('    simp only [ic0, ic1, ic2, id0, id1, id2] at e5')
    s.append('    simp only [hc0, hc1, hc2] at e1 e2 e3 e4 e5 e6')
    s.append('    exact ⟨by linear_combination e1, by linear_combination e2, by linear_combination e3, by linear_combination e4,')
    s.append('      by linear_combination e5, by linear_combination e6⟩')
    s.append("  have hlift : ∀ t ∈ blkL L rr cc, ∀ i k, tauMap ![κ1, κ2, κ3] rr cc t i k =")
    s.append("      ∑ e, (∑ i', ∑ k', (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') *" % PPl)
    s.append('        (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i k := by' % EEl)
    s.append('    intro t ht i k')
    s.append('    obtain ⟨R1, R2, R3, R4, R5, _⟩ := rel t ht')
    s.append('    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>')
    s.append('      simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, %s, hr1, hr2, hr3, hc0, hc1, hc2]' % CV)
    for (lam, Pq) in lift:
        parts = ['(%s) * R%d' % (lp(lam[q]), q + 1) for q in range(5) if lam[q] != 0]
        s.append('    · linear_combination %s%s' % (' + '.join(parts) if parts else '0', hjt(Pq)))
    zl = '![' + ', '.join(lp(x) for x in z) + ']'
    s.append('  have hzk : ∀ t ∈ blkL L rr cc, ∑ e, (%s : Fin 4 → ℂ) e *' % zl)
    s.append("      (∑ i', ∑ k', (%s : Fin 4 → Fin 3 → Fin 3 → ℂ) e i' k' * tauMap ![κ1, κ2, κ3] rr cc t i' k') = 0 := by" % PPl)
    s.append('    intro t ht')
    s.append('    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := rel t ht')
    s.append('    simp only [tauMap_apply, Fin.sum_univ_four, Fin.sum_univ_three, %s, hr1, hr2, hr3, hc0, hc1, hc2]' % CV)
    parts = ['R6'] + ['(%s) * R%d' % (lp(lamz[q]), q + 1) for q in range(5) if lamz[q] != 0]
    s.append('    linear_combination %s%s' % (' + '.join(parts), hjt(Pz)))
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
    kap = [[sp.Symbol('KS%d_%d' % (i, k)) for k in range(3)] for i in range(3)]
    NM.update({kap[i][k]: '(κ%d S%d)' % (i + 1, k) for i in range(3) for k in range(3)})
    cS = [1, sp.Symbol('c2'), sp.Symbol('c3')]
    NM.update({cS[1]: 'c2', cS[2]: 'c3'})
    W2 = [{1: 1, 2: -1, 0: j}[fa[k]] for k in range(3)]
    W3 = [{1: 1, 2: -1, 0: eps * j}[fb[k]] for k in range(3)]
    for i in range(3):
        for k in range(3):
            if i == 0:
                s.append('    · ring')
                continue
            wv = (W2 if i == 1 else W3)[k]
            goal = kap[i][k] * u[i][k] - cS[i] * kap[0][k]
            hyp = kap[i][k] - wv * (cS[i] * kap[0][k])
            rest = sp.expand(goal - u[i][k] * hyp)
            Pq = quot(rest)
            s.append('    · linear_combination (%s) * hw%d_%d%s' % (lp(u[i][k]), i + 1, k, hjt(Pq)))
    s.append('  have hD := %s j hj %s (bridge hL h9 rr cc (h0_of_X123 rr cc r1 r2 r3 hr1 hr2 hr3 hX)' % (en, zl))
    s.append('    ![κ1, κ2, κ3] hκs _ _ _ hlift hzk _ ![1, c2, c3] hU)')
    nb = len(brs)
    s.append('  have h := hD' if nb == 1 else '  rcases hD with ' + ' | '.join(['h'] * nb))
    for bi, eqs in enumerate(brs):
        if nb == 1:
            prefix, close = '', ''
        elif nb == 2:
            prefix, close = ['Or.inl', 'Or.inr'][bi], ''
        else:
            prefix = ['Or.inl', 'Or.inr (Or.inl', 'Or.inr (Or.inr'][bi]
            close = ['', ')', ')'][bi]
        items, haves = [], []
        for qi, (a0, b, raw, rd) in enumerate(eqs):
            if a0 is None:
                haves.append('have q%d := congrFun h %d' % (qi, b))
                items.append('by linear_combination q%d' % qi)
            else:
                Pq = quot(rd - raw)
                haves.append('have q%d := h %d %d' % (qi, a0, b))
                items.append('by linear_combination q%d%s' % (qi, hjt(Pq)))
        qn = ' '.join('q%d' % qi for qi in range(len(eqs)))
        lines = haves + ['simp only [%s, Pi.zero_apply] at %s' % (CV, qn), 'exact %s %s%s' % (prefix, ('(%s)' % items[0]) if len(items) == 1 else ('⟨%s⟩' % ', '.join(items)), close)]
        if nb == 1:
            s += ['  ' + x for x in lines]
        else:
            s.append('  · ' + lines[0])
            s += ['    ' + x for x in lines[1:]]
    out.append('\n'.join(s) + '\n')
    nmade += 1
    print(ptag, 'typ', typ, 'rep', inst[0], 'n', len(inst), file=sys.stderr)
open(OUT, 'w').write('\n' + '\n'.join(out))
print('patterns', nmade, 'bytes', sum(len(x.encode()) for x in out))
