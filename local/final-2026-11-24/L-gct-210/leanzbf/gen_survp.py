# gen_survp.py: survivor version of gen_cfgp.py (bundled inst_<tag> + surv_<tag>; surviving leaves -> e5_<tag>).
# gen_cfgp.py s12 s13 eps OUT : bundled version of one killed R3-1 configuration. Emits ONLY inst_<tag> (same name and
# signature as gen_cfg5's inst lemma, so the dispatch r12_1 is unchanged); its body calls the shared pattern wrappers
# pw_<pat> (gen_pat.py) for the kept column triples and runs the DFS. Configurations whose minimal subset needs a d = 5
# triple are refused (exit 3): keep gen_cfg5 for those.
import sys, ast, glob, itertools
import sympy as sp
sys.path.insert(0, '/home/kevxhk/work/L-gct-210/leanzbf')
_src = open('/home/kevxhk/work/L-gct-210/leanzbf/gen_cfg5.py').read()
exec(_src[:_src.index('\ndef main():')])
from gen_e3 import gq, j

s12 = tuple(int(c) for c in sys.argv[1]); s13 = tuple(int(c) for c in sys.argv[2]); eps = int(sys.argv[3]); out = sys.argv[4]
tag = '%s_%s_%s' % (sys.argv[1], sys.argv[2], 'p' if eps == 1 else 'm')
rows = [ast.literal_eval(l) for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_export_p*.txt'))
        for l in open(f) if l.strip()]
pat = {}
for line in open('/home/kevxhk/work/L-gct-210/leanzbf/patterns.txt'):
    if not line.startswith('#'):
        w = line.split()
        pat[(w[0], w[1], int(w[2]))] = w[6].split(':')
Q12 = [m for m in range(5) if s12[m] == 1]; Q13 = [m for m in range(5) if s13[m] == 1]
data = []
for r in rows:
    if r['s12'] != s12 or r['s13'] != s13 or r['eps'] != eps:
        continue
    if not ((r['typ'] in (0, 1, 3) and r['d'] == 4) or (r['typ'] == 1 and r['d'] == 5)):
        continue
    S = tuple(r['S'])
    key = (''.join(str(s12[m]) for m in S), ''.join(str(s13[m]) for m in S), eps)
    if r['d'] == 5 or key not in pat:
        data.append(dict(S=S, d=r['d'], typ=r['typ'], usable=False))
        continue
    rtag, rS = pat[key]
    rr_ = next(x for x in rows if ''.join(map(str, x['s12'])) == rtag[:5] and ''.join(map(str, x['s13'])) == rtag[6:11]
               and x['eps'] == eps and ''.join(map(str, x['S'])) == rS)
    E = [[toj(toI(gq(v))) for v in e] for e in rr_['E']]
    facs = [[toj(toI(gq(v))) for v in f_] for f_ in rr_['facs']]
    if rr_['typ'] == 3:
        k0 = toj(toI(gq(rr_['k'])))
        facs[0] = [redj(k0 * v) for v in facs[0]]
    z = [redj(sum(A[S[k]] * E[e][3 + k] + B[S[k]] * E[e][6 + k] for k in range(3))) for e in range(4)]
    brs = []
    if rr_['typ'] in (0, 1):
        brs.append([(None, e, z[e], z[e]) for e in range(4) if sp.expand(z[e]) != 0])
    for l in facs:
        a0 = next(a for a in range(4) if l[a] != 0)
        eqs = []
        for b in range(4):
            if b != a0:
                raw = sp.expand(l[a0] * z[b] - l[b] * z[a0])
                if redj(raw) != 0:
                    eqs.append((a0, b, raw, redj(raw)))
        brs.append(eqs)
    data.append(dict(S=S, d=4, typ=rr_['typ'], usable=True, brs=brs, pname='pw_%s_%s_%s' % (key[0], key[1], 'p' if eps == 1 else 'm')))


B12 = [m for m in range(5) if s12[m] == 2]; B13 = [m for m in range(5) if s13[m] == 2]
import re as _re
_txt = open('/home/kevxhk/work/L-gct-210/leanzbf/surv_families.txt').read()
_blk = _txt.split('== %s %s %d' % (sys.argv[1], sys.argv[2], eps))[1].split('==')[0]
fam = [sp.sympify(l.strip()) for l in _blk.splitlines() if l.strip().startswith('[')]
nf = len(fam)
Vmax = sp.Matrix([[fam[i][c] for i in range(nf)] for c in range(10)])
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
    Mx = sp.Matrix([[sp.expand(toI(e)).coeff(v) for v in MV] for e in eqs])
    return Mx.nullspace()


def inspan(vecs, base):
    Bm = sp.Matrix(base).T
    r0 = Bm.rank()
    return all(sp.Matrix.hstack(Bm, v).rank() == r0 for v in vecs)


q13 = [1 if m in Q13 else 0 for m in range(5)]
q12 = [1 if m in Q12 else 0 for m in range(5)]


def adm_info(eqs):
    V = null(eqs)
    if not V:
        return 'zero'
    if inspan([sp.Matrix(list(v[5:10])) for v in V], [[1] * 5, q13]):
        return 'm3'
    if inspan([sp.Matrix(list(v[0:5])) for v in V], [[1] * 5, q12]):
        return 'm2'
    return None


def run(order):
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


usable = [i for i in range(len(data)) if data[i]['usable']]
costf = lambda dd: {3: 1, 1: 3, 0: 7}[dd['typ']]
best = None
for ksz in range(1, len(usable) + 1):
    for sub in itertools.combinations(usable, ksz):
        c = sum(costf(data[i]) for i in sub)
        if best is not None and c >= best[0]:
            continue
        if run(list(sub)) is not None:
            best = (c, list(sub))
    if best is not None:
        break
if best is None:
    print(tag, 'REFUSED (needs a d = 5 triple or > 4 triples)')
    sys.exit(3)
order = best[1]
tree = run(order)
fl = '![' + ', '.join(str(x) for x in s12) + ']'
f13l = '![' + ', '.join(str(x) for x in s13) + ']'
EPS = '1' if eps == 1 else '-1'
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
      '    (hs : s = %s)' % EPS,
      '    (hk1 : ∑ m, κ1 m = 1) (hk2 : ∑ m, κ2 m = 1) (hk3 : ∑ m, κ3 m = 1)',
      '    (hK12 : (∑ m, ((if f m = 2 then (1 : ℂ) else 0) * κ1 m + (if f m = 1 then (1 : ℂ) else 0) * κ2 m)) * (1 + j) = 1)',
      '    (hK13 : (∑ m, ((if f13 m = 2 then (1 : ℂ) else 0) * κ1 m + (if f13 m = 1 then (1 : ℂ) else 0) * κ3 m)) * (1 + s * j) = 1)',
      '    (hJn : ∑ m, (M2 m * κ2 m + M3 m * κ3 m) = 0) : False := by']
for m in range(5):
    si.append('  have fv%d : f %d = %d := by rw [hf %d] <;> rfl' % (m, m, s12[m], m))
    si.append('  have gv%d : f13 %d = %d := by rw [hf13 %d] <;> rfl' % (m, m, s13[m], m))
for m in range(5):
    si.append('  have ib%d : (if f %d = 1 then (1 : ℂ) else 0) = %d := by rw [fv%d] <;> rfl' % (m, m, 1 if s12[m] == 1 else 0, m))
    si.append('  have id%d : (if f13 %d = 1 then (1 : ℂ) else 0) = %d := by rw [gv%d] <;> rfl' % (m, m, 1 if s13[m] == 1 else 0, m))
for m in range(5):
    si.append('  have ia%d : (if f %d = 2 then (1 : ℂ) else 0) = %d := by rw [fv%d] <;> rfl' % (m, m, 1 if s12[m] == 2 else 0, m))
    si.append('  have ic%d : (if f13 %d = 2 then (1 : ℂ) else 0) = %d := by rw [gv%d] <;> rfl' % (m, m, 1 if s13[m] == 2 else 0, m))
WT = {1: '1', 2: '(-1)', 0: 'j'}
hw2x = ' ∧ '.join('κ2 %d = %s * (c2 * κ1 %d)' % (m, WT[s12[m]], m) for m in range(5))
hw3x = ' ∧ '.join('κ3 %d = %s * (c3 * κ1 %d)' % (m, {1: '1', 2: '(-1)', 0: ('j' if eps == 1 else '(-1) * j')}[s13[m]], m) for m in range(5))
CMP = {1: '.1', 2: '.2.1', 0: '.2.2'}
si.append('  have hw2x : %s :=' % hw2x)
si.append('    ⟨%s⟩' % ', '.join('by rw [(hw2 %d)%s fv%d] <;> ring' % (m, CMP[s12[m]], m) for m in range(5)))
si.append('  have hw3x : %s :=' % hw3x)
si.append('    ⟨%s⟩' % ', '.join('by rw [(hw3 %d)%s gv%d%s] <;> ring' % (m, CMP[s13[m]], m, ', hs' if s13[m] == 0 else '') for m in range(5)))
g12 = ' + '.join(['κ1 %d * t (r1, %d)' % (m, m) for m in B12] + ['κ2 %d * t (r2, %d)' % (m, m) for m in Q12]) + ' = 0'
g13 = ' + '.join(['κ1 %d * t (r1, %d)' % (m, m) for m in B13] + ['κ3 %d * t (r3, %d)' % (m, m) for m in Q13]) + ' = 0'
si.append('  have hg12x : ∀ t ∈ L, %s := by' % g12)
si.append('    intro t ht')
si.append('    have e := hG12 t ht')
si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ia%d, ib%d' % (m, m) for m in range(5)))
si.append('    linear_combination e')
si.append('  have hg13x : ∀ t ∈ L, %s := by' % g13)
si.append('    intro t ht')
si.append('    have e := hG13 t ht')
si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ic%d, id%d' % (m, m) for m in range(5)))
si.append('    linear_combination e')
K12txt = ' + '.join(['κ1 %d' % m for m in B12] + ['κ2 %d' % m for m in Q12])
K13txt = ' + '.join(['κ1 %d' % m for m in B13] + ['κ3 %d' % m for m in Q13])
si.append('  have hK12x : (%s) * (1 + j) = 1 := by' % K12txt)
si.append('    have e := hK12')
si.append('    simp only [Fin.sum_univ_five, %s] at e' % ', '.join('ia%d, ib%d' % (m, m) for m in range(5)))
si.append('    linear_combination e')
si.append('  have hK13x : (%s) * (1 + %s * j) = 1 := by' % (K13txt, '1' if eps == 1 else '(-1)'))
si.append('    have e := hK13')
si.append('    simp only [Fin.sum_univ_five, hs, %s] at e' % ', '.join('ic%d, id%d' % (m, m) for m in range(5)))
si.append('    linear_combination e')
e3a = '¬ ∃ α β : ℂ, ' + ' ∧ '.join('M3 %d = α + β * %d' % (m, q13[m]) for m in range(5))
e3b = '¬ ∃ α β : ℂ, ' + ' ∧ '.join('M2 %d = α + β * %d' % (m, q12[m]) for m in range(5))
for nm, typ_, src, ind in (('hE3a\'', e3a, 'hE3a', 'id'), ('hE3b\'', e3b, 'hE3b', 'ib')):
    si.append('  have %s : %s := by' % (nm, typ_))
    si.append('    rintro ⟨α, β, e0, e1, e2, e3, e4⟩')
    si.append('    refine %s ⟨α, β, fun m => ?_⟩' % src)
    si.append('    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl')
    for m in range(5):
        si.append('    · rw [%s%d]' % (ind, m))
        si.append('      exact e%d' % m)
for idx in order:
    S = data[idx]['S']
    si.append('  have D%d := %s hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3' % (idx, data[idx]['pname']))
    si.append('    hw2 hw3 hG12 hG13 hn %d %d %d (by decide) (by decide) (by decide) fv%d fv%d fv%d gv%d gv%d gv%d hs' % (S + S + S))
cnt = [0]


CTXARGS = 'hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j hj hw2x hw3x hF1 hF2 hF3 hg12x hg13x M2 M3 hn hk1 hk2 hk3 hK12x hK13x'


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
        out_.append('· exact e5_%s %s hJn %s %s %s' % (tag, CTXARGS, ' '.join('(%s)' % lp(pf) for pf in pforms), ' '.join(items), hq))
        return out_
    if t[0] == 'leaf':
        kind = t[1]
        if kind in ('m3', 'zero'):
            Mv, qv, hname = B, q13, "hE3a'"
        else:
            Mv, qv, hname = A, q12, "hE3b'"
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
    pats, names = [], []
    for eqs in dd['brs']:
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


si += ['  ' + x for x in emit(tree, [])]
args = ('L hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3 hw2 hw3 hG12 hG13 hn '
        'hE3a hE3b hf hf13 hs hk1 hk2 hk3 hK12 hK13 hJn')
si.append('')
si.append('theorem surv_%s : R31Surv (%s : Fin 5 → Fin 3) (%s : Fin 5 → Fin 3) (%s) :=\n  fun %s =>\n    inst_%s %s' % (
    tag, fl, f13l, '1' if eps == 1 else '-1', args, tag, args.split(' ', 1)[1]))
open(out, 'w', encoding='utf-8').write('\n' + '\n'.join(si) + '\n')
print(tag, 'kept', [data[i]['S'] for i in order], 'bytes', len('\n'.join(si).encode()))
