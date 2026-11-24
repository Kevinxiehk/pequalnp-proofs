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


usable = [i for i in range(len(data)) if data[i]['usable']]
costf = lambda dd: {3: 1, 1: 3, 0: 7}[dd['typ']]
best = None
for ksz in (1, 2, 3, 4):
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
      '    (hs : s = %s) : False := by' % EPS]
for m in range(5):
    si.append('  have fv%d : f %d = %d := by rw [hf %d] <;> rfl' % (m, m, s12[m], m))
    si.append('  have gv%d : f13 %d = %d := by rw [hf13 %d] <;> rfl' % (m, m, s13[m], m))
for m in range(5):
    si.append('  have ib%d : (if f %d = 1 then (1 : ℂ) else 0) = %d := by rw [fv%d] <;> rfl' % (m, m, 1 if s12[m] == 1 else 0, m))
    si.append('  have id%d : (if f13 %d = 1 then (1 : ℂ) else 0) = %d := by rw [gv%d] <;> rfl' % (m, m, 1 if s13[m] == 1 else 0, m))
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


def emit(t, hyps):
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
open(out, 'w', encoding='utf-8').write('\n' + '\n'.join(si) + '\n')
print(tag, 'kept', [data[i]['S'] for i in order], 'bytes', len('\n'.join(si).encode()))
