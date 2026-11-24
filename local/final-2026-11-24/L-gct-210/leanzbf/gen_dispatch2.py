# gen_dispatch2.py MODE OUT [available-tags-file]: the proof of R31CfgAll by case split
# (canon_patterns x f13_cases_P x sign), leaves = inst_<tag> (killed) / e5_<tag> (survivor) / sorry (MODE shape).
import sys, itertools, ast, glob
mode, out = sys.argv[1], sys.argv[2]
avail = set(open(sys.argv[3]).read().split()) if len(sys.argv) > 3 else None
pats = [(0, 0, 0, 1, 2), (0, 0, 1, 1, 2), (0, 1, 1, 1, 2), (0, 0, 1, 2, 2), (0, 1, 1, 2, 2), (0, 1, 2, 2, 2)]
surv = set()
for f in glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_dump_p*.log'):
    for line in open(f):
        if 'survivor' in line:
            t = ast.literal_eval(line.split('survivor', 1)[1].strip())
            surv.add((t[0], t[1], t[2]))
D5 = set()
import os
for f in glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/%s/*.txt' % os.environ.get('CFGDIR', 'cfg_out')):
    txt = open(f, encoding='utf-8').read()
    i = txt.find('theorem inst_')
    if i >= 0 and '(hK13 :' in txt[i:i + 4000]:
        b = f.split('/')[-1][:-4].split('_')
        D5.add((tuple(int(c) for c in b[0]), tuple(int(c) for c in b[1]), 1 if b[2] == 'p' else -1))
print('configurations with K arguments:', len(D5))
args = ('hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hF1 hF2 hF3 f f13 M2 M3 hw2 hw3 '
        'hG12 hG13 hn hE3a hE3b hf hf13 hs')
def disj(items):
    if len(items) == 1:
        return items[0]
    return items[0] + ' | ' + disj(items[1:])
def orpath(i, n):
    s = ''
    for _ in range(i):
        s += 'Or.inr ('
    s += ('Or.inl hm' if i < n - 1 else 'hm')
    return s + ')' * i
L = []
survl = sorted(surv)
if mode == 'surv':
    hyps = ' '.join('(hS%d : R31Surv (![%s] : Fin 5 → Fin 3) (![%s] : Fin 5 → Fin 3) (%d))' % (i, ', '.join(map(str, c[0])), ', '.join(map(str, c[1])), c[2]) for i, c in enumerate(survl))
    L.append('theorem r31_cfgall_of_surv %s : R31CfgAll := by' % hyps)
else:
    L.append('theorem r31_cfgall : R31CfgAll := by')
L.append('  intro L hL h9 r1 r2 r3 h12 h13 h23 hX κ1 κ2 κ3 hκ1 hκ2 hκ3 c2 c3 j s hj hs hF1 hF2 hF3 f f13 M2 M3')
L.append('    hw2 hw3 hG12 hG13 hn hE3a hE3b hmono hf0 hf1 hf2 hE1 hg0 hg1 hg2 hk1 hk2 hk3 hK12 hK13 hJn')
for v, hn_ in ((0, 'hg0'), (1, 'hg1'), (2, 'hg2')):
    L.append("  have %s' : f13 0 = %d ∨ f13 1 = %d ∨ f13 2 = %d ∨ f13 3 = %d ∨ f13 4 = %d := by" % ((hn_,) + (v,) * 5))
    L.append('    obtain ⟨m, hm⟩ := %s' % hn_)
    L.append('    rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl')
    for i in range(5):
        L.append('    · exact %s' % orpath(i, 5))
L.append('  obtain ⟨e0, e4, hpat⟩ := canon_patterns f hmono hf0 hf1 hf2')
L.append('  rcases hpat with ' + disj(['⟨e1, e2, e3⟩'] * 6))
cnt = {'inst': 0, 'e5': 0, 'sorry': 0}
for P in pats:
    allowed = []
    for w in itertools.product(range(3), repeat=5):
        if len(set(w)) < 3:
            continue
        same = all((w[m] == 2) == (P[m] == 2) for m in range(5))
        comp = all((w[m] == 2) == (P[m] != 2) for m in range(5))
        if same or comp:
            allowed.append(w)
    pl = '![' + ', '.join(map(str, P)) + ']'
    L.append('  · have hf : ∀ m, f m = (%s : Fin 5 → Fin 3) m := by' % pl)
    L.append('      intro m')
    L.append('      rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl')
    L.append('      exacts [e0, e1, e2, e3, e4]')
    L.append('    have hE : (%s) ∨' % ' ∧ '.join('(f13 %d = 2 ↔ (%d : Fin 3) = 2)' % (m, P[m]) for m in range(5)))
    L.append('        (%s) := by' % ' ∧ '.join('(f13 %d = 2 ↔ ¬ (%d : Fin 3) = 2)' % (m, P[m]) for m in range(5)))
    L.append('      rcases hE1 with h | h')
    L.append('      · exact Or.inl ⟨%s⟩' % ', '.join('by rw [h %d, e%d]' % (m, m) for m in range(5)))
    L.append('      · exact Or.inr ⟨%s⟩' % ', '.join('by rw [h %d, e%d]' % (m, m) for m in range(5)))
    L.append("    rcases f13_cases_%s (f13 0) (f13 1) (f13 2) (f13 3) (f13 4) hE hg0' hg1' hg2' with" % ''.join(map(str, P)))
    L.append('      ' + disj(['⟨g0, g1, g2, g3, g4⟩'] * len(allowed)))
    for w in allowed:
        wl = '![' + ', '.join(map(str, w)) + ']'
        L.append('    · have hf13 : ∀ m, f13 m = (%s : Fin 5 → Fin 3) m := by' % wl)
        L.append('        intro m')
        L.append('        rcases fin5_cases m with rfl | rfl | rfl | rfl | rfl')
        L.append('        exacts [g0, g1, g2, g3, g4]')
        L.append('      rcases hs with hs | hs')
        for eps in (1, -1):
            tag = '%s_%s_%s' % (''.join(map(str, P)), ''.join(map(str, w)), 'p' if eps == 1 else 'm')
            key = (P, w, eps)
            name = ('e5_' if key in surv else 'inst_') + tag
            extra = ' hk1 hk2 hk3 hK12 hK13' + (' hJn' if key in surv else '') if key in D5 or key in surv else ''
            if mode == 'surv' and key in surv:
                L.append('      · exact hS%d L %s%s' % (survl.index(key), args, extra))
                cnt['e5'] += 1
                continue
            if mode == 'shape' and (avail is None or tag not in avail):
                L.append('      · sorry')
                cnt['sorry'] += 1
            else:
                L.append('      · exact %s %s%s' % (name, args, extra))
                cnt['e5' if key in surv else 'inst'] += 1
L.append('')
if mode == 'surv':
    L.append('theorem r31_hyp_of_surv %s : R31Hyp := r31_of_cfgall (r31_cfgall_of_surv %s)' % (hyps, ' '.join('hS%d' % i for i in range(len(survl)))))
else:
    L.append('theorem r31_hyp_proof : R31Hyp := r31_of_cfgall r31_cfgall')
open(out, 'w', encoding='utf-8').write('\n' + '\n'.join(L) + '\n')
print(out, cnt, sum(len(x) for x in L), 'chars')
