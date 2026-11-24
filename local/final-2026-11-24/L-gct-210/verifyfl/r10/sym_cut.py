import sys, os, re, subprocess, time; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""sym_cut.py -- subsystem cut (R7.2) for a generic rank-2 [DC3] cell of the SYMBOLIC-m family (gen_sym, chart A/B): GB of the plane
   subsystem S1 = R_i(x_0 Z_0 + x_1 Z_1) (+ quadric of v_3), S2 = its column-swap image (renaming checked), then FULL + both GBs.
   usage: python3 -I sym_cut.py P CHART PIV OUTPREFIX"""
import exactlib as X, gen_sym, subcut
p, chart, piv, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
case = (3, 2, (piv,), 0, 'ab', 'ab')
names, eqs, extra = gen_sym.build(p, chart, case, keyed=True)
x1, x2 = X.XOFF + 1, X.XOFF + 2
q3 = [q for q in extra if any(names[v] in ('a3', 'b3') for mon in q for v in mon)]
q4 = [q for q in extra if any(names[v] in ('a4', 'b4') for mon in q for v in mon)]
S1 = [e for (i, xm), e in eqs.items() if e and x2 not in xm] + q3
S2 = [e for (i, xm), e in eqs.items() if e and x1 not in xm] + q4
ren = {names.index('a3'): names.index('a4'), names.index('b3'): names.index('b4')}
for d in range(6):
    if d != piv: ren[names.index('y0_%d' % d)] = names.index('y1_%d' % d)
def canon(q):
    lead = max(q); iv = X.inv(q[lead], p); return frozenset((k, v * iv % p) for k, v in q.items())
def rn(q): return {tuple(sorted(ren.get(v, v) for v in mon)): c for mon, c in q.items()}
assert set(canon(rn(q)) for q in S1) == set(canon(q) for q in S2), 'S2 is not the renamed S1'
def write_used(fn, polys):
    ids = sorted({v for q in polys for mon in q for v in mon})
    with open(fn, 'w') as f: f.write(','.join(names[i] for i in ids) + '\n' + str(p) + '\n' + ',\n'.join(X.fmt_poly(q, names) for q in polys) + '\n')
write_used(out + '_S1.ms', S1); g1, dt = subcut.msolve(out + '_S1.ms', 1500); print('GB(S1): %d elements (%.1fs)' % (len(g1), dt), flush=True)
nm = {names[a]: names[b] for a, b in ren.items()}; pat = re.compile(r'\b(' + '|'.join(map(re.escape, nm)) + r')\b')
g2 = [pat.sub(lambda mm: nm[mm.group(1)], x) for x in g1]
full = [e for e in eqs.values() if e] + list(extra)
with open(out + '_FULLGB.ms', 'w') as f:
    f.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in full] + g1 + g2) + '\n')
g, dt = subcut.msolve(out + '_FULLGB.ms', 1500)
print('VERDICT sym_cut chart %s case %s p=%d: %s (%d elements, %.1fs)' % (chart, case, p, 'UNIT' if g == ['1'] else 'NONUNIT', len(g), dt), flush=True)
