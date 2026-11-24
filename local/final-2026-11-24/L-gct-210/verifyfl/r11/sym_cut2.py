import sys, os, re; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""sym_cut2.py -- generic rank-2 [DC3] cell of the SYMBOLIC-m family (gen_sym chart A or B) with the vartheta(Z_0) split (NOTES R11.10):
   (F2) on Z_0 (doubly centred, supported on P): <z_j,z_j> = vartheta(Z_0) m_j.  Chart A (m_0 = 1): if vartheta(Z_0) != 0 then
   t = m_1 = <z_1,z_1>/<z_0,z_0>; chart B (m_1 = 1): t = m_0 = <z_0,z_0>/<z_1,z_1>.  The equations are linear in t.
   MODE 'sub': multiply by the denominator, substitute (t eliminated), add u*den = 1;   MODE 'zero': keep t, add den-numerator... i.e.
   vartheta(Z_0) = 0 <=> <z_0,z_0> = 0 (chart A) resp. <z_1,z_1> = 0 (chart B).  Then the plane-subsystem cut (S1 GB, renamed S2, all).
   usage: python3 -I sym_cut2.py P CHART PIV MODE OUTPREFIX"""
import exactlib as X, gen_sym, subcut
p, chart, piv, mode, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
case = (3, 2, (piv,), 0, 'ab', 'ab')
names, eqs, extra = gen_sym.build(p, chart, case, keyed=True)
it = names.index('mt')
# Z_0 = first N_P generator: dcsub coordinates co[3t+a] = entry (a,t); pivot 1, coordinates < pivot 0, others u0_d
co = []
for d in range(6):
    if d == piv: co.append(X.pconst(1, p))
    elif d < piv: co.append({})
    else: co.append({(names.index('u0_%d' % d),): 1})
def colvec(t_):
    c = [co[3 * t_ + a] for a in range(3)]; last = {}
    for q in c: last = X.padd(last, q, p, -1)
    return c + [last]
def ip(u, v):
    q = {}
    for a, b in zip(u, v): q = X.padd(q, X.pmul(a, b, p), p)
    return q
z0, z1 = colvec(0), colvec(1); n00, n11 = ip(z0, z0), ip(z1, z1)
num, den = (n11, n00) if chart == 'A' else (n00, n11)
def split_t(q):
    A, Bt = {}, {}
    for mon, c in q.items():
        k = mon.count(it); rest = tuple(v for v in mon if v != it)
        assert k <= 1, 'equation not linear in t'
        (A if k == 0 else Bt)[rest] = c
    return A, Bt
neqs = {}
for key, q in eqs.items():
    if not q: continue
    if mode == 'sub':
        A, Bt = split_t(q); r = X.padd(X.pmul(den, A, p), X.pmul(num, Bt, p), p)
        if r: neqs[key] = r
    else: neqs[key] = q
extra = list(extra)
if mode == 'ne':      # vartheta(Z_0) != 0, t kept: u * den = 1 and the (F2) relation num - t den = 0 (a consequence, stated explicitly)
    u = len(names); names = names + ['une']; extra.append(X.padd(X.pmul({(u,): 1}, den, p), X.pconst(1, p), p, -1))
    extra.append(X.padd(num, X.pmul({(it,): 1}, den, p), p, -1))
elif mode == 'sub':
    u = len(names); names = names + ['usub']; extra.append(X.padd(X.pmul({(u,): 1}, den, p), X.pconst(1, p), p, -1))
elif mode == 'zero': extra.append(den)
x1, x2 = X.XOFF + 1, X.XOFF + 2
q3 = [q for q in extra if any(names[v] in ('a3', 'b3') for mon in q for v in mon)]
rest = [q for q in extra if q not in q3 and not any(names[v] in ('a4', 'b4') for mon in q for v in mon)]
S1 = [e for (i, xm), e in neqs.items() if x2 not in xm] + q3 + rest
def write_used(fn, polys, txt=()):
    ids = sorted({v for q in polys for mon in q for v in mon})
    with open(fn, 'w') as f: f.write(','.join(names[i] for i in ids) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys] + list(txt)) + '\n')
write_used(out + '_S1.ms', S1)
try:
    g1, dt = subcut.msolve(out + '_S1.ms', 1500); print('GB(S1): %d elements (%.1fs)' % (len(g1), dt), flush=True)
except Exception as ex:
    print('VERDICT sym_cut2 %s piv%d %s: FAIL at S1 (%s)' % (chart, piv, mode, type(ex).__name__)); sys.exit()
if g1 == ['1']: print('VERDICT sym_cut2 %s piv%d %s: UNIT (at S1)' % (chart, piv, mode)); sys.exit()
ren = {'a3': 'a4', 'b3': 'b4'}; ren.update({'y0_%d' % d: 'y1_%d' % d for d in range(6) if d != piv})
pat = re.compile(r'\b(' + '|'.join(map(re.escape, ren)) + r')\b')
g2 = [pat.sub(lambda mm: ren[mm.group(1)], x) for x in g1]
full = list(neqs.values()) + extra
with open(out + '_FULLGB.ms', 'w') as f:
    f.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in full] + g1 + g2) + '\n')
try: g, dt = subcut.msolve(out + '_FULLGB.ms', 1500)
except Exception as ex: print('VERDICT sym_cut2 %s piv%d %s: FAIL at FULL (%s)' % (chart, piv, mode, type(ex).__name__)); sys.exit()
print('VERDICT sym_cut2 %s piv%d %s: %s (%d elements, %.1fs)' % (chart, piv, mode, 'UNIT' if g == ['1'] else 'NONUNIT', len(g), dt), flush=True)
