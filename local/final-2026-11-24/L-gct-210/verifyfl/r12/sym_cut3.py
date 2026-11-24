import sys, os, re; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""sym_cut3.py -- SYM-M [DC3] generic rank-2 cell (case (3,2,(PIV,),0,'ab','ab')), piece vartheta(Z_0) != 0, with the THETA-ORTHOGONAL
   normalisation (round 12, NOTES R12.3).  vartheta(Z_0) != 0 => each complement element Z_r (r = 1, 2; neutral parts v_3 resp. v_4) has a
   unique representative in Z_r + C Z_0 with vartheta(Z_r, Z_0) = 0.  Chart A (m_0 = 1): vartheta(Z_r, Z_0) = <c_0(Z_r), c_0(Z_0)>; chart B
   (m_1 = 1): <c_1(Z_r), c_1(Z_0)>.  So: all 6 P-coordinates of Z_r free (pivot coordinate no longer 0) + that ONE normalisation equation;
   added consequences (in the ideal by polarised (F2)): <c_j(Z_r), c_j(Z_0)> = 0 for j = 0, 1, 2.  Piece equations: u*den = 1, num - t*den = 0
   (den, num = |c_0(Z_0)|^2, |c_1(Z_0)|^2 in chart A, swapped in chart B).  Then sym_cut2's plane cut: S1 = plane (Z_0, Z_1) system, its GB
   renamed (a3,b3,y0_d -> a4,b4,y1_d; columns 3 <-> 4 symmetry) = plane (Z_0, Z_2) GB, FULL = everything + both GBs.
   msolve timeout SYMTMO (env, default 1500); guarded subcut_fixed.   usage: python3 -I sym_cut3.py P CHART PIV OUTPREFIX"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_sym
SYMTMO = float(os.environ.get('SYMTMO', '1500'))
p, chart, piv, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
k, rho, lc, t3, t4 = 3, 2, 0, 'ab', 'ab'; pv = (piv,)
cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); one = X.pconst(1, p)
e = lambda j: [one if a == j else {} for a in range(5)]
if chart == 'A': Wp = [e(3), e(4), [X.pmul(X.pconst(p - 1, p), t, p), one, {}, {}, {}], [X.padd(one, t, p), {}, one, {}, {}]]
else: Wp = [e(3), e(4), [one, X.pmul(X.pconst(p - 1, p), t, p), {}, {}, {}], [{}, X.padd(one, t, p), one, {}, {}]]
rows = X.echelon_rows(6, pv, V, 'u'); B = [X.dcsub_matrix(r, [0, 1, 2], p) for r in rows]; assert len(B) == 1
vec = {}; extra = []
for name in ('3', '4'):
    a = V.new('a' + name); b = V.new('b' + name); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
    vec[name] = [one, a, b, last]; q = X.pconst(1, p)
    for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
    extra.append(q)
for r, (l3, l4) in enumerate([({(): 1}, {}), ({}, {(): 1})]):
    co = [V.new('y%d_%d' % (r, d)) for d in range(6)]                     # ALL coordinates free (theta-orthogonal normalisation)
    M = X.dcsub_matrix(co, [0, 1, 2], p)
    for lam, name, col in ((l3, '3', 3), (l4, '4', 4)):
        if lam:
            for a in range(4):
                ee = X.pmul(lam, vec[name][a], p); M[a][col] = X.padd(M[a][col], ee, p); M[a][2] = X.padd(M[a][2], ee, p, -1)
    B.append(M)
names = V.names; it = names.index('mt')
def col(M, j): return [M[a][j] for a in range(4)]
def ip(u, v):
    q = {}
    for x, y in zip(u, v): q = X.padd(q, X.pmul(x, y, p), p)
    return q
Z0 = B[0]; n00, n11 = ip(col(Z0, 0), col(Z0, 0)), ip(col(Z0, 1), col(Z0, 1))
num, den = (n11, n00) if chart == 'A' else (n00, n11)
jn = 0 if chart == 'A' else 1
norm = {r: [ip(col(B[r], j), col(Z0, j)) for j in range(3)] for r in (1, 2)}   # j = jn is the normalisation, the others consequences
u = len(names); names = names + ['une']
extra.append(X.padd(X.pmul({(u,): 1}, den, p), X.pconst(1, p), p, -1)); extra.append(X.padd(num, X.pmul({(it,): 1}, den, p), p, -1))
for r in (1, 2): extra += [q for q in norm[r] if q]
eqs = gen_sym.equations_poly(B, Wp, p, keyed=True)
x2 = X.XOFF + 2
def has(q, pref): return any(names[v] in pref or any(names[v].startswith(s) for s in pref if s.endswith('_')) for mon in q for v in mon)
bad2 = ('a4', 'b4', 'y1_')
S1 = [q for (i, xm), q in eqs.items() if q and x2 not in xm] + [q for q in extra if not has(q, bad2)]
def write_used(fn, polys, txt=()):
    ids = sorted({v for q in polys for mon in q for v in mon})
    with open(fn, 'w') as f: f.write(','.join(names[i] for i in ids) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys] + list(txt)) + '\n')
write_used(out + '_S1.ms', S1)
try:
    g1, dt = subcut.msolve(out + '_S1.ms', SYMTMO); print('GB(S1): %d elements (%.1fs)' % (len(g1), dt), flush=True)
except Exception as ex:
    print('VERDICT sym_cut3 %s piv%d ne: FAIL at S1 (%s)' % (chart, piv, type(ex).__name__)); sys.exit()
if g1 == ['1']: print('VERDICT sym_cut3 %s piv%d ne: UNIT (at S1)' % (chart, piv)); sys.exit()
ren = {'a3': 'a4', 'b3': 'b4'}; ren.update({'y0_%d' % d: 'y1_%d' % d for d in range(6)})
pat = re.compile(r'\b(' + '|'.join(map(re.escape, ren)) + r')\b')
g2 = [pat.sub(lambda mm: ren[mm.group(1)], x) for x in g1]
full = [q for q in eqs.values() if q] + extra
with open(out + '_FULLGB.ms', 'w') as f:
    f.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in full] + g1 + g2) + '\n')
try: g, dt = subcut.msolve(out + '_FULLGB.ms', SYMTMO)
except Exception as ex: print('VERDICT sym_cut3 %s piv%d ne: FAIL at FULL (%s)' % (chart, piv, type(ex).__name__)); sys.exit()
print('VERDICT sym_cut3 %s piv%d ne: %s (%d elements, %.1fs)' % (chart, piv, 'UNIT' if g == ['1'] else 'NONUNIT', len(g), dt), flush=True)
