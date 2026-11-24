import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""sym_cut4.py -- SYM-M [DC3] generic rank-2 cell (3, 2, (PIV,), 0, 'ab', 'ab'), piece vartheta(Z_0) != 0, via ISOTROPIC-COLUMN
   complement generators (round 13, NOTES R13.3).
   N = span(Z_0, Z_1, Z_2) (Z_0 in N_P, pivot PIV; Z_1, Z_2 with neutral parts (v_3, 0), (0, v_4)).  vartheta(alpha Z_0 + Z_1) is a quadratic
   in alpha with leading coefficient vartheta(Z_0) != 0, so some Z_1' = alpha Z_0 + Z_1 has vartheta(Z_1') = 0, i.e. ALL its columns are
   isotropic ((F2)); likewise Z_2' = beta Z_0 + Z_2.  N = span(Z_0, Z_1', Z_2').  Z_1' = isotropic-column generator with neutral part (v_3, 0):
   u-charts {ab, z1, z2, 0}^3 (+ det sub-split of the all-'ab' triple, gen_t22pc.isocol).
   PLANE CUT: the plane (Z_0, Z_1') carries the 2-dim defect system S1 (equations of R(x_0 Z_0 + x_1 Z_1')); if S1 is UNIT for EVERY u-chart
   item of Z_1', the ne piece is empty.  Added (in the ideal by polarised (F2)): <c_j(Z_0), c_j(Z_1')> = vartheta(Z_0, Z_1') m_j, j = 0,1,2.
   Piece equations: une * den = 1, num - t den = 0 (den, num = |c_0(Z_0)|^2, |c_1(Z_0)|^2 in chart A, swapped in chart B).
   usage: python3 -I sym_cut4.py P CHART PIV OUTDIR TMO [ITEMS = U0:U1:U2/DSPLIT,...; default all 64 charts + the det split]"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_sym
from gen_t22t0 import isovec
from gen_t22pc import isocol, ip, col
p, chart, piv, od, tmo = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], float(sys.argv[5]); os.makedirs(od, exist_ok=True)
if len(sys.argv) > 6: items = sys.argv[6].split(',')
else:
    ch = ('ab', 'z1', 'z2', '0')
    items = ['%s:%s:%s/-' % (a, b, c) for a in ch for b in ch for c in ch if (a, b, c) != ('ab', 'ab', 'ab')] + ['ab:ab:ab/%s' % d for d in ('ne', '01', '02', '12')]
def system(uk, ds):
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); one = X.pconst(1, p)
    e = lambda j: [one if a == j else {} for a in range(5)]
    if chart == 'A': Wp = [e(3), e(4), [X.pmul(X.pconst(p - 1, p), t, p), one, {}, {}, {}], [X.padd(one, t, p), {}, one, {}, {}]]
    else: Wp = [e(3), e(4), [one, X.pmul(X.pconst(p - 1, p), t, p), {}, {}, {}], [{}, X.padd(one, t, p), one, {}, {}]]
    rows = X.echelon_rows(6, (piv,), V, 'u'); Z0 = X.dcsub_matrix(rows[0], [0, 1, 2], p)
    v3, e3 = isovec(p, cs, V, 'ab', '3'); extra = list(e3)
    Z1, ex = isocol(p, cs, V, uk.split(':'), v3, [{}] * 4, ds, ''); extra += ex
    j0, j1 = (0, 1) if chart == 'A' else (1, 0)
    den, num = ip(col(Z0, j0), col(Z0, j0), p), ip(col(Z0, j1), col(Z0, j1), p)
    une = V.new('une'); extra += [X.padd(X.pmul(une, den, p), X.pconst(1, p), p, -1), X.padd(num, X.pmul({(0,): 1}, den, p), p, -1)]
    th = ip(col(Z0, j0), col(Z1, j0), p)                                      # vartheta(Z_0, Z_1') (m_j0 = 1)
    mj = {j0: one, j1: t, 2: X.pmul(X.pconst(p - 1, p), X.padd(one, t, p), p)}
    for j in range(3):
        if j != j0: extra.append(X.padd(ip(col(Z0, j), col(Z1, j), p), X.pmul(mj[j], th, p), p, -1))
    polys = gen_sym.equations_poly([Z0, Z1], Wp, p) + extra
    return V.names, [q for q in polys if q]
nunit = 0; bad = []
for it in items:
    uk, ds = it.split('/'); ds = None if ds == '-' else ds
    names, polys = system(uk, ds)
    if X.trivially_unit(polys): v = 'UNIT(const)'
    else:
        fn = '%s/s4_%s%d_%s_%s.ms' % (od, chart, piv, uk.replace(':', ''), ds or 'x'); X.write_msolve(fn, names, p, polys)
        try:
            g, dt = subcut.msolve(fn, tmo); v = 'UNIT' if g == ['1'] else 'NONUNIT(%d)' % len(g)
        except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__
    nunit += v.startswith('UNIT')
    if not v.startswith('UNIT'): bad.append(it)
    print('S1 %s piv%d %s: %s' % (chart, piv, it, v), flush=True)
print('VERDICT sym_cut4 %s piv%d S1: %d/%d items UNIT%s' % (chart, piv, nunit, len(items), '' if not bad else '; not unit: ' + ' '.join(bad)), flush=True)
