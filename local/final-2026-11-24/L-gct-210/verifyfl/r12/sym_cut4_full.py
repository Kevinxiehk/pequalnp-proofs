import sys, os, re; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""sym_cut4_full.py -- FULL stage of sym_cut4 (NOTES R13.3): for chart items C1 (of Z_1', neutral (v_3, 0)) and C2 (of Z_2', neutral (0, v_4))
   whose plane systems S1 are NOT unit: the full system R(x_0 Z_0 + x_1 Z_1' + x_2 Z_2') + piece equations + polarised (F2) for the pairs
   (Z_0, Z_1'), (Z_0, Z_2'), (Z_1', Z_2'), plus GB(S1, C1) and GB(S1, C2) RENAMED to the plane (Z_0, Z_2') (columns 3 <-> 4 symmetry:
   a3,b3 -> a4,b4; au_j,bu_j,mu_j,udet -> aqu_j,bqu_j,qmu_j,qudet).  Every pair (C1, C2) with both S1 non-unit must be UNIT.
   usage: python3 -I sym_cut4_full.py P CHART PIV S4DIR OUTDIR TMO PAIRS   (PAIRS = C1+C2,...; C = U0:U1:U2/DSPLIT)"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_sym
from gen_t22t0 import isovec
from gen_t22pc import isocol, ip, col
p, chart, piv, s4d, od, tmo, pairs = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], float(sys.argv[6]), sys.argv[7].split(',')
os.makedirs(od, exist_ok=True)
def gbfile(it):
    uk, ds = it.split('/'); return '%s/s4_%s%d_%s_%s.ms.gb' % (s4d, chart, piv, uk.replace(':', ''), ds if ds != '-' else 'x')
def readgb(fn):
    s = open(fn).read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; return [x.strip() for x in body.split(',\n') if x.strip()]
ren = {'a3': 'a4', 'b3': 'b4', 'udet': 'qudet'}
for j in range(3): ren.update({'au%d' % j: 'aqu%d' % j, 'bu%d' % j: 'bqu%d' % j, 'mu%d' % j: 'qmu%d' % j})
pat = re.compile(r'\b(' + '|'.join(map(re.escape, ren)) + r')\b')
for pr in pairs:
    c1, c2 = pr.split('+')
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); one = X.pconst(1, p)
    e = lambda j: [one if a == j else {} for a in range(5)]
    if chart == 'A': Wp = [e(3), e(4), [X.pmul(X.pconst(p - 1, p), t, p), one, {}, {}, {}], [X.padd(one, t, p), {}, one, {}, {}]]
    else: Wp = [e(3), e(4), [one, X.pmul(X.pconst(p - 1, p), t, p), {}, {}, {}], [{}, X.padd(one, t, p), one, {}, {}]]
    rows = X.echelon_rows(6, (piv,), V, 'u'); Z0 = X.dcsub_matrix(rows[0], [0, 1, 2], p)
    v3, e3 = isovec(p, cs, V, 'ab', '3'); v4, e4 = isovec(p, cs, V, 'ab', '4'); extra = list(e3) + list(e4)
    uk1, d1 = c1.split('/'); uk2, d2 = c2.split('/')
    Z1, ex = isocol(p, cs, V, uk1.split(':'), v3, [{}] * 4, None if d1 == '-' else d1, ''); extra += ex
    Z2, ex = isocol(p, cs, V, uk2.split(':'), [{}] * 4, v4, None if d2 == '-' else d2, 'q'); extra += ex
    j0, j1 = (0, 1) if chart == 'A' else (1, 0)
    den, num = ip(col(Z0, j0), col(Z0, j0), p), ip(col(Z0, j1), col(Z0, j1), p)
    une = V.new('une'); extra += [X.padd(X.pmul(une, den, p), X.pconst(1, p), p, -1), X.padd(num, X.pmul({(0,): 1}, den, p), p, -1)]
    mj = {j0: one, j1: t, 2: X.pmul(X.pconst(p - 1, p), X.padd(one, t, p), p)}
    for A_, B_ in ((Z0, Z1), (Z0, Z2), (Z1, Z2)):
        th = ip(col(A_, j0), col(B_, j0), p)
        for j in range(3):
            if j != j0: extra.append(X.padd(ip(col(A_, j), col(B_, j), p), X.pmul(mj[j], th, p), p, -1))
    polys = [q for q in gen_sym.equations_poly([Z0, Z1, Z2], Wp, p) + extra if q]
    tag = '%s/f4_%s%d_%s__%s' % (od, chart, piv, c1.replace(':', '').replace('/', '_'), c2.replace(':', '').replace('/', '_'))
    try:
        g1 = readgb(gbfile(c1)); g2 = [pat.sub(lambda mm: ren[mm.group(1)], x) for x in readgb(gbfile(c2))]
    except Exception as ex:
        print('FULL %s piv%d %s: no S1 GB (%s)' % (chart, piv, pr, type(ex).__name__), flush=True); continue
    names = V.names
    with open(tag + '.ms', 'w') as f: f.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join([X.fmt_poly(q, names) for q in polys] + g1 + g2) + '\n')
    try:
        g, dt = subcut.msolve(tag + '.ms', tmo); v = 'UNIT' if g == ['1'] else 'NONUNIT(%d)' % len(g)
    except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__; dt = 0
    print('FULL %s piv%d %s: %s (%.1fs)' % (chart, piv, pr, v, dt), flush=True)
