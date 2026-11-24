import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n3sym_split.py -- SYM-M [T22] case CI, chart C, with the vartheta(Z_g) SPLIT (round 12, NOTES R12.1).  Z_g = the first generator of N
   (Z_0 in N_P for rho <= 1, the first complement element for rho = 2); its P-columns satisfy <z_j,z_j> = vartheta(Z_g) m_j ((F2)).
   chart A (m_0 = 1): den = <z_0,z_0>, num = <z_1,z_1> (= vartheta * t);  chart B (m_1 = 1): den = <z_1,z_1>, num = <z_0,z_0>.
   MODE zero: den = 0;  MODE ne: u * den = 1 and num - t * den = 0.  (A char-p case split; both pieces together = the case.)
   The extra equations are added to the N-system and to every stage.   usage: python3 -I n3sym_split.py P C CI MODE OUTDIR [TIMEOUT NTIMEOUT]"""
import exactlib as X, gen_n1s, gen_sym, gen_sym_n3, gen_n3, subcut
p, chart, ci, mode, od = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
tmo = float(sys.argv[6]) if len(sys.argv) > 6 else 900; ntmo = float(sys.argv[7]) if len(sys.argv) > 7 else 600
case = gen_n1s.cases(2)[ci]; tag = '%s/sp%s_c%d_%s' % (od, chart, ci, mode)
names, polys = gen_sym.build(p, chart, case)
cs = X.Consts(p); V2 = X.Vars(); V2.new('mt'); B, ex2, ells = gen_n3.nbasis(p, cs, case, V2); assert V2.names == names
Zg = B[0]; it = names.index('mt')
def ip(u, v):
    q = {}
    for a, b in zip(u, v): q = X.padd(q, X.pmul(a, b, p), p)
    return q
col = lambda j: [Zg[a][j] for a in range(4)]
n00, n11 = ip(col(0), col(0)), ip(col(1), col(1))
den, num = (n00, n11) if chart == 'A' else (n11, n00)
def split_extra(nm):
    if mode == 'zero': return [den], nm
    u = len(nm); nm2 = nm + ['usp']
    return [X.padd(X.pmul({(u,): 1}, den, p), X.pconst(1, p), p, -1), X.padd(num, X.pmul({(it,): 1}, den, p), p, -1)], nm2
sx, names2 = split_extra(names)
X.write_msolve(tag + '_N.ms', names2, p, polys + sx)
try:
    GN, dt = subcut.msolve(tag + '_N.ms', ntmo); print('N-system: %d elements (%.1fs)' % (len(GN), dt), flush=True)
except Exception:
    GN = []; print('N-system: timeout/fail -> no N-GB', flush=True)
if GN == ['1']: print('VERDICT n3sym-split %s case %d %s %s: UNIT (no N)' % (chart, ci, case, mode)); sys.exit()
res = []
for s in (0, 1, 2):
    nm, eqs, extra = gen_sym_n3.build(p, chart, case, s, keyed=True)
    assert nm[:len(names)] == names
    if mode == 'ne': nm = nm + ['usp']
    # the split equations use the N-variable ids, which coincide; the extra variable usp is appended last
    sx2 = [den] if mode == 'zero' else [X.padd(X.pmul({(len(nm) - 1,): 1}, den, p), X.pconst(1, p), p, -1), X.padd(num, X.pmul({(it,): 1}, den, p), p, -1)]
    try:
        v = subcut.run(nm, eqs, list(extra) + sx2, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], '%s_s%d' % (tag, s), tmo, pre=[g for g in GN if 'usp' not in g] if mode == 'ne' and False else GN)
    except Exception as exn:
        v = 'FAIL(%s)' % type(exn).__name__
    res.append(v); print('  scell %d: %s' % (s, v), flush=True)
print('VERDICT n3sym-split %s case %d %s %s: %s' % (chart, ci, case, mode, 'UNIT' if all(r == 'UNIT' for r in res) else 'NONUNIT/FAIL %s' % res))
