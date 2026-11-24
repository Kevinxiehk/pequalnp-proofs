import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n3sym_case.py -- SYM-M [T22] for one N-case CI (gen_n1s.cases(2)) in chart A or B: symbolic N-system GB first (NTIMEOUT), then the
   stages N+Y_1, N+Y_2, all per S-cell (subcut.run, GB_N inherited).   usage: python3 -I n3sym_case.py P CHART CI OUTDIR TIMEOUT NTIMEOUT"""
import exactlib as X, gen_n1s, gen_sym, gen_sym_n3, subcut
p, chart, ci, od = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
tmo = float(sys.argv[5]) if len(sys.argv) > 5 else 900; ntmo = float(sys.argv[6]) if len(sys.argv) > 6 else 600
case = gen_n1s.cases(2)[ci]; tag = '%s/sym%s_c%d' % (od, chart, ci)
names, polys = gen_sym.build(p, chart, case)
if X.trivially_unit(polys): print('VERDICT n3sym %s case %d %s: UNIT (N-system constant)' % (chart, ci, case)); sys.exit()
X.write_msolve(tag + '_N.ms', names, p, polys)
try:
    GN, dt = subcut.msolve(tag + '_N.ms', ntmo); print('N-system: %d elements (%.1fs)' % (len(GN), dt), flush=True)
except Exception:
    GN = []; print('N-system: timeout/fail -> no N-GB', flush=True)
if GN == ['1']: print('VERDICT n3sym %s case %d %s: UNIT (no N)' % (chart, ci, case)); sys.exit()
res = []
for s in (0, 1, 2):
    nm, eqs, extra = gen_sym_n3.build(p, chart, case, s, keyed=True)
    try:
        v = subcut.run(nm, eqs, extra, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], '%s_s%d' % (tag, s), tmo, pre=GN)
    except Exception as ex:
        v = 'FAIL(%s)' % type(ex).__name__
    res.append(v); print('  scell %d: %s' % (s, v), flush=True)
print('VERDICT n3sym %s case %d %s: %s' % (chart, ci, case, 'UNIT' if all(r == 'UNIT' for r in res) else 'NONUNIT/FAIL %s' % res))
