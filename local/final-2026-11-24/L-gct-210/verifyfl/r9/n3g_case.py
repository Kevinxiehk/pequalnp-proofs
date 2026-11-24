import sys, os, time; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n3g_case.py -- [T22] for ANY m via gen_dc / gen_n3g: one N-case (index CI of gen_dc.cases(2, P, Nt)), all three S-cells; the GB of the 2-dim
   N-system (gen_dc.build) is computed first (NTIMEOUT) and inherited by the stages N+Y_1, N+Y_2, all (subcut.run).
   usage: python3 -I n3g_case.py P MSPEC CI OUTDIR TIMEOUT NTIMEOUT"""
import exactlib as X, gen_dc, gen_n3g, subcut
p, mspec, ci, od = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
tmo = float(sys.argv[5]) if len(sys.argv) > 5 else 900; ntmo = float(sys.argv[6]) if len(sys.argv) > 6 else 900
cs, m, W, P, Nt = gen_dc.setup(p, mspec); case = gen_dc.cases(2, P, Nt)[ci]; tag = '%s/%s_c%d' % (od, mspec, ci)
names, polys = gen_dc.build(p, mspec, case)
if X.trivially_unit(polys): print('VERDICT n3g case %d %s m=%s p=%d: UNIT (N-system constant)' % (ci, case, mspec, p)); sys.exit()
X.write_msolve(tag + '_N.ms', names, p, polys)
try:
    GN, dt = subcut.msolve(tag + '_N.ms', ntmo); print('N-system: %d elements (%.1fs)' % (len(GN), dt), flush=True)
except Exception:
    GN = []; print('N-system: timeout/fail -> no N-GB', flush=True)
if GN == ['1']: print('VERDICT n3g case %d %s m=%s p=%d: UNIT (no N)' % (ci, case, mspec, p)); sys.exit()
res = []
for s in (0, 1, 2):
    nm, eqs, extra = gen_n3g.build(p, mspec, case, s, keyed=True)
    assert nm[:len(names)] == names
    v = subcut.run(nm, eqs, extra, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], '%s_s%d' % (tag, s), tmo, pre=GN); res.append(v)
    print('  scell %d: %s' % (s, v), flush=True)
print('VERDICT n3g case %d %s m=%s p=%d: %s' % (ci, case, mspec, p, 'UNIT' if all(r == 'UNIT' for r in res) else 'NONUNIT %s' % res))
