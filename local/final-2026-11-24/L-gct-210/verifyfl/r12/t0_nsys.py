import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""t0_nsys.py: piece (IV) N-systems (gen_t22t0, scell None) for N-case CI, chart C, all u-chart pairs.  usage: P C CI OUTDIR TMO"""
import subcut_fixed as subcut, exactlib as X, gen_t22t0 as G
p, chart, ci, od, tmo = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], float(sys.argv[5]); os.makedirs(od, exist_ok=True)
for u0 in ('ab', 'z1', 'z2', '0'):
    for u1 in ('ab', 'z1', 'z2', '0'):
        names, polys = G.build(p, chart, ci, u0, u1, None)
        if X.trivially_unit(polys): print('N %s c%d u0=%s u1=%s: UNIT (constant)' % (chart, ci, u0, u1), flush=True); continue
        fn = '%s/t0N_%s_c%d_%s_%s.ms' % (od, chart, ci, u0, u1); X.write_msolve(fn, names, p, polys)
        try:
            G_, dt = subcut.msolve(fn, tmo); v = 'UNIT' if G_ == ['1'] else 'NONUNIT(%d)' % len(G_)
        except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__; dt = 0
        print('N %s c%d u0=%s u1=%s: %s (%.1fs)' % (chart, ci, u0, u1, v, dt), flush=True)
