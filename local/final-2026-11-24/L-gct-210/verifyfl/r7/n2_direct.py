import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n2_direct.py -- [T31] one Zs-cell: GB of the Zs-subsystem (x_0 only), then the FULL cell + that GB (same ideal).
   usage: python3 -I n2_direct.py P MSPEC CELL STAGE OUTPREFIX [timeout]"""
import exactlib as X, gen_n2, subcut
p = int(sys.argv[1]); mspec = sys.argv[2]; cell = int(sys.argv[3]); st = sys.argv[4]; out = sys.argv[5]; tmo = float(sys.argv[6]) if len(sys.argv) > 6 else 900
names, eqs, extra = gen_n2.build(p, mspec, cell, st, keyed=True)
R = 3 if st == 'a' else 4
v = subcut.run_deg(names, eqs, extra, p, [(4,) + (0,) * (R - 1), (4,) * R], out, tmo)
print('VERDICT n2 cell %d stage %s m=%s p=%d: %s' % (cell, st, mspec, p, v), flush=True)
