import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n2_cell.py -- [T31] stage a/b for one Zs-cell with DEGREE-STAGED subsystem cut (subcut.run_deg).  The coefficients of x_0^i x_r
   (x_r-degree 1) are LINEAR in Y_r: they are the first-order conditions "Y_r + t Zs in K".
   usage: python3 -I n2_cell.py P MSPEC CELL STAGE(a|b) OUTPREFIX [timeout]"""
import exactlib as X, gen_n2, subcut
p = int(sys.argv[1]); mspec = sys.argv[2]; cell = int(sys.argv[3]); st = sys.argv[4]; out = sys.argv[5]; tmo = float(sys.argv[6]) if len(sys.argv) > 6 else 900
names, eqs, extra = gen_n2.build(p, mspec, cell, st, keyed=True)
if st == 'a': T = [(4,0,0), (4,1,0), (4,0,1), (4,1,1), (4,2,0), (4,0,2), (4,2,1), (4,1,2), (4,2,2), (4,4,4)]
else: T = [(4,0,0,0), (4,1,0,0), (4,0,1,0), (4,0,0,1), (4,1,1,0), (4,1,0,1), (4,0,1,1), (4,1,1,1), (4,2,1,1), (4,1,2,1), (4,1,1,2), (4,4,4,4)]
v = subcut.run_deg(names, eqs, extra, p, T, out, tmo)
print('VERDICT n2 cell %d stage %s m=%s p=%d: %s' % (cell, st, mspec, p, v), flush=True)
