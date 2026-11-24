import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""write gen_n1s split A / split B files for one case: python3 -I mk_split.py P MSPEC PIV T3 T4 OUTPREFIX"""
import exactlib as X, gen_n1s
p = int(sys.argv[1]); mspec = sys.argv[2]; piv = int(sys.argv[3]); t3, t4 = sys.argv[4], sys.argv[5]; out = sys.argv[6]
for sp in ('A', 'B'):
    names, polys = gen_n1s.build(p, mspec, (3, 2, (piv,), 0, t3, t4), split=sp)
    X.write_msolve('%s_split%s.ms' % (out, sp), names, p, polys); print(sp, len(names), 'vars', len(polys), 'eqs')
