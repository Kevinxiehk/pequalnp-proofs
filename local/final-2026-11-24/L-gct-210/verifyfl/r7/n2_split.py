import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""n2_split.py -- [T31] stage a/b under the vartheta(Zs) split (gen_n2 zsmode): MODE = R1:vt:lc | A:cell | B:cell.
   Stages: Zs alone, then full (Zs-GB inherited).   usage: python3 -I n2_split.py P MSPEC MODE STAGE OUTPREFIX [timeout]"""
import exactlib as X, gen_n2, subcut
p = int(sys.argv[1]); mspec = sys.argv[2]; mode = sys.argv[3].split(':'); st = sys.argv[4]; out = sys.argv[5]; tmo = float(sys.argv[6]) if len(sys.argv) > 6 else 900
if mode[0] == 'R1': zm = ('R1', mode[1], int(mode[2])); cell = -1
else: zm = mode[0]; cell = int(mode[1])
names, eqs, extra = gen_n2.build(p, mspec, cell, st, keyed=True, zsmode=zm)
R = 3 if st == 'a' else 4
v = subcut.run_deg(names, eqs, extra, p, [(4,) + (0,) * (R - 1), (4,) * R], out, tmo)
print('VERDICT n2 %s stage %s m=%s p=%d: %s' % (sys.argv[3], st, mspec, p, v), flush=True)
