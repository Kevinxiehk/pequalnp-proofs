import sys; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7')
"""staged run of gen_sym_n2 (symbolic-m [T31] split A): stages Zs+Y_1, Zs+Y_2, all.  usage: python3 -I t31A_sym.py P CHART ZMODE OUTPREFIX"""
import exactlib as X, gen_sym_n2, subcut
p, chart, zm, out = int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
names, eqs, extra, B = gen_sym_n2.build(p, chart, zm, keyed=True)
try: v = subcut.run(names, eqs, extra, p, [[0, 1], [0, 2], [0, 1, 2]], out, 1500)
except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__
print('VERDICT t31A-sym chart %s %s: %s' % (chart, zm, v), flush=True)
