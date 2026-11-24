import sys, os, glob; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""b1sym_run.py -- SYM-M [T31] split B1, chart A (gen_sym_b1, three-column form, par = True), one x-cell: Z-set GB, then stages Z+Y3 | Z+Y1 |
   all (subcut_fixed.run).  usage: python3 -I b1sym_run.py P XCELL OUTPREFIX TMO"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_sym_b1 as G
p, xc, out, tmo = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], float(sys.argv[4])
os.makedirs(os.path.dirname(out) or '.', exist_ok=True)
nm, eqs, extra, B = G.build(p, xc, keyed=True)
zx = [q for q in extra if not any(nm[v][0] in 'UwxX' for mon in q for v in mon)]
zeq = [e for (i, xm), e in eqs.items() if e and set(xm) <= {X.XOFF}]
X.write_msolve(out + '_Z.ms', nm, p, zeq + zx)
try: GZ, dt = subcut.msolve(out + '_Z.ms', tmo); print('Z-set GB: %d elements (%.1fs)' % (len(GZ), dt), flush=True)
except Exception as ex: GZ = []; print('Z-set GB FAIL(%s)' % type(ex).__name__, flush=True)
if GZ == ['1']: print('VERDICT b1sym A xcell %d: UNIT (no Z)' % xc); sys.exit()
try: v = subcut.run(nm, eqs, extra, p, [[0, 1], [0, 2], [0, 1, 2]], out, tmo, pre=GZ)
except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__
print('VERDICT b1sym A xcell %d: %s' % (xc, v), flush=True)
