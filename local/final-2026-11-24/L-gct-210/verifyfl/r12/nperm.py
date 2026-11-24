import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""nperm.py -- piece-IV N-system (t0c pieces) + the permanent relations R14.4 (perm34) and R14.5 (permP): is the N-system alone UNIT?
   usage: python3 -I nperm.py P C CI DSPLIT OUTPREFIX TMO [perm34|both]"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_t22rad as G
p, chart, ci, ds, out, tmo = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], float(sys.argv[6])
mode = sys.argv[7] if len(sys.argv) > 7 else 'both'
nm, eqs, extra = G.build(p, chart, ci, 't0c', ds, 1, keyed=True, perm34=True, permP=(mode == 'both'))
yv = {i for i, n in enumerate(nm) if n.startswith('w') or n.startswith('r')}
polys = [e for (i, xm), e in eqs.items() if e and set(xm) <= {X.XOFF, X.XOFF + 1}] + [q for q in extra if not any(v in yv for mon in q for v in mon)]
ids = sorted({v for q in polys for mon in q for v in mon}); names = [nm[i] for i in ids]
with open(out + '.ms', 'w') as f: f.write(','.join(names) + '\n' + str(p) + '\n' + ',\n'.join(X.fmt_poly(q, nm) for q in polys) + '\n')
try:
    g, dt = subcut.msolve(out + '.ms', tmo); v = 'UNIT' if g == ['1'] else 'NONUNIT(%d)' % len(g)
except Exception as ex: v = 'FAIL(%s)' % type(ex).__name__; dt = 0
print('VERDICT nperm %s c%d t0c %s %s: N-system + permanents: %s (%.1fs, %d vars)' % (chart, ci, ds, mode, v, dt, len(names)), flush=True)
