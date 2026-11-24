import sys; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""B1 plane stage (Z + Y_omega, s(Y_omega) = omega exactly, omega != 0 chart I) with the Y_omega variables in the FIRST block: msolve -e 6
computes the elimination ideal in (Z, u) = the B1 Z-locus.   usage: python3 -I b1_elim.py P MSPEC I OUT.ms"""
import exactlib as X, gen_t31b1
p, mspec, I, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
names, eqs, extra, B = gen_t31b1.build(p, mspec, 2, I, keyed=True, xomega=True)
xs = {X.XOFF, X.XOFF + 1}
polys = [e for (i, xm), e in eqs.items() if e and set(xm) <= xs]
yv = [i for i, n in enumerate(names) if n.startswith('U')]; zv = [i for i, n in enumerate(names) if n.startswith('Z') or n == 'uom']
allowed = set(yv) | set(zv)
polys += [q for q in extra if {v for mon in q for v in mon} <= allowed]
order = yv + zv
with open(out, 'w') as f:
    f.write(','.join(names[i] for i in order) + '\n' + str(p) + '\n' + ',\n'.join(X.fmt_poly(q, names) for q in polys) + '\n')
print(len(order), 'vars (first %d eliminated):' % len(yv), [names[i] for i in order], len(polys), 'polys')
