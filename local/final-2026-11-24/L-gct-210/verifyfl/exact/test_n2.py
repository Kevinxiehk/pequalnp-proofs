import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""substitution tests for gen_n2.py ([T31]); control = 3-dim subspace span(Zs, Y_1, Y_2) of the exact two-column space K_2 (DI5-R6 H1)"""
import exactlib as X, random, gen_n2
p = 2147483629; cs = X.Consts(p); rnd = random.Random(11); res = []
def dcoords(M): return [M[a][q] % p for a in range(3) for q in range(4)]
def check(name, mspec, cell, vals, expect, **kw):
    names, polys = gen_n2.build(p, mspec, cell, **kw); assert len(names) == len(vals), (len(names), len(vals))
    val = dict(enumerate(vals)); ok = all(X.peval(q, val, p) == 0 for q in polys)
    rv = {i: rnd.randrange(p) for i in range(len(names))}; bad = sum(1 for q in polys if X.peval(q, rv, p))
    print('%-50s m=%-6s cell %d: %d unknowns, %d eqs; satisfies all: %s (expected %s); random point violates %d' % (name, mspec, cell, len(names), len(polys), ok, expect, bad))
    res.append(ok == expect and bad > 0)
zeta, zb, h = cs.zeta, cs.zetab, cs.h
Zs = X.outer(zeta, [1, p - 1, 0, 0, 0], p)
def Ypart(s, extra):          # D-part of Y = extra + Zs (gauge c = 1) minus s e_0^T
    Y = X.msum(extra, Zs, p); return X.msum(Y, X.outer(s, [1, 0, 0, 0, 0], p), p, -1)
D1 = dcoords(Ypart(zb, X.outer(zb, [0, 0, 1, 0, 0], p))); D2 = dcoords(Ypart(h, X.outer(h, [0, 0, 0, 1, 0], p)))
assert D1[0] == 0 and D2[0] == 0
vals = [zeta[1], zeta[2]] + D1[1:] + D2[1:]
check('K_2 slice span(Zs, zb e2, h e3), svec zb;h', 'two', 0, vals, True, stage='a', svec=['zb', 'h'])
check('same point, m = (1,2,-3,0,0)  [must fail]', 'm12m3', 0, vals + [0] * 3 * 0, False, stage='a', svec=['zb', 'h']) if False else None
# with the wrong row sums the same coordinates must fail (the constant part s e_0^T changes)
check('same coordinates, svec b1;b2  [must fail]', 'two', 0, vals, False, stage='a', svec=['b1', 'b2'])
# Zs fixed (calibration mode): chi_1 (1,1,-2,0,0) with m12m3 -- only a syntax/size check here (no known solution)
names, polys = gen_n2.build(p, 'm12m3', -1, 'b', None, ('chi1', [1, 1, p - 2, 0, 0]))
print('zsfix chi1 (1,1,-2,0,0), stage b: %d unknowns, %d eqs' % (len(names), len(polys)))
print('ALL TESTS PASSED' if all(res) else 'SOME TEST FAILED', res)
