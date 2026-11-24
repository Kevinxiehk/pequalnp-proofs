import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""substitution tests for gen_n3.py ([T22]); positive control = the exact two-column space K_2 (DI5-R6 H1), m = (1,-1,0,0,0)"""
import exactlib as X, random, gen_n1s, gen_n3
p = 2147483629; cs = X.Consts(p); rnd = random.Random(13); res = []
zeta, zb, h, w = cs.zeta, cs.zetab, cs.h, cs.w
def check(name, mspec, case, scell, valbyname, expect, **kw):
    names, polys = gen_n3.build(p, mspec, case, scell, **kw)
    assert len(set(names)) == len(names), 'duplicate variable names'
    val = {i: valbyname[n] for i, n in enumerate(names)}; ok = all(X.peval(q, val, p) == 0 for q in polys)
    rv = {i: rnd.randrange(p) for i in range(len(names))}; bad = sum(1 for q in polys if X.peval(q, rv, p))
    print('%-46s m=%-6s case %s s%d: %d unknowns, %d eqs; satisfies all: %s (expected %s); random violates %d' % (name, mspec, case, scell, len(names), len(polys), ok, expect, bad))
    res.append(ok == expect and bad > 0)
Z0 = X.outer(zeta, [1, p - 1, 0, 0, 0], p); Z1 = X.msum(X.outer(zb, [0, 0, 0, 1, 0], p), X.outer(zb, [0, 0, 1, 0, 0], p), p, -1)
val = {}
co = [Z0[a][t] for t in (0, 1) for a in range(3)]; assert co[0] == 1
for d in range(1, 6): val['u0_%d' % d] = co[d]
val.update({'a3': zb[1], 'b3': zb[2], 'a4': zb[1], 'b4': zb[2], 'al': 0})
for d in range(1, 6): val['y0_%d' % d] = 0
# S = span(zb, h) in scell 0: s1 = b1 + al b3, s2 = b2 + be b3 ; coordinates of x in basis b: c1 = x0, c2 = x0 + x1, c3 = -x3
def bco(x): return [x[0] % p, (x[0] + x[1]) % p, (-x[3]) % p]
rows, piv = X.rref([bco(zb), bco(h)], p); assert piv == [0, 1]
sal, sbe = rows[0][2], rows[1][2]; val['sal'] = sal; val['sbe'] = sbe
s = [[(1 * bb + sal * cc) % p for bb, cc in zip([1, p - 1, 0, 0], [0, 0, 1, p - 1])], [(bb + sbe * cc) % p for bb, cc in zip([0, 1, p - 1, 0], [0, 0, 1, p - 1])]]
for r in range(2):
    # s_r = al*zb + be*h : solve from coordinates 3 (zb_3 = 0, h_3 = -3) and 0
    be_ = s[r][3] * X.inv(p - 3, p) % p; al_ = (s[r][0] - be_ * h[0]) * X.inv(zb[0], p) % p
    assert all((al_ * zb[a] + be_ * h[a] - s[r][a]) % p == 0 for a in range(4))
    Y = X.msum(X.outer([al_ * x % p for x in zb], [0, 0, 1, 0, 0], p), X.outer([be_ * x % p for x in h], [0, 0, 0, 1, 0], p), p)
    D = X.msum(Y, X.outer(s[r], [1, 0, 0, 0, 0], p), p, -1)
    c0 = D[0][0]; D = X.msum(D, [[c0 * x % p for x in row] for row in Z0], p, -1)
    c1 = D[0][3]; D = X.msum(D, [[c1 * x % p for x in row] for row in Z1], p, -1)
    assert D[0][0] == 0 and D[0][3] == 0
    for a in range(3):
        for q in range(4): val['w%d_%d' % (r, 4 * a + q)] = D[a][q]
case = (2, 1, (0,), 0, 'ab', 'ab')
check('K_2 (type (2,2), two-column control)', 'two', case, 0, val, True)
check('K_2 point with m = (1,2,-3,0,0)  [must fail]', 'm12m3', case, 0, val, False)
v2 = dict(val); v2['sal'] = (sal + 1) % p
check('K_2 point with perturbed S  [must fail]', 'two', case, 0, v2, False)
print('ALL TESTS PASSED' if all(res) else 'SOME TEST FAILED', res)
