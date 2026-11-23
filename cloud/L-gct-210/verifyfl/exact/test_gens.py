import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""Substitution tests of the generators (no Groebner engine needed): known spaces must satisfy every generated equation of their cell,
   random points of the same cell must not."""
import exactlib as X, random, itertools
import gen_n1
def pick_prime():
    for p in (2147483629, 2147483497, 2147483077, 2147483053, 2147482921, 2147482873):
        if p % 12 == 1 and pow(7, (p - 1) // 2, p) == 1: return p
p = pick_prime(); cs = X.Consts(p); r7 = X.sqrtm(7, p); rnd = random.Random(5)
def col(v, cvec): return X.outer(v, cvec, p)
def test_dc(name, mspec, basis, expect=True):
    co = [X.dc_coords(M, p) for M in basis]; rows, piv = X.rref(co, p); k = len(rows); assert k == len(basis)
    names, polys = gen_n1.build(p, mspec, k, 'dc', tuple(piv))
    val = {}; it = 0
    for r, pr in enumerate(piv):
        for d in range(12):
            if d != pr and d not in piv and d > pr: val[it] = rows[r][d]; it += 1
            else: assert rows[r][d] == (1 if d == pr else 0)
    assert it == len(names)
    ok = all(X.peval(q, val, p) == 0 for q in polys)
    rv = {i: rnd.randrange(p) for i in range(len(names))}; bad = sum(1 for q in polys if X.peval(q, rv, p))
    print('[DC-%d] %-34s m=%-6s cell %s: %d unknowns, %d equations; known space satisfies all: %s (expected %s); random point violates %d' % (
        k, name, mspec, tuple(piv), len(names), len(polys), ok, expect, bad))
    return ok == expect and bad > 0
res = []
cp = [1, (-3 + r7) % p, (2 - r7) % p, 0, 0]; cm = [1, (-3 - r7) % p, (2 + r7) % p, 0, 0]
NV = [col(cs.chi1, cp), col(cs.chi3, cm)]
res.append(test_dc('type V plane N_V', 'm12m3', NV))
res.append(test_dc('type V plane of (1,2,-3) with wrong m', 'm11m2', NV, expect=False))
res.append(test_dc('type I plane chi_1 x Lam_{0,1,3}', 'm12m3', [col(cs.chi1, [1, p - 1, 0, 0, 0]), col(cs.chi1, [0, 1, 0, p - 1, 0])]))
res.append(test_dc('type II plane', 'm12m3', [col(cs.zeta, [1, p - 1, 0, 0, 0]), col(cs.zetab, [0, 0, 0, 1, p - 1])]))
res.append(test_dc('type II plane', 'SL', [col(cs.zeta, [1, p - 1, 0, 0, 0]), col(cs.zetab, [0, 0, 0, 1, p - 1])]))
res.append(test_dc('type V plane (not strongly level)', 'SL', NV, expect=False))
mb = [1, cs.w * cs.w % p, cs.w, 0, 0]
res.append(test_dc('U_2 x (1/m), isotropic m', 'iso', [col([1, 0, p - 1, 0], mb), col([0, 1, 0, p - 1], mb)]))
res.append(test_dc('three-dim: type I plane + chi_3 (e_3-e_4) [not a solution]', 'm12m3',
                   [col(cs.chi1, [1, p - 1, 0, 0, 0]), col(cs.chi1, [0, 1, p - 1, 0, 0]), col(cs.chi3, [0, 0, 0, 1, p - 1])], expect=False))
# 3col mode: chi_1 x C^{0,1,2} (strongly level, 3-dim)
names, polys = gen_n1.build(p, 'm12m3', 3, '3col', (0, 3, 6))
# coordinates 3q+a = entry (a,q): chi_1 e_q^T has coords (chi1[0],chi1[1],chi1[2]) in block q -> rref pivots (0,3,6), free values chi1[1], chi1[2]
val = {}; it = 0
for r in range(3):
    for d in range(9):
        if d > 3 * r and d not in (0, 3, 6):
            val[it] = (cs.chi1[d - 3 * r] if d < 3 * r + 3 else 0); it += 1
ok = all(X.peval(q, val, p) == 0 for q in polys); print('[3col k=3] chi_1 x C^P: %d unknowns, %d equations, satisfies all: %s' % (len(names), len(polys), ok)); res.append(ok)
print('prime', p, 'ALL TESTS PASSED' if all(res) else 'SOME TEST FAILED', res)
