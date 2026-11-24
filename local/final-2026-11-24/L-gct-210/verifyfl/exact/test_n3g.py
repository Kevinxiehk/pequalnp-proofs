import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""tests for gen_n3g.py: (1) identical to gen_n3.py for m = (1,2,-3,0,0) on all 96 N-cases x 3 S-cells; (2) the exact two-column
control K_2 satisfies every equation of its case when the defect line (1,-1,0,0,0) is treated with THREE neutral columns (gen_dc: P = {0,1})."""
import exactlib as X, random, gen_n1s, gen_n3, gen_n3g, gen_dc
p = 2147483629; cs = X.Consts(p); ok = True
A = gen_n1s.cases(2); cs_, m, W, P, Nt = gen_dc.setup(p, 'm12m3'); Bc = gen_dc.cases(2, P, Nt); bad = 0
SAMPLE = [(i, s) for i in range(0, 96, 6) for s in (0, 2)] + [(9, 1), (11, 1), (57, 0), (83, 1)]   # (full comparison > 10 min)
for i, s in SAMPLE:
    ca, cb = A[i], Bc[i]
    if True:
        n1, p1 = gen_n3.build(p, 'm12m3', ca, s); n2, p2 = gen_n3g.build(p, 'm12m3', cb, s)
        if not (n1 == n2 and sorted(sorted(q.items()) for q in p1) == sorted(sorted(q.items()) for q in p2)): bad += 1
print('(1) gen_n3g vs gen_n3, m12m3: %d sampled systems, mismatches %d' % (len(SAMPLE), bad)); ok &= bad == 0
# (2) K_2 with Nt = {2,3,4}
zeta, zb, h = cs.zeta, cs.zetab, cs.h
cs_, m, W, P, Nt = gen_dc.setup(p, 'two'); assert P == [0, 1] and Nt == [2, 3, 4]
cands = [c for c in gen_dc.cases(2, P, Nt) if c[1] == 1 and c[2] == (0,) and c[3] == (0,) and dict(c[4]).get(0) == 'ab' and dict(c[4]).get(1) == 'ab' and dict(c[4]).get(2) == 'ab']
case = cands[0]; names, polys = gen_n3g.build(p, 'two', case, 0)
Z0 = X.outer(zeta, [1, p - 1, 0, 0, 0], p); Z1 = X.msum(X.outer(zb, [0, 0, 1, 0, 0], p), X.outer(zb, [0, 0, 0, 1, 0], p), p, -1)   # zb (e2 - e3)
val = {'u0_1': zeta[1], 'u0_2': zeta[2], 'a2': zb[1], 'b2': zb[2], 'a3': zb[1], 'b3': zb[2], 'a4': zb[1], 'b4': zb[2],
       'al0_1': p - 1, 'al0_2': 0}
for d in range(1, 3): val['y0_%d' % d] = 0
def bco(x): return [x[0] % p, (x[0] + x[1]) % p, (-x[3]) % p]
rows, piv = X.rref([bco(zb), bco(h)], p); sal, sbe = rows[0][2], rows[1][2]; val['sal'] = sal; val['sbe'] = sbe
S = [[(bb + sal * cc) % p for bb, cc in zip([1, p - 1, 0, 0], [0, 0, 1, p - 1])], [(bb + sbe * cc) % p for bb, cc in zip([0, 1, p - 1, 0], [0, 0, 1, p - 1])]]
for r in range(2):
    be_ = S[r][3] * X.inv(p - 3, p) % p; al_ = (S[r][0] - be_ * h[0]) % p
    Y = X.msum(X.outer([al_ * x % p for x in zb], [0, 0, 1, 0, 0], p), X.outer([be_ * x % p for x in h], [0, 0, 0, 1, 0], p), p)
    D = X.msum(Y, X.outer(S[r], [1, 0, 0, 0, 0], p), p, -1)
    c0 = D[0][0]; D = X.msum(D, [[c0 * x % p for x in row] for row in Z0], p, -1)       # ell_0 = entry (0,0)
    c1 = D[0][2]; D = X.msum(D, [[c1 * x % p for x in row] for row in Z1], p, -1)       # ell_1 = entry (0, Nt[0] = 2)
    for a in range(3):
        for q in range(4): val['w%d_%d' % (r, 4 * a + q)] = D[a][q]
missing = [n for n in names if n not in val]; assert not missing, missing
vv = {i: val[n] for i, n in enumerate(names)}
sat = all(X.peval(q, vv, p) == 0 for q in polys)
rnd = random.Random(3); rv = {i: rnd.randrange(p) for i in range(len(names))}; viol = sum(1 for q in polys if X.peval(q, rv, p))
print('(2) K_2 in gen_n3g with Nt = {2,3,4}, case %s: %d unknowns, %d eqs, satisfies all: %s; random point violates %d' % (case, len(names), len(polys), sat, viol))
ok &= sat and viol > 0
print('ALL TESTS PASSED' if ok else 'SOME TEST FAILED')
