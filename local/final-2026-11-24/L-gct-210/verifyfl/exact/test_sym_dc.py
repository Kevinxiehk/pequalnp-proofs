import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exactlib as X, gen_sym, gen_sym_dc, gen_n1s, gen_dc
p = 2147483629; cs = X.Consts(p); ok = True
# (1) s = 3: chart c = 0 == gen_sym chart A, chart c = 1 == chart B (up to the parameter name), on all k = 2 cases
for c, ch in ((0, 'A'), (1, 'B')):
    bad = 0
    P, Nt = gen_sym_dc.setup(3)
    for ca, cb in zip(gen_n1s.cases(2), gen_dc.cases(2, P, Nt)):
        n1, p1 = gen_sym.build(p, ch, ca); n2, p2 = gen_sym_dc.build(p, 3, c, cb)
        n2r = ['mt' if x.startswith('mp') else x for x in n2]
        if not (n1 == n2r and sorted(sorted(q.items()) for q in p1) == sorted(sorted(q.items()) for q in p2)): bad += 1
    print('(1) s = 3 chart %d vs gen_sym chart %s: mismatches %d / 96' % (c, ch, bad)); ok &= bad == 0
# (2) s = 4, chart 0, m = (1, 2, -3, 0): the exact type-V plane of m12m3 (supported on columns 0..2) satisfies its case
r7 = X.sqrtm(7, p)
cp = [1, (-3 + r7) % p, (2 - r7) % p, 0, 0]; cm = [1, (-3 - r7) % p, (2 + r7) % p, 0, 0]
def pc(M): return [M[a][t] for t in (0, 1, 2) for a in range(3)]       # dcsub([0,1,2,3]) coordinates 3t + a
rows, piv = X.rref([pc(X.outer(cs.chi1, cp, p)), pc(X.outer(cs.chi3, cm, p))], p)
P, Nt = gen_sym_dc.setup(4); case = [cc for cc in gen_dc.cases(2, P, Nt) if cc[1] == 0 and cc[2] == tuple(piv)][0]
names, polys = gen_sym_dc.build(p, 4, 0, case)
for (m1, m2), expect in (((2, p - 3), True), ((5, 7), False)):
    val = {'mp1': m1, 'mp2': m2}; free = [rows[r][d] for r in range(2) for d in range(9) if d > piv[r] and d not in piv]
    un = [n for n in names if n.startswith('u')]; assert len(un) == len(free); val.update(dict(zip(un, free)))
    vv = {i: val[n] for i, n in enumerate(names)}; sat = all(X.peval(q, vv, p) == 0 for q in polys)
    print('(2) s = 4 type-V plane at (mp1, mp2) = (%d, %d): satisfies all: %s (expected %s)' % (m1 if m1 < p // 2 else m1 - p, m2 if m2 < p // 2 else m2 - p, sat, expect)); ok &= sat == expect
print('ALL TESTS PASSED' if ok else 'SOME TEST FAILED')
