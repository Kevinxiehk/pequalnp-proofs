import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""substitution tests for gen_n1s.py"""
import exactlib as X, random, gen_n1s
p = 2147483629; cs = X.Consts(p); r7 = X.sqrtm(7, p); rnd = random.Random(7); res = []
def pcoords(M): return [M[a][t] for t in (0, 1) for a in range(3)]
def check(name, mspec, case, val_list, expect=True):
    names, polys = gen_n1s.build(p, mspec, case); assert len(names) == len(val_list), (names, len(val_list))
    val = dict(enumerate(val_list)); ok = all(X.peval(q, val, p) == 0 for q in polys)
    rv = {i: rnd.randrange(p) for i in range(len(names))}; bad = sum(1 for q in polys if X.peval(q, rv, p))
    print('%-46s m=%-6s case %s: %d unknowns, %d eqs; satisfies all: %s (expected %s); random point violates %d' % (name, mspec, case, len(names), len(polys), ok, expect, bad))
    res.append(ok == expect and bad > 0)
# type V plane: rho = 0, N_P in Gr(2,6)
cp = [1, (-3 + r7) % p, (2 - r7) % p, 0, 0]; cm = [1, (-3 - r7) % p, (2 + r7) % p, 0, 0]
rows, piv = X.rref([pcoords(X.outer(cs.chi1, cp, p)), pcoords(X.outer(cs.chi3, cm, p))], p)
vals = [rows[r][d] for r in range(2) for d in range(6) if d > piv[r] and d not in piv]
check('type V plane N_V', 'm12m3', (2, 0, tuple(piv), 0, '-', '-'), vals)
check('type V plane N_V (wrong m)', 'm11m2', (2, 0, tuple(piv), 0, '-', '-'), vals, expect=False)
# type II plane zeta (e0-e1), zetab (e3-e4): rho = 1, line (1, al), v3 = v4 = v(th0), al = -1
zb = cs.zetab; p0 = sum(a * b for a, b in zip(zb, cs.chi3)) * X.inv(4, p) % p; q0 = sum(a * b for a, b in zip(zb, cs.chi2)) * X.inv(4, p) % p; th0 = q0 * X.inv(p0, p) % p
rows, piv = X.rref([pcoords(X.outer(cs.zeta, [1, p - 1, 0, 0, 0], p))], p)
vals = [rows[0][d] for d in range(6) if d > piv[0]] + [th0, th0, p - 1] + [0] * 5      # order of creation: u..., th3, th4, al, y0_*
check('type II plane (pairs (0,1),(3,4))', 'm12m3', (2, 1, tuple(piv), 0, 'th', 'th'), vals)
check('type II plane (pairs (0,1),(3,4))', 'SL', (2, 1, tuple(piv), 0, 'th', 'th'), vals)
check('type II plane (pairs (0,1),(3,4))', 'two', (2, 1, tuple(piv), 0, 'th', 'th'), vals)
# type I plane chi_1 x Lam_{0,3,4}: rho = 2, N_P = 0: Z_1 = chi_1 (e_3 - e_0) -> column 3 = chi_1 = v(0), Z_2 = chi_1 (e_4 - e_0)
z1 = pcoords(X.outer(cs.chi1, [p - 1, 0, 0, 0, 0], p))
check('type I plane chi_1 x Lam_{0,3,4}', 'm12m3', (2, 2, (), 0, 'th', 'th'), [0, 0] + z1 + z1)
# the non-solution chi_1 x W_P + chi_3 (e_3 - e_4): k = 3, rho = 1, N_P = chi_1 x W_P, line (1, al), v3 = v4 = chi_3, al = -1
rows, piv = X.rref([pcoords(X.outer(cs.chi1, [1, p - 1, 0, 0, 0], p)), pcoords(X.outer(cs.chi1, [0, 1, p - 1, 0, 0], p))], p)
vals = [rows[r][d] for r in range(2) for d in range(6) if d > piv[r] and d not in piv] + [p - 1] + [0] * 4
check('chi_1 x W_P + chi_3 (e_3 - e_4)  [not a solution]', 'm12m3', (3, 1, tuple(piv), 0, 'c3', 'c3'), vals, expect=False)
print('ALL TESTS PASSED' if all(res) else 'SOME TEST FAILED', res)
