import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""gen_t22iso.py -- SYM-M [T22] rho = 2 N-cases (idx 0..8), PIECE (P2): vartheta(Z_1) != 0  (round 12, NOTES R12.5).
   N contains the isotropic element Z_a = alpha Z_1 + Z_2 (vartheta(alpha Z_1 + Z_2) = 0 is a quadratic in alpha with leading coefficient
   vartheta(Z_1) != 0, so it has a root); EVERY column of Z_a is isotropic ((F2) with vartheta(Z_a) = 0), so
     Z_a = [mu_0 u_0, mu_1 u_1, mu_2 u_2, alpha v_3, v_4],  u_j in {ab, z1, z2, 0},  row sums sum_j c_j(Z_a) = 0 LINEAR in (mu, alpha).
   N = span(Z_1, Z_a) (Z_1 as in gen_n3.nbasis: y0-coordinates, c_3 = v_3, c_4 = 0); gauge forms unchanged (det [[1, alpha],[0, 1]] = 1).
   Piece equations: usp * den = 1, num - t * den = 0 (den, num = |c_0(Z_1)|^2, |c_1(Z_1)|^2 in chart A; swapped in chart B).
   build(p, chart, ci, u0k, u1k, u2k, scell, keyed)."""
import exactlib as X, gen_n1s, gen_n3, gen_sym, gen_sym_n3
from gen_t22t0 import isovec
def nbasis_iso(p, cs, case, V, chart, uk):
    k, rho, piv, lc, t3, t4 = case; assert k == 2 and rho == 2 and piv == ()
    it = 0                                                     # 'mt' is variable 0
    v3, e3 = isovec(p, cs, V, t3, '3'); v4, e4 = isovec(p, cs, V, t4, '4'); extra = e3 + e4
    co = [V.new('y0_%d' % d) for d in range(6)]
    Z1 = X.dcsub_matrix(co, [0, 1, 2], p)
    for a in range(4): Z1[a][3] = X.padd(Z1[a][3], v3[a], p); Z1[a][2] = X.padd(Z1[a][2], v3[a], p, -1)
    us = [isovec(p, cs, V, uk[j], 'u%d' % j) for j in range(3)]
    for u, f in us: extra += f
    al = V.new('alp')
    cols = [[{} for a in range(4)] for j in range(5)]
    for j in range(3):
        if us[j][0] is not None:
            mu = V.new('mu%d' % j); cols[j] = [X.pmul(mu, us[j][0][a], p) for a in range(4)]
    cols[3] = [X.pmul(al, v3[a], p) for a in range(4)]; cols[4] = [dict(x) for x in v4]
    for a in range(4):
        q = {}
        for j in range(5): q = X.padd(q, cols[j][a], p)
        extra.append(q)
    Za = [[cols[j][a] for j in range(5)] for a in range(4)]
    def ip(u, v):
        q = {}
        for x, y in zip(u, v): q = X.padd(q, X.pmul(x, y, p), p)
        return q
    c = lambda M, j: [M[a][j] for a in range(4)]
    n00, n11 = ip(c(Z1, 0), c(Z1, 0)), ip(c(Z1, 1), c(Z1, 1))
    den, num = (n00, n11) if chart == 'A' else (n11, n00)
    usp = V.new('usp'); extra.append(X.padd(X.pmul(usp, den, p), X.pconst(1, p), p, -1)); extra.append(X.padd(num, X.pmul({(it,): 1}, den, p), p, -1))
    vrow = {'ab': 0, 'z1': 1, 'z2': 1}
    return [Z1, Za], [e for e in extra if e], [[(vrow[t3], 3)], [(vrow[t4], 4)]]
def build(p, chart, ci, u0k, u1k, u2k, scell, keyed=False):
    case = gen_n1s.cases(2)[ci]
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    B, extra, ells = nbasis_iso(p, cs, case, V, chart, (u0k, u1k, u2k))
    if scell is not None:
        S = gen_n3.svectors(p, scell, V)
        for r in range(2):
            co = [V.new('w%d_%d' % (r, d)) for d in range(12)]
            M = X.dc_matrix(co, p); D = [[dict(x) for x in row] for row in M]
            M = X.madd_const_col(M, S[r], 0, p)
            for ell in ells: extra.append(gen_n3.entry_form(D, ell, p))
            B.append(M)
        ip = lambda u, v: gen_n3.ip(u, v, p)
        g = X.padd(X.pmul(ip(S[0], S[0]), ip(S[1], S[1]), p), X.pmul(ip(S[0], S[1]), ip(S[0], S[1]), p), p, -1)
        if g: extra.append(g)
    extra = [e for e in extra if e]
    if keyed: return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra
    return V.names, gen_sym.equations_poly(B, Wp, p) + extra
if __name__ == '__main__':
    p = 2147483629; cs = X.Consts(p)
    V = X.Vars(); V.new('mt'); B0, _, ells0 = gen_n3.nbasis(p, cs, gen_n1s.cases(2)[0], V); n0 = V.names
    V2 = X.Vars(); V2.new('mt'); B1, _, ells1 = nbasis_iso(p, cs, gen_n1s.cases(2)[0], V2, 'A', ('ab', 'ab', 'ab'))
    ren = lambda M, names: [[X.fmt_poly(x, names) for x in row] for row in M]
    assert ren(B0[0], n0) == ren(B1[0], V2.names), 'Z_1 differs from gen_n3.nbasis'
    assert ells0 == ells1
    print('self-check ok: Z_1 = gen_n3.nbasis B[0], same gauge entries')
