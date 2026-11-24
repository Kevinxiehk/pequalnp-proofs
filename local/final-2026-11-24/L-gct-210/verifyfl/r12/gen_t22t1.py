import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""gen_t22t1.py -- SYM-M [T22], rho = 1 N-cases with N_P pivot (0,) and line cell 0 (gen_n1s.cases(2) idx 9, 10, 11: v_3 = 'ab', v_4 in
   {ab, z1, z2}; Z_0 in N_P with entry (0,0) = 1, Z_1 = complement with c_3 = v_3, c_4 = al v_4, entry (0,0) = 0), PIECE (IV) vartheta == 0
   (round 12, NOTES R12.2).  As in gen_t22t0b: every c_j(N) totally isotropic => rank <= 1, isotropic image.  c_0(Z_0) has first coordinate 1,
   so c_0 = lam_0 u_0 with u_0 = (1,a,b,-1-a-b) ('ab' chart forced), lam_0(Z_0) = 1, lam_0(Z_1) = 0 (entry (0,0) of Z_1 is 0);
   c_1 = lam_1 u_1, c_2 = lam_2 u_2, u_1, u_2 in {ab, z1, z2, 0}; row sums 0 as LINEAR equations.  Gauge, S-cells, Gram as in gen_n3 (rho = 1).
   build(p, chart, ci, u1k, u2k, scell, keyed)."""
import exactlib as X, gen_n1s, gen_n3, gen_sym, gen_sym_n3
from gen_t22t0 import isovec
def nbasis_t1(p, cs, case, V, u1k, u2k):
    k, rho, piv, lc, t3, t4 = case; assert k == 2 and rho == 1 and piv == (0,) and lc == 0 and t3 == 'ab'
    extra = []
    v3, e3 = isovec(p, cs, V, t3, '3'); v4, e4 = isovec(p, cs, V, t4, '4'); extra += e3 + e4
    al = V.new('al')
    u0, f0 = isovec(p, cs, V, 'ab', 'u0'); u1, f1 = isovec(p, cs, V, u1k, 'u1'); u2, f2 = isovec(p, cs, V, u2k, 'u2'); extra += f0 + f1 + f2
    B = []
    for r in range(2):
        cols = [[{} for a in range(4)] for j in range(5)]
        if r == 0: cols[0] = [dict(x) for x in u0]
        for j, u in ((1, u1), (2, u2)):
            if u is not None:
                l = V.new('l%d%d' % (r, j)); cols[j] = [X.pmul(l, u[a], p) for a in range(4)]
        if r == 1:
            cols[3] = [dict(x) for x in v3]; cols[4] = [X.pmul(al, v4[a], p) for a in range(4)]
        for a in range(4):
            q = {}
            for j in range(5): q = X.padd(q, cols[j][a], p)
            extra.append(q)
        B.append([[cols[j][a] for j in range(5)] for a in range(4)])
    ells = [[(0, 0)], [(0, 3)]]                         # pivot entry (0,0); neutral pivot entry (vrow = 0 for 'ab', column 3)
    return B, [e for e in extra if e], ells
def build(p, chart, ci, u1k, u2k, scell, keyed=False):
    case = gen_n1s.cases(2)[ci]
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    B, extra, ells = nbasis_t1(p, cs, case, V, u1k, u2k)
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
    p = 2147483629
    for ci in (9, 10, 11): assert gen_n1s.cases(2)[ci][:4] == (2, 1, (0,), 0) and gen_n1s.cases(2)[ci][4] == 'ab', gen_n1s.cases(2)[ci]
    # the gauge entries agree with gen_n3.nbasis for these cases
    cs = X.Consts(p); V = X.Vars(); V.new('mt'); B0, ex0, ells0 = gen_n3.nbasis(p, cs, gen_n1s.cases(2)[9], V)
    V = X.Vars(); V.new('mt'); B1, ex1, ells1 = nbasis_t1(p, cs, gen_n1s.cases(2)[9], V, 'ab', 'z1')
    assert ells0 == ells1, (ells0, ells1)
    assert [[gen_n3.entry_form(M, ell, p) for M in B1] for ell in ells1] == [[{(): 1}, {}], [{}, {(): 1}]]
    print('self-check ok', gen_n1s.cases(2)[9:12])
