import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""gen_t22t0.py -- SYM-M [T22], rho = 2 N-cases (gen_n1s.cases(2) idx 0..8: N_P = 0, neutral columns 3, 4 active with charts t3, t4),
   PIECE (IV): vartheta == 0 on N  (round 12, NOTES R12.2).
   (F2) on N: |c_j(Z)|^2 = vartheta(Z) m_j for every column map c_j: N -> V (V = sum-zero vectors of C^4, a 3-dim nondegenerate quadratic
   space).  vartheta == 0 <=> every c_j(N) is totally isotropic <=> (dim V = 3) every c_j has rank <= 1 with isotropic image.
   PARAMETRISATION (complete for piece IV): c_0 = lam_0 u_0, c_1 = lam_1 u_1 with u_j in {'ab': (1,a,b,-1-a-b) + isotropy, 'z1': (0,1,w,w^2),
   'z2': (0,1,w^2,w), '0'}, lam_j = linear forms on N (values lam_rj on Z_1, Z_2); c_3, c_4 as in gen_n3.nbasis (Z_1: (v_3, 0), Z_2: (0, v_4));
   c_2 = -(c_0 + c_1 + c_3 + c_4) (row sums 0) and c_2(N) totally isotropic: |c_2(Z_1)|^2 = |c_2(Z_2)|^2 = <c_2(Z_1), c_2(Z_2)> = 0.
   The gauge (ell = neutral pivot entries), S-cells and Gram equation (F4) are those of gen_n3/gen_sym_n3 (rho = 2).
   build(p, chart, ci, u0, u1, scell, keyed) -> (names, eqs, extra); scell = None gives the N-system only (x-indices 0, 1)."""
import exactlib as X, gen_n1s, gen_n3, gen_sym, gen_sym_n3
def isovec(p, cs, V, kind, nm):
    if kind == 'ab':
        a = V.new('a' + nm); b = V.new('b' + nm); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
        q = X.pconst(1, p)
        for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
        return [X.pconst(1, p), a, b, last], [q]
    if kind == 'z1': return [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)], []
    if kind == 'z2': return [X.pconst(c, p) for c in (0, 1, cs.w * cs.w % p, cs.w)], []
    return None, []
def nbasis_t0(p, cs, case, V, u0k, u1k):
    k, rho, piv, lc, t3, t4 = case; assert k == 2 and rho == 2 and piv == ()
    extra = []
    v3, e3 = isovec(p, cs, V, t3, '3'); v4, e4 = isovec(p, cs, V, t4, '4'); extra += e3 + e4
    u0, f0 = isovec(p, cs, V, u0k, 'u0'); u1, f1 = isovec(p, cs, V, u1k, 'u1'); extra += f0 + f1
    vrow = {'ab': 0, 'z1': 1, 'z2': 1}
    B = []
    for r in range(2):
        cols = [[{} for a in range(4)] for j in range(5)]
        if u0 is not None:
            l = V.new('l%d0' % r); cols[0] = [X.pmul(l, u0[a], p) for a in range(4)]
        if u1 is not None:
            l = V.new('l%d1' % r); cols[1] = [X.pmul(l, u1[a], p) for a in range(4)]
        if r == 0: cols[3] = [dict(x) for x in v3]
        else: cols[4] = [dict(x) for x in v4]
        cols[2] = [{} for a in range(4)]
        for j in (0, 1, 3, 4):
            cols[2] = [X.padd(cols[2][a], cols[j][a], p, -1) for a in range(4)]
        B.append([[cols[j][a] for j in range(5)] for a in range(4)])
    c2 = [[B[r][a][2] for a in range(4)] for r in range(2)]
    extra += [gen_n3.ip(c2[0], c2[0], p), gen_n3.ip(c2[1], c2[1], p), gen_n3.ip(c2[0], c2[1], p)]
    ells = [[(vrow[t3], 3)], [(vrow[t4], 4)]]
    return B, [e for e in extra if e], ells
def build(p, chart, ci, u0k, u1k, scell, keyed=False):
    case = gen_n1s.cases(2)[ci]
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    B, extra, ells = nbasis_t0(p, cs, case, V, u0k, u1k)
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
    # self-check: every generator is doubly centred, the gauge matrix is the identity, and vartheta == 0 holds on N symbolically
    p = 2147483629
    for u0k in ('ab', 'z1', '0'):
        for u1k in ('ab', 'z2', '0'):
            cs = X.Consts(p); V = X.Vars(); V.new('mt'); B, ex, ells = nbasis_t0(p, cs, gen_n1s.cases(2)[0], V, u0k, u1k)
            for M in B:
                for a in range(4): assert not X.padd(X.padd(X.padd(M[a][0], M[a][1], p), X.padd(M[a][2], M[a][3], p), p), M[a][4], p)
                for j in range(5):
                    s = {}
                    for a in range(4): s = X.padd(s, M[a][j], p)
                    assert not s
            assert [[gen_n3.entry_form(M, ell, p) for M in B] for ell in ells] == [[{(): 1}, {}], [{}, {(): 1}]]
    print('self-check ok')
