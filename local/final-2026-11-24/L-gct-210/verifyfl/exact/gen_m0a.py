import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_m0a.py -- [T31] split A for m0 = (1,1,1,1,-4): the two cases of stage3's Lemma SA1 (COMPUTE-stage3 item 12)  (round 9, verifyfl).
   (beta)  all five columns of Z nonzero (isotropic, sum 0): Z-ONLY system.  z_j = c_j w(t_j), w(t) = chi_1 + 2t chi_2 - 2t^2 chi_3 (finite t_j)
           or z_j = c_j chi_3 (t_j = infinity); every nonzero isotropic vector of V is uniquely of one of these forms.  sum z_j = 0 <=>
           sum_fin c_j = 0, sum_fin c_j t_j = 0, -2 sum_fin c_j t_j^2 + sum_inf c_j = 0.  c_0 = 1 (scale; c_0 != 0 in (beta)), u prod c_j = 1.
           Equations: these, and all coefficients of R_i(xZ) (degrees 3, 4; degree 2 holds by isotropy).  INF = set of columns at infinity.
           (Contains rank-one Z = case (beta-1) as well; harmless.)
   (alpha) z_4 = 0 and l = Theta(., Z) == 0 on K: Zs in dcsub([0,1,2,3]) (echelon cell CELL; by the row symmetry and the S_4 on columns
           0..3, cell 0 suffices), <z_j,z_j> = 0 (j = 0..3), Y_r = b_r e_0^T + D(c_r) (r = 1, 2; gauge at the pivot entry), and the LINEAR
           equations <2 y_{r,j} - b_r, z_j> = 0 (j = 0..3) (= 2 m_j l(Y_r) = 0); all coefficients of R_i(x_0 Zs + x_1 Y_1 + x_2 Y_2).
   usage: python3 -I gen_m0a.py P beta INF OUT.ms  (INF e.g. '' or '04')  |  python3 -I gen_m0a.py P alpha CELL OUT.ms"""
import exactlib as X
def build_beta(p, inf, keyed=False):
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    t = {j: V.new('t%d' % j) for j in range(5) if j not in inf}
    c = {j: (X.pconst(1, p) if j == 0 else V.new('c%d' % j)) for j in range(5)}
    cols = []
    for j in range(5):
        if j in inf: vec = [X.pmul(c[j], X.pconst(x, p), p) for x in cs.chi3]
        else:
            tt = t[j]; t2 = X.pmul(tt, tt, p)
            vec = []
            for a in range(4):
                q = X.pconst(cs.chi1[a], p); q = X.padd(q, X.pmul(X.pconst(2 * cs.chi2[a], p), tt, p), p)
                q = X.padd(q, X.pmul(X.pconst((-2 * cs.chi3[a]) % p, p), t2, p), p)
                vec.append(X.pmul(c[j], q, p))
        cols.append(vec)
    Z = [[cols[j][a] for j in range(5)] for a in range(4)]
    extra = []
    s0 = {}; s1 = {}; s2 = {}
    for j in range(5):
        if j in inf: s2 = X.padd(s2, c[j], p)
        else:
            s0 = X.padd(s0, c[j], p); s1 = X.padd(s1, X.pmul(c[j], t[j], p), p)
            s2 = X.padd(s2, X.pmul(X.pconst(p - 2, p), X.pmul(c[j], X.pmul(t[j], t[j], p), p), p), p)
    extra += [q for q in (s0, s1, s2) if q]
    u = V.new('u'); pr = X.pconst(1, p)
    for j in range(1, 5): pr = X.pmul(pr, c[j], p)
    extra.append(X.padd(X.pmul(u, pr, p), X.pconst(1, p), p, -1))
    if keyed: return V.names, X.equations([Z], W, p, keyed=True), extra, [Z]
    polys, nx = X.equations([Z], W, p)
    return V.names, polys + extra
def build_alpha(p, cell, keyed=False, stage='a'):
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    P = [0, 1, 2, 3]
    row = X.echelon_rows(9, (cell,), V, 'z')[0]
    Zs = X.dcsub_matrix(row, P, p)
    a0, t0 = cell % 3, cell // 3; gidx = 4 * a0 + P[t0]
    extra = []
    for j in range(4):
        q = {}
        for a in range(4): q = X.padd(q, X.pmul(Zs[a][j], Zs[a][j], p), p)
        extra.append(q)
    bv = [[1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1]]
    B = [Zs]
    for r in range(2 if stage == 'a' else 3):
        co = [({} if d == gidx else V.new('y%d_%d' % (r, d))) for d in range(12)]
        M = X.dc_matrix(co, p); M = X.madd_const_col(M, [X.pconst(x, p) for x in bv[r]], 0, p)
        for j in range(4):
            q = {}
            for a in range(4):
                bj = X.padd(X.pmul(X.pconst(2, p), M[a][j], p), X.pconst(bv[r][a], p), p, -1)
                q = X.padd(q, X.pmul(bj, Zs[a][j], p), p)
            extra.append(q)
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
if __name__ == '__main__':
    p = int(sys.argv[1]); kind = sys.argv[2]
    if kind == 'beta': names, polys = build_beta(p, {int(ch) for ch in sys.argv[3]})
    else: names, polys = build_alpha(p, int(sys.argv[3]))
    X.write_msolve(sys.argv[4], names, p, polys); print(kind, sys.argv[3], len(names), 'vars', len(polys), 'eqs')
def build_alpha_kt(p, inf, keyed=False, nY=2):
    """(alpha) with W parametrised like (beta): z_j = k_j n_j (j = 0..3), n_j = w(t_j) or chi_3 (j in INF), z_4 = 0, k_0 = 1 (WLOG z_0 != 0 by the
    S_4 on columns 0..3; the remaining S_3 on 1..3 leaves 8 INF patterns), sum_j z_j = 0 (linear in k), k_1..k_3 may vanish.
    Y_r = b_r e_0^T + D(c_r); gauge: the chi_1-coordinate (<., chi_3>) of column 0 of Y_r is 0 (if 0 not in INF; else the chi_3-coordinate
    <., chi_1>), which is nonzero on Z.  l == 0: <2 y_{r,j} - b_r, z_j> = 0, j = 0..3.  Isotropy and vartheta(Z) = 0 hold by construction."""
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    t = {j: V.new('t%d' % j) for j in range(4) if j not in inf}
    k = {j: (X.pconst(1, p) if j == 0 else V.new('k%d' % j)) for j in range(4)}
    cols = []
    for j in range(4):
        if j in inf: vec = [X.pmul(k[j], X.pconst(x, p), p) for x in cs.chi3]
        else:
            tt = t[j]; t2 = X.pmul(tt, tt, p); vec = []
            for a in range(4):
                q = X.pconst(cs.chi1[a], p); q = X.padd(q, X.pmul(X.pconst(2 * cs.chi2[a], p), tt, p), p)
                q = X.padd(q, X.pmul(X.pconst((-2 * cs.chi3[a]) % p, p), t2, p), p); vec.append(X.pmul(k[j], q, p))
        cols.append(vec)
    cols.append([{} for _ in range(4)])
    Z = [[cols[j][a] for j in range(5)] for a in range(4)]
    extra = []; s0 = {}; s1 = {}; s2 = {}
    for j in range(4):
        if j in inf: s2 = X.padd(s2, k[j], p)
        else:
            s0 = X.padd(s0, k[j], p); s1 = X.padd(s1, X.pmul(k[j], t[j], p), p)
            s2 = X.padd(s2, X.pmul(X.pconst(p - 2, p), X.pmul(k[j], X.pmul(t[j], t[j], p), p), p), p)
    extra += [q for q in (s0, s1, s2) if q]
    gvec = cs.chi1 if 0 in inf else cs.chi3
    bv = [[1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1]]
    B = [Z]
    for r in range(nY):
        co = [V.new('y%d_%d' % (r, d)) for d in range(12)]
        M = X.dc_matrix(co, p); M = X.madd_const_col(M, [X.pconst(x, p) for x in bv[r]], 0, p)
        g = {}
        for a in range(4): g = X.padd(g, X.pmul(M[a][0], X.pconst(gvec[a], p), p), p)
        extra.append(g)
        for j in range(4):
            q = {}
            for a in range(4):
                bj = X.padd(X.pmul(X.pconst(2, p), M[a][j], p), X.pconst(bv[r][a], p), p, -1)
                q = X.padd(q, X.pmul(bj, Z[a][j], p), p)
            extra.append(q)
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def build_alpha_r1(p, vchart, keyed=False, nY=2):
    """(alpha) with RANK-ONE W = v l^T (v isotropic: vchart 'w' -> v = w(t) = chi_1 + 2t chi_2 - 2t^2 chi_3, 'c3' -> v = chi_3; l = (1, l1, l2,
    -1-l1-l2, 0), l_0 = 1 WLOG by the S_4 on columns 0..3).  Covers every (alpha) Z with at most two nonzero columns (they are rank one:
    three isotropic columns summing to 0 span a totally isotropic space) and the rank-one part of the four-column case.
    Y_r, gauge (chi_1- resp. chi_3-coordinate of column 0) and l == 0 equations as in build_alpha_kt."""
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    if vchart == 'w':
        tt = V.new('t'); t2 = X.pmul(tt, tt, p); v = []
        for a in range(4):
            q = X.pconst(cs.chi1[a], p); q = X.padd(q, X.pmul(X.pconst(2 * cs.chi2[a], p), tt, p), p)
            q = X.padd(q, X.pmul(X.pconst((-2 * cs.chi3[a]) % p, p), t2, p), p); v.append(q)
        gvec = cs.chi3
    else:
        v = [X.pconst(x, p) for x in cs.chi3]; gvec = cs.chi1
    l1, l2 = V.new('l1'), V.new('l2'); l3 = X.padd(X.padd(X.pconst(-1, p), l1, p, -1), l2, p, -1)
    l = [X.pconst(1, p), l1, l2, l3, {}]
    Z = [[X.pmul(v[a], l[j], p) for j in range(5)] for a in range(4)]
    extra = []; bv = [[1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1]]; B = [Z]
    for r in range(nY):
        co = [V.new('y%d_%d' % (r, d)) for d in range(12)]
        M = X.dc_matrix(co, p); M = X.madd_const_col(M, [X.pconst(x, p) for x in bv[r]], 0, p)
        g = {}
        for a in range(4): g = X.padd(g, X.pmul(M[a][0], X.pconst(gvec[a], p), p), p)
        extra.append(g)
        for j in range(4):
            q = {}
            for a in range(4):
                bj = X.padd(X.pmul(X.pconst(2, p), M[a][j], p), X.pconst(bv[r][a], p), p, -1)
                q = X.padd(q, X.pmul(bj, Z[a][j], p), p)
            extra.append(q)
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def build_alpha_nf(p, inf, keyed=False, nY=2, signs=None, nondeg=True):
    """(alpha) with RANK-TWO W, explicit normal form (NOTES R9.6): z_j = k_j n_j (j = 0..3) as in build_alpha_kt (k_0 = 1, all z_j != 0 for
    rank-two W), and for Y_r in K' with s(Y_r) = b_r:  y_{r,j} = (b_r + mu_{r,j} z_j + nu_r e_j g_j)/2 (j = 0..3), y_{r,4} = b_r - sum_{j<4} y_{r,j},
    g_j = (1/2) chi_2 - t_j chi_3 (finite t_j) or (1/2) chi_2 (t_j = inf), e_j^2 = 1 (e_0 = 1), mu_{r,0} = 0 (complement gauge).
    (A_j = z_j psi_j^T + e_j g_j f^T; mu_{r,j} = <psi_j, b_r>, nu_r = <f, b_r>; f = 0 is case (alpha0).)"""
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    t = {j: V.new('t%d' % j) for j in range(4) if j not in inf}
    k = {j: (X.pconst(1, p) if j == 0 else V.new('k%d' % j)) for j in range(4)}
    eps = {j: (X.pconst(1, p) if j == 0 else (V.new('e%d' % j) if signs is None else X.pconst(signs[j - 1] % p, p))) for j in range(4)}
    half = X.inv(2, p); cols = []; gs = []
    for j in range(4):
        if j in inf:
            vec = [X.pmul(k[j], X.pconst(x, p), p) for x in cs.chi3]; g = [X.pconst(half * x % p, p) for x in cs.chi2]
        else:
            tt = t[j]; t2 = X.pmul(tt, tt, p); vec = []; g = []
            for a in range(4):
                q = X.pconst(cs.chi1[a], p); q = X.padd(q, X.pmul(X.pconst(2 * cs.chi2[a], p), tt, p), p)
                q = X.padd(q, X.pmul(X.pconst((-2 * cs.chi3[a]) % p, p), t2, p), p); vec.append(X.pmul(k[j], q, p))
                g.append(X.padd(X.pconst(half * cs.chi2[a] % p, p), X.pmul(X.pconst(cs.chi3[a], p), tt, p), p, -1))
        cols.append(vec); gs.append(g)
    Z = [[(cols[j][a] if j < 4 else {}) for j in range(5)] for a in range(4)]
    extra = []; s0 = {}; s1 = {}; s2 = {}
    for j in range(4):
        if j in inf: s2 = X.padd(s2, k[j], p)
        else:
            s0 = X.padd(s0, k[j], p); s1 = X.padd(s1, X.pmul(k[j], t[j], p), p)
            s2 = X.padd(s2, X.pmul(X.pconst(p - 2, p), X.pmul(k[j], X.pmul(t[j], t[j], p), p), p), p)
    extra += [q for q in (s0, s1, s2) if q]
    if signs is None:
        for j in range(1, 4): extra.append(X.padd(X.pmul(eps[j], eps[j], p), X.pconst(1, p), p, -1))
    if nondeg:   # rank-two W: all k_j != 0, and (all-finite chart) WLOG t_1 != t_0 by the S_3 on columns 1..3 [other charts: automatic]
        if 0 in inf and 1 in inf and 2 in inf and 3 in inf: extra.append(X.pconst(1, p))      # all at infinity: W rank one -> empty here
        pr = X.pmul(X.pmul(k[1], k[2], p), k[3], p)
        if not inf: pr = X.pmul(pr, X.padd(t[1], t[0], p, -1), p)
        u = V.new('unz'); extra.append(X.padd(X.pmul(u, pr, p), X.pconst(1, p), p, -1))
    bv = [[1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1]]; B = [Z]
    for r in range(nY):
        mu = {j: ({} if j == 0 else V.new('mu%d_%d' % (r, j))) for j in range(4)}; nu = V.new('nu%d' % r)
        M = [[{} for _ in range(5)] for _ in range(4)]
        for a in range(4):
            tot = {}
            for j in range(4):
                e = X.pconst(bv[r][a], p)
                e = X.padd(e, X.pmul(mu[j], cols[j][a], p), p)
                e = X.padd(e, X.pmul(X.pmul(nu, eps[j], p), gs[j][a], p), p)
                e = X.pmul(X.pconst(half, p), e, p); M[a][j] = e; tot = X.padd(tot, e, p)
            M[a][4] = X.padd(X.pconst(bv[r][a], p), tot, p, -1)
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def build_alpha_s(p, inf, scell, keyed=False, nondeg=True):
    """(alpha), RANK-TWO W, plane-adapted form (NOTES R10.2): with A_j = z_j psi_j^T + e_j g_j f^T (R9.6), every s in f^perp has
    A_j s = <psi_j,s> z_j.  Choose Y_1, Y_2 in K' with s(Y_1), s(Y_2) spanning a plane S c f^perp (S = f^perp if f != 0; any plane if f = 0),
    S in one of the three cells of Gr(2,V) (gen_n3.svectors).  Then y_{r,j} = (s_r + mu_{r,j} z_j)/2 (j < 4), y_{r,4} = s_r - sum_{j<4} y_{r,j},
    mu_{r,0} = 0 (complement gauge psi -> psi + 2 lam, solvable for both r as s_1, s_2 are independent).  W as in build_alpha_kt (k_0 = 1),
    nondeg: k_1 k_2 k_3 != 0 and (all-finite chart) t_1 != t_0 [rank two; WLOG by S_3 on columns 1..3]."""
    import gen_n3
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    t = {j: V.new('t%d' % j) for j in range(4) if j not in inf}
    k = {j: (X.pconst(1, p) if j == 0 else V.new('k%d' % j)) for j in range(4)}
    cols = []
    for j in range(4):
        if j in inf: vec = [X.pmul(k[j], X.pconst(x, p), p) for x in cs.chi3]
        else:
            tt = t[j]; t2 = X.pmul(tt, tt, p); vec = []
            for a in range(4):
                q = X.pconst(cs.chi1[a], p); q = X.padd(q, X.pmul(X.pconst(2 * cs.chi2[a], p), tt, p), p)
                q = X.padd(q, X.pmul(X.pconst((-2 * cs.chi3[a]) % p, p), t2, p), p); vec.append(X.pmul(k[j], q, p))
        cols.append(vec)
    Z = [[(cols[j][a] if j < 4 else {}) for j in range(5)] for a in range(4)]
    extra = []; s0 = {}; s1 = {}; s2 = {}
    for j in range(4):
        if j in inf: s2 = X.padd(s2, k[j], p)
        else:
            s0 = X.padd(s0, k[j], p); s1 = X.padd(s1, X.pmul(k[j], t[j], p), p)
            s2 = X.padd(s2, X.pmul(X.pconst(p - 2, p), X.pmul(k[j], X.pmul(t[j], t[j], p), p), p), p)
    extra += [q for q in (s0, s1, s2) if q]
    if nondeg:
        if len(inf) == 4: extra.append(X.pconst(1, p))
        pr = X.pmul(X.pmul(k[1], k[2], p), k[3], p)
        if not inf: pr = X.pmul(pr, X.padd(t[1], t[0], p, -1), p)
        u = V.new('unz'); extra.append(X.padd(X.pmul(u, pr, p), X.pconst(1, p), p, -1))
    S = gen_n3.svectors(p, scell, V)
    half = X.inv(2, p); B = [Z]
    for r in range(2):
        mu = {j: ({} if j == 0 else V.new('mu%d_%d' % (r, j))) for j in range(4)}
        M = [[{} for _ in range(5)] for _ in range(4)]
        for a in range(4):
            tot = {}
            for j in range(4):
                e = X.pmul(X.pconst(half, p), X.padd(S[r][a], X.pmul(mu[j], cols[j][a], p), p), p); M[a][j] = e; tot = X.padd(tot, e, p)
            M[a][4] = X.padd(S[r][a], tot, p, -1)
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def _iso(cs, p, V, chart, name):
    """isotropic vector of V in chart 'w' (w(t), new variable) or 'c3' (chi_3); returns (vector, g) with g the norm-1 partner in v^perp."""
    half = X.inv(2, p)
    if chart == 'c3': return [X.pconst(x, p) for x in cs.chi3], [X.pconst(half * x % p, p) for x in cs.chi2]
    tt = V.new(name); t2 = X.pmul(tt, tt, p); v = []; g = []
    for a in range(4):
        q = X.pconst(cs.chi1[a], p); q = X.padd(q, X.pmul(X.pconst(2 * cs.chi2[a], p), tt, p), p)
        q = X.padd(q, X.pmul(X.pconst((-2 * cs.chi3[a]) % p, p), t2, p), p); v.append(q)
        g.append(X.padd(X.pconst(half * cs.chi2[a] % p, p), X.pmul(X.pconst(cs.chi3[a], p), tt, p), p, -1))
    return v, g
def build_alpha_r1s(p, vchart, nzero, scell, ncharts=(), keyed=False):
    """(alpha), RANK-ONE W = v l^T, plane-adapted form (NOTES R10.6).  l = (1, l1, l2, l3, 0): nzero = 0 (l1 l2 l3 != 0), 1 (l3 = 0,
    l = (1, l1, -1-l1, 0, 0), l1 (1 + l1) != 0) or 2 (l = (1, -1, 0, 0, 0)) [WLOG by the S_3 on columns 1..3].  Y_r in K' with s(Y_r) = s_r
    spanning a plane S c f^perp (S-cell): columns j with l_j != 0: (s_r + mu_{r,j} v)/2 (mu_{r,0} = 0, complement gauge); zero columns j:
    (s_r + nu_{r,j} n_j)/2 with n_j isotropic (chart ncharts[i] in {'w','c3'}); column 4 = s_r - sum_{j<4}."""
    import gen_n3
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    v, g = _iso(cs, p, V, vchart, 't')
    one = X.pconst(1, p); extra = []
    if nzero == 0:
        l1, l2 = V.new('l1'), V.new('l2'); l3 = X.padd(X.padd(X.pconst(-1, p), l1, p, -1), l2, p, -1); l = [one, l1, l2, l3]
        u = V.new('unz'); extra.append(X.padd(X.pmul(u, X.pmul(X.pmul(l1, l2, p), l3, p), p), one, p, -1))
    elif nzero == 1:
        l1 = V.new('l1'); l2 = X.padd(X.pconst(-1, p), l1, p, -1); l = [one, l1, l2, {}]
        u = V.new('unz'); extra.append(X.padd(X.pmul(u, X.pmul(l1, l2, p), p), one, p, -1))
    else: l = [one, X.pconst(p - 1, p), {}, {}]
    zero_cols = [j for j in range(4) if not l[j]]
    nvec = {j: _iso(cs, p, V, ncharts[i], 'tn%d' % j)[0] for i, j in enumerate(zero_cols)}
    Z = [[(X.pmul(v[a], l[j], p) if j < 4 else {}) for j in range(5)] for a in range(4)]
    S = gen_n3.svectors(p, scell, V); half = X.inv(2, p); B = [Z]
    for r in range(2):
        M = [[{} for _ in range(5)] for _ in range(4)]
        coef = {}
        for j in range(4):
            if l[j]: coef[j] = ({} if j == 0 else V.new('mu%d_%d' % (r, j))), v
            else: coef[j] = V.new('nu%d_%d' % (r, j)), nvec[j]
        for a in range(4):
            tot = {}
            for j in range(4):
                c, vec = coef[j]
                e = X.pmul(X.pconst(half, p), X.padd(S[r][a], X.pmul(c, vec[a], p), p), p); M[a][j] = e; tot = X.padd(tot, e, p)
            M[a][4] = X.padd(S[r][a], tot, p, -1)
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def build_alpha_r2s(p, c1, c2, scell, keyed=False):
    """(alpha), RANK-TWO W, structured (NOTES R10.7): four nonzero isotropic columns spanning a 2-dim U lie on the (at most) two isotropic
    lines of U, two opposite columns per line, so (S_4 on columns 0..3) W = u_1 (e_0 - e_1)^T + k u_2 (e_2 - e_3)^T, u_i isotropic
    (charts c1, c2 in {'w','c3'}), u_1, u_2 independent, k != 0.  On a plane S c f^perp: A_j(S) c C z_j (l-equations + P_1 rank <= 1), so
    y_{r,0} = s_r/2 (gauge), y_{r,1} = (s_r + mu_{r,1} u_1)/2, y_{r,2} = (s_r + mu_{r,2} u_2)/2, y_{r,3} = (s_r + mu_{r,3} u_2)/2, y_{r,4} = s_r - sum."""
    import gen_n3
    cs = X.Consts(p); m, W = X.parse_m('1,1,1,1,-4', cs); V = X.Vars()
    u1, g1 = _iso(cs, p, V, c1, 't1'); u2, g2 = _iso(cs, p, V, c2, 't2')
    k = V.new('kk'); one = X.pconst(1, p); extra = []
    nz = k
    if c1 == 'w' and c2 == 'w': nz = X.pmul(k, X.padd(V and {(V.names.index('t1'),): 1}, {(V.names.index('t2'),): 1}, p, -1), p)
    if c1 == 'c3' and c2 == 'c3': extra.append(one)                # u_1 = u_2 line: rank one, excluded here
    u = V.new('unz'); extra.append(X.padd(X.pmul(u, nz, p), one, p, -1))
    ku2 = [X.pmul(k, x, p) for x in u2]
    cols = [u1, [X.pmul(X.pconst(p - 1, p), x, p) for x in u1], ku2, [X.pmul(X.pconst(p - 1, p), x, p) for x in ku2]]
    Z = [[(cols[j][a] if j < 4 else {}) for j in range(5)] for a in range(4)]
    S = gen_n3.svectors(p, scell, V); half = X.inv(2, p); B = [Z]
    for r in range(2):
        mu = {0: {}, 1: V.new('mu%d_1' % r), 2: V.new('mu%d_2' % r), 3: V.new('mu%d_3' % r)}
        dirs = {0: u1, 1: u1, 2: u2, 3: u2}
        M = [[{} for _ in range(5)] for _ in range(4)]
        for a in range(4):
            tot = {}
            for j in range(4):
                e = X.pmul(X.pconst(half, p), X.padd(S[r][a], X.pmul(mu[j], dirs[j][a], p), p), p); M[a][j] = e; tot = X.padd(tot, e, p)
            M[a][4] = X.padd(S[r][a], tot, p, -1)
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
