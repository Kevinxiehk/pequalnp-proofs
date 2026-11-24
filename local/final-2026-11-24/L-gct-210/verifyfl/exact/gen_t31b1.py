import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_t31b1.py -- [T31] split B1 (vartheta(Z) != 0, omega != 0) in THREE-COLUMN normal form  (round 9, verifyfl; NOTES R9.2).
   |supp m| = 3 on columns 0,1,2 (any such m; distinct entries NOT needed).  Facts (char p > 3): K' = {Theta(.,Z) = 0} complement of C Z,
   s : K' -> V bijective, y_n = M_n s on K' (n = 3, 4), and the t^3-coefficient of (C4'_n) gives M_n^* omega = 0, A_n = 2 M_n - 1
   orthogonal, so A_n omega = -omega and M_n omega = 0: the element Y_omega of K' with s = omega has y_3 = y_4 = 0.  Hence (B1)
   K' contains a nonzero THREE-COLUMN element Y3 (s(Y3) = x != 0).
   Unknowns:  Z = (z_0, z_1, -z_0-z_1, 0, 0), vartheta(Z) = 1 (<z_j,z_j> = m_j);
              Y3: x in an echelon cell of P(V) w.r.t. b_1, b_2, b_3 (xcell 0: b_1 + al b_2 + be b_3; 1: b_2 + al b_3; 2: b_3),
                  columns y_0, y_1 in V free, y_2 = x - y_0 - y_1, y_3 = y_4 = 0, Theta(Y3, Z) = 0;
              Y1: s(Y1) = b_r' with b_r' not proportional to x (xcell 0: b_3, xcells 1, 2: b_1), Theta(Y1, Z) = 0.
   Theta(Y, Z) = (2 <y_0, z_0> - <s(Y), z_0>) / (2 m_0)  (polarised (C2') in column 0).
   par=True (default): Y3 = Y_omega, i.e. x parallel to omega (2 equations per x-cell); complete since Y_omega exists in B1.
   Optional: omega != 0 chart u (c_i - c_0) = 1 (i = 1, 2, 3), c_i = perm of z_0, z_1, z_2 on the rows != i.
   Equations: all coefficients of R_i(x_Z Z + x_3 Y3 + x_1 Y1) + the extras above.   B = [Z, Y3, Y1]."""
import exactlib as X, itertools
def build(p, mspec, xcell, omchart=None, keyed=False, with_y1=True, par=True, xomega=False):
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs)
    assert m[3] == 0 and m[4] == 0 and all(m[j] for j in range(3))
    V = X.Vars()
    def vvec(nm):
        a, b, c = V.new(nm + 'a'), V.new(nm + 'b'), V.new(nm + 'c')
        return [a, b, c, X.padd(X.padd(X.pmul(a, X.pconst(-1, p), p), b, p, -1), c, p, -1)]
    def dot(u, v):
        q = {}
        for a, b in zip(u, v): q = X.padd(q, X.pmul(a, b, p), p)
        return q
    neg = lambda u: [X.pmul(X.pconst(-1, p), a, p) for a in u]
    add = lambda u, v: [X.padd(a, b, p) for a, b in zip(u, v)]
    bvec = [[X.pconst(c, p) for c in v] for v in ([1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1])]
    zero = [{} for _ in range(4)]
    z0, z1 = vvec('Za'), vvec('Zb'); z2 = neg(add(z0, z1)); zc = [z0, z1, z2, zero, zero]
    extra = [X.padd(dot(zc[j], zc[j]), X.pconst(m[j], p), p, -1) for j in range(3)]
    cvec0 = []
    for i in range(4):
        rows = [r for r in range(4) if r != i]; q = {}
        for f in itertools.permutations(range(3)):
            term = X.pconst(1, p)
            for r, c in zip(rows, f): term = X.pmul(term, zc[c][r], p)
            q = X.padd(q, term, p)
        cvec0.append(q)
    sc0 = {}
    for q in cvec0: sc0 = X.padd(sc0, q, p)
    omV = [X.padd(cvec0[i], X.pmul(X.pconst(X.inv(4, p), p), sc0, p), p, -1) for i in range(4)]
    # Y3
    if xomega: x = omV; rp = xcell; par = False                  # Y3 = Y_omega exactly (s = omega); Y1 gets s = b_{xcell} (no scale freedom)
    elif xcell == 0: al, be = V.new('xal'), V.new('xbe'); x = add(bvec[0], add([X.pmul(al, c, p) for c in bvec[1]], [X.pmul(be, c, p) for c in bvec[2]])); rp = 2
    elif xcell == 1: al = V.new('xal'); x = add(bvec[1], [X.pmul(al, c, p) for c in bvec[2]]); rp = 0
    elif xcell == 2: x = bvec[2]; rp = 0
    y0, y1 = vvec('Ua'), vvec('Ub'); y2 = add(x, neg(add(y0, y1)))
    Y3c = [y0, y1, y2, zero, zero]
    Y3 = [[Y3c[j][a] for j in range(5)] for a in range(4)]
    extra.append(X.padd(X.pmul(X.pconst(2, p), dot(y0, z0), p), dot(x, z0), p, -1))           # Theta(Y3, Z) = 0
    B = [[[zc[j][a] for j in range(5)] for a in range(4)], Y3]
    if with_y1:
        co = [V.new('w%d' % d) for d in range(12)]
        M = X.dc_matrix(co, p); M = X.madd_const_col(M, bvec[rp], 0, p)
        col0 = [M[a][0] for a in range(4)]
        extra.append(X.padd(X.pmul(X.pconst(2, p), dot(col0, z0), p), dot(bvec[rp], z0), p, -1))  # Theta(Y1, Z) = 0
        B.append(M)
    cvec = []
    if omchart is not None or par:
        cvec = []
        for i in range(4):
            rows = [r for r in range(4) if r != i]; q = {}
            for f in itertools.permutations(range(3)):
                term = X.pconst(1, p)
                for r, c in zip(rows, f): term = X.pmul(term, zc[c][r], p)
                q = X.padd(q, term, p)
            cvec.append(q)
        if omchart is not None:
            u = V.new('uom'); extra.append(X.padd(X.pmul(u, X.padd(cvec[omchart], cvec[0], p, -1), p), X.pconst(1, p), p, -1))
        if par:
            # Y3 = Y_omega: x parallel to omega = V-part of c (omega_V = c - (sum c)/4 1); b-coordinates of v in V: (v_0, v_0 + v_1, -v_3)
            sc = {}
            for q in cvec: sc = X.padd(sc, q, p)
            qt = X.inv(4, p); om = [X.padd(cvec[i], X.pmul(X.pconst(qt, p), sc, p), p, -1) for i in range(4)]
            o1, o2, o3 = om[0], X.padd(om[0], om[1], p), X.pmul(X.pconst(-1, p), om[3], p)
            if xcell == 0: extra += [X.padd(X.pmul(al, o1, p), o2, p, -1), X.padd(X.pmul(be, o1, p), o3, p, -1)]
            elif xcell == 1: extra += [o1, X.padd(X.pmul(al, o2, p), o3, p, -1)]
            else: extra += [o1, o2]
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
