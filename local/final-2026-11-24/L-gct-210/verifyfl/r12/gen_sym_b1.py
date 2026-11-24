import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""gen_sym_b1.py (round 15, NOTES R15.1) -- SYMBOLIC-m version of gen_t31b1.py, chart A (m = (1, t, -1-t, 0, 0); W = gen_sym chart A;
   the two-column points t = 0, -1 are exempt (TC5, R11.6) and the Rabinowitsch variable urt with urt t (t+1) = 1 is ADDED, so the facts of
   R9.2 (which need m_j != 0) apply).  Original docstring:
   [T31] split B1 (vartheta(Z) != 0, omega != 0) in THREE-COLUMN normal form  (round 9, verifyfl; NOTES R9.2).
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
import exactlib as X, itertools, gen_sym
def build(p, xcell, omchart=None, keyed=False, with_y1=True, par=True, xomega=False):
    V = X.Vars(); t = V.new('mt'); one = X.pconst(1, p)
    e_ = lambda j: [one if a == j else {} for a in range(5)]
    W = [e_(3), e_(4), [X.pmul(X.pconst(p - 1, p), t, p), one, {}, {}, {}], [X.padd(one, t, p), {}, one, {}, {}]]
    mj = [one, t, X.pmul(X.pconst(p - 1, p), X.padd(one, t, p), p)]
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
    extra = [X.padd(dot(zc[j], zc[j]), mj[j], p, -1) for j in range(3)]
    urt = V.new('urt'); extra.append(X.padd(X.pmul(urt, X.pmul(t, X.padd(one, t, p), p), p), one, p, -1))   # t (t+1) != 0
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
    if keyed: return V.names, gen_sym.equations_poly(B, W, p, keyed=True), extra, B
    return V.names, gen_sym.equations_poly(B, W, p) + extra

if __name__ == '__main__':
    # self-check: at t = 2 (urt fixed to 1/6) the polynomials coincide up to scalars with gen_t31b1 for m12m3 (xcell 0, par)
    import gen_t31b1
    p = 2147483629
    n1, pol1 = build(p, 0); n0, pol0 = gen_t31b1.build(p, 'm12m3', 0)
    it, iu = n1.index('mt'), n1.index('urt'); rest = [n for n in n1 if n not in ('mt', 'urt')]; assert rest == n0, (rest[:5], n0[:5])
    inv6 = pow(6, p - 2, p)
    def subst(q):
        r = {}
        for mon, c in q.items():
            c2 = c * pow(2, mon.count(it), p) * pow(inv6, mon.count(iu), p) % p
            m2 = tuple(rest.index(n1[v]) for v in mon if v not in (it, iu)); m2 = tuple(sorted(m2))
            r[m2] = (r.get(m2, 0) + c2) % p
        return {m: c for m, c in r.items() if c}
    def norm(q):
        if not q: return None
        k = min(q); iv = pow(q[k], p - 2, p); return frozenset((m, c * iv % p) for m, c in q.items())
    S1 = {norm(subst(q)) for q in pol1} - {None}; S0 = {norm({tuple(sorted(m)): c for m, c in q.items()}) for q in pol0}
    print('t = 2 substitution: %d vs %d, equal up to scalars: %s' % (len(S1), len(S0), S1 == S0))
