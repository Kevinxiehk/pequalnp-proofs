import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_t31b0g.py -- [T31] split B0 (vartheta(Z) != 0, omega = 0) WITHOUT the eigen normal form (any m with |supp m| = 3; round 9).
   Z = (z_0, z_1, -z_0-z_1, 0, 0) with <z_j,z_j> = m_j (vartheta(Z) = 1) and omega = 0 (c_0 = c_1 = c_2 = c_3); Y_r (r = 1..R) column-centred
   with s(Y_r) = b_r and Theta(Y_r, Z) = 0 (2 <y_{r,0}, z_0> = <b_r, z_0>).  B = [Z, Y_1, ..., Y_R].  Variable names of Z as in omega_zero.py
   (Zaa, Zab, Zac, Zba, Zbb, Zbc) so that the B0 component factors (r9/factors_*.txt with r9/lin_*.txt) apply."""
import exactlib as X, itertools
def build(p, mspec, R=2, keyed=False):
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
    def vvec(nm):
        a, b, c = V.new(nm + 'a'), V.new(nm + 'b'), V.new(nm + 'c')
        return [a, b, c, X.padd(X.padd(X.pmul(a, X.pconst(-1, p), p), b, p, -1), c, p, -1)]
    def dot(u, v):
        q = {}
        for a, b in zip(u, v): q = X.padd(q, X.pmul(a, b, p), p)
        return q
    z0, z1 = vvec('Za'), vvec('Zb'); z2 = [X.pmul(X.pconst(-1, p), X.padd(a, b, p), p) for a, b in zip(z0, z1)]
    zero = [{} for _ in range(4)]; zc = [z0, z1, z2, zero, zero]
    extra = [X.padd(dot(zc[j], zc[j]), X.pconst(m[j], p), p, -1) for j in range(3)]
    cvec = []
    for i in range(4):
        rows = [r for r in range(4) if r != i]; q = {}
        for f in itertools.permutations(range(3)):
            term = X.pconst(1, p)
            for r, c in zip(rows, f): term = X.pmul(term, zc[c][r], p)
            q = X.padd(q, term, p)
        cvec.append(q)
    extra += [X.padd(cvec[i], cvec[0], p, -1) for i in (1, 2, 3)]
    B = [[[zc[j][a] for j in range(5)] for a in range(4)]]
    bv = [[1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1]]
    for r in range(R):
        co = [V.new('y%d_%d' % (r, d)) for d in range(12)]
        M = X.dc_matrix(co, p); M = X.madd_const_col(M, [X.pconst(x, p) for x in bv[r]], 0, p)
        col0 = [M[a][0] for a in range(4)]
        extra.append(X.padd(X.pmul(X.pconst(2, p), dot(col0, z0), p), dot([X.pconst(x, p) for x in bv[r]], z0), p, -1))
        B.append(M)
    extra = [q for q in extra if q]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
