import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_t31e.py -- [T31] split B in EIGEN-NORMALISED form (round 8, verifyfl; mathematics NOTES-verifyfl R8.1).
   m = (m_0, m_1, m_2, 0, 0) with three DISTINCT nonzero entries.  K = 4-dim column-centred, type (3,1), N = C Z (Z doubly centred,
   supported on P = {0,1,2} by (F3)), vartheta(Z) != 0.  K' = {Y in K : Theta(Y,Z) = 0}.  On K', b_j(Y) = A_j s(Y) with
     A_n^* A_n = 1 (neutral n),  A_j^* A_j = 1 + 4 m_j Psi (j in P),  A_j^* z_j = 0,  sum_j A_j = -3,
   Psi has the distinct eigenvalues lam_k = -1/(4 m_k) with an ORTHONORMAL eigenframe e_0, e_1, e_2 of V, and A_k e_k = 0.
   Normal form: Y_k in K' with s(Y_k) = e_k (k = 0,1,2), Z scaled to vartheta(Z) = 1.
   Unknowns: beta_{k,j} = b_j(Y_k) = 2 y_{k,j} - e_k in V for j != k (beta_{k,k} = 0), 3 coordinates each; e_k := -(1/3) sum_j beta_{k,j}
   (row sums); y_{k,j} = (beta_{k,j} + e_k)/2;  z_0, z_1 in V (3 coordinates each), z_2 = -z_0 - z_1, z_3 = z_4 = 0.
   Equations:  (N1) <e_k,e_l> = delta_kl;   (N2) <beta_{k,j}, beta_{l,j}> = delta_kl alpha_{jk}, alpha_{jk} = 1 - m_j/m_k (1 for neutral j);
               (N3) <z_j,z_j> = m_j;   (N4) <beta_{k,j}, z_j> = 0;   (N5) all coefficients of R_i(x_Z Z + sum_k x_k Y_k).
   KS = subset of {0,1,2} of the Y_k used (all three: the full split-B system; two: a sub-system, valid by the same normal form).
   usage: python3 -I gen_t31e.py P MSPEC KS OUT.ms      (KS like 012 or 01)"""
import exactlib as X
def build(p, mspec, ks, keyed=False, omega=None):
    """omega: None, 'zero' (split B0: perm[z0,z1,z2,.] vanishes on V, i.e. c_0 = c_1 = c_2 = c_3) or ('ne', i) (split B1, chart
    c_i - c_0 != 0 via a new variable u: u (c_i - c_0) = 1; i = 1, 2, 3 cover omega != 0)."""
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs)
    assert m[3] == 0 and m[4] == 0 and all(m[j] for j in range(3)) and len({m[0], m[1], m[2]}) == 3, 'needs three distinct entries on columns 0,1,2'
    V = X.Vars(); inv3 = X.inv(3, p); half = X.inv(2, p)
    def vvec(name):
        a, b, c = V.new(name + 'a'), V.new(name + 'b'), V.new(name + 'c')
        return [a, b, c, X.padd(X.padd(X.pmul(a, X.pconst(-1, p), p), b, p, -1), c, p, -1)]
    def ip(u, v):
        q = {}
        for t in range(4): q = X.padd(q, X.pmul(u[t], v[t], p), p)
        return q
    def scal(c, u): return [X.pmul(X.pconst(c, p), x, p) for x in u]
    def vadd(u, v, cb=1): return [X.padd(a, b, p, cb) for a, b in zip(u, v)]
    zero = [{} for _ in range(4)]
    beta = {}
    for k in ks:
        for j in range(5):
            beta[(k, j)] = zero if j == k else vvec('B%d%d' % (k, j))
    e = {}
    for k in ks:
        tot = zero
        for j in range(5): tot = vadd(tot, beta[(k, j)])
        e[k] = scal((-inv3) % p, tot)
    z0, z1 = vvec('Za'), vvec('Zb'); z2 = scal(p - 1, vadd(z0, z1)); zc = [z0, z1, z2, zero, zero]
    # matrices
    Ys = []
    for k in ks:
        M = [[{} for _ in range(5)] for _ in range(4)]
        for j in range(5):
            col = scal(half, vadd(beta[(k, j)], e[k]))
            for a in range(4): M[a][j] = col[a]
        Ys.append(M)
    Zm = [[zc[j][a] for j in range(5)] for a in range(4)]
    extra = []
    for i1, k in enumerate(ks):
        for l in ks[i1:]:
            extra.append(X.padd(ip(e[k], e[l]), X.pconst(1 if k == l else 0, p), p, -1))                      # (N1)
            for j in range(5):
                if j == k or j == l: continue
                al = 1 if j >= 3 else (1 - m[j] * X.inv(m[k], p)) % p
                extra.append(X.padd(ip(beta[(k, j)], beta[(l, j)]), X.pconst(al if k == l else 0, p), p, -1))  # (N2)
    for j in range(3): extra.append(X.padd(ip(zc[j], zc[j]), X.pconst(m[j], p), p, -1))                           # (N3)
    for k in ks:
        for j in range(3):
            if j != k: extra.append(ip(beta[(k, j)], zc[j]))                                                      # (N4)
    if omega is not None:
        import itertools
        cvec = []
        for i in range(4):
            rows = [r for r in range(4) if r != i]; q = {}
            for f in itertools.permutations(range(3)):
                term = X.pconst(1, p)
                for r, c in zip(rows, f): term = X.pmul(term, zc[c][r], p)
                q = X.padd(q, term, p)
            cvec.append(q)
        if omega == 'zero': extra += [X.padd(cvec[i], cvec[0], p, -1) for i in (1, 2, 3)]
        else:
            u = V.new('uom'); extra.append(X.padd(X.pmul(u, X.padd(cvec[omega[1]], cvec[0], p, -1), p), X.pconst(1, p), p, -1))
    extra = [q for q in extra if q]
    B = [Zm] + Ys
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra, B
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
if __name__ == '__main__':
    p = int(sys.argv[1]); mspec = sys.argv[2]; ks = [int(c) for c in sys.argv[3]]; out = sys.argv[4]
    names, polys = build(p, mspec, ks)
    X.write_msolve(out, names, p, polys); print(len(names), 'vars', len(polys), 'eqs ->', out)
