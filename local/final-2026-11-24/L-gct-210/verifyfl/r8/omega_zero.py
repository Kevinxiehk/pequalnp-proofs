import sys; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""split B, Z-family (Z doubly centred on P, vartheta(Z) = 1 [<z_j,z_j> = m_j], tau(z0 z1 z2) = 0) plus omega = 0, where
perm[z0,z1,z2,u] = sum_i c_i u_i and omega = 0 means c_0 = c_1 = c_2 = c_3 (the form vanishes on V).  Writes an msolve file."""
import exactlib as X, itertools
p = int(sys.argv[1]); mspec = sys.argv[2]; out = sys.argv[3]
cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
def vvec(nm):
    a, b, c = V.new(nm + 'a'), V.new(nm + 'b'), V.new(nm + 'c'); return [a, b, c, X.padd(X.padd(X.pmul(a, X.pconst(-1, p), p), b, p, -1), c, p, -1)]
z0, z1 = vvec('Za'), vvec('Zb'); z2 = [X.pmul(X.pconst(-1, p), X.padd(a, b, p), p) for a, b in zip(z0, z1)]
ip = lambda u, v: [X.padd(q, X.pmul(a, b, p), p) for q in [{}] for a, b in [(0, 0)]] and None
def dot(u, v):
    q = {}
    for a, b in zip(u, v): q = X.padd(q, X.pmul(a, b, p), p)
    return q
eqs = [X.padd(dot(z, z), X.pconst(mj, p), p, -1) for z, mj in ((z0, m[0]), (z1, m[1]), (z2, m[2]))]
t = {}
for i in range(4): t = X.padd(t, X.pmul(X.pmul(z0[i], z1[i], p), z2[i], p), p)
eqs.append(t)
cvec = []
for i in range(4):
    rows = [r for r in range(4) if r != i]; q = {}
    for f in itertools.permutations(range(3)):
        cols = (z0, z1, z2); term = X.pconst(1, p)
        for r, c in zip(rows, f): term = X.pmul(term, cols[c][r], p)
        q = X.padd(q, term, p)
    cvec.append(q)
for i in range(1, 4): eqs.append(X.padd(cvec[i], cvec[0], p, -1))
X.write_msolve(out, V.names, p, [e for e in eqs if e]); print(len(V.names), 'vars', len(eqs), 'eqs')
