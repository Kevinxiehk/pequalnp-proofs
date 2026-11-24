import sys, itertools; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""t-free symbolic B0 Z-set (chart A: <z_0,z_0> = 1, m_1 = <z_1,z_1>, m_2 = <z_2,z_2>, 1 + m_1 + m_2 = 0; tau(z0 z1 z2) = 0; omega = 0) -> Singular dim."""
import exactlib as X
p = 2147483629; V = X.Vars()
def vvec(nm):
    a, b, c = V.new(nm + 'a'), V.new(nm + 'b'), V.new(nm + 'c'); return [a, b, c, X.padd(X.padd(X.pmul(a, X.pconst(-1, p), p), b, p, -1), c, p, -1)]
z0, z1 = vvec('Za'), vvec('Zb'); z2 = [X.pmul(X.pconst(-1, p), X.padd(a, b, p), p) for a, b in zip(z0, z1)]
def dot(u, v):
    q = {}
    for a, b in zip(u, v): q = X.padd(q, X.pmul(a, b, p), p)
    return q
eqs = [X.padd(dot(z0, z0), X.pconst(1, p), p, -1), X.padd(X.padd(X.pconst(1, p), dot(z1, z1), p), dot(z2, z2), p)]
t = {}
for i in range(4): t = X.padd(t, X.pmul(X.pmul(z0[i], z1[i], p), z2[i], p), p)
eqs.append(t)
cv = []
for i in range(4):
    rows = [r for r in range(4) if r != i]; q = {}
    for f in itertools.permutations(range(3)):
        term = X.pconst(1, p)
        for r, c in zip(rows, f): term = X.pmul(term, (z0, z1, z2)[c][r], p)
        q = X.padd(q, term, p)
    cv.append(q)
eqs += [X.padd(cv[i], cv[0], p, -1) for i in (1, 2, 3)]
print('ring r = %d, (%s), dp; ideal I = %s; ideal J = std(I); print(dim(J)); print(vdim(J)); quit;' % (p, ','.join(V.names), ','.join(X.fmt_poly(e, V.names) for e in eqs)))
