import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""gen_sym_b0.py -- SYM-M [T31] split B0 (vartheta(Z) != 0, omega = 0) with m SYMBOLIC on P(W_P), chart A (round 14, NOTES R14.1; plan R11.17).
   In split B (vartheta(Z) != 0) normalise vartheta(Z) = 1; (F2) gives <z_j, z_j> = m_j.  Chart A (m_0 = 1, m = (1, t, -1-t, 0, 0)):
   <z_0,z_0> = 1, t = <z_1,z_1>, and <z_2,z_2> = -1-t.  Chart B (m_1 = 1) adds only m_0 = 0, i.e. the two-column line (0,1,-1,0,0)
   (TC5, R11.6), so chart A suffices for R11.6 (non-unit -> Rabinowitsch u t (t+1) - 1).
   System = gen_t31b0g.build with m_j replaced by these relations and W = gen_sym chart A (polynomial in t): Z = (z_0, z_1, -z_0-z_1, 0, 0),
   omega = 0 (c_0 = c_1 = c_2 = c_3), Y_r column-centred with s(Y_r) = b_r and Theta(Y_r, Z) = 0, r = 1..R.
   build(p, R, keyed) -> (names, eqs|polys, extra, B)."""
import exactlib as X, gen_sym, itertools
def build(p, R=2, keyed=False):
    V = X.Vars(); t = V.new('mt'); one = X.pconst(1, p)
    e = lambda j: [one if a == j else {} for a in range(5)]
    Wp = [e(3), e(4), [X.pmul(X.pconst(p - 1, p), t, p), one, {}, {}, {}], [X.padd(one, t, p), {}, one, {}, {}]]
    def vvec(nm):
        a, b, c = V.new(nm + 'a'), V.new(nm + 'b'), V.new(nm + 'c')
        return [a, b, c, X.padd(X.padd(X.pmul(a, X.pconst(-1, p), p), b, p, -1), c, p, -1)]
    def dot(u, v):
        q = {}
        for x, y in zip(u, v): q = X.padd(q, X.pmul(x, y, p), p)
        return q
    z0, z1 = vvec('Za'), vvec('Zb'); z2 = [X.pmul(X.pconst(-1, p), X.padd(a, b, p), p) for a, b in zip(z0, z1)]
    zero = [{} for _ in range(4)]; zc = [z0, z1, z2, zero, zero]
    mj = [one, t, X.pmul(X.pconst(p - 1, p), X.padd(one, t, p), p)]
    extra = [X.padd(dot(zc[j], zc[j]), mj[j], p, -1) for j in range(3)]
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
    if keyed: return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra, B
    return V.names, gen_sym.equations_poly(B, Wp, p) + extra
if __name__ == '__main__':
    # self-check: at t = 2 (m = (1,2,-3)) the system equals gen_t31b0g's for m12m3 after substituting mt = 2
    import gen_t31b0g
    p = 2147483629
    n1, pol1 = build(p, 2); n0, pol0 = gen_t31b0g.build(p, 'm12m3', 2)
    it = n1.index('mt'); assert n1[1:] == n0
    def subst(q):
        r = {}
        for mon, c in q.items():
            k = mon.count(it); m2 = tuple(v - 1 for v in mon if v != it)
            r[m2] = (r.get(m2, 0) + c * pow(2, k, p)) % p
        return {m: c for m, c in r.items() if c}
    canon = lambda q: frozenset(q.items())
    s1 = {canon(subst(q)) for q in pol1} - {frozenset()}; s0 = {canon(q) for q in pol0}
    # equal up to nonzero scalar multiples of individual polynomials: compare normalised (leading coefficient 1)
    def norm(fs):
        d = dict(fs)
        if not d: return fs
        k = min(d); inv = pow(d[k], p - 2, p); return frozenset((m, c * inv % p) for m, c in d.items())
    S1 = {norm(f) for f in s1}; S0 = {norm(f) for f in s0}
    print('t = 2 substitution: %d vs %d polynomials, same span-generators up to scalars: %s' % (len(S1), len(S0), S1 == S0))
