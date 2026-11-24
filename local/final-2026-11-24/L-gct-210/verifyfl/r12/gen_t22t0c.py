import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""gen_t22t0c.py -- piece (IV) of the rho = 2 [T22] N-cases, sub-piece u_0, u_1, u_2 all in the 'ab' chart (the generic sub-piece of
   gen_t22t0b), split by D = det(u_0, u_1, u_2) (3x3 minor on coordinates 0, 1, 2 = determinant in V, since the vectors sum to 0)
   (round 12, NOTES R12.4):
     'ne': D != 0: udet * D = 1 and the row-sum equations U lam_r = -v_r SOLVED: lam_r = -udet * adj(U) v_r (polynomial; 6 unknowns fewer);
     'ij' (ij = 01, 02, 12): u_i = u_j (the same 'ab' point);
     'nl' (round 15): D != 0 by udet * D = 1 only, lam's kept as variables (same piece as 'ne', other presentation).
   COVER [rigorous, char p > 2]: if D = 0 the three isotropic vectors lie in a plane P of V; P carries at most two isotropic lines (P
   nondegenerate: two; P degenerate: its radical only; P totally isotropic is impossible in the 3-dim nondegenerate V), so two of the u's
   are proportional, i.e. EQUAL in the 'ab' chart (first coordinate 1).   build(p, chart, ci, dsplit, scell, keyed)."""
import exactlib as X, gen_n1s, gen_n3, gen_sym, gen_sym_n3
from gen_t22t0 import isovec
def det3(M, p):
    q = {}
    for perm, sg in (((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1), ((0, 2, 1), -1), ((2, 1, 0), -1), ((1, 0, 2), -1)):
        term = X.pconst(1 if sg == 1 else p - 1, p)
        for r in range(3): term = X.pmul(term, M[r][perm[r]], p)
        q = X.padd(q, term, p)
    return q
def nbasis_t0c(p, cs, case, V, dsplit):
    k, rho, piv, lc, t3, t4 = case; assert k == 2 and rho == 2 and piv == ()
    extra = []
    v3, e3 = isovec(p, cs, V, t3, '3'); v4, e4 = isovec(p, cs, V, t4, '4'); extra += e3 + e4
    us = {}
    for j in range(3):
        same = {'01': {1: 0}, '02': {2: 0}, '12': {2: 1}}.get(dsplit, {})
        if j in same: us[j] = us[same[j]]
        else: us[j], f = isovec(p, cs, V, 'ab', 'u%d' % j); extra += f
    U = [[us[j][a] for j in range(3)] for a in range(3)]          # U[a][j] = coordinate a of u_j
    vrow = {'ab': 0, 'z1': 1, 'z2': 1}
    if dsplit == 'nl':   # round 15 (R15.5): D != 0 by Rabinowitsch only, lam's kept as variables with the LINEAR row-sum equations
        ud = V.new('udet'); extra.append(X.padd(X.pmul(ud, det3(U, p), p), X.pconst(1, p), p, -1))
    if dsplit == 'ne':
        ud = V.new('udet'); D = det3(U, p); extra.append(X.padd(X.pmul(ud, D, p), X.pconst(1, p), p, -1))
        # adjugate: adj[j][a] = cofactor C[a][j]
        def minor(a, j):
            rr = [r for r in range(3) if r != a]; cc = [c for c in range(3) if c != j]
            return X.padd(X.pmul(U[rr[0]][cc[0]], U[rr[1]][cc[1]], p), X.pmul(U[rr[0]][cc[1]], U[rr[1]][cc[0]], p), p, -1)
        adj = [[X.pmul(X.pconst(1 if (a + j) % 2 == 0 else p - 1, p), minor(a, j), p) for a in range(3)] for j in range(3)]
    B = []
    for r in range(2):
        vr = v3 if r == 0 else v4
        cols = [[{} for a in range(4)] for j in range(5)]
        if r == 0: cols[3] = [dict(x) for x in v3]
        else: cols[4] = [dict(x) for x in v4]
        if dsplit == 'ne':
            for j in range(3):
                lam = {}
                for a in range(3): lam = X.padd(lam, X.pmul(adj[j][a], vr[a], p), p)
                lam = X.pmul(X.pmul(ud, lam, p), X.pconst(p - 1, p), p)
                cols[j] = [X.pmul(lam, us[j][a], p) for a in range(4)]
        else:
            for j in range(3):
                l = V.new('l%d%d' % (r, j)); cols[j] = [X.pmul(l, us[j][a], p) for a in range(4)]
            for a in range(4):
                q = {}
                for j in range(5): q = X.padd(q, cols[j][a], p)
                extra.append(q)
        B.append([[cols[j][a] for j in range(5)] for a in range(4)])
    ells = [[(vrow[t3], 3)], [(vrow[t4], 4)]]
    return B, [e for e in extra if e], ells
def build(p, chart, ci, dsplit, scell, keyed=False):
    case = gen_n1s.cases(2)[ci]
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    B, extra, ells = nbasis_t0c(p, cs, case, V, dsplit)
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
    # self-check of the 'ne' form: row sums of each generator = (D * udet - 1) * (-v_r) -> vanish modulo udet*D = 1; test numerically
    import random
    p = 2147483629; cs = X.Consts(p); V = X.Vars(); V.new('mt'); B, ex, ells = nbasis_t0c(p, cs, gen_n1s.cases(2)[0], V, 'ne')
    names = V.names; ud = names.index('udet')
    def ev(q, val): 
        s = 0
        for mon, c in q.items():
            t = c
            for v in mon: t = t * val[v] % p
            s = (s + t) % p
        return s
    val = [random.randrange(p) for _ in names]
    U = None
    # choose udet = 1/D at the random point
    cs2 = X.Consts(p); V2 = X.Vars(); V2.new('mt'); _ = nbasis_t0c(p, cs2, gen_n1s.cases(2)[0], V2, 'ne')
    Dq = [e for e in ex if any(ud in mon for mon in e)][0]       # udet*D - 1
    Dval = (ev(Dq, val[:ud] + [0] + val[ud + 1:]) + 1) % p           # at udet = 0: -1 -> D = ?
    # Dq = udet*D - 1 : evaluate D as (Dq(udet=1) - Dq(udet=0))
    D1 = ev(Dq, val[:ud] + [1] + val[ud + 1:]); D0 = ev(Dq, val[:ud] + [0] + val[ud + 1:]); Dv = (D1 - D0) % p
    val[ud] = pow(Dv, p - 2, p)
    for M in B:
        for a in range(4):
            assert sum(ev(M[a][j], val) for j in range(5)) % p == 0, 'row sum'
    print('self-check ok (ne: row sums vanish at udet = 1/D)')
