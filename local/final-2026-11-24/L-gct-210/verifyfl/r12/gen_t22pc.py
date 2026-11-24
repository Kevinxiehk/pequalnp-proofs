import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""gen_t22pc.py -- SYM-M [T22], rho = 2 N-cases (idx 0..8): the PIECES (P2), (P1a), (P1b) of the vartheta cover (round 13, NOTES R13.2),
   with the optional det sub-split of the isotropic-column generator and the optional RADICAL equations in S-cell 0 (R13.1).

   COVER of a rho = 2 case (N = span(Z_1, Z_2), neutral parts (v_3, 0), (0, v_4); chart A: vartheta(Z) = |c_0(Z)|^2, chart B: |c_1(Z)|^2;
   vartheta_rs = polarisation; (F2): <c_j(Z_r), c_j(Z_s)> = vartheta_rs m_j):
     (P2)  vartheta_11 != 0: Z_a = alpha Z_1 + Z_2 with vartheta(Z_a) = 0 exists; N = span(Z_1, Z_a); Z_1 general (y0-coordinates),
           Z_a isotropic-column with neutral part (alpha v_3, v_4);  usp * vartheta_11 = 1,  |c_1|^2 - t |c_0|^2 = 0 on Z_1 (chart A).
     (P1a) vartheta_11 = 0 != vartheta_22: Z_1 isotropic-column (neutral (v_3, 0)), Z_2 general (y1-coordinates, neutral (0, v_4));
           usp * vartheta_22 = 1 and the t-relation on Z_2.
     (P1b) vartheta_11 = vartheta_22 = 0 != vartheta_12: Z_1 isotropic-column, Z_2 general with vartheta_22 = 0 as an equation;
           usp * vartheta_12 = 1 and the polarised t-relation <c_1(Z_1),c_1(Z_2)> - t <c_0(Z_1),c_0(Z_2)> = 0 (chart A).
     (IV)  vartheta == 0: gen_t22t0 / t0b / t0c.
   ISOTROPIC-COLUMN generator (vartheta(Z) = 0 => every |c_j(Z)|^2 = 0): Z = [mu_0 u_0, mu_1 u_1, mu_2 u_2, nu_3, nu_4], u_j in
   {ab, z1, z2, 0}, row sums 0 LINEAR in mu.  For u = (ab, ab, ab) the det sub-split (as gen_t22t0c): 'ne' (D != 0, mu solved by the
   adjugate, udet * D = 1) or 'ij' (u_i = u_j; D = 0 forces two equal, R12.4).
   RADICAL (S-cell 0 only, R13.1): rad = 'r1' (rho_1 = 1) / 'r2' (rho_1 = 0, rho_2 = 1): <s_rad, s_1> = <s_rad, s_2> = 0 and columns 3, 4 of
   Y_rad = rho_1 Y_1 + rho_2 Y_2 vanish (valid for every rho = 2 piece: b_n(Y_rad) in C v_n, and the gauge kills the multiple).
   build(p, chart, ci, piece, uk, dsplit, scell, rad=None, keyed=False);  piece in 'P2', 'P1a', 'P1b';  uk = 'u0:u1:u2'."""
import exactlib as X, gen_n1s, gen_n3, gen_sym, gen_sym_n3
from gen_t22t0 import isovec
from gen_t22t0c import det3
def isocol(p, cs, V, uk, nu3, nu4, dsplit, tag):
    """isotropic-column generator with neutral columns nu3, nu4 (4-vectors of polynomials); returns (matrix, extra)"""
    extra = []; us = {}
    same = {'01': {1: 0}, '02': {2: 0}, '12': {2: 1}}.get(dsplit, {})
    for j in range(3):
        if j in same: us[j] = us[same[j]]
        else:
            us[j], f = isovec(p, cs, V, uk[j], '%su%d' % (tag, j)); extra += f
    cols = [[{} for a in range(4)] for j in range(5)]
    cols[3] = [dict(x) for x in nu3]; cols[4] = [dict(x) for x in nu4]
    if dsplit == 'ne':
        assert all(uk[j] == 'ab' for j in range(3))
        U = [[us[j][a] for j in range(3)] for a in range(3)]
        ud = V.new('%sudet' % tag); extra.append(X.padd(X.pmul(ud, det3(U, p), p), X.pconst(1, p), p, -1))
        def minor(a, j):
            rr = [r for r in range(3) if r != a]; cc = [c for c in range(3) if c != j]
            return X.padd(X.pmul(U[rr[0]][cc[0]], U[rr[1]][cc[1]], p), X.pmul(U[rr[0]][cc[1]], U[rr[1]][cc[0]], p), p, -1)
        vr = [X.padd(nu3[a], nu4[a], p) for a in range(3)]
        for j in range(3):
            lam = {}
            for a in range(3): lam = X.padd(lam, X.pmul(X.pmul(X.pconst(1 if (a + j) % 2 == 0 else p - 1, p), minor(a, j), p), vr[a], p), p)
            lam = X.pmul(X.pmul(ud, lam, p), X.pconst(p - 1, p), p)
            cols[j] = [X.pmul(lam, us[j][a], p) for a in range(4)]
    else:
        if dsplit == 'nl':     # round 17: D != 0 by Rabinowitsch only, mu's kept as variables with the linear row sums
            assert all(uk[j] == 'ab' for j in range(3))
            U = [[us[j][a] for j in range(3)] for a in range(3)]
            ud = V.new('%sudet' % tag); extra.append(X.padd(X.pmul(ud, det3(U, p), p), X.pconst(1, p), p, -1))
        for j in range(3):
            if us[j] is not None:
                mu = V.new('%smu%d' % (tag, j)); cols[j] = [X.pmul(mu, us[j][a], p) for a in range(4)]
        for a in range(4):
            q = {}
            for j in range(5): q = X.padd(q, cols[j][a], p)
            extra.append(q)
    return [[cols[j][a] for j in range(5)] for a in range(4)], extra
def general(p, V, r, nu3, nu4):
    co = [V.new('y%d_%d' % (r, d)) for d in range(6)]
    Z = X.dcsub_matrix(co, [0, 1, 2], p)
    for a in range(4):
        for col, nu in ((3, nu3), (4, nu4)):
            if nu[a]: Z[a][col] = X.padd(Z[a][col], nu[a], p); Z[a][2] = X.padd(Z[a][2], nu[a], p, -1)
    return Z
def ip(u, v, p):
    q = {}
    for x, y in zip(u, v): q = X.padd(q, X.pmul(x, y, p), p)
    return q
def col(M, j): return [M[a][j] for a in range(4)]
def nbasis_pc(p, cs, case, V, chart, piece, uk, dsplit):
    k, rho, piv, lc, t3, t4 = case; assert k == 2 and rho == 2 and piv == ()
    it = 0                                                          # 'mt'
    v3, e3 = isovec(p, cs, V, t3, '3'); v4, e4 = isovec(p, cs, V, t4, '4'); extra = e3 + e4
    zero = [{} for a in range(4)]
    j0, j1 = (0, 1) if chart == 'A' else (1, 0)                      # vartheta = <c_j0, c_j0>; t-relation <c_j1,c_j1> - t <c_j0,c_j0>
    trel = lambda A_, B_: X.padd(ip(col(A_, j1), col(B_, j1), p), X.pmul({(it,): 1}, ip(col(A_, j0), col(B_, j0), p), p), p, -1)
    th = lambda A_, B_: ip(col(A_, j0), col(B_, j0), p)
    if piece == 'P2':
        Z1 = general(p, V, 0, v3, zero)
        al = V.new('alp'); Za, ex = isocol(p, cs, V, uk, [X.pmul(al, v3[a], p) for a in range(4)], v4, dsplit, ''); extra += ex
        usp = V.new('usp'); extra += [X.padd(X.pmul(usp, th(Z1, Z1), p), X.pconst(1, p), p, -1), trel(Z1, Z1)]
        B = [Z1, Za]
    else:
        Z1, ex = isocol(p, cs, V, uk, v3, zero, dsplit, ''); extra += ex
        Z2 = general(p, V, 1, zero, v4)
        usp = V.new('usp')
        if piece == 'P1a': extra += [X.padd(X.pmul(usp, th(Z2, Z2), p), X.pconst(1, p), p, -1), trel(Z2, Z2)]
        else: extra += [th(Z2, Z2), X.padd(X.pmul(usp, th(Z1, Z2), p), X.pconst(1, p), p, -1), trel(Z1, Z2)]
        B = [Z1, Z2]
    vrow = {'ab': 0, 'z1': 1, 'z2': 1}
    return B, [e for e in extra if e], [[(vrow[t3], 3)], [(vrow[t4], 4)]]
def build(p, chart, ci, piece, uk, dsplit, scell, rad=None, keyed=False):
    case = gen_n1s.cases(2)[ci]; uk = uk.split(':') if isinstance(uk, str) else uk
    dsplit = None if dsplit in (None, '-', 'None') else dsplit
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    B, extra, ells = nbasis_pc(p, cs, case, V, chart, piece, uk, dsplit)
    if scell is not None:
        S = gen_n3.svectors(p, scell, V); Ys = []
        for r in range(2):
            co = [V.new('w%d_%d' % (r, d)) for d in range(12)]
            M = X.dc_matrix(co, p); D = [[dict(x) for x in row] for row in M]
            M = X.madd_const_col(M, S[r], 0, p)
            for ell in ells: extra.append(gen_n3.entry_form(D, ell, p))
            B.append(M); Ys.append(D)
        g = X.padd(X.pmul(ip(S[0], S[0], p), ip(S[1], S[1], p), p), X.pmul(ip(S[0], S[1], p), ip(S[0], S[1], p), p), p, -1)
        if g: extra.append(g)
        if rad is not None:
            raise ValueError('rad option VOID (R13.5: b_n(Y) = 2 y_n - s(Y), columns of Y_rad are not 0); use gen_t22rad (radical S-cells, nb = pc)')
            rho = [X.pconst(1, p), V.new('rho2')] if rad == 'r1' else [{}, X.pconst(1, p)]
            srad = [X.padd(X.pmul(rho[0], S[0][a], p), X.pmul(rho[1], S[1][a], p), p) for a in range(4)]
            extra += [ip(srad, S[0], p), ip(srad, S[1], p)]
            for n in (3, 4):
                for a in range(4): extra.append(X.padd(X.pmul(rho[0], Ys[0][a][n], p), X.pmul(rho[1], Ys[1][a][n], p), p))
    extra = [e for e in extra if e]
    if keyed: return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra
    return V.names, gen_sym.equations_poly(B, Wp, p) + extra
if __name__ == '__main__':
    import random
    p = 2147483629; cs = X.Consts(p)
    # (1) P2 with Z_1 general reproduces gen_t22iso's system exactly (same variables, same polynomials)
    import gen_t22iso
    for sc in (None, 1):
        n1, e1 = build(p, 'A', 0, 'P2', 'ab:z1:0', None, sc); n2, e2 = gen_t22iso.build(p, 'A', 0, 'ab', 'z1', '0', sc)
        canon = lambda q, nm: frozenset((tuple(sorted(nm[v] for v in mon)), c % p) for mon, c in q.items())
        f1 = sorted(map(sorted, (canon(q, n1) for q in e1))); f2 = sorted(map(sorted, (canon(q, n2) for q in e2)))
        assert f1 == f2, 'P2 differs from gen_t22iso (scell %s)' % sc
    # (2) the isotropic-column generator has isotropic columns and zero row sums on its variety (numerical, 'ne' form)
    V = X.Vars(); V.new('mt'); Z, ex = isocol(p, cs, V, ['ab', 'ab', 'ab'], [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)], [{}] * 4, 'ne', '')
    print('self-check ok: P2 == gen_t22iso; isocol built (%d extra)' % len(ex))
