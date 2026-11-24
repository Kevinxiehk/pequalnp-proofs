import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""gen_t22pc1.py -- SYM-M [T22] rho = 1 N-cases with N_P pivot (0,) and line cell 0 (gen_n1s.cases(2) idx 9, 10, 11): the vartheta cover
   at the N level with JUNK REMOVAL (round 18, NOTES R18.3).  N = span(Z_0, Z_1): Z_0 in N_P (columns 0-2, entry (0,0) = 1), Z_1 with
   neutral part (v_3, al v_4) and entry (0,0) = 0.  Chart A: vartheta(Z) = |c_0(Z)|^2, t-relation |c_1|^2 = t |c_0|^2 (chart B swapped).
   Pieces (cover: vartheta_00 != 0 -> Q2; = 0: vartheta_11 != 0 -> Q1a; = 0: vartheta_01 != 0 -> Q1b; = 0 -> IV1):
     IV1: vartheta == 0: gen_t22t1 (u_0 forced 'ab', lam_0(Z_0) = 1, lam_0(Z_1) = 0; u_1, u_2 charts); lambda-words over k = 1, 2.
     Q2 : vartheta(Z_0) != 0: Z_a = alpha Z_0 + Z_1 isotropic-column with neutral part (v_3, al v_4), Z_0 general; mu_k != 0.
     Q1a: vartheta(Z_0) = 0 != vartheta(Z_1): Z_0 isotropic-column P-supported (u_0 'ab', mu_0 = 1), Z_1 general; mu_k != 0 (k = 1, 2).
     Q1b: vartheta(Z_0) = vartheta(Z_1) = 0 != vartheta(Z_0, Z_1): as Q1a with vartheta(Z_1) = 0, polarised t-relation.
   JUNK: a vanishing column of the isotropic-column generator (mu_k = 0) / of N (lam_k == 0) is the u_k = '0' item of the same piece (decided
   by induction on the number of '0' columns).  Early two-column Rabinowitsch urt t (t+1) = 1 (R16.2).
   nsystem(p, chart, ci, piece, uk, dsplit, word) -> (names, polys): the N-system only (keyed x-monomials in Z_0, Z_1 + extras)."""
import exactlib as X, gen_n1s, gen_sym, gen_sym_n3, gen_n3, itertools
from gen_t22t0 import isovec
from gen_t22t0c import det3
from gen_t22pc import isocol, ip, col
def general_np(p, V, r, nu3, nu4, pivot_zero):
    """general element: P-part dcsub on columns 0-2 with coordinates y{r}_d (d = 0 the pivot entry (0,0): fixed 1 for Z_0 (pivot_zero False) or
    0 for Z_1 (pivot_zero True)); neutral columns nu3, nu4 (subtracted from column 2)."""
    co = []
    for d in range(6):
        if d == 0: co.append(X.pconst(0 if pivot_zero else 1, p) if not pivot_zero else {})
        else: co.append(V.new('y%d_%d' % (r, d)))
    if not pivot_zero: co[0] = X.pconst(1, p)
    Z = X.dcsub_matrix(co, [0, 1, 2], p)
    for a in range(4):
        for c_, nu in ((3, nu3), (4, nu4)):
            if nu[a]: Z[a][c_] = X.padd(Z[a][c_], nu[a], p); Z[a][2] = X.padd(Z[a][2], nu[a], p, -1)
    return Z
def nbasis_full(p, chart, ci, piece, uk, dsplit, word=None):
    """returns (V, t, Wp, B, extra) - N generators with all junk-removal / piece / Rabinowitsch extras (no N-equations)."""
    case = gen_n1s.cases(2)[ci]; k_, rho, piv, lc, t3, t4 = case; assert rho == 1 and piv == (0,) and lc == 0 and t3 == 'ab'
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    uks = uk.split(':'); dsplit = None if dsplit in (None, '-') else dsplit
    v3, e3 = isovec(p, cs, V, t3, '3'); v4, e4 = isovec(p, cs, V, t4, '4'); extra = list(e3) + list(e4)
    al = V.new('al'); v4al = [X.pmul(al, v4[a], p) for a in range(4)]; zero = [{} for a in range(4)]
    j0, j1 = (0, 1) if chart == 'A' else (1, 0)
    th = lambda A_, B_: ip(col(A_, j0), col(B_, j0), p)
    trel = lambda A_, B_: X.padd(ip(col(A_, j1), col(B_, j1), p), X.pmul({(0,): 1}, th(A_, B_), p), p, -1)
    mus = []                                            # (generator, k, vrow) whose column k must be nonzero (junk removal)
    if piece == 'IV1':
        import gen_t22t1
        V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
        B, extra, ells = gen_t22t1.nbasis_t1(p, cs, case, V, uks[1], uks[2])
        lam_ks = [kk for kk in (1, 2) if uks[kk] != '0']
    else:
        if piece == 'Q2':
            Z0 = general_np(p, V, 0, zero, zero, False)
            Za, ex = isocol(p, cs, V, uks, v3, v4al, dsplit, ''); extra += ex
            usp = V.new('usp'); extra += [X.padd(X.pmul(usp, th(Z0, Z0), p), X.pconst(1, p), p, -1), trel(Z0, Z0)]
            B = [Z0, Za]; gi = 1
        else:
            assert uks[0] == 'ab'
            Z0, ex = isocol(p, cs, V, uks, zero, zero, dsplit, ''); extra += ex
            # entry (0,0) of Z_0 = mu_0 * u_0[0] = mu_0 must be 1 (pivot normalisation)
            ix = {n_: i_ for i_, n_ in enumerate(V.names)}
            if 'mu0' in ix: extra.append(X.padd({(ix['mu0'],): 1}, X.pconst(1, p), p, -1))
            Z1 = general_np(p, V, 1, v3, v4al, True)
            usp = V.new('usp')
            if piece == 'Q1a': extra += [X.padd(X.pmul(usp, th(Z1, Z1), p), X.pconst(1, p), p, -1), trel(Z1, Z1)]
            else: extra += [th(Z1, Z1), X.padd(X.pmul(usp, th(Z0, Z1), p), X.pconst(1, p), p, -1), trel(Z0, Z1)]
            B = [Z0, Z1]; gi = 0
        for kk in range(3):
            if uks[kk] == '0': continue
            if piece != 'Q2' and kk == 0: continue          # mu_0 = 1 already
            vr = 0 if uks[kk] == 'ab' else 1
            uu = V.new('um%d' % kk); extra.append(X.padd(X.pmul(uu, B[gi][vr][kk], p), X.pconst(1, p), p, -1))
        lam_ks = []
    if piece == 'IV1' and word is not None:
        for kk, c_ in zip((1, 2), word):
            if kk not in lam_ks: continue
            vr = 0 if uks[kk] == 'ab' else 1
            l0, l1 = B[0][vr][kk], B[1][vr][kk]; uu = V.new('ul%d' % kk)
            if c_ == 'A': extra.append(X.padd(X.pmul(uu, l0, p), X.pconst(1, p), p, -1))
            else: extra += [dict(l0), X.padd(X.pmul(uu, l1, p), X.pconst(1, p), p, -1)]
    urt = V.new('urt'); extra.append(X.padd(X.pmul(urt, X.pmul(t, X.padd(t, X.pconst(1, p), p), p), p), X.pconst(1, p), p, -1))
    return V, t, Wp, B, extra
def nsystem(p, chart, ci, piece, uk, dsplit, word=None):
    V, t, Wp, B, extra = nbasis_full(p, chart, ci, piece, uk, dsplit, word)
    polys = [q for q in gen_sym.equations_poly(B, Wp, p) + extra if q]
    return V.names, polys
def cellsystem(p, chart, ci, piece, uk, dsplit, word, scell, keyed=True):
    """N (as nbasis_full) + Y_1, Y_2 with the old S-cells (gen_n3.svectors scell 0/1/2), gauge forms (0,0) [N_P pivot] and (0,3) [v_3 row 0],
    and the Gram equation (F4) - the rho = 1 K-system of gen_n3/gen_sym_n3 with the N-part replaced by the piece."""
    V, t, Wp, B, extra = nbasis_full(p, chart, ci, piece, uk, dsplit, word)
    B = list(B); extra = list(extra); ells = [[(0, 0)], [(0, 3)]]
    S = gen_n3.svectors(p, scell, V)
    for r in range(2):
        co = [V.new('w%d_%d' % (r, d)) for d in range(12)]
        M = X.dc_matrix(co, p); D = [[dict(x) for x in row] for row in M]
        M = X.madd_const_col(M, S[r], 0, p)
        for ell in ells: extra.append(gen_n3.entry_form(D, ell, p))
        B.append(M)
    g = X.padd(X.pmul(gen_n3.ip(S[0], S[0], p), gen_n3.ip(S[1], S[1], p), p), X.pmul(gen_n3.ip(S[0], S[1], p), gen_n3.ip(S[0], S[1], p), p), p, -1)
    if g: extra.append(g)
    extra = [e for e in extra if e]
    return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra
if __name__ == '__main__':
    p = 2147483629
    for pc, uk, ds in (('IV1', 'ab:z1:0', None), ('Q2', 'ab:z1:0', None), ('Q1a', 'ab:z1:0', None), ('Q1b', 'ab:ab:z1', None), ('Q2', 'ab:ab:ab', 'nl')):
        n, pol = nsystem(p, 'A', 9, pc, uk, ds, 'AA' if pc == 'IV1' else None); assert len(n) == len(set(n)); print(pc, uk, ds, len(n), 'vars', len(pol), 'polys')
