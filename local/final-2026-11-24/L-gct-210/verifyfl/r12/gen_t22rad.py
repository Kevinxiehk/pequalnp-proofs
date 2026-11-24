import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""gen_t22rad.py -- RADICAL S-CELLS for [T22] with rho = 2 (round 13, NOTES R13.4).  Replaces the S-cells 0/1/2 + Gram equation.
   S = s(K) is a degenerate plane of V ((F4)); its radical C r is an isotropic line and S = r^perp.  By R13.1 the element Y_1 of K with
   s(Y_1) = r can be taken with columns 3 AND 4 equal to 0 (b_n(Y_1) in C v_n, n = 3, 4; subtract the N-elements with neutral part v_3 resp.
   v_4; for rho = 2 this normalisation is unique, since N has no element with zero neutral part).  Y_2: s(Y_2) = s_2, a complement of r in S
   in echelon form relative to r's pivot, standard gauge (ell entries 0).
   Radical cells (b_1, b_2, b_3 the basis of V of gen_n3.svectors):
     rc0: r = b_1 + rho b_2 + gam b_3, s_2 = b_2 + sig b_3      rc1: r = b_1 + rho b_2 + gam b_3, s_2 = b_3
     rc2: r = b_2 + gam b_3,           s_2 = b_1 + sig b_3      rc3: r = b_2 + gam b_3,           s_2 = b_3
     (r = b_3 is not isotropic: <b_3, b_3> = 2.)   Equations <r, r> = 0, <r, s_2> = 0.
   COVER: every degenerate plane S has a unique isotropic radical line C r in exactly one echelon cell, and S/C r has a unique echelon
   representative s_2 with zero coefficient at r's pivot; rc0..rc3 enumerate these.
   [R13.5 CORRECTION: columns 3, 4 of Y_1 are (r - r[vrow_n] v_n)/2, not 0.]  Y_1 = r e_0^T + D_P(c) + neutral columns (D_P: 6 coordinates); Y_2 = s_2 e_0^T + D(c') (12 coordinates)
   with ell(D(c')) = 0 for the two gauge forms of the N-basis.
   build(p, chart, ci, nb, nbargs, rc, keyed, xn): xn adds <v_n, b_n(Y_2)> = 0, |b_n(Y_2)|^2 = |s_2|^2 (n = 3, 4; (F3/F4)_p).
   nb = 'n3' (gen_n3.nbasis, original y-parametrisation), 't0c' (gen_t22t0c, piece IV
   all-ab det split; nbargs = dsplit), 't0b' (gen_t22t0b; nbargs = 'u0:u1:u2'), 'pc' (gen_t22pc; nbargs = 'PIECE/U0:U1:U2/DSPLIT')."""
import exactlib as X, gen_n1s, gen_n3, gen_sym, gen_sym_n3
def nbasis_any(p, cs, case, V, chart, nb, nbargs):
    if nb == 'n3': return gen_n3.nbasis(p, cs, case, V)
    if nb == 't0c':
        import gen_t22t0c; return gen_t22t0c.nbasis_t0c(p, cs, case, V, nbargs)
    if nb == 't0b':
        import gen_t22t0b; u = nbargs.split(':'); return gen_t22t0b.nbasis_t0(p, cs, case, V, u[0], u[1], None if u[2] == '-' else u[2])
    if nb == 'pc':
        import gen_t22pc; pc, uk, ds = nbargs.split('/'); return gen_t22pc.nbasis_pc(p, cs, case, V, chart, pc, uk.split(':'), None if ds == '-' else ds)
    if nb == 'sl':
        # R17.1 SINGLE-LINE sub-family of piece IV (rho = 2): all columns of N on ONE isotropic line u = v_3 = v_4 ('ab' chart):
        # N = u (x) L, Z_r = u lam_r^T, lam_r = (l_r0, l_r1, -l_r0 - l_r1 - 1, 1, 0) resp. (..., 0, 1); gauge entries (0,3), (0,4).
        from gen_t22t0 import isovec
        k, rho, piv, lc, t3, t4 = case; assert rho == 2 and t3 == 'ab' and t4 == 'ab'
        u, fu = isovec(p, cs, V, 'ab', '3'); Bn = []
        for r_ in range(2):
            l0, l1 = V.new('l%d0' % r_), V.new('l%d1' % r_)
            neu = [X.pconst(1, p), {}] if r_ == 0 else [{}, X.pconst(1, p)]
            l2 = X.padd(X.padd(X.pmul(X.pconst(p - 1, p), l0, p), l1, p, -1), X.pconst(1, p), p, -1)
            lam = [l0, l1, l2] + neu
            Bn.append([[X.pmul(lam[j], u[a], p) for j in range(5)] for a in range(4)])
        return Bn, list(fu), [[(0, 3)], [(0, 4)]]
    raise ValueError(nb)
def build(p, chart, ci, nb, nbargs, rc, keyed=False, calib_rho1=False, xn=False, rsplit=None, perm34=False, permP=False, gam0=False, spec=None, rab=False, lamch=None, mu=False, muperm=False, p2rank=None, alsplit=None):
    """calib_rho1 (CALIBRATION ONLY, not a valid cover): allow a rho = 1 case; Y_1 then also gets the N_P pivot gauge (ells[0])."""
    case = gen_n1s.cases(2)[ci]; assert case[1] == 2 or (calib_rho1 and case[1] == 1)
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    B, extra, ells = nbasis_any(p, cs, case, V, chart, nb, nbargs)
    extra = list(extra)
    if perm34:
        # R14.4 [rigorous given the '0'-chart pieces]: in piece IV (t0c: u_0, u_1, u_2 all 'ab'), the quartic part of C_n for a NEUTRAL column
        # n is perm(Z^(n)) = prod_{k != n} lam_k(Z) perm[u_k]_{k != n} = 0 on N; lam_3, lam_4 are not identically 0 (rho = 2), so either some
        # lam_k (k <= 2) vanishes on N (= a '0'-chart piece, all UNIT) or perm[u_0,u_1,u_2,v_4] = perm[u_0,u_1,u_2,v_3] = 0.
        assert nb == 't0c'
        ix = {n_: i_ for i_, n_ in enumerate(V.names)}; var = lambda n_: {(ix[n_],): 1}
        def abvec(tag):
            a_, b_ = var('a' + tag), var('b' + tag)
            return [X.pconst(1, p), a_, b_, X.padd(X.padd(X.pconst(p - 1, p), a_, p, -1), b_, p, -1)]
        same = {'01': {1: 0}, '02': {2: 0}, '12': {2: 1}}.get(nbargs, {})
        us = []
        for j in range(3): us.append(us[same[j]] if j in same else abvec('u%d' % j))
        v3_, v4_ = abvec('3'), abvec('4')
        import itertools
        def perm4(cols):
            q = {}
            for f in itertools.permutations(range(4)):
                term = X.pconst(1, p)
                for a_ in range(4): term = X.pmul(term, cols[f[a_]][a_], p)
                q = X.padd(q, term, p)
            return q
        extra += [perm4(us + [v4_]), perm4(us + [v3_])]
        if permP:
            # R14.5: quartic parts of the P-columns: perm(Z^(j)) = theta_4(Z) m_j, j = 0, 1, 2, so m_1 perm(Z^(0)) = m_0 perm(Z^(1)) etc.;
            # cancelling lam_2 lam_3 lam_4 (resp. lam_1 lam_3 lam_4), all != 0 off the '0'-chart pieces:
            #   m_1 lam_1 Q_0 = m_0 lam_0 Q_1  and  m_2 lam_2 Q_0 = m_0 lam_0 Q_2  as linear forms on N  (Q_j = perm[u_k]_{k != j}).
            ucols = us + [v3_, v4_]
            Q = [perm4([ucols[k] for k in range(5) if k != j]) for j in range(3)]
            one_ = X.pconst(1, p)
            mm = [one_, t, X.pmul(X.pconst(p - 1, p), X.padd(one_, t, p), p)] if chart == 'A' else [t, one_, X.pmul(X.pconst(p - 1, p), X.padd(one_, t, p), p)]
            for Zr in B[:2]:
                lam = [Zr[0][k] for k in range(3)]              # u_k[0] = 1 ('ab'), so lam_k(Z_r) = entry (0, k)
                extra.append(X.padd(X.pmul(X.pmul(mm[1], lam[1], p), Q[0], p), X.pmul(X.pmul(mm[0], lam[0], p), Q[1], p), p, -1))
                extra.append(X.padd(X.pmul(X.pmul(mm[2], lam[2], p), Q[0], p), X.pmul(X.pmul(mm[0], lam[0], p), Q[2], p), p, -1))
    bb = [[X.pconst(x, p) for x in row] for row in ([1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1])]
    lin = lambda cs_: [X.padd({}, {}, p) if False else sum_vec(cs_, a) for a in range(4)]
    def sum_vec(cs_, a):
        q = {}
        for c, i in cs_: q = X.padd(q, X.pmul(c, bb[i][a], p), p)
        return q
    one = X.pconst(1, p)
    if rc in (0, 1):
        rho = V.new('rrho'); gam = V.new('rgam'); r = [sum_vec([(one, 0), (rho, 1), (gam, 2)], a) for a in range(4)]
        if rc == 0: sig = V.new('rsig'); s2 = [sum_vec([(one, 1), (sig, 2)], a) for a in range(4)]
        else: s2 = [sum_vec([(one, 2)], a) for a in range(4)]
    elif rc in (2, 3):
        gam = V.new('rgam'); r = [sum_vec([(one, 1), (gam, 2)], a) for a in range(4)]
        if rc == 2: sig = V.new('rsig'); s2 = [sum_vec([(one, 0), (sig, 2)], a) for a in range(4)]
        else: s2 = [sum_vec([(one, 2)], a) for a in range(4)]
    elif rc in (4, 5):
        # R14.6 OPEN radical chart {r_3 != 0} (coefficient of b_3): r = alp b_1 + bet b_2 + b_3; s_2 = complement in S = r^perp with zero
        # b_3-coefficient: rc4: s_2 = b_1 + sig b_2, rc5: s_2 = b_2.  (Staged refinement: once rc4, rc5 are UNIT, the other cells may add
        # gam = 0 - see option gam0.)
        al_ = V.new('ralp'); be_ = V.new('rbet'); r = [sum_vec([(al_, 0), (be_, 1), (one, 2)], a) for a in range(4)]
        if rc == 4: sig = V.new('rsig'); s2 = [sum_vec([(one, 0), (sig, 1)], a) for a in range(4)]
        else: s2 = [sum_vec([(one, 1)], a) for a in range(4)]
    elif rc in (6, 7):
        # R15.7 RATIONAL radical cells: the isotropic lines of V are C w(tau), w(tau) = chi_1 + 2 tau chi_2 - 2 tau^2 chi_3, and C chi_3
        # (chi_1 = (1,i,-1,-i), chi_2 = (1,-1,1,-1), chi_3 = (1,-i,-1,i)).  <w, w'> = 0, so S = r^perp = span(w(tau), w'(tau)) with
        # w'(tau) = 2 chi_2 - 4 tau chi_3 (never parallel to w): rc6 = all tau, NO extra equation; rc7: r = chi_3, s_2 = chi_2.
        c1 = [X.pconst(x, p) for x in cs.chi1]; c2 = [X.pconst(x, p) for x in cs.chi2]; c3 = [X.pconst(x, p) for x in cs.chi3]
        if rc == 6:
            tau = V.new('rtau'); t2 = X.pmul(tau, tau, p)
            r = [X.padd(X.padd(c1[a], X.pmul(X.pmul(X.pconst(2, p), tau, p), c2[a], p), p), X.pmul(X.pmul(X.pconst(2, p), t2, p), c3[a], p), p, -1) for a in range(4)]
            s2 = [X.padd(X.pmul(X.pconst(2, p), c2[a], p), X.pmul(X.pmul(X.pconst(4, p), tau, p), c3[a], p), p, -1) for a in range(4)]
        else: r = c3; s2 = c2
    else: raise ValueError(rc)
    extra += [gen_n3.ip(r, r, p), gen_n3.ip(r, s2, p)]
    if lamch is not None:
        # R17.4 JUNK REMOVAL: the branches "column k of N vanishes" (lam_k == 0 on N, k = 0, 1, 2) belong to the '0'-chart pieces, which are
        # decided UNIT; they survive inside every piece-IV system (the quartic N-coefficients only force a PRODUCT of linear forms to vanish)
        # and make the GBs heavy.  Charts per k: 'A' lam_k(Z_1) != 0;  'B' lam_k(Z_1) = 0, lam_k(Z_2) != 0.  The 8 words cover the
        # complement of the decided branches.  lam_k(Z_r) = entry (0, k) of Z_r (u_k[0] = 1 in the 'ab' chart; t0c pieces).
        assert nb in ('t0c', 't0b') and len(lamch) == 3
        uks = ['ab', 'ab', 'ab'] if nb == 't0c' else nbargs.split(':')
        for k_, c_ in enumerate(lamch):
            if uks[k_] == '0': continue                       # column k is 0 by construction (no lam_k)
            vr_ = 0 if uks[k_] == 'ab' else 1                  # u_k[vr_] = 1
            l1_, l2_ = B[0][vr_][k_], B[1][vr_][k_]
            uu = V.new('ul%d' % k_)
            if c_ == 'A': extra.append(X.padd(X.pmul(uu, l1_, p), X.pconst(1, p), p, -1))
            else: extra += [dict(l1_), X.padd(X.pmul(uu, l2_, p), X.pconst(1, p), p, -1)]
    if mu:
        # R17.5 JUNK REMOVAL for the pieces P2 / P1a / P1b: the isotropic-column generator (P1a/P1b: B[0]; P2: B[1]) has columns mu_k u_k;
        # mu_k = 0 is the item with u_k = '0' of the same piece (decided separately), so in an item with u_k != '0' we may impose mu_k != 0:
        # uu * (entry (vrow(u_k), k)) = 1, vrow = 0 for 'ab', 1 for z1/z2 (u_k[vrow] = 1).
        assert nb == 'pc'
        pc_, uk_, ds_ = nbargs.split('/'); uks = uk_.split(':')
        Zi = B[1] if pc_ == 'P2' else B[0]
        for k_ in range(3):
            if uks[k_] == '0': continue
            vr_ = 0 if uks[k_] == 'ab' else 1
            uu = V.new('um%d' % k_); extra.append(X.padd(X.pmul(uu, Zi[vr_][k_], p), X.pconst(1, p), p, -1))
    if muperm:
        # R17.7 single-element quartic relations for the isotropic-column generator Z_i of a P-piece (valid with mu: all mu_k != 0):
        # C_n(s Z_i) == 24 for neutral n, so perm(Z_i^(n)) = 0.  P1a/P1b (Z_i = B[0], neutral part (v_3, 0)): perm[u_0,u_1,u_2,v_3] = 0.
        # P2 (Z_i = B[1], neutral part (alp v_3, v_4)): perm[u_0,u_1,u_2,v_4] = 0 and alp * perm[u_0,u_1,u_2,v_3] = 0.
        assert nb == 'pc' and mu
        import itertools as _it
        pc_, uk_, ds_ = nbargs.split('/'); uks = uk_.split(':')
        if '0' not in uks:
            ix = {n_: i_ for i_, n_ in enumerate(V.names)}; var = lambda n_: {(ix[n_],): 1}
            def vec(kind, tag):
                if kind == 'ab':
                    a_, b_ = var('a' + tag), var('b' + tag)
                    return [X.pconst(1, p), a_, b_, X.padd(X.padd(X.pconst(p - 1, p), a_, p, -1), b_, p, -1)]
                return [X.pconst(c, p) for c in ((0, 1, cs.w, cs.w * cs.w % p) if kind == 'z1' else (0, 1, cs.w * cs.w % p, cs.w))]
            same = {'01': {1: 0}, '02': {2: 0}, '12': {2: 1}}.get(ds_, {})
            us = []
            for j in range(3): us.append(us[same[j]] if j in same else vec(uks[j], 'u%d' % j))
            case_ = gen_n1s.cases(2)[ci]; v3_, v4_ = vec(case_[4], '3'), vec(case_[5], '4')
            def perm4(cols):
                q = {}
                for f in _it.permutations(range(4)):
                    term = X.pconst(1, p)
                    for a_ in range(4): term = X.pmul(term, cols[f[a_]][a_], p)
                    q = X.padd(q, term, p)
                return q
            if pc_ in ('P1a', 'P1b'): extra.append(perm4(us + [v3_]))
            else: extra += [perm4(us + [v4_]), X.pmul(var('alp'), perm4(us + [v3_]), p)]
    if alsplit is not None:
        # R18.4 P2: split by alpha (Z_a = alpha Z_1 + Z_2): 'a0' alpha = 0 (Z_2 itself isotropic: neutral part of Z_a = (0, v_4)),
        # 'an' alpha != 0 (Rabinowitsch).
        assert nb == 'pc' and nbargs.startswith('P2/')
        ixa = V.names.index('alp')
        if alsplit == 'a0': extra.append({(ixa,): 1})
        else: ua_ = V.new('ual'); extra.append(X.padd(X.pmul(ua_, {(ixa,): 1}, p), X.pconst(1, p), p, -1))
    if p2rank is not None:
        # R18.1 P2 split by the RANK of vartheta on N = span(Z_1, Z_a) (vartheta(Z_a) = 0, vartheta(Z_1) != 0): disc = -vartheta(Z_1, Z_a)^2.
        # 'r1': vartheta(Z_1, Z_a) = 0 (Z_a is the radical): <c_j(Z_1), c_j(Z_a)> = vartheta(Z_1,Z_a) m_j = 0 for j = 0,1,2 and, with mu,
        #       <c_j(Z_1), u_j> = 0 (written as <c_j(Z_1), c_j(Z_a)> = 0; the mu_k != 0 Rabinowitsch makes them equivalent);
        # 'r2': vartheta(Z_1, Z_a) != 0 (Rabinowitsch).
        assert nb == 'pc' and nbargs.startswith('P2/')
        Z1_, Za_ = B[0], B[1]
        col_ = lambda M_, j_: [M_[a][j_] for a in range(4)]
        j0_ = 0 if chart == 'A' else 1
        th1a = gen_n3.ip(col_(Z1_, j0_), col_(Za_, j0_), p)
        if p2rank == 'r1': extra += [gen_n3.ip(col_(Z1_, j_), col_(Za_, j_), p) for j_ in range(3)]
        else: ur_ = V.new('ur2'); extra.append(X.padd(X.pmul(ur_, th1a, p), X.pconst(1, p), p, -1))
    if rab:
        # R16.2: under R11.6 only m off the two-column points matter, so the Rabinowitsch condition urt t (t+1) = 1 may be imposed from the
        # START (chart A: t = 0, -1 are the two-column points); it removes the two-column solution components before any stage.
        urt = V.new('urt'); extra.append(X.padd(X.pmul(urt, X.pmul(t, X.padd(t, X.pconst(1, p), p), p), p), X.pconst(1, p), p, -1))
    if spec is not None:
        # R16.1 SPECIAL RADICALS: an isotropic sum-zero r has e_1(r) = e_2(r) = 0, so its entries are the roots of x^4 - e_3 x + e_4.
        # Special points: e_4(r) = 0 (an entry of r vanishes; K_2 is of this kind) and e_3(r) = 0 (r a row-permutation of chi_1 = 4th roots
        # of unity; chi_3 is one).  Pieces: 'e3' (e_3(r) = 0), 'e4' (e_4(r) = 0), 'gen' (uspec e_3(r) e_4(r) = 1); together = the cell.
        import itertools as _it
        def esym(k):
            q = {}
            for cmb in _it.combinations(range(4), k):
                term = X.pconst(1, p)
                for a in cmb: term = X.pmul(term, r[a], p)
                q = X.padd(q, term, p)
            return q
        e3, e4 = esym(3), esym(4)
        if spec == 'e3': extra.append(e3)
        elif spec == 'e4': extra.append(e4)
        else: us_ = V.new('uspec'); extra.append(X.padd(X.pmul(us_, X.pmul(e3, e4, p), p), X.pconst(1, p), p, -1))
    if gam0 and rc in (0, 1, 2, 3):
        # STAGED REFINEMENT (ncol, BRIEF UPDATE 16): valid only AFTER the open chart {r_3 != 0} (rc4 + rc5) is verified empty for this piece:
        # then every point has r_3 = 0, i.e. gam = 0.
        extra.append(dict(gam))
    # Y_1: radical element, columns 3, 4 zero
    co1 = [V.new('w0_%d' % d) for d in range(6)]
    Y1 = X.dcsub_matrix(co1, [0, 1, 2], p)
    if calib_rho1: extra.append(gen_n3.entry_form(Y1, ells[0], p))
    # neutral columns of Y_1 (R13.5): y_n(Y_1) = (r - r[vrow_n] v_n)/2 for an active neutral column n (b_n(Y_1) = 2 y_n - r in C v_n,
    # gauge entry (vrow_n, n) = 0); v_n = column n of the N-generator Z with Z[vrow_n][n] = 1.
    half = X.pconst((p + 1) // 2, p)
    for n in (3, 4):
        vr = [e for ell in ells for e in ell if e[1] == n]
        if calib_rho1 and not vr:                                   # CALIBRATION ONLY: inactive column -> free sum-zero column
            fv = [V.new('w0n%d_%d' % (n, a)) for a in range(3)]; cn = fv + [X.pmul(X.pconst(p - 1, p), X.padd(X.padd(fv[0], fv[1], p), fv[2], p), p)]
        else:
            vrow = vr[0][0]; Zs = [Z for Z in B if Z[vrow][n] == {(): 1}]; assert len(Zs) == 1, ('no unique N-generator for column', n)
            vn = [Zs[0][a][n] for a in range(4)]
            cn = [X.pmul(half, X.padd(r[a], X.pmul(r[vrow], vn[a], p), p, -1), p) for a in range(4)]
        for a in range(4):
            Y1[a][n] = X.padd(Y1[a][n], cn[a], p); Y1[a][2] = X.padd(Y1[a][2], cn[a], p, -1)
    Y1 = X.madd_const_col(Y1, r, 0, p)
    # Y_2: standard gauge
    co2 = [V.new('w1_%d' % d) for d in range(12)]
    M = X.dc_matrix(co2, p); D = [[dict(x) for x in row] for row in M]
    for ell in ells: extra.append(gen_n3.entry_form(D, ell, p))
    Y2 = X.madd_const_col(M, s2, 0, p)
    if rsplit is not None:
        # R14.2: split of a radical cell by the position of r relative to v_3, v_4 (all isotropic, first coordinate 1 in rc0/rc1 and in the
        # 'ab' charts): <r, v_n> = 0 <=> r || v_n <=> r = v_n.  Pieces: 'v3' (r = v_3), 'v4' (r = v_4), 'gen' (<r,v_3> != 0 != <r,v_4>).
        assert rc in (0, 1)
        vv = {}
        for n in (3, 4):
            vr = [e for ell in ells for e in ell if e[1] == n][0]; Zs = [Z for Z in B if Z[vr[0]][n] == {(): 1}]
            vv[n] = [Zs[0][a][n] for a in range(4)]; assert vv[n][0] == {(): 1}, 'r-split needs v_n in the ab chart'
        if rsplit in ('v3', 'v4'):
            n = int(rsplit[1]); extra += [X.padd(r[a], vv[n][a], p, -1) for a in range(4)]
        else:
            u3 = V.new('ur3'); u4 = V.new('ur4')
            extra += [X.padd(X.pmul(u3, gen_n3.ip(r, vv[3], p), p), X.pconst(1, p), p, -1), X.padd(X.pmul(u4, gen_n3.ip(r, vv[4], p), p), X.pconst(1, p), p, -1)]
    if xn:   # (F3/F4)_p consequences for the neutral columns n = 3, 4: <v_n, b_n(Y_2)> = 0 and |b_n(Y_2)|^2 = |s_2|^2 (b_n^* g = s^* g)
        for n in (3, 4):
            vr = [e for ell in ells for e in ell if e[1] == n]
            bn = [X.padd(X.pmul(X.pconst(2, p), Y2[a][n], p), s2[a], p, -1) for a in range(4)]      # b_n(Y_2) = 2 y_n - s_2
            extra.append(X.padd(gen_n3.ip(bn, bn, p), gen_n3.ip(s2, s2, p), p, -1))
            if vr:
                Zs = [Z for Z in B if Z[vr[0][0]][n] == {(): 1}]; vn = [Zs[0][a][n] for a in range(4)]
                extra.append(gen_n3.ip(vn, bn, p))
    B = list(B) + [Y1, Y2]
    extra = [e for e in extra if e]
    if keyed: return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra
    return V.names, gen_sym.equations_poly(B, Wp, p) + extra
if __name__ == '__main__':
    p = 2147483629
    for rc in range(4):
        n, e = build(p, 'A', 0, 'n3', None, rc); assert len(n) == len(set(n)), ('duplicate variable names', rc)
    for nb, a in (('n3', None), ('t0c', '01'), ('t0b', 'ab:z1:-'), ('pc', 'P2/ab:z1:0/-')):
        for rc in range(4):
            n, e = build(p, 'A', 0, nb, a, rc)
            M = None
        print(nb, a, 'vars', len(n), 'eqs', len(e))
    # column sums / row sums of Y_1 (symbolic): rebuild and check
    cs = X.Consts(p); V = X.Vars(); V.new('mt')
    co1 = [V.new('w0_%d' % d) for d in range(6)]; Y1 = X.dcsub_matrix(co1, [0, 1, 2], p)
    for a in range(4):
        s = {}
        for j in range(5): s = X.padd(s, Y1[a][j], p)
        assert not s
    for j in range(5):
        s = {}
        for a in range(4): s = X.padd(s, Y1[a][j], p)
        assert not s
    print('self-check ok: D_P part doubly centred')
