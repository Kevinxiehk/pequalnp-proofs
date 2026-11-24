import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_n3.py -- [T22]: 4-dim COLUMN-CENTRED spaces K of type (q,d) = (2,2) with defect in C m, m supported on columns 0,1,2
   (columns 3, 4 neutral; also usable for 'two' = (1,-1,0,0,0), where column 2 is treated like a column of P).   (round 7, verifyfl)
   Mathematics: COMPUTE-verifyfl.md NEXT N3; NOTES-verifyfl.md DI5-R7.
   K = N (+) C Y_1 (+) C Y_2,  N = K cap ker s (2-dim doubly centred, defect in C m),  S = s(K) a plane in V.
   N is parametrised EXACTLY as in gen_n1s.py with k = 2 (case = (2, rho, pivots of N_P, line cell, vtype3, vtype4); all 96 cases
   together cover every 2-dim doubly centred space with defect in C m, by (F2), valid in characteristic p > 3).
   S: reduced-echelon cell of Gr(2,3) in the basis b_1, b_2, b_3 of V:  scell 0: s_1 = b_1 + al b_3, s_2 = b_2 + be b_3;
      scell 1: s_1 = b_1 + al b_2, s_2 = b_3;   scell 2: s_1 = b_2, s_2 = b_3.
   (F4) [char p > 3]: if a neutral column is active on N (rho >= 1) then S is degenerate: Gram determinant of (s_1, s_2) = 0 is added.
   Y_r = s_r e_0^T + D(c_r) (D = doubly centred, 12 coordinates); gauge Y_r -> Y_r + N fixed by two linear forms ell_1, ell_2 on D
   with det [ell_i(Z_j)] = 1 (triangular), chosen per case (see gauge()).
   Mode Nfix=NAME (calibration): N = an explicit plane from NFIX below; gauge = D-coordinates at the rref pivots of N.
   Equations: all coefficients in (x_1..x_4) of R_i(x_1 Z_1 + x_2 Z_2 + x_3 Y_1 + x_4 Y_2), the isotropy quadrics of the line charts,
   the gauge equations, and the Gram equation (if rho >= 1 and not Nfix).
   usage: python3 -I gen_n3.py P MSPEC OUTDIR [cases=i,j,..|all] [scells=0,1,2] [Nfix=NAME] [gram=0|1] [run] [timeout=T]"""
import exactlib as X, gen_n1s, time
def nbasis(p, cs, case, V):
    """the two generators of N for a gen_n1s case with k = 2 (same construction as gen_n1s.build); returns (B, extra, ells),
    ells = list of linear forms on 4x5 matrices, given as lists of (row, col) entries whose SUM is the form."""
    k, rho, piv, lc, t3, t4 = case; assert k == 2
    rows = X.echelon_rows(6, piv, V, 'u') if k - rho > 0 else []
    B = [X.dcsub_matrix(r, [0, 1, 2], p) for r in rows]
    ells = [[(d % 3, d // 3)] for d in piv]                        # P-coordinate d = 3t + a  ->  entry (a, t)
    vec = {}; extra = []; vrow = {}
    for name, t in (('3', t3), ('4', t4)):
        if t == 'ab':
            a = V.new('a' + name); b = V.new('b' + name); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
            vec[name] = [X.pconst(1, p), a, b, last]; vrow[name] = 0
            q = X.pconst(1, p)
            for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
            extra.append(q)
        elif t == 'z1': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)]; vrow[name] = 1
        elif t == 'z2': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w * cs.w % p, cs.w)]; vrow[name] = 1
        else: vec[name] = None
    if rho == 2: nus = [({(): 1}, {}), ({}, {(): 1})]; nell = [[(vrow['3'], 3)], [(vrow['4'], 4)]]
    elif rho == 1:
        if lc == 0: nus = [({(): 1}, V.new('al'))]; nell = [[(vrow['3'], 3)]]
        else: nus = [({}, {(): 1})]; nell = [[(vrow['4'], 4)]]
    else: nus = []; nell = []
    for r, (l3, l4) in enumerate(nus):
        co = [({} if d in piv else V.new('y%d_%d' % (r, d))) for d in range(6)]
        M = X.dcsub_matrix(co, [0, 1, 2], p)
        for lam, name, col in ((l3, '3', 3), (l4, '4', 4)):
            if lam and vec[name] is not None:
                for a in range(4):
                    e = X.pmul(lam, vec[name][a], p); M[a][col] = X.padd(M[a][col], e, p); M[a][2] = X.padd(M[a][2], e, p, -1)
        B.append(M)
    # order of B: N_P generators first, then complement elements; ells in the same order -> [ell_i(Z_j)] is the identity
    return B, extra, ells + nell
def NFIX(cs, p):
    zeta, zb, chi1 = cs.zeta, cs.zetab, cs.chi1
    return {'II': [X.outer(zeta, [1, p - 1, 0, 0, 0], p), X.outer(zb, [0, 0, 0, 1, p - 1], p)],        # type II plane, pairs (0,1),(3,4)
            'II2': [X.outer(zeta, [1, 0, p - 1, 0, 0], p), X.outer(zb, [0, 1, 0, p - 1, 0], p)],       # type II plane, pairs (0,2),(1,3)
            'IP': [X.outer(chi1, [1, p - 1, 0, 0, 0], p), X.outer(chi1, [0, 1, p - 1, 0, 0], p)],      # type I' plane chi_1 x W_P
            'I034': [X.outer(chi1, [1, 0, 0, p - 1, 0], p), X.outer(chi1, [1, 0, 0, 0, p - 1], p)],    # type I plane chi_1 x Lam_{0,3,4}
            'K2N': [X.outer(zeta, [1, p - 1, 0, 0, 0], p), X.outer(zb, [0, 0, p - 1, 1, 0], p)]}      # N of the control K_2
def svectors(p, scell, V):
    b = [[1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1]]
    def lin(c0, i0, c1=None, i1=None):
        return [X.padd(X.pmul(c0, X.pconst(b[i0][a], p), p), X.pmul(c1, X.pconst(b[i1][a], p), p) if c1 is not None else {}, p) for a in range(4)]
    one = X.pconst(1, p)
    if scell == 0: al = V.new('sal'); be = V.new('sbe'); return [lin(one, 0, al, 2), lin(one, 1, be, 2)]
    if scell == 1: al = V.new('sal'); return [lin(one, 0, al, 1), lin(one, 2)]
    return [lin(one, 1), lin(one, 2)]
def ip(u, v, p):
    q = {}
    for a in range(4): q = X.padd(q, X.pmul(u[a], v[a], p), p)
    return q
def entry_form(M, ell, p):
    q = {}
    for (a, c) in ell: q = X.padd(q, M[a][c], p)
    return q
def build(p, mspec, case, scell, nfix=None, gram=None, keyed=False):
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
    if nfix is None:
        B, extra, ells = nbasis(p, cs, case, V); rho = case[1]
    else:
        B = [[[X.pconst(x, p) for x in row] for row in Mz] for Mz in NFIX(cs, p)[nfix]]; extra = []; rho = None
        rows, piv = X.rref([[Mz[a][q] for a in range(3) for q in range(4)] for Mz in NFIX(cs, p)[nfix]], p)
        assert len(piv) == 2
        ells = [[(d // 4, d % 4)] for d in piv]
        # replace the generators by the rref combination so that [ell_i(Z_j)] = identity
        B = [X.dc_matrix([X.pconst(x, p) for x in r], p) for r in rows]
    S = svectors(p, scell, V)
    for r in range(2):
        co = [V.new('w%d_%d' % (r, d)) for d in range(12)]
        M = X.dc_matrix(co, p)
        D = [[dict(x) for x in row] for row in M]
        M = X.madd_const_col(M, S[r], 0, p)
        for ell in ells: extra.append(entry_form(D, ell, p))          # gauge: ell(D-part of Y_r) = 0
        B.append(M)
    use_gram = (rho is not None and rho >= 1) if gram is None else bool(gram)
    if use_gram:
        g = X.padd(X.pmul(ip(S[0], S[0], p), ip(S[1], S[1], p), p), X.pmul(ip(S[0], S[1], p), ip(S[0], S[1], p), p), p, -1)
        if g: extra.append(g)
    if keyed: return V.names, X.equations(B, W, p, keyed=True), [e for e in extra if e]
    polys, nx = X.equations(B, W, p)
    return V.names, polys + [e for e in extra if e]
def casename(c, s): return gen_n1s.casename(c) + '_s%d' % s
def main():
    p = int(sys.argv[1]); mspec = sys.argv[2]; outdir = sys.argv[3]
    opts = dict(a.split('=', 1) for a in sys.argv[4:] if '=' in a); run = 'run' in sys.argv; tmo = float(opts.get('timeout', 60))
    nfix = opts.get('Nfix'); gram = int(opts['gram']) if 'gram' in opts else None
    cl = gen_n1s.cases(2)
    idx = list(range(len(cl))) if opts.get('cases', 'all') == 'all' else [int(c) for c in opts['cases'].split(',')]
    if nfix: idx = [-1]
    scells = [int(s) for s in opts.get('scells', '0,1,2').split(',')]
    os.makedirs(outdir, exist_ok=True); tag = 'n3_%s_p%d%s' % (mspec.replace(',', '_'), p, '_fix' + nfix if nfix else '')
    man = open(os.path.join(outdir, tag + '.manifest'), 'a'); t0 = time.time(); stats = {}
    for i in idx:
        for s in scells:
            case = cl[i] if i >= 0 else None
            names, polys = build(p, mspec, case, s, nfix, gram)
            fn = os.path.join(outdir, '%s_%s.ms' % (tag, casename(case, s) if case else 's%d' % s))
            if X.trivially_unit(polys): verdict = 'UNIT(constant-equation)'; extra = ''
            else:
                X.write_msolve(fn, names, p, polys); verdict = 'not-run'; extra = ''
                if run:
                    v, nb, dt = X.run_msolve(fn, timeout=tmo); verdict = v; extra = ' basis=%s time=%.2fs' % (nb, dt)
                    if v == 'UNIT':
                        os.remove(fn)
                        if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
            stats[verdict] = stats.get(verdict, 0) + 1
            man.write('%s case=%s idx=%d scell=%d nvars=%d npolys=%d verdict=%s%s\n' % (os.path.basename(fn), case, i, s, len(names), len(polys), verdict, extra)); man.flush()
            print(i, case, 's%d' % s, len(names), 'vars', verdict, extra, flush=True)
    print('%s: %s  (%.0fs)' % (tag, stats, time.time() - t0))
if __name__ == '__main__': main()
