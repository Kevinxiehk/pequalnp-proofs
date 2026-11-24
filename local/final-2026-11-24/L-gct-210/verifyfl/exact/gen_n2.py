import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_n2.py -- [T31]: 4-dim COLUMN-CENTRED spaces K of type (q,d) = (3,1) with defect in C m  (round 7, verifyfl).
   Mathematics: COMPUTE-verifyfl.md NEXT N2; NOTES-verifyfl.md DI5-R7.
   (F3) [valid in every characteristic p > 3, see DI5-R7]: if q = 3 the doubly centred line N = C Zs has all NEUTRAL columns 0,
        i.e. Zs lies in dcsub(P) = doubly centred matrices supported on the columns of P = supp m (dim 3(|P|-1)).
   Unknowns of a cell:
     Zs   : reduced-echelon cell of P(dcsub(P)): coordinate c (= entry (a, P[t]), c = 3t + a) equal to 1, coordinates < c equal to 0;
     Y_r  : r = 1..R, Y_r = s_r e_0^T + D(c_r), D = doubly centred 4x5 matrices (12 coordinates 4a+q = entry (a,q), a < 3, q < 4),
            s_r = prescribed row-sum vectors (default b_1 = (1,-1,0,0), b_2 = (0,1,-1,0), b_3 = (0,0,1,-1), a basis of V);
            gauge Y_r -> Y_r + c Zs fixed by "D-coordinate of Y_r at the pivot entry of Zs = 0" (Zs has 1 there).
   COMPLETENESS (q = 3): s(K) = V, so K contains Y_r with s(Y_r) = b_r, unique modulo Zs; scale Zs into its echelon cell.
   stage a: R = 2 (K would contain the 3-dim space span(Zs, Y_1, Y_2): UNIT for all cells => no type (3,1));  stage b: R = 3.
   Equations: all coefficients in (x_0..x_R) of R_i(x_0 Zs + x_1 Y_1 + ... + x_R Y_R)  (exactlib.equations).
   Options: stage=a|b, svec=NAME;NAME[;NAME] (names: b1 b2 b3 zb zeta h chi1 chi2 chi3), zsfix=NAME:l0,l1,l2,l3,l4 (Zs fixed to the outer
   product NAME l^T; calibration), cells=i,j,..., timeout=T, run.
   usage: python3 -I gen_n2.py P MSPEC OUTDIR [options]"""
import exactlib as X, time
def vecs(cs):
    p = cs.p
    return {'b1': [1, p - 1, 0, 0], 'b2': [0, 1, p - 1, 0], 'b3': [0, 0, 1, p - 1], 'zb': cs.zetab, 'zeta': cs.zeta, 'h': cs.h,
            'chi1': cs.chi1, 'chi2': cs.chi2, 'chi3': cs.chi3}
def support(m, mspec):
    if m is None: return [0, 1, 2, 3, 4]
    return [j for j in range(5) if m[j]]
def cells(p, mspec):
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs); P = support(m, mspec)
    return list(range(3 * (len(P) - 1)))
def rank1_cells():
    return [(vt, lc) for vt in ('ab', 'z1', 'z2') for lc in (0, 1)]
def build(p, mspec, cell, stage='a', svec=None, zsfix=None, keyed=False, zsmode=None):
    """zsmode (case split of a cell by vartheta(Zs) = <z_P0,z_P0>/m_P0, valid in char p):
       'B'     : the echelon cell plus u*<z_P0,z_P0> = 1               (vartheta(Zs) != 0);
       'A'     : the echelon cell plus <z_P0,z_P0> = 0                 (vartheta(Zs) = 0);
       ('R1', vt, lc): vartheta(Zs) = 0 parametrised: Zs = v l^T, v isotropic (chart vt), l zero-sum on P (lc = 0: l_P0 = 1, free
               l_P1..; lc = 1: l_P0 = 0, l_P1 = 1) [char p: columns of Zs pairwise orthogonal isotropic => rank 1]; |P| = 3 only.
               The 6 pairs (vt, lc) cover all; 'cell' is ignored."""
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs); P = support(m, mspec); V = X.Vars(); vv = vecs(cs)
    R = 2 if stage == 'a' else 3
    S = [vv[n] for n in (svec or ['b1', 'b2', 'b3'])][:R]
    nz = 3 * (len(P) - 1)
    extra = []
    if isinstance(zsmode, tuple):
        _, vt, lc = zsmode; assert len(P) == 3
        if vt == 'ab':
            a = V.new('va'); b = V.new('vb'); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
            v = [X.pconst(1, p), a, b, last]; q = X.pconst(1, p)
            for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
            extra.append(q); vrow = 0
        elif vt == 'chi1':                     # split A after R8.2: v = chi_1 (row symmetry), all l_j != 0 (use lc = 0)
            v = [X.pconst(c, p) for c in cs.chi1]; vrow = 0
        else:
            v = [X.pconst(c, p) for c in ((0, 1, cs.w, cs.w * cs.w % p) if vt == 'z1' else (0, 1, cs.w * cs.w % p, cs.w))]; vrow = 1
        if lc == 0:
            t = V.new('lt'); l = {P[0]: X.pconst(1, p), P[1]: t, P[2]: X.padd(X.pconst(-1, p), t, p, -1)}; lcol = P[0]
        elif lc == 2:                          # kind (R2): Zs = v (e_P0 - e_P1)^T (needed when m_P0 = m_P1, e.g. (1,1,-2,0,0))
            l = {P[0]: X.pconst(1, p), P[1]: X.pconst(-1, p), P[2]: {}}; lcol = P[0]
        else:
            l = {P[0]: {}, P[1]: X.pconst(1, p), P[2]: X.pconst(-1, p)}; lcol = P[1]
        Zs = [[(X.pmul(v[a], l[c], p) if c in l else {}) for c in range(5)] for a in range(4)]
        piv = 3 * P.index(lcol) + vrow
    elif zsfix is None:
        row = X.echelon_rows(nz, (cell,), V, 'z')[0]
        Zs = X.dcsub_matrix(row, P, p); piv = cell
        if zsmode in ('A', 'B'):
            nrm = {}
            for a in range(4): nrm = X.padd(nrm, X.pmul(Zs[a][P[0]], Zs[a][P[0]], p), p)
            extra.append(nrm if zsmode == 'A' else X.padd(X.pmul(V.new('u'), nrm, p), X.pconst(-1, p), p))
    else:
        name, l = zsfix
        Zs = [[X.pconst(vv[name][a] * l[c], p) for c in range(5)] for a in range(4)]
        piv = None
        for t, q in enumerate(P[:-1]):
            for a in range(3):
                if piv is None and Zs[a][q]: piv = 3 * t + a
        assert piv is not None
    a0, t0 = piv % 3, piv // 3; gidx = 4 * a0 + P[t0]          # D-coordinate of the pivot entry (a0, P[t0])
    B = [Zs]
    for r in range(R):
        co = [({} if d == gidx else V.new('y%d_%d' % (r, d))) for d in range(12)]
        M = X.dc_matrix(co, p)
        M = X.madd_const_col(M, [X.pconst(S[r][a], p) for a in range(4)], 0, p)
        B.append(M)
    extra = [e for e in extra if e]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def main():
    p = int(sys.argv[1]); mspec = sys.argv[2]; outdir = sys.argv[3]
    opts = dict(a.split('=', 1) for a in sys.argv[4:] if '=' in a); run = 'run' in sys.argv
    stage = opts.get('stage', 'a'); tmo = float(opts.get('timeout', 60))
    svec = opts['svec'].split(';') if 'svec' in opts else None
    zsfix = None
    if 'zsfix' in opts:
        nm, l = opts['zsfix'].split(':'); cs = X.Consts(p); zsfix = (nm, [cs.tok(t) for t in l.split(',')])
    cl = cells(p, mspec) if zsfix is None else [-1]
    if 'cells' in opts: cl = [int(c) for c in opts['cells'].split(',')]
    os.makedirs(outdir, exist_ok=True)
    tag = 'n2_%s_p%d_st%s%s' % (mspec.replace(',', '_'), p, stage, '_fix' if zsfix else '')
    man = open(os.path.join(outdir, tag + '.manifest'), 'a'); t0 = time.time(); stats = {}
    for c in cl:
        names, polys = build(p, mspec, c, stage, svec, zsfix); fn = os.path.join(outdir, '%s_c%d.ms' % (tag, c))
        if X.trivially_unit(polys): verdict = 'UNIT(constant-equation)'; extra = ''
        else:
            X.write_msolve(fn, names, p, polys); verdict = 'not-run'; extra = ''
            if run:
                v, nb, dt = X.run_msolve(fn, timeout=tmo); verdict = v; extra = ' basis=%s time=%.2fs' % (nb, dt)
        stats[verdict] = stats.get(verdict, 0) + 1
        man.write('%s cell=%d nvars=%d npolys=%d verdict=%s%s\n' % (os.path.basename(fn), c, len(names), len(polys), verdict, extra)); man.flush()
        print('cell', c, len(names), 'vars', len(polys), 'eqs', verdict, extra, flush=True)
    print('%s: %s  (%.0fs)' % (tag, stats, time.time() - t0))
if __name__ == '__main__': main()
