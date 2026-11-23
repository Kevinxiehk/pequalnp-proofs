import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""gen_n1s.py -- [DC-k], STRUCTURED version for defect lines m supported on the columns 0,1,2 (columns 3,4 neutral), also for 'SL', 'two'.
   Uses the proved fact (F2): on a doubly centred space N with defect in C m the columns 3 and 4 lie on isotropic lines C v_3, C v_4
   (or vanish).  Every isotropic line of V is spanned by v(th) = chi_1 + th chi_2 - (th^2/2) chi_3 for a unique th, or by chi_3.
   N is described by:  rho = rank of nu : N -> C^2, Z -> (lam_3, lam_4)  (column 3 = lam_3 v_3, column 4 = lam_4 v_4);
     N_P = ker nu = a (k - rho)-dim space of doubly centred matrices supported on the columns 0,1,2: reduced echelon cell of Gr(k - rho, 6)
           in the coordinates 3t + a = entry (a,t), t in {0,1}, a < 3  (column 2 and row 3 are determined);
     rho complement elements with nu-values the reduced echelon basis of the image:  rho = 2: (1,0), (0,1);
           rho = 1: line cell 0: (1, al) with al unknown, line cell 1: (0,1);
           their P-coordinates are unknowns except the pivot coordinates of N_P, which are 0 (unique representative modulo N_P).
   vtypes (charts of the isotropic lines, used by cases()): 'ab': v = (1, a, b, -1-a-b) with the equation 1 + a^2 + b^2 + (1+a+b)^2 = 0;
           'z1': v = (0,1,w,w^2);  'z2': v = (0,1,w^2,w)   [an isotropic v in V with v_0 = 0 is a multiple of one of these two];  '-': unused.
           (legacy charts, still accepted by build(): 'th': v = chi_1 + th chi_2 - (th^2/2) chi_3, 'c3': v = chi_3.)
   A case is the tuple (k, rho, pivots of N_P, line cell, vtype3, vtype4); cases(k) enumerates all of them.
   usage: python3 -I gen_n1s.py P MSPEC K OUTDIR [first last] [run] [timeout=T] [rho=R]"""
import exactlib as X, time, os, itertools
def vtheta(cs, th, p):
    """vector of 4 polynomials chi_1 + th chi_2 - th^2/2 chi_3"""
    h = X.inv(2, p); out = []
    for a in range(4):
        q = X.pconst(cs.chi1[a], p); q = X.padd(q, X.pmul(th, X.pconst(cs.chi2[a], p), p), p)
        q = X.padd(q, X.pmul(X.pmul(th, th, p), X.pconst((-h * cs.chi3[a]) % p, p), p), p); out.append(q)
    return out
VT = ('ab', 'z1', 'z2')      # charts of the isotropic lines: v_0 = 1 (two unknowns, one quadric) / v = (0,1,w,w^2) / v = (0,1,w^2,w)
def cases(k, vt=VT):
    out = []
    for rho in (2, 1, 0):
        if k - rho < 0 or k - rho > 6: continue
        for piv in X.cells(6, k - rho):
            if rho == 2:
                for v3 in vt:
                    for v4 in vt: out.append((k, rho, piv, 0, v3, v4))
            elif rho == 1:
                for v3 in vt:
                    for v4 in vt: out.append((k, rho, piv, 0, v3, v4))
                for v4 in vt: out.append((k, rho, piv, 1, '-', v4))
            else: out.append((k, rho, piv, 0, '-', '-'))
    return out
def build(p, mspec, case, split=None):
    k, rho, piv, lc, t3, t4 = case
    cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
    rows = X.echelon_rows(6, piv, V, 'u') if k - rho > 0 else []
    B = [X.dcsub_matrix(r, [0, 1, 2], p) for r in rows]
    vec = {}; extra = []
    for name, t in (('3', t3), ('4', t4)):
        if t == 'th': vec[name] = vtheta(cs, V.new('th' + name), p)
        elif t == 'c3': vec[name] = [X.pconst(c, p) for c in cs.chi3]
        elif t == 'ab':
            a = V.new('a' + name); b = V.new('b' + name); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
            vec[name] = [X.pconst(1, p), a, b, last]
            q = X.pconst(1, p)
            for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
            extra.append(q)
        elif t == 'z1': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)]
        elif t == 'z2': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w * cs.w % p, cs.w)]
        else: vec[name] = None
    if rho == 2: nus = [({(): 1}, {}), ({}, {(): 1})]
    elif rho == 1: nus = [({(): 1}, V.new('al'))] if lc == 0 else [({}, {(): 1})]
    else: nus = []
    # optional split of the case "N_P = C Z_0" by vartheta(Z_0) = <column 0 of Z_0, itself>/m_0:
    #   split 'A': vartheta(Z_0) = 0 (one more equation);  split 'B': vartheta(Z_0) != 0 (new variable u, u*<z,z> = 1) and the
    #   complement elements are normalised by Theta(Z_r, Z_0) = 0, i.e. <column j of Z_r, column j of Z_0> = 0 for j = 0,1,2
    #   (instead of "pivot coordinates = 0"); A and B together cover the case.
    if split:
        assert k - rho == 1
        nrm = {}
        for a in range(4): nrm = X.padd(nrm, X.pmul(B[0][a][0], B[0][a][0], p), p)
        if split == 'A': extra.append(nrm)
        else: extra.append(X.padd(X.pmul(V.new('u'), nrm, p), X.pconst(-1, p), p))
    for r, (l3, l4) in enumerate(nus):
        co = [({} if (d in piv and split != 'B') else V.new('y%d_%d' % (r, d))) for d in range(6)]
        M = X.dcsub_matrix(co, [0, 1, 2], p)
        for lam, name, col in ((l3, '3', 3), (l4, '4', 4)):
            if lam and vec[name] is not None:
                for a in range(4):
                    e = X.pmul(lam, vec[name][a], p); M[a][col] = X.padd(M[a][col], e, p); M[a][2] = X.padd(M[a][2], e, p, -1)
        if split == 'B':
            for j in range(3):
                q = {}
                for a in range(4): q = X.padd(q, X.pmul(M[a][j], B[0][a][j], p), p)
                extra.append(q)
        B.append(M)
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
def casename(c): return 'k%d_rho%d_piv%s_l%d_%s_%s' % (c[0], c[1], ''.join(map(str, c[2])) or 'none', c[3], c[4].replace('-', 'x'), c[5].replace('-', 'x'))
def main():
    p = int(sys.argv[1]); mspec = sys.argv[2]; k = int(sys.argv[3]); outdir = sys.argv[4]; cl = cases(k)
    opts = dict(a.split('=') for a in sys.argv if '=' in a); run = 'run' in sys.argv; tmo = float(opts.get('timeout', 30))
    if 'rho' in opts: cl = [c for c in cl if c[1] == int(opts['rho'])]
    nums = [a for a in sys.argv[5:] if a.isdigit()]
    first = int(nums[0]) if len(nums) == 2 else 0; last = int(nums[1]) if len(nums) == 2 else len(cl)
    os.makedirs(outdir, exist_ok=True); tag = 'n1s_%s_p%d' % (mspec.replace(',', '_'), p)
    man = open(os.path.join(outdir, tag + '_k%d.manifest' % k), 'a'); t0 = time.time(); stats = {}
    for idx in range(first, min(last, len(cl))):
        names, polys = build(p, mspec, cl[idx]); fn = os.path.join(outdir, '%s_%s.ms' % (tag, casename(cl[idx])))
        if not polys: verdict = 'NONUNIT(no-equations)'; extra = ''
        elif X.trivially_unit(polys): verdict = 'UNIT(constant-equation)'; extra = ''
        else:
            X.write_msolve(fn, names, p, polys); verdict = 'not-run'; extra = ''
            if run:
                v, nb, dt = X.run_msolve(fn, timeout=tmo); verdict = v; extra = ' basis=%s time=%.2fs' % (nb, dt)
                if v == 'UNIT':
                    os.remove(fn)
                    if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
        stats[verdict] = stats.get(verdict, 0) + 1
        man.write('%s case=%s nvars=%d npolys=%d verdict=%s%s\n' % (os.path.basename(fn), cl[idx], len(names), len(polys), verdict, extra)); man.flush()
    print('%s k=%d cases %d..%d of %d: %s  (%.0fs)' % (tag, k, first, min(last, len(cl)) - 1, len(cl), stats, time.time() - t0))
if __name__ == '__main__': main()
