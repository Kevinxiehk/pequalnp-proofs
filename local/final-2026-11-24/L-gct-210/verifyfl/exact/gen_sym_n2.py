import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_sym_n2.py -- SYM-M for [T31] SPLIT A (vartheta(Z) = 0), |supp m| <= 3 on columns 0,1,2, m symbolic (charts A/B as gen_sym_n3)  (round 11).
   Uniform reduction (no distinctness of entries used, NOTES R11.3): Z = v l^T (v isotropic, l zero-sum on P); either all l_j != 0, then
   tau(v^3) = 0 and v = chi_1 after a row permutation (Newton; independent of m): ZMODE 'chi1' (l = (1, lt, -1-lt)); or l = e_a - e_b:
   ZMODE 'R2:ab:VT' (pair {a,b} = 01, 02, 12; v in chart VT = ab / z1 / z2).  Y_r (r = 1, 2) column-centred with s = b_r, gauge at the pivot
   entry of Zs.  Equations: all coefficients of R_i(x_0 Zs + x_1 Y_1 + x_2 Y_2) with W polynomial in t (gen_sym_n3.wpoly), + chart quadric."""
import exactlib as X, gen_sym, gen_sym_n3
def build(p, chart, zmode, keyed=False):
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t); one = X.pconst(1, p); extra = []
    if zmode == 'chi1':
        v = [X.pconst(c, p) for c in cs.chi1]; vrow = 0
        lt = V.new('lt'); l = [one, lt, X.padd(X.pconst(-1, p), lt, p, -1), {}, {}]; lcol = 0
    else:
        _, pair, vt = zmode.split(':'); a, b = int(pair[0]), int(pair[1])
        if vt == 'ab':
            aa, bb = V.new('va'), V.new('vb'); last = X.padd(X.padd(X.pconst(-1, p), aa, p, -1), bb, p, -1)
            v = [one, aa, bb, last]; q = X.pconst(1, p)
            for c in (aa, bb, last): q = X.padd(q, X.pmul(c, c, p), p)
            extra.append(q); vrow = 0
        else:
            v = [X.pconst(c, p) for c in ((0, 1, cs.w, cs.w * cs.w % p) if vt == 'z1' else (0, 1, cs.w * cs.w % p, cs.w))]; vrow = 1
        l = [{} for _ in range(5)]; l[a] = one; l[b] = X.pconst(p - 1, p); lcol = a
    Zs = [[X.pmul(v[r], l[c], p) for c in range(5)] for r in range(4)]
    gidx = 4 * vrow + lcol                                                        # D-coordinate of the pivot entry (vrow, lcol)
    bv = [[1, p - 1, 0, 0], [0, 1, p - 1, 0]]; B = [Zs]
    for r in range(2):
        co = [({} if d == gidx else V.new('y%d_%d' % (r, d))) for d in range(12)]
        M = X.dc_matrix(co, p); M = X.madd_const_col(M, [X.pconst(x, p) for x in bv[r]], 0, p); B.append(M)
    if keyed: return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra, B
    return V.names, gen_sym.equations_poly(B, Wp, p) + extra
