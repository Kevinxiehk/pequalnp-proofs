import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_n3g.py -- [T22] for ANY defect line m (|supp m| = 2..5)   (round 8, verifyfl; generalises gen_n3.py).
   N = 2-dim doubly centred with defect in C m: any case of gen_dc.cases(2, P, Nt) (complete by (F2)_p); S = s(K) in one of the three
   cells of Gr(2,V); Y_r = s_r e_0^T + D(c_r); gauge Y_r -> Y_r + N fixed by gen_dc's gauge forms (identity matrix on the generators);
   Gram determinant of S = 0 when a neutral column is active on N (rho >= 1; (F4)_p).  For Nt = {3,4} the equation sets coincide with
   gen_n3.py (test_n3g.py).   usage: python3 -I gen_n3g.py P MSPEC CASEIDX SCELL OUT.ms"""
import exactlib as X, gen_dc, gen_n3
def build(p, mspec, case, scell, keyed=False):
    cs, m, W, P, Nt = gen_dc.setup(p, mspec); V = X.Vars()
    B, extra, ells = gen_dc.basis(p, cs, P, Nt, case, V); extra = list(extra)
    S = gen_n3.svectors(p, scell, V)
    for r in range(2):
        co = [V.new('w%d_%d' % (r, d)) for d in range(12)]
        M = X.dc_matrix(co, p); D = [[dict(x) for x in row] for row in M]
        M = X.madd_const_col(M, S[r], 0, p)
        for ell in ells: extra.append(gen_n3.entry_form(D, ell, p))
        B.append(M)
    if case[1] >= 1:
        ip = lambda u, v: gen_n3.ip(u, v, p)
        g = X.padd(X.pmul(ip(S[0], S[0]), ip(S[1], S[1]), p), X.pmul(ip(S[0], S[1]), ip(S[0], S[1]), p), p, -1)
        if g: extra.append(g)
    extra = [e for e in extra if e]
    if keyed: return V.names, X.equations(B, W, p, keyed=True), extra
    polys, nx = X.equations(B, W, p)
    return V.names, polys + extra
if __name__ == '__main__':
    p = int(sys.argv[1]); mspec = sys.argv[2]; ci = int(sys.argv[3]); sc = int(sys.argv[4])
    cs, m, W, P, Nt = gen_dc.setup(p, mspec); case = gen_dc.cases(2, P, Nt)[ci]
    names, polys = build(p, mspec, case, sc); X.write_msolve(sys.argv[5], names, p, polys); print(case, len(names), 'vars', len(polys), 'eqs')
