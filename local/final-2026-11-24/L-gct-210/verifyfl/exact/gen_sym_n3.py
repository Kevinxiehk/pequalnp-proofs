import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_sym_n3.py -- SYM-M for [T22] (round 11): gen_n3's cover with the defect line m SYMBOLIC on the projective line of lines supported on
   columns 0, 1, 2 (charts A: m = (1, t, -1-t, 0, 0), B: m = (t, 1, -1-t, 0, 0); W polynomial in t, rank 4 for every t; see gen_sym.py).
   The [T22] cover is valid for EVERY m on the line: the N-cases use (F2) only on the neutral columns 3, 4, and the Gram equation (F4) only a
   neutral column.  By properness of Gr x P^1 (NOTES R10.8), UNIT in F_p[t, x] in both charts => no K of that case for any m (char 0).
   Variable 'mt' first; the N-variables then coincide with gen_sym.build(case) (k = 2)."""
import exactlib as X, gen_n3, gen_sym
def wpoly(p, chart, t):
    one = X.pconst(1, p); e = lambda j: [one if a == j else {} for a in range(5)]
    if chart == 'A': return [e(3), e(4), [X.pmul(X.pconst(p - 1, p), t, p), one, {}, {}, {}], [X.padd(one, t, p), {}, one, {}, {}]]
    return [e(3), e(4), [one, X.pmul(X.pconst(p - 1, p), t, p), {}, {}, {}], [{}, X.padd(one, t, p), one, {}, {}]]
def build(p, chart, case, scell, keyed=False):
    cs = X.Consts(p); V = X.Vars(); t = V.new('mt'); Wp = wpoly(p, chart, t)
    B, extra, ells = gen_n3.nbasis(p, cs, case, V); rho = case[1]
    S = gen_n3.svectors(p, scell, V)
    for r in range(2):
        co = [V.new('w%d_%d' % (r, d)) for d in range(12)]
        M = X.dc_matrix(co, p); D = [[dict(x) for x in row] for row in M]
        M = X.madd_const_col(M, S[r], 0, p)
        for ell in ells: extra.append(gen_n3.entry_form(D, ell, p))
        B.append(M)
    if rho >= 1:
        ip = lambda u, v: gen_n3.ip(u, v, p)
        g = X.padd(X.pmul(ip(S[0], S[0]), ip(S[1], S[1]), p), X.pmul(ip(S[0], S[1]), ip(S[0], S[1]), p), p, -1)
        if g: extra.append(g)
    extra = [e for e in extra if e]
    if keyed: return V.names, gen_sym.equations_poly(B, Wp, p, keyed=True), extra
    return V.names, gen_sym.equations_poly(B, Wp, p) + extra
