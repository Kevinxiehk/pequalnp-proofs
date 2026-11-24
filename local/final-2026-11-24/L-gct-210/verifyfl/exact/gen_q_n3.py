import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""gen_q_n3.py -- the SYM-M [T22] system of gen_sym_n3 with INTEGER coefficients, for computations over Q (round 11, NOTES R11.5).
   The only irrational constant of the structured covers is w (charts z1 = (0,1,w,w^2), z2 = (0,1,w^2,w)); here both are replaced by ONE
   chart 'zw' v = (0, 1, ww, -1-ww) with the extra equation ww^2 + ww + 1 = 0 (its two roots are z1 and z2).  The arithmetic is done mod a
   62-bit prime and the coefficients (small integers) are lifted to Z (symmetric residues; sanity-checked to be small).
   Output: a Singular script over Q with the Rabinowitsch equation u*mt*(mt+1) - 1 (solutions off the two-column points t = 0, -1), std, unit?
   usage: python3 -I gen_q_n3.py CHART CI SCELL OUT.sing   (case = gen_n1s.cases(2)[CI] with z1/z2 replaced by zw)"""
import exactlib as X, gen_n3, gen_sym, gen_sym_n3, gen_n1s
PBIG = 4611686018427387847        # prime, 62 bits
def nbasis_zw(p, cs, case, V):
    """gen_n3.nbasis with the charts z1/z2 replaced by 'zw' (ww a variable; returns the extra equation ww^2+ww+1)."""
    k, rho, piv, lc, t3, t4 = case
    rows = X.echelon_rows(6, piv, V, 'u') if k - rho > 0 else []
    B = [X.dcsub_matrix(r, [0, 1, 2], p) for r in rows]
    ells = [[(d % 3, d // 3)] for d in piv]; vec = {}; extra = []; vrow = {}; one = X.pconst(1, p)
    for name, t in (('3', t3), ('4', t4)):
        if t == 'ab':
            a = V.new('a' + name); b = V.new('b' + name); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
            vec[name] = [one, a, b, last]; vrow[name] = 0; q = X.pconst(1, p)
            for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
            extra.append(q)
        elif t in ('z1', 'z2', 'zw'):
            ww = V.new('ww' + name); vec[name] = [{}, one, ww, X.padd(X.pconst(-1, p), ww, p, -1)]; vrow[name] = 1
            extra.append(X.padd(X.padd(X.pmul(ww, ww, p), ww, p), one, p))
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
    return B, extra, ells + nell
def build(chart, case, scell):
    p = PBIG; cs = None; V = X.Vars(); t = V.new('mt'); Wp = gen_sym_n3.wpoly(p, chart, t)
    B, extra, ells = nbasis_zw(p, cs, case, V); rho = case[1]
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
    polys = gen_sym.equations_poly(B, Wp, p) + [e for e in extra if e]
    return V.names, polys
def lift(q, p):
    out = {}
    for mon, c in q.items():
        c = c if c <= p // 2 else c - p; assert abs(c) < 10 ** 12, 'coefficient not small'; out[mon] = c
    return out
def fmt(q, names):
    terms = []
    for mon, c in sorted(q.items()):
        f = '*'.join(names[v] if mon.count(v) == 1 else '%s^%d' % (names[v], mon.count(v)) for v in sorted(set(mon)))
        terms.append('(%d)%s' % (c, ('*' + f) if f else ''))
    return '+'.join(terms) if terms else '0'
if __name__ == '__main__':
    chart, ci, sc, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    case = list(gen_n1s.cases(2)[ci]); case = tuple(c if c not in ('z1', 'z2') else 'zw' for c in case)
    names, polys = build(chart, case, sc); polys = [lift(q, PBIG) for q in polys]
    with open(out, 'w') as f:
        f.write('option(redSB); ring r = 0, (%s, urab), dp;\nideal I = %s,\n urab*mt*(mt+1) - 1;\nideal J = std(I);\nif (size(J) == 1 and deg(J[1]) == 0) { print("UNIT over Q"); } else { print("NOT unit over Q: size " + string(size(J)) + " dim " + string(dim(J))); }\nquit;\n' % (','.join(names), ',\n '.join(fmt(q, names) for q in polys)))
    print(case, len(names), 'vars', len(polys), 'polys ->', out)
