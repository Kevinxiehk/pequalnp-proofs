import sys, os; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact')
"""cut_rank2.py -- the generic rank-2 cell of [DC3] (gen_n1s case (3,2,(piv,),0,t3,t4)): split the equations by x-support.
   S1 = coefficients of R_i(x_0 Z_0 + x_1 Z_1)   (the plane span(Z_0,Z_1): one neutral column active, dim N_P = 1)
   S2 = coefficients of R_i(x_0 Z_0 + x_2 Z_2)
   Writes S1, S2 and FULL (= the cell, identical equations to gen_n1s.build) as msolve files; the caller computes GB(S1), GB(S2)
   and then FULL + GB(S1) + GB(S2) (the same ideal: GB(Si) lie in the ideal of the cell).
   usage: python3 -I cut_rank2.py P MSPEC PIV T3 T4 OUTPREFIX"""
import exactlib as X, gen_n1s
p = int(sys.argv[1]); mspec = sys.argv[2]; piv = int(sys.argv[3]); t3, t4 = sys.argv[4], sys.argv[5]; out = sys.argv[6]
case = (3, 2, (piv,), 0, t3, t4)
# --- same construction as gen_n1s.build (copied; checked below to give the same equation set) ---
cs = X.Consts(p); m, W = X.parse_m(mspec, cs); V = X.Vars()
rows = X.echelon_rows(6, (piv,), V, 'u'); B = [X.dcsub_matrix(r, [0, 1, 2], p) for r in rows]
vec = {}; extra = {}
for name, t in (('3', t3), ('4', t4)):
    if t == 'ab':
        a = V.new('a' + name); b = V.new('b' + name); last = X.padd(X.padd(X.pconst(-1, p), a, p, -1), b, p, -1)
        vec[name] = [X.pconst(1, p), a, b, last]; q = X.pconst(1, p)
        for c in (a, b, last): q = X.padd(q, X.pmul(c, c, p), p)
        extra[name] = q
    elif t == 'z1': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w, cs.w * cs.w % p)]
    elif t == 'z2': vec[name] = [X.pconst(c, p) for c in (0, 1, cs.w * cs.w % p, cs.w)]
for r, (l3, l4) in enumerate([({(): 1}, {}), ({}, {(): 1})]):
    co = [({} if d == piv else V.new('y%d_%d' % (r, d))) for d in range(6)]
    M = X.dcsub_matrix(co, [0, 1, 2], p)
    for lam, name, col in ((l3, '3', 3), (l4, '4', 4)):
        if lam:
            for a in range(4):
                e = X.pmul(lam, vec[name][a], p); M[a][col] = X.padd(M[a][col], e, p); M[a][2] = X.padd(M[a][2], e, p, -1)
    B.append(M)
eqs = X.equations(B, W, p, keyed=True)
full = [e for e in eqs.values() if e] + list(extra.values())
names0, polys0 = gen_n1s.build(p, mspec, case)
assert names0 == V.names and sorted(map(lambda q: sorted(q.items()), polys0)) == sorted(map(lambda q: sorted(q.items()), full)), 'mismatch with gen_n1s'
x1, x2 = X.XOFF + 1, X.XOFF + 2
S1 = [e for (i, xm), e in eqs.items() if e and x2 not in xm] + ([extra['3']] if '3' in extra else [])
S2 = [e for (i, xm), e in eqs.items() if e and x1 not in xm] + ([extra['4']] if '4' in extra else [])
def used(polys): return sorted({v for q in polys for mon in q for v in mon})
for tag, P_ in (('S1', S1), ('S2', S2)):
    ids = used(P_); sub = [V.names[i] for i in ids]
    # rename into a compact variable list (same names)
    X.write_msolve(out + '_' + tag + '.ms', V.names, p, P_)
    # msolve needs only used variables? keep the full list (unused variables are harmless for -g 2)
    print(tag, len(P_), 'eqs, vars used:', sub)
X.write_msolve(out + '_FULL.ms', V.names, p, full)
print('FULL', len(full), 'eqs', len(V.names), 'vars; identical to gen_n1s.build: yes')
