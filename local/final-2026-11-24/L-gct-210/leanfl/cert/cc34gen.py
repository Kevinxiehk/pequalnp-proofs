# leanfl r15: CC34 chart systems (same construction as verify2/r18/cc34_p1.py), written as Singular input
# usage: python3 -I cc34gen.py OUTDIR [all|reps]
import sympy as sp, itertools, sys, os
out = sys.argv[1]; mode = sys.argv[2] if len(sys.argv) > 2 else 'reps'
idx = list(range(8))
def act(perm, swap, I):
    o = set()
    for x in I:
        col = x % 4; side = x // 4
        if swap: side = 1 - side
        o.add(side * 4 + perm[col])
    return frozenset(o)
seen = set(); reps = []
for I in itertools.combinations(idx, 4):
    I = frozenset(I)
    if I in seen: continue
    orb = {act(p, s, I) for p in itertools.permutations(range(4)) for s in (0, 1)}
    seen |= orb; reps.append(sorted(I))
charts = reps if mode == 'reps' else [list(I) for I in itertools.combinations(idx, 4)]
lam = sp.symbols('l0:4')
e3 = lambda v: sum(v[i]*v[j]*v[k] for i, j, k in itertools.combinations(range(4), 3))
vs = sp.symbols('t0:16')
for I in charts:
    T = iter(vs); M = []
    J = [c for c in idx if c not in I]
    for r in range(4):
        row = [0]*8; row[I[r]] = 1
        for c in J: row[c] = next(T)
        M.append(row)
    s = [sum(lam[r]*M[r][c] for r in range(4)) for c in range(8)]
    a, b = s[:4], s[4:]
    P2 = sp.expand(sum(x*y for x, y in zip(a, b)) - sum(a)*sum(b)); P3 = sp.expand(e3(a) + e3(b))
    eqs = sp.Poly(P2, *lam).coeffs() + sp.Poly(P3, *lam).coeffs()
    tag = ''.join(map(str, I))
    with open(os.path.join(out, 'cc34_%s.eqs' % tag), 'w') as f:
        f.write(',\n'.join(str(sp.expand(e)).replace('**', '^') for e in eqs) + '\n')
print(len(charts), 'charts')
