# e5_search.py s12 s13 eps : for a survivor, search column triples S, free hat positions F (3 of the 9 [123;S] cells) and two
# points x0, x1 in {0,1}^3 (lambda = 1) with perm(y(x1)) - perm(y(x0)) a NONZERO CONSTANT (independent of the family
# parameters p), where y = the hat block and the dependent cells are solved from the 6 relations (rows, K12, K13, n**).
# Also reports pivot = det of the dependent system (linear in p) and whether pivot = 0 is (E3)-inadmissible.
import sys, itertools
import sympy as sp
I = sp.I
s12 = tuple(int(c) for c in sys.argv[1]); s13 = tuple(int(c) for c in sys.argv[2]); eps = int(sys.argv[3])
txt = open('/home/kevxhk/work/L-gct-210/leanzbf/surv_families.txt').read()
blk = txt.split('== %s %s %d' % (sys.argv[1], sys.argv[2], eps))[1].split('==')[0]
fam = [sp.sympify(l.strip()) for l in blk.splitlines() if l.strip().startswith('[')]
P = sp.symbols('p0:%d' % len(fam))
Mv = [sp.expand(sum(P[i] * fam[i][c] for i in range(len(fam)))) for c in range(10)]
M2 = Mv[:5]; M3 = Mv[5:]
B12 = [m for m in range(5) if s12[m] == 2]; Q12 = [m for m in range(5) if s12[m] == 1]
B13 = [m for m in range(5) if s13[m] == 2]; Q13 = [m for m in range(5) if s13[m] == 1]
K12 = sp.nsimplify(1 / (1 + I)); K13 = sp.nsimplify(1 / (1 + eps * I))
def w2(m): return {1: 1, 2: -1, 0: I}[s12[m]]
def w3(m): return {1: 1, 2: -1, 0: eps * I}[s13[m]]
q12 = [1 if m in Q12 else 0 for m in range(5)]; q13 = [1 if m in Q13 else 0 for m in range(5)]
def inspan(vecs, base):
    Bm = sp.Matrix(base).T; r0 = Bm.rank()
    return all(sp.Matrix.hstack(Bm, sp.Matrix(v)).rank() == r0 for v in vecs)
def e3_dead(lin):
    # restricted family lin = 0 (lin linear in p): all members have M3 in span(1,1_Q13) or all have M2 in span(1,1_Q12)?
    co = [sp.expand(lin).coeff(p) for p in P]
    ns = sp.Matrix([co]).nullspace()
    vecs = [sp.Matrix([sum(n[i] * fam[i][c] for i in range(len(fam))) for c in range(10)]) for n in ns]
    if inspan([list(v[5:]) for v in vecs], [[1] * 5, q13]): return 'E3a(M3)'
    if inspan([list(v[:5]) for v in vecs], [[1] * 5, q12]): return 'E3b(M2)'
    return None
out = []
for S in itertools.combinations(range(5), 3):
    V = [[sp.Symbol('v%d%d' % (i, k)) for k in range(3)] for i in range(3)]
    flat = [V[i][k] for i in range(3) for k in range(3)]
    rel = [sum(V[i]) - 1 for i in range(3)]
    rel.append(sum(V[0][k] for k in range(3) if S[k] in B12) + sum(V[1][k] for k in range(3) if S[k] in Q12) - K12)
    rel.append(sum(V[0][k] for k in range(3) if S[k] in B13) + sum(V[2][k] for k in range(3) if S[k] in Q13) - K13)
    rel.append(sum(M2[S[k]] * V[1][k] + M3[S[k]] * V[2][k] for k in range(3)))
    A0 = sp.Matrix([[sp.expand(r).coeff(x) for x in flat] for r in rel[:5]])
    if A0.rank() != 5: continue
    found = None
    for F in itertools.combinations(range(9), 3):
        D = [c for c in range(9) if c not in F]
        AD = sp.Matrix([[sp.expand(r).coeff(flat[c]) for c in D] for r in rel])
        det = sp.factor(AD.det())
        if det == 0: continue
        X = sp.symbols('x0:3')
        sub = {flat[F[l]]: X[l] for l in range(3)}
        eqs = [sp.expand(r.subs(sub)) for r in rel]
        sol = sp.solve(eqs, [flat[c] for c in D], dict=True)
        if not sol: continue
        sol = sol[0]
        val = {flat[F[l]]: X[l] for l in range(3)}
        for c in D: val[flat[c]] = sol[flat[c]]
        T = [[val[V[i][k]] / (1 if i == 0 else (w2(S[k]) if i == 1 else w3(S[k]))) for k in range(3)] for i in range(3)]
        perm = sum(T[0][s[0]] * T[1][s[1]] * T[2][s[2]] for s in itertools.permutations(range(3)))
        pts = list(itertools.product([0, 1], repeat=3))
        Pv = {pt: sp.simplify(sp.together(perm.subs(dict(zip(X, pt))))) for pt in pts}
        for a, b in itertools.combinations(pts, 2):
            d = sp.simplify(Pv[b] - Pv[a])
            if d != 0 and d.is_number:
                # pivot: the p-dependent factor of det
                pf = [f for f, _ in sp.factor_list(det)[1] if f.free_symbols]
                piv = sp.Mul(*pf) if pf else 1
                e3 = None if not pf else e3_dead(piv)
                found = (S, F, a, b, d, det, e3); break
        if found: break
    if found:
        out.append(found); print('S', found[0], 'F', found[1], 'x0', found[2], 'x1', found[3], 'diff', found[4], 'det', found[5], 'pivot=0:', found[6]); sys.stdout.flush()
        if len(out) >= 2: break
if not out: print('NO constant difference found')
