# e5_an.py s12 s13 eps : for a survivor, the surviving family (from the DFS over all d = 4 triples) and, for each column
# triple S, the cube-condition polynomial on the lambda = 1 slice of Pi_S.
import sys, ast, glob, itertools
import sympy as sp
sys.path.insert(0, '/home/kevxhk/work/L-gct-210/leanzbf')
from gen_e3 import gq, red, j
I = sp.I
s12 = tuple(int(c) for c in sys.argv[1]); s13 = tuple(int(c) for c in sys.argv[2]); eps = int(sys.argv[3])
rows = [ast.literal_eval(l) for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_export_p*.txt')) for l in open(f)
        if l.strip() and ast.literal_eval(l)['s12'] == s12 and ast.literal_eval(l)['s13'] == s13 and ast.literal_eval(l)['eps'] == eps]
fam = []
txt = open('/home/kevxhk/work/L-gct-210/leanzbf/surv_families.txt').read()
blk = txt.split('== %s %s %d' % (sys.argv[1], sys.argv[2], eps))[1].split('==')[0]
for line in blk.splitlines():
    line = line.strip()
    if line.startswith('['):
        fam.append([sp.sympify(x.replace('I', 'I')) for x in ast.literal_eval(line.replace('I', '"I"').replace('"I"', '1j')) ] if False else sp.sympify(line))
P = sp.symbols('p0:%d' % len(fam))
M = [sp.expand(sum(P[i] * fam[i][c] for i in range(len(fam)))) for c in range(10)]
B12 = [m for m in range(5) if s12[m] == 2]; Q12 = [m for m in range(5) if s12[m] == 1]
B13 = [m for m in range(5) if s13[m] == 2]; Q13 = [m for m in range(5) if s13[m] == 1]
K12 = 1 / (1 + I); K13 = 1 / (1 + eps * I)
Y = sp.symbols('y0:4')
for r in rows:
    if r['d'] != 4:
        continue
    S = r['S']
    E = [[gq(v).subs(j, I) for v in e] for e in r['E']]
    u = [[gq(v).subs(j, I) for v in row] for row in r['u']]
    V = sp.symbols('v0:9')
    eqs = [sum(V[3 * i + k] for k in range(3)) - 1 for i in range(3)]
    eqs.append(sum(V[k] for k in range(3) if S[k] in B12) + sum(V[3 + k] for k in range(3) if S[k] in Q12) - K12)
    eqs.append(sum(V[k] for k in range(3) if S[k] in B13) + sum(V[6 + k] for k in range(3) if S[k] in Q13) - K13)
    sol = sp.solve(eqs, V, dict=True)
    if not sol:
        continue
    V0 = [sp.expand(sol[0].get(V[i], V[i]).subs({x: 0 for x in V})) for i in range(9)]
    nstar = lambda v: sum(M[S[k]] * v[3 + k] + M[5 + S[k]] * v[6 + k] for k in range(3))
    n0 = sp.expand(nstar(V0)); z = [sp.expand(nstar(E[e])) for e in range(4)]
    pt = [sp.expand(V0[i] + sum(Y[e] * E[e][i] for e in range(4))) for i in range(9)]
    T = [[pt[3 * i + k] * u[i][k] for k in range(3)] for i in range(3)]
    perm = sp.expand(T[0][0] * T[1][1] * T[2][2] + T[0][0] * T[1][2] * T[2][1] + T[0][1] * T[1][0] * T[2][2] +
                     T[0][1] * T[1][2] * T[2][0] + T[0][2] * T[1][0] * T[2][1] + T[0][2] * T[1][1] * T[2][0])
    print('S', S, 'n0 =', n0, ' z =', z)
    # eliminate one y using the hyperplane if some z_e is a nonzero constant
    piv = next((e for e in range(4) if z[e] != 0 and z[e].is_number), None)
    if piv is None:
        piv = next((e for e in range(4) if z[e] != 0), None)
    if piv is None:
        print('   z = 0'); continue
    sub = {Y[piv]: sp.expand(-(n0 + sum(z[e] * Y[e] for e in range(4) if e != piv)) / z[piv])}
    Pp = sp.expand(perm.subs(sub))
    poly = sp.Poly(Pp, *[Y[e] for e in range(4) if e != piv])
    nonconst = [(m, sp.factor(sp.together(c))) for m, c in poly.terms() if sum(m) > 0]
    free = [e for e in range(4) if e != piv]
    good = []
    for a in range(3):
        lin = tuple(1 if b == a else 0 for b in range(3))
        sq = tuple(2 if b == a else 0 for b in range(3))
        cub = tuple(3 if b == a else 0 for b in range(3))
        d = {m: c for m, c in nonconst}
        if lin in d and d[lin].is_number and d[lin] != 0 and sq not in d and cub not in d:
            good.append((free[a], d[lin]))
    print('   pivot y%d (z = %s), constant-coefficient free directions: %s' % (piv, z[piv], good))
