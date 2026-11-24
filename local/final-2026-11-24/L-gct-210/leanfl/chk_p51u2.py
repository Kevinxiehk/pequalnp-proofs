import sympy as sp, itertools
a=sp.symbols('a0:4')
E2=[sp.expand(sum(a[p]*a[q] for p,q in itertools.combinations([k for k in range(4) if k!=i],2))) for i in range(4)]
mons=[sp.Mul(*c) for c in itertools.combinations_with_replacement(a,2)]
cs=[[sp.Symbol('g%d_%d'%(i,j)) for j in range(len(mons))] for i in range(4)]
g=[sum(cs[i][j]*mons[j] for j in range(len(mons))) for i in range(4)]
expr=sp.expand(sum(g[i]*E2[i] for i in range(4))-(a[0]*a[1])**2)
eqs=sp.Poly(expr,*a).coeffs()
sol=sp.solve(eqs,[c for row in cs for c in row],dict=True)[0]
gs=[sp.expand(g[i].subs(sol).subs({c:0 for row in cs for c in row})) for i in range(4)]
print(gs)
print('check',sp.expand(sum(gs[i]*E2[i] for i in range(4))-(a[0]*a[1])**2))
