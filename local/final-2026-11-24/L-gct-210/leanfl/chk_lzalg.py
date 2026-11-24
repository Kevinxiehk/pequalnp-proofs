import sympy as sp
P,Q,R,X,Y,W=sp.symbols('P Q R X Y W')
f=lambda c,t: 2*t*c*(4*X+2*c*Y+c**2*W)+t**2*(4*P+2*c*Q+c**2*R)
pts=[(0,1),(1,1),(1,-1),(-1,1),(-1,-1),(2,1),(2,-1)]
names=['f01','f11','f1m','fm1','fmm','f21','f2m']
F=[sp.expand(f(*p)) for p in pts]
lam=sp.symbols('l0:7')
for target in [P,Q,R,X,Y,W]:
    expr=sp.expand(sum(lam[i]*F[i] for i in range(7))-target)
    eqs=[expr.coeff(v) for v in [P,Q,R,X,Y,W]]
    sol=sp.solve(eqs,lam,dict=True)[0]
    sol={k:sol.get(k,0) for k in lam}
    sol={k:sp.sympify(v).subs({l:0 for l in lam}) for k,v in sol.items()}
    print(target, ' + '.join('(%s)*%s'%(sol[lam[i]],names[i]) for i in range(7) if sol[lam[i]]!=0))
    assert sp.expand(sum(sol[lam[i]]*F[i] for i in range(7))-target)==0
