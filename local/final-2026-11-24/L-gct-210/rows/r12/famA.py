# three-column (2,1) kernels, family (A): x in V nonisotropic with diag(x) - kappa*I vanishing on W = x^perp cap V.
# Equivalently: for y in W, sum x_i y_i^2 = kappa sum y_i^2.  Unknowns x (Sigma x = 0), kappa; projective in x.
import sympy as sp
x1,x2,x3,k,a,b=sp.symbols('x1 x2 x3 k a b')
x4=-x1-x2-x3
X=[x1,x2,x3,x4]
# W = {y: sum y = 0, sum x_i y_i = 0}; generic parametrization: y = a*v1 + b*v2 with v1, v2 spanning W (cross-product style in C^4 via 3x3 minors)
import itertools
M=sp.Matrix([[1,1,1,1],X])
ns=M.nullspace()
v1,v2=[sp.simplify(n) for n in ns]
y=[a*v1[i]+b*v2[i] for i in range(4)]
Q=sp.expand(sp.together(sum(X[i]*y[i]**2 for i in range(4))-k*sum(y[i]**2 for i in range(4))))
num=sp.numer(sp.together(Q))
eqs=sp.Poly(sp.expand(num),a,b).coeffs()
G=sp.groebner(eqs+[x1-1],x2,x3,k,x1,order='lex')
print(G.exprs[-3:] if len(G.exprs)>3 else G)
sols=sp.solve(list(G.exprs),[x1,x2,x3,k],dict=True)
for s in sols: print({kk:sp.nsimplify(v) for kk,v in s.items()}, 'x4 =', sp.simplify(x4.subs(s)))
