# Exceptional locus for the D003-PROP Case-A family over the chart alpha = (1, a2, a3, -1-a2-a3): where does dim T_1 jump, and does the
# (cleared) complement basis degenerate? gcd of determinants of random integer compressions (rigorous superset of the bad locus).
import sys, itertools, random, sympy as sp
random.seed(2)
a2,a3=sp.symbols('a2 a3'); z=sp.symbols('z1:8')
al=[sp.Integer(1),a2,a3,-1-a2-a3]
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
# A^perp cap 1^perp spanning set: 4D cross products of (1, alpha, e_m)
def cross3(u,v,w):
    out=[]
    for j in range(4):
        cs=[c for c in range(4) if c!=j]; M=sp.Matrix([[u[c] for c in cs],[v[c] for c in cs],[w[c] for c in cs]])
        out.append((-1)**j*M.det())
    return out
W=[cross3([1]*4,al,[1 if c==m else 0 for c in range(4)]) for m in range(4)]
Bs=[mat({(1,0):1,(2,0):-1}), mat({(3,0):1,(4,0):-1}), mat({(3,j+1):al[j] for j in range(4)})]+[mat({(4,j+1):W[m][j] for j in range(4)}) for m in range(4)]
m=sum((z[k]*Bs[k] for k in range(len(Bs))),sp.zeros(5,5)); U=sp.ones(5,5)+m
def permsym(M):
    n=M.shape[0]; return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def minor(M,rows,cols): return M.extract([r for r in range(5) if r not in rows],[c for c in range(5) if c not in cols])
C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
t=sp.symbols('t0:25'); expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
eqs=sp.Poly(expr,*z).coeffs()
A=sp.Matrix([[sp.Poly(e,*t).coeff_monomial(t[k]) for k in range(25)] for e in eqs])
def rnd(r,c): return sp.Matrix(r,c,lambda i,j: random.randint(-3,3))
rkg=A.subs({a2:sp.Rational(3,7),a3:sp.Rational(-5,11)}).rank(); print('generic rank of T_1 system',rkg,'-> dim T_1 =',25-rkg,flush=True)
g1=0
for _ in range(3):
    d=sp.factor((rnd(rkg,A.rows)*A*rnd(25,rkg)).det()); g1=sp.gcd(g1,d) if g1!=0 else d
print('rank test polynomial (T_1 jumps only on its zero set):',sp.factor(g1),flush=True)
Xm=sp.Matrix([[Bs[k][i,j] for i in range(5) for j in range(5)] for k in range(len(Bs))])
print('rank of X spanning set generic:',Xm.subs({a2:sp.Rational(3,7),a3:sp.Rational(-5,11)}).rank(),flush=True)
