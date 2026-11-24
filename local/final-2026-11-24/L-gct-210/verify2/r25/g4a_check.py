# verify2 r25: rows R21.9/R21.9'' checks: (1) the deletion-j ka-coefficients with column 5 constant (w = g5), exact on random rational data
# satisfying sum be c = 0, sum al c = 3u - w; (2) Gr-identity coordinates = M-form; (3) B^u for a vertex u has a triple root; (4) case (b) 8 D_5 = k0.
import sympy as sp, random
from itertools import permutations
random.seed(11); R=lambda: sp.Rational(random.randint(-9,9),random.randint(1,4))
def K(x,y,z): return sum(x[p[0]]*y[p[1]]*z[p[2]] for p in permutations(range(3)))
ka=sp.Symbol('ka'); ok=True
for trial in range(4):
    c=[sp.Matrix([R(),R(),R()]) for _ in range(3)]; be=[R() or 1 for _ in range(4)]; al=[R() for _ in range(4)]
    c.append(-(be[0]*c[0]+be[1]*c[1]+be[2]*c[2])/be[3]); w=sp.Matrix([R(),R(),R()])
    u=(sum((al[k]*c[k] for k in range(4)),sp.zeros(3,1))+w)/3
    v=2*u-w
    y=[(u-(al[k]+ka*be[k])*c[k])/2 for k in range(4)]+[(u-w)/2]
    Bv=[[K(c[a],c[b],v) for b in range(4)] for a in range(4)]
    l=lambda x: 3*K(x,u,u)-3*K(x,u,w)+K(x,w,w)
    for j in range(4):
        Rr=[a for a in range(4) if a!=j]; a1,b1,c1=Rr
        P3=sp.expand(8*(K(y[a1],y[b1],y[c1])+K(y[a1],y[b1],y[4])+K(y[a1],y[c1],y[4])+K(y[b1],y[c1],y[4])))
        P=sp.Poly(P3,ka); C=K(c[a1],c[b1],c[c1])
        cyc2=al[a1]*be[b1]*be[c1]+al[b1]*be[a1]*be[c1]+al[c1]*be[a1]*be[b1]; cyc1=al[a1]*al[b1]*be[c1]+al[a1]*al[c1]*be[b1]+al[b1]*al[c1]*be[a1]
        f3=-be[a1]*be[b1]*be[c1]*C
        f2=-sum(be[a]**2*Bv[a][a] for a in range(4))/2+be[j]**2*Bv[j][j]-cyc2*C
        f1=-be[j]*l(c[j])-sum(al[a]*be[a]*Bv[a][a] for a in range(4))+2*al[j]*be[j]*Bv[j][j]-cyc1*C
        ok&=(P.coeff_monomial(ka**3)==f3 and P.coeff_monomial(ka**2)==f2 and P.coeff_monomial(ka)==f1)
print('(1) R21.9 deletion-j ka^3, ka^2, ka^1 coefficients exact on 4 random instances:',ok)
u1,u2,u3,w1,w2,w3,x1,x2,x3=sp.symbols('u1 u2 u3 w1 w2 w3 x1 x2 x3'); U=[u1,u2,u3]; W=[w1,w2,w3]; X=[x1,x2,x3]
lx=sp.expand(3*K(X,U,U)-3*K(X,U,W)+K(X,W,W)); M=sp.Matrix([[6,-3],[-3,2]])
okM=all(sp.expand(lx.coeff(X[i]) - (sp.Matrix([U[j],W[j]]).T*M*sp.Matrix([U[k],W[k]]))[0])==0 for i,j,k in [(0,1,2),(1,0,2),(2,0,1)])
print('(2) coefficient of x_i in l(x) = (u_j,w_j) M (u_k,w_k)^T, M = [[6,-3],[-3,2]]:',okM)
z=sp.Symbol('z'); I=sp.I; cz=[z**2-1,I*(z**2+1),2*z]
for uv in ([0,I,1],[0,1,I],[1,I,0],[I,0,1]):
    print('(3) vertex u =',uv,': B^u(z) =',sp.factor(sp.expand(K(cz,cz,uv))))
mu=sp.Symbol('mu'); print('(4) 4 - 3(3-mu) + (3-mu)^2 mod mu^2-3mu+3 =',sp.rem(sp.expand(4-3*(3-mu)+(3-mu)**2),mu**2-3*mu+3,mu))
