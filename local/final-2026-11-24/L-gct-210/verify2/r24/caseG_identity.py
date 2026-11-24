# verify2 r24: exact check of rows R21.8 ka-coefficient identities with random rational data satisfying the two linear relations
# (isotropy is not needed for the identities; it is used only in the final binary-quadratic step, checked separately below).
import sympy as sp, random
from itertools import permutations
random.seed(7); R=lambda: sp.Rational(random.randint(-9,9),random.randint(1,5))
def K(x,y,z): return sum(x[p[0]]*y[p[1]]*z[p[2]] for p in permutations(range(3)))
ka=sp.Symbol('ka')
for trial in range(5):
    c=[sp.Matrix([R(),R(),R()]) for _ in range(3)]; be=[R() or 1 for _ in range(4)]; al=[R() for _ in range(4)]
    c.append(-(be[0]*c[0]+be[1]*c[1]+be[2]*c[2])/be[3])
    u=sum((al[k]*c[k] for k in range(4)),sp.zeros(3,1))/2
    y=[(u-(al[k]+ka*be[k])*c[k])/2 for k in range(4)]
    A=[K(c[k],u,u) for k in range(4)]; B=[[K(c[a],c[b],u) for b in range(4)] for a in range(4)]
    ok=True
    for k in range(4):
        T=[a for a in range(4) if a!=k]; a1,b1,c1=T
        C=K(c[a1],c[b1],c[c1])
        poly=sp.Poly(sp.expand(8*K(y[a1],y[b1],y[c1])),ka)
        S2=sum(be[a]**2*B[a][a] for a in range(4)); S1=sum(al[a]*be[a]*B[a][a] for a in range(4))
        cyc2=al[a1]*be[b1]*be[c1]+al[b1]*be[a1]*be[c1]+al[c1]*be[a1]*be[b1]
        cyc1=al[a1]*al[b1]*be[c1]+al[a1]*al[c1]*be[b1]+al[b1]*al[c1]*be[a1]
        f3=-be[a1]*be[b1]*be[c1]*C
        f2=-S2/2+be[k]**2*B[k][k]-cyc2*C
        f1=-be[k]*A[k]+2*al[k]*be[k]*B[k][k]-S1-cyc1*C
        ok&=(poly.coeff_monomial(ka**3)==f3 and poly.coeff_monomial(ka**2)==f2 and poly.coeff_monomial(ka)==f1)
    print('trial',trial,'identities exact:',ok)
# final step: z -> K(c(z),u,u) for isotropic u != 0 is a nonzero binary quadratic. c(z) = (z^2-1, i(z^2+1), 2z) (Walsh, isotropic)
z,s=sp.symbols('z s'); I=sp.I
cz=sp.Matrix([z**2-1,I*(z**2+1),2*z]); u=sp.Matrix([s**2-1,I*(s**2+1),2*s])   # u isotropic, generic point of the conic
q=sp.factor(sp.expand(K(cz,u,u))); print('K(c(z),u(s),u(s)) =',q)
u8=sp.Matrix([1,I,0]); print('u = c(inf) direction (1,i,0): K(c(z),u,u) =',sp.factor(sp.expand(K(cz,u8,u8))))
