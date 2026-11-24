# exact: rank of (A0 - 2I) on the 10-dim space of cubic forms (A0 = sum_j pullback by B_j^0).  Since each pullback preserves
# Sym^3 = H_3 (+) |x|^2 V^*, and A0 = 2 on the 3-dim |x|^2 V^* part (sum B_j = 2I), rank 7 <=> 2 is NOT an eigenvalue of A0 on H_3.
import sympy as sp
from sympy.polys.matrices import DomainMatrix
x1,x2,x3=sp.symbols('x1 x2 x3'); X=sp.Matrix([x1,x2,x3])
mons=[x1**a*x2**b*x3**(3-a-b) for a in range(4) for b in range(4-a)]
def cx(h): a,b,c=h; return sp.Matrix([[0,-c,b],[c,0,-a],[-b,a,0]])
H=[sp.Matrix(r) for r in ([1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1])]; I3=sp.eye(3)
r5=sp.sqrt(5); r3=sp.sqrt(3); r2=sp.sqrt(2); i=sp.I
def rot(s,v): return (s**2-(v.T*v)[0])*I3+2*v*v.T+2*s*cx(v)
s=[3/(2*r2),3/(2*r2),-r3/(2*r2),-r3/(2*r2)]; e=[1,1,-1,-1]
v=[sp.Matrix([-i/2,0,1/(2*r2)]),sp.Matrix([i/2,0,1/(2*r2)]),sp.Matrix([0,sp.Rational(1,2),-r3/(2*r2)]),sp.Matrix([0,-sp.Rational(1,2),-r3/(2*r2)])]
confs={'++++':([I3/4+h*h.T/4+r5*cx(h)/4 for h in H],[r5]),
       '----':([5*I3/4-3*h*h.T/4-i*r3*cx(h)/4 for h in H],[i*r3]),
       '++--':([e[j]*rot(s[j],v[j]) for j in range(4)],[r2,r3,i]),
       '++--inv':([e[j]*rot(s[j],-v[j]) for j in range(4)],[r2,r3,i])}
for name,(Bs,gens) in confs.items():
    assert sp.simplify(sum(Bs,sp.zeros(3,3))-2*I3)==sp.zeros(3,3), name
    A=sp.zeros(10,10)
    for k,m in enumerate(mons):
        img=0
        for B in Bs:
            Y=B*X; img+=m.subs({x1:Y[0],x2:Y[1],x3:Y[2]},simultaneous=True)
        P=sp.Poly(sp.expand(img),x1,x2,x3)
        for l,mm in enumerate(mons):
            A[l,k]=P.coeff_monomial(mm)
    K=sp.QQ.algebraic_field(*gens)
    M=DomainMatrix.from_Matrix(A-2*sp.eye(10)).convert_to(K)
    print(name,': rank(A0 - 2I) on cubics =',M.rank(),' (7 <=> 2 not an eigenvalue on H_3)',flush=True)
