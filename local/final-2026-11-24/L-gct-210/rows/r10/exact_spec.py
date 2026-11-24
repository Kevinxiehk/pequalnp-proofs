# exact: characteristic polynomial of A0 = sum_j rho_3(B_j^0) on harmonic cubics, evaluated at 2 (PL4 base configurations)
import sympy as sp, itertools
x1,x2,x3,lam=sp.symbols('x1 x2 x3 lam'); X=sp.Matrix([x1,x2,x3])
mons=[x1**a*x2**b*x3**c for a in range(4) for b in range(4) for c in range(4) if a+b+c==3]
# harmonic basis: kernel of the Laplacian on cubics
def lapl(p): return sp.expand(sum(sp.diff(p,v,2) for v in (x1,x2,x3)))
coeffs=sp.symbols('k0:10'); gen=sum(k*m for k,m in zip(coeffs,mons))
sol=sp.solve(sp.Poly(lapl(gen),x1,x2,x3).coeffs(),coeffs,dict=True)[0]
free=[k for k in coeffs if k not in sol]; Hbasis=[sp.expand(gen.subs(sol).subs({f:(1 if f==g else 0) for f in free})) for g in free]
def coords(p):   # coordinates of a harmonic cubic in Hbasis
    cs=sp.symbols('q0:%d'%len(Hbasis)); eqs=sp.Poly(sp.expand(p-sum(c*h for c,h in zip(cs,Hbasis))),x1,x2,x3).coeffs()
    s=sp.solve(eqs,cs,dict=True)[0]; return [sp.simplify(s[c]) for c in cs]
def cx(h): a,b,c=h; return sp.Matrix([[0,-c,b],[c,0,-a],[-b,a,0]])
H=[sp.Matrix(r) for r in ([1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1])]
I3=sp.eye(3)
confs={}
r5=sp.sqrt(5); r3=sp.sqrt(3); r2=sp.sqrt(2); i=sp.I
confs['++++']=[I3/4+h*h.T/4+r5*cx(h)/4 for h in H]
confs['----']=[5*I3/4-3*h*h.T/4-i*r3*cx(h)/4 for h in H]
def rot(s,v): return (s**2-(v.T*v)[0])*I3+2*v*v.T+2*s*cx(v)
s=[3/(2*r2),3/(2*r2),-r3/(2*r2),-r3/(2*r2)]; e=[1,1,-1,-1]
v=[sp.Matrix([-i/2,0,1/(2*r2)]),sp.Matrix([i/2,0,1/(2*r2)]),sp.Matrix([0,sp.Rational(1,2),-r3/(2*r2)]),sp.Matrix([0,-sp.Rational(1,2),-r3/(2*r2)])]
confs['++--']=[e[j]*rot(s[j],v[j]) for j in range(4)]
confs['++--inv']=[e[j]*rot(s[j],-v[j]) for j in range(4)]
for name,Bs in confs.items():
    assert sp.simplify(sum(Bs,sp.zeros(3,3))-2*I3)==sp.zeros(3,3)
    cols=[]
    for hb in Hbasis:
        img=sum(sp.expand(hb.subs({x1:(B*X)[0],x2:(B*X)[1],x3:(B*X)[2]},simultaneous=True)) for B in Bs)
        cols.append(coords(sp.expand(img)))
    A=sp.Matrix(cols).T
    chi=sp.factor(sp.simplify((A-lam*sp.eye(A.shape[0])).det()),extension=[sp.sqrt(5),sp.sqrt(3),sp.sqrt(2),sp.I])
    val=sp.nsimplify(sp.simplify(chi.subs(lam,2)))
    print(name,': char.poly on H_3 =',chi,'\n    value at lam = 2:',val)
