# verify2 r12: independent check of rows R10.2. For each configuration: B_j orthogonal up to sign (B^T B = I), det B_j = eps_j, sum B_j = 2I;
# then the action A0 f = sum_j f o B_j on the 7-dim space H_3 of HARMONIC cubics (own basis), and det(A0|H_3 - 2) as an exact algebraic number.
import sympy as sp, itertools
x1,x2,x3=sp.symbols('x1 x2 x3'); X=sp.Matrix([x1,x2,x3])
def cx(h): a,b,c=h; return sp.Matrix([[0,-c,b],[c,0,-a],[-b,a,0]])
H=[sp.Matrix(r) for r in ([1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1])]; I3=sp.eye(3)
r5=sp.sqrt(5); r3=sp.sqrt(3); r2=sp.sqrt(2); i=sp.I
def rot(s,v): return (s**2-(v.T*v)[0])*I3+2*v*v.T+2*s*cx(v)
s=[3/(2*r2),3/(2*r2),-r3/(2*r2),-r3/(2*r2)]; e=[1,1,-1,-1]
v=[sp.Matrix([-i/2,0,1/(2*r2)]),sp.Matrix([i/2,0,1/(2*r2)]),sp.Matrix([0,sp.Rational(1,2),-r3/(2*r2)]),sp.Matrix([0,-sp.Rational(1,2),-r3/(2*r2)])]
confs={'++++':([I3/4+h*h.T/4+r5*cx(h)/4 for h in H],[1,1,1,1]),
       '++++conj':([I3/4+h*h.T/4-r5*cx(h)/4 for h in H],[1,1,1,1]),
       '----':([5*I3/4-3*h*h.T/4-i*r3*cx(h)/4 for h in H],[-1]*4),
       '----conj':([5*I3/4-3*h*h.T/4+i*r3*cx(h)/4 for h in H],[-1]*4),
       '++--':([e[j]*rot(s[j],v[j]) for j in range(4)],e),
       '++--inv':([e[j]*rot(s[j],-v[j]) for j in range(4)],e)}
# harmonic cubic basis: Laplacian kernel in Sym^3, computed by linear algebra
mons=[x1**a*x2**b*x3**(3-a-b) for a in range(4) for b in range(4-a)]
cf=sp.symbols('c0:10'); gen=sum(c*m for c,m in zip(cf,mons))
lap=sp.expand(sum(sp.diff(gen,x,2) for x in (x1,x2,x3)))
sol=sp.solve(sp.Poly(lap,x1,x2,x3).coeffs(),cf,dict=True)[0]
free=[c for c in cf if c not in sol]
Hb=[sp.expand(gen.subs(sol).subs({c:(1 if c==f else 0) for c in free})) for f in free]
print('dim H_3 =',len(Hb), ' c = x1x2x3 harmonic:', sp.expand(sum(sp.diff(x1*x2*x3,x,2) for x in (x1,x2,x3)))==0)
def coords(f):   # coordinates of harmonic f in basis Hb
    a=sp.symbols('a0:%d'%len(Hb)); eq=sp.Poly(sp.expand(f-sum(ai*h for ai,h in zip(a,Hb))),x1,x2,x3).coeffs()
    so=sp.solve(eq,a,dict=True); assert so, 'not harmonic?'; return [sp.simplify(so[0][ai]) for ai in a]
for name,(Bs,eps) in confs.items():
    orth=all(sp.simplify(B.T*B-I3)==sp.zeros(3,3) for B in Bs); dets=[sp.simplify(B.det()) for B in Bs]
    sB=sp.simplify(sum(Bs,sp.zeros(3,3))-2*I3)==sp.zeros(3,3)
    A=sp.zeros(len(Hb),len(Hb))
    for k,h in enumerate(Hb):
        img=0
        for B in Bs:
            Y=B*X; img+=h.subs({x1:Y[0],x2:Y[1],x3:Y[2]},simultaneous=True)
        col=coords(sp.expand(img))
        for l in range(len(Hb)): A[l,k]=col[l]
    d=sp.nsimplify(sp.simplify((A-2*sp.eye(len(Hb))).det()))
    cpoly=sp.factor(sp.simplify((A-sp.Symbol('lam')*sp.eye(len(Hb))).det()),extension=None)
    print(name,': orthogonal',orth,' dets',dets,'(eps',eps,') sumB=2I',sB,' det(A0|H3 - 2) =',sp.simplify(d),flush=True)
