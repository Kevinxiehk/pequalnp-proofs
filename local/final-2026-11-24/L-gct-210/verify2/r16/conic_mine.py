# verify2 r17: independent check of reg2 R11-1 (conic double deformation trivial) -- own membership test via the ideal (Q) (Groebner reduction)
# and an exact point check on the conic over Q(sqrt(D)).
import sympy as sp, itertools
m3,m4=sp.symbols('m3 m4'); S=1+m3+m4
v0=sp.Matrix([0,m3-1,-m3,1,0]); v1=sp.Matrix([0,m4-1,-m4,0,1]); u0=sp.Matrix([4,-1,-1,-1,-1]); u1=sp.Matrix([-S,-S,5-S,5*m3-S,5*m4-S])
d=lambda a,b:sp.expand((a.T*b)[0])
Q=3*m3**2-2*m3*m4+3*m4**2-2*m3-2*m4+3
GV=sp.Matrix([[d(v0,v0),d(v0,v1)],[d(v1,v0),d(v1,v1)]]); GU=sp.Matrix([[d(u0,u0),d(u0,u1)],[d(u1,u0),d(u1,u1)]])
print('det GV / Q =',sp.cancel(GV.det()/Q),'  det GU / Q =',sp.cancel(GU.det()/Q),'  <V0,U> =',[d(a,b) for a in (v0,v1) for b in (u0,u1)])
print('row sums: v0,v1,u0,u1 ->',[sum(x) for x in (v0,v1,u0,u1)])
# the radical of a rank-1 2x2 Gram: adj(G) maps onto ker G; J_V v = adj-type combination
Jv=[GV[0,1]*v0-GV[0,0]*v1, GV[1,1]*v0-GV[0,1]*v1]; Ju=[GU[0,1]*u0-GU[0,0]*u1, GU[1,1]*u0-GU[0,1]*u1]
G=sp.groebner([Q],m3,m4,order='lex')
def in_span_modQ(a,b,x):
    A=sp.Matrix.hstack(a,b,x)
    return all(G.reduce(sp.expand(A.extract(list(r),[0,1,2]).det()))[1]==0 for r in itertools.combinations(range(5),3))
print('J_V(v_k) in U mod Q:',[in_span_modQ(u0,u1,x) for x in Jv],'  J_U(u_k) in V0 mod Q:',[in_span_modQ(v0,v1,x) for x in Ju])
# exact point on the conic: m4 = 0 -> 3 m3^2 - 2 m3 + 3 = 0, m3 = (1 +- 2 sqrt(-2))/3
for m3v in ((1+2*sp.sqrt(-2))/3,(1-2*sp.sqrt(-2))/3):
    sub={m3:m3v,m4:0}; A=sp.Matrix.hstack(u0,u1,*[x.subs(sub) for x in Jv]).subs(sub).applyfunc(sp.expand)
    B=sp.Matrix.hstack(v0,v1,*[x.subs(sub) for x in Ju]).subs(sub).applyfunc(sp.expand)
    print('point m3 =',m3v,': rank[U | J_V V] =',A.rank(simplify=True),' rank[V | J_U U] =',B.rank(simplify=True),' rank U =',sp.Matrix.hstack(u0,u1).subs(sub).rank(simplify=True))
