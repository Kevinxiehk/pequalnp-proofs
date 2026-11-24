# round 11: the (2,2|2) "conic double deformation" is TRIVIAL.  f22 basis (gen_rank.py): V0 = row-0 part, U = row-1 part.
# Claim: det G(V0) and det G(U) both vanish exactly on the conic Q = 3m3^2-2m3m4+3m4^2-2m3-2m4+3 = 0; <V0,U> = 0 identically; hence
# J_V(V0) = rad(V0) = V0 cap U and J_U(U) = rad(U) = U cap V0, so both skew deformations only add elements e_1 x (x in U) resp. e_0 x
# (x in V0) that already lie in M: M(t,t2) = M(0,0), a member of the complete pattern (2,2|2) (Theorem DR22).
import sympy as sp
m3,m4=sp.symbols('m3 m4'); S=1+m3+m4
v0=sp.Matrix([0,m3-1,-m3,1,0]); v1=sp.Matrix([0,m4-1,-m4,0,1])
u0=sp.Matrix([4,-1,-1,-1,-1]); u1=sp.Matrix([-S,-S,5-S,5*m3-S,5*m4-S])
dot=lambda a,b:(a.T*b)[0]
GV=sp.Matrix([[dot(v0,v0),dot(v0,v1)],[dot(v1,v0),dot(v1,v1)]]); GU=sp.Matrix([[dot(u0,u0),dot(u0,u1)],[dot(u1,u0),dot(u1,u1)]])
Q=3*m3**2-2*m3*m4+3*m4**2-2*m3-2*m4+3
print('det G(V0) =',sp.factor(GV.det())); print('det G(U)  =',sp.factor(GU.det()))
print('<V0,U> =',[sp.expand(dot(a,b)) for a in (v0,v1) for b in (u0,u1)])
Sk=sp.Matrix([[0,1],[-1,0]])
JV=GV.adjugate()*Sk; JU=GU.adjugate()*Sk
# J(v_k) = sum_l JV[l,k] v_l (as in gen_rank_defo: J(v1) = g12 v1 - g11 v2, J(v2) = g22 v1 - g12 v2)
Jv=[GV[0,1]*v0-GV[0,0]*v1, GV[1,1]*v0-GV[0,1]*v1]; Ju=[GU[0,1]*u0-GU[0,0]*u1, GU[1,1]*u0-GU[0,1]*u1]
# membership: rank [u0,u1,Jv_k] = 2 and rank [v0,v1,Ju_k] = 2 modulo Q  (all 3x3 minors divisible by Q)
def in_span(a,b,x):
    A=sp.Matrix.hstack(a,b,x); ms=[A.extract(list(r),[0,1,2]).det() for r in __import__('itertools').combinations(range(5),3)]
    return all(sp.rem(sp.expand(m),Q,m3)==0 for m in ms)
print('J_V(v_k) in U on Q=0:',[in_span(u0,u1,x) for x in Jv]); print('J_U(u_k) in V0 on Q=0:',[in_span(v0,v1,x) for x in Ju])
